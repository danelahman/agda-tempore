------------------------------------------------------------------
-- Narrowing the var-rule disjunctions of a reported hypothesis   --
-- set                                                            --
--                                                                --
-- `simplify` settles every `disj` entry one of whose sides the    --
-- deciders decide: a met eternality demand drops the entry, a     --
-- refuted one leaves the grade ordering behind, and a refuted     --
-- grade leaves the eternality atoms behind. Entries with both     --
-- sides open are kept.                                           --
--                                                                --
-- The justification is semantic: `simplify Q` and `Q` are         --
-- satisfied by exactly the same groundings. Entailment cannot     --
-- narrow — a `disj` hypothesis proves `VarOK` with neither        --
-- disjunct in hand — so this is a simplification of the report,   --
-- not of the solver, and `solve-principal` is untouched.          --
------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.Open.Hyps as H

module TypeInference.SolverImpl.Simplify
  (S : LanguageSpec)
  (_≾ᵣ?_ : Decidable (Grade._≾_ (GradeSystem.RGrade (LanguageSpec.Grades S))))
  (_≾ₑ?_ : Decidable (Grade._≾_ (GradeSystem.EGrade (LanguageSpec.Grades S))))
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  where

open LanguageSpec S
open GradeSystemInterface Grades

-- The `Eternal` constructors share their names with those of the
-- mirrored `_⊩ᴱ_`; each occurrence below is resolved by its type.

open import Syntax.Types S
  using (Eternal; Baseₑ; Unitₑ; Boolₑ; _|×|ₑ_; Emptyₑ;
         EternalBaseType; eternalBaseType?)

open import TypeInference.Open.Grades    S
open import TypeInference.Open.Types     S
open import TypeInference.Open.Hyps      S
open import TypeInference.Open.Grounding S

open import TypeInference.SolverImpl.Core.Rigid S using (zip₂-just)

open import TypeInference.SolverImpl.Resid  S using (etDec)
open import TypeInference.SolverImpl.Refute S _≾ᵣ?_ _≾ₑ?_ umin?ᵣ umin?ₑ
  using (Refutedᵤ; scanᵤ)

-- `etDec` read at a grounding: the closed `Eternal` of `Syntax.Types`
-- has the same clauses as the mirrored `_⊩ᴱ_`.

etDec-Et : ∀ {Θ} {θ : Grounding Θ} → (A : OVType Θ) → {αs : List (TyVar Θ)}
         → etDec A ≡ just αs → (∀ {α} → α ∈ αs → Eternal (gTy θ α))
         → Eternal (⟦ A ⟧ᵛ θ)
etDec-Et (tvar α) refl k = k (here refl)
etDec-Et (Base b) q k with eternalBaseType? b
etDec-Et (Base b) refl k | yes p = Baseₑ p
etDec-Et Unit  refl k = Unitₑ
etDec-Et Bool  refl k = Boolₑ
etDec-Et Empty refl k = Emptyₑ
etDec-Et (A |×| B) q k with zip₂-just _++_ (etDec A) (etDec B) q
... | as , bs , qa , qb , refl =
      etDec-Et A qa (λ m → k (∈-++⁺ˡ m)) |×|ₑ
      etDec-Et B qb (λ m → k (∈-++⁺ʳ as m))

etDec-atoms : ∀ {Θ} {θ : Grounding Θ} → (A : OVType Θ) → {αs : List (TyVar Θ)}
            → etDec A ≡ just αs → Eternal (⟦ A ⟧ᵛ θ)
            → ∀ {α} → α ∈ αs → Eternal (gTy θ α)
etDec-atoms (tvar β) refl et (here refl) = et
etDec-atoms (Base b) q et with eternalBaseType? b
etDec-atoms (Base b) refl et | yes p = λ ()
etDec-atoms Unit  refl et = λ ()
etDec-atoms Bool  refl et = λ ()
etDec-atoms Empty refl et = λ ()
etDec-atoms (A |×| B) q (p |×|ₑ p') with zip₂-just _++_ (etDec A) (etDec B) q
... | as , bs , qa , qb , refl =
      λ m → [ etDec-atoms A qa p , etDec-atoms B qb p' ]′ (∈-++⁻ as m)

etDec-¬Et : ∀ {Θ} {θ : Grounding Θ} → (A : OVType Θ) → etDec A ≡ nothing
          → ¬ Eternal (⟦ A ⟧ᵛ θ)
etDec-¬Et (Base b) q with eternalBaseType? b
etDec-¬Et (Base b) q | no ¬p = λ { (Baseₑ p') → ⊥-elim-irr (¬p p') }
etDec-¬Et (A |×| B) q with etDec A in e₁ | etDec B in e₂
etDec-¬Et (A |×| B) q | just _  | nothing = λ { (p |×|ₑ p') → etDec-¬Et B e₂ p' }
etDec-¬Et (A |×| B) q | nothing | _       = λ { (p |×|ₑ p') → etDec-¬Et A e₁ p }
etDec-¬Et (A ⇒ C)   q = λ ()
etDec-¬Et ([ ρ ] A) q = λ ()

-- The ground reading of one var-rule disjunction, as `_⊨ᴴ_` states it

Disj : ∀ {Θ} → Grounding Θ → OVType Θ → RExp Θ → Set
Disj θ A ρ = Eternal (⟦ A ⟧ᵛ θ) ⊎ (⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)

-- One disjunction, settled against the two deciders

narrow : ∀ {Θ} → OVType Θ → RExp Θ → Hyps Θ → Hyps Θ
narrow A ρ Q with etDec A
... | just []       = Q
... | nothing       = hyps (ets Q) ((ρ , ûᵣ) ∷ ordᵣ Q) (ordₑ Q) (disj Q)
... | just (α ∷ αs) with scanᵤ ρ
...   | just _  = hyps ((α ∷ αs) ++ ets Q) (ordᵣ Q) (ordₑ Q) (disj Q)
...   | nothing = hyps (ets Q) (ordᵣ Q) (ordₑ Q) ((A , ρ) ∷ disj Q)

narrow-⊨ : ∀ {Θ} {θ : Grounding Θ} → (A : OVType Θ) → (ρ : RExp Θ) → (Q : Hyps Θ)
         → Disj θ A ρ → θ ⊨ᴴ Q → θ ⊨ᴴ narrow A ρ Q
narrow-⊨ {θ = θ} A ρ Q d h with etDec A in e
... | just []       = h
... | nothing       = mk⊨ᴴ (etOK h) ordR (ordEOK h) (disjOK h)
      where
        ordR : ∀ {ρ₀ ρ₀'} → (ρ₀ , ρ₀') ∈ ((ρ , ûᵣ) ∷ ordᵣ Q)
             → ⟦ ρ₀ ⟧ʳ θ ≾ᵣ ⟦ ρ₀' ⟧ʳ θ
        ordR (here refl) = [ (λ et → ⊥-elim (etDec-¬Et A e et)) , (λ le → le) ]′ d
        ordR (there m)   = ordROK h m
... | just (α ∷ αs) with scanᵤ ρ
...   | just ref = mk⊨ᴴ et' (ordROK h) (ordEOK h) (disjOK h)
      where
        etA : Eternal (⟦ A ⟧ᵛ θ)
        etA = [ (λ et → et) , (λ le → ⊥-elim (ref θ le)) ]′ d

        et' : ∀ {β} → β ∈ ((α ∷ αs) ++ ets Q) → Eternal (gTy θ β)
        et' m = [ etDec-atoms A e etA , etOK h ]′ (∈-++⁻ (α ∷ αs) m)
...   | nothing = mk⊨ᴴ (etOK h) (ordROK h) (ordEOK h) dsj'
      where
        dsj' : ∀ {A₀ ρ₀} → (A₀ , ρ₀) ∈ ((A , ρ) ∷ disj Q) → Disj θ A₀ ρ₀
        dsj' (here refl) = d
        dsj' (there m)   = disjOK h m

narrow-⊨⁻ : ∀ {Θ} {θ : Grounding Θ} → (A : OVType Θ) → (ρ : RExp Θ) → (Q : Hyps Θ)
          → θ ⊨ᴴ narrow A ρ Q → (θ ⊨ᴴ Q) × Disj θ A ρ
narrow-⊨⁻ A ρ Q h with etDec A in e
... | just []       = h , inj₁ (etDec-Et A e (λ ()))
... | nothing       = mk⊨ᴴ (etOK h) (λ m → ordROK h (there m)) (ordEOK h) (disjOK h)
                    , inj₂ (ordROK h (here refl))
... | just (α ∷ αs) with scanᵤ ρ
...   | just _  = mk⊨ᴴ (λ m → etOK h (∈-++⁺ʳ (α ∷ αs) m))
                       (ordROK h) (ordEOK h) (disjOK h)
                , inj₁ (etDec-Et A e (λ m → etOK h (∈-++⁺ˡ m)))
...   | nothing = mk⊨ᴴ (etOK h) (ordROK h) (ordEOK h) (λ m → disjOK h (there m))
                , disjOK h (here refl)

narrowAll : ∀ {Θ} → List (OVType Θ × RExp Θ) → Hyps Θ → Hyps Θ
narrowAll []             Q₀ = Q₀
narrowAll ((A , ρ) ∷ l) Q₀ = narrow A ρ (narrowAll l Q₀)

narrowAll-⊨ : ∀ {Θ} {θ : Grounding Θ} → (l : List (OVType Θ × RExp Θ))
            → (Q₀ : Hyps Θ) → (∀ {A ρ} → (A , ρ) ∈ l → Disj θ A ρ) → θ ⊨ᴴ Q₀
            → θ ⊨ᴴ narrowAll l Q₀
narrowAll-⊨ []             Q₀ k h = h
narrowAll-⊨ ((A , ρ) ∷ l) Q₀ k h =
  narrow-⊨ A ρ (narrowAll l Q₀) (k (here refl))
           (narrowAll-⊨ l Q₀ (λ m → k (there m)) h)

narrowAll-⊨⁻ : ∀ {Θ} {θ : Grounding Θ} → (l : List (OVType Θ × RExp Θ))
             → (Q₀ : Hyps Θ) → θ ⊨ᴴ narrowAll l Q₀
             → (θ ⊨ᴴ Q₀) × (∀ {A ρ} → (A , ρ) ∈ l → Disj θ A ρ)
narrowAll-⊨⁻ []             Q₀ h = h , λ ()
narrowAll-⊨⁻ ((A , ρ) ∷ l) Q₀ h with narrow-⊨⁻ A ρ (narrowAll l Q₀) h
... | h' , d with narrowAll-⊨⁻ l Q₀ h'
...   | h'' , k = h'' , λ { (here refl) → d ; (there m) → k m }

simplify : ∀ {Θ} → Hyps Θ → Hyps Θ
simplify Q = narrowAll (disj Q) (hyps (ets Q) (ordᵣ Q) (ordₑ Q) [])

-- Simplification changes nothing a grounding can see

simplify-⊨ : ∀ {Θ} → (Q : Hyps Θ) → (θ : Grounding Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ simplify Q
simplify-⊨ Q θ h =
  narrowAll-⊨ (disj Q) (hyps (ets Q) (ordᵣ Q) (ordₑ Q) []) (disjOK h)
              (mk⊨ᴴ (etOK h) (ordROK h) (ordEOK h) (λ ()))

simplify-⊨⁻ : ∀ {Θ} → (Q : Hyps Θ) → (θ : Grounding Θ) → θ ⊨ᴴ simplify Q → θ ⊨ᴴ Q
simplify-⊨⁻ Q θ h
  with narrowAll-⊨⁻ (disj Q) (hyps (ets Q) (ordᵣ Q) (ordₑ Q) []) h
... | h₀ , k = mk⊨ᴴ (etOK h₀) (ordROK h₀) (ordEOK h₀) k

simplify-≃ : ∀ {Θ} → (Q : Hyps Θ) → (θ : Grounding Θ)
           → (θ ⊨ᴴ Q → θ ⊨ᴴ simplify Q) × (θ ⊨ᴴ simplify Q → θ ⊨ᴴ Q)
simplify-≃ Q θ = simplify-⊨ Q θ , simplify-⊨⁻ Q θ
