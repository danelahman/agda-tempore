------------------------------------------------------------------
-- Narrowing and pruning a reported hypothesis set                --
--                                                                --
-- `simplify` settles every `disj` entry one of whose sides is     --
-- settled: a met eternality demand drops the entry, a refuted     --
-- one leaves the grade ordering behind, and a refuted grade       --
-- leaves the eternality atoms behind. Eternality is met either    --
-- outright or through the set's own atoms and subtyping           --
-- hypotheses. It then drops every hypothesis the rest of the set  --
-- still entails.                                                  --
--                                                                --
-- The justification is semantic: `simplify Q` and `Q` are         --
-- satisfied by exactly the same groundings. Entailment cannot     --
-- narrow — a `disj` hypothesis proves `VarOK` with neither        --
-- disjunct in hand — so this is a simplification of the report,   --
-- not of the solver, and `solve-principal` is untouched.          --
------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
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

-- Derivations reading only a list of subtyping hypotheses and a list
-- of eternality atoms: `_⊢ᵖ_≾_` mirrors `_⊩ᵗᵛ_≾_`, `Etᴾ` mirrors
-- `_⊩ᴱ_` at a type variable. Eternality moves along a hypothesis in
-- both directions, subtyping only forwards.

infix 4 _⊢ᵖ_≾_

data _⊢ᵖ_≾_ {n : ℕ} (l : List (Fin n × Fin n)) : Fin n → Fin n → Set where
  stopᵖ : ∀ {α} → l ⊢ᵖ α ≾ α
  stepᵖ : ∀ {α β γ} → (α , β) ∈ l → l ⊢ᵖ β ≾ γ → l ⊢ᵖ α ≾ γ

data Etᴾ {n : ℕ} (l : List (Fin n × Fin n)) (as : List (Fin n)) : Fin n → Set where
  atomᴾ : ∀ {α} → α ∈ as → Etᴾ l as α
  downᴾ : ∀ {α β} → (α , β) ∈ l → Etᴾ l as β → Etᴾ l as α
  upᴾ   : ∀ {α β} → (α , β) ∈ l → Etᴾ l as α → Etᴾ l as β

transᵖ : ∀ {n} {l : List (Fin n × Fin n)} {α β γ}
       → l ⊢ᵖ α ≾ β → l ⊢ᵖ β ≾ γ → l ⊢ᵖ α ≾ γ
transᵖ stopᵖ       q = q
transᵖ (stepᵖ m p) q = stepᵖ m (transᵖ p q)

⊢ᵖ-mono : ∀ {n} {l l' : List (Fin n × Fin n)} {α β}
        → (∀ {p} → p ∈ l → p ∈ l') → l ⊢ᵖ α ≾ β → l' ⊢ᵖ α ≾ β
⊢ᵖ-mono k stopᵖ       = stopᵖ
⊢ᵖ-mono k (stepᵖ m p) = stepᵖ (k m) (⊢ᵖ-mono k p)

⊢ᵖ-⊩ : ∀ {Θ} {Q : Hyps Θ} {l α β} → (∀ {p} → p ∈ l → p ∈ subᵥ Q)
     → l ⊢ᵖ α ≾ β → Q ⊩ᵗᵛ α ≾ β
⊢ᵖ-⊩ k stopᵖ       = reflᵗᵛ
⊢ᵖ-⊩ k (stepᵖ m p) = transᵗᵛ (hypᵗᵛ (k m)) (⊢ᵖ-⊩ k p)

Etᴾ-mono : ∀ {n} {l l' : List (Fin n × Fin n)} {as as' : List (Fin n)} {α}
         → (∀ {p} → p ∈ l → p ∈ l') → (∀ {β} → β ∈ as → β ∈ as')
         → Etᴾ l as α → Etᴾ l' as' α
Etᴾ-mono k j (atomᴾ m)    = atomᴾ (j m)
Etᴾ-mono k j (downᴾ m et) = downᴾ (k m) (Etᴾ-mono k j et)
Etᴾ-mono k j (upᴾ m et)   = upᴾ (k m) (Etᴾ-mono k j et)

Etᴾ-⊩ : ∀ {Θ} {Q : Hyps Θ} {l as α} → (∀ {p} → p ∈ l → p ∈ subᵥ Q)
      → (∀ {β} → β ∈ as → β ∈ ets Q) → Etᴾ l as α → Q ⊩ᴱ tvar α
Etᴾ-⊩ k j (atomᴾ m)    = et-hyp (j m)
Etᴾ-⊩ k j (downᴾ m et) = et-subˡ (hypᵗᵛ (k m)) (Etᴾ-⊩ k j et)
Etᴾ-⊩ k j (upᴾ m et)   = et-subʳ (hypᵗᵛ (k m)) (Etᴾ-⊩ k j et)

-- Both searches saturate a labelled vertex set along the hypotheses,
-- one round per edge: a shortest path uses at most that many.

module _ {n : ℕ} (l : List (Fin n × Fin n)) where

  findᴱ : ∀ {as} → List (Σ[ α ∈ Fin n ] Etᴾ l as α) → (α : Fin n)
        → Maybe (Etᴾ l as α)
  findᴱ []            α = nothing
  findᴱ ((β , w) ∷ s) α with α ≟ᶠ β
  ... | yes refl = just w
  ... | no  _    = findᴱ s α

  growᴱ : ∀ {as} → (m : List (Fin n × Fin n)) → (∀ {p} → p ∈ m → p ∈ l)
        → List (Σ[ α ∈ Fin n ] Etᴾ l as α) → List (Σ[ α ∈ Fin n ] Etᴾ l as α)
  growᴱ []            k s = s
  growᴱ ((α , β) ∷ m) k s with growᴱ m (λ q → k (there q)) s
  ... | s' with findᴱ s' α | findᴱ s' β
  ...   | just w  | nothing = (β , upᴾ (k (here refl)) w) ∷ s'
  ...   | nothing | just w  = (α , downᴾ (k (here refl)) w) ∷ s'
  ...   | _       | _       = s'

  satᴱ : ∀ {as} → ℕ → List (Σ[ α ∈ Fin n ] Etᴾ l as α)
       → List (Σ[ α ∈ Fin n ] Etᴾ l as α)
  satᴱ ℕ.zero    s = s
  satᴱ (ℕ.suc n) s = satᴱ n (growᴱ l (λ q → q) s)

  seedᴱ : ∀ {as} → (bs : List (Fin n)) → (∀ {β} → β ∈ bs → β ∈ as)
        → List (Σ[ α ∈ Fin n ] Etᴾ l as α)
  seedᴱ []       k = []
  seedᴱ (β ∷ bs) k = (β , atomᴾ (k (here refl))) ∷ seedᴱ bs (λ q → k (there q))

  etᴾ? : (as : List (Fin n)) → (α : Fin n) → Maybe (Etᴾ l as α)
  etᴾ? as = findᴱ (satᴱ (length l) (seedᴱ as (λ q → q)))

  findᵖ : ∀ {α} → List (Σ[ γ ∈ Fin n ] (l ⊢ᵖ α ≾ γ)) → (β : Fin n)
        → Maybe (l ⊢ᵖ α ≾ β)
  findᵖ []            β = nothing
  findᵖ ((γ , w) ∷ s) β with β ≟ᶠ γ
  ... | yes refl = just w
  ... | no  _    = findᵖ s β

  growᵖ : ∀ {α} → (m : List (Fin n × Fin n)) → (∀ {p} → p ∈ m → p ∈ l)
        → List (Σ[ γ ∈ Fin n ] (l ⊢ᵖ α ≾ γ))
        → List (Σ[ γ ∈ Fin n ] (l ⊢ᵖ α ≾ γ))
  growᵖ []            k s = s
  growᵖ ((β , γ) ∷ m) k s with growᵖ m (λ q → k (there q)) s
  ... | s' with findᵖ s' β | findᵖ s' γ
  ...   | just w | nothing = (γ , transᵖ w (stepᵖ (k (here refl)) stopᵖ)) ∷ s'
  ...   | _      | _       = s'

  satᵖ : ∀ {α} → ℕ → List (Σ[ γ ∈ Fin n ] (l ⊢ᵖ α ≾ γ))
       → List (Σ[ γ ∈ Fin n ] (l ⊢ᵖ α ≾ γ))
  satᵖ ℕ.zero    s = s
  satᵖ (ℕ.suc n) s = satᵖ n (growᵖ l (λ q → q) s)

  reach? : (α β : Fin n) → Maybe (l ⊢ᵖ α ≾ β)
  reach? α = findᵖ (satᵖ (length l) ((α , stopᵖ) ∷ []))

-- Eternality of every atom a type decomposes to, from the set itself

ets? : ∀ {Θ} → (Q : Hyps Θ) → (as : List (TyVar Θ))
     → Maybe (∀ {α} → α ∈ as → Q ⊩ᴱ tvar α)
ets? Q []       = just (λ ())
ets? Q (α ∷ as) with etᴾ? (subᵥ Q) (ets Q) α | ets? Q as
... | just w | just k = just (λ { (here refl) → Etᴾ-⊩ (λ q → q) (λ q → q) w
                                ; (there m)   → k m })
... | _      | _      = nothing

-- One disjunction, settled against the deciders and the set itself

narrow : ∀ {Θ} → OVType Θ → RExp Θ → Hyps Θ → Hyps Θ
narrow A ρ Q with etDec A
... | nothing = hyps (ets Q) (subᵥ Q) ((ρ , ûᵣ) ∷ ordᵣ Q) (ordₑ Q) (disj Q)
... | just αs with ets? Q αs
...   | just _  = Q
...   | nothing with scanᵤ ρ
...     | just _  = hyps (αs ++ ets Q) (subᵥ Q) (ordᵣ Q) (ordₑ Q) (disj Q)
...     | nothing = hyps (ets Q) (subᵥ Q) (ordᵣ Q) (ordₑ Q) ((A , ρ) ∷ disj Q)

narrow-⊨ : ∀ {Θ} {θ : Grounding Θ} → (A : OVType Θ) → (ρ : RExp Θ) → (Q : Hyps Θ)
         → Disj θ A ρ → θ ⊨ᴴ Q → θ ⊨ᴴ narrow A ρ Q
narrow-⊨ {θ = θ} A ρ Q d h with etDec A in e
... | nothing = mk⊨ᴴ (etOK h) (subOK h) ordR (ordEOK h) (disjOK h)
      where
        ordR : ∀ {ρ₀ ρ₀'} → (ρ₀ , ρ₀') ∈ ((ρ , ûᵣ) ∷ ordᵣ Q)
             → ⟦ ρ₀ ⟧ʳ θ ≾ᵣ ⟦ ρ₀' ⟧ʳ θ
        ordR (here refl) = [ (λ et → ⊥-elim (etDec-¬Et A e et)) , (λ le → le) ]′ d
        ordR (there m)   = ordROK h m
... | just αs with ets? Q αs
...   | just _  = h
...   | nothing with scanᵤ ρ
...     | just ref = mk⊨ᴴ et' (subOK h) (ordROK h) (ordEOK h) (disjOK h)
      where
        etA : Eternal (⟦ A ⟧ᵛ θ)
        etA = [ (λ et → et) , (λ le → ⊥-elim (ref θ le)) ]′ d

        et' : ∀ {β} → β ∈ (αs ++ ets Q) → Eternal (gTy θ β)
        et' m = [ etDec-atoms A e etA , etOK h ]′ (∈-++⁻ αs m)
...     | nothing = mk⊨ᴴ (etOK h) (subOK h) (ordROK h) (ordEOK h) dsj'
      where
        dsj' : ∀ {A₀ ρ₀} → (A₀ , ρ₀) ∈ ((A , ρ) ∷ disj Q) → Disj θ A₀ ρ₀
        dsj' (here refl) = d
        dsj' (there m)   = disjOK h m

narrow-⊨⁻ : ∀ {Θ} {θ : Grounding Θ} → (A : OVType Θ) → (ρ : RExp Θ) → (Q : Hyps Θ)
          → θ ⊨ᴴ narrow A ρ Q → (θ ⊨ᴴ Q) × Disj θ A ρ
narrow-⊨⁻ A ρ Q h with etDec A in e
... | nothing = mk⊨ᴴ (etOK h) (subOK h) (λ m → ordROK h (there m)) (ordEOK h) (disjOK h)
              , inj₂ (ordROK h (here refl))
... | just αs with ets? Q αs
...   | just k  = h , inj₁ (etDec-Et A e (λ m → ground-Et h (k m)))
...   | nothing with scanᵤ ρ
...     | just _  = mk⊨ᴴ (λ m → etOK h (∈-++⁺ʳ αs m))
                         (subOK h) (ordROK h) (ordEOK h) (disjOK h)
                  , inj₁ (etDec-Et A e (λ m → etOK h (∈-++⁺ˡ m)))
...     | nothing = mk⊨ᴴ (etOK h) (subOK h) (ordROK h) (ordEOK h) (λ m → disjOK h (there m))
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

-- A hypothesis the rest of the set still entails is redundant, and is
-- dropped. The criterion is decided here for the subtyping atoms and
-- the eternality atoms, where entailment is reachability in a finite
-- digraph; it is left undecided for the grade orderings, `_⊩_≾̂ᵣ_` and
-- `_⊩_≾̂ₑ_` closing the hypotheses under `monoᵣ`, `map-mono`, `eqᵣ`
-- and transitivity as well. Each atom is tested against the suffix
-- already decided, so its justification survives into the result.

pruneᵛ : ∀ {n} → List (Fin n × Fin n) → List (Fin n × Fin n) → List (Fin n × Fin n)
pruneᵛ acc []            = acc
pruneᵛ acc ((α , β) ∷ l) with reach? acc α β
... | just _  = pruneᵛ acc l
... | nothing = pruneᵛ ((α , β) ∷ acc) l

pruneᵛ-⊇ : ∀ {n} → (acc l : List (Fin n × Fin n)) → ∀ {p} → p ∈ acc → p ∈ pruneᵛ acc l
pruneᵛ-⊇ acc []            m = m
pruneᵛ-⊇ acc ((α , β) ∷ l) m with reach? acc α β
... | just _  = pruneᵛ-⊇ acc l m
... | nothing = pruneᵛ-⊇ ((α , β) ∷ acc) l (there m)

pruneᵛ-⊆ : ∀ {n} → (acc l : List (Fin n × Fin n))
         → ∀ {p} → p ∈ pruneᵛ acc l → (p ∈ acc) ⊎ (p ∈ l)
pruneᵛ-⊆ acc []            m = inj₁ m
pruneᵛ-⊆ acc ((α , β) ∷ l) m with reach? acc α β
... | just _  = [ inj₁ , (λ q → inj₂ (there q)) ]′ (pruneᵛ-⊆ acc l m)
... | nothing with pruneᵛ-⊆ ((α , β) ∷ acc) l m
...   | inj₁ (here refl) = inj₂ (here refl)
...   | inj₁ (there q)   = inj₁ q
...   | inj₂ q           = inj₂ (there q)

pruneᵛ-path : ∀ {n} → (acc l : List (Fin n × Fin n)) → ∀ {α β}
            → (α , β) ∈ l → pruneᵛ acc l ⊢ᵖ α ≾ β
pruneᵛ-path acc ((α₀ , β₀) ∷ l) m with reach? acc α₀ β₀
pruneᵛ-path acc ((α₀ , β₀) ∷ l) (here refl) | just p  =
  ⊢ᵖ-mono (pruneᵛ-⊇ acc l) p
pruneᵛ-path acc ((α₀ , β₀) ∷ l) (there m)   | just p  = pruneᵛ-path acc l m
pruneᵛ-path acc ((α₀ , β₀) ∷ l) (here refl) | nothing =
  stepᵖ (pruneᵛ-⊇ ((α₀ , β₀) ∷ acc) l (here refl)) stopᵖ
pruneᵛ-path acc ((α₀ , β₀) ∷ l) (there m)   | nothing =
  pruneᵛ-path ((α₀ , β₀) ∷ acc) l m

pruneᴱ : ∀ {n} → List (Fin n × Fin n) → List (Fin n) → List (Fin n) → List (Fin n)
pruneᴱ l acc []       = acc
pruneᴱ l acc (α ∷ as) with etᴾ? l acc α
... | just _  = pruneᴱ l acc as
... | nothing = pruneᴱ l (α ∷ acc) as

pruneᴱ-⊇ : ∀ {n} → (l : List (Fin n × Fin n)) → (acc as : List (Fin n))
         → ∀ {α} → α ∈ acc → α ∈ pruneᴱ l acc as
pruneᴱ-⊇ l acc []        m = m
pruneᴱ-⊇ l acc (α₀ ∷ as) m with etᴾ? l acc α₀
... | just _  = pruneᴱ-⊇ l acc as m
... | nothing = pruneᴱ-⊇ l (α₀ ∷ acc) as (there m)

pruneᴱ-⊆ : ∀ {n} → (l : List (Fin n × Fin n)) → (acc as : List (Fin n))
         → ∀ {α} → α ∈ pruneᴱ l acc as → (α ∈ acc) ⊎ (α ∈ as)
pruneᴱ-⊆ l acc []        m = inj₁ m
pruneᴱ-⊆ l acc (α₀ ∷ as) m with etᴾ? l acc α₀
... | just _  = [ inj₁ , (λ q → inj₂ (there q)) ]′ (pruneᴱ-⊆ l acc as m)
... | nothing with pruneᴱ-⊆ l (α₀ ∷ acc) as m
...   | inj₁ (here refl) = inj₂ (here refl)
...   | inj₁ (there q)   = inj₁ q
...   | inj₂ q           = inj₂ (there q)

pruneᴱ-et : ∀ {n} → (l : List (Fin n × Fin n)) → (acc as : List (Fin n))
          → ∀ {α} → α ∈ as → Etᴾ l (pruneᴱ l acc as) α
pruneᴱ-et l acc (α₀ ∷ as) m with etᴾ? l acc α₀
pruneᴱ-et l acc (α₀ ∷ as) (here refl) | just w  =
  Etᴾ-mono (λ q → q) (pruneᴱ-⊇ l acc as) w
pruneᴱ-et l acc (α₀ ∷ as) (there m)   | just w  = pruneᴱ-et l acc as m
pruneᴱ-et l acc (α₀ ∷ as) (here refl) | nothing =
  atomᴾ (pruneᴱ-⊇ l (α₀ ∷ acc) as (here refl))
pruneᴱ-et l acc (α₀ ∷ as) (there m)   | nothing = pruneᴱ-et l (α₀ ∷ acc) as m

-- A grade ordering is entailed by the rest exactly when the rest
-- repeats it: `hypᵣ`/`hypₑ` is the only rule deciding here.

memʳ? : ∀ {Θ} → (p : RExp Θ × RExp Θ) → (l : List (RExp Θ × RExp Θ)) → Maybe (p ∈ l)
memʳ? p []              = nothing
memʳ? (ρ , ρ') ((ρ₀ , ρ₀') ∷ l) with ρ ≟ʳ ρ₀ | ρ' ≟ʳ ρ₀'
... | yes refl | yes refl = just (here refl)
... | _        | _        with memʳ? (ρ , ρ') l
...   | just m  = just (there m)
...   | nothing = nothing

memᵉ? : ∀ {Θ} → (p : EExp Θ × EExp Θ) → (l : List (EExp Θ × EExp Θ)) → Maybe (p ∈ l)
memᵉ? p []              = nothing
memᵉ? (ε , ε') ((ε₀ , ε₀') ∷ l) with ε ≟ᵉ ε₀ | ε' ≟ᵉ ε₀'
... | yes refl | yes refl = just (here refl)
... | _        | _        with memᵉ? (ε , ε') l
...   | just m  = just (there m)
...   | nothing = nothing

pruneᴼʳ : ∀ {Θ} → List (RExp Θ × RExp Θ) → List (RExp Θ × RExp Θ)
        → List (RExp Θ × RExp Θ)
pruneᴼʳ acc []      = acc
pruneᴼʳ acc (p ∷ l) with memʳ? p acc
... | just _  = pruneᴼʳ acc l
... | nothing = pruneᴼʳ (p ∷ acc) l

pruneᴼʳ-⊇ : ∀ {Θ} → (acc l : List (RExp Θ × RExp Θ))
          → ∀ {p} → p ∈ acc → p ∈ pruneᴼʳ acc l
pruneᴼʳ-⊇ acc []       m = m
pruneᴼʳ-⊇ acc (p₀ ∷ l) m with memʳ? p₀ acc
... | just _  = pruneᴼʳ-⊇ acc l m
... | nothing = pruneᴼʳ-⊇ (p₀ ∷ acc) l (there m)

pruneᴼʳ-⊆ : ∀ {Θ} → (acc l : List (RExp Θ × RExp Θ))
          → ∀ {p} → p ∈ pruneᴼʳ acc l → (p ∈ acc) ⊎ (p ∈ l)
pruneᴼʳ-⊆ acc []       m = inj₁ m
pruneᴼʳ-⊆ acc (p₀ ∷ l) m with memʳ? p₀ acc
... | just _  = [ inj₁ , (λ q → inj₂ (there q)) ]′ (pruneᴼʳ-⊆ acc l m)
... | nothing with pruneᴼʳ-⊆ (p₀ ∷ acc) l m
...   | inj₁ (here refl) = inj₂ (here refl)
...   | inj₁ (there q)   = inj₁ q
...   | inj₂ q           = inj₂ (there q)

pruneᴼʳ-mem : ∀ {Θ} → (acc l : List (RExp Θ × RExp Θ))
            → ∀ {p} → p ∈ l → p ∈ pruneᴼʳ acc l
pruneᴼʳ-mem acc (p₀ ∷ l) m with memʳ? p₀ acc
pruneᴼʳ-mem acc (p₀ ∷ l) (here refl) | just m₀ = pruneᴼʳ-⊇ acc l m₀
pruneᴼʳ-mem acc (p₀ ∷ l) (there m)   | just m₀ = pruneᴼʳ-mem acc l m
pruneᴼʳ-mem acc (p₀ ∷ l) (here refl) | nothing =
  pruneᴼʳ-⊇ (p₀ ∷ acc) l (here refl)
pruneᴼʳ-mem acc (p₀ ∷ l) (there m)   | nothing = pruneᴼʳ-mem (p₀ ∷ acc) l m

pruneᴼᵉ : ∀ {Θ} → List (EExp Θ × EExp Θ) → List (EExp Θ × EExp Θ)
        → List (EExp Θ × EExp Θ)
pruneᴼᵉ acc []      = acc
pruneᴼᵉ acc (p ∷ l) with memᵉ? p acc
... | just _  = pruneᴼᵉ acc l
... | nothing = pruneᴼᵉ (p ∷ acc) l

pruneᴼᵉ-⊇ : ∀ {Θ} → (acc l : List (EExp Θ × EExp Θ))
          → ∀ {p} → p ∈ acc → p ∈ pruneᴼᵉ acc l
pruneᴼᵉ-⊇ acc []       m = m
pruneᴼᵉ-⊇ acc (p₀ ∷ l) m with memᵉ? p₀ acc
... | just _  = pruneᴼᵉ-⊇ acc l m
... | nothing = pruneᴼᵉ-⊇ (p₀ ∷ acc) l (there m)

pruneᴼᵉ-⊆ : ∀ {Θ} → (acc l : List (EExp Θ × EExp Θ))
          → ∀ {p} → p ∈ pruneᴼᵉ acc l → (p ∈ acc) ⊎ (p ∈ l)
pruneᴼᵉ-⊆ acc []       m = inj₁ m
pruneᴼᵉ-⊆ acc (p₀ ∷ l) m with memᵉ? p₀ acc
... | just _  = [ inj₁ , (λ q → inj₂ (there q)) ]′ (pruneᴼᵉ-⊆ acc l m)
... | nothing with pruneᴼᵉ-⊆ (p₀ ∷ acc) l m
...   | inj₁ (here refl) = inj₂ (here refl)
...   | inj₁ (there q)   = inj₁ q
...   | inj₂ q           = inj₂ (there q)

pruneᴼᵉ-mem : ∀ {Θ} → (acc l : List (EExp Θ × EExp Θ))
            → ∀ {p} → p ∈ l → p ∈ pruneᴼᵉ acc l
pruneᴼᵉ-mem acc (p₀ ∷ l) m with memᵉ? p₀ acc
pruneᴼᵉ-mem acc (p₀ ∷ l) (here refl) | just m₀ = pruneᴼᵉ-⊇ acc l m₀
pruneᴼᵉ-mem acc (p₀ ∷ l) (there m)   | just m₀ = pruneᴼᵉ-mem acc l m
pruneᴼᵉ-mem acc (p₀ ∷ l) (here refl) | nothing =
  pruneᴼᵉ-⊇ (p₀ ∷ acc) l (here refl)
pruneᴼᵉ-mem acc (p₀ ∷ l) (there m)   | nothing = pruneᴼᵉ-mem (p₀ ∷ acc) l m

prune : ∀ {Θ} → Hyps Θ → Hyps Θ
prune Q = hyps (pruneᴱ (pruneᵛ [] (subᵥ Q)) [] (ets Q)) (pruneᵛ [] (subᵥ Q))
               (pruneᴼʳ [] (ordᵣ Q)) (pruneᴼᵉ [] (ordₑ Q)) (disj Q)

prune-⊨ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ prune Q
prune-⊨ Q h =
  mk⊨ᴴ (λ m → [ (λ ()) , etOK h ]′ (pruneᴱ-⊆ (pruneᵛ [] (subᵥ Q)) [] (ets Q) m))
       (λ m → [ (λ ()) , subOK h ]′ (pruneᵛ-⊆ [] (subᵥ Q) m))
       (λ m → [ (λ ()) , ordROK h ]′ (pruneᴼʳ-⊆ [] (ordᵣ Q) m))
       (λ m → [ (λ ()) , ordEOK h ]′ (pruneᴼᵉ-⊆ [] (ordₑ Q) m))
       (disjOK h)

prune-⊨⁻ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ prune Q → θ ⊨ᴴ Q
prune-⊨⁻ Q h =
  mk⊨ᴴ (λ m → ground-Et h
                (Etᴾ-⊩ (λ q → q) (λ q → q)
                       (pruneᴱ-et (pruneᵛ [] (subᵥ Q)) [] (ets Q) m)))
       (λ m → ground-⊩ᵗᵛ h (⊢ᵖ-⊩ (λ q → q) (pruneᵛ-path [] (subᵥ Q) m)))
       (λ m → ordROK h (pruneᴼʳ-mem [] (ordᵣ Q) m))
       (λ m → ordEOK h (pruneᴼᵉ-mem [] (ordₑ Q) m))
       (disjOK h)

simplify : ∀ {Θ} → Hyps Θ → Hyps Θ
simplify Q = prune (narrowAll (disj Q) (hyps (ets Q) (subᵥ Q) (ordᵣ Q) (ordₑ Q) []))

-- Simplification changes nothing a grounding can see

simplify-⊨ : ∀ {Θ} → (Q : Hyps Θ) → (θ : Grounding Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ simplify Q
simplify-⊨ Q θ h =
  prune-⊨ (narrowAll (disj Q) (hyps (ets Q) (subᵥ Q) (ordᵣ Q) (ordₑ Q) []))
    (narrowAll-⊨ (disj Q) (hyps (ets Q) (subᵥ Q) (ordᵣ Q) (ordₑ Q) []) (disjOK h)
                 (mk⊨ᴴ (etOK h) (subOK h) (ordROK h) (ordEOK h) (λ ())))

simplify-⊨⁻ : ∀ {Θ} → (Q : Hyps Θ) → (θ : Grounding Θ) → θ ⊨ᴴ simplify Q → θ ⊨ᴴ Q
simplify-⊨⁻ Q θ h
  with narrowAll-⊨⁻ (disj Q) (hyps (ets Q) (subᵥ Q) (ordᵣ Q) (ordₑ Q) [])
         (prune-⊨⁻ (narrowAll (disj Q) (hyps (ets Q) (subᵥ Q) (ordᵣ Q) (ordₑ Q) [])) h)
... | h₀ , k = mk⊨ᴴ (etOK h₀) (subOK h₀) (ordROK h₀) (ordEOK h₀) k

simplify-≃ : ∀ {Θ} → (Q : Hyps Θ) → (θ : Grounding Θ)
           → (θ ⊨ᴴ Q → θ ⊨ᴴ simplify Q) × (θ ⊨ᴴ simplify Q → θ ⊨ᴴ Q)
simplify-≃ Q θ = simplify-⊨ Q θ , simplify-⊨⁻ Q θ
