------------------------------------------------------------------
-- Normalising, settling and pruning a reported hypothesis set   --
--                                                                --
-- `simplify` first replaces every grade expression of the set by --
-- its canonical form. It then settles every `disj` entry one of  --
-- whose sides is settled: a met eternality demand or an entailed --
-- grade ordering drops the entry, a refuted eternality demand    --
-- leaves the grade ordering behind, in skeleton order, and a     --
-- refuted grade leaves the eternality atoms behind. It then      --
-- prunes: a subtyping or eternality atom entailed by the atoms   --
-- kept before it is dropped, entailment there being reachability --
-- in a finite digraph, and a grade ordering is dropped when it   --
-- repeats one kept before it. It finally lists the grade         --
-- orderings by the skeletons of their two sides.                 --
--                                                                --
-- `trim` settles the disjunctions again, then drops every        --
-- subtyping atom and grade ordering entailed by those kept and   --
-- those not yet examined, the orderings by `decide≾`; an         --
-- ordering that holds outright is dropped too.                   --
--                                                                --
-- `simplify Q`, `trim Q` and `Q` are satisfied by exactly the    --
-- same groundings. This is a simplification of the report, not   --
-- of the solver, and `solve-principal` is untouched.             --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
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
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps as H

module TypeInference.SolverImpl.Simplify
  (S : LanguageSpec)
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
open import Syntax.Subtyping S using (_<:ᵛ_; <:ᶜ-refl)

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Grounding S

open import TypeInference.SolverImpl.Core.Rigid S using (zip₂-just)

open import TypeInference.SolverImpl.Canon  S umin?ᵣ umin?ₑ using (canonᴴ; canonᴴ-⊨; canonᴴ-⊨⁻)
open import TypeInference.SolverImpl.Eliminate S using (Elim; mkElim)
open import TypeInference.SolverImpl.Normal  S umin?ᵣ umin?ₑ using (decide≾ᵣ; decide≾ₑ)
open import TypeInference.SolverImpl.Product S using (_≺ᵣ_; _≺ₑ_)
open import TypeInference.SolverImpl.Resid  S using (etDec)
open import TypeInference.SolverImpl.Refute S umin?ᵣ umin?ₑ
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

-- Insertion into a list ordered by `_≺_`, after every entry below the
-- one inserted, and the sort built from it, which only permutes the
-- list

module _ {A : Set} (_≺_ : A → A → 𝔹) where

  insertᴼ : A → List A → List A
  insertᴼ p []      = p ∷ []
  insertᴼ p (q ∷ l) with q ≺ p
  ... | true  = q ∷ insertᴼ p l
  ... | false = p ∷ q ∷ l

  sortᴼ : List A → List A
  sortᴼ []      = []
  sortᴼ (p ∷ l) = insertᴼ p (sortᴼ l)

  insertᴼ-⊆ : ∀ p l {x} → x ∈ insertᴼ p l → x ∈ p ∷ l
  insertᴼ-⊆ p []      m = m
  insertᴼ-⊆ p (q ∷ l) m with q ≺ p
  insertᴼ-⊆ p (q ∷ l) (here refl) | true = there (here refl)
  insertᴼ-⊆ p (q ∷ l) (there m)   | true with insertᴼ-⊆ p l m
  ... | here refl = here refl
  ... | there m'  = there (there m')
  insertᴼ-⊆ p (q ∷ l) m           | false = m

  insertᴼ-⊇ : ∀ p l {x} → x ∈ p ∷ l → x ∈ insertᴼ p l
  insertᴼ-⊇ p []      m = m
  insertᴼ-⊇ p (q ∷ l) m with q ≺ p
  insertᴼ-⊇ p (q ∷ l) (here refl)         | true  = there (insertᴼ-⊇ p l (here refl))
  insertᴼ-⊇ p (q ∷ l) (there (here refl)) | true  = here refl
  insertᴼ-⊇ p (q ∷ l) (there (there m))   | true  = there (insertᴼ-⊇ p l (there m))
  insertᴼ-⊇ p (q ∷ l) m                   | false = m

  sortᴼ-⊆ : ∀ l {x} → x ∈ sortᴼ l → x ∈ l
  sortᴼ-⊆ (p ∷ l) m with insertᴼ-⊆ p (sortᴼ l) m
  ... | here refl = here refl
  ... | there m'  = there (sortᴼ-⊆ l m')

  sortᴼ-⊇ : ∀ l {x} → x ∈ l → x ∈ sortᴼ l
  sortᴼ-⊇ (p ∷ l) (here refl) = insertᴼ-⊇ p (sortᴼ l) (here refl)
  sortᴼ-⊇ (p ∷ l) (there m)   = insertᴼ-⊇ p (sortᴼ l) (there (sortᴼ-⊇ l m))

-- One disjunction, settled against the deciders and the set itself

settle : ∀ {Θ} → OVType Θ → RExp Θ → Hyps Θ → Hyps Θ
settle A ρ Q with decide≾ᵣ {Q = Q} ρ ûᵣ
... | just _  = Q
... | nothing with etDec A
...   | nothing = hyps (ets Q) (subᵥ Q) (insertᴼ _≺ᵣ_ (ρ , ûᵣ) (ordᵣ Q)) (ordₑ Q) (disj Q)
...   | just αs with ets? Q αs
...     | just _  = Q
...     | nothing with scanᵤ ρ
...       | just _  = hyps (αs ++ ets Q) (subᵥ Q) (ordᵣ Q) (ordₑ Q) (disj Q)
...       | nothing = hyps (ets Q) (subᵥ Q) (ordᵣ Q) (ordₑ Q) ((A , ρ) ∷ disj Q)

settle-⊨ : ∀ {Θ} {θ : Grounding Θ} → (A : OVType Θ) → (ρ : RExp Θ) → (Q : Hyps Θ)
         → Disj θ A ρ → θ ⊨ᴴ Q → θ ⊨ᴴ settle A ρ Q
settle-⊨ {θ = θ} A ρ Q d h with decide≾ᵣ {Q = Q} ρ ûᵣ
... | just _  = h
... | nothing with etDec A in e
...   | nothing = mk⊨ᴴ (etOK h) (subOK h) ordR (ordEOK h) (disjOK h)
      where
        ordR : ∀ {ρ₀ ρ₀'} → (ρ₀ , ρ₀') ∈ insertᴼ _≺ᵣ_ (ρ , ûᵣ) (ordᵣ Q)
             → ⟦ ρ₀ ⟧ʳ θ ≾ᵣ ⟦ ρ₀' ⟧ʳ θ
        ordR m with insertᴼ-⊆ _≺ᵣ_ (ρ , ûᵣ) (ordᵣ Q) m
        ... | here refl = [ (λ et → ⊥-elim (etDec-¬Et A e et)) , (λ le → le) ]′ d
        ... | there m'  = ordROK h m'
...   | just αs with ets? Q αs
...     | just _  = h
...     | nothing with scanᵤ ρ
...       | just ref = mk⊨ᴴ et' (subOK h) (ordROK h) (ordEOK h) (disjOK h)
      where
        etA : Eternal (⟦ A ⟧ᵛ θ)
        etA = [ (λ et → et) , (λ le → ⊥-elim (ref θ le)) ]′ d

        et' : ∀ {β} → β ∈ (αs ++ ets Q) → Eternal (gTy θ β)
        et' m = [ etDec-atoms A e etA , etOK h ]′ (∈-++⁻ αs m)
...       | nothing = mk⊨ᴴ (etOK h) (subOK h) (ordROK h) (ordEOK h) dsj'
      where
        dsj' : ∀ {A₀ ρ₀} → (A₀ , ρ₀) ∈ ((A , ρ) ∷ disj Q) → Disj θ A₀ ρ₀
        dsj' (here refl) = d
        dsj' (there m)   = disjOK h m

settle-⊨⁻ : ∀ {Θ} {θ : Grounding Θ} → (A : OVType Θ) → (ρ : RExp Θ) → (Q : Hyps Θ)
          → θ ⊨ᴴ settle A ρ Q → (θ ⊨ᴴ Q) × Disj θ A ρ
settle-⊨⁻ A ρ Q h with decide≾ᵣ {Q = Q} ρ ûᵣ
... | just d  = h , inj₂ (ground-≾ᵣ h d)
... | nothing with etDec A in e
...   | nothing =
        mk⊨ᴴ (etOK h) (subOK h) (λ m → ordROK h (insertᴼ-⊇ _≺ᵣ_ (ρ , ûᵣ) (ordᵣ Q) (there m)))
             (ordEOK h) (disjOK h)
        , inj₂ (ordROK h (insertᴼ-⊇ _≺ᵣ_ (ρ , ûᵣ) (ordᵣ Q) (here refl)))
...   | just αs with ets? Q αs
...     | just k  = h , inj₁ (etDec-Et A e (λ m → ground-Et h (k m)))
...     | nothing with scanᵤ ρ
...       | just _  = mk⊨ᴴ (λ m → etOK h (∈-++⁺ʳ αs m))
                           (subOK h) (ordROK h) (ordEOK h) (disjOK h)
                    , inj₁ (etDec-Et A e (λ m → etOK h (∈-++⁺ˡ m)))
...       | nothing = mk⊨ᴴ (etOK h) (subOK h) (ordROK h) (ordEOK h) (λ m → disjOK h (there m))
                    , disjOK h (here refl)

settleAll : ∀ {Θ} → List (OVType Θ × RExp Θ) → Hyps Θ → Hyps Θ
settleAll []             Q₀ = Q₀
settleAll ((A , ρ) ∷ l) Q₀ = settle A ρ (settleAll l Q₀)

settleAll-⊨ : ∀ {Θ} {θ : Grounding Θ} → (l : List (OVType Θ × RExp Θ))
            → (Q₀ : Hyps Θ) → (∀ {A ρ} → (A , ρ) ∈ l → Disj θ A ρ) → θ ⊨ᴴ Q₀
            → θ ⊨ᴴ settleAll l Q₀
settleAll-⊨ []             Q₀ k h = h
settleAll-⊨ ((A , ρ) ∷ l) Q₀ k h =
  settle-⊨ A ρ (settleAll l Q₀) (k (here refl))
           (settleAll-⊨ l Q₀ (λ m → k (there m)) h)

settleAll-⊨⁻ : ∀ {Θ} {θ : Grounding Θ} → (l : List (OVType Θ × RExp Θ))
             → (Q₀ : Hyps Θ) → θ ⊨ᴴ settleAll l Q₀
             → (θ ⊨ᴴ Q₀) × (∀ {A ρ} → (A , ρ) ∈ l → Disj θ A ρ)
settleAll-⊨⁻ []             Q₀ h = h , λ ()
settleAll-⊨⁻ ((A , ρ) ∷ l) Q₀ h with settle-⊨⁻ A ρ (settleAll l Q₀) h
... | h' , d with settleAll-⊨⁻ l Q₀ h'
...   | h'' , k = h'' , λ { (here refl) → d ; (there m) → k m }

-- The set with its disjunctions taken out, to be settled one at a time

split : ∀ {Θ} → Hyps Θ → Hyps Θ
split Q₀ = hyps (ets Q₀) (subᵥ Q₀) (ordᵣ Q₀) (ordₑ Q₀) []

-- Every disjunction of the set settled

settleᴴ : ∀ {Θ} → Hyps Θ → Hyps Θ
settleᴴ Q = settleAll (disj Q) (split Q)

settleᴴ-⊨ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ settleᴴ Q
settleᴴ-⊨ Q h =
  settleAll-⊨ (disj Q) (split Q) (disjOK h)
              (mk⊨ᴴ (etOK h) (subOK h) (ordROK h) (ordEOK h) (λ ()))

settleᴴ-⊨⁻ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ settleᴴ Q → θ ⊨ᴴ Q
settleᴴ-⊨⁻ Q h with settleAll-⊨⁻ (disj Q) (split Q) h
... | h₀ , k = mk⊨ᴴ (etOK h₀) (subOK h₀) (ordROK h₀) (ordEOK h₀) k

-- A subtyping or eternality atom entailed by the atoms kept before it
-- is dropped: entailment of such atoms is reachability in a finite
-- digraph.

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

-- The type atoms pruned, the rest untouched

pruneᵀ : ∀ {Θ} → Hyps Θ → Hyps Θ
pruneᵀ Q = hyps (pruneᴱ (pruneᵛ [] (subᵥ Q)) [] (ets Q)) (pruneᵛ [] (subᵥ Q))
                (ordᵣ Q) (ordₑ Q) (disj Q)

pruneᵀ-⊨ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ pruneᵀ Q
pruneᵀ-⊨ Q h =
  mk⊨ᴴ (λ m → [ (λ ()) , etOK h ]′ (pruneᴱ-⊆ (pruneᵛ [] (subᵥ Q)) [] (ets Q) m))
       (λ m → [ (λ ()) , subOK h ]′ (pruneᵛ-⊆ [] (subᵥ Q) m))
       (ordROK h) (ordEOK h) (disjOK h)

pruneᵀ-⊨⁻ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ pruneᵀ Q → θ ⊨ᴴ Q
pruneᵀ-⊨⁻ Q h =
  mk⊨ᴴ (λ m → ground-Et h
                (Etᴾ-⊩ (λ q → q) (λ q → q)
                       (pruneᴱ-et (pruneᵛ [] (subᵥ Q)) [] (ets Q) m)))
       (λ m → ground-⊩ᵗᵛ h (⊢ᵖ-⊩ (λ q → q) (pruneᵛ-path [] (subᵥ Q) m)))
       (ordROK h) (ordEOK h) (disjOK h)

-- A walk down a list dropping every entry a test settles, those kept
-- staying in place. The test sees the entries kept so far and those
-- not yet examined.

module Walk {A : Set} (Ok : List A → List A → A → Set)
            (test : (seen rest : List A) → (p : A) → Maybe (Ok seen rest p))
            where

  walk : List A → List A → List A
  walk seen []      = []
  walk seen (p ∷ l) with test seen l p
  ... | just _  = walk seen l
  ... | nothing = p ∷ walk (p ∷ seen) l

  walk-⊆ : (seen l : List A) → ∀ {p} → p ∈ walk seen l → p ∈ l
  walk-⊆ seen (p₀ ∷ l) m with test seen l p₀
  walk-⊆ seen (p₀ ∷ l) m           | just _  = there (walk-⊆ seen l m)
  walk-⊆ seen (p₀ ∷ l) (here refl) | nothing = here refl
  walk-⊆ seen (p₀ ∷ l) (there m)   | nothing = there (walk-⊆ (p₀ ∷ seen) l m)

  -- A property that a settled entry has whenever everything its test
  -- saw has it, and that holds of the entries seen and those kept,
  -- holds of every entry

  walk-⊨ : (P : A → Set)
         → (∀ seen rest {p} → Ok seen rest p → (∀ {q} → q ∈ seen ++ rest → P q) → P p)
         → (seen l : List A) → (∀ {q} → q ∈ seen → P q)
         → (∀ {q} → q ∈ walk seen l → P q)
         → ∀ {q} → q ∈ l → P q
  walk-⊨ P close seen (p₀ ∷ l) hs hk m with test seen l p₀
  walk-⊨ P close seen (p₀ ∷ l) hs hk (here refl) | just d  =
    close seen l d (λ q → [ hs , walk-⊨ P close seen l hs hk ]′ (∈-++⁻ seen q))
  walk-⊨ P close seen (p₀ ∷ l) hs hk (there m)   | just _  =
    walk-⊨ P close seen l hs hk m
  walk-⊨ P close seen (p₀ ∷ l) hs hk (here refl) | nothing = hk (here refl)
  walk-⊨ P close seen (p₀ ∷ l) hs hk (there m)   | nothing =
    walk-⊨ P close (p₀ ∷ seen) l
           (λ { (here refl) → hk (here refl) ; (there q) → hs q })
           (λ q → hk (there q)) m

-- A subtyping atom reachable from the atoms kept and those not yet
-- examined

Okᵛ : ∀ {n} → (seen rest : List (Fin n × Fin n)) → Fin n × Fin n → Set
Okᵛ seen rest p = seen ++ rest ⊢ᵖ proj₁ p ≾ proj₂ p

reachᵛ? : ∀ {n} → (seen rest : List (Fin n × Fin n)) → (p : Fin n × Fin n)
        → Maybe (Okᵛ seen rest p)
reachᵛ? seen rest (α , β) = reach? (seen ++ rest) α β

-- The subtyping atoms walked, the rest untouched

walkᵛ : ∀ {Θ} → Hyps Θ → Hyps Θ
walkᵛ Q = hyps (ets Q) (Walk.walk Okᵛ reachᵛ? [] (subᵥ Q)) (ordᵣ Q) (ordₑ Q) (disj Q)

walkᵛ-⊨ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ walkᵛ Q
walkᵛ-⊨ Q h =
  mk⊨ᴴ (etOK h) (λ m → subOK h (Walk.walk-⊆ Okᵛ reachᵛ? [] (subᵥ Q) m))
       (ordROK h) (ordEOK h) (disjOK h)

walkᵛ-⊨⁻ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ walkᵛ Q → θ ⊨ᴴ Q
walkᵛ-⊨⁻ {Θ} {θ} Q h =
  mk⊨ᴴ (etOK h)
       (Walk.walk-⊨ Okᵛ reachᵛ? (λ p → gTy θ (proj₁ p) <:ᵛ gTy θ (proj₂ p)) close
                    [] (subᵥ Q) (λ ()) (subOK h))
       (ordROK h) (ordEOK h) (disjOK h)
  where
    close : ∀ (seen rest : List (TyVar Θ × TyVar Θ)) {p} → Okᵛ seen rest p
          → (∀ {q} → q ∈ seen ++ rest → gTy θ (proj₁ q) <:ᵛ gTy θ (proj₂ q))
          → gTy θ (proj₁ p) <:ᵛ gTy θ (proj₂ p)
    close seen rest w hs =
      ground-⊩ᵗᵛ {θ = θ} {Q = hyps [] (seen ++ rest) [] [] []}
                 (mk⊨ᴴ (λ ()) hs (λ ()) (λ ()) (λ ())) (⊢ᵖ-⊩ (λ q → q) w)

-- Grade orderings are pruned by a walk against a test of entailment:
-- one the test proves is dropped. The effect orderings are pruned
-- first, and the resource ones read with the effect ones kept.

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

-- The set of the grade orderings `seen`, with the effect orderings `lₑ`

Hʳ : ∀ {Θ} → List (EExp Θ × EExp Θ) → List (RExp Θ × RExp Θ) → Hyps Θ
Hʳ lₑ seen = hyps [] [] seen lₑ []

Hᵉ : ∀ {Θ} → List (EExp Θ × EExp Θ) → Hyps Θ
Hᵉ seen = hyps [] [] [] seen []

-- An ordering entailed by the orderings the test sees

Okʳ : ∀ {Θ} → List (EExp Θ × EExp Θ) → (seen rest : List (RExp Θ × RExp Θ))
    → RExp Θ × RExp Θ → Set
Okʳ lₑ seen rest p = Hʳ lₑ (seen ++ rest) ⊩ proj₁ p ≾̂ᵣ proj₂ p

Okᵉ : ∀ {Θ} → (seen rest : List (EExp Θ × EExp Θ)) → EExp Θ × EExp Θ → Set
Okᵉ seen rest p = Hᵉ (seen ++ rest) ⊩ proj₁ p ≾̂ₑ proj₂ p

Testʳ : Set
Testʳ = ∀ {Θ} → (lₑ : List (EExp Θ × EExp Θ)) → (seen rest : List (RExp Θ × RExp Θ))
      → (p : RExp Θ × RExp Θ) → Maybe (Okʳ lₑ seen rest p)

Testᵉ : Set
Testᵉ = ∀ {Θ} → (seen rest : List (EExp Θ × EExp Θ))
      → (p : EExp Θ × EExp Θ) → Maybe (Okᵉ seen rest p)

-- A repeat of an ordering kept

repeatʳ? : Testʳ
repeatʳ? lₑ seen rest (ρ , ρ') with memʳ? (ρ , ρ') seen
... | just m  = just (hypᵣ (∈-++⁺ˡ m))
... | nothing = nothing

repeatᵉ? : Testᵉ
repeatᵉ? seen rest (ε , ε') with memᵉ? (ε , ε') seen
... | just m  = just (hypₑ (∈-++⁺ˡ m))
... | nothing = nothing

-- An ordering among those kept and those not yet examined, or one
-- `decide≾` proves from them

entailsʳ? : Testʳ
entailsʳ? lₑ seen rest (ρ , ρ') with memʳ? (ρ , ρ') (seen ++ rest)
... | just m  = just (hypᵣ m)
... | nothing = decide≾ᵣ ρ ρ'

entailsᵉ? : Testᵉ
entailsᵉ? seen rest (ε , ε') with memᵉ? (ε , ε') (seen ++ rest)
... | just m  = just (hypₑ m)
... | nothing = decide≾ₑ ε ε'

module Pruneᴼ (testʳ : Testʳ) (testᵉ : Testᵉ) where

  pruneᴼᵉ : ∀ {Θ} → List (EExp Θ × EExp Θ) → List (EExp Θ × EExp Θ)
  pruneᴼᵉ = Walk.walk Okᵉ testᵉ []

  pruneᴼʳ : ∀ {Θ} → List (EExp Θ × EExp Θ) → List (RExp Θ × RExp Θ)
          → List (RExp Θ × RExp Θ)
  pruneᴼʳ lₑ = Walk.walk (Okʳ lₑ) (testʳ lₑ) []

  -- The grade orderings pruned, the rest untouched

  pruneᴼ : ∀ {Θ} → Hyps Θ → Hyps Θ
  pruneᴼ Q = hyps (ets Q) (subᵥ Q) (pruneᴼʳ (pruneᴼᵉ (ordₑ Q)) (ordᵣ Q))
                  (pruneᴼᵉ (ordₑ Q)) (disj Q)

  pruneᴼ-⊨ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ pruneᴼ Q
  pruneᴼ-⊨ Q h =
    mk⊨ᴴ (etOK h) (subOK h)
         (λ m → ordROK h (Walk.walk-⊆ (Okʳ lₑ) (testʳ lₑ) [] (ordᵣ Q) m))
         (λ m → ordEOK h (Walk.walk-⊆ Okᵉ testᵉ [] (ordₑ Q) m))
         (disjOK h)
    where lₑ = pruneᴼᵉ (ordₑ Q)

  pruneᴼ-⊨⁻ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ pruneᴼ Q → θ ⊨ᴴ Q
  pruneᴼ-⊨⁻ {θ = θ} Q h =
    mk⊨ᴴ (etOK h) (subOK h)
         (Walk.walk-⊨ (Okʳ lₑ) (testʳ lₑ) (λ p → ⟦ proj₁ p ⟧ʳ θ ≾ᵣ ⟦ proj₂ p ⟧ʳ θ)
                      (λ _ _ d hs → ground-≾ᵣ (mk⊨ᴴ (λ ()) (λ ()) hs (ordEOK h) (λ ())) d)
                      [] (ordᵣ Q) (λ ()) (ordROK h))
         (Walk.walk-⊨ Okᵉ testᵉ (λ p → ⟦ proj₁ p ⟧ᵉ θ ≾ₑ ⟦ proj₂ p ⟧ᵉ θ)
                      (λ _ _ d hs → ground-≾ₑ (mk⊨ᴴ (λ ()) (λ ()) (λ ()) hs (λ ())) d)
                      [] (ordₑ Q) (λ ()) (ordEOK h))
         (disjOK h)
    where lₑ = pruneᴼᵉ (ordₑ Q)

module Repeats  = Pruneᴼ repeatʳ?  repeatᵉ?
module Entailed = Pruneᴼ entailsʳ? entailsᵉ?

prune : ∀ {Θ} → Hyps Θ → Hyps Θ
prune Q = Repeats.pruneᴼ (pruneᵀ Q)

prune-⊨ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ prune Q
prune-⊨ Q h = Repeats.pruneᴼ-⊨ (pruneᵀ Q) (pruneᵀ-⊨ Q h)

prune-⊨⁻ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ prune Q → θ ⊨ᴴ Q
prune-⊨⁻ Q h = pruneᵀ-⊨⁻ Q (Repeats.pruneᴼ-⊨⁻ (pruneᵀ Q) h)

order : ∀ {Θ} → Hyps Θ → Hyps Θ
order Q = hyps (ets Q) (subᵥ Q) (sortᴼ _≺ᵣ_ (ordᵣ Q)) (sortᴼ _≺ₑ_ (ordₑ Q)) (disj Q)

order-⊨ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ order Q
order-⊨ Q h =
  mk⊨ᴴ (etOK h) (subOK h)
       (λ m → ordROK h (sortᴼ-⊆ _≺ᵣ_ (ordᵣ Q) m))
       (λ m → ordEOK h (sortᴼ-⊆ _≺ₑ_ (ordₑ Q) m))
       (disjOK h)

order-⊨⁻ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ order Q → θ ⊨ᴴ Q
order-⊨⁻ Q h =
  mk⊨ᴴ (etOK h) (subOK h)
       (λ m → ordROK h (sortᴼ-⊇ _≺ᵣ_ (ordᵣ Q) m))
       (λ m → ordEOK h (sortᴼ-⊇ _≺ₑ_ (ordₑ Q) m))
       (disjOK h)

simplify : ∀ {Θ} → Hyps Θ → Hyps Θ
simplify Q = order (prune (settleᴴ (canonᴴ Q)))

-- Simplification changes nothing a grounding can see

simplify-⊨ : ∀ {Θ} → (Q : Hyps Θ) → (θ : Grounding Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ simplify Q
simplify-⊨ Q θ h =
  order-⊨ (prune (settleᴴ (canonᴴ Q)))
    (prune-⊨ (settleᴴ (canonᴴ Q)) (settleᴴ-⊨ (canonᴴ Q) (canonᴴ-⊨ Q h)))

simplify-⊨⁻ : ∀ {Θ} → (Q : Hyps Θ) → (θ : Grounding Θ) → θ ⊨ᴴ simplify Q → θ ⊨ᴴ Q
simplify-⊨⁻ Q θ h =
  canonᴴ-⊨⁻ Q (settleᴴ-⊨⁻ (canonᴴ Q)
    (prune-⊨⁻ (settleᴴ (canonᴴ Q)) (order-⊨⁻ (prune (settleᴴ (canonᴴ Q))) h)))

simplify-≃ : ∀ {Θ} → (Q : Hyps Θ) → (θ : Grounding Θ)
           → (θ ⊨ᴴ Q → θ ⊨ᴴ simplify Q) × (θ ⊨ᴴ simplify Q → θ ⊨ᴴ Q)
simplify-≃ Q θ = simplify-⊨ Q θ , simplify-⊨⁻ Q θ

-- The disjunctions settled, then every subtyping atom and grade
-- ordering entailed by those kept and those not yet examined dropped

trim : ∀ {Θ} → Hyps Θ → Hyps Θ
trim Q = Entailed.pruneᴼ (walkᵛ (settleᴴ Q))

trim-⊨ : ∀ {Θ} → (Q : Hyps Θ) → (θ : Grounding Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ trim Q
trim-⊨ Q θ h = Entailed.pruneᴼ-⊨ (walkᵛ (settleᴴ Q)) (walkᵛ-⊨ (settleᴴ Q) (settleᴴ-⊨ Q h))

trim-⊨⁻ : ∀ {Θ} → (Q : Hyps Θ) → (θ : Grounding Θ) → θ ⊨ᴴ trim Q → θ ⊨ᴴ Q
trim-⊨⁻ Q θ h =
  settleᴴ-⊨⁻ Q (walkᵛ-⊨⁻ (settleᴴ Q) (Entailed.pruneᴼ-⊨⁻ (walkᵛ (settleᴴ Q)) h))

trim-≃ : ∀ {Θ} → (Q : Hyps Θ) → (θ : Grounding Θ)
       → (θ ⊨ᴴ Q → θ ⊨ᴴ trim Q) × (θ ⊨ᴴ trim Q → θ ⊨ᴴ Q)
trim-≃ Q θ = trim-⊨ Q θ , trim-⊨⁻ Q θ

-- Trimming a whole report, as an elimination step that instantiates
-- no unknown

trimElim : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → Elim C Q
trimElim C Q =
  mkElim C (trim Q) (trim-⊨ Q) (λ θ h → θ , trim-⊨⁻ Q θ h , refl)
         (λ θ h → <:ᶜ-refl (⟦ C ⟧ᶜ θ))
