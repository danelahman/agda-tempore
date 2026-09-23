------------------------------------------------------------------
-- Closed grade orderings                                         --
--                                                                --
-- A grade expression with no unknowns has a value. An ordering   --
-- between two such is decided by the grade's own `_≾?_`:         --
-- `closedᴴ` drops each one that holds and fails on one that does --
-- not. A var-rule disjunction whose grade has a value is decided --
-- the same way against the unit: it is dropped when that holds,  --
-- and fails when it does not and the type is refuted eternal     --
-- (`etDec`). What is left entails what was there; a failure      --
-- leaves an atom that no grounding of any instance satisfies.    --
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Closed (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (Eternal; Baseₑ; _|×|ₑ_; eternalBaseType?)

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Grounding S using (Grounding; _⊨ᴴ_; ⟦_⟧ʳ; ⟦_⟧ᵉ; ⟦_⟧ᵛ;
                                                       ground-≡̂ᵣ; ground-≡̂ₑ;
                                                       ground-≾ᵣ; ground-≾ₑ; ground-VarOK)

open import TypeInference.SolverImpl.Resid S using (etDec)

------------------------------------------------------------------------
-- The value of an expression with no unknowns

valᵉ? : ∀ {Θ} → EExp Θ → Maybe E
valᵉ? (evar i)   = nothing
valᵉ? (econst c) = just c
valᵉ? (ε ·̂ₑ ε') with valᵉ? ε | valᵉ? ε'
... | just c | just c' = just (c ·ₑ c')
... | _      | _       = nothing
valᵉ? (ε ⊔̂ₑ ε') with valᵉ? ε | valᵉ? ε'
... | just c | just c' = just (c ⊔ₑ c')
... | _      | _       = nothing

valʳ? : ∀ {Θ} → RExp Θ → Maybe R
valʳ? (rvar i)   = nothing
valʳ? (rconst c) = just c
valʳ? (ρ ·̂ᵣ ρ') with valʳ? ρ | valʳ? ρ'
... | just c | just c' = just (c ·ᵣ c')
... | _      | _       = nothing
valʳ? (ρ ⊔̂ᵣ ρ') with valʳ? ρ | valʳ? ρ'
... | just c | just c' = just (c ⊔ᵣ c')
... | _      | _       = nothing
valʳ? ∣ ε ∣̂ᵉ with valᵉ? ε
... | just c  = just (mapᵉ c)
... | nothing = nothing

-- An expression with a value is convertible to it

convᵉ : ∀ {Θ} {c : E} → (ε : EExp Θ) → valᵉ? ε ≡ just c → ε ≡̂ₑ econst c
convᵉ (evar i) ()
convᵉ (econst c) refl = ≡̂ₑ-refl
convᵉ (ε ·̂ₑ ε') q with valᵉ? ε in e₁ | valᵉ? ε' in e₂
convᵉ (ε ·̂ₑ ε') refl | just c | just c' =
  ≡̂ₑ-trans (≡̂ₑ-cong (convᵉ ε e₁) (convᵉ ε' e₂)) ≡̂ₑ-const-·
convᵉ (ε ·̂ₑ ε') () | just _  | nothing
convᵉ (ε ·̂ₑ ε') () | nothing | _
convᵉ (ε ⊔̂ₑ ε') q with valᵉ? ε in e₁ | valᵉ? ε' in e₂
convᵉ (ε ⊔̂ₑ ε') refl | just c | just c' =
  ≡̂ₑ-trans (≡̂ₑ-cong-⊔ (convᵉ ε e₁) (convᵉ ε' e₂)) ≡̂ₑ-const-⊔
convᵉ (ε ⊔̂ₑ ε') () | just _  | nothing
convᵉ (ε ⊔̂ₑ ε') () | nothing | _

convʳ : ∀ {Θ} {c : R} → (ρ : RExp Θ) → valʳ? ρ ≡ just c → ρ ≡̂ᵣ rconst c
convʳ (rvar i) ()
convʳ (rconst c) refl = ≡̂ᵣ-refl
convʳ (ρ ·̂ᵣ ρ') q with valʳ? ρ in e₁ | valʳ? ρ' in e₂
convʳ (ρ ·̂ᵣ ρ') refl | just c | just c' =
  ≡̂ᵣ-trans (≡̂ᵣ-cong (convʳ ρ e₁) (convʳ ρ' e₂)) ≡̂ᵣ-const-·
convʳ (ρ ·̂ᵣ ρ') () | just _  | nothing
convʳ (ρ ·̂ᵣ ρ') () | nothing | _
convʳ (ρ ⊔̂ᵣ ρ') q with valʳ? ρ in e₁ | valʳ? ρ' in e₂
convʳ (ρ ⊔̂ᵣ ρ') refl | just c | just c' =
  ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (convʳ ρ e₁) (convʳ ρ' e₂)) ≡̂ᵣ-const-⊔
convʳ (ρ ⊔̂ᵣ ρ') () | just _  | nothing
convʳ (ρ ⊔̂ᵣ ρ') () | nothing | _
convʳ ∣ ε ∣̂ᵉ q with valᵉ? ε in e
convʳ ∣ ε ∣̂ᵉ refl | just c = ≡̂ᵣ-trans (≡̂ᵣ-map-cong (convᵉ ε e)) ≡̂ᵣ-map-const
convʳ ∣ ε ∣̂ᵉ ()   | nothing

-- and so is every instance of it

convᵉ-inst : ∀ {Θ Θ'} {c : E} → (ε : EExp Θ) → valᵉ? ε ≡ just c
           → (δ : Subst Θ Θ') → ε [ δ ]ᵉ ≡̂ₑ econst c
convᵉ-inst ε q δ = ≡̂ₑ-subst δ (convᵉ ε q)

convʳ-inst : ∀ {Θ Θ'} {c : R} → (ρ : RExp Θ) → valʳ? ρ ≡ just c
           → (δ : Subst Θ Θ') → ρ [ δ ]ʳ ≡̂ᵣ rconst c
convʳ-inst ρ q δ = ≡̂ᵣ-subst δ (convʳ ρ q)

------------------------------------------------------------------------
-- Deciding the closed orderings of a list

-- A closed ordering that fails

Falseʳ : ∀ {Θ} → List (RExp Θ × RExp Θ) → Set
Falseʳ {Θ} l = Σ[ ρ ∈ RExp Θ ] Σ[ ρ' ∈ RExp Θ ] Σ[ c ∈ R ] Σ[ c' ∈ R ]
                 ((ρ , ρ') ∈ l × valʳ? ρ ≡ just c × valʳ? ρ' ≡ just c' × ¬ (c ≾ᵣ c'))

Falseᵉ : ∀ {Θ} → List (EExp Θ × EExp Θ) → Set
Falseᵉ {Θ} l = Σ[ ε ∈ EExp Θ ] Σ[ ε' ∈ EExp Θ ] Σ[ c ∈ E ] Σ[ c' ∈ E ]
                 ((ε , ε') ∈ l × valᵉ? ε ≡ just c × valᵉ? ε' ≡ just c' × ¬ (c ≾ₑ c'))

-- The orderings left once the closed ones that hold are dropped

record Keptʳ {Θ : Scope} (l : List (RExp Θ × RExp Θ)) : Set where
  constructor keptʳ
  field
    lʳ   : List (RExp Θ × RExp Θ)
    subʳ : ∀ {p} → p ∈ lʳ → p ∈ l
    entʳ : ∀ {Θ'} {Q : Hyps Θ'} → (δ : Subst Θ Θ')
         → (∀ {ρ ρ'} → (ρ , ρ') ∈ lʳ → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ)
         → ∀ {ρ ρ'} → (ρ , ρ') ∈ l → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ

record Keptᵉ {Θ : Scope} (l : List (EExp Θ × EExp Θ)) : Set where
  constructor keptᵉ
  field
    lᵉ   : List (EExp Θ × EExp Θ)
    subᵉ : ∀ {p} → p ∈ lᵉ → p ∈ l
    entᵉ : ∀ {Θ'} {Q : Hyps Θ'} → (δ : Subst Θ Θ')
         → (∀ {ε ε'} → (ε , ε') ∈ lᵉ → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ)
         → ∀ {ε ε'} → (ε , ε') ∈ l → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ

open Keptʳ
open Keptᵉ

consʳ : ∀ {Θ} {l : List (RExp Θ × RExp Θ)} {ρ ρ'} → Keptʳ l → Keptʳ ((ρ , ρ') ∷ l)
consʳ {ρ = ρ} {ρ'} k =
  keptʳ ((ρ , ρ') ∷ lʳ k)
        (λ { (here refl) → here refl ; (there m) → there (subʳ k m) })
        (λ δ f → λ { (here refl) → f (here refl)
                   ; (there m)   → entʳ k δ (λ m' → f (there m')) m })

consᵉ : ∀ {Θ} {l : List (EExp Θ × EExp Θ)} {ε ε'} → Keptᵉ l → Keptᵉ ((ε , ε') ∷ l)
consᵉ {ε = ε} {ε'} k =
  keptᵉ ((ε , ε') ∷ lᵉ k)
        (λ { (here refl) → here refl ; (there m) → there (subᵉ k m) })
        (λ δ f → λ { (here refl) → f (here refl)
                   ; (there m)   → entᵉ k δ (λ m' → f (there m')) m })

dropʳ : ∀ {Θ} {l : List (RExp Θ × RExp Θ)} {ρ ρ' c c'}
      → valʳ? ρ ≡ just c → valʳ? ρ' ≡ just c' → c ≾ᵣ c'
      → Keptʳ l → Keptʳ ((ρ , ρ') ∷ l)
dropʳ {ρ = ρ} {ρ'} q q' p k =
  keptʳ (lʳ k) (λ m → there (subʳ k m))
        (λ δ f → λ { (here refl) → transᵣ (eqᵣ (convʳ-inst ρ q δ))
                                           (transᵣ (atomᵣ p) (eqᵣ (≡̂ᵣ-sym (convʳ-inst ρ' q' δ))))
                   ; (there m)   → entʳ k δ f m })

dropᵉ : ∀ {Θ} {l : List (EExp Θ × EExp Θ)} {ε ε' c c'}
      → valᵉ? ε ≡ just c → valᵉ? ε' ≡ just c' → c ≾ₑ c'
      → Keptᵉ l → Keptᵉ ((ε , ε') ∷ l)
dropᵉ {ε = ε} {ε'} q q' p k =
  keptᵉ (lᵉ k) (λ m → there (subᵉ k m))
        (λ δ f → λ { (here refl) → transₑ (eqₑ (convᵉ-inst ε q δ))
                                           (transₑ (atomₑ p) (eqₑ (≡̂ₑ-sym (convᵉ-inst ε' q' δ))))
                   ; (there m)   → entᵉ k δ f m })

thereʳ : ∀ {Θ} {l : List (RExp Θ × RExp Θ)} {p} → Falseʳ l → Falseʳ (p ∷ l)
thereʳ (ρ , ρ' , c , c' , m , q , q' , n) = ρ , ρ' , c , c' , there m , q , q' , n

thereᵉ : ∀ {Θ} {l : List (EExp Θ × EExp Θ)} {p} → Falseᵉ l → Falseᵉ (p ∷ l)
thereᵉ (ε , ε' , c , c' , m , q , q' , n) = ε , ε' , c , c' , there m , q , q' , n

closedʳ : ∀ {Θ} → (l : List (RExp Θ × RExp Θ)) → Falseʳ l ⊎ Keptʳ l
closedʳ [] = inj₂ (keptʳ [] (λ ()) (λ δ k → λ ()))
closedʳ ((ρ , ρ') ∷ l) with closedʳ l
... | inj₁ f = inj₁ (thereʳ f)
... | inj₂ k with valʳ? ρ in q | valʳ? ρ' in q'
...   | just c  | just c' with c ≾ᵣ? c'
...     | yes p = inj₂ (dropʳ q q' p k)
...     | no n  = inj₁ (ρ , ρ' , c , c' , here refl , q , q' , n)
closedʳ ((ρ , ρ') ∷ l) | inj₂ k | just _  | nothing = inj₂ (consʳ k)
closedʳ ((ρ , ρ') ∷ l) | inj₂ k | nothing | _       = inj₂ (consʳ k)

closedᵉ : ∀ {Θ} → (l : List (EExp Θ × EExp Θ)) → Falseᵉ l ⊎ Keptᵉ l
closedᵉ [] = inj₂ (keptᵉ [] (λ ()) (λ δ k → λ ()))
closedᵉ ((ε , ε') ∷ l) with closedᵉ l
... | inj₁ f = inj₁ (thereᵉ f)
... | inj₂ k with valᵉ? ε in q | valᵉ? ε' in q'
...   | just c  | just c' with c ≾ₑ? c'
...     | yes p = inj₂ (dropᵉ q q' p k)
...     | no n  = inj₁ (ε , ε' , c , c' , here refl , q , q' , n)
closedᵉ ((ε , ε') ∷ l) | inj₂ k | just _  | nothing = inj₂ (consᵉ k)
closedᵉ ((ε , ε') ∷ l) | inj₂ k | nothing | _       = inj₂ (consᵉ k)

------------------------------------------------------------------------
-- Var-rule disjunctions

-- A type `etDec` refutes is eternal at no grounding of any instance

etDec-ground : ∀ {Θ Θ'} → (A : OVType Θ) → etDec A ≡ nothing
             → (δ : Subst Θ Θ') → (θ : Grounding Θ') → ¬ Eternal (⟦ A [ δ ]ᵛ ⟧ᵛ θ)
etDec-ground (tvar α) () δ θ
etDec-ground (Base b) q δ θ with eternalBaseType? b
etDec-ground (Base b) () δ θ | yes p
etDec-ground (Base b) q  δ θ | no ¬p = λ { (Baseₑ p') → ⊥-elim-irr (¬p p') }
etDec-ground Unit      () δ θ
etDec-ground Bool      () δ θ
etDec-ground Empty     () δ θ
etDec-ground (A |×| B) q δ θ with etDec A in e₁ | etDec B in e₂
etDec-ground (A |×| B) () δ θ | just _  | just _
etDec-ground (A |×| B) q  δ θ | just _  | nothing =
  λ { (p |×|ₑ p') → etDec-ground B e₂ δ θ p' }
etDec-ground (A |×| B) q  δ θ | nothing | _       =
  λ { (p |×|ₑ p') → etDec-ground A e₁ δ θ p }
etDec-ground (A ⇒ C)   q δ θ = λ ()
etDec-ground ([ ρ ] A) q δ θ = λ ()

-- A disjunction whose grade has a value above the unit, at a type
-- refuted eternal

Falseᵈ : ∀ {Θ} → List (OVType Θ × RExp Θ) → Set
Falseᵈ {Θ} l = Σ[ A ∈ OVType Θ ] Σ[ ρ ∈ RExp Θ ] Σ[ c ∈ R ]
                 ((A , ρ) ∈ l × etDec A ≡ nothing × valʳ? ρ ≡ just c × ¬ (c ≾ᵣ uᵣ))

record Keptᵈ {Θ : Scope} (l : List (OVType Θ × RExp Θ)) : Set where
  constructor keptᵈ
  field
    lᵈ   : List (OVType Θ × RExp Θ)
    subᵈ : ∀ {p} → p ∈ lᵈ → p ∈ l
    entᵈ : ∀ {Θ'} {Q : Hyps Θ'} → (δ : Subst Θ Θ')
         → (∀ {A ρ} → (A , ρ) ∈ lᵈ → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ))
         → ∀ {A ρ} → (A , ρ) ∈ l → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ)

open Keptᵈ

consᵈ : ∀ {Θ} {l : List (OVType Θ × RExp Θ)} {A ρ} → Keptᵈ l → Keptᵈ ((A , ρ) ∷ l)
consᵈ {A = A} {ρ} k =
  keptᵈ ((A , ρ) ∷ lᵈ k)
        (λ { (here refl) → here refl ; (there m) → there (subᵈ k m) })
        (λ δ f → λ { (here refl) → f (here refl)
                   ; (there m)   → entᵈ k δ (λ m' → f (there m')) m })

dropᵈ : ∀ {Θ} {l : List (OVType Θ × RExp Θ)} {A ρ c}
      → valʳ? ρ ≡ just c → c ≾ᵣ uᵣ → Keptᵈ l → Keptᵈ ((A , ρ) ∷ l)
dropᵈ {ρ = ρ} q p k =
  keptᵈ (lᵈ k) (λ m → there (subᵈ k m))
        (λ δ f → λ { (here refl) → ≾ᵘ-ok (transᵣ (eqᵣ (convʳ-inst ρ q δ)) (atomᵣ p))
                   ; (there m)   → entᵈ k δ f m })

thereᵈ : ∀ {Θ} {l : List (OVType Θ × RExp Θ)} {p} → Falseᵈ l → Falseᵈ (p ∷ l)
thereᵈ (A , ρ , c , m , e , q , n) = A , ρ , c , there m , e , q , n

closedᵈ : ∀ {Θ} → (l : List (OVType Θ × RExp Θ)) → Falseᵈ l ⊎ Keptᵈ l
closedᵈ [] = inj₂ (keptᵈ [] (λ ()) (λ δ k → λ ()))
closedᵈ ((A , ρ) ∷ l) with closedᵈ l
... | inj₁ f = inj₁ (thereᵈ f)
... | inj₂ k with valʳ? ρ in q
...   | nothing = inj₂ (consᵈ k)
...   | just c with c ≾ᵣ? uᵣ
...     | yes p = inj₂ (dropᵈ q p k)
...     | no n with etDec A in e
...       | nothing = inj₁ (A , ρ , c , here refl , e , q , n)
...       | just _  = inj₂ (consᵈ k)

falseᵈ : ∀ {Θ Θ'} {l : List (OVType Θ × RExp Θ)} → Falseᵈ l
       → (δ : Subst Θ Θ') → {Q : Hyps Θ'} → (θ : Grounding Θ') → θ ⊨ᴴ Q
       → (∀ {A ρ} → (A , ρ) ∈ l → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ)) → ⊥
falseᵈ (A , ρ , c , m , e , q , n) δ θ h k with ground-VarOK h (k m)
... | inj₁ et = etDec-ground A e δ θ et
... | inj₂ le = n (subst (_≾ᵣ uᵣ) (ground-≡̂ᵣ {θ = θ} (convʳ-inst ρ q δ)) le)

------------------------------------------------------------------------
-- A failing closed ordering is entailed under no satisfiable set

falseʳ : ∀ {Θ Θ'} {l : List (RExp Θ × RExp Θ)} → Falseʳ l
       → (δ : Subst Θ Θ') → {Q : Hyps Θ'} → (θ : Grounding Θ') → θ ⊨ᴴ Q
       → (∀ {ρ ρ'} → (ρ , ρ') ∈ l → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ) → ⊥
falseʳ (ρ , ρ' , c , c' , m , q , q' , n) δ θ h k =
  n (subst₂ _≾ᵣ_ (ground-≡̂ᵣ {θ = θ} (convʳ-inst ρ q δ))
                 (ground-≡̂ᵣ {θ = θ} (convʳ-inst ρ' q' δ))
                 (ground-≾ᵣ h (k m)))

falseᵉ : ∀ {Θ Θ'} {l : List (EExp Θ × EExp Θ)} → Falseᵉ l
       → (δ : Subst Θ Θ') → {Q : Hyps Θ'} → (θ : Grounding Θ') → θ ⊨ᴴ Q
       → (∀ {ε ε'} → (ε , ε') ∈ l → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ) → ⊥
falseᵉ (ε , ε' , c , c' , m , q , q' , n) δ θ h k =
  n (subst₂ _≾ₑ_ (ground-≡̂ₑ {θ = θ} (convᵉ-inst ε q δ))
                 (ground-≡̂ₑ {θ = θ} (convᵉ-inst ε' q' δ))
                 (ground-≾ₑ h (k m)))

------------------------------------------------------------------------
-- The closed orderings of a hypothesis set decided

closedᴴ : ∀ {Θ} → Hyps Θ → Maybe (Hyps Θ)
closedᴴ Q with closedʳ (ordᵣ Q) | closedᵉ (ordₑ Q) | closedᵈ (disj Q)
... | inj₂ kʳ | inj₂ kᵉ | inj₂ kᵈ =
      just (hyps (ets Q) (subᵥ Q) (lʳ kʳ) (lᵉ kᵉ) (lᵈ kᵈ))
... | _       | _       | _       = nothing

-- What is left entails the set

closedᴴ-⊩ : ∀ {Θ} → (Q : Hyps Θ) → {Q₁ : Hyps Θ} → closedᴴ Q ≡ just Q₁ → Q₁ ⊩ᴴ Q [ idˢ ]
closedᴴ-⊩ Q eq with closedʳ (ordᵣ Q) | closedᵉ (ordₑ Q) | closedᵈ (disj Q)
closedᴴ-⊩ Q refl | inj₂ kʳ | inj₂ kᵉ | inj₂ kᵈ =
  mk⊩ᴴ (⊩ets r) (⊩subᵥ r) (entʳ kʳ idˢ (⊩ordᵣ r)) (entᵉ kᵉ idˢ (⊩ordₑ r))
       (entᵈ kᵈ idˢ (⊩disj r))
  where r = ⊩ᴴ-refl {Q = hyps (ets Q) (subᵥ Q) (lʳ kʳ) (lᵉ kᵉ) (lᵈ kᵈ)}
closedᴴ-⊩ Q () | inj₁ _ | _      | _
closedᴴ-⊩ Q () | inj₂ _ | inj₁ _ | _
closedᴴ-⊩ Q () | inj₂ _ | inj₂ _ | inj₁ _

-- and is entailed wherever the set is

closedᴴ-⊆ : ∀ {Θ Θ'} → (Q : Hyps Θ) → {Q₁ : Hyps Θ} → closedᴴ Q ≡ just Q₁
          → {Q' : Hyps Θ'} {δ : Subst Θ Θ'} → Q' ⊩ᴴ Q [ δ ] → Q' ⊩ᴴ Q₁ [ δ ]
closedᴴ-⊆ Q eq h with closedʳ (ordᵣ Q) | closedᵉ (ordₑ Q) | closedᵈ (disj Q)
closedᴴ-⊆ Q refl h | inj₂ kʳ | inj₂ kᵉ | inj₂ kᵈ =
  mk⊩ᴴ (⊩ets h) (⊩subᵥ h) (λ m → ⊩ordᵣ h (subʳ kʳ m)) (λ m → ⊩ordₑ h (subᵉ kᵉ m))
       (λ m → ⊩disj h (subᵈ kᵈ m))
closedᴴ-⊆ Q () h | inj₁ _ | _      | _
closedᴴ-⊆ Q () h | inj₂ _ | inj₁ _ | _
closedᴴ-⊆ Q () h | inj₂ _ | inj₂ _ | inj₁ _

-- A failure is entailed under no satisfiable set

closedᴴ-fail : ∀ {Θ Θ'} → (Q : Hyps Θ) → closedᴴ Q ≡ nothing
             → (δ : Subst Θ Θ') → {Q' : Hyps Θ'} → Q' ⊩ᴴ Q [ δ ]
             → (θ : Grounding Θ') → θ ⊨ᴴ Q' → ⊥
closedᴴ-fail Q eq δ h θ s with closedʳ (ordᵣ Q) | closedᵉ (ordₑ Q) | closedᵈ (disj Q)
... | inj₁ f | _      | _      = falseʳ f δ θ s (⊩ordᵣ h)
... | inj₂ _ | inj₁ f | _      = falseᵉ f δ θ s (⊩ordₑ h)
... | inj₂ _ | inj₂ _ | inj₁ f = falseᵈ f δ θ s (⊩disj h)
closedᴴ-fail Q () δ h θ s | inj₂ _ | inj₂ _ | inj₂ _
