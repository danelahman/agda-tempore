------------------------------------------------------------------
-- Principal values for the unknowns local to a rigid scope     --
--                                                              --
-- An unknown is local to a scope when it is free in the image  --
-- of none of the unknowns the scope was entered with; the      --
-- rigid is one of those, so it is never local and never        --
-- assigned. Before the atoms of the scope are split, every     --
-- var-rule disjunction with a side decided true (the type      --
-- eternal, or the grade below the unit) is dropped, and each   --
-- local unknown with a principal value is sent to it:          --
--   * the join of its lower bounds, where it occurs on a right --
--     side only as the whole side (Pottier's condition);       --
--   * dually, its one upper bound, where it occurs on a left   --
--     side only as the whole side;                             --
--   * the unit, where it has no bound below and the unit is    --
--     least, the unit being then the join of no bounds.        --
-- In every case it occurs in no type of the residual. A value  --
-- may mention the rigid, so the value over the rigid is one    --
-- expression, uniform in it.                                   --
--                                                              --
-- Every grade former is monotone, so each step keeps every     --
-- instance that satisfied the residual (`lowerᵉ-⊩` and its     --
-- three siblings). A reflexive ordering holds at every         --
-- instance and bounds nothing.                                 --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _+_) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps as H

module TypeInference.SolverImpl.Localise
  (S : LanguageSpec)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.Constraints.Properties S using (≐ˢ-sym)

open import TypeInference.SolverImpl.Core.Occurs S
  using (occᵉ-e; occᵉ-r; occᵉ-v; occᵉ-c; occʳ-r; occʳ-v; occʳ-c)

open import TypeInference.SolverImpl.Resid     S
open import TypeInference.SolverImpl.State     S
  using (≐ˢ-refl; ≐ˢ-trans; ⨟-idˡ; ⨟-idʳ; ⨟-assoc; ⨟-congˡ)
open import TypeInference.SolverImpl.Eliminate S using (joinₑ; joinᵣ)
open import TypeInference.SolverImpl.Normal    S umin?ᵣ umin?ₑ using (decide≾ᵣ)

------------------------------------------------------------------------
-- Booleans and finite enumerations

∨-false : (b b' : 𝔹) → b ∨ b' ≡ false → (b ≡ false) × (b' ≡ false)
∨-false false b' q = refl , q
∨-false true  b' ()

isFalse : (b : 𝔹) → Maybe (b ≡ false)
isFalse false = just refl
isFalse true  = nothing

true≢false : true ≡ false → ⊥
true≢false ()

refl-true : ∀ {n} → (i : Fin n) → ⌊ i ≟ᶠ i ⌋ ≡ true
refl-true i with i ≟ᶠ i
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

anyᶠ : ∀ {n} → (Fin n → 𝔹) → 𝔹
anyᶠ {nzero}  f = false
anyᶠ {nsuc n} f = f zero ∨ anyᶠ (λ i → f (suc i))

anyᶠ-false : ∀ {n} → (f : Fin n → 𝔹) → anyᶠ f ≡ false → (i : Fin n) → f i ≡ false
anyᶠ-false {nsuc n} f q zero    = proj₁ (∨-false (f zero) _ q)
anyᶠ-false {nsuc n} f q (suc i) =
  anyᶠ-false (λ i' → f (suc i')) (proj₂ (∨-false (f zero) _ q)) i

anyᶠ-true : ∀ {n} → (f : Fin n → 𝔹) → anyᶠ f ≡ true → Σ[ i ∈ Fin n ] (f i ≡ true)
anyᶠ-true {nsuc n} f q with f zero in r
... | true  = zero , r
... | false with anyᶠ-true (λ i → f (suc i)) q
...   | i , r' = suc i , r'

-- The elements of `Fin n` at which a test fails, with the failure

misses : ∀ {n} → (f : Fin n → 𝔹) → List (Σ[ i ∈ Fin n ] (f i ≡ false))
misses {nzero}  f = []
misses {nsuc n} f = head (isFalse (f zero)) (shift (misses (λ i → f (suc i))))
  where
    head : Maybe (f zero ≡ false) → List (Σ[ i ∈ Fin (nsuc n) ] (f i ≡ false))
         → List (Σ[ i ∈ Fin (nsuc n) ] (f i ≡ false))
    head (just q) l = (zero , q) ∷ l
    head nothing  l = l

    shift : List (Σ[ i ∈ Fin n ] (f (suc i) ≡ false))
          → List (Σ[ i ∈ Fin (nsuc n) ] (f i ≡ false))
    shift []             = []
    shift ((i , q) ∷ l) = (suc i , q) ∷ shift l

anyL : ∀ {X : Set} → (X → 𝔹) → List X → 𝔹
anyL f []      = false
anyL f (x ∷ l) = f x ∨ anyL f l

------------------------------------------------------------------------
-- An assignment leaves alone what the assigned unknown does not occur in

updᵉ-hit : ∀ {Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → sE (updᵉ k b) k ≡ b
updᵉ-hit k b with k ≟ᶠ k
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

updᵉ-miss : ∀ {Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → (i : EVar Ψ)
          → ⌊ k ≟ᶠ i ⌋ ≡ false → sE (updᵉ k b) i ≡ evar i
updᵉ-miss k b i q with i ≟ᶠ k
... | no _     = refl
... | yes refl = ⊥-elim (true≢false (trans (sym (refl-true k)) q))

updʳ-hit : ∀ {Ψ} → (k : RVar Ψ) → (b : RExp Ψ) → sR (updʳ k b) k ≡ b
updʳ-hit k b with k ≟ᶠ k
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

updʳ-miss : ∀ {Ψ} → (k : RVar Ψ) → (b : RExp Ψ) → (i : RVar Ψ)
          → ⌊ k ≟ᶠ i ⌋ ≡ false → sR (updʳ k b) i ≡ rvar i
updʳ-miss k b i q with i ≟ᶠ k
... | no _     = refl
... | yes refl = ⊥-elim (true≢false (trans (sym (refl-true k)) q))

updᵉ-e : ∀ {Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → (ε : EExp Ψ)
       → occᵉ-e k ε ≡ false → ε [ updᵉ k b ]ᵉ ≡ ε
updᵉ-e k b (evar i)   q = updᵉ-miss k b i q
updᵉ-e k b (econst c) q = refl
updᵉ-e k b (ε ·̂ₑ ε')  q with ∨-false (occᵉ-e k ε) (occᵉ-e k ε') q
... | q₁ , q₂ = cong₂ _·̂ₑ_ (updᵉ-e k b ε q₁) (updᵉ-e k b ε' q₂)
updᵉ-e k b (ε ⊔̂ₑ ε')  q with ∨-false (occᵉ-e k ε) (occᵉ-e k ε') q
... | q₁ , q₂ = cong₂ _⊔̂ₑ_ (updᵉ-e k b ε q₁) (updᵉ-e k b ε' q₂)

updᵉ-r : ∀ {Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → (ρ : RExp Ψ)
       → occᵉ-r k ρ ≡ false → ρ [ updᵉ k b ]ʳ ≡ ρ
updᵉ-r k b (rvar i)   q = refl
updᵉ-r k b (rconst c) q = refl
updᵉ-r k b (ρ ·̂ᵣ ρ')  q with ∨-false (occᵉ-r k ρ) (occᵉ-r k ρ') q
... | q₁ , q₂ = cong₂ _·̂ᵣ_ (updᵉ-r k b ρ q₁) (updᵉ-r k b ρ' q₂)
updᵉ-r k b (ρ ⊔̂ᵣ ρ')  q with ∨-false (occᵉ-r k ρ) (occᵉ-r k ρ') q
... | q₁ , q₂ = cong₂ _⊔̂ᵣ_ (updᵉ-r k b ρ q₁) (updᵉ-r k b ρ' q₂)
updᵉ-r k b ∣ ε ∣̂ᵉ     q = cong ∣_∣̂ᵉ (updᵉ-e k b ε q)

mutual

  updᵉ-v : ∀ {Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → (A : OVType Ψ)
         → occᵉ-v k A ≡ false → A [ updᵉ k b ]ᵛ ≡ A
  updᵉ-v k b (tvar α)  q = refl
  updᵉ-v k b (Base c)  q = refl
  updᵉ-v k b Unit      q = refl
  updᵉ-v k b Bool      q = refl
  updᵉ-v k b Empty     q = refl
  updᵉ-v k b (A |×| B) q with ∨-false (occᵉ-v k A) (occᵉ-v k B) q
  ... | q₁ , q₂ = cong₂ _|×|_ (updᵉ-v k b A q₁) (updᵉ-v k b B q₂)
  updᵉ-v k b (A ⇒ C)   q with ∨-false (occᵉ-v k A) (occᵉ-c k C) q
  ... | q₁ , q₂ = cong₂ _⇒_ (updᵉ-v k b A q₁) (updᵉ-c k b C q₂)
  updᵉ-v k b ([ ρ ] A) q with ∨-false (occᵉ-r k ρ) (occᵉ-v k A) q
  ... | q₁ , q₂ = cong₂ [_]_ (updᵉ-r k b ρ q₁) (updᵉ-v k b A q₂)

  updᵉ-c : ∀ {Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → (C : OCType Ψ)
         → occᵉ-c k C ≡ false → C [ updᵉ k b ]ᶜ ≡ C
  updᵉ-c k b (A ‼ ε) q with ∨-false (occᵉ-v k A) (occᵉ-e k ε) q
  ... | q₁ , q₂ = cong₂ _‼_ (updᵉ-v k b A q₁) (updᵉ-e k b ε q₂)

updʳ-e : ∀ {Ψ} → (k : RVar Ψ) → (b : RExp Ψ) → (ε : EExp Ψ) → ε [ updʳ k b ]ᵉ ≡ ε
updʳ-e k b (evar i)   = refl
updʳ-e k b (econst c) = refl
updʳ-e k b (ε ·̂ₑ ε')  = cong₂ _·̂ₑ_ (updʳ-e k b ε) (updʳ-e k b ε')
updʳ-e k b (ε ⊔̂ₑ ε')  = cong₂ _⊔̂ₑ_ (updʳ-e k b ε) (updʳ-e k b ε')

updʳ-r : ∀ {Ψ} → (k : RVar Ψ) → (b : RExp Ψ) → (ρ : RExp Ψ)
       → occʳ-r k ρ ≡ false → ρ [ updʳ k b ]ʳ ≡ ρ
updʳ-r k b (rvar i)   q = updʳ-miss k b i q
updʳ-r k b (rconst c) q = refl
updʳ-r k b (ρ ·̂ᵣ ρ')  q with ∨-false (occʳ-r k ρ) (occʳ-r k ρ') q
... | q₁ , q₂ = cong₂ _·̂ᵣ_ (updʳ-r k b ρ q₁) (updʳ-r k b ρ' q₂)
updʳ-r k b (ρ ⊔̂ᵣ ρ')  q with ∨-false (occʳ-r k ρ) (occʳ-r k ρ') q
... | q₁ , q₂ = cong₂ _⊔̂ᵣ_ (updʳ-r k b ρ q₁) (updʳ-r k b ρ' q₂)
updʳ-r k b ∣ ε ∣̂ᵉ     q = cong ∣_∣̂ᵉ (updʳ-e k b ε)

mutual

  updʳ-v : ∀ {Ψ} → (k : RVar Ψ) → (b : RExp Ψ) → (A : OVType Ψ)
         → occʳ-v k A ≡ false → A [ updʳ k b ]ᵛ ≡ A
  updʳ-v k b (tvar α)  q = refl
  updʳ-v k b (Base c)  q = refl
  updʳ-v k b Unit      q = refl
  updʳ-v k b Bool      q = refl
  updʳ-v k b Empty     q = refl
  updʳ-v k b (A |×| B) q with ∨-false (occʳ-v k A) (occʳ-v k B) q
  ... | q₁ , q₂ = cong₂ _|×|_ (updʳ-v k b A q₁) (updʳ-v k b B q₂)
  updʳ-v k b (A ⇒ C)   q with ∨-false (occʳ-v k A) (occʳ-c k C) q
  ... | q₁ , q₂ = cong₂ _⇒_ (updʳ-v k b A q₁) (updʳ-c k b C q₂)
  updʳ-v k b ([ ρ ] A) q with ∨-false (occʳ-r k ρ) (occʳ-v k A) q
  ... | q₁ , q₂ = cong₂ [_]_ (updʳ-r k b ρ q₁) (updʳ-v k b A q₂)

  updʳ-c : ∀ {Ψ} → (k : RVar Ψ) → (b : RExp Ψ) → (C : OCType Ψ)
         → occʳ-c k C ≡ false → C [ updʳ k b ]ᶜ ≡ C
  updʳ-c k b (A ‼ ε) q = cong₂ _‼_ (updʳ-v k b A q) (updʳ-e k b ε)

-- ... and so does a later substitution

updᵉ-⨟e : ∀ {Ψ Ψ'} → (k : EVar Ψ) → (b : EExp Ψ) → (τ : Subst Ψ Ψ') → (ε : EExp Ψ)
        → occᵉ-e k ε ≡ false → ε [ updᵉ k b ⨟ˢ τ ]ᵉ ≡ ε [ τ ]ᵉ
updᵉ-⨟e k b τ ε q = trans (sym ([⨟]ᵉ ε (updᵉ k b) τ)) (cong (_[ τ ]ᵉ) (updᵉ-e k b ε q))

updᵉ-⨟r : ∀ {Ψ Ψ'} → (k : EVar Ψ) → (b : EExp Ψ) → (τ : Subst Ψ Ψ') → (ρ : RExp Ψ)
        → occᵉ-r k ρ ≡ false → ρ [ updᵉ k b ⨟ˢ τ ]ʳ ≡ ρ [ τ ]ʳ
updᵉ-⨟r k b τ ρ q = trans (sym ([⨟]ʳ ρ (updᵉ k b) τ)) (cong (_[ τ ]ʳ) (updᵉ-r k b ρ q))

updᵉ-⨟v : ∀ {Ψ Ψ'} → (k : EVar Ψ) → (b : EExp Ψ) → (τ : Subst Ψ Ψ') → (A : OVType Ψ)
        → occᵉ-v k A ≡ false → A [ updᵉ k b ⨟ˢ τ ]ᵛ ≡ A [ τ ]ᵛ
updᵉ-⨟v k b τ A q = trans (sym ([⨟]ᵛ A (updᵉ k b) τ)) (cong (_[ τ ]ᵛ) (updᵉ-v k b A q))

updʳ-⨟e : ∀ {Ψ Ψ'} → (k : RVar Ψ) → (b : RExp Ψ) → (τ : Subst Ψ Ψ') → (ε : EExp Ψ)
        → ε [ updʳ k b ⨟ˢ τ ]ᵉ ≡ ε [ τ ]ᵉ
updʳ-⨟e k b τ ε = trans (sym ([⨟]ᵉ ε (updʳ k b) τ)) (cong (_[ τ ]ᵉ) (updʳ-e k b ε))

updʳ-⨟r : ∀ {Ψ Ψ'} → (k : RVar Ψ) → (b : RExp Ψ) → (τ : Subst Ψ Ψ') → (ρ : RExp Ψ)
        → occʳ-r k ρ ≡ false → ρ [ updʳ k b ⨟ˢ τ ]ʳ ≡ ρ [ τ ]ʳ
updʳ-⨟r k b τ ρ q = trans (sym ([⨟]ʳ ρ (updʳ k b) τ)) (cong (_[ τ ]ʳ) (updʳ-r k b ρ q))

updʳ-⨟v : ∀ {Ψ Ψ'} → (k : RVar Ψ) → (b : RExp Ψ) → (τ : Subst Ψ Ψ') → (A : OVType Ψ)
        → occʳ-v k A ≡ false → A [ updʳ k b ⨟ˢ τ ]ᵛ ≡ A [ τ ]ᵛ
updʳ-⨟v k b τ A q = trans (sym ([⨟]ᵛ A (updʳ k b) τ)) (cong (_[ τ ]ᵛ) (updʳ-v k b A q))

-- An assignment below (above) the unknown's own value lowers (raises)
-- the substitution pointwise

updᵉ-below : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (k : EVar Ψ) → (b : EExp Ψ) → (τ : Subst Ψ Ψ')
           → Q ⊩ b [ τ ]ᵉ ≾̂ₑ sE τ k → Q ⊩ (updᵉ k b ⨟ˢ τ) ≾ˢ τ
updᵉ-below {Ψ} {Q = Q} k b τ p = mk≾ˢ (λ i → ⊩≾̂ᵣ-refl) e
  where
    e : (i : EVar Ψ) → Q ⊩ sE (updᵉ k b) i [ τ ]ᵉ ≾̂ₑ sE τ i
    e i with i ≟ᶠ k
    ... | yes refl = p
    ... | no _     = ⊩≾̂ₑ-refl

updᵉ-above : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (k : EVar Ψ) → (b : EExp Ψ) → (τ : Subst Ψ Ψ')
           → Q ⊩ sE τ k ≾̂ₑ b [ τ ]ᵉ → Q ⊩ τ ≾ˢ (updᵉ k b ⨟ˢ τ)
updᵉ-above {Ψ} {Q = Q} k b τ p = mk≾ˢ (λ i → ⊩≾̂ᵣ-refl) e
  where
    e : (i : EVar Ψ) → Q ⊩ sE τ i ≾̂ₑ sE (updᵉ k b) i [ τ ]ᵉ
    e i with i ≟ᶠ k
    ... | yes refl = p
    ... | no _     = ⊩≾̂ₑ-refl

updʳ-below : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (k : RVar Ψ) → (b : RExp Ψ) → (τ : Subst Ψ Ψ')
           → Q ⊩ b [ τ ]ʳ ≾̂ᵣ sR τ k → Q ⊩ (updʳ k b ⨟ˢ τ) ≾ˢ τ
updʳ-below {Ψ} {Q = Q} k b τ p = mk≾ˢ r (λ i → ⊩≾̂ₑ-refl)
  where
    r : (i : RVar Ψ) → Q ⊩ sR (updʳ k b) i [ τ ]ʳ ≾̂ᵣ sR τ i
    r i with i ≟ᶠ k
    ... | yes refl = p
    ... | no _     = ⊩≾̂ᵣ-refl

updʳ-above : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (k : RVar Ψ) → (b : RExp Ψ) → (τ : Subst Ψ Ψ')
           → Q ⊩ sR τ k ≾̂ᵣ b [ τ ]ʳ → Q ⊩ τ ≾ˢ (updʳ k b ⨟ˢ τ)
updʳ-above {Ψ} {Q = Q} k b τ p = mk≾ˢ r (λ i → ⊩≾̂ₑ-refl)
  where
    r : (i : RVar Ψ) → Q ⊩ sR τ i ≾̂ᵣ sR (updʳ k b) i [ τ ]ʳ
    r i with i ≟ᶠ k
    ... | yes refl = p
    ... | no _     = ⊩≾̂ᵣ-refl

------------------------------------------------------------------------
-- Locality: free in the image of no unknown the scope was entered with

freeᵉ : ∀ {Θ Φ} → EVar Φ → Subst Θ Φ → 𝔹
freeᵉ k O = anyᶠ (λ α → occᵉ-v k (sTy O α))
          ∨ (anyᶠ (λ i → occᵉ-r k (sR O i)) ∨ anyᶠ (λ i → occᵉ-e k (sE O i)))

freeʳ : ∀ {Θ Φ} → RVar Φ → Subst Θ Φ → 𝔹
freeʳ k O = anyᶠ (λ α → occʳ-v k (sTy O α)) ∨ anyᶠ (λ i → occʳ-r k (sR O i))

freeᵉ-fix : ∀ {Θ Φ} → (k : EVar Φ) → (O : Subst Θ Φ) → freeᵉ k O ≡ false
          → (b : EExp Φ) → (O ⨟ˢ updᵉ k b) ≐ˢ O
freeᵉ-fix k O q b with ∨-false (anyᶠ (λ α → occᵉ-v k (sTy O α))) _ q
... | qT , q' with ∨-false (anyᶠ (λ i → occᵉ-r k (sR O i))) _ q'
...   | qR , qE =
        mk≐ˢ (λ α → updᵉ-v k b (sTy O α) (anyᶠ-false (λ α' → occᵉ-v k (sTy O α')) qT α))
             (λ i → updᵉ-r k b (sR O i) (anyᶠ-false (λ i' → occᵉ-r k (sR O i')) qR i))
             (λ i → updᵉ-e k b (sE O i) (anyᶠ-false (λ i' → occᵉ-e k (sE O i')) qE i))

freeʳ-fix : ∀ {Θ Φ} → (k : RVar Φ) → (O : Subst Θ Φ) → freeʳ k O ≡ false
          → (b : RExp Φ) → (O ⨟ˢ updʳ k b) ≐ˢ O
freeʳ-fix k O q b with ∨-false (anyᶠ (λ α → occʳ-v k (sTy O α))) _ q
... | qT , qR =
      mk≐ˢ (λ α → updʳ-v k b (sTy O α) (anyᶠ-false (λ α' → occʳ-v k (sTy O α')) qT α))
           (λ i → updʳ-r k b (sR O i) (anyᶠ-false (λ i' → occʳ-r k (sR O i')) qR i))
           (λ i → updʳ-e k b (sE O i))

------------------------------------------------------------------------
-- How an unknown `v` occurs in a list of orderings, over either sort of
-- grade expression

module Sides {X : Set} (_≟_ : Decidable (_≡_ {A = X})) (occ : X → 𝔹) where

  -- an ordering holds at every instance, or the unknown is absent from
  -- its right (left) side

  FreeR : X × X → Set
  FreeR (x , x') = (x ≡ x') ⊎ (occ x' ≡ false)

  FreeL : X × X → Set
  FreeL (x , x') = (x ≡ x') ⊎ (occ x ≡ false)

  freeRs : (l : List (X × X)) → Maybe (∀ {a} → a ∈ l → FreeR a)
  freeRs []             = just (λ ())
  freeRs ((x , x') ∷ l) = go (freeRs l) (x ≟ x') (isFalse (occ x'))
    where
      go : Maybe (∀ {a} → a ∈ l → FreeR a) → _ → Maybe (occ x' ≡ false)
         → Maybe (∀ {a} → a ∈ (x , x') ∷ l → FreeR a)
      go nothing  _        _        = nothing
      go (just f) (yes e)  _        = just (λ { (here refl) → inj₁ e ; (there m) → f m })
      go (just f) (no _)   (just q) = just (λ { (here refl) → inj₂ q ; (there m) → f m })
      go (just f) (no _)   nothing  = nothing

  freeLs : (l : List (X × X)) → Maybe (∀ {a} → a ∈ l → FreeL a)
  freeLs []             = just (λ ())
  freeLs ((x , x') ∷ l) = go (freeLs l) (x ≟ x') (isFalse (occ x))
    where
      go : Maybe (∀ {a} → a ∈ l → FreeL a) → _ → Maybe (occ x ≡ false)
         → Maybe (∀ {a} → a ∈ (x , x') ∷ l → FreeL a)
      go nothing  _        _        = nothing
      go (just f) (yes e)  _        = just (λ { (here refl) → inj₁ e ; (there m) → f m })
      go (just f) (no _)   (just q) = just (λ { (here refl) → inj₂ q ; (there m) → f m })
      go (just f) (no _)   nothing  = nothing

module Bounds {X : Set} (_≟_ : Decidable (_≡_ {A = X})) (occ : X → 𝔹) (v : X) where

  open Sides _≟_ occ public

  -- `v` occurs on a right side only as the whole side, below a bound in
  -- `L`

  LowAt : List X → X × X → Set
  LowAt L (x , x') = FreeR (x , x') ⊎ ((x' ≡ v) × (x ∈ L))

  -- `v` occurs on a left side only as the whole side, below `U`

  UpAt : X → X × X → Set
  UpAt U (x , x') = FreeL (x , x') ⊎ ((x ≡ v) × (x' ≡ U))

  record Lows (l : List (X × X)) : Set where
    constructor lows
    field
      bnds : List X
      cls  : ∀ {a} → a ∈ l → LowAt bnds a
      src  : ∀ {x} → x ∈ bnds → (x , v) ∈ l

  open Lows public

  record Ups (l : List (X × X)) : Set where
    constructor ups
    field
      cap  : X
      clsᵘ : ∀ {a} → a ∈ l → UpAt cap a
      srcᵘ : (v , cap) ∈ l

  open Ups public

  -- The lower bounds, none of them mentioning `v`

  lowsOf : (l : List (X × X)) → Maybe (Lows l)
  lowsOf []             = just (lows [] (λ ()) (λ ()))
  lowsOf ((x , x') ∷ l) = go (lowsOf l) (x' ≟ v) (isFalse (occ x)) (x ≟ x') (isFalse (occ x'))
    where
      wk : ∀ {L a} → LowAt L a → LowAt (x ∷ L) a
      wk (inj₁ f)            = inj₁ f
      wk (inj₂ (e , m))      = inj₂ (e , there m)

      go : Maybe (Lows l) → _ → Maybe (occ x ≡ false) → _ → Maybe (occ x' ≡ false)
         → Maybe (Lows ((x , x') ∷ l))
      go nothing                _        _        _       _        = nothing
      go (just (lows L c s))    (yes e)  (just _) _       _        =
        just (lows (x ∷ L) (λ { (here refl) → inj₂ (e , here refl) ; (there m) → wk (c m) })
                           (λ { (here refl) → here (cong (x ,_) (sym e)) ; (there m) → there (s m) }))
      go (just (lows L c s))    _        _        (yes e) _        =
        just (lows L (λ { (here refl) → inj₁ (inj₁ e) ; (there m) → c m }) (λ m → there (s m)))
      go (just (lows L c s))    _        _        (no _)  (just q) =
        just (lows L (λ { (here refl) → inj₁ (inj₂ q) ; (there m) → c m }) (λ m → there (s m)))
      go (just (lows L c s))    _        _        (no _)  nothing  = nothing

  -- The one upper bound: the first found, every other one equal to it

  capOf : (l : List (X × X)) → Maybe (Σ[ U ∈ X ] ((v , U) ∈ l))
  capOf []             = nothing
  capOf ((x , x') ∷ l) = go (x ≟ v) (isFalse (occ x')) (capOf l)
    where
      go : _ → Maybe (occ x' ≡ false) → Maybe (Σ[ U ∈ X ] ((v , U) ∈ l))
         → Maybe (Σ[ U ∈ X ] ((v , U) ∈ (x , x') ∷ l))
      go (yes e)    (just _) _              = just (x' , here (cong (_, x') (sym e)))
      go _          _        (just (U , m)) = just (U , there m)
      go _          _        nothing        = nothing

  upsAt : (U : X) → (l : List (X × X)) → Maybe (∀ {a} → a ∈ l → UpAt U a)
  upsAt U []             = just (λ ())
  upsAt U ((x , x') ∷ l) = go (upsAt U l) (x ≟ x') (isFalse (occ x)) (x ≟ v) (x' ≟ U)
    where
      go : Maybe (∀ {a} → a ∈ l → UpAt U a) → _ → Maybe (occ x ≡ false) → _ → _
         → Maybe (∀ {a} → a ∈ (x , x') ∷ l → UpAt U a)
      go nothing  _       _        _       _       = nothing
      go (just f) (yes e) _        _       _       =
        just (λ { (here refl) → inj₁ (inj₁ e) ; (there m) → f m })
      go (just f) (no _)  (just q) _       _       =
        just (λ { (here refl) → inj₁ (inj₂ q) ; (there m) → f m })
      go (just f) (no _)  nothing  (yes e) (yes e') =
        just (λ { (here refl) → inj₂ (e , e') ; (there m) → f m })
      go (just f) (no _)  nothing  _       _       = nothing

  upsOf : (l : List (X × X)) → Maybe (Ups l)
  upsOf l with capOf l
  ... | nothing      = nothing
  ... | just (U , m) with upsAt U l
  ...   | nothing = nothing
  ...   | just f  = just (ups U f m)

allFalse : ∀ {Y : Set} → (f : Y → 𝔹) → (l : List Y) → Maybe (∀ {y} → y ∈ l → f y ≡ false)
allFalse f []      = just (λ ())
allFalse f (y ∷ l) with isFalse (f y) | allFalse f l
... | just q  | just g  = just (λ { (here refl) → q ; (there m) → g m })
... | just _  | nothing = nothing
... | nothing | _       = nothing

module Bᵉ {Ψ} (k : EVar Ψ) = Bounds (_≟ᵉ_ {Ψ}) (occᵉ-e {Ψ} k) (evar k)
module Bᵉʳ {Ψ} (k : EVar Ψ) = Sides (_≟ʳ_ {Ψ}) (occᵉ-r {Ψ} k)
module Bʳ {Ψ} (k : RVar Ψ) = Bounds (_≟ʳ_ {Ψ}) (occʳ-r {Ψ} k) (rvar k)

-- An unknown absent from every type of a residual

record Cleanᵉ {Ψ} (k : EVar Ψ) (R : Resid Ψ) : Set where
  constructor cleanᵉ
  field
    cts : ∀ {A}   → A ∈ ts R       → occᵉ-v k A ≡ false
    css : ∀ {A B} → (A , B) ∈ ss R → (occᵉ-v k A ∨ occᵉ-v k B) ≡ false
    cds : ∀ {A ρ} → (A , ρ) ∈ ds R → (occᵉ-v k A ∨ occᵉ-r k ρ) ≡ false

record Cleanʳ {Ψ} (k : RVar Ψ) (R : Resid Ψ) : Set where
  constructor cleanʳ
  field
    cts : ∀ {A}   → A ∈ ts R       → occʳ-v k A ≡ false
    css : ∀ {A B} → (A , B) ∈ ss R → (occʳ-v k A ∨ occʳ-v k B) ≡ false
    cds : ∀ {A ρ} → (A , ρ) ∈ ds R → (occʳ-v k A ∨ occʳ-r k ρ) ≡ false

cleanᵉ? : ∀ {Ψ} → (k : EVar Ψ) → (R : Resid Ψ) → Maybe (Cleanᵉ k R)
cleanᵉ? k R with allFalse (occᵉ-v k) (ts R)
                | allFalse (λ { (A , B) → occᵉ-v k A ∨ occᵉ-v k B }) (ss R)
                | allFalse (λ { (A , ρ) → occᵉ-v k A ∨ occᵉ-r k ρ }) (ds R)
... | just t  | just s  | just d  = just (cleanᵉ t s d)
... | _       | _       | _       = nothing

cleanʳ? : ∀ {Ψ} → (k : RVar Ψ) → (R : Resid Ψ) → Maybe (Cleanʳ k R)
cleanʳ? k R with allFalse (occʳ-v k) (ts R)
                | allFalse (λ { (A , B) → occʳ-v k A ∨ occʳ-v k B }) (ss R)
                | allFalse (λ { (A , ρ) → occʳ-v k A ∨ occʳ-r k ρ }) (ds R)
... | just t  | just s  | just d  = just (cleanʳ t s d)
... | _       | _       | _       = nothing

------------------------------------------------------------------------
-- The lowering lemma and its siblings: an assignment the conditions
-- license keeps every instance that satisfied the residual

-- the types, where the unknown does not occur, are left as they were

cleanᵉ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : EVar Ψ} {R : Resid Ψ}
         → Cleanᵉ k R → (b : EExp Ψ) → (τ : Subst Ψ Ψ') → Q ⊩ᴿ R [ τ ]
         → (∀ {A} → A ∈ ts R → Q ⊩ᴱ A [ updᵉ k b ⨟ˢ τ ]ᵛ)
         × (∀ {A B} → (A , B) ∈ ss R → Q ∣ A [ updᵉ k b ⨟ˢ τ ]ᵛ <:̂ᵛ B [ updᵉ k b ⨟ˢ τ ]ᵛ)
         × (∀ {A ρ} → (A , ρ) ∈ ds R
              → VarOK Q (A [ updᵉ k b ⨟ˢ τ ]ᵛ) (ρ [ updᵉ k b ⨟ˢ τ ]ʳ))
cleanᵉ-⊩ {Q = Q} {k} {R} (cleanᵉ ct cs cd) b τ h = ts' , ss' , ds'
  where
    ts' : ∀ {A} → A ∈ ts R → Q ⊩ᴱ A [ updᵉ k b ⨟ˢ τ ]ᵛ
    ts' {A} m = subst (Q ⊩ᴱ_) (sym (updᵉ-⨟v k b τ A (ct m))) (⊩ts h m)

    ss' : ∀ {A B} → (A , B) ∈ ss R → Q ∣ A [ updᵉ k b ⨟ˢ τ ]ᵛ <:̂ᵛ B [ updᵉ k b ⨟ˢ τ ]ᵛ
    ss' {A} {B} m with ∨-false (occᵉ-v k A) (occᵉ-v k B) (cs m)
    ... | qA , qB = subst₂ (Q ∣_<:̂ᵛ_) (sym (updᵉ-⨟v k b τ A qA)) (sym (updᵉ-⨟v k b τ B qB))
                           (⊩ss h m)

    ds' : ∀ {A ρ} → (A , ρ) ∈ ds R → VarOK Q (A [ updᵉ k b ⨟ˢ τ ]ᵛ) (ρ [ updᵉ k b ⨟ˢ τ ]ʳ)
    ds' {A} {ρ} m with ∨-false (occᵉ-v k A) (occᵉ-r k ρ) (cd m)
    ... | qA , qρ = subst₂ (VarOK Q) (sym (updᵉ-⨟v k b τ A qA)) (sym (updᵉ-⨟r k b τ ρ qρ))
                           (⊩ds h m)

cleanʳ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : RVar Ψ} {R : Resid Ψ}
         → Cleanʳ k R → (b : RExp Ψ) → (τ : Subst Ψ Ψ') → Q ⊩ᴿ R [ τ ]
         → (∀ {A} → A ∈ ts R → Q ⊩ᴱ A [ updʳ k b ⨟ˢ τ ]ᵛ)
         × (∀ {A B} → (A , B) ∈ ss R → Q ∣ A [ updʳ k b ⨟ˢ τ ]ᵛ <:̂ᵛ B [ updʳ k b ⨟ˢ τ ]ᵛ)
         × (∀ {A ρ} → (A , ρ) ∈ ds R
              → VarOK Q (A [ updʳ k b ⨟ˢ τ ]ᵛ) (ρ [ updʳ k b ⨟ˢ τ ]ʳ))
cleanʳ-⊩ {Q = Q} {k} {R} (cleanʳ ct cs cd) b τ h = ts' , ss' , ds'
  where
    ts' : ∀ {A} → A ∈ ts R → Q ⊩ᴱ A [ updʳ k b ⨟ˢ τ ]ᵛ
    ts' {A} m = subst (Q ⊩ᴱ_) (sym (updʳ-⨟v k b τ A (ct m))) (⊩ts h m)

    ss' : ∀ {A B} → (A , B) ∈ ss R → Q ∣ A [ updʳ k b ⨟ˢ τ ]ᵛ <:̂ᵛ B [ updʳ k b ⨟ˢ τ ]ᵛ
    ss' {A} {B} m with ∨-false (occʳ-v k A) (occʳ-v k B) (cs m)
    ... | qA , qB = subst₂ (Q ∣_<:̂ᵛ_) (sym (updʳ-⨟v k b τ A qA)) (sym (updʳ-⨟v k b τ B qB))
                           (⊩ss h m)

    ds' : ∀ {A ρ} → (A , ρ) ∈ ds R → VarOK Q (A [ updʳ k b ⨟ˢ τ ]ᵛ) (ρ [ updʳ k b ⨟ˢ τ ]ʳ)
    ds' {A} {ρ} m with ∨-false (occʳ-v k A) (occʳ-r k ρ) (cd m)
    ... | qA , qρ = subst₂ (VarOK Q) (sym (updʳ-⨟v k b τ A qA)) (sym (updʳ-⨟r k b τ ρ qρ))
                           (⊩ds h m)

-- Lowering an effect unknown below its value, to a bound above each of
-- its lower bounds

lowerᵉ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : EVar Ψ} {R : Resid Ψ}
         → (lw : Bᵉ.Lows {Ψ} k (es R))
         → (∀ {a} → a ∈ rs R → Bᵉʳ.FreeR {Ψ} k a)
         → Cleanᵉ k R
         → (b : EExp Ψ) → (τ : Subst Ψ Ψ')
         → Q ⊩ b [ τ ]ᵉ ≾̂ₑ sE τ k
         → (∀ {x} → x ∈ Bᵉ.bnds lw → Q ⊩ x [ τ ]ᵉ ≾̂ₑ b [ τ ]ᵉ)
         → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updᵉ k b ⨟ˢ τ ]
lowerᵉ-⊩ {Q = Q} {k} {R} lw fr cl b τ below ub h =
  mk⊩ᴿ rs' es' (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
  where
    τ₁ = updᵉ k b ⨟ˢ τ

    le : Q ⊩ τ₁ ≾ˢ τ
    le = updᵉ-below k b τ below

    c = cleanᵉ-⊩ cl b τ h

    es' : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ τ₁ ]ᵉ ≾̂ₑ ε' [ τ₁ ]ᵉ
    es' {ε} {ε'} m with Bᵉ.cls lw m
    ... | inj₁ (inj₁ refl) = ⊩≾̂ₑ-refl
    ... | inj₁ (inj₂ q)    =
          transₑ (mono-substₑ le ε)
                 (subst (λ x → Q ⊩ ε [ τ ]ᵉ ≾̂ₑ x) (sym (updᵉ-⨟e k b τ ε' q)) (⊩es h m))
    ... | inj₂ (refl , mx) =
          transₑ (mono-substₑ le ε)
                 (subst (λ x → Q ⊩ ε [ τ ]ᵉ ≾̂ₑ x [ τ ]ᵉ) (sym (updᵉ-hit k b)) (ub mx))

    rs' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ τ₁ ]ʳ ≾̂ᵣ ρ' [ τ₁ ]ʳ
    rs' {ρ} {ρ'} m with fr m
    ... | inj₁ refl = ⊩≾̂ᵣ-refl
    ... | inj₂ q    =
          transᵣ (mono-substᵣ le ρ)
                 (subst (λ x → Q ⊩ ρ [ τ ]ʳ ≾̂ᵣ x) (sym (updᵉ-⨟r k b τ ρ' q)) (⊩rs h m))

-- Raising an effect unknown to its one upper bound

raiseᵉ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : EVar Ψ} {R : Resid Ψ}
         → (up : Bᵉ.Ups {Ψ} k (es R))
         → (∀ {a} → a ∈ rs R → Bᵉʳ.FreeL {Ψ} k a)
         → Cleanᵉ k R
         → (τ : Subst Ψ Ψ')
         → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updᵉ k (Bᵉ.cap up) ⨟ˢ τ ]
raiseᵉ-⊩ {Q = Q} {k} {R} up fl cl τ h =
  mk⊩ᴿ rs' es' (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
  where
    U  = Bᵉ.cap up
    τ₁ = updᵉ k U ⨟ˢ τ

    ge : Q ⊩ τ ≾ˢ τ₁
    ge = updᵉ-above k U τ (⊩es h (Bᵉ.srcᵘ up))

    c = cleanᵉ-⊩ cl U τ h

    es' : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ τ₁ ]ᵉ ≾̂ₑ ε' [ τ₁ ]ᵉ
    es' {ε} {ε'} m with Bᵉ.clsᵘ up m
    ... | inj₁ (inj₁ refl) = ⊩≾̂ₑ-refl
    ... | inj₁ (inj₂ q)    =
          transₑ (subst (λ x → Q ⊩ x ≾̂ₑ ε' [ τ ]ᵉ) (sym (updᵉ-⨟e k U τ ε q)) (⊩es h m))
                 (mono-substₑ ge ε')
    ... | inj₂ (refl , refl) =
          subst (λ x → Q ⊩ x [ τ ]ᵉ ≾̂ₑ U [ τ₁ ]ᵉ) (sym (updᵉ-hit k U)) (mono-substₑ ge U)

    rs' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ τ₁ ]ʳ ≾̂ᵣ ρ' [ τ₁ ]ʳ
    rs' {ρ} {ρ'} m with fl m
    ... | inj₁ refl = ⊩≾̂ᵣ-refl
    ... | inj₂ q    =
          transᵣ (subst (λ x → Q ⊩ x ≾̂ᵣ ρ' [ τ ]ʳ) (sym (updᵉ-⨟r k U τ ρ q)) (⊩rs h m))
                 (mono-substᵣ ge ρ')

-- The same two for a resource unknown, which no effect ordering mentions

lowerʳ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : RVar Ψ} {R : Resid Ψ}
         → (lw : Bʳ.Lows {Ψ} k (rs R))
         → Cleanʳ k R
         → (b : RExp Ψ) → (τ : Subst Ψ Ψ')
         → Q ⊩ b [ τ ]ʳ ≾̂ᵣ sR τ k
         → (∀ {x} → x ∈ Bʳ.bnds lw → Q ⊩ x [ τ ]ʳ ≾̂ᵣ b [ τ ]ʳ)
         → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updʳ k b ⨟ˢ τ ]
lowerʳ-⊩ {Q = Q} {k} {R} lw cl b τ below ub h =
  mk⊩ᴿ rs' es' (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
  where
    τ₁ = updʳ k b ⨟ˢ τ

    le : Q ⊩ τ₁ ≾ˢ τ
    le = updʳ-below k b τ below

    c = cleanʳ-⊩ cl b τ h

    rs' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ τ₁ ]ʳ ≾̂ᵣ ρ' [ τ₁ ]ʳ
    rs' {ρ} {ρ'} m with Bʳ.cls lw m
    ... | inj₁ (inj₁ refl) = ⊩≾̂ᵣ-refl
    ... | inj₁ (inj₂ q)    =
          transᵣ (mono-substᵣ le ρ)
                 (subst (λ x → Q ⊩ ρ [ τ ]ʳ ≾̂ᵣ x) (sym (updʳ-⨟r k b τ ρ' q)) (⊩rs h m))
    ... | inj₂ (refl , mx) =
          transᵣ (mono-substᵣ le ρ)
                 (subst (λ x → Q ⊩ ρ [ τ ]ʳ ≾̂ᵣ x [ τ ]ʳ) (sym (updʳ-hit k b)) (ub mx))

    es' : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ τ₁ ]ᵉ ≾̂ₑ ε' [ τ₁ ]ᵉ
    es' {ε} {ε'} m =
      subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym (updʳ-⨟e k b τ ε)) (sym (updʳ-⨟e k b τ ε')) (⊩es h m)

raiseʳ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : RVar Ψ} {R : Resid Ψ}
         → (up : Bʳ.Ups {Ψ} k (rs R))
         → Cleanʳ k R
         → (τ : Subst Ψ Ψ')
         → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updʳ k (Bʳ.cap up) ⨟ˢ τ ]
raiseʳ-⊩ {Q = Q} {k} {R} up cl τ h =
  mk⊩ᴿ rs' es' (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
  where
    U  = Bʳ.cap up
    τ₁ = updʳ k U ⨟ˢ τ

    ge : Q ⊩ τ ≾ˢ τ₁
    ge = updʳ-above k U τ (⊩rs h (Bʳ.srcᵘ up))

    c = cleanʳ-⊩ cl U τ h

    rs' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ τ₁ ]ʳ ≾̂ᵣ ρ' [ τ₁ ]ʳ
    rs' {ρ} {ρ'} m with Bʳ.clsᵘ up m
    ... | inj₁ (inj₁ refl) = ⊩≾̂ᵣ-refl
    ... | inj₁ (inj₂ q)    =
          transᵣ (subst (λ x → Q ⊩ x ≾̂ᵣ ρ' [ τ ]ʳ) (sym (updʳ-⨟r k U τ ρ q)) (⊩rs h m))
                 (mono-substᵣ ge ρ')
    ... | inj₂ (refl , refl) =
          subst (λ x → Q ⊩ x [ τ ]ʳ ≾̂ᵣ U [ τ₁ ]ʳ) (sym (updʳ-hit k U)) (mono-substᵣ ge U)

    es' : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ τ₁ ]ᵉ ≾̂ₑ ε' [ τ₁ ]ᵉ
    es' {ε} {ε'} m =
      subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym (updʳ-⨟e k U τ ε)) (sym (updʳ-⨟e k U τ ε')) (⊩es h m)

------------------------------------------------------------------------
-- The join of a list of bounds is their least upper bound

joinₑ-ub⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (τ : Subst Ψ Ψ') → (x₀ : EExp Ψ) → (xs : List (EExp Ψ))
          → ∀ {x} → x ∈ x₀ ∷ xs → Q ⊩ x [ τ ]ᵉ ≾̂ₑ joinₑ x₀ xs [ τ ]ᵉ
joinₑ-ub⊩ τ x₀ []        (here refl) = ⊩≾̂ₑ-refl
joinₑ-ub⊩ τ x₀ (x₁ ∷ xs) (here refl) = transₑ ⊔-ubˡₑ (joinₑ-ub⊩ τ (x₀ ⊔̂ₑ x₁) xs (here refl))
joinₑ-ub⊩ τ x₀ (x₁ ∷ xs) (there (here refl)) =
  transₑ ⊔-ubʳₑ (joinₑ-ub⊩ τ (x₀ ⊔̂ₑ x₁) xs (here refl))
joinₑ-ub⊩ τ x₀ (x₁ ∷ xs) (there (there m)) = joinₑ-ub⊩ τ (x₀ ⊔̂ₑ x₁) xs (there m)

joinₑ-lub⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {y : EExp Ψ'} → (τ : Subst Ψ Ψ')
           → (x₀ : EExp Ψ) → (xs : List (EExp Ψ))
           → (∀ {x} → x ∈ x₀ ∷ xs → Q ⊩ x [ τ ]ᵉ ≾̂ₑ y)
           → Q ⊩ joinₑ x₀ xs [ τ ]ᵉ ≾̂ₑ y
joinₑ-lub⊩ τ x₀ []        k = k (here refl)
joinₑ-lub⊩ τ x₀ (x₁ ∷ xs) k =
  joinₑ-lub⊩ τ (x₀ ⊔̂ₑ x₁) xs
    (λ { (here refl) → ⊔-lubₑ (k (here refl)) (k (there (here refl)))
       ; (there m)   → k (there (there m)) })

joinᵣ-ub⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (τ : Subst Ψ Ψ') → (x₀ : RExp Ψ) → (xs : List (RExp Ψ))
          → ∀ {x} → x ∈ x₀ ∷ xs → Q ⊩ x [ τ ]ʳ ≾̂ᵣ joinᵣ x₀ xs [ τ ]ʳ
joinᵣ-ub⊩ τ x₀ []        (here refl) = ⊩≾̂ᵣ-refl
joinᵣ-ub⊩ τ x₀ (x₁ ∷ xs) (here refl) = transᵣ ⊔-ubˡᵣ (joinᵣ-ub⊩ τ (x₀ ⊔̂ᵣ x₁) xs (here refl))
joinᵣ-ub⊩ τ x₀ (x₁ ∷ xs) (there (here refl)) =
  transᵣ ⊔-ubʳᵣ (joinᵣ-ub⊩ τ (x₀ ⊔̂ᵣ x₁) xs (here refl))
joinᵣ-ub⊩ τ x₀ (x₁ ∷ xs) (there (there m)) = joinᵣ-ub⊩ τ (x₀ ⊔̂ᵣ x₁) xs (there m)

joinᵣ-lub⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {y : RExp Ψ'} → (τ : Subst Ψ Ψ')
           → (x₀ : RExp Ψ) → (xs : List (RExp Ψ))
           → (∀ {x} → x ∈ x₀ ∷ xs → Q ⊩ x [ τ ]ʳ ≾̂ᵣ y)
           → Q ⊩ joinᵣ x₀ xs [ τ ]ʳ ≾̂ᵣ y
joinᵣ-lub⊩ τ x₀ []        k = k (here refl)
joinᵣ-lub⊩ τ x₀ (x₁ ∷ xs) k =
  joinᵣ-lub⊩ τ (x₀ ⊔̂ᵣ x₁) xs
    (λ { (here refl) → ⊔-lubᵣ (k (here refl)) (k (there (here refl)))
       ; (there m)   → k (there (there m)) })

------------------------------------------------------------------------
-- One step: the value an unknown is sent to, with the proof that every
-- instance survives it

Keeps : ∀ {Ψ} → Subst Ψ Ψ → Resid Ψ → Set
Keeps {Ψ} σ R = ∀ {Ψ'} → (τ : Subst Ψ Ψ') → (Q : Hyps Ψ') → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ σ ⨟ˢ τ ]

first : ∀ {X : Set} → Maybe X → Maybe X → Maybe X
first (just x) _ = just x
first nothing  y = y

-- The unit, for an unknown with no bound that does occur

occursᵉ : ∀ {Ψ} → EVar Ψ → Resid Ψ → 𝔹
occursᵉ k R = anyL (λ { (ε , _) → occᵉ-e k ε }) (es R) ∨ anyL (λ { (ρ , _) → occᵉ-r k ρ }) (rs R)

occursʳ : ∀ {Ψ} → RVar Ψ → Resid Ψ → 𝔹
occursʳ k R = anyL (λ { (ρ , _) → occʳ-r k ρ }) (rs R)

stepᵉ : ∀ {Ψ} → (k : EVar Ψ) → (R : Resid Ψ) → Maybe (Σ[ b ∈ EExp Ψ ] Keeps (updᵉ k b) R)
stepᵉ {Ψ} k R with cleanᵉ? k R
... | nothing = nothing
... | just cl =
      first (lower (Bᵉ.lowsOf {Ψ} k (es R)) (Bᵉʳ.freeRs {Ψ} k (rs R)))
            (first (raise (Bᵉ.upsOf {Ψ} k (es R)) (Bᵉʳ.freeLs {Ψ} k (rs R)))
                   (unit umin?ₑ (Bᵉ.lowsOf {Ψ} k (es R)) (Bᵉʳ.freeRs {Ψ} k (rs R)) (occursᵉ k R)))
  where
    lower : Maybe (Bᵉ.Lows {Ψ} k (es R)) → Maybe (∀ {a} → a ∈ rs R → Bᵉʳ.FreeR {Ψ} k a)
          → Maybe (Σ[ b ∈ EExp _ ] Keeps (updᵉ k b) R)
    lower (just lw@(Bᵉ.lows (x ∷ xs) c s)) (just fr) =
      just (joinₑ x xs ,
            λ τ Q h → lowerᵉ-⊩ lw fr cl (joinₑ x xs) τ
                        (joinₑ-lub⊩ τ x xs (λ m → ⊩es h (s m)))
                        (joinₑ-ub⊩ τ x xs) h)
    lower _ _ = nothing

    raise : Maybe (Bᵉ.Ups {Ψ} k (es R)) → Maybe (∀ {a} → a ∈ rs R → Bᵉʳ.FreeL {Ψ} k a)
          → Maybe (Σ[ b ∈ EExp _ ] Keeps (updᵉ k b) R)
    raise (just up) (just fl) = just (Bᵉ.cap up , λ τ Q h → raiseᵉ-⊩ up fl cl τ h)
    raise _         _         = nothing

    unit : Maybe (UnitMinₑ) → Maybe (Bᵉ.Lows {Ψ} k (es R))
         → Maybe (∀ {a} → a ∈ rs R → Bᵉʳ.FreeR {Ψ} k a) → 𝔹
         → Maybe (Σ[ b ∈ EExp _ ] Keeps (updᵉ k b) R)
    unit (just um) (just lw@(Bᵉ.lows [] c s)) (just fr) true =
      just (ûₑ , λ τ Q h → lowerᵉ-⊩ lw fr cl ûₑ τ (minₑ um) (λ ()) h)
    unit _ _ _ _ = nothing

stepʳ : ∀ {Ψ} → (k : RVar Ψ) → (R : Resid Ψ) → Maybe (Σ[ b ∈ RExp Ψ ] Keeps (updʳ k b) R)
stepʳ {Ψ} k R with cleanʳ? k R
... | nothing = nothing
... | just cl =
      first (lower (Bʳ.lowsOf {Ψ} k (rs R)))
            (first (raise (Bʳ.upsOf {Ψ} k (rs R)))
                   (unit umin?ᵣ (Bʳ.lowsOf {Ψ} k (rs R)) (occursʳ k R)))
  where
    lower : Maybe (Bʳ.Lows {Ψ} k (rs R)) → Maybe (Σ[ b ∈ RExp _ ] Keeps (updʳ k b) R)
    lower (just lw@(Bʳ.lows (x ∷ xs) c s)) =
      just (joinᵣ x xs ,
            λ τ Q h → lowerʳ-⊩ lw cl (joinᵣ x xs) τ
                        (joinᵣ-lub⊩ τ x xs (λ m → ⊩rs h (s m)))
                        (joinᵣ-ub⊩ τ x xs) h)
    lower _ = nothing

    raise : Maybe (Bʳ.Ups {Ψ} k (rs R)) → Maybe (Σ[ b ∈ RExp _ ] Keeps (updʳ k b) R)
    raise (just up) = just (Bʳ.cap up , λ τ Q h → raiseʳ-⊩ up cl τ h)
    raise nothing   = nothing

    unit : Maybe (UnitMinᵣ) → Maybe (Bʳ.Lows {Ψ} k (rs R)) → 𝔹
         → Maybe (Σ[ b ∈ RExp _ ] Keeps (updʳ k b) R)
    unit (just um) (just lw@(Bʳ.lows [] c s)) true =
      just (ûᵣ , λ τ Q h → lowerʳ-⊩ lw cl ûᵣ τ (minᵣ um) (λ ()) h)
    unit _ _ _ = nothing

------------------------------------------------------------------------
-- Settled disjunctions: a side decided true against no hypotheses

settledᵈ : ∀ {Ψ} → (A : OVType Ψ) → (ρ : RExp Ψ)
         → Maybe (∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ))
settledᵈ A ρ with decide≾ᵣ {Q = ∅ᴴ} ρ ûᵣ
... | just p  = just (λ δ → ≾ᵘ-ok (⊩-substᵣ ∅ᴴ-⊩ᴴ p))
... | nothing with etDec A in e
...   | just [] = just (λ δ → et-ok (⊩ᴱ-subst ∅ᴴ-⊩ᴴ (etDec-sound {Q = ∅ᴴ} A e (λ ()))))
...   | just (_ ∷ _) = nothing
...   | nothing      = nothing

-- The disjunctions of a list that are not settled

record Unsettled {Ψ} (l : List (OVType Ψ × RExp Ψ)) : Set where
  constructor unset
  field
    kept  : List (OVType Ψ × RExp Ψ)
    kept⊆ : ∀ {a} → a ∈ kept → a ∈ l
    back  : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
          → (∀ {A ρ} → (A , ρ) ∈ kept → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ))
          → ∀ {A ρ} → (A , ρ) ∈ l → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ)

unsettled : ∀ {Ψ} → (l : List (OVType Ψ × RExp Ψ)) → Unsettled l
unsettled []            = unset [] (λ ()) (λ δ k → λ ())
unsettled ((A , ρ) ∷ l) = go (settledᵈ A ρ) (unsettled l)
  where
    go : Maybe (∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst _ Ψ') → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ))
       → Unsettled l → Unsettled ((A , ρ) ∷ l)
    go (just p) (unset l' sb bk) =
      unset l' (λ m → there (sb m))
            (λ δ k → λ { (here refl) → p δ ; (there m) → bk δ k m })
    go nothing  (unset l' sb bk) =
      unset ((A , ρ) ∷ l')
            (λ { (here refl) → here refl ; (there m) → there (sb m) })
            (λ δ k → λ { (here refl) → k (here refl)
                       ; (there m)   → bk δ (λ m' → k (there m')) m })

------------------------------------------------------------------------
-- Localisation: the settled disjunctions dropped, then the steps
-- iterated over the local unknowns

record Localised {Θ Φ} (O : Subst Θ Φ) (R : Resid Φ) : Set where
  constructor loc
  field
    lσ   : Subst Φ Φ
    lR   : Resid Φ
    lfix : (O ⨟ˢ lσ) ≐ˢ O
    lsnd : ∀ {Ψ'} → (δ : Subst Φ Ψ') → (Q : Hyps Ψ') → Q ⊩ᴿ lR [ δ ] → Q ⊩ᴿ R [ lσ ⨟ˢ δ ]
    lcpl : ∀ {Ψ'} → (τ : Subst Φ Ψ') → (Q : Hyps Ψ') → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ lR [ τ ]

open Localised public

-- The settled disjunctions dropped: the instances are unchanged

loc-settle : ∀ {Θ Φ} {O : Subst Θ Φ} {R : Resid Φ} → Localised O R
loc-settle {O = O} {R} =
  loc idˢ (resid (rs R) (es R) (ts R) (ss R) (Unsettled.kept U)) (⨟-idʳ O)
      (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ))
                   (mk⊩ᴿ (⊩rs h) (⊩es h) (⊩ts h) (⊩ss h) (Unsettled.back U δ (⊩ds h))))
      (λ τ Q h → mk⊩ᴿ (⊩rs h) (⊩es h) (⊩ts h) (⊩ss h) (λ m → ⊩ds h (Unsettled.kept⊆ U m)))
  where
    U = unsettled (ds R)

loc-ext : ∀ {Θ Φ} {O : Subst Θ Φ} {R : Resid Φ} → (L : Localised O R)
        → (σ : Subst Φ Φ) → (O ⨟ˢ σ) ≐ˢ O → Keeps σ (lR L) → Localised O R
loc-ext {O = O} {R} (loc σ₀ R₀ fx sn cp) σ fσ st =
  loc (σ₀ ⨟ˢ σ) (R₀ [ σ ]ᴿ)
      (≐ˢ-trans (≐ˢ-sym (⨟-assoc O σ₀ σ)) (≐ˢ-trans (⨟-congˡ fx σ) fσ))
      (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-assoc σ₀ σ δ)) (sn (σ ⨟ˢ δ) Q (⊩ᴿ-subst h)))
      (λ τ Q h → ⊩ᴿ-subst⁻ (st τ Q (cp τ Q h)))

module _ {Θ Φ} (O : Subst Θ Φ) (R : Resid Φ) where

  passᵉ : List (Σ[ k ∈ EVar Φ ] (freeᵉ k O ≡ false)) → Localised O R → Localised O R × 𝔹
  passᵉ []             L = L , false
  passᵉ ((k , q) ∷ ks) L with stepᵉ k (lR L)
  ... | nothing      = passᵉ ks L
  ... | just (b , st) = proj₁ (passᵉ ks (loc-ext L (updᵉ k b) (freeᵉ-fix k O q b) st)) , true

  passʳ : List (Σ[ k ∈ RVar Φ ] (freeʳ k O ≡ false)) → Localised O R → Localised O R × 𝔹
  passʳ []             L = L , false
  passʳ ((k , q) ∷ ks) L with stepʳ k (lR L)
  ... | nothing      = passʳ ks L
  ... | just (b , st) = proj₁ (passʳ ks (loc-ext L (updʳ k b) (freeʳ-fix k O q b) st)) , true

  -- Each round that changes something settles an unknown for good, so
  -- as many rounds as there are unknowns reach the fixed point.

  rounds : ℕ → Localised O R → Localised O R
  rounds nzero    L = L
  rounds (nsuc n) L = next (passᵉ (misses (λ k → freeᵉ k O)) L)
    where
      next₂ : Localised O R × 𝔹 → Localised O R
      next₂ (L' , true)  = rounds n L'
      next₂ (L' , false) = L'

      next : Localised O R × 𝔹 → Localised O R
      next (L' , changed) with passʳ (misses (λ k → freeʳ k O)) L'
      ... | L'' , changed' = next₂ (L'' , (changed ∨ changed'))

localise : ∀ {Θ Φ} → (O : Subst Θ Φ) → (R : Resid Φ) → Localised O R
localise {Φ = Φ} O R = rounds O R (nE Φ + nR Φ) loc-settle

-- An assignment the later substitution already agrees with is absorbed

updᵉ-absorb : ∀ {Ψ Ψ'} → (k : EVar Ψ) → (b : EExp Ψ) → (Y : Subst Ψ Ψ')
            → sE Y k ≡ b [ Y ]ᵉ → (updᵉ k b ⨟ˢ Y) ≐ˢ Y
updᵉ-absorb {Ψ} k b Y q = mk≐ˢ (λ α → refl) (λ i → refl) e
  where
    e : (i : EVar Ψ) → sE (updᵉ k b) i [ Y ]ᵉ ≡ sE Y i
    e i with i ≟ᶠ k
    ... | yes refl = sym q
    ... | no _     = refl
