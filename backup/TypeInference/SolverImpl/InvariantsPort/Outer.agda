------------------------------------------------------------------
-- Unknowns free in the images of a substitution                 --
--                                                                --
-- `P ⊆ᶠ P'`: every unknown free in an image of `P` is free in    --
-- one of `P'`. A good side (`Goodₑ`, `Goodᵣ`) is a whole unknown --
-- or mentions only unknowns free in the images of `P`; a type is --
-- good when its grades are (`TyGoodᵛ`), a substitution when its  --
-- images are (`GV`). Closure under `⊆ᶠ` and good substitutions.  --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; true; false) renaming (Bool to 𝔹)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Invariants.Outer (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Instances S using (_+eⁿ_; _↑ᵉⁿ_; ≐ˢ-↑ᵉⁿ)

open import TypeInference.SolverImpl.Core.Occurs S
  using (occᵉ-e; occᵉ-r; occᵉ-v; occᵉ-c; occʳ-r; occʳ-v; occʳ-c; occᵗ-v; occᵗ-c)
open import TypeInference.SolverImpl.Core.Rigid S
  using (∨-true; ∨-left; ∨-right; dec-true; true-dec)
open import TypeInference.SolverImpl.Deferred S using (κ⟨_⟩; κ-wkᵛ; κ-wkʳ; κ-wkᵉ)
open import TypeInference.SolverImpl.Localise S
  using (freeᵉ; freeʳ; Outerₑ; Outerᵣ; anyᶠ; anyᶠ-true)

------------------------------------------------------------------------
-- Finite disjunctions

anyᶠ-intro : ∀ {n} → (f : Fin n → 𝔹) → (i : Fin n) → f i ≡ true → anyᶠ f ≡ true
anyᶠ-intro f zero    q = ∨-left (f zero) _ q
anyᶠ-intro f (suc i) q = ∨-right (f zero) _ (anyᶠ-intro (λ i' → f (suc i')) i q)

anyᶠ-cong : ∀ {n} → {f g : Fin n → 𝔹} → (∀ i → f i ≡ g i) → anyᶠ f ≡ anyᶠ g
anyᶠ-cong {nzero}  p = refl
anyᶠ-cong {nsuc n} p = cong₂ _∨_ (p zero) (anyᶠ-cong (λ i → p (suc i)))

------------------------------------------------------------------------
-- An unknown of a substituted expression comes from the image of one of
-- the expression's own

module _ {Ψ Ψ'} (σ : Subst Ψ Ψ') where

  occᵉ-e⁻ : ∀ {k} → (ε : EExp Ψ) → occᵉ-e k (ε [ σ ]ᵉ) ≡ true
          → Σ[ i ∈ EVar Ψ ] ((occᵉ-e i ε ≡ true) × (occᵉ-e k (sE σ i) ≡ true))
  occᵉ-e⁻     (evar i)   q = i , dec-true (i ≟ᶠ i) refl , q
  occᵉ-e⁻     (econst c) ()
  occᵉ-e⁻ {k} (a ·̂ₑ b)   q with ∨-true (occᵉ-e k (a [ σ ]ᵉ)) _ q
  ... | inj₁ r with occᵉ-e⁻ a r
  ...   | i , p , s = i , ∨-left (occᵉ-e i a) (occᵉ-e i b) p , s
  occᵉ-e⁻ {k} (a ·̂ₑ b)   q | inj₂ r with occᵉ-e⁻ b r
  ...   | i , p , s = i , ∨-right (occᵉ-e i a) (occᵉ-e i b) p , s
  occᵉ-e⁻ {k} (a ⊔̂ₑ b)   q with ∨-true (occᵉ-e k (a [ σ ]ᵉ)) _ q
  ... | inj₁ r with occᵉ-e⁻ a r
  ...   | i , p , s = i , ∨-left (occᵉ-e i a) (occᵉ-e i b) p , s
  occᵉ-e⁻ {k} (a ⊔̂ₑ b)   q | inj₂ r with occᵉ-e⁻ b r
  ...   | i , p , s = i , ∨-right (occᵉ-e i a) (occᵉ-e i b) p , s

  -- an effect-grade unknown of a resource expression

  OccRE : EVar Ψ' → RExp Ψ → Set
  OccRE k ρ = (Σ[ i ∈ RVar Ψ ] ((occʳ-r i ρ ≡ true) × (occᵉ-r k (sR σ i) ≡ true)))
            ⊎ (Σ[ i ∈ EVar Ψ ] ((occᵉ-r i ρ ≡ true) × (occᵉ-e k (sE σ i) ≡ true)))

  occᵉ-r⁻ : ∀ {k} → (ρ : RExp Ψ) → occᵉ-r k (ρ [ σ ]ʳ) ≡ true → OccRE k ρ
  occᵉ-r⁻     (rvar i)   q = inj₁ (i , dec-true (i ≟ᶠ i) refl , q)
  occᵉ-r⁻     (rconst c) ()
  occᵉ-r⁻ {k} (a ·̂ᵣ b)   q with ∨-true (occᵉ-r k (a [ σ ]ʳ)) _ q
  ... | inj₁ r = left (occᵉ-r⁻ a r)
    where
      left : OccRE k a → OccRE k (a ·̂ᵣ b)
      left (inj₁ (i , p , s)) = inj₁ (i , ∨-left (occʳ-r i a) (occʳ-r i b) p , s)
      left (inj₂ (i , p , s)) = inj₂ (i , ∨-left (occᵉ-r i a) (occᵉ-r i b) p , s)
  ... | inj₂ r = right (occᵉ-r⁻ b r)
    where
      right : OccRE k b → OccRE k (a ·̂ᵣ b)
      right (inj₁ (i , p , s)) = inj₁ (i , ∨-right (occʳ-r i a) (occʳ-r i b) p , s)
      right (inj₂ (i , p , s)) = inj₂ (i , ∨-right (occᵉ-r i a) (occᵉ-r i b) p , s)
  occᵉ-r⁻ {k} (a ⊔̂ᵣ b)   q with ∨-true (occᵉ-r k (a [ σ ]ʳ)) _ q
  ... | inj₁ r = left (occᵉ-r⁻ a r)
    where
      left : OccRE k a → OccRE k (a ⊔̂ᵣ b)
      left (inj₁ (i , p , s)) = inj₁ (i , ∨-left (occʳ-r i a) (occʳ-r i b) p , s)
      left (inj₂ (i , p , s)) = inj₂ (i , ∨-left (occᵉ-r i a) (occᵉ-r i b) p , s)
  ... | inj₂ r = right (occᵉ-r⁻ b r)
    where
      right : OccRE k b → OccRE k (a ⊔̂ᵣ b)
      right (inj₁ (i , p , s)) = inj₁ (i , ∨-right (occʳ-r i a) (occʳ-r i b) p , s)
      right (inj₂ (i , p , s)) = inj₂ (i , ∨-right (occᵉ-r i a) (occᵉ-r i b) p , s)
  occᵉ-r⁻     ∣ ε ∣̂ᵉ     q = inj₂ (occᵉ-e⁻ ε q)

  occʳ-r⁻ : ∀ {k} → (ρ : RExp Ψ) → occʳ-r k (ρ [ σ ]ʳ) ≡ true
          → Σ[ i ∈ RVar Ψ ] ((occʳ-r i ρ ≡ true) × (occʳ-r k (sR σ i) ≡ true))
  occʳ-r⁻     (rvar i)   q = i , dec-true (i ≟ᶠ i) refl , q
  occʳ-r⁻     (rconst c) ()
  occʳ-r⁻ {k} (a ·̂ᵣ b)   q with ∨-true (occʳ-r k (a [ σ ]ʳ)) _ q
  ... | inj₁ r with occʳ-r⁻ a r
  ...   | i , p , s = i , ∨-left (occʳ-r i a) (occʳ-r i b) p , s
  occʳ-r⁻ {k} (a ·̂ᵣ b)   q | inj₂ r with occʳ-r⁻ b r
  ...   | i , p , s = i , ∨-right (occʳ-r i a) (occʳ-r i b) p , s
  occʳ-r⁻ {k} (a ⊔̂ᵣ b)   q with ∨-true (occʳ-r k (a [ σ ]ʳ)) _ q
  ... | inj₁ r with occʳ-r⁻ a r
  ...   | i , p , s = i , ∨-left (occʳ-r i a) (occʳ-r i b) p , s
  occʳ-r⁻ {k} (a ⊔̂ᵣ b)   q | inj₂ r with occʳ-r⁻ b r
  ...   | i , p , s = i , ∨-right (occʳ-r i a) (occʳ-r i b) p , s
  occʳ-r⁻     ∣ ε ∣̂ᵉ     ()

  -- in a type: through a type variable or a grade one

  OccVE : EVar Ψ' → OVType Ψ → Set
  OccVE k A = (Σ[ α ∈ TyVar Ψ ] ((occᵗ-v α A ≡ true) × (occᵉ-v k (sTy σ α) ≡ true)))
            ⊎ ((Σ[ i ∈ RVar Ψ ] ((occʳ-v i A ≡ true) × (occᵉ-r k (sR σ i) ≡ true)))
            ⊎ (Σ[ i ∈ EVar Ψ ] ((occᵉ-v i A ≡ true) × (occᵉ-e k (sE σ i) ≡ true))))

  OccCE : EVar Ψ' → OCType Ψ → Set
  OccCE k C = (Σ[ α ∈ TyVar Ψ ] ((occᵗ-c α C ≡ true) × (occᵉ-v k (sTy σ α) ≡ true)))
            ⊎ ((Σ[ i ∈ RVar Ψ ] ((occʳ-c i C ≡ true) × (occᵉ-r k (sR σ i) ≡ true)))
            ⊎ (Σ[ i ∈ EVar Ψ ] ((occᵉ-c i C ≡ true) × (occᵉ-e k (sE σ i) ≡ true))))

  private
    mapVE : ∀ {k} → (A B : OVType Ψ)
          → (∀ {α} → occᵗ-v α A ≡ true → occᵗ-v α B ≡ true)
          → (∀ {i} → occʳ-v i A ≡ true → occʳ-v i B ≡ true)
          → (∀ {i} → occᵉ-v i A ≡ true → occᵉ-v i B ≡ true)
          → OccVE k A → OccVE k B
    mapVE A B ft fr fe (inj₁ (α , p , q))        = inj₁ (α , ft p , q)
    mapVE A B ft fr fe (inj₂ (inj₁ (i , p , q))) = inj₂ (inj₁ (i , fr p , q))
    mapVE A B ft fr fe (inj₂ (inj₂ (i , p , q))) = inj₂ (inj₂ (i , fe p , q))

  mutual

    occᵉ-v⁻ : ∀ {k} → (A : OVType Ψ) → occᵉ-v k (A [ σ ]ᵛ) ≡ true → OccVE k A
    occᵉ-v⁻     (tvar α)  q = inj₁ (α , dec-true (α ≟ᶠ α) refl , q)
    occᵉ-v⁻     (Base b)  ()
    occᵉ-v⁻     Unit      ()
    occᵉ-v⁻     Bool      ()
    occᵉ-v⁻     Empty     ()
    occᵉ-v⁻ {k} (A |×| B) q with ∨-true (occᵉ-v k (A [ σ ]ᵛ)) _ q
    ... | inj₁ r = mapVE A (A |×| B) (λ {α} p → ∨-left (occᵗ-v α A) _ p) (λ {i} p → ∨-left (occʳ-v i A) _ p)
                         (λ {i} p → ∨-left (occᵉ-v i A) _ p) (occᵉ-v⁻ A r)
    ... | inj₂ r = mapVE B (A |×| B) (λ {α} p → ∨-right (occᵗ-v α A) _ p) (λ {i} p → ∨-right (occʳ-v i A) _ p)
                         (λ {i} p → ∨-right (occᵉ-v i A) _ p) (occᵉ-v⁻ B r)
    occᵉ-v⁻ {k} (A ⇒ C)   q with ∨-true (occᵉ-v k (A [ σ ]ᵛ)) _ q
    ... | inj₁ r = mapVE A (A ⇒ C) (λ {α} p → ∨-left (occᵗ-v α A) _ p) (λ {i} p → ∨-left (occʳ-v i A) _ p)
                         (λ {i} p → ∨-left (occᵉ-v i A) _ p) (occᵉ-v⁻ A r)
    ... | inj₂ r = fromC (occᵉ-c⁻ C r)
      where
        fromC : OccCE k C → OccVE k (A ⇒ C)
        fromC (inj₁ (α , p , q'))        = inj₁ (α , ∨-right (occᵗ-v α A) _ p , q')
        fromC (inj₂ (inj₁ (i , p , q'))) = inj₂ (inj₁ (i , ∨-right (occʳ-v i A) _ p , q'))
        fromC (inj₂ (inj₂ (i , p , q'))) = inj₂ (inj₂ (i , ∨-right (occᵉ-v i A) _ p , q'))
    occᵉ-v⁻ {k} ([ ρ ] A) q with ∨-true (occᵉ-r k (ρ [ σ ]ʳ)) _ q
    ... | inj₁ r = fromR (occᵉ-r⁻ ρ r)
      where
        fromR : OccRE k ρ → OccVE k ([ ρ ] A)
        fromR (inj₁ (i , p , q')) = inj₂ (inj₁ (i , ∨-left (occʳ-r i ρ) _ p , q'))
        fromR (inj₂ (i , p , q')) = inj₂ (inj₂ (i , ∨-left (occᵉ-r i ρ) _ p , q'))
    ... | inj₂ r = mapVE A ([ ρ ] A) (λ p → p) (λ {i} p → ∨-right (occʳ-r i ρ) _ p)
                         (λ {i} p → ∨-right (occᵉ-r i ρ) _ p) (occᵉ-v⁻ A r)

    occᵉ-c⁻ : ∀ {k} → (C : OCType Ψ) → occᵉ-c k (C [ σ ]ᶜ) ≡ true → OccCE k C
    occᵉ-c⁻ {k} (A ‼ ε) q with ∨-true (occᵉ-v k (A [ σ ]ᵛ)) _ q
    ... | inj₁ r = fromV (occᵉ-v⁻ A r)
      where
        fromV : OccVE k A → OccCE k (A ‼ ε)
        fromV (inj₁ (α , p , q'))        = inj₁ (α , p , q')
        fromV (inj₂ (inj₁ (i , p , q'))) = inj₂ (inj₁ (i , p , q'))
        fromV (inj₂ (inj₂ (i , p , q'))) = inj₂ (inj₂ (i , ∨-left (occᵉ-v i A) _ p , q'))
    ... | inj₂ r with occᵉ-e⁻ ε r
    ...   | i , p , q' = inj₂ (inj₂ (i , ∨-right (occᵉ-v i A) _ p , q'))

  OccVR : RVar Ψ' → OVType Ψ → Set
  OccVR k A = (Σ[ α ∈ TyVar Ψ ] ((occᵗ-v α A ≡ true) × (occʳ-v k (sTy σ α) ≡ true)))
            ⊎ (Σ[ i ∈ RVar Ψ ] ((occʳ-v i A ≡ true) × (occʳ-r k (sR σ i) ≡ true)))

  mutual

    occʳ-v⁻ : ∀ {k} → (A : OVType Ψ) → occʳ-v k (A [ σ ]ᵛ) ≡ true → OccVR k A
    occʳ-v⁻     (tvar α)  q = inj₁ (α , dec-true (α ≟ᶠ α) refl , q)
    occʳ-v⁻     (Base b)  ()
    occʳ-v⁻     Unit      ()
    occʳ-v⁻     Bool      ()
    occʳ-v⁻     Empty     ()
    occʳ-v⁻ {k} (A |×| B) q with ∨-true (occʳ-v k (A [ σ ]ᵛ)) _ q
    ... | inj₁ r with occʳ-v⁻ A r
    ...   | inj₁ (α , p , q') = inj₁ (α , ∨-left (occᵗ-v α A) _ p , q')
    ...   | inj₂ (i , p , q') = inj₂ (i , ∨-left (occʳ-v i A) _ p , q')
    occʳ-v⁻ {k} (A |×| B) q | inj₂ r with occʳ-v⁻ B r
    ...   | inj₁ (α , p , q') = inj₁ (α , ∨-right (occᵗ-v α A) _ p , q')
    ...   | inj₂ (i , p , q') = inj₂ (i , ∨-right (occʳ-v i A) _ p , q')
    occʳ-v⁻ {k} (A ⇒ C)   q with ∨-true (occʳ-v k (A [ σ ]ᵛ)) _ q
    ... | inj₁ r with occʳ-v⁻ A r
    ...   | inj₁ (α , p , q') = inj₁ (α , ∨-left (occᵗ-v α A) _ p , q')
    ...   | inj₂ (i , p , q') = inj₂ (i , ∨-left (occʳ-v i A) _ p , q')
    occʳ-v⁻ {k} (A ⇒ (B ‼ ε)) q | inj₂ r with occʳ-v⁻ B r
    ...   | inj₁ (α , p , q') = inj₁ (α , ∨-right (occᵗ-v α A) _ p , q')
    ...   | inj₂ (i , p , q') = inj₂ (i , ∨-right (occʳ-v i A) _ p , q')
    occʳ-v⁻ {k} ([ ρ ] A) q with ∨-true (occʳ-r k (ρ [ σ ]ʳ)) _ q
    ... | inj₁ r with occʳ-r⁻ ρ r
    ...   | i , p , q' = inj₂ (i , ∨-left (occʳ-r i ρ) _ p , q')
    occʳ-v⁻ {k} ([ ρ ] A) q | inj₂ r with occʳ-v⁻ A r
    ...   | inj₁ (α , p , q') = inj₁ (α , p , q')
    ...   | inj₂ (i , p , q') = inj₂ (i , ∨-right (occʳ-r i ρ) _ p , q')

------------------------------------------------------------------------
-- ... and every unknown of the image of one of its unknowns is one of
-- the substituted expression

module _ {Ψ Ψ'} (σ : Subst Ψ Ψ') where

  -- an effect-grade unknown, through an effect-grade one

  occᵉ-e⁺ : ∀ {i k} → (ε : EExp Ψ) → occᵉ-e i ε ≡ true → occᵉ-e k (sE σ i) ≡ true
          → occᵉ-e k (ε [ σ ]ᵉ) ≡ true
  occᵉ-e⁺ {i} {k} (evar j)   p q =
    subst (λ x → occᵉ-e k (sE σ x) ≡ true) (true-dec (i ≟ᶠ j) p) q
  occᵉ-e⁺         (econst c) () q
  occᵉ-e⁺ {i} {k} (a ·̂ₑ b)   p q with ∨-true (occᵉ-e i a) _ p
  ... | inj₁ r = ∨-left  (occᵉ-e k (a [ σ ]ᵉ)) _ (occᵉ-e⁺ a r q)
  ... | inj₂ r = ∨-right (occᵉ-e k (a [ σ ]ᵉ)) _ (occᵉ-e⁺ b r q)
  occᵉ-e⁺ {i} {k} (a ⊔̂ₑ b)   p q with ∨-true (occᵉ-e i a) _ p
  ... | inj₁ r = ∨-left  (occᵉ-e k (a [ σ ]ᵉ)) _ (occᵉ-e⁺ a r q)
  ... | inj₂ r = ∨-right (occᵉ-e k (a [ σ ]ᵉ)) _ (occᵉ-e⁺ b r q)

  occᵉ-r⁺ : ∀ {i k} → (ρ : RExp Ψ) → occᵉ-r i ρ ≡ true → occᵉ-e k (sE σ i) ≡ true
          → occᵉ-r k (ρ [ σ ]ʳ) ≡ true
  occᵉ-r⁺         (rvar j)   () q
  occᵉ-r⁺         (rconst c) () q
  occᵉ-r⁺ {i} {k} (a ·̂ᵣ b)   p q with ∨-true (occᵉ-r i a) _ p
  ... | inj₁ r = ∨-left  (occᵉ-r k (a [ σ ]ʳ)) _ (occᵉ-r⁺ a r q)
  ... | inj₂ r = ∨-right (occᵉ-r k (a [ σ ]ʳ)) _ (occᵉ-r⁺ b r q)
  occᵉ-r⁺ {i} {k} (a ⊔̂ᵣ b)   p q with ∨-true (occᵉ-r i a) _ p
  ... | inj₁ r = ∨-left  (occᵉ-r k (a [ σ ]ʳ)) _ (occᵉ-r⁺ a r q)
  ... | inj₂ r = ∨-right (occᵉ-r k (a [ σ ]ʳ)) _ (occᵉ-r⁺ b r q)
  occᵉ-r⁺         ∣ ε ∣̂ᵉ     p q = occᵉ-e⁺ ε p q

  mutual

    occᵉ-v⁺ : ∀ {i k} → (A : OVType Ψ) → occᵉ-v i A ≡ true → occᵉ-e k (sE σ i) ≡ true
            → occᵉ-v k (A [ σ ]ᵛ) ≡ true
    occᵉ-v⁺         (tvar α)  () q
    occᵉ-v⁺         (Base b)  () q
    occᵉ-v⁺         Unit      () q
    occᵉ-v⁺         Bool      () q
    occᵉ-v⁺         Empty     () q
    occᵉ-v⁺ {i} {k} (A |×| B) p q with ∨-true (occᵉ-v i A) _ p
    ... | inj₁ r = ∨-left  (occᵉ-v k (A [ σ ]ᵛ)) _ (occᵉ-v⁺ A r q)
    ... | inj₂ r = ∨-right (occᵉ-v k (A [ σ ]ᵛ)) _ (occᵉ-v⁺ B r q)
    occᵉ-v⁺ {i} {k} (A ⇒ C)   p q with ∨-true (occᵉ-v i A) _ p
    ... | inj₁ r = ∨-left  (occᵉ-v k (A [ σ ]ᵛ)) _ (occᵉ-v⁺ A r q)
    ... | inj₂ r = ∨-right (occᵉ-v k (A [ σ ]ᵛ)) _ (occᵉ-c⁺ C r q)
    occᵉ-v⁺ {i} {k} ([ ρ ] A) p q with ∨-true (occᵉ-r i ρ) _ p
    ... | inj₁ r = ∨-left  (occᵉ-r k (ρ [ σ ]ʳ)) _ (occᵉ-r⁺ ρ r q)
    ... | inj₂ r = ∨-right (occᵉ-r k (ρ [ σ ]ʳ)) _ (occᵉ-v⁺ A r q)

    occᵉ-c⁺ : ∀ {i k} → (C : OCType Ψ) → occᵉ-c i C ≡ true → occᵉ-e k (sE σ i) ≡ true
            → occᵉ-c k (C [ σ ]ᶜ) ≡ true
    occᵉ-c⁺ {i} {k} (A ‼ ε) p q with ∨-true (occᵉ-v i A) _ p
    ... | inj₁ r = ∨-left  (occᵉ-v k (A [ σ ]ᵛ)) _ (occᵉ-v⁺ A r q)
    ... | inj₂ r = ∨-right (occᵉ-v k (A [ σ ]ᵛ)) _ (occᵉ-e⁺ ε r q)

  -- an effect-grade unknown, through a resource-grade one

  occʳᵉ-r⁺ : ∀ {i k} → (ρ : RExp Ψ) → occʳ-r i ρ ≡ true → occᵉ-r k (sR σ i) ≡ true
           → occᵉ-r k (ρ [ σ ]ʳ) ≡ true
  occʳᵉ-r⁺ {i} {k} (rvar j)   p q =
    subst (λ x → occᵉ-r k (sR σ x) ≡ true) (true-dec (i ≟ᶠ j) p) q
  occʳᵉ-r⁺         (rconst c) () q
  occʳᵉ-r⁺ {i} {k} (a ·̂ᵣ b)   p q with ∨-true (occʳ-r i a) _ p
  ... | inj₁ r = ∨-left  (occᵉ-r k (a [ σ ]ʳ)) _ (occʳᵉ-r⁺ a r q)
  ... | inj₂ r = ∨-right (occᵉ-r k (a [ σ ]ʳ)) _ (occʳᵉ-r⁺ b r q)
  occʳᵉ-r⁺ {i} {k} (a ⊔̂ᵣ b)   p q with ∨-true (occʳ-r i a) _ p
  ... | inj₁ r = ∨-left  (occᵉ-r k (a [ σ ]ʳ)) _ (occʳᵉ-r⁺ a r q)
  ... | inj₂ r = ∨-right (occᵉ-r k (a [ σ ]ʳ)) _ (occʳᵉ-r⁺ b r q)
  occʳᵉ-r⁺         ∣ ε ∣̂ᵉ     () q

  mutual

    occʳᵉ-v⁺ : ∀ {i k} → (A : OVType Ψ) → occʳ-v i A ≡ true → occᵉ-r k (sR σ i) ≡ true
             → occᵉ-v k (A [ σ ]ᵛ) ≡ true
    occʳᵉ-v⁺         (tvar α)  () q
    occʳᵉ-v⁺         (Base b)  () q
    occʳᵉ-v⁺         Unit      () q
    occʳᵉ-v⁺         Bool      () q
    occʳᵉ-v⁺         Empty     () q
    occʳᵉ-v⁺ {i} {k} (A |×| B) p q with ∨-true (occʳ-v i A) _ p
    ... | inj₁ r = ∨-left  (occᵉ-v k (A [ σ ]ᵛ)) _ (occʳᵉ-v⁺ A r q)
    ... | inj₂ r = ∨-right (occᵉ-v k (A [ σ ]ᵛ)) _ (occʳᵉ-v⁺ B r q)
    occʳᵉ-v⁺ {i} {k} (A ⇒ C)   p q with ∨-true (occʳ-v i A) _ p
    ... | inj₁ r = ∨-left  (occᵉ-v k (A [ σ ]ᵛ)) _ (occʳᵉ-v⁺ A r q)
    ... | inj₂ r = ∨-right (occᵉ-v k (A [ σ ]ᵛ)) _ (occʳᵉ-c⁺ C r q)
    occʳᵉ-v⁺ {i} {k} ([ ρ ] A) p q with ∨-true (occʳ-r i ρ) _ p
    ... | inj₁ r = ∨-left  (occᵉ-r k (ρ [ σ ]ʳ)) _ (occʳᵉ-r⁺ ρ r q)
    ... | inj₂ r = ∨-right (occᵉ-r k (ρ [ σ ]ʳ)) _ (occʳᵉ-v⁺ A r q)

    occʳᵉ-c⁺ : ∀ {i k} → (C : OCType Ψ) → occʳ-c i C ≡ true → occᵉ-r k (sR σ i) ≡ true
             → occᵉ-c k (C [ σ ]ᶜ) ≡ true
    occʳᵉ-c⁺ {i} {k} (A ‼ ε) p q = ∨-left (occᵉ-v k (A [ σ ]ᵛ)) _ (occʳᵉ-v⁺ A p q)

  -- a resource-grade unknown, through a resource-grade one

  occʳ-r⁺ : ∀ {i k} → (ρ : RExp Ψ) → occʳ-r i ρ ≡ true → occʳ-r k (sR σ i) ≡ true
          → occʳ-r k (ρ [ σ ]ʳ) ≡ true
  occʳ-r⁺ {i} {k} (rvar j)   p q =
    subst (λ x → occʳ-r k (sR σ x) ≡ true) (true-dec (i ≟ᶠ j) p) q
  occʳ-r⁺         (rconst c) () q
  occʳ-r⁺ {i} {k} (a ·̂ᵣ b)   p q with ∨-true (occʳ-r i a) _ p
  ... | inj₁ r = ∨-left  (occʳ-r k (a [ σ ]ʳ)) _ (occʳ-r⁺ a r q)
  ... | inj₂ r = ∨-right (occʳ-r k (a [ σ ]ʳ)) _ (occʳ-r⁺ b r q)
  occʳ-r⁺ {i} {k} (a ⊔̂ᵣ b)   p q with ∨-true (occʳ-r i a) _ p
  ... | inj₁ r = ∨-left  (occʳ-r k (a [ σ ]ʳ)) _ (occʳ-r⁺ a r q)
  ... | inj₂ r = ∨-right (occʳ-r k (a [ σ ]ʳ)) _ (occʳ-r⁺ b r q)
  occʳ-r⁺         ∣ ε ∣̂ᵉ     () q

  mutual

    occʳ-v⁺ : ∀ {i k} → (A : OVType Ψ) → occʳ-v i A ≡ true → occʳ-r k (sR σ i) ≡ true
            → occʳ-v k (A [ σ ]ᵛ) ≡ true
    occʳ-v⁺         (tvar α)  () q
    occʳ-v⁺         (Base b)  () q
    occʳ-v⁺         Unit      () q
    occʳ-v⁺         Bool      () q
    occʳ-v⁺         Empty     () q
    occʳ-v⁺ {i} {k} (A |×| B) p q with ∨-true (occʳ-v i A) _ p
    ... | inj₁ r = ∨-left  (occʳ-v k (A [ σ ]ᵛ)) _ (occʳ-v⁺ A r q)
    ... | inj₂ r = ∨-right (occʳ-v k (A [ σ ]ᵛ)) _ (occʳ-v⁺ B r q)
    occʳ-v⁺ {i} {k} (A ⇒ C)   p q with ∨-true (occʳ-v i A) _ p
    ... | inj₁ r = ∨-left  (occʳ-v k (A [ σ ]ᵛ)) _ (occʳ-v⁺ A r q)
    ... | inj₂ r = ∨-right (occʳ-v k (A [ σ ]ᵛ)) _ (occʳ-c⁺ C r q)
    occʳ-v⁺ {i} {k} ([ ρ ] A) p q with ∨-true (occʳ-r i ρ) _ p
    ... | inj₁ r = ∨-left  (occʳ-r k (ρ [ σ ]ʳ)) _ (occʳ-r⁺ ρ r q)
    ... | inj₂ r = ∨-right (occʳ-r k (ρ [ σ ]ʳ)) _ (occʳ-v⁺ A r q)

    occʳ-c⁺ : ∀ {i k} → (C : OCType Ψ) → occʳ-c i C ≡ true → occʳ-r k (sR σ i) ≡ true
            → occʳ-c k (C [ σ ]ᶜ) ≡ true
    occʳ-c⁺ (A ‼ ε) p q = occʳ-v⁺ A p q

------------------------------------------------------------------------
-- Free in the images of a substitution, and of it followed by another

module _ {Θ Ψ Ψ'} (P : Subst Θ Ψ) (σ : Subst Ψ Ψ') where

  freeᵉ-⨟ : ∀ {i k} → freeᵉ i P ≡ true → occᵉ-e k (sE σ i) ≡ true
          → freeᵉ k (P ⨟ˢ σ) ≡ true
  freeᵉ-⨟ {i} {k} q s with ∨-true (anyᶠ (λ α → occᵉ-v i (sTy P α))) _ q
  ... | inj₁ qt with anyᶠ-true (λ α → occᵉ-v i (sTy P α)) qt
  ...   | α , r = ∨-left (anyᶠ (λ α' → occᵉ-v k (sTy (P ⨟ˢ σ) α'))) _
                    (anyᶠ-intro (λ α' → occᵉ-v k (sTy (P ⨟ˢ σ) α')) α
                                (occᵉ-v⁺ σ (sTy P α) r s))
  freeᵉ-⨟ {i} {k} q s | inj₂ q' with ∨-true (anyᶠ (λ j → occᵉ-r i (sR P j))) _ q'
  ...   | inj₁ qr with anyᶠ-true (λ j → occᵉ-r i (sR P j)) qr
  ...     | j , r = ∨-right (anyᶠ (λ α' → occᵉ-v k (sTy (P ⨟ˢ σ) α'))) _
                      (∨-left (anyᶠ (λ j' → occᵉ-r k (sR (P ⨟ˢ σ) j'))) _
                        (anyᶠ-intro (λ j' → occᵉ-r k (sR (P ⨟ˢ σ) j')) j
                                    (occᵉ-r⁺ σ (sR P j) r s)))
  freeᵉ-⨟ {i} {k} q s | inj₂ q' | inj₂ qe with anyᶠ-true (λ j → occᵉ-e i (sE P j)) qe
  ...     | j , r = ∨-right (anyᶠ (λ α' → occᵉ-v k (sTy (P ⨟ˢ σ) α'))) _
                      (∨-right (anyᶠ (λ j' → occᵉ-r k (sR (P ⨟ˢ σ) j'))) _
                        (anyᶠ-intro (λ j' → occᵉ-e k (sE (P ⨟ˢ σ) j')) j
                                    (occᵉ-e⁺ σ (sE P j) r s)))

  freeʳᵉ-⨟ : ∀ {i k} → freeʳ i P ≡ true → occᵉ-r k (sR σ i) ≡ true
           → freeᵉ k (P ⨟ˢ σ) ≡ true
  freeʳᵉ-⨟ {i} {k} q s with ∨-true (anyᶠ (λ α → occʳ-v i (sTy P α))) _ q
  ... | inj₁ qt with anyᶠ-true (λ α → occʳ-v i (sTy P α)) qt
  ...   | α , r = ∨-left (anyᶠ (λ α' → occᵉ-v k (sTy (P ⨟ˢ σ) α'))) _
                    (anyᶠ-intro (λ α' → occᵉ-v k (sTy (P ⨟ˢ σ) α')) α
                                (occʳᵉ-v⁺ σ (sTy P α) r s))
  freeʳᵉ-⨟ {i} {k} q s | inj₂ qr with anyᶠ-true (λ j → occʳ-r i (sR P j)) qr
  ...   | j , r = ∨-right (anyᶠ (λ α' → occᵉ-v k (sTy (P ⨟ˢ σ) α'))) _
                    (∨-left (anyᶠ (λ j' → occᵉ-r k (sR (P ⨟ˢ σ) j'))) _
                      (anyᶠ-intro (λ j' → occᵉ-r k (sR (P ⨟ˢ σ) j')) j
                                  (occʳᵉ-r⁺ σ (sR P j) r s)))

  freeʳ-⨟ : ∀ {i k} → freeʳ i P ≡ true → occʳ-r k (sR σ i) ≡ true
          → freeʳ k (P ⨟ˢ σ) ≡ true
  freeʳ-⨟ {i} {k} q s with ∨-true (anyᶠ (λ α → occʳ-v i (sTy P α))) _ q
  ... | inj₁ qt with anyᶠ-true (λ α → occʳ-v i (sTy P α)) qt
  ...   | α , r = ∨-left (anyᶠ (λ α' → occʳ-v k (sTy (P ⨟ˢ σ) α'))) _
                    (anyᶠ-intro (λ α' → occʳ-v k (sTy (P ⨟ˢ σ) α')) α
                                (occʳ-v⁺ σ (sTy P α) r s))
  freeʳ-⨟ {i} {k} q s | inj₂ qr with anyᶠ-true (λ j → occʳ-r i (sR P j)) qr
  ...   | j , r = ∨-right (anyᶠ (λ α' → occʳ-v k (sTy (P ⨟ˢ σ) α'))) _
                    (anyᶠ-intro (λ j' → occʳ-r k (sR (P ⨟ˢ σ) j')) j
                                (occʳ-r⁺ σ (sR P j) r s))

  -- An expression over the unknowns free in `P` is, substituted, one
  -- over those free in `P ⨟ σ`

  outerₑ-⨟ : ∀ {ε} → Outerₑ P ε → Outerₑ (P ⨟ˢ σ) (ε [ σ ]ᵉ)
  outerₑ-⨟ {ε} o q with occᵉ-e⁻ σ ε q
  ... | i , p , s = freeᵉ-⨟ (o p) s

  outerᵣ-⨟ : ∀ {ρ} → Outerᵣ P ρ → Outerᵣ (P ⨟ˢ σ) (ρ [ σ ]ʳ)
  outerᵣ-⨟ {ρ} (oe , or) = e , r
    where
      e : ∀ {k} → occᵉ-r k (ρ [ σ ]ʳ) ≡ true → freeᵉ k (P ⨟ˢ σ) ≡ true
      e q with occᵉ-r⁻ σ ρ q
      ... | inj₁ (i , p , s) = freeʳᵉ-⨟ (or p) s
      ... | inj₂ (i , p , s) = freeᵉ-⨟ (oe p) s

      r : ∀ {k} → occʳ-r k (ρ [ σ ]ʳ) ≡ true → freeʳ k (P ⨟ˢ σ) ≡ true
      r q with occʳ-r⁻ σ ρ q
      ... | i , p , s = freeʳ-⨟ (or p) s

------------------------------------------------------------------------
-- Pointwise equal substitutions have the same free unknowns, and a
-- substitution free in fewer unknowns makes fewer expressions outer

freeᵉ-≐ : ∀ {Θ Ψ} {P P' : Subst Θ Ψ} → P ≐ˢ P' → ∀ k → freeᵉ k P ≡ freeᵉ k P'
freeᵉ-≐ p k =
  cong₂ _∨_ (anyᶠ-cong (λ α → cong (occᵉ-v k) (≐ᵗ p α)))
            (cong₂ _∨_ (anyᶠ-cong (λ i → cong (occᵉ-r k) (≐ʳ p i)))
                       (anyᶠ-cong (λ i → cong (occᵉ-e k) (≐ᵉ p i))))

freeʳ-≐ : ∀ {Θ Ψ} {P P' : Subst Θ Ψ} → P ≐ˢ P' → ∀ k → freeʳ k P ≡ freeʳ k P'
freeʳ-≐ p k =
  cong₂ _∨_ (anyᶠ-cong (λ α → cong (occʳ-v k) (≐ᵗ p α)))
            (anyᶠ-cong (λ i → cong (occʳ-r k) (≐ʳ p i)))

record _⊆ᶠ_ {Θ Θ' Ψ} (P : Subst Θ Ψ) (P' : Subst Θ' Ψ) : Set where
  constructor mk⊆ᶠ
  field
    ⊆ᵉ : ∀ {k} → freeᵉ k P ≡ true → freeᵉ k P' ≡ true
    ⊆ʳ : ∀ {k} → freeʳ k P ≡ true → freeʳ k P' ≡ true

open _⊆ᶠ_ public

⊆ᶠ-refl : ∀ {Θ Ψ} {P : Subst Θ Ψ} → P ⊆ᶠ P
⊆ᶠ-refl = mk⊆ᶠ (λ q → q) (λ q → q)

⊆ᶠ-trans : ∀ {Θ Θ' Θ'' Ψ} {P : Subst Θ Ψ} {P' : Subst Θ' Ψ} {P'' : Subst Θ'' Ψ}
         → P ⊆ᶠ P' → P' ⊆ᶠ P'' → P ⊆ᶠ P''
⊆ᶠ-trans a b = mk⊆ᶠ (λ q → ⊆ᵉ b (⊆ᵉ a q)) (λ q → ⊆ʳ b (⊆ʳ a q))

≐→⊆ᶠ : ∀ {Θ Ψ} {P P' : Subst Θ Ψ} → P ≐ˢ P' → P ⊆ᶠ P'
≐→⊆ᶠ {P = P} {P'} p =
  mk⊆ᶠ (λ {k} q → trans (sym (freeᵉ-≐ p k)) q) (λ {k} q → trans (sym (freeʳ-≐ p k)) q)

outerₑ-⊆ : ∀ {Θ Θ' Ψ} {P : Subst Θ Ψ} {P' : Subst Θ' Ψ} {ε : EExp Ψ}
         → P ⊆ᶠ P' → Outerₑ P ε → Outerₑ P' ε
outerₑ-⊆ i o q = ⊆ᵉ i (o q)

outerᵣ-⊆ : ∀ {Θ Θ' Ψ} {P : Subst Θ Ψ} {P' : Subst Θ' Ψ} {ρ : RExp Ψ}
         → P ⊆ᶠ P' → Outerᵣ P ρ → Outerᵣ P' ρ
outerᵣ-⊆ i (oe , or) = (λ q → ⊆ᵉ i (oe q)) , (λ q → ⊆ʳ i (or q))

-- A substitution each of whose images is one of another's, or has no
-- effect-grade unknown, is free in fewer unknowns

Closedₑ : ∀ {Ψ} → EExp Ψ → Set
Closedₑ {Ψ} ε = ∀ (k : EVar Ψ) → occᵉ-e k ε ≡ false

⊆ᶠ-images : ∀ {Θ Θ' Ψ} {P : Subst Θ Ψ} {P' : Subst Θ' Ψ}
          → (∀ α → Σ[ β ∈ TyVar Θ' ] (sTy P α ≡ sTy P' β))
          → (∀ i → Σ[ j ∈ RVar Θ' ] (sR P i ≡ sR P' j))
          → (∀ i → (Σ[ j ∈ EVar Θ' ] (sE P i ≡ sE P' j)) ⊎ Closedₑ (sE P i))
          → P ⊆ᶠ P'
⊆ᶠ-images {P = P} {P'} ft fr fe = mk⊆ᶠ e r
  where
    e : ∀ {k} → freeᵉ k P ≡ true → freeᵉ k P' ≡ true
    e {k} q with ∨-true (anyᶠ (λ α → occᵉ-v k (sTy P α))) _ q
    ... | inj₁ qt with anyᶠ-true (λ α → occᵉ-v k (sTy P α)) qt
    ...   | α , r with ft α
    ...     | β , eq =
              ∨-left (anyᶠ (λ β' → occᵉ-v k (sTy P' β'))) _
                (anyᶠ-intro (λ β' → occᵉ-v k (sTy P' β')) β
                            (subst (λ X → occᵉ-v k X ≡ true) eq r))
    e {k} q | inj₂ q' with ∨-true (anyᶠ (λ i → occᵉ-r k (sR P i))) _ q'
    ...   | inj₁ qr with anyᶠ-true (λ i → occᵉ-r k (sR P i)) qr
    ...     | i , r with fr i
    ...       | j , eq =
                ∨-right (anyᶠ (λ β' → occᵉ-v k (sTy P' β'))) _
                  (∨-left (anyᶠ (λ j' → occᵉ-r k (sR P' j'))) _
                    (anyᶠ-intro (λ j' → occᵉ-r k (sR P' j')) j
                                (subst (λ X → occᵉ-r k X ≡ true) eq r)))
    e {k} q | inj₂ q' | inj₂ qe with anyᶠ-true (λ i → occᵉ-e k (sE P i)) qe
    ...     | i , r with fe i
    ...       | inj₁ (j , eq) =
                ∨-right (anyᶠ (λ β' → occᵉ-v k (sTy P' β'))) _
                  (∨-right (anyᶠ (λ j' → occᵉ-r k (sR P' j'))) _
                    (anyᶠ-intro (λ j' → occᵉ-e k (sE P' j')) j
                                (subst (λ X → occᵉ-e k X ≡ true) eq r)))
    ...       | inj₂ cl with trans (sym r) (cl k)
    ...         | ()

    r : ∀ {k} → freeʳ k P ≡ true → freeʳ k P' ≡ true
    r {k} q with ∨-true (anyᶠ (λ α → occʳ-v k (sTy P α))) _ q
    ... | inj₁ qt with anyᶠ-true (λ α → occʳ-v k (sTy P α)) qt
    ...   | α , r' with ft α
    ...     | β , eq =
              ∨-left (anyᶠ (λ β' → occʳ-v k (sTy P' β'))) _
                (anyᶠ-intro (λ β' → occʳ-v k (sTy P' β')) β
                            (subst (λ X → occʳ-v k X ≡ true) eq r'))
    r {k} q | inj₂ qr with anyᶠ-true (λ i → occʳ-r k (sR P i)) qr
    ...   | i , r' with fr i
    ...     | j , eq =
              ∨-right (anyᶠ (λ β' → occʳ-v k (sTy P' β'))) _
                (anyᶠ-intro (λ j' → occʳ-r k (sR P' j')) j
                            (subst (λ X → occʳ-r k X ≡ true) eq r'))

-- Free in an extension: in the new image, or in the old ones

module _ {Θ Ψ} (X : Subst Θ Ψ) (e : EExp Ψ) where

  freeᵉ-,ᵉ⁻ : ∀ {k} → freeᵉ k (X ,ᵉ e) ≡ true → (occᵉ-e k e ≡ true) ⊎ (freeᵉ k X ≡ true)
  freeᵉ-,ᵉ⁻ {k} q with ∨-true (anyᶠ (λ α → occᵉ-v k (sTy X α))) _ q
  ... | inj₁ r = inj₂ (∨-left (anyᶠ (λ α → occᵉ-v k (sTy X α))) _ r)
  ... | inj₂ q' with ∨-true (anyᶠ (λ i → occᵉ-r k (sR X i))) _ q'
  ...   | inj₁ r = inj₂ (∨-right (anyᶠ (λ α → occᵉ-v k (sTy X α))) _
                          (∨-left (anyᶠ (λ i → occᵉ-r k (sR X i))) _ r))
  ...   | inj₂ q'' with ∨-true (occᵉ-e k e) _ q''
  ...     | inj₁ r = inj₁ r
  ...     | inj₂ r = inj₂ (∨-right (anyᶠ (λ α → occᵉ-v k (sTy X α))) _
                            (∨-right (anyᶠ (λ i → occᵉ-r k (sR X i))) _ r))

  freeᵉ-,ᵉ⁺ : ∀ {k} → freeᵉ k X ≡ true → freeᵉ k (X ,ᵉ e) ≡ true
  freeᵉ-,ᵉ⁺ {k} q with ∨-true (anyᶠ (λ α → occᵉ-v k (sTy X α))) _ q
  ... | inj₁ r = ∨-left (anyᶠ (λ α → occᵉ-v k (sTy X α))) _ r
  ... | inj₂ q' with ∨-true (anyᶠ (λ i → occᵉ-r k (sR X i))) _ q'
  ...   | inj₁ r = ∨-right (anyᶠ (λ α → occᵉ-v k (sTy X α))) _
                     (∨-left (anyᶠ (λ i → occᵉ-r k (sR X i))) _ r)
  ...   | inj₂ r = ∨-right (anyᶠ (λ α → occᵉ-v k (sTy X α))) _
                     (∨-right (anyᶠ (λ i → occᵉ-r k (sR X i))) _
                       (∨-right (occᵉ-e k e) _ r))

  freeᵉ-,ᵉ-new : ∀ {k} → occᵉ-e k e ≡ true → freeᵉ k (X ,ᵉ e) ≡ true
  freeᵉ-,ᵉ-new {k} r = ∨-right (anyᶠ (λ α → occᵉ-v k (sTy X α))) _
                         (∨-right (anyᶠ (λ i → occᵉ-r k (sR X i))) _
                           (∨-left (occᵉ-e k e) _ r))

-- Free in a substitution followed by another: through a type variable,
-- or through a grade unknown free in the first

module _ {Θ Ψ Ψ'} (P : Subst Θ Ψ) (σ : Subst Ψ Ψ') where

  FreeVia : EVar Ψ' → Set
  FreeVia k = (Σ[ α ∈ TyVar Ψ ] (occᵉ-v k (sTy σ α) ≡ true))
            ⊎ ((Σ[ i ∈ RVar Ψ ] ((freeʳ i P ≡ true) × (occᵉ-r k (sR σ i) ≡ true)))
            ⊎ (Σ[ i ∈ EVar Ψ ] ((freeᵉ i P ≡ true) × (occᵉ-e k (sE σ i) ≡ true))))

  private
    viaV : ∀ {k} → (A : OVType Ψ) → (∀ {i} → occʳ-v i A ≡ true → freeʳ i P ≡ true)
         → (∀ {i} → occᵉ-v i A ≡ true → freeᵉ i P ≡ true) → OccVE σ k A → FreeVia k
    viaV A fr fe (inj₁ (α , p , q))        = inj₁ (α , q)
    viaV A fr fe (inj₂ (inj₁ (i , p , q))) = inj₂ (inj₁ (i , fr p , q))
    viaV A fr fe (inj₂ (inj₂ (i , p , q))) = inj₂ (inj₂ (i , fe p , q))

  freeᵉ-⨟⁻ : ∀ {k} → freeᵉ k (P ⨟ˢ σ) ≡ true → FreeVia k
  freeᵉ-⨟⁻ {k} q with ∨-true (anyᶠ (λ α → occᵉ-v k (sTy (P ⨟ˢ σ) α))) _ q
  ... | inj₁ qt with anyᶠ-true (λ α → occᵉ-v k (sTy (P ⨟ˢ σ) α)) qt
  ...   | α , r =
          viaV (sTy P α)
               (λ {i} p → ∨-left (anyᶠ (λ α' → occʳ-v i (sTy P α'))) _
                            (anyᶠ-intro (λ α' → occʳ-v i (sTy P α')) α p))
               (λ {i} p → ∨-left (anyᶠ (λ α' → occᵉ-v i (sTy P α'))) _
                            (anyᶠ-intro (λ α' → occᵉ-v i (sTy P α')) α p))
               (occᵉ-v⁻ σ (sTy P α) r)
  freeᵉ-⨟⁻ {k} q | inj₂ q' with ∨-true (anyᶠ (λ j → occᵉ-r k (sR (P ⨟ˢ σ) j))) _ q'
  ...   | inj₁ qr with anyᶠ-true (λ j → occᵉ-r k (sR (P ⨟ˢ σ) j)) qr
  ...     | j , r with occᵉ-r⁻ σ (sR P j) r
  ...       | inj₁ (i , p , s') =
              inj₂ (inj₁ (i , ∨-right (anyᶠ (λ α' → occʳ-v i (sTy P α'))) _
                                (anyᶠ-intro (λ j' → occʳ-r i (sR P j')) j p) , s'))
  ...       | inj₂ (i , p , s') =
              inj₂ (inj₂ (i , ∨-right (anyᶠ (λ α' → occᵉ-v i (sTy P α'))) _
                                (∨-left (anyᶠ (λ j' → occᵉ-r i (sR P j'))) _
                                  (anyᶠ-intro (λ j' → occᵉ-r i (sR P j')) j p)) , s'))
  freeᵉ-⨟⁻ {k} q | inj₂ q' | inj₂ qe with anyᶠ-true (λ j → occᵉ-e k (sE (P ⨟ˢ σ) j)) qe
  ...     | j , r with occᵉ-e⁻ σ (sE P j) r
  ...       | i , p , s' =
              inj₂ (inj₂ (i , ∨-right (anyᶠ (λ α' → occᵉ-v i (sTy P α'))) _
                                (∨-right (anyᶠ (λ j' → occᵉ-r i (sR P j'))) _
                                  (anyᶠ-intro (λ j' → occᵉ-e i (sE P j')) j p)) , s'))

  FreeViaʳ : RVar Ψ' → Set
  FreeViaʳ k = (Σ[ α ∈ TyVar Ψ ] (occʳ-v k (sTy σ α) ≡ true))
             ⊎ (Σ[ i ∈ RVar Ψ ] ((freeʳ i P ≡ true) × (occʳ-r k (sR σ i) ≡ true)))

  freeʳ-⨟⁻ : ∀ {k} → freeʳ k (P ⨟ˢ σ) ≡ true → FreeViaʳ k
  freeʳ-⨟⁻ {k} q with ∨-true (anyᶠ (λ α → occʳ-v k (sTy (P ⨟ˢ σ) α))) _ q
  ... | inj₁ qt with anyᶠ-true (λ α → occʳ-v k (sTy (P ⨟ˢ σ) α)) qt
  ...   | α , r with occʳ-v⁻ σ (sTy P α) r
  ...     | inj₁ (β , p , s') = inj₁ (β , s')
  ...     | inj₂ (i , p , s') =
            inj₂ (i , ∨-left (anyᶠ (λ α' → occʳ-v i (sTy P α'))) _
                        (anyᶠ-intro (λ α' → occʳ-v i (sTy P α')) α p) , s')
  freeʳ-⨟⁻ {k} q | inj₂ qr with anyᶠ-true (λ j → occʳ-r k (sR (P ⨟ˢ σ) j)) qr
  ...   | j , r with occʳ-r⁻ σ (sR P j) r
  ...     | i , p , s' =
            inj₂ (i , ∨-right (anyᶠ (λ α' → occʳ-v i (sTy P α'))) _
                        (anyᶠ-intro (λ j' → occʳ-r i (sR P j')) j p) , s')

-- Followed by a substitution sending type variables to type variables,
-- fewer free unknowns stay fewer

⊆ᶠ-⨟ : ∀ {Θ Θ' Ψ Ψ'} {P : Subst Θ Ψ} {P' : Subst Θ' Ψ} → P ⊆ᶠ P'
     → (σ : Subst Ψ Ψ') → (∀ α → Σ[ β ∈ TyVar Ψ' ] (sTy σ α ≡ tvar β))
     → (P ⨟ˢ σ) ⊆ᶠ (P' ⨟ˢ σ)
⊆ᶠ-⨟ {P = P} {P'} inc σ ft = mk⊆ᶠ e r
  where
    e : ∀ {k} → freeᵉ k (P ⨟ˢ σ) ≡ true → freeᵉ k (P' ⨟ˢ σ) ≡ true
    e q with freeᵉ-⨟⁻ P σ q
    ... | inj₁ (α , r) with sTy σ α | ft α
    ...   | .(tvar β) | β , refl with r
    ...     | ()
    e q | inj₂ (inj₁ (i , p , s')) = freeʳᵉ-⨟ P' σ (⊆ʳ inc p) s'
    e q | inj₂ (inj₂ (i , p , s')) = freeᵉ-⨟ P' σ (⊆ᵉ inc p) s'

    r : ∀ {k} → freeʳ k (P ⨟ˢ σ) ≡ true → freeʳ k (P' ⨟ˢ σ) ≡ true
    r q with freeʳ-⨟⁻ P σ q
    ... | inj₁ (α , r') with sTy σ α | ft α
    ...   | .(tvar β) | β , refl with r'
    ...     | ()
    r q | inj₂ (i , p , s') = freeʳ-⨟ P' σ (⊆ʳ inc p) s'

-- Lifting over a rigid

↑ᵉ-≐ : ∀ {Θ Ψ} → (P : Subst Θ Ψ) → (P ↑ᵉ) ≐ˢ ((P ⨟ˢ wkˢᵉ) ,ᵉ evar (newᵉ {Ψ}))
↑ᵉ-≐ P = mk≐ˢ (λ α → sym (wkˢᵉ-v (sTy P α))) (λ i → sym (wkˢᵉ-r (sR P i)))
              (λ { zero → refl ; (suc i) → sym (wkˢᵉ-e (sE P i)) })

⊆ᶠ-↑ᵉ : ∀ {Θ Θ' Ψ} {P : Subst Θ Ψ} {P' : Subst Θ' Ψ} → P ⊆ᶠ P' → (P ↑ᵉ) ⊆ᶠ (P' ↑ᵉ)
⊆ᶠ-↑ᵉ {Ψ = Ψ} {P} {P'} inc =
  ⊆ᶠ-trans (≐→⊆ᶠ (↑ᵉ-≐ P)) (⊆ᶠ-trans (mk⊆ᶠ e r) (≐→⊆ᶠ (≐ˢ-sym (↑ᵉ-≐ P'))))
  where
    inc' = ⊆ᶠ-⨟ inc wkˢᵉ (λ α → α , refl)
    z = evar (newᵉ {Ψ})

    e : ∀ {k} → freeᵉ k ((P ⨟ˢ wkˢᵉ) ,ᵉ z) ≡ true → freeᵉ k ((P' ⨟ˢ wkˢᵉ) ,ᵉ z) ≡ true
    e q with freeᵉ-,ᵉ⁻ (P ⨟ˢ wkˢᵉ) z q
    ... | inj₁ r = freeᵉ-,ᵉ-new (P' ⨟ˢ wkˢᵉ) z r
    ... | inj₂ r = freeᵉ-,ᵉ⁺ (P' ⨟ˢ wkˢᵉ) z (⊆ᵉ inc' r)

    r : ∀ {k} → freeʳ k ((P ⨟ˢ wkˢᵉ) ,ᵉ z) ≡ true → freeʳ k ((P' ⨟ˢ wkˢᵉ) ,ᵉ z) ≡ true
    r q = ⊆ʳ inc' q

⊆ᶠ-↑ᵉⁿ : ∀ {Θ Θ' Ψ} {P : Subst Θ Ψ} {P' : Subst Θ' Ψ} → (n : ℕ) → P ⊆ᶠ P'
       → (P ↑ᵉⁿ n) ⊆ᶠ (P' ↑ᵉⁿ n)
⊆ᶠ-↑ᵉⁿ nzero    inc = inc
⊆ᶠ-↑ᵉⁿ (nsuc n) inc = ⊆ᶠ-↑ᵉⁿ n (⊆ᶠ-↑ᵉ inc)

-- The rigid sent to a closed grade: no new free unknown

↑ᵉ-κ-⊆ᶠ : ∀ {Θ Ψ} → (P : Subst Θ Ψ) → (c : E) → ((P ↑ᵉ) ⨟ˢ κ⟨ econst c ⟩) ⊆ᶠ P
↑ᵉ-κ-⊆ᶠ P c =
  ⊆ᶠ-images (λ α → α , trans (cong (_[ κ⟨ econst c ⟩ ]ᵛ) (sym (wkˢᵉ-v (sTy P α))))
                             (κ-wkᵛ (econst c) (sTy P α)))
            (λ i → i , trans (cong (_[ κ⟨ econst c ⟩ ]ʳ) (sym (wkˢᵉ-r (sR P i))))
                             (κ-wkʳ (econst c) (sR P i)))
            (λ { zero    → inj₂ (λ k → refl)
               ; (suc i) → inj₁ (i , trans (cong (_[ κ⟨ econst c ⟩ ]ᵉ) (sym (wkˢᵉ-e (sE P i))))
                                           (κ-wkᵉ (econst c) (sE P i))) })

------------------------------------------------------------------------
-- Good sides: a whole unknown, or an expression over the unknowns free
-- in the images of `P`

data Goodₑ {Θ Ψ} (P : Subst Θ Ψ) : EExp Ψ → Set where
  whole : ∀ k → Goodₑ P (evar k)
  outer : ∀ {ε} → Outerₑ P ε → Goodₑ P ε

data Goodᵣ {Θ Ψ} (P : Subst Θ Ψ) : RExp Ψ → Set where
  whole : ∀ k → Goodᵣ P (rvar k)
  outer : ∀ {ρ} → Outerᵣ P ρ → Goodᵣ P ρ

-- Every grade of a type good: its latent effects and its box grades

mutual

  TyGoodᵛ : ∀ {Θ Ψ} → Subst Θ Ψ → OVType Ψ → Set
  TyGoodᵛ P (tvar α)  = ⊤
  TyGoodᵛ P (Base b)  = ⊤
  TyGoodᵛ P Unit      = ⊤
  TyGoodᵛ P Bool      = ⊤
  TyGoodᵛ P Empty     = ⊤
  TyGoodᵛ P (A |×| B) = TyGoodᵛ P A × TyGoodᵛ P B
  TyGoodᵛ P (A ⇒ C)   = TyGoodᵛ P A × TyGoodᶜ P C
  TyGoodᵛ P ([ ρ ] A) = Goodᵣ P ρ × TyGoodᵛ P A

  TyGoodᶜ : ∀ {Θ Ψ} → Subst Θ Ψ → OCType Ψ → Set
  TyGoodᶜ P (A ‼ ε) = TyGoodᵛ P A × Goodₑ P ε

-- A good substitution: every image good

record GV {Θ Ψ Ψ'} (P : Subst Θ Ψ') (σ : Subst Ψ Ψ') : Set where
  constructor mkGV
  field
    gvᵗ : ∀ α → TyGoodᵛ P (sTy σ α)
    gvʳ : ∀ i → Goodᵣ P (sR σ i)
    gvᵉ : ∀ i → Goodₑ P (sE σ i)

open GV public

-- Fewer free unknowns, fewer good sides

module _ {Θ Θ' Ψ} {P : Subst Θ Ψ} {P' : Subst Θ' Ψ} (i : P ⊆ᶠ P') where

  goodₑ-⊆ : ∀ {ε} → Goodₑ P ε → Goodₑ P' ε
  goodₑ-⊆     (whole k) = whole k
  goodₑ-⊆ {ε} (outer o) = outer (outerₑ-⊆ {ε = ε} i o)

  goodᵣ-⊆ : ∀ {ρ} → Goodᵣ P ρ → Goodᵣ P' ρ
  goodᵣ-⊆     (whole k) = whole k
  goodᵣ-⊆ {ρ} (outer o) = outer (outerᵣ-⊆ {ρ = ρ} i o)

  mutual

    tygoodᵛ-⊆ : ∀ A → TyGoodᵛ P A → TyGoodᵛ P' A
    tygoodᵛ-⊆ (tvar α)  g       = tt
    tygoodᵛ-⊆ (Base b)  g       = tt
    tygoodᵛ-⊆ Unit      g       = tt
    tygoodᵛ-⊆ Bool      g       = tt
    tygoodᵛ-⊆ Empty     g       = tt
    tygoodᵛ-⊆ (A |×| B) (g , h) = tygoodᵛ-⊆ A g , tygoodᵛ-⊆ B h
    tygoodᵛ-⊆ (A ⇒ C)   (g , h) = tygoodᵛ-⊆ A g , tygoodᶜ-⊆ C h
    tygoodᵛ-⊆ ([ ρ ] A) (g , h) = goodᵣ-⊆ g , tygoodᵛ-⊆ A h

    tygoodᶜ-⊆ : ∀ C → TyGoodᶜ P C → TyGoodᶜ P' C
    tygoodᶜ-⊆ (A ‼ ε) (g , h) = tygoodᵛ-⊆ A g , goodₑ-⊆ h

  GV-⊆ : ∀ {Ψ₀} {σ : Subst Ψ₀ Ψ} → GV P σ → GV P' σ
  GV-⊆ {σ = σ} g = mkGV (λ α → tygoodᵛ-⊆ (sTy σ α) (gvᵗ g α))
                        (λ j → goodᵣ-⊆ (gvʳ g j)) (λ j → goodₑ-⊆ (gvᵉ g j))

-- Good sides stay good under a good substitution

module _ {Θ Ψ Ψ'} {P : Subst Θ Ψ} {σ : Subst Ψ Ψ'} (g : GV (P ⨟ˢ σ) σ) where

  goodₑ-⨟ : ∀ {ε} → Goodₑ P ε → Goodₑ (P ⨟ˢ σ) (ε [ σ ]ᵉ)
  goodₑ-⨟     (whole k) = gvᵉ g k
  goodₑ-⨟ {ε} (outer o) = outer (outerₑ-⨟ P σ {ε} o)

  goodᵣ-⨟ : ∀ {ρ} → Goodᵣ P ρ → Goodᵣ (P ⨟ˢ σ) (ρ [ σ ]ʳ)
  goodᵣ-⨟     (whole k) = gvʳ g k
  goodᵣ-⨟ {ρ} (outer o) = outer (outerᵣ-⨟ P σ {ρ} o)

  mutual

    tygoodᵛ-⨟ : ∀ A → TyGoodᵛ P A → TyGoodᵛ (P ⨟ˢ σ) (A [ σ ]ᵛ)
    tygoodᵛ-⨟ (tvar α)  h       = gvᵗ g α
    tygoodᵛ-⨟ (Base b)  h       = tt
    tygoodᵛ-⨟ Unit      h       = tt
    tygoodᵛ-⨟ Bool      h       = tt
    tygoodᵛ-⨟ Empty     h       = tt
    tygoodᵛ-⨟ (A |×| B) (h , k) = tygoodᵛ-⨟ A h , tygoodᵛ-⨟ B k
    tygoodᵛ-⨟ (A ⇒ C)   (h , k) = tygoodᵛ-⨟ A h , tygoodᶜ-⨟ C k
    tygoodᵛ-⨟ ([ ρ ] A) (h , k) = goodᵣ-⨟ h , tygoodᵛ-⨟ A k

    tygoodᶜ-⨟ : ∀ C → TyGoodᶜ P C → TyGoodᶜ (P ⨟ˢ σ) (C [ σ ]ᶜ)
    tygoodᶜ-⨟ (A ‼ ε) (h , k) = tygoodᵛ-⨟ A h , goodₑ-⨟ k

-- Good substitutions compose

GV-⨟ : ∀ {Θ Ψ₀ Ψ Ψ'} {P : Subst Θ Ψ} {σ : Subst Ψ₀ Ψ} {τ : Subst Ψ Ψ'}
     → GV P σ → GV (P ⨟ˢ τ) τ → GV (P ⨟ˢ τ) (σ ⨟ˢ τ)
GV-⨟ {P = P} {σ = σ} g h =
  mkGV (λ α → tygoodᵛ-⨟ {P = P} h (sTy σ α) (gvᵗ g α)) (λ i → goodᵣ-⨟ {P = P} h (gvʳ g i))
       (λ i → goodₑ-⨟ {P = P} h (gvᵉ g i))

-- A renaming is good

GV-ren : ∀ {Θ Ψ Ψ'} {P : Subst Θ Ψ'} {σ : Subst Ψ Ψ'}
       → (∀ α → Σ[ β ∈ TyVar Ψ' ] (sTy σ α ≡ tvar β))
       → (∀ i → Σ[ j ∈ RVar Ψ' ] (sR σ i ≡ rvar j))
       → (∀ i → Σ[ j ∈ EVar Ψ' ] (sE σ i ≡ evar j))
       → GV P σ
GV-ren {P = P} {σ} ft fr fe = mkGV t r e
  where
    t : ∀ α → TyGoodᵛ P (sTy σ α)
    t α with sTy σ α | ft α
    ... | .(tvar β) | β , refl = tt

    r : ∀ i → Goodᵣ P (sR σ i)
    r i with sR σ i | fr i
    ... | .(rvar j) | j , refl = whole j

    e : ∀ i → Goodₑ P (sE σ i)
    e i with sE σ i | fe i
    ... | .(evar j) | j , refl = whole j

GV-wkᵗ : ∀ {Θ Ψ} {P : Subst Θ (Ψ +ty)} → GV P (wkˢᵗ {Ψ})
GV-wkᵗ {Ψ = Ψ} = GV-ren (λ α → wkᵗ-tv Ψ α , refl) (λ i → i , refl) (λ i → i , refl)

GV-wkʳ : ∀ {Θ Ψ} {P : Subst Θ (Ψ +r)} → GV P (wkˢʳ {Ψ})
GV-wkʳ {Ψ = Ψ} = GV-ren (λ α → α , refl) (λ i → wkʳ-rv Ψ i , refl) (λ i → i , refl)

GV-wkᵉ : ∀ {Θ Ψ} {P : Subst Θ (Ψ +e)} → GV P (wkˢᵉ {Ψ})
GV-wkᵉ {Ψ = Ψ} = GV-ren (λ α → α , refl) (λ i → i , refl) (λ i → wkᵉ-ev Ψ i , refl)

GV-id : ∀ {Θ Ψ} {P : Subst Θ Ψ} → GV P (idˢ {Ψ})
GV-id = GV-ren (λ α → α , refl) (λ i → i , refl) (λ i → i , refl)

-- Weakening under a lift, with the new variable sent to a closed grade

GV-κ : ∀ {Θ Ψ} {P : Subst Θ Ψ} → (c : E) → GV P (κ⟨_⟩ {Ψ} (econst c))
GV-κ {Ψ = Ψ} {P} c = mkGV (λ α → tt) (λ i → whole i) e
  where
    e : ∀ i → Goodₑ P (sE (κ⟨_⟩ {Ψ} (econst c)) i)
    e zero    = outer (λ ())
    e (suc i) = whole i

module _ {Θ Ψ} (X : Subst Θ Ψ) where

  private
    κ = κ⟨_⟩ {Ψ} ûₑ
    back = ↑ᵉ-κ-⊆ᶠ X uₑ

    wk-κᵉ : (ε : EExp Ψ) → wkᵉ-e ε [ κ ]ᵉ ≡ ε
    wk-κᵉ ε = trans (cong (_[ κ ]ᵉ) (sym (wkˢᵉ-e ε))) (κ-wkᵉ ûₑ ε)

    wk-κʳ : (ρ : RExp Ψ) → wkᵉ-r ρ [ κ ]ʳ ≡ ρ
    wk-κʳ ρ = trans (cong (_[ κ ]ʳ) (sym (wkˢᵉ-r ρ))) (κ-wkʳ ûₑ ρ)

    wk-κᵛ : (A : OVType Ψ) → wkᵉ-v A [ κ ]ᵛ ≡ A
    wk-κᵛ A = trans (cong (_[ κ ]ᵛ) (sym (wkˢᵉ-v A))) (κ-wkᵛ ûₑ A)

  unwkₑ : ∀ {ε} → Goodₑ (X ↑ᵉ) (wkᵉ-e ε) → Goodₑ X ε
  unwkₑ {ε} g =
    goodₑ-⊆ back (subst (Goodₑ ((X ↑ᵉ) ⨟ˢ κ)) (wk-κᵉ ε) (goodₑ-⨟ {P = X ↑ᵉ} (GV-κ uₑ) g))

  unwkᵣ : ∀ {ρ} → Goodᵣ (X ↑ᵉ) (wkᵉ-r ρ) → Goodᵣ X ρ
  unwkᵣ {ρ} g =
    goodᵣ-⊆ back (subst (Goodᵣ ((X ↑ᵉ) ⨟ˢ κ)) (wk-κʳ ρ) (goodᵣ-⨟ {P = X ↑ᵉ} (GV-κ uₑ) g))

  unwkᵛ : ∀ A → TyGoodᵛ (X ↑ᵉ) (wkᵉ-v A) → TyGoodᵛ X A
  unwkᵛ A g =
    tygoodᵛ-⊆ back A (subst (TyGoodᵛ ((X ↑ᵉ) ⨟ˢ κ)) (wk-κᵛ A)
                            (tygoodᵛ-⨟ {P = X ↑ᵉ} (GV-κ uₑ) (wkᵉ-v A) g))

-- Good substitutions under the three lifts, and restricted to the old
-- variables

GV-≐ : ∀ {Θ Ψ Ψ'} {P : Subst Θ Ψ'} {σ σ' : Subst Ψ Ψ'} → σ ≐ˢ σ' → GV P σ → GV P σ'
GV-≐ {P = P} p g = mkGV (λ α → subst (TyGoodᵛ P) (≐ᵗ p α) (gvᵗ g α))
                        (λ i → subst (Goodᵣ P) (≐ʳ p i) (gvʳ g i))
                        (λ i → subst (Goodₑ P) (≐ᵉ p i) (gvᵉ g i))

module _ {Θ Ψ Ψ'} {P : Subst Θ Ψ'} {σ : Subst Ψ Ψ'} (g : GV P σ) where

  GV-↑ᵗ : GV (P ⨟ˢ wkˢᵗ) (σ ↑ᵗ)
  GV-↑ᵗ = mkGV t (λ i → subst (Goodᵣ (P ⨟ˢ wkˢᵗ)) (wkˢᵗ-r (sR σ i)) (goodᵣ-⨟ {P = P} GV-wkᵗ (gvʳ g i)))
                 (λ i → subst (Goodₑ (P ⨟ˢ wkˢᵗ)) (wkˢᵗ-e (sE σ i)) (goodₑ-⨟ {P = P} GV-wkᵗ (gvᵉ g i)))
    where
      t : ∀ α → TyGoodᵛ (P ⨟ˢ wkˢᵗ) (sTy (σ ↑ᵗ) α)
      t zero    = tt
      t (suc α) = subst (TyGoodᵛ (P ⨟ˢ wkˢᵗ)) (wkˢᵗ-v (sTy σ α))
                        (tygoodᵛ-⨟ {P = P} GV-wkᵗ (sTy σ α) (gvᵗ g α))

  GV-↑ʳ : GV (P ⨟ˢ wkˢʳ) (σ ↑ʳ)
  GV-↑ʳ = mkGV (λ α → subst (TyGoodᵛ (P ⨟ˢ wkˢʳ)) (wkˢʳ-v (sTy σ α))
                            (tygoodᵛ-⨟ {P = P} GV-wkʳ (sTy σ α) (gvᵗ g α)))
               r
               (λ i → subst (Goodₑ (P ⨟ˢ wkˢʳ)) (wkˢʳ-e (sE σ i)) (goodₑ-⨟ {P = P} GV-wkʳ (gvᵉ g i)))
    where
      r : ∀ i → Goodᵣ (P ⨟ˢ wkˢʳ) (sR (σ ↑ʳ) i)
      r zero    = whole zero
      r (suc i) = subst (Goodᵣ (P ⨟ˢ wkˢʳ)) (wkˢʳ-r (sR σ i)) (goodᵣ-⨟ {P = P} GV-wkʳ (gvʳ g i))

  GV-↑ᵉ : GV (P ⨟ˢ wkˢᵉ) (σ ↑ᵉ)
  GV-↑ᵉ = mkGV (λ α → subst (TyGoodᵛ (P ⨟ˢ wkˢᵉ)) (wkˢᵉ-v (sTy σ α))
                            (tygoodᵛ-⨟ {P = P} GV-wkᵉ (sTy σ α) (gvᵗ g α)))
               (λ i → subst (Goodᵣ (P ⨟ˢ wkˢᵉ)) (wkˢᵉ-r (sR σ i)) (goodᵣ-⨟ {P = P} GV-wkᵉ (gvʳ g i)))
               e
    where
      e : ∀ i → Goodₑ (P ⨟ˢ wkˢᵉ) (sE (σ ↑ᵉ) i)
      e zero    = whole zero
      e (suc i) = subst (Goodₑ (P ⨟ˢ wkˢᵉ)) (wkˢᵉ-e (sE σ i)) (goodₑ-⨟ {P = P} GV-wkᵉ (gvᵉ g i))

module _ {Θ Ψ Ψ'} {P : Subst Θ Ψ'} where

  GV-wkᵗ⨟ : ∀ {σ : Subst (Ψ +ty) Ψ'} → GV P σ → GV P (wkˢᵗ {Ψ} ⨟ˢ σ)
  GV-wkᵗ⨟ g = mkGV (λ α → gvᵗ g (suc α)) (gvʳ g) (gvᵉ g)

  GV-wkʳ⨟ : ∀ {σ : Subst (Ψ +r) Ψ'} → GV P σ → GV P (wkˢʳ {Ψ} ⨟ˢ σ)
  GV-wkʳ⨟ g = mkGV (gvᵗ g) (λ i → gvʳ g (suc i)) (gvᵉ g)

  GV-wkᵉ⨟ : ∀ {σ : Subst (Ψ +e) Ψ'} → GV P σ → GV P (wkˢᵉ {Ψ} ⨟ˢ σ)
  GV-wkᵉ⨟ g = mkGV (gvᵗ g) (gvʳ g) (λ i → gvᵉ g (suc i))

-- The images of a weakening sit among those of the lift

wk-⊆ᶠ-↑ᵉ : ∀ {Θ Ψ} → (X : Subst Θ Ψ) → (X ⨟ˢ wkˢᵉ) ⊆ᶠ (X ↑ᵉ)
wk-⊆ᶠ-↑ᵉ X = ⊆ᶠ-images (λ α → α , wkˢᵉ-v (sTy X α)) (λ i → i , wkˢᵉ-r (sR X i))
                       (λ i → inj₁ (suc i , wkˢᵉ-e (sE X i)))

-- Every unknown of an image of `τ ⨟ O` is free in an image of `O`

⨟-⊆ᶠ : ∀ {Θ₀ Θ Φ} → (τ : Subst Θ₀ Θ) → (O : Subst Θ Φ) → (τ ⨟ˢ O) ⊆ᶠ O
⨟-⊆ᶠ τ O = mk⊆ᶠ e r
  where
    e : ∀ {k} → freeᵉ k (τ ⨟ˢ O) ≡ true → freeᵉ k O ≡ true
    e {k} q with freeᵉ-⨟⁻ τ O q
    ... | inj₁ (α , s') =
          ∨-left (anyᶠ (λ α' → occᵉ-v k (sTy O α'))) _
            (anyᶠ-intro (λ α' → occᵉ-v k (sTy O α')) α s')
    ... | inj₂ (inj₁ (i , p , s')) =
          ∨-right (anyᶠ (λ α' → occᵉ-v k (sTy O α'))) _
            (∨-left (anyᶠ (λ j → occᵉ-r k (sR O j))) _
              (anyᶠ-intro (λ j → occᵉ-r k (sR O j)) i s'))
    ... | inj₂ (inj₂ (i , p , s')) =
          ∨-right (anyᶠ (λ α' → occᵉ-v k (sTy O α'))) _
            (∨-right (anyᶠ (λ j → occᵉ-r k (sR O j))) _
              (anyᶠ-intro (λ j → occᵉ-e k (sE O j)) i s'))

    r : ∀ {k} → freeʳ k (τ ⨟ˢ O) ≡ true → freeʳ k O ≡ true
    r {k} q with freeʳ-⨟⁻ τ O q
    ... | inj₁ (α , s') =
          ∨-left (anyᶠ (λ α' → occʳ-v k (sTy O α'))) _
            (anyᶠ-intro (λ α' → occʳ-v k (sTy O α')) α s')
    ... | inj₂ (i , p , s') =
          ∨-right (anyᶠ (λ α' → occʳ-v k (sTy O α'))) _
            (anyᶠ-intro (λ j → occʳ-r k (sR O j)) i s')
