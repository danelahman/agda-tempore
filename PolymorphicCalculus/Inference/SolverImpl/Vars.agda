--------------------------------------------------------------------
-- Sets of variables                                              --
--                                                                --
-- A set of variables of a scope is a mask on each sort. The      --
-- variables occurring in an expression, a type, a hypothesis set --
-- or the image of a substitution form one, and a substitution    --
-- fixes one when it sends each of its variables to itself.       --
--------------------------------------------------------------------

open import Data.Bool.Base using (true; false; _∨_) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (zero; suc)
open import Data.Product using (_×_; _,_)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.SolverImpl.Vars (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses               S

open import PolymorphicCalculus.Inference.SolverImpl.Core.Occurs S
  using (occᵗ-v; occᵗ-c; occʳ-r; occʳ-v; occʳ-c; occᵉ-e; occᵉ-r; occᵉ-v; occᵉ-c)

------------------------------------------------------------------------
-- Sets of variables, as masks of the three sorts

record Vars (Θ : Scope) : Set where
  constructor vars
  field
    vᵗ : TyVar Θ → 𝔹
    vʳ : RVar Θ → 𝔹
    vᵉ : EVar Θ → 𝔹

open Vars public

infixr 6 _∪ᵛ_
infix  4 _⊆ᵛ_

∅ᵛ : ∀ {Θ} → Vars Θ
∅ᵛ = vars (λ _ → false) (λ _ → false) (λ _ → false)

_∪ᵛ_ : ∀ {Θ} → Vars Θ → Vars Θ → Vars Θ
V ∪ᵛ W = vars (λ α → vᵗ V α ∨ vᵗ W α) (λ i → vʳ V i ∨ vʳ W i) (λ i → vᵉ V i ∨ vᵉ W i)

⋃ᵛ : ∀ {Θ} {X : Set} → (X → Vars Θ) → List X → Vars Θ
⋃ᵛ f []       = ∅ᵛ
⋃ᵛ f (x ∷ xs) = f x ∪ᵛ ⋃ᵛ f xs

record _⊆ᵛ_ {Θ : Scope} (V W : Vars Θ) : Set where
  constructor mk⊆ᵛ
  field
    ⊆ᵗ : ∀ α → vᵗ V α ≡ true → vᵗ W α ≡ true
    ⊆ʳ : ∀ i → vʳ V i ≡ true → vʳ W i ≡ true
    ⊆ᵉ : ∀ i → vᵉ V i ≡ true → vᵉ W i ≡ true

open _⊆ᵛ_ public

∨-inˡ : ∀ {a b} → a ≡ true → a ∨ b ≡ true
∨-inˡ refl = refl

∨-inʳ : ∀ a {b} → b ≡ true → a ∨ b ≡ true
∨-inʳ true  _ = refl
∨-inʳ false h = h

⊆-∪ˡ : ∀ {Θ} (V W : Vars Θ) {M : Vars Θ} → V ∪ᵛ W ⊆ᵛ M → V ⊆ᵛ M
⊆-∪ˡ V W h = mk⊆ᵛ (λ α o → ⊆ᵗ h α (∨-inˡ o)) (λ i o → ⊆ʳ h i (∨-inˡ o))
                  (λ i o → ⊆ᵉ h i (∨-inˡ o))

⊆-∪ʳ : ∀ {Θ} (V W : Vars Θ) {M : Vars Θ} → V ∪ᵛ W ⊆ᵛ M → W ⊆ᵛ M
⊆-∪ʳ V W h = mk⊆ᵛ (λ α o → ⊆ᵗ h α (∨-inʳ (vᵗ V α) o))
                  (λ i o → ⊆ʳ h i (∨-inʳ (vʳ V i) o))
                  (λ i o → ⊆ᵉ h i (∨-inʳ (vᵉ V i) o))

⊆-refl : ∀ {Θ} {V : Vars Θ} → V ⊆ᵛ V
⊆-refl = mk⊆ᵛ (λ _ o → o) (λ _ o → o) (λ _ o → o)

≟-self : ∀ {n} → (i : Fin n) → ⌊ i ≟ᶠ i ⌋ ≡ true
≟-self i with i ≟ᶠ i
... | yes _  = refl
... | no  ¬p = ⊥-elim (¬p refl)

------------------------------------------------------------------------
-- The variables occurring in an expression, a type, and a hypothesis set

fvᵉ : ∀ {Θ} → EExp Θ → Vars Θ
fvᵉ ε = vars (λ _ → false) (λ _ → false) (λ i → occᵉ-e i ε)

fvʳ : ∀ {Θ} → RExp Θ → Vars Θ
fvʳ ρ = vars (λ _ → false) (λ i → occʳ-r i ρ) (λ i → occᵉ-r i ρ)

fvᵛ : ∀ {Θ} → OVType Θ → Vars Θ
fvᵛ A = vars (λ α → occᵗ-v α A) (λ i → occʳ-v i A) (λ i → occᵉ-v i A)

fvᶜ : ∀ {Θ} → OCType Θ → Vars Θ
fvᶜ C = vars (λ α → occᵗ-c α C) (λ i → occʳ-c i C) (λ i → occᵉ-c i C)

fvᵗ : ∀ {Θ} → TyVar Θ → Vars Θ
fvᵗ α = fvᵛ (tvar α)

fvᵗᵗ : ∀ {Θ} → TyVar Θ × TyVar Θ → Vars Θ
fvᵗᵗ (α , β) = fvᵗ α ∪ᵛ fvᵗ β

fvʳʳ : ∀ {Θ} → RExp Θ × RExp Θ → Vars Θ
fvʳʳ (ρ , ρ') = fvʳ ρ ∪ᵛ fvʳ ρ'

fvᵉᵉ : ∀ {Θ} → EExp Θ × EExp Θ → Vars Θ
fvᵉᵉ (ε , ε') = fvᵉ ε ∪ᵛ fvᵉ ε'

fvᵛʳ : ∀ {Θ} → OVType Θ × RExp Θ → Vars Θ
fvᵛʳ (A , ρ) = fvᵛ A ∪ᵛ fvʳ ρ

fvᴴ : ∀ {Θ} → Hyps Θ → Vars Θ
fvᴴ Q = ⋃ᵛ fvᵗ (ets Q) ∪ᵛ ⋃ᵛ fvᵗᵗ (subᵥ Q) ∪ᵛ ⋃ᵛ fvʳʳ (ordᵣ Q)
        ∪ᵛ ⋃ᵛ fvᵉᵉ (ordₑ Q) ∪ᵛ ⋃ᵛ fvᵛʳ (disj Q)
-- a union indexed by the variables of one sort

⋃ᶠ : ∀ {Θ n} → (Fin n → Vars Θ) → Vars Θ
⋃ᶠ {n = zero}  f = ∅ᵛ
⋃ᶠ {n = suc n} f = f zero ∪ᵛ ⋃ᶠ (λ i → f (suc i))

⋃ᶠ-⊆ : ∀ {Θ n} {M : Vars Θ} → (f : Fin n → Vars Θ) → ⋃ᶠ f ⊆ᵛ M → (i : Fin n) → f i ⊆ᵛ M
⋃ᶠ-⊆ f h zero    = ⊆-∪ˡ (f zero) _ h
⋃ᶠ-⊆ f h (suc i) = ⋃ᶠ-⊆ (λ j → f (suc j)) (⊆-∪ʳ (f zero) _ h) i

-- the variables of the image of a substitution

fvˢ : ∀ {Θ₀ Θ} → Subst Θ₀ Θ → Vars Θ
fvˢ τ = ⋃ᶠ (λ α → fvᵛ (sTy τ α)) ∪ᵛ ⋃ᶠ (λ i → fvʳ (sR τ i)) ∪ᵛ ⋃ᶠ (λ i → fvᵉ (sE τ i))

------------------------------------------------------------------------
-- A substitution fixing a set of variables

record Fixes {Θ : Scope} (F : Vars Θ) (η : Subst Θ Θ) : Set where
  constructor mkFixes
  field
    fixᵗ : ∀ α → vᵗ F α ≡ true → sTy η α ≡ tvar α
    fixʳ : ∀ i → vʳ F i ≡ true → sR η i ≡ rvar i
    fixᵉ : ∀ i → vᵉ F i ≡ true → sE η i ≡ evar i

open Fixes public

fixes-id : ∀ {Θ} {F : Vars Θ} → Fixes F idˢ
fixes-id = mkFixes (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl)

fixes-⨟ : ∀ {Θ} {F : Vars Θ} {η η' : Subst Θ Θ} → Fixes F η → Fixes F η' → Fixes F (η ⨟ˢ η')
fixes-⨟ {η' = η'} f g =
  mkFixes (λ α h → trans (cong (_[ η' ]ᵛ) (fixᵗ f α h)) (fixᵗ g α h))
          (λ i h → trans (cong (_[ η' ]ʳ) (fixʳ f i h)) (fixʳ g i h))
          (λ i h → trans (cong (_[ η' ]ᵉ) (fixᵉ f i h)) (fixᵉ g i h))

-- a variable outside the set differs from every variable in it

outside : ∀ {n} → (p : Fin n → 𝔹) → {i j : Fin n} → p i ≡ false → p j ≡ true
        → ⌊ i ≟ᶠ j ⌋ ≡ false
outside p {i} {j} o h with i ≟ᶠ j
... | no  _    = refl
... | yes refl = ⊥-elim (t≢f (trans (sym h) o))
  where
    t≢f : true ≡ false → ⊥
    t≢f ()

fixes-updᵉ : ∀ {Θ} {F : Vars Θ} → (i : EVar Θ) → (b : EExp Θ) → vᵉ F i ≡ false
           → Fixes F (updᵉ i b)
fixes-updᵉ {F = F} i b o =
  mkFixes (λ _ _ → refl) (λ _ _ → refl) (λ j h → updᵉ-miss i b j (outside (vᵉ F) o h))

fixes-updʳ : ∀ {Θ} {F : Vars Θ} → (i : RVar Θ) → (b : RExp Θ) → vʳ F i ≡ false
           → Fixes F (updʳ i b)
fixes-updʳ {F = F} i b o =
  mkFixes (λ _ _ → refl) (λ j h → updʳ-miss i b j (outside (vʳ F) o h)) (λ _ _ → refl)

-- an expression or a type over fixed variables is fixed

fix-e : ∀ {Θ} {F : Vars Θ} {ρ : Subst Θ Θ} → Fixes F ρ
      → (ε : EExp Θ) → fvᵉ ε ⊆ᵛ F → ε [ ρ ]ᵉ ≡ ε
fix-e f (evar i)   h = fixᵉ f i (⊆ᵉ h i (≟-self i))
fix-e f (econst c) h = refl
fix-e f (ε ·̂ₑ ε')  h = cong₂ _·̂ₑ_ (fix-e f ε (⊆-∪ˡ (fvᵉ ε) (fvᵉ ε') h))
                                  (fix-e f ε' (⊆-∪ʳ (fvᵉ ε) (fvᵉ ε') h))
fix-e f (ε ⊔̂ₑ ε')  h = cong₂ _⊔̂ₑ_ (fix-e f ε (⊆-∪ˡ (fvᵉ ε) (fvᵉ ε') h))
                                  (fix-e f ε' (⊆-∪ʳ (fvᵉ ε) (fvᵉ ε') h))

fix-r : ∀ {Θ} {F : Vars Θ} {ρ : Subst Θ Θ} → Fixes F ρ
      → (r : RExp Θ) → fvʳ r ⊆ᵛ F → r [ ρ ]ʳ ≡ r
fix-r f (rvar i)   h = fixʳ f i (⊆ʳ h i (≟-self i))
fix-r f (rconst c) h = refl
fix-r f (r ·̂ᵣ r')  h = cong₂ _·̂ᵣ_ (fix-r f r (⊆-∪ˡ (fvʳ r) (fvʳ r') h))
                                  (fix-r f r' (⊆-∪ʳ (fvʳ r) (fvʳ r') h))
fix-r f (r ⊔̂ᵣ r')  h = cong₂ _⊔̂ᵣ_ (fix-r f r (⊆-∪ˡ (fvʳ r) (fvʳ r') h))
                                  (fix-r f r' (⊆-∪ʳ (fvʳ r) (fvʳ r') h))
fix-r f ∣ ε ∣̂ᵉ     h = cong ∣_∣̂ᵉ (fix-e f ε h)
mutual

  fix-v : ∀ {Θ} {F : Vars Θ} {ρ : Subst Θ Θ} → Fixes F ρ
        → (A : OVType Θ) → fvᵛ A ⊆ᵛ F → A [ ρ ]ᵛ ≡ A
  fix-v f (tvar α)  h = fixᵗ f α (⊆ᵗ h α (≟-self α))
  fix-v f (Base b)  h = refl
  fix-v f Unit      h = refl
  fix-v f Bool      h = refl
  fix-v f Nat       h = refl
  fix-v f Empty     h = refl
  fix-v f (A |×| B) h = cong₂ _|×|_ (fix-v f A (⊆-∪ˡ (fvᵛ A) (fvᵛ B) h))
                                    (fix-v f B (⊆-∪ʳ (fvᵛ A) (fvᵛ B) h))
  fix-v f (A |+| B) h = cong₂ _|+|_ (fix-v f A (⊆-∪ˡ (fvᵛ A) (fvᵛ B) h))
                                    (fix-v f B (⊆-∪ʳ (fvᵛ A) (fvᵛ B) h))
  fix-v f (|List| A) h = cong |List| (fix-v f A h)
  fix-v f (A ⇒ C)   h = cong₂ _⇒_ (fix-v f A (⊆-∪ˡ (fvᵛ A) (fvᶜ C) h))
                                  (fix-c f C (⊆-∪ʳ (fvᵛ A) (fvᶜ C) h))
  fix-v f (C ⇛ D)   h = cong₂ _⇛_ (fix-c f C (⊆-∪ˡ (fvᶜ C) (fvᶜ D) h))
                                  (fix-c f D (⊆-∪ʳ (fvᶜ C) (fvᶜ D) h))
  fix-v f ([ ρ ] A) h = cong₂ [_]_ (fix-r f ρ (⊆-∪ˡ (fvʳ ρ) (fvᵛ A) h))
                                   (fix-v f A (⊆-∪ʳ (fvʳ ρ) (fvᵛ A) h))

  fix-c : ∀ {Θ} {F : Vars Θ} {ρ : Subst Θ Θ} → Fixes F ρ
        → (C : OCType Θ) → fvᶜ C ⊆ᵛ F → C [ ρ ]ᶜ ≡ C
  fix-c f (A ‼ ε) h =
    cong₂ _‼_ (fix-v f A (mk⊆ᵛ (⊆ᵗ h) (⊆ʳ h) (λ i o → ⊆ᵉ h i (∨-inˡ o))))
              (fix-e f ε (mk⊆ᵛ (λ _ ()) (λ _ ()) (λ i o → ⊆ᵉ h i (∨-inʳ (occᵉ-v i A) o))))
