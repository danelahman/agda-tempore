------------------------------------------------------------------------
-- Interpretation of the subtyping witnesses as coercion morphisms.     --
--                                                                    --
-- A witness `A <:ᵛ A'` denotes a morphism `⟦ A ⟧ᵛ →ᵐ ⟦ A' ⟧ᵛ`, built   --
-- by recursion on the witness: products and the box act functorially,   --
-- a function by `map⇒ᵐ` (contravariant in the domain), a box's grade    --
-- by `[]-≤` and a computation's effect by `T-≤`.                        --
--                                                                    --
-- The assignment is functorial and witness-irrelevant: `⟦ <:ᵛ-refl ⟧`   --
-- is the identity, `⟦ <:ᵛ-trans p q ⟧` the composite, and any two       --
-- witnesses of the same inclusion denote equal morphisms.               --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.Monad

module DenotationalSemantics.Interpretation.Subtyping
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
       where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S
open import Syntax.Subtyping S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-≤; []-idᵐ; []-∘ᵐ; []-congᶠ;
                       []-≤-refl; []-≤-trans; []-≤-nat)
open GroundTypes GTy
open Monad Mon using (Tᵒ; Tᶠ; T-≤; T-idᵐ; T-∘ᵐ; T-congᶠ;
                      T-≤-refl; T-≤-trans; T-≤-nat)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon

-- The coercion morphism

⟦_⟧<:ᵛ : ∀ {A A'} → A <:ᵛ A' → ⟦ A ⟧ᵛ →ᵐ ⟦ A' ⟧ᵛ
⟦_⟧<:ᶜ : ∀ {C C'} → C <:ᶜ C' → ⟦ C ⟧ᶜ →ᵐ ⟦ C' ⟧ᶜ

⟦ Baseₛ refl ⟧<:ᵛ = idᵐ
⟦ Unitₛ      ⟧<:ᵛ = idᵐ
⟦ Boolₛ      ⟧<:ᵛ = idᵐ
⟦ p |×|ₛ q   ⟧<:ᵛ = mapˣᵐ ⟦ p ⟧<:ᵛ ⟦ q ⟧<:ᵛ
⟦ p |+|ₛ q   ⟧<:ᵛ = map+ᵐ ⟦ p ⟧<:ᵛ ⟦ q ⟧<:ᵛ
⟦ Emptyₛ     ⟧<:ᵛ = idᵐ
⟦ p ⇒ₛ q     ⟧<:ᵛ = map⇒ᵐ ⟦ p ⟧<:ᵛ ⟦ q ⟧<:ᶜ
⟦ [_]ₛ_ {ρ' = ρ'} q p ⟧<:ᵛ = [ ρ' ]ᶠ ⟦ p ⟧<:ᵛ ∘ᵐ []-≤ q

⟦ p ‼ₛ q ⟧<:ᶜ = Tᶠ ⟦ p ⟧<:ᵛ ∘ᵐ T-≤ q

-- Witness irrelevance, inherited from the relation's own irrelevance

⟦⟧<:ᵛ-irr : ∀ {A A'} → (p q : A <:ᵛ A') → ⟦ p ⟧<:ᵛ ≈ᵐ ⟦ q ⟧<:ᵛ
⟦⟧<:ᵛ-irr p q rewrite <:ᵛ-irrelevant p q = ≈ᵐ-refl

⟦⟧<:ᶜ-irr : ∀ {C C'} → (p q : C <:ᶜ C') → ⟦ p ⟧<:ᶜ ≈ᵐ ⟦ q ⟧<:ᶜ
⟦⟧<:ᶜ-irr p q rewrite <:ᶜ-irrelevant p q = ≈ᵐ-refl

-- Functoriality: identities and composites

⟦⟧<:ᵛ-refl : (A : VType) → ⟦ <:ᵛ-refl A ⟧<:ᵛ ≈ᵐ idᵐ
⟦⟧<:ᶜ-refl : (C : CType) → ⟦ <:ᶜ-refl C ⟧<:ᶜ ≈ᵐ idᵐ

⟦⟧<:ᵛ-refl (Base b)  = ≈ᵐ-refl
⟦⟧<:ᵛ-refl Unit      = ≈ᵐ-refl
⟦⟧<:ᵛ-refl Bool      = ≈ᵐ-refl
⟦⟧<:ᵛ-refl (A |×| B) =
  ≈ᵐ-trans (mapˣᵐ-cong (⟦⟧<:ᵛ-refl A) (⟦⟧<:ᵛ-refl B)) mapˣᵐ-idᵐ
⟦⟧<:ᵛ-refl (A |+| B) =
  ≈ᵐ-trans (map+ᵐ-cong (⟦⟧<:ᵛ-refl A) (⟦⟧<:ᵛ-refl B)) map+ᵐ-idᵐ
⟦⟧<:ᵛ-refl Empty     = ≈ᵐ-refl
⟦⟧<:ᵛ-refl (A ⇒ C)   =
  ≈ᵐ-trans (map⇒ᵐ-cong (⟦⟧<:ᵛ-refl A) (⟦⟧<:ᶜ-refl C)) map⇒ᵐ-idᵐ
⟦⟧<:ᵛ-refl ([ ρ ] A) =
  ≈ᵐ-trans (∘ᵐ-cong ([]-congᶠ (⟦⟧<:ᵛ-refl A)) []-≤-refl)
           (≈ᵐ-trans (∘ᵐ-congˡ []-idᵐ) (∘ᵐ-identityˡ _))

⟦⟧<:ᶜ-refl (A ‼ ε) =
  ≈ᵐ-trans (∘ᵐ-cong (T-congᶠ (⟦⟧<:ᵛ-refl A)) (T-≤-refl ≾ₑ-refl))
           (≈ᵐ-trans (∘ᵐ-congˡ T-idᵐ) (∘ᵐ-identityˡ _))

⟦⟧<:ᵛ-trans : ∀ {A B C} → (p : A <:ᵛ B) → (q : B <:ᵛ C)
            → ⟦ <:ᵛ-trans p q ⟧<:ᵛ ≈ᵐ ⟦ q ⟧<:ᵛ ∘ᵐ ⟦ p ⟧<:ᵛ
⟦⟧<:ᶜ-trans : ∀ {C₁ C₂ C₃} → (p : C₁ <:ᶜ C₂) → (q : C₂ <:ᶜ C₃)
            → ⟦ <:ᶜ-trans p q ⟧<:ᶜ ≈ᵐ ⟦ q ⟧<:ᶜ ∘ᵐ ⟦ p ⟧<:ᶜ

⟦⟧<:ᵛ-trans (Baseₛ refl) (Baseₛ refl) = ≈ᵐ-sym (∘ᵐ-identityˡ _)
⟦⟧<:ᵛ-trans Unitₛ        Unitₛ        = ≈ᵐ-sym (∘ᵐ-identityˡ _)
⟦⟧<:ᵛ-trans Boolₛ        Boolₛ        = ≈ᵐ-sym (∘ᵐ-identityˡ _)
⟦⟧<:ᵛ-trans (p |×|ₛ r)   (q |×|ₛ s)   =
  ≈ᵐ-trans (mapˣᵐ-cong (⟦⟧<:ᵛ-trans p q) (⟦⟧<:ᵛ-trans r s))
           (≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _))
⟦⟧<:ᵛ-trans (p |+|ₛ r)   (q |+|ₛ s)   =
  ≈ᵐ-trans (map+ᵐ-cong (⟦⟧<:ᵛ-trans p q) (⟦⟧<:ᵛ-trans r s))
           (≈ᵐ-sym (map+ᵐ-∘ _ _ _ _))
⟦⟧<:ᵛ-trans Emptyₛ       Emptyₛ       = ≈ᵐ-sym (∘ᵐ-identityˡ _)
⟦⟧<:ᵛ-trans (p ⇒ₛ r)     (q ⇒ₛ s)     =
  ≈ᵐ-trans (map⇒ᵐ-cong (⟦⟧<:ᵛ-trans q p) (⟦⟧<:ᶜ-trans r s))
           (map⇒ᵐ-∘ _ _ _ _)
-- the two grade relaxations meet after the inner coercion crosses the
-- outer one (`[]-≤-nat`), and then compose
⟦⟧<:ᵛ-trans ([ p ]ₛ r)   ([ q ]ₛ s)   =
  ≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (⟦⟧<:ᵛ-trans r s)))
  (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym ([]-≤-trans q p)))
                                (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-≤-nat _ q)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))

⟦⟧<:ᶜ-trans (p ‼ₛ r) (q ‼ₛ s) =
  ≈ᵐ-trans (∘ᵐ-congˡ (T-congᶠ (⟦⟧<:ᵛ-trans p q)))
  (≈ᵐ-trans (∘ᵐ-congˡ (T-∘ᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (T-≤-trans r s _)))
                                (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-nat _ s)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))

-- Hence a coercion between equal types is the identity

⟦⟧<:ᵛ-id : ∀ {A} → (p : A <:ᵛ A) → ⟦ p ⟧<:ᵛ ≈ᵐ idᵐ
⟦⟧<:ᵛ-id {A} p = ≈ᵐ-trans (⟦⟧<:ᵛ-irr p (<:ᵛ-refl A)) (⟦⟧<:ᵛ-refl A)

⟦⟧<:ᶜ-id : ∀ {C} → (p : C <:ᶜ C) → ⟦ p ⟧<:ᶜ ≈ᵐ idᵐ
⟦⟧<:ᶜ-id {C} p = ≈ᵐ-trans (⟦⟧<:ᶜ-irr p (<:ᶜ-refl C)) (⟦⟧<:ᶜ-refl C)

-- A witness at box type splits into its two halves. The family is inductive,
-- so the split is only propositional; `<:ᵛ-irrelevant` recovers it.

⟦⟧<:ᵛ-box : ∀ {ρ ρ' A A'} → (w : ([ ρ ] A) <:ᵛ ([ ρ' ] A'))
          → ⟦ w ⟧<:ᵛ ≈ᵐ [ ρ' ]ᶠ ⟦ <:ᵛ-box-type w ⟧<:ᵛ ∘ᵐ []-≤ (<:ᵛ-box-grade w)
⟦⟧<:ᵛ-box w = ⟦⟧<:ᵛ-irr w ([ <:ᵛ-box-grade w ]ₛ <:ᵛ-box-type w)

-- An eternal type has no clause carrying a grade or a function, so a
-- coercion out of one goes nowhere.

<:ᵛ-eternal-≡ : ∀ {A B} → Eternal A → A <:ᵛ B → A ≡ B
<:ᵛ-eternal-≡ et          (Baseₛ refl) = refl
<:ᵛ-eternal-≡ et          Unitₛ        = refl
<:ᵛ-eternal-≡ et          Boolₛ        = refl
<:ᵛ-eternal-≡ (et |×|ₑ e) (p |×|ₛ q)   =
  cong₂ _|×|_ (<:ᵛ-eternal-≡ et p) (<:ᵛ-eternal-≡ e q)
<:ᵛ-eternal-≡ (et |+|ₑ e) (p |+|ₛ q)   =
  cong₂ _|+|_ (<:ᵛ-eternal-≡ et p) (<:ᵛ-eternal-≡ e q)
<:ᵛ-eternal-≡ et          Emptyₛ       = refl
