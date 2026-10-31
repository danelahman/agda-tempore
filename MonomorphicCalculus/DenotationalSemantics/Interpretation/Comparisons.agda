------------------------------------------------------------------------
-- Comparison at the eternal types, and the data as points.           --
--                                                                    --
-- `cmpᵐ` is the comparison morphism of an eternal type, by recursion --
-- on its eternality: the base types' own (`GroundEternal`), and the  --
-- derived ones of `Model.Comparison` for the formers. `⌜_⌝ᵈ` sends a --
-- datum to a point of the type's interpretation. Compared at points, --
-- `cmpᵐ` returns the structural order of the data (`cmpᵐ-pt`), and a --
-- coercion acts on points as on data (`⌜⌝ᵈ-coe`).                    --
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundEternal
open import MonomorphicCalculus.DenotationalSemantics.Model.Monad

module MonomorphicCalculus.DenotationalSemantics.Interpretation.Comparisons
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.List.Base using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open LanguageSpec S

open import Language.Comparisons
open import MonomorphicCalculus.Syntax.Types     S
open import MonomorphicCalculus.Syntax.Subtyping S
open import MonomorphicCalculus.Syntax.Data      S

open Category Cat
open GroundTypes GTy
open GroundEternal GE using (cmpᵇᵐ; cmpᵇᵐ-pt)

open import MonomorphicCalculus.DenotationalSemantics.Model.Comparison Cat public

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types     S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon

private
  infixr 3 _∙_
  _∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙_ = ≈ᵐ-trans

-- The comparison morphism of an eternal type

cmpᵐ : ∀ {A} → Et A → ⟦ A ⟧ᵛ ×ᵐ ⟦ A ⟧ᵛ →ᵐ Ordᵐ
cmpᵐ (Baseₑ eb)     = cmpᵇᵐ _ eb
cmpᵐ unitₑ          = cmp𝟙ᵐ
cmpᵐ boolₑ          = cmp𝔹ᵐ
cmpᵐ natₑ           = cmpℕᵐ
cmpᵐ (et₁ |×|ₑ et₂) = cmp×ᵐ (cmpᵐ et₁) (cmpᵐ et₂)
cmpᵐ (et₁ |+|ₑ et₂) = cmp+ᵐ (cmpᵐ et₁) (cmpᵐ et₂)
cmpᵐ (listₑ et)     = cmpLᵐ (cmpᵐ et)
cmpᵐ emptyₑ         = cmp𝟘ᵐ

-- A datum as a point

⌜_⌝ᵈ : ∀ {A} → Et A → ⟪ A ⟫ → 𝟙ᵐ →ᵐ ⟦ A ⟧ᵛ
⌜ Baseₑ _ ⌝ᵈ        c        = ⟦ c ⟧ᵇᶜ
⌜ unitₑ ⌝ᵈ          _        = terminalᵐ
⌜ boolₑ ⌝ᵈ          b        = ⌜ b ⌝ᵇ
⌜ natₑ ⌝ᵈ           n        = ⌜ n ⌝ᴺ
⌜ et₁ |×|ₑ et₂ ⌝ᵈ   (x , y)  = ⟨ ⌜ et₁ ⌝ᵈ x , ⌜ et₂ ⌝ᵈ y ⟩ᵐ
⌜ et₁ |+|ₑ et₂ ⌝ᵈ   (inj₁ x) = inlᵐ ∘ᵐ ⌜ et₁ ⌝ᵈ x
⌜ et₁ |+|ₑ et₂ ⌝ᵈ   (inj₂ y) = inrᵐ ∘ᵐ ⌜ et₂ ⌝ᵈ y
⌜ listₑ et ⌝ᵈ       xs       = ⌜ ⌜ et ⌝ᵈ ⌝ᴸ xs
⌜ emptyₑ ⌝ᵈ         ()

-- Compared at the points of data, the comparison returns the data's order.

cmpᵐ-pt : ∀ {A} → (et : Et A) → Compares (cmpᵐ et) ⌜ et ⌝ᵈ (compareᵈ et)
cmpᵐ-pt (Baseₑ eb) c c' = cmpᵇᵐ-pt eb c c'
cmpᵐ-pt unitₑ      _ _  = cmp𝟙ᵐ-pt _ _
cmpᵐ-pt boolₑ      b b' = cmp𝔹ᵐ-pt b b'
cmpᵐ-pt natₑ       n m  = cmpℕᵐ-pt n m
cmpᵐ-pt (et₁ |×|ₑ et₂) (x , y) (x' , y') =
    cmp×ᵐ-⟨⟩ _ _ _ _ _ _
  ∙ ∘ᵐ-congʳ ⟨ cmpᵐ-pt et₁ x x' , cmpᵐ-pt et₂ y y' ⟩ᵐ-cong
  ∙ lexᵐ-pt (compareᵈ et₁ x x') (compareᵈ et₂ y y')
cmpᵐ-pt (et₁ |+|ₑ et₂) (inj₁ x) (inj₁ x') = cmp+ᵐ-inl-inl _ _ _ _ ∙ cmpᵐ-pt et₁ x x'
cmpᵐ-pt (et₁ |+|ₑ et₂) (inj₁ x) (inj₂ y)  = cmp+ᵐ-inl-inr _ _ _ _
cmpᵐ-pt (et₁ |+|ₑ et₂) (inj₂ y) (inj₁ x)  = cmp+ᵐ-inr-inl _ _ _ _
cmpᵐ-pt (et₁ |+|ₑ et₂) (inj₂ y) (inj₂ y') = cmp+ᵐ-inr-inr _ _ _ _ ∙ cmpᵐ-pt et₂ y y'
cmpᵐ-pt (listₑ et) xs ys = cmpLᵐ-pt (cmpᵐ et) ⌜ et ⌝ᵈ (compareᵈ et) (cmpᵐ-pt et) xs ys
cmpᵐ-pt emptyₑ () _

-- A coercion at an eternal type acts on points as on data.

⌜⌝ᵈ-coe : ∀ {A₀ A} → (p : A₀ <:ᵛ A) → (et : Et A) → (d : ⟪ A₀ ⟫)
        → ⟦ p ⟧<:ᵛ ∘ᵐ ⌜ <:ᵛ-eternalˡ p et ⌝ᵈ d ≈ᵐ ⌜ et ⌝ᵈ (⟪ p ⟫ˢ d)
⌜⌝ᵈ-coe (Baseₛ refl) (Baseₑ _) c = ∘ᵐ-identityˡ _
⌜⌝ᵈ-coe unitₛ        unitₑ     _ = ∘ᵐ-identityˡ _
⌜⌝ᵈ-coe boolₛ        boolₑ     _ = ∘ᵐ-identityˡ _
⌜⌝ᵈ-coe natₛ         natₑ      _ = ∘ᵐ-identityˡ _
⌜⌝ᵈ-coe (p |×|ₛ q) (et₁ |×|ₑ et₂) (x , y) =
  mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ⌜⌝ᵈ-coe p et₁ x , ⌜⌝ᵈ-coe q et₂ y ⟩ᵐ-cong
⌜⌝ᵈ-coe (p |+|ₛ q) (et₁ |+|ₑ et₂) (inj₁ x) =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ ([]ᵐ-inlᵐ _ _)
  ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⌜⌝ᵈ-coe p et₁ x)
⌜⌝ᵈ-coe (p |+|ₛ q) (et₁ |+|ₑ et₂) (inj₂ y) =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ ([]ᵐ-inrᵐ _ _)
  ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⌜⌝ᵈ-coe q et₂ y)
⌜⌝ᵈ-coe (listₛ p) (listₑ et) []           = mapListᵐ-nil _
⌜⌝ᵈ-coe (listₛ p) (listₑ et) (x ∷ xs)     =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (mapListᵐ-cons _) ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
             ∙ ⟨ ⌜⌝ᵈ-coe p et x , ⌜⌝ᵈ-coe (listₛ p) (listₑ et) xs ⟩ᵐ-cong)
⌜⌝ᵈ-coe emptyₛ emptyₑ ()
