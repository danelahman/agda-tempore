------------------------------------------------------------------------
-- Soundness of the beta/eta equations of the pure fragment.            --
--                                                                    --
-- These are the cartesian closed structure of the model: `unit-eta` is  --
-- the terminal object's uniqueness, `fun-beta`/`fun-eta` the            --
-- exponential's beta/eta (`βᵐ`, `uncurryᵐ-curryᵐ-iso`),                 --
-- `match-beta`/`match-eta` the product's, and `absurd-eta` the          --
-- strictness of the initial object (`𝟘ᵐ-strict`) — with an empty-typed  --
-- value in scope every computation is the same one.                    --
--                                                                    --
-- The substitutions on the right-hand sides are discharged by           --
-- `V-subst-nat`/`C-subst-nat`: `sub-env Hd W` is the pairing            --
-- `⟨ idᵐ , ⟦ W ⟧ ⟩ᵐ`, so each beta rule reduces to a product            --
-- manipulation.                                                        --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module EquationalTheory.Soundness.Values
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; yes; no)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S using (V-rename; C-rename)
open import Syntax.Substitutions S

open import EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; ⟨⟩-≤; ⟨⟩-≤-refl; ⟨⟩-εᵘ∘η≡id; εᵘ)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE

-- The head variable denotes the second projection: at a non-eternal type the
-- grade bound is reflexive and the possibility counit cancels `η`; at an
-- eternal one the extraction cancels it (`eternalᵛ-η-ext`).

var-morphism-Hd : ∀ {Γ A} → (f : ¬ Eternal A → uᵣ ≾ᵣ uᵣ)
                → var-morphism {Γ ∷ A} f Hd ≈ᵐ sndᵐ
var-morphism-Hd {A = A} f with eternal? A
... | yes et =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ (eternalᵛ-extᵉ-u et) ∙ ⟨⟩-εᵘ∘η≡id)
  ∙ ∘ᵐ-identityˡ _
... | no ¬et =
    ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr (f ¬et) ≾ᵣ-refl ∙ ⟨⟩-≤-refl) ∙ ∘ᵐ-identityˡ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ ⟨⟩-εᵘ∘η≡id
  ∙ ∘ᵐ-identityˡ _
  where
    open Past Pst using (⟨⟩-≤-irr)


sound-unit-eta : ∀ {Γ} → (V : Γ ⊢V⦂ Unit) → Soundᵛ== (unit-eta V)
sound-unit-eta V pV _ = terminalᵐ-unique

sound-fun-eta : ∀ {Γ A C} → (V : Γ ⊢V⦂ A ⇒ C) → Soundᵛ== (fun-eta V)
sound-fun-eta {Γ} {A} V pV (p₁ , _) =
    ≈ᵐ-sym (uncurryᵐ-curryᵐ-iso (⟦ V ⟧ᵛᵗ pV))
  ∙ curryᵐ-cong (  ≈ᵐ-sym (uncurryᵐ-cong (∘ᵐ-identityˡ (⟦ V ⟧ᵛᵗ pV)))
                 ∙ uncurryᵐ-nat (⟦ V ⟧ᵛᵗ pV) idᵐ
                 ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
                 ∙ ∘ᵐ-congʳ (≈ᵐ-sym
                     (⟨ ⟦⟧ᵛᵗ-irr (V-rename wk-ren V) p₁ (renᵛ wk-ren V pV)
                        ∙ V-rename-nat wk-ren V pV
                      , var-morphism-Hd {Γ} {A} (λ _ → ≾ᵣ-refl) ⟩ᵐ-cong)))

sound-fun-beta : ∀ {Γ A C} → (M : Γ ∷ A ⊢C⦂ C) → (W : Γ ⊢V⦂ A)
               → Soundᶜ== (fun-beta M W)
sound-fun-beta M W (pM , pW) pR =
    βᵐ (⟦ M ⟧ᶜᵗ pM) (⟦ W ⟧ᵛᵗ pW)
  ∙ ≈ᵐ-sym (C-subst-nat M Hd W pM pW)
  ∙ ⟦⟧ᶜᵗ-irr (M [ Hd ↦ W ]c) (subᶜ M Hd W pM pW) pR

sound-absurd-eta : ∀ {Γ C} → (V : Γ ⊢V⦂ Empty) → (M : Γ ∷ Empty ⊢C⦂ C)
                 → Soundᶜ== (absurd-eta V M)
sound-absurd-eta V M pV pR = 𝟘ᵐ-strict (⟦ V ⟧ᵛᵗ pV) _ _

sound-match-beta : ∀ {Γ A B C} → (V : Γ ⊢V⦂ A) → (W : Γ ⊢V⦂ B) → (M : Γ ∷ A ∷ B ⊢C⦂ C)
                 → Soundᶜ== (match-beta V W M)
sound-match-beta V W M ((pV , pW) , pM) pR =
    -- the two projections of the pair being matched
    ∘ᵐ-congʳ (⟨ ⟨ ≈ᵐ-refl , ⟨⟩ᵐ-fstᵐ _ _ ⟩ᵐ-cong , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)
    -- the two substitutions, composed and reassociated
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr ((M [ Hd ↦ V-rename wk-ren W ]c) [ Hd ↦ V ]c) pR
                (subᶜ (M [ Hd ↦ V-rename wk-ren W ]c) Hd V
                   (subᶜ M Hd (V-rename wk-ren W) pM (renᵛ wk-ren W pW)) pV)
            ∙ C-subst-nat (M [ Hd ↦ V-rename wk-ren W ]c) Hd V
                (subᶜ M Hd (V-rename wk-ren W) pM (renᵛ wk-ren W pW)) pV
            ∙ ∘ᵐ-congˡ (  C-subst-nat M Hd (V-rename wk-ren W) pM (renᵛ wk-ren W pW)
                        ∙ ∘ᵐ-congʳ ⟨ ≈ᵐ-refl , V-rename-nat wk-ren W pW ⟩ᵐ-cong)
            ∙ ∘ᵐ-assoc _ _ _
            ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                        ∙ ⟨ ∘ᵐ-identityˡ _
                          , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                            ∙ ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
