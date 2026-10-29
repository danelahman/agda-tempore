------------------------------------------------------------------------
-- The handler-uniformity condition and the clause the semantics applies --
-- to a handled operation.                                               --
--                                                                      --
-- Split off from `Preservation` because it is interpretation-only (no    --
-- operational machinery) and its normalisation is heavy: keeping it in    --
-- its own module lets `Preservation` import `clause-sound` rather than    --
-- re-elaborate its body. `HANDLE-OP` includes the handler's clause into  --
-- the ambient context `Γ` along `barrier-ren`, whose denotation is the    --
-- free algebra's unit `⟨⊤⟩-η` on the nose.                                --
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import ClosedCalculus.DenotationalSemantics.Model.Category
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Future
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Past
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import ClosedCalculus.DenotationalSemantics.Model.GroundTypes
open import ClosedCalculus.DenotationalSemantics.Model.GroundEternal
open import ClosedCalculus.DenotationalSemantics.Model.Monad

module ClosedCalculus.OperationalSemantics.Soundness.Preservation.HandleOpClause
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Product using (_,_; proj₁; proj₂)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import ClosedCalculus.Syntax.Types S
open import ClosedCalculus.Syntax.Contexts   S
open import ClosedCalculus.Syntax.Terms   S
open import ClosedCalculus.Syntax.Renaming   S
open import ClosedCalculus.Syntax.Renaming.Action S using (C-rename)
open import ClosedCalculus.Syntax.Substitution  S

open Category Cat
open Future Fut
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η)
open Adjunction Adj using (η⊣)
open GroundTypes GTy using (⟦_⟧ᵍ)
open Monad Mon

open import ClosedCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ; ⟨⊤⟩-η)

open import ClosedCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
  using (renᶜ; C-rename-nat)
open import ClosedCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
  using (C-subst-nat; subᶜ)

infixr 3 _∙_
_∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
_∙_ = ≈ᵐ-trans

gty-cancelᵛ : ∀ {X Y Y'} → (e : Y ≡ Y') → (g : X →ᵐ Y)
            → subst (λ O → Y' →ᵐ O) (sym e) idᵐ ∘ᵐ subst (λ O → X →ᵐ O) e g ≈ᵐ g
gty-cancelᵛ refl g = ∘ᵐ-identityˡ _

-- `×ᵐ-assoc⁻¹` on a canonical pairing.
assoc⁻¹-⟨⟩ : ∀ {X A B C} → (a : X →ᵐ A) → (b : X →ᵐ B) → (c : X →ᵐ C)
           → ×ᵐ-assoc⁻¹ ∘ᵐ ⟨ a , ⟨ b , c ⟩ᵐ ⟩ᵐ ≈ᵐ ⟨ ⟨ a , b ⟩ᵐ , c ⟩ᵐ
assoc⁻¹-⟨⟩ a b c =
    ⟨⟩ᵐ-∘ _ _ _
  ∙ ⟨ ⟨⟩ᵐ-∘ _ _ _
      ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _
        , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-fstᵐ _ _ ⟩ᵐ-cong
    , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong

clause-sound : ∀ {Γ B ε''} → (op : Op)
             → (H : (op' : Op) → (ε' : E)
                  → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op')
                       ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε')
                    ⊢C⦂ B ‼ (op-grade op' ·ₑ ε'))
             → (pH : ∀ op' ε' → Paramᶜ (H op' ε'))
             → (uH : EffUniformʰ {Γ} H pH)
             → (V : Γ ⊢V⦂ type-of-gtype (param op)) → (pV : Paramᵛ V)
             → (W : ⟦ Γ ⟧ᶜᵗˣ →ᵐ [ mapᵉ (op-grade op) ]ᵒ
                      (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ ⟦ B ⟧ᵛ ε''))
             → ⟦ (C-rename (cong-∷-ren (cong-∷-ren (barrier-ren {Γ}))) (H op ε''))
                     [ split-∷ split-[] ↦ V ]c ⟧ᶜᵗ
                 (subᶜ (C-rename (cong-∷-ren (cong-∷-ren (barrier-ren {Γ}))) (H op ε''))
                       (split-∷ split-[]) V
                       (renᶜ (cong-∷-ren (cong-∷-ren (barrier-ren {Γ})))
                             (H op ε'') (pH op ε''))
                       pV)
                 ∘ᵐ ⟨ idᵐ
                    , [ mapᵉ (op-grade op) ]ᶠ
                        (map⇒ᵐ (subst (λ O → O →ᵐ ⟦ arity op ⟧ᵍ)
                                      (sym (ty-gty (arity op))) idᵐ) idᵐ)
                      ∘ᵐ W ⟩ᵐ
             ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {Γ} H pH uH) op ε''
                  ∘ᵐ ⟨ ⟨⊤⟩-η
                     , ⟨ subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op))
                               (⟦ V ⟧ᵛᵗ pV)
                       , W ⟩ᵐ ⟩ᵐ
clause-sound {Γ} {B} {ε''} op H pH uH V pV W =
    ∘ᵐ-congˡ (C-subst-nat Hcl (split-∷ split-[]) V pHcl pV)
  ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ mid)
  ∙ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (mapˣᵐ-∘ _ _ _ _))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)
  ∙ ∘ᵐ-congʳ
      (⟨ ∘ᵐ-identityʳ _
         ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
         ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
       , ∘ᵐ-congˡ (∘ᵐ-identityˡ _) ∙ ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  -- the semantic clause unfolds through its adapter: the associator rearranges
  -- the pairing (`assoc⁻¹-⟨⟩`) and the parameter's ground coercions cancel
  -- (`gty-cancelᵛ`)
  ∙ ≈ᵐ-sym
      (  ∘ᵐ-assoc _ _ _
       ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (assoc⁻¹-⟨⟩ ⟨⊤⟩-η _ _))
       ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)
       ∙ ∘ᵐ-congʳ (⟨ mapˣᵐ-∘⟨⟩ _ _ _ _
                     ∙ ⟨ ∘ᵐ-identityˡ _
                       , gty-cancelᵛ (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV) ⟩ᵐ-cong
                   , ≈ᵐ-refl ⟩ᵐ-cong))
  where
    Hcl  = C-rename (cong-∷-ren (cong-∷-ren (barrier-ren {Γ}))) (H op ε'')
    pHcl = renᶜ (cong-∷-ren (cong-∷-ren (barrier-ren {Γ}))) (H op ε'') (pH op ε'')
    -- the clause's inclusion along `barrier-ren` is `⟨⊤⟩-η` on the ambient slot
    mid : ⟦ Hcl ⟧ᶜᵗ pHcl
        ≈ᵐ ⟦ H op ε'' ⟧ᶜᵗ (pH op ε'') ∘ᵐ mapˣᵐ (mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ
    mid =
      C-rename-nat (cong-∷-ren (cong-∷-ren (barrier-ren {Γ}))) (H op ε'') (pH op ε'')

