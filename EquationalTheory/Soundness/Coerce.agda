------------------------------------------------------------------------
-- Soundness of the sub-effecting equations.                           --
--                                                                    --
-- `coerce` denotes `T-≤`, and each equation is the corresponding law of --
-- the monad: `coerce-refl`/`coerce-trans` are `T-≤`'s functoriality in  --
-- the grade, `coerce-perform`/`coerce-delay` are `opᵀ-≤`/`delayᵀ-≤`     --
-- (a coercion of the continuation escaping the node), and               --
-- `coerce-seq`/`coerce-handle` are `strᵀ-≤` followed by `T-≤-μᵀ`        --
-- resp. `T-alg-of-handlerᵀ-≤` (a coercion of the sequenced computation   --
-- escaping the composite). The last two also move the continuation      --
-- across the lock the coercion relaxes, which is `η⊣-≤`.                --
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

module EquationalTheory.Soundness.Coerce
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

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types      S
open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.Renamings  S
open import Syntax.RenActions S using (C-rename)

open import EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-∘ᵐ; []-congᶠ; []-≤)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-≤)
open Adjunction Adj using (η⊣; η⊣-≤)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE

-- Postcomposition commutes with a transport in the second component of a
-- morphism's product domain (the `ty-gty` coercion of an operation's arity).

substᵈ-post : ∀ {X Z Z' A B} → (e : A ≡ B) → (h : Z →ᵐ Z') → (g : (X ×ᵐ A) →ᵐ Z)
            → h ∘ᵐ subst (λ O → (X ×ᵐ O) →ᵐ Z) e g
            ≡ subst (λ O → (X ×ᵐ O) →ᵐ Z') e (h ∘ᵐ g)
substᵈ-post refl h g = refl


sound-coerce-refl : ∀ {Γ A ε} → (rel : ε ≾ₑ ε) → (M : Γ ⊢C⦂ A ‼ ε)
                  → Soundᶜ== (coerce-refl rel M)
sound-coerce-refl rel M pL pR =
  ∘ᵐ-congˡ (T-≤-refl rel) ∙ ∘ᵐ-identityˡ _ ∙ ⟦⟧ᶜᵗ-irr M pL pR

sound-coerce-trans : ∀ {Γ A ε₁ ε₂ ε₃}
                   → (rel : ε₁ ≾ₑ ε₂) → (rel' : ε₂ ≾ₑ ε₃) → (rel'' : ε₁ ≾ₑ ε₃)
                   → (M : Γ ⊢C⦂ A ‼ ε₁)
                   → Soundᶜ== (coerce-trans rel rel' rel'' M)
sound-coerce-trans rel rel' rel'' M pL pR =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-≤-trans rel rel' rel'')
  ∙ ∘ᵐ-congʳ (⟦⟧ᶜᵗ-irr M pL pR)

sound-coerce-perform : ∀ {Γ A ε ε' op}
                     → (rel : ε ≾ₑ ε')
                     → (V : Γ ⊢V⦂ type-of-gtype (param op))
                     → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                            ⊢C⦂ A ‼ ε)
                     → Soundᶜ== (coerce-perform rel V M)
sound-coerce-perform {op = op} rel V M (pV , pM) (pV' , pM') =
    ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ substᶜ-≈ (ty-gty (param op)) (⟦⟧ᵛᵗ-irr V pV pV')
                        , ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                            (substᵈ-≈ (ty-gty (arity op)) (⟦⟧ᶜᵗ-irr M pM pM'))))
                        ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (opᵀ-≤ op rel))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ ∘ᵐ-identityˡ _
                , ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym ([]-∘ᵐ _ _)
                              ∙ []-congᶠ (  map⇒ᵐ-curryᵐ _ _
                                          ∙ curryᵐ-cong (≡→≈ᵐ (substᵈ-post
                                              (ty-gty (arity op)) (T-≤ rel) (⟦ M ⟧ᶜᵗ pM'))))) ⟩ᵐ-cong)

sound-coerce-delay : ∀ {Γ A τ ε ε'}
                   → (rel : ε ≾ₑ ε')
                   → (M : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
                   → Soundᶜ== (coerce-delay rel M)
sound-coerce-delay {τ = τ} rel M pM pM' =
    ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (⟦⟧ᶜᵗ-irr M pM pM'))))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (delayᵀ-≤ τ rel))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))

-- The continuation of a `⨟`/`handle` lives under the lock the coercion
-- relaxes. Transposing it at the smaller grade and relaxing the lock
-- (`⟨⟩-≤`, the renaming the equations apply) is the same as transposing at
-- the larger grade and relaxing the box (`[]-≤`, what `strᵀ-≤` produces).

coe-str : ∀ {Γ A B ε₁ ε₂ ε'}
        → (rel : ε₁ ≾ₑ ε₂)
        → (N : Γ ⟨ mapᵉ ε₂ ⟩ ∷ A ⊢C⦂ B ‼ ε')
        → (pN : Paramᶜ N)
        → (m : ⟦ Γ ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ A ⟧ᵛ ε₁)
        →    Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , T-≤ rel ∘ᵐ m ⟩ᵐ
        ≈ᵐ T-≤ rel
             ∘ᵐ Tᶠ (⟦ C-rename (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N ⟧ᶜᵗ
                      (renᶜ (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N pN))
             ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ
coe-str rel N pN m =
    -- push the coercion out of the pairing and through the strength
    ∘ᵐ-congʳ (  ∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                  ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (strᵀ-≤ rel)
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                      ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
    -- and out past the continuation's functorial action
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-≤-nat _ rel)
  ∙ ∘ᵐ-assoc _ _ _
    -- what is left on the environment is the transposed lock relaxation,
    -- i.e. the renaming the equation applies to the continuation
  ∙ ∘ᵐ-congʳ (  ∘ᵐ-congʳ (  ∘ᵐ-congʳ (⟨ η⊣-≤ (map-monotoneᵉ rel) , ≈ᵐ-refl ⟩ᵐ-cong)
                          ∙ ∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                              ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
                          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                          ∙ ∘ᵐ-congˡ (≈ᵐ-sym (strᵀ-natˡ _))
                          ∙ ∘ᵐ-assoc _ _ _)
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym (T-∘ᵐ _ _)
                          ∙ T-congᶠ (≈ᵐ-sym (C-rename-nat _ N pN))))

sound-coerce-seq : ∀ {Γ A B ε₁ ε₂ ε'}
                 → (rel : ε₁ ≾ₑ ε₂)
                 → (M : Γ ⊢C⦂ A ‼ ε₁)
                 → (N : Γ ⟨ mapᵉ ε₂ ⟩ ∷ A ⊢C⦂ B ‼ ε')
                 → Soundᶜ== (coerce-seq rel M N)
sound-coerce-seq rel M N (pM , pN) (pM' , pN') =
    ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (⟨ ≈ᵐ-refl , ∘ᵐ-congʳ (⟦⟧ᶜᵗ-irr M pM pM') ⟩ᵐ-cong)))
  ∙ ∘ᵐ-congʳ (coe-str rel N pN (⟦ M ⟧ᶜᵗ pM'))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-≤-μᵀ rel)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
      (⟦⟧ᶜᵗ-irr (C-rename (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N)
                (renᶜ (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N pN) pN'))))

sound-coerce-handle : ∀ {Γ A B ε₁ ε₂ ε'}
                    → (rel : ε₁ ≾ₑ ε₂)
                    → (M : Γ ⊢C⦂ A ‼ ε₁)
                    → (H : (op : Op) → (ε₀ : E) →
                             Γ ᴱ ∷ type-of-gtype (param op)
                                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₀)
                             ⊢C⦂ B ‼ (op-grade op ·ₑ ε₀))
                    → (N : Γ ⟨ mapᵉ ε₂ ⟩ ∷ A ⊢C⦂ B ‼ ε')
                    → Soundᶜ== (coerce-handle rel M H N)
sound-coerce-handle {Γ = Γ} rel M H N
                    (pM , pN , pH , uH) (pM' , pN' , pH' , uH') =
    ∘ᵐ-cong (T-alg-of-handlerᵀ-cong (⟦ Γ ⟧ᴱ-Eternalᵒ)
              (λ op ε'' → ∘ᵐ-congˡ
                            (⟦⟧ᶜᵗ-irr (H op ε'') (pH op ε'') (pH' op ε''))))
            (⟨ ≈ᵐ-refl
             , ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ∘ᵐ-congʳ (⟦⟧ᶜᵗ-irr M pM pM') ⟩ᵐ-cong))
               ∙ coe-str rel N pN (⟦ M ⟧ᶜᵗ pM') ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-≤ (⟦ Γ ⟧ᴱ-Eternalᵒ) _ rel)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ∘ᵐ-congˡ (T-congᶠ
      (⟦⟧ᶜᵗ-irr (C-rename (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N)
                (renᶜ (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N pN) pN')) ⟩ᵐ-cong))
