------------------------------------------------------------------------
-- Soundness of the sequencing associativity equation `seq-assoc`.      --
--                                                                    --
-- `(M ⨟ N) ⨟ P == …(M ⨟ (N ⨟ P'))` is the graded monad's associativity --
-- (`T-μ∘μ≡μ∘Tμ`) threaded through the strength's multiplication law     --
-- (`strᵀ-μᵀ`) and product-associativity (`strᵀ-assoc`). Because the box --
-- is *lax* (no `δ⁻¹`), the environment box is reconciled with the       --
-- possibility multiplication `μ` by the adjunction laws `η⊣-δ`,         --
-- `η⊣-monoidal`, `η⊣-≤` (as in `sound-seq-delay`), rather than by       --
-- cancelling `δ⁻¹ ∘ δ`.                                                --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality hiding (begin_; _∎)

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module EquationalTheory.Soundness.SeqAssoc
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

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S using (C-rename)
open import Syntax.Substitutions S

open import EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-≤; []-∘ᵐ; []-idᵐ; []-congᶠ; δ; []-monoidal;
                       []-δ-nat; []-monoidal-nat)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; μ; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ)
open Adjunction Adj using (η⊣; η⊣-nat; η⊣-≤; η⊣-δ; η⊣-monoidal; ε⊣)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.Seq S Cat Fut Pst Adj GTy Mon GE using (seq-extend)

-- Equational reasoning on the hom-setoids `(A →ᵐ B , _≈ᵐ_)`.

open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

private
  homSetoid : ∀ {A B} → Setoid 0ℓ 0ℓ
  homSetoid {A} {B} = record
    { Carrier = A →ᵐ B
    ; _≈_ = _≈ᵐ_
    ; isEquivalence = record { refl = ≈ᵐ-refl ; sym = ≈ᵐ-sym ; trans = ≈ᵐ-trans }
    }

module ≈-Reasoning {A B} = SetoidReasoning (homSetoid {A} {B})
open ≈-Reasoning

sound-seq-assoc : ∀ {Γ A B C ε ε' ε''}
                → (M : Γ ⊢C⦂ A ‼ ε)
                → (N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε')
                → (P : Γ ⟨ mapᵉ (ε ·ₑ ε') ⟩ ∷ B ⊢C⦂ C ‼ ε'')
                → Soundᶜ== (seq-assoc M N P)
sound-seq-assoc {Γ} {A} {B} {C} {ε} {ε'} {ε''} M N P ((pM , pN) , pP) pR =
    bigchase
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-subst e (M ⨟ (N ⨟ C-rename r P))) pR (ε-substᴾ e _ pRc)
            ∙ sound-ε-subst e (M ⨟ (N ⨟ C-rename r P)) pRc)
  where
    e   = sym (·ₑ-assoc ε ε' ε'')
    rin = (eq-ren (cong (Γ ⟨_⟩) map-·ᵉ)
           ∘ʳ ⟨⟩-μ-ren)
          ∘ʳ cong-⟨⟩-ren wk-ren
    r   = cong-∷-ren rin
    pRc = pM , (pN , renᶜ r P pP)

    m = ⟦ M ⟧ᶜᵗ pM
    n = ⟦ N ⟧ᶜᵗ pN
    p = ⟦ P ⟧ᶜᵗ pP

    q = ⟦ C-rename r P ⟧ᶜᵗ (renᶜ r P pP)

    φ = ⟦ rin ⟧ʳ

    -- The lock-merging renaming denotes exactly "weaken, then fold the two
    -- locks with `μ`, then relax the merged grade" — this is (‡), the only
    -- place the syntax of `rin` is used.
    φ-def : φ ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε' ⟩ᶠ fstᵐ
    φ-def = ∘ᵐ-congˡ (∘ᵐ-congˡ (eq-ren-grade {Γ} map-·ᵉ)) ∙ ∘ᵐ-assoc _ _ _

    -- The environment's `⟨ mapᵉ ε ⟩`-lock, transposed at `mapᵉ ε'` and merged
    -- with the outer lock by `μ`. This is the *value* the box carries once the
    -- comultiplication `δ` has split it.
    α : ⟨ mapᵉ ε ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ →ᵐ [ mapᵉ ε' ]ᵒ (⟨ mapᵉ (ε ·ₑ ε') ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ)
    α = [ mapᵉ ε' ]ᶠ (⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ) ∘ᵐ η⊣

    -- (†) The transposed lock-merge `α`, precomposed with the projection that
    -- forgets the bound value, is the renaming `φ` transposed.
    α-fstᵐ : α ∘ᵐ fstᵐ {B = ⟦ A ⟧ᵛ} ≈ᵐ [ mapᵉ ε' ]ᶠ φ ∘ᵐ η⊣
    α-fstᵐ =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat fstᵐ))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym ([]-∘ᵐ _ _)
                  ∙ []-congᶠ (∘ᵐ-assoc _ _ _ ∙ ≈ᵐ-sym φ-def))

    -- (Step B) The split box `δ ∘ []-≤ σ ∘ η⊣` is the transpose of `α`: the
    -- adjunction reconciles the comultiplication with the lock merge.
    box-split : δ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ η⊣
              ≈ᵐ [ mapᵉ ε ]ᶠ α ∘ᵐ η⊣
    box-split =
        ∘ᵐ-congʳ (η⊣-≤ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-δ-nat _))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ η⊣-δ
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym ([]-∘ᵐ _ _)
                  ∙ []-congᶠ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                              ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))

    -- Reshape the inner pair into `mapˣᵐ`-layers, so the outer strength meets
    -- `mapˣᵐ idᵐ μᵀ` (the input of `strᵀ-μᵀ`).
    step1-pair :
         ⟨ η⊣ , μᵀ ∘ᵐ Tᶠ n ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ ⟩ᵐ
      ≈ᵐ mapˣᵐ idᵐ μᵀ ∘ᵐ mapˣᵐ η⊣ (Tᶠ n) ∘ᵐ mapˣᵐ idᵐ strᵀ ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , m ⟩ᵐ ⟩ᵐ
    step1-pair = ≈ᵐ-sym (
        ∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
      ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityʳ _ , ≈ᵐ-refl ⟩ᵐ-cong)
      ∙ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))

    -- (★★) With the box split, what remains under the outer `Tᶠ` is a pure
    -- strength-naturality statement: threading the merged lock through the
    -- inner strength is reindexing the inner computation by `φ`.
    inner : strᵀ ∘ᵐ mapˣᵐ idᵐ n ∘ᵐ ×ᵐ-assoc ∘ᵐ mapˣᵐ ⟨ α , idᵐ ⟩ᵐ idᵐ
          ≈ᵐ Tᶠ (mapˣᵐ φ idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , n ⟩ᵐ
    inner =
        ∘ᵐ-congʳ (  ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                              ∙ ⟨   ∘ᵐ-assoc _ _ _
                                  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                                  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                                  ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
                                ,   ⟨⟩ᵐ-∘ _ _ _
                                  ∙ ⟨   ∘ᵐ-assoc _ _ _
                                      ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                                      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                                      ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)
                                      ∙ ∘ᵐ-identityˡ _
                                    ,   ⟨⟩ᵐ-sndᵐ _ _
                                      ∙ ∘ᵐ-identityˡ _ ⟩ᵐ-cong
                                  ∙ ≈ᵐ-sym (⟨⟩ᵐ-unique fstᵐ sndᵐ idᵐ
                                              (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _)) ⟩ᵐ-cong)
                  ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
                  ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong)
      ∙ ∘ᵐ-congʳ (⟨ α-fstᵐ , ≈ᵐ-refl ⟩ᵐ-cong)
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (strᵀ-natˡ φ))
      ∙ ∘ᵐ-assoc _ _ _

    -- (★) The strength-coherence core: the two nestings of the strength agree
    -- once the environment box is split (`box-split`) and re-threaded.
    core :
         (Tᶠ strᵀ ∘ᵐ strᵀ ∘ᵐ mapˣᵐ (δ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym map-·ᵉ))) idᵐ)
           ∘ᵐ mapˣᵐ η⊣ (Tᶠ n) ∘ᵐ mapˣᵐ idᵐ strᵀ ∘ᵐ ⟨ idᵐ , ⟨ η⊣ , m ⟩ᵐ ⟩ᵐ
      ≈ᵐ Tᶠ (Tᶠ (mapˣᵐ φ idᵐ)) ∘ᵐ Tᶠ strᵀ ∘ᵐ Tᶠ ⟨ η⊣ , n ⟩ᵐ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ
    core =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
            ∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
          ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityʳ _ , ≈ᵐ-refl ⟩ᵐ-cong)
          ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
          ∙ ⟨ ∘ᵐ-assoc _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                   ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))
      ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ (  ∘ᵐ-congʳ (mapˣᵐ-cong (≈ᵐ-sym []-idᵐ) ≈ᵐ-refl)
                              ∙ strᵀ-nat idᵐ n)
                  ∙ ∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
            ∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                              ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙ ∘ᵐ-congˡ (≈ᵐ-sym strᵀ-assoc)
          ∙ ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
                      ∙ ∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
                                  ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                                              ∙ ⟨   ⟨⟩ᵐ-∘ _ _ _
                                                  ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _
                                                    ,   ∘ᵐ-assoc _ _ _
                                                      ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
                                                      ∙ ⟨⟩ᵐ-fstᵐ _ _ ⟩ᵐ-cong
                                                ,   ∘ᵐ-assoc _ _ _
                                                  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
                                                  ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)
                                  ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
                                  ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨
            ∘ᵐ-congʳ (⟨ box-split , ≈ᵐ-refl ⟩ᵐ-cong)
          ∙ ∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                              ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙ ∘ᵐ-congˡ (  ∘ᵐ-congʳ (mapˣᵐ-cong ≈ᵐ-refl (≈ᵐ-sym []-idᵐ))
                      ∙ ≈ᵐ-sym ([]-monoidal-nat _ _))
          ∙ ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ η⊣-monoidal
          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym ([]-∘ᵐ _ _)
                      ∙ []-congᶠ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                  ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
          , ≈ᵐ-refl ⟩ᵐ-cong))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (
            ∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                              ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙ ∘ᵐ-congˡ (≈ᵐ-sym (strᵀ-natˡ _))
          ∙ ∘ᵐ-assoc _ _ _)))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym (T-∘ᵐ _ _)
                  ∙ T-congᶠ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-assoc _ _ _ ∙ inner)
                  ∙ T-∘ᵐ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (  ∘ᵐ-congˡ (T-∘ᵐ _ _)
                  ∙ ∘ᵐ-assoc _ _ _)

    -- The right-hand side, unfolded and re-associated (`T-∘ᵐ`, `T-μ∘μ≡μ∘Tμ`,
    -- and the `ε-subst` cancelling the associativity coercion), meets the
    -- left-hand side at the common midpoint `COMMON`.
    rhs→common :
         ε-substᵀ e ∘ᵐ ⟦ M ⨟ (N ⨟ C-rename r P) ⟧ᶜᵗ pRc
      ≈ᵐ μᵀ ∘ᵐ μᵀ ∘ᵐ Tᶠ (Tᶠ q) ∘ᵐ Tᶠ strᵀ ∘ᵐ Tᶠ ⟨ η⊣ , n ⟩ᵐ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ
    rhs→common =
        ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
          (T-∘ᵐ _ _ ∙ ∘ᵐ-congʳ (T-∘ᵐ _ _ ∙ ∘ᵐ-congʳ (T-∘ᵐ _ _)))))
      ∙ ∘ᵐ-congʳ (  ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
                  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ T-μ∘μ≡μ∘Tμ)
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (  ε-substᵀ-trans (·ₑ-assoc ε ε' ε'') e
                  ∙ ≡→≈ᵐ (cong ε-substᵀ uip)
                  ∙ ε-substᵀ-refl)
      ∙ ∘ᵐ-identityˡ _
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))

    bigchase :
         μᵀ ∘ᵐ Tᶠ p ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , μᵀ ∘ᵐ Tᶠ n ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ ⟩ᵐ
      ≈ᵐ ε-substᵀ e ∘ᵐ ⟦ M ⨟ (N ⨟ C-rename r P) ⟧ᶜᵗ pRc
    bigchase =
      begin
        μᵀ ∘ᵐ Tᶠ p ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , μᵀ ∘ᵐ Tᶠ n ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ ⟩ᵐ
      ≈⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ step1-pair))
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ strᵀ-μᵀ ∙ ∘ᵐ-assoc _ _ _))
       ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (≈ᵐ-sym (μᵀ-nat p)) ∙ ∘ᵐ-assoc _ _ _)
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ core))
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
             ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
           ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym (T-∘ᵐ _ _)
                       ∙ T-congᶠ (  ≈ᵐ-sym (T-∘ᵐ _ _)
                                  ∙ T-congᶠ (≈ᵐ-sym (C-rename-nat r P pP)))))) ⟩
        μᵀ ∘ᵐ μᵀ ∘ᵐ Tᶠ (Tᶠ q) ∘ᵐ Tᶠ strᵀ ∘ᵐ Tᶠ ⟨ η⊣ , n ⟩ᵐ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ
      ≈˘⟨ rhs→common ⟩
        ε-substᵀ e ∘ᵐ ⟦ M ⨟ (N ⨟ C-rename r P) ⟧ᶜᵗ pRc
      ∎
