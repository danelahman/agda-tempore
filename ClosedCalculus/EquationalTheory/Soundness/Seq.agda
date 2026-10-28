------------------------------------------------------------------------
-- Soundness of the sequencing equations.                              --
-- `M ⨟ N` denotes `μᵀ ∘ Tᶠ ⟦N⟧ ∘ strᵀ ∘ ⟨ η⊣ , ⟦M⟧ ⟩`; each equation  --
-- is a graded monad law threaded through the strength.                --
-- `seq-box`/`seq-unbox`: a resource binder commutes with sequencing   --
-- (`seq-extend`); `seq-delay`/`seq-perform`: `delay`/the operation    --
-- are algebraic over `⨟`.                                             --
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

module ClosedCalculus.EquationalTheory.Soundness.Seq
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

open import Language.Types                      S
open import ClosedCalculus.Syntax.Contexts      S
open import ClosedCalculus.Syntax.Terms         S
open import ClosedCalculus.Syntax.Renamings     S
open import ClosedCalculus.Syntax.RenActions    S using (V-rename; C-rename)
open import ClosedCalculus.Syntax.Substitutions S

open import ClosedCalculus.EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-≤; []-∘ᵐ; []-congᶠ; []-ε-nat; []-ε∘ηᵘ≡id; ηᵘ;
                       δ; []-monoidal; []-δ-nat; []-monoidal-nat)
                renaming (ε to εᵇ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; μ; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ; ⟨⟩-≤-irr)
open Adjunction Adj using (η⊣; η⊣-nat; η⊣-≤; η⊣-u; ε⊣; η⊣-δ; η⊣-monoidal)
open GroundTypes GTy
open Monad Mon

open import ClosedCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE

open import ClosedCalculus.OperationalSemantics.Soundness.Preservation.Unbox S Cat Fut Pst Adj GTy Mon GE
       using (unbox-def)

open import ClosedCalculus.EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE

-- Extending the environment commutes with sequencing: if `g` extends the
-- environment and `f` undoes the extension, then reindexing the whole `⨟`
-- along `g` is reindexing only the sequenced computation, the continuation
-- being reindexed under the lock instead (which is what the equations'
-- `cong-⟨⟩-ren wk-ren` does).

-- The `μᵀ`-free core: the same statement about the strengthened continuation
-- alone. `handle` puts its sub-computation in the same position as `⨟` but
-- under `T-alg-of-handlerᵀ` rather than `μᵀ`, so the handling equations reuse
-- this directly.

str-extend : ∀ {X Y A B ε ε'}
           → (m : Y →ᵐ Tᵒ A ε)
           → (n : ⟨ mapᵉ ε ⟩ᵒ X ×ᵐ A →ᵐ Tᵒ B ε')
           → (g : X →ᵐ Y) → (f : Y →ᵐ X)
           → f ∘ᵐ g ≈ᵐ idᵐ
           →    Tᶠ (n ∘ᵐ mapˣᵐ (⟨ mapᵉ ε ⟩ᶠ f) idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ ∘ᵐ g
             ≈ᵐ Tᶠ n ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ∘ᵐ g ⟩ᵐ
str-extend m n g f fg =  ∘ᵐ-congˡ (T-∘ᵐ _ _)
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                          ∙ ∘ᵐ-congˡ (strᵀ-natˡ _)
                          ∙ ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                                      ∙ ∘ᵐ-congˡ (mapˣᵐ-∘⟨⟩ _ _ _ _)
                                      ∙ ⟨⟩ᵐ-∘ _ _ _
                                      ∙ ⟨   ∘ᵐ-congˡ (η⊣-nat f)
                                          ∙ ∘ᵐ-assoc _ _ _
                                          ∙ ∘ᵐ-congʳ fg
                                          ∙ ∘ᵐ-identityʳ _
                                        , ∘ᵐ-congˡ (∘ᵐ-identityˡ _) ⟩ᵐ-cong))

seq-extend : ∀ {X Y A B ε ε'}
           → (m : Y →ᵐ Tᵒ A ε)
           → (n : ⟨ mapᵉ ε ⟩ᵒ X ×ᵐ A →ᵐ Tᵒ B ε')
           → (g : X →ᵐ Y) → (f : Y →ᵐ X)
           → f ∘ᵐ g ≈ᵐ idᵐ
           →    μᵀ ∘ᵐ Tᶠ (n ∘ᵐ mapˣᵐ (⟨ mapᵉ ε ⟩ᶠ f) idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ ∘ᵐ g
             ≈ᵐ μᵀ ∘ᵐ Tᶠ n ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ∘ᵐ g ⟩ᵐ
seq-extend m n g f fg = ∘ᵐ-congʳ (str-extend m n g f fg)


-- The unit law: sequencing a `return` is substitution. The environment the
-- continuation is given is the transposed one, which at the unit grade is the
-- possibility unit `η` (`η⊣-≤` down to `uᵣ`, then `η⊣-u`).

εᵇ-η⊣-u : ∀ {X ρ} → (e : ρ ≃ᵣ uᵣ)
        → εᵇ ∘ᵐ []-≤ (≃ᵣ⇒≿ᵣ e) ∘ᵐ η⊣ {X} {ρ}
        ≈ᵐ ⟨⟩-≤ (≃ᵣ⇒≿ᵣ e) ∘ᵐ η
εᵇ-η⊣-u {X} e =
    ∘ᵐ-congʳ (η⊣-≤ (≃ᵣ⇒≿ᵣ e))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-ε-nat _))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ∘ᵐ-congʳ η⊣-u
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-ε-nat _))
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ []-ε∘ηᵘ≡id
              ∙ ∘ᵐ-identityʳ _)

sound-seq-return : ∀ {Γ A B ε} → (V : Γ ⊢V⦂ A) → (M : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
                 → Soundᶜ== (seq-return V M)
sound-seq-return {Γ} {A} {B} {ε} V M (pV , pM) pR =
    ∘ᵐ-congʳ (  ∘ᵐ-congʳ (  ∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                              ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
                          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                          ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
                          ∙ ∘ᵐ-assoc _ _ _)
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ηᵀ-nat _))
              ∙ ∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ T-μ∘η≡id
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                        ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ εᵇ-η⊣-u {⟦ Γ ⟧ᶜᵗˣ} map-uᵉ
                          , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-≃ (≃ₑ-sym (·ₑ-identityˡ ε)) ((C-rename r M) [ split-[] ↦ V ]c))
                pR pRc
            ∙ sound-ε-≃ (≃ₑ-sym (·ₑ-identityˡ ε)) ((C-rename r M) [ split-[] ↦ V ]c) pRc
            ∙ ∘ᵐ-congʳ (  C-subst-nat (C-rename r M) split-[] V (renᶜ r M pM) pV
                        ∙ ∘ᵐ-congˡ (C-rename-nat r M pM)
                        ∙ ∘ᵐ-assoc _ _ _
                        ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                    ∙ ⟨ ∘ᵐ-identityʳ _
                                        ∙ ∘ᵐ-congˡ (⟨⟩-≤-irr _ _)
                                      , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  where
    r   = cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren)
    pRc = subᶜ (C-rename r M) split-[] V (renᶜ r M pM) pV

-- The counit law: sequencing a `return` of the bound variable is the identity.

sound-seq-eta : ∀ {Γ A ε} → (M : Γ ⊢C⦂ A ‼ ε) → Soundᶜ== (seq-eta M)
sound-seq-eta {Γ} {A} {ε} M pM pN =
    ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-≃ (·ₑ-identityʳ ε) (M ⨟ return (var (λ _ → ≾ᵣ-refl) Hd)))
                pN (pM , tt)
            ∙ sound-ε-≃ (·ₑ-identityʳ ε)
                (M ⨟ return (var (λ _ → ≾ᵣ-refl) Hd)) (pM , tt)
            ∙ ∘ᵐ-congʳ seq-body
            ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
            ∙ ∘ᵐ-congˡ (T-≤-trans _ _ ≾ₑ-refl ∙ T-≤-refl _)
            ∙ ∘ᵐ-identityˡ _)
  where
    -- `M ⨟ return x` folds to `μᵀ ∘ Tᶠ ηᵀ` after the strength projects (`x`
    -- is the bound variable `sndᵐ`), which the monad's right unit collapses.
    seq-body : ⟦ M ⨟ return (var (λ _ → ≾ᵣ-refl) Hd) ⟧ᶜᵗ (pM , tt)
             ≈ᵐ T-≤ (≃ₑ⇒≿ₑ (·ₑ-identityʳ ε)) ∘ᵐ ⟦ M ⟧ᶜᵗ pM
    seq-body =
        ∘ᵐ-congʳ (  ∘ᵐ-congˡ (T-congᶠ (∘ᵐ-congʳ (var-morphism-Hd {Γ ⟨ mapᵉ ε ⟩} {A} _)))
                  ∙ ∘ᵐ-congˡ (T-∘ᵐ _ _)
                  ∙ ∘ᵐ-assoc _ _ _
                  ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                              ∙ ∘ᵐ-congˡ strᵀ-sndᵐ
                              ∙ ⟨⟩ᵐ-sndᵐ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ T-μ∘Tη≡id

-- `seq-box`/`seq-unbox`: a resource binder commutes with sequencing.

sound-seq-box : ∀ {Γ A B C ρ ε ε'}
              → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A) → (M : Γ ∷ [ ρ ] A ⊢C⦂ B ‼ ε)
              → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
              → Soundᶜ== (seq-box V M N)
sound-seq-box {ρ = ρ} V M N ((pV , pM) , pN) pR =
    ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (box _ V (M ⨟ C-rename r N)) pR (pV , (pM , renᶜ r N pN))
            ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (C-rename-nat r N pN))))
            ∙ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
            ∙ seq-extend (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN) g fstᵐ (⟨⟩ᵐ-fstᵐ _ _))
  where
    r = cong-∷-ren (cong-⟨⟩-ren wk-ren)
    g = ⟨ idᵐ , [ ρ ]ᶠ (⟦ V ⟧ᵛᵗ pV) ∘ᵐ η⊣ ⟩ᵐ

sound-seq-unbox : ∀ {Γ A A₀ B C ρ₀ ρ' ε ε'}
                → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ) → (rel : ρ' ≾ᵣ ρ₀) → (w : A₀ <:ᵛ A)
                → (M : Γ ∷ A ⊢C⦂ B ‼ ε) → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
                → Soundᶜ== (seq-unbox x rel w M N)
sound-seq-unbox {ε = ε} x rel w M N (pM , pN) pR =
    ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (unbox x rel w (M ⨟ C-rename r N)) pR (pM , renᶜ r N pN)
            ∙ unbox-def x rel w (M ⨟ C-rename r N) (pM , renᶜ r N pN)
            ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (C-rename-nat r N pN))))
            ∙ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
            ∙ seq-extend (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN) g fstᵐ (⟨⟩ᵐ-fstᵐ _ _)
            ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
                (⟨ ≈ᵐ-refl , ≈ᵐ-sym (unbox-def x rel w M pM) ⟩ᵐ-cong))))
  where
    r = cong-∷-ren (cong-⟨⟩-ren wk-ren)
    g = ⟨ idᵐ , ⟦ w ⟧<:ᵛ ∘ᵐ ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj x ⟩ᵐ




-- The transposed pair, boxed, is exactly the tail that `strᵀ-delayᵀ-algebraicity` produces.

delay-core3 : ∀ {X A ε} → (τ : 𝔻) → (m : ⟨ of-durʳ τ ⟩ᵒ X →ᵐ Tᵒ A ε)
            → [ of-durʳ τ ]ᶠ
                 ⟨ [ mapᵉ ε ]ᶠ (⟨⟩-≤ (≃ᵣ⇒≿ᵣ
                       (≃ᵣ-trans map-·ᵉ (·ᵣ-cong map-of-durᵉ ≃ᵣ-refl))) ∘ᵐ μ)
                     ∘ᵐ η⊣
                 , m ⟩ᵐ
                ∘ᵐ η⊣
            ≈ᵐ []-monoidal
                 ∘ᵐ mapˣᵐ (δ ∘ᵐ []-≤ (≃ᵣ⇒≿ᵣ
                       (≃ᵣ-trans map-·ᵉ (·ᵣ-cong map-of-durᵉ ≃ᵣ-refl)))) idᵐ
                 ∘ᵐ ⟨ η⊣ , [ of-durʳ τ ]ᶠ m ∘ᵐ η⊣ ⟩ᵐ
delay-core3 τ m =
    ∘ᵐ-congˡ (  []-congᶠ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                  ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
              ∙ []-∘ᵐ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym η⊣-monoidal)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ ([]-monoidal-nat _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨   ∘ᵐ-congˡ (  []-congᶠ (∘ᵐ-congˡ ([]-∘ᵐ _ _) ∙ ∘ᵐ-assoc _ _ _)
                            ∙ []-∘ᵐ _ _)
                ∙ ∘ᵐ-assoc _ _ _
                ∙ ∘ᵐ-congʳ (≈ᵐ-sym η⊣-δ)
                ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                ∙ ∘ᵐ-congˡ ([]-δ-nat _)
                ∙ ∘ᵐ-assoc _ _ _
                ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-≤ _))
              , ≈ᵐ-sym (∘ᵐ-identityˡ _) ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (  ⟨ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) , ≈ᵐ-refl ⟩ᵐ-cong
              ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))

-- The `μᵀ`-free core of the delay equation: pulling `delayᵀ` out of a
-- strengthened continuation. `seq-delay` is this plus `delayᵀ-algebraicity`;
-- `handle-delay` is this plus `T-alg-of-handlerᵀ-delayᵀ`.

str-delay : ∀ {X A B ε ε'} → (τ : 𝔻)
          → (m : ⟨ of-durʳ τ ⟩ᵒ X →ᵐ Tᵒ A ε)
          → (n : ⟨ mapᵉ (of-durᵉ τ ·ₑ ε) ⟩ᵒ X ×ᵐ A →ᵐ Tᵒ B ε')
          → Tᶠ n ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , delayᵀ τ ∘ᵐ [ of-durʳ τ ]ᶠ m ∘ᵐ η⊣ ⟩ᵐ
          ≈ᵐ delayᵀ τ
               ∘ᵐ [ of-durʳ τ ]ᶠ
                    (Tᶠ (n ∘ᵐ mapˣᵐ (⟨⟩-≤ (≃ᵣ⇒≿ᵣ
                            (≃ᵣ-trans map-·ᵉ (·ᵣ-cong map-of-durᵉ ≃ᵣ-refl))) ∘ᵐ μ) idᵐ)
                     ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ)
               ∘ᵐ η⊣
str-delay {X} {A} {B} {ε} {ε'} τ m n =
    ∘ᵐ-congʳ (∘ᵐ-congʳ (  ⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _) , ≈ᵐ-refl ⟩ᵐ-cong
                        ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _)))
  ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (strᵀ-delayᵀ-algebraicity {ε = ε} τ))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (delayᵀ-nat τ n))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
                        ∙ ≈ᵐ-sym (delay-core3 {X} {A} {ε} τ m)))
  ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym ([]-∘ᵐ _ _)
                          ∙ []-congᶠ (  ∘ᵐ-assoc _ _ _
                                      ∙ ≈ᵐ-sym (  ∘ᵐ-congˡ (T-∘ᵐ _ _)
                                                ∙ ∘ᵐ-assoc _ _ _
                                                ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                                                            ∙ ∘ᵐ-congˡ (strᵀ-natˡ _)
                                                            ∙ ∘ᵐ-assoc _ _ _
                                                            ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                                                        ∙ ⟨ ≈ᵐ-refl
                                                                          , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))))))

sound-seq-delay : ∀ {Γ A B τ ε ε'}
                → (M : Γ ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε)
                → (N : Γ ⟨ mapᵉ (of-durᵉ τ ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
                → Soundᶜ== (seq-delay M N)
sound-seq-delay {Γ} {A} {B} {τ} {ε} {ε'} M N (pM , pN) pR =
    ∘ᵐ-congʳ (str-delay τ (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (delayᵀ-algebraicity τ)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                          ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym ([]-∘ᵐ _ _)
                                      ∙ []-congᶠ (∘ᵐ-congʳ (∘ᵐ-congˡ (
                                          ≈ᵐ-sym (  T-congᶠ (C-rename-nat r N pN)
                                                  ∙ T-congᶠ (∘ᵐ-congʳ (mapˣᵐ-cong
                                                      (∘ᵐ-congˡ (⟨⟩-≤-irr _ _))
                                                      ≈ᵐ-refl)))))))))
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-≃ e (delay τ (M ⨟ C-rename r N)))
                pR pRc
            ∙ sound-ε-≃ e (delay τ (M ⨟ C-rename r N)) pRc)
  where
    e = ≃ₑ-sym (·ₑ-assoc (of-durᵉ τ) ε ε')
    rin = ⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ (≃ᵣ-trans map-·ᵉ (·ᵣ-cong map-of-durᵉ ≃ᵣ-refl)))
          ∘ʳ ⟨⟩-μ-ren
    r   = cong-∷-ren rin
    pRc = pM , renᶜ r N pN

sound-seq-perform : ∀ {Γ A B ε ε' op}
                  → (V : Γ ⊢V⦂ type-of-gtype (param op))
                  → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
                  → (N : Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
                  → Soundᶜ== (seq-perform V M N)
sound-seq-perform {Γ} {A} {B} {ε} {ε'} {op} V M N ((pV , pM) , pN) pR =
    ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-≃ e' (perform op V (M ⨟ C-rename r' N)))
                pR pRc'
            ∙ sound-ε-≃ e' (perform op V (M ⨟ C-rename r' N)) pRc'
            ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                , ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (substᵈ-≈ (ty-gty (arity op)) (
                    ∘ᵐ-congʳ (
                        ∘ᵐ-congˡ (T-congᶠ (C-rename-nat r' N pN) ∙ T-∘ᵐ _ _)
                      ∙ ∘ᵐ-assoc _ _ _
                      ∙ ∘ᵐ-congʳ (
                          ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                        ∙ ∘ᵐ-congˡ (strᵀ-natˡ ⟦ rin' ⟧ʳ)
                        ∙ ∘ᵐ-assoc _ _ _
                        ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                    ∙ ⟨ ∘ᵐ-congˡ ([]-congᶠ (∘ᵐ-congˡ (∘ᵐ-congˡ
                                          (⟨⟩-≤-irr _ _))))
                                      , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))))))
                ⟩ᵐ-cong))
            ∙ ≈ᵐ-sym (
                ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (
                    ⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _) , ≈ᵐ-refl ⟩ᵐ-cong
                  ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))))
              ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
                    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ (strᵀ-opᵀ-algebraicity op)))
              ∙ ∘ᵐ-congʳ (
                    ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
                  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (opᵀ-nat op _)))
              ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (opᵀ-algebraicity op)
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
                    ∘ᵐ-congʳ (∘ᵐ-congʳ (
                        ∘ᵐ-assoc _ _ _
                      ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                                  ∙ ⟨   ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-fstᵐ _ _
                                      ,   ⟨⟩ᵐ-∘ _ _ _
                                        ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _
                                          , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong ⟩ᵐ-cong)
                      ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
                  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)
                  ∙ mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
              ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl ,
                    ∘ᵐ-congʳ (∘ᵐ-congʳ (
                        ∘ᵐ-assoc _ _ _
                      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ≈ᵐ-sym (
                            ∘ᵐ-congˡ (  []-congᶠ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                                          ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
                                      ∙ []-∘ᵐ _ _)
                          ∙ ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (≈ᵐ-sym η⊣-monoidal)
                          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                          ∙ ∘ᵐ-congˡ ([]-monoidal-nat _ _)
                          ∙ ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)
                          ∙ ∘ᵐ-congʳ (⟨   ∘ᵐ-congˡ (  []-congᶠ (∘ᵐ-congˡ ([]-∘ᵐ _ _) ∙ ∘ᵐ-assoc _ _ _)
                                                    ∙ []-∘ᵐ _ _)
                                        ∙ ∘ᵐ-assoc _ _ _
                                        ∙ ∘ᵐ-congʳ (≈ᵐ-sym η⊣-δ)
                                        ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                                        ∙ ∘ᵐ-congˡ ([]-δ-nat _)
                                        ∙ ∘ᵐ-assoc _ _ _
                                        ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-≤ _))
                                      , ≈ᵐ-sym (∘ᵐ-identityˡ _) ⟩ᵐ-cong)
                          ∙ ∘ᵐ-congʳ (  ⟨ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) , ≈ᵐ-refl ⟩ᵐ-cong
                                      ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))))))
                  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
                        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                      ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym ([]-∘ᵐ _ _)
                                  ∙ []-congᶠ (  ∘ᵐ-assoc _ _ _
                                              ∙ ∘ᵐ-congʳ (exp-strᵐ-⟨⟩ _ _)
                                              ∙ map⇒ᵐ-curryᵐ _ _))))
                  ∙ ∘ᵐ-congʳ (
                        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _) ∙ []-congᶠ (map⇒ᵐ-curryᵐ _ _)))
                  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _) ∙ []-congᶠ (map⇒ᵐ-curryᵐ _ _))
                  ∙ ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (c4 (ty-gty (arity op)))))
                  ⟩ᵐ-cong))))
  where
    e' = ≃ₑ-sym (·ₑ-assoc (op-grade op) ε ε')
    rin' = (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren
    r'   = cong-∷-ren rin'
    pRc' = pV , (pM , renᶜ r' N pN)
    -- The arity type occurs (a) in the continuation `M`'s domain and (b) in the
    -- environment box `η⊣ ∘ fstᵐ`; transporting it commutes with both. At `refl`
    -- the two boxed environments agree by `η⊣`-naturality.
    c4 : ∀ {O} → (eq : ⟦ type-of-gtype (arity op) ⟧ᵛ ≡ O)
       → μᵀ ∘ᵐ Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ
           ∘ᵐ ⟨ ([ mapᵉ ε ]ᶠ (⟨⟩-≤ (≃ᵣ⇒≿ᵣ map-·ᵉ) ∘ᵐ μ) ∘ᵐ η⊣) ∘ᵐ fstᵐ
              , subst (λ O' → ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ ×ᵐ O' →ᵐ Tᵒ ⟦ A ⟧ᵛ ε)
                      eq (⟦ M ⟧ᶜᵗ pM) ⟩ᵐ
       ≈ᵐ subst (λ O' → ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ ×ᵐ O' →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε ·ₑ ε'))
                eq (μᵀ ∘ᵐ Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ
                      ∘ᵐ ⟨ [ mapᵉ ε ]ᶠ ((⟨⟩-≤ (≃ᵣ⇒≿ᵣ map-·ᵉ) ∘ᵐ μ)
                                         ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ) ∘ᵐ η⊣
                         , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ)
    c4 refl =
      ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨   ∘ᵐ-assoc _ _ _
                                      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat fstᵐ))
                                      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                                      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
                                    , ≈ᵐ-refl ⟩ᵐ-cong)))


