------------------------------------------------------------------------
-- Soundness of the sequencing equations.                              --
--                                                                    --
-- `M ⨟ N` denotes `μᵀ ∘ Tᶠ ⟦N⟧ ∘ strᵀ ∘ ⟨ η⊣ , ⟦M⟧ ⟩`, so its         --
-- equations are the graded monad's laws threaded through the strength: --
-- `seq-return` is `T-μ∘η≡id` after `strᵀ-ηᵀ`, `seq-eta` is             --
-- `T-μ∘Tη≡id` after `strᵀ-sndᵐ`.                                       --
--                                                                    --
-- `seq-box`/`seq-unbox` say that a resource binder commutes with       --
-- sequencing. Both binders denote `⟦M⟧ ∘ ⟨ idᵐ , _ ⟩ᵐ` — an            --
-- environment extension that the first projection undoes — which is    --
-- exactly the premise of the shared `seq-extend` below.                --
--                                                                    --
-- `seq-delay` says `delay` is algebraic: `delayᵀ` pulls out of `⨟`     --
-- (`strᵀ-delayᵀ-algebraicity`, `delayᵀ-nat`, `delayᵀ-algebraicity`),   --
-- the continuation's `⟨⟩-μ-ren` re-lock realigning the two graded locks --
-- via `η⊣-δ` / `[]-δ-nat`.                                             --
--                                                                    --
-- `seq-perform` is the same for `opᵀ` (`strᵀ-opᵀ-algebraicity`,        --
-- `opᵀ-nat`, `opᵀ-algebraicity`): the lock-split core is reused,        --
-- wrapped by the operation continuation's `exp-strᵐ`/`map⇒ᵐ`, with the  --
-- arity's `ty-gty` transport threaded through the pair.                 --
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

module EquationalTheory.Soundness.Seq
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
open import Syntax.RenActions    S using (V-rename; C-rename; unbox⇒var)
open import Syntax.Substitutions S

open import EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-≤; []-∘ᵐ; []-congᶠ; []-ε-nat; []-ε∘ηᵘ≡id; ηᵘ;
                       δ; []-monoidal; []-δ-nat; []-monoidal-nat)
                renaming (ε to εᵇ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; μ; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ)
open Adjunction Adj using (η⊣; η⊣-nat; η⊣-≤; η⊣-u; ε⊣; η⊣-δ; η⊣-monoidal)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE

open import DenotationalSemantics.Soundness.Preservation.Unbox S Cat Fut Pst Adj GTy Mon GE
       using (unbox-def)

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE

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

εᵇ-η⊣-u : ∀ {X ρ} → (e : ρ ≡ uᵣ)
        → εᵇ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym e)) ∘ᵐ η⊣ {X} {ρ}
        ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym e)) ∘ᵐ η
εᵇ-η⊣-u {X} e =
    ∘ᵐ-congʳ (η⊣-≤ (≾ᵣ-reflexive (sym e)))
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
    -- `return` sequenced: the strength's unit law, then the monad's
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
    -- the environment the continuation receives is the transposed one
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                        ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ εᵇ-η⊣-u {⟦ Γ ⟧ᶜᵗˣ} map-uᵉ
                          , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
    -- which is what the right-hand side's renaming and substitution build
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-subst (sym (·ₑ-identityˡ ε)) ((C-rename r M) [ Hd ↦ V ]c))
                pR (ε-substᴾ (sym (·ₑ-identityˡ ε)) _ pRc)
            ∙ sound-ε-subst (sym (·ₑ-identityˡ ε)) ((C-rename r M) [ Hd ↦ V ]c) pRc
            ∙ ∘ᵐ-congʳ (  C-subst-nat (C-rename r M) Hd V (renᶜ r M pM) pV
                        ∙ ∘ᵐ-congˡ (C-rename-nat r M pM)
                        ∙ ∘ᵐ-assoc _ _ _
                        ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                    ∙ ⟨ ∘ᵐ-identityʳ _
                                        ∙ ∘ᵐ-congˡ (eq-ren-grade {Γ} map-uᵉ)
                                      , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  where
    r   = cong-∷-ren (⟨⟩-η-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-uᵉ))
    pRc = subᶜ (C-rename r M) Hd V (renᶜ r M pM) pV

-- The counit law: sequencing a `return` of the bound variable is the identity.

sound-seq-eta : ∀ {Γ A ε} → (M : Γ ⊢C⦂ A ‼ ε) → Soundᶜ== (seq-eta M)
sound-seq-eta {Γ} {A} {ε} M pM pN =
    ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-subst (·ₑ-identityʳ ε) (M ⨟ return (var (λ _ → ≾ᵣ-refl) Hd)))
                pN (ε-substᴾ (·ₑ-identityʳ ε) _ (pM , tt))
            ∙ sound-ε-subst (·ₑ-identityʳ ε)
                (M ⨟ return (var (λ _ → ≾ᵣ-refl) Hd)) (pM , tt)
            ∙ ∘ᵐ-congʳ seq-body
            ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
            ∙ ∘ᵐ-congˡ (  ε-substᵀ-trans (sym (·ₑ-identityʳ ε)) (·ₑ-identityʳ ε)
                        ∙ ≡→≈ᵐ (cong ε-substᵀ (uip {p = trans (sym (·ₑ-identityʳ ε))
                                                              (·ₑ-identityʳ ε)}
                                                   {q = refl}))
                        ∙ ε-substᵀ-refl)
            ∙ ∘ᵐ-identityˡ _)
  where
    -- `M ⨟ return x` folds to `μᵀ ∘ Tᶠ ηᵀ` after the strength projects (`x`
    -- is the bound variable `sndᵐ`), which the monad's right unit collapses.
    seq-body : ⟦ M ⨟ return (var (λ _ → ≾ᵣ-refl) Hd) ⟧ᶜᵗ (pM , tt)
             ≈ᵐ ε-substᵀ (sym (·ₑ-identityʳ ε)) ∘ᵐ ⟦ M ⟧ᶜᵗ pM
    seq-body =
        ∘ᵐ-congʳ (  ∘ᵐ-congˡ (T-congᶠ (∘ᵐ-congʳ (var-morphism-Hd {Γ ⟨ mapᵉ ε ⟩} {A} _)))
                  ∙ ∘ᵐ-congˡ (T-∘ᵐ _ _)
                  ∙ ∘ᵐ-assoc _ _ _
                  ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                              ∙ ∘ᵐ-congˡ strᵀ-sndᵐ
                              ∙ ⟨⟩ᵐ-sndᵐ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ T-μ∘Tη≡id

-- `seq-box`/`seq-unbox`: a resource binder commutes with sequencing. The
-- binder denotes precomposition by an environment extension `g` (undone by
-- `fstᵐ`), and the continuation's renaming `cong-∷-ren (cong-⟨⟩-ren wk-ren)`
-- denotes exactly the `mapˣᵐ (⟨ mapᵉ ε ⟩ᶠ fstᵐ) idᵐ` that `seq-extend` moves.

sound-seq-box : ∀ {Γ A B C ρ ε ε'}
              → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A) → (M : Γ ∷ [ ρ ] A ⊢C⦂ B ‼ ε)
              → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
              → Soundᶜ== (seq-box V M N)
sound-seq-box {ρ = ρ} V M N ((pV , pM) , pN) pR =
    ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (box V (M ⨟ C-rename r N)) pR (pV , (pM , renᶜ r N pN))
            ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (C-rename-nat r N pN))))
            ∙ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
            ∙ seq-extend (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN) g fstᵐ (⟨⟩ᵐ-fstᵐ _ _))
  where
    r = cong-∷-ren (cong-⟨⟩-ren wk-ren)
    g = ⟨ idᵐ , [ ρ ]ᶠ (⟦ V ⟧ᵛᵗ pV) ∘ᵐ η⊣ ⟩ᵐ

sound-seq-unbox : ∀ {Γ A B C ρ Δ ε ε'}
                → (w : Ren (Δ ⟨ ρ ⟩) Γ) → (V : Δ ⊢V⦂ [ ρ ] A)
                → (M : Γ ∷ A ⊢C⦂ B ‼ ε) → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
                → Soundᶜ== (seq-unbox w V M N)
sound-seq-unbox {ε = ε} w V M N ((pV , pM) , pN) pR =
    ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (unbox w V (M ⨟ C-rename r N)) pR (pV , (pM , renᶜ r N pN))
            ∙ unbox-def w V (M ⨟ C-rename r N) pV (pM , renᶜ r N pN)
            ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (C-rename-nat r N pN))))
            ∙ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
            ∙ seq-extend (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN) g fstᵐ (⟨⟩ᵐ-fstᵐ _ _)
            ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
                (⟨ ≈ᵐ-refl , ≈ᵐ-sym (unbox-def w V M pV pM) ⟩ᵐ-cong))))
  where
    r = cong-∷-ren (cong-⟨⟩-ren wk-ren)
    g = ⟨ idᵐ , ε⊣ ∘ᵐ ⟨⟩-≤ (proj₂ (proj₂ (unbox⇒var w V)))
                    ∘ᵐ var-proj (proj₁ (proj₂ (unbox⇒var w V))) ⟩ᵐ




-- The transposed pair, boxed, is exactly the tail that
-- `strᵀ-delayᵀ-algebraicity` produces: `η⊣-monoidal` supplies the diagonal,
-- `[]-δ-nat`/`η⊣-δ` split the lock `of-natʳ τ ·ᵣ mapᵉ ε`, and `η⊣-≤` relaxes it.

delay-core3 : ∀ {X A ε} → (τ : ℕ) → (m : ⟨ of-natʳ τ ⟩ᵒ X →ᵐ Tᵒ A ε)
            → [ of-natʳ τ ]ᶠ
                 ⟨ [ mapᵉ ε ]ᶠ (⟨⟩-≤ (≾ᵣ-reflexive
                       (sym (trans map-·ᵉ (cong (_·ᵣ mapᵉ ε) map-of-natᵉ)))) ∘ᵐ μ)
                     ∘ᵐ η⊣
                 , m ⟩ᵐ
                ∘ᵐ η⊣
            ≈ᵐ []-monoidal
                 ∘ᵐ mapˣᵐ (δ ∘ᵐ []-≤ (≾ᵣ-reflexive
                       (sym (trans map-·ᵉ (cong (_·ᵣ mapᵉ ε) map-of-natᵉ))))) idᵐ
                 ∘ᵐ ⟨ η⊣ , [ of-natʳ τ ]ᶠ m ∘ᵐ η⊣ ⟩ᵐ
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

str-delay : ∀ {X A B ε ε'} → (τ : ℕ)
          → (m : ⟨ of-natʳ τ ⟩ᵒ X →ᵐ Tᵒ A ε)
          → (n : ⟨ mapᵉ (of-natᵉ τ ·ₑ ε) ⟩ᵒ X ×ᵐ A →ᵐ Tᵒ B ε')
          → Tᶠ n ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ m ∘ᵐ η⊣ ⟩ᵐ
          ≈ᵐ delayᵀ τ
               ∘ᵐ [ of-natʳ τ ]ᶠ
                    (Tᶠ (n ∘ᵐ mapˣᵐ (⟨⟩-≤ (≾ᵣ-reflexive
                            (sym (trans map-·ᵉ (cong (_·ᵣ mapᵉ ε) map-of-natᵉ)))) ∘ᵐ μ) idᵐ)
                     ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ)
               ∘ᵐ η⊣
str-delay {X} {A} {B} {ε} {ε'} τ m n =
    -- p1: factor `delayᵀ τ` out of the pair
    ∘ᵐ-congʳ (∘ᵐ-congʳ (  ⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _) , ≈ᵐ-refl ⟩ᵐ-cong
                        ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _)))
    -- p2: the strength's delay-algebraicity
  ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (strᵀ-delayᵀ-algebraicity {ε = ε} τ))
    -- p3: `delayᵀ` commutes past `Tᶠ n`
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (delayᵀ-nat τ n))
    -- recombine the two `[ of-natʳ τ ]ᶠ` factors
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
    -- core3, reversed: rebuild the transposed pair out of the algebraicity tail
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
                        ∙ ≈ᵐ-sym (delay-core3 {X} {A} {ε} τ m)))
    -- and put the re-lock back outside the strength pair
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
                → (M : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
                → (N : Γ ⟨ mapᵉ (of-natᵉ τ ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
                → Soundᶜ== (seq-delay M N)
sound-seq-delay {Γ} {A} {B} {τ} {ε} {ε'} M N (pM , pN) pR =
    -- the strength part is `str-delay`; the continuation's `⟨⟩-μ-ren` denotes
    -- exactly its `φ` (`eq-ren-grade`)
    ∘ᵐ-congʳ (str-delay τ (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN))
    -- then `delayᵀ` is algebraic over `μᵀ`
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (delayᵀ-algebraicity τ)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                          ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym ([]-∘ᵐ _ _)
                                      ∙ []-congᶠ (∘ᵐ-congʳ (∘ᵐ-congˡ (
                                          ≈ᵐ-sym (  T-congᶠ (C-rename-nat r N pN)
                                                  ∙ T-congᶠ (∘ᵐ-congʳ (mapˣᵐ-cong
                                                      (∘ᵐ-congˡ (eq-ren-grade (trans map-·ᵉ
                                                        (cong (_·ᵣ mapᵉ ε) map-of-natᵉ))))
                                                      ≈ᵐ-refl)))))))))
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-subst e (delay τ (M ⨟ C-rename r N)))
                pR (ε-substᴾ e _ pRc)
            ∙ sound-ε-subst e (delay τ (M ⨟ C-rename r N)) pRc)
  where
    e   = sym (·ₑ-assoc (of-natᵉ τ) ε ε')
    rin = ⟨⟩-μ-ren
          ∘ʳ eq-ren (cong (Γ ⟨_⟩) (trans map-·ᵉ (cong (_·ᵣ mapᵉ ε) map-of-natᵉ)))
    r   = cong-∷-ren rin
    pRc = pM , renᶜ r N pN

sound-seq-perform : ∀ {Γ A B ε ε' op}
                  → (V : Γ ⊢V⦂ type-of-gtype (param op))
                  → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
                  → (N : Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
                  → Soundᶜ== (seq-perform V M N)
sound-seq-perform {Γ} {A} {B} {ε} {ε'} {op} V M N ((pV , pM) , pN) pR =
    ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-subst e' (perform op V (M ⨟ C-rename r' N)))
                pR (ε-substᴾ e' _ pRc')
            ∙ sound-ε-subst e' (perform op V (M ⨟ C-rename r' N)) pRc'
            -- segment A: under the param/arity substs, move the continuation's
            -- renaming inside the strength pair by strᵀ-naturality.
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
                                          (eq-ren-grade map-·ᵉ))))
                                      , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))))))
                ⟩ᵐ-cong))
            -- `op` is algebraic: pull `opᵀ op` out of `⨟`.
            ∙ ≈ᵐ-sym (
                -- p1: factor `opᵀ op` out of the pair
                ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (
                    ⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _) , ≈ᵐ-refl ⟩ᵐ-cong
                  ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))))
                -- p2: strᵀ-op algebraicity
              ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
                    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ (strᵀ-opᵀ-algebraicity op)))
                -- p3: opᵀ commutes past `Tᶠ n`
              ∙ ∘ᵐ-congʳ (
                    ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
                  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (opᵀ-nat op _)))
                -- p4: opᵀ is algebraic over `μᵀ`
              ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (opᵀ-algebraicity op)
                -- collapse the `strᵀ-opᵀ-algebraicity` reshape and the three
                -- `mapˣᵐ idᵐ _` layers onto the pair `⟨ Vp , S ⟩`
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
                  -- C2: rebuild the lock-split tail (seq-delay's core3, reversed)
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
                  -- C3: peel `strᵀ` (through `exp-strᵐ`), then `Tᶠ n`, then `μᵀ`
                  -- into the curried continuation
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
                  -- C4: transporting the arity type across the pair — the
                  -- continuation's `subst` and the boxed environment's `fstᵐ`.
                  ∙ ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (c4 (ty-gty (arity op)))))
                  ⟩ᵐ-cong))))
  where
    e'   = sym (·ₑ-assoc (op-grade op) ε ε')
    rin' = cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-·ᵉ)
    r'   = cong-∷-ren rin'
    pRc' = pV , (pM , renᶜ r' N pN)
    -- The arity type occurs (a) in the continuation `M`'s domain and (b) in the
    -- environment box `η⊣ ∘ fstᵐ`; transporting it commutes with both. At `refl`
    -- the two boxed environments agree by `η⊣`-naturality.
    c4 : ∀ {O} → (eq : ⟦ type-of-gtype (arity op) ⟧ᵛ ≡ O)
       → μᵀ ∘ᵐ Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ
           ∘ᵐ ⟨ ([ mapᵉ ε ]ᶠ (⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ) ∘ᵐ η⊣) ∘ᵐ fstᵐ
              , subst (λ O' → ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ ×ᵐ O' →ᵐ Tᵒ ⟦ A ⟧ᵛ ε)
                      eq (⟦ M ⟧ᶜᵗ pM) ⟩ᵐ
       ≈ᵐ subst (λ O' → ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ ×ᵐ O' →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε ·ₑ ε'))
                eq (μᵀ ∘ᵐ Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ
                      ∘ᵐ ⟨ [ mapᵉ ε ]ᶠ ((⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ)
                                         ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ) ∘ᵐ η⊣
                         , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ)
    c4 refl =
      ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨   ∘ᵐ-assoc _ _ _
                                      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat fstᵐ))
                                      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                                      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
                                    , ≈ᵐ-refl ⟩ᵐ-cong)))


