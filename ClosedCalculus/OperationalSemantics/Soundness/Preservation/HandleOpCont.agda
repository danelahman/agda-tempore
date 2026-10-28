------------------------------------------------------------------------
-- The HANDLE-OP continuation lemma.                                     --
--                                                                    --
-- `sound-HANDLE-OP`'s reduct boxes up the handled remainder as a        --
-- continuation: `handle M with H' in N'`, where `H'` is `H` renamed by  --
-- `barrier-wk-ren` (its clauses now sit behind the barrier of the       --
-- extended ambient) and `N'` is `N` renamed by the commuting            --
-- conversion. This lemma reconciles that inner handle's interpretation   --
-- with the handler's fold at the ambient context `Γ`, its parameter      --
-- reindexed along the clause renaming: `⟦H'⟧ʰᵗ`-naturality for the       --
-- renaming, `T-alg-of-handlerᵀ-natᴾ`, and the barrier at `wk-ren`.       --
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

module ClosedCalculus.OperationalSemantics.Soundness.Preservation.HandleOpCont
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

open import Language.Types                   S
open import ClosedCalculus.Syntax.Contexts   S
open import ClosedCalculus.Syntax.Terms      S
open import ClosedCalculus.Syntax.Renamings  S
open import ClosedCalculus.Syntax.RenActions S using (C-rename)

open Category Cat
open Future Fut
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; μ; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ; ⟨⟩-≤-nat; ⟨⟩-≤-irr;
                    ⟨⟩-≤-trans; μ-≤ˡ)
open Adjunction Adj using (η⊣; η⊣-nat)
open GroundTypes GTy using (⟦_⟧ᵍ)
open Monad Mon

open import ClosedCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj
       using (Eternalᵒ; ⟨⊤⟩-eternalᵒ; ⟨⊤⟩-η; ⟨⊤⟩-μ; ⟨⊤⟩-μ-nat; ⟨⊤⟩-μ∘μ≡μ∘Tμ;
              ⟨⊤⟩-μ∘Tη≡id; ⟨⊤⟩-η-nat; free-extᵉ-nat; free-necᵉ-nat; barrier-μ;
              barrier-lock)

open import ClosedCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE

infixr 3 _∙_
_∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
_∙_ = ≈ᵐ-trans

bcᴱ : ∀ (Γ : Ctx) → Eternalᵒ ⟦ Γ ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ
bcᴱ Γ = ⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ

-- `free-extᵉ-nat`, `free-necᵉ-nat`, `barrier-μ`, `barrier-lock` are facts
-- about the free `⟨⊤⟩`-algebra, imported above from `Eternal`. `free-necᵉ-nat`
-- applied to `free-extᵉ-nat` is the coalgebra-morphism premise of
-- `T-alg-of-handlerᵀ-natᴾ` that every reindexing of a handler's parameter
-- has to discharge.

-- The inner handle's interpretation equals the outer fold applied to the
-- (renamed) sequel. `H'` renames `H`'s clauses along `barrier-wk-ren`, so this
-- is the renaming coherence of the handler at that renaming, with the fold's
-- parameter reindexed along the same renaming.
module _ {Γ : Ctx} {A₀ A B : VType} {ρ σ : _} {ε ε' : E}
         (H : (op' : Op) → (ε₀ : E)
              → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op')
                   ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε₀)
                ⊢C⦂ B ‼ (op-grade op' ·ₑ ε₀))
         (M : Γ ⟨ ρ ⟩ ∷ A₀ ⊢C⦂ A ‼ ε)
         (N : Γ ⟨ σ ⟩ ∷ A ⊢C⦂ B ‼ ε')
         (ren : Ren [] ((Γ ⟨ ρ ⟩ ∷ A₀) ⟨ mapᵉ ε ⟩) (Γ ⟨ σ ⟩))
         (pM : Paramᶜ M) (pN : Paramᶜ N)
         (pH : ∀ op' ε₀ → Paramᶜ (H op' ε₀))
         (uH : ∀ (op' : Op) {ε₁ ε₂} → (q : ε₁ ≾ₑ ε₂)
             → ⟦ H op' ε₂ ⟧ᶜᵗ (pH op' ε₂)
                 ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op') ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
             ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H op' ε₁ ⟧ᶜᵗ (pH op' ε₁))
       where

  -- The reduct's clause family: `H` re-barred along `barrier-wk-ren`, with the
  -- renamed parametricity and uniformity certificates.
  H' : (op' : Op) → (ε₀ : E)
     → ((Γ ⟨ ρ ⟩) ∷ A₀) ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op')
          ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε₀)
       ⊢C⦂ B ‼ (op-grade op' ·ₑ ε₀)
  H' op' ε₀ = C-rename (cong-∷-ren (cong-∷-ren (barrier-wk-ren ρ A₀))) (H op' ε₀)

  pH' : ∀ op' ε₀ → Paramᶜ (H' op' ε₀)
  pH' op' ε₀ =
    renᶜ (cong-∷-ren (cong-∷-ren (barrier-wk-ren ρ A₀))) (H op' ε₀) (pH op' ε₀)

  uH' = ren-clauses-uniform (barrier-wk-ren ρ A₀) H pH uH

  handle-op-cont :
      ⟦ handle M `with H' `in (C-rename (cong-∷-ren ren) N) ⟧ᶜᵗ
        (pM , renᶜ (cong-∷-ren ren) N pN , pH' , uH')
    ≈ᵐ T-alg-of-handlerᵀ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H pH uH)
       ∘ᵐ ⟨ (Eternalᵒ.extᵉ (bcᴱ Γ) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (⟨⊤⟩-η {⟦ Γ ⟧ᶜᵗˣ})) ∘ᵐ fstᵐ
          ,   Tᶠ (⟦ N ⟧ᶜᵗ pN ∘ᵐ mapˣᵐ ⟦ ren ⟧ʳ idᵐ)
            ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ ⟩ᵐ
  handle-op-cont =
      ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , seq-eq ⟩ᵐ-cong)
    ∙ ∘ᵐ-congˡ alg-nat
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)
    ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-sym barrier-wk , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
    where
      f : ⟦ ((Γ ⟨ ρ ⟩) ∷ A₀) ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ
      f = ⟦ barrier-wk-ren {Γ} ρ A₀ ⟧ʳ

      -- `f` is the free-algebra morphism induced by `g`
      g : ⟦ (Γ ⟨ ρ ⟩) ∷ A₀ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ
      g = ⟨⟩-≤ (≾-⊤ᵣ ρ) ∘ᵐ fstᵐ

      f≈ : f ≈ᵐ ⟨⊤⟩-μ ∘ᵐ ⟨ ⊤ᵣ ⟩ᶠ g
      f≈ =
          ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
        ∙ ∘ᵐ-congˡ (barrier-μ (≾-⊤ᵣ (ρ ·ᵣ ⊤ᵣ)))
        ∙ ∘ᵐ-assoc _ _ _
        ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))

      -- the barrier is untouched by the arity binder
      barrier-wk : (Eternalᵒ.extᵉ (bcᴱ Γ) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (⟨⊤⟩-η {⟦ Γ ⟧ᶜᵗˣ})) ∘ᵐ fstᵐ
                 ≈ᵐ f ∘ᵐ ⟨⊤⟩-η
      barrier-wk =
          ∘ᵐ-congˡ (barrier-lock {⟦ Γ ⟧ᶜᵗˣ} {ρ})
        ∙ ≈ᵐ-sym (  ∘ᵐ-congˡ f≈
                  ∙ ∘ᵐ-assoc _ _ _
                  ∙ ∘ᵐ-congʳ (⟨⊤⟩-η-nat g)
                  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ (Eternalᵒ.α-unit (bcᴱ Γ))
                  ∙ ∘ᵐ-identityˡ _)

      -- the renamed sequel commutes back to the un-renamed one under `Tᶠ`
      seq-eq : Tᶠ (⟦ C-rename (cong-∷-ren ren) N ⟧ᶜᵗ (renᶜ (cong-∷-ren ren) N pN))
                 ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ
             ≈ᵐ Tᶠ (⟦ N ⟧ᶜᵗ pN ∘ᵐ mapˣᵐ ⟦ ren ⟧ʳ idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ
      seq-eq = ∘ᵐ-congˡ (T-congᶠ (C-rename-nat (cong-∷-ren ren) N pN))

      -- the inner (renamed) handler equals the outer one reindexed by `f`
      ⟦H'⟧ʰᵗ-nat : ∀ op ε''
                 → clauseᵀ (⟦_⟧ʰᵗ {(Γ ⟨ ρ ⟩) ∷ A₀} H' pH' uH') op ε''
                 ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {Γ} H pH uH) op ε'' ∘ᵐ mapˣᵐ f idᵐ
      ⟦H'⟧ʰᵗ-nat op ε'' =
          ∘ᵐ-congˡ (C-rename-nat (cong-∷-ren (cong-∷-ren (barrier-wk-ren ρ A₀)))
                      (H op ε'') (pH op ε''))
        ∙ ∘ᵐ-assoc _ _ _
        ∙ ∘ᵐ-congʳ (adapt-commute _ _ _)
        ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

      f-necᵉ : ∀ {ρ₁} → [ ρ₁ ]ᶠ f ∘ᵐ Eternalᵒ.necᵉ (bcᴱ ((Γ ⟨ ρ ⟩) ∷ A₀))
                      ≈ᵐ Eternalᵒ.necᵉ (bcᴱ Γ) ∘ᵐ f
      f-necᵉ {ρ₁} =
          ∘ᵐ-congˡ ([]-congᶠ f≈)
        ∙ free-necᵉ-nat (⟨⊤⟩-μ ∘ᵐ ⟨ ⊤ᵣ ⟩ᶠ g) (free-extᵉ-nat g)
        ∙ ∘ᵐ-congʳ (≈ᵐ-sym f≈)

      alg-nat : T-alg-of-handlerᵀ (bcᴱ ((Γ ⟨ ρ ⟩) ∷ A₀)) (⟦_⟧ʰᵗ {(Γ ⟨ ρ ⟩) ∷ A₀} H' pH' uH')
              ≈ᵐ T-alg-of-handlerᵀ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H pH uH) ∘ᵐ mapˣᵐ f idᵐ
      alg-nat =
        T-alg-of-handlerᵀ-natᴾ (bcᴱ Γ) (bcᴱ ((Γ ⟨ ρ ⟩) ∷ A₀)) f f-necᵉ
          (⟦_⟧ʰᵗ {Γ} H pH uH) _ ⟦H'⟧ʰᵗ-nat
