open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundEternal
open import MonomorphicCalculus.DenotationalSemantics.Model.Monad

module MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Step
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import MonomorphicCalculus.Syntax.Types S
open import MonomorphicCalculus.Syntax.Contexts  S
open import MonomorphicCalculus.Syntax.Terms  S
open import MonomorphicCalculus.Syntax.Renaming  S
open import MonomorphicCalculus.Syntax.Renaming.Action S using (V-rename; C-rename; var-rename)
open import MonomorphicCalculus.Syntax.Substitution  S
open import MonomorphicCalculus.Syntax.Substitution.Subsumption  S

open import MonomorphicCalculus.OperationalSemantics.State S
open import MonomorphicCalculus.OperationalSemantics.Reduction           S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-congᶠ; []-idᵐ; []-∘ᵐ; []-≤; []-≤-refl; []-≤-nat;
                       []-ε-nat; []-ε∘ηᵘ≡id; ηᵘ; δ; []-δ-nat; []-monoidal; []-≤-trans;
                       []-monoidal-nat; []-monoidal-fstᵐ; []-monoidal-sndᵐ; []-monoidal-η;
                       []-𝟙-unique) renaming (ε to εᵇ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; μ; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ; ⟨⟩-η-nat; ⟨⟩-μ-nat;
                     ⟨⟩-≤-nat; ⟨⟩-≤-irr; ⟨⟩-≤-refl; ⟨⟩-≤-trans; μ-≤ˡ; μ-≤ʳ;
                     ⟨⟩-μ∘Tη≡id; ⟨⟩-μ∘η≡id)
open Adjunction Adj using (η⊣; η⊣-nat; η⊣-𝟏; η⊣-≤; η⊣-δ; η⊣-monoidal;
                           ε⊣; ε⊣-nat; triangleˡ)
open GroundTypes GTy using (⟦_⟧ᵍ)
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.State S Cat Fut Pst Adj GTy Mon GE

open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Unbox S Cat Fut Pst Adj GTy Mon GE public

-- Splitting the environment box: a box available `ρ₁`-far ahead, where
-- `ρ₁ ⊒ σ ·ᵣ ρ₃`, can be transposed in two stages, once at `σ` and once at
-- `ρ₃`, the two pasts folded back together by `μ`. This is `η⊣-δ` packaged
-- with the grade relaxation.

box-split : ∀ {X σ ρ₁ ρ₃} → (a : σ ·ᵣ ρ₃ ≾ᵣ ρ₁)
          → δ ∘ᵐ []-≤ a ∘ᵐ η⊣ {X} {ρ₁}
          ≈ᵐ [ σ ]ᶠ ([ ρ₃ ]ᶠ (⟨⟩-≤ a ∘ᵐ μ) ∘ᵐ η⊣ {⟨ σ ⟩ᵒ X} {ρ₃}) ∘ᵐ η⊣ {X} {σ}
box-split a =
    ∘ᵐ-congʳ (η⊣-≤ a)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-δ-nat (⟨⟩-≤ a)))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ η⊣-δ
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
  ∙ ∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                        ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))

-- `box-split` with an environment postcomposed. The environment is pulled out
-- to the right, the split applied, and `η⊣`-naturality then carries it back
-- under the box, so the transposition ends up at the environment's source.
-- This is what lets `DELAY`'s strength components share one `η⊣`.

box-split-env : ∀ {X Y σ ρ₁ ρ₃} → (a : σ ·ᵣ ρ₃ ≾ᵣ ρ₁) → (env : Y →ᵐ X)
              → (δ ∘ᵐ []-≤ a) ∘ᵐ (η⊣ {X} {ρ₁} ∘ᵐ env)
              ≈ᵐ [ σ ]ᶠ (([ ρ₃ ]ᶠ (⟨⟩-≤ a ∘ᵐ μ) ∘ᵐ η⊣ {⟨ σ ⟩ᵒ X} {ρ₃}) ∘ᵐ ⟨ σ ⟩ᶠ env)
                  ∘ᵐ η⊣ {Y} {σ}
box-split-env {ρ₁ = ρ₁} a env =
    ≈ᵐ-sym (∘ᵐ-assoc (δ ∘ᵐ []-≤ a) (η⊣ {_} {ρ₁}) env)
  ∙ ∘ᵐ-congˡ (∘ᵐ-assoc δ ([]-≤ a) (η⊣ {_} {ρ₁}) ∙ box-split a)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat env))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))

-- Pushing an outer box-split through one that has already happened.
--
-- `DELAY` produces a double `δ` stack and a single split peels only one layer.
-- This pushes the outer layer through, exposing a bare `δ ∘ᵐ []-≤ ∘ᵐ η⊣` on
-- which `box-split` fires again, leaving the transposition at the tick's own
-- grade.

box-push : ∀ {Y Z ρ₁ ρ₂ ρ'} → (e : ρ₁ ·ᵣ ρ₂ ≾ᵣ ρ')
         → (h : ⟨ ρ' ⟩ᵒ Y →ᵐ Z)
         → (δ {Z} {ρ₁} {ρ₂} ∘ᵐ []-≤ e) ∘ᵐ ([ ρ' ]ᶠ h ∘ᵐ η⊣ {Y} {ρ'})
         ≈ᵐ [ ρ₁ ]ᶠ ([ ρ₂ ]ᶠ h
                      ∘ᵐ ([ ρ₂ ]ᶠ (⟨⟩-≤ e ∘ᵐ μ) ∘ᵐ η⊣ {⟨ ρ₁ ⟩ᵒ Y} {ρ₂}))
              ∘ᵐ η⊣ {Y} {ρ₁}
box-push {ρ' = ρ'} e h =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  -- commute the relaxation past the already-split box
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-≤-nat h e)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  -- and commute `δ` past it too
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-δ-nat h))
  ∙ ∘ᵐ-assoc _ _ _
  -- what is left is a bare split
  ∙ ∘ᵐ-congʳ (box-split e)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))

-- Discharging a unit-graded box: at grade `𝟏` the box counit turns a
-- transposition into the possibility unit. (The object-general form of
-- `ret-env`.)

εᵇ-η⊣ : ∀ {X ρ} → (e : ρ ≃ᵣ 𝟏ᵣ)
      → εᵇ ∘ᵐ []-≤ (≃ᵣ⇒≿ᵣ e) ∘ᵐ η⊣ {X} {ρ}
      ≈ᵐ ⟨⟩-≤ (≃ᵣ⇒≿ᵣ e) ∘ᵐ η
εᵇ-η⊣ e =
    ∘ᵐ-congʳ (η⊣-≤ (≃ᵣ⇒≿ᵣ e))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-ε-nat _))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ
      (  ∘ᵐ-congʳ η⊣-𝟏
       ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
       ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-ε-nat η))
       ∙ ∘ᵐ-assoc _ _ _
       ∙ ∘ᵐ-congʳ []-ε∘ηᵘ≡id
       ∙ ∘ᵐ-identityʳ _)

-- Opening a unit-graded box around an arbitrary map.
--
-- At a grade that is the unit (`e : ρ ≡ 𝟏ᵣ`), the box counit discharges the
-- transposition entirely, leaving the possibility unit relaxed to the grade.
-- `εᵇ-η⊣` with a map `H` carried through.

box-open : ∀ {X Z ρ} → (e : ρ ≃ᵣ 𝟏ᵣ) → (H : ⟨ ρ ⟩ᵒ X →ᵐ Z)
         → (εᵇ ∘ᵐ []-≤ (≃ᵣ⇒≿ᵣ e)) ∘ᵐ [ ρ ]ᶠ H ∘ᵐ η⊣ {X} {ρ}
         ≈ᵐ H ∘ᵐ (⟨⟩-≤ (≃ᵣ⇒≿ᵣ e) ∘ᵐ η)
box-open e H =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-≤-nat H (≃ᵣ⇒≿ᵣ e))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-ε-nat H))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (εᵇ-η⊣ e)

-- Pairing two transposes is transposing the pair (the derived form of
-- `η⊣-monoidal` that `delayᵀ`'s strength law needs).

η⊣-⟨⟩ : ∀ {X Y Z ρ} → (f : ⟨ ρ ⟩ᵒ X →ᵐ Y) → (g : ⟨ ρ ⟩ᵒ X →ᵐ Z)
      → []-monoidal ∘ᵐ ⟨ [ ρ ]ᶠ f ∘ᵐ η⊣ , [ ρ ]ᶠ g ∘ᵐ η⊣ ⟩ᵐ
      ≈ᵐ [ ρ ]ᶠ ⟨ f , g ⟩ᵐ ∘ᵐ η⊣ {X} {ρ}
η⊣-⟨⟩ f g =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-monoidal-nat f g))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ η⊣-monoidal
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
  ∙ ∘ᵐ-congˡ ([]-congᶠ (mapˣᵐ-∘⟨⟩ _ _ _ _
                        ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))

-- The rules that do not advance time transition by `ηᵀ`: the
-- environment box must survive unchanged, opened by `strᵀ-ηᵀ` at the unit
-- grade and given back boxed at the continuation's grade `ρ₃`, by
-- `box-split`.

box-η : ∀ {X ρ₁ ρ₃} → (a : ∣ 𝟏ₑ ∣ᵉ ·ᵣ ρ₃ ≾ᵣ ρ₁) → (w : ρ₃ ≾ᵣ ρ₁)
      → εᵇ ∘ᵐ []-≤ (≃ᵣ⇒≿ᵣ map-𝟏ᵉ) ∘ᵐ δ ∘ᵐ []-≤ a ∘ᵐ η⊣ {X} {ρ₁}
      ≈ᵐ [ ρ₃ ]ᶠ (⟨⟩-≤ w) ∘ᵐ η⊣ {X} {ρ₃}
box-η {X} {ρ₁} {ρ₃} a w =
    ∘ᵐ-congʳ (∘ᵐ-congʳ (box-split a))
  -- the outer box is at the unit grade, so the counit discharges it
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-≤-nat _ (≃ᵣ⇒≿ᵣ map-𝟏ᵉ))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-ε-nat _))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (εᵇ-η⊣ map-𝟏ᵉ)
  -- and the inner box reassembles, the grade relaxations collapsing
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
  ∙ ∘ᵐ-congˡ ([]-congᶠ collapse)
  where
    collapse : (⟨⟩-≤ a ∘ᵐ μ {X} {ρ₃} {∣ 𝟏ₑ ∣ᵉ})
                 ∘ᵐ ⟨ ρ₃ ⟩ᶠ (⟨⟩-≤ (≃ᵣ⇒≿ᵣ map-𝟏ᵉ) ∘ᵐ η)
             ≈ᵐ ⟨⟩-≤ w
    collapse =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μ-≤ˡ (≃ᵣ⇒≿ᵣ map-𝟏ᵉ))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ ⟨⟩-μ∘Tη≡id)
      ∙ ∘ᵐ-congʳ (⟨⟩-≤-trans _ _)
      ∙ ⟨⟩-≤-trans _ _
      ∙ ⟨⟩-≤-irr _ w

-- Interpreting an effect-grade coercion is the transport `ε-substᵀ`.

-- `SEQ-STEP` and `HANDLE-STEP` both have the shape
-- `alg ∘ Tᶠ⟦N⟧ ∘ strᵀ ∘ ⟨ η⊣ , ⟦M⟧ ⟩ᵐ`, differing only in the algebra (`μᵀ`
-- resp. the handler's), bottoming out in `step-box`: the environment carried
-- across the step is the new state's environment, renamed by `suc-comp-ren`.

-- Naturality of the strength in its monadic (tree) component alone, the
-- dual of `strᵀ-natˡ`. Derived from `strᵀ-nat` and `[]-idᵐ`.

strᵀ-natʳ : ∀ {A B B' ε} → (g : B →ᵐ B')
          → strᵀ {A} {B'} {ε} ∘ᵐ mapˣᵐ idᵐ (Tᶠ g)
          ≈ᵐ Tᶠ (mapˣᵐ idᵐ g) ∘ᵐ strᵀ {A} {B} {ε}
strᵀ-natʳ g =
    ∘ᵐ-congʳ (⟨ ∘ᵐ-congˡ (≈ᵐ-sym []-idᵐ) , ≈ᵐ-refl ⟩ᵐ-cong)
  ∙ strᵀ-nat idᵐ g

-- Subsuming the sequel's binder is the step's value refinement, moved from the
-- bound computation to the binder: the strength carries it across.

subCtx-str : ∀ {Γ A A₀ B ε₁ ε₂ X} {t : A₀ <:ᵛ A}
           → (N : Γ ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε₂) → (pN : Paramᶜ N)
           → (b : X →ᵐ [ ∣ ε₁ ∣ᵉ ]ᵒ (⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ))
           → (m : X →ᵐ Tᵒ ⟦ A₀ ⟧ᵛ ε₁)
           → Tᶠ (⟦ subCtx t N ⟧ᶜᵗ (subCtxᴾ t N pN))
               ∘ᵐ strᵀ {⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ} {⟦ A₀ ⟧ᵛ} {ε₁} ∘ᵐ ⟨ b , m ⟩ᵐ
           ≈ᵐ Tᶠ (⟦ N ⟧ᶜᵗ pN)
               ∘ᵐ strᵀ {⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {ε₁}
               ∘ᵐ ⟨ b , Tᶠ ⟦ t ⟧<:ᵛ ∘ᵐ m ⟩ᵐ
subCtx-str {t = t} N pN b m =
    ∘ᵐ-congˡ (T-congᶠ (subCtx-nat t N pN))
  ∙ ∘ᵐ-congˡ (T-∘ᵐ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (strᵀ-natʳ ⟦ t ⟧<:ᵛ)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))

-- Pushing an environment reindexing into a sequencing/handling composite.
-- Stated generically (over objects) so the associativity metas are pinned.

seq-push : ∀ {Γ Δ A B ε₁ ε₂}
         → (n : ⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ ×ᵐ A →ᵐ Tᵒ B ε₂) → (m : Γ →ᵐ Tᵒ A ε₁)
         → (env : Δ →ᵐ Γ)
         → (Tᶠ n ∘ᵐ strᵀ {⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ} {A} {ε₁} ∘ᵐ ⟨ η⊣ , m ⟩ᵐ) ∘ᵐ env
         ≈ᵐ Tᶠ n ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ ∘ᵐ env , m ∘ᵐ env ⟩ᵐ
seq-push n m env =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _))

-- The algebra the two step rules share: `⨟` folds with the monad
-- multiplication and `handle` with the handler's fold, so the algebra carries
-- an eternal parameter `P` supplied at the ambient context. For `⨟` the
-- parameter is trivial.

μalg : ∀ {A ε ε'} → 𝟙ᵐ ×ᵐ Tᵒ (Tᵒ A ε') ε →ᵐ Tᵒ A (ε ·ₑ ε')
μalg = μᵀ ∘ᵐ sndᵐ

μalg-drop : ∀ {X A ε ε'} → (t : X →ᵐ 𝟙ᵐ) → (g : X →ᵐ Tᵒ (Tᵒ A ε') ε)
          → μalg ∘ᵐ ⟨ t , g ⟩ᵐ ≈ᵐ μᵀ ∘ᵐ g
μalg-drop t g = ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)

μalg-≤ : ∀ {A ε₂ εa εb} → (q : εa ≾ₑ εb)
       → μalg {A} {εb} {ε₂} ∘ᵐ mapˣᵐ idᵐ (T-≤ q)
       ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ μalg {A} {εa} {ε₂}
μalg-≤ q =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-≤-μᵀ q)
  ∙ ∘ᵐ-assoc _ _ _

-- Pulling the IH coercion `T-≤ p` out to the front of a sequencing composite.
-- `strᵀ-≤` moves it past the strength (relaxing the box's grade), then
-- `T-≤-nat` and `T-≤-μᵀ` bubble it up past `Tᶠ n` and `μᵀ`.

coe-out : ∀ {Γ Δ A B P ε₀ ε₁ ε₂}
        → (alg : ∀ {ε} → P ×ᵐ Tᵒ (Tᵒ B ε₂) ε →ᵐ Tᵒ B (ε ·ₑ ε₂))
        → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
                 → alg {εb} ∘ᵐ mapˣᵐ idᵐ (T-≤ q)
                 ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
        → (pv : Δ →ᵐ P)
        → (bx : Δ →ᵐ [ ∣ ε₁ ∣ᵉ ]ᵒ (⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ))
        → (n : ⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ ×ᵐ A →ᵐ Tᵒ B ε₂)
        → (W : Δ →ᵐ Tᵒ A ε₀) → (p : ε₀ ≾ₑ ε₁)
        → alg {ε₁} ∘ᵐ ⟨ pv
                      , Tᶠ n ∘ᵐ strᵀ {⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ} {A} {ε₁}
                          ∘ᵐ ⟨ bx , T-≤ p ∘ᵐ W ⟩ᵐ ⟩ᵐ
        ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ p)
            ∘ᵐ alg {ε₀} ∘ᵐ ⟨ pv
                          , Tᶠ n ∘ᵐ strᵀ {⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ} {A} {ε₀}
                              ∘ᵐ ⟨ []-≤ (map-monotoneᵉ p) ∘ᵐ bx , W ⟩ᵐ ⟩ᵐ
coe-out alg alg-≤ pv bx n W p =
    ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , inner ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (alg-≤ p)
  ∙ ∘ᵐ-assoc _ _ _
  where
    inner : Tᶠ n ∘ᵐ strᵀ ∘ᵐ ⟨ bx , T-≤ p ∘ᵐ W ⟩ᵐ
          ≈ᵐ T-≤ p ∘ᵐ Tᶠ n ∘ᵐ strᵀ ∘ᵐ ⟨ []-≤ (map-monotoneᵉ p) ∘ᵐ bx , W ⟩ᵐ
    inner =
        ∘ᵐ-congʳ (∘ᵐ-congʳ
            (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ (T-≤ p) bx W
                     ∙ ⟨ ∘ᵐ-identityˡ bx , ≈ᵐ-refl ⟩ᵐ-cong)))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-≤ p))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
                                      ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (T-≤-nat _ p)
      ∙ ∘ᵐ-assoc _ _ _

-- Splitting the strength across a bind, via `strᵀ-μᵀ` and `strᵀ-nat`.

str-split : ∀ {Γ Δ Δ' A d ε₁ ε₃}
          → (box₂ : Δ →ᵐ [ ∣ d ·ₑ ε₃ ∣ᵉ ]ᵒ (⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ))
          → (g' : Δ' →ᵐ Tᵒ A ε₃) → (t : Δ →ᵐ Tᵒ Δ' d)
          → strᵀ {⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ} {A} {d ·ₑ ε₃} ∘ᵐ ⟨ box₂ , μᵀ ∘ᵐ Tᶠ g' ∘ᵐ t ⟩ᵐ
          ≈ᵐ μᵀ ∘ᵐ Tᶠ (strᵀ {⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ} {A} {ε₃}) ∘ᵐ Tᶠ (mapˣᵐ idᵐ g')
              ∘ᵐ strᵀ {[ ∣ ε₃ ∣ᵉ ]ᵒ (⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ)} {Δ'} {d}
              ∘ᵐ ⟨ (δ {⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ} {∣ d ∣ᵉ} {∣ ε₃ ∣ᵉ}
                      ∘ᵐ []-≤ (≃ᵣ⇒≿ᵣ (map-·ᵉ {d} {ε₃}))) ∘ᵐ box₂ , t ⟩ᵐ
str-split {Γ = Γ} {d = d} {ε₁ = ε₁} {ε₃ = ε₃} box₂ g' t =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ μᵀ box₂ (Tᶠ g' ∘ᵐ t)
                      ∙ ⟨ ∘ᵐ-identityˡ box₂ , ≈ᵐ-refl ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-μᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
                                  ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ (Tᶠ g') _ t
               ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natʳ g')))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ≈ᵐ-refl


-- Pushing the inductive hypothesis' coercion out through the sequencing
-- composite, down to the `strᵀ ∘ ⟨ box , stepᵀ ⟩` core. Generic over objects
-- (so the metas are pinned by the explicit arguments); each step is one of
-- the strength/sub-effecting laws.

push-str : ∀ {Γ Δ Δ' A B P d ε₁ ε₂ ε₃}
         → (alg : ∀ {ε} → P ×ᵐ Tᵒ (Tᵒ B ε₂) ε →ᵐ Tᵒ B (ε ·ₑ ε₂))
         → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
                  → alg {εb} ∘ᵐ mapˣᵐ idᵐ (T-≤ q)
                  ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
         → (pv : Δ →ᵐ P)
         → (bx : Δ →ᵐ [ ∣ ε₁ ∣ᵉ ]ᵒ (⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ))
         → (n : ⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ ×ᵐ A →ᵐ Tᵒ B ε₂)
         → (g' : Δ' →ᵐ Tᵒ A ε₃) → (t : Δ →ᵐ Tᵒ Δ' d)
         → (p : d ·ₑ ε₃ ≾ₑ ε₁)
         → alg {ε₁} ∘ᵐ ⟨ pv
                       , Tᶠ n ∘ᵐ strᵀ {⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ} {A} {ε₁}
                           ∘ᵐ ⟨ bx , T-≤ p ∘ᵐ μᵀ ∘ᵐ Tᶠ g' ∘ᵐ t ⟩ᵐ ⟩ᵐ
         ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ p)
             ∘ᵐ alg {d ·ₑ ε₃}
             ∘ᵐ ⟨ pv
                ,   Tᶠ n ∘ᵐ μᵀ
                  ∘ᵐ Tᶠ (strᵀ {⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ} {A} {ε₃})
                  ∘ᵐ Tᶠ (mapˣᵐ idᵐ g')
                  ∘ᵐ strᵀ {[ ∣ ε₃ ∣ᵉ ]ᵒ (⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ)} {Δ'} {d}
                  ∘ᵐ ⟨ (δ {⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ Γ} {∣ d ∣ᵉ} {∣ ε₃ ∣ᵉ}
                          ∘ᵐ []-≤ (≃ᵣ⇒≿ᵣ (map-·ᵉ {d} {ε₃})))
                         ∘ᵐ ([]-≤ (map-monotoneᵉ p) ∘ᵐ bx)
                     , t ⟩ᵐ ⟩ᵐ
push-str alg alg-≤ pv bx n g' t p =
    coe-out alg alg-≤ pv bx n (μᵀ ∘ᵐ Tᶠ g' ∘ᵐ t) p
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
      , ∘ᵐ-congʳ (str-split ([]-≤ (map-monotoneᵉ p) ∘ᵐ bx) g' t) ⟩ᵐ-cong))

-- The two coercions a sequencing step produces (the re-association of the
-- effect grades, and the step's own refinement) merge into `step-≾`'s.

seq-coe : ∀ {X A d ε₁ ε₂ ε₃}
        → (p : d ·ₑ ε₃ ≾ₑ ε₁)
        → (q : d ·ₑ (ε₃ ·ₑ ε₂) ≾ₑ ε₁ ·ₑ ε₂)
        → (f : X →ᵐ Tᵒ A (d ·ₑ (ε₃ ·ₑ ε₂)))
        → T-≤ (·ₑ-monoˡ-≾ₑ p) ∘ᵐ T-≤ (≃ₑ⇒≿ₑ (·ₑ-assoc d ε₃ ε₂)) ∘ᵐ f
        ≈ᵐ T-≤ q ∘ᵐ f
seq-coe {d = d} {ε₂ = ε₂} {ε₃ = ε₃} p q f =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-≤-trans (≃ₑ⇒≿ₑ (·ₑ-assoc d ε₃ ε₂))
                        (·ₑ-monoˡ-≾ₑ p) q)

-- SEQ-STEP (scaffold: isolating the `step-box` residual).
--
-- Stated in `push-str`'s natural grade `(d ·ₑ ε₃) ·ₑ ε₂`; `seq-coe` re-associates
-- to the goal's `d ·ₑ (ε₃ ·ₑ ε₂)` afterwards.

seq-step-core : ∀ {ε₁ ε₂ ε₃ A A₀ B P} {𝕊 𝕊' : State []}
  → (alg : ∀ {ε} → P ×ᵐ Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε ·ₑ ε₂))
  → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
           → alg {εb} ∘ᵐ mapˣᵐ idᵐ (T-≤ q) ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
  → (pv : ⟦ toCtx 𝕊 ⟧ᶜᵗˣ →ᵐ P)
  → {M : toCtx 𝕊 ⊢C⦂ A ! ε₁} → (N : toCtx 𝕊 ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε₂)
  → {M' : toCtx 𝕊' ⊢C⦂ A₀ ! ε₃}
  → (r : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩)
  → (c : κₛ (step-extends-state r) ·ᵣ ∣ ε₃ ∣ᵉ ≾ᵣ ∣ ε₁ ∣ᵉ)
  → (pS : Paramˢ 𝕊)
  → (pM : Paramᶜ M) → (pN : Paramᶜ N)
  → (m' : ⟦ hist 𝕊' ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ A ⟧ᵛ ε₃)
  → ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ 𝕊 ⟧ˢ pS
    ≈ᵐ T-≤ (step-≾ r)
       ∘ᵐ _⋄_ {⟦ hist 𝕊 ⟧ᶜᵗˣ} {⟦ hist 𝕊' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {step-grade r} {ε₃}
              m' (stepᵀ r)
  → (alg {ε₁} ∘ᵐ ⟨ pv , Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ ⟩ᵐ)
       ∘ᵐ ⟦ 𝕊 ⟧ˢ pS
    ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ (step-≾ r))
       ∘ᵐ alg {step-grade r ·ₑ ε₃}
       ∘ᵐ ⟨ pv ∘ᵐ ⟦ 𝕊 ⟧ˢ pS
          ,   Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ μᵀ
            ∘ᵐ Tᶠ (strᵀ {⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ ⟦ toCtx 𝕊 ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {ε₃})
            ∘ᵐ Tᶠ (mapˣᵐ idᵐ m')
            ∘ᵐ strᵀ {[ ∣ ε₃ ∣ᵉ ]ᵒ (⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ ⟦ toCtx 𝕊 ⟧ᶜᵗˣ)} {⟦ hist 𝕊' ⟧ᶜᵗˣ}
                    {step-grade r}
            ∘ᵐ ⟨ (δ {⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ ⟦ toCtx 𝕊 ⟧ᶜᵗˣ} {∣ step-grade r ∣ᵉ} {∣ ε₃ ∣ᵉ}
                    ∘ᵐ []-≤ (≃ᵣ⇒≿ᵣ (map-·ᵉ {step-grade r} {ε₃})))
                   ∘ᵐ ([]-≤ (map-monotoneᵉ (step-≾ r)) ∘ᵐ (η⊣ ∘ᵐ ⟦ 𝕊 ⟧ˢ pS))
               , stepᵀ r ⟩ᵐ ⟩ᵐ
seq-step-core {ε₁} {ε₂} {ε₃} {A} {A₀} {B} {P} {𝕊} {𝕊'} alg alg-≤ pv {M} N {M'} r c pS pM pN m' ih =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
              , seq-push {⟦ toCtx 𝕊 ⟧ᶜᵗˣ} {⟦ hist 𝕊 ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {⟦ B ⟧ᵛ} {ε₁} {ε₂}
                         (⟦ N ⟧ᶜᵗ pN) (⟦ M ⟧ᶜᵗ pM) (⟦ 𝕊 ⟧ˢ pS) ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ∘ᵐ-congʳ (∘ᵐ-congʳ
      (⟨_,_⟩ᵐ-cong {f = η⊣ ∘ᵐ ⟦ 𝕊 ⟧ˢ pS} {f' = η⊣ ∘ᵐ ⟦ 𝕊 ⟧ˢ pS}
                   {g = ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ 𝕊 ⟧ˢ pS}
                   {g' = T-≤ (step-≾ r) ∘ᵐ (μᵀ ∘ᵐ Tᶠ m' ∘ᵐ stepᵀ r)}
                   ≈ᵐ-refl ih)) ⟩ᵐ-cong)
  ∙ push-str {⟦ toCtx 𝕊 ⟧ᶜᵗˣ} {⟦ hist 𝕊 ⟧ᶜᵗˣ} {⟦ hist 𝕊' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {⟦ B ⟧ᵛ} {P}
             {step-grade r} {ε₁} {ε₂} {ε₃}
             alg alg-≤ (pv ∘ᵐ ⟦ 𝕊 ⟧ˢ pS)
             (η⊣ ∘ᵐ ⟦ 𝕊 ⟧ˢ pS) (⟦ N ⟧ᶜᵗ pN) m'
             (stepᵀ r) (step-≾ r)

-- The `≤ₛ-refl` box identity: the residual left by `strᵀ-ηᵀ` in the
-- rules that neither advance time nor allocate. The box's two grade
-- relaxations merge by `[]-≤-trans` into exactly `box-η`'s hypothesis.

box-core : ∀ {X ρ₂ ρ₄}
         → (a : ∣ 𝟏ₑ ∣ᵉ ·ᵣ ρ₄ ≾ᵣ ρ₂) → (w : ρ₄ ≾ᵣ ρ₂)
         → (εᵇ ∘ᵐ []-≤ (≃ᵣ⇒≿ᵣ map-𝟏ᵉ))
             ∘ᵐ ((δ ∘ᵐ []-≤ a) ∘ᵐ η⊣ {X} {ρ₂})
         ≈ᵐ [ ρ₄ ]ᶠ (⟨⟩-≤ w) ∘ᵐ η⊣ {X} {ρ₄}
box-core a w =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc δ ([]-≤ a) η⊣))
  ∙ box-η a w

box-≤ₛ-refl : ∀ {X Y ρ₂ ρ₄}
            → (a : ∣ 𝟏ₑ ∣ᵉ ·ᵣ ρ₄ ≾ᵣ ρ₂) → (w : ρ₄ ≾ᵣ ρ₂)
            → (env : Y →ᵐ X)
            → (εᵇ ∘ᵐ []-≤ (≃ᵣ⇒≿ᵣ map-𝟏ᵉ))
               ∘ᵐ (δ ∘ᵐ []-≤ a) ∘ᵐ (η⊣ {X} {ρ₂} ∘ᵐ env)
            ≈ᵐ [ ρ₄ ]ᶠ (⟨⟩-≤ w ∘ᵐ ⟨ ρ₄ ⟩ᶠ env) ∘ᵐ η⊣ {Y} {ρ₄}
box-≤ₛ-refl {ρ₂ = ρ₂} a w env =
    ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc (δ ∘ᵐ []-≤ a) (η⊣ {_} {ρ₂}) env))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc (εᵇ ∘ᵐ []-≤ (≃ᵣ⇒≿ᵣ map-𝟏ᵉ))
                     ((δ ∘ᵐ []-≤ a) ∘ᵐ η⊣ {_} {ρ₂}) env)
  ∙ ∘ᵐ-congˡ (box-core a w)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat env))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))

-- What `DELAY` finally reduces to, once every box has been discharged: a pure
-- statement about the context modality.

-- Folding the unit that the tick's transposition introduced. `μ` against `η`
-- is the graded monad's unit law, so the whole `⟨⟩-≤ ∘ μ ∘ ⟨⟩-≤ ∘ η` collapses
-- to a single grade relaxation (the order being proof-irrelevant).

past-η : ∀ {A ρ σ u'} → (pu : 𝟏ᵣ ≾ᵣ u') → (e : ρ ·ᵣ u' ≾ᵣ σ) → (k : ρ ≾ᵣ σ)
       → (⟨⟩-≤ e ∘ᵐ μ {A} {u'} {ρ}) ∘ᵐ (⟨⟩-≤ pu ∘ᵐ η)
       ≈ᵐ ⟨⟩-≤ k
past-η pu e k =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μ-≤ʳ pu)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ ⟨⟩-μ∘η≡id)
  ∙ ∘ᵐ-congʳ (⟨⟩-≤-trans _ _)
  ∙ ⟨⟩-≤-trans _ _
  ∙ ⟨⟩-≤-irr _ k

-- The environment commutes past that relaxation (`⟨⟩-≤-nat`) and `μ` absorbs it
-- (`μ-≤ˡ`), leaving the renaming `suc-comp-ren` builds for a `≤ₛ-lock`: the `μ`
-- folding the state's lock with the new tick.

past-tick : ∀ {A B ρ ρ₂ ρ₄ σ u'}
          → (pu : 𝟏ᵣ ≾ᵣ u') → (e : ρ ·ᵣ u' ≾ᵣ σ) → (k : ρ ≾ᵣ σ)
          → (g : σ ·ᵣ ρ₄ ≾ᵣ ρ₂) → (w : ρ ·ᵣ ρ₄ ≾ᵣ ρ₂)
          → (E : A →ᵐ B)
          → (⟨⟩-≤ g ∘ᵐ μ {B} {ρ₄} {σ})
              ∘ᵐ ⟨ ρ₄ ⟩ᶠ (⟨ σ ⟩ᶠ E ∘ᵐ (⟨⟩-≤ e ∘ᵐ μ {A} {u'} {ρ}) ∘ᵐ (⟨⟩-≤ pu ∘ᵐ η))
          ≈ᵐ (⟨⟩-≤ w ∘ᵐ μ {B} {ρ₄} {ρ}) ∘ᵐ ⟨ ρ₄ ⟩ᶠ (⟨ ρ ⟩ᶠ E)
past-tick pu e k g w E =
    ∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-congʳ (past-η pu e k)))
  ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩-≤-nat E k))
  ∙ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μ-≤ˡ k)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (⟨⟩-≤-trans _ _ ∙ ⟨⟩-≤-irr _ w)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- The grade witness that `suc-comp-ren ≤ₛ-refl` carries.

wk-w : ∀ {ρ₂ ρ₄} → (c : 𝟏ᵣ ·ᵣ ρ₄ ≾ᵣ ρ₂) → ρ₄ ≾ᵣ ρ₂
wk-w {ρ₄ = ρ₄} c = ≾ᵣ-trans (≃ᵣ⇒≿ᵣ (·ᵣ-identityˡ ρ₄)) c

-- The `≤ₛ-res` cancellation: `suc-comp-ren` prefixes a `cong-⟨⟩-ren wk-ren`,
-- whose `fstᵐ` projects away exactly the cell that `⟦_⟧ˢ` just allocated, so
-- allocation leaves the environment untouched.

box-≤ₛ-res : ∀ {X Y Z ρ₂ ρ₄} → (w w' : ρ₄ ≾ᵣ ρ₂)
           → (env : Y →ᵐ X) → (cell : X →ᵐ Z)
           → ⟨⟩-≤ w ∘ᵐ ⟨ ρ₄ ⟩ᶠ env
           ≈ᵐ (⟨⟩-≤ w' ∘ᵐ ⟨ ρ₄ ⟩ᶠ fstᵐ) ∘ᵐ ⟨ ρ₄ ⟩ᶠ (⟨ idᵐ , cell ⟩ᵐ ∘ᵐ env)
box-≤ₛ-res w w' env cell =
    ∘ᵐ-congˡ (⟨⟩-≤-irr w w')
  ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym (≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                                ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
                                ∙ ∘ᵐ-identityˡ _)))
  ∙ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- The semantic content of "reduction only extends the state": the boxed
-- environment of the source state, carried along the step's time transition,
-- is the target state's boxed environment reindexed by the renaming
-- `suc-comp-ren` builds. Generic in the two resource grades: a reduction's
-- own effect grades only instantiate them.

step-box : ∀ {ε₁ ε₃ A A₀} {𝕊 𝕊' : State []} {ρ₂ ρ₄ : R}
         → {M : toCtx 𝕊 ⊢C⦂ A ! ε₁} → {M' : toCtx 𝕊' ⊢C⦂ A₀ ! ε₃}
         → (r : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩)
         → (c : κₛ (step-extends-state r) ·ᵣ ρ₄ ≾ᵣ ρ₂)
         → (g : ∣ step-grade r ∣ᵉ ·ᵣ ρ₄ ≾ᵣ ρ₂)
         → (pS : Paramˢ 𝕊) → (pM : Paramᶜ M)
         → strᵀ {[ ρ₄ ]ᵒ (⟨ ρ₂ ⟩ᵒ ⟦ toCtx 𝕊 ⟧ᶜᵗˣ)} {⟦ hist 𝕊' ⟧ᶜᵗˣ} {step-grade r}
             ∘ᵐ ⟨ (δ {⟨ ρ₂ ⟩ᵒ ⟦ toCtx 𝕊 ⟧ᶜᵗˣ} {∣ step-grade r ∣ᵉ} {ρ₄} ∘ᵐ []-≤ g)
                    ∘ᵐ (η⊣ ∘ᵐ ⟦ 𝕊 ⟧ˢ pS)
                , stepᵀ r ⟩ᵐ
           ≈ᵐ Tᶠ ⟨ [ ρ₄ ]ᶠ (⟦ suc-comp-ren (step-extends-state r) c ⟧ʳ
                             ∘ᵐ ⟨ ρ₄ ⟩ᶠ (⟦ 𝕊' ⟧ˢ (stepᴾˢ r pS pM)))
                    ∘ᵐ η⊣
                 , idᵐ ⟩ᵐ
              ∘ᵐ stepᵀ r

-- The time-preserving rules: `strᵀ-ηᵀ` opens the box, and `box-≤ₛ-refl`
-- is what is left: the environment survives unchanged.

step-box APP c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box MATCH c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box MATCHL c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box RECL c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box CMP c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box IF-TRUE c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box IF-FALSE c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box MATCHℕ-ZERO c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box RECℕ-ZERO c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box RECℕ-SUCC c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box MATCHℕ-SUCC c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box MATCH+ c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box SEQ-RET c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box SEQ-OP c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box HANDLE-RET c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box HANDLE-OP c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box UNBOX c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box SUB-APP c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box SUB-HANDLE c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box SUB-HANDLE-TRANS c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box SUB-IF c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box SUB-MATCHℕ c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box SUB-RECℕ c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box SUB c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

-- The recursive rules: `stepᵀ`, `step-extends-state`, and both states are all
-- inherited from the sub-step, so the statement is the sub-step's.

step-box (SEQ-STEP r c') c g pS (pM , pN) = step-box r c g pS pM
step-box (HANDLE-STEP r c') c g pS (pM , pN , pH , uH) = step-box r c g pS pM

-- BOX: allocation. `stepᵀ` is still `ηᵀ`; the `fstᵐ` that `suc-comp-ren`
-- contributes cancels exactly the cell just written.

step-box (BOX {ρ' = ρ'} {𝕊 = 𝕊} {V = V}) c g pS (pV , pM) =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-≤ₛ-refl _ (wk-w c) (⟦ 𝕊 ⟧ˢ pS)
                  ∙ ∘ᵐ-congˡ ([]-congᶠ (box-≤ₛ-res (wk-w c) (wk-w c) (⟦ 𝕊 ⟧ˢ pS)
                                (  [ ρ' ]ᶠ (⟦ V-rename (eq-ren (sym ++ᶜ-identityˡ)) V ⟧ᵛᵗ
                                              (renᵛ (eq-ren (sym ++ᶜ-identityˡ)) V pV)
                                            ∘ᵐ ⟦ eq-ren (++ᶜ-identityˡ
                                                  {toCtx 𝕊 ⟨ ρ' ⟩}) ⟧ʳ)
                                 ∘ᵐ η⊣)))
                , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

-- DELAY: the tick, the one rule that advances time.
--
-- `strᵀ-delayᵀ-algebraicity` leaves a double `δ` stack on the first component,
-- which `box-split-env` and `box-push` peel down to a transposition at the
-- tick's own grade. Inside the resulting box the shape is the time-preserving
-- one again.

step-box (DELAY {τ = τ} {𝕊 = 𝕊}) c g pS pM =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ (delayᵀ τ) _ ([ ιᵣ τ ]ᶠ ηᵀ ∘ᵐ η⊣)
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (strᵀ-delayᵀ-algebraicity τ)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
                                  ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (⟨ ∘ᵐ-congʳ (box-split-env _ _) ∙ box-push _ _ , ≈ᵐ-refl ⟩ᵐ-cong)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (η⊣-⟨⟩ _ _))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (
        ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                          ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
                  ∙ ⟨   -- merge the two unit-graded boxes, then open them
                        ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
                      ∙ box-open map-𝟏ᵉ _
                      -- regroup so the `η⊣` inside can be pulled to the front
                      -- reassociate so the `η⊣` sits second from the left
                      ∙ ∘ᵐ-assoc _ _ _
                      ∙ ∘ᵐ-assoc _ _ _
                      ∙ ∘ᵐ-assoc _ _ _
                      -- pull `η⊣` to the front (its naturality), so both sides
                      -- are `[ ρ₄ ]ᶠ (…) ∘ᵐ η⊣`
                      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat _))
                      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
                      -- and what is left is the pure possibility identity
                      ∙ ∘ᵐ-congˡ ([]-congᶠ
                          (past-tick _ _
                            (≾ᵣ-trans (≃ᵣ⇒≿ᵣ (·ᵣ-identityʳ (ιᵣ τ)))
                              (≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ (≃ᵣ⇒≿ᵣ map-𝟏ᵉ))
                                        (≃ᵣ⇒≿ᵣ (≃ᵣ-trans map-·ᵉ (·ᵣ-cong map-ιᵉ ≃ᵣ-refl)))))
                            g _ (⟦ 𝕊 ⟧ˢ pS)))
                    , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
      ∙ ηᵀ-nat _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-∘ᵐ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (delayᵀ-nat τ _)
  ∙ ∘ᵐ-assoc _ _ _

-- Re-associating two multiplications. `T-μ∘μ≡μ∘Tμ` runs the other way (it
-- produces the transport), so the inverse direction cancels a transport
-- against its own inverse, which is `refl` by uniqueness of identity proofs.

μμ : ∀ {A ε ε' ε''}
   → μᵀ {A} {ε ·ₑ ε'} {ε''} ∘ᵐ μᵀ {Tᵒ A ε''} {ε} {ε'}
   ≈ᵐ T-≤ (≃ₑ⇒≿ₑ (·ₑ-assoc ε ε' ε''))
       ∘ᵐ μᵀ {A} {ε} {ε' ·ₑ ε''} ∘ᵐ Tᶠ (μᵀ {A} {ε'} {ε''})
μμ {ε = ε} {ε' = ε'} {ε'' = ε''} =
  ≈ᵐ-sym
      (∘ᵐ-congʳ T-μ∘μ≡μ∘Tμ
    ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙ ∘ᵐ-congˡ (T-≤-trans _ _ ≾ₑ-refl ∙ T-≤-refl _)
    ∙ ∘ᵐ-identityˡ _)

-- `SEQ-STEP`: `seq-step-core` reduces the source to the
-- `strᵀ ∘ ⟨ box , stepᵀ r ⟩` core; `step-box` replaces that core by the
-- new state's box, renamed by `suc-comp-ren`; and `seq-coe` reconciles the
-- effect grades (which differ by an associativity).

-- The box `seq-step-core` produces carries two grade relaxations, which merge
-- into the single one `step-box` expects.

seq-g : ∀ {ε₁ ε₃ A A₀} {𝕊 𝕊' : State []}
      → {M : toCtx 𝕊 ⊢C⦂ A ! ε₁} → {M' : toCtx 𝕊' ⊢C⦂ A₀ ! ε₃}
      → (r : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩)
      → ∣ step-grade r ∣ᵉ ·ᵣ ∣ ε₃ ∣ᵉ ≾ᵣ ∣ ε₁ ∣ᵉ
seq-g {ε₃ = ε₃} r =
  ≾ᵣ-trans (≃ᵣ⇒≿ᵣ (map-·ᵉ {step-grade r} {ε₃}))
           (map-monotoneᵉ (step-≾ r))

box-merge : ∀ {X Y Z ρ₁ ρ₂ ρ₃} → (p : ρ₁ ≾ᵣ ρ₂) → (q : ρ₂ ≾ᵣ ρ₃) → (m : ρ₁ ≾ᵣ ρ₃)
          → (d : [ ρ₁ ]ᵒ X →ᵐ Y) → (h : Z →ᵐ [ ρ₃ ]ᵒ X)
          → (d ∘ᵐ []-≤ p) ∘ᵐ ([]-≤ q ∘ᵐ h) ≈ᵐ (d ∘ᵐ []-≤ m) ∘ᵐ h
box-merge p q m d h =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-≤-trans p q ∙ []-≤-irr _ m))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- The target's denotation, unfolded to the same normal form. Generic in the
-- algebra: `⨟` uses `μᵀ`, `handle` uses the handler's fold, and they thread the
-- environment through the strength in the same way. The renaming
-- `suc-comp-ren` sits in the continuation, and `strᵀ-natˡ` moves it into the
-- environment box, which is the box `step-box` delivers.

seq-target : ∀ {ε₁ ε₂ ε₃ A B P} {Γ Γ' : Ctx} {H : Obj}
           → (alg : P ×ᵐ Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε₃ →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε₃ ·ₑ ε₂))
           → (pv : ⟦ Γ' ⟧ᶜᵗˣ →ᵐ P)
           → (N : Γ ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε₂)
           → (ρ : Ren [] (Γ' ⟨ ∣ ε₃ ∣ᵉ ⟩) (Γ ⟨ ∣ ε₁ ∣ᵉ ⟩))
           → (m' : ⟦ Γ' ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ A ⟧ᵛ ε₃)
           → (env : H →ᵐ ⟦ Γ' ⟧ᶜᵗˣ)
           → (pN : Paramᶜ N)
           → (alg ∘ᵐ ⟨ pv
                     ,   Tᶠ (⟦ C-rename (cong-∷-ren ρ) N ⟧ᶜᵗ
                               (renᶜ (cong-∷-ren ρ) N pN))
                       ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m' ⟩ᵐ ⟩ᵐ)
               ∘ᵐ env
           ≈ᵐ alg ∘ᵐ ⟨ pv ∘ᵐ env
                     ,   Tᶠ (⟦ N ⟧ᶜᵗ pN)
                       ∘ᵐ strᵀ {⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {ε₃}
                       ∘ᵐ ⟨ [ ∣ ε₃ ∣ᵉ ]ᶠ (⟦ ρ ⟧ʳ ∘ᵐ ⟨ ∣ ε₃ ∣ᵉ ⟩ᶠ env) ∘ᵐ η⊣
                          , m' ∘ᵐ env ⟩ᵐ ⟩ᵐ
seq-target {ε₃ = ε₃} {A = A} {B = B} {Γ' = Γ'} alg pv N ρ m' env pN =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , body ⟩ᵐ-cong)
  where
    body =
        seq-push {⟦ Γ' ⟧ᶜᵗˣ} {_} {⟦ A ⟧ᵛ} {⟦ B ⟧ᵛ} {ε₃} {_}
                 (⟦ C-rename (cong-∷-ren ρ) N ⟧ᶜᵗ (renᶜ (cong-∷-ren ρ) N pN))
                 m' env
      -- the renaming in the continuation …
      ∙ ∘ᵐ-congˡ (T-congᶠ (C-rename-nat (cong-∷-ren ρ) N pN))
      ∙ ∘ᵐ-congˡ (T-∘ᵐ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      -- … moves into the environment box (`strᵀ-natˡ`)
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
                            ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      -- the environment moves under the box (`η⊣`-naturality), giving exactly
      -- the box that `step-box` delivers
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
          (⟨ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat env))
             ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
             ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
           , ≈ᵐ-refl ⟩ᵐ-cong))

sound-SEQ-STEP : ∀ {ε₁ ε₂ ε₃ A A₀ B} {𝕊 𝕊' : State []}
  → {M : toCtx 𝕊 ⊢C⦂ A ! ε₁} → (N : toCtx 𝕊 ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε₂)
  → {M' : toCtx 𝕊' ⊢C⦂ A₀ ! ε₃}
  → (r : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩)
  → (c : κₛ (step-extends-state r) ·ᵣ ∣ ε₃ ∣ᵉ ≾ᵣ ∣ ε₁ ∣ᵉ)
  → (pS : Paramˢ 𝕊) → (pM : Paramᶜ M) → (pN : Paramᶜ N) → (pM' : Paramᶜ M')
  → ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ 𝕊 ⟧ˢ pS
    ≈ᵐ T-≤ (step-≾ r)
       ∘ᵐ Tᶠ ⟦ step-refines-type r ⟧<:ᵛ
       ∘ᵐ _⋄_ {⟦ hist 𝕊 ⟧ᶜᵗˣ} {⟦ hist 𝕊' ⟧ᶜᵗˣ} {⟦ A₀ ⟧ᵛ} {step-grade r} {ε₃}
              (⟦ M' ⟧ᶜᵗ pM' ∘ᵐ ⟦ 𝕊' ⟧ˢ (stepᴾˢ r pS pM)) (stepᵀ r)
  → ⟦ M ⨟ N ⟧ᶜᵗ (pM , pN) ∘ᵐ ⟦ 𝕊 ⟧ˢ pS
    ≈ᵐ T-≤ (step-≾ (SEQ-STEP {N = N} r c))
       ∘ᵐ _⋄_ {⟦ hist 𝕊 ⟧ᶜᵗˣ} {⟦ hist 𝕊' ⟧ᶜᵗˣ} {⟦ B ⟧ᵛ} {step-grade r} {ε₃ ·ₑ ε₂}
              (⟦ M' ⨟ subCtx (step-refines-type r)
                        (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N) ⟧ᶜᵗ
                 (pM' , subCtxᴾ (step-refines-type r)
                          (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N)
                          (renᶜ (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N pN))
                 ∘ᵐ ⟦ 𝕊' ⟧ˢ (stepᴾˢ r pS pM))
              (stepᵀ r)
sound-SEQ-STEP {ε₁} {ε₂} {ε₃} {A} {A₀} {B} {𝕊} {𝕊'} {M} N {M'} r c pS pM pN pM' ih =
    ∘ᵐ-congˡ (≈ᵐ-sym (μalg-drop _ _))
  ∙ seq-step-core μalg μalg-≤ terminalᵐ N r c pS pM pN mt ih'
  ∙ ∘ᵐ-congʳ (μalg-drop _ _)
  -- merge the box's two relaxations into the one `step-box` expects
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (⟨ box-merge _ _ (seq-g r) _ _ , ≈ᵐ-refl ⟩ᵐ-cong)))))))
  -- and replace the core by the new state's box
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (step-box r c (seq-g r) pS pM))))))
  -- collect the functorial actions under one `Tᶠ`
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _))))))
  -- the inner term is the target's normal form (`seq-target`)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
      (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))))))
  -- push `Tᶠ ⟦N⟧` past the inner `μᵀ` …
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μᵀ-nat _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  -- … and re-associate the two `μᵀ`s, which is where the `ε-substᵀ` appears
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ μμ)
  -- regroup: the transport floats to the front, and the rest collects under
  -- one `Tᶠ`, which is `seq-target`'s normal form
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)))))
  -- drop the identity the strength's pairing picked up
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
      (∘ᵐ-congʳ ⟨ ≈ᵐ-refl , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))))))
  -- collect the last two functorial actions under one `Tᶠ`
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)))))
  -- … and what is under it is the target's denotation, the step's value
  -- refinement moving from the bound computation onto the sequel's binder
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
      (∘ᵐ-assoc _ _ _
       ∙ ≈ᵐ-sym (  ∘ᵐ-congˡ (∘ᵐ-congʳ
                     (subCtx-str {t = step-refines-type r}
                        (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N)
                        (renᶜ (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N pN)
                        η⊣ (⟦ M' ⟧ᶜᵗ pM')))
                 ∙ ∘ᵐ-congˡ (≈ᵐ-sym (μalg-drop _ _))
                 ∙ seq-target {ε₁} {ε₂} {ε₃} {A} {B} {𝟙ᵐ}
                              {toCtx 𝕊} {toCtx 𝕊'} {⟦ hist 𝕊' ⟧ᶜᵗˣ}
                              μalg terminalᵐ N (suc-comp-ren (step-extends-state r) c)
                              (Tᶠ ⟦ step-refines-type r ⟧<:ᵛ ∘ᵐ ⟦ M' ⟧ᶜᵗ pM')
                              (⟦ 𝕊' ⟧ˢ (stepᴾˢ r pS pM)) pN
                 ∙ μalg-drop _ _))))))
  -- … and the `ε-substᵀ` that `μμ` exposed is exactly what `seq-coe` absorbs
  ∙ seq-coe (step-≾ r) (step-≾ (SEQ-STEP {N = N} r c)) _
  where
    g : ⟦ hist 𝕊' ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ A₀ ⟧ᵛ ε₃
    g = ⟦ M' ⟧ᶜᵗ pM' ∘ᵐ ⟦ 𝕊' ⟧ˢ (stepᴾˢ r pS pM)

    mt : ⟦ hist 𝕊' ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ A ⟧ᵛ ε₃
    mt = (Tᶠ ⟦ step-refines-type r ⟧<:ᵛ ∘ᵐ ⟦ M' ⟧ᶜᵗ pM') ∘ᵐ ⟦ 𝕊' ⟧ˢ (stepᴾˢ r pS pM)

    ih' : ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ 𝕊 ⟧ˢ pS
        ≈ᵐ T-≤ (step-≾ r)
           ∘ᵐ _⋄_ {⟦ hist 𝕊 ⟧ᶜᵗˣ} {⟦ hist 𝕊' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {step-grade r} {ε₃}
                  mt (stepᵀ r)
    ih' = ih
        ∙ ∘ᵐ-congʳ (≈ᵐ-sym (Tᶠ-bind ⟦ step-refines-type r ⟧<:ᵛ g (stepᵀ r)))
        ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))


-- `SUB`: subsumption at a computation is discarded. Its value half becomes the
-- step's own type refinement, its effect half the step's sub-effecting.

sound-SUB : ∀ {ε ε' A A'} {𝕊 : State []}
  → {M : toCtx 𝕊 ⊢C⦂ A ! ε}
  → (p : A <:ᵛ A') → (q : ε ≾ₑ ε')
  → (pS : Paramˢ 𝕊) → (pM : Paramᶜ M)
  → ⟦ subC M (p !ₛ q) ⟧ᶜᵗ pM ∘ᵐ ⟦ 𝕊 ⟧ˢ pS
    ≈ᵐ T-≤ q ∘ᵐ Tᶠ ⟦ p ⟧<:ᵛ ∘ᵐ (⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ 𝕊 ⟧ˢ pS)
sound-SUB p q pS pM =
    ∘ᵐ-congˡ (∘ᵐ-congˡ (T-≤-nat ⟦ p ⟧<:ᵛ q))
  ∙ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)

-- `SUB-HANDLE`: a coerced handler literal, applied at its own grade, is the
-- literal applied at the restricted index (`curryʰ-nat`, `curryʰ-β`). The
-- input coercion enters the return clause, the output coercion stays in
-- front and becomes the step's refinement.

-- Applying a morphism into `Hᵒ` at a pairing.

appʰ-⟨⟩ : ∀ {X A ε B ε' ε₀} → (p : ε₀ ≾ₑ ε) → (k : X →ᵐ Hᵒ A ε B ε')
        → (m : X →ᵐ Tᵒ A ε₀)
        → appʰ p ∘ᵐ ⟨ k , m ⟩ᵐ ≈ᵐ (appʰ p ∘ᵐ mapˣᵐ k idᵐ) ∘ᵐ ⟨ idᵐ , m ⟩ᵐ
appʰ-⟨⟩ p k m =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- The fold reads a coercion of the handled values through its return clause.

handle-foldᵗ-Tᶠ : ∀ {X A A' B ε ε'} → (h : Handlerᵀ (⟨ ⊤ᵣ ⟩ᵒ X) B)
                → (n : ⟨ ∣ ε ∣ᵉ ⟩ᵒ X ×ᵐ A →ᵐ Tᵒ B ε') → (a : A' →ᵐ A)
                → handle-foldᵗ h n ∘ᵐ mapˣᵐ idᵐ (Tᶠ a)
                ≈ᵐ handle-foldᵗ h (n ∘ᵐ mapˣᵐ idᵐ a)
handle-foldᵗ-Tᶠ h n a =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ ( ⟨⟩ᵐ-∘ _ _ _
             ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _ ∙ ∘ᵐ-identityˡ _)
               ,   ∘ᵐ-assoc _ _ _
                 ∙ ∘ᵐ-congʳ ( ∘ᵐ-assoc _ _ _
                            ∙ ∘ᵐ-congʳ (mapˣᵐ-comm _ _)
                            ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                            ∙ ∘ᵐ-congˡ (strᵀ-natʳ a)
                            ∙ ∘ᵐ-assoc _ _ _)
                 ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                 ∙ ∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)) ⟩ᵐ-cong)

-- A relaxed return clause, coerced on its binder.

relax-coe : ∀ {X A A' C ρ₀ ρ} → (n : ⟨ ρ ⟩ᵒ X ×ᵐ A →ᵐ C) → (c : ρ₀ ≾ᵣ ρ)
          → (a : A' →ᵐ A)
          → (n ∘ᵐ mapˣᵐ (⟨⟩-≤ c) idᵐ) ∘ᵐ mapˣᵐ idᵐ a ≈ᵐ n ∘ᵐ mapˣᵐ (⟨⟩-≤ c) a
relax-coe n c a =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘ _ _ _ _ ∙ mapˣᵐ-cong (∘ᵐ-identityʳ _) (∘ᵐ-identityˡ _))

sound-SUB-HANDLE : ∀ {Γ A A₁ B B₁ ε ε₁ ε' ε₁'}
  → (M : Γ ⊢C⦂ A ! ε) → (N : Γ ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A₁ ⊢C⦂ B₁ ! ε₁')
  → (H : (op : Op) → (ε'' : E)
       → Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
            ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B₁ ! ε'')
         ⊢C⦂ B₁ ! (op-grade op ·ₑ ε''))
  → (p : A <:ᵛ A₁) → (pε : ε ≾ₑ ε₁) → (q : B₁ <:ᵛ B) → (s : ε₁' ≾ₑ ε')
  → (pM : Paramᶜ M) → (pN : Paramᶜ N)
  → (pH : ∀ op ε'' → Paramᶜ (H op ε'')) → (uH : EffUniformʰ {Γ} {B₁} H pH)
  → ⟦ handle M `with subV (handler N H) ((p !ₛ pε) ⇛ₛ (q !ₛ s)) ⟧ᶜᵗ
      (pM , pN , pH , uH)
  ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ s) ∘ᵐ Tᶠ ⟦ q ⟧<:ᵛ
     ∘ᵐ ⟦ handle M
          `with handler
                  (subCtx p (C-rename (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ pε))) N))
                  H ⟧ᶜᵗ
          ( pM
          , subCtxᴾ p (C-rename (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ pε))) N)
              (renᶜ (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ pε))) N pN)
          , pH , uH)
sound-SUB-HANDLE {Γ} M N H p pε q s pM pN pH uH = lhs ∙ ≈ᵐ-sym rhs
  where
    a = ⟦ p ⟧<:ᵛ
    b = ⟦ q ⟧<:ᵛ
    h = ⟦_⟧ʰᵗ {Γ} H pH uH
    n = ⟦ N ⟧ᶜᵗ pN
    m = ⟦ M ⟧ᶜᵗ pM
    k = curryʰ (handler-famᵗ h n) (handler-famᵗ-nat h n)

    Nr = C-rename (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ pε))) N
    pNr = renᶜ (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ pε))) N pN
    n' = ⟦ subCtx p Nr ⟧ᶜᵗ (subCtxᴾ p Nr pNr)

    -- the common core: the fold, its return clause relaxed and coerced
    G = handle-foldᵗ h (n ∘ᵐ mapˣᵐ (⟨⟩-≤ (map-monotoneᵉ pε)) a)

    n'≈ : n' ≈ᵐ n ∘ᵐ mapˣᵐ (⟨⟩-≤ (map-monotoneᵉ pε)) a
    n'≈ = subCtx-nat p Nr pNr
        ∙ ∘ᵐ-congˡ (C-rename-nat (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ pε))) N pN)
        ∙ relax-coe n (map-monotoneᵉ pε) a

    lhs : ⟦ handle M `with subV (handler N H) ((p !ₛ pε) ⇛ₛ (q !ₛ s)) ⟧ᶜᵗ
            (pM , pN , pH , uH)
        ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ s) ∘ᵐ Tᶠ b ∘ᵐ G ∘ᵐ ⟨ idᵐ , m ⟩ᵐ
    lhs =
        appʰ-⟨⟩ ≾ₑ-refl _ m
      ∙ ∘ᵐ-congˡ
          ( ∘ᵐ-congʳ (mapˣᵐ-cong (curryʰ-nat (mapʰ-fam a b pε s) (mapʰ-fam-nat a b pε s) k)
                                 ≈ᵐ-refl)
          ∙ curryʰ-β (λ e → mapʰ-fam a b pε s e ∘ᵐ mapˣᵐ k idᵐ)
                     (Naturalʰ-∘ (mapʰ-fam-nat a b pε s) k) ≾ₑ-refl
          ∙ ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
          -- the input coercion passes the handler value, which is applied
          ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
              ( ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-comm _ _))
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (curryʰ-β (handler-famᵗ h n) (handler-famᵗ-nat h n) _)
              ∙ handle-foldᵗ-Tᶠ h _ a
              ∙ handle-foldᵗ-cong h
                  ( relax-coe n _ a
                  ∙ ∘ᵐ-congʳ (mapˣᵐ-cong (⟨⟩-≤-irr _ _) ≈ᵐ-refl))))
          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙ ∘ᵐ-congˡ (T-≤-nat b _)
          ∙ ∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)

    rhs : T-≤ (·ₑ-monoʳ-≾ₑ s) ∘ᵐ Tᶠ b
            ∘ᵐ ⟦ handle M `with handler (subCtx p Nr) H ⟧ᶜᵗ
                 (pM , subCtxᴾ p Nr pNr , pH , uH)
        ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ s) ∘ᵐ Tᶠ b ∘ᵐ G ∘ᵐ ⟨ idᵐ , m ⟩ᵐ
    rhs =
      ∘ᵐ-congʳ (∘ᵐ-congʳ
        ( appʰ-⟨⟩ ≾ₑ-refl _ m
        ∙ ∘ᵐ-congˡ
            ( curryʰ-β (handler-famᵗ h n') (handler-famᵗ-nat h n') ≾ₑ-refl
            ∙ handle-foldᵗ-cong h
                ( ∘ᵐ-congʳ ( mapˣᵐ-cong (⟨⟩-≤-irr _ _ ∙ ⟨⟩-≤-refl) ≈ᵐ-refl
                           ∙ mapˣᵐ-idᵐ)
                ∙ ∘ᵐ-identityʳ _
                ∙ n'≈))))

-- `SUB-HANDLE-TRANS`: nested coercions denote their composite.

sound-SUB-HANDLE-TRANS : ∀ {Γ A₀ A' A B ε ε'}
  → (M : Γ ⊢C⦂ A ! ε) → (V : Γ ⊢V⦂ A₀)
  → (p : A₀ <:ᵛ A') → (p' : A' <:ᵛ (A ! ε) ⇛ (B ! ε'))
  → (pM : Paramᶜ M) → (pV : Paramᵛ V)
  → ⟦ handle M `with subV (subV V p) p' ⟧ᶜᵗ (pM , pV)
  ≈ᵐ ⟦ handle M `with subV V (<:ᵛ-trans p p') ⟧ᶜᵗ (pM , pV)
sound-SUB-HANDLE-TRANS M V p p' pM pV =
  ∘ᵐ-congʳ ⟨ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟦⟧<:ᵛ-trans p p'))
           , ≈ᵐ-refl ⟩ᵐ-cong
