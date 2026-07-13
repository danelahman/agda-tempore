------------------------------------------------------------------------
-- Soundness of the small-step operational semantics.                   --
--                                                                    --
-- A configuration `⟨ S , M ⟩` interprets as the open computation `M`   --
-- with its context plugged by the state:                                --
--                                                                    --
--   ⟦ ⟨ S , M ⟩ ⟧ᶜᶠ = ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ S ⟧ˢ                                --
--                                                                    --
-- The plug is total on the *cells* of `toCtx S` (each carries its       --
-- stored value) but not on the *locks*: `⟨ ρ ⟩ᵒ X` has no global points, --
-- so the passage of time cannot be manufactured. What remains is the     --
-- state's history `hist S`, and a configuration therefore denotes a      --
-- morphism out of `⟦ hist S ⟧ᶜᵗˣ` — for an initial state `∅` that is     --
-- `𝟙ᵐ`, i.e. a genuine global point.                                     --
--                                                                    --
-- A reduction step then relates the two denotations. Since the two       --
-- configurations have different histories and different effect grades,   --
-- the statement is mediated by                                          --
--                                                                    --
--   * a *time transition* `stepᵀ r : ⟦ hist S ⟧ →ᵐ Tᵒ ⟦ hist S' ⟧ δ`,    --
--     which is the identity (`ηᵀ`) for every rule but `DELAY` — the only --
--     rule that adds a lock — where it is the tick built from `delayᵀ`;  --
--                                                                    --
--   * a sub-effecting coercion `T-≤`, because reduction *refines* the    --
--     effect grade (`COERCE` peels a coercion off; `SEQ-STEP` sharpens   --
--     a grade). The tree equality collapses coercion nodes, so `T-≤` is  --
--     functorial in the grade and the relation stays a preorder.         --
--                                                                    --
-- Note `BOX` needs no transition: allocating a resource and extending    --
-- the store are the *same* morphism (`[ ρ ]ᶠ ⟦ V ⟧ ∘ᵐ η⊣`), which is     --
-- what `⟦_⟧ˢ`'s cell clause and `⟦ box V M ⟧ᶜᵗ` both use. Dually `UNBOX` --
-- needs none either: it is already a projection out of the environment.  --
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

module DenotationalSemantics.Soundness.Preservation
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types     S
open import Syntax.Contexts  S
open import Syntax.Language  S
open import Syntax.Renamings S

open import OperationalSemantics.State S
open import OperationalSemantics.PreservationTheorem S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ)
open Adjunction Adj using (η⊣)
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst GTy Mon
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.State S Cat Fut Pst Adj GTy Mon GE

-- THE INTERPRETATION OF A CONFIGURATION
--
-- The computation, with its context plugged by the state.

⟦_⟧ᶜᶠ : ∀ {C} → (cf : Config C) → ⟦ hist (Config.state cf) ⟧ᶜᵗˣ →ᵐ ⟦ C ⟧ᶜ
⟦ ⟨ St , M ⟩ ⟧ᶜᶠ = ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ St ⟧ˢ

-- KLEISLI COMPOSITION WITH A TIME TRANSITION
--
-- Running a computation over the later history, after the transition that
-- produces it. The effect grades multiply.

_⋄_ : ∀ {H H' A ε ε'}
    → (⟦ H' ⟧ᶜᵗˣ →ᵐ Tᵒ A ε')
    → (⟦ H ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ H' ⟧ᶜᵗˣ ε)
    → ⟦ H ⟧ᶜᵗˣ →ᵐ Tᵒ A (ε ·ₑ ε')
f ⋄ t = μᵀ ∘ᵐ Tᶠ f ∘ᵐ t

infixl 25 _⋄_

-- THE TIME TRANSITION OF A STEP
--
-- The effect it performs. Only `DELAY` does anything: it is the sole rule
-- that advances time, and it does so by exactly its own delay. Resources
-- (cells) are allocated into the *shape* of the store, never into the
-- effect grade, which is why allocation contributes `uₑ`.

step-grade : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
           → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
           → ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩
           → E
step-grade APP                  = uₑ
step-grade MATCH                = uₑ
step-grade (SEQ-STEP r _)       = step-grade r
step-grade SEQ-RET              = uₑ
step-grade SEQ-OP               = uₑ
step-grade (DELAY {τ = τ})      = of-natᵉ τ
step-grade HANDLE-RET           = uₑ
step-grade (HANDLE-STEP r _)    = step-grade r
step-grade HANDLE-OP            = uₑ
step-grade BOX                  = uₑ
step-grade UNBOX                = uₑ
step-grade COERCE               = uₑ

-- The transition itself. `DELAY` ticks: it names the present as the past of
-- every world one delay ahead (`η⊣`), and `delayᵀ` is what actually reaches
-- those worlds — this is the only way a lock can ever be produced.

stepᵀ : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
      → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
      → (r : ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩)
      → ⟦ hist St ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ hist St' ⟧ᶜᵗˣ (step-grade r)
stepᵀ APP               = ηᵀ
stepᵀ MATCH             = ηᵀ
stepᵀ (SEQ-STEP r _)    = stepᵀ r
stepᵀ SEQ-RET           = ηᵀ
stepᵀ SEQ-OP            = ηᵀ
stepᵀ (DELAY {τ = τ})   =
  ε-substᵀ (·ₑ-identityʳ (of-natᵉ τ)) ∘ᵐ delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣
stepᵀ HANDLE-RET        = ηᵀ
stepᵀ (HANDLE-STEP r _) = stepᵀ r
stepᵀ HANDLE-OP         = ηᵀ
stepᵀ BOX               = ηᵀ
stepᵀ UNBOX             = ηᵀ
stepᵀ COERCE            = ηᵀ

-- The step's effect, composed with the target's, refines the source's.
-- (This is the *effect*-graded counterpart of `step-invariants`, whose
-- grade-decrease condition lives in the resource grades.)

step-≾ : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
       → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
       → (r : ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩)
       → step-grade r ·ₑ ε' ≾ₑ ε
step-≾ {ε = ε} APP    = ≾ₑ-reflexive (·ₑ-identityˡ ε)
step-≾ {ε = ε} MATCH  = ≾ₑ-reflexive (·ₑ-identityˡ ε)
step-≾ (SEQ-STEP {ε₂ = ε₂} {ε₃ = ε₃} r _) =
  ≾ₑ-trans
    (≾ₑ-reflexive (sym (·ₑ-assoc (step-grade r) ε₃ ε₂)))
    (·ₑ-monoˡ-≾ₑ (step-≾ r))
step-≾ SEQ-RET        = ≾ₑ-reflexive refl
step-≾ {ε = ε} SEQ-OP = ≾ₑ-reflexive (·ₑ-identityˡ ε)
step-≾ DELAY          = ≾ₑ-reflexive refl
step-≾ HANDLE-RET     = ≾ₑ-reflexive refl
step-≾ (HANDLE-STEP {ε₂ = ε₂} {ε₁' = ε₁'} r _) =
  ≾ₑ-trans
    (≾ₑ-reflexive (sym (·ₑ-assoc (step-grade r) ε₁' ε₂)))
    (·ₑ-monoˡ-≾ₑ (step-≾ r))
step-≾ (HANDLE-OP {ε = ε} {ε'' = ε''} {op = op}) =
  ≾ₑ-reflexive
    (trans (·ₑ-identityˡ _) (sym (·ₑ-assoc (op-grade op) ε ε'')))
step-≾ {ε = ε} BOX    = ≾ₑ-reflexive (·ₑ-identityˡ ε)
step-≾ {ε = ε} UNBOX  = ≾ₑ-reflexive (·ₑ-identityˡ ε)
step-≾ (COERCE {ε = ε} {ε≾ε' = ε≾ε'}) =
  ≾ₑ-trans (≾ₑ-reflexive (·ₑ-identityˡ ε)) ε≾ε'
