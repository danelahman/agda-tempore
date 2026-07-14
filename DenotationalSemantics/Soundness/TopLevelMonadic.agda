------------------------------------------------------------------------
-- Soundness of the MONADIC top-level operational semantics.             --
--                                                                    --
-- The top-level machine runs a program against external implementations  --
-- of the algebraic operations, which now live in a runtime monad `T` on  --
-- `Set` — the reduct of a step is a `T`-computation of configurations:   --
--                                                                    --
--   OP-STEPₘ : ⟨ S , perform op V M ⟩                                   --
--            ⟿ₘ (mon-op-sem op V >>=                                    --
--                 λ V' → returnM ⟨ S ⟨ mapᵉ (op-grade op) ⟩ₛ            --
--                                , M [ Hd ↦ V' ]c ⟩)                    --
--                                                                    --
-- `T` is a monad over the *syntax*. Its denotational counterpart is a    --
-- strong monad `Mᵒ` over the model (`Model.RuntimeMonad`), and the two   --
-- are related by `RuntimeSemantics` below. A term denotes a morphism,    --
-- i.e. a point of an exponential, so a `T`-computation of terms denotes  --
-- a point of `Mᵒ` applied to that exponential; `kleisliᵐ` derives the     --
-- Kleisli map from it (`Soundness.RuntimeLemmas`).                       --
--                                                                    --
-- Computations are run into the tick monad by `implᵐ ∘ᵐ ⟦_⟧ᶜᶠ`, and the   --
-- runtime effects are absorbed by the algebra `algᴹ` that the tick       --
-- monad's computations carry (`Model.MonadicImplementation`).            --
--                                                                    --
-- The reducts of a step do NOT share a state — `BOX` stores the value    --
-- the runtime computed — but they do share a HISTORY, which is all a     --
-- configuration's denotation takes as its domain. `⟿ₘ-target` proves     --
-- the operational reduct is a `T`-computation of `HConfig`s over one     --
-- history, and soundness is stated about that.                           --
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
open import DenotationalSemantics.Model.TickMonad
open import DenotationalSemantics.Model.RuntimeMonad
open import DenotationalSemantics.Model.MonadicImplementation

module DenotationalSemantics.Soundness.TopLevelMonadic
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
         (TMon : TickMonad S Cat Fut)
         (RMon : RuntimeMonad Cat)
         (MImpl : MonadicImplementation S Cat Fut Pst Adj GTy Mon TMon RMon)
       where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; _×_)

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.Substitutions S

open import OperationalSemantics.State                       S
open import OperationalSemantics.PreservationTheorem         S
open import OperationalSemantics.TopLevelOpSemantics         S
open import OperationalSemantics.TopLevelPreservationTheorem S

import Util.Monad as RT

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-congᶠ; []-∘ᵐ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ)
open Adjunction Adj using (η⊣; η⊣-nat)
open GroundTypes GTy using (⟦_⟧ᵍ)
open Monad Mon using (Tᵒ; Tᶠ; ηᵀ; μᵀ; T-≤; ε-substᵀ; delayᵀ; opᵀ)
open TickMonad TMon
open RuntimeMonad RMon
open MonadicImplementation MImpl

open import DenotationalSemantics.Interpretation.Types S Cat Fut GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst GTy Mon
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.State S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Soundness.Preservation S Cat Fut Pst Adj GTy Mon GE

open import DenotationalSemantics.Soundness.TickLemmas S Cat Fut GTy Mon TMon
open ImplLemmas implᵐ implᵐ-μᵀ implᵐ-nat

open import DenotationalSemantics.Soundness.RuntimeLemmas Cat RMon

-- The operation's continuation, with the interpretation's ground-type coercion
-- on the arity applied. This is the morphism both the implementation's
-- operation node and the reduct's bind carry.

contᵐ : ∀ {A ε} → (op : Op) → (St : 𝕊 [])
      → toCtx St ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε
      → (⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ toCtx St ⟧ᶜᵗˣ ×ᵐ ⟦ arity op ⟧ᵍ)
        →ᵐ Tᵒ ⟦ A ⟧ᵛ ε
contᵐ {A} {ε} op St M =
  subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ toCtx St ⟧ᶜᵗˣ ×ᵐ O) →ᵐ Tᵒ ⟦ A ⟧ᵛ ε)
        (ty-gty (arity op)) ⟦ M ⟧ᶜᵗ


module MonadicTopLevelSoundness
         {rt : RT.Monad}
         (MOpSem : TopLevelMonadicOpSemantics rt)
       where

  open RT.Monad rt
  open TopLevelMonadicOpSemantics MOpSem
  open MonadicTopLevelPreservationTheorem {rt} MOpSem

  ------------------------------------------------------------------------
  -- CONFIGURATIONS OVER A HISTORY
  --
  -- The reducts of a step do NOT share a state: `BOX` stores the value the
  -- runtime computed, so each of them extends the state with its own cell.
  -- What they do share is the *history* — cells are dropped from it — and the
  -- history is all a configuration's denotation takes as its domain.
  ------------------------------------------------------------------------

  record HConfig (H : Ctx) (C : CType) : Set where
    constructor ⟪_,_,_⟫
    field
      state : 𝕊 []
      hist≡ : hist state ≡ H
      comp  : toCtx state ⊢C⦂ C

  hcfg : ∀ {C} → (St : 𝕊 []) → toCtx St ⊢C⦂ C → HConfig (hist St) C
  hcfg St M = ⟪ St , refl , M ⟫

  ⟦_⟧ʰᶜᶠ : ∀ {H C} → HConfig H C → (⟦ H ⟧ᶜᵗˣ →ᵐ ⟦ C ⟧ᶜ)
  ⟦ ⟪ St , refl , M ⟫ ⟧ʰᶜᶠ = ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ St ⟧ˢ

  flattenᴴ : ∀ {H C} → T (HConfig H C) → T (Config C)
  flattenᴴ th =
    th >>= (λ hcf → returnM (⟨ HConfig.state hcf , HConfig.comp hcf ⟩))

  ------------------------------------------------------------------------
  -- THE RUNTIME MONAD'S SEMANTICS
  --
  -- A term denotes a morphism, i.e. a POINT of the exponential. So a runtime
  -- computation of terms denotes a point of `Mᵒ` applied to that exponential.
  -- The Kleisli map it induces is derived, not assumed (`kleisliᵐ`).
  --
  -- The only law needed of it here is that `returnM` names the configuration's
  -- denotation. What the machine's operation step denotes is the theorem's
  -- coherence condition, `MOpSemCoherent` below.
  ------------------------------------------------------------------------

  record RuntimeSemantics : Set₁ where
    field
      ⟦_⟧ᵐᶜᶠ : ∀ {H C} → T (HConfig H C) → (𝟙ᵐ →ᵐ Mᵒ (⟦ H ⟧ᶜᵗˣ ⇒ᵐ ⟦ C ⟧ᶜ))

      ⟦⟧ᵐᶜᶠ-return : ∀ {H C} → (hcf : HConfig H C)
                   → ⟦ returnM hcf ⟧ᵐᶜᶠ ≈ᵐ ηᴹ ∘ᵐ ptᵐ ⟦ hcf ⟧ʰᶜᶠ

  ------------------------------------------------------------------------
  -- THE REDUCTS OF A STEP
  ------------------------------------------------------------------------

  hist-of : ∀ {A ε ε'} {St : 𝕊 []}
          → {M : toCtx St ⊢C⦂ A ‼ ε} → {tcf : T (Config (A ‼ ε'))}
          → ⟨ St , M ⟩ ⟿ₘ tcf → Ctx
  hist-of (↝-STEPₘ {S' = St'} _)          = hist St'
  hist-of (OP-STEPₘ {op = op} {S = St})   = hist St ⟨ mapᵉ (op-grade op) ⟩

  target : ∀ {A ε ε'} {St : 𝕊 []}
         → {M : toCtx St ⊢C⦂ A ‼ ε} → {tcf : T (Config (A ‼ ε'))}
         → (r : ⟨ St , M ⟩ ⟿ₘ tcf)
         → T (HConfig (hist-of r) (A ‼ ε'))
  target (↝-STEPₘ {S' = St'} {M' = M'} _) = returnM (hcfg St' M')
  target (OP-STEPₘ {op = op} {S = St} {V = V} {M = M}) =
    mon-op-sem op V >>=
      (λ V' → returnM (hcfg (grade-pass St (mapᵉ (op-grade op)))
                            (M [ Hd ↦ V' ]c)))

  -- The operational reduct is exactly the flattening of those: every
  -- configuration the step can produce has the same history.

  ⟿ₘ-target : ∀ {A ε ε'} {St : 𝕊 []}
            → {M : toCtx St ⊢C⦂ A ‼ ε} → {tcf : T (Config (A ‼ ε'))}
            → (r : ⟨ St , M ⟩ ⟿ₘ tcf)
            → tcf ≡ flattenᴴ (target r)
  ⟿ₘ-target (↝-STEPₘ {S' = St'} {M' = M'} _) =
    sym (>>=-apply (hcfg St' M')
                   (λ hcf → returnM (⟨ HConfig.state hcf , HConfig.comp hcf ⟩)))
  ⟿ₘ-target (OP-STEPₘ {op = op} {S = St} {V = V} {M = M}) =
    sym
      (trans
        (>>=-assoc (mon-op-sem op V)
                   (λ V' → returnM (hcfg (grade-pass St (mapᵉ (op-grade op)))
                                         (M [ Hd ↦ V' ]c)))
                   (λ hcf → returnM (⟨ HConfig.state hcf , HConfig.comp hcf ⟩)))
        (cong (mon-op-sem op V >>=_)
              (fun-ext (λ V' →
                 >>=-apply (hcfg (grade-pass St (mapᵉ (op-grade op)))
                                 (M [ Hd ↦ V' ]c))
                           (λ hcf → returnM
                                      (⟨ HConfig.state hcf
                                       , HConfig.comp hcf ⟩))))))

  -- THE STEP'S GRADE, TRANSITION AND REFINEMENT

  top-gradeₘ : ∀ {A ε ε'} {St : 𝕊 []}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {tcf : T (Config (A ‼ ε'))}
             → ⟨ St , M ⟩ ⟿ₘ tcf → E
  top-gradeₘ (↝-STEPₘ r)          = step-grade r
  top-gradeₘ (OP-STEPₘ {op = op}) = op-grade op ·ₑ uₑ

  top-stepᵏₘ : ∀ {A ε ε'} {St : 𝕊 []}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {tcf : T (Config (A ‼ ε'))}
             → (r : ⟨ St , M ⟩ ⟿ₘ tcf)
             → ⟦ hist St ⟧ᶜᵗˣ →ᵐ Tᵏ ⟦ hist-of r ⟧ᶜᵗˣ (top-gradeₘ r)
  top-stepᵏₘ (↝-STEPₘ r) = implᵐ ∘ᵐ stepᵀ r
  top-stepᵏₘ (OP-STEPₘ {op = op}) =
    tickᵏ (op-grade op) ∘ᵐ [ mapᵉ (op-grade op) ]ᶠ ηᵏ ∘ᵐ η⊣

  top-≾ₘ : ∀ {A ε ε'} {St : 𝕊 []}
         → {M : toCtx St ⊢C⦂ A ‼ ε} → {tcf : T (Config (A ‼ ε'))}
         → (r : ⟨ St , M ⟩ ⟿ₘ tcf)
         → top-gradeₘ r ·ₑ ε' ≾ₑ ε
  top-≾ₘ (↝-STEPₘ r) = step-≾ r
  top-≾ₘ (OP-STEPₘ {ε = ε} {op = op}) =
    ≾ₑ-reflexive (cong (_·ₑ ε) (·ₑ-identityʳ (op-grade op)))

  Uniform⟿ₘ : ∀ {A ε ε'} {St : 𝕊 []}
            → {M : toCtx St ⊢C⦂ A ‼ ε} → {tcf : T (Config (A ‼ ε'))}
            → ⟨ St , M ⟩ ⟿ₘ tcf → Set
  Uniform⟿ₘ (↝-STEPₘ r) = Uniform↝ r
  Uniform⟿ₘ OP-STEPₘ    = ⊤


  module _ (RS : RuntimeSemantics) where

    open RuntimeSemantics RS

    -- The operation's parameter, with the ground-type coercion the
    -- interpretation carries.

    paramᵐ : (op : Op) → (St : 𝕊 [])
           → toCtx St ⊢V⦂ type-of-gtype (param op)
           → ⟦ toCtx St ⟧ᶜᵗˣ →ᵐ ⟦ param op ⟧ᵍ
    paramᵐ op St V =
      subst (λ O → ⟦ toCtx St ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) ⟦ V ⟧ᵛᵗ

    -- THE THEOREM'S ONLY CONDITION
    --
    -- What an operation step's reducts denote: run the implementation
    -- `op-semᵐ` on the parameter — a Kleisli map into `Mᵒ ⟦ arity op ⟧ᵍ`, which
    -- is what a monadic implementation of an operation is — carry the locked
    -- state's environment into it with the strength, and substitute the value
    -- it returns into the operation's continuation.
    --
    -- `op-semᵐ` is a single morphism out of the *parameter*, not indexed by the
    -- state, which is the naturality in `S` that `mon-op-sem` is annotated as
    -- requiring.

    MOpSemCoherent : Set
    MOpSemCoherent =
      ∀ {A ε} → (op : Op) → (St : 𝕊 [])
      → (V : toCtx St ⊢V⦂ type-of-gtype (param op))
      → (M : toCtx St ⟨ mapᵉ (op-grade op) ⟩
             ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
      → kleisliᵐ ⟦ mon-op-sem op V >>= (λ V' → returnM
                     (hcfg (grade-pass St (mapᵉ (op-grade op)))
                           (M [ Hd ↦ V' ]c))) ⟧ᵐᶜᶠ
      ≈ᵐ Mᶠ (contᵐ op St M)
         ∘ᵐ strᴹ
         ∘ᵐ ⟨ idᵐ , op-semᵐ op ∘ᵐ ⟨ mapᵉ (op-grade op) ⟩ᶠ (paramᵐ op St V) ⟩ᵐ
         ∘ᵐ ⟦ grade-pass St (mapᵉ (op-grade op)) ⟧ˢ

    module _ (op-coh : MOpSemCoherent) where

      -- THE TOP-LEVEL DENOTATIONS
      --
      -- A configuration denotes as in the pure semantics. A runtime
      -- computation of configurations is applied to the history, its
      -- operations are run, and the runtime effects are absorbed by the
      -- algebra.

      ⟦_⟧ᵏᶜᶠ : ∀ {A ε} → (cf : Config (A ‼ ε))
             → ⟦ hist (Config.state cf) ⟧ᶜᵗˣ →ᵐ Tᵏ ⟦ A ⟧ᵛ ε
      ⟦ cf ⟧ᵏᶜᶠ = implᵐ ∘ᵐ ⟦ cf ⟧ᶜᶠ

      runᵐ : ∀ {X B ε} → (𝟙ᵐ →ᵐ Mᵒ (X ⇒ᵐ Tᵒ B ε)) → (X →ᵐ Tᵏ B ε)
      runᵐ b = algᴹ ∘ᵐ Mᶠ implᵐ ∘ᵐ kleisliᵐ b

      runᵐ-cong : ∀ {X B ε} → {b b' : 𝟙ᵐ →ᵐ Mᵒ (X ⇒ᵐ Tᵒ B ε)}
                → b ≈ᵐ b' → runᵐ b ≈ᵐ runᵐ b'
      runᵐ-cong e = ∘ᵐ-congʳ (∘ᵐ-congʳ (kleisliᵐ-cong e))

      -- A returned configuration runs as that configuration: the algebra
      -- swallows the runtime monad's unit.

      runᵐ-return : ∀ {X B ε} → (f : X →ᵐ Tᵒ B ε)
                  → runᵐ (ηᴹ ∘ᵐ ptᵐ f) ≈ᵐ implᵐ ∘ᵐ f
      runᵐ-return f =
          ∘ᵐ-congʳ (∘ᵐ-congʳ (kleisliᵐ-ptᵐ f))
        ∙ᵏ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (ηᴹ-nat implᵐ))
        ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
        ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
        ∙ᵏ ∘ᵐ-congˡ algᴹ-ηᴹ
        ∙ᵏ ∘ᵐ-identityˡ _

      -- OP-STEPₘ
      --
      -- The implementation computes the arity value in the runtime monad,
      -- carries the environment into it with the strength, and runs the
      -- continuation under it. By `MOpSemCoherent` that is the very runtime
      -- computation the reduct binds, so what is left is the operation's tick.

      sound-OP-STEPₘ : ∀ {A ε} → (op : Op) → (St : 𝕊 [])
                     → (V : toCtx St ⊢V⦂ type-of-gtype (param op))
                     → (M : toCtx St ⟨ mapᵉ (op-grade op) ⟩
                            ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
                     → ⟦ ⟨ St , perform op V M ⟩ ⟧ᵏᶜᶠ
                     ≈ᵐ T-≤ᵏ (top-≾ₘ (OP-STEPₘ {op = op} {S = St} {V = V} {M = M}))
                        ∘ᵐ _⋄ᵏ_ {⟦ hist St ⟧ᶜᵗˣ}
                                {⟦ hist St ⟨ mapᵉ (op-grade op) ⟩ ⟧ᶜᵗˣ}
                                {⟦ A ⟧ᵛ} {op-grade op ·ₑ uₑ} {ε}
                                (runᵐ ⟦ target (OP-STEPₘ {op = op} {S = St}
                                                         {V = V} {M = M}) ⟧ᵐᶜᶠ)
                                (top-stepᵏₘ (OP-STEPₘ {op = op} {S = St}
                                                      {V = V} {M = M}))
      sound-OP-STEPₘ {A} {ε} op St V M =
        -- run the operation
          ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
        ∙ᵏ ∘ᵐ-congˡ (implᵐ-opᵀ op (paramᵐ op St V) k)
        ∙ᵏ ∘ᵐ-assoc _ _ _
        ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
        -- the state's environment goes under the operation's box
        ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat ⟦ St ⟧ˢ)))
        ∙ᵏ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
        -- and what is boxed is the reduct, run
        ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ cont))
        -- what is left is a tick, and `tick-nf` says the target is its bind
        ∙ᵏ ≈ᵐ-sym (∘ᵐ-congʳ (tick-nf d η⊣ (runᵐ ⟦ tgt ⟧ᵐᶜᶠ)) ∙ᵏ coe)
        where
          d = op-grade op

          St' : 𝕊 []
          St' = grade-pass St (mapᵉ d)

          tgt : T (HConfig (hist St ⟨ mapᵉ d ⟩) (A ‼ ε))
          tgt = target (OP-STEPₘ {op = op} {S = St} {V = V} {M = M})

          k : (⟨ mapᵉ d ⟩ᵒ ⟦ toCtx St ⟧ᶜᵗˣ ×ᵐ ⟦ arity op ⟧ᵍ) →ᵐ Tᵒ ⟦ A ⟧ᵛ ε
          k = contᵐ op St M

          -- the target bag, run: `MOpSemCoherent` says it is the very shape
          -- the implementation produces
          tgt-run : runᵐ ⟦ tgt ⟧ᵐᶜᶠ
                  ≈ᵐ algᴹ
                     ∘ᵐ Mᶠ (implᵐ ∘ᵐ k)
                     ∘ᵐ strᴹ
                     ∘ᵐ ⟨ idᵐ , op-semᵐ op ∘ᵐ ⟨ mapᵉ d ⟩ᶠ (paramᵐ op St V) ⟩ᵐ
                     ∘ᵐ ⟨ mapᵉ d ⟩ᶠ ⟦ St ⟧ˢ
          tgt-run =
              ∘ᵐ-congʳ (∘ᵐ-congʳ (op-coh op St V M))
            ∙ᵏ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (Mᶠ-∘ᵐ _ _)))

          -- the operation's continuation, run under the runtime computation the
          -- implementation returns, IS the reduct
          cont : (algᴹ
                  ∘ᵐ Mᶠ (implᵐ ∘ᵐ k)
                  ∘ᵐ strᴹ
                  ∘ᵐ ⟨ idᵐ , op-semᵐ op ∘ᵐ ⟨ mapᵉ d ⟩ᶠ (paramᵐ op St V) ⟩ᵐ)
                 ∘ᵐ ⟨ mapᵉ d ⟩ᶠ ⟦ St ⟧ˢ
               ≈ᵐ runᵐ ⟦ tgt ⟧ᵐᶜᶠ
          cont =
              ∘ᵐ-assoc _ _ _
            ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
            ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
            ∙ᵏ ≈ᵐ-sym tgt-run

          -- the coercions collapse: the source's grade is reached exactly
          coe : T-≤ᵏ (top-≾ₘ (OP-STEPₘ {op = op} {S = St} {V = V} {M = M}))
                  ∘ᵐ (T-≤ᵏ (tick-z d ε)
                      ∘ᵐ tickᵏ d ∘ᵐ [ mapᵉ d ]ᶠ (runᵐ ⟦ tgt ⟧ᵐᶜᶠ) ∘ᵐ η⊣)
              ≈ᵐ tickᵏ d ∘ᵐ [ mapᵉ d ]ᶠ (runᵐ ⟦ tgt ⟧ᵐᶜᶠ) ∘ᵐ η⊣
          coe =
              ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
            ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-trans _ _ (≾ₑ-reflexive {d ·ₑ ε} refl))
            ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-refl _)
            ∙ᵏ ∘ᵐ-identityˡ _

      -- SOUNDNESS OF A MONADIC TOP-LEVEL STEP

      ⟿ₘ-sound : ∀ {A ε ε'} {St : 𝕊 []}
                → {M : toCtx St ⊢C⦂ A ‼ ε} → {tcf : T (Config (A ‼ ε'))}
                → (r : ⟨ St , M ⟩ ⟿ₘ tcf)
                → Uniform⟿ₘ r
                → ⟦ ⟨ St , M ⟩ ⟧ᵏᶜᶠ
                ≈ᵐ T-≤ᵏ (top-≾ₘ r)
                   ∘ᵐ _⋄ᵏ_ {⟦ hist St ⟧ᶜᵗˣ} {⟦ hist-of r ⟧ᶜᵗˣ}
                           {⟦ A ⟧ᵛ} {top-gradeₘ r} {ε'}
                           (runᵐ ⟦ target r ⟧ᵐᶜᶠ) (top-stepᵏₘ r)
      ⟿ₘ-sound (↝-STEPₘ {S' = St'} {M' = M'} r) u =
          ∘ᵐ-congʳ (↝-sound r u)
        ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
        ∙ᵏ ∘ᵐ-congˡ (implᵐ-T-≤ (step-≾ r))
        ∙ᵏ ∘ᵐ-assoc _ _ _
        ∙ᵏ ∘ᵐ-congʳ (impl-⋄ ⟦ ⟨ St' , M' ⟩ ⟧ᶜᶠ (stepᵀ r))
        ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (Tᵏ-congᶠ
             (≈ᵐ-sym (  runᵐ-cong (⟦⟧ᵐᶜᶠ-return (hcfg St' M'))
                      ∙ᵏ runᵐ-return ⟦ ⟨ St' , M' ⟩ ⟧ᶜᶠ)))))
      ⟿ₘ-sound (OP-STEPₘ {op = op} {S = St} {V = V} {M = M}) _ =
        sound-OP-STEPₘ op St V M
