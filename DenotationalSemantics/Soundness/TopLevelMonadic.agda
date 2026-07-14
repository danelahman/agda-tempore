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
-- are related by `RuntimeSemantics` below: a `T`-computation of terms    --
-- denotes an `Mᵒ`-computation of their denotations.                      --
--                                                                    --
-- The top-level denotation is again `implᵐ ∘ᵐ ⟦_⟧ᶜᶠ` into the tick monad --
-- (`Model.MonadicImplementation`), whose computations are now            --
-- `Mᵒ`-algebras: that is how the runtime monad's effects are absorbed     --
-- into a top-level computation.                                          --
--                                                                    --
-- A step's reducts all share one state — only the value the operation    --
-- returns varies inside `T` — so they form an `MConfig`: a state and a   --
-- `T`-computation of computations. `⟿ₘ-target` proves the operational   --
-- reduct is exactly such a thing, and soundness is stated about it.      --
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

-- The interpretation's ground-type coercion, on the two sides of the arity, is
-- cancelled by the strength.

substᴹ-str : ∀ {Z W Y Y'} → (e : Y ≡ Y')
           → (f : (Z ×ᵐ Y) →ᵐ W) → (g : Z →ᵐ Mᵒ Y)
           → Mᶠ (subst (λ O → (Z ×ᵐ O) →ᵐ W) e f)
               ∘ᵐ strᴹ ∘ᵐ ⟨ idᵐ , subst (λ O → Z →ᵐ Mᵒ O) e g ⟩ᵐ
           ≈ᵐ Mᶠ f ∘ᵐ strᴹ ∘ᵐ ⟨ idᵐ , g ⟩ᵐ
substᴹ-str refl f g = ≈ᵐ-refl


module MonadicTopLevelSoundness
         {rt : RT.Monad}
         (MOpSem : TopLevelMonadicOpSemantics rt)
       where

  open RT.Monad rt
  open TopLevelMonadicOpSemantics MOpSem
  open MonadicTopLevelPreservationTheorem {rt} MOpSem

  ------------------------------------------------------------------------
  -- THE RUNTIME MONAD'S SEMANTICS
  --
  -- `Mᵒ` is the counterpart of `T`: a `T`-computation of terms denotes an
  -- `Mᵒ`-computation of their denotations, compatibly with `returnM`, and with
  -- the one bind the operational semantics performs — substituting the value
  -- the runtime computes into a continuation.
  ------------------------------------------------------------------------

  record RuntimeSemantics : Set₁ where
    field
      ⟦_⟧ᵛᵐ : ∀ {Γ A} → T (Γ ⊢V⦂ A) → (⟦ Γ ⟧ᶜᵗˣ →ᵐ Mᵒ ⟦ A ⟧ᵛ)
      ⟦_⟧ᶜᵐ : ∀ {Γ C} → T (Γ ⊢C⦂ C) → (⟦ Γ ⟧ᶜᵗˣ →ᵐ Mᵒ ⟦ C ⟧ᶜ)

      ⟦⟧ᵛᵐ-return : ∀ {Γ A} → (V : Γ ⊢V⦂ A)
                  → ⟦ returnM V ⟧ᵛᵐ ≈ᵐ ηᴹ ∘ᵐ ⟦ V ⟧ᵛᵗ
      ⟦⟧ᶜᵐ-return : ∀ {Γ C} → (M : Γ ⊢C⦂ C)
                  → ⟦ returnM M ⟧ᶜᵐ ≈ᵐ ηᴹ ∘ᵐ ⟦ M ⟧ᶜᵗ

      ⟦⟧ᶜᵐ-bind : ∀ {Γ A C} → (t : T (Γ ⊢V⦂ A)) → (M : Γ ∷ A ⊢C⦂ C)
                → ⟦ t >>= (λ V → returnM (M [ Hd ↦ V ]c)) ⟧ᶜᵐ
                ≈ᵐ Mᶠ ⟦ M ⟧ᶜᵗ ∘ᵐ strᴹ ∘ᵐ ⟨ idᵐ , ⟦ t ⟧ᵛᵐ ⟩ᵐ

  ------------------------------------------------------------------------
  -- THE REDUCTS OF A MONADIC STEP
  --
  -- One state, and a runtime computation of computations over it.
  ------------------------------------------------------------------------

  record MConfig (C : CType) : Set where
    constructor ⟪_,_⟫
    field
      state : 𝕊 []
      comps : T (toCtx state ⊢C⦂ C)

  flatten : ∀ {C} → MConfig C → T (Config C)
  flatten ⟪ St , t ⟫ = t >>= (λ M → returnM (⟨ St , M ⟩))

  target : ∀ {A ε ε'} {St : 𝕊 []}
         → {M : toCtx St ⊢C⦂ A ‼ ε} → {tcf : T (Config (A ‼ ε'))}
         → ⟨ St , M ⟩ ⟿ₘ tcf
         → MConfig (A ‼ ε')
  target (↝-STEPₘ {S' = St'} {M' = M'} _) = ⟪ St' , returnM M' ⟫
  target (OP-STEPₘ {op = op} {S = St} {V = V} {M = M}) =
    ⟪ grade-pass St (mapᵉ (op-grade op))
    , mon-op-sem op V >>= (λ V' → returnM (M [ Hd ↦ V' ]c)) ⟫

  -- The operational reduct IS the flattening of those reducts: every
  -- configuration the step can produce has the same state.

  ⟿ₘ-target : ∀ {A ε ε'} {St : 𝕊 []}
            → {M : toCtx St ⊢C⦂ A ‼ ε} → {tcf : T (Config (A ‼ ε'))}
            → (r : ⟨ St , M ⟩ ⟿ₘ tcf)
            → tcf ≡ flatten (target r)
  ⟿ₘ-target (↝-STEPₘ {S' = St'} {M' = M'} _) =
    sym (>>=-apply M' (λ M → returnM (⟨ St' , M ⟩)))
  ⟿ₘ-target (OP-STEPₘ {op = op} {S = St} {V = V} {M = M}) =
    sym
      (trans
        (>>=-assoc (mon-op-sem op V)
                   (λ V' → returnM (M [ Hd ↦ V' ]c))
                   (λ M' → returnM (⟨ grade-pass St (mapᵉ (op-grade op)) , M' ⟩)))
        (cong (mon-op-sem op V >>=_)
              (fun-ext (λ V' →
                 >>=-apply (M [ Hd ↦ V' ]c)
                           (λ M' → returnM (⟨ grade-pass St (mapᵉ (op-grade op)) , M' ⟩))))))

  -- THE STEP'S GRADE, TRANSITION AND REFINEMENT
  --
  -- As in the pure semantics: `↝-STEPₘ` inherits the ordinary ones, run through
  -- the implementation, and `OP-STEPₘ` costs `op-grade op` and ticks.

  top-gradeₘ : ∀ {A ε ε'} {St : 𝕊 []}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {tcf : T (Config (A ‼ ε'))}
             → ⟨ St , M ⟩ ⟿ₘ tcf → E
  top-gradeₘ (↝-STEPₘ r)         = step-grade r
  top-gradeₘ (OP-STEPₘ {op = op}) = op-grade op ·ₑ uₑ

  top-stepᵏₘ : ∀ {A ε ε'} {St : 𝕊 []}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {tcf : T (Config (A ‼ ε'))}
             → (r : ⟨ St , M ⟩ ⟿ₘ tcf)
             → ⟦ hist St ⟧ᶜᵗˣ
             →ᵐ Tᵏ ⟦ hist (MConfig.state (target r)) ⟧ᶜᵗˣ (top-gradeₘ r)
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

    -- The operation's parameter, and the runtime computation its
    -- implementation returns, as morphisms (with the ground-type coercions the
    -- interpretation carries).

    paramᵐ : (op : Op) → (St : 𝕊 [])
           → toCtx St ⊢V⦂ type-of-gtype (param op)
           → ⟦ toCtx St ⟧ᶜᵗˣ →ᵐ ⟦ param op ⟧ᵍ
    paramᵐ op St V =
      subst (λ O → ⟦ toCtx St ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) ⟦ V ⟧ᵛᵗ

    arityᵐ : (op : Op) → (St : 𝕊 [])
           → (V : toCtx St ⊢V⦂ type-of-gtype (param op))
           → ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ toCtx St ⟧ᶜᵗˣ →ᵐ Mᵒ ⟦ arity op ⟧ᵍ
    arityᵐ op St V =
      subst (λ O → ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ toCtx St ⟧ᶜᵗˣ →ᵐ Mᵒ O)
            (ty-gty (arity op)) ⟦ mon-op-sem op V ⟧ᵛᵐ

    -- The theorem's only condition: the syntactic implementation `mon-op-sem`
    -- is the semantic one, `op-semᵐ`. As `op-semᵐ` is a single morphism, not
    -- indexed by the state, this also forces `mon-op-sem` to be uniform in the
    -- state.

    MOpSemCoherent : Set
    MOpSemCoherent = ∀ (op : Op) → (St : 𝕊 [])
                   → (V : toCtx St ⊢V⦂ type-of-gtype (param op))
                   → arityᵐ op St V
                   ≈ᵐ op-semᵐ op ∘ᵐ ⟨ mapᵉ (op-grade op) ⟩ᶠ (paramᵐ op St V)

    module _ (op-coh : MOpSemCoherent) where

      -- THE TOP-LEVEL DENOTATIONS
      --
      -- A configuration denotes as in the pure semantics. A `T`-computation of
      -- configurations denotes by running its `Mᵒ`-counterpart into the tick
      -- monad's algebra.

      ⟦_⟧ᵏᶜᶠ : ∀ {A ε} → (cf : Config (A ‼ ε))
             → ⟦ hist (Config.state cf) ⟧ᶜᵗˣ →ᵐ Tᵏ ⟦ A ⟧ᵛ ε
      ⟦ cf ⟧ᵏᶜᶠ = implᵐ ∘ᵐ ⟦ cf ⟧ᶜᶠ

      ⟦_⟧ᵐᶜᶠ : ∀ {A ε} → (mcf : MConfig (A ‼ ε))
             → ⟦ hist (MConfig.state mcf) ⟧ᶜᵗˣ →ᵐ Tᵏ ⟦ A ⟧ᵛ ε
      ⟦ ⟪ St , t ⟫ ⟧ᵐᶜᶠ = algᴹ ∘ᵐ Mᶠ implᵐ ∘ᵐ ⟦ t ⟧ᶜᵐ ∘ᵐ ⟦ St ⟧ˢ

      -- A returned configuration denotes as that configuration: the algebra
      -- swallows the runtime monad's unit.

      ⟦⟧ᵐᶜᶠ-return : ∀ {A ε} → (St : 𝕊 []) → (M : toCtx St ⊢C⦂ A ‼ ε)
                   → ⟦ ⟪ St , returnM M ⟫ ⟧ᵐᶜᶠ ≈ᵐ ⟦ ⟨ St , M ⟩ ⟧ᵏᶜᶠ
      ⟦⟧ᵐᶜᶠ-return St M =
          ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (⟦⟧ᶜᵐ-return M)))
        ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
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
                                ⟦ target (OP-STEPₘ {op = op} {S = St}
                                                   {V = V} {M = M}) ⟧ᵐᶜᶠ
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
        -- and what is boxed is the reduct
        ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ cont))
        -- what is left is a tick, and `tick-nf` says the target is its bind
        ∙ᵏ ≈ᵐ-sym (∘ᵐ-congʳ (tick-nf d η⊣ ⟦ mcf ⟧ᵐᶜᶠ) ∙ᵏ coe)
        where
          d = op-grade op

          mcf : MConfig (A ‼ ε)
          mcf = target (OP-STEPₘ {op = op} {S = St} {V = V} {M = M})

          k : (⟨ mapᵉ d ⟩ᵒ ⟦ toCtx St ⟧ᶜᵗˣ ×ᵐ ⟦ arity op ⟧ᵍ) →ᵐ Tᵒ ⟦ A ⟧ᵛ ε
          k = subst (λ O → (⟨ mapᵉ d ⟩ᵒ ⟦ toCtx St ⟧ᶜᵗˣ ×ᵐ O) →ᵐ Tᵒ ⟦ A ⟧ᵛ ε)
                    (ty-gty (arity op)) ⟦ M ⟧ᶜᵗ

          -- the operation's continuation, run under the runtime computation the
          -- implementation returns, IS the reduct
          cont : (algᴹ
                  ∘ᵐ Mᶠ (implᵐ ∘ᵐ k)
                  ∘ᵐ strᴹ
                  ∘ᵐ ⟨ idᵐ , op-semᵐ op ∘ᵐ ⟨ mapᵉ d ⟩ᶠ (paramᵐ op St V) ⟩ᵐ)
                 ∘ᵐ ⟨ mapᵉ d ⟩ᶠ ⟦ St ⟧ˢ
               ≈ᵐ ⟦ mcf ⟧ᵐᶜᶠ
          cont =
              ∘ᵐ-congˡ
                (  ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
                     (⟨ ≈ᵐ-refl , ≈ᵐ-sym (op-coh op St V) ⟩ᵐ-cong)))
                 ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (Mᶠ-∘ᵐ implᵐ k))
                 ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
                 ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ
                     (substᴹ-str (ty-gty (arity op)) ⟦ M ⟧ᶜᵗ
                                 ⟦ mon-op-sem op V ⟧ᵛᵐ))
                 ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ
                     (≈ᵐ-sym (⟦⟧ᶜᵐ-bind (mon-op-sem op V) M))))
            ∙ᵏ ∘ᵐ-assoc _ _ _
            ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)

          -- the coercions collapse: the source's grade is reached exactly
          coe : T-≤ᵏ (top-≾ₘ (OP-STEPₘ {op = op} {S = St} {V = V} {M = M}))
                  ∘ᵐ (T-≤ᵏ (tick-z d ε)
                      ∘ᵐ tickᵏ d ∘ᵐ [ mapᵉ d ]ᶠ ⟦ mcf ⟧ᵐᶜᶠ ∘ᵐ η⊣)
              ≈ᵐ tickᵏ d ∘ᵐ [ mapᵉ d ]ᶠ ⟦ mcf ⟧ᵐᶜᶠ ∘ᵐ η⊣
          coe =
              ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
            ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-trans _ _ (≾ₑ-reflexive {d ·ₑ ε} refl))
            ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-refl _)
            ∙ᵏ ∘ᵐ-identityˡ _

      -- SOUNDNESS OF A MONADIC TOP-LEVEL STEP
      --
      -- `↝-STEPₘ` is `↝-sound` carried along the monad morphism `implᵐ`.

      ⟿ₘ-sound : ∀ {A ε ε'} {St : 𝕊 []}
                → {M : toCtx St ⊢C⦂ A ‼ ε} → {tcf : T (Config (A ‼ ε'))}
                → (r : ⟨ St , M ⟩ ⟿ₘ tcf)
                → Uniform⟿ₘ r
                → ⟦ ⟨ St , M ⟩ ⟧ᵏᶜᶠ
                ≈ᵐ T-≤ᵏ (top-≾ₘ r)
                   ∘ᵐ _⋄ᵏ_ {⟦ hist St ⟧ᶜᵗˣ}
                           {⟦ hist (MConfig.state (target r)) ⟧ᶜᵗˣ}
                           {⟦ A ⟧ᵛ} {top-gradeₘ r} {ε'}
                           ⟦ target r ⟧ᵐᶜᶠ (top-stepᵏₘ r)
      ⟿ₘ-sound (↝-STEPₘ {S' = St'} {M' = M'} r) u =
          ∘ᵐ-congʳ (↝-sound r u)
        ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
        ∙ᵏ ∘ᵐ-congˡ (implᵐ-T-≤ (step-≾ r))
        ∙ᵏ ∘ᵐ-assoc _ _ _
        ∙ᵏ ∘ᵐ-congʳ (impl-⋄ ⟦ ⟨ St' , M' ⟩ ⟧ᶜᶠ (stepᵀ r))
        ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
             (Tᵏ-congᶠ (≈ᵐ-sym (⟦⟧ᵐᶜᶠ-return St' M')))))
      ⟿ₘ-sound (OP-STEPₘ {op = op} {S = St} {V = V} {M = M}) _ =
        sound-OP-STEPₘ op St V M
