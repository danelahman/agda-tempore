------------------------------------------------------------------------
-- Soundness of the PURE top-level operational semantics.                --
--                                                                    --
-- The top-level semantics runs a program against *external implementa-  --
-- tions* of the algebraic operations (`op-sem`). It has two rules: an    --
-- ordinary step `↝-STEP`, and `OP-STEP`, which performs an operation by  --
-- running its implementation:                                           --
--                                                                    --
--   ⟨ S , perform op V M ⟩ ⟿ ⟨ S ⟨ mapᵉ (op-grade op) ⟩ₛ                --
--                            , M [ Hd ↦ op-sem op V ]c ⟩                --
--                                                                    --
-- Note the state gains a lock: performing an operation takes            --
-- `mapᵉ (op-grade op)` worth of time. So — unlike every rule of `_↝_`    --
-- but `DELAY` — the transition is not `ηᵀ`; it is the operation itself,  --
-- `opᵀ op`, with a continuation that hands back the (now locked) history.--
--                                                                    --
-- THE COHERENCE CONDITION                                              --
--                                                                    --
-- In the model an operation is *uninterpreted* — `opᵀ op` is a free      --
-- node, and it hands its continuation an arbitrary arity value at the    --
-- later world. The top-level machine instead hands it `op-sem op V`. So  --
-- the two agree only in a model that *implements* the operations the way --
-- `op-sem` does, and that is exactly what `OpSemSound` below assumes. It --
-- is not derivable, and should not be: it is the statement that the      --
-- denotational and the external implementations of the operations are    --
-- the same one.                                                        --
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

module DenotationalSemantics.Soundness.TopLevelPure
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

open import Data.Unit using (⊤; tt)

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.Substitutions S

open import OperationalSemantics.State                S
open import OperationalSemantics.PreservationTheorem  S
open import OperationalSemantics.TopLevelOpSemantics  S
open import OperationalSemantics.TopLevelPreservationTheorem S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-congᶠ; []-∘ᵐ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ)
open Adjunction Adj using (η⊣; η⊣-nat)
open GroundTypes GTy using (⟦_⟧ᵍ)
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst GTy Mon
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.State S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Soundness.Preservation S Cat Fut Pst Adj GTy Mon GE

module PureTopLevelSoundness (OpSemantics : TopLevelOpSemantics) where

  open TopLevelOpSemantics OpSemantics
  open PureTopLevelPreservationTheorem OpSemantics

  -- The operation's parameter, and the arity value its implementation returns,
  -- as morphisms (with the ground-type coercions the interpretation carries).

  paramᵐ : (op : Op) → (St : 𝕊 [])
         → toCtx St ⊢V⦂ type-of-gtype (param op)
         → ⟦ toCtx St ⟧ᶜᵗˣ →ᵐ ⟦ param op ⟧ᵍ
  paramᵐ op St V = subst (λ O → ⟦ toCtx St ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) ⟦ V ⟧ᵛᵗ

  arityᵐ : (op : Op) → (St : 𝕊 [])
         → (V : toCtx St ⊢V⦂ type-of-gtype (param op))
         → ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ toCtx St ⟧ᶜᵗˣ →ᵐ ⟦ arity op ⟧ᵍ
  arityᵐ op St V =
    subst (λ O → ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ toCtx St ⟧ᶜᵗˣ →ᵐ O)
          (ty-gty (arity op)) ⟦ op-sem op V ⟧ᵛᵗ

  -- THE COHERENCE CONDITION
  --
  -- The model implements the operations the way `op-sem` does: the arity value
  -- `opᵀ op` hands its continuation is the one `op-sem op V` computes. Stated as
  -- a permission to replace the continuation's arity argument, which is how it
  -- is used. (The continuation may still read the past environment — that is the
  -- `fstᵐ` — so this says nothing about what the continuation does with it.)

  OpSemSound : Set₁
  OpSemSound = ∀ (op : Op) → (St : 𝕊 []) → ∀ {A ε}
             → (V : toCtx St ⊢V⦂ type-of-gtype (param op))
             → (k : (⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ toCtx St ⟧ᶜᵗˣ ×ᵐ ⟦ arity op ⟧ᵍ)
                    →ᵐ Tᵒ A ε)
             → opᵀ op ∘ᵐ ⟨ paramᵐ op St V
                         , [ mapᵉ (op-grade op) ]ᶠ (curryᵐ k) ∘ᵐ η⊣ ⟩ᵐ
             ≈ᵐ opᵀ op ∘ᵐ ⟨ paramᵐ op St V
                          , [ mapᵉ (op-grade op) ]ᶠ
                              (curryᵐ (k ∘ᵐ ⟨ fstᵐ , arityᵐ op St V ∘ᵐ fstᵐ ⟩ᵐ))
                            ∘ᵐ η⊣ ⟩ᵐ

  module _ (op-sound : OpSemSound) where

    -- THE TOP-LEVEL STEP'S GRADE, TRANSITION AND REFINEMENT
    --
    -- `↝-STEP` inherits them. `OP-STEP` performs the operation: it spends
    -- `op-grade op`, and its transition is `opᵀ op` itself, with a continuation
    -- that discards the arity value and returns the history — now behind the
    -- lock that the elapsed `mapᵉ (op-grade op)` has placed on it.

    top-grade : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
              → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
              → ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩ → E
    top-grade (↝-STEP r)          = step-grade r
    top-grade (OP-STEP {op = op}) = op-grade op ·ₑ uₑ

    top-stepᵀ : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
              → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
              → (r : ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩)
              → ⟦ hist St ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ hist St' ⟧ᶜᵗˣ (top-grade r)
    top-stepᵀ (↝-STEP r) = stepᵀ r
    top-stepᵀ (OP-STEP {op = op} {S = St} {V = V}) =
      opᵀ op ∘ᵐ ⟨ paramᵐ op St V ∘ᵐ ⟦ St ⟧ˢ
                , [ mapᵉ (op-grade op) ]ᶠ (curryᵐ (ηᵀ ∘ᵐ fstᵐ)) ∘ᵐ η⊣ ⟩ᵐ

    top-≾ : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
          → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
          → (r : ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩)
          → top-grade r ·ₑ ε' ≾ₑ ε
    top-≾ (↝-STEP r) = step-≾ r
    top-≾ (OP-STEP {ε = ε} {op = op}) =
      ≾ₑ-reflexive (cong (_·ₑ ε) (·ₑ-identityʳ (op-grade op)))

    -- Handlers reached by the underlying steps must be uniform, as before.

    Uniform⟿ : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
             → ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩ → Set
    Uniform⟿ (↝-STEP r) = Uniform↝ r
    Uniform⟿ OP-STEP    = ⊤

    -- SUBSTITUTING THE IMPLEMENTATION'S VALUE
    --
    -- The ground-type coercions the interpretation puts on the arity cancel
    -- against the ones it puts on the substituted value.

    substᵈ-⟨⟩ : ∀ {Z W Y Y'} → (e : Y ≡ Y') → (f : (Z ×ᵐ Y) →ᵐ W) → (g : Z →ᵐ Y)
              → subst (λ O → (Z ×ᵐ O) →ᵐ W) e f
                  ∘ᵐ ⟨ idᵐ , subst (λ O → Z →ᵐ O) e g ⟩ᵐ
              ≈ᵐ f ∘ᵐ ⟨ idᵐ , g ⟩ᵐ
    substᵈ-⟨⟩ refl f g = ≈ᵐ-refl

    -- Transporting the operation's residual grade commutes with the operation
    -- (both sides are the same node, at propositionally equal grades).

    opᵀ-ε-subst : ∀ {A ε ε'} → (op : Op) → (e : ε ≡ ε')
                → opᵀ {A} {ε'} op
                    ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (ε-substᵀ e)))
                ≈ᵐ ε-substᵀ (cong (op-grade op ·ₑ_) e) ∘ᵐ opᵀ {A} {ε} op
    opᵀ-ε-subst op refl =
        ∘ᵐ-congʳ (mapˣᵐ-cong ≈ᵐ-refl
                    ([]-congᶠ (map⇒ᵐ-cong-ε ∙ map⇒ᵐ-idᵐ) ∙ []-idᵐ'))
      ∙ ∘ᵐ-congʳ mapˣᵐ-idᵐ
      ∙ ∘ᵐ-identityʳ _
      ∙ ≈ᵐ-sym (∘ᵐ-congˡ ε-substᵀ-refl ∙ ∘ᵐ-identityˡ _)
      where
        map⇒ᵐ-cong-ε : ∀ {X Y Z} → map⇒ᵐ (idᵐ {X}) (ε-substᵀ {Y} {Z} refl)
                                 ≈ᵐ map⇒ᵐ idᵐ idᵐ
        map⇒ᵐ-cong-ε = curryᵐ-cong (∘ᵐ-congˡ ε-substᵀ-refl)

        []-idᵐ' : ∀ {ρ X} → [ ρ ]ᶠ (idᵐ {X}) ≈ᵐ idᵐ
        []-idᵐ' = Future.[]-idᵐ Fut

    -- OP-STEP
    --
    -- Both sides are the operation, applied to the parameter, with the rest of
    -- the computation as its (boxed) continuation. On the left the continuation
    -- is `M` — which reads the arity value. On the right the operation's arity
    -- value has already been substituted away, and the transition's continuation
    -- merely returns the locked history; `opᵀ-nat` and `opᵀ-algebraicity` push
    -- the bind back inside, and the two continuations then agree — *because* the
    -- coherence condition says the value the operation supplies is `op-sem`'s.

    sound-OP-STEP : ∀ {A ε} → (op : Op) → (St : 𝕊 [])
                  → (V : toCtx St ⊢V⦂ type-of-gtype (param op))
                  → (M : toCtx St ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                         ⊢C⦂ A ‼ ε)
                  → ⟦ ⟨ St , perform op V M ⟩ ⟧ᶜᶠ
                  ≈ᵐ T-≤ (top-≾ (OP-STEP {op = op} {S = St} {V = V} {M = M}))
                     ∘ᵐ _⋄_ {⟦ hist St ⟧ᶜᵗˣ} {⟦ hist St ⟨ mapᵉ (op-grade op) ⟩ ⟧ᶜᵗˣ}
                            {⟦ A ⟧ᵛ} {op-grade op ·ₑ uₑ} {ε}
                            ⟦ ⟨ grade-pass St (mapᵉ (op-grade op))
                              , M [ Hd ↦ op-sem op V ]c ⟩ ⟧ᶜᶠ
                            (top-stepᵀ (OP-STEP {op = op} {S = St} {V = V} {M = M}))
    sound-OP-STEP {A} {ε} op St V M =
      -- THE COHERENCE CONDITION: the operation supplies `op-sem`'s value
        ∘ᵐ-congˡ (op-sound op St V _)
      -- so the continuation is the reduct, weakened past the arity value
      ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong cont)) ⟩ᵐ-cong))
      -- push the state's environment inside the operation
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
      ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , env ⟩ᵐ-cong)
      -- and the target is the same operation, with the bind pushed into it
      ∙ ≈ᵐ-sym (∘ᵐ-congʳ tgt ∙ coe)
      where
        d = op-grade op

        -- the reduct, in the new state's environment
        g : ⟦ hist St ⟨ mapᵉ d ⟩ ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ A ⟧ᵛ ε
        g = ⟦ M [ Hd ↦ op-sem op V ]c ⟧ᶜᵗ ∘ᵐ ⟨ mapᵉ d ⟩ᶠ ⟦ St ⟧ˢ

        -- the operation's continuation, with the implementation's value plugged
        -- in, no longer reads the arity: it is the reduct, weakened
        cont : subst (λ O → (⟨ mapᵉ d ⟩ᵒ ⟦ toCtx St ⟧ᶜᵗˣ ×ᵐ O) →ᵐ Tᵒ ⟦ A ⟧ᵛ ε)
                     (ty-gty (arity op)) ⟦ M ⟧ᶜᵗ
                 ∘ᵐ ⟨ fstᵐ , arityᵐ op St V ∘ᵐ fstᵐ ⟩ᵐ
             ≈ᵐ ⟦ M [ Hd ↦ op-sem op V ]c ⟧ᶜᵗ ∘ᵐ fstᵐ
        cont =
            ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙ ∘ᵐ-congˡ (substᵈ-⟨⟩ (ty-gty (arity op)) ⟦ M ⟧ᶜᵗ ⟦ op-sem op V ⟧ᵛᵗ)
          ∙ ∘ᵐ-congˡ (≈ᵐ-sym (C-subst-nat M Hd (op-sem op V)))

        -- the environment goes under the operation's box, by `η⊣`-naturality
        env : ([ mapᵉ d ]ᶠ (curryᵐ (⟦ M [ Hd ↦ op-sem op V ]c ⟧ᶜᵗ ∘ᵐ fstᵐ)) ∘ᵐ η⊣)
                ∘ᵐ ⟦ St ⟧ˢ
            ≈ᵐ [ mapᵉ d ]ᶠ (curryᵐ (g ∘ᵐ fstᵐ)) ∘ᵐ η⊣
        env =
            ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat ⟦ St ⟧ˢ))
          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
          ∙ ∘ᵐ-congˡ ([]-congᶠ
              (  ≈ᵐ-sym (curryᵐ-nat _ _)
               ∙ curryᵐ-cong
                   (  ∘ᵐ-assoc _ _ _
                    ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                    ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _))))

        -- the target: bind the reduct after the transition. `opᵀ` is natural and
        -- algebraic, so the bind goes into the continuation, where the
        -- transition's `ηᵀ` absorbs it — leaving the reduct, and a regrading.
        tgt : _⋄_ {⟦ hist St ⟧ᶜᵗˣ} {⟦ hist St ⟨ mapᵉ d ⟩ ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ}
                  {d ·ₑ uₑ} {ε} g
                  (opᵀ op ∘ᵐ ⟨ paramᵐ op St V ∘ᵐ ⟦ St ⟧ˢ
                             , [ mapᵉ d ]ᶠ (curryᵐ (ηᵀ ∘ᵐ fstᵐ)) ∘ᵐ η⊣ ⟩ᵐ)
            ≈ᵐ (ε-substᵀ (sym (·ₑ-assoc d uₑ ε))
                ∘ᵐ ε-substᵀ (cong (d ·ₑ_) (sym (·ₑ-identityˡ ε))))
               ∘ᵐ opᵀ op ∘ᵐ ⟨ paramᵐ op St V ∘ᵐ ⟦ St ⟧ˢ
                           , [ mapᵉ d ]ᶠ (curryᵐ (g ∘ᵐ fstᵐ)) ∘ᵐ η⊣ ⟩ᵐ
        tgt =
          -- the bind is natural for the operation …
            ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
          ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (opᵀ-nat op g)))
          ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          -- … and the operation is algebraic for the multiplication
          ∙ ∘ᵐ-congˡ (opᵀ-algebraicity op)
          ∙ ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
          -- collect the two maps on the continuation
          ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
              (  ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)
               ∙ mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
          -- inside the box, the transition's `ηᵀ` is absorbed by the bind
          ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
              , ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
                ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
                ∙ ∘ᵐ-congˡ ([]-congᶠ
                    (  ∘ᵐ-assoc _ _ _
                     ∙ ∘ᵐ-congʳ (map⇒ᵐ-curryᵐ _ _)
                     ∙ map⇒ᵐ-curryᵐ _ _
                     ∙ curryᵐ-cong
                         (  ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                          ∙ ∘ᵐ-congˡ (⋄-ηᵀ g)
                          ∙ ∘ᵐ-assoc _ _ _)
                     ∙ ≈ᵐ-sym (map⇒ᵐ-curryᵐ _ _)))
                ∙ ∘ᵐ-congˡ ([]-∘ᵐ _ _)
                ∙ ∘ᵐ-assoc _ _ _ ⟩ᵐ-cong))
          -- and the regrading floats out of the operation
          ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _
                                        ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))
          ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
          ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (opᵀ-ε-subst op (sym (·ₑ-identityˡ ε))))
          ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

        -- the three coercions the target carries collapse: the source's grade is
        -- reached exactly
        coe : T-≤ (top-≾ (OP-STEP {op = op} {S = St} {V = V} {M = M}))
                ∘ᵐ ((ε-substᵀ (sym (·ₑ-assoc d uₑ ε))
                     ∘ᵐ ε-substᵀ (cong (d ·ₑ_) (sym (·ₑ-identityˡ ε))))
                    ∘ᵐ opᵀ op ∘ᵐ ⟨ paramᵐ op St V ∘ᵐ ⟦ St ⟧ˢ
                                 , [ mapᵉ d ]ᶠ (curryᵐ (g ∘ᵐ fstᵐ)) ∘ᵐ η⊣ ⟩ᵐ)
            ≈ᵐ opᵀ op ∘ᵐ ⟨ paramᵐ op St V ∘ᵐ ⟦ St ⟧ˢ
                         , [ mapᵉ d ]ᶠ (curryᵐ (g ∘ᵐ fstᵐ)) ∘ᵐ η⊣ ⟩ᵐ
        coe =
            ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-≡ _) ∙ ∘ᵐ-congʳ (T-≤-≡ _)))
          ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (T-≤-trans _ _ up))
          ∙ ∘ᵐ-congˡ (T-≤-trans up _ (≾ₑ-reflexive {d ·ₑ ε} refl))
          ∙ ∘ᵐ-congˡ (T-≤-refl _)
          ∙ ∘ᵐ-identityˡ _
          where
            up : d ·ₑ ε ≾ₑ (d ·ₑ uₑ) ·ₑ ε
            up = ≾ₑ-reflexive
                   (trans (cong (d ·ₑ_) (sym (·ₑ-identityˡ ε)))
                          (sym (·ₑ-assoc d uₑ ε)))

    -- SOUNDNESS OF A TOP-LEVEL STEP

    ⟿-sound : ∀ {ε ε' A} {St St' : 𝕊 []}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
             → (r : ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩)
             → Uniform⟿ r
             → ⟦ ⟨ St , M ⟩ ⟧ᶜᶠ
             ≈ᵐ T-≤ (top-≾ r)
                ∘ᵐ _⋄_ {⟦ hist St ⟧ᶜᵗˣ} {⟦ hist St' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ}
                       {top-grade r} {ε'}
                       ⟦ ⟨ St' , M' ⟩ ⟧ᶜᶠ (top-stepᵀ r)
    ⟿-sound (↝-STEP r) u = ↝-sound r u
    ⟿-sound (OP-STEP {op = op} {S = St} {V = V} {M = M}) _ =
      sound-OP-STEP op St V M
