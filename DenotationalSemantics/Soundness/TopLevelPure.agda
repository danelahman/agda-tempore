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
open import Data.Product using (_,_; _×_)

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

  -- SUB-EFFECTING COMMUTES WITH PERFORMING AN OPERATION
  --
  -- The second half of "the model implements the operations". In the free tree
  -- model an `op-node` records the residual grade at the node, so coercing the
  -- continuation's grade and coercing the whole computation give different
  -- trees. In a model that *implements* the operation there is no node to record
  -- anything, and the two coincide. (This is only assumable, not provable, for
  -- the same reason `OpSemSound` is: it is a statement about the operation's
  -- implementation. And it cannot be moved into the model interface — the free
  -- model would have to satisfy it, and making it do so would force the handler
  -- fold to know that clauses are natural in the residual grade, since the fold
  -- selects `h op ε''` *by* that grade.)

  OpTᵀ-≤ : Set₁
  OpTᵀ-≤ = ∀ {A ε₁ ε₂} → (op : Op) → (p : ε₁ ≾ₑ ε₂)
         → opᵀ {A} {ε₂} op
             ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ p)))
         ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ p) ∘ᵐ opᵀ {A} {ε₁} op

  module _ (op-sound : OpSemSound) (op-≤ : OpTᵀ-≤) where

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

    -- BINDING AFTER AN OPERATION
    --
    -- `opᵀ` is natural and algebraic, so a bind after the operation goes into
    -- the operation's continuation — where the transition's `ηᵀ` absorbs it,
    -- leaving the bound computation and a regrading.

    op-bind : ∀ {X A ε} → (op : Op)
            → (pv : X →ᵐ ⟦ param op ⟧ᵍ)
            → (f : ⟨ mapᵉ (op-grade op) ⟩ᵒ X →ᵐ Tᵒ A ε)
            → μᵀ ∘ᵐ Tᶠ f
                ∘ᵐ (opᵀ op ∘ᵐ ⟨ pv
                              , [ mapᵉ (op-grade op) ]ᶠ (curryᵐ (ηᵀ ∘ᵐ fstᵐ))
                                ∘ᵐ η⊣ ⟩ᵐ)
            ≈ᵐ (ε-substᵀ (sym (·ₑ-assoc (op-grade op) uₑ ε))
                ∘ᵐ ε-substᵀ (cong (op-grade op ·ₑ_) (sym (·ₑ-identityˡ ε))))
               ∘ᵐ opᵀ op ∘ᵐ ⟨ pv
                            , [ mapᵉ (op-grade op) ]ᶠ (curryᵐ (f ∘ᵐ fstᵐ)) ∘ᵐ η⊣ ⟩ᵐ
    op-bind {ε = ε} op pv f =
        -- the bind is natural for the operation …
          ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (opᵀ-nat op f)))
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
                        ∙ ∘ᵐ-congˡ (⋄-ηᵀ f)
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
        tgt = op-bind op (paramᵐ op St V ∘ᵐ ⟦ St ⟧ˢ) g

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

    -- THE COERCION ESCAPES A TOP-LEVEL TRANSITION
    --
    -- The multi-step closure substitutes the rest of the run's coercion under
    -- the bind of the first step's transition. For `↝-STEP` this is `T-≤-stepᵀ`
    -- (proved by induction on the underlying step). For `OP-STEP` the transition
    -- performs the operation, and it is `OpTᵀ-≤` that lets the coercion out.

    T-≤-topᵀ : ∀ {ε ε' εa εb A} {St St' : 𝕊 []} → (B : Obj)
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
             → (r : ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩)
             → (g : ⟦ hist St' ⟧ᶜᵗˣ →ᵐ Tᵒ B εa) → (q : εa ≾ₑ εb)
             → μᵀ ∘ᵐ Tᶠ (T-≤ q ∘ᵐ g) ∘ᵐ top-stepᵀ r
             ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ μᵀ ∘ᵐ Tᶠ g ∘ᵐ top-stepᵀ r
    T-≤-topᵀ B (↝-STEP r) g q = T-≤-stepᵀ B r g q
    T-≤-topᵀ {εa = εa} {εb = εb} B
             (OP-STEP {op = op} {S = St} {V = V}) g q =
      -- bind after the operation, on both sides …
        op-bind op (paramᵐ op St V ∘ᵐ ⟦ St ⟧ˢ) (T-≤ q ∘ᵐ g)
      -- … the coercion in the continuation is a map on the operation's box …
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
          , ∘ᵐ-congˡ ([]-congᶠ
              (curryᵐ-cong (∘ᵐ-assoc _ _ _) ∙ ≈ᵐ-sym (map⇒ᵐ-curryᵐ _ _))
              ∙ []-∘ᵐ _ _)
            ∙ ∘ᵐ-assoc _ _ _ ⟩ᵐ-cong))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _
                                    ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))
      -- … so `OpTᵀ-≤` pulls it out of the operation
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (op-≤ op q))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      -- and the coercions collapse to the same one on both sides
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ (∘ᵐ-congˡ (T-≤-≡ _) ∙ ∘ᵐ-congʳ (T-≤-≡ _))
                  ∙ ∘ᵐ-congˡ (T-≤-trans _ _ (wz εb))
                  ∙ T-≤-trans (·ₑ-monoʳ-≾ₑ q) (wz εb) z)
      ∙ ≈ᵐ-sym
          (  ∘ᵐ-congʳ (op-bind op (paramᵐ op St V ∘ᵐ ⟦ St ⟧ˢ) g)
           ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
           ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-≡ _) ∙ ∘ᵐ-congʳ (T-≤-≡ _))
                       ∙ ∘ᵐ-congʳ (T-≤-trans _ _ (wz εa))
                       ∙ T-≤-trans (wz εa) (·ₑ-monoʳ-≾ₑ q) z))
      where
        -- the regrading `op-bind` leaves behind
        wz : (e : E) → op-grade op ·ₑ e ≾ₑ (op-grade op ·ₑ uₑ) ·ₑ e
        wz e = ≾ₑ-reflexive
                 (trans (cong (op-grade op ·ₑ_) (sym (·ₑ-identityˡ e)))
                        (sym (·ₑ-assoc (op-grade op) uₑ e)))

        z : op-grade op ·ₑ εa ≾ₑ (op-grade op ·ₑ uₑ) ·ₑ εb
        z = ≾ₑ-trans (·ₑ-monoʳ-≾ₑ q) (wz εb)

    -- THE MULTI-STEP CLOSURE

    top-steps-grade : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
                    → cf ⟿* cf' → E
    top-steps-grade ε*ᵗ        = uₑ
    top-steps-grade (r ◅ᵗ rs)  = top-grade r ·ₑ top-steps-grade rs

    top-stepsᵀ : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
               → (rs : cf ⟿* cf')
               → ⟦ hist (Config.state cf) ⟧ᶜᵗˣ
               →ᵐ Tᵒ ⟦ hist (Config.state cf') ⟧ᶜᵗˣ (top-steps-grade rs)
    top-stepsᵀ ε*ᵗ        = ηᵀ
    top-stepsᵀ (r ◅ᵗ rs)  = top-stepsᵀ rs ⋄ top-stepᵀ r

    top-steps-≾ : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
                → (rs : cf ⟿* cf') → top-steps-grade rs ·ₑ ε' ≾ₑ ε
    top-steps-≾ {ε = ε} ε*ᵗ = ≾ₑ-reflexive (·ₑ-identityˡ ε)
    top-steps-≾ {ε' = ε'} (_◅ᵗ_ r rs) =
      ≾ₑ-trans (≾ₑ-reflexive (·ₑ-assoc (top-grade r) (top-steps-grade rs) ε'))
      (≾ₑ-trans (·ₑ-monoʳ-≾ₑ (top-steps-≾ rs)) (top-≾ r))

    Uniform⟿* : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
              → cf ⟿* cf' → Set
    Uniform⟿* ε*ᵗ       = ⊤
    Uniform⟿* (r ◅ᵗ rs) = Uniform⟿ r × Uniform⟿* rs

    -- A run of the top-level machine is sound.

    ⟿*-sound : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
              → (rs : cf ⟿* cf') → Uniform⟿* rs
              → ⟦ cf ⟧ᶜᶠ
              ≈ᵐ T-≤ (top-steps-≾ rs)
                 ∘ᵐ _⋄_ {⟦ hist (Config.state cf) ⟧ᶜᵗˣ}
                        {⟦ hist (Config.state cf') ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ}
                        {top-steps-grade rs} {ε'}
                        ⟦ cf' ⟧ᶜᶠ (top-stepsᵀ rs)
    ⟿*-sound {A = A} {ε = ε} {cf = cf} ε*ᵗ _ =
      pure-step-≡ (top-steps-≾ (ε*ᵗ {A} {ε} {cf})) ≈ᵐ-refl
    ⟿*-sound {A = A} {ε' = ε'} (_◅ᵗ_ {ε₂ = ε₂} {cf₃ = cf₃} r rs) (u , us) =
        ⟿-sound r u
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (⟿*-sound rs us))))
      -- the run's coercion escapes the step's bind
      ∙ ∘ᵐ-congʳ (T-≤-topᵀ ⟦ A ⟧ᵛ r (⟦ cf₃ ⟧ᶜᶠ ⋄ top-stepsᵀ rs) (top-steps-≾ rs))
      -- and the two binds re-associate into one
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (bind-bind ⟦ cf₃ ⟧ᶜᶠ (top-stepsᵀ rs) (top-stepᵀ r)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-≡ _)))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-trans _ _ b))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (T-≤-trans b (top-≾ r) (top-steps-≾ (r ◅ᵗ rs)))
      where
        b : top-steps-grade (r ◅ᵗ rs) ·ₑ ε' ≾ₑ top-grade r ·ₑ ε₂
        b = ≾ₑ-trans
              (≾ₑ-reflexive (·ₑ-assoc (top-grade r) (top-steps-grade rs) ε'))
              (·ₑ-monoʳ-≾ₑ (top-steps-≾ rs))

    -- DENOTATIONAL RUNNING, FOR THE TOP-LEVEL MACHINE
    --
    -- As for `_↝_`, the relation is directed, not an equivalence, and reflexive
    -- but not (freely) transitive: transitivity along a run is the induction in
    -- `⟿*-sound`, which needs the coercion to escape each transition's bind.

    infix 4 _⊳ᵗ_

    record _⊳ᵗ_ {A ε ε'} (cf : Config (A ‼ ε)) (cf' : Config (A ‼ ε')) : Set where
      constructor mk⊳ᵗ
      field
        gradeᵗ  : E
        refineᵗ : gradeᵗ ·ₑ ε' ≾ₑ ε
        trᵗ     : ⟦ hist (Config.state cf) ⟧ᶜᵗˣ
                →ᵐ Tᵒ ⟦ hist (Config.state cf') ⟧ᶜᵗˣ gradeᵗ
        soundᵗ  : ⟦ cf ⟧ᶜᶠ
                ≈ᵐ T-≤ refineᵗ
                   ∘ᵐ _⋄_ {⟦ hist (Config.state cf) ⟧ᶜᵗˣ}
                          {⟦ hist (Config.state cf') ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {gradeᵗ} {ε'}
                          ⟦ cf' ⟧ᶜᶠ trᵗ

    ⟿*-⊳ᵗ : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
           → (rs : cf ⟿* cf') → Uniform⟿* rs → cf ⊳ᵗ cf'
    ⟿*-⊳ᵗ rs us =
      mk⊳ᵗ (top-steps-grade rs) (top-steps-≾ rs) (top-stepsᵀ rs) (⟿*-sound rs us)

    -- CLOSED PROGRAMS
    --
    -- A program run to a value by the top-level machine *is* that value
    -- returned, after the run's transition (which now performs the operations
    -- the program requested), at the run's refined grade.

    ⟿*-value : ∀ {A ε} {St' : 𝕊 []}
             → (M : Program A ε)
             → (V : toCtx St' ⊢V⦂ A)
             → (rs : ⟨ ∅ , M ⟩ ⟿* ⟨ St' , return V ⟩)
             → Uniform⟿* rs
             → ⟦ M ⟧ᵖ
             ≈ᵐ T-≤ (top-steps-≾ rs)
                ∘ᵐ _⋄_ {𝟙ᵐ} {⟦ hist St' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {top-steps-grade rs} {uₑ}
                       (ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ St' ⟧ˢ) (top-stepsᵀ rs)
    ⟿*-value M V rs us =
        ≈ᵐ-sym (∘ᵐ-identityʳ _)
      ∙ ⟿*-sound rs us
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (∘ᵐ-assoc _ _ _))))
