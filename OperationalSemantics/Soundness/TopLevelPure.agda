------------------------------------------------------------------------
-- Soundness of the PURE top-level operational semantics.                --
--                                                                    --
-- The top-level machine runs a program against external implementations  --
-- of the algebraic operations (`op-sem`). It has two rules: an ordinary  --
-- step `↝-STEP`, and                                                    --
--                                                                    --
--   OP-STEP : ⟨ S , perform op V M ⟩                                    --
--           ⟿ ⟨ S ⟨ mapᵉ (op-grade op) ⟩ₛ , M [ split-[] ↦ op-sem op V ]c ⟩   --
--                                                                    --
-- which replaces the operation call by the value the implementation      --
-- computes, and locks the state: performing the operation took           --
-- `mapᵉ (op-grade op)` worth of time.                                   --
--                                                                    --
-- Every operation is therefore run, and the top-level denotation lands   --
-- in the tick monad (`Model.TickMonad`), where the only effect is the    --
-- passage of time. It is the tree-monad denotation, composed with the    --
-- implementation `implᵐ : Tᵒ A ε →ᵐ Tᵏ A ε` (`Model.Implementation`):    --
--                                                                    --
--   ⟦ cf ⟧ᵏᶜᶠ  =  implᵐ ∘ᵐ ⟦ cf ⟧ᶜᶠ                                     --
--                                                                    --
-- Operations under a handler are handled by `⟦_⟧ᶜᵗ` in the tree monad,   --
-- `HANDLE-OP` being an `↝-STEP`; `implᵐ` runs the ones surviving to the  --
-- top. The theorem's one condition, `OpSemCoherent`, is that `op-sem` is --
-- the semantic implementation `op-semᵐ`.                                --
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
open import DenotationalSemantics.Model.Implementation

module OperationalSemantics.Soundness.TopLevelPure
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
         (TMon : TickMonad S Cat Fut)
         (Impl : Implementation S Cat Fut Pst Adj GTy Mon TMon)
       where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; _×_; proj₁; proj₂)

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.Substitutions S

open import OperationalSemantics.State                       S
open import OperationalSemantics.PreservationTheorem         S
open import OperationalSemantics.TopLevelOpSemantics         S
open import OperationalSemantics.TopLevelPreservationTheorem S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-congᶠ; []-∘ᵐ; []-≤; []-≤-nat)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ)
open Adjunction Adj using (η⊣; η⊣-nat)
open GroundTypes GTy using (⟦_⟧ᵍ)
open Monad Mon using (Tᵒ; Tᶠ; ηᵀ; μᵀ; T-≤; ε-substᵀ; delayᵀ; opᵀ)
open TickMonad TMon
open Implementation Impl

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.State S Cat Fut Pst Adj GTy Mon GE
open import OperationalSemantics.Soundness.Preservation S Cat Fut Pst Adj GTy Mon GE

open import OperationalSemantics.Soundness.TickLemmas S Cat Fut Pst Adj GTy Mon TMon
open ImplLemmas implᵐ implᵐ-μᵀ implᵐ-nat

module PureTopLevelSoundness (OpSemantics : TopLevelOpSemantics) where

  open TopLevelOpSemantics OpSemantics
  open PureTopLevelPreservationTheorem OpSemantics

  -- The operation's parameter, and the value its implementation returns, as
  -- morphisms (with the ground-type coercions the interpretation carries).

  paramᵐ : (op : Op) → (St : 𝕊 [])
         → (V : toCtx St ⊢V⦂ type-of-gtype (param op)) → Paramᵛ V
         → ⟦ toCtx St ⟧ᶜᵗˣ →ᵐ ⟦ param op ⟧ᵍ
  paramᵐ op St V pV =
    subst (λ O → ⟦ toCtx St ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV)

  arityᵐ : (op : Op) → (St : 𝕊 [])
         → (V : toCtx St ⊢V⦂ type-of-gtype (param op))
         → Paramᵛ (op-sem op V)
         → ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ toCtx St ⟧ᶜᵗˣ →ᵐ ⟦ arity op ⟧ᵍ
  arityᵐ op St V pOp =
    subst (λ O → ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ toCtx St ⟧ᶜᵗˣ →ᵐ O)
          (ty-gty (arity op)) (⟦ op-sem op V ⟧ᵛᵗ pOp)

  -- The theorem's only condition: the syntactic implementation `op-sem` is the
  -- semantic one, `op-semᵐ`. Both take the parameter as seen from
  -- `mapᵉ (op-grade op)` in its future, and return the arity value. As
  -- `op-semᵐ` is a single morphism, not indexed by the state, this also forces
  -- `op-sem` to be uniform in the state.

  -- The implementation's values are parametric. `op-sem` is a parameter of the
  -- theorem, so this is assumed alongside its coherence.

  OpSemParametric : Set
  OpSemParametric = ∀ (op : Op) → (St : 𝕊 [])
                  → (V : toCtx St ⊢V⦂ type-of-gtype (param op))
                  → Paramᵛ (op-sem op V)

  OpSemCoherent : OpSemParametric → Set
  OpSemCoherent op-par = ∀ (op : Op) → (St : 𝕊 [])
                → (V : toCtx St ⊢V⦂ type-of-gtype (param op))
                → (pV : Paramᵛ V)
                → arityᵐ op St V (op-par op St V)
                ≈ᵐ op-semᵐ op ∘ᵐ ⟨ mapᵉ (op-grade op) ⟩ᶠ (paramᵐ op St V pV)

  module _ (op-par : OpSemParametric) (op-coh : OpSemCoherent op-par) where

    -- THE TOP-LEVEL DENOTATION OF A CONFIGURATION

    ⟦_⟧ᵏᶜᶠ : ∀ {A ε} → (cf : Config (A ‼ ε)) → Paramᶜᶠ cf
           → ⟦ hist (Config.state cf) ⟧ᶜᵗˣ →ᵐ Tᵏ ⟦ A ⟧ᵛ ε
    ⟦ cf ⟧ᵏᶜᶠ p = implᵐ ∘ᵐ ⟦ cf ⟧ᶜᶠ p

    -- The certificate across a top-level step: `↝-STEP` inherits the ordinary
    -- one, `OP-STEP` substitutes the implementation's (parametric) value.

    topᴾᶜᶠ : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
           → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
           → (r : ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩)
           → Paramᶜᶠ (⟨ St , M ⟩) → Paramᶜᶠ (⟨ St' , M' ⟩)
    topᴾᶜᶠ (↝-STEP r) p = stepᴾᶜᶠ r p
    topᴾᶜᶠ (OP-STEP {op = op} {S = St} {V = V} {M = M}) (pSt , (pV , pM)) =
      pSt , subᶜ M split-[] (op-sem op V) pM (op-par op St V)

    -- THE TOP-LEVEL STEP'S GRADE, TRANSITION AND REFINEMENT
    --
    -- `↝-STEP` inherits the ordinary ones, run through the implementation.
    -- `OP-STEP` performs the operation: it costs `op-grade op`, and its
    -- transition is a tick.

    top-grade : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
              → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
              → ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩ → E
    top-grade (↝-STEP r)          = step-grade r
    top-grade (OP-STEP {op = op}) = op-grade op ·ₑ uₑ

    top-stepᵏ : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
              → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
              → (r : ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩)
              → ⟦ hist St ⟧ᶜᵗˣ →ᵐ Tᵏ ⟦ hist St' ⟧ᶜᵗˣ (top-grade r)
    top-stepᵏ (↝-STEP r) = implᵐ ∘ᵐ stepᵀ r
    top-stepᵏ (OP-STEP {op = op}) =
      tickᵏ (op-grade op) ∘ᵐ [ mapᵉ (op-grade op) ]ᶠ ηᵏ ∘ᵐ η⊣

    top-≾ : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
          → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
          → (r : ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩)
          → top-grade r ·ₑ ε' ≾ₑ ε
    top-≾ (↝-STEP r) = step-≾ r
    top-≾ (OP-STEP {ε = ε} {op = op}) =
      ≾ₑ-reflexive (cong (_·ₑ ε) (·ₑ-identityʳ (op-grade op)))

    Uniform⟿ : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
             → ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩ → Paramᶜ M → Set
    Uniform⟿ (↝-STEP r) pM = Uniform↝ r pM
    Uniform⟿ OP-STEP    _  = ⊤

    -- The interpretation's ground-type coercions on the arity cancel against
    -- the ones on the substituted value.

    substᵈ-⟨⟩ : ∀ {Z W Y Y'} → (e : Y ≡ Y') → (f : (Z ×ᵐ Y) →ᵐ W) → (g : Z →ᵐ Y)
              → subst (λ O → (Z ×ᵐ O) →ᵐ W) e f
                  ∘ᵐ ⟨ idᵐ , subst (λ O → Z →ᵐ O) e g ⟩ᵐ
              ≈ᵐ f ∘ᵐ ⟨ idᵐ , g ⟩ᵐ
    substᵈ-⟨⟩ refl f g = ≈ᵐ-refl

    -- OP-STEP
    --
    -- The implementation feeds the continuation `op-semᵐ`'s value, which by
    -- `OpSemCoherent` is the value the reduct substitutes, and leaves a tick.

    sound-OP-STEP : ∀ {A ε} → (op : Op) → (St : 𝕊 [])
                  → (V : toCtx St ⊢V⦂ type-of-gtype (param op))
                  → (M : toCtx St ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                         ⊢C⦂ A ‼ ε)
                  → (pSt : Paramˢ St) → (pV : Paramᵛ V) → (pM : Paramᶜ M)
                  → ⟦ ⟨ St , perform op V M ⟩ ⟧ᵏᶜᶠ (pSt , (pV , pM))
                  ≈ᵐ T-≤ᵏ (top-≾ (OP-STEP {op = op} {S = St} {V = V} {M = M}))
                     ∘ᵐ _⋄ᵏ_ {⟦ hist St ⟧ᶜᵗˣ}
                             {⟦ hist St ⟨ mapᵉ (op-grade op) ⟩ ⟧ᶜᵗˣ}
                             {⟦ A ⟧ᵛ} {op-grade op ·ₑ uₑ} {ε}
                             (⟦ ⟨ grade-pass St (mapᵉ (op-grade op))
                                , M [ split-[] ↦ op-sem op V ]c ⟩ ⟧ᵏᶜᶠ
                                (pSt , subᶜ M split-[] (op-sem op V) pM (op-par op St V)))
                             (top-stepᵏ (OP-STEP {op = op} {S = St} {V = V} {M = M}))
    sound-OP-STEP {A} {ε} op St V M pSt pV pM =
      -- run the operation away
        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ᵏ ∘ᵐ-congˡ (implᵐ-opᵀ op (paramᵐ op St V pV) _)
      ∙ᵏ ∘ᵐ-assoc _ _ _
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      -- the value it feeds the continuation is the one the reduct substitutes
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (∘ᵐ-congʳ cont)))
      -- and the state's environment goes under the tick's box
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat (⟦ St ⟧ˢ pSt))))
      ∙ᵏ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (∘ᵐ-assoc _ _ _)))
      -- what is left is a tick, and `tick-nf` says the target is its bind
      ∙ᵏ ≈ᵐ-sym (∘ᵐ-congʳ (tick-nf (op-grade op) η⊣ (⟦ cf' ⟧ᵏᶜᶠ pcf')) ∙ᵏ coe)
      where
        d = op-grade op

        cf' : Config (A ‼ ε)
        cf' = ⟨ grade-pass St (mapᵉ d) , M [ split-[] ↦ op-sem op V ]c ⟩

        pcf' : Paramᶜᶠ cf'
        pcf' = pSt , subᶜ M split-[] (op-sem op V) pM (op-par op St V)

        -- the operation's continuation, fed `op-semᵐ`'s value, IS the reduct
        cont : subst (λ O → (⟨ mapᵉ d ⟩ᵒ ⟦ toCtx St ⟧ᶜᵗˣ ×ᵐ O) →ᵐ Tᵒ ⟦ A ⟧ᵛ ε)
                     (ty-gty (arity op)) (⟦ M ⟧ᶜᵗ pM)
                 ∘ᵐ ⟨ idᵐ , op-semᵐ op ∘ᵐ ⟨ mapᵉ d ⟩ᶠ (paramᵐ op St V pV) ⟩ᵐ
             ≈ᵐ ⟦ M [ split-[] ↦ op-sem op V ]c ⟧ᶜᵗ
                  (subᶜ M split-[] (op-sem op V) pM (op-par op St V))
        cont =
            ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ≈ᵐ-sym (op-coh op St V pV) ⟩ᵐ-cong)
          ∙ᵏ substᵈ-⟨⟩ (ty-gty (arity op)) (⟦ M ⟧ᶜᵗ pM)
               (⟦ op-sem op V ⟧ᵛᵗ (op-par op St V))
          ∙ᵏ ≈ᵐ-sym (C-subst-nat M split-[] (op-sem op V) pM (op-par op St V))

        -- the coercions collapse: the source's grade is reached exactly
        coe : T-≤ᵏ (top-≾ (OP-STEP {op = op} {S = St} {V = V} {M = M}))
                ∘ᵐ (T-≤ᵏ (tick-z d ε)
                    ∘ᵐ tickᵏ d ∘ᵐ [ mapᵉ d ]ᶠ (⟦ cf' ⟧ᵏᶜᶠ pcf') ∘ᵐ η⊣)
            ≈ᵐ tickᵏ d ∘ᵐ [ mapᵉ d ]ᶠ (⟦ cf' ⟧ᵏᶜᶠ pcf') ∘ᵐ η⊣
        coe =
            ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-trans _ _ (≾ₑ-reflexive {d ·ₑ ε} refl))
          ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-refl _)
          ∙ᵏ ∘ᵐ-identityˡ _

    -- SOUNDNESS OF A TOP-LEVEL STEP
    --
    -- `↝-STEP` is `↝-sound` carried along the monad morphism `implᵐ`.

    ⟿-sound : ∀ {ε ε' A} {St St' : 𝕊 []}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
             → (r : ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩)
             → (p : Paramᶜᶠ (⟨ St , M ⟩))
             → Uniform⟿ r (proj₂ p)
             → ⟦ ⟨ St , M ⟩ ⟧ᵏᶜᶠ p
             ≈ᵐ T-≤ᵏ (top-≾ r)
                ∘ᵐ _⋄ᵏ_ {⟦ hist St ⟧ᶜᵗˣ} {⟦ hist St' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ}
                        {top-grade r} {ε'}
                        (⟦ ⟨ St' , M' ⟩ ⟧ᵏᶜᶠ (topᴾᶜᶠ r p)) (top-stepᵏ r)
    ⟿-sound (↝-STEP {S' = St'} {N = M'} r) (pSt , pM) u =
        ∘ᵐ-congʳ (↝-sound r pSt pM u)
      ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ᵏ ∘ᵐ-congˡ (implᵐ-T-≤ (step-≾ r))
      ∙ᵏ ∘ᵐ-assoc _ _ _
      ∙ᵏ ∘ᵐ-congʳ (impl-⋄ (⟦ ⟨ St' , M' ⟩ ⟧ᶜᶠ (stepᴾᶜᶠ r (pSt , pM))) (stepᵀ r))
    ⟿-sound (OP-STEP {op = op} {S = St} {V = V} {M = M}) (pSt , (pV , pM)) _ =
      sound-OP-STEP op St V M pSt pV pM

    -- THE COERCION ESCAPES A TOP-LEVEL TRANSITION
    --
    -- Every top-level transition is built from `ηᵏ` and ticks, and a tick
    -- records nothing, so `tickᵏ-≤` lets a coercion through it.

    ηᵏ-case : ∀ {X B εa εb} → (g : X →ᵐ Tᵏ B εa) → (q : εa ≾ₑ εb)
            → μᵏ ∘ᵐ Tᵏᶠ (T-≤ᵏ q ∘ᵐ g) ∘ᵐ ηᵏ
            ≈ᵐ T-≤ᵏ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ μᵏ ∘ᵐ Tᵏᶠ g ∘ᵐ ηᵏ
    ηᵏ-case {εa = εa} {εb = εb} g q =
        ⋄ᵏ-ηᵏ (T-≤ᵏ q ∘ᵐ g)
      ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-≡ _)
      ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-trans q _ w)
      ∙ᵏ ≈ᵐ-sym
          (  ∘ᵐ-congʳ (⋄ᵏ-ηᵏ g ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-≡ _))
           ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
           ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-trans _ _ w))
      where
        w : εa ≾ₑ uₑ ·ₑ εb
        w = ≾ₑ-trans q (≾ₑ-reflexive (sym (·ₑ-identityˡ εb)))

    tick-case : ∀ {X Y B εa εb} → (δ : E) → (env : X →ᵐ [ mapᵉ δ ]ᵒ Y)
              → (g : Y →ᵐ Tᵏ B εa) → (q : εa ≾ₑ εb)
              → μᵏ ∘ᵐ Tᵏᶠ (T-≤ᵏ q ∘ᵐ g) ∘ᵐ (tickᵏ δ ∘ᵐ [ mapᵉ δ ]ᶠ ηᵏ ∘ᵐ env)
              ≈ᵐ T-≤ᵏ (·ₑ-monoʳ-≾ₑ q)
                 ∘ᵐ μᵏ ∘ᵐ Tᵏᶠ g ∘ᵐ (tickᵏ δ ∘ᵐ [ mapᵉ δ ]ᶠ ηᵏ ∘ᵐ env)
    tick-case {εa = εa} {εb = εb} δ env g q =
        tick-nf δ env (T-≤ᵏ q ∘ᵐ g)
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-∘ᵐ _ _)))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙ᵏ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (tickᵏ-≤ δ q))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-trans (·ₑ-monoʳ-≾ₑ q) (tick-z δ εb) z)
      ∙ᵏ ≈ᵐ-sym
          (  ∘ᵐ-congʳ (tick-nf δ env g)
           ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
           ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-trans (tick-z δ εa) (·ₑ-monoʳ-≾ₑ q) z))
      where
        z : δ ·ₑ εa ≾ₑ (δ ·ₑ uₑ) ·ₑ εb
        z = ≾ₑ-trans (·ₑ-monoʳ-≾ₑ q) (tick-z δ εb)

    -- the nine `ηᵀ` rules, with the implementation applied
    ηᵀ-step : ∀ {X B εa εb} → (g : X →ᵐ Tᵏ B εa) → (q : εa ≾ₑ εb)
            → μᵏ ∘ᵐ Tᵏᶠ (T-≤ᵏ q ∘ᵐ g) ∘ᵐ (implᵐ ∘ᵐ ηᵀ)
            ≈ᵐ T-≤ᵏ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ μᵏ ∘ᵐ Tᵏᶠ g ∘ᵐ (implᵐ ∘ᵐ ηᵀ)
    ηᵀ-step g q =
        ∘ᵐ-congʳ (∘ᵐ-congʳ implᵐ-ηᵀ)
      ∙ᵏ ηᵏ-case g q
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym implᵐ-ηᵀ)))

    -- `DELAY`'s transition, implemented: a tick
    delay-tick : ∀ {X} → (τ : ℕ)
               → implᵐ ∘ᵐ (delayᵀ {⟨ of-natʳ τ ⟩ᵒ X} {uₑ} τ
                           ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣ {X} {of-natʳ τ})
               ≈ᵐ tickᵏ (of-natᵉ τ)
                  ∘ᵐ [ mapᵉ (of-natᵉ τ) ]ᶠ ηᵏ
                  ∘ᵐ ([]-≤ (≾ᵣ-reflexive map-of-natᵉ) ∘ᵐ η⊣)
    delay-tick τ =
        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ᵏ ∘ᵐ-congˡ (implᵐ-delayᵀ τ)
      ∙ᵏ ∘ᵐ-assoc _ _ _
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _) ∙ᵏ []-congᶠ implᵐ-ηᵀ)))
      ∙ᵏ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-≤-nat ηᵏ _)))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)

    -- The implementation of an ordinary step's transition: `ηᵀ` becomes `ηᵏ`,
    -- and `DELAY`'s delay becomes a tick.

    T-≤ᵏ-implstep : ∀ {ε ε' εa εb A} {St St' : 𝕊 []} → (B : Obj)
                  → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
                  → (r : ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩)
                  → (g : ⟦ hist St' ⟧ᶜᵗˣ →ᵐ Tᵏ B εa) → (q : εa ≾ₑ εb)
                  → μᵏ ∘ᵐ Tᵏᶠ (T-≤ᵏ q ∘ᵐ g) ∘ᵐ (implᵐ ∘ᵐ stepᵀ r)
                  ≈ᵐ T-≤ᵏ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ μᵏ ∘ᵐ Tᵏᶠ g ∘ᵐ (implᵐ ∘ᵐ stepᵀ r)
    T-≤ᵏ-implstep B APP        g q = ηᵀ-step g q
    T-≤ᵏ-implstep B MATCH      g q = ηᵀ-step g q
    T-≤ᵏ-implstep B SEQ-RET    g q = ηᵀ-step g q
    T-≤ᵏ-implstep B SEQ-OP     g q = ηᵀ-step g q
    T-≤ᵏ-implstep B HANDLE-RET g q = ηᵀ-step g q
    T-≤ᵏ-implstep B HANDLE-OP  g q = ηᵀ-step g q
    T-≤ᵏ-implstep B BOX        g q = ηᵀ-step g q
    T-≤ᵏ-implstep B UNBOX      g q = ηᵀ-step g q
    T-≤ᵏ-implstep B COERCE     g q = ηᵀ-step g q
    T-≤ᵏ-implstep B (SEQ-STEP r _)    g q = T-≤ᵏ-implstep B r g q
    T-≤ᵏ-implstep B (HANDLE-STEP r _) g q = T-≤ᵏ-implstep B r g q
    T-≤ᵏ-implstep B (DELAY {τ = τ}) g q =
        ∘ᵐ-congʳ (∘ᵐ-congʳ (delay-tick τ))
      ∙ᵏ tick-case (of-natᵉ τ) _ g q
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (delay-tick τ))))


    -- The coercion escapes any top-level transition.

    T-≤ᵏ-topᵏ : ∀ {ε ε' εa εb A} {St St' : 𝕊 []} → (B : Obj)
              → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
              → (r : ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩)
              → (g : ⟦ hist St' ⟧ᶜᵗˣ →ᵐ Tᵏ B εa) → (q : εa ≾ₑ εb)
              → μᵏ ∘ᵐ Tᵏᶠ (T-≤ᵏ q ∘ᵐ g) ∘ᵐ top-stepᵏ r
              ≈ᵐ T-≤ᵏ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ μᵏ ∘ᵐ Tᵏᶠ g ∘ᵐ top-stepᵏ r
    T-≤ᵏ-topᵏ B (↝-STEP r) g q = T-≤ᵏ-implstep B r g q
    T-≤ᵏ-topᵏ B (OP-STEP {op = op}) g q = tick-case (op-grade op) η⊣ g q

    -- THE MULTI-STEP CLOSURE

    top-steps-grade : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
                    → cf ⟿* cf' → E
    top-steps-grade ε*ᵗ       = uₑ
    top-steps-grade (r ◅ᵗ rs) = top-grade r ·ₑ top-steps-grade rs

    top-stepsᵏ : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
               → (rs : cf ⟿* cf')
               → ⟦ hist (Config.state cf) ⟧ᶜᵗˣ
               →ᵐ Tᵏ ⟦ hist (Config.state cf') ⟧ᶜᵗˣ (top-steps-grade rs)
    top-stepsᵏ ε*ᵗ       = ηᵏ
    top-stepsᵏ (r ◅ᵗ rs) = top-stepsᵏ rs ⋄ᵏ top-stepᵏ r

    top-steps-≾ : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
                → (rs : cf ⟿* cf') → top-steps-grade rs ·ₑ ε' ≾ₑ ε
    top-steps-≾ {ε = ε} ε*ᵗ = ≾ₑ-reflexive (·ₑ-identityˡ ε)
    top-steps-≾ {ε' = ε'} (r ◅ᵗ rs) =
      ≾ₑ-trans (≾ₑ-reflexive (·ₑ-assoc (top-grade r) (top-steps-grade rs) ε'))
      (≾ₑ-trans (·ₑ-monoʳ-≾ₑ (top-steps-≾ rs)) (top-≾ r))

    top-stepsᴾᶜᶠ : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
                 → cf ⟿* cf' → Paramᶜᶠ cf → Paramᶜᶠ cf'
    top-stepsᴾᶜᶠ ε*ᵗ       p = p
    top-stepsᴾᶜᶠ (r ◅ᵗ rs) p = top-stepsᴾᶜᶠ rs (topᴾᶜᶠ r p)

    Uniform⟿* : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
              → cf ⟿* cf' → Paramᶜᶠ cf → Set
    Uniform⟿* ε*ᵗ       _ = ⊤
    Uniform⟿* (r ◅ᵗ rs) p = Uniform⟿ r (proj₂ p) × Uniform⟿* rs (topᴾᶜᶠ r p)

    -- A run of the top-level machine is sound: a program means what it runs
    -- to, after the ticks its operations cost, at the run's refined grade.

    ⟿*-sound : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
              → (rs : cf ⟿* cf') → (p : Paramᶜᶠ cf) → Uniform⟿* rs p
              → ⟦ cf ⟧ᵏᶜᶠ p
              ≈ᵐ T-≤ᵏ (top-steps-≾ rs)
                 ∘ᵐ _⋄ᵏ_ {⟦ hist (Config.state cf) ⟧ᶜᵗˣ}
                         {⟦ hist (Config.state cf') ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ}
                         {top-steps-grade rs} {ε'}
                         (⟦ cf' ⟧ᵏᶜᶠ (top-stepsᴾᶜᶠ rs p)) (top-stepsᵏ rs)
    ⟿*-sound {A = A} {ε = ε} {cf = cf} ε*ᵗ p _ =
      ≈ᵐ-sym
        (  ∘ᵐ-congʳ (⋄ᵏ-ηᵏ (⟦ cf ⟧ᵏᶜᶠ p) ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-≡ _))
         ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
         ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-trans _ _ (≾ₑ-reflexive {ε} refl))
         ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-refl _)
         ∙ᵏ ∘ᵐ-identityˡ _)
    ⟿*-sound {A = A} {ε' = ε'} (_◅ᵗ_ {ε₂ = ε₂} {cf₃ = cf₃} r rs) p (u , us) =
        ⟿-sound r p u
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (Tᵏ-congᶠ (⟿*-sound rs (topᴾᶜᶠ r p) us))))
      -- the run's coercion escapes the step's transition …
      ∙ᵏ ∘ᵐ-congʳ (T-≤ᵏ-topᵏ ⟦ A ⟧ᵛ r
           (⟦ cf₃ ⟧ᵏᶜᶠ (top-stepsᴾᶜᶠ rs (topᴾᶜᶠ r p)) ⋄ᵏ top-stepsᵏ rs)
           (top-steps-≾ rs))
      -- … and the two binds re-associate into one
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (bind-bindᵏ (⟦ cf₃ ⟧ᵏᶜᶠ (top-stepsᴾᶜᶠ rs (topᴾᶜᶠ r p)))
                               (top-stepsᵏ rs) (top-stepᵏ r)))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤ᵏ-≡ _)))
      ∙ᵏ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤ᵏ-trans _ _ b))
      ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-trans b (top-≾ r) (top-steps-≾ (r ◅ᵗ rs)))
      where
        b : top-steps-grade (r ◅ᵗ rs) ·ₑ ε' ≾ₑ top-grade r ·ₑ ε₂
        b = ≾ₑ-trans
              (≾ₑ-reflexive (·ₑ-assoc (top-grade r) (top-steps-grade rs) ε'))
              (·ₑ-monoʳ-≾ₑ (top-steps-≾ rs))
