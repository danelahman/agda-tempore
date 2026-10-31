---------------------------------------------------------------------------
-- Soundness of the pure top-level operational semantics.                --
--                                                                       --
-- The top-level machine runs a program against external                 --
-- implementations of the algebraic operations (`op-sem`): an ordinary   --
-- step `⟶-STEP`, and `OP-STEP`, which replaces an operation call by     --
-- the implementation's value and locks the state by `op-grade op`.      --
--                                                                       --
-- Its denotation lands in the tick monad (`Model.TickMonad`), composed  --
-- with the tree-monad denotation via the implementation                 --
-- `implᵐ : Tᵒ A ε →ᵐ Tᵏ A ε` (`Model.Implementation`).                  --
--                                                                       --
-- The theorem's one condition, `OpSemCoherent`, is that `op-sem` is the --
-- semantic implementation `op-semᵐ`.                                    --
---------------------------------------------------------------------------

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
open import MonomorphicCalculus.DenotationalSemantics.Model.TickMonad
open import MonomorphicCalculus.DenotationalSemantics.Model.Implementation

module MonomorphicCalculus.OperationalSemantics.Soundness.TopLevel
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

open import MonomorphicCalculus.Syntax.Types         S
open import MonomorphicCalculus.Syntax.Contexts      S
open import MonomorphicCalculus.Syntax.Terms         S
open import MonomorphicCalculus.Syntax.Renaming      S
open import MonomorphicCalculus.Syntax.Substitution  S

open import MonomorphicCalculus.OperationalSemantics.State                       S
open import MonomorphicCalculus.OperationalSemantics.Reduction                   S
open import MonomorphicCalculus.OperationalSemantics.TopLevel                    S
open import MonomorphicCalculus.OperationalSemantics.TopLevel.Reduction          S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-congᶠ; []-∘ᵐ; []-≤; []-≤-nat)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ)
open Adjunction Adj using (η⊣; η⊣-nat)
open GroundTypes GTy using (⟦_⟧ᵍ)
open Monad Mon using (Tᵒ; Tᶠ; ηᵀ; μᵀ; T-≤; ε-substᵀ; delayᵀ; opᵀ)
open TickMonad TMon
open Implementation Impl

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.State S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation S Cat Fut Pst Adj GTy Mon GE

open import MonomorphicCalculus.OperationalSemantics.Soundness.TickLemmas S Cat Fut Pst Adj GTy Mon TMon
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

    ⟦_⟧ᵏᶜᶠ : ∀ {A ε} → (cf : Config (A ‼ ε)) → Paramᶜᶠ cf
           → ⟦ hist (Config.state cf) ⟧ᶜᵗˣ →ᵐ Tᵏ ⟦ A ⟧ᵛ ε
    ⟦ cf ⟧ᵏᶜᶠ p = implᵐ ∘ᵐ ⟦ cf ⟧ᶜᶠ p

    -- The certificate across a top-level step: `⟶-STEP` inherits the ordinary
    -- one, `OP-STEP` substitutes the implementation's (parametric) value.

    topᴾᶜᶠ : ∀ {ε ε'} {St St' : 𝕊 []} {A A₀ : VType}
           → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A₀ ‼ ε'}
           → (r : ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩)
           → Paramᶜᶠ (⟨ St , M ⟩) → Paramᶜᶠ (⟨ St' , M' ⟩)
    topᴾᶜᶠ (⟶-STEP r) p = stepᴾᶜᶠ r p
    topᴾᶜᶠ (OP-STEP {op = op} {S = St} {V = V} {M = M}) (pSt , (pV , pM)) =
      pSt , subᶜ M split-[] (op-sem op V) pM (op-par op St V)

    -- The top-level step's grade, transition and refinement: `⟶-STEP`
    -- inherits the ordinary ones, run through the implementation; `OP-STEP`
    -- performs the operation, costing `op-grade op`, with a tick transition.

    top-grade : ∀ {ε ε'} {St St' : 𝕊 []} {A A₀ : VType}
              → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A₀ ‼ ε'}
              → ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩ → E
    top-grade (⟶-STEP r)          = step-grade r
    top-grade (OP-STEP {op = op}) = op-grade op ·ₑ uₑ

    top-stepᵏ : ∀ {ε ε'} {St St' : 𝕊 []} {A A₀ : VType}
              → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A₀ ‼ ε'}
              → (r : ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩)
              → ⟦ hist St ⟧ᶜᵗˣ →ᵐ Tᵏ ⟦ hist St' ⟧ᶜᵗˣ (top-grade r)
    top-stepᵏ (⟶-STEP r) = implᵐ ∘ᵐ stepᵀ r
    top-stepᵏ (OP-STEP {op = op}) =
      tickᵏ (op-grade op) ∘ᵐ [ mapᵉ (op-grade op) ]ᶠ ηᵏ ∘ᵐ η⊣

    top-≾ : ∀ {ε ε'} {St St' : 𝕊 []} {A A₀ : VType}
          → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A₀ ‼ ε'}
          → (r : ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩)
          → top-grade r ·ₑ ε' ≾ₑ ε
    top-≾ (⟶-STEP r) = step-≾ r
    top-≾ (OP-STEP {ε = ε} {op = op}) =
      ≃ₑ⇒≾ₑ (·ₑ-cong (·ₑ-identityʳ (op-grade op)) ≃ₑ-refl)

    -- The value type a top-level step refines to.

    top-refines-type : ∀ {ε ε'} {St St' : 𝕊 []} {A A₀ : VType}
                     → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A₀ ‼ ε'}
                     → ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩ → A₀ <:ᵛ A
    top-refines-type (⟶-STEP r)      = step-refines-type r
    top-refines-type {A = A} OP-STEP = <:ᵛ-refl A

    -- A refinement at a type the step does not move denotes the identity.

    T⟦⟧<:ᵛ-idᵏ : ∀ {A ε} → (t : A <:ᵛ A) → Tᵏᶠ {⟦ A ⟧ᵛ} {⟦ A ⟧ᵛ} {ε} ⟦ t ⟧<:ᵛ ≈ᵐ idᵐ
    T⟦⟧<:ᵛ-idᵏ t = Tᵏ-congᶠ (⟦⟧<:ᵛ-id t) ∙ᵏ Tᵏ-idᵐ

    insert-coeᵏ : ∀ {X A ε} {h : X →ᵐ Tᵏ ⟦ A ⟧ᵛ ε} → (t : A <:ᵛ A)
                → h ≈ᵐ Tᵏᶠ ⟦ t ⟧<:ᵛ ∘ᵐ h
    insert-coeᵏ {h = h} t = ≈ᵐ-sym (∘ᵐ-congˡ (T⟦⟧<:ᵛ-idᵏ t) ∙ᵏ ∘ᵐ-identityˡ h)

    -- A functorial action escapes a bind, by naturality of the multiplication.

    Tᵏᶠ-bind : ∀ {X Y A B ε ε'} → (h : A →ᵐ B) → (g : Y →ᵐ Tᵏ A ε')
             → (t : X →ᵐ Tᵏ Y ε)
             → (Tᵏᶠ h ∘ᵐ g) ⋄ᵏ t ≈ᵐ Tᵏᶠ h ∘ᵐ (g ⋄ᵏ t)
    Tᵏᶠ-bind h g t =
        ∘ᵐ-congʳ (∘ᵐ-congˡ (Tᵏ-∘ᵐ _ _))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ᵏ ∘ᵐ-congˡ (μᵏ-nat h)
      ∙ᵏ ∘ᵐ-assoc _ _ _

    -- The two refinements a step and the run after it contribute, with the
    -- three sub-effectings between them, collapse into the run's own pair.

    run-collapseᵏ : ∀ {X A B C ε₁ ε₂ ε₃ ε₄}
                  → (h₁ : B →ᵐ A) → (h₂ : C →ᵐ B)
                  → (a : ε₂ ≾ₑ ε₁) → (m : ε₃ ≾ₑ ε₂) → (c : ε₄ ≾ₑ ε₃)
                  → (w : ε₄ ≾ₑ ε₁) → (K : X →ᵐ Tᵏ C ε₄)
                  → T-≤ᵏ a ∘ᵐ Tᵏᶠ h₁ ∘ᵐ T-≤ᵏ m ∘ᵐ Tᵏᶠ h₂ ∘ᵐ T-≤ᵏ c ∘ᵐ K
                  ≈ᵐ T-≤ᵏ w ∘ᵐ Tᵏᶠ (h₁ ∘ᵐ h₂) ∘ᵐ K
    run-collapseᵏ h₁ h₂ a m c w K =
        ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤ᵏ-nat h₂ c))))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤ᵏ-trans c m (≾ₑ-trans c m))))
      ∙ᵏ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤ᵏ-nat h₁ (≾ₑ-trans c m)))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-trans (≾ₑ-trans c m) a w)
      ∙ᵏ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (Tᵏ-∘ᵐ h₁ h₂)))

    Uniform⟿ : ∀ {ε ε'} {St St' : 𝕊 []} {A A₀ : VType}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A₀ ‼ ε'}
             → ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩ → Paramᶜ M → Set
    Uniform⟿ (⟶-STEP r) pM = Uniform⟶ r pM
    Uniform⟿ OP-STEP    _  = ⊤

    -- The interpretation's ground-type coercions on the arity cancel against
    -- the ones on the substituted value.

    substᵈ-⟨⟩ : ∀ {Z W Y Y'} → (e : Y ≡ Y') → (f : (Z ×ᵐ Y) →ᵐ W) → (g : Z →ᵐ Y)
              → subst (λ O → (Z ×ᵐ O) →ᵐ W) e f
                  ∘ᵐ ⟨ idᵐ , subst (λ O → Z →ᵐ O) e g ⟩ᵐ
              ≈ᵐ f ∘ᵐ ⟨ idᵐ , g ⟩ᵐ
    substᵈ-⟨⟩ refl f g = ≈ᵐ-refl

    -- `OP-STEP`: the implementation feeds the continuation `op-semᵐ`'s value,
    -- which by `OpSemCoherent` is the value the reduct substitutes, and
    -- leaves a tick.

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

        -- the operation's continuation, fed `op-semᵐ`'s value, is the reduct
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

    -- Soundness of a top-level step: `⟶-STEP` is `⟶-sound` carried along the
    -- monad morphism `implᵐ`.

    ⟿-sound : ∀ {ε ε' A A₀} {St St' : 𝕊 []}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A₀ ‼ ε'}
             → (r : ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩)
             → (p : Paramᶜᶠ (⟨ St , M ⟩))
             → Uniform⟿ r (proj₂ p)
             → ⟦ ⟨ St , M ⟩ ⟧ᵏᶜᶠ p
             ≈ᵐ T-≤ᵏ (top-≾ r)
                ∘ᵐ Tᵏᶠ ⟦ top-refines-type r ⟧<:ᵛ
                ∘ᵐ _⋄ᵏ_ {⟦ hist St ⟧ᶜᵗˣ} {⟦ hist St' ⟧ᶜᵗˣ} {⟦ A₀ ⟧ᵛ}
                        {top-grade r} {ε'}
                        (⟦ ⟨ St' , M' ⟩ ⟧ᵏᶜᶠ (topᴾᶜᶠ r p)) (top-stepᵏ r)
    ⟿-sound (⟶-STEP {S' = St'} {N = M'} r) (pSt , pM) u =
        ∘ᵐ-congʳ (⟶-sound r pSt pM u)
      ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ᵏ ∘ᵐ-congˡ (implᵐ-T-≤ (step-≾ r))
      ∙ᵏ ∘ᵐ-assoc _ _ _
      ∙ᵏ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (implᵐ-nat ⟦ step-refines-type r ⟧<:ᵛ))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ
           (impl-⋄ (⟦ ⟨ St' , M' ⟩ ⟧ᶜᶠ (stepᴾᶜᶠ r (pSt , pM))) (stepᵀ r)))
    ⟿-sound {A = A} (OP-STEP {op = op} {S = St} {V = V} {M = M}) (pSt , (pV , pM)) _ =
      sound-OP-STEP op St V M pSt pV pM ∙ᵏ ∘ᵐ-congʳ (insert-coeᵏ (<:ᵛ-refl A))

    -- The coercion escapes a top-level transition: every one is built from
    -- `ηᵏ` and ticks, and a tick records nothing, so `tickᵏ-≤` lets a
    -- coercion through it.

    ηᵏ-case : ∀ {X B εa εb} → (g : X →ᵐ Tᵏ B εa) → (q : εa ≾ₑ εb)
            → μᵏ ∘ᵐ Tᵏᶠ (T-≤ᵏ q ∘ᵐ g) ∘ᵐ ηᵏ
            ≈ᵐ T-≤ᵏ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ μᵏ ∘ᵐ Tᵏᶠ g ∘ᵐ ηᵏ
    ηᵏ-case {εa = εa} {εb = εb} g q =
        ⋄ᵏ-ηᵏ (T-≤ᵏ q ∘ᵐ g)
      ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-trans q _ w)
      ∙ᵏ ≈ᵐ-sym
          (  ∘ᵐ-congʳ (⋄ᵏ-ηᵏ g)
           ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
           ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-trans _ _ w))
      where
        w : εa ≾ₑ uₑ ·ₑ εb
        w = ≾ₑ-trans q (≃ₑ⇒≿ₑ (·ₑ-identityˡ εb))

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

    -- the `ηᵀ` rules, with the implementation applied
    ηᵀ-step : ∀ {X B εa εb} → (g : X →ᵐ Tᵏ B εa) → (q : εa ≾ₑ εb)
            → μᵏ ∘ᵐ Tᵏᶠ (T-≤ᵏ q ∘ᵐ g) ∘ᵐ (implᵐ ∘ᵐ ηᵀ)
            ≈ᵐ T-≤ᵏ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ μᵏ ∘ᵐ Tᵏᶠ g ∘ᵐ (implᵐ ∘ᵐ ηᵀ)
    ηᵀ-step g q =
        ∘ᵐ-congʳ (∘ᵐ-congʳ implᵐ-ηᵀ)
      ∙ᵏ ηᵏ-case g q
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym implᵐ-ηᵀ)))

    -- `DELAY`'s transition, implemented: a tick
    delay-tick : ∀ {X} → (τ : 𝔻)
               → implᵐ ∘ᵐ (delayᵀ {⟨ of-durʳ τ ⟩ᵒ X} {uₑ} τ
                           ∘ᵐ [ of-durʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣ {X} {of-durʳ τ})
               ≈ᵐ tickᵏ (of-durᵉ τ)
                  ∘ᵐ [ mapᵉ (of-durᵉ τ) ]ᶠ ηᵏ
                  ∘ᵐ ([]-≤ (≃ᵣ⇒≾ᵣ map-of-durᵉ) ∘ᵐ η⊣)
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

    T-≤ᵏ-implstep : ∀ {ε ε' εa εb A A₀} {St St' : 𝕊 []} → (B : Obj)
                  → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A₀ ‼ ε'}
                  → (r : ⟨ St , M ⟩ ⟶ ⟨ St' , M' ⟩)
                  → (g : ⟦ hist St' ⟧ᶜᵗˣ →ᵐ Tᵏ B εa) → (q : εa ≾ₑ εb)
                  → μᵏ ∘ᵐ Tᵏᶠ (T-≤ᵏ q ∘ᵐ g) ∘ᵐ (implᵐ ∘ᵐ stepᵀ r)
                  ≈ᵐ T-≤ᵏ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ μᵏ ∘ᵐ Tᵏᶠ g ∘ᵐ (implᵐ ∘ᵐ stepᵀ r)
    T-≤ᵏ-implstep B APP        g q = ηᵀ-step g q
    T-≤ᵏ-implstep B MATCH      g q = ηᵀ-step g q
    T-≤ᵏ-implstep B CASEL      g q = ηᵀ-step g q
    T-≤ᵏ-implstep B RECL       g q = ηᵀ-step g q
    T-≤ᵏ-implstep B IF-TRUE    g q = ηᵀ-step g q
    T-≤ᵏ-implstep B CMP        g q = ηᵀ-step g q
    T-≤ᵏ-implstep B IF-FALSE   g q = ηᵀ-step g q
    T-≤ᵏ-implstep B CASE+      g q = ηᵀ-step g q
    T-≤ᵏ-implstep B CASEℕ-ZERO g q = ηᵀ-step g q
    T-≤ᵏ-implstep B CASEℕ-SUCC g q = ηᵀ-step g q
    T-≤ᵏ-implstep B RECℕ-ZERO  g q = ηᵀ-step g q
    T-≤ᵏ-implstep B RECℕ-SUCC  g q = ηᵀ-step g q
    T-≤ᵏ-implstep B SEQ-RET    g q = ηᵀ-step g q
    T-≤ᵏ-implstep B SEQ-OP     g q = ηᵀ-step g q
    T-≤ᵏ-implstep B HANDLE-RET g q = ηᵀ-step g q
    T-≤ᵏ-implstep B HANDLE-OP  g q = ηᵀ-step g q
    T-≤ᵏ-implstep B BOX        g q = ηᵀ-step g q
    T-≤ᵏ-implstep B UNBOX      g q = ηᵀ-step g q
    T-≤ᵏ-implstep B SUB-APP    g q = ηᵀ-step g q
    T-≤ᵏ-implstep B SUB-HANDLE g q = ηᵀ-step g q
    T-≤ᵏ-implstep B SUB-HANDLE-TRANS g q = ηᵀ-step g q
    T-≤ᵏ-implstep B SUB-IF     g q = ηᵀ-step g q
    T-≤ᵏ-implstep B SUB-CASEℕ  g q = ηᵀ-step g q
    T-≤ᵏ-implstep B SUB-RECℕ   g q = ηᵀ-step g q
    T-≤ᵏ-implstep B SUB        g q = ηᵀ-step g q
    T-≤ᵏ-implstep B (SEQ-STEP r _)    g q = T-≤ᵏ-implstep B r g q
    T-≤ᵏ-implstep B (HANDLE-STEP r _) g q = T-≤ᵏ-implstep B r g q
    T-≤ᵏ-implstep B (DELAY {τ = τ}) g q =
        ∘ᵐ-congʳ (∘ᵐ-congʳ (delay-tick τ))
      ∙ᵏ tick-case (of-durᵉ τ) _ g q
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (delay-tick τ))))


    -- The coercion escapes any top-level transition.

    T-≤ᵏ-topᵏ : ∀ {ε ε' εa εb A A₀} {St St' : 𝕊 []} → (B : Obj)
              → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A₀ ‼ ε'}
              → (r : ⟨ St , M ⟩ ⟿ ⟨ St' , M' ⟩)
              → (g : ⟦ hist St' ⟧ᶜᵗˣ →ᵐ Tᵏ B εa) → (q : εa ≾ₑ εb)
              → μᵏ ∘ᵐ Tᵏᶠ (T-≤ᵏ q ∘ᵐ g) ∘ᵐ top-stepᵏ r
              ≈ᵐ T-≤ᵏ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ μᵏ ∘ᵐ Tᵏᶠ g ∘ᵐ top-stepᵏ r
    T-≤ᵏ-topᵏ B (⟶-STEP r) g q = T-≤ᵏ-implstep B r g q
    T-≤ᵏ-topᵏ B (OP-STEP {op = op}) g q = tick-case (op-grade op) η⊣ g q

    top-steps-grade : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
                    → cf ⟿* cf' → E
    top-steps-grade ε*ᵗ       = uₑ
    top-steps-grade (r ◅ᵗ rs) = top-grade r ·ₑ top-steps-grade rs

    top-stepsᵏ : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
               → (rs : cf ⟿* cf')
               → ⟦ hist (Config.state cf) ⟧ᶜᵗˣ
               →ᵐ Tᵏ ⟦ hist (Config.state cf') ⟧ᶜᵗˣ (top-steps-grade rs)
    top-stepsᵏ ε*ᵗ       = ηᵏ
    top-stepsᵏ (r ◅ᵗ rs) = top-stepsᵏ rs ⋄ᵏ top-stepᵏ r

    top-steps-≾ : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
                → (rs : cf ⟿* cf') → top-steps-grade rs ·ₑ ε' ≾ₑ ε
    top-steps-≾ {ε = ε} ε*ᵗ = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
    top-steps-≾ {ε' = ε'} (r ◅ᵗ rs) =
      ≾ₑ-trans (≃ₑ⇒≾ₑ (·ₑ-assoc (top-grade r) (top-steps-grade rs) ε'))
      (≾ₑ-trans (·ₑ-monoʳ-≾ₑ (top-steps-≾ rs)) (top-≾ r))

    top-stepsᴾᶜᶠ : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
                 → cf ⟿* cf' → Paramᶜᶠ cf → Paramᶜᶠ cf'
    top-stepsᴾᶜᶠ ε*ᵗ       p = p
    top-stepsᴾᶜᶠ (r ◅ᵗ rs) p = top-stepsᴾᶜᶠ rs (topᴾᶜᶠ r p)

    Uniform⟿* : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
              → cf ⟿* cf' → Paramᶜᶠ cf → Set
    Uniform⟿* ε*ᵗ       _ = ⊤
    Uniform⟿* (r ◅ᵗ rs) p = Uniform⟿ r (proj₂ p) × Uniform⟿* rs (topᴾᶜᶠ r p)

    -- A run of the top-level machine is sound: a program means what it runs
    -- to, after the ticks its operations cost, at the run's refined grade.

    -- The refinement a top-level run accumulates.

    run⟿-refines-type : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
                      → cf ⟿* cf' → B <:ᵛ A
    run⟿-refines-type {A = A} ε*ᵗ = <:ᵛ-refl A
    run⟿-refines-type (r ◅ᵗ rs) =
      <:ᵛ-trans (run⟿-refines-type rs) (top-refines-type r)

    ⟿*-sound : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
              → (rs : cf ⟿* cf') → (p : Paramᶜᶠ cf) → Uniform⟿* rs p
              → ⟦ cf ⟧ᵏᶜᶠ p
              ≈ᵐ T-≤ᵏ (top-steps-≾ rs)
                 ∘ᵐ Tᵏᶠ ⟦ run⟿-refines-type rs ⟧<:ᵛ
                 ∘ᵐ _⋄ᵏ_ {⟦ hist (Config.state cf) ⟧ᶜᵗˣ}
                         {⟦ hist (Config.state cf') ⟧ᶜᵗˣ} {⟦ B ⟧ᵛ}
                         {top-steps-grade rs} {ε'}
                         (⟦ cf' ⟧ᵏᶜᶠ (top-stepsᴾᶜᶠ rs p)) (top-stepsᵏ rs)
    ⟿*-sound {A = A} {ε = ε} {cf = cf} ε*ᵗ p _ =
      ≈ᵐ-sym
        (  ∘ᵐ-congʳ (∘ᵐ-congˡ (T⟦⟧<:ᵛ-idᵏ (<:ᵛ-refl A)) ∙ᵏ ∘ᵐ-identityˡ _)
         ∙ᵏ ∘ᵐ-congʳ (⋄ᵏ-ηᵏ (⟦ cf ⟧ᵏᶜᶠ p))
         ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
         ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-trans _ _ (≾ₑ-reflexive {ε} refl))
         ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-refl _)
         ∙ᵏ ∘ᵐ-identityˡ _)
    ⟿*-sound {A = A} {ε' = ε'} (_◅ᵗ_ {B = B} {ε₂ = ε₂} {cf₃ = cf₃} r rs) p (u , us) =
        ⟿-sound r p u
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (Tᵏ-congᶠ
           (⟿*-sound rs (topᴾᶜᶠ r p) us)))))
      -- the run's coercion escapes the step's transition, its refinement by
      -- naturality alone …
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (T-≤ᵏ-topᵏ ⟦ B ⟧ᵛ r
           (Tᵏᶠ ⟦ run⟿-refines-type rs ⟧<:ᵛ
              ∘ᵐ (⟦ cf₃ ⟧ᵏᶜᶠ (top-stepsᴾᶜᶠ rs (topᴾᶜᶠ r p)) ⋄ᵏ top-stepsᵏ rs))
           (top-steps-≾ rs)))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (Tᵏᶠ-bind ⟦ run⟿-refines-type rs ⟧<:ᵛ
           (⟦ cf₃ ⟧ᵏᶜᶠ (top-stepsᴾᶜᶠ rs (topᴾᶜᶠ r p)) ⋄ᵏ top-stepsᵏ rs)
           (top-stepᵏ r))))
      -- … and the two binds re-associate into one
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
           (bind-bindᵏ (⟦ cf₃ ⟧ᵏᶜᶠ (top-stepsᴾᶜᶠ rs (topᴾᶜᶠ r p)))
                       (top-stepsᵏ rs) (top-stepᵏ r)))))
      -- … and the two refinements collapse into the run's own
      ∙ᵏ run-collapseᵏ ⟦ top-refines-type r ⟧<:ᵛ ⟦ run⟿-refines-type rs ⟧<:ᵛ
           (top-≾ r) (·ₑ-monoʳ-≾ₑ (top-steps-≾ rs)) _ (top-steps-≾ (r ◅ᵗ rs))
           (⟦ cf₃ ⟧ᵏᶜᶠ (top-stepsᴾᶜᶠ rs (topᴾᶜᶠ r p)) ⋄ᵏ top-stepsᵏ (r ◅ᵗ rs))
      ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (Tᵏ-congᶠ
           (≈ᵐ-sym (⟦⟧<:ᵛ-trans (run⟿-refines-type rs) (top-refines-type r)))))
