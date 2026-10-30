------------------------------------------------------------------
-- Erasure of well-typed terms to their underlying raw terms.    --
--                                                               --
-- `ErV`/`ErC` are the term formers with every type, side       --
-- condition and subsumption witness dropped; a box keeps its    --
-- grade and a delay its duration, both being part of the        --
-- program. Variables become de Bruijn positions, counting       --
-- binders and skipping locks. Two derivations have the same     --
-- erasure exactly when they are the same program typed          --
-- differently.                                                  --
--                                                               --
-- A handler's clause family is indexed by the operation and the --
-- continuation's effect, as in the typing rule, so that equal   --
-- erasures compare clauses at every effect.                     --
------------------------------------------------------------------

open import Grades.Base
open import Language.Comparisons using (Cmp)
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.Syntax.Erasure (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts S
open import MonomorphicCalculus.Syntax.Terms    S
open import MonomorphicCalculus.Syntax.Types    S

-- Raw terms

mutual

  data ErV : Set where
    var   : ℕ → ErV
    const : (B : BaseType) → BaseConstants B → ErV
    ⋆     : ErV
    true  : ErV
    false : ErV
    zero  : ErV
    succ  : ErV → ErV
    ⦉_,_⦊ : ErV → ErV → ErV
    inl   : ErV → ErV
    inr   : ErV → ErV
    nil   : ErV
    cons  : ErV → ErV → ErV
    lam   : ErC → ErV
    handler : ErC → (Op → E → ErC) → ErV

  data ErC : Set where
    return            : ErV → ErC
    _⨟_               : ErC → ErC → ErC
    _·_               : ErV → ErV → ErC
    match_`in_        : ErV → ErC → ErC
    absurd            : ErV → ErC
    cmp               : Cmp → ErV → ErV → ErC
    if_`then_`else_   : ErV → ErC → ErC → ErC
    caseℕ_`zero_`succ_ : ErV → ErC → ErC → ErC
    recℕ              : ErV → ErC → ErC → ErC
    case+_`inl_`inr_  : ErV → ErC → ErC → ErC
    caseL_`nil_`cons_ : ErV → ErC → ErC → ErC
    recL              : ErV → ErC → ErC → ErC
    perform           : Op → ErV → ErC → ErC
    delay             : 𝔻 → ErC → ErC
    handle_`with_     : ErC → ErV → ErC
    unbox             : ℕ → ErC → ErC
    box               : R → ErV → ErC → ErC

-- De Bruijn position of a variable: locks contribute nothing.

var-pos : ∀ {Γ A ρ} → A ∈[ ρ ] Γ → ℕ
var-pos Hd        = zero
var-pos (Tl-∷ x)  = suc (var-pos x)
var-pos (Tl-⟨⟩ x) = var-pos x

-- Erasure

mutual

  ⌊_⌋ᵛ : ∀ {Γ A} → Γ ⊢V⦂ A → ErV

  ⌊ var f x ⌋ᵛ   = var (var-pos x)
  ⌊ const c ⌋ᵛ   = const _ c
  ⌊ ⋆ ⌋ᵛ         = ⋆
  ⌊ true ⌋ᵛ      = true
  ⌊ false ⌋ᵛ     = false
  ⌊ zero ⌋ᵛ      = zero
  ⌊ succ V ⌋ᵛ    = succ ⌊ V ⌋ᵛ
  ⌊ ⦉ V , W ⦊ ⌋ᵛ  = ⦉ ⌊ V ⌋ᵛ , ⌊ W ⌋ᵛ ⦊
  ⌊ inl V ⌋ᵛ     = inl ⌊ V ⌋ᵛ
  ⌊ inr V ⌋ᵛ     = inr ⌊ V ⌋ᵛ
  ⌊ nil ⌋ᵛ       = nil
  ⌊ cons V W ⌋ᵛ  = cons ⌊ V ⌋ᵛ ⌊ W ⌋ᵛ
  ⌊ lam M ⌋ᵛ     = lam ⌊ M ⌋ᶜ
  ⌊ handler N H ⌋ᵛ = handler ⌊ N ⌋ᶜ (λ op ε'' → ⌊ H op ε'' ⌋ᶜ)
  ⌊ subV V p ⌋ᵛ  = ⌊ V ⌋ᵛ

  ⌊_⌋ᶜ : ∀ {Γ C} → Γ ⊢C⦂ C → ErC

  ⌊ return V ⌋ᶜ               = return ⌊ V ⌋ᵛ
  ⌊ M ⨟ N ⌋ᶜ                  = ⌊ M ⌋ᶜ ⨟ ⌊ N ⌋ᶜ
  ⌊ V · W ⌋ᶜ                  = ⌊ V ⌋ᵛ · ⌊ W ⌋ᵛ
  ⌊ match V `in M ⌋ᶜ          = match ⌊ V ⌋ᵛ `in ⌊ M ⌋ᶜ
  ⌊ absurd V ⌋ᶜ               = absurd ⌊ V ⌋ᵛ
  ⌊ cmp ⋈ V W _ ⌋ᶜ            = cmp ⋈ ⌊ V ⌋ᵛ ⌊ W ⌋ᵛ
  ⌊ if V `then M `else N ⌋ᶜ   = if ⌊ V ⌋ᵛ `then ⌊ M ⌋ᶜ `else ⌊ N ⌋ᶜ
  ⌊ caseℕ V `zero M `succ N ⌋ᶜ = caseℕ ⌊ V ⌋ᵛ `zero ⌊ M ⌋ᶜ `succ ⌊ N ⌋ᶜ
  ⌊ recℕ V M N p ⌋ᶜ            = recℕ ⌊ V ⌋ᵛ ⌊ M ⌋ᶜ ⌊ N ⌋ᶜ
  ⌊ case+ V `inl M `inr N ⌋ᶜ = case+ ⌊ V ⌋ᵛ `inl ⌊ M ⌋ᶜ `inr ⌊ N ⌋ᶜ
  ⌊ caseL V `nil M `cons N ⌋ᶜ = caseL ⌊ V ⌋ᵛ `nil ⌊ M ⌋ᶜ `cons ⌊ N ⌋ᶜ
  ⌊ recL V M N p ⌋ᶜ            = recL ⌊ V ⌋ᵛ ⌊ M ⌋ᶜ ⌊ N ⌋ᶜ
  ⌊ perform op V M ⌋ᶜ         = perform op ⌊ V ⌋ᵛ ⌊ M ⌋ᶜ
  ⌊ delay τ M ⌋ᶜ              = delay τ ⌊ M ⌋ᶜ
  ⌊ handle M `with V ⌋ᶜ       = handle ⌊ M ⌋ᶜ `with ⌊ V ⌋ᵛ
  ⌊ unbox x rel p N ⌋ᶜ        = unbox (var-pos x) ⌊ N ⌋ᶜ
  ⌊ box ρ V N ⌋ᶜ              = box ρ ⌊ V ⌋ᵛ ⌊ N ⌋ᶜ
  ⌊ subC M p ⌋ᶜ               = ⌊ M ⌋ᶜ
