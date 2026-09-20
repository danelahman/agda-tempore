------------------------------------------------------------------
-- Erasure of mirrored derivations to raw terms                   --
--                                                                --
-- `⌊_⌋ᵛ` and `⌊_⌋ᶜ` are total functions from the well-typed      --
-- syntax of `TypeInference.Open.Language` to the well-scoped raw     --
-- syntax of `TypeInference.Raw.Syntax`. They forget types, grades    --
-- and entailment premises, keeping only what a raw term          --
-- annotates.                                                     --
--                                                                --
-- Erasure is index-preserving: a handler clause — typed at the   --
-- extended scope `Θ +e` over a context of arity `2 + n` —        --
-- erases to a `RawC (2 + n)` with no adjustment, and a           --
-- variable's raw index is its full-context position `var-pos`.   --
--                                                                --
-- Erasure is not injective: `coerce` erases to its subject.      --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero)
open import Data.Nat using (ℕ)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Erase (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.Open.Grades   S
open import TypeInference.Open.Types    S
open import TypeInference.Open.Contexts S
open import TypeInference.Open.Hyps     S
open import TypeInference.Open.Language S

open import TypeInference.Raw.Syntax    S

mutual

  ⌊_⌋ᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
       → Q ∣ Γ ⊢V⦂ A
       -------------
       → RawV n

  -- the raw index of a variable is its full-context position

  ⌊ var x p ⌋ᵛ    = var (var-pos x)
  ⌊ const B c ⌋ᵛ  = const B c
  ⌊ ⋆ ⌋ᵛ          = ⋆
  ⌊ true ⌋ᵛ       = true
  ⌊ false ⌋ᵛ      = false
  ⌊ ⦉ V , W ⦊ ⌋ᵛ   = ⦉ ⌊ V ⌋ᵛ , ⌊ W ⌋ᵛ ⦊
  ⌊ lam M ⌋ᵛ      = lam ⌊ M ⌋ᶜ


  ⌊_⌋ᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
       → Q ∣ Γ ⊢C⦂ C
       -------------
       → RawC n

  ⌊ return V ⌋ᶜ                 = return ⌊ V ⌋ᵛ
  ⌊ M ⨟ N ⌋ᶜ                    = ⌊ M ⌋ᶜ ⨟ ⌊ N ⌋ᶜ
  ⌊ V · W ⌋ᶜ                    = ⌊ V ⌋ᵛ · ⌊ W ⌋ᵛ
  ⌊ match V `in M ⌋ᶜ            = match ⌊ V ⌋ᵛ `in ⌊ M ⌋ᶜ
  ⌊ absurd V ⌋ᶜ                 = absurd ⌊ V ⌋ᵛ
  ⌊ if V `then M `else N ⌋ᶜ     = if ⌊ V ⌋ᵛ `then ⌊ M ⌋ᶜ `else ⌊ N ⌋ᶜ
  ⌊ perform op V M ⌋ᶜ           = perform op ⌊ V ⌋ᵛ ⌊ M ⌋ᶜ
  ⌊ delay τ M ⌋ᶜ                = delay τ ⌊ M ⌋ᶜ

  -- the clause family is erased pointwise; `H op` is typed over a context of
  -- arity `2 + n`, which is the raw clause's scope on the nose

  ⌊ handle M `with H `in N ⌋ᶜ   = handle ⌊ M ⌋ᶜ `with (λ op → ⌊ H op ⌋ᶜ) `in ⌊ N ⌋ᶜ

  ⌊ unbox x p N ⌋ᶜ              = unbox (var-pos x) ⌊ N ⌋ᶜ

  -- the grade of a box is dropped, being existentially bound by inference

  ⌊ box ρ V N ⌋ᶜ                = box ⌊ V ⌋ᵛ ⌊ N ⌋ᶜ

  -- sub-effecting is invisible

  ⌊ coerce p M ⌋ᶜ               = ⌊ M ⌋ᶜ

-- Sanity checks: erasure computes as intended.

-- The scope has to be given explicitly, as in `TypeInference.Open.Language`:
-- `OCtx`'s scope is not determined by `[]`.

private

  ∅ᶜ : OCtx ∅ˢ 0
  ∅ᶜ = []

  -- a value in a plain context

  ex-⋆ : ∅ᴴ ∣ (∅ᶜ ∷ Unit) ⊢V⦂ Unit
  ex-⋆ = ⋆

  ex-⋆-erase : ⌊ ex-⋆ ⌋ᵛ ≡ ⋆
  ex-⋆-erase = refl

  -- a variable used after time-passage: the lock is forgotten, the position kept

  ex-var-lock : ∅ᴴ ∣ ((∅ᶜ ∷ Unit) ⟨ rconst uᵣ ⟩) ⊢V⦂ Unit
  ex-var-lock = var (Tl-⟨⟩ Hd) (et-ok Unitₑ)

  ex-var-lock-erase : ⌊ ex-var-lock ⌋ᵛ ≡ var zero
  ex-var-lock-erase = refl

  -- a variable used across a clause barrier: that lock too is forgotten

  ex-var-barrier : ∅ᴴ ∣ ((∅ᶜ ∷ Unit) ⟨ rconst ⊤ᵣ ⟩) ⊢V⦂ Unit
  ex-var-barrier = var (Tl-⟨⟩ Hd) (et-ok Unitₑ)

  ex-var-barrier-erase : ⌊ ex-var-barrier ⌋ᵛ ≡ var zero
  ex-var-barrier-erase = refl

  -- unboxing a boxed variable

  ex-unbox : ∅ᴴ ∣ (∅ᶜ ∷ [ ûᵣ ] Unit) ⊢C⦂ Unit ‼ ûₑ
  ex-unbox = unbox Hd ⊩≾̂ᵣ-refl (return ⋆)

  ex-unbox-erase : ⌊ ex-unbox ⌋ᶜ ≡ unbox zero (return ⋆)
  ex-unbox-erase = refl

  -- coerce-invisibility: a sub-effecting step leaves the raw term untouched

  ex-coerce-erase : ⌊ coerce ⊩≾̂ₑ-refl ex-unbox ⌋ᶜ ≡ ⌊ ex-unbox ⌋ᶜ
  ex-coerce-erase = refl
