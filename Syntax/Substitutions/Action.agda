-------------------------------------------------------------
-- Action of a generating substitution on well-typed terms  --
-------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions.Action (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.RenActions S
open import Syntax.Renamings  S
open import Syntax.Types      S

open import Syntax.Substitutions.Base      S
open import Syntax.Substitutions.Lookup S

-- Structural on the term, exactly as `V-rename`/`C-rename` is: the recursion
-- grows the substitution at each binder (`cong-sub₀`) and never inspects it.
-- The observations recurse on the substitution alone and never call back here,
-- so the two recursions are independent.
--
-- At the empty ambient throughout, and so transport-free: a handler clause's
-- context is the substituted one under one more lock and two more binders.

mutual

  V-sub₀ : ∀ {Γ Γ' A}
         → Sub₀ [] Γ Γ'
         → Γ' ⊢V⦂ A
         ------------
         → Γ ⊢V⦂ A

  V-sub₀ s (var f x)   = sub-var₀ s x f
  V-sub₀ s (const c)   = const c
  V-sub₀ s ⋆           = ⋆
  V-sub₀ s true        = true
  V-sub₀ s false       = false
  V-sub₀ s (⦉ V , W ⦊)  = ⦉ V-sub₀ s V , V-sub₀ s W ⦊
  V-sub₀ s (lam M)     = lam (C-sub₀ (cong-sub₀ s) M)
  V-sub₀ s (subV V p)  = subV (V-sub₀ s V) p

  C-sub₀ : ∀ {Γ Γ' C}
         → Sub₀ [] Γ Γ'
         → Γ' ⊢C⦂ C
         ------------
         → Γ ⊢C⦂ C

  C-sub₀ s (return V)       = return (V-sub₀ s V)
  C-sub₀ s (M ⨟ N)          = C-sub₀ s M ⨟ C-sub₀ (cong-sub₀ s) N
  C-sub₀ s (V · W)          = V-sub₀ s V · V-sub₀ s W
  C-sub₀ s (match V `in M)  = match V-sub₀ s V `in C-sub₀ (cong-sub₀ s) M
  C-sub₀ s (absurd V)       = absurd (V-sub₀ s V)
  C-sub₀ s (if V `then M `else N) =
    if V-sub₀ s V `then C-sub₀ s M `else C-sub₀ s N
  C-sub₀ s (perform op V M) = perform op (V-sub₀ s V) (C-sub₀ (cong-sub₀ s) M)
  C-sub₀ s (delay τ M)      = delay τ (C-sub₀ (cong-sub₀ s) M)
  C-sub₀ s (handle M `with H `in N) =
    handle C-sub₀ s M
    `with (λ op ε'' →
             C-sub₀ (cong-∷-sub (cong-∷-sub (cong-⟨⟩-sub s))) (H op ε''))
    `in (C-sub₀ (cong-sub₀ s) N)
  -- The unboxed resource variable is taken to another resource variable by
  -- `sub-tgt₀`, at a grade that drops and at a declared payload type the named
  -- one only bounds; both witnesses compose into the node's own. Read off with
  -- accessors rather than a `with`, so that this clause reduces to an `unbox`
  -- node at an abstract `s`.
  C-sub₀ s (unbox x rel p M) =
    unbox (tgt-var₀ s x)
          (≾ᵣ-trans (≾ᵣ-trans (tgt-≾₀ s x) rel) (tgt-grade-≾₀ s x))
          (<:ᵛ-trans (tgt-type-<:₀ s x) p)
          (C-sub₀ (cong-sub₀ s) M)
  C-sub₀ s (box V M) = box (V-sub₀ (cong-sub₀ s) V) (C-sub₀ (cong-sub₀ s) M)
  C-sub₀ s (subC M p) = subC (C-sub₀ s M) p
