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
-- so the two recursions are independent — which is what a composition generator
-- in `Sub₀` would have destroyed.
--
-- At the empty ambient throughout, and so transport-free: the handler clauses'
-- `restrict-sub₀ s` stays there because `[] ᴱ` is `[]`.

mutual

  V-sub₀ : ∀ {Γ Γ' A}
         → Sub₀ [] Γ Γ'
         → Γ' ⊢V⦂ A
         ------------
         → Γ ⊢V⦂ A

  V-sub₀ s (var f x)   = sub-var₀ s x f
  V-sub₀ s (const c)   = const c
  V-sub₀ s ⋆           = ⋆
  V-sub₀ s (⦉ V , W ⦊)  = ⦉ V-sub₀ s V , V-sub₀ s W ⦊
  V-sub₀ s (lam M)     = lam (C-sub₀ (cong-sub₀ s) M)

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
  C-sub₀ s (perform op V M) = perform op (V-sub₀ s V) (C-sub₀ (cong-sub₀ s) M)
  C-sub₀ s (delay τ M)      = delay τ (C-sub₀ (cong-sub₀ s) M)
  C-sub₀ s (handle M `with H `in N) =
    handle C-sub₀ s M
    `with (λ op ε'' →
             C-sub₀ (cong-∷-sub (cong-∷-sub (restrict-sub₀ s))) (H op ε''))
    `in (C-sub₀ (cong-sub₀ s) N)
  -- The unboxed resource variable is taken to another resource variable by
  -- `sub-tgt₀`, at a grade that drops. Read off with projections rather than a
  -- `with`, so that this clause reduces to an `unbox` node at an abstract `s`.
  C-sub₀ s (unbox x rel M) =
    unbox (proj₁ (proj₂ (sub-tgt₀ s x)))
          (≾ᵣ-trans (proj₂ (proj₂ (sub-tgt₀ s x))) rel)
          (C-sub₀ (cong-sub₀ s) M)
  C-sub₀ s (box V M) = box (V-sub₀ (cong-sub₀ s) V) (C-sub₀ (cong-sub₀ s) M)
  C-sub₀ s (coerce rel M) = coerce rel (C-sub₀ s M)

-- ACTING BY AN AMBIENT-INDEXED SUBSTITUTION
--
-- As for renamings, a substitution that fixes an ambient acts by first
-- forgetting what it fixes (`expose-sub₀-[]`).

V-sub₀ᴬ : ∀ {Ξ Δ Δ' A} → Sub₀ Ξ Δ Δ' → (Ξ ++ᶜ Δ') ⊢V⦂ A → (Ξ ++ᶜ Δ) ⊢V⦂ A
V-sub₀ᴬ s V = V-sub₀ (expose-sub₀-[] s) V

C-sub₀ᴬ : ∀ {Ξ Δ Δ' C} → Sub₀ Ξ Δ Δ' → (Ξ ++ᶜ Δ') ⊢C⦂ C → (Ξ ++ᶜ Δ) ⊢C⦂ C
C-sub₀ᴬ s M = C-sub₀ (expose-sub₀-[] s) M
