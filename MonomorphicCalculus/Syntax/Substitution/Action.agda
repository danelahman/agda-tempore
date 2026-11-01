-------------------------------------------------------------
-- Action of a generating substitution on well-typed terms --
-------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.Syntax.Substitution.Action (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming.Action S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Types           S

open import MonomorphicCalculus.Syntax.Substitution.Base       S
open import MonomorphicCalculus.Syntax.Substitution.Lookup  S

-- Structural on the term, exactly as `V-rename`/`C-rename` is: the recursion
-- grows the substitution at each binder (`cong-sub₀`) and never inspects it.
-- The observations recurse on the substitution alone and never call back here,
-- so the two recursions are independent.
--
-- At the empty ambient throughout, and so transport-free: a handler clause's
-- context is the substituted one under one more modality and two more binders.

mutual

  V-sub₀ : ∀ {Γ Γ' A}
         → Sub₀ [] Γ Γ'
         → Γ' ⊢ᵛ⦂ A
         ------------
         → Γ ⊢ᵛ⦂ A

  V-sub₀ s (var x f)   = sub-var₀ s x f
  V-sub₀ s (const B c) = const B c
  V-sub₀ s ⋆           = ⋆
  V-sub₀ s true        = true
  V-sub₀ s false       = false
  V-sub₀ s zero        = zero
  V-sub₀ s (succ V)    = succ (V-sub₀ s V)
  V-sub₀ s (⦉ V , W ⦊)  = ⦉ V-sub₀ s V , V-sub₀ s W ⦊
  V-sub₀ s (inl V)     = inl (V-sub₀ s V)
  V-sub₀ s (inr V)     = inr (V-sub₀ s V)
  V-sub₀ s nil         = nil
  V-sub₀ s (cons V W)  = cons (V-sub₀ s V) (V-sub₀ s W)
  V-sub₀ s (cmp ⋈ V W et) = cmp ⋈ (V-sub₀ s V) (V-sub₀ s W) et
  V-sub₀ s (fun M)     = fun (C-sub₀ (cong-sub₀ s) M)
  V-sub₀ s (handler N H) =
    handler (C-sub₀ (cong-sub₀ s) N)
            (λ op ε'' →
               C-sub₀ (cong-∷-sub (cong-∷-sub (cong-⟨⟩-sub s))) (H op ε''))
  V-sub₀ s (subV V p)  = subV (V-sub₀ s V) p

  C-sub₀ : ∀ {Γ Γ' C}
         → Sub₀ [] Γ Γ'
         → Γ' ⊢ᶜ⦂ C
         ------------
         → Γ ⊢ᶜ⦂ C

  C-sub₀ s (return V)         = return (V-sub₀ s V)
  C-sub₀ s (M ⨟ N)            = C-sub₀ s M ⨟ C-sub₀ (cong-sub₀ s) N
  C-sub₀ s (V · W)            = V-sub₀ s V · V-sub₀ s W
  C-sub₀ s (match V `with M)  = match V-sub₀ s V `with C-sub₀ (cong-sub₀ s) M
  C-sub₀ s (absurd V)         = absurd (V-sub₀ s V)
  C-sub₀ s (if V `then M `else N) =
    if V-sub₀ s V `then C-sub₀ s M `else C-sub₀ s N
  C-sub₀ s (matchℕ V `zero M `succ N) =
    matchℕ V-sub₀ s V `zero C-sub₀ s M `succ C-sub₀ (cong-sub₀ s) N
  C-sub₀ s (recℕ V M N p) =
    recℕ (V-sub₀ s V) (C-sub₀ s M)
         (C-sub₀ (cong-∷-sub (cong-⟨⟩-sub (cong-∷-sub (cong-⟨⟩-sub s)))) N) p
  C-sub₀ s (matchL V `nil M `cons N) =
    matchL V-sub₀ s V `nil C-sub₀ s M `cons C-sub₀ (cong-sub₀ s) N
  C-sub₀ s (recL V M N p) =
    recL (V-sub₀ s V) (C-sub₀ s M)
         (C-sub₀ (cong-∷-sub (cong-⟨⟩-sub (cong-∷-sub (cong-∷-sub (cong-⟨⟩-sub s))))) N) p
  C-sub₀ s (match+ V `inl M `inr N) =
    match+ V-sub₀ s V `inl C-sub₀ (cong-sub₀ s) M `inr C-sub₀ (cong-sub₀ s) N
  C-sub₀ s (perform op V M) = perform op (V-sub₀ s V) (C-sub₀ (cong-sub₀ s) M)
  C-sub₀ s (delay τ M)      = delay τ (C-sub₀ (cong-sub₀ s) M)
  C-sub₀ s (handle M `with V) = handle C-sub₀ s M `with V-sub₀ s V
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
  C-sub₀ s (box _ V M) = box _ (V-sub₀ (cong-sub₀ s) V) (C-sub₀ (cong-sub₀ s) M)
  C-sub₀ s (subC M p) = subC (C-sub₀ s M) p
