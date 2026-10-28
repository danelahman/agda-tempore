------------------------------------------------------------------
-- Constraint generation                                        --
--                                                              --
-- `genV Γ V A` and `genC Γ M C` map a raw term and an expected --
-- open type to a constraint over the same scope. They are      --
-- structural on the raw term and follow the rules of           --
-- `OpenCalculus.Typing` former by former: every                --
-- type a rule leaves undetermined is an ∃-bound variable, and  --
-- every side condition is a constraint atom.                   --
--                                                              --
-- The expected type is an upper bound. Where a rule meets two  --
-- types that generation does not determine, the expected type  --
-- is the right-hand side of a `_≾̂ᵥᶜ_` or `_≾̂ₑᶜ_` atom;         --
-- elsewhere the shape is fixed by `_≐ᵥ_`, and the bound is     --
-- passed to the subterms.                                      --
--                                                              --
-- Under a binder, the arguments of the recursive calls and the --
-- interpretation of the raw term's type and grade variables    --
-- are weakened; the constraints are built under the innermost  --
-- binder.                                                      --
--                                                              --
-- Contract. `σ ⊨[ Q ] genC Γ M (A ‼ t)` holds exactly when     --
-- some derivation of `Q ∣ Γ [ σ ] ⊢C⦂ (A ‼ t) [ σ ]` erases to --
-- `M [ σ ]` (`charV`, `charC`, from `soundV`/`soundC` in       --
-- `Soundness` and `completeV`/`completeC` in `Completeness`).  --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Inference.Generate (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OpenCalculus.Syntax.Grades   S
open import OpenCalculus.Syntax.Types    S
open import OpenCalculus.Syntax.Contexts S
open import OpenCalculus.Syntax.Subst    S

open import OpenCalculus.Syntax.Raw S

open import OpenCalculus.Inference.Constraints.Syntax S

-- The looked-up type subtypes into the expected one, and its grade owes
-- `VarOK`'s disjunction.

varConstraint : ∀ {Θ n} → OCtx Θ n → Fin n → OVType Θ → Constraint Θ
varConstraint Γ i A =
  (lookup-ty Γ i ≾̂ᵥᶜ A) ∧̂ Et∨≾ᵘ (lookup-ty Γ i) (lookup-gr Γ i)

-- `genVˢ ι` and `genCˢ ι` generate for a raw term whose type and grade
-- variables `ι` interprets in the generation scope. Under a binder, `ι`
-- is composed with the binder's weakening; the recursion is structural
-- on the raw term.

mutual

  genVˢ : ∀ {Θ₀ Θ n} → Subst Θ₀ Θ → OCtx Θ n → RawV Θ₀ n → OVType Θ → Constraint Θ

  -- variables

  genVˢ ι Γ (var i) A = varConstraint Γ i A

  -- base-typed constants, unit, booleans

  genVˢ ι Γ (const B c) A = Base B ≐ᵥ A
  genVˢ ι Γ ⋆           A = Unit ≐ᵥ A
  genVˢ ι Γ true        A = Bool ≐ᵥ A
  genVˢ ι Γ false       A = Bool ≐ᵥ A

  -- natural numbers

  genVˢ ι Γ zero        A = Nat ≐ᵥ A
  genVˢ ι Γ (succ V)    A = (Nat ≐ᵥ A) ∧̂ genVˢ ι Γ V Nat

  -- pairing

  genVˢ {Θ = Θ} ι Γ ⦉ V₁ , V₂ ⦊ A =
    ∃ᵗ (∃ᵗ ((α₁ |×| α₂ ≐ᵥ A↑) ∧̂ genVˢ ι↑ Γ↑ V₁ α₁ ∧̂ genVˢ ι↑ Γ↑ V₂ α₂))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})
      A↑ = wkᵗ-v (wkᵗ-v A)
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)

  -- injections into a sum
  --
  -- As for pairing, both summands are ∃-bound and the sum they form is
  -- the expected type; the injected value is checked against its own.

  genVˢ {Θ = Θ} ι Γ (inl V) A =
    ∃ᵗ (∃ᵗ ((α₁ |+| α₂ ≐ᵥ A↑) ∧̂ genVˢ ι↑ Γ↑ V α₁))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})
      A↑ = wkᵗ-v (wkᵗ-v A)
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)

  genVˢ {Θ = Θ} ι Γ (inr V) A =
    ∃ᵗ (∃ᵗ ((α₁ |+| α₂ ≐ᵥ A↑) ∧̂ genVˢ ι↑ Γ↑ V α₂))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})
      A↑ = wkᵗ-v (wkᵗ-v A)
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)

  -- lists
  --
  -- The element type is ∃-bound and the list type it forms is the
  -- expected type; the head is checked against the element type and the
  -- tail against the list type.

  genVˢ {Θ = Θ} ι Γ nil A =
    ∃ᵗ (|List| α ≐ᵥ wkᵗ-v A)
    where
      α = tvar (newᵗ {Θ})

  genVˢ {Θ = Θ} ι Γ (cons V W) A =
    ∃ᵗ ((|List| α ≐ᵥ A↑) ∧̂ genVˢ ι↑ Γ↑ V α ∧̂ genVˢ ι↑ Γ↑ W (|List| α))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ
      α  = tvar (newᵗ {Θ})
      A↑ = wkᵗ-v A
      Γ↑ = wkᵗ-ctx Γ

  -- comparison
  --
  -- The operands' common type is ∃-bound and has to be eternal; the
  -- result is a `Bool`, pinned as for the boolean constants.

  genVˢ {Θ = Θ} ι Γ (cmp ⋈ V W) A =
    ∃ᵗ ((Bool ≐ᵥ A↑) ∧̂ genVˢ ι↑ Γ↑ V α ∧̂ genVˢ ι↑ Γ↑ W α ∧̂ Etᶜ α)
    where
      ι↑ = ι ⨟ˢ wkˢᵗ
      α  = tvar (newᵗ {Θ})
      A↑ = wkᵗ-v A
      Γ↑ = wkᵗ-ctx Γ

  -- lambda abstraction
  --
  -- The body is typed at the arrow the lambda synthesises, which is a
  -- subtype of the expected type.

  genVˢ {Θ = Θ} ι Γ (lam M) A =
    ∃ᵗ (∃ᵗ (∃ᵉ ((α₁ ⇒ (α₂ ‼ e) ≾̂ᵥᶜ A↑) ∧̂ genCˢ ι↑ (Γ↑ ∷ α₁) M (α₂ ‼ e))))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      α₁ = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      α₂ = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e  = evar (newᵉ {Θ +ty +ty})
      A↑ = wkᵉ-v (wkᵗ-v (wkᵗ-v A))
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))

  -- type annotation
  --
  -- The value is checked against the annotation, read through `ι`, which
  -- subtypes into the expected type.

  genVˢ ι Γ (V ⦂ᵛ B) A = genVˢ ι Γ V (B [ ι ]ᵛ) ∧̂ (B [ ι ]ᵛ ≾̂ᵥᶜ A)


  genCˢ : ∀ {Θ₀ Θ n} → Subst Θ₀ Θ → OCtx Θ n → RawC Θ₀ n → OCType Θ → Constraint Θ

  -- returning a value

  genCˢ ι Γ (return V) (A ‼ t) = genVˢ ι Γ V A ∧̂ (ûₑ ≾̂ₑᶜ t)

  -- sequential composition

  genCˢ {Θ = Θ} ι Γ (M₁ ⨟ M₂) (A ‼ t) =
    ∃ᵗ (∃ᵉ (∃ᵉ (  genCˢ ι↑ Γ↑ M₁ (α ‼ e₁)
                ∧̂ genCˢ ι↑ (Γ↑ ⟨ ∣ e₁ ∣̂ᵉ ⟩ ∷ α) M₂ (A↑ ‼ e₂)
                ∧̂ ((e₁ ·̂ₑ e₂) ≾̂ₑᶜ t↑))))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ ⨟ˢ wkˢᵉ
      α  = wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ})))
      e₁ = wkᵉ-e (evar (newᵉ {Θ +ty}))
      e₂ = evar (newᵉ {Θ +ty +e})
      A↑ = wkᵉ-v (wkᵉ-v (wkᵗ-v A))
      t↑ = wkᵉ-e (wkᵉ-e (wkᵗ-e t))
      Γ↑ = wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx Γ))

  -- function application
  --
  -- The function's result type is a subtype of the expected type, and
  -- its latent effect lies below the expected effect.

  genCˢ {Θ = Θ} ι Γ (V₁ · V₂) (A ‼ t) =
    ∃ᵗ (∃ᵗ (∃ᵉ (  genVˢ ι↑ Γ↑ V₁ (α ⇒ (β ‼ e))
                ∧̂ genVˢ ι↑ Γ↑ V₂ α
                ∧̂ (β ≾̂ᵥᶜ A↑)
                ∧̂ (e ≾̂ₑᶜ t↑))))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      α  = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      β  = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e  = evar (newᵉ {Θ +ty +ty})
      A↑ = wkᵉ-v (wkᵗ-v (wkᵗ-v A))
      t↑ = wkᵉ-e (wkᵗ-e (wkᵗ-e t))
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))

  -- pattern-matching

  genCˢ {Θ = Θ} ι Γ (match V `in M) (A ‼ t) =
    ∃ᵗ (∃ᵗ (genVˢ ι↑ Γ↑ V (α₁ |×| α₂) ∧̂ genCˢ ι↑ (Γ↑ ∷ α₁ ∷ α₂) M (A↑ ‼ t↑)))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})
      A↑ = wkᵗ-v (wkᵗ-v A)
      t↑ = wkᵗ-e (wkᵗ-e t)
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)

  -- empty type elimination

  genCˢ ι Γ (absurd V) C = genVˢ ι Γ V Empty

  -- boolean elimination

  genCˢ ι Γ (if V `then M₁ `else M₂) (A ‼ t) =
    genVˢ ι Γ V Bool ∧̂ genCˢ ι Γ M₁ (A ‼ t) ∧̂ genCˢ ι Γ M₂ (A ‼ t)

  -- natural-number elimination

  genCˢ ι Γ (caseℕ V `zero M₁ `succ M₂) (A ‼ t) =
    genVˢ ι Γ V Nat ∧̂ genCˢ ι Γ M₁ (A ‼ t) ∧̂ genCˢ ι (Γ ∷ Nat) M₂ (A ‼ t)

  -- sum elimination
  --
  -- The summands are ∃-bound, as the components are for `match`; both
  -- branches are checked against the expected type, as for `if`.

  genCˢ {Θ = Θ} ι Γ (case+ V `inl M₁ `inr M₂) (A ‼ t) =
    ∃ᵗ (∃ᵗ (  genVˢ ι↑ Γ↑ V (α₁ |+| α₂)
            ∧̂ genCˢ ι↑ (Γ↑ ∷ α₁) M₁ (A↑ ‼ t↑)
            ∧̂ genCˢ ι↑ (Γ↑ ∷ α₂) M₂ (A↑ ‼ t↑)))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})
      A↑ = wkᵗ-v (wkᵗ-v A)
      t↑ = wkᵗ-e (wkᵗ-e t)
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)

  -- primitive recursion on natural numbers
  --
  -- The result type, which the step also binds, and the effect are
  -- ∃-bound, below the expected type and effect, shared by the base and
  -- the step; the effect absorbs its own iteration.

  genCˢ {Θ = Θ} ι Γ (recℕ V M₁ M₂) (A ‼ t) =
    ∃ᵗ (∃ᵉ (  genVˢ ι↑ Γ↑ V Nat
            ∧̂ genCˢ ι↑ Γ↑ M₁ (β ‼ e)
            ∧̂ genCˢ ι↑ ((Γ↑ ⟨ rconst ⊤ᵣ ⟩ ∷ Nat) ⟨ ∣ e ∣̂ᵉ ⟩ ∷ β) M₂ (β ‼ e)
            ∧̂ ((e ·̂ₑ e) ≾̂ₑᶜ e)
            ∧̂ (β ≾̂ᵥᶜ A↑)
            ∧̂ (e ≾̂ₑᶜ t↑)))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      β  = wkᵉ-v (tvar (newᵗ {Θ}))
      e  = evar (newᵉ {Θ +ty})
      A↑ = wkᵉ-v (wkᵗ-v A)
      t↑ = wkᵉ-e (wkᵗ-e t)
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx Γ)

  -- list elimination
  --
  -- The element type is ∃-bound; both branches are checked against the
  -- expected type, as for `if`.

  genCˢ {Θ = Θ} ι Γ (caseL V `nil M₁ `cons M₂) (A ‼ t) =
    ∃ᵗ (  genVˢ ι↑ Γ↑ V (|List| α)
        ∧̂ genCˢ ι↑ Γ↑ M₁ (A↑ ‼ t↑)
        ∧̂ genCˢ ι↑ (Γ↑ ∷ α ∷ |List| α) M₂ (A↑ ‼ t↑))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ
      α  = tvar (newᵗ {Θ})
      A↑ = wkᵗ-v A
      t↑ = wkᵗ-e t
      Γ↑ = wkᵗ-ctx Γ

  -- primitive recursion on lists
  --
  -- As for `recℕ`, with the element type ∃-bound in addition.

  genCˢ {Θ = Θ} ι Γ (recL V M₁ M₂) (A ‼ t) =
    ∃ᵗ (∃ᵗ (∃ᵉ (  genVˢ ι↑ Γ↑ V (|List| α)
                ∧̂ genCˢ ι↑ Γ↑ M₁ (β ‼ e)
                ∧̂ genCˢ ι↑ ((Γ↑ ⟨ rconst ⊤ᵣ ⟩ ∷ α ∷ |List| α) ⟨ ∣ e ∣̂ᵉ ⟩ ∷ β) M₂ (β ‼ e)
                ∧̂ ((e ·̂ₑ e) ≾̂ₑᶜ e)
                ∧̂ (β ≾̂ᵥᶜ A↑)
                ∧̂ (e ≾̂ₑᶜ t↑))))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      α  = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      β  = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e  = evar (newᵉ {Θ +ty +ty})
      A↑ = wkᵉ-v (wkᵗ-v (wkᵗ-v A))
      t↑ = wkᵉ-e (wkᵗ-e (wkᵗ-e t))
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))

  -- performing algebraic operations

  genCˢ {Θ = Θ} ι Γ (perform op V M) (A ‼ t) =
    ∃ᵉ (  genVˢ ι↑ Γ↑ V ⌜ param op ⌝ᵍ
        ∧̂ genCˢ ι↑ (Γ↑ ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ) M (A↑ ‼ e)
        ∧̂ ((econst (op-grade op) ·̂ₑ e) ≾̂ₑᶜ t↑))
    where
      ι↑ = ι ⨟ˢ wkˢᵉ
      e  = evar (newᵉ {Θ})
      A↑ = wkᵉ-v A
      t↑ = wkᵉ-e t
      Γ↑ = wkᵉ-ctx Γ

  -- explicit delaying of a computation

  genCˢ {Θ = Θ} ι Γ (delay τ M) (A ‼ t) =
    ∃ᵉ (  genCˢ ι↑ (Γ↑ ⟨ rconst (of-durʳ τ) ⟩) M (A↑ ‼ e)
        ∧̂ ((econst (of-durᵉ τ) ·̂ₑ e) ≾̂ₑᶜ t↑))
    where
      ι↑ = ι ⨟ˢ wkˢᵉ
      e  = evar (newᵉ {Θ})
      A↑ = wkᵉ-v A
      t↑ = wkᵉ-e t
      Γ↑ = wkᵉ-ctx Γ

  -- effect handling
  --
  -- The handled result type, which occurs contravariantly in the clause
  -- contexts inside the boxed continuation, is an ∃-bound variable of its
  -- own, a subtype of the expected type, shared by the clauses and the
  -- continuation. The clause's continuation grade is the rigid variable
  -- of its `∀ᵉ`.

  genCˢ {Θ = Θ} ι Γ (handle M `with H `in N) (A ‼ t) =
    ∃ᵗ (∃ᵗ (∃ᵉ (∃ᵉ (  genCˢ ι↑ Γ↑ M (α ‼ e₁)
                    ∧̂ genCˢ ι↑ (Γ↑ ⟨ ∣ e₁ ∣̂ᵉ ⟩ ∷ α) N (γ ‼ e₂)
                    ∧̂ (γ ≾̂ᵥᶜ A↑)
                    ∧̂ ((e₁ ·̂ₑ e₂) ≾̂ₑᶜ t↑)
                    ∧̂ ⋀ᵒᵖ (λ op →
                         ∀ᵉ (genCˢ (ι↑ ↑ᵉ)
                                  (Γ⇑ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                                    ∷ [ rconst (mapᵉ (op-grade op)) ]
                                        (⌜ arity op ⌝ᵍ ⇒ γ⇑ ‼ e''))
                                  (H op)
                                  (γ⇑ ‼ (econst (op-grade op) ·̂ₑ e''))))))))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ ⨟ˢ wkˢᵉ
      α  = wkᵉ-v (wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ}))))
      γ  = wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ +ty})))
      e₁ = wkᵉ-e (evar (newᵉ {Θ +ty +ty}))
      e₂ = evar (newᵉ {Θ +ty +ty +e})
      A↑ = wkᵉ-v (wkᵉ-v (wkᵗ-v (wkᵗ-v A)))
      t↑ = wkᵉ-e (wkᵉ-e (wkᵗ-e (wkᵗ-e t)))
      Γ↑ = wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ)))
      -- and additionally under the rigid `∀ᵉ` of a clause
      e'' = evar (newᵉ {Θ +ty +ty +e +e})
      γ⇑  = wkᵉ-v (wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ +ty}))))
      Γ⇑  = wkᵉ-ctx (wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))))

  -- unboxing a boxed variable
  --
  -- The declared box type is pinned, being read off the context; the
  -- continuation binds a supertype of the payload.

  genCˢ {Θ = Θ} ι Γ (unbox i N) (A ‼ t) =
    ∃ᵗ (∃ᵗ (∃ʳ (  (lookup-ty Γ↑ i ≐ᵥ [ r ] α)
                ∧̂ (lookup-gr Γ↑ i ≾̂ᵣᶜ r)
                ∧̂ (α ≾̂ᵥᶜ β)
                ∧̂ genCˢ ι↑ (Γ↑ ∷ β) N (A↑ ‼ t↑))))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢʳ
      α  = wkʳ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      β  = wkʳ-v (tvar (newᵗ {Θ +ty}))
      r  = rvar (newʳ {Θ +ty +ty})
      A↑ = wkʳ-v (wkᵗ-v (wkᵗ-v A))
      t↑ = wkʳ-e (wkᵗ-e (wkᵗ-e t))
      Γ↑ = wkʳ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))

  -- boxing up a value
  --
  -- The grade is the term's annotation; only the payload's type is fresh.

  genCˢ {Θ = Θ} ι Γ (box ρ V N) (A ‼ t) =
    ∃ᵗ (genVˢ ι↑ (Γ↑ ⟨ r ⟩) V α ∧̂ genCˢ ι↑ (Γ↑ ∷ [ r ] α) N (A↑ ‼ t↑))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ
      r  = ρ [ ι↑ ]ʳ
      α  = tvar (newᵗ {Θ})
      A↑ = wkᵗ-v A
      t↑ = wkᵗ-e t
      Γ↑ = wkᵗ-ctx Γ

  -- type annotation
  --
  -- As for values, the subtyping split into its value and effect atoms.

  genCˢ ι Γ (M ⦂ᶜ (B ‼ u)) (A ‼ t) =
    genCˢ ι Γ M (B' ‼ u') ∧̂ (B' ≾̂ᵥᶜ A) ∧̂ (u' ≾̂ₑᶜ t)
    where
      B' = B [ ι ]ᵛ
      u' = u [ ι ]ᵉ

-- A handler-free term generates a constraint with no rigid binder

mutual

  genVˢ-rigidFree : ∀ {Θ₀ Θ n} {ι : Subst Θ₀ Θ} {Γ : OCtx Θ n} → (V : RawV Θ₀ n)
                  → {A : OVType Θ} → HandlerFreeᵛ V → RigidFree (genVˢ ι Γ V A)
  genVˢ-rigidFree (var i)      h       = tt , tt
  genVˢ-rigidFree (const B c)  h       = tt , tt
  genVˢ-rigidFree ⋆            h       = tt , tt
  genVˢ-rigidFree true         h       = tt , tt
  genVˢ-rigidFree false        h       = tt , tt
  genVˢ-rigidFree zero         h       = tt , tt
  genVˢ-rigidFree (succ V)     h       = (tt , tt) , genVˢ-rigidFree V h
  genVˢ-rigidFree ⦉ V₁ , V₂ ⦊   (h , k) = (tt , tt) , genVˢ-rigidFree V₁ h , genVˢ-rigidFree V₂ k
  genVˢ-rigidFree (inl V)      h       = (tt , tt) , genVˢ-rigidFree V h
  genVˢ-rigidFree (inr V)      h       = (tt , tt) , genVˢ-rigidFree V h
  genVˢ-rigidFree nil          h       = tt , tt
  genVˢ-rigidFree (cons V W)   (h , k) = (tt , tt) , genVˢ-rigidFree V h , genVˢ-rigidFree W k
  genVˢ-rigidFree (cmp ⋈ V W)  (h , k) = (tt , tt) , genVˢ-rigidFree V h , genVˢ-rigidFree W k , tt
  genVˢ-rigidFree (lam M)      h       = tt , genCˢ-rigidFree M h
  genVˢ-rigidFree (V ⦂ᵛ B)     h       = genVˢ-rigidFree V h , tt

  genCˢ-rigidFree : ∀ {Θ₀ Θ n} {ι : Subst Θ₀ Θ} {Γ : OCtx Θ n} → (M : RawC Θ₀ n)
                  → {C : OCType Θ} → HandlerFreeᶜ M → RigidFree (genCˢ ι Γ M C)
  genCˢ-rigidFree (return V)               {A ‼ t} h           =
    genVˢ-rigidFree V h , tt
  genCˢ-rigidFree (M₁ ⨟ M₂)                {A ‼ t} (h , k)     =
    genCˢ-rigidFree M₁ h , genCˢ-rigidFree M₂ k , tt
  genCˢ-rigidFree (V₁ · V₂)                {A ‼ t} (h , k)     =
    genVˢ-rigidFree V₁ h , genVˢ-rigidFree V₂ k , tt , tt
  genCˢ-rigidFree (match V `in M)          {A ‼ t} (h , k)     =
    genVˢ-rigidFree V h , genCˢ-rigidFree M k
  genCˢ-rigidFree (absurd V)               {A ‼ t} h           =
    genVˢ-rigidFree V h
  genCˢ-rigidFree (if V `then M₁ `else M₂) {A ‼ t} (h , k , l) =
    genVˢ-rigidFree V h , genCˢ-rigidFree M₁ k , genCˢ-rigidFree M₂ l
  genCˢ-rigidFree (caseℕ V `zero M₁ `succ M₂) {A ‼ t} (h , k , l) =
    genVˢ-rigidFree V h , genCˢ-rigidFree M₁ k , genCˢ-rigidFree M₂ l
  genCˢ-rigidFree (case+ V `inl M₁ `inr M₂) {A ‼ t} (h , k , l) =
    genVˢ-rigidFree V h , genCˢ-rigidFree M₁ k , genCˢ-rigidFree M₂ l
  genCˢ-rigidFree (recℕ V M₁ M₂)           {A ‼ t} (h , k , l) =
    genVˢ-rigidFree V h , genCˢ-rigidFree M₁ k , genCˢ-rigidFree M₂ l , tt , tt , tt
  genCˢ-rigidFree (caseL V `nil M₁ `cons M₂) {A ‼ t} (h , k , l) =
    genVˢ-rigidFree V h , genCˢ-rigidFree M₁ k , genCˢ-rigidFree M₂ l
  genCˢ-rigidFree (recL V M₁ M₂)           {A ‼ t} (h , k , l) =
    genVˢ-rigidFree V h , genCˢ-rigidFree M₁ k , genCˢ-rigidFree M₂ l , tt , tt , tt
  genCˢ-rigidFree (perform op V M)        {A ‼ t} (h , k)     =
    genVˢ-rigidFree V h , genCˢ-rigidFree M k , tt
  genCˢ-rigidFree (delay τ M)              {A ‼ t} h           =
    genCˢ-rigidFree M h , tt
  genCˢ-rigidFree (handle M `with H `in N) {A ‼ t} ()
  genCˢ-rigidFree (unbox i N)              {A ‼ t} h           =
    (tt , tt) , tt , tt , genCˢ-rigidFree N h
  genCˢ-rigidFree (box ρ V N)              {A ‼ t} (h , k)     =
    genVˢ-rigidFree V h , genCˢ-rigidFree N k
  genCˢ-rigidFree (M ⦂ᶜ (B ‼ u))           {A ‼ t} h           =
    genCˢ-rigidFree M h , tt , tt

-- Generation for a raw term over the scope of the context

genV : ∀ {Θ n} → OCtx Θ n → RawV Θ n → OVType Θ → Constraint Θ
genV = genVˢ idˢ

genC : ∀ {Θ n} → OCtx Θ n → RawC Θ n → OCType Θ → Constraint Θ
genC = genCˢ idˢ

-- Sanity checks: generation computes.

private

  -- a scope with one type variable, and a context binding it

  Θ₁ : Scope
  Θ₁ = ∅ˢ +ty

  α₀ : OVType Θ₁
  α₀ = tvar (newᵗ {∅ˢ})

  Γ₁ : OCtx Θ₁ 1
  Γ₁ = [] ∷ α₀

  -- a variable: the subtyping atom and the disjunction

  ex-var : genV Γ₁ (var zero) α₀ ≡ (α₀ ≾̂ᵥᶜ α₀) ∧̂ Et∨≾ᵘ α₀ ûᵣ
  ex-var = refl

  -- the same variable behind a clause barrier: the grade has picked up `⊤ᵣ`

  ex-var-⊤ : genV (Γ₁ ⟨ rconst ⊤ᵣ ⟩) (var zero) α₀
           ≡ (α₀ ≾̂ᵥᶜ α₀) ∧̂ Et∨≾ᵘ α₀ (ûᵣ ·̂ᵣ rconst ⊤ᵣ)
  ex-var-⊤ = refl

  -- boxing a value: the annotation is the box's grade, in the payload's
  -- context lock and in the continuation's box type

  ∅ᶜ : OCtx ∅ˢ 0
  ∅ᶜ = []

  ex-box : (c : R)
         → genC ∅ᶜ (box (rconst c) ⋆ (return (var zero))) ([ rconst c ] Unit ‼ ûₑ)
           ≡ (∃ᵗ (  (Unit ≐ᵥ α₀)
                  ∧̂ ((([ rconst c ] α₀ ≾̂ᵥᶜ [ rconst c ] Unit)
                       ∧̂ Et∨≾ᵘ ([ rconst c ] α₀) ûᵣ)
                     ∧̂ (ûₑ ≾̂ₑᶜ ûₑ))))
  ex-box c = refl
