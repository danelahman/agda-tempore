------------------------------------------------------------------
-- Constraint generation                                          --
--                                                                --
-- `genV Γ V A` and `genC Γ M C` are total functions from a raw   --
-- term and an expected (open) type to a constraint of the same   --
-- scope. They are structural on the raw term and mirror the      --
-- rules of `TypeInference.Open.Language` former by former: every     --
-- type the rule leaves free becomes a fresh `∃`-bound variable,  --
-- every side condition becomes a constraint atom.                --
--                                                                --
-- Slack invariant: the expected effect grade (`t` in `A ‼ t`) is --
-- only ever the right-hand side of a `_≾̂ₑᶜ_` — at the formers    --
-- that pin an effect (`return`, `_·_`, `_⨟_`, `perform`,         --
-- `delay`, `handle`) — or passed down unchanged. Expected value  --
-- types are pinned exactly, by `_≐ᵥ_`.                           --
--                                                                --
-- Under a binder the *arguments* of the recursive calls are      --
-- weakened (`wk*-ctx`, `wk*-v`, `wk*-c`, `wk*-e`, `wk*-r`); the  --
-- constraints themselves are built inside the innermost binder,  --
-- so `wk*-cn` is never needed.                                   --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero)
open import Data.Nat using (ℕ)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Generate (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.Open.Grades   S
open import TypeInference.Open.Types    S
open import TypeInference.Open.Contexts S

open import TypeInference.Raw.Syntax S

open import TypeInference.Constraints.Syntax S

-- The looked-up type is pinned, and its grade owes `VarOK`'s disjunction.

varConstraint : ∀ {Θ n} → OCtx Θ n → Fin n → OVType Θ → Constraint Θ
varConstraint Γ i A =
  (lookup-ty Γ i ≐ᵥ A) ∧̂ Et∨≾ᵘ (lookup-ty Γ i) (lookup-gr Γ i)

mutual

  genV : ∀ {Θ n} → OCtx Θ n → RawV n → OVType Θ → Constraint Θ

  -- variables

  genV Γ (var i) A = varConstraint Γ i A

  -- base-typed constants, unit, booleans

  genV Γ (const B c) A = Base B ≐ᵥ A
  genV Γ ⋆           A = Unit ≐ᵥ A
  genV Γ true        A = Bool ≐ᵥ A
  genV Γ false       A = Bool ≐ᵥ A

  -- pairing

  genV {Θ} Γ ⦉ V₁ , V₂ ⦊ A =
    ∃ᵗ (∃ᵗ ((α₁ |×| α₂ ≐ᵥ A↑) ∧̂ genV Γ↑ V₁ α₁ ∧̂ genV Γ↑ V₂ α₂))
    where
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})
      A↑ = wkᵗ-v (wkᵗ-v A)
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)

  -- lambda abstraction

  genV {Θ} Γ (lam M) A =
    ∃ᵗ (∃ᵗ (∃ᵉ ((α₁ ⇒ (α₂ ‼ e) ≐ᵥ A↑) ∧̂ genC (Γ↑ ∷ α₁) M (α₂ ‼ e))))
    where
      α₁ = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      α₂ = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e  = evar (newᵉ {Θ +ty +ty})
      A↑ = wkᵉ-v (wkᵗ-v (wkᵗ-v A))
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))


  genC : ∀ {Θ n} → OCtx Θ n → RawC n → OCType Θ → Constraint Θ

  -- returning a value

  genC Γ (return V) (A ‼ t) = genV Γ V A ∧̂ (ûₑ ≾̂ₑᶜ t)

  -- sequential composition

  genC {Θ} Γ (M₁ ⨟ M₂) (A ‼ t) =
    ∃ᵗ (∃ᵉ (∃ᵉ (  genC Γ↑ M₁ (α ‼ e₁)
                ∧̂ genC (Γ↑ ⟨ ∣ e₁ ∣̂ᵉ ⟩ ∷ α) M₂ (A↑ ‼ e₂)
                ∧̂ ((e₁ ·̂ₑ e₂) ≾̂ₑᶜ t↑))))
    where
      α  = wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ})))
      e₁ = wkᵉ-e (evar (newᵉ {Θ +ty}))
      e₂ = evar (newᵉ {Θ +ty +e})
      A↑ = wkᵉ-v (wkᵉ-v (wkᵗ-v A))
      t↑ = wkᵉ-e (wkᵉ-e (wkᵗ-e t))
      Γ↑ = wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx Γ))

  -- function application

  genC {Θ} Γ (V₁ · V₂) (A ‼ t) =
    ∃ᵗ (∃ᵉ (genV Γ↑ V₁ (α ⇒ (A↑ ‼ e)) ∧̂ genV Γ↑ V₂ α ∧̂ (e ≾̂ₑᶜ t↑)))
    where
      α  = wkᵉ-v (tvar (newᵗ {Θ}))
      e  = evar (newᵉ {Θ +ty})
      A↑ = wkᵉ-v (wkᵗ-v A)
      t↑ = wkᵉ-e (wkᵗ-e t)
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx Γ)

  -- pattern-matching

  genC {Θ} Γ (match V `in M) (A ‼ t) =
    ∃ᵗ (∃ᵗ (genV Γ↑ V (α₁ |×| α₂) ∧̂ genC (Γ↑ ∷ α₁ ∷ α₂) M (A↑ ‼ t↑)))
    where
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})
      A↑ = wkᵗ-v (wkᵗ-v A)
      t↑ = wkᵗ-e (wkᵗ-e t)
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)

  -- empty type elimination

  genC Γ (absurd V) C = genV Γ V Empty

  -- boolean elimination

  genC Γ (if V `then M₁ `else M₂) (A ‼ t) =
    genV Γ V Bool ∧̂ genC Γ M₁ (A ‼ t) ∧̂ genC Γ M₂ (A ‼ t)

  -- performing algebraic operations

  genC {Θ} Γ (perform op V M) (A ‼ t) =
    ∃ᵉ (  genV Γ↑ V ⌜ param op ⌝ᵍ
        ∧̂ genC (Γ↑ ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ) M (A↑ ‼ e)
        ∧̂ ((econst (op-grade op) ·̂ₑ e) ≾̂ₑᶜ t↑))
    where
      e  = evar (newᵉ {Θ})
      A↑ = wkᵉ-v A
      t↑ = wkᵉ-e t
      Γ↑ = wkᵉ-ctx Γ

  -- explicit delaying of a computation

  genC {Θ} Γ (delay τ M) (A ‼ t) =
    ∃ᵉ (  genC (Γ↑ ⟨ rconst (of-natʳ τ) ⟩) M (A↑ ‼ e)
        ∧̂ ((econst (of-natᵉ τ) ·̂ₑ e) ≾̂ₑᶜ t↑))
    where
      e  = evar (newᵉ {Θ})
      A↑ = wkᵉ-v A
      t↑ = wkᵉ-e t
      Γ↑ = wkᵉ-ctx Γ

  -- effect handling

  genC {Θ} Γ (handle M `with H `in N) (A ‼ t) =
    ∃ᵗ (∃ᵉ (∃ᵉ (  genC Γ↑ M (α ‼ e₁)
                ∧̂ genC (Γ↑ ⟨ ∣ e₁ ∣̂ᵉ ⟩ ∷ α) N (A↑ ‼ e₂)
                ∧̂ ((e₁ ·̂ₑ e₂) ≾̂ₑᶜ t↑)
                ∧̂ ⋀ᵒᵖ (λ op →
                     ∀ᵉ (genC (Γ⇑ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                                ∷ [ rconst (mapᵉ (op-grade op)) ]
                                    (⌜ arity op ⌝ᵍ ⇒ A⇑ ‼ e''))
                              (H op)
                              (A⇑ ‼ (econst (op-grade op) ·̂ₑ e'')))))))
    where
      α  = wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ})))
      e₁ = wkᵉ-e (evar (newᵉ {Θ +ty}))
      e₂ = evar (newᵉ {Θ +ty +e})
      A↑ = wkᵉ-v (wkᵉ-v (wkᵗ-v A))
      t↑ = wkᵉ-e (wkᵉ-e (wkᵗ-e t))
      Γ↑ = wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx Γ))
      -- and additionally under the rigid `∀ᵉ` of a clause
      e'' = evar (newᵉ {Θ +ty +e +e})
      A⇑  = wkᵉ-v (wkᵉ-v (wkᵉ-v (wkᵗ-v A)))
      Γ⇑  = wkᵉ-ctx (wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx Γ)))

  -- unboxing a boxed variable

  genC {Θ} Γ (unbox i N) (A ‼ t) =
    ∃ᵗ (∃ʳ (  (lookup-ty Γ↑ i ≐ᵥ [ r ] α)
            ∧̂ (lookup-gr Γ↑ i ≾̂ᵣᶜ r)
            ∧̂ genC (Γ↑ ∷ α) N (A↑ ‼ t↑)))
    where
      α  = wkʳ-v (tvar (newᵗ {Θ}))
      r  = rvar (newʳ {Θ +ty})
      A↑ = wkʳ-v (wkᵗ-v A)
      t↑ = wkʳ-e (wkᵗ-e t)
      Γ↑ = wkʳ-ctx (wkᵗ-ctx Γ)

  -- boxing up a value

  genC {Θ} Γ (box V N) (A ‼ t) =
    ∃ᵗ (∃ʳ (genV (Γ↑ ⟨ r ⟩) V α ∧̂ genC (Γ↑ ∷ [ r ] α) N (A↑ ‼ t↑)))
    where
      α  = wkʳ-v (tvar (newᵗ {Θ}))
      r  = rvar (newʳ {Θ +ty})
      A↑ = wkʳ-v (wkᵗ-v A)
      t↑ = wkʳ-e (wkᵗ-e t)
      Γ↑ = wkʳ-ctx (wkᵗ-ctx Γ)

-- Sanity checks: generation computes.

private

  -- a scope with one type variable, and a context binding it

  Θ₁ : Scope
  Θ₁ = ∅ˢ +ty

  α₀ : OVType Θ₁
  α₀ = tvar (newᵗ {∅ˢ})

  Γ₁ : OCtx Θ₁ 1
  Γ₁ = [] ∷ α₀

  -- a variable: the type equation and the disjunction

  ex-var : genV Γ₁ (var zero) α₀ ≡ (α₀ ≐ᵥ α₀) ∧̂ Et∨≾ᵘ α₀ ûᵣ
  ex-var = refl

  -- the same variable behind a clause barrier: the grade has picked up `⊤ᵣ`

  ex-var-⊤ : genV (Γ₁ ⟨ rconst ⊤ᵣ ⟩) (var zero) α₀
           ≡ (α₀ ≐ᵥ α₀) ∧̂ Et∨≾ᵘ α₀ (ûᵣ ·̂ᵣ rconst ⊤ᵣ)
  ex-var-⊤ = refl
