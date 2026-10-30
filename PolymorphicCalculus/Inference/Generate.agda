------------------------------------------------------------------
-- Constraint generation                                        --
--                                                              --
-- `genV Γ V A` and `genC Γ M C` map a raw term and an expected --
-- open type to a constraint, structurally on the term and rule --
-- by rule: each type a rule leaves undetermined is ∃-bound,    --
-- each side condition an atom. The expected type is an upper   --
-- bound: where a rule meets two undetermined types it is the   --
-- right side of a `_≾̂ᵥᶜ_` or `_≾̂ₑᶜ_` atom; elsewhere `_≐ᵥ_`  --
-- fixes its shape. A use of a definition owes the constraint   --
-- of its scheme (`instᶜ`), an unbound position the             --
-- unsatisfiable one.                                           --
--                                                              --
-- Contract. `σ ⊨[ Q ] genC Γ M (A ‼ t)` holds exactly when     --
-- some derivation of `Q ∣ Γ [ σ ] ⊢C⦂ (A ‼ t) [ σ ]` erases to --
-- `M [ σ ]` (`charV`, `charC`).                                --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Data.List.Base using ([])
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.Generate (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.Contexts          S
open import PolymorphicCalculus.Syntax.GradeSubstitution S

open import PolymorphicCalculus.Syntax.Raw S
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution S using (_[_]ᴿᵛ; _[_]ᴿᶜ)
open import PolymorphicCalculus.Hypotheses S using (qhyps)

open import PolymorphicCalculus.Inference.Constraints.Syntax  S
open import PolymorphicCalculus.Inference.Constraints.Schemes S using (instᶜ; instᶜ-rigidFree)

-- The looked-up type subtypes into the expected one; its grade owes `VarOK`'s
-- disjunction

varConstraint : ∀ {Θ n} → OCtx Θ n → Fin n → OVType Θ → Constraint Θ
varConstraint Γ i A =
  (lookup-ty Γ i ≾̂ᵥᶜ A) ∧̂ Et∨≾ᵘ (lookup-ty Γ i) (lookup-gr Γ i)

-- A use of a definition: of its scheme, if there is one

useDefConstraint : ∀ {Θ} → Maybe Scheme → OVType Θ → Constraint Θ
useDefConstraint nothing  A = ⊥̂
useDefConstraint (just s) A = instᶜ s A

-- An `unbox` of a variable under annotations: the type it reaches, its grade,
-- and each annotation's subtyping atom; any other value is unsatisfiable

resTy : ∀ {Θ₀ Θ n} → Subst Θ₀ Θ → OCtx Θ n → RawV Θ₀ n → OVType Θ
resTy ι Γ (var i)  = lookup-ty Γ i
resTy ι Γ (V ⦂ᵛ B) = B [ ι ]ᵛ
resTy ι Γ _        = Unit

resGr : ∀ {Θ₀ Θ n} → OCtx Θ n → RawV Θ₀ n → RExp Θ
resGr Γ (var i)  = lookup-gr Γ i
resGr Γ (V ⦂ᵛ B) = resGr Γ V
resGr Γ _        = ûᵣ

resC : ∀ {Θ₀ Θ n} → Subst Θ₀ Θ → OCtx Θ n → RawV Θ₀ n → Constraint Θ
resC ι Γ (var i)  = ⊤̂
resC ι Γ (V ⦂ᵛ B) = resC ι Γ V ∧̂ (resTy ι Γ V ≾̂ᵥᶜ B [ ι ]ᵛ)
resC ι Γ _        = ⊥̂

-- `genVˢ ι` and `genCˢ ι` generate for a raw term whose type and grade variables
-- `ι` interprets; under a binder `ι` is composed with the weakening

mutual

  genVˢ : ∀ {Θ₀ Θ n} → Subst Θ₀ Θ → OCtx Θ n → RawV Θ₀ n → OVType Θ → Constraint Θ

  -- variables

  genVˢ ι Γ (var i) A = varConstraint Γ i A

  -- uses of definitions

  genVˢ ι Γ (usedef k) A = useDefConstraint (lookupᵖ (defs Γ) k) A

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

  -- injections into a sum: both summands ∃-bound, their sum the expected type

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

  -- lists: the element type ∃-bound, its list type the expected type

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

  -- comparison: the operands' type ∃-bound and eternal, the result `Bool`

  genVˢ {Θ = Θ} ι Γ (cmp ⋈ V W) A =
    ∃ᵗ ((Bool ≐ᵥ A↑) ∧̂ genVˢ ι↑ Γ↑ V α ∧̂ genVˢ ι↑ Γ↑ W α ∧̂ Etᶜ α)
    where
      ι↑ = ι ⨟ˢ wkˢᵗ
      α  = tvar (newᵗ {Θ})
      A↑ = wkᵗ-v A
      Γ↑ = wkᵗ-ctx Γ

  -- lambda abstraction: the body at the synthesised arrow, below the expected type

  genVˢ {Θ = Θ} ι Γ (lam M) A =
    ∃ᵗ (∃ᵗ (∃ᵉ ((α₁ ⇒ (α₂ ‼ e) ≾̂ᵥᶜ A↑) ∧̂ genCˢ ι↑ (Γ↑ ∷ α₁) M (α₂ ‼ e))))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      α₁ = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      α₂ = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e  = evar (newᵉ {Θ +ty +ty})
      A↑ = wkᵉ-v (wkᵗ-v (wkᵗ-v A))
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))

  -- handlers: at the synthesised handler type, below the expected one; the
  -- result type is ∃-bound and shared by all clauses, and a clause's
  -- continuation grade is the rigid of its `∀ᵉ`

  genVˢ {Θ = Θ} ι Γ (handler N H) A =
    ∃ᵗ (∃ᵗ (∃ᵉ (∃ᵉ (  ((α ‼ e₁) ⇛ (γ ‼ e₂) ≾̂ᵥᶜ A↑)
                    ∧̂ genCˢ ι↑ (Γ↑ ⟨ ∣ e₁ ∣̂ᵉ ⟩ ∷ α) N (γ ‼ e₂)
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
      Γ↑ = wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ)))
      -- and additionally under the rigid `∀ᵉ` of a clause
      e'' = evar (newᵉ {Θ +ty +ty +e +e})
      γ⇑  = wkᵉ-v (wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ +ty}))))
      Γ⇑  = wkᵉ-ctx (wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))))

  -- type annotation: the value checked against the annotation, below the
  -- expected type

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

  -- function application: the result type and latent effect below the expected

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

  -- sum elimination: the summands ∃-bound, both branches at the expected type

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

  -- primitive recursion on natural numbers: the result type and effect
  -- ∃-bound below the expected ones, the effect absorbing its own iteration

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

  -- list elimination: the element type ∃-bound, both branches at the expected type

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

  -- primitive recursion on lists: as for `recℕ`, the element type ∃-bound too

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

  -- effect handling: the handled type and the handler's result type ∃-bound,
  -- the result below the expected type and effect

  genCˢ {Θ = Θ} ι Γ (handle M `with V) (A ‼ t) =
    ∃ᵗ (∃ᵗ (∃ᵉ (∃ᵉ (  genCˢ ι↑ Γ↑ M (α ‼ e₁)
                    ∧̂ genVˢ ι↑ Γ↑ V ((α ‼ e₁) ⇛ (γ ‼ e₂))
                    ∧̂ (γ ≾̂ᵥᶜ A↑)
                    ∧̂ ((e₁ ·̂ₑ e₂) ≾̂ₑᶜ t↑)))))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ ⨟ˢ wkˢᵉ
      α  = wkᵉ-v (wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ}))))
      γ  = wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ +ty})))
      e₁ = wkᵉ-e (evar (newᵉ {Θ +ty +ty}))
      e₂ = evar (newᵉ {Θ +ty +ty +e})
      A↑ = wkᵉ-v (wkᵉ-v (wkᵗ-v (wkᵗ-v A)))
      t↑ = wkᵉ-e (wkᵉ-e (wkᵗ-e (wkᵗ-e t)))
      Γ↑ = wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ)))

  -- unboxing a resource value: it reaches a box of ∃-bound grade and payload,
  -- the grade above the one accumulated at its variable

  genCˢ {Θ = Θ} ι Γ (unbox V N) (A ‼ t) =
    ∃ᵗ (∃ʳ (  resC ι↑ Γ↑ V
            ∧̂ (resTy ι↑ Γ↑ V ≐ᵥ [ r ] β)
            ∧̂ (resGr Γ↑ V ≾̂ᵣᶜ r)
            ∧̂ genCˢ ι↑ (Γ↑ ∷ β) N (A↑ ‼ t↑)))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢʳ
      β  = wkʳ-v (tvar (newᵗ {Θ}))
      r  = rvar (newʳ {Θ +ty})
      A↑ = wkʳ-v (wkᵗ-v A)
      t↑ = wkʳ-e (wkᵗ-e t)
      Γ↑ = wkʳ-ctx (wkᵗ-ctx Γ)

  -- boxing up a value: the grade is the annotation, only the payload's type fresh

  genCˢ {Θ = Θ} ι Γ (box ρ V N) (A ‼ t) =
    ∃ᵗ (genVˢ ι↑ (Γ↑ ⟨ r ⟩) V α ∧̂ genCˢ ι↑ (Γ↑ ∷ [ r ] α) N (A↑ ‼ t↑))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ
      r  = ρ [ ι↑ ]ʳ
      α  = tvar (newᵗ {Θ})
      A↑ = wkᵗ-v A
      t↑ = wkᵗ-e t
      Γ↑ = wkᵗ-ctx Γ

  -- type annotation: as for values, split into value and effect atoms

  genCˢ ι Γ (M ⦂ᶜ (B ‼ u)) (A ‼ t) =
    genCˢ ι Γ M (B' ‼ u') ∧̂ (B' ≾̂ᵥᶜ A) ∧̂ (u' ≾̂ₑᶜ t)
    where
      B' = B [ ι ]ᵛ
      u' = u [ ι ]ᵉ

-- A handler-free term using no definition with quantified hypotheses
-- (`NoRigidᵛ Δ V`) generates a constraint with no rigid binder

-- The definition at a position has no quantified hypotheses

UnquantifiedAt : PCtx → ℕ → Set
UnquantifiedAt Δ k = ∀ {s} → s ∈ᵖ[ k ] Δ → qhyps (Qˢ s) ≡ []

mutual

  NoRigidᵛ : ∀ {Θ n} → PCtx → RawV Θ n → Set
  NoRigidᵛ Δ (usedef k)    = UnquantifiedAt Δ k
  NoRigidᵛ Δ (succ V)      = NoRigidᵛ Δ V
  NoRigidᵛ Δ ⦉ V , W ⦊      = NoRigidᵛ Δ V × NoRigidᵛ Δ W
  NoRigidᵛ Δ (inl V)       = NoRigidᵛ Δ V
  NoRigidᵛ Δ (inr V)       = NoRigidᵛ Δ V
  NoRigidᵛ Δ (cons V W)    = NoRigidᵛ Δ V × NoRigidᵛ Δ W
  NoRigidᵛ Δ (cmp ⋈ V W)   = NoRigidᵛ Δ V × NoRigidᵛ Δ W
  NoRigidᵛ Δ (lam M)       = NoRigidᶜ Δ M
  NoRigidᵛ Δ (handler N H) = ⊥
  NoRigidᵛ Δ (V ⦂ᵛ A)      = NoRigidᵛ Δ V
  NoRigidᵛ Δ _             = ⊤

  NoRigidᶜ : ∀ {Θ n} → PCtx → RawC Θ n → Set
  NoRigidᶜ Δ (return V)                = NoRigidᵛ Δ V
  NoRigidᶜ Δ (M ⨟ N)                   = NoRigidᶜ Δ M × NoRigidᶜ Δ N
  NoRigidᶜ Δ (V · W)                   = NoRigidᵛ Δ V × NoRigidᵛ Δ W
  NoRigidᶜ Δ (match V `in M)           = NoRigidᵛ Δ V × NoRigidᶜ Δ M
  NoRigidᶜ Δ (absurd V)                = NoRigidᵛ Δ V
  NoRigidᶜ Δ (if V `then M `else N)    = NoRigidᵛ Δ V × NoRigidᶜ Δ M × NoRigidᶜ Δ N
  NoRigidᶜ Δ (caseℕ V `zero M `succ N) = NoRigidᵛ Δ V × NoRigidᶜ Δ M × NoRigidᶜ Δ N
  NoRigidᶜ Δ (case+ V `inl M `inr N)   = NoRigidᵛ Δ V × NoRigidᶜ Δ M × NoRigidᶜ Δ N
  NoRigidᶜ Δ (recℕ V M N)              = NoRigidᵛ Δ V × NoRigidᶜ Δ M × NoRigidᶜ Δ N
  NoRigidᶜ Δ (caseL V `nil M `cons N)  = NoRigidᵛ Δ V × NoRigidᶜ Δ M × NoRigidᶜ Δ N
  NoRigidᶜ Δ (recL V M N)              = NoRigidᵛ Δ V × NoRigidᶜ Δ M × NoRigidᶜ Δ N
  NoRigidᶜ Δ (perform op V M)          = NoRigidᵛ Δ V × NoRigidᶜ Δ M
  NoRigidᶜ Δ (delay τ M)               = NoRigidᶜ Δ M
  NoRigidᶜ Δ (handle M `with V)        = NoRigidᶜ Δ M × NoRigidᵛ Δ V
  NoRigidᶜ Δ (unbox V N)               = NoRigidᵛ Δ V × NoRigidᶜ Δ N
  NoRigidᶜ Δ (box ρ V N)               = NoRigidᵛ Δ V × NoRigidᶜ Δ N
  NoRigidᶜ Δ (M ⦂ᶜ C)                  = NoRigidᶜ Δ M

-- A handler-free term in a program context without quantified
-- hypotheses has none

unquantified-at : ∀ {Δ} → Unquantified Δ → ∀ k → UnquantifiedAt Δ k
unquantified-at u k f = unquantified-∈ u f

mutual

  handlerFree-noRigidᵛ : ∀ {Θ n Δ} → Unquantified Δ → (V : RawV Θ n)
                       → HandlerFreeᵛ V → NoRigidᵛ Δ V
  handlerFree-noRigidᵛ u (var i)      h       = tt
  handlerFree-noRigidᵛ u (usedef k)   h       = unquantified-at u k
  handlerFree-noRigidᵛ u (const B c)  h       = tt
  handlerFree-noRigidᵛ u ⋆            h       = tt
  handlerFree-noRigidᵛ u true         h       = tt
  handlerFree-noRigidᵛ u false        h       = tt
  handlerFree-noRigidᵛ u zero         h       = tt
  handlerFree-noRigidᵛ u (succ V)     h       = handlerFree-noRigidᵛ u V h
  handlerFree-noRigidᵛ u ⦉ V , W ⦊     (h , k) = handlerFree-noRigidᵛ u V h , handlerFree-noRigidᵛ u W k
  handlerFree-noRigidᵛ u (inl V)      h       = handlerFree-noRigidᵛ u V h
  handlerFree-noRigidᵛ u (inr V)      h       = handlerFree-noRigidᵛ u V h
  handlerFree-noRigidᵛ u nil          h       = tt
  handlerFree-noRigidᵛ u (cons V W)   (h , k) = handlerFree-noRigidᵛ u V h , handlerFree-noRigidᵛ u W k
  handlerFree-noRigidᵛ u (cmp ⋈ V W)  (h , k) = handlerFree-noRigidᵛ u V h , handlerFree-noRigidᵛ u W k
  handlerFree-noRigidᵛ u (lam M)      h       = handlerFree-noRigidᶜ u M h
  handlerFree-noRigidᵛ u (handler N H) ()
  handlerFree-noRigidᵛ u (V ⦂ᵛ A)     h       = handlerFree-noRigidᵛ u V h

  handlerFree-noRigidᶜ : ∀ {Θ n Δ} → Unquantified Δ → (M : RawC Θ n)
                       → HandlerFreeᶜ M → NoRigidᶜ Δ M
  handlerFree-noRigidᶜ u (return V)               h           = handlerFree-noRigidᵛ u V h
  handlerFree-noRigidᶜ u (M ⨟ N)                  (h , k)     =
    handlerFree-noRigidᶜ u M h , handlerFree-noRigidᶜ u N k
  handlerFree-noRigidᶜ u (V · W)                  (h , k)     =
    handlerFree-noRigidᵛ u V h , handlerFree-noRigidᵛ u W k
  handlerFree-noRigidᶜ u (match V `in M)          (h , k)     =
    handlerFree-noRigidᵛ u V h , handlerFree-noRigidᶜ u M k
  handlerFree-noRigidᶜ u (absurd V)               h           = handlerFree-noRigidᵛ u V h
  handlerFree-noRigidᶜ u (if V `then M `else N)   (h , k , l) =
    handlerFree-noRigidᵛ u V h , handlerFree-noRigidᶜ u M k , handlerFree-noRigidᶜ u N l
  handlerFree-noRigidᶜ u (caseℕ V `zero M `succ N) (h , k , l) =
    handlerFree-noRigidᵛ u V h , handlerFree-noRigidᶜ u M k , handlerFree-noRigidᶜ u N l
  handlerFree-noRigidᶜ u (case+ V `inl M `inr N)  (h , k , l) =
    handlerFree-noRigidᵛ u V h , handlerFree-noRigidᶜ u M k , handlerFree-noRigidᶜ u N l
  handlerFree-noRigidᶜ u (recℕ V M N)             (h , k , l) =
    handlerFree-noRigidᵛ u V h , handlerFree-noRigidᶜ u M k , handlerFree-noRigidᶜ u N l
  handlerFree-noRigidᶜ u (caseL V `nil M `cons N) (h , k , l) =
    handlerFree-noRigidᵛ u V h , handlerFree-noRigidᶜ u M k , handlerFree-noRigidᶜ u N l
  handlerFree-noRigidᶜ u (recL V M N)             (h , k , l) =
    handlerFree-noRigidᵛ u V h , handlerFree-noRigidᶜ u M k , handlerFree-noRigidᶜ u N l
  handlerFree-noRigidᶜ u (perform op V M)         (h , k)     =
    handlerFree-noRigidᵛ u V h , handlerFree-noRigidᶜ u M k
  handlerFree-noRigidᶜ u (delay τ M)              h           = handlerFree-noRigidᶜ u M h
  handlerFree-noRigidᶜ u (handle M `with V)       (h , k)     =
    handlerFree-noRigidᶜ u M h , handlerFree-noRigidᵛ u V k
  handlerFree-noRigidᶜ u (unbox V N)              (h , k)     =
    handlerFree-noRigidᵛ u V h , handlerFree-noRigidᶜ u N k
  handlerFree-noRigidᶜ u (box ρ V N)              (h , k)     =
    handlerFree-noRigidᵛ u V h , handlerFree-noRigidᶜ u N k
  handlerFree-noRigidᶜ u (M ⦂ᶜ C)                 h           = handlerFree-noRigidᶜ u M h

-- Substitution keeps it

mutual

  noRigid-[]ᴿᵛ : ∀ {Θ Θ' n Δ} {σ : Subst Θ Θ'} → (V : RawV Θ n)
               → NoRigidᵛ Δ V → NoRigidᵛ Δ (V [ σ ]ᴿᵛ)
  noRigid-[]ᴿᵛ (var i)      h       = tt
  noRigid-[]ᴿᵛ (usedef k)   h       = h
  noRigid-[]ᴿᵛ (const B c)  h       = tt
  noRigid-[]ᴿᵛ ⋆            h       = tt
  noRigid-[]ᴿᵛ true         h       = tt
  noRigid-[]ᴿᵛ false        h       = tt
  noRigid-[]ᴿᵛ zero         h       = tt
  noRigid-[]ᴿᵛ (succ V)     h       = noRigid-[]ᴿᵛ V h
  noRigid-[]ᴿᵛ (inl V)      h       = noRigid-[]ᴿᵛ V h
  noRigid-[]ᴿᵛ (inr V)      h       = noRigid-[]ᴿᵛ V h
  noRigid-[]ᴿᵛ nil          h       = tt
  noRigid-[]ᴿᵛ (cons V W)   (h , k) = noRigid-[]ᴿᵛ V h , noRigid-[]ᴿᵛ W k
  noRigid-[]ᴿᵛ (cmp ⋈ V W)  (h , k) = noRigid-[]ᴿᵛ V h , noRigid-[]ᴿᵛ W k
  noRigid-[]ᴿᵛ ⦉ V , W ⦊     (h , k) = noRigid-[]ᴿᵛ V h , noRigid-[]ᴿᵛ W k
  noRigid-[]ᴿᵛ (lam M)      h       = noRigid-[]ᴿᶜ M h
  noRigid-[]ᴿᵛ (handler N H) ()
  noRigid-[]ᴿᵛ (V ⦂ᵛ A)     h       = noRigid-[]ᴿᵛ V h

  noRigid-[]ᴿᶜ : ∀ {Θ Θ' n Δ} {σ : Subst Θ Θ'} → (M : RawC Θ n)
               → NoRigidᶜ Δ M → NoRigidᶜ Δ (M [ σ ]ᴿᶜ)
  noRigid-[]ᴿᶜ (return V)               h           = noRigid-[]ᴿᵛ V h
  noRigid-[]ᴿᶜ (M ⨟ N)                  (h , k)     = noRigid-[]ᴿᶜ M h , noRigid-[]ᴿᶜ N k
  noRigid-[]ᴿᶜ (V · W)                  (h , k)     = noRigid-[]ᴿᵛ V h , noRigid-[]ᴿᵛ W k
  noRigid-[]ᴿᶜ (match V `in M)          (h , k)     = noRigid-[]ᴿᵛ V h , noRigid-[]ᴿᶜ M k
  noRigid-[]ᴿᶜ (absurd V)               h           = noRigid-[]ᴿᵛ V h
  noRigid-[]ᴿᶜ (if V `then M `else N)   (h , k , l) =
    noRigid-[]ᴿᵛ V h , noRigid-[]ᴿᶜ M k , noRigid-[]ᴿᶜ N l
  noRigid-[]ᴿᶜ (caseℕ V `zero M `succ N) (h , k , l) =
    noRigid-[]ᴿᵛ V h , noRigid-[]ᴿᶜ M k , noRigid-[]ᴿᶜ N l
  noRigid-[]ᴿᶜ (case+ V `inl M `inr N)  (h , k , l) =
    noRigid-[]ᴿᵛ V h , noRigid-[]ᴿᶜ M k , noRigid-[]ᴿᶜ N l
  noRigid-[]ᴿᶜ (recℕ V M N)             (h , k , l) =
    noRigid-[]ᴿᵛ V h , noRigid-[]ᴿᶜ M k , noRigid-[]ᴿᶜ N l
  noRigid-[]ᴿᶜ (caseL V `nil M `cons N) (h , k , l) =
    noRigid-[]ᴿᵛ V h , noRigid-[]ᴿᶜ M k , noRigid-[]ᴿᶜ N l
  noRigid-[]ᴿᶜ (recL V M N)             (h , k , l) =
    noRigid-[]ᴿᵛ V h , noRigid-[]ᴿᶜ M k , noRigid-[]ᴿᶜ N l
  noRigid-[]ᴿᶜ (perform op V M)         (h , k)     = noRigid-[]ᴿᵛ V h , noRigid-[]ᴿᶜ M k
  noRigid-[]ᴿᶜ (delay τ M)              h           = noRigid-[]ᴿᶜ M h
  noRigid-[]ᴿᶜ (handle M `with V)       (h , k)     = noRigid-[]ᴿᶜ M h , noRigid-[]ᴿᵛ V k
  noRigid-[]ᴿᶜ (unbox V N)              (h , k)     = noRigid-[]ᴿᵛ V h , noRigid-[]ᴿᶜ N k
  noRigid-[]ᴿᶜ (box ρ V N)              (h , k)     = noRigid-[]ᴿᵛ V h , noRigid-[]ᴿᶜ N k
  noRigid-[]ᴿᶜ (M ⦂ᶜ C)                 h           = noRigid-[]ᴿᶜ M h

-- The constraint has no rigid binder, the program context being the hypothesis's

private

  eᵗ : ∀ {Θ n Δ} → (Γ : OCtx Θ n) → defs Γ ≡ Δ → defs (wkᵗ-ctx Γ) ≡ Δ
  eᵗ Γ e = trans (defs-wkᵗ Γ) e

  eʳ : ∀ {Θ n Δ} → (Γ : OCtx Θ n) → defs Γ ≡ Δ → defs (wkʳ-ctx Γ) ≡ Δ
  eʳ Γ e = trans (defs-wkʳ Γ) e

  eᵉ : ∀ {Θ n Δ} → (Γ : OCtx Θ n) → defs Γ ≡ Δ → defs (wkᵉ-ctx Γ) ≡ Δ
  eᵉ Γ e = trans (defs-wkᵉ Γ) e

  eᵗᵗ : ∀ {Θ n Δ} → (Γ : OCtx Θ n) → defs Γ ≡ Δ → defs (wkᵗ-ctx (wkᵗ-ctx Γ)) ≡ Δ
  eᵗᵗ Γ e = eᵗ (wkᵗ-ctx Γ) (eᵗ Γ e)

  eᵗᵉ : ∀ {Θ n Δ} → (Γ : OCtx Θ n) → defs Γ ≡ Δ → defs (wkᵉ-ctx (wkᵗ-ctx Γ)) ≡ Δ
  eᵗᵉ Γ e = eᵉ (wkᵗ-ctx Γ) (eᵗ Γ e)

  eᵗᵗᵉ : ∀ {Θ n Δ} → (Γ : OCtx Θ n) → defs Γ ≡ Δ
       → defs (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))) ≡ Δ
  eᵗᵗᵉ Γ e = eᵉ (wkᵗ-ctx (wkᵗ-ctx Γ)) (eᵗᵗ Γ e)

  eᵗᵉᵉ : ∀ {Θ n Δ} → (Γ : OCtx Θ n) → defs Γ ≡ Δ
       → defs (wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx Γ))) ≡ Δ
  eᵗᵉᵉ Γ e = eᵉ (wkᵉ-ctx (wkᵗ-ctx Γ)) (eᵗᵉ Γ e)

  eᵗᵗᵉᵉ : ∀ {Θ n Δ} → (Γ : OCtx Θ n) → defs Γ ≡ Δ
        → defs (wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ)))) ≡ Δ
  eᵗᵗᵉᵉ Γ e = eᵉ (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))) (eᵗᵗᵉ Γ e)

  eᵗʳ : ∀ {Θ n Δ} → (Γ : OCtx Θ n) → defs Γ ≡ Δ → defs (wkʳ-ctx (wkᵗ-ctx Γ)) ≡ Δ
  eᵗʳ Γ e = eʳ (wkᵗ-ctx Γ) (eᵗ Γ e)

  resC-rigidFree : ∀ {Θ₀ Θ n} {ι : Subst Θ₀ Θ} {Γ : OCtx Θ n} → (V : RawV Θ₀ n)
                 → RigidFree (resC ι Γ V)
  resC-rigidFree (var i)       = tt
  resC-rigidFree (V ⦂ᵛ B)      = resC-rigidFree V , tt
  resC-rigidFree (usedef k)    = tt
  resC-rigidFree (const B c)   = tt
  resC-rigidFree ⋆             = tt
  resC-rigidFree true          = tt
  resC-rigidFree false         = tt
  resC-rigidFree zero          = tt
  resC-rigidFree (succ V)      = tt
  resC-rigidFree ⦉ V , W ⦊      = tt
  resC-rigidFree (inl V)       = tt
  resC-rigidFree (inr V)       = tt
  resC-rigidFree nil           = tt
  resC-rigidFree (cons V W)    = tt
  resC-rigidFree (cmp ⋈ V W)   = tt
  resC-rigidFree (lam M)       = tt
  resC-rigidFree (handler N H) = tt

  useDefConstraint-rigidFree : ∀ {Θ} → (Δ : PCtx) → (k : ℕ) → UnquantifiedAt Δ k
                             → (A : OVType Θ) → RigidFree (useDefConstraint (lookupᵖ Δ k) A)
  useDefConstraint-rigidFree Δ k u A with lookupᵖ Δ k in eq
  ... | nothing = tt
  ... | just s  = instᶜ-rigidFree s A (u (lookupᵖ-∈ Δ eq))

mutual

  genVˢ-rigidFree : ∀ {Θ₀ Θ n Δ} {ι : Subst Θ₀ Θ} {Γ : OCtx Θ n} → defs Γ ≡ Δ
                  → (V : RawV Θ₀ n) → {A : OVType Θ} → NoRigidᵛ Δ V
                  → RigidFree (genVˢ ι Γ V A)
  genVˢ-rigidFree e (var i)      h       = tt , tt
  genVˢ-rigidFree e (usedef k) {A} h rewrite e = useDefConstraint-rigidFree _ k h A
  genVˢ-rigidFree e (const B c)  h       = tt , tt
  genVˢ-rigidFree e ⋆            h       = tt , tt
  genVˢ-rigidFree e true         h       = tt , tt
  genVˢ-rigidFree e false        h       = tt , tt
  genVˢ-rigidFree e zero         h       = tt , tt
  genVˢ-rigidFree e (succ V)     h       = (tt , tt) , genVˢ-rigidFree e V h
  genVˢ-rigidFree {Γ = Γ} e ⦉ V₁ , V₂ ⦊ (h , k) =
    (tt , tt) , genVˢ-rigidFree (eᵗᵗ Γ e) V₁ h , genVˢ-rigidFree (eᵗᵗ Γ e) V₂ k
  genVˢ-rigidFree {Γ = Γ} e (inl V) h = (tt , tt) , genVˢ-rigidFree (eᵗᵗ Γ e) V h
  genVˢ-rigidFree {Γ = Γ} e (inr V) h = (tt , tt) , genVˢ-rigidFree (eᵗᵗ Γ e) V h
  genVˢ-rigidFree e nil          h       = tt , tt
  genVˢ-rigidFree {Γ = Γ} e (cons V W) (h , k) =
    (tt , tt) , genVˢ-rigidFree (eᵗ Γ e) V h , genVˢ-rigidFree (eᵗ Γ e) W k
  genVˢ-rigidFree {Γ = Γ} e (cmp ⋈ V W) (h , k) =
    (tt , tt) , genVˢ-rigidFree (eᵗ Γ e) V h , genVˢ-rigidFree (eᵗ Γ e) W k , tt
  genVˢ-rigidFree {Γ = Γ} e (lam M) h = tt , genCˢ-rigidFree (eᵗᵗᵉ Γ e) M h
  genVˢ-rigidFree e (handler N H) ()
  genVˢ-rigidFree e (V ⦂ᵛ B)     h       = genVˢ-rigidFree e V h , tt

  genCˢ-rigidFree : ∀ {Θ₀ Θ n Δ} {ι : Subst Θ₀ Θ} {Γ : OCtx Θ n} → defs Γ ≡ Δ
                  → (M : RawC Θ₀ n) → {C : OCType Θ} → NoRigidᶜ Δ M
                  → RigidFree (genCˢ ι Γ M C)
  genCˢ-rigidFree e (return V)               {A ‼ t} h           =
    genVˢ-rigidFree e V h , tt
  genCˢ-rigidFree {Γ = Γ} e (M₁ ⨟ M₂)        {A ‼ t} (h , k)     =
    genCˢ-rigidFree (eᵗᵉᵉ Γ e) M₁ h , genCˢ-rigidFree (eᵗᵉᵉ Γ e) M₂ k , tt
  genCˢ-rigidFree {Γ = Γ} e (V₁ · V₂)        {A ‼ t} (h , k)     =
    genVˢ-rigidFree (eᵗᵗᵉ Γ e) V₁ h , genVˢ-rigidFree (eᵗᵗᵉ Γ e) V₂ k , tt , tt
  genCˢ-rigidFree {Γ = Γ} e (match V `in M)  {A ‼ t} (h , k)     =
    genVˢ-rigidFree (eᵗᵗ Γ e) V h , genCˢ-rigidFree (eᵗᵗ Γ e) M k
  genCˢ-rigidFree e (absurd V)               {A ‼ t} h           =
    genVˢ-rigidFree e V h
  genCˢ-rigidFree e (if V `then M₁ `else M₂) {A ‼ t} (h , k , l) =
    genVˢ-rigidFree e V h , genCˢ-rigidFree e M₁ k , genCˢ-rigidFree e M₂ l
  genCˢ-rigidFree e (caseℕ V `zero M₁ `succ M₂) {A ‼ t} (h , k , l) =
    genVˢ-rigidFree e V h , genCˢ-rigidFree e M₁ k , genCˢ-rigidFree e M₂ l
  genCˢ-rigidFree {Γ = Γ} e (case+ V `inl M₁ `inr M₂) {A ‼ t} (h , k , l) =
    genVˢ-rigidFree (eᵗᵗ Γ e) V h , genCˢ-rigidFree (eᵗᵗ Γ e) M₁ k
    , genCˢ-rigidFree (eᵗᵗ Γ e) M₂ l
  genCˢ-rigidFree {Γ = Γ} e (recℕ V M₁ M₂)   {A ‼ t} (h , k , l) =
    genVˢ-rigidFree (eᵗᵉ Γ e) V h , genCˢ-rigidFree (eᵗᵉ Γ e) M₁ k
    , genCˢ-rigidFree (eᵗᵉ Γ e) M₂ l , tt , tt , tt
  genCˢ-rigidFree {Γ = Γ} e (caseL V `nil M₁ `cons M₂) {A ‼ t} (h , k , l) =
    genVˢ-rigidFree (eᵗ Γ e) V h , genCˢ-rigidFree (eᵗ Γ e) M₁ k
    , genCˢ-rigidFree (eᵗ Γ e) M₂ l
  genCˢ-rigidFree {Γ = Γ} e (recL V M₁ M₂)   {A ‼ t} (h , k , l) =
    genVˢ-rigidFree (eᵗᵗᵉ Γ e) V h , genCˢ-rigidFree (eᵗᵗᵉ Γ e) M₁ k
    , genCˢ-rigidFree (eᵗᵗᵉ Γ e) M₂ l , tt , tt , tt
  genCˢ-rigidFree {Γ = Γ} e (perform op V M) {A ‼ t} (h , k)     =
    genVˢ-rigidFree (eᵉ Γ e) V h , genCˢ-rigidFree (eᵉ Γ e) M k , tt
  genCˢ-rigidFree {Γ = Γ} e (delay τ M)      {A ‼ t} h           =
    genCˢ-rigidFree (eᵉ Γ e) M h , tt
  genCˢ-rigidFree {Γ = Γ} e (handle M `with V) {A ‼ t} (h , k)   =
    genCˢ-rigidFree (eᵗᵗᵉᵉ Γ e) M h , genVˢ-rigidFree (eᵗᵗᵉᵉ Γ e) V k , tt , tt
  genCˢ-rigidFree {Γ = Γ} e (unbox V N)      {A ‼ t} (h , k)     =
    resC-rigidFree V , (tt , tt) , tt , genCˢ-rigidFree (eᵗʳ Γ e) N k
  genCˢ-rigidFree {Γ = Γ} e (box ρ V N)      {A ‼ t} (h , k)     =
    genVˢ-rigidFree (eᵗ Γ e) V h , genCˢ-rigidFree (eᵗ Γ e) N k
  genCˢ-rigidFree e (M ⦂ᶜ (B ‼ u'))          {A ‼ t} h           =
    genCˢ-rigidFree e M h , tt , tt

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

  -- boxing a value: the annotation is the box's grade, in the payload's context
  -- lock and the continuation's box type

  ∅ᶜ : OCtx ∅ˢ 0
  ∅ᶜ = []

  ex-box : (c : R)
         → genC ∅ᶜ (box (rconst c) ⋆ (return (var zero))) ([ rconst c ] Unit ‼ ûₑ)
           ≡ (∃ᵗ (  (Unit ≐ᵥ α₀)
                  ∧̂ ((([ rconst c ] α₀ ≾̂ᵥᶜ [ rconst c ] Unit)
                       ∧̂ Et∨≾ᵘ ([ rconst c ] α₀) ûᵣ)
                     ∧̂ (ûₑ ≾̂ₑᶜ ûₑ))))
  ex-box c = refl
