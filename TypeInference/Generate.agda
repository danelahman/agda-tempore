------------------------------------------------------------------
-- Constraint generation                                          --
--                                                                --
-- `genV Γ V A` and `genC Γ M C` are total functions from a raw   --
-- term and an expected (open) type to a constraint of the same   --
-- scope. They are structural on the raw term and mirror the      --
-- rules of `TypeInference.OpenSyntax.Language` former by         --
-- former: every type a rule leaves free becomes a fresh          --
-- `∃`-bound variable, every side condition becomes a             --
-- constraint atom.                                               --
--                                                                --
-- The expected type is an upper bound, not a pin: where two      --
-- types generation cannot choose meet, it is the right-hand side --
-- of a `_≾̂ᵥᶜ_` or `_≾̂ₑᶜ_`; everywhere else the shape is pinned   --
-- by `_≐ᵥ_` and the slack is passed on to the subterms.          --
--                                                                --
-- Under a binder the arguments of the recursive calls are        --
-- weakened, and so is the interpretation of the raw term's type  --
-- and grade variables; the constraints are built inside the      --
-- innermost binder.                                              --
--                                                                --
-- Contract: `σ ⊨[ Q ] genC Γ M (A ‼ t)` holds exactly when some  --
-- derivation `Q ∣ Γ [ σ ] ⊢C⦂ (A ‼ t) [ σ ]` erases to `M [ σ ]` --
-- (`charV`/`charC`, from `soundV`/`soundC` in `Soundness` and    --
-- `completeV`/`completeC` in `Completeness`).                    --
--                                                                --
-- Every `_≐ᵥ_` emitted has one side that is a former with no     --
-- grade slot (`Base`, `Unit`, `Bool`) or is made of unknowns     --
-- bound by the enclosing `∃` and constrained first by that       --
-- equation (`α₁ |×| α₂`, `[ r ] α`). A grade expression in an    --
-- equation so meets only an unbound unknown, which is what the   --
-- unifier's syntactic grade cases rely on (`Core.Unify`).        --
-- Argued, not proved.                                            --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Generate (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades   S
open import TypeInference.OpenSyntax.Types    S
open import TypeInference.OpenSyntax.Contexts S
open import TypeInference.OpenSyntax.Subst    S

open import TypeInference.Raw.Syntax S

open import TypeInference.Constraints.Syntax S

-- The looked-up type subtypes into the expected one, and its grade owes
-- `VarOK`'s disjunction.

varConstraint : ∀ {Θ n} → OCtx Θ n → Fin n → OVType Θ → Constraint Θ
varConstraint Γ i A =
  (lookup-ty Γ i ≾̂ᵥᶜ A) ∧̂ Et∨≾ᵘ (lookup-ty Γ i) (lookup-gr Γ i)

-- `genVˢ ι` and `genCˢ ι` generate for a raw term whose type and grade
-- variables `ι` interprets in the generation scope. Under a binder `ι` is composed
-- with the binder's weakening, so the recursion stays on the subterms.

mutual

  genVˢ : ∀ {Θ₀ Θ n} → Subst Θ₀ Θ → OCtx Θ n → RawV Θ₀ n → OVType Θ → Constraint Θ

  -- variables

  genVˢ ι Γ (var i) A = varConstraint Γ i A

  -- base-typed constants, unit, booleans

  genVˢ ι Γ (const B c) A = Base B ≐ᵥ A
  genVˢ ι Γ ⋆           A = Unit ≐ᵥ A
  genVˢ ι Γ true        A = Bool ≐ᵥ A
  genVˢ ι Γ false       A = Bool ≐ᵥ A

  -- pairing

  genVˢ {Θ = Θ} ι Γ ⦉ V₁ , V₂ ⦊ A =
    ∃ᵗ (∃ᵗ ((α₁ |×| α₂ ≐ᵥ A↑) ∧̂ genVˢ ι↑ Γ↑ V₁ α₁ ∧̂ genVˢ ι↑ Γ↑ V₂ α₂))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})
      A↑ = wkᵗ-v (wkᵗ-v A)
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)

  -- lambda abstraction
  --
  -- The domain is contravariant, so the body is typed at the arrow the
  -- lambda itself synthesises and that arrow subtypes into the expected type.

  genVˢ {Θ = Θ} ι Γ (lam M) A =
    ∃ᵗ (∃ᵗ (∃ᵉ ((α₁ ⇒ (α₂ ‼ e) ≾̂ᵥᶜ A↑) ∧̂ genCˢ ι↑ (Γ↑ ∷ α₁) M (α₂ ‼ e))))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      α₁ = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      α₂ = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e  = evar (newᵉ {Θ +ty +ty})
      A↑ = wkᵉ-v (wkᵗ-v (wkᵗ-v A))
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))

  -- lambda abstraction with an annotated argument
  --
  -- As for `lam`, with the annotation, read through `ι`, in place of the
  -- binder's fresh type.

  genVˢ {Θ = Θ} ι Γ (lam[ B ] M) A =
    ∃ᵗ (∃ᵉ ((B' ⇒ (α ‼ e) ≾̂ᵥᶜ A↑) ∧̂ genCˢ ι↑ (Γ↑ ∷ B') M (α ‼ e)))
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      B' = B [ ι↑ ]ᵛ
      α  = wkᵉ-v (tvar (newᵗ {Θ}))
      e  = evar (newᵉ {Θ +ty})
      A↑ = wkᵉ-v (wkᵗ-v A)
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx Γ)

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
  -- The function's own result type is synthesised and then reconciled with
  -- the expected one, as its latent effect already is.

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
    ∃ᵉ (  genCˢ ι↑ (Γ↑ ⟨ rconst (of-natʳ τ) ⟩) M (A↑ ‼ e)
        ∧̂ ((econst (of-natᵉ τ) ·̂ₑ e) ≾̂ₑᶜ t↑))
    where
      ι↑ = ι ⨟ˢ wkˢᵉ
      e  = evar (newᵉ {Θ})
      A↑ = wkᵉ-v A
      t↑ = wkᵉ-e t
      Γ↑ = wkᵉ-ctx Γ

  -- effect handling
  --
  -- The handled result type occurs contravariantly in the clause contexts,
  -- inside the boxed continuation, so it gets an existential of its own and
  -- is reconciled with the expected type once, for the clauses and the
  -- continuation together. A clause's own effect variable, rigid under
  -- `∀ᵉ`, interprets the clause's.

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
  genVˢ-rigidFree (const B c)  h       = tt
  genVˢ-rigidFree ⋆            h       = tt
  genVˢ-rigidFree true         h       = tt
  genVˢ-rigidFree false        h       = tt
  genVˢ-rigidFree ⦉ V₁ , V₂ ⦊   (h , k) = tt , genVˢ-rigidFree V₁ h , genVˢ-rigidFree V₂ k
  genVˢ-rigidFree (lam M)      h       = tt , genCˢ-rigidFree M h
  genVˢ-rigidFree (lam[ B ] M) h       = tt , genCˢ-rigidFree M h
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
  genCˢ-rigidFree (perform op V M)         {A ‼ t} (h , k)     =
    genVˢ-rigidFree V h , genCˢ-rigidFree M k , tt
  genCˢ-rigidFree (delay τ M)              {A ‼ t} h           =
    genCˢ-rigidFree M h , tt
  genCˢ-rigidFree (handle M `with H `in N) {A ‼ t} ()
  genCˢ-rigidFree (unbox i N)              {A ‼ t} h           =
    tt , tt , tt , genCˢ-rigidFree N h
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
