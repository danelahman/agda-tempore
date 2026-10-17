------------------------------------------------------------------
-- Well-typed syntax of the open calculus                       --
--                                                              --
-- The intrinsic judgements `Q ∣ Γ ⊢V⦂ A` and `Q ∣ Γ ⊢C⦂ C`     --
-- follow `Syntax.Language` former by former, with open types   --
-- and grade expressions, and with the side conditions entailed --
-- from the hypothesis set `Q`.                                 --
--                                                              --
-- One rule deviates, as marked at its definition: `handle`     --
-- types its operation clauses over the extended scope `Θ +e`,  --
-- the continuation grade, quantified at the meta level in      --
-- `Syntax.Language`, being a rigid effect-grade variable.      --
--                                                              --
-- The rules `annᵛ` and `annᶜ` record a type annotation of the  --
-- raw term, have no counterpart in `Syntax.Language`, and are  --
-- identities on typing.                                        --
--                                                              --
-- The rules `zero`, `succ`, `caseℕ` and `recℕ` for natural     --
-- numbers, and `inl`, `inr` and `case+` for sums, have no      --
-- counterpart in `Syntax.Language` either.                     --
------------------------------------------------------------------

open import Data.Nat using (ℕ; suc)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.OpenSyntax.Language (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

-- Only the base-type signature is needed; the type formers of the closed
-- language would otherwise clash with those of `OVType`/`OCType`.

open import Syntax.Types S using (BaseType; BaseConstants)

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S
open import TypeInference.OpenSyntax.Hyps      S

infix 26 _∣_⊢V⦂_
infix 26 _∣_⊢C⦂_

mutual

  data _∣_⊢V⦂_ {Θ : Scope} {n : ℕ} (Q : Hyps Θ) (Γ : OCtx Θ n) : OVType Θ → Set where

    -- variables

    var     : {A : OVType Θ}
            → {ρ : RExp Θ}
            → (x : A ∈̂[ ρ ] Γ)
            → VarOK Q A ρ
            -------------
            → Q ∣ Γ ⊢V⦂ A

    -- base-typed constants

    -- DEVIATION: the base type is explicit; inference reads it off the term.

    const   : (B : BaseType)
            → BaseConstants B
            -----------------
            → Q ∣ Γ ⊢V⦂ Base B

    -- unit type

    ⋆       :
              -------------
              Q ∣ Γ ⊢V⦂ Unit

    -- booleans

    true    :
              -------------
              Q ∣ Γ ⊢V⦂ Bool

    false   :
              -------------
              Q ∣ Γ ⊢V⦂ Bool

    -- natural numbers

    zero    :
              ------------
              Q ∣ Γ ⊢V⦂ Nat

    succ    : Q ∣ Γ ⊢V⦂ Nat
              -------------
            → Q ∣ Γ ⊢V⦂ Nat

    -- pairing

    ⦉_,_⦊    : {A B : OVType Θ}
            → Q ∣ Γ ⊢V⦂ A
            → Q ∣ Γ ⊢V⦂ B
            -------------------
            → Q ∣ Γ ⊢V⦂ A |×| B

    -- injections into a sum

    inl     : {A B : OVType Θ}
            → Q ∣ Γ ⊢V⦂ A
            -------------------
            → Q ∣ Γ ⊢V⦂ A |+| B

    inr     : {A B : OVType Θ}
            → Q ∣ Γ ⊢V⦂ B
            -------------------
            → Q ∣ Γ ⊢V⦂ A |+| B

    -- lambda abstraction

    lam     : {A : OVType Θ}
            → {C : OCType Θ}
            → Q ∣ Γ ∷ A ⊢C⦂ C
            -----------------
            → Q ∣ Γ ⊢V⦂ A ⇒ C

    -- type annotation

    annᵛ    : (A : OVType Θ)
            → Q ∣ Γ ⊢V⦂ A
            -------------
            → Q ∣ Γ ⊢V⦂ A

    -- subsumption

    subV    : {A A' : OVType Θ}
            → Q ∣ Γ ⊢V⦂ A
            → Q ∣ A <:̂ᵛ A'
            --------------
            → Q ∣ Γ ⊢V⦂ A'


  data _∣_⊢C⦂_ {Θ : Scope} {n : ℕ} (Q : Hyps Θ) (Γ : OCtx Θ n) : OCType Θ → Set where

    -- returning a value

    return  : {A : OVType Θ}
            → Q ∣ Γ ⊢V⦂ A
            -----------------
            → Q ∣ Γ ⊢C⦂ A ‼ ûₑ

    -- sequential composition (omitting the bound variable due to using de Bruijn indices)

    _⨟_     : {A B : OVType Θ}      -- NOTE: use \;2 to get this unicode semicolon
            → {ε' : EExp Θ}
            → {ε : EExp Θ}
            → Q ∣ Γ ⊢C⦂ A ‼ ε
            → Q ∣ Γ ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ A ⊢C⦂ B ‼ ε'
            ---------------------------------
            → Q ∣ Γ ⊢C⦂ B ‼ (ε ·̂ₑ ε')

    -- function application

    _·_     : {A : OVType Θ}
            → {C : OCType Θ}
            → Q ∣ Γ ⊢V⦂ A ⇒ C
            → Q ∣ Γ ⊢V⦂ A
            -----------------
            → Q ∣ Γ ⊢C⦂ C

    -- pattern-matching

    match_`in_ : {A B : OVType Θ}
               → {C : OCType Θ}
               → Q ∣ Γ ⊢V⦂ A |×| B
               → Q ∣ Γ ∷ A ∷ B ⊢C⦂ C
               ---------------------
               → Q ∣ Γ ⊢C⦂ C

    -- empty type elimination

    absurd  : {C : OCType Θ}
            → Q ∣ Γ ⊢V⦂ Empty
            -----------------
            → Q ∣ Γ ⊢C⦂ C

    -- boolean elimination

    -- Both branches are typed at the same computation type `C`; differing
    -- types are reconciled by `subC`.

    if_`then_`else_
            : {C : OCType Θ}
            → Q ∣ Γ ⊢V⦂ Bool
            → Q ∣ Γ ⊢C⦂ C
            → Q ∣ Γ ⊢C⦂ C
            ----------------
            → Q ∣ Γ ⊢C⦂ C

    -- natural-number elimination

    -- As for `if`, both branches are typed at the same computation type;
    -- the successor branch binds the predecessor, as `match` binds the
    -- components of a pair.

    caseℕ_`zero_`succ_
            : {C : OCType Θ}
            → Q ∣ Γ ⊢V⦂ Nat
            → Q ∣ Γ ⊢C⦂ C
            → Q ∣ Γ ∷ Nat ⊢C⦂ C
            -------------------
            → Q ∣ Γ ⊢C⦂ C

    -- sum elimination

    -- As for `if`, both branches are typed at the same computation type;
    -- each binds the injected value, as `match` binds the components of
    -- a pair.

    case+_`inl_`inr_
            : {A B : OVType Θ}
            → {C : OCType Θ}
            → Q ∣ Γ ⊢V⦂ A |+| B
            → Q ∣ Γ ∷ A ⊢C⦂ C
            → Q ∣ Γ ∷ B ⊢C⦂ C
            -------------------
            → Q ∣ Γ ⊢C⦂ C

    -- primitive recursion on natural numbers

    -- The step is typed as an operation clause is, under a lock at `⊤ᵣ`;
    -- it binds the predecessor and, after a lock at the effect, the
    -- result of the recursive call, as `_⨟_` binds its continuation.
    -- The effect absorbs its own iteration.

    recℕ    : {B : OVType Θ}
            → {ε : EExp Θ}
            → Q ∣ Γ ⊢V⦂ Nat
            → Q ∣ Γ ⊢C⦂ B ‼ ε
            → Q ∣ (Γ ⟨ rconst ⊤ᵣ ⟩ ∷ Nat) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B ⊢C⦂ B ‼ ε
            → Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε
            ----------------------------------------------------
            → Q ∣ Γ ⊢C⦂ B ‼ ε

    -- performing algebraic operations

    -- Parameter and arity types are ground, hence closed: they embed at any
    -- scope with `⌜_⌝ᵍ` and never mention a type variable.

    perform : {A : OVType Θ}
            → {ε : EExp Θ}
            → (op : Op)
            → Q ∣ Γ ⊢V⦂ ⌜ param op ⌝ᵍ
            → Q ∣ Γ ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ A ‼ ε
            ------------------------------------------------------------------
            → Q ∣ Γ ⊢C⦂ A ‼ (econst (op-grade op) ·̂ₑ ε)

    -- explicit delaying of a computation

    delay   : {A : OVType Θ}
            → {ε : EExp Θ}
            → (τ : 𝔻)
            → Q ∣ Γ ⟨ rconst (of-durʳ τ) ⟩ ⊢C⦂ A ‼ ε
            ----------------------------------------
            → Q ∣ Γ ⊢C⦂ A ‼ (econst (of-durᵉ τ) ·̂ₑ ε)

    -- effect handling

    -- The operation clauses are typed under a lock at `⊤ᵣ`, the greatest
    -- grade: a clause runs at a time the handler does not fix.

    -- DEVIATION: the original's meta-level quantification over the
    -- continuation grade is here the rigid variable `evar newᵉ`.

    handle_`with_`in
            : {A B : OVType Θ}
            → {ε ε' : EExp Θ}
            → Q ∣ Γ ⊢C⦂ A ‼ ε
            → ((op : Op) →
                 wkᵉ-H Q ∣ wkᵉ-ctx Γ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                             ∷ [ rconst (mapᵉ (op-grade op)) ]
                                 (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ}))
                   ⊢C⦂ wkᵉ-v B ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ})))
            → Q ∣ Γ ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ A ⊢C⦂ B ‼ ε'
            ---------------------------------------------------------------
            → Q ∣ Γ ⊢C⦂ B ‼ (ε ·̂ₑ ε')

    -- unboxing a boxed value/resource after enough time has passed for it to be ready

    -- As in the original, the value being unboxed is a variable, named at its
    -- *declared* box type `[ ρ₀ ] A₀`, the time that has passed since it was
    -- brought into scope is the grade `ρ'` read off the context, and the
    -- continuation may bind any supertype `A` of the payload.

    unbox   : {A A₀ : OVType Θ}
            → {C : OCType Θ}
            → {ρ₀ ρ' : RExp Θ}
            → (x : [ ρ₀ ] A₀ ∈̂[ ρ' ] Γ)
            → Q ⊩ ρ' ≾̂ᵣ ρ₀
            → Q ∣ A₀ <:̂ᵛ A
            → Q ∣ Γ ∷ A ⊢C⦂ C
            -----------------
            → Q ∣ Γ ⊢C⦂ C

    -- boxing up a value/resource that is ready for use in at least `ρ` grade steps

    box     : {A : OVType Θ}
            → {C : OCType Θ}
            → (ρ : RExp Θ)
            → Q ∣ Γ ⟨ ρ ⟩ ⊢V⦂ A
            → Q ∣ Γ ∷ [ ρ ] A ⊢C⦂ C
            -----------------------
            → Q ∣ Γ ⊢C⦂ C

    -- type annotation

    annᶜ    : (C : OCType Θ)
            → Q ∣ Γ ⊢C⦂ C
            -------------
            → Q ∣ Γ ⊢C⦂ C

    -- subsumption

    subC    : {C C' : OCType Θ}
            → Q ∣ Γ ⊢C⦂ C
            → Q ∣ C <:̂ᶜ C'
            --------------
            → Q ∣ Γ ⊢C⦂ C'

-- Numerals

numeralᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → ℕ → Q ∣ Γ ⊢V⦂ Nat
numeralᵛ 0       = zero
numeralᵛ (suc k) = succ (numeralᵛ k)

-- Sub-effecting, recovered as subsumption at an effect-only derivation

coerce : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A ε ε'}
       → Q ⊩ ε ≾̂ₑ ε'
       → Q ∣ Γ ⊢C⦂ A ‼ ε
       ------------------
       → Q ∣ Γ ⊢C⦂ A ‼ ε'

coerce {A = A} p M = subC M (<:̂ᵛ-refl A ‼ₛ p)

-- Effect-grade annotations

ε̂-subst : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A ε ε'}
          → ε ≡ ε'
          → Q ∣ Γ ⊢C⦂ A ‼ ε
          ------------------
          → Q ∣ Γ ⊢C⦂ A ‼ ε'

ε̂-subst refl M = M

-- Value types

ty-subst : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A A'}
           → A ≡ A'
           → Q ∣ Γ ⊢V⦂ A
           -------------
           → Q ∣ Γ ⊢V⦂ A'

ty-subst refl V = V

-- Computation types

c-subst : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C C'}
          → C ≡ C'
          → Q ∣ Γ ⊢C⦂ C
          -------------
          → Q ∣ Γ ⊢C⦂ C'

c-subst refl M = M

-- Sanity checks: the rules are usable.

-- The empty scope has to be given explicitly: `OCtx`'s scope is not
-- determined by `[]`, and `Scope`'s fields are projections, not constructors.

private

  ∅ᶜ : OCtx ∅ˢ 0
  ∅ᶜ = []

  -- a value in a plain context

  ex-⋆ : ∅ᴴ ∣ (∅ᶜ ∷ Unit) ⊢V⦂ Unit
  ex-⋆ = ⋆

  -- a variable used after time-passage, justified by eternality of its type

  ex-var-lock : ∅ᴴ ∣ ((∅ᶜ ∷ Unit) ⟨ rconst uᵣ ⟩) ⊢V⦂ Unit
  ex-var-lock = var (Tl-⟨⟩ Hd) (et-ok Unitₑ)

  -- a variable used across a clause barrier, the lock at `⊤ᵣ`

  ex-var-barrier : ∅ᴴ ∣ ((∅ᶜ ∷ Unit) ⟨ rconst ⊤ᵣ ⟩) ⊢V⦂ Unit
  ex-var-barrier = var (Tl-⟨⟩ Hd) (et-ok Unitₑ)

  -- returning a value, sequenced with another such computation

  ex-seq : ∅ᴴ ∣ (∅ᶜ ∷ Unit) ⊢C⦂ Unit ‼ (ûₑ ·̂ₑ ûₑ)
  ex-seq = return ⋆ ⨟ return ⋆

  -- unboxing a boxed variable, no time having passed since it came into scope

  ex-unbox : ∅ᴴ ∣ (∅ᶜ ∷ [ ûᵣ ] Unit) ⊢C⦂ Unit ‼ ûₑ
  ex-unbox = unbox Hd ⊩≾̂ᵣ-refl (<:̂ᵛ-refl Unit) (return ⋆)
