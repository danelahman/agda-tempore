------------------------------------------------------------------
-- Well-typed syntax of the polymorphic calculus                --
--                                                              --
-- The intrinsic judgements `Q ∣ Γ ⊢V⦂ A` and `Q ∣ Γ ⊢C⦂ C`     --
-- over open types and grade expressions, with side conditions  --
-- entailed from the hypothesis set `Q`.                        --
--                                                              --
-- A handler is a value of a handler type, used by              --
-- `handle_`with_`; its operation clauses are typed over `Θ     --
-- +e`, the continuation grade being a rigid effect-grade       --
-- variable. `unbox` takes a resource value, a variable under   --
-- annotations (`_∣_⊢↪[_]_⦂[_]_`). `usedef` types the use of a  --
-- definition of the program context. The rules `annᵛ` and      --
-- `annᶜ` record a type annotation of the raw term.             --
------------------------------------------------------------------

open import Data.Nat using (ℕ; suc)

open import Grades.Base
open import Language.BaseTypes using (module BaseTypes)
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import Language.Comparisons using (Cmp; eq; ne; lt; le; gt; ge)

module PolymorphicCalculus.Typing (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

-- Only the base-type signature is needed.

open BaseTypes BTs using (BaseType; BaseConstants)

open import PolymorphicCalculus.Syntax.Grades    S
open import PolymorphicCalculus.Syntax.Types     S
open import PolymorphicCalculus.Syntax.Contexts  S
open import PolymorphicCalculus.Syntax.GradeSubstitution S using (Subst; _[_]ᵛ)
open import PolymorphicCalculus.Hypotheses      S

infix 26 _∣_⊢V⦂_
infix 26 _∣_⊢C⦂_
infix 26 _∣_⊢↪[_]_⦂[_]_

-- Resource values

-- `Q ∣ Γ ⊢↪[ ρ' ] z ⦂[ ρ ] X`: a variable `z`, at its declared box type
-- and accumulated grade `ρ'`, under annotations, each a box type below
-- (in grade) and above (in payload) the one inside it, reaching `[ ρ ] X`.
-- `unbox` checks the grade, so the variable carries no `VarOK`.

data _∣_⊢↪[_]_⦂[_]_ {Θ : Scope} {n : ℕ} (Q : Hyps Θ) (Γ : OCtx Θ n) (ρ' : RExp Θ)
     {ρ₀ : RExp Θ} {X₀ : OVType Θ} (z : [ ρ₀ ] X₀ ∈̂[ ρ' ] Γ)
     : RExp Θ → OVType Θ → Set where

  -- the variable at its declared type

  res-var : -------------------------------
            Q ∣ Γ ⊢↪[ ρ' ] z ⦂[ ρ₀ ] X₀

  -- an annotation

  res-ann : {ρ : RExp Θ} {X : OVType Θ}
          → (ρₐ : RExp Θ) (Xₐ : OVType Θ)
          → Q ∣ Γ ⊢↪[ ρ' ] z ⦂[ ρ ] X
          → Q ⊩ ρₐ ≾̂ᵣ ρ
          → Q ∣ X <:̂ᵛ Xₐ
          -------------------------------
          → Q ∣ Γ ⊢↪[ ρ' ] z ⦂[ ρₐ ] Xₐ

mutual

  data _∣_⊢V⦂_ {Θ : Scope} {n : ℕ} (Q : Hyps Θ) (Γ : OCtx Θ n) : OVType Θ → Set where

    -- variables

    var     : {A : OVType Θ}
            → {ρ : RExp Θ}
            → (x : A ∈̂[ ρ ] Γ)
            → VarOK Q A ρ
            -------------
            → Q ∣ Γ ⊢V⦂ A

    -- uses of definitions

    -- The definition at position `k` of the program context, at an
    -- instance `δ` of its scheme along which `Q` entails the scheme's
    -- hypotheses. There is no lock condition: a definition is closed.

    usedef  : ∀ {k} {s : Scheme} {A : OVType Θ}
            → s ∈ᵖ[ k ] defs Γ
            → (δ : Subst (Θˢ s) Θ)
            → Q ⊩ᴴ Qˢ s [ δ ]
            → A ≡ Xˢ s [ δ ]ᵛ
            -----------------
            → Q ∣ Γ ⊢V⦂ A

    -- base-typed constants

    -- The base type is explicit; inference reads it off the term.

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


    -- lists

    nil     : {A : OVType Θ}
              ---------------------
            → Q ∣ Γ ⊢V⦂ |List| A

    cons    : {A : OVType Θ}
            → Q ∣ Γ ⊢V⦂ A
            → Q ∣ Γ ⊢V⦂ |List| A
            --------------------
            → Q ∣ Γ ⊢V⦂ |List| A

    -- comparison

    -- One rule for the six relations of `Cmp`: both operands at one
    -- type, which has to be eternal, and the result a `Bool`.

    -- A comparison is a value.

    cmp     : {A : OVType Θ}
            → (⋈ : Cmp)
            → Q ∣ Γ ⊢V⦂ A
            → Q ∣ Γ ⊢V⦂ A
            → Q ⊩ᴱ A
            --------------
            → Q ∣ Γ ⊢V⦂ Bool

    -- lambda abstraction

    lam     : {A : OVType Θ}
            → {C : OCType Θ}
            → Q ∣ Γ ∷ A ⊢C⦂ C
            -----------------
            → Q ∣ Γ ⊢V⦂ A ⇒ C

    -- handlers

    -- The return clause is typed as the continuation of `_⨟_` is, after
    -- a lock at the handled effect. The operation clauses are typed
    -- under a lock at `⊤ᵣ`, as a clause runs at a time the handler does
    -- not fix. The continuation grade is the rigid `evar newᵉ`.

    handler : {A B : OVType Θ}
            → {ε ε' : EExp Θ}
            → Q ∣ Γ ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ A ⊢C⦂ B ‼ ε'
            → ((op : Op) →
                 wkᵉ-H Q ∣ wkᵉ-ctx Γ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                             ∷ [ rconst (mapᵉ (op-grade op)) ]
                                 (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ}))
                   ⊢C⦂ wkᵉ-v B ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ})))
            ---------------------------------------------------------------
            → Q ∣ Γ ⊢V⦂ (A ‼ ε) ⇛ (B ‼ ε')

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

    -- sequential composition

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

    -- Both branches have the same computation type; the successor
    -- branch binds the predecessor.

    caseℕ_`zero_`succ_
            : {C : OCType Θ}
            → Q ∣ Γ ⊢V⦂ Nat
            → Q ∣ Γ ⊢C⦂ C
            → Q ∣ Γ ∷ Nat ⊢C⦂ C
            -------------------
            → Q ∣ Γ ⊢C⦂ C

    -- sum elimination

    -- Both branches have the same computation type; each binds the
    -- injected value.

    case+_`inl_`inr_
            : {A B : OVType Θ}
            → {C : OCType Θ}
            → Q ∣ Γ ⊢V⦂ A |+| B
            → Q ∣ Γ ∷ A ⊢C⦂ C
            → Q ∣ Γ ∷ B ⊢C⦂ C
            -------------------
            → Q ∣ Γ ⊢C⦂ C

    -- list elimination

    -- Both branches have the same computation type; the `cons` branch
    -- binds the head and then the tail.

    caseL_`nil_`cons_
            : {A : OVType Θ}
            → {C : OCType Θ}
            → Q ∣ Γ ⊢V⦂ |List| A
            → Q ∣ Γ ⊢C⦂ C
            → Q ∣ Γ ∷ A ∷ |List| A ⊢C⦂ C
            ----------------------------
            → Q ∣ Γ ⊢C⦂ C

    -- primitive recursion on natural numbers

    -- The step is typed under a lock at `⊤ᵣ`; it binds the predecessor
    -- and, after a lock at the effect, the result of the recursive call.
    -- The effect absorbs its own iteration.

    recℕ    : {B : OVType Θ}
            → {ε : EExp Θ}
            → Q ∣ Γ ⊢V⦂ Nat
            → Q ∣ Γ ⊢C⦂ B ‼ ε
            → Q ∣ (Γ ⟨ rconst ⊤ᵣ ⟩ ∷ Nat) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B ⊢C⦂ B ‼ ε
            → Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε
            ----------------------------------------------------
            → Q ∣ Γ ⊢C⦂ B ‼ ε

    -- primitive recursion on lists

    -- As `recℕ`, the step binding the head and the tail in place of the
    -- predecessor.

    recL    : {A B : OVType Θ}
            → {ε : EExp Θ}
            → Q ∣ Γ ⊢V⦂ |List| A
            → Q ∣ Γ ⊢C⦂ B ‼ ε
            → Q ∣ (Γ ⟨ rconst ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B ⊢C⦂ B ‼ ε
            → Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε
            -------------------------------------------------------------
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

    handle_`with_
            : {A B : OVType Θ}
            → {ε ε' : EExp Θ}
            → Q ∣ Γ ⊢C⦂ A ‼ ε
            → Q ∣ Γ ⊢V⦂ (A ‼ ε) ⇛ (B ‼ ε')
            ------------------------------
            → Q ∣ Γ ⊢C⦂ B ‼ (ε ·̂ₑ ε')

    -- unboxing a resource after enough time has passed for it to be ready

    -- The value is a resource value reaching `[ ρ ] X`; the time passed
    -- since `z` came into scope is the grade `ρ'` read off the context.

    unbox   : {X : OVType Θ}
            → {C : OCType Θ}
            → {ρ₀ ρ' ρ : RExp Θ}
            → {X₀ : OVType Θ}
            → {z : [ ρ₀ ] X₀ ∈̂[ ρ' ] Γ}
            → Q ∣ Γ ⊢↪[ ρ' ] z ⦂[ ρ ] X
            → Q ⊩ ρ' ≾̂ᵣ ρ
            → Q ∣ Γ ∷ X ⊢C⦂ C
            -----------------
            → Q ∣ Γ ⊢C⦂ C

    -- boxing a value that is ready for use in at least `ρ` grade steps

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

-- Sub-effecting, as subsumption at an effect-only derivation

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
  ex-unbox = unbox (res-var {z = Hd}) ⊩≾̂ᵣ-refl (return ⋆)

  -- unboxing an annotated variable

  ex-unbox-ann : ∅ᴴ ∣ (∅ᶜ ∷ [ ûᵣ ] Unit) ⊢C⦂ Unit ‼ ûₑ
  ex-unbox-ann = unbox (res-ann ûᵣ Unit (res-var {z = Hd}) ⊩≾̂ᵣ-refl Unitₛ) ⊩≾̂ᵣ-refl (return ⋆)
