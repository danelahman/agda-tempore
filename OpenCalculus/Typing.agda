------------------------------------------------------------------
-- Well-typed syntax of the open calculus                       --
--                                                              --
-- The intrinsic judgements `Q ∣ Γ ⊢V⦂ A` and `Q ∣ Γ ⊢C⦂ C`     --
-- follow `ClosedCalculus.Syntax.Terms` former by former, with  --
-- open types and grade expressions, and with the side          --
-- conditions entailed from the hypothesis set `Q`.             --
--                                                              --
-- Four rules deviate, as marked at their definitions: a        --
-- handler is a value, `handler`, of a handler type, used by    --
-- `handle_`with_`, where `ClosedCalculus.Syntax.Terms` has     --
-- one form taking the clauses; `handler` types its operation   --
-- clauses over the extended scope `Θ +e`, the continuation     --
-- grade, quantified at the meta level in                       --
-- `ClosedCalculus.Syntax.Terms`, being a rigid effect-grade    --
-- variable; a comparison `cmp` is a value, where it is a       --
-- computation in `ClosedCalculus.Syntax.Terms`; and `unbox`    --
-- takes a resource value, a variable under annotations         --
-- (`_∣_⊢↪[_]_⦂[_]_`), and binds the payload, where             --
-- `ClosedCalculus.Syntax.Terms` takes a variable and binds any --
-- supertype of the payload.                                    --
--                                                              --
-- The rules `annᵛ` and `annᶜ` record a type annotation of the  --
-- raw term, have no counterpart in                             --
-- `ClosedCalculus.Syntax.Terms`, and are identities on typing. --
-- Nor has the rule `def` of the top-level definitions of the   --
-- program context.                                             --
------------------------------------------------------------------

open import Data.Nat using (ℕ; suc)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes
open import Language.Comparisons using (Cmp; eq; ne; lt; le; gt; ge)

module OpenCalculus.Typing (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

-- Only the base-type signature is needed; the type formers of the closed
-- language would otherwise clash with those of `OVType`/`OCType`.

open import Language.Types S using (BaseType; BaseConstants)

open import OpenCalculus.Syntax.Grades    S
open import OpenCalculus.Syntax.Types     S
open import OpenCalculus.Syntax.Contexts  S
open import OpenCalculus.Syntax.Subst     S using (Subst; _[_]ᵛ)
open import OpenCalculus.Hypotheses      S

infix 26 _∣_⊢V⦂_
infix 26 _∣_⊢C⦂_
infix 26 _∣_⊢↪[_]_⦂[_]_

-- Resource values

-- `Q ∣ Γ ⊢↪[ ρ' ] z ⦂[ ρ ] X`: a variable `z`, at its declared box type
-- and accumulated grade `ρ'`, under annotations, each a box type and a
-- supertype of the one inside it, reaching `[ ρ ] X`. The annotations
-- follow `[_]ₛ_`: the grade of each is below the grade inside it and
-- the payload above. The variable carries no `VarOK`; `unbox` checks
-- the grade.

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

    -- top-level definitions

    -- The definition at position `k` of the program context, at an
    -- instance `δ` of its scheme along which `Q` entails the scheme's
    -- hypotheses. There is no lock condition: a definition is closed.
    -- The type is given by an equation, so that it is a variable of
    -- the rule.

    def     : ∀ {k} {s : Scheme} {A : OVType Θ}
            → s ∈ᵖ[ k ] defs Γ
            → (δ : Subst (Θˢ s) Θ)
            → Q ⊩ᴴ Qˢ s [ δ ]
            → A ≡ Xˢ s [ δ ]ᵛ
            -----------------
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

    -- DEVIATION: a value, where the original's comparison is a
    -- computation.

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
    -- under a lock at `⊤ᵣ`, the greatest grade: a clause runs at a time
    -- the handler does not fix.

    -- DEVIATION: a value, where the original has one computation taking
    -- the clauses; and the original's meta-level quantification over the
    -- continuation grade is here the rigid variable `evar newᵉ`.

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

    -- list elimination

    -- As for `if`, both branches are typed at the same computation type;
    -- the `cons` branch binds the head and then the tail, as `match`
    -- binds the components of a pair.

    caseL_`nil_`cons_
            : {A : OVType Θ}
            → {C : OCType Θ}
            → Q ∣ Γ ⊢V⦂ |List| A
            → Q ∣ Γ ⊢C⦂ C
            → Q ∣ Γ ∷ A ∷ |List| A ⊢C⦂ C
            ----------------------------
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

    -- unboxing a boxed value/resource after enough time has passed for it to be ready

    -- The value being unboxed is a resource value: a variable `z`, under
    -- annotations, reaching `[ ρ ] X`. The time that has passed since `z`
    -- was brought into scope is the grade `ρ'` read off the context, and
    -- the continuation binds the payload `X`.

    -- DEVIATION: a resource value, where the original names a variable;
    -- and the continuation binds the payload, where the original binds
    -- any supertype of it.

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
  ex-unbox = unbox (res-var {z = Hd}) ⊩≾̂ᵣ-refl (return ⋆)

  -- unboxing an annotated variable

  ex-unbox-ann : ∅ᴴ ∣ (∅ᶜ ∷ [ ûᵣ ] Unit) ⊢C⦂ Unit ‼ ûₑ
  ex-unbox-ann = unbox (res-ann ûᵣ Unit (res-var {z = Hd}) ⊩≾̂ᵣ-refl Unitₛ) ⊩≾̂ᵣ-refl (return ⋆)
