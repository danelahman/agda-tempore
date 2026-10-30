------------------------------------------------------------------
-- Well-typed syntax of the polymorphic calculus                --
--                                                              --
-- The intrinsic judgements `Q ∣ Γ ⊢V⦂ A` and `Q ∣ Γ ⊢C⦂ C`     --
-- over open types and grade expressions, side conditions       --
-- entailed from the hypothesis set `Q`. Handler operation      --
-- clauses are typed over `Θ +e`, the continuation grade a      --
-- rigid variable; `unbox` takes a resource value, a variable   --
-- under annotations; `usedef` uses a definition of the program --
-- context.                                                     --
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

open BaseTypes BTs using (BaseType; BaseConstants)

open import PolymorphicCalculus.Syntax.Grades    S
open import PolymorphicCalculus.Syntax.Types     S
open import PolymorphicCalculus.Syntax.Contexts  S
open import PolymorphicCalculus.Syntax.GradeSubstitution S using (Subst; _[_]ᵛ)
open import PolymorphicCalculus.Hypotheses      S

infix 26 _∣_⊢V⦂_
infix 26 _∣_⊢C⦂_
infix 26 _∣_⊢↪[_]_⦂[_]_

-- Resource values: a box-typed variable `z` at accumulated grade `ρ'`,
-- under annotations each lower in grade and higher in payload; no `VarOK`

data _∣_⊢↪[_]_⦂[_]_ {Θ : Scope} {n : ℕ} (Q : Hyps Θ) (Γ : OCtx Θ n) (ρ' : RExp Θ)
     {ρ₀ : RExp Θ} {X₀ : OVType Θ} (z : [ ρ₀ ] X₀ ∈̂[ ρ' ] Γ)
     : RExp Θ → OVType Θ → Set where

  res-var : -------------------------------
            Q ∣ Γ ⊢↪[ ρ' ] z ⦂[ ρ₀ ] X₀

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

    -- use of a definition, at an instance of its scheme; no lock
    -- condition, as a definition is closed

    usedef  : ∀ {k} {s : Scheme} {A : OVType Θ}
            → s ∈ᵖ[ k ] defs Γ
            → (δ : Subst (Θˢ s) Θ)
            → Q ⊩ᴴ Qˢ s [ δ ]
            → A ≡ Xˢ s [ δ ]ᵛ
            -----------------
            → Q ∣ Γ ⊢V⦂ A

    -- base-typed constants, the base type explicit

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

    -- comparison, a value: one rule for the relations of `Cmp`, at an
    -- eternal type

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

    -- handlers: the return clause as the continuation of `_⨟_`; the
    -- operation clauses under a lock at `⊤ᵣ`, continuation grade rigid

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

    -- boolean elimination, both branches at one type

    if_`then_`else_
            : {C : OCType Θ}
            → Q ∣ Γ ⊢V⦂ Bool
            → Q ∣ Γ ⊢C⦂ C
            → Q ∣ Γ ⊢C⦂ C
            ----------------
            → Q ∣ Γ ⊢C⦂ C

    -- natural-number elimination

    caseℕ_`zero_`succ_
            : {C : OCType Θ}
            → Q ∣ Γ ⊢V⦂ Nat
            → Q ∣ Γ ⊢C⦂ C
            → Q ∣ Γ ∷ Nat ⊢C⦂ C
            -------------------
            → Q ∣ Γ ⊢C⦂ C

    -- sum elimination

    case+_`inl_`inr_
            : {A B : OVType Θ}
            → {C : OCType Θ}
            → Q ∣ Γ ⊢V⦂ A |+| B
            → Q ∣ Γ ∷ A ⊢C⦂ C
            → Q ∣ Γ ∷ B ⊢C⦂ C
            -------------------
            → Q ∣ Γ ⊢C⦂ C

    -- list elimination

    caseL_`nil_`cons_
            : {A : OVType Θ}
            → {C : OCType Θ}
            → Q ∣ Γ ⊢V⦂ |List| A
            → Q ∣ Γ ⊢C⦂ C
            → Q ∣ Γ ∷ A ∷ |List| A ⊢C⦂ C
            ----------------------------
            → Q ∣ Γ ⊢C⦂ C

    -- primitive recursion on natural numbers: the step under a lock at
    -- `⊤ᵣ`, the effect absorbing its own iteration

    recℕ    : {B : OVType Θ}
            → {ε : EExp Θ}
            → Q ∣ Γ ⊢V⦂ Nat
            → Q ∣ Γ ⊢C⦂ B ‼ ε
            → Q ∣ (Γ ⟨ rconst ⊤ᵣ ⟩ ∷ Nat) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B ⊢C⦂ B ‼ ε
            → Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε
            ----------------------------------------------------
            → Q ∣ Γ ⊢C⦂ B ‼ ε

    -- primitive recursion on lists, as `recℕ`

    recL    : {A B : OVType Θ}
            → {ε : EExp Θ}
            → Q ∣ Γ ⊢V⦂ |List| A
            → Q ∣ Γ ⊢C⦂ B ‼ ε
            → Q ∣ (Γ ⟨ rconst ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B ⊢C⦂ B ‼ ε
            → Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε
            -------------------------------------------------------------
            → Q ∣ Γ ⊢C⦂ B ‼ ε

    -- performing algebraic operations; parameter and arity types are ground

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

    -- unboxing a resource value once enough time `ρ'` has passed since
    -- its variable came into scope

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

-- Transport along equal types

ε̂-subst : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A ε ε'}
          → ε ≡ ε'
          → Q ∣ Γ ⊢C⦂ A ‼ ε
          ------------------
          → Q ∣ Γ ⊢C⦂ A ‼ ε'

ε̂-subst refl M = M

ty-subst : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A A'}
           → A ≡ A'
           → Q ∣ Γ ⊢V⦂ A
           -------------
           → Q ∣ Γ ⊢V⦂ A'

ty-subst refl V = V

c-subst : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C C'}
          → C ≡ C'
          → Q ∣ Γ ⊢C⦂ C
          -------------
          → Q ∣ Γ ⊢C⦂ C'

c-subst refl M = M

-- Sanity checks; the empty scope is explicit, as `[]` does not determine it

private

  ∅ᶜ : OCtx ∅ˢ 0
  ∅ᶜ = []

  ex-⋆ : ∅ᴴ ∣ (∅ᶜ ∷ Unit) ⊢V⦂ Unit
  ex-⋆ = ⋆

  -- a variable used under a lock, by eternality of its type

  ex-var-lock : ∅ᴴ ∣ ((∅ᶜ ∷ Unit) ⟨ rconst uᵣ ⟩) ⊢V⦂ Unit
  ex-var-lock = var (Tl-⟨⟩ Hd) (et-ok Unitₑ)

  ex-var-barrier : ∅ᴴ ∣ ((∅ᶜ ∷ Unit) ⟨ rconst ⊤ᵣ ⟩) ⊢V⦂ Unit
  ex-var-barrier = var (Tl-⟨⟩ Hd) (et-ok Unitₑ)

  ex-seq : ∅ᴴ ∣ (∅ᶜ ∷ Unit) ⊢C⦂ Unit ‼ (ûₑ ·̂ₑ ûₑ)
  ex-seq = return ⋆ ⨟ return ⋆

  ex-unbox : ∅ᴴ ∣ (∅ᶜ ∷ [ ûᵣ ] Unit) ⊢C⦂ Unit ‼ ûₑ
  ex-unbox = unbox (res-var {z = Hd}) ⊩≾̂ᵣ-refl (return ⋆)

  ex-unbox-ann : ∅ᴴ ∣ (∅ᶜ ∷ [ ûᵣ ] Unit) ⊢C⦂ Unit ‼ ûₑ
  ex-unbox-ann = unbox (res-ann ûᵣ Unit (res-var {z = Hd}) ⊩≾̂ᵣ-refl Unitₛ) ⊩≾̂ᵣ-refl (return ⋆)
