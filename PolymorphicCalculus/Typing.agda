------------------------------------------------------------------
-- Well-typed syntax of the polymorphic calculus                --
--                                                              --
-- The intrinsic judgements `Q ∣ Γ ⊢ᵛ⦂ A` and `Q ∣ Γ ⊢ᶜ⦂ C`     --
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

infix 26 _∣_⊢ᵛ⦂_
infix 26 _∣_⊢ᶜ⦂_
infix 26 _⊢_∈̂[_]_

-- Resource access: the lookup `_∈̂[_]_` of a box-typed variable, under
-- annotations each lower in grade and higher in payload; no `_⊩_Et∨≾ᵘ_`

data _⊢_∈̂[_]_ {Θ : Scope} (Q : Hyps Θ) : OVType Θ → RExp Θ → {n : ℕ} → OCtx Θ n → Set where

  res-var : ∀ {n} {Γ : OCtx Θ n} {ρ' ρ : RExp Θ} {X : OVType Θ}
          → [ ρ ] X ∈̂[ ρ' ] Γ
          -----------------------
          → Q ⊢ [ ρ ] X ∈̂[ ρ' ] Γ

  res-ann : ∀ {n} {Γ : OCtx Θ n} {ρ' ρ : RExp Θ} {X : OVType Θ}
          → (ρₐ : RExp Θ) (Xₐ : OVType Θ)
          → Q ⊢ [ ρ ] X ∈̂[ ρ' ] Γ
          → Q ⊩ ρₐ ≾̂ᵣ ρ
          → Q ⊩ X <:̂ᵛ Xₐ
          -------------------------
          → Q ⊢ [ ρₐ ] Xₐ ∈̂[ ρ' ] Γ

-- The variable of a resource access, and the grade and payload of its type

module _ {Θ : Scope} {Q : Hyps Θ} {n : ℕ} {Γ : OCtx Θ n} {ρ' : RExp Θ} where

  res-grade-of : {A : OVType Θ} → Q ⊢ A ∈̂[ ρ' ] Γ → RExp Θ
  res-grade-of (res-var {ρ = ρ} _) = ρ
  res-grade-of (res-ann _ _ R _ _) = res-grade-of R

  res-payload-of : {A : OVType Θ} → Q ⊢ A ∈̂[ ρ' ] Γ → OVType Θ
  res-payload-of (res-var {X = X} _) = X
  res-payload-of (res-ann _ _ R _ _) = res-payload-of R

  res-var-of : {A : OVType Θ} → (R : Q ⊢ A ∈̂[ ρ' ] Γ)
             → [ res-grade-of R ] res-payload-of R ∈̂[ ρ' ] Γ
  res-var-of (res-var z)         = z
  res-var-of (res-ann _ _ R _ _) = res-var-of R

mutual

  data _∣_⊢ᵛ⦂_ {Θ : Scope} {n : ℕ} (Q : Hyps Θ) (Γ : OCtx Θ n) : OVType Θ → Set where

    -- variables

    var     : {A : OVType Θ}
            → {ρ : RExp Θ}
            → (x : A ∈̂[ ρ ] Γ)
            → Q ⊩ A Et∨≾ᵘ ρ
            -------------
            → Q ∣ Γ ⊢ᵛ⦂ A

    -- use of a definition, at an instance of its scheme; no modality
    -- condition, as a definition is closed

    usedef  : ∀ {k} {s : Scheme} {A : OVType Θ}
            → s ∈ᵖ[ k ] defs Γ
            → (δ : Subst (Θˢ s) Θ)
            → Q ⊩ᴴ Qˢ s [ δ ]
            → A ≡ Xˢ s [ δ ]ᵛ
            -----------------
            → Q ∣ Γ ⊢ᵛ⦂ A

    -- base-typed constants, the base type explicit

    const   : (B : BaseType)
            → BaseConstants B
            -----------------
            → Q ∣ Γ ⊢ᵛ⦂ Base B

    -- unit type

    ⋆       :
              -------------
              Q ∣ Γ ⊢ᵛ⦂ unit

    -- booleans

    true    :
              -------------
              Q ∣ Γ ⊢ᵛ⦂ bool

    false   :
              -------------
              Q ∣ Γ ⊢ᵛ⦂ bool

    -- natural numbers

    zero    :
              ------------
              Q ∣ Γ ⊢ᵛ⦂ nat

    succ    : Q ∣ Γ ⊢ᵛ⦂ nat
              -------------
            → Q ∣ Γ ⊢ᵛ⦂ nat

    -- pairing

    ⦉_,_⦊    : {A B : OVType Θ}
            → Q ∣ Γ ⊢ᵛ⦂ A
            → Q ∣ Γ ⊢ᵛ⦂ B
            -------------------
            → Q ∣ Γ ⊢ᵛ⦂ A |×| B

    -- injections into a sum

    inl     : {A B : OVType Θ}
            → Q ∣ Γ ⊢ᵛ⦂ A
            -------------------
            → Q ∣ Γ ⊢ᵛ⦂ A |+| B

    inr     : {A B : OVType Θ}
            → Q ∣ Γ ⊢ᵛ⦂ B
            -------------------
            → Q ∣ Γ ⊢ᵛ⦂ A |+| B


    -- lists

    nil     : {A : OVType Θ}
              ---------------------
            → Q ∣ Γ ⊢ᵛ⦂ list A

    cons    : {A : OVType Θ}
            → Q ∣ Γ ⊢ᵛ⦂ A
            → Q ∣ Γ ⊢ᵛ⦂ list A
            --------------------
            → Q ∣ Γ ⊢ᵛ⦂ list A

    -- comparison, a value: one rule for the relations of `Cmp`, at an
    -- eternal type

    cmp     : {A : OVType Θ}
            → (⋈ : Cmp)
            → Q ∣ Γ ⊢ᵛ⦂ A
            → Q ∣ Γ ⊢ᵛ⦂ A
            → Q ⊩Et A
            --------------
            → Q ∣ Γ ⊢ᵛ⦂ bool

    -- lambda abstraction

    fun     : {A : OVType Θ}
            → {C : OCType Θ}
            → Q ∣ Γ ∷ A ⊢ᶜ⦂ C
            -----------------
            → Q ∣ Γ ⊢ᵛ⦂ A ⇒ C

    -- handlers: the return clause as the continuation of `_⨟_`; the
    -- operation clauses under a modality at `⊤ᵣ`, continuation grade rigid

    handler : {A B : OVType Θ}
            → {ε ε' : EExp Θ}
            → Q ∣ Γ ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'
            → ((op : Op) →
                 wkᵉ-H Q ∣ wkᵉ-ctx Γ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                             ∷ [ rconst ∣ op-grade op ∣ᵉ ]
                                 (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ! evar (newᵉ {Θ}))
                   ⊢ᶜ⦂ wkᵉ-v B ! (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ})))
            ---------------------------------------------------------------
            → Q ∣ Γ ⊢ᵛ⦂ (A ! ε) ⇛ (B ! ε')

    -- type annotation

    annᵛ    : (A : OVType Θ)
            → Q ∣ Γ ⊢ᵛ⦂ A
            -------------
            → Q ∣ Γ ⊢ᵛ⦂ A

    -- subsumption

    subV    : {A A' : OVType Θ}
            → Q ∣ Γ ⊢ᵛ⦂ A
            → Q ⊩ A <:̂ᵛ A'
            --------------
            → Q ∣ Γ ⊢ᵛ⦂ A'


  data _∣_⊢ᶜ⦂_ {Θ : Scope} {n : ℕ} (Q : Hyps Θ) (Γ : OCtx Θ n) : OCType Θ → Set where

    -- returning a value

    return  : {A : OVType Θ}
            → Q ∣ Γ ⊢ᵛ⦂ A
            -----------------
            → Q ∣ Γ ⊢ᶜ⦂ A ! 𝟏̂ₑ

    -- sequential composition

    _⨟_     : {A B : OVType Θ}      -- input: \;2
            → {ε' : EExp Θ}
            → {ε : EExp Θ}
            → Q ∣ Γ ⊢ᶜ⦂ A ! ε
            → Q ∣ Γ ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'
            ---------------------------------
            → Q ∣ Γ ⊢ᶜ⦂ B ! (ε ·̂ₑ ε')

    -- function application

    _·_     : {A : OVType Θ}
            → {C : OCType Θ}
            → Q ∣ Γ ⊢ᵛ⦂ A ⇒ C
            → Q ∣ Γ ⊢ᵛ⦂ A
            -----------------
            → Q ∣ Γ ⊢ᶜ⦂ C

    -- pattern-matching

    match_`with_ : {A B : OVType Θ}
                 → {C : OCType Θ}
                 → Q ∣ Γ ⊢ᵛ⦂ A |×| B
                 → Q ∣ Γ ∷ A ∷ B ⊢ᶜ⦂ C
                 ---------------------
                 → Q ∣ Γ ⊢ᶜ⦂ C

    -- empty type elimination

    absurd  : {C : OCType Θ}
            → Q ∣ Γ ⊢ᵛ⦂ empty
            -----------------
            → Q ∣ Γ ⊢ᶜ⦂ C

    -- boolean elimination, both branches at one type

    if_`then_`else_
            : {C : OCType Θ}
            → Q ∣ Γ ⊢ᵛ⦂ bool
            → Q ∣ Γ ⊢ᶜ⦂ C
            → Q ∣ Γ ⊢ᶜ⦂ C
            ----------------
            → Q ∣ Γ ⊢ᶜ⦂ C

    -- natural-number elimination

    matchℕ_`zero_`succ_
            : {C : OCType Θ}
            → Q ∣ Γ ⊢ᵛ⦂ nat
            → Q ∣ Γ ⊢ᶜ⦂ C
            → Q ∣ Γ ∷ nat ⊢ᶜ⦂ C
            -------------------
            → Q ∣ Γ ⊢ᶜ⦂ C

    -- sum elimination

    match+_`inl_`inr_
            : {A B : OVType Θ}
            → {C : OCType Θ}
            → Q ∣ Γ ⊢ᵛ⦂ A |+| B
            → Q ∣ Γ ∷ A ⊢ᶜ⦂ C
            → Q ∣ Γ ∷ B ⊢ᶜ⦂ C
            -------------------
            → Q ∣ Γ ⊢ᶜ⦂ C

    -- list elimination

    matchL_`nil_`cons_
            : {A : OVType Θ}
            → {C : OCType Θ}
            → Q ∣ Γ ⊢ᵛ⦂ list A
            → Q ∣ Γ ⊢ᶜ⦂ C
            → Q ∣ Γ ∷ A ∷ list A ⊢ᶜ⦂ C
            ----------------------------
            → Q ∣ Γ ⊢ᶜ⦂ C

    -- primitive recursion on natural numbers: the step under a modality at
    -- `⊤ᵣ`, the effect absorbing its own iteration

    recℕ    : {B : OVType Θ}
            → {ε : EExp Θ}
            → Q ∣ Γ ⊢ᵛ⦂ nat
            → Q ∣ Γ ⊢ᶜ⦂ B ! ε
            → Q ∣ (Γ ⟨ rconst ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε
            → Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε
            ----------------------------------------------------
            → Q ∣ Γ ⊢ᶜ⦂ B ! ε

    -- primitive recursion on lists, as `recℕ`

    recL    : {A B : OVType Θ}
            → {ε : EExp Θ}
            → Q ∣ Γ ⊢ᵛ⦂ list A
            → Q ∣ Γ ⊢ᶜ⦂ B ! ε
            → Q ∣ (Γ ⟨ rconst ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε
            → Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε
            -------------------------------------------------------------
            → Q ∣ Γ ⊢ᶜ⦂ B ! ε

    -- performing algebraic operations; parameter and arity types are ground

    perform : {A : OVType Θ}
            → {ε : EExp Θ}
            → (op : Op)
            → Q ∣ Γ ⊢ᵛ⦂ ⌜ param op ⌝ᵍ
            → Q ∣ Γ ⟨ rconst ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ A ! ε
            ------------------------------------------------------------------
            → Q ∣ Γ ⊢ᶜ⦂ A ! (econst (op-grade op) ·̂ₑ ε)

    -- explicit delaying of a computation

    delay   : {A : OVType Θ}
            → {ε : EExp Θ}
            → (τ : 𝔻)
            → Q ∣ Γ ⟨ rconst (ιᵣ τ) ⟩ ⊢ᶜ⦂ A ! ε
            ----------------------------------------
            → Q ∣ Γ ⊢ᶜ⦂ A ! (econst (ιₑ τ) ·̂ₑ ε)

    -- effect handling

    handle_`with_
            : {A B : OVType Θ}
            → {ε ε' : EExp Θ}
            → Q ∣ Γ ⊢ᶜ⦂ A ! ε
            → Q ∣ Γ ⊢ᵛ⦂ (A ! ε) ⇛ (B ! ε')
            ------------------------------
            → Q ∣ Γ ⊢ᶜ⦂ B ! (ε ·̂ₑ ε')

    -- unboxing a resource value while the grade `ρ'` accumulated since
    -- its variable came into scope is below its grade `ρ`

    unbox   : {X : OVType Θ}
            → {C : OCType Θ}
            → {ρ' ρ : RExp Θ}
            → Q ⊢ [ ρ ] X ∈̂[ ρ' ] Γ
            → Q ⊩ ρ' ≾̂ᵣ ρ
            → Q ∣ Γ ∷ X ⊢ᶜ⦂ C
            -----------------
            → Q ∣ Γ ⊢ᶜ⦂ C

    -- boxing a value as a resource usable within the grade `ρ`

    box     : {A : OVType Θ}
            → {C : OCType Θ}
            → (ρ : RExp Θ)
            → Q ∣ Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A
            → Q ∣ Γ ∷ [ ρ ] A ⊢ᶜ⦂ C
            -----------------------
            → Q ∣ Γ ⊢ᶜ⦂ C

    -- type annotation

    annᶜ    : (C : OCType Θ)
            → Q ∣ Γ ⊢ᶜ⦂ C
            -------------
            → Q ∣ Γ ⊢ᶜ⦂ C

    -- subsumption

    subC    : {C C' : OCType Θ}
            → Q ∣ Γ ⊢ᶜ⦂ C
            → Q ⊩ C <:̂ᶜ C'
            --------------
            → Q ∣ Γ ⊢ᶜ⦂ C'

-- Numerals

numeralᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → ℕ → Q ∣ Γ ⊢ᵛ⦂ nat
numeralᵛ 0       = zero
numeralᵛ (suc k) = succ (numeralᵛ k)

-- Sub-effecting, as subsumption at an effect-only derivation

coerce : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A ε ε'}
       → Q ⊩ ε ≾̂ₑ ε'
       → Q ∣ Γ ⊢ᶜ⦂ A ! ε
       ------------------
       → Q ∣ Γ ⊢ᶜ⦂ A ! ε'

coerce {A = A} p M = subC M (<:̂ᵛ-refl A !ₛ p)

-- Transport along equal types

ε̂-subst : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A ε ε'}
          → ε ≡ ε'
          → Q ∣ Γ ⊢ᶜ⦂ A ! ε
          ------------------
          → Q ∣ Γ ⊢ᶜ⦂ A ! ε'

ε̂-subst refl M = M

ty-subst : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A A'}
           → A ≡ A'
           → Q ∣ Γ ⊢ᵛ⦂ A
           -------------
           → Q ∣ Γ ⊢ᵛ⦂ A'

ty-subst refl V = V

c-subst : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C C'}
          → C ≡ C'
          → Q ∣ Γ ⊢ᶜ⦂ C
          -------------
          → Q ∣ Γ ⊢ᶜ⦂ C'

c-subst refl M = M

-- Sanity checks; the empty scope is explicit, as `[]` does not determine it

private

  ∅ᶜ : OCtx ∅ˢ 0
  ∅ᶜ = []

  ex-⋆ : ∅ᴴ ∣ (∅ᶜ ∷ unit) ⊢ᵛ⦂ unit
  ex-⋆ = ⋆

  -- a variable used under a modality, by eternality of its type

  ex-var-⟨⟩ : ∅ᴴ ∣ ((∅ᶜ ∷ unit) ⟨ rconst 𝟏ᵣ ⟩) ⊢ᵛ⦂ unit
  ex-var-⟨⟩ = var (Tl-⟨⟩ Hd) (et-ok unitₑ)

  ex-var-barrier : ∅ᴴ ∣ ((∅ᶜ ∷ unit) ⟨ rconst ⊤ᵣ ⟩) ⊢ᵛ⦂ unit
  ex-var-barrier = var (Tl-⟨⟩ Hd) (et-ok unitₑ)

  ex-seq : ∅ᴴ ∣ (∅ᶜ ∷ unit) ⊢ᶜ⦂ unit ! (𝟏̂ₑ ·̂ₑ 𝟏̂ₑ)
  ex-seq = return ⋆ ⨟ return ⋆

  ex-unbox : ∅ᴴ ∣ (∅ᶜ ∷ [ 𝟏̂ᵣ ] unit) ⊢ᶜ⦂ unit ! 𝟏̂ₑ
  ex-unbox = unbox (res-var Hd) ⊩≾̂ᵣ-refl (return ⋆)

  ex-unbox-ann : ∅ᴴ ∣ (∅ᶜ ∷ [ 𝟏̂ᵣ ] unit) ⊢ᶜ⦂ unit ! 𝟏̂ₑ
  ex-unbox-ann = unbox (res-ann 𝟏̂ᵣ unit (res-var Hd) ⊩≾̂ᵣ-refl unitₛ) ⊩≾̂ᵣ-refl (return ⋆)
