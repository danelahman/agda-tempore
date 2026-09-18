------------------------------------------------------------------
-- Well-typed syntax of the mirrored (open) language              --
--                                                                --
-- The intrinsic judgements `Q ∣ Γ ⊢V⦂ A` and `Q ∣ Γ ⊢C⦂ C`       --
-- mirror `Syntax.Language` former by former, with grades and     --
-- types replaced by open expressions and with the side           --
-- conditions of the original discharged by entailment from the   --
-- hypothesis set `Q` instead of by closed-grade facts.           --
--                                                                --
-- Three rules deviate, each marked at its definition: `var` and  --
-- `unbox` are indexed by whether their variable is reached by    --
-- crossing an `_ᴱ̂` barrier, and `handle` types its operation     --
-- clauses at the extended scope `Θ +e`, the original's meta-level --
-- quantification over the continuation grade becoming a rigid    --
-- effect-grade variable.                                         --
------------------------------------------------------------------

-- `Bool` is renamed, as `OVType` has a constructor of that name
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import Inference.Scopes

module Inference.Open.Language (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

-- Only the base-type signature is needed; the type formers of the closed
-- language would otherwise clash with those of `OVType`/`OCType`.

open import Syntax.Types S using (BaseType; BaseConstants)

open import Inference.Open.Grades   S
open import Inference.Open.Types    S
open import Inference.Open.Contexts S
open import Inference.Open.Hyps     S

--------------------------------------------------------------
-- Side conditions of the two barrier-sensitive rules         --
--------------------------------------------------------------

-- What a use of a variable has to establish. The original demands
-- `¬ Eternal A → ρ ≾ᵣ uᵣ`; at open types `Eternal` is undecided, so the
-- implication becomes a disjunction. A use that crosses a barrier drops the
-- second disjunct and the grade with it: the eternality obligation is
-- unconditional.

VarOK : ∀ {Θ} → Hyps Θ → OVType Θ → RExp Θ → 𝔹 → Set
VarOK Q A ρ true  = Q ⊩ᴱ A
VarOK Q A ρ false = (Q ⊩ᴱ A) ⊎ (Q ⊩ ρ ≾̂ᵣ ûᵣ)

-- What an unboxing has to establish. Away from a barrier it is the original's
-- grade bound `ρ' ≾ᵣ ρ`. Across a barrier it is unsatisfiable: a box type is
-- never eternal, so the continuation of a handler clause cannot escape.

UnboxOK : ∀ {Θ} → Hyps Θ → RExp Θ → RExp Θ → 𝔹 → Set
UnboxOK Q ρ' ρ true  = ⊥
UnboxOK Q ρ' ρ false = Q ⊩ ρ' ≾̂ᵣ ρ

--------------------------------------------------------------
-- Well-typed terms (values and computations)                --
--------------------------------------------------------------

infix 26 _∣_⊢V⦂_
infix 26 _∣_⊢C⦂_

mutual

  data _∣_⊢V⦂_ {Θ : Scope} {n : ℕ} (Q : Hyps Θ) (Γ : OCtx Θ n) : OVType Θ → Set where

    -- variables

    -- DEVIATION: the premise is `VarOK`, whose shape is determined by the
    -- membership witness — one constructor covering the rule's two modes.

    var     : {A : OVType Θ}
            → {ρ : RExp Θ}
            → (x : A ∈̂[ ρ ] Γ)
            → VarOK Q A ρ (crossesᴱ̂ x)
            --------------------------
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

    -- pairing

    ⦉_,_⦊    : {A B : OVType Θ}
            → Q ∣ Γ ⊢V⦂ A
            → Q ∣ Γ ⊢V⦂ B
            -------------------
            → Q ∣ Γ ⊢V⦂ A |×| B

    -- lambda abstraction

    lam     : {A : OVType Θ}
            → {C : OCType Θ}
            → Q ∣ Γ ∷ A ⊢C⦂ C
            -----------------
            → Q ∣ Γ ⊢V⦂ A ⇒ C


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

    -- Both branches are typed at the same computation type `C`, so they carry
    -- the same effect grade; differing grades are equalised by `coerce`.

    if_`then_`else_
            : {C : OCType Θ}
            → Q ∣ Γ ⊢V⦂ Bool
            → Q ∣ Γ ⊢C⦂ C
            → Q ∣ Γ ⊢C⦂ C
            ----------------
            → Q ∣ Γ ⊢C⦂ C

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
            → (τ : ℕ)
            → Q ∣ Γ ⟨ rconst (of-natʳ τ) ⟩ ⊢C⦂ A ‼ ε
            ----------------------------------------
            → Q ∣ Γ ⊢C⦂ A ‼ (econst (of-natᵉ τ) ·̂ₑ ε)

    -- effect handling

    -- The operation clauses are typed behind the barrier `_ᴱ̂`, the mirrored
    -- eternal restriction of the ambient context: no entry is dropped and no
    -- lock stands above it, but every use of an ambient variable inside a
    -- clause crosses it and so owes an unconditional eternality entailment
    -- (`var`), while unboxing across it is impossible (`unbox`).

    -- DEVIATION: the original quantifies the clause family over the
    -- continuation grade `ε''` at the meta level. Here the clauses are typed
    -- once, at the extended scope `Θ +e`, against the *rigid* effect-grade
    -- variable `evar newᵉ`; `Q` and `Γ` are weakened into that scope, while
    -- the closed embeddings `⌜_⌝ᵍ` are formed at `Θ +e` directly.

    handle_`with_`in
            : {A B : OVType Θ}
            → {ε ε' : EExp Θ}
            → Q ∣ Γ ⊢C⦂ A ‼ ε
            → ((op : Op) →
                 wkᵉ-H Q ∣ (wkᵉ-ctx Γ) ᴱ̂ ∷ ⌜ param op ⌝ᵍ
                             ∷ [ rconst (mapᵉ (op-grade op)) ]
                                 (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ}))
                   ⊢C⦂ wkᵉ-v B ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ})))
            → Q ∣ Γ ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ A ⊢C⦂ B ‼ ε'
            ---------------------------------------------------------------
            → Q ∣ Γ ⊢C⦂ B ‼ (ε ·̂ₑ ε')

    -- unboxing a boxed value/resource after enough time has passed for it to be ready

    -- As in the original, the value being unboxed is a variable of box type
    -- `[ ρ ] A`, and the time that has passed since it was brought into scope
    -- is the grade `ρ'` read off the context.

    -- DEVIATION: the premise is `UnboxOK`, the grade bound `Q ⊩ ρ' ≾̂ᵣ ρ` for a
    -- variable that stays on this side of a barrier and `⊥` for one that does
    -- not (see `UnboxOK`).

    unbox   : {A : OVType Θ}
            → {C : OCType Θ}
            → {ρ ρ' : RExp Θ}
            → (x : [ ρ ] A ∈̂[ ρ' ] Γ)
            → UnboxOK Q ρ' ρ (crossesᴱ̂ x)
            → Q ∣ Γ ∷ A ⊢C⦂ C
            -----------------------------
            → Q ∣ Γ ⊢C⦂ C

    -- boxing up a value/resource that is ready for use in at least `ρ` grade steps

    -- DEVIATION: the grade is explicit; it is bound existentially by inference.

    box     : {A : OVType Θ}
            → {C : OCType Θ}
            → (ρ : RExp Θ)
            → Q ∣ Γ ⟨ ρ ⟩ ⊢V⦂ A
            → Q ∣ Γ ∷ [ ρ ] A ⊢C⦂ C
            -----------------------
            → Q ∣ Γ ⊢C⦂ C

    -- (shallow explicit) sub-effecting

    coerce : {A : OVType Θ}
           → {ε ε' : EExp Θ}
           → Q ⊩ ε ≾̂ₑ ε'
           → Q ∣ Γ ⊢C⦂ A ‼ ε
           ------------------
           → Q ∣ Γ ⊢C⦂ A ‼ ε'

--------------------------------------------------------------
-- Useful substitutions of annotations                       --
--------------------------------------------------------------

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

--------------------------------------------------------------
-- Sanity checks: the rules are usable                       --
--------------------------------------------------------------

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
  ex-var-lock = var (Tl-⟨⟩ Hd) (inj₁ Unitₑ)

  -- a variable used across a barrier: the eternality entailment is unconditional

  ex-var-barrier : ∅ᴴ ∣ ((∅ᶜ ∷ Unit) ᴱ̂) ⊢V⦂ Unit
  ex-var-barrier = var (Tl-ᴱ̂ Hd) Unitₑ

  -- returning a value, sequenced with another such computation

  ex-seq : ∅ᴴ ∣ (∅ᶜ ∷ Unit) ⊢C⦂ Unit ‼ (ûₑ ·̂ₑ ûₑ)
  ex-seq = return ⋆ ⨟ return ⋆

  -- unboxing a boxed variable, no time having passed since it came into scope

  ex-unbox : ∅ᴴ ∣ (∅ᶜ ∷ [ ûᵣ ] Unit) ⊢C⦂ Unit ‼ ûₑ
  ex-unbox = unbox Hd ⊩≾̂ᵣ-refl (return ⋆)
