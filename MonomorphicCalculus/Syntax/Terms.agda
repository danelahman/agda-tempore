---------------------------------------
-- Well-typed syntax of the language --
---------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum

open import Relation.Nullary using (¬_)

open import Grades.Base
open import Language.Spec
open import Language.Operations
open import Language.Comparisons using (Cmp)

open import Util.Equality

module MonomorphicCalculus.Syntax.Terms (S : LanguageSpec) where

open import Data.Nat public

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts S
open import MonomorphicCalculus.Syntax.Types    S

-- Re-exported because the typing rules' own premises mention `_<:ᵛ_`: anything
-- that builds a term needs the relation in scope.

open import MonomorphicCalculus.Syntax.Subtyping S public

-- Well-typed terms (values and computations)

infix 26 _⊢ᵛ⦂_
infix 26 _⊢ᶜ⦂_

mutual

  data _⊢ᵛ⦂_ (Γ : Ctx) : VType → Set where

    -- variables, under the side condition `A Et∨≾ᵘ ρ`. The term does not
    -- record which disjunct holds, so the condition is irrelevant.

    var     : {A : VType}
            → {ρ : R}
            → A ∈[ ρ ] Γ
            → .(A Et∨≾ᵘ ρ)
            -------------
            → Γ ⊢ᵛ⦂ A

    -- base-typed constants

    const   : (B : BaseType)
            → BaseConstants B
            -----------------
            → Γ ⊢ᵛ⦂ Base B

    -- unit type

    ⋆       :
              -----------
              Γ ⊢ᵛ⦂ unit

    -- booleans

    true    :
              -----------
              Γ ⊢ᵛ⦂ bool

    false   :
              -----------
              Γ ⊢ᵛ⦂ bool

    -- natural numbers

    zero    :
              ----------
              Γ ⊢ᵛ⦂ nat

    succ    : Γ ⊢ᵛ⦂ nat
              ---------
            → Γ ⊢ᵛ⦂ nat

    -- pairing

    ⦉_,_⦊    : {A B : VType}
            → Γ ⊢ᵛ⦂ A
            → Γ ⊢ᵛ⦂ B
            ---------------
            → Γ ⊢ᵛ⦂ A |×| B

    -- injections into a sum

    inl     : {A B : VType}
            → Γ ⊢ᵛ⦂ A
            ---------------
            → Γ ⊢ᵛ⦂ A |+| B

    inr     : {A B : VType}
            → Γ ⊢ᵛ⦂ B
            ---------------
            → Γ ⊢ᵛ⦂ A |+| B

    -- lists

    nil     : {A : VType}
              ---------------
            → Γ ⊢ᵛ⦂ list A

    cons    : {A : VType}
            → Γ ⊢ᵛ⦂ A
            → Γ ⊢ᵛ⦂ list A
            ---------------
            → Γ ⊢ᵛ⦂ list A

    -- comparison at an eternal type

    -- One rule for the six relations of `Cmp`: both operands at one
    -- eternal type, the outcome a boolean.

    cmp     : {A : VType}
            → (⋈ : Cmp)
            → Γ ⊢ᵛ⦂ A
            → Γ ⊢ᵛ⦂ A
            → Et A
            -----------
            → Γ ⊢ᵛ⦂ bool

    -- lambda abstraction
          
    fun     : {A : VType}
            → {C : CType}
            → Γ ∷ A ⊢ᶜ⦂ C
            -------------
            → Γ ⊢ᵛ⦂ A ⇒ C

    -- handlers: the return clause binds the handled computation's result
    -- behind the modality of its effect, as the continuation of `_⨟_`. An
    -- operation clause runs at a time the handler does not fix, so its view
    -- of the ambient context `Γ` is barred by the `≾ᵣ`-greatest modality
    -- `⟨ ⊤ᵣ ⟩`; the parameter and boxed continuation are added on top.

    handler : {A B : VType}
            → {ε ε' : E}
            → Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'
            → ((op : Op) → (ε'' : E) →
                 Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                   ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                 ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε''))
            ---------------------------------------------------------------------
            → Γ ⊢ᵛ⦂ (A ! ε) ⇛ (B ! ε')

    -- subsumption
    --
    -- Erased: a value is retyped, never transformed, so no coercion is
    -- computed and nothing is eta-expanded.

    subV    : {A A' : VType}
            → Γ ⊢ᵛ⦂ A
            → A <:ᵛ A'
            -----------
            → Γ ⊢ᵛ⦂ A'

  data _⊢ᶜ⦂_ (Γ : Ctx) : CType → Set where

    -- returning a value

    return  : {A : VType}
            → Γ ⊢ᵛ⦂ A
            -------------
            → Γ ⊢ᶜ⦂ A ! 𝟏ₑ

    -- sequential composition (the bound variable is a de Bruijn index)

    _⨟_     : {A B : VType}      -- input: \;2
            → {ε' : E}
            → {ε : E}
            → Γ ⊢ᶜ⦂ A ! ε
            → Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'
            -----------------------------
            → Γ ⊢ᶜ⦂ B ! (ε ·ₑ ε')

    -- function application
    
    _·_     : {A : VType}
            → {C : CType}
            → Γ ⊢ᵛ⦂ A ⇒ C
            → Γ ⊢ᵛ⦂ A
            -------------
            → Γ ⊢ᶜ⦂ C

    -- pattern-matching

    match_`with_ : {A B : VType}
                 → {C : CType}
                 → Γ ⊢ᵛ⦂ A |×| B
                 → Γ ∷ A ∷ B ⊢ᶜ⦂ C
                 -----------------
                 → Γ ⊢ᶜ⦂ C

    -- empty type elimination

    absurd  : {C : CType}
            → Γ ⊢ᵛ⦂ empty
            -------------
            → Γ ⊢ᶜ⦂ C

    -- boolean elimination

    -- Both branches are typed at the same computation type `C`; differing
    -- types are equalised by subsumption.

    if_`then_`else_
            : {C : CType}
            → Γ ⊢ᵛ⦂ bool
            → Γ ⊢ᶜ⦂ C
            → Γ ⊢ᶜ⦂ C
            ------------
            → Γ ⊢ᶜ⦂ C

    -- natural-number elimination

    -- As for `if`, both branches are typed at the same computation type;
    -- the successor branch binds the predecessor.

    matchℕ_`zero_`succ_
            : {C : CType}
            → Γ ⊢ᵛ⦂ nat
            → Γ ⊢ᶜ⦂ C
            → Γ ∷ nat ⊢ᶜ⦂ C
            ---------------
            → Γ ⊢ᶜ⦂ C

    -- primitive recursion on natural numbers

    -- The step runs at a time the recursion does not fix, so, as a handler
    -- clause, it sees the ambient context barred by `⟨ ⊤ᵣ ⟩`; it binds the
    -- predecessor, and, as `_⨟_` binds its continuation, the result of the
    -- recursive call. The effect absorbs its own iteration.

    recℕ    : {B : VType}
            → {ε : E}
            → Γ ⊢ᵛ⦂ nat
            → Γ ⊢ᶜ⦂ B ! ε
            → (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε
            → ε ·ₑ ε ≾ₑ ε
            ------------------------------------------
            → Γ ⊢ᶜ⦂ B ! ε

    -- sum elimination

    -- As for `if`, both branches are typed at the same computation type;
    -- each binds the injected value.

    match+_`inl_`inr_
            : {A B : VType}
            → {C : CType}
            → Γ ⊢ᵛ⦂ A |+| B
            → Γ ∷ A ⊢ᶜ⦂ C
            → Γ ∷ B ⊢ᶜ⦂ C
            ---------------
            → Γ ⊢ᶜ⦂ C

    -- list elimination

    -- As for `if`, both branches are typed at the same computation type;
    -- the `cons` branch binds the head and then the tail, as `match`.

    matchL_`nil_`cons_
            : {A : VType}
            → {C : CType}
            → Γ ⊢ᵛ⦂ list A
            → Γ ⊢ᶜ⦂ C
            → Γ ∷ A ∷ list A ⊢ᶜ⦂ C
            ------------------------
            → Γ ⊢ᶜ⦂ C

    -- primitive recursion on lists

    -- As for `recℕ`: the step sees the ambient context behind `⟨ ⊤ᵣ ⟩`,
    -- binds the head and the tail, and, behind the modality of the recursion's
    -- grade, the result of the recursive call on the tail.

    recL    : {A B : VType}
            → {ε : E}
            → Γ ⊢ᵛ⦂ list A
            → Γ ⊢ᶜ⦂ B ! ε
            → (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε
            → ε ·ₑ ε ≾ₑ ε
            ----------------------------------------------------
            → Γ ⊢ᶜ⦂ B ! ε

    -- performing algebraic operations

    perform : {A : VType}
            → {ε : E}
            → (op : Op)
            → Γ ⊢ᵛ⦂ ⌜ param op ⌝ᵍ
            → Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ A ! ε
            ---------------------------------------------------------------
            → Γ ⊢ᶜ⦂ A ! ((op-grade op) ·ₑ ε)

    -- explicit delaying of a computation

    delay   : {A : VType}
            → {ε : E}
            → (τ : 𝔻)
            → Γ ⟨ ιᵣ τ ⟩ ⊢ᶜ⦂ A ! ε
            ------------------------------
            → Γ ⊢ᶜ⦂ A ! (ιₑ τ ·ₑ ε)

    -- effect handling

    handle_`with_
            : {A B : VType}
            → {ε ε' : E}
            → Γ ⊢ᶜ⦂ A ! ε
            → Γ ⊢ᵛ⦂ (A ! ε) ⇛ (B ! ε')
            --------------------------
            → Γ ⊢ᶜ⦂ B ! (ε ·ₑ ε')

    -- unboxing a boxed value/resource after enough time has passed for it to be ready

    -- The value being unboxed is a variable of box type, named at its declared
    -- type `[ ρ₀ ] A₀`; the premise `A₀ <:ᵛ A` lets the continuation bind any
    -- supertype of the payload. That enough time has passed is the grade bound
    -- `ρ' ≾ᵣ ρ₀`, with `ρ'` the product of the modalities standing to the
    -- variable's right.

    unbox   : {A A₀ : VType}
            → {C : CType}
            → {ρ₀ ρ' : R}
            → [ ρ₀ ] A₀ ∈[ ρ' ] Γ
            → ρ' ≾ᵣ ρ₀
            → A₀ <:ᵛ A
            → Γ ∷ A ⊢ᶜ⦂ C
            ---------------------------
            → Γ ⊢ᶜ⦂ C

    -- boxing up a value/resource that is ready for use in at least `ρ` grade steps

    box     : {A : VType}
            → {C : CType}
            → (ρ : R)
            → Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A
            → Γ ∷ [ ρ ] A ⊢ᶜ⦂ C
            --------------------
            → Γ ⊢ᶜ⦂ C

    -- subsumption

    subC    : {C C' : CType}
            → Γ ⊢ᶜ⦂ C
            → C <:ᶜ C'
            -----------
            → Γ ⊢ᶜ⦂ C'

-- Handling with a handler written in place

handle_`with_`in_ : ∀ {Γ A B ε ε'}
                  → Γ ⊢ᶜ⦂ A ! ε
                  → ((op : Op) → (ε'' : E) →
                       Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                         ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                       ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε''))
                  → Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'
                  ---------------------------------------------------------------------
                  → Γ ⊢ᶜ⦂ B ! (ε ·ₑ ε')

handle M `with H `in N = handle M `with handler N H

-- Sub-effecting, recovered as subsumption at an effect-only derivation

coerce : ∀ {Γ A ε ε'}
       → ε ≾ₑ ε'
       → Γ ⊢ᶜ⦂ A ! ε
       --------------
       → Γ ⊢ᶜ⦂ A ! ε'

coerce {A = A} p M = subC M (<:ᵛ-refl A !ₛ p)

-- Numerals

numeralᵛ : ∀ {Γ} → ℕ → Γ ⊢ᵛ⦂ nat
numeralᵛ 0       = zero
numeralᵛ (suc k) = succ (numeralᵛ k)

-- Useful substitution of effect annotations

ε-subst : ∀ {Γ A ε ε'}
          → ε ≡ ε'
          → Γ ⊢ᶜ⦂ A ! ε
          ---------------
          → Γ ⊢ᶜ⦂ A ! ε'

ε-subst refl M = M

-- Regrading along an equivalence of effects, as sub-effecting

ε-≃ : ∀ {Γ A ε ε'}
    → ε ≃ₑ ε'
    → Γ ⊢ᶜ⦂ A ! ε
    ---------------
    → Γ ⊢ᶜ⦂ A ! ε'

ε-≃ e M = coerce (proj₁ e) M

-- Values with graded modal types are variables, up to subsumption: the
-- occurrence is at the declared box type, which the value's type only
-- bounds.

grad-typ⇒var<: : ∀ {Γ A ρ}
               → Γ ⊢ᵛ⦂ [ ρ ] A
               → Σ[ ρ₀ ∈ R ] Σ[ A₀ ∈ VType ] Σ[ ρ' ∈ R ]
                   (([ ρ₀ ] A₀ ∈[ ρ' ] Γ) × ([ ρ₀ ] A₀ <:ᵛ [ ρ ] A) × ρ' ≾ᵣ 𝟏ᵣ)

grad-typ⇒var<: (var x f) =
  _ , _ , _ , x , <:ᵛ-refl _ , Et∨≾ᵘ→¬Et⇒≾ f (λ ())
grad-typ⇒var<: (subV V p@([ _ ]ₛ _)) with grad-typ⇒var<: V
... | ρ₀ , A₀ , ρ' , x , q , b =
  ρ₀ , A₀ , ρ' , x , <:ᵛ-trans q p , b

-- A value of eternal type stays typed under any grade extension of its context

eternal-val-ext : ∀ {Γ A ρ} → Et A → Γ ⊢ᵛ⦂ A → Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A
eternal-val-ext et (var x _) =
  var (Tl-⟨⟩ x) (et-ok et)
eternal-val-ext _ (const B b) =
  const B b
eternal-val-ext _ ⋆ =
  ⋆
eternal-val-ext _ true =
  true
eternal-val-ext _ false =
  false
eternal-val-ext _ zero =
  zero
eternal-val-ext et (succ V) =
  succ (eternal-val-ext et V)
eternal-val-ext (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ =
  ⦉ eternal-val-ext et₁ V₁ , eternal-val-ext et₂ V₂ ⦊
eternal-val-ext (et₁ |+|ₑ _) (inl V) =
  inl (eternal-val-ext et₁ V)
eternal-val-ext (_ |+|ₑ et₂) (inr V) =
  inr (eternal-val-ext et₂ V)
eternal-val-ext _ nil =
  nil
eternal-val-ext (listₑ et) (cons V W) =
  cons (eternal-val-ext et V) (eternal-val-ext (listₑ et) W)
eternal-val-ext _ (cmp ⋈ V W et) =
  cmp ⋈ (eternal-val-ext et V) (eternal-val-ext et W) et
eternal-val-ext et (subV V p) =
  subV (eternal-val-ext (<:ᵛ-eternalˡ p et) V) p
