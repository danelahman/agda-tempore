---------------------------------------
-- Well-typed syntax of the language --
---------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Language (S : LanguageSpec) where

open import Data.Nat public

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   S
open import Syntax.Types      S

-- Re-exported because the typing rules' own premises mention `_<:ᵛ_`: anything
-- that builds a term needs the relation in scope.

open import Syntax.Subtyping S public

-- Well-typed terms (values and computations)

infix 26 _⊢V⦂_
infix 26 _⊢C⦂_

mutual

  data _⊢V⦂_ (Γ : Ctx) : VType → Set where

    -- variables

    var     : {A : VType}
            → {ρ : R}
            → (¬ Eternal A → ρ ≾ᵣ uᵣ)
            → A ∈[ ρ ] Γ
            -------------------------
            → Γ ⊢V⦂ A           

    -- base-typed constants

    const   : {B : BaseType}
            → BaseConstants B
            -----------------
            → Γ ⊢V⦂ Base B

    -- unit type

    ⋆       :
              -----------
              Γ ⊢V⦂ Unit

    -- booleans

    true    :
              -----------
              Γ ⊢V⦂ Bool

    false   :
              -----------
              Γ ⊢V⦂ Bool

    -- pairing

    ⦉_,_⦊    : {A B : VType}
            → Γ ⊢V⦂ A
            → Γ ⊢V⦂ B
            ---------------
            → Γ ⊢V⦂ A |×| B

    -- injections into a sum

    inl     : {A B : VType}
            → Γ ⊢V⦂ A
            ---------------
            → Γ ⊢V⦂ A |+| B

    inr     : {A B : VType}
            → Γ ⊢V⦂ B
            ---------------
            → Γ ⊢V⦂ A |+| B

    -- lambda abstraction
          
    lam     : {A : VType}
            → {C : CType}
            → Γ ∷ A ⊢C⦂ C
            -------------
            → Γ ⊢V⦂ A ⇒ C

    -- subsumption
    --
    -- Erased: a value is retyped, never transformed, so no coercion is
    -- computed and nothing is eta-expanded.

    subV    : {A A' : VType}
            → Γ ⊢V⦂ A
            → A <:ᵛ A'
            -----------
            → Γ ⊢V⦂ A'

  data _⊢C⦂_ (Γ : Ctx) : CType → Set where

    -- returning a value

    return  : {A : VType}
            → Γ ⊢V⦂ A
            -------------
            → Γ ⊢C⦂ A ‼ uₑ

    -- sequential composition (omitting the bound variable due to using de Bruijn indices)
    
    _⨟_     : {A B : VType}      -- NOTE: use \;2 to get this unicode semicolon
            → {ε' : E}
            → {ε : E}
            → Γ ⊢C⦂ A ‼ ε
            → Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'
            -----------------------------
            → Γ ⊢C⦂ B ‼ (ε ·ₑ ε')

    -- function application
    
    _·_     : {A : VType}
            → {C : CType}
            → Γ ⊢V⦂ A ⇒ C
            → Γ ⊢V⦂ A
            -------------
            → Γ ⊢C⦂ C

    -- pattern-matching

    match_`in_ : {A B : VType}
               → {C : CType}
               → Γ ⊢V⦂ A |×| B
               → Γ ∷ A ∷ B ⊢C⦂ C
               -----------------
               → Γ ⊢C⦂ C

    -- empty type elimination

    absurd  : {C : CType}
            → Γ ⊢V⦂ Empty
            -------------
            → Γ ⊢C⦂ C

    -- boolean elimination

    -- Both branches are typed at the same computation type `C`; differing
    -- types are equalised by subsumption.

    if_`then_`else_
            : {C : CType}
            → Γ ⊢V⦂ Bool
            → Γ ⊢C⦂ C
            → Γ ⊢C⦂ C
            ------------
            → Γ ⊢C⦂ C

    -- sum elimination

    -- As for `if`, both branches are typed at the same computation type;
    -- each binds the injected value.

    case+_`inl_`inr_
            : {A B : VType}
            → {C : CType}
            → Γ ⊢V⦂ A |+| B
            → Γ ∷ A ⊢C⦂ C
            → Γ ∷ B ⊢C⦂ C
            ---------------
            → Γ ⊢C⦂ C

    -- performing algebraic operations

    perform : {A : VType}
            → {ε : E}
            → (op : Op)
            → Γ ⊢V⦂ type-of-gtype (param op)
            → Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε
            ---------------------------------------------------------------
            → Γ ⊢C⦂ A ‼ ((op-grade op) ·ₑ ε)

    -- explicit delaying of a computation

    delay   : {A : VType}
            → {ε : E}
            → (τ : 𝔻)
            → Γ ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε
            ------------------------------
            → Γ ⊢C⦂ A ‼ (of-durᵉ τ ·ₑ ε)

    -- effect handling

    -- A clause runs at a time the handler does not fix, so its view of the
    -- ambient context `Γ` is barred by the `≾ᵣ`-greatest lock `⟨ ⊤ᵣ ⟩`; the
    -- parameter and boxed continuation are added on top.

    handle_`with_`in
            : {A B : VType}
            → {ε ε' : E}
            → Γ ⊢C⦂ A ‼ ε
            → ((op : Op) → (ε'' : E) →
                 Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                   ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                 ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
            → Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'
            ---------------------------------------------------------------------
            → Γ ⊢C⦂ B ‼ (ε ·ₑ ε')

    -- unboxing a boxed value/resource after enough time has passed for it to be ready

    -- The value being unboxed is a variable of box type, named at its declared
    -- type `[ ρ₀ ] A₀`; the premise `A₀ <:ᵛ A` lets the continuation bind any
    -- supertype of the payload. That enough time has passed is the grade bound
    -- `ρ' ≾ᵣ ρ₀`, with `ρ'` the product of the locks standing to the variable's
    -- right.

    unbox   : {A A₀ : VType}
            → {C : CType}
            → {ρ₀ ρ' : R}
            → [ ρ₀ ] A₀ ∈[ ρ' ] Γ
            → ρ' ≾ᵣ ρ₀
            → A₀ <:ᵛ A
            → Γ ∷ A ⊢C⦂ C
            ---------------------------
            → Γ ⊢C⦂ C

    -- boxing up a value/resource that is ready for use in at least `ρ` grade steps

    box     : {A : VType}
            → {C : CType}
            → {ρ : R}
            → Γ ⟨ ρ ⟩ ⊢V⦂ A
            → Γ ∷ [ ρ ] A ⊢C⦂ C
            --------------------
            → Γ ⊢C⦂ C

    -- subsumption

    subC    : {C C' : CType}
            → Γ ⊢C⦂ C
            → C <:ᶜ C'
            -----------
            → Γ ⊢C⦂ C'

-- Sub-effecting, recovered as subsumption at an effect-only derivation

coerce : ∀ {Γ A ε ε'}
       → ε ≾ₑ ε'
       → Γ ⊢C⦂ A ‼ ε
       --------------
       → Γ ⊢C⦂ A ‼ ε'

coerce {A = A} p M = subC M (<:ᵛ-refl A ‼ₛ p)

-- Useful substitution of effect annotations

ε-subst : ∀ {Γ A ε ε'}
          → ε ≡ ε'
          → Γ ⊢C⦂ A ‼ ε
          ---------------
          → Γ ⊢C⦂ A ‼ ε'

ε-subst refl M = M

-- Values with graded modal types are variables, up to subsumption: the
-- occurrence is at the *declared* box type, which the value's type only
-- bounds.

grad-typ⇒var<: : ∀ {Γ A ρ}
               → Γ ⊢V⦂ [ ρ ] A
               → Σ[ ρ₀ ∈ R ] Σ[ A₀ ∈ VType ] Σ[ ρ' ∈ R ]
                   (([ ρ₀ ] A₀ ∈[ ρ' ] Γ) × ([ ρ₀ ] A₀ <:ᵛ [ ρ ] A) × ρ' ≾ᵣ uᵣ)

grad-typ⇒var<: (var f x) =
  _ , _ , _ , x , <:ᵛ-refl _ , f (λ ())
grad-typ⇒var<: (subV V p@([ _ ]ₛ _)) with grad-typ⇒var<: V
... | ρ₀ , A₀ , ρ' , x , q , b =
  ρ₀ , A₀ , ρ' , x , <:ᵛ-trans q p , b

-- Values typing with eternal types can type under any grade extension of its typing context

eternal-val-ext : ∀ {Γ A ρ} → Eternal A → Γ ⊢V⦂ A → Γ ⟨ ρ ⟩ ⊢V⦂ A
eternal-val-ext et (var _ x) =
  var (λ ¬et → ⊥-elim (¬et et)) (Tl-⟨⟩ x)
eternal-val-ext _ (const b) =
  const b
eternal-val-ext _ ⋆ =
  ⋆
eternal-val-ext _ true =
  true
eternal-val-ext _ false =
  false
eternal-val-ext (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ =
  ⦉ eternal-val-ext et₁ V₁ , eternal-val-ext et₂ V₂ ⦊
eternal-val-ext (et₁ |+|ₑ _) (inl V) =
  inl (eternal-val-ext et₁ V)
eternal-val-ext (_ |+|ₑ et₂) (inr V) =
  inr (eternal-val-ext et₂ V)
eternal-val-ext et (subV V p) =
  subV (eternal-val-ext (<:ᵛ-eternalˡ p et) V) p
