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

    -- pairing

    ⦉_,_⦊    : {A B : VType}
            → Γ ⊢V⦂ A
            → Γ ⊢V⦂ B
            ---------------
            → Γ ⊢V⦂ A |×| B

    -- lambda abstraction
          
    lam     : {A : VType}
            → {C : CType}
            → Γ ∷ A ⊢C⦂ C
            -------------
            → Γ ⊢V⦂ A ⇒ C


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
            → (τ : ℕ)
            → Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε
            ------------------------------
            → Γ ⊢C⦂ A ‼ (of-natᵉ τ ·ₑ ε)

    -- effect handling

    -- The operation clauses may close over the *eternal* part of the ambient
    -- context `Γ` (the variables whose types survive arbitrary time-passage),
    -- captured by the eternal restriction `Γ ᴱ`; the parameter and boxed
    -- continuation are added on top. Being eternal, `Γ ᴱ` is an eternal context
    -- (`ᴱ-EternalCtx`), so `Γ ᴱ` includes back into `Γ` as a renaming
    -- (`ᴱ-ren`) — the rules that use a clause apply that renaming themselves.

    handle_`with_`in
            : {A B : VType}
            → {ε ε' : E}
            → Γ ⊢C⦂ A ‼ ε
            → ((op : Op) → (ε'' : E) →
                 Γ ᴱ ∷ type-of-gtype (param op)
                   ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                 ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
            → Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'
            ---------------------------------------------------------------------
            → Γ ⊢C⦂ B ‼ (ε ·ₑ ε')

    -- unboxing a boxed value/resource after enough time has passed for it to be ready

    -- The value being unboxed is a variable of box type `[ ρ ] A`: every value of
    -- a graded modal type is one (`grad-typ⇒var` below). That enough time has
    -- passed since it was brought into scope is the grade bound `ρ' ≾ᵣ ρ`, where
    -- `ρ'` is the product of the locks standing to the variable's right. Reading
    -- that product off the context is what rewinds it to the variable's world,
    -- with no subtraction operation on contexts.

    unbox   : {A : VType}
            → {C : CType}
            → {ρ ρ' : R}
            → [ ρ ] A ∈[ ρ' ] Γ
            → ρ' ≾ᵣ ρ
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

    -- (shallow explicit) sub-effecting

    coerce : {A : VType}
           → {ε ε' : E}
           → ε ≾ₑ ε'
           → Γ ⊢C⦂ A ‼ ε
           --------------
           → Γ ⊢C⦂ A ‼ ε'

-- Useful substitution of effect annotations

ε-subst : ∀ {Γ A ε ε'}
          → ε ≡ ε'
          → Γ ⊢C⦂ A ‼ ε
          ---------------
          → Γ ⊢C⦂ A ‼ ε'

ε-subst refl M = M

-- Values with graded modal types are variables

grad-typ⇒var : ∀ {Γ A ρ}
             → (V : Γ ⊢V⦂ [ ρ ] A)
             → Σ[ ρ' ∈ R ] Σ[ x ∈ ([ ρ ] A ∈[ ρ' ] Γ) ] Σ[ f ∈ (¬ Eternal ([ ρ ] A) → ρ' ≾ᵣ uᵣ) ] (V ≡ var f x)

grad-typ⇒var (var f x) = _ , x , f , refl

-- Values typing with eternal types can type under any grade extension of its typing context

eternal-val-ext : ∀ {Γ A ρ} → Eternal A → Γ ⊢V⦂ A → Γ ⟨ ρ ⟩ ⊢V⦂ A
eternal-val-ext et (var _ x) =
  var (λ ¬et → ⊥-elim (¬et et)) (Tl-⟨⟩ x)
eternal-val-ext _ (const b) =
  const b
eternal-val-ext _ ⋆ =
  ⋆
eternal-val-ext (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ =
  ⦉ eternal-val-ext et₁ V₁ , eternal-val-ext et₂ V₂ ⦊

-- An eternal-typed value mentions only eternal variables, so it restricts to
-- the eternal part of its typing context. This is the value-level counterpart
-- of `restrict-ren`, and lets effect handler clauses closing over `Γ ᴱ` be
-- substituted into.

eternal-val-restrict : ∀ {Γ A} → Eternal A → Γ ⊢V⦂ A → Γ ᴱ ⊢V⦂ A
eternal-val-restrict et (var _ x) =
  var (λ ¬et → ⊥-elim (¬et et)) (∈-ᴱ et x)
eternal-val-restrict _ (const b) =
  const b
eternal-val-restrict _ ⋆ =
  ⋆
eternal-val-restrict (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ =
  ⦉ eternal-val-restrict et₁ V₁ , eternal-val-restrict et₂ V₂ ⦊
