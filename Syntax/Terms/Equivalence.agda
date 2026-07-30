------------------------------------------------------------------------
-- Terms up to irrelevant stored data.                                --
--                                                                    --
-- A term stores two pieces of data no rule inspects: a `var`'s grade  --
-- bound and a `coerce`'s effect ordering, plus the `unbox` node's own --
-- grade bound. All three are proof-irrelevant (`≾ᵣ-irrelevant`,       --
-- `≾ₑ-irrelevant`, the first through `fun-ext`), so terms carrying    --
-- them are propositionally equal and `_≐ᵛ_`/`_≐ᶜ_` are `_≡_`.         --
--                                                                    --
-- The combinators below are the congruences at each former, named so  --
-- that the metatheory reads uniformly.                               --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Terms.Equivalence (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   Spec
open import Syntax.Language   Spec
open import Syntax.RenActions Spec
open import Syntax.Renamings  Spec
open import Syntax.Types      Spec
open import Syntax.Renamings.Equivalence Spec

infix 4 _≐ᵛ_
infix 4 _≐ᶜ_

_≐ᵛ_ : ∀ {Γ A} → Γ ⊢V⦂ A → Γ ⊢V⦂ A → Set
_≐ᵛ_ = _≡_

_≐ᶜ_ : ∀ {Γ C} → Γ ⊢C⦂ C → Γ ⊢C⦂ C → Set
_≐ᶜ_ = _≡_

-- A `var`'s grade bound is a function into an irrelevant relation.

bound-irr : ∀ {A ρ} → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ) → f ≡ f'
bound-irr f f' = fun-ext (λ z → ≾ᵣ-irrelevant _ _)

-- CONGRUENCES, ONE PER FORMER
--
-- The three leaves that carry stored data go by irrelevance; the rest are
-- `cong`s.

var-≐   : ∀ {Γ A ρ} {f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ} {x : A ∈[ ρ ] Γ}
        → var f x ≐ᵛ var f' x
var-≐ {f = f} {f' = f'} {x = x} = cong (λ g → var g x) (bound-irr f f')

const-≐ : ∀ {Γ b} {c : BaseConstants b} → const {Γ} c ≐ᵛ const c
const-≐ = refl

⋆-≐     : ∀ {Γ} → ⋆ {Γ} ≐ᵛ ⋆
⋆-≐ = refl

pair-≐  : ∀ {Γ A B} {V V' : Γ ⊢V⦂ A} {W W' : Γ ⊢V⦂ B}
        → V ≐ᵛ V' → W ≐ᵛ W' → ⦉ V , W ⦊ ≐ᵛ ⦉ V' , W' ⦊
pair-≐ = cong₂ ⦉_,_⦊

lam-≐   : ∀ {Γ A C} {M M' : Γ ∷ A ⊢C⦂ C}
        → M ≐ᶜ M' → lam M ≐ᵛ lam M'
lam-≐ = cong lam

return-≐  : ∀ {Γ A} {V V' : Γ ⊢V⦂ A}
          → V ≐ᵛ V' → return V ≐ᶜ return V'
return-≐ = cong return

seq-≐     : ∀ {Γ A B ε ε'} {M M' : Γ ⊢C⦂ A ‼ ε}
              {N N' : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
          → M ≐ᶜ M' → N ≐ᶜ N' → (M ⨟ N) ≐ᶜ (M' ⨟ N')
seq-≐ = cong₂ _⨟_

app-≐     : ∀ {Γ A C} {V V' : Γ ⊢V⦂ A ⇒ C} {W W' : Γ ⊢V⦂ A}
          → V ≐ᵛ V' → W ≐ᵛ W' → (V · W) ≐ᶜ (V' · W')
app-≐ = cong₂ _·_

match-≐   : ∀ {Γ A B C} {V V' : Γ ⊢V⦂ A |×| B} {M M' : Γ ∷ A ∷ B ⊢C⦂ C}
          → V ≐ᵛ V' → M ≐ᶜ M'
          → (match V `in M) ≐ᶜ (match V' `in M')
match-≐ = cong₂ match_`in_

absurd-≐  : ∀ {Γ C} {V V' : Γ ⊢V⦂ Empty}
          → V ≐ᵛ V' → absurd {C = C} V ≐ᶜ absurd V'
absurd-≐ = cong absurd

perform-≐ : ∀ {Γ A ε} {op : Op} {V V' : Γ ⊢V⦂ type-of-gtype (param op)}
              {M M' : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                        ⊢C⦂ A ‼ ε}
          → V ≐ᵛ V' → M ≐ᶜ M'
          → perform op V M ≐ᶜ perform op V' M'
perform-≐ {op = op} = cong₂ (perform op)

delay-≐   : ∀ {Γ A ε} {τ : ℕ} {M M' : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε}
          → M ≐ᶜ M' → delay τ M ≐ᶜ delay τ M'
delay-≐ {τ = τ} = cong (delay τ)

handle-≐  : ∀ {Γ A B ε ε'} {M M' : Γ ⊢C⦂ A ‼ ε}
              {H H' : (op : Op) → (ε'' : E) →
                        Γ ᴱ ∷ type-of-gtype (param op)
                          ∷ [ mapᵉ (op-grade op) ]
                              (type-of-gtype (arity op) ⇒ B ‼ ε'')
                        ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
              {N N' : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
          → M ≐ᶜ M'
          → (∀ op ε'' → H op ε'' ≐ᶜ H' op ε'')
          → N ≐ᶜ N'
          → (handle M `with H `in N) ≐ᶜ (handle M' `with H' `in N')
handle-≐ {M = M} {N = N} refl eH refl =
  cong (λ H₀ → handle M `with H₀ `in N)
       (fun-ext (λ op → fun-ext (λ ε'' → eH op ε'')))

-- `unbox` is compared at the *resource variable* it names; the grade bound it
-- stores alongside is irrelevant.

unbox-≐   : ∀ {Γ A C ρ ρ' ρ''} {x : [ ρ ] A ∈[ ρ' ] Γ} {y : [ ρ ] A ∈[ ρ'' ] Γ}
              {rel : ρ' ≾ᵣ ρ} {rel' : ρ'' ≾ᵣ ρ} {M M' : Γ ∷ A ⊢C⦂ C}
          → _≡_ {A = Var Γ ([ ρ ] A)} (ρ' , x) (ρ'' , y) → M ≐ᶜ M'
          → unbox x rel M ≐ᶜ unbox y rel' M'
unbox-≐ {x = x} {rel = rel} {rel' = rel'} {M = M} refl refl =
  cong (λ r → unbox x r M) (≾ᵣ-irrelevant rel rel')

coerce-≐  : ∀ {Γ A ε ε'} {p p' : ε ≾ₑ ε'} {M M' : Γ ⊢C⦂ A ‼ ε}
          → M ≐ᶜ M' → coerce p M ≐ᶜ coerce p' M'
coerce-≐ {p = p} {p' = p'} {M = M} refl =
  cong (λ q → coerce q M) (≾ₑ-irrelevant p p')

box-≐     : ∀ {Γ A C ρ} {V V' : Γ ⟨ ρ ⟩ ⊢V⦂ A} {M M' : Γ ∷ [ ρ ] A ⊢C⦂ C}
          → V ≐ᵛ V' → M ≐ᶜ M' → box V M ≐ᶜ box V' M'
box-≐ = cong₂ box

-- Reflexivity, symmetry and transitivity.

≐ᵛ-refl : ∀ {Γ A} → (V : Γ ⊢V⦂ A) → V ≐ᵛ V
≐ᵛ-refl _ = refl

≐ᶜ-refl : ∀ {Γ C} → (M : Γ ⊢C⦂ C) → M ≐ᶜ M
≐ᶜ-refl _ = refl

≐ᵛ-trans : ∀ {Γ A} {V V' V'' : Γ ⊢V⦂ A} → V ≐ᵛ V' → V' ≐ᵛ V'' → V ≐ᵛ V''
≐ᵛ-trans = trans

≐ᶜ-trans : ∀ {Γ C} {M M' M'' : Γ ⊢C⦂ C} → M ≐ᶜ M' → M' ≐ᶜ M'' → M ≐ᶜ M''
≐ᶜ-trans = trans

≐ᵛ-sym : ∀ {Γ A} {V V' : Γ ⊢V⦂ A} → V ≐ᵛ V' → V' ≐ᵛ V
≐ᵛ-sym = sym

≐ᶜ-sym : ∀ {Γ C} {M M' : Γ ⊢C⦂ C} → M ≐ᶜ M' → M' ≐ᶜ M
≐ᶜ-sym = sym

-- Propositional equality of terms and the equivalence agree.

≡→≐ᵛ : ∀ {Γ A} {V V' : Γ ⊢V⦂ A} → V ≡ V' → V ≐ᵛ V'
≡→≐ᵛ e = e

≡→≐ᶜ : ∀ {Γ C} {M M' : Γ ⊢C⦂ C} → M ≡ M' → M ≐ᶜ M'
≡→≐ᶜ e = e

≐ᵛ→≡ : ∀ {Γ A} {V V' : Γ ⊢V⦂ A} → V ≐ᵛ V' → V ≡ V'
≐ᵛ→≡ e = e

≐ᶜ→≡ : ∀ {Γ C} {M M' : Γ ⊢C⦂ C} → M ≐ᶜ M' → M ≡ M'
≐ᶜ→≡ e = e
