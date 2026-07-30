------------------------------------------------------------------------
-- Terms up to irrelevant stored data.                                --
--                                                                    --
-- A term stores three pieces of data no rule inspects: a `var`'s      --
-- grade bound, a `coerce`'s effect ordering, and an `unbox`'s grade   --
-- bound. All three are proof-irrelevant (`≾ᵣ-irrelevant`,             --
-- `≾ₑ-irrelevant`, the first through `fun-ext`), so terms differing   --
-- only in them are propositionally equal.                            --
--                                                                    --
-- Equality of terms is therefore `_≡_`, and the congruence at each    --
-- former is `cong`/`cong₂`. Named here are only the four that are     --
-- not: the three irrelevance laws, and `handle-≡`, whose clause       --
-- family is compared pointwise and so needs `fun-ext`.                --
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

-- A `var`'s grade bound is a function into an irrelevant relation.

bound-irr : ∀ {A ρ} → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ) → f ≡ f'
bound-irr f f' = fun-ext (λ z → ≾ᵣ-irrelevant _ _)

var-≡ : ∀ {Γ A ρ} {f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ} {x : A ∈[ ρ ] Γ}
      → var f x ≡ var f' x
var-≡ {f = f} {f' = f'} {x = x} = cong (λ g → var g x) (bound-irr f f')

coerce-≡ : ∀ {Γ A ε ε'} {p p' : ε ≾ₑ ε'} {M M' : Γ ⊢C⦂ A ‼ ε}
         → M ≡ M' → coerce p M ≡ coerce p' M'
coerce-≡ {p = p} {p' = p'} {M = M} refl =
  cong (λ q → coerce q M) (≾ₑ-irrelevant p p')

-- `unbox` is compared at the *resource variable* it names; the grade bound it
-- stores alongside is irrelevant.

unbox-≡ : ∀ {Γ A C ρ ρ' ρ''} {x : [ ρ ] A ∈[ ρ' ] Γ} {y : [ ρ ] A ∈[ ρ'' ] Γ}
            {rel : ρ' ≾ᵣ ρ} {rel' : ρ'' ≾ᵣ ρ} {M M' : Γ ∷ A ⊢C⦂ C}
        → _≡_ {A = Var Γ ([ ρ ] A)} (ρ' , x) (ρ'' , y) → M ≡ M'
        → unbox x rel M ≡ unbox y rel' M'
unbox-≡ {x = x} {rel = rel} {rel' = rel'} {M = M} refl refl =
  cong (λ r → unbox x r M) (≾ᵣ-irrelevant rel rel')

-- The clause family is a function of the operation and its effect, so its
-- congruence goes through `fun-ext`.

handle-≡ : ∀ {Γ A B ε ε'} {M M' : Γ ⊢C⦂ A ‼ ε}
             {H H' : (op : Op) → (ε'' : E) →
                       Γ ᴱ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε'')
                       ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
             {N N' : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
         → M ≡ M'
         → (∀ op ε'' → H op ε'' ≡ H' op ε'')
         → N ≡ N'
         → (handle M `with H `in N) ≡ (handle M' `with H' `in N')
handle-≡ {M = M} {N = N} refl eH refl =
  cong (λ H₀ → handle M `with H₀ `in N)
       (fun-ext (λ op → fun-ext (λ ε'' → eH op ε'')))
