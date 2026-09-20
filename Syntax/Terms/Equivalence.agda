------------------------------------------------------------------------
-- Terms up to irrelevant stored data.                                --
--                                                                    --
-- A term stores three pieces of data no rule inspects: a `var`'s      --
-- grade bound, a subsumption's subtyping witness, and an `unbox`'s    --
-- grade bound. All three are proof-irrelevant (`≾ᵣ-irrelevant`,       --
-- `<:ᵛ-irrelevant`/`<:ᶜ-irrelevant`, the first through `fun-ext`), so --
-- terms differing only in them are propositionally equal.            --
--                                                                    --
-- Equality of terms is therefore `_≡_`, and the congruence at each    --
-- former is `cong`/`cong₂`. Named here are only the five that are     --
-- not: the four irrelevance laws, and `handle-≡`, whose clause        --
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
open import Syntax.Subtyping  Spec
open import Syntax.Types      Spec
open import Syntax.Renamings.Equivalence Spec

-- A `var`'s grade bound is a function into an irrelevant relation.

bound-irr : ∀ {A ρ} → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ) → f ≡ f'
bound-irr f f' = fun-ext (λ z → ≾ᵣ-irrelevant _ _)

var-≡ : ∀ {Γ A ρ} {f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ} {x : A ∈[ ρ ] Γ}
      → var f x ≡ var f' x
var-≡ {f = f} {f' = f'} {x = x} = cong (λ g → var g x) (bound-irr f f')

subV-≡ : ∀ {Γ A A'} {p p' : A <:ᵛ A'} {V V' : Γ ⊢V⦂ A}
       → V ≡ V' → subV V p ≡ subV V' p'
subV-≡ {p = p} {p' = p'} {V = V} refl =
  cong (subV V) (<:ᵛ-irrelevant p p')

subC-≡ : ∀ {Γ C C'} {p p' : C <:ᶜ C'} {M M' : Γ ⊢C⦂ C}
       → M ≡ M' → subC M p ≡ subC M' p'
subC-≡ {p = p} {p' = p'} {M = M} refl =
  cong (subC M) (<:ᶜ-irrelevant p p')

-- `unbox<:` is compared at the *resource variable* it names, together with the
-- declared box type that variable stands at; the grade bound and the subtyping
-- witness it stores alongside are irrelevant.

unbox-≡ : ∀ {Γ A C ρ ρ₀ ρ₀' A₀ A₀' ρ' ρ''}
            {x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ} {y : [ ρ₀' ] A₀' ∈[ ρ'' ] Γ}
            {p : ([ ρ₀ ] A₀) <:ᵛ ([ ρ ] A)} {p' : ([ ρ₀' ] A₀') <:ᵛ ([ ρ ] A)}
            {rel : ρ' ≾ᵣ ρ} {rel' : ρ'' ≾ᵣ ρ} {M M' : Γ ∷ A ⊢C⦂ C}
        → _≡_ {A = RVar Γ} (ρ₀ , A₀ , ρ' , x) (ρ₀' , A₀' , ρ'' , y) → M ≡ M'
        → unbox<: x p rel M ≡ unbox<: y p' rel' M'
unbox-≡ {A = A} {ρ = ρ} {ρ₀ = ρ₀} {A₀ = A₀}
        {x = x} {p = p} {p' = p'} {rel = rel} {rel' = rel'} {M = M} refl refl =
  cong₂ (λ q r → unbox<: x q r M)
        (<:ᵛ-irrelevant {[ ρ₀ ] A₀} {[ ρ ] A} p p')
        (≾ᵣ-irrelevant rel rel')

-- The clause family is a function of the operation and its effect, so its
-- congruence goes through `fun-ext`.

handle-≡ : ∀ {Γ A B ε ε'} {M M' : Γ ⊢C⦂ A ‼ ε}
             {H H' : (op : Op) → (ε'' : E) →
                       Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
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
