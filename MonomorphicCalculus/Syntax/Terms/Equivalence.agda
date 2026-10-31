-------------------------------------------------------------------------
-- Terms up to irrelevant stored data.                                 --
--                                                                     --
-- A term stores three pieces of data no rule inspects: a `var`'s side --
-- condition, a subsumption's subtyping witness, and an `unbox`'s      --
-- grade bound. The first is an irrelevant argument, so it is never    --
-- compared; the other two are proof-irrelevant (`<:ᵛ-irrelevant`/     --
-- `<:ᶜ-irrelevant`, `≾ᵣ-irrelevant`), so terms differing only in them --
-- are propositionally equal.                                          --
--                                                                     --
-- Equality of terms is therefore `_≡_`, and the congruence at each    --
-- former is `cong`/`cong₂`. Named here are only the four that are     --
-- not: the three irrelevance laws, and `handler-≡`, whose clause      --
-- family is compared pointwise and so needs `fun-ext`.                --
-------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.Syntax.Terms.Equivalence (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts   Spec
open import MonomorphicCalculus.Syntax.Terms   Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming   Spec
open import MonomorphicCalculus.Syntax.Types Spec
open import MonomorphicCalculus.Syntax.Renaming.Equivalence  Spec

-- Subsumption is compared at the subsumed term; the witness is irrelevant.

subV-≡ : ∀ {Γ A A'} {p p' : A <:ᵛ A'} {V V' : Γ ⊢ᵛ⦂ A}
       → V ≡ V' → subV V p ≡ subV V' p'
subV-≡ {p = p} {p' = p'} {V = V} refl =
  cong (subV V) (<:ᵛ-irrelevant p p')

subC-≡ : ∀ {Γ C C'} {p p' : C <:ᶜ C'} {M M' : Γ ⊢ᶜ⦂ C}
       → M ≡ M' → subC M p ≡ subC M' p'
subC-≡ {p = p} {p' = p'} {M = M} refl =
  cong (subC M) (<:ᶜ-irrelevant p p')

-- `unbox` is compared at the resource variable it names, together with the
-- declared box type that variable stands at; the grade bound and the payload
-- subsumption it stores alongside are irrelevant.

unbox-≡ : ∀ {Γ A C ρ₀ ρ₀' A₀ A₀' ρ' ρ''}
            {x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ} {y : [ ρ₀' ] A₀' ∈[ ρ'' ] Γ}
            {rel : ρ' ≾ᵣ ρ₀} {rel' : ρ'' ≾ᵣ ρ₀'}
            {p : A₀ <:ᵛ A} {p' : A₀' <:ᵛ A} {M M' : Γ ∷ A ⊢ᶜ⦂ C}
        → _≡_ {A = RVar Γ} (ρ₀ , A₀ , ρ' , x) (ρ₀' , A₀' , ρ'' , y) → M ≡ M'
        → unbox x rel p M ≡ unbox y rel' p' M'
unbox-≡ {x = x} {rel = rel} {rel' = rel'} {p = p} {p' = p'} {M = M} refl refl =
  cong₂ (λ r q → unbox x r q M)
        (≾ᵣ-irrelevant rel rel')
        (<:ᵛ-irrelevant p p')

-- The clause family is a function of the operation and its effect, so its
-- congruence goes through `fun-ext`.

handler-≡ : ∀ {Γ A B ε ε'}
              {N N' : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'}
              {H H' : (op : Op) → (ε'' : E) →
                        Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                          ∷ [ ∣ op-grade op ∣ᵉ ]
                              (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                        ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε'')}
          → N ≡ N'
          → (∀ op ε'' → H op ε'' ≡ H' op ε'')
          → handler N H ≡ handler N' H'
handler-≡ {N = N} refl eH =
  cong (handler N) (fun-ext (λ op → fun-ext (λ ε'' → eH op ε'')))
