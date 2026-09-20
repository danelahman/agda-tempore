-------------------------------------------------------------------
-- Shape-preserving subtyping of value and computation types      --
--                                                                --
-- `_<:ᵛ_` is a recursive predicate on the skeleton the two types --
-- share, not an inductive family, so reflexivity, transitivity   --
-- and proof irrelevance are lemmas rather than constructors.     --
--                                                                --
-- A function's domain and a box's grade are contravariant, a     --
-- computation's effect covariant. The box direction agrees with  --
-- `unbox`'s premise: a larger box grade is the weaker obligation. --
-------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

module Syntax.Subtyping (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S

infix 4 _<:ᵛ_ _<:ᶜ_ _∼ˢ_

-- The relation

_<:ᵛ_ : VType → VType → Set
_<:ᶜ_ : CType → CType → Set

Base b    <:ᵛ Base b'     = b ≡ b'
Unit      <:ᵛ Unit        = ⊤
Bool      <:ᵛ Bool        = ⊤
(A |×| B) <:ᵛ (A' |×| B') = A <:ᵛ A' × B <:ᵛ B'
Empty     <:ᵛ Empty       = ⊤
(A ⇒ C)   <:ᵛ (A' ⇒ C')   = A' <:ᵛ A × C <:ᶜ C'
([ ρ ] A) <:ᵛ ([ ρ' ] A') = ρ' ≾ᵣ ρ × A <:ᵛ A'
_         <:ᵛ _           = ⊥

(A ‼ ε) <:ᶜ (A' ‼ ε') = A <:ᵛ A' × ε ≾ₑ ε'

-- Relatedness of two types under `_<:ᵛ_` fixes their common skeleton.
-- Reading it off once is what keeps the lemmas below to one case per
-- type former instead of one per pair of type formers.

data _∼ˢ_ : VType → VType → Set where
  Baseˢ  : ∀ {b b'} → Base b ∼ˢ Base b'
  Unitˢ  : Unit ∼ˢ Unit
  Boolˢ  : Bool ∼ˢ Bool
  Prodˢ  : ∀ {A A' B B'} → (A |×| B) ∼ˢ (A' |×| B')
  Emptyˢ : Empty ∼ˢ Empty
  Arrˢ   : ∀ {A A' C C'} → (A ⇒ C) ∼ˢ (A' ⇒ C')
  Boxˢ   : ∀ {ρ ρ' A A'} → ([ ρ ] A) ∼ˢ ([ ρ' ] A')

<:ᵛ-shape : ∀ {A B} → A <:ᵛ B → A ∼ˢ B
<:ᵛ-shape {Base _}  {Base _}  _ = Baseˢ
<:ᵛ-shape {Base _}  {Unit}    ()
<:ᵛ-shape {Base _}  {Bool}    ()
<:ᵛ-shape {Base _}  {_ |×| _} ()
<:ᵛ-shape {Base _}  {Empty}   ()
<:ᵛ-shape {Base _}  {_ ⇒ _}   ()
<:ᵛ-shape {Base _}  {[ _ ] _} ()
<:ᵛ-shape {Unit}    {Base _}  ()
<:ᵛ-shape {Unit}    {Unit}    _ = Unitˢ
<:ᵛ-shape {Unit}    {Bool}    ()
<:ᵛ-shape {Unit}    {_ |×| _} ()
<:ᵛ-shape {Unit}    {Empty}   ()
<:ᵛ-shape {Unit}    {_ ⇒ _}   ()
<:ᵛ-shape {Unit}    {[ _ ] _} ()
<:ᵛ-shape {Bool}    {Base _}  ()
<:ᵛ-shape {Bool}    {Unit}    ()
<:ᵛ-shape {Bool}    {Bool}    _ = Boolˢ
<:ᵛ-shape {Bool}    {_ |×| _} ()
<:ᵛ-shape {Bool}    {Empty}   ()
<:ᵛ-shape {Bool}    {_ ⇒ _}   ()
<:ᵛ-shape {Bool}    {[ _ ] _} ()
<:ᵛ-shape {_ |×| _} {Base _}  ()
<:ᵛ-shape {_ |×| _} {Unit}    ()
<:ᵛ-shape {_ |×| _} {Bool}    ()
<:ᵛ-shape {_ |×| _} {_ |×| _} _ = Prodˢ
<:ᵛ-shape {_ |×| _} {Empty}   ()
<:ᵛ-shape {_ |×| _} {_ ⇒ _}   ()
<:ᵛ-shape {_ |×| _} {[ _ ] _} ()
<:ᵛ-shape {Empty}   {Base _}  ()
<:ᵛ-shape {Empty}   {Unit}    ()
<:ᵛ-shape {Empty}   {Bool}    ()
<:ᵛ-shape {Empty}   {_ |×| _} ()
<:ᵛ-shape {Empty}   {Empty}   _ = Emptyˢ
<:ᵛ-shape {Empty}   {_ ⇒ _}   ()
<:ᵛ-shape {Empty}   {[ _ ] _} ()
<:ᵛ-shape {_ ⇒ _}   {Base _}  ()
<:ᵛ-shape {_ ⇒ _}   {Unit}    ()
<:ᵛ-shape {_ ⇒ _}   {Bool}    ()
<:ᵛ-shape {_ ⇒ _}   {_ |×| _} ()
<:ᵛ-shape {_ ⇒ _}   {Empty}   ()
<:ᵛ-shape {_ ⇒ _}   {_ ⇒ _}   _ = Arrˢ
<:ᵛ-shape {_ ⇒ _}   {[ _ ] _} ()
<:ᵛ-shape {[ _ ] _} {Base _}  ()
<:ᵛ-shape {[ _ ] _} {Unit}    ()
<:ᵛ-shape {[ _ ] _} {Bool}    ()
<:ᵛ-shape {[ _ ] _} {_ |×| _} ()
<:ᵛ-shape {[ _ ] _} {Empty}   ()
<:ᵛ-shape {[ _ ] _} {_ ⇒ _}   ()
<:ᵛ-shape {[ _ ] _} {[ _ ] _} _ = Boxˢ

-- Reflexivity

<:ᵛ-refl : (A : VType) → A <:ᵛ A
<:ᶜ-refl : (C : CType) → C <:ᶜ C

<:ᵛ-refl (Base b)  = refl
<:ᵛ-refl Unit      = tt
<:ᵛ-refl Bool      = tt
<:ᵛ-refl (A |×| B) = <:ᵛ-refl A , <:ᵛ-refl B
<:ᵛ-refl Empty     = tt
<:ᵛ-refl (A ⇒ C)   = <:ᵛ-refl A , <:ᶜ-refl C
<:ᵛ-refl ([ ρ ] A) = ≾ᵣ-refl , <:ᵛ-refl A

<:ᶜ-refl (A ‼ ε) = <:ᵛ-refl A , ≾ₑ-refl

-- Transitivity; the contravariant positions compose in the opposite order

<:ᵛ-trans : ∀ {A B C} → A <:ᵛ B → B <:ᵛ C → A <:ᵛ C
<:ᶜ-trans : ∀ {C₁ C₂ C₃} → C₁ <:ᶜ C₂ → C₂ <:ᶜ C₃ → C₁ <:ᶜ C₃

<:ᵛ-transˢ : ∀ {A B C} → A ∼ˢ B → B ∼ˢ C → A <:ᵛ B → B <:ᵛ C → A <:ᵛ C
<:ᵛ-transˢ Baseˢ  Baseˢ  p       q       = trans p q
<:ᵛ-transˢ Unitˢ  Unitˢ  p       q       = tt
<:ᵛ-transˢ Boolˢ  Boolˢ  p       q       = tt
<:ᵛ-transˢ Prodˢ  Prodˢ  (p , r) (q , s) = <:ᵛ-trans p q , <:ᵛ-trans r s
<:ᵛ-transˢ Emptyˢ Emptyˢ p       q       = tt
<:ᵛ-transˢ Arrˢ   Arrˢ   (p , r) (q , s) = <:ᵛ-trans q p , <:ᶜ-trans r s
<:ᵛ-transˢ Boxˢ   Boxˢ   (p , r) (q , s) = ≾ᵣ-trans q p , <:ᵛ-trans r s

<:ᵛ-trans p q = <:ᵛ-transˢ (<:ᵛ-shape p) (<:ᵛ-shape q) p q

<:ᶜ-trans {_ ‼ _} {_ ‼ _} {_ ‼ _} (p , r) (q , s) =
  <:ᵛ-trans p q , ≾ₑ-trans r s

-- Subtyping is a *property* of a pair of types: any two witnesses
-- coincide, by irrelevance of the grade orderings and UIP at `Base`.

<:ᵛ-irrelevant : ∀ {A B} → (p q : A <:ᵛ B) → p ≡ q
<:ᶜ-irrelevant : ∀ {C₁ C₂} → (p q : C₁ <:ᶜ C₂) → p ≡ q

<:ᵛ-irrelevantˢ : ∀ {A B} → A ∼ˢ B → (p q : A <:ᵛ B) → p ≡ q
<:ᵛ-irrelevantˢ Baseˢ  p       q       = uip
<:ᵛ-irrelevantˢ Unitˢ  p       q       = refl
<:ᵛ-irrelevantˢ Boolˢ  p       q       = refl
<:ᵛ-irrelevantˢ Prodˢ  (p , r) (q , s) =
  cong₂ _,_ (<:ᵛ-irrelevant p q) (<:ᵛ-irrelevant r s)
<:ᵛ-irrelevantˢ Emptyˢ p       q       = refl
<:ᵛ-irrelevantˢ Arrˢ   (p , r) (q , s) =
  cong₂ _,_ (<:ᵛ-irrelevant p q) (<:ᶜ-irrelevant r s)
<:ᵛ-irrelevantˢ Boxˢ   (p , r) (q , s) =
  cong₂ _,_ (≾ᵣ-irrelevant p q) (<:ᵛ-irrelevant r s)

<:ᵛ-irrelevant p q = <:ᵛ-irrelevantˢ (<:ᵛ-shape p) p q

<:ᶜ-irrelevant {_ ‼ _} {_ ‼ _} (p , r) (q , s) =
  cong₂ _,_ (<:ᵛ-irrelevant p q) (≾ₑ-irrelevant r s)

-- Eternality lives on the shared skeleton — `Eternal` has no `_⇒_` and
-- no `[_]_` clause, and the only grade it could see is a box's — so it
-- transfers along `_<:ᵛ_` in both directions.

<:ᵛ-eternalˡ : ∀ {A B} → A <:ᵛ B → Eternal B → Eternal A
<:ᵛ-eternalʳ : ∀ {A B} → A <:ᵛ B → Eternal A → Eternal B

<:ᵛ-eternalˡˢ : ∀ {A B} → A ∼ˢ B → A <:ᵛ B → Eternal B → Eternal A
<:ᵛ-eternalˡˢ Baseˢ  refl    et          = et
<:ᵛ-eternalˡˢ Unitˢ  p       et          = et
<:ᵛ-eternalˡˢ Boolˢ  p       et          = et
<:ᵛ-eternalˡˢ Prodˢ  (p , r) (et |×|ₑ e) = <:ᵛ-eternalˡ p et |×|ₑ <:ᵛ-eternalˡ r e
<:ᵛ-eternalˡˢ Emptyˢ p       et          = et
<:ᵛ-eternalˡˢ Arrˢ   p       ()
<:ᵛ-eternalˡˢ Boxˢ   p       ()

<:ᵛ-eternalˡ p et = <:ᵛ-eternalˡˢ (<:ᵛ-shape p) p et

<:ᵛ-eternalʳˢ : ∀ {A B} → A ∼ˢ B → A <:ᵛ B → Eternal A → Eternal B
<:ᵛ-eternalʳˢ Baseˢ  refl    et          = et
<:ᵛ-eternalʳˢ Unitˢ  p       et          = et
<:ᵛ-eternalʳˢ Boolˢ  p       et          = et
<:ᵛ-eternalʳˢ Prodˢ  (p , r) (et |×|ₑ e) = <:ᵛ-eternalʳ p et |×|ₑ <:ᵛ-eternalʳ r e
<:ᵛ-eternalʳˢ Emptyˢ p       et          = et
<:ᵛ-eternalʳˢ Arrˢ   p       ()
<:ᵛ-eternalʳˢ Boxˢ   p       ()

<:ᵛ-eternalʳ p et = <:ᵛ-eternalʳˢ (<:ᵛ-shape p) p et
