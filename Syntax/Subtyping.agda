-------------------------------------------------------------------
-- Shape-preserving subtyping of value and computation types      --
--                                                                --
-- `_<:_` is a recursive predicate on the skeleton the two types  --
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

infix 4 _<:_ _<:ᶜ_ _∼ˢ_

-- The relation

_<:_ : VType → VType → Set
_<:ᶜ_ : CType → CType → Set

Base b    <: Base b'     = b ≡ b'
Unit      <: Unit        = ⊤
Bool      <: Bool        = ⊤
(A |×| B) <: (A' |×| B') = A <: A' × B <: B'
Empty     <: Empty       = ⊤
(A ⇒ C)   <: (A' ⇒ C')   = A' <: A × C <:ᶜ C'
([ ρ ] A) <: ([ ρ' ] A') = ρ' ≾ᵣ ρ × A <: A'
_         <: _           = ⊥

(A ‼ ε) <:ᶜ (A' ‼ ε') = A <: A' × ε ≾ₑ ε'

-- Relatedness of two types under `_<:_` fixes their common skeleton.
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

<:-shape : ∀ {A B} → A <: B → A ∼ˢ B
<:-shape {Base _}  {Base _}  _ = Baseˢ
<:-shape {Base _}  {Unit}    ()
<:-shape {Base _}  {Bool}    ()
<:-shape {Base _}  {_ |×| _} ()
<:-shape {Base _}  {Empty}   ()
<:-shape {Base _}  {_ ⇒ _}   ()
<:-shape {Base _}  {[ _ ] _} ()
<:-shape {Unit}    {Base _}  ()
<:-shape {Unit}    {Unit}    _ = Unitˢ
<:-shape {Unit}    {Bool}    ()
<:-shape {Unit}    {_ |×| _} ()
<:-shape {Unit}    {Empty}   ()
<:-shape {Unit}    {_ ⇒ _}   ()
<:-shape {Unit}    {[ _ ] _} ()
<:-shape {Bool}    {Base _}  ()
<:-shape {Bool}    {Unit}    ()
<:-shape {Bool}    {Bool}    _ = Boolˢ
<:-shape {Bool}    {_ |×| _} ()
<:-shape {Bool}    {Empty}   ()
<:-shape {Bool}    {_ ⇒ _}   ()
<:-shape {Bool}    {[ _ ] _} ()
<:-shape {_ |×| _} {Base _}  ()
<:-shape {_ |×| _} {Unit}    ()
<:-shape {_ |×| _} {Bool}    ()
<:-shape {_ |×| _} {_ |×| _} _ = Prodˢ
<:-shape {_ |×| _} {Empty}   ()
<:-shape {_ |×| _} {_ ⇒ _}   ()
<:-shape {_ |×| _} {[ _ ] _} ()
<:-shape {Empty}   {Base _}  ()
<:-shape {Empty}   {Unit}    ()
<:-shape {Empty}   {Bool}    ()
<:-shape {Empty}   {_ |×| _} ()
<:-shape {Empty}   {Empty}   _ = Emptyˢ
<:-shape {Empty}   {_ ⇒ _}   ()
<:-shape {Empty}   {[ _ ] _} ()
<:-shape {_ ⇒ _}   {Base _}  ()
<:-shape {_ ⇒ _}   {Unit}    ()
<:-shape {_ ⇒ _}   {Bool}    ()
<:-shape {_ ⇒ _}   {_ |×| _} ()
<:-shape {_ ⇒ _}   {Empty}   ()
<:-shape {_ ⇒ _}   {_ ⇒ _}   _ = Arrˢ
<:-shape {_ ⇒ _}   {[ _ ] _} ()
<:-shape {[ _ ] _} {Base _}  ()
<:-shape {[ _ ] _} {Unit}    ()
<:-shape {[ _ ] _} {Bool}    ()
<:-shape {[ _ ] _} {_ |×| _} ()
<:-shape {[ _ ] _} {Empty}   ()
<:-shape {[ _ ] _} {_ ⇒ _}   ()
<:-shape {[ _ ] _} {[ _ ] _} _ = Boxˢ

-- Reflexivity

<:-refl  : (A : VType) → A <: A
<:ᶜ-refl : (C : CType) → C <:ᶜ C

<:-refl (Base b)  = refl
<:-refl Unit      = tt
<:-refl Bool      = tt
<:-refl (A |×| B) = <:-refl A , <:-refl B
<:-refl Empty     = tt
<:-refl (A ⇒ C)   = <:-refl A , <:ᶜ-refl C
<:-refl ([ ρ ] A) = ≾ᵣ-refl , <:-refl A

<:ᶜ-refl (A ‼ ε) = <:-refl A , ≾ₑ-refl

-- Transitivity; the contravariant positions compose in the opposite order

<:-trans  : ∀ {A B C} → A <: B → B <: C → A <: C
<:ᶜ-trans : ∀ {C₁ C₂ C₃} → C₁ <:ᶜ C₂ → C₂ <:ᶜ C₃ → C₁ <:ᶜ C₃

<:-transˢ : ∀ {A B C} → A ∼ˢ B → B ∼ˢ C → A <: B → B <: C → A <: C
<:-transˢ Baseˢ  Baseˢ  p       q       = trans p q
<:-transˢ Unitˢ  Unitˢ  p       q       = tt
<:-transˢ Boolˢ  Boolˢ  p       q       = tt
<:-transˢ Prodˢ  Prodˢ  (p , r) (q , s) = <:-trans p q , <:-trans r s
<:-transˢ Emptyˢ Emptyˢ p       q       = tt
<:-transˢ Arrˢ   Arrˢ   (p , r) (q , s) = <:-trans q p , <:ᶜ-trans r s
<:-transˢ Boxˢ   Boxˢ   (p , r) (q , s) = ≾ᵣ-trans q p , <:-trans r s

<:-trans p q = <:-transˢ (<:-shape p) (<:-shape q) p q

<:ᶜ-trans {_ ‼ _} {_ ‼ _} {_ ‼ _} (p , r) (q , s) =
  <:-trans p q , ≾ₑ-trans r s

-- Subtyping is a *property* of a pair of types: any two witnesses
-- coincide, by irrelevance of the grade orderings and UIP at `Base`.

<:-irrelevant  : ∀ {A B} → (p q : A <: B) → p ≡ q
<:ᶜ-irrelevant : ∀ {C₁ C₂} → (p q : C₁ <:ᶜ C₂) → p ≡ q

<:-irrelevantˢ : ∀ {A B} → A ∼ˢ B → (p q : A <: B) → p ≡ q
<:-irrelevantˢ Baseˢ  p       q       = uip
<:-irrelevantˢ Unitˢ  p       q       = refl
<:-irrelevantˢ Boolˢ  p       q       = refl
<:-irrelevantˢ Prodˢ  (p , r) (q , s) =
  cong₂ _,_ (<:-irrelevant p q) (<:-irrelevant r s)
<:-irrelevantˢ Emptyˢ p       q       = refl
<:-irrelevantˢ Arrˢ   (p , r) (q , s) =
  cong₂ _,_ (<:-irrelevant p q) (<:ᶜ-irrelevant r s)
<:-irrelevantˢ Boxˢ   (p , r) (q , s) =
  cong₂ _,_ (≾ᵣ-irrelevant p q) (<:-irrelevant r s)

<:-irrelevant p q = <:-irrelevantˢ (<:-shape p) p q

<:ᶜ-irrelevant {_ ‼ _} {_ ‼ _} (p , r) (q , s) =
  cong₂ _,_ (<:-irrelevant p q) (≾ₑ-irrelevant r s)

-- Eternality lives on the shared skeleton — `Eternal` has no `_⇒_` and
-- no `[_]_` clause, and the only grade it could see is a box's — so it
-- transfers along `_<:_` in both directions.

<:-eternalˡ : ∀ {A B} → A <: B → Eternal B → Eternal A
<:-eternalʳ : ∀ {A B} → A <: B → Eternal A → Eternal B

<:-eternalˡˢ : ∀ {A B} → A ∼ˢ B → A <: B → Eternal B → Eternal A
<:-eternalˡˢ Baseˢ  refl    et          = et
<:-eternalˡˢ Unitˢ  p       et          = et
<:-eternalˡˢ Boolˢ  p       et          = et
<:-eternalˡˢ Prodˢ  (p , r) (et |×|ₑ e) = <:-eternalˡ p et |×|ₑ <:-eternalˡ r e
<:-eternalˡˢ Emptyˢ p       et          = et
<:-eternalˡˢ Arrˢ   p       ()
<:-eternalˡˢ Boxˢ   p       ()

<:-eternalˡ p et = <:-eternalˡˢ (<:-shape p) p et

<:-eternalʳˢ : ∀ {A B} → A ∼ˢ B → A <: B → Eternal A → Eternal B
<:-eternalʳˢ Baseˢ  refl    et          = et
<:-eternalʳˢ Unitˢ  p       et          = et
<:-eternalʳˢ Boolˢ  p       et          = et
<:-eternalʳˢ Prodˢ  (p , r) (et |×|ₑ e) = <:-eternalʳ p et |×|ₑ <:-eternalʳ r e
<:-eternalʳˢ Emptyˢ p       et          = et
<:-eternalʳˢ Arrˢ   p       ()
<:-eternalʳˢ Boxˢ   p       ()

<:-eternalʳ p et = <:-eternalʳˢ (<:-shape p) p et
