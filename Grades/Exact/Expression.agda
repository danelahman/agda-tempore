------------------------------------------------------------------------
-- One-sided expressions over interval letters, and the sets of exact --
-- words they denote.                                                 --
--                                                                    --
-- An expression of an instance has letters                           --
--                                                                    --
--   ops A      exactly one operation of the set `A`, running for a   --
--              time its running-time interval admits                 --
--   str S e    a stretch admitting the operations of `S`, of a       --
--              length within the one-sided interval with end `e`     --
--                                                                    --
-- and is built with the empty word, union, concatenation and         --
-- iteration. In the upper instance a stretch's interval reaches down --
-- to zero and its end is an upper end, a cut or `∞`; in the lower    --
-- instance it reaches up to `∞` and its end is a lower end, a cut.   --
-- A strict wait is a stretch with the empty set. A stretch of length --
-- zero is the empty word.                                            --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Expression
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Fin.Subset using (_∈_; ⁅_⁆)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Grades.Durations.Monus T using (Carrier)
open import Grades.Durations.Intervals T using (Cut; Hi; fin; ∞; _⊑_; _⊑ʰ_; ⁻; ⁺)
  renaming (_∣_ to _∣ᶜ_)
open import Grades.Durations.Intervals.Dense T using (_∈ⁱ_)

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Lift T Op n code code-injective

open RunningTimes.RunningTimes running using (rt)

------------------------------------------------------------------------
-- Instances and their ends

data Instance : Set where
  upper lower : Instance

End : Instance → Set
End upper = Hi
End lower = Cut

-- the lengths an end admits

admits : (s : Instance) → End s → Carrier → Set
admits upper h τ = fin (τ ∣ᶜ ⁺) ⊑ʰ h
admits lower c τ = c ⊑ (τ ∣ᶜ ⁻)

infix 4 _∈ᵉ_

_∈ᵉ_ : Carrier → {s : Instance} → End s → Set
_∈ᵉ_ τ {s} e = admits s e τ

------------------------------------------------------------------------
-- Expressions

infixl 6 _∣_
infixl 7 _·_
infix  8 _*

data Expr (s : Instance) : Set where
  ε   : Expr s
  ops : OpSet → Expr s
  str : OpSet → End s → Expr s
  _∣_ : Expr s → Expr s → Expr s
  _·_ : Expr s → Expr s → Expr s
  _*  : Expr s → Expr s

-- one operation, and an operation that may be left out

‵_ : ∀ {s} → Op → Expr s
‵ o = ops ⁅ code o ⁆

infix 9 ‵_ _？

_？ : ∀ {s} → Op → Expr s
o ？ = ‵ o ∣ ε

------------------------------------------------------------------------
-- Meaning

-- one operation of a set, with a running time its interval admits

opsᴸ : OpSet → Lang
opsᴸ A w = Σ[ o ∈ Op ] Σ[ d ∈ D⁺ ] code o ∈ A × ∣ d ∣⁺ ∈ⁱ rt o × w ≡ op o d ∷ []

-- a stretch of a length the end admits

strᴸ : ∀ {s} → OpSet → End s → Lang
strᴸ S e w = Σ[ τ ∈ Carrier ] τ ∈ᵉ e × w ≡ stretch S τ

-- iteration

data Star (X : Lang) : Lang where
  stop : Star X []
  more : ∀ {x y} → X x → Star X y → Star X (x ++ y)

⟦_⟧ : ∀ {s} → Expr s → Lang
⟦ ε       ⟧ = 𝟏ᴸ
⟦ ops A   ⟧ = opsᴸ A
⟦ str S e ⟧ = strᴸ S e
⟦ e ∣ f   ⟧ = ⟦ e ⟧ ∪ᴸ ⟦ f ⟧
⟦ e · f   ⟧ = ⟦ e ⟧ ·ᴸ ⟦ f ⟧
⟦ e *     ⟧ = Star ⟦ e ⟧

------------------------------------------------------------------------
-- Bounded repetition, unrolled

open import Data.Nat.Base using (ℕ; zero; suc; _∸_)

infix 8 _^_ _^[_,_] _^≥_

_^_ : ∀ {s} → Expr s → ℕ → Expr s
e ^ zero  = ε
e ^ suc m = e · e ^ m

-- between `m` and `n` repetitions

_^[_,_] : ∀ {s} → Expr s → ℕ → ℕ → Expr s
e ^[ m , n ] = e ^ m · (e ∣ ε) ^ (n ∸ m)

-- at least `m` repetitions

_^≥_ : ∀ {s} → Expr s → ℕ → Expr s
e ^≥ m = e ^ m · e *
