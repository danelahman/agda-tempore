------------------------------------------------------------------------
-- Timed traces as words, over a finite set of operations.            --
--                                                                    --
-- The operations are coded injectively into `Fin n`, and the letters --
-- are `Fin (suc n)`, with `tick` first. A timed trace is encoded as  --
-- a word, a delay `d` becoming the block `tickᵈ`. The encoding is an --
-- injective monoid morphism: merging of delays is concatenation of   --
-- lists, and a regular language over the letters is a regular set of --
-- timed traces.                                                      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Syntax.Grades.Example.Traces.Regular.Base
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Properties using (suc-injective)
open import Data.List.Base using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ∷-injective)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (refl; sym; trans; cong; cong₂)

open import Syntax.Grades.Regular.Automaton  (suc n) public
open import Syntax.Grades.Regular.Canonical  (suc n) public
open import Syntax.Grades.Regular.Operations (suc n) public
open import Syntax.Grades.Regular.Inclusion  (suc n) public

import Syntax.Grades.Traces.Base Op as T
open T using (Trace; Trace⁻; ε; operation; delay; ε⁻; operation⁻; prepend; _∙_; ℕ⁺; 𝟏; suc⁺; _+⁺_; 1+_)

------------------------------------------------------------------------
-- Letters

tick : Letter
tick = zero

op : Op → Letter
op o = suc (code o)

------------------------------------------------------------------------
-- The encoding

ticks : ℕ⁺ → Word
ticks 𝟏        = tick ∷ []
ticks (suc⁺ d) = tick ∷ ticks d

ticks-+⁺ : (d e : ℕ⁺) → ticks (d +⁺ e) ≡ ticks d ++ ticks e
ticks-+⁺ 𝟏        e = refl
ticks-+⁺ (suc⁺ d) e = cong (tick ∷_) (ticks-+⁺ d e)

mutual
  enc : Trace → Word
  enc ε               = []
  enc (operation o t) = op o ∷ enc t
  enc (delay d t⁻)    = ticks d ++ enc⁻ t⁻

  enc⁻ : Trace⁻ → Word
  enc⁻ ε⁻               = []
  enc⁻ (operation⁻ o t) = op o ∷ enc t

enc-prepend : (d : ℕ⁺) (t : Trace) → enc (prepend d t) ≡ ticks d ++ enc t
enc-prepend d ε               = refl
enc-prepend d (operation o t) = refl
enc-prepend d (delay e t⁻)    =
  trans (cong (_++ enc⁻ t⁻) (ticks-+⁺ d e)) (++-assoc (ticks d) (ticks e) (enc⁻ t⁻))

-- a monoid morphism

enc-∙ : (s t : Trace) → enc (s ∙ t) ≡ enc s ++ enc t
enc-∙ ε                          t = refl
enc-∙ (operation o s)            t = cong (op o ∷_) (enc-∙ s t)
enc-∙ (delay d ε⁻)               t =
  trans (enc-prepend d t) (cong (_++ enc t) (sym (++-identityʳ (ticks d))))
enc-∙ (delay d (operation⁻ o s)) t =
  trans (cong (λ z → ticks d ++ (op o ∷ z)) (enc-∙ s t))
        (sym (++-assoc (ticks d) (op o ∷ enc s) (enc t)))

-- a pure delay is a block of ticks

enc-⟨⟩ : (m : ℕ) → enc T.⟨ m ⟩ ≡ replicate m tick
enc-⟨⟩ zero    = refl
enc-⟨⟩ (suc m) = trans (++-identityʳ (ticks (1+ m))) (ticks-1+ m)
  where
  ticks-1+ : (m : ℕ) → ticks (1+ m) ≡ replicate (suc m) tick
  ticks-1+ zero    = refl
  ticks-1+ (suc m) = cong (tick ∷_) (ticks-1+ m)

-- injective: operation letters are not ticks, and a delay-free trace
-- does not begin with a tick

private
  op-injective : ∀ {o o′} → op o ≡ op o′ → o ≡ o′
  op-injective eq = code-injective (suc-injective eq)

  enc⁻-no-tick : ∀ t⁻ e {w} → enc⁻ t⁻ ≡ ticks e ++ w → ⊥
  enc⁻-no-tick ε⁻               𝟏        ()
  enc⁻-no-tick ε⁻               (suc⁺ e) ()
  enc⁻-no-tick (operation⁻ o t) 𝟏        ()
  enc⁻-no-tick (operation⁻ o t) (suc⁺ e) ()

  ticks-split : ∀ d e s⁻ t⁻ → ticks d ++ enc⁻ s⁻ ≡ ticks e ++ enc⁻ t⁻
              → d ≡ e × enc⁻ s⁻ ≡ enc⁻ t⁻
  ticks-split 𝟏        𝟏        s⁻ t⁻ eq = refl , proj₂ (∷-injective eq)
  ticks-split 𝟏        (suc⁺ e) s⁻ t⁻ eq = ⊥-elim (enc⁻-no-tick s⁻ e (proj₂ (∷-injective eq)))
  ticks-split (suc⁺ d) 𝟏        s⁻ t⁻ eq = ⊥-elim (enc⁻-no-tick t⁻ d (sym (proj₂ (∷-injective eq))))
  ticks-split (suc⁺ d) (suc⁺ e) s⁻ t⁻ eq with ticks-split d e s⁻ t⁻ (proj₂ (∷-injective eq))
  ... | refl , eq′ = refl , eq′

mutual
  enc-injective : ∀ {s t} → enc s ≡ enc t → s ≡ t
  enc-injective {ε}             {ε}             _  = refl
  enc-injective {ε}             {operation _ _} ()
  enc-injective {ε}             {delay 𝟏 _}     ()
  enc-injective {ε}             {delay (suc⁺ _) _} ()
  enc-injective {operation _ _} {ε}             ()
  enc-injective {operation o s} {operation o′ t} eq
    with ∷-injective eq
  ... | e₁ , e₂ = cong₂ operation (op-injective e₁) (enc-injective e₂)
  enc-injective {operation _ _} {delay 𝟏 _}     ()
  enc-injective {operation _ _} {delay (suc⁺ _) _} ()
  enc-injective {delay 𝟏 _}     {ε}             ()
  enc-injective {delay (suc⁺ _) _} {ε}          ()
  enc-injective {delay 𝟏 _}     {operation _ _} ()
  enc-injective {delay (suc⁺ _) _} {operation _ _} ()
  enc-injective {delay d s⁻}    {delay e t⁻}    eq with ticks-split d e s⁻ t⁻ eq
  ... | refl , eq′ = cong (delay d) (enc⁻-injective eq′)

  enc⁻-injective : ∀ {s⁻ t⁻} → enc⁻ s⁻ ≡ enc⁻ t⁻ → s⁻ ≡ t⁻
  enc⁻-injective {ε⁻}             {ε⁻}             _  = refl
  enc⁻-injective {ε⁻}             {operation⁻ _ _} ()
  enc⁻-injective {operation⁻ _ _} {ε⁻}             ()
  enc⁻-injective {operation⁻ o s} {operation⁻ o′ t} eq with ∷-injective eq
  ... | e₁ , e₂ = cong₂ operation⁻ (op-injective e₁) (enc-injective e₂)

------------------------------------------------------------------------
-- Tables for single operations and delays

⌈_⌉ : Op → DFA
⌈ o ⌉ = ⟦ op o ∷ [] ⟧

⟨_⟩ : ℕ → DFA
⟨ d ⟩ = tick ^ d
