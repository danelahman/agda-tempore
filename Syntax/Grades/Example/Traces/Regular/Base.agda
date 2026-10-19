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

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Syntax.Durations.Nat using (ℕᵀ)

module Syntax.Grades.Example.Traces.Regular.Base
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Properties using (suc-injective)
open import Data.List.Base using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ∷-injective)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (refl; sym; trans; cong; cong₂)

open import Syntax.Grades.Regular.Automaton  (suc n) public
open import Syntax.Grades.Regular.Canonical  (suc n) public
open import Syntax.Grades.Regular.Operations (suc n) public
open import Syntax.Grades.Regular.Inclusion  (suc n) public

import Syntax.Grades.Traces.Base ℕᵀ Op as T
open T using (Trace; Trace⁻; ε; operation; delay; ε⁻; operation⁻; prepend; _∙_;
              D⁺; ∣_∣⁺; _+⁺_; ∣∣⁺-nz; ∣∣⁺-inj; delay-of)
open import Syntax.Durations.Monus ℕᵀ using (_<ᴰ_; _<ᴰ?_; ≮0⇒≡0)

------------------------------------------------------------------------
-- Letters

tick : Letter
tick = zero

op : Op → Letter
op o = suc (code o)

------------------------------------------------------------------------
-- The encoding

ticks : D⁺ → Word
ticks d = replicate ∣ d ∣⁺ tick

private
  replicate-+ : ∀ m n → replicate (m + n) tick ≡ replicate m tick ++ replicate n tick
  replicate-+ zero    n = refl
  replicate-+ (suc m) n = cong (tick ∷_) (replicate-+ m n)

ticks-+⁺ : (d e : D⁺) → ticks (d +⁺ e) ≡ ticks d ++ ticks e
ticks-+⁺ d e = replicate-+ ∣ d ∣⁺ ∣ e ∣⁺

mutual
  enc : Trace → Word
  enc ε               = []
  enc (operation o t) = op o ∷ enc t
  enc (delay d t⁻)    = ticks d ++ enc⁻ t⁻

  enc⁻ : Trace⁻ → Word
  enc⁻ ε⁻               = []
  enc⁻ (operation⁻ o t) = op o ∷ enc t

enc-prepend : (d : D⁺) (t : Trace) → enc (prepend d t) ≡ ticks d ++ enc t
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
enc-⟨⟩ m = case (0 <ᴰ? m)
  where
    case : (p : Dec (0 <ᴰ m)) → enc (delay-of m p) ≡ replicate m tick
    case (yes _) = ++-identityʳ (replicate m tick)
    case (no ¬p) = cong (λ k → replicate k tick) (sym (≮0⇒≡0 ¬p))

-- injective: operation letters are not ticks, and a delay-free trace
-- does not begin with a tick

private
  op-injective : ∀ {o o′} → op o ≡ op o′ → o ≡ o′
  op-injective eq = code-injective (suc-injective eq)

  -- a delay encodes to a tick followed by the rest

  ticks-head : ∀ d → Σ Word (λ r → ticks d ≡ tick ∷ r)
  ticks-head d with ∣ d ∣⁺ | ∣∣⁺-nz d
  ... | zero  | nz = ⊥-elim (nz refl)
  ... | suc k | _  = replicate k tick , refl

  -- the encoding of a delay-free trace does not begin with a tick

  NoTick : Word → Set
  NoTick w = ∀ r → w ≡ tick ∷ r → ⊥

  enc⁻-no-tick : ∀ t⁻ → NoTick (enc⁻ t⁻)
  enc⁻-no-tick ε⁻               _ ()
  enc⁻-no-tick (operation⁻ o t) _ ()

  -- blocks of ticks before tick-free words split uniquely

  rep-split : ∀ a b {x y} → NoTick x → NoTick y
            → replicate a tick ++ x ≡ replicate b tick ++ y → a ≡ b × x ≡ y
  rep-split zero    zero    _  _  eq = refl , eq
  rep-split zero    (suc b) nx _  eq = ⊥-elim (nx _ eq)
  rep-split (suc a) zero    _  ny eq = ⊥-elim (ny _ (sym eq))
  rep-split (suc a) (suc b) nx ny eq with rep-split a b nx ny (proj₂ (∷-injective eq))
  ... | refl , eq′ = refl , eq′

  ticks-split : ∀ d e s⁻ t⁻ → ticks d ++ enc⁻ s⁻ ≡ ticks e ++ enc⁻ t⁻
              → d ≡ e × enc⁻ s⁻ ≡ enc⁻ t⁻
  ticks-split d e s⁻ t⁻ eq with rep-split ∣ d ∣⁺ ∣ e ∣⁺ (enc⁻-no-tick s⁻) (enc⁻-no-tick t⁻) eq
  ... | e₁ , e₂ = ∣∣⁺-inj e₁ , e₂

  -- a delay's encoding is neither empty nor headed by an operation

  delay-not-[] : ∀ d t⁻ → [] ≡ ticks d ++ enc⁻ t⁻ → ⊥
  delay-not-[] d t⁻ eq with ticks-head d
  ... | r , h rewrite h with eq
  ... | ()

  delay-not-op : ∀ d t⁻ {o w} → op o ∷ w ≡ ticks d ++ enc⁻ t⁻ → ⊥
  delay-not-op d t⁻ eq with ticks-head d
  ... | r , h rewrite h with eq
  ... | ()

mutual
  enc-injective : ∀ {s t} → enc s ≡ enc t → s ≡ t
  enc-injective {ε}             {ε}             _  = refl
  enc-injective {ε}             {operation _ _} ()
  enc-injective {ε}             {delay d t⁻}    eq = ⊥-elim (delay-not-[] d t⁻ eq)
  enc-injective {operation _ _} {ε}             ()
  enc-injective {operation o s} {operation o′ t} eq
    with ∷-injective eq
  ... | e₁ , e₂ = cong₂ operation (op-injective e₁) (enc-injective e₂)
  enc-injective {operation _ _} {delay d t⁻}    eq = ⊥-elim (delay-not-op d t⁻ eq)
  enc-injective {delay d s⁻}    {ε}             eq = ⊥-elim (delay-not-[] d s⁻ (sym eq))
  enc-injective {delay d s⁻}    {operation _ _} eq = ⊥-elim (delay-not-op d s⁻ (sym eq))
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
