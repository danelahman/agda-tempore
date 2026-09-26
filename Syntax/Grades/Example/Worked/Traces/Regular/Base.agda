------------------------------------------------------------------------
-- Worked instances of the regular trace sets, as tables.             --
--                                                                    --
-- Languages over `read`, `send` and `tick`, built by the operations  --
-- on canonical tables: inclusions with their shortest                --
-- counterexamples, and equalities of tables, from single letters to  --
-- an eight-state language and delays of twenty ticks.                --
--                                                                    --
-- Every claim is established by running the procedures.              --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Regular.Base where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; replicate)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Op : Set where
  read send : Op

code : Op → Fin 2
code read = zero
code send = suc zero

code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
code-injective {read} {read} _ = refl
code-injective {send} {send} _ = refl

open import Syntax.Grades.Example.Traces.Regular.Base Op 2 code code-injective

⊤ : DFA
⊤ = Σ*

of-nat : ℕ → DFA
of-nat = ⟨_⟩

R S : DFA
R = ⌈ read ⌉
S = ⌈ send ⌉

-- any single letter
Σ₁ : DFA
Σ₁ = ⟨ 1 ⟩ ∪ R ∪ S

------------------------------------------------------------------------
-- Inclusions

read-tick²⊆⊤ : (R · ⟨ 2 ⟩ ⊆ᵇ ⊤) ≡ true
read-tick²⊆⊤ = refl

read*⊆[read|send]* : (R * ⊆ᵇ (R ∪ S) *) ≡ true
read*⊆[read|send]* = refl

send⊈read* : counterexample S (R *) ≡ just (op send ∷ [])
send⊈read* = refl

[read|send]*⊈read* : counterexample ((R ∪ S) *) (R *) ≡ just (op send ∷ [])
[read|send]*⊈read* = refl

------------------------------------------------------------------------
-- Equalities of canonical tables

distrib-== : ((R ∪ S) · ⟨ 1 ⟩ ==ᴰ R · ⟨ 1 ⟩ ∪ S · ⟨ 1 ⟩) ≡ true
distrib-== = refl

distrib-≡ : (R ∪ S) · ⟨ 1 ⟩ ≡ R · ⟨ 1 ⟩ ∪ S · ⟨ 1 ⟩
distrib-≡ = refl

of-nat-+-== : (of-nat 2 · of-nat 3 ==ᴰ of-nat 5) ≡ true
of-nat-+-== = refl

of-nat-+-≡ : of-nat 2 · of-nat 3 ≡ of-nat 5
of-nat-+-≡ = refl

------------------------------------------------------------------------
-- A moderately larger language: runs of `read`/`send`, each followed
-- by one or two ticks, ending in `read`

M : DFA
M = ((R ∪ S) · (⟨ 1 ⟩ ∪ ⟨ 2 ⟩)) * · R

M-size : size M ≡ 5
M-size = refl

M⊆⊤ : (M ⊆ᵇ ⊤) ≡ true
M⊆⊤ = refl

M⊆Σ*read : (M ⊆ᵇ ⊤ · R) ≡ true
M⊆Σ*read = refl

M⊈Σ*send : counterexample M (⊤ · S) ≡ just (op read ∷ [])
M⊈Σ*send = refl

------------------------------------------------------------------------
-- Eight states: the letter two before the end is `read`

pow : ℕ → DFA → DFA
pow zero    L = ε
pow (suc j) L = L · pow j L

K₂ : DFA
K₂ = Σ₁ * · R · pow 2 Σ₁

K₂-size : size K₂ ≡ 8
K₂-size = refl

K₂⊆Σ*readΣ* : (K₂ ⊆ᵇ ⊤ · R · ⊤) ≡ true
K₂⊆Σ*readΣ* = refl

K₂⊈Σ*read : counterexample K₂ (⊤ · R) ≡ just (op read ∷ tick ∷ tick ∷ [])
K₂⊈Σ*read = refl

------------------------------------------------------------------------
-- Delays: `⟨ d ⟩` has `d + 2` states

⟨5⟩-size : size ⟨ 5 ⟩ ≡ 7
⟨5⟩-size = refl

⟨5⟩·⟨5⟩ : (⟨ 5 ⟩ · ⟨ 5 ⟩ ==ᴰ ⟨ 10 ⟩) ≡ true
⟨5⟩·⟨5⟩ = refl

⟨5⟩⊆⊤·⟨5⟩ : (⟨ 5 ⟩ ⊆ᵇ ⊤ · ⟨ 5 ⟩) ≡ true
⟨5⟩⊆⊤·⟨5⟩ = refl

⟨10⟩·⟨10⟩ : (⟨ 10 ⟩ · ⟨ 10 ⟩ ==ᴰ ⟨ 20 ⟩) ≡ true
⟨10⟩·⟨10⟩ = refl

⟨10⟩⊆⊤·⟨10⟩ : (⟨ 10 ⟩ ⊆ᵇ ⊤ · ⟨ 10 ⟩) ≡ true
⟨10⟩⊆⊤·⟨10⟩ = refl

⟨20⟩·⟨20⟩ : (⟨ 20 ⟩ · ⟨ 20 ⟩ ==ᴰ ⟨ 40 ⟩) ≡ true
⟨20⟩·⟨20⟩ = refl

⟨20⟩⊆⊤·⟨20⟩ : (⟨ 20 ⟩ ⊆ᵇ ⊤ · ⟨ 20 ⟩) ≡ true
⟨20⟩⊆⊤·⟨20⟩ = refl

⟨20⟩⊈⟨21⟩ : counterexample ⟨ 20 ⟩ ⟨ 21 ⟩ ≡ just (replicate 20 tick)
⟨20⟩⊈⟨21⟩ = refl
