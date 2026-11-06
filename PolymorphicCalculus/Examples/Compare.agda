------------------------------------------------------------------------
-- Inference on comparisons                                           --
--                                                                    --
-- A comparison `cmp ⋈ V W` compares two operands of one eternal      --
-- type: natural numbers, lists, pairs and sums compare, functions    --
-- and boxes do not. An operand of unknown type is asked to be        --
-- eternal outright, without the alternative the variable rule        --
-- allows.                                                            --
--                                                                    --
-- The examples                                                       --
--   lt-nats         two natural numbers                              --
--   eq-lists        two lists of natural numbers                     --
--   ge-pairs        two pairs                                        --
--   ne-sums,        two sums, annotated and unannotated              --
--   ne-sums'                                                         --
--   equal,          a polymorphic comparison, and one operand        --
--   reflexive       compared with itself                             --
--   eq-funs,        functions and boxes, which do not compare        --
--   eq-boxes                                                         --
--   later-lt,       comparisons after a delay                        --
--   later-equal                                                      --
--   max             a comparison inspected by `if`                   --
--                                                                    --
-- How to read them                                                   --
--   Each program is written above its definition in ordinary         --
--   syntax. Where a typing is written out as a derivation, the       --
--   program is checked here to be typed by inference at every        --
--   grade (`lt-nats-typed`). The modules under `Compare/` run        --
--   inference at upper and lower bounds and check                    --
--   the answer with `refl`:                                          --
--     lt-nats-reported : schemeOf (infer [] lt-nats)                 --
--                          ≡ just expected-lt-nats                   --
--   `eq-funs` and `eq-boxes` are refuted there, each with a proof    --
--   that it is untypable; every other example is typed at both.      --
------------------------------------------------------------------------

open import Data.Unit using (tt)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat using (ℕ)

open import Grades.Durations using (Stepped)
open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Examples.Compare (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S)
  (st : Stepped (GradeSystem.Dur (LanguageSpec.Grades S))) where

open LanguageSpec S
open GradeSystemInterface Grades using (𝔻; ιᵣ; ιₑ)

open import PolymorphicCalculus.Syntax.Grades      S
open import PolymorphicCalculus.Syntax.Types       S
open import PolymorphicCalculus.Syntax.Contexts    S hiding (Scheme)
open import PolymorphicCalculus.Syntax.GradeSubstitution S using (idˢ)
open import PolymorphicCalculus.Hypotheses        S
open import PolymorphicCalculus.Hypotheses.Instances   S using (Satisfiable-∅)
open import Language.Comparisons using (Cmp; eq; ne; lt; le; gt; ge)
open import PolymorphicCalculus.Typing    S
open import PolymorphicCalculus.Syntax.Raw             S
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution  S using (_[_]ᴿᶜ)
open import PolymorphicCalculus.Typing.Erasure                  S using (⌊_⌋ᶜ)
open import PolymorphicCalculus.Inference.Principality           S
open import PolymorphicCalculus.Inference.SolverImpl             S hints opEnum
  using (infer-complete; infer-handlerFree)

open import PolymorphicCalculus.Inference.SolverImpl S hints opEnum using (infer) public
open import PolymorphicCalculus.Examples.Scheme S public
open import PolymorphicCalculus.Examples.Variables

------------------------------------------------------------------
-- The duration of `n` ticks, and its grades

⌜_⌝ : ℕ → 𝔻
⌜ n ⌝ = Stepped.fromℕ st n

⌜_⌝ʳ : ∀ {Θ} → ℕ → RExp Θ
⌜ n ⌝ʳ = rconst (ιᵣ ⌜ n ⌝)

⌜_⌝ᵉ : ∀ {Θ} → ℕ → EExp Θ
⌜ n ⌝ᵉ = econst (ιₑ ⌜ n ⌝)

------------------------------------------------------------------
-- Verdicts

-- A closed derivation in the empty context is a typing

closed : {M : RawC ∅ˢ 0} {C : OCType ∅ˢ} → (D : ∅ᴴ ∣ [] ⊢ᶜ⦂ C)
       → ⌊ D ⌋ᶜ ≡ M [ idˢ ]ᴿᶜ → Typable [] M
closed {C = C} D e = typable ∅ˢ idˢ ∅ᴴ C D e Satisfiable-∅

-- Typable and handler-free: `typed`

typed-of : (M : RawC ∅ˢ 0) → Typable [] M → HandlerFreeᶜ M → IsTyped (infer [] M)
typed-of M t h with infer [] M | infer-complete [] M t | infer-handlerFree [] M tt h
... | typed p   | _  | _  = is-typed p
... | untypable | nu | _  = ⊥-elim (nu refl)
... | stuck     | _  | ns = ⊥-elim (ns refl)

------------------------------------------------------------------
-- Side conditions

private

  -- A variable no time has passed over

  ok₀ : ∀ {Θ} {Q : Hyps Θ} {A : OVType Θ} → Q ⊩ A Et∨≾ᵘ 𝟏̂ᵣ
  ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

------------------------------------------------------------------
-- 1. Natural numbers
--
--   lt-nats = 2 < 3
--
-- Typed at every grade.

lt-nats : RawC ∅ˢ 0
lt-nats = return (cmp lt (numeral 2) (numeral 3))

lt-nats-D : ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ bool ! 𝟏̂ₑ
lt-nats-D = return (cmp lt (numeralᵛ 2) (numeralᵛ 3) natₑ)

lt-nats-typed : IsTyped (infer [] lt-nats)
lt-nats-typed = typed-of lt-nats (closed lt-nats-D refl) _

expected-lt-nats : Scheme
expected-lt-nats = ∀[ 0 , 0 , 0 ] ⊤ ⟹ bool ! 𝟏̂ₑ

------------------------------------------------------------------
-- 2. Lists of natural numbers
--
--   eq-lists = [1] = [2]
--
-- A list type is eternal when its element type is.

eq-lists : RawC ∅ˢ 0
eq-lists = return (cmp eq (cons (numeral 1) nil) (cons (numeral 2) nil))

eq-lists-D : ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ bool ! 𝟏̂ₑ
eq-lists-D =
  return (cmp eq (cons (numeralᵛ 1) nil) (cons (numeralᵛ 2) nil) (listₑ natₑ))

eq-lists-typed : IsTyped (infer [] eq-lists)
eq-lists-typed = typed-of eq-lists (closed eq-lists-D refl) _

expected-eq-lists : Scheme
expected-eq-lists = ∀[ 0 , 0 , 0 ] ⊤ ⟹ bool ! 𝟏̂ₑ

------------------------------------------------------------------
-- 3. Pairs and sums of eternal types
--
--   ge-pairs = (0, true) ≥ (1, false)
--   ne-sums  = (inl 0 : Nat + Bool) ≠ (inr true : Nat + Bool)

ge-pairs : RawC ∅ˢ 0
ge-pairs = return (cmp ge ⦉ zero , true ⦊ ⦉ numeral 1 , false ⦊)

expected-ge-pairs : Scheme
expected-ge-pairs = ∀[ 0 , 0 , 0 ] ⊤ ⟹ bool ! 𝟏̂ₑ

ne-sums : RawC ∅ˢ 0
ne-sums = return (cmp ne (inl zero ⦂ᵛ (nat |+| bool)) (inr true ⦂ᵛ (nat |+| bool)))

ne-sums-D : ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ bool ! 𝟏̂ₑ
ne-sums-D =
  return (cmp ne (annᵛ (nat |+| bool) (inl zero)) (annᵛ (nat |+| bool) (inr true))
              (natₑ |+|ₑ boolₑ))

ne-sums-typed : IsTyped (infer [] ne-sums)
ne-sums-typed = typed-of ne-sums (closed ne-sums-D refl) _

expected-ne-sums : Scheme
expected-ne-sums = ∀[ 0 , 0 , 0 ] ⊤ ⟹ bool ! 𝟏̂ₑ

--   ne-sums' = inl 0 ≠ inr true
--
-- Unannotated, the summands meet at `Nat + Bool`.

ne-sums' : RawC ∅ˢ 0
ne-sums' = return (cmp ne (inl zero) (inr true))

expected-ne-sums' : Scheme
expected-ne-sums' = ∀[ 0 , 0 , 0 ] ⊤ ⟹ bool ! 𝟏̂ₑ

------------------------------------------------------------------
-- 4. A polymorphic comparison
--
--   equal x y = x = y
--
-- The operands get a common eternal supertype.

equal : RawC ∅ˢ 0
equal = return (fun (return (fun (return (cmp eq v₁ v₀)))))

expected-equal : Scheme
expected-equal =
  ∀[ 3 , 0 , 0 ] eternal α₀ ∧ α₂ <: α₀ ∧ α₁ <: α₀ ⟹
    (α₂ ⇒ (α₁ ⇒ bool ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ

-- An instance at `nat`, as a derivation

equal-D : ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ (nat ⇒ (nat ⇒ bool ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ
equal-D = return (fun (return (fun (return (cmp eq (var (Tl-∷ Hd) ok₀) (var Hd ok₀) natₑ)))))

equal-typed : IsTyped (infer [] equal)
equal-typed = typed-of equal (closed equal-D refl) _

-- One operand compared with itself
--
--   reflexive x = x = x

reflexive : RawC ∅ˢ 0
reflexive = return (fun (return (cmp eq v₀ v₀)))

expected-reflexive : Scheme
expected-reflexive = ∀[ 1 , 0 , 0 ] eternal α₀ ⟹ (α₀ ⇒ bool ! 𝟏̂ₑ) ! 𝟏̂ₑ

------------------------------------------------------------------
-- 5. Functions and boxes do not compare
--
--   eq-funs  = (λ _. ()) = (λ _. ())
--   eq-boxes = box[0] () as x in box[0] () as y in x = y

eq-funs : RawC ∅ˢ 0
eq-funs = return (cmp eq (fun (return ⋆)) (fun (return ⋆)))

eq-boxes : RawC ∅ˢ 0
eq-boxes = box 𝟏̂ᵣ ⋆ (box 𝟏̂ᵣ ⋆ (return (cmp eq v₁ v₀)))

------------------------------------------------------------------
-- 6. Comparisons under a modality
--
--   later-lt = let n = 2 in delay 1; n < 3
--
-- `nat` survives the modality; typed at every grade.

later-lt : RawC ∅ˢ 0
later-lt = return (numeral 2) ⨟ delay ⌜ 1 ⌝ (return (cmp lt v₀ (numeral 3)))

later-lt-D : ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ bool ! (𝟏̂ₑ ·̂ₑ (⌜ 1 ⌝ᵉ ·̂ₑ 𝟏̂ₑ))
later-lt-D =
  return (numeralᵛ 2)
  ⨟ delay ⌜ 1 ⌝ (return (cmp lt (var (Tl-⟨⟩ Hd) (et-ok natₑ)) (numeralᵛ 3) natₑ))

later-lt-typed : IsTyped (infer [] later-lt)
later-lt-typed = typed-of later-lt (closed later-lt-D refl) _

expected-later-lt : Scheme
expected-later-lt = ∀[ 0 , 0 , 0 ] ⊤ ⟹ bool ! ⌜ 1 ⌝ᵉ

--   later-equal x y = delay 1; x = y
--
-- The eternality the comparison asks for meets the variable rule.

later-equal : RawC ∅ˢ 0
later-equal = return (fun (return (fun (delay ⌜ 1 ⌝ (return (cmp eq v₁ v₀))))))

expected-later-equal : Scheme
expected-later-equal =
  ∀[ 3 , 0 , 0 ] eternal α₀ ∧ α₂ <: α₀ ∧ α₁ <: α₀ ⟹
    (α₂ ⇒ (α₁ ⇒ bool ! ⌜ 1 ⌝ᵉ) ! 𝟏̂ₑ) ! 𝟏̂ₑ

------------------------------------------------------------------
-- 7. A comparison inspected by `if`
--
--   max x y = if x < y then y else x
--
-- The result is a common supertype of `x` and `y`.

max : RawC ∅ˢ 0
max = return (fun (return (fun (if cmp lt v₁ v₀ `then return v₀ `else return v₁))))

max-D : ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ (nat ⇒ (nat ⇒ nat ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ
max-D =
  return (fun (return (fun
    (if cmp lt (var (Tl-∷ Hd) ok₀) (var Hd ok₀) natₑ
     `then return (var Hd ok₀) `else return (var (Tl-∷ Hd) ok₀)))))

max-typed : IsTyped (infer [] max)
max-typed = typed-of max (closed max-D refl) _

expected-max : Scheme
expected-max =
  ∀[ 4 , 0 , 0 ] eternal α₀ ∧ α₃ <: α₀ ∧ α₁ <: α₀ ∧ α₁ <: α₂ ∧ α₃ <: α₂ ⟹
    (α₃ ⇒ (α₁ ⇒ α₂ ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ
