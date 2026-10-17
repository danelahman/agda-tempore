--------------------------------------------------------------------
-- Inference on comparisons                                       --
--                                                                --
-- Programs exercising `cmp ⋈ V W`, one rule for the six          --
-- relations of `Cmp`. Both operands are typed at one type,       --
-- which has to be eternal, and the comparison is a pure `Bool`.  --
-- Natural numbers, lists of them, pairs and sums of eternal      --
-- types compare; functions and boxes are never eternal and do    --
-- not. An unknown operand type is asked to be eternal at every   --
-- grade: unlike the variable rule's, the condition is not a      --
-- disjunction with a grade bound.                                --
--                                                                --
-- The instances under `Compare/` check the verdicts and schemes  --
-- by `refl` at right- and left-sided time.                       --
--------------------------------------------------------------------

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat using (ℕ)

open import Syntax.Durations using (Stepped)
open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.Examples.Compare (S : LanguageSpec) (opEnum : OpEnum S)
  (st : Stepped (GradeSystem.Dur (LanguageSpec.Grades S))) where

open LanguageSpec S
open GradeSystemInterface Grades using (𝔻; of-durʳ; of-durᵉ)

open import TypeInference.OpenSyntax.Grades      S
open import TypeInference.OpenSyntax.Types       S
open import TypeInference.OpenSyntax.Contexts    S
open import TypeInference.OpenSyntax.Subst       S using (idˢ)
open import TypeInference.OpenSyntax.Hyps        S
open import TypeInference.OpenSyntax.Instances   S using (Satisfiable-∅)
open import TypeInference.OpenSyntax.Comparisons
open import TypeInference.OpenSyntax.Language    S
open import TypeInference.Raw.Syntax             S
open import TypeInference.Raw.Subst              S using (_[_]ᴿᶜ)
open import TypeInference.Erase                  S using (⌊_⌋ᶜ)
open import TypeInference.Principality           S
open import TypeInference.SolverImpl             S opEnum
  using (infer-complete; infer-handlerFree)

open import TypeInference.SolverImpl S opEnum using (infer) public
open import TypeInference.Examples.Scheme S public
open import TypeInference.Examples.Variables

------------------------------------------------------------------
-- The duration of `n` ticks, and its grades

⌜_⌝ : ℕ → 𝔻
⌜ n ⌝ = Stepped.fromℕ st n

⌜_⌝ʳ : ∀ {Θ} → ℕ → RExp Θ
⌜ n ⌝ʳ = rconst (of-durʳ ⌜ n ⌝)

⌜_⌝ᵉ : ∀ {Θ} → ℕ → EExp Θ
⌜ n ⌝ᵉ = econst (of-durᵉ ⌜ n ⌝)

------------------------------------------------------------------
-- Verdicts

-- A closed derivation in the empty context is a typing

closed : {M : RawC ∅ˢ 0} {C : OCType ∅ˢ} → (D : ∅ᴴ ∣ [] ⊢C⦂ C)
       → ⌊ D ⌋ᶜ ≡ M [ idˢ ]ᴿᶜ → Typable [] M
closed {C = C} D e = typable ∅ˢ idˢ ∅ᴴ C D e Satisfiable-∅

-- Typable and handler-free: inference answers `typed`

typed-of : (M : RawC ∅ˢ 0) → Typable [] M → HandlerFreeᶜ M → IsTyped (infer [] M)
typed-of M t h with infer [] M | infer-complete [] M t | infer-handlerFree [] M h
... | typed p   | _  | _  = is-typed p
... | untypable | nu | _  = ⊥-elim (nu refl)
... | stuck     | _  | ns = ⊥-elim (ns refl)

------------------------------------------------------------------
-- Side conditions

private

  -- A variable no time has passed over

  ok₀ : ∀ {Θ} {Q : Hyps Θ} {A : OVType Θ} → VarOK Q A ûᵣ
  ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

------------------------------------------------------------------
-- 1. Natural numbers
--
--   lt-nats = 2 < 3
--
-- `Nat` is eternal; typed at every grade, with no type variable.

lt-nats : RawC ∅ˢ 0
lt-nats = cmp lt (numeral 2) (numeral 3)

lt-nats-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Bool ‼ ûₑ
lt-nats-D = cmp lt (numeralᵛ 2) (numeralᵛ 3) Natₑ

lt-nats-typed : IsTyped (infer [] lt-nats)
lt-nats-typed = typed-of lt-nats (closed lt-nats-D refl) _

expected-lt-nats : Scheme
expected-lt-nats = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Bool ‼ ûₑ

------------------------------------------------------------------
-- 2. Lists of natural numbers
--
--   eq-lists = [1] = [2]
--
-- A list type is eternal when its element type is.

eq-lists : RawC ∅ˢ 0
eq-lists = cmp eq (cons (numeral 1) nil) (cons (numeral 2) nil)

eq-lists-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Bool ‼ ûₑ
eq-lists-D =
  cmp eq (cons (numeralᵛ 1) nil) (cons (numeralᵛ 2) nil) (|List|ₑ Natₑ)

eq-lists-typed : IsTyped (infer [] eq-lists)
eq-lists-typed = typed-of eq-lists (closed eq-lists-D refl) _

expected-eq-lists : Scheme
expected-eq-lists = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Bool ‼ ûₑ

------------------------------------------------------------------
-- 3. Pairs and sums of eternal types
--
--   ge-pairs = (0, true) ≥ (1, false)
--   ne-sums  = (inl 0 : Nat + Bool) ≠ (inr true : Nat + Bool)

ge-pairs : RawC ∅ˢ 0
ge-pairs = cmp ge ⦉ zero , true ⦊ ⦉ numeral 1 , false ⦊

expected-ge-pairs : Scheme
expected-ge-pairs = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Bool ‼ ûₑ

ne-sums : RawC ∅ˢ 0
ne-sums = cmp ne (inl zero ⦂ᵛ (Nat |+| Bool)) (inr true ⦂ᵛ (Nat |+| Bool))

ne-sums-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Bool ‼ ûₑ
ne-sums-D =
  cmp ne (annᵛ (Nat |+| Bool) (inl zero)) (annᵛ (Nat |+| Bool) (inr true))
      (Natₑ |+|ₑ Boolₑ)

ne-sums-typed : IsTyped (infer [] ne-sums)
ne-sums-typed = typed-of ne-sums (closed ne-sums-D refl) _

expected-ne-sums : Scheme
expected-ne-sums = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Bool ‼ ûₑ

-- Unannotated, the sum's other summands are unknowns: `inl 0` and
-- `inr true` meet at `Nat + Bool`.
--
--   ne-sums' = inl 0 ≠ inr true

ne-sums' : RawC ∅ˢ 0
ne-sums' = cmp ne (inl zero) (inr true)

expected-ne-sums' : Scheme
expected-ne-sums' = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Bool ‼ ûₑ

------------------------------------------------------------------
-- 4. A polymorphic comparison
--
--   equal x y = x = y
--
-- The operands' types are unknowns with a common eternal supertype,
-- asked for at every grade.

equal : RawC ∅ˢ 0
equal = return (lam (return (lam (cmp eq v₁ v₀))))

expected-equal : Scheme
expected-equal =
  ∀[ 3 , 0 , 0 ] eternal α₀ ∧ α₂ <: α₀ ∧ α₁ <: α₀ ⟹
    (α₂ ⇒ (α₁ ⇒ Bool ‼ ûₑ) ‼ ûₑ) ‼ ûₑ

-- An instance at `Nat`, as a derivation

equal-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat ⇒ (Nat ⇒ Bool ‼ ûₑ) ‼ ûₑ) ‼ ûₑ
equal-D = return (lam (return (lam (cmp eq (var (Tl-∷ Hd) ok₀) (var Hd ok₀) Natₑ))))

equal-typed : IsTyped (infer [] equal)
equal-typed = typed-of equal (closed equal-D refl) _

-- One operand compared with itself
--
--   reflexive x = x = x

reflexive : RawC ∅ˢ 0
reflexive = return (lam (cmp eq v₀ v₀))

expected-reflexive : Scheme
expected-reflexive = ∀[ 1 , 0 , 0 ] eternal α₀ ⟹ (α₀ ⇒ Bool ‼ ûₑ) ‼ ûₑ

------------------------------------------------------------------
-- 5. Functions and boxes do not compare
--
--   eq-funs  = (λ _. ()) = (λ _. ())
--   eq-boxes = box[0] () as x in box[0] () as y in x = y

eq-funs : RawC ∅ˢ 0
eq-funs = cmp eq (lam (return ⋆)) (lam (return ⋆))

eq-boxes : RawC ∅ˢ 0
eq-boxes = box ûᵣ ⋆ (box ûᵣ ⋆ (cmp eq v₁ v₀))

------------------------------------------------------------------
-- 6. Comparisons under a lock
--
--   later-lt = let n = 2 in delay 1; n < 3
--
-- `n` is used under the lock `⟨ ⌜ 1 ⌝ʳ ⟩`, which `Nat` survives;
-- typed at every grade.

later-lt : RawC ∅ˢ 0
later-lt = return (numeral 2) ⨟ delay ⌜ 1 ⌝ (cmp lt v₀ (numeral 3))

later-lt-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Bool ‼ (ûₑ ·̂ₑ (⌜ 1 ⌝ᵉ ·̂ₑ ûₑ))
later-lt-D =
  return (numeralᵛ 2)
  ⨟ delay ⌜ 1 ⌝ (cmp lt (var (Tl-⟨⟩ Hd) (et-ok Natₑ)) (numeralᵛ 3) Natₑ)

later-lt-typed : IsTyped (infer [] later-lt)
later-lt-typed = typed-of later-lt (closed later-lt-D refl) _

expected-later-lt : Scheme
expected-later-lt = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Bool ‼ ⌜ 1 ⌝ᵉ

-- A polymorphic comparison after a tick: the eternality the
-- comparison asks for is the one the variable rule needs.
--
--   later-equal x y = delay 1; x = y

later-equal : RawC ∅ˢ 0
later-equal = return (lam (return (lam (delay ⌜ 1 ⌝ (cmp eq v₁ v₀)))))

expected-later-equal : Scheme
expected-later-equal =
  ∀[ 3 , 0 , 0 ] eternal α₀ ∧ α₂ <: α₀ ∧ α₁ <: α₀ ⟹
    (α₂ ⇒ (α₁ ⇒ Bool ‼ ⌜ 1 ⌝ᵉ) ‼ ûₑ) ‼ ûₑ
