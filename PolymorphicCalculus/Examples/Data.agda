--------------------------------------------------------------------
-- Inference on natural numbers, sums and lists                   --
--                                                                --
-- `caseℕ`, `case+` and `caseL` with their constructors. `Nat` is --
-- eternal; sums and lists are covariant, and eternal exactly     --
-- when their components are, so they survive a lock where a      --
-- function does not. `⌜ n ⌝` is the duration of `n` ticks. The   --
-- instances under `Data/` check each answer by `refl` at both    --
-- time grades.                                                   --
--------------------------------------------------------------------

open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat using (ℕ; suc)

open import Relation.Nullary.Decidable using (True; toWitness)

open import Grades.Durations using (Stepped)
open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Examples.Data (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S)
  (st : Stepped (GradeSystem.Dur (LanguageSpec.Grades S))) where

open LanguageSpec S
open GradeSystemInterface Grades
  using (R; 𝔻; ιᵣ; ιₑ; 𝟏ᵣ; _⊔ₑ_; _≾ᵣ?_)
  renaming (_≾ᵣ_ to _≾ᴳ_)

open import PolymorphicCalculus.Syntax.Grades                S
open import PolymorphicCalculus.Syntax.Types                 S
open import PolymorphicCalculus.Syntax.Contexts              S hiding (Scheme)
open import PolymorphicCalculus.Syntax.GradeSubstitution     S using (idˢ)
open import PolymorphicCalculus.Hypotheses                   S
open import PolymorphicCalculus.Hypotheses.Instances         S using (Satisfiable-∅)
open import PolymorphicCalculus.Typing                       S
open import PolymorphicCalculus.Syntax.Raw                   S
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution S using (_[_]ᴿᶜ)
open import PolymorphicCalculus.Typing.Erasure               S using (⌊_⌋ᶜ)
open import PolymorphicCalculus.Inference.Principality       S
open import PolymorphicCalculus.Inference.SolverImpl         S hints opEnum
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

closed : {M : RawC ∅ˢ 0} {C : OCType ∅ˢ} → (D : ∅ᴴ ∣ [] ⊢C⦂ C)
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

  ok₀ : ∀ {Θ} {Q : Hyps Θ} {A : OVType Θ} → VarOK Q A 𝟏̂ᵣ
  ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

  -- A claim made after exactly the box's grade

  on-time : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → Q ⊩ 𝟏̂ᵣ ·̂ᵣ ρ ≾̂ᵣ ρ
  on-time = eqᵣ ≡̂ᵣ-identityˡ

  -- A use after a closed grade below the unit

  after : ∀ {Θ} {Q : Hyps Θ} {c : R} → c ≾ᴳ 𝟏ᵣ → Q ⊩ 𝟏̂ᵣ ·̂ᵣ rconst c ≾̂ᵣ 𝟏̂ᵣ
  after p = transᵣ on-time (atomᵣ p)

------------------------------------------------------------------
-- 1. Eliminating a natural number
--
--   is-zero n = caseℕ n of zero ↦ true | succ m ↦ false
--   pred n    = caseℕ n of zero ↦ 0    | succ m ↦ m
--
-- Typed at every grade.

is-zero : RawC ∅ˢ 0
is-zero = return (lam (caseℕ v₀ `zero return true `succ return false))

is-zero-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat ⇒ Bool ‼ 𝟏̂ₑ) ‼ 𝟏̂ₑ
is-zero-D = return (lam (caseℕ var Hd ok₀ `zero return true `succ return false))

is-zero-typed : IsTyped (infer [] is-zero)
is-zero-typed = typed-of is-zero (closed is-zero-D refl) _

expected-is-zero : Scheme
expected-is-zero = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Nat ⇒ Bool ‼ 𝟏̂ₑ) ‼ 𝟏̂ₑ

pred : RawC ∅ˢ 0
pred = return (lam (caseℕ v₀ `zero return zero `succ return v₀))

pred-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat ⇒ Nat ‼ 𝟏̂ₑ) ‼ 𝟏̂ₑ
pred-D = return (lam (caseℕ var Hd ok₀ `zero return zero `succ return (var Hd ok₀)))

pred-typed : IsTyped (infer [] pred)
pred-typed = typed-of pred (closed pred-D refl) _

expected-pred : Scheme
expected-pred = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Nat ⇒ Nat ‼ 𝟏̂ₑ) ‼ 𝟏̂ₑ

--   case-of-bool = caseℕ true of zero ↦ () | succ m ↦ ()
--
-- Refused: `Bool` is not `Nat`.

case-of-bool : RawC ∅ˢ 0
case-of-bool = caseℕ true `zero return ⋆ `succ return ⋆

------------------------------------------------------------------
-- 2. A natural number used under a lock
--
--   later-succ n = delay 1; succ n
--
-- `Nat` is eternal: typed at every grade.

later-succ : RawC ∅ˢ 0
later-succ = return (lam (delay ⌜ 1 ⌝ (return (succ v₀))))

later-succ-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat ⇒ Nat ‼ (⌜ 1 ⌝ᵉ ·̂ₑ 𝟏̂ₑ)) ‼ 𝟏̂ₑ
later-succ-D = return (lam (delay ⌜ 1 ⌝ (return (succ (var (Tl-⟨⟩ Hd) (et-ok Natₑ))))))

later-succ-typed : IsTyped (infer [] later-succ)
later-succ-typed = typed-of later-succ (closed later-succ-D refl) _

expected-later-succ : Scheme
expected-later-succ = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Nat ⇒ Nat ‼ ⌜ 1 ⌝ᵉ) ‼ 𝟏̂ₑ

--   later-id x = delay 1; x
--
-- `eternal α ∨ ⌜ 1 ⌝ʳ ≾ 𝟏ᵣ`: dropped at the left-sided grades,
-- `eternal α` at the right-sided ones.

later-id : RawC ∅ˢ 0
later-id = return (lam (delay ⌜ 1 ⌝ (return v₀)))

expected-later-id-eternal : Scheme
expected-later-id-eternal =
  ∀[ 1 , 0 , 0 ] eternal α₀ ⟹ (α₀ ⇒ α₀ ‼ ⌜ 1 ⌝ᵉ) ‼ 𝟏̂ₑ

expected-later-id : Scheme
expected-later-id = ∀[ 1 , 0 , 0 ] ⊤ ⟹ (α₀ ⇒ α₀ ‼ ⌜ 1 ⌝ᵉ) ‼ 𝟏̂ₑ

--   numeral-later = let n = 2 in delay 1; succ n
--
-- Typed at every grade.

numeral-later : RawC ∅ˢ 0
numeral-later = return (numeral 2) ⨟ delay ⌜ 1 ⌝ (return (succ v₀))

numeral-later-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Nat ‼ (𝟏̂ₑ ·̂ₑ (⌜ 1 ⌝ᵉ ·̂ₑ 𝟏̂ₑ))
numeral-later-D =
  return (numeralᵛ 2) ⨟ delay ⌜ 1 ⌝ (return (succ (var (Tl-⟨⟩ Hd) (et-ok Natₑ))))

numeral-later-typed : IsTyped (infer [] numeral-later)
numeral-later-typed = typed-of numeral-later (closed numeral-later-D refl) _

expected-numeral-later : Scheme
expected-numeral-later = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Nat ‼ ⌜ 1 ⌝ᵉ

--   function-later = let f = (λ _. ()) in delay 1; f ()
--
-- A function is not eternal: typed at the left-sided grades only.

function-later : RawC ∅ˢ 0
function-later = return (lam (return ⋆)) ⨟ delay ⌜ 1 ⌝ (v₀ · ⋆)

function-later-D : ιᵣ ⌜ 1 ⌝ ≾ᴳ 𝟏ᵣ → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Unit ‼ (𝟏̂ₑ ·̂ₑ (⌜ 1 ⌝ᵉ ·̂ₑ 𝟏̂ₑ))
function-later-D q =
  return (lam {A = Unit} (return ⋆))
  ⨟ delay ⌜ 1 ⌝ (var (Tl-⟨⟩ Hd) (≾ᵘ-ok (after q)) · ⋆)

function-later-typable : True (ιᵣ ⌜ 1 ⌝ ≾ᵣ? 𝟏ᵣ) → Typable [] function-later
function-later-typable q = closed (function-later-D (toWitness q)) refl

expected-function-later : Scheme
expected-function-later = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Unit ‼ ⌜ 1 ⌝ᵉ

------------------------------------------------------------------
-- 3. A boxed numeral
--
--   boxed-numeral = box[2] 3 as x in delay 2; unbox x as n in succ n
--
-- The claim is on time at every grade.

boxed-numeral : RawC ∅ˢ 0
boxed-numeral = box ⌜ 2 ⌝ʳ (numeral 3) (delay ⌜ 2 ⌝ (unbox (var fzero) (return (succ v₀))))

boxed-numeral-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Nat ‼ (⌜ 2 ⌝ᵉ ·̂ₑ 𝟏̂ₑ)
boxed-numeral-D =
  box ⌜ 2 ⌝ʳ (numeralᵛ 3)
    (delay ⌜ 2 ⌝ (unbox (res-var {z = Tl-⟨⟩ Hd}) on-time (return (succ (var Hd ok₀)))))

boxed-numeral-typed : IsTyped (infer [] boxed-numeral)
boxed-numeral-typed = typed-of boxed-numeral (closed boxed-numeral-D refl) _

expected-boxed-numeral : Scheme
expected-boxed-numeral = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Nat ‼ ⌜ 2 ⌝ᵉ

------------------------------------------------------------------
-- 4. Branches of different effects
--
--   joined n = caseℕ n of zero ↦ delay 1; 0 | succ m ↦ delay 3; m
--
-- The effect is the join: three ticks at the right-sided grades, one
-- at the left-sided ones.

joined : RawC ∅ˢ 0
joined =
  return (lam (caseℕ v₀ `zero delay ⌜ 1 ⌝ (return zero)
                        `succ delay ⌜ 3 ⌝ (return v₀)))

joined-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat ⇒ Nat ‼ (⌜ 1 ⌝ᵉ ⊔̂ₑ ⌜ 3 ⌝ᵉ)) ‼ 𝟏̂ₑ
joined-D =
  return (lam (caseℕ var Hd ok₀
    `zero coerce (transₑ (eqₑ ≡̂ₑ-identityʳ) ⊔-ubˡₑ) (delay ⌜ 1 ⌝ (return zero))
    `succ coerce (transₑ (eqₑ ≡̂ₑ-identityʳ) ⊔-ubʳₑ)
            (delay ⌜ 3 ⌝ (return (var (Tl-⟨⟩ Hd) (et-ok Natₑ))))))

joined-typed : IsTyped (infer [] joined)
joined-typed = typed-of joined (closed joined-D refl) _

expected-joined : Scheme
expected-joined =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹
    (Nat ⇒ Nat ‼ econst (ιₑ ⌜ 1 ⌝ ⊔ₑ ιₑ ⌜ 3 ⌝)) ‼ 𝟏̂ₑ

------------------------------------------------------------------
-- 5. Sums
--
--   swap s = case+ s of inl x ↦ inr x | inr y ↦ inl y
--
-- Typed at every grade.

swap : RawC ∅ˢ 0
swap = return (lam (case+ v₀ `inl return (inr v₀) `inr return (inl v₀)))

swap-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat |+| Bool ⇒ Bool |+| Nat ‼ 𝟏̂ₑ) ‼ 𝟏̂ₑ
swap-D =
  return (lam (case+ var Hd ok₀ `inl return (inr (var Hd ok₀))
                                `inr return (inl (var Hd ok₀))))

swap-typed : IsTyped (infer [] swap)
swap-typed = typed-of swap (closed swap-D refl) _

expected-swap : Scheme
expected-swap = ∀[ 2 , 0 , 0 ] ⊤ ⟹ (α₁ |+| α₀ ⇒ α₀ |+| α₁ ‼ 𝟏̂ₑ) ‼ 𝟏̂ₑ

--   choose s = case+ s of inl n ↦ delay 1; succ n | inr _ ↦ delay 3; 0
--
-- The effects are joined as for `caseℕ`.

choose : RawC ∅ˢ 0
choose =
  return (lam (case+ v₀ `inl delay ⌜ 1 ⌝ (return (succ v₀))
                        `inr delay ⌜ 3 ⌝ (return zero)))

choose-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat |+| Bool ⇒ Nat ‼ (⌜ 1 ⌝ᵉ ⊔̂ₑ ⌜ 3 ⌝ᵉ)) ‼ 𝟏̂ₑ
choose-D =
  return (lam (case+ var Hd ok₀
    `inl coerce (transₑ (eqₑ ≡̂ₑ-identityʳ) ⊔-ubˡₑ)
            (delay ⌜ 1 ⌝ (return (succ (var (Tl-⟨⟩ Hd) (et-ok Natₑ)))))
    `inr coerce (transₑ (eqₑ ≡̂ₑ-identityʳ) ⊔-ubʳₑ) (delay ⌜ 3 ⌝ (return zero))))

choose-typed : IsTyped (infer [] choose)
choose-typed = typed-of choose (closed choose-D refl) _

expected-choose : Scheme
expected-choose =
  ∀[ 1 , 0 , 0 ] ⊤ ⟹
    (Nat |+| α₀ ⇒ Nat ‼ econst (ιₑ ⌜ 1 ⌝ ⊔ₑ ιₑ ⌜ 3 ⌝)) ‼ 𝟏̂ₑ

-- Subtyping in a summand; typed at every grade.
--
--   subsume-sum = let f = (λ s. case+ s of inl _ ↦ delay 3; ()
--                                  | inr g ↦ g ())
--                   : Nat + (Unit ⇒ Unit ‼ 1 ⊔ 3) ⇒ Unit ‼ 1 ⊔ 3
--           in f (inr (λ _. delay 1; ()) : Nat + (Unit ⇒ Unit ‼ 1))

private

  j₁₃ : ∀ {Θ} → EExp Θ
  j₁₃ = ⌜ 1 ⌝ᵉ ⊔̂ₑ ⌜ 3 ⌝ᵉ

  Wide Narrow : ∀ {Θ} → OVType Θ
  Wide   = Nat |+| (Unit ⇒ Unit ‼ j₁₃)
  Narrow = Nat |+| (Unit ⇒ Unit ‼ ⌜ 1 ⌝ᵉ)

subsume-sum : RawC ∅ˢ 0
subsume-sum =
  return (lam (case+ v₀ `inl delay ⌜ 3 ⌝ (return ⋆) `inr (v₀ · ⋆))
            ⦂ᵛ (Wide ⇒ Unit ‼ j₁₃))
  ⨟ (v₀ · (inr (lam (delay ⌜ 1 ⌝ (return ⋆))) ⦂ᵛ Narrow))

subsume-sum-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Unit ‼ (𝟏̂ₑ ·̂ₑ j₁₃)
subsume-sum-D =
  return (annᵛ (Wide ⇒ Unit ‼ j₁₃)
           (lam (case+ var Hd ok₀
                  `inl coerce (transₑ (eqₑ ≡̂ₑ-identityʳ) ⊔-ubʳₑ) (delay ⌜ 3 ⌝ (return ⋆))
                  `inr (var Hd ok₀ · ⋆))))
  ⨟ (var Hd ok₀ · subV (annᵛ Narrow
                           (inr (lam (coerce (eqₑ ≡̂ₑ-identityʳ) (delay ⌜ 1 ⌝ (return ⋆))))))
                         (Natₛ |+|ₛ (Unitₛ ⇒ₛ (Unitₛ ‼ₛ ⊔-ubˡₑ))))

subsume-sum-typed : IsTyped (infer [] subsume-sum)
subsume-sum-typed = typed-of subsume-sum (closed subsume-sum-D refl) _

expected-subsume-sum : Scheme
expected-subsume-sum = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Unit ‼ econst (ιₑ ⌜ 1 ⌝ ⊔ₑ ιₑ ⌜ 3 ⌝)

--   sum-later = let s = (inl 2 : Nat + Bool) in delay 1; s
--
-- `Nat + Bool` is eternal: typed at every grade.

sum-later : RawC ∅ˢ 0
sum-later = return (inl (numeral 2) ⦂ᵛ (Nat |+| Bool)) ⨟ delay ⌜ 1 ⌝ (return v₀)

sum-later-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat |+| Bool) ‼ (𝟏̂ₑ ·̂ₑ (⌜ 1 ⌝ᵉ ·̂ₑ 𝟏̂ₑ))
sum-later-D =
  return (annᵛ (Nat |+| Bool) (inl (numeralᵛ 2)))
  ⨟ delay ⌜ 1 ⌝ (return (var (Tl-⟨⟩ Hd) (et-ok (Natₑ |+|ₑ Boolₑ))))

sum-later-typed : IsTyped (infer [] sum-later)
sum-later-typed = typed-of sum-later (closed sum-later-D refl) _

expected-sum-later : Scheme
expected-sum-later = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Nat |+| Bool) ‼ ⌜ 1 ⌝ᵉ

--   inl-later = let s = inl 2 in delay 1; s
--
-- The unknown summand is asked to be eternal at the right-sided grades.

inl-later : RawC ∅ˢ 0
inl-later = return (inl (numeral 2)) ⨟ delay ⌜ 1 ⌝ (return v₀)

expected-inl-later-eternal : Scheme
expected-inl-later-eternal = ∀[ 1 , 0 , 0 ] eternal α₀ ⟹ (Nat |+| α₀) ‼ ⌜ 1 ⌝ᵉ

expected-inl-later : Scheme
expected-inl-later = ∀[ 1 , 0 , 0 ] ⊤ ⟹ (Nat |+| α₀) ‼ ⌜ 1 ⌝ᵉ

--   fun-sum-later = let s = (inr (λ _. delay 1; ()) : Nat + (Unit ⇒ Unit ‼ 1))
--                   in delay 1; s
--
-- A function summand is not eternal: typed at the left-sided grades only.

fun-sum-later : RawC ∅ˢ 0
fun-sum-later =
  return (inr (lam (delay ⌜ 1 ⌝ (return ⋆))) ⦂ᵛ Narrow) ⨟ delay ⌜ 1 ⌝ (return v₀)

fun-sum-later-D : ιᵣ ⌜ 1 ⌝ ≾ᴳ 𝟏ᵣ → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Narrow ‼ (𝟏̂ₑ ·̂ₑ (⌜ 1 ⌝ᵉ ·̂ₑ 𝟏̂ₑ))
fun-sum-later-D q =
  return (annᵛ Narrow (inr (lam (coerce (eqₑ ≡̂ₑ-identityʳ) (delay ⌜ 1 ⌝ (return ⋆))))))
  ⨟ delay ⌜ 1 ⌝ (return (var (Tl-⟨⟩ Hd) (≾ᵘ-ok (after q))))

fun-sum-later-typable : True (ιᵣ ⌜ 1 ⌝ ≾ᵣ? 𝟏ᵣ) → Typable [] fun-sum-later
fun-sum-later-typable q = closed (fun-sum-later-D (toWitness q)) refl

expected-fun-sum-later : Scheme
expected-fun-sum-later =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Nat |+| (Unit ⇒ Unit ‼ ⌜ 1 ⌝ᵉ)) ‼ ⌜ 1 ⌝ᵉ

--   case-of-bool+ = case+ true of inl _ ↦ () | inr _ ↦ ()
--
-- Refused: `Bool` is not a sum.

case-of-bool+ : RawC ∅ˢ 0
case-of-bool+ = case+ true `inl return ⋆ `inr return ⋆

------------------------------------------------------------------
-- 6. Lists
--
--   head-or d l = caseL l of nil ↦ d | cons h t ↦ h
--
-- The result is a common supertype of `d` and `h`; typed everywhere.

head-or : RawC ∅ˢ 0
head-or = return (lam (return (lam (caseL v₀ `nil return v₁ `cons return v₁))))

head-or-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat ⇒ (|List| Nat ⇒ Nat ‼ 𝟏̂ₑ) ‼ 𝟏̂ₑ) ‼ 𝟏̂ₑ
head-or-D =
  return (lam (return (lam (caseL var Hd ok₀ `nil return (var (Tl-∷ Hd) ok₀)
                                            `cons return (var (Tl-∷ Hd) ok₀)))))

head-or-typed : IsTyped (infer [] head-or)
head-or-typed = typed-of head-or (closed head-or-D refl) _

expected-head-or : Scheme
expected-head-or =
  ∀[ 3 , 0 , 0 ] α₂ <: α₁ ∧ α₀ <: α₁ ⟹ (α₂ ⇒ (|List| α₀ ⇒ α₁ ‼ 𝟏̂ₑ) ‼ 𝟏̂ₑ) ‼ 𝟏̂ₑ

--   list-later = let l = ([2] : List Nat) in delay 1; l
--
-- `List Nat` is eternal: typed at every grade.

list-later : RawC ∅ˢ 0
list-later = return (cons (numeral 2) nil ⦂ᵛ |List| Nat) ⨟ delay ⌜ 1 ⌝ (return v₀)

list-later-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ |List| Nat ‼ (𝟏̂ₑ ·̂ₑ (⌜ 1 ⌝ᵉ ·̂ₑ 𝟏̂ₑ))
list-later-D =
  return (annᵛ (|List| Nat) (cons (numeralᵛ 2) nil))
  ⨟ delay ⌜ 1 ⌝ (return (var (Tl-⟨⟩ Hd) (et-ok (|List|ₑ Natₑ))))

list-later-typed : IsTyped (infer [] list-later)
list-later-typed = typed-of list-later (closed list-later-D refl) _

expected-list-later : Scheme
expected-list-later = ∀[ 0 , 0 , 0 ] ⊤ ⟹ |List| Nat ‼ ⌜ 1 ⌝ᵉ

--   nil-later = let l = [] in delay 1; l
--
-- The unknown element type is asked to be eternal at the right-sided
-- grades.

nil-later : RawC ∅ˢ 0
nil-later = return nil ⨟ delay ⌜ 1 ⌝ (return v₀)

expected-nil-later-eternal : Scheme
expected-nil-later-eternal = ∀[ 1 , 0 , 0 ] eternal α₀ ⟹ |List| α₀ ‼ ⌜ 1 ⌝ᵉ

expected-nil-later : Scheme
expected-nil-later = ∀[ 1 , 0 , 0 ] ⊤ ⟹ |List| α₀ ‼ ⌜ 1 ⌝ᵉ

--   fun-list-later = let l = ([λ _. ()] : List (Unit ⇒ Unit)) in delay 1; l
--
-- Not eternal: typed at the left-sided grades only.

private

  Fn : ∀ {Θ} → OVType Θ
  Fn = Unit ⇒ Unit ‼ 𝟏̂ₑ

fun-list-later : RawC ∅ˢ 0
fun-list-later =
  return (cons (lam (return ⋆)) nil ⦂ᵛ |List| Fn) ⨟ delay ⌜ 1 ⌝ (return v₀)

fun-list-later-D : ιᵣ ⌜ 1 ⌝ ≾ᴳ 𝟏ᵣ → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ |List| Fn ‼ (𝟏̂ₑ ·̂ₑ (⌜ 1 ⌝ᵉ ·̂ₑ 𝟏̂ₑ))
fun-list-later-D q =
  return (annᵛ (|List| Fn) (cons (lam (return ⋆)) nil))
  ⨟ delay ⌜ 1 ⌝ (return (var (Tl-⟨⟩ Hd) (≾ᵘ-ok (after q))))

fun-list-later-typable : True (ιᵣ ⌜ 1 ⌝ ≾ᵣ? 𝟏ᵣ) → Typable [] fun-list-later
fun-list-later-typable q = closed (fun-list-later-D (toWitness q)) refl

expected-fun-list-later : Scheme
expected-fun-list-later = ∀[ 0 , 0 , 0 ] ⊤ ⟹ |List| Fn ‼ ⌜ 1 ⌝ᵉ

--   case-of-nat = caseL 0 of nil ↦ () | cons h t ↦ ()
--
-- Refused: `Nat` is not a list.

case-of-nat : RawC ∅ˢ 0
case-of-nat = caseL zero `nil return ⋆ `cons return ⋆
