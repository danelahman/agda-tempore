------------------------------------------------------------------------
-- Inference on primitive recursion                                   --
--                                                                    --
-- Recursion on natural numbers, `recℕ V M N`, and on lists,          --
-- `recL V M N`. The step is typed under a modality at `⊤ᵣ`, so only  --
-- outer variables of eternal type are usable in it. It binds the     --
-- predecessor (or the head and tail), then, after a modality at the  --
-- effect `ε` of the recursion, the recursive result. That effect     --
-- absorbs its own iteration, `ε · ε ≾ ε`. `⌜ n ⌝` is the duration of --
-- `n` ticks.                                                         --
--                                                                    --
-- The examples                                                       --
--   add                  pure recursion on the recursive result      --
--   rebuild, mul         the predecessor, and an outer natural       --
--                        number, in the step                         --
--   each                 a function from outside the step            --
--   countdown            a tick per step; also on a numeral,         --
--                        annotated at `k` ticks (`countdown-at`), at --
--                        the top (`countdown-top`), and two ticks    --
--                        annotated at one (`wait-2-at-1`)            --
--   in-clause-pure,      recursion inside an operation clause, with  --
--   in-clause-tick       a pure step and with a tick per step        --
--   drop-clause          a clause that counts down and drops its     --
--                        continuation                                --
--   length, sum,         pure recursion on lists                     --
--   inc-all                                                          --
--   copy, call-all,      the head in the step: of any type, a        --
--   last-or, last-box,   function, after a tick, boxed, and unboxed  --
--   latest, latest-ready                                             --
--   ticks                a tick per element; also annotated          --
--                        (`ticks-at`, `ticks-top`)                   --
--   twice, twice-run     a function calling the recursive result     --
--                        twice; also annotated (`twice-run-at`)      --
--                                                                    --
-- How to read them                                                   --
--   Each program is written above its definition in ordinary         --
--   syntax. Where a typing is written out as a derivation, it is     --
--   checked here (`add-typed`, `countdown-top-typable`). The modules --
--   under `Recursion/` run inference at upper and lower bounds and   --
--   check the answer with `refl`:                                    --
--     add-reported : schemeOf (infer [] add) ≡ just expected-add     --
--   Where checking the closed program finds a satisfying instance,   --
--   the verdict `established` is checked too, and read back as a     --
--   typing (`check-typable`). A refuted example comes with a proof   --
--   that it is untypable. `twice` and `twice-run` are checked at     --
--   upper bounds only.                                               --
------------------------------------------------------------------------

open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat using (ℕ; suc)

open import Grades.Durations using (Stepped)
open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Examples.Recursion (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S)
  (st : Stepped (GradeSystem.Dur (LanguageSpec.Grades S))) where

open LanguageSpec S
open GradeSystemInterface Grades using (R; 𝔻; ιᵣ; ιₑ; ⊤ᵣ; ⊤ₑ; ≃ᵣ⇒≾ᵣ; map-𝟏ᵉ)
open Operations Ops using (Op; op-grade)

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
  using (infer-complete; infer-handlerFree; check-established)

open import PolymorphicCalculus.Inference.SolverImpl S hints opEnum using (infer; check) public
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

-- The verdict of a check, its evidence dropped

data Verdict : Set where
  established untypable unestablished stuck : Verdict

verdict : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} → Check Γ M → Verdict
verdict (established _ _)  = established
verdict Check.untypable    = untypable
verdict (unestablished _)  = unestablished
verdict Check.stuck        = stuck

-- An established verdict, read back as a typing (`check-established`)

check-typable : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
              → verdict (check Γ M) ≡ established → Typable Γ M
check-typable Γ M v with check Γ M in e
check-typable Γ M v  | established p s = check-established Γ M e
check-typable Γ M () | Check.untypable
check-typable Γ M () | unestablished _
check-typable Γ M () | Check.stuck

------------------------------------------------------------------
-- Side conditions

private

  -- A variable no time has passed over

  ok₀ : ∀ {Θ} {Q : Hyps Θ} {A : OVType Θ} → Q ⊩ A Et∨≾ᵘ 𝟏̂ᵣ
  ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

  -- A natural number, usable under any modality

  okℕ : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → Q ⊩ nat Et∨≾ᵘ ρ
  okℕ = et-ok natₑ

  -- A unit effect has passed

  𝟏-passed : ∀ {Θ} {Q : Hyps Θ} → Q ⊩ 𝟏̂ᵣ ·̂ᵣ ∣ 𝟏̂ₑ ∣̂ᵉ ≾̂ᵣ 𝟏̂ᵣ
  𝟏-passed = transᵣ (eqᵣ ≡̂ᵣ-identityˡ)
               (transᵣ (eqᵣ ≡̂ᵣ-map-const) (atomᵣ (≃ᵣ⇒≾ᵣ map-𝟏ᵉ)))

  -- A pure step iterates purely

  pure : ∀ {Θ} {Q : Hyps Θ} → Q ⊩ 𝟏̂ₑ ·̂ₑ 𝟏̂ₑ ≾̂ₑ 𝟏̂ₑ
  pure = eqₑ ≡̂ₑ-identityˡ

------------------------------------------------------------------
-- 1. Pure recursion: the result of the recursive call
--
--   add m n = recℕ m with zero ↦ n | succ p, r ↦ succ r
--
-- The effect is the unit; typed at every grade.

add : RawC ∅ˢ 0
add = return (fun (return (fun (recℕ v₁ (return v₀) (return (succ v₀))))))

add-D : ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ (nat ⇒ (nat ⇒ nat ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ
add-D =
  return (fun (return (fun
    (recℕ (var (Tl-∷ Hd) ok₀) (return (var Hd ok₀)) (return (succ (var Hd ok₀))) pure))))

add-typed : IsTyped (infer [] add)
add-typed = typed-of add (closed add-D refl) _

------------------------------------------------------------------
-- 2. The predecessor, and an outer natural number, in the step
--
--   rebuild n = recℕ n with zero ↦ 0 | succ p, r ↦ succ p
--   mul m n   = recℕ m with zero ↦ 0 | succ p, r ↦ add n r
--
-- `p` and `n` are `nat`, so the variable rule asks nothing; `add n r`
-- is written out as a second `recℕ`. Typed at every grade.

rebuild : RawC ∅ˢ 0
rebuild = return (fun (recℕ v₀ (return zero) (return (succ v₁))))

rebuild-D : ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ (nat ⇒ nat ! 𝟏̂ₑ) ! 𝟏̂ₑ
rebuild-D =
  return (fun
    (recℕ (var Hd ok₀) (return zero) (return (succ (var (Tl-∷ (Tl-⟨⟩ Hd)) okℕ))) pure))

rebuild-typed : IsTyped (infer [] rebuild)
rebuild-typed = typed-of rebuild (closed rebuild-D refl) _

mul : RawC ∅ˢ 0
mul =
  return (fun (return (fun
    (recℕ v₁ (return zero) (recℕ v₂ (return v₀) (return (succ v₀)))))))

mul-D : ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ (nat ⇒ (nat ⇒ nat ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ
mul-D =
  return (fun (return (fun
    (recℕ (var (Tl-∷ Hd) ok₀) (return zero)
          (recℕ (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) okℕ)
                (return (var Hd ok₀)) (return (succ (var Hd ok₀))) pure)
          pure))))

mul-typed : IsTyped (infer [] mul)
mul-typed = typed-of mul (closed mul-D refl) _

------------------------------------------------------------------
-- 3. A function from outside the step
--
--   each f n = recℕ n with zero ↦ () | succ p, r ↦ f ()
--
-- `f` is not eternal, so the variable rule asks `⊤ᵣ ≾ 𝟏ᵣ`.

each : RawC ∅ˢ 0
each = return (fun (return (fun (recℕ v₀ (return ⋆) (v₃ · ⋆)))))

------------------------------------------------------------------
-- 4. A countdown: a tick per step
--
--   countdown n = recℕ n with zero ↦ () | succ p, r ↦ delay 1; ()
--
-- `⌜ 1 ⌝ ≾ ε` and `ε · ε ≾ ε`.

countdown : RawC ∅ˢ 0
countdown = return (fun (recℕ v₀ (return ⋆) (delay ⌜ 1 ⌝ (return ⋆))))

-- On a numeral, annotated at `k` ticks
--
--   countdown-at k = (recℕ 3 with zero ↦ () | succ p, r ↦ delay 1; ()) : Unit ! k

countdown-on : RawC ∅ˢ 0
countdown-on = recℕ (numeral 3) (return ⋆) (delay ⌜ 1 ⌝ (return ⋆))

countdown-at : ℕ → RawC ∅ˢ 0
countdown-at k = countdown-on ⦂ᶜ (unit ! ⌜ k ⌝ᵉ)

-- Two ticks annotated at one, as Tempore's `wait 2 : unit # 1`

wait-2-at-1 : RawC ∅ˢ 0
wait-2-at-1 = recℕ (numeral 2) (return ⋆) (delay ⌜ 1 ⌝ (return ⋆)) ⦂ᶜ (unit ! ⌜ 1 ⌝ᵉ)

-- annotated at the top

countdown-top : RawC ∅ˢ 0
countdown-top = countdown-on ⦂ᶜ (unit ! econst ⊤ₑ)

-- typable at every grade

countdown-top-D : ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ unit ! econst ⊤ₑ
countdown-top-D =
  annᶜ (unit ! econst ⊤ₑ)
    (recℕ (numeralᵛ 3) (coerce topₑ (return ⋆)) (coerce topₑ (delay ⌜ 1 ⌝ (return ⋆))) topₑ)

countdown-top-typable : Typable [] countdown-top
countdown-top-typable = closed countdown-top-D refl

------------------------------------------------------------------
-- 5. Recursion inside an operation clause
--
--   in-clause step = handle () with handler {
--                      op p k ↦ recℕ 2 with zero ↦ () | succ p', r ↦ step;
--                               let a = op p in unbox k as k' in k' a;
--                      return x ↦ ()}
--
-- The recursion's effect is local to the clause, and bounded by
-- `op · j` only through its product with the resumption's effect.

rec-then-resume : ∀ {Θ n} → RawC (Θ +e) (suc (suc (suc (suc n)))) → Op
                → RawC (Θ +e) (suc (suc n))
rec-then-resume step op =
  recℕ (numeral 2) (return ⋆) step
  ⨟ perform op v₂ (unbox (var (fsuc (fsuc fzero))) (v₀ · v₁))

in-clause : (∀ {Θ n} → RawC (Θ +e) (suc (suc (suc (suc n))))) → RawC ∅ˢ 0
in-clause step = handle (return ⋆) `with handler (return ⋆) (rec-then-resume step)

-- a pure step, and a step of a tick

in-clause-pure : RawC ∅ˢ 0
in-clause-pure = in-clause (return ⋆)

in-clause-tick : RawC ∅ˢ 0
in-clause-tick = in-clause (delay ⌜ 1 ⌝ (return ⋆))

-- With a pure step, typable at every grade

in-clause-pure-D : ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ unit ! (𝟏̂ₑ ·̂ₑ 𝟏̂ₑ)
in-clause-pure-D =
  handle (return ⋆)
  `with handler (return ⋆) (λ op →
    coerce (eqₑ ≡̂ₑ-identityˡ)
      (recℕ (numeralᵛ 2) (return ⋆) (return ⋆) pure
       ⨟ perform op (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) (≾ᵘ-ok 𝟏-passed))
           (unbox (res-var (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))))
                  (transᵣ (monoᵣ 𝟏-passed ⊩≾̂ᵣ-refl) (eqᵣ ≡̂ᵣ-identityˡ))
                  (var Hd ok₀ · var (Tl-∷ Hd) ok₀))))

in-clause-pure-typable : Typable [] in-clause-pure
in-clause-pure-typable = closed in-clause-pure-D refl

------------------------------------------------------------------
-- 6. A clause that drops its continuation
--
--   drop-clause = handle () with handler {
--                   op p k ↦ recℕ 2 with zero ↦ () | succ p', r ↦ delay 1; ();
--                   return x ↦ ()}
--
-- The recursion's effect, at least a tick, must lie below `op · j`
-- for every `j`.

drop-clause : RawC ∅ˢ 0
drop-clause =
  handle (return ⋆) `with handler (return ⋆) (λ op → recℕ (numeral 2) (return ⋆) (delay ⌜ 1 ⌝ (return ⋆)))

------------------------------------------------------------------
-- 7. Pure recursion on lists
--
--   length l  = recL l with nil ↦ 0  | cons h t, r ↦ succ r
--   sum l     = recL l with nil ↦ 0  | cons h t, r ↦ add h r
--   inc-all l = recL l with nil ↦ [] | cons h t, r ↦ cons (succ h) r
--
-- `add h r` is written out as a `recℕ` on the head. Typed at every
-- grade.

length : RawC ∅ˢ 0
length = return (fun (recL v₀ (return zero) (return (succ v₀))))

length-D : ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ (list bool ⇒ nat ! 𝟏̂ₑ) ! 𝟏̂ₑ
length-D = return (fun (recL (var Hd ok₀) (return zero) (return (succ (var Hd ok₀))) pure))

length-typed : IsTyped (infer [] length)
length-typed = typed-of length (closed length-D refl) _

sum : RawC ∅ˢ 0
sum = return (fun (recL v₀ (return zero) (recℕ v₂ (return v₀) (return (succ v₀)))))

inc-all : RawC ∅ˢ 0
inc-all = return (fun (recL v₀ (return nil) (return (cons (succ v₂) v₀))))

------------------------------------------------------------------
-- 8. The head in the step
--
--   copy l       = recL l with nil ↦ [] | cons h t, r ↦ cons h r
--   call-all l   = recL l with nil ↦ () | cons h t, r ↦ h ()
--   last-or d l  = recL l with nil ↦ d  | cons h t, r ↦ delay 1; h
--   last-box d l = last-or d (l : List ([1] Nat))
--
-- The head needs `eternal A ∨ ∣ ε ∣ ≾ 𝟏ᵣ`: any type with a pure step;
-- with a tick, eternal at the upper-bound grades, so boxes are refused.

copy : RawC ∅ˢ 0
copy = return (fun (recL v₀ (return nil) (return (cons v₂ v₀))))

private

  Fn : ∀ {Θ} → OVType Θ
  Fn = unit ⇒ unit ! 𝟏̂ₑ

copy-D : ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ (list Fn ⇒ list Fn ! 𝟏̂ₑ) ! 𝟏̂ₑ
copy-D =
  return (fun
    (recL (var Hd ok₀) (return nil)
          (return (cons (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) (≾ᵘ-ok 𝟏-passed)) (var Hd ok₀)))
          pure))

copy-typed : IsTyped (infer [] copy)
copy-typed = typed-of copy (closed copy-D refl) _

call-all : RawC ∅ˢ 0
call-all = return (fun (recL v₀ (return ⋆) (v₂ · ⋆)))

last-or : RawC ∅ˢ 0
last-or = return (fun (return (fun (recL v₀ (return v₁) (delay ⌜ 1 ⌝ (return v₂))))))

last-box : RawC ∅ˢ 0
last-box =
  return (fun (return (fun
    (recL (v₀ ⦂ᵛ list ([ ⌜ 1 ⌝ʳ ] nat)) (return v₁) (delay ⌜ 1 ⌝ (return v₂))))))

--   latest l = recL l with nil ↦ 0 | cons h t, r ↦ delay 1; unbox h as x in x
--
-- Unboxing the head asks only that the box's grade be reached.

latest : RawC ∅ˢ 0
latest =
  return (fun (recL v₀ (return zero) (delay ⌜ 1 ⌝ (unbox (var (fsuc (fsuc fzero))) (return v₀)))))

latest-ready : RawC ∅ˢ 0
latest-ready =
  return (fun (recL (v₀ ⦂ᵛ list ([ ⌜ 1 ⌝ʳ ] nat)) (return zero)
                    (delay ⌜ 1 ⌝ (unbox (var (fsuc (fsuc fzero))) (return v₀)))))

------------------------------------------------------------------
-- 9. A tick per element
--
--   ticks l = recL l with nil ↦ () | cons h t, r ↦ delay 1; ()
--
-- As `countdown`.

ticks : RawC ∅ˢ 0
ticks = return (fun (recL v₀ (return ⋆) (delay ⌜ 1 ⌝ (return ⋆))))

-- On a list of three, annotated at `k` ticks, and at the top

ticks-on : RawC ∅ˢ 0
ticks-on = recL (cons ⋆ (cons ⋆ (cons ⋆ nil))) (return ⋆) (delay ⌜ 1 ⌝ (return ⋆))

ticks-at : ℕ → RawC ∅ˢ 0
ticks-at k = ticks-on ⦂ᶜ (unit ! ⌜ k ⌝ᵉ)

ticks-top : RawC ∅ˢ 0
ticks-top = ticks-on ⦂ᶜ (unit ! econst ⊤ₑ)

ticks-top-D : ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ unit ! econst ⊤ₑ
ticks-top-D =
  annᶜ (unit ! econst ⊤ₑ)
    (recL (cons ⋆ (cons ⋆ (cons ⋆ nil))) (coerce topₑ (return ⋆))
          (coerce topₑ (delay ⌜ 1 ⌝ (return ⋆))) topₑ)

ticks-top-typable : Typable [] ticks-top
ticks-top-typable = closed ticks-top-D refl

------------------------------------------------------------------
-- 10. A function calling the recursive result twice
--
--   twice n = recℕ n with zero    ↦ box⊤ (λx. delay 1; ())
--                       | succ p, r ↦ box⊤ (λx. unbox r as f in f x;
--                                               unbox r as g in g x)
--   twice-run = unbox (twice 2) as f in f ()
--
-- Boxed at `⊤ᵣ`, so it can be unboxed after the first call; `ε`
-- absorbs the product of the two calls' effects.

twice-base : ∀ {Θ n} → RawC Θ n
twice-base = box (rconst ⊤ᵣ) (fun (delay ⌜ 1 ⌝ (return ⋆))) (return v₀)

twice-step : ∀ {Θ n} → RawC Θ (suc (suc n))
twice-step =
  box (rconst ⊤ᵣ)
      (fun (unbox (var (fsuc fzero)) (v₀ · v₁) ⨟ unbox (var (fsuc (fsuc fzero))) (v₀ · v₂)))
      (return v₀)

twice : RawC ∅ˢ 0
twice = return (fun (recℕ v₀ twice-base twice-step))

twice-run : RawC ∅ˢ 0
twice-run = recℕ (numeral 2) twice-base twice-step ⨟ unbox (var fzero) (v₀ · ⋆)

-- annotated at `k` ticks

twice-run-at : ℕ → RawC ∅ˢ 0
twice-run-at k = twice-run ⦂ᶜ (unit ! ⌜ k ⌝ᵉ)
