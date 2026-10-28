--------------------------------------------------------------------
-- Inference on primitive recursion                               --
--                                                                --
-- Programs exercising `recℕ V M N`: `M` is the base and `N` the  --
-- step, which binds the predecessor and, after a lock at the     --
-- effect, the result of the recursive call. The step is typed    --
-- under a lock at `⊤ᵣ`, as an operation clause is, so only an    --
-- eternal outer variable, such as a `Nat`, is usable in it. The  --
-- effect `ε` absorbs its own iteration, `ε · ε ≾ ε`.             --
--                                                                --
-- `recL V M N` is the same on lists, its step binding the head   --
-- and the tail before the lock at the effect, so a head of       --
-- non-eternal type is usable in it only where `∣ ε ∣ ≾ uᵣ`.      --
--                                                                --
-- The durations are stepped: `⌜ n ⌝` is the duration of `n`      --
-- ticks, and `⌜ n ⌝ʳ` and `⌜ n ⌝ᵉ` its grades.                   --
--                                                                --
-- The instances under `Recursion/` check the verdicts and        --
-- schemes by `refl` at right- and left-sided time.               --
--------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat using (ℕ; suc)

open import Grades.Durations using (Stepped)
open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes
open import OpenCalculus.Inference.SolverImpl.Enum using (OpEnum)

module OpenCalculus.Examples.Recursion (S : LanguageSpec) (opEnum : OpEnum S)
  (st : Stepped (GradeSystem.Dur (LanguageSpec.Grades S))) where

open LanguageSpec S
open GradeSystemInterface Grades using (R; 𝔻; of-durʳ; of-durᵉ; ⊤ᵣ; ⊤ₑ; ≃ᵣ⇒≾ᵣ; map-uᵉ)
open Operations Ops using (Op; op-grade)

open import OpenCalculus.Syntax.Grades          S
open import OpenCalculus.Syntax.Types           S
open import OpenCalculus.Syntax.Contexts        S
open import OpenCalculus.Syntax.Subst           S using (idˢ)
open import OpenCalculus.Hypotheses             S
open import OpenCalculus.Hypotheses.Instances   S using (Satisfiable-∅)
open import OpenCalculus.Typing                 S
open import OpenCalculus.Syntax.Raw             S
open import OpenCalculus.Syntax.Raw.Subst       S using (_[_]ᴿᶜ)
open import OpenCalculus.Typing.Erasure         S using (⌊_⌋ᶜ)
open import OpenCalculus.Inference.Principality S
open import OpenCalculus.Inference.SolverImpl   S opEnum
  using (infer-complete; infer-handlerFree; check-established)

open import OpenCalculus.Inference.SolverImpl S opEnum using (infer; check) public
open import OpenCalculus.Examples.Scheme S public
open import OpenCalculus.Examples.Variables

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

  ok₀ : ∀ {Θ} {Q : Hyps Θ} {A : OVType Θ} → VarOK Q A ûᵣ
  ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

  -- A natural number, usable under any lock

  okℕ : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → VarOK Q Nat ρ
  okℕ = et-ok Natₑ

  -- A unit effect has passed

  u-passed : ∀ {Θ} {Q : Hyps Θ} → Q ⊩ ûᵣ ·̂ᵣ ∣ ûₑ ∣̂ᵉ ≾̂ᵣ ûᵣ
  u-passed = transᵣ (eqᵣ ≡̂ᵣ-identityˡ)
               (transᵣ (eqᵣ ≡̂ᵣ-map-const) (atomᵣ (≃ᵣ⇒≾ᵣ map-uᵉ)))

  -- A pure step iterates purely

  pure : ∀ {Θ} {Q : Hyps Θ} → Q ⊩ ûₑ ·̂ₑ ûₑ ≾̂ₑ ûₑ
  pure = eqₑ ≡̂ₑ-identityˡ

------------------------------------------------------------------
-- 1. Pure recursion: the result of the recursive call
--
--   add m n = recℕ m with zero ↦ n | succ p, r ↦ succ r
--
-- The step uses `r`, bound after the lock at the effect. The
-- effect is the unit, which absorbs itself. Typed at every grade.

add : RawC ∅ˢ 0
add = return (lam (return (lam (recℕ v₁ (return v₀) (return (succ v₀))))))

add-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat ⇒ (Nat ⇒ Nat ‼ ûₑ) ‼ ûₑ) ‼ ûₑ
add-D =
  return (lam (return (lam
    (recℕ (var (Tl-∷ Hd) ok₀) (return (var Hd ok₀)) (return (succ (var Hd ok₀))) pure))))

add-typed : IsTyped (infer [] add)
add-typed = typed-of add (closed add-D refl) _

------------------------------------------------------------------
-- 2. The predecessor, and an outer natural number, in the step
--
--   rebuild n = recℕ n with zero ↦ 0 | succ p, r ↦ succ p
--   mul m n   = recℕ m with zero ↦ 0 | succ p, r ↦ add n r
--
-- The predecessor is bound before the lock at the effect; `n` is
-- bound outside the step, behind the lock at `⊤ᵣ`. Both are `Nat`,
-- which is eternal, so `var` asks for nothing. `add n r` is written
-- out as a second `recℕ`. Typed at every grade.

rebuild : RawC ∅ˢ 0
rebuild = return (lam (recℕ v₀ (return zero) (return (succ v₁))))

rebuild-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat ⇒ Nat ‼ ûₑ) ‼ ûₑ
rebuild-D =
  return (lam
    (recℕ (var Hd ok₀) (return zero) (return (succ (var (Tl-∷ (Tl-⟨⟩ Hd)) okℕ))) pure))

rebuild-typed : IsTyped (infer [] rebuild)
rebuild-typed = typed-of rebuild (closed rebuild-D refl) _

mul : RawC ∅ˢ 0
mul =
  return (lam (return (lam
    (recℕ v₁ (return zero) (recℕ v₂ (return v₀) (return (succ v₀)))))))

mul-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat ⇒ (Nat ⇒ Nat ‼ ûₑ) ‼ ûₑ) ‼ ûₑ
mul-D =
  return (lam (return (lam
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
-- `f` is bound outside the step, behind the lock at `⊤ᵣ`; a
-- function type is never eternal, so `var` asks for `⊤ᵣ ≾ uᵣ`.

each : RawC ∅ˢ 0
each = return (lam (return (lam (recℕ v₀ (return ⋆) (v₃ · ⋆)))))

------------------------------------------------------------------
-- 4. A countdown: a tick per step
--
--   countdown n = recℕ n with zero ↦ () | succ p, r ↦ delay 1; ()
--
-- The effect `ε` of the recursion is at least a tick and absorbs
-- itself: `ε · ε ≾ ε` and `⌜ 1 ⌝ ≾ ε`.

countdown : RawC ∅ˢ 0
countdown = return (lam (recℕ v₀ (return ⋆) (delay ⌜ 1 ⌝ (return ⋆))))

-- On a numeral, annotated at `k` ticks
--
--   countdown-at k = (recℕ 3 with zero ↦ () | succ p, r ↦ delay 1; ()) : Unit ! k

countdown-on : RawC ∅ˢ 0
countdown-on = recℕ (numeral 3) (return ⋆) (delay ⌜ 1 ⌝ (return ⋆))

countdown-at : ℕ → RawC ∅ˢ 0
countdown-at k = countdown-on ⦂ᶜ (Unit ‼ ⌜ k ⌝ᵉ)

-- Two ticks annotated at one, the shape of `wait 2 : unit # 1`

wait-2-at-1 : RawC ∅ˢ 0
wait-2-at-1 = recℕ (numeral 2) (return ⋆) (delay ⌜ 1 ⌝ (return ⋆)) ⦂ᶜ (Unit ‼ ⌜ 1 ⌝ᵉ)

-- annotated at the top

countdown-top : RawC ∅ˢ 0
countdown-top = countdown-on ⦂ᶜ (Unit ‼ econst ⊤ₑ)

-- typable at every grade, the effect at the top

countdown-top-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Unit ‼ econst ⊤ₑ
countdown-top-D =
  annᶜ (Unit ‼ econst ⊤ₑ)
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
-- The clause resumes after the recursion. The recursion's effect is
-- an unknown of the clause, below `op · j` for the clause's rigid
-- `j` only through the product with the resumption's.

rec-then-resume : ∀ {Θ n} → RawC (Θ +e) (suc (suc (suc (suc n)))) → Op
                → RawC (Θ +e) (suc (suc n))
rec-then-resume step op =
  recℕ (numeral 2) (return ⋆) step
  ⨟ perform op v₂ (unbox (fsuc (fsuc fzero)) (v₀ · v₁))

in-clause : (∀ {Θ n} → RawC (Θ +e) (suc (suc (suc (suc n))))) → RawC ∅ˢ 0
in-clause step = handle (return ⋆) `with handler (return ⋆) (rec-then-resume step)

-- a pure step, and a step of a tick

in-clause-pure : RawC ∅ˢ 0
in-clause-pure = in-clause (return ⋆)

in-clause-tick : RawC ∅ˢ 0
in-clause-tick = in-clause (delay ⌜ 1 ⌝ (return ⋆))

-- With a pure step, typable at every grade: the recursion's effect
-- is the unit

in-clause-pure-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Unit ‼ (ûₑ ·̂ₑ ûₑ)
in-clause-pure-D =
  handle (return ⋆)
  `with handler (return ⋆) (λ op →
    coerce (eqₑ ≡̂ₑ-identityˡ)
      (recℕ (numeralᵛ 2) (return ⋆) (return ⋆) pure
       ⨟ perform op (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) (≾ᵘ-ok u-passed))
           (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))))
                  (transᵣ (monoᵣ u-passed ⊩≾̂ᵣ-refl) (eqᵣ ≡̂ᵣ-identityˡ))
                  (<:̂ᵛ-refl _)
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
-- The recursion's effect is the clause's: at least a tick, absorbing
-- itself, and below the clause's bound `op · j` for every `j`.

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
-- `recL` is `recℕ` with the head and the tail in place of the
-- predecessor; `add h r` is written out as a `recℕ` on the head. The
-- effect is the unit. Typed at every grade.

length : RawC ∅ˢ 0
length = return (lam (recL v₀ (return zero) (return (succ v₀))))

length-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (|List| Bool ⇒ Nat ‼ ûₑ) ‼ ûₑ
length-D = return (lam (recL (var Hd ok₀) (return zero) (return (succ (var Hd ok₀))) pure))

length-typed : IsTyped (infer [] length)
length-typed = typed-of length (closed length-D refl) _

sum : RawC ∅ˢ 0
sum = return (lam (recL v₀ (return zero) (recℕ v₂ (return v₀) (return (succ v₀)))))

inc-all : RawC ∅ˢ 0
inc-all = return (lam (recL v₀ (return nil) (return (cons (succ v₂) v₀))))

------------------------------------------------------------------
-- 8. The head in the step
--
--   copy l       = recL l with nil ↦ [] | cons h t, r ↦ cons h r
--   call-all l   = recL l with nil ↦ () | cons h t, r ↦ h ()
--   last-or d l  = recL l with nil ↦ d  | cons h t, r ↦ delay 1; h
--   last-box d l = last-or d (l : List ([1] Nat))
--
-- The head is bound behind the lock at the effect `ε`, so `var` asks
-- for `eternal A ∨ ∣ ε ∣ ≾ uᵣ` at the element type `A`. A pure step
-- leaves `ε` the unit: the head is usable at any type, a function
-- among them (`copy-D`). A step of a tick makes `ε` at least a tick:
-- at the right-sided grades the head's type is then asked to be
-- eternal, and a list of boxes is refused.

copy : RawC ∅ˢ 0
copy = return (lam (recL v₀ (return nil) (return (cons v₂ v₀))))

private

  Fn : ∀ {Θ} → OVType Θ
  Fn = Unit ⇒ Unit ‼ ûₑ

copy-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (|List| Fn ⇒ |List| Fn ‼ ûₑ) ‼ ûₑ
copy-D =
  return (lam
    (recL (var Hd ok₀) (return nil)
          (return (cons (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) (≾ᵘ-ok u-passed)) (var Hd ok₀)))
          pure))

copy-typed : IsTyped (infer [] copy)
copy-typed = typed-of copy (closed copy-D refl) _

call-all : RawC ∅ˢ 0
call-all = return (lam (recL v₀ (return ⋆) (v₂ · ⋆)))

last-or : RawC ∅ˢ 0
last-or = return (lam (return (lam (recL v₀ (return v₁) (delay ⌜ 1 ⌝ (return v₂))))))

last-box : RawC ∅ˢ 0
last-box =
  return (lam (return (lam
    (recL (v₀ ⦂ᵛ |List| ([ ⌜ 1 ⌝ʳ ] Nat)) (return v₁) (delay ⌜ 1 ⌝ (return v₂))))))

-- Unboxing the head instead asks only that the time passed reach the
-- box's grade.
--
--   latest l = recL l with nil ↦ 0 | cons h t, r ↦ delay 1; unbox h as x in x

latest : RawC ∅ˢ 0
latest =
  return (lam (recL v₀ (return zero) (delay ⌜ 1 ⌝ (unbox (fsuc (fsuc fzero)) (return v₀)))))

latest-ready : RawC ∅ˢ 0
latest-ready =
  return (lam (recL (v₀ ⦂ᵛ |List| ([ ⌜ 1 ⌝ʳ ] Nat)) (return zero)
                    (delay ⌜ 1 ⌝ (unbox (fsuc (fsuc fzero)) (return v₀)))))

------------------------------------------------------------------
-- 9. A tick per element
--
--   ticks l = recL l with nil ↦ () | cons h t, r ↦ delay 1; ()
--
-- As for `countdown`: the effect is at least a tick and absorbs
-- itself.

ticks : RawC ∅ˢ 0
ticks = return (lam (recL v₀ (return ⋆) (delay ⌜ 1 ⌝ (return ⋆))))

-- On a list of three, annotated at `k` ticks, and at the top

ticks-on : RawC ∅ˢ 0
ticks-on = recL (cons ⋆ (cons ⋆ (cons ⋆ nil))) (return ⋆) (delay ⌜ 1 ⌝ (return ⋆))

ticks-at : ℕ → RawC ∅ˢ 0
ticks-at k = ticks-on ⦂ᶜ (Unit ‼ ⌜ k ⌝ᵉ)

ticks-top : RawC ∅ˢ 0
ticks-top = ticks-on ⦂ᶜ (Unit ‼ econst ⊤ₑ)

ticks-top-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Unit ‼ econst ⊤ₑ
ticks-top-D =
  annᶜ (Unit ‼ econst ⊤ₑ)
    (recL (cons ⋆ (cons ⋆ (cons ⋆ nil))) (coerce topₑ (return ⋆))
          (coerce topₑ (delay ⌜ 1 ⌝ (return ⋆))) topₑ)

ticks-top-typable : Typable [] ticks-top
ticks-top-typable = closed ticks-top-D refl

------------------------------------------------------------------
-- 10. A recursion building a function that calls the recursive
-- result twice
--
--   twice n = recℕ n with zero    ↦ box⊤ (λx. delay 1; ())
--                       | succ p, r ↦ box⊤ (λx. unbox r as f in f x;
--                                               unbox r as g in g x)
--   twice-run = unbox (twice 2) as f in f ()
--
-- The result is boxed at `⊤ᵣ`, so it is unboxed after the first call's
-- time has passed. Each call has its own effect unknown above the
-- function's latent effect `ε`, and the step's body lies above their
-- product, so `ε` absorbs its own iteration through the two calls.

twice-base : ∀ {Θ n} → RawC Θ n
twice-base = box (rconst ⊤ᵣ) (lam (delay ⌜ 1 ⌝ (return ⋆))) (return v₀)

twice-step : ∀ {Θ n} → RawC Θ (suc (suc n))
twice-step =
  box (rconst ⊤ᵣ)
      (lam (unbox (fsuc fzero) (v₀ · v₁) ⨟ unbox (fsuc (fsuc fzero)) (v₀ · v₂)))
      (return v₀)

twice : RawC ∅ˢ 0
twice = return (lam (recℕ v₀ twice-base twice-step))

twice-run : RawC ∅ˢ 0
twice-run = recℕ (numeral 2) twice-base twice-step ⨟ unbox fzero (v₀ · ⋆)

-- annotated at `k` ticks

twice-run-at : ℕ → RawC ∅ˢ 0
twice-run-at k = twice-run ⦂ᶜ (Unit ‼ ⌜ k ⌝ᵉ)
