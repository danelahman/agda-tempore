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

open import Syntax.Durations using (Stepped)
open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.Examples.Recursion (S : LanguageSpec) (opEnum : OpEnum S)
  (st : Stepped (GradeSystem.Dur (LanguageSpec.Grades S))) where

open LanguageSpec S
open GradeSystemInterface Grades using (R; 𝔻; of-durʳ; of-durᵉ; ⊤ₑ; ≾ᵣ-reflexive; map-uᵉ)
open Operations Ops using (Op; op-grade)

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S
open import TypeInference.OpenSyntax.Subst     S using (idˢ)
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S using (Satisfiable-∅)
open import TypeInference.OpenSyntax.Language  S
open import TypeInference.Raw.Syntax           S
open import TypeInference.Raw.Subst            S using (_[_]ᴿᶜ)
open import TypeInference.Erase                S using (⌊_⌋ᶜ)
open import TypeInference.Principality         S
open import TypeInference.SolverImpl           S opEnum
  using (infer-complete; infer-handlerFree; check-established)

open import TypeInference.SolverImpl S opEnum using (infer; check) public
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
               (transᵣ (eqᵣ ≡̂ᵣ-map-const) (atomᵣ (≾ᵣ-reflexive map-uᵉ)))

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
--   in-clause step = handle () with
--                      op p k ↦ recℕ 2 with zero ↦ () | succ p', r ↦ step;
--                               let a = op p in unbox k as k' in k' a
--                      return x ↦ ()
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
in-clause step = handle (return ⋆) `with rec-then-resume step `in (return ⋆)

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
  `with (λ op →
    coerce (eqₑ ≡̂ₑ-identityˡ)
      (recℕ (numeralᵛ 2) (return ⋆) (return ⋆) pure
       ⨟ perform op (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) (≾ᵘ-ok u-passed))
           (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))))
                  (transᵣ (monoᵣ u-passed ⊩≾̂ᵣ-refl) (eqᵣ ≡̂ᵣ-identityˡ))
                  (<:̂ᵛ-refl _)
                  (var Hd ok₀ · var (Tl-∷ Hd) ok₀))))
  `in (return ⋆)

in-clause-pure-typable : Typable [] in-clause-pure
in-clause-pure-typable = closed in-clause-pure-D refl
