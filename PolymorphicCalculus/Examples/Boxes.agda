------------------------------------------------------------------------
-- Inference on boxes and delays                                      --
--                                                                    --
-- `unbox` asks that the grade elapsed since the box was bound lie    --
-- below the box's grade. At the right-sided grades a box is a lease, --
-- claimable until its grade has elapsed; at the left-sided ones it   --
-- is a promise, claimable once its grade has elapsed. `⌜ n ⌝` is the --
-- duration of `n` ticks.                                             --
--                                                                    --
-- The examples, in nine numbered groups                              --
--   stale-call           a function argument called after a tick     --
--   boxed-call           the same, with the argument boxed first     --
--   handed-box-call      a box from the caller, claimed after a tick --
--   boxing-an-argument   an argument boxed for a tick                --
--   boxing-a-pair-D      a pair boxed under a hypothesis, meeting    --
--                        the variable rule component by component    --
--   claim-after d        a box of three ticks claimed after `d`      --
--   inferred-grade       a box argument whose grade is inferred      --
--   kept-and-claimed     a box argument claimed and handed back      --
--   escaping-after d     a box returned by a function, claimed after --
--                        `d` ticks                                   --
--   branches             claims after different delays in the two    --
--                        branches of an `if`                         --
--   op-licensed op       a claim after an operation, whose time is   --
--                        all that elapsed                            --
--   nested, nesting      a box inside a box, passed in or built in   --
--                        place                                       --
--   claimed-in-clause    a box claimed inside an operation clause    --
--   handed-to-clause     the same, with a box from the caller        --
--   annotated-claim      a box argument annotated with its grade     --
--   relabelled a d       a box of three annotated as a box of `a`,   --
--                        claimed after `d` ticks                     --
--                                                                    --
-- How to read them                                                   --
--   Each program is written above its definition in ordinary syntax, --
--   with what it needs and where it is typable. A box argument that  --
--   is only claimed is reported at the least grade its claims need,  --
--   a constant. A claim refused at constant grades makes inference   --
--   answer `untypable`. The modules under `Boxes/` run inference at  --
--   four grades and check each answer with `refl`:                   --
--     nested-reported :                                              --
--       schemeOf (infer [] nested) ≡ just expected-nested            --
--   A refused claim comes with the verdict `infer [] p ≡ untypable`  --
--   and the proof `¬ Typable [] p` drawn from it.                    --
------------------------------------------------------------------------

open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; suc)

open import Relation.Nullary.Decidable using (True; toWitness)

open import Grades.Durations using (Stepped)
open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Examples.Boxes (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S)
  (st : Stepped (GradeSystem.Dur (LanguageSpec.Grades S))) where

open LanguageSpec S
open GradeSystemInterface Grades
  using (R; 𝔻; ιᵣ; ιₑ; ⊤ᵣ; 𝟏ᵣ; _⊔ᵣ_; _⊔ₑ_; _·ₑ_; ∣_∣ᵉ; _≾ᵣ?_; ≾ᵣ-refl)
  renaming (_≾ᵣ_ to _≾ᴳ_)
open Operations Ops using (Op; param; arity; op-grade)

open import PolymorphicCalculus.Syntax.Grades                S
open import PolymorphicCalculus.Syntax.Types                 S
open import PolymorphicCalculus.Syntax.Contexts              S hiding (Scheme) renaming (_∷_ to _▸_)
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

  -- A claim made after exactly the box's grade

  on-time : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → Q ⊩ 𝟏̂ᵣ ·̂ᵣ ρ ≾̂ᵣ ρ
  on-time = eqᵣ ≡̂ᵣ-identityˡ

  -- A claim, or a use, after a closed grade below the bound

  after : ∀ {Θ} {Q : Hyps Θ} {c c' : R} → c ≾ᴳ c' → Q ⊩ 𝟏̂ᵣ ·̂ᵣ rconst c ≾̂ᵣ rconst c'
  after p = transᵣ on-time (atomᵣ p)

U⇒U : ∀ {Θ} → OVType Θ
U⇒U = unit ⇒ unit ! 𝟏̂ₑ

------------------------------------------------------------------
-- 1. Boxing to survive time
--
--   stale-call f = delay 1; f ()
--
-- A function is not eternal, so `var` asks `⌜ 1 ⌝ʳ ≾ 𝟏ᵣ`: typed at the
-- left-sided grades, refuted at the right-sided ones.

stale-call : RawC ∅ˢ 0
stale-call = return (fun (delay ⌜ 1 ⌝ (v₀ · ⋆)))

stale-call-D : ιᵣ ⌜ 1 ⌝ ≾ᴳ 𝟏ᵣ → ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ (U⇒U ⇒ unit ! (⌜ 1 ⌝ᵉ ·̂ₑ 𝟏̂ₑ)) ! 𝟏̂ₑ
stale-call-D q = return (fun (delay ⌜ 1 ⌝ (var (Tl-⟨⟩ Hd) (≾ᵘ-ok (after q)) · ⋆)))

stale-call-typable : True (ιᵣ ⌜ 1 ⌝ ≾ᵣ? 𝟏ᵣ) → Typable [] stale-call
stale-call-typable q = closed (stale-call-D (toWitness q)) refl

expected-stale-call : Scheme
expected-stale-call =
  ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((unit ⇒ α₀ ! ε₀) ⇒ α₀ ! (⌜ 1 ⌝ᵉ ·̂ₑ ε₀)) ! 𝟏̂ₑ

--   boxed-call f = box[1] f as g in delay 1; unbox g as g' in g' ()
--
-- `box` types `f` under `⟨ ⌜ 1 ⌝ʳ ⟩`: the same condition and verdicts
-- as `stale-call`.

boxed-call : RawC ∅ˢ 0
boxed-call = return (fun (box ⌜ 1 ⌝ʳ v₀ (delay ⌜ 1 ⌝ (unbox (var fzero) (v₀ · ⋆)))))

boxed-call-D : ιᵣ ⌜ 1 ⌝ ≾ᴳ 𝟏ᵣ → ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ (U⇒U ⇒ unit ! (⌜ 1 ⌝ᵉ ·̂ₑ 𝟏̂ₑ)) ! 𝟏̂ₑ
boxed-call-D q =
  return (fun (box ⌜ 1 ⌝ʳ (var (Tl-⟨⟩ Hd) (≾ᵘ-ok (after q)))
    (delay ⌜ 1 ⌝ (unbox (res-var (Tl-⟨⟩ Hd)) on-time (var Hd ok₀ · ⋆)))))

boxed-call-typable : True (ιᵣ ⌜ 1 ⌝ ≾ᵣ? 𝟏ᵣ) → Typable [] boxed-call
boxed-call-typable q = closed (boxed-call-D (toWitness q)) refl

--   handed-box-call b = delay 1; unbox b as g in g ()
--
-- The caller's box is claimed, not used: typed at every grade.

handed-box-call : RawC ∅ˢ 0
handed-box-call = return (fun (delay ⌜ 1 ⌝ (unbox (var fzero) (v₀ · ⋆))))

handed-box-call-typed : IsTyped (infer [] handed-box-call)
handed-box-call-typed =
  typed-of handed-box-call
    (closed {C = ([ ⌜ 1 ⌝ʳ ] U⇒U ⇒ unit ! (⌜ 1 ⌝ᵉ ·̂ₑ 𝟏̂ₑ)) ! 𝟏̂ₑ}
      (return (fun (delay ⌜ 1 ⌝ (unbox (res-var (Tl-⟨⟩ Hd)) on-time (var Hd ok₀ · ⋆)))))
      refl) _

expected-handed-box-call : Scheme
expected-handed-box-call =
  ∀[ 1 , 0 , 1 ] ⊤ ⟹
    ([ ⌜ 1 ⌝ʳ ] (unit ⇒ α₀ ! ε₀) ⇒ α₀ ! (⌜ 1 ⌝ᵉ ·̂ₑ ε₀)) ! 𝟏̂ₑ

--   boxing-an-argument x = box[1] x as b in b
--
-- `eternal α ∨ ⌜ 1 ⌝ʳ ≾ 𝟏ᵣ` is decided on its grade: dropped at the
-- left-sided grades, `eternal α` at the right-sided ones.

boxing-an-argument : RawC ∅ˢ 0
boxing-an-argument = return (fun (box ⌜ 1 ⌝ʳ v₀ (return v₀)))

boxing-an-argument-typed : IsTyped (infer [] boxing-an-argument)
boxing-an-argument-typed =
  typed-of boxing-an-argument
    (closed {C = (unit ⇒ [ ⌜ 1 ⌝ʳ ] unit ! 𝟏̂ₑ) ! 𝟏̂ₑ}
      (return (fun (box ⌜ 1 ⌝ʳ (var (Tl-⟨⟩ Hd) (et-ok unitₑ)) (return (var Hd ok₀)))))
      refl) _

expected-boxing-an-eternal : Scheme
expected-boxing-an-eternal =
  ∀[ 1 , 0 , 0 ] eternal α₀ ⟹ (α₀ ⇒ [ ⌜ 1 ⌝ʳ ] α₀ ! 𝟏̂ₑ) ! 𝟏̂ₑ

expected-boxing-anything : Scheme
expected-boxing-anything =
  ∀[ 1 , 0 , 0 ] ⊤ ⟹ (α₀ ⇒ [ ⌜ 1 ⌝ʳ ] α₀ ! 𝟏̂ₑ) ! 𝟏̂ₑ

--   boxing-a-pair p = box[ρ₀] p as b in b
--
-- Under `eternal α₀ ∨ ρ₀ ≾𝟏̂ᵣ`, the pair `α₀ |×| α₀` meets the
-- variable rule only component by component (`_|×|-ok_`).

boxing-a-pair-D : hypsOf {scope 1 1 0} (eternal α₀ ∨ ρ₀ ≾𝟏̂ᵣ)
                  ∣ [] ⊢ᶜ⦂ (α₀ |×| α₀ ⇒ [ ρ₀ ] (α₀ |×| α₀) ! 𝟏̂ₑ) ! 𝟏̂ₑ
boxing-a-pair-D =
  return (fun (box ρ₀ (var (Tl-⟨⟩ Hd) (hyp-ok (here refl) on-time |×|-ok hyp-ok (here refl) on-time))
                      (return (var Hd ok₀))))

------------------------------------------------------------------
-- 2. Claiming early, on time, late
--
--   claim-after d = box[3] () as x in delay d; unbox x as y in y
--
-- `⌜ d ⌝ʳ ≾ ⌜ 3 ⌝ʳ`: on time (`d = 3`) typed everywhere; a lease refuses
-- `d = 4`, a promise `d = 2`.

claim-after : ℕ → RawC ∅ˢ 0
claim-after d = box ⌜ 3 ⌝ʳ ⋆ (delay ⌜ d ⌝ (unbox (var fzero) (return v₀)))

claim-after-D : ∀ d → ιᵣ ⌜ d ⌝ ≾ᴳ ιᵣ ⌜ 3 ⌝ → ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ unit ! (⌜ d ⌝ᵉ ·̂ₑ 𝟏̂ₑ)
claim-after-D d p =
  box ⌜ 3 ⌝ʳ ⋆ (delay ⌜ d ⌝ (unbox (res-var (Tl-⟨⟩ Hd)) (after p) (return (var Hd ok₀))))

claim-after-typable : ∀ d → True (ιᵣ ⌜ d ⌝ ≾ᵣ? ιᵣ ⌜ 3 ⌝) → Typable [] (claim-after d)
claim-after-typable d p = closed (claim-after-D d (toWitness p)) refl

claim-on-time-typed : IsTyped (infer [] (claim-after 3))
claim-on-time-typed = typed-of (claim-after 3) (closed (claim-after-D 3 ≾ᵣ-refl) refl) _

expected-claim-after : ℕ → Scheme
expected-claim-after d = ∀[ 0 , 0 , 0 ] ⊤ ⟹ unit ! ⌜ d ⌝ᵉ

------------------------------------------------------------------
-- 3. An inferred box grade
--
--   inferred-grade b = delay 2; unbox b as y in y
--
-- The least grade with `⌜ 2 ⌝ʳ ≾ ρ` is principal: `[ ⌜ 2 ⌝ʳ ] α₀`, no
-- grade variable.

inferred-grade : RawC ∅ˢ 0
inferred-grade = return (fun (delay ⌜ 2 ⌝ (unbox (var fzero) (return v₀))))

inferred-grade-typed : IsTyped (infer [] inferred-grade)
inferred-grade-typed =
  typed-of inferred-grade
    (closed {C = ([ ⌜ 2 ⌝ʳ ] unit ⇒ unit ! (⌜ 2 ⌝ᵉ ·̂ₑ 𝟏̂ₑ)) ! 𝟏̂ₑ}
      (return (fun (delay ⌜ 2 ⌝ (unbox (res-var (Tl-⟨⟩ Hd)) on-time (return (var Hd ok₀))))))
      refl) _

expected-inferred-grade : Scheme
expected-inferred-grade =
  ∀[ 1 , 0 , 0 ] ⊤ ⟹ ([ ⌜ 2 ⌝ʳ ] α₀ ⇒ α₀ ! ⌜ 2 ⌝ᵉ) ! 𝟏̂ₑ

--   kept-and-claimed b = (b , λ _. delay 2; unbox b as y in y)
--
-- The grade also flows out, so it is quantified: a box at
-- `⌜ 2 ⌝ʳ ⊔̂ᵣ ρ₀`, handed back at `ρ₀`.

kept-and-claimed : RawC ∅ˢ 0
kept-and-claimed =
  return (fun (return ⦉ v₀ , fun (delay ⌜ 2 ⌝ (unbox (var (fsuc fzero)) (return v₀))) ⦊))

kept-and-claimed-typed : IsTyped (infer [] kept-and-claimed)
kept-and-claimed-typed =
  typed-of kept-and-claimed
    (closed {C = ([ ⌜ 2 ⌝ʳ ] unit
                   ⇒ ([ ⌜ 2 ⌝ʳ ] unit |×| (unit ⇒ unit ! (⌜ 2 ⌝ᵉ ·̂ₑ 𝟏̂ₑ))) ! 𝟏̂ₑ) ! 𝟏̂ₑ}
      (return (fun (return ⦉ var Hd ok₀
                           , fun (delay ⌜ 2 ⌝ (unbox (res-var (Tl-⟨⟩ (Tl-∷ Hd))) on-time
                                            (return (var Hd ok₀)))) ⦊)))
      refl) _

expected-kept-and-claimed : Scheme
expected-kept-and-claimed =
  ∀[ 2 , 1 , 0 ] ⊤ ⟹
    ([ ⌜ 2 ⌝ʳ ⊔̂ᵣ ρ₀ ] α₀ ⇒ ([ ρ₀ ] α₀ |×| (α₁ ⇒ α₀ ! ⌜ 2 ⌝ᵉ)) ! 𝟏̂ₑ) ! 𝟏̂ₑ

------------------------------------------------------------------
-- 4. A box escaping through `return`
--
--   escaping-after d =
--     let mk () = box[2] () as x in x in
--     let r = mk () in delay d; unbox r as y in y
--
-- `⌜ d ⌝ʳ ≾ ⌜ 2 ⌝ʳ`, reached only through `mk`'s result type, so a
-- refused claim is refuted by a chain of orderings between constants:
-- typed at `d = 2`; refused late (`d = 4`) or early (`d = 1`).

escaping-after : ℕ → RawC ∅ˢ 0
escaping-after d =
  return (fun (box ⌜ 2 ⌝ʳ ⋆ (return v₀)))
  ⨟ ((v₀ · ⋆) ⨟ delay ⌜ d ⌝ (unbox (var fzero) (return v₀)))

escaping-after-D : ∀ d → ιᵣ ⌜ d ⌝ ≾ᴳ ιᵣ ⌜ 2 ⌝
                 → ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ unit ! (𝟏̂ₑ ·̂ₑ (𝟏̂ₑ ·̂ₑ (⌜ d ⌝ᵉ ·̂ₑ 𝟏̂ₑ)))
escaping-after-D d p =
  return (fun {A = unit} (box ⌜ 2 ⌝ʳ ⋆ (return (var Hd ok₀))))
  ⨟ ((var Hd ok₀ · ⋆)
     ⨟ delay ⌜ d ⌝ (unbox (res-var (Tl-⟨⟩ Hd)) (after p) (return (var Hd ok₀))))

escaping-after-typable : ∀ d → True (ιᵣ ⌜ d ⌝ ≾ᵣ? ιᵣ ⌜ 2 ⌝) → Typable [] (escaping-after d)
escaping-after-typable d p = closed (escaping-after-D d (toWitness p)) refl

escaping-typed : IsTyped (infer [] (escaping-after 2))
escaping-typed = typed-of (escaping-after 2) (closed (escaping-after-D 2 ≾ᵣ-refl) refl) _

expected-escaping : ℕ → Scheme
expected-escaping d = ∀[ 0 , 0 , 0 ] ⊤ ⟹ unit ! ⌜ d ⌝ᵉ

------------------------------------------------------------------
-- 5. Claiming in both branches, after different delays
--
--   branches c b = if c then (delay 1; unbox b as y in y)
--                       else (delay 3; unbox b as y in y)
--
-- The box's grade and the effect are the join `⌜ 1 ⌝ ⊔ ⌜ 3 ⌝`: three
-- ticks at the right-sided grades, one at the left-sided ones.

branches : RawC ∅ˢ 0
branches =
  return (fun (return (fun
    (if v₁ `then delay ⌜ 1 ⌝ (unbox (var fzero) (return v₀))
           `else delay ⌜ 3 ⌝ (unbox (var fzero) (return v₀))))))

branches-typed : IsTyped (infer [] branches)
branches-typed =
  typed-of branches
    (closed {C = (bool ⇒ ([ ⌜ 1 ⌝ʳ ⊔̂ᵣ ⌜ 3 ⌝ʳ ] unit ⇒ unit ! (⌜ 1 ⌝ᵉ ⊔̂ₑ ⌜ 3 ⌝ᵉ)) ! 𝟏̂ₑ) ! 𝟏̂ₑ}
      (return (fun (return (fun
        (if var (Tl-∷ Hd) ok₀
          `then coerce (transₑ (eqₑ ≡̂ₑ-identityʳ) ⊔-ubˡₑ)
                  (delay ⌜ 1 ⌝ (unbox (res-var (Tl-⟨⟩ Hd)) (transᵣ on-time ⊔-ubˡᵣ)
                              (return (var Hd ok₀))))
          `else coerce (transₑ (eqₑ ≡̂ₑ-identityʳ) ⊔-ubʳₑ)
                  (delay ⌜ 3 ⌝ (unbox (res-var (Tl-⟨⟩ Hd)) (transᵣ on-time ⊔-ubʳᵣ)
                              (return (var Hd ok₀)))))))))
      refl) _

expected-branches : Scheme
expected-branches =
  ∀[ 1 , 0 , 0 ] ⊤ ⟹
    (bool ⇒ ([ rconst (ιᵣ ⌜ 1 ⌝ ⊔ᵣ ιᵣ ⌜ 3 ⌝) ] α₀
               ⇒ α₀ ! econst (ιₑ ⌜ 1 ⌝ ⊔ₑ ιₑ ⌜ 3 ⌝)) ! 𝟏̂ₑ) ! 𝟏̂ₑ

------------------------------------------------------------------
-- 6. An operation's time licensing a claim
--
--   op-licensed op p = box[2] () as x in op p; unbox x as y in y
--
-- `op-grade op ≾ ⌜ 2 ⌝ʳ`: the operation's time is all that elapsed.

op-licensed : Op → RawC ∅ˢ 0
op-licensed op =
  return (fun (box ⌜ 2 ⌝ʳ ⋆ (perform op v₁ (unbox (var (fsuc fzero)) (return v₀)))))

op-licensed-D : (op : Op) → ∣ op-grade op ∣ᵉ ≾ᴳ ιᵣ ⌜ 2 ⌝
              → ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ (⌜ param op ⌝ᵍ ⇒ unit ! (econst (op-grade op) ·̂ₑ 𝟏̂ₑ)) ! 𝟏̂ₑ
op-licensed-D op p =
  return (fun (box ⌜ 2 ⌝ʳ ⋆
    (perform op (var (Tl-∷ Hd) ok₀)
      (unbox (res-var (Tl-∷ (Tl-⟨⟩ Hd))) (after p) (return (var Hd ok₀))))))

op-licensed-typable : (op : Op) → True (∣ op-grade op ∣ᵉ ≾ᵣ? ιᵣ ⌜ 2 ⌝)
                    → Typable [] (op-licensed op)
op-licensed-typable op p = closed (op-licensed-D op (toWitness p)) refl

expected-op-licensed : Op → Scheme
expected-op-licensed op =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹ (⌜ param op ⌝ᵍ ⇒ unit ! econst (op-grade op)) ! 𝟏̂ₑ

------------------------------------------------------------------
-- 7. Nested boxes
--
--   nested b = delay 1; unbox b as c in delay 2; unbox c as z in z
--
-- Each claim counts from its own binding; typed at every grade.

nested : RawC ∅ˢ 0
nested = return (fun (delay ⌜ 1 ⌝ (unbox (var fzero) (delay ⌜ 2 ⌝ (unbox (var fzero) (return v₀))))))

nested-typed : IsTyped (infer [] nested)
nested-typed =
  typed-of nested
    (closed {C = ([ ⌜ 1 ⌝ʳ ] ([ ⌜ 2 ⌝ʳ ] unit) ⇒ unit ! (⌜ 1 ⌝ᵉ ·̂ₑ (⌜ 2 ⌝ᵉ ·̂ₑ 𝟏̂ₑ))) ! 𝟏̂ₑ}
      (return (fun (delay ⌜ 1 ⌝ (unbox (res-var (Tl-⟨⟩ Hd)) on-time
        (delay ⌜ 2 ⌝ (unbox (res-var (Tl-⟨⟩ Hd)) on-time (return (var Hd ok₀))))))))
      refl) _

expected-nested : Scheme
expected-nested =
  ∀[ 1 , 0 , 0 ] ⊤ ⟹
    ([ ⌜ 1 ⌝ʳ ] ([ ⌜ 2 ⌝ʳ ] α₀) ⇒ α₀ ! econst (ιₑ ⌜ 1 ⌝ ·ₑ ιₑ ⌜ 2 ⌝)) ! 𝟏̂ₑ

--   nesting = box[2] () as x in box[1] x as y in
--             delay 1; unbox y as x' in delay 2; unbox x' as z in z
--
-- A box is not eternal, so boxing `x` asks `⌜ 1 ⌝ʳ ≾ 𝟏ᵣ`, as `stale-call`.

nesting : RawC ∅ˢ 0
nesting =
  box ⌜ 2 ⌝ʳ ⋆ (box ⌜ 1 ⌝ʳ v₀
    (delay ⌜ 1 ⌝ (unbox (var fzero) (delay ⌜ 2 ⌝ (unbox (var fzero) (return v₀))))))

nesting-D : ιᵣ ⌜ 1 ⌝ ≾ᴳ 𝟏ᵣ → ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ unit ! (⌜ 1 ⌝ᵉ ·̂ₑ (⌜ 2 ⌝ᵉ ·̂ₑ 𝟏̂ₑ))
nesting-D q =
  box ⌜ 2 ⌝ʳ ⋆ (box ⌜ 1 ⌝ʳ (var (Tl-⟨⟩ Hd) (≾ᵘ-ok (after q)))
    (delay ⌜ 1 ⌝ (unbox (res-var (Tl-⟨⟩ Hd)) on-time
      (delay ⌜ 2 ⌝ (unbox (res-var (Tl-⟨⟩ Hd)) on-time (return (var Hd ok₀)))))))

nesting-typable : True (ιᵣ ⌜ 1 ⌝ ≾ᵣ? 𝟏ᵣ) → Typable [] nesting
nesting-typable q = closed (nesting-D (toWitness q)) refl

expected-nesting : Scheme
expected-nesting = ∀[ 0 , 0 , 0 ] ⊤ ⟹ unit ! econst (ιₑ ⌜ 1 ⌝ ·ₑ ιₑ ⌜ 2 ⌝)

------------------------------------------------------------------
-- 8. A box claimed inside an operation clause
--
--   claimed-in-clause ρ m = box[ρ] () as x in
--     handle m () with handler {op p k ↦ unbox x as y in
--                               let a = op p in unbox k as k' in k' a}
--
-- A clause sees the context behind `⟨ ⊤ᵣ ⟩`, so `⊤ᵣ ≾ ρ`: typed at
-- `ρ = ⊤ᵣ`, at `ρ = 𝟏ᵣ` where the unit is the top, at `⌜ 1 ⌝ʳ` nowhere.

clause-claim : ∀ {Θ n} → Op → RawC (Θ +e) (suc (suc (suc n)))
clause-claim op =
  unbox (var (fsuc (fsuc fzero)))
    (perform op v₂ (unbox (var (fsuc (fsuc fzero))) (v₀ · v₁)))

claimed-in-clause : RExp ∅ˢ → RawC ∅ˢ 0
claimed-in-clause ρ =
  return (fun (box ρ ⋆ (handle (v₁ · ⋆) `with handler (return ⋆) (clause-claim {∅ˢ}))))

private

  clause-claim-D : ∀ {c} → ⊤ᵣ ≾ᴳ c → (op : Op)
                 → ∅ᴴ ∣ wkᵉ-ctx {∅ˢ} ([] ▸ U⇒U ▸ [ rconst c ] unit) ⟨ rconst ⊤ᵣ ⟩
                          ▸ ⌜ param op ⌝ᵍ
                          ▸ [ rconst ∣ op-grade op ∣ᵉ ]
                              (⌜ arity op ⌝ᵍ ⇒ unit ! evar (newᵉ {∅ˢ}))
                   ⊢ᶜ⦂ unit ! (econst (op-grade op) ·̂ₑ evar (newᵉ {∅ˢ}))
  clause-claim-D p op =
    unbox (res-var (Tl-∷ (Tl-∷ (Tl-⟨⟩ Hd)))) (after p)
      (perform op (var (Tl-∷ (Tl-∷ Hd)) ok₀)
        (unbox (res-var (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))) on-time
          (var Hd ok₀ · var (Tl-∷ Hd) ok₀)))

claimed-in-clause-D : ∀ {c} → ⊤ᵣ ≾ᴳ c
                    → ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ (U⇒U ⇒ unit ! (𝟏̂ₑ ·̂ₑ 𝟏̂ₑ)) ! 𝟏̂ₑ
claimed-in-clause-D {c} p =
  return (fun (box (rconst c) ⋆
    (handle var (Tl-∷ Hd) ok₀ · ⋆ `with handler (return ⋆) (clause-claim-D p))))

claimed-in-clause-typable : ∀ c → True (⊤ᵣ ≾ᵣ? c) → Typable [] (claimed-in-clause (rconst c))
claimed-in-clause-typable c p = closed (claimed-in-clause-D (toWitness p)) refl

claimed-at-⊤-typable : Typable [] (claimed-in-clause (rconst ⊤ᵣ))
claimed-at-⊤-typable = closed (claimed-in-clause-D {⊤ᵣ} ≾ᵣ-refl) refl

expected-claimed-in-clause : Scheme
expected-claimed-in-clause =
  ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((unit ⇒ α₀ ! ε₀) ⇒ unit ! ε₀) ! 𝟏̂ₑ

--   handed-to-clause m b = handle m () with handler {op p k ↦ unbox b as y in …}
--
-- The caller's box is inferred at `⊤ᵣ`.

handed-to-clause : RawC ∅ˢ 0
handed-to-clause =
  return (fun (return (fun (handle (v₁ · ⋆) `with handler (return ⋆) (clause-claim {∅ˢ})))))

handed-to-clause-typable : Typable [] handed-to-clause
handed-to-clause-typable =
  closed {C = (U⇒U ⇒ ([ rconst ⊤ᵣ ] unit ⇒ unit ! (𝟏̂ₑ ·̂ₑ 𝟏̂ₑ)) ! 𝟏̂ₑ) ! 𝟏̂ₑ}
    (return (fun (return (fun
      (handle var (Tl-∷ Hd) ok₀ · ⋆ `with handler (return ⋆) (clause-claim-D ≾ᵣ-refl))))))
    refl

expected-handed-to-clause : Scheme
expected-handed-to-clause =
  ∀[ 2 , 0 , 1 ] ⊤ ⟹
    ((unit ⇒ α₁ ! ε₀) ⇒ ([ rconst ⊤ᵣ ] α₀ ⇒ unit ! ε₀) ! 𝟏̂ₑ) ! 𝟏̂ₑ

------------------------------------------------------------------
-- 9. Claiming an annotated box
--
--   annotated-claim b = delay 2; unbox (b : [2] ()) as y in y
--
-- The claim is weighed against the annotation's grade, which is the
-- argument's principal grade; typed at every grade.

annotated-claim : RawC ∅ˢ 0
annotated-claim =
  return (fun (delay ⌜ 2 ⌝ (unbox (var fzero ⦂ᵛ [ ⌜ 2 ⌝ʳ ] unit) (return v₀))))

annotated-claim-typed : IsTyped (infer [] annotated-claim)
annotated-claim-typed =
  typed-of annotated-claim
    (closed {C = ([ ⌜ 2 ⌝ʳ ] unit ⇒ unit ! (⌜ 2 ⌝ᵉ ·̂ₑ 𝟏̂ₑ)) ! 𝟏̂ₑ}
      (return (fun (delay ⌜ 2 ⌝
        (unbox (res-ann ⌜ 2 ⌝ʳ unit (res-var (Tl-⟨⟩ Hd)) ⊩≾̂ᵣ-refl unitₛ) on-time
               (return (var Hd ok₀))))))
      refl) _

expected-annotated-claim : Scheme
expected-annotated-claim =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹ ([ ⌜ 2 ⌝ʳ ] unit ⇒ unit ! ⌜ 2 ⌝ᵉ) ! 𝟏̂ₑ

--   relabelled a d = box[3] () as x in delay d; unbox (x : [a] ()) as y in y
--
-- Needs `⌜ a ⌝ʳ ≾ ⌜ 3 ⌝ʳ` and `⌜ d ⌝ʳ ≾ ⌜ a ⌝ʳ`: a lease of three narrows
-- to two, a promise of three to four.

relabelled : ℕ → ℕ → RawC ∅ˢ 0
relabelled a d =
  box ⌜ 3 ⌝ʳ ⋆ (delay ⌜ d ⌝ (unbox (var fzero ⦂ᵛ [ ⌜ a ⌝ʳ ] unit) (return v₀)))

relabelled-D : ∀ a d → ιᵣ ⌜ a ⌝ ≾ᴳ ιᵣ ⌜ 3 ⌝ → ιᵣ ⌜ d ⌝ ≾ᴳ ιᵣ ⌜ a ⌝
             → ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ unit ! (⌜ d ⌝ᵉ ·̂ₑ 𝟏̂ₑ)
relabelled-D a d q p =
  box ⌜ 3 ⌝ʳ ⋆ (delay ⌜ d ⌝
    (unbox (res-ann ⌜ a ⌝ʳ unit (res-var (Tl-⟨⟩ Hd)) (atomᵣ q) unitₛ) (after p)
           (return (var Hd ok₀))))

relabelled-typable : ∀ a d → True (ιᵣ ⌜ a ⌝ ≾ᵣ? ιᵣ ⌜ 3 ⌝)
                   → True (ιᵣ ⌜ d ⌝ ≾ᵣ? ιᵣ ⌜ a ⌝) → Typable [] (relabelled a d)
relabelled-typable a d q p = closed (relabelled-D a d (toWitness q) (toWitness p)) refl

expected-relabelled : ℕ → Scheme
expected-relabelled d = ∀[ 0 , 0 , 0 ] ⊤ ⟹ unit ! ⌜ d ⌝ᵉ
