--------------------------------------------------------------------
-- Inference on boxes and delays                                  --
--                                                                --
-- Programs exercising `box`, `unbox` and `delay`. None has an    --
-- annotation. `box ρ V as x in N` types `V` under the lock       --
-- `⟨ ρ ⟩`, and `unbox x as y in N` asks that the grade elapsed   --
-- since `x` was bound be below the box's grade: at the           --
-- right-sided grades the box is a lease, claimable up to `ρ`; at --
-- the left-sided ones a promise, claimable from `ρ` on.          --
--                                                                --
-- `⌜ n ⌝ʳ` and `⌜ n ⌝ᵉ` are the grades of `n` ticks. A box       --
-- type is contravariant in its grade, so a box argument that is  --
-- only claimed is reported at the least grade the claims need,   --
-- a constant; a grade variable appears only where the box also   --
-- flows out (`kept-and-claimed`).                                --
--                                                                --
-- A `typed` verdict is a principal scheme, and the term is       --
-- typable exactly when the scheme's conditions are satisfiable.  --
-- An `unbox` refused at a box of a constant grade is             --
-- `untypable`: the unbox's grade unknown lies between the        --
-- elapsed grade and the box's, and the ordering this entails     --
-- between the two is decided false (`closedᴴ`).                  --
--                                                                --
-- The instances under `Boxes/` check the verdicts and schemes by --
-- `refl` at the four example grades.                             --
--------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat using (ℕ; suc)

open import Relation.Nullary.Decidable using (True; toWitness)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.Examples.Boxes (S : LanguageSpec) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades
  using (R; of-natʳ; of-natᵉ; ⊤ᵣ; uᵣ; _⊔ᵣ_; _⊔ₑ_; _·ₑ_; mapᵉ; _≾ᵣ?_; ≾ᵣ-refl)
  renaming (_≾ᵣ_ to _≾ᴳ_)
open Operations Ops using (Op; param; arity; op-grade)

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S renaming (_∷_ to _▸_)
open import TypeInference.OpenSyntax.Subst     S using (idˢ)
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S using (Satisfiable-∅)
open import TypeInference.OpenSyntax.Language  S
open import TypeInference.Raw.Syntax           S
open import TypeInference.Raw.Subst            S using (_[_]ᴿᶜ)
open import TypeInference.Erase                S using (⌊_⌋ᶜ)
open import TypeInference.Principality         S
open import TypeInference.SolverImpl           S opEnum
  using (infer-complete; infer-handlerFree)

open import TypeInference.SolverImpl S opEnum using (infer) public
open import TypeInference.Examples.Scheme S public
open import TypeInference.Examples.Variables

------------------------------------------------------------------
-- Grades of `n` ticks

⌜_⌝ʳ : ∀ {Θ} → ℕ → RExp Θ
⌜ n ⌝ʳ = rconst (of-natʳ n)

⌜_⌝ᵉ : ∀ {Θ} → ℕ → EExp Θ
⌜ n ⌝ᵉ = econst (of-natᵉ n)

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

  -- A claim made after exactly the box's grade

  on-time : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → Q ⊩ ûᵣ ·̂ᵣ ρ ≾̂ᵣ ρ
  on-time = eqᵣ ≡̂ᵣ-identityˡ

  -- A claim, or a use, after a closed grade below the bound

  after : ∀ {Θ} {Q : Hyps Θ} {c c' : R} → c ≾ᴳ c' → Q ⊩ ûᵣ ·̂ᵣ rconst c ≾̂ᵣ rconst c'
  after p = transᵣ on-time (atomᵣ p)

U⇒U : ∀ {Θ} → OVType Θ
U⇒U = Unit ⇒ Unit ‼ ûₑ

------------------------------------------------------------------
-- 1. Boxing to survive time
--
-- Calling a function argument after a tick:
--
--   stale-call f = delay 1; f ()
--
-- `f` is used under the lock `⟨ ⌜ 1 ⌝ʳ ⟩` and its type, a function
-- type, is never eternal, so `var` asks for `⌜ 1 ⌝ʳ ≾ uᵣ`. It holds
-- where the unit is the top (the left-sided grades) and fails where
-- the unit is least (the right-sided ones).

stale-call : RawC ∅ˢ 0
stale-call = return (lam (delay 1 (v₀ · ⋆)))

stale-call-D : of-natʳ 1 ≾ᴳ uᵣ → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (U⇒U ⇒ Unit ‼ (⌜ 1 ⌝ᵉ ·̂ₑ ûₑ)) ‼ ûₑ
stale-call-D q = return (lam (delay 1 (var (Tl-⟨⟩ Hd) (≾ᵘ-ok (after q)) · ⋆)))

stale-call-typable : True (of-natʳ 1 ≾ᵣ? uᵣ) → Typable [] stale-call
stale-call-typable q = closed (stale-call-D (toWitness q)) refl

expected-stale-call : Scheme
expected-stale-call =
  ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((Unit ⇒ α₀ ‼ ε₀) ⇒ α₀ ‼ (⌜ 1 ⌝ᵉ ·̂ₑ ε₀)) ‼ ûₑ

-- Boxing `f` first does not help:
--
--   boxed-call f = box[1] f as g in delay 1; unbox g as g' in g' ()
--
-- `box` types its payload under the lock `⟨ ⌜ 1 ⌝ʳ ⟩`, so `f` meets
-- the same `var` condition there. The claim itself is on time at
-- every grade. The verdicts are those of `stale-call`, and so is the
-- scheme where it is typed.

boxed-call : RawC ∅ˢ 0
boxed-call = return (lam (box ⌜ 1 ⌝ʳ v₀ (delay 1 (unbox fzero (v₀ · ⋆)))))

boxed-call-D : of-natʳ 1 ≾ᴳ uᵣ → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (U⇒U ⇒ Unit ‼ (⌜ 1 ⌝ᵉ ·̂ₑ ûₑ)) ‼ ûₑ
boxed-call-D q =
  return (lam (box ⌜ 1 ⌝ʳ (var (Tl-⟨⟩ Hd) (≾ᵘ-ok (after q)))
    (delay 1 (unbox (Tl-⟨⟩ Hd) on-time (<:̂ᵛ-refl _) (var Hd ok₀ · ⋆)))))

boxed-call-typable : True (of-natʳ 1 ≾ᵣ? uᵣ) → Typable [] boxed-call
boxed-call-typable q = closed (boxed-call-D (toWitness q)) refl

-- What survives the tick is a box the caller made: the argument is
-- claimed, not used, so `var` asks for nothing, and it is typed at
-- every grade.
--
--   handed-box-call b = delay 1; unbox b as g in g ()

handed-box-call : RawC ∅ˢ 0
handed-box-call = return (lam (delay 1 (unbox fzero (v₀ · ⋆))))

handed-box-call-typed : IsTyped (infer [] handed-box-call)
handed-box-call-typed =
  typed-of handed-box-call
    (closed {C = ([ ⌜ 1 ⌝ʳ ] U⇒U ⇒ Unit ‼ (⌜ 1 ⌝ᵉ ·̂ₑ ûₑ)) ‼ ûₑ}
      (return (lam (delay 1 (unbox (Tl-⟨⟩ Hd) on-time (<:̂ᵛ-refl _) (var Hd ok₀ · ⋆)))))
      refl) _

expected-handed-box-call : Scheme
expected-handed-box-call =
  ∀[ 1 , 0 , 1 ] ⊤ ⟹
    ([ ⌜ 1 ⌝ʳ ] (Unit ⇒ α₀ ‼ ε₀) ⇒ α₀ ‼ (⌜ 1 ⌝ᵉ ·̂ₑ ε₀)) ‼ ûₑ

-- Boxing an argument of unknown type: the payload is used under
-- `⟨ ⌜ 1 ⌝ʳ ⟩`, and the var-rule disjunction `eternal α ∨ ⌜ 1 ⌝ʳ ≾ uᵣ`
-- is decided on its grade: dropped at the left-sided grades, left as
-- `eternal α` at the right-sided ones.
--
--   boxing-an-argument x = box[1] x as b in b

boxing-an-argument : RawC ∅ˢ 0
boxing-an-argument = return (lam (box ⌜ 1 ⌝ʳ v₀ (return v₀)))

boxing-an-argument-typed : IsTyped (infer [] boxing-an-argument)
boxing-an-argument-typed =
  typed-of boxing-an-argument
    (closed {C = (Unit ⇒ [ ⌜ 1 ⌝ʳ ] Unit ‼ ûₑ) ‼ ûₑ}
      (return (lam (box ⌜ 1 ⌝ʳ (var (Tl-⟨⟩ Hd) (et-ok Unitₑ)) (return (var Hd ok₀)))))
      refl) _

expected-boxing-an-eternal : Scheme
expected-boxing-an-eternal =
  ∀[ 1 , 0 , 0 ] eternal α₀ ⟹ (α₀ ⇒ [ ⌜ 1 ⌝ʳ ] α₀ ‼ ûₑ) ‼ ûₑ

expected-boxing-anything : Scheme
expected-boxing-anything =
  ∀[ 1 , 0 , 0 ] ⊤ ⟹ (α₀ ⇒ [ ⌜ 1 ⌝ʳ ] α₀ ‼ ûₑ) ‼ ûₑ

------------------------------------------------------------------
-- 2. Claiming early, on time, late
--
--   claim-after d = box[3] () as x in delay d; unbox x as y in y
--
-- The premise is `⌜ d ⌝ʳ ≾ ⌜ 3 ⌝ʳ`. On time (`d = 3`) it holds at
-- every grade. A lease refuses a late claim (`d = 4`), a promise an
-- early one (`d = 2`).

claim-after : ℕ → RawC ∅ˢ 0
claim-after d = box ⌜ 3 ⌝ʳ ⋆ (delay d (unbox fzero (return v₀)))

claim-after-D : ∀ d → of-natʳ d ≾ᴳ of-natʳ 3 → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Unit ‼ (⌜ d ⌝ᵉ ·̂ₑ ûₑ)
claim-after-D d p =
  box ⌜ 3 ⌝ʳ ⋆ (delay d (unbox (Tl-⟨⟩ Hd) (after p) (<:̂ᵛ-refl _) (return (var Hd ok₀))))

claim-after-typable : ∀ d → True (of-natʳ d ≾ᵣ? of-natʳ 3) → Typable [] (claim-after d)
claim-after-typable d p = closed (claim-after-D d (toWitness p)) refl

claim-on-time-typed : IsTyped (infer [] (claim-after 3))
claim-on-time-typed = typed-of (claim-after 3) (closed (claim-after-D 3 ≾ᵣ-refl) refl) _

expected-claim-after : ℕ → Scheme
expected-claim-after d = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Unit ‼ ⌜ d ⌝ᵉ

------------------------------------------------------------------
-- 3. An inferred box grade
--
--   inferred-grade b = delay 2; unbox b as y in y
--
-- The claim asks for `⌜ 2 ⌝ʳ ≾ ρ` of the argument's grade `ρ`, and
-- the argument sits contravariantly, so the least such grade is the
-- principal one: the scheme has `[ ⌜ 2 ⌝ʳ ] α₀`, with no grade
-- variable. At the right-sided grades the function accepts any lease
-- of at least two ticks, at the left-sided ones any promise due
-- within two.

inferred-grade : RawC ∅ˢ 0
inferred-grade = return (lam (delay 2 (unbox fzero (return v₀))))

inferred-grade-typed : IsTyped (infer [] inferred-grade)
inferred-grade-typed =
  typed-of inferred-grade
    (closed {C = ([ ⌜ 2 ⌝ʳ ] Unit ⇒ Unit ‼ (⌜ 2 ⌝ᵉ ·̂ₑ ûₑ)) ‼ ûₑ}
      (return (lam (delay 2 (unbox (Tl-⟨⟩ Hd) on-time (<:̂ᵛ-refl _) (return (var Hd ok₀))))))
      refl) _

expected-inferred-grade : Scheme
expected-inferred-grade =
  ∀[ 1 , 0 , 0 ] ⊤ ⟹ ([ ⌜ 2 ⌝ʳ ] α₀ ⇒ α₀ ‼ ⌜ 2 ⌝ᵉ) ‼ ûₑ

-- Handing the box back as well as claiming it: the argument's grade
-- also flows out, so it is quantified. The scheme takes a box at
-- `⌜ 2 ⌝ʳ ⊔̂ᵣ ρ₀` and hands it back at `ρ₀`, the join being the
-- least grade both below `ρ₀`'s box and claimable after two ticks.
--
--   kept-and-claimed b = (b , λ _. delay 2; unbox b as y in y)

kept-and-claimed : RawC ∅ˢ 0
kept-and-claimed =
  return (lam (return ⦉ v₀ , lam (delay 2 (unbox (fsuc fzero) (return v₀))) ⦊))

kept-and-claimed-typed : IsTyped (infer [] kept-and-claimed)
kept-and-claimed-typed =
  typed-of kept-and-claimed
    (closed {C = ([ ⌜ 2 ⌝ʳ ] Unit
                   ⇒ ([ ⌜ 2 ⌝ʳ ] Unit |×| (Unit ⇒ Unit ‼ (⌜ 2 ⌝ᵉ ·̂ₑ ûₑ))) ‼ ûₑ) ‼ ûₑ}
      (return (lam (return ⦉ var Hd ok₀
                           , lam (delay 2 (unbox (Tl-⟨⟩ (Tl-∷ Hd)) on-time (<:̂ᵛ-refl _)
                                            (return (var Hd ok₀)))) ⦊)))
      refl) _

expected-kept-and-claimed : Scheme
expected-kept-and-claimed =
  ∀[ 2 , 1 , 0 ] ⊤ ⟹
    ([ ⌜ 2 ⌝ʳ ⊔̂ᵣ ρ₀ ] α₀ ⇒ ([ ρ₀ ] α₀ |×| (α₁ ⇒ α₀ ‼ ⌜ 2 ⌝ᵉ)) ‼ ûₑ) ‼ ûₑ

------------------------------------------------------------------
-- 4. A box escaping through `return`
--
--   escaping-after d =
--     let mk () = box[2] () as x in x in
--     let r = mk () in delay d; unbox r as y in y
--
-- The box is bound by the caller, when `mk` returns it, and claimed
-- `d` ticks later: the premise is `⌜ d ⌝ʳ ≾ ⌜ 2 ⌝ʳ`, on time at every
-- grade at `d = 2`. The unbox's grade is bounded by the box's only
-- through the subtyping of `mk`'s result, so a refused claim is
-- refuted by the ordering the two bounds entail, the transitive
-- closure of the closed orderings (`closedᴴ`): late at the
-- right-sided grades (`d = 4`), early at the left-sided ones
-- (`d = 1`).

escaping-after : ℕ → RawC ∅ˢ 0
escaping-after d =
  return (lam (box ⌜ 2 ⌝ʳ ⋆ (return v₀)))
  ⨟ ((v₀ · ⋆) ⨟ delay d (unbox fzero (return v₀)))

escaping-after-D : ∀ d → of-natʳ d ≾ᴳ of-natʳ 2
                 → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Unit ‼ (ûₑ ·̂ₑ (ûₑ ·̂ₑ (⌜ d ⌝ᵉ ·̂ₑ ûₑ)))
escaping-after-D d p =
  return (lam {A = Unit} (box ⌜ 2 ⌝ʳ ⋆ (return (var Hd ok₀))))
  ⨟ ((var Hd ok₀ · ⋆)
     ⨟ delay d (unbox (Tl-⟨⟩ Hd) (after p) (<:̂ᵛ-refl _) (return (var Hd ok₀))))

escaping-after-typable : ∀ d → True (of-natʳ d ≾ᵣ? of-natʳ 2) → Typable [] (escaping-after d)
escaping-after-typable d p = closed (escaping-after-D d (toWitness p)) refl

escaping-typed : IsTyped (infer [] (escaping-after 2))
escaping-typed = typed-of (escaping-after 2) (closed (escaping-after-D 2 ≾ᵣ-refl) refl) _

expected-escaping : ℕ → Scheme
expected-escaping d = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Unit ‼ ⌜ d ⌝ᵉ

------------------------------------------------------------------
-- 5. Claiming in both branches, after different delays
--
--   branches c b = if c then (delay 1; unbox b as y in y)
--                       else (delay 3; unbox b as y in y)
--
-- Each branch asks the argument's grade to be above what it waited,
-- so the least grade is the join `⌜ 1 ⌝ ⊔ ⌜ 3 ⌝`, and so is the
-- conditional's effect: three ticks at the right-sided grades, one at
-- the left-sided ones. The payload `α₀` and the result `α₁` are
-- related by `α₀ <: α₁`, one bound per branch merged into one.

branches : RawC ∅ˢ 0
branches =
  return (lam (return (lam
    (if v₁ `then delay 1 (unbox fzero (return v₀))
           `else delay 3 (unbox fzero (return v₀))))))

branches-typed : IsTyped (infer [] branches)
branches-typed =
  typed-of branches
    (closed {C = (Bool ⇒ ([ ⌜ 1 ⌝ʳ ⊔̂ᵣ ⌜ 3 ⌝ʳ ] Unit ⇒ Unit ‼ (⌜ 1 ⌝ᵉ ⊔̂ₑ ⌜ 3 ⌝ᵉ)) ‼ ûₑ) ‼ ûₑ}
      (return (lam (return (lam
        (if var (Tl-∷ Hd) ok₀
          `then coerce (transₑ (eqₑ ≡̂ₑ-identityʳ) ⊔-ubˡₑ)
                  (delay 1 (unbox (Tl-⟨⟩ Hd) (transᵣ on-time ⊔-ubˡᵣ) (<:̂ᵛ-refl _)
                              (return (var Hd ok₀))))
          `else coerce (transₑ (eqₑ ≡̂ₑ-identityʳ) ⊔-ubʳₑ)
                  (delay 3 (unbox (Tl-⟨⟩ Hd) (transᵣ on-time ⊔-ubʳᵣ) (<:̂ᵛ-refl _)
                              (return (var Hd ok₀)))))))))
      refl) _

expected-branches : Scheme
expected-branches =
  ∀[ 2 , 0 , 0 ] α₀ <: α₁ ⟹
    (Bool ⇒ ([ rconst (of-natʳ 1 ⊔ᵣ of-natʳ 3) ] α₀
               ⇒ α₁ ‼ econst (of-natᵉ 1 ⊔ₑ of-natᵉ 3)) ‼ ûₑ) ‼ ûₑ

------------------------------------------------------------------
-- 6. An operation's time licensing a claim
--
--   op-licensed op p = box[2] () as x in op p; unbox x as y in y
--
-- The premise is `op-grade op ≾ ⌜ 2 ⌝ʳ`: the operation's time is all
-- that has elapsed. At the time grades `read` takes one tick, `write`
-- two or three and `send` four or six; at the trace grades the
-- operation is weighed at its cost.

op-licensed : Op → RawC ∅ˢ 0
op-licensed op =
  return (lam (box ⌜ 2 ⌝ʳ ⋆ (perform op v₁ (unbox (fsuc fzero) (return v₀)))))

op-licensed-D : (op : Op) → mapᵉ (op-grade op) ≾ᴳ of-natʳ 2
              → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (⌜ param op ⌝ᵍ ⇒ Unit ‼ (econst (op-grade op) ·̂ₑ ûₑ)) ‼ ûₑ
op-licensed-D op p =
  return (lam (box ⌜ 2 ⌝ʳ ⋆
    (perform op (var (Tl-∷ Hd) ok₀)
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (after p) (<:̂ᵛ-refl _) (return (var Hd ok₀))))))

op-licensed-typable : (op : Op) → True (mapᵉ (op-grade op) ≾ᵣ? of-natʳ 2)
                    → Typable [] (op-licensed op)
op-licensed-typable op p = closed (op-licensed-D op (toWitness p)) refl

expected-op-licensed : Op → Scheme
expected-op-licensed op =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹ (⌜ param op ⌝ᵍ ⇒ Unit ‼ econst (op-grade op)) ‼ ûₑ

------------------------------------------------------------------
-- 7. Nested boxes
--
--   nested b = delay 1; unbox b as c in delay 2; unbox c as z in z
--
-- Each claim is weighed against what elapsed since its own binding:
-- the outer box after one tick, the inner one after two more. The
-- delays multiply, `⌜ 1 ⌝ᵉ ·ₑ ⌜ 2 ⌝ᵉ`, into the effect; typed at every
-- grade.

nested : RawC ∅ˢ 0
nested = return (lam (delay 1 (unbox fzero (delay 2 (unbox fzero (return v₀))))))

nested-typed : IsTyped (infer [] nested)
nested-typed =
  typed-of nested
    (closed {C = ([ ⌜ 1 ⌝ʳ ] ([ ⌜ 2 ⌝ʳ ] Unit) ⇒ Unit ‼ (⌜ 1 ⌝ᵉ ·̂ₑ (⌜ 2 ⌝ᵉ ·̂ₑ ûₑ))) ‼ ûₑ}
      (return (lam (delay 1 (unbox (Tl-⟨⟩ Hd) on-time (<:̂ᵛ-refl _)
        (delay 2 (unbox (Tl-⟨⟩ Hd) on-time (<:̂ᵛ-refl _) (return (var Hd ok₀))))))))
      refl) _

expected-nested : Scheme
expected-nested =
  ∀[ 1 , 0 , 0 ] ⊤ ⟹
    ([ ⌜ 1 ⌝ʳ ] ([ ⌜ 2 ⌝ʳ ] α₀) ⇒ α₀ ‼ econst (of-natᵉ 1 ·ₑ of-natᵉ 2)) ‼ ûₑ

-- Building the nesting in place:
--
--   nesting = box[2] () as x in box[1] x as y in
--             delay 1; unbox y as x' in delay 2; unbox x' as z in z
--
-- The outer payload `x` is used under `⟨ ⌜ 1 ⌝ʳ ⟩`, and a box type is
-- never eternal, so `var` asks for `⌜ 1 ⌝ʳ ≾ uᵣ`, as in `stale-call`.

nesting : RawC ∅ˢ 0
nesting =
  box ⌜ 2 ⌝ʳ ⋆ (box ⌜ 1 ⌝ʳ v₀
    (delay 1 (unbox fzero (delay 2 (unbox fzero (return v₀))))))

nesting-D : of-natʳ 1 ≾ᴳ uᵣ → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Unit ‼ (⌜ 1 ⌝ᵉ ·̂ₑ (⌜ 2 ⌝ᵉ ·̂ₑ ûₑ))
nesting-D q =
  box ⌜ 2 ⌝ʳ ⋆ (box ⌜ 1 ⌝ʳ (var (Tl-⟨⟩ Hd) (≾ᵘ-ok (after q)))
    (delay 1 (unbox (Tl-⟨⟩ Hd) on-time (<:̂ᵛ-refl _)
      (delay 2 (unbox (Tl-⟨⟩ Hd) on-time (<:̂ᵛ-refl _) (return (var Hd ok₀)))))))

nesting-typable : True (of-natʳ 1 ≾ᵣ? uᵣ) → Typable [] nesting
nesting-typable q = closed (nesting-D (toWitness q)) refl

expected-nesting : Scheme
expected-nesting = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Unit ‼ econst (of-natᵉ 1 ·ₑ of-natᵉ 2)

------------------------------------------------------------------
-- 8. A box claimed inside an operation clause
--
--   claimed-in-clause ρ m = box[ρ] () as x in
--     handle m () with op p k ↦ unbox x as y in
--                               let a = op p in unbox k as k' in k' a
--
-- A clause sees the ambient context behind the lock `⟨ ⊤ᵣ ⟩`, so the
-- premise is `⊤ᵣ ≾ ρ`. At `ρ = ⊤ᵣ` it holds at every grade; at
-- `ρ = uᵣ` exactly where the unit is the top (the left-sided grades);
-- at `ρ = ⌜ 1 ⌝ʳ` nowhere.

clause-claim : ∀ {Θ n} → Op → RawC (Θ +e) (suc (suc (suc n)))
clause-claim op =
  unbox (fsuc (fsuc fzero))
    (perform op v₂ (unbox (fsuc (fsuc fzero)) (v₀ · v₁)))

claimed-in-clause : RExp ∅ˢ → RawC ∅ˢ 0
claimed-in-clause ρ =
  return (lam (box ρ ⋆ (handle (v₁ · ⋆) `with clause-claim {∅ˢ} `in (return ⋆))))

private

  clause-claim-D : ∀ {c} → ⊤ᵣ ≾ᴳ c → (op : Op)
                 → ∅ᴴ ∣ wkᵉ-ctx {∅ˢ} ([] ▸ U⇒U ▸ [ rconst c ] Unit) ⟨ rconst ⊤ᵣ ⟩
                          ▸ ⌜ param op ⌝ᵍ
                          ▸ [ rconst (mapᵉ (op-grade op)) ]
                              (⌜ arity op ⌝ᵍ ⇒ Unit ‼ evar (newᵉ {∅ˢ}))
                   ⊢C⦂ Unit ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {∅ˢ}))
  clause-claim-D p op =
    unbox (Tl-∷ (Tl-∷ (Tl-⟨⟩ Hd))) (after p) (<:̂ᵛ-refl _)
      (perform op (var (Tl-∷ (Tl-∷ Hd)) ok₀)
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) on-time (<:̂ᵛ-refl _)
          (var Hd ok₀ · var (Tl-∷ Hd) ok₀)))

claimed-in-clause-D : ∀ {c} → ⊤ᵣ ≾ᴳ c
                    → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (U⇒U ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ
claimed-in-clause-D {c} p =
  return (lam (box (rconst c) ⋆
    (handle var (Tl-∷ Hd) ok₀ · ⋆ `with clause-claim-D p `in (return ⋆))))

claimed-in-clause-typable : ∀ c → True (⊤ᵣ ≾ᵣ? c) → Typable [] (claimed-in-clause (rconst c))
claimed-in-clause-typable c p = closed (claimed-in-clause-D (toWitness p)) refl

-- at the top it is typable at every grade

claimed-at-⊤-typable : Typable [] (claimed-in-clause (rconst ⊤ᵣ))
claimed-at-⊤-typable = closed (claimed-in-clause-D {⊤ᵣ} ≾ᵣ-refl) refl

expected-claimed-in-clause : Scheme
expected-claimed-in-clause =
  ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((Unit ⇒ α₀ ‼ ε₀) ⇒ Unit ‼ ε₀) ‼ ûₑ

-- The same clause claiming a box the caller hands in: its grade is
-- inferred, and the least grade above `⊤ᵣ` is `⊤ᵣ`.
--
--   handed-to-clause m b = handle m () with op p k ↦ unbox b as y in …

handed-to-clause : RawC ∅ˢ 0
handed-to-clause =
  return (lam (return (lam (handle (v₁ · ⋆) `with clause-claim {∅ˢ} `in (return ⋆)))))

handed-to-clause-typable : Typable [] handed-to-clause
handed-to-clause-typable =
  closed {C = (U⇒U ⇒ ([ rconst ⊤ᵣ ] Unit ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ) ‼ ûₑ}
    (return (lam (return (lam
      (handle var (Tl-∷ Hd) ok₀ · ⋆ `with clause-claim-D ≾ᵣ-refl `in (return ⋆))))))
    refl

expected-handed-to-clause : Scheme
expected-handed-to-clause =
  ∀[ 2 , 0 , 1 ] ⊤ ⟹
    ((Unit ⇒ α₁ ‼ ε₀) ⇒ ([ rconst ⊤ᵣ ] α₀ ⇒ Unit ‼ ε₀) ‼ ûₑ) ‼ ûₑ
