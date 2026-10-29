--------------------------------------------------------------------
-- Inference on handlers                                          --
--                                                                --
-- A handler whose clause leaves unknowns local to the clause's   --
-- rigid scope, which `Localise` gives values, and handlers whose --
-- typability depends on the grade. None has an annotation.       --
--                                                                --
-- `relay` resumes through the identity applied to its own        --
-- result: a cycle of two clause-local unknowns. `relay-boxed`    --
-- passes the boxed continuation through the identity twice:      --
-- cycles of box grades and of latent effects. Both are typable   --
-- over an arbitrary language, so inference never refutes them.   --
--                                                                --
-- `discard` drops its continuation, and is typable where the     --
-- unit is least; `resume-twice` calls it twice, and is typable   --
-- where the unit is the top.                                     --
--                                                                --
-- `bound`, `run` and `run-forward` use a handler as a value.     --
--                                                                --
-- The instances under `Handlers/` check by `refl`, at the four   --
-- example grades, that inference types each program where it is  --
-- typable and refutes it elsewhere.                              --
--------------------------------------------------------------------

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.Definitions using (Minimum)
open import Data.Nat using (suc)

open import Relation.Nullary.Decidable using (True; toWitness)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes
open import OpenCalculus.Inference.SolverImpl.Enum using (OpEnum)

module OpenCalculus.Examples.Handlers (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades
  using (≃ᵣ⇒≾ᵣ; map-uᵉ; EGrade; uₑ; ⊤ₑ; ⊤ᵣ; _≾ₑ?_; mapᵉ)
open Operations Ops using (Op; param; arity; op-grade)

open import OpenCalculus.Syntax.Grades          S
open import OpenCalculus.Syntax.Types           S
open import OpenCalculus.Syntax.Contexts        S hiding (_∷_)
open import OpenCalculus.Syntax.Contexts        S using () renaming (_∷_ to _∷ᶜ_)
open import OpenCalculus.Syntax.Subst           S using (idˢ)
open import OpenCalculus.Hypotheses             S
open import OpenCalculus.Hypotheses.Instances   S using (Satisfiable-∅)
open import OpenCalculus.Typing                 S
open import OpenCalculus.Syntax.Raw             S
open import OpenCalculus.Syntax.Raw.Subst       S using (_[_]ᴿᶜ)
open import OpenCalculus.Typing.Erasure         S using (⌊_⌋ᶜ)
open import OpenCalculus.Inference.Principality S
open import OpenCalculus.Inference.SolverImpl   S hints opEnum using (infer-complete)

open import OpenCalculus.Inference.SolverImpl S hints opEnum using (infer) public
open import OpenCalculus.Examples.Scheme S public
open import OpenCalculus.Examples.Variables

------------------------------------------------------------------
-- A closed derivation in the empty context is a typing

closed : {M : RawC ∅ˢ 0} {C : OCType ∅ˢ} → (D : ∅ᴴ ∣ [] ⊢C⦂ C)
       → ⌊ D ⌋ᶜ ≡ M [ idˢ ]ᴿᶜ → Typable [] M
closed {C = C} D e = typable ∅ˢ idˢ ∅ᴴ C D e Satisfiable-∅

-- A variable no time has passed over

ok₀ : ∀ {Θ} {A : OVType Θ} → VarOK ∅ᴴ A ûᵣ
ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

-- A variable a value's unit effect has passed over

ok₁ : ∀ {Θ} {A : OVType Θ} → VarOK ∅ᴴ A (ûᵣ ·̂ᵣ ∣ ûₑ ∣̂ᵉ)
ok₁ = ≾ᵘ-ok (transᵣ (eqᵣ ≡̂ᵣ-identityˡ)
               (transᵣ (eqᵣ ≡̂ᵣ-map-const) (atomᵣ (≃ᵣ⇒≾ᵣ map-uᵉ))))

U⇒U : ∀ {Θ} → OVType Θ
U⇒U = Unit ⇒ Unit ‼ ûₑ

------------------------------------------------------------------
-- A handler resuming through a helper
--
-- A handler, as a function of the thunk it handles, whose clause
-- forwards the operation and resumes through a helper `h` applied
-- to its own result:
--
--   relay m = handle m () with handler {
--     op p k ↦ let a = op p in
--              let h = λ x. x in h (h (λ _. k a)) ()}
--
-- `h` is monomorphic, so the latent effects of its argument and of
-- its result bound each other: a cycle of two clause-local unknowns,
-- entered from below by the resumption's grade `j`, the clause's
-- rigid, and bounded above by the clause's grade `op · j`. The two
-- are identified, and then sent to `j`: `h` is typed at
-- `Unit ⇒ Unit ‼ j`.

resume-through : ∀ {Θ n} → Op → RawC (Θ +e) (suc (suc n))
resume-through op =
  perform op v₁ (unbox (fsuc fzero)
    (return (lam (return v₀)) ⨟ ((v₀ · lam (v₂ · v₃)) ⨟ ((v₁ · v₀) ⨟ (v₀ · ⋆)))))

relay : RawC ∅ˢ 0
relay = return (lam (handle (v₀ · ⋆) `with handler (return ⋆) resume-through))

-- It is typable, `h` at `Unit ⇒ Unit ‼ j`

private

  T : OVType (∅ˢ +e)
  T = Unit ⇒ Unit ‼ evar (newᵉ {∅ˢ})

  u³ : ∀ {Θ} {ε : EExp Θ} → ûₑ ·̂ₑ (ûₑ ·̂ₑ (ûₑ ·̂ₑ ε)) ≡̂ₑ ε
  u³ = ≡̂ₑ-trans ≡̂ₑ-identityˡ (≡̂ₑ-trans ≡̂ₑ-identityˡ ≡̂ₑ-identityˡ)

  H : ∀ {n} {Γ : OCtx (∅ˢ +e) n} → ∅ᴴ ∣ Γ ⊢V⦂ T ⇒ T ‼ ûₑ
  H = lam (return (var Hd ok₀))

  relay-D : ∅ᴴ ∣ [] ⊢C⦂ (U⇒U ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ
  relay-D =
    return (lam (handle var Hd ok₀ · ⋆
      `with handler (return ⋆) (λ op →
        perform op (var (Tl-∷ Hd) ok₀)
          (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl _)
            (coerce (eqₑ u³)
              (return H
               ⨟ ((var Hd ok₀ · lam (var (Tl-∷ (Tl-∷ (Tl-⟨⟩ Hd))) ok₁
                                     · var (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))) ok₁))
                  ⨟ ((var (Tl-∷ (Tl-⟨⟩ Hd)) ok₁ · var Hd ok₀)
                     ⨟ (var Hd ok₀ · ⋆)))))))))

relay-typable : Typable [] relay
relay-typable = closed relay-D refl

-- so inference never refutes it

relay-unrefuted : infer [] relay ≢ untypable
relay-unrefuted = infer-complete [] relay relay-typable

expected-relay : Scheme
expected-relay = ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((Unit ⇒ α₀ ‼ ε₀) ⇒ Unit ‼ ε₀) ‼ ûₑ

------------------------------------------------------------------
-- A handler resuming through a helper on boxes
--
-- The same helper applied twice to the boxed continuation itself:
--
--   relay-boxed m = handle m () with handler {
--     op p k ↦ let h = λ x. x in let k₁ = h k in let k₂ = h k₁ in
--              let a = op p in unbox k₂ as k' in k' a}
--
-- `h`'s argument and result are boxes, so two cycles of
-- clause-local unknowns form, one per sort: the box grades of `h`'s
-- argument and result, and the latent effects of the functions
-- inside them, each entered from below by the continuation's type.
-- Both are identified, and `h` is typed at the continuation's type.

through-box : ∀ {Θ n} → Op → RawC (Θ +e) (suc (suc n))
through-box op =
  return (lam (return v₀)) ⨟ ((v₀ · v₁) ⨟ ((v₁ · v₀) ⨟
    perform op v₄ (unbox (fsuc fzero) (v₀ · v₁))))

relay-boxed : RawC ∅ˢ 0
relay-boxed = return (lam (handle (v₀ · ⋆) `with handler (return ⋆) through-box))

-- It is typable, `h` at the continuation's type

private

  K : Op → OVType (∅ˢ +e)
  K op = [ rconst (mapᵉ (op-grade op)) ] (⌜ arity op ⌝ᵍ ⇒ Unit ‼ evar (newᵉ {∅ˢ}))

  -- a variable three unit effects have passed over

  ok₃ : ∀ {Θ} {A : OVType Θ} → VarOK ∅ᴴ A (((ûᵣ ·̂ᵣ ∣ ûₑ ∣̂ᵉ) ·̂ᵣ ∣ ûₑ ∣̂ᵉ) ·̂ᵣ ∣ ûₑ ∣̂ᵉ)
  ok₃ = ≾ᵘ-ok (step (step (step ⊩≾̂ᵣ-refl)))
    where
      u-map : ∀ {Θ} → ∅ᴴ {Θ} ⊩ ∣ ûₑ ∣̂ᵉ ≾̂ᵣ ûᵣ
      u-map = transᵣ (eqᵣ ≡̂ᵣ-map-const) (atomᵣ (≃ᵣ⇒≾ᵣ map-uᵉ))

      step : ∀ {Θ} {ρ : RExp Θ} → ∅ᴴ ⊩ ρ ≾̂ᵣ ûᵣ → ∅ᴴ ⊩ ρ ·̂ᵣ ∣ ûₑ ∣̂ᵉ ≾̂ᵣ ûᵣ
      step p = transᵣ (monoᵣ p u-map) (eqᵣ ≡̂ᵣ-identityˡ)

  relay-boxed-D : ∅ᴴ ∣ [] ⊢C⦂ (U⇒U ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ
  relay-boxed-D =
    return (lam (handle var Hd ok₀ · ⋆
      `with handler (return ⋆) (λ op →
        coerce (eqₑ u³)
          (return (lam {A = K op} (return (var Hd ok₀)))
           ⨟ ((var Hd ok₀ · var (Tl-∷ (Tl-⟨⟩ Hd)) ok₁)
              ⨟ ((var (Tl-∷ (Tl-⟨⟩ Hd)) ok₁ · var Hd ok₀)
                 ⨟ perform op (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))))) ok₃)
                     (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl _)
                       (var Hd ok₀ · var (Tl-∷ Hd) ok₀))))))))

relay-boxed-typable : Typable [] relay-boxed
relay-boxed-typable = closed relay-boxed-D refl

relay-boxed-unrefuted : infer [] relay-boxed ≢ untypable
relay-boxed-unrefuted = infer-complete [] relay-boxed relay-boxed-typable

expected-relay-boxed : Scheme
expected-relay-boxed = ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((Unit ⇒ α₀ ‼ ε₀) ⇒ Unit ‼ ε₀) ‼ ûₑ

------------------------------------------------------------------
-- A handler that drops its continuation
--
-- A handler, as a function of the thunk it handles, whose clause
-- returns at once:
--
--   discard m = handle m () with handler {op p k ↦ return ()}
--
-- The clause's grade `ûₑ` must be below `op · j` for the rigid `j`,
-- so for every continuation grade: the condition of `discarding` in
-- `ClosedCalculus/Examples/Typing/Core.agda`. It holds where the unit is least
-- (`nothing-fits` at the right-sided grades), and fails at `j = ûₑ`
-- where the unit is not below `op-grade read` (`no-discarding` at
-- the left-sided grades).

discard : RawC ∅ˢ 0
discard = return (lam (handle (v₀ · ⋆) `with handler (return ⋆) (λ _ → return ⋆)))

-- It is typable where the unit is least

discard-D : Minimum (Grade._≾_ EGrade) uₑ → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (U⇒U ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ
discard-D least =
  return (lam (handle var Hd ok₀ · ⋆
                `with handler (return ⋆) (λ _ → coerce (minₑ least) (return ⋆))))

discard-typable : Minimum (Grade._≾_ EGrade) uₑ → Typable [] discard
discard-typable least = closed (discard-D least) refl

expected-discard : Scheme
expected-discard = ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((Unit ⇒ α₀ ‼ ε₀) ⇒ Unit ‼ ε₀) ‼ ûₑ

------------------------------------------------------------------
-- A handler that resumes twice
--
-- A handler, as a function of the thunk it handles, whose clause
-- forwards the operation and calls the continuation twice on its
-- result:
--
--   resume-twice m = handle m () with handler {
--     op p k ↦ let a = op p in let k' = unbox k in (k' a ; k' a)}
--
-- Performing the operation gives an argument of its arity, and the
-- lock under which `k` is unboxed, at every operation. The clause's
-- grade is `op · (j · j)`, against `op · j`; and the second call
-- uses `k'` and `a` after `∣ j ∣` has passed, neither type being
-- eternal (`a` is a reading at `read`), so `var` asks for
-- `∣ j ∣ ≾ uᵣ`. Both hold for every `j` where the unit is the top
-- effect grade: the left-sided grades. At the right-sided grades
-- neither does, `j` being above the unit.

resume-twice-clause : ∀ {Θ n} → Op → RawC (Θ +e) (suc (suc n))
resume-twice-clause op =
  perform op v₁ (unbox (fsuc fzero) ((v₀ · v₁) ⨟ (v₁ · v₂)))

resume-twice : RawC ∅ˢ 0
resume-twice =
  return (lam (handle (v₀ · ⋆) `with handler (return ⋆) resume-twice-clause))

-- It is typable where the unit is the top

resume-twice-D : True (⊤ₑ ≾ₑ? uₑ)
               → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (U⇒U ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ
resume-twice-D top =
  return (lam (handle var Hd ok₀ · ⋆
    `with handler (return ⋆) (λ op →
      coerce (monoₑ ⊩≾̂ₑ-refl twice≾once)
        (perform op (var (Tl-∷ Hd) ok₀)
          (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl _)
            ((var Hd ok₀ · var (Tl-∷ Hd) ok₀)
             ⨟ (var (Tl-∷ (Tl-⟨⟩ Hd)) okʲ · var (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) okʲ)))))))
  where
    below-u : ∀ {Θ} {Q : Hyps Θ} {ε} → Q ⊩ ε ≾̂ₑ ûₑ
    below-u = transₑ topₑ (atomₑ (toWitness top))

    twice≾once : ∀ {Θ} {Q : Hyps Θ} {ε} → Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε
    twice≾once = transₑ (monoₑ ⊩≾̂ₑ-refl below-u) (eqₑ ≡̂ₑ-identityʳ)

    okʲ : ∀ {Θ} {Q : Hyps Θ} {A ε} → VarOK Q A (ûᵣ ·̂ᵣ ∣ ε ∣̂ᵉ)
    okʲ = ≾ᵘ-ok (transᵣ (eqᵣ ≡̂ᵣ-identityˡ)
                  (transᵣ (map-mono below-u)
                    (transᵣ (eqᵣ ≡̂ᵣ-map-const) (atomᵣ (≃ᵣ⇒≾ᵣ map-uᵉ)))))

resume-twice-typable : True (⊤ₑ ≾ₑ? uₑ) → Typable [] resume-twice
resume-twice-typable top = closed (resume-twice-D top) refl

expected-resume-twice : Scheme
expected-resume-twice = ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((Unit ⇒ α₀ ‼ ε₀) ⇒ Unit ‼ ε₀) ‼ ûₑ

------------------------------------------------------------------
-- Handlers as values
--
-- A handler is a value of a handler type: it can be bound by `let`,
-- passed to a function and returned, and `handle` takes any value of
-- a handler type. `forwarder` returns what it handles and forwards
-- each operation, resuming with the answer:
--
--   forwarder = handler {return x ↦ return x;
--                        op p k ↦ let a = op p in unbox k as k' in k' a}
--
--   bound m     = let h = forwarder in handle m () with h
--   run h m     = handle m () with h
--   run-forward = run forwarder
--
-- The clause's grade is `op · j` for the rigid `j`, as the rule asks,
-- so all three are typable over an arbitrary language.

forward : ∀ {Θ n} → Op → RawC (Θ +e) (suc (suc n))
forward op = perform op v₁ (unbox (fsuc fzero) (v₀ · v₁))

forwarder : ∀ {Θ n} → RawV Θ n
forwarder = handler (return v₀) forward

bound : RawC ∅ˢ 0
bound = return (lam (return forwarder ⨟ (handle (v₁ · ⋆) `with v₀)))

run : RawC ∅ˢ 0
run = return (lam (return (lam (handle (v₀ · ⋆) `with v₁))))

run-forward : RawC ∅ˢ 0
run-forward = run ⨟ (v₀ · forwarder)

-- `bound` is typable, `forwarder` at `Unit ‼ ûₑ ⇛ Unit ‼ ûₑ`

private

  forward-D : ∀ {n} {Γ : OCtx (∅ˢ +e) n} → (op : Op)
            → ∅ᴴ ∣ Γ ⟨ rconst ⊤ᵣ ⟩ ∷ᶜ ⌜ param op ⌝ᵍ
                   ∷ᶜ [ rconst (mapᵉ (op-grade op)) ] (⌜ arity op ⌝ᵍ ⇒ Unit ‼ evar (newᵉ {∅ˢ}))
              ⊢C⦂ Unit ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {∅ˢ}))
  forward-D op =
    perform op (var (Tl-∷ Hd) ok₀)
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl _)
        (var Hd ok₀ · var (Tl-∷ Hd) ok₀))

  bound-D : ∅ᴴ ∣ [] ⊢C⦂ (U⇒U ⇒ Unit ‼ (ûₑ ·̂ₑ (ûₑ ·̂ₑ ûₑ))) ‼ ûₑ
  bound-D =
    return (lam (return (handler (return (var Hd ok₀)) forward-D)
                 ⨟ (handle var (Tl-∷ (Tl-⟨⟩ Hd)) ok₁ · ⋆ `with var Hd ok₀)))

bound-typable : Typable [] bound
bound-typable = closed bound-D refl

bound-unrefuted : infer [] bound ≢ untypable
bound-unrefuted = infer-complete [] bound bound-typable

expected-bound : Scheme
expected-bound = ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((Unit ⇒ α₀ ‼ ε₀) ⇒ α₀ ‼ ε₀) ‼ ûₑ

-- `run` is typed at a handler type, its result at the handled
-- effect followed by the handler's; where the product commutes, the
-- canonical form lists the two the other way round

expected-run : Scheme
expected-run =
  ∀[ 2 , 0 , 2 ] ⊤ ⟹ ((α₁ ‼ ε₁ ⇛ α₀ ‼ ε₀) ⇒ ((Unit ⇒ α₁ ‼ ε₁) ⇒ α₀ ‼ (ε₁ ·̂ₑ ε₀)) ‼ ûₑ) ‼ ûₑ

expected-run-commuted : Scheme
expected-run-commuted =
  ∀[ 2 , 0 , 2 ] ⊤ ⟹ ((α₁ ‼ ε₁ ⇛ α₀ ‼ ε₀) ⇒ ((Unit ⇒ α₁ ‼ ε₁) ⇒ α₀ ‼ (ε₀ ·̂ₑ ε₁)) ‼ ûₑ) ‼ ûₑ

expected-run-forward : Scheme
expected-run-forward = ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((Unit ⇒ α₀ ‼ ε₀) ⇒ α₀ ‼ ε₀) ‼ ûₑ
