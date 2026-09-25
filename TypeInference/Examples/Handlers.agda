------------------------------------------------------------------
-- Inference on handlers                                          --
--                                                                --
-- Handlers whose clauses leave unknowns local to the clause's    --
-- rigid scope, which `Localise` gives values, and handlers whose --
-- typability depends on the grade. None has an annotation.       --
--                                                                --
-- `relay` resumes through the identity applied to its own        --
-- result: a cycle of two clause-local unknowns. `abort`'s clause --
-- grade is a unit factor times a clause-local unknown, below the --
-- clause's grade. Both are typable over an arbitrary language,   --
-- so inference never refutes them.                               --
--                                                                --
-- `discard` drops its continuation, and is typable where the     --
-- unit is least; `resume-twice` calls it twice, and is typable   --
-- where the unit is the top.                                     --
--                                                                --
-- The instances under `Handlers/` check by `refl`, at the four   --
-- example grades, that inference types each program where it is  --
-- typable and refutes it elsewhere.                              --
------------------------------------------------------------------

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Is-just)
open import Data.Nat using (suc)

open import Relation.Nullary.Decidable using (True; toWitness)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.Examples.Handlers (S : LanguageSpec) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades
  using (≾ᵣ-reflexive; map-uᵉ; uₑ; ⊤ₑ; _≾ₑ?_; uₑ-least?)
open Operations Ops using (Op)

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S hiding (_∷_)
open import TypeInference.OpenSyntax.Subst     S using (idˢ)
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S using (Satisfiable-∅)
open import TypeInference.OpenSyntax.Language  S
open import TypeInference.Raw.Syntax           S
open import TypeInference.Raw.Subst            S using (_[_]ᴿᶜ)
open import TypeInference.Erase                S using (⌊_⌋ᶜ)
open import TypeInference.Principality         S
open import TypeInference.SolverImpl           S opEnum using (infer-complete)

open import TypeInference.SolverImpl S opEnum using (infer) public
open import TypeInference.Examples.Report S public
open import TypeInference.Examples.Variables

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
               (transᵣ (eqᵣ ≡̂ᵣ-map-const) (atomᵣ (≾ᵣ-reflexive map-uᵉ))))

U⇒U : ∀ {Θ} → OVType Θ
U⇒U = Unit ⇒ Unit ‼ ûₑ

------------------------------------------------------------------
-- A handler resuming through a helper
--
-- A handler, as a function of the thunk it handles, whose clause
-- forwards the operation and resumes through a helper `h` applied
-- to its own result:
--
--   relay m = handle m () with
--     op p k ↦ let a = op p in
--              let h = λ x. x in h (h (λ _. k a)) ()
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
relay = return (lam (handle (v₀ · ⋆) `with resume-through `in (return ⋆)))

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
      `with (λ op →
        perform op (var (Tl-∷ Hd) ok₀)
          (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl _)
            (coerce (eqₑ u³)
              (return H
               ⨟ ((var Hd ok₀ · lam (var (Tl-∷ (Tl-∷ (Tl-⟨⟩ Hd))) ok₁
                                     · var (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))) ok₁))
                  ⨟ ((var (Tl-∷ (Tl-⟨⟩ Hd)) ok₁ · var Hd ok₀)
                     ⨟ (var Hd ok₀ · ⋆)))))))
      `in (return ⋆)))

relay-typable : Typable [] relay
relay-typable = closed relay-D refl

-- so inference never refutes it

relay-unrefuted : infer [] relay ≢ untypable
relay-unrefuted = infer-complete [] relay relay-typable

expected-relay : Report
expected-relay = ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((Unit ⇒ α₀ ‼ ε₀) ⇒ Unit ‼ ε₀) ‼ ûₑ

------------------------------------------------------------------
-- A clause with an effect nothing bounds below
--
-- A handler, as a function of an eternal `z : Empty` and of the
-- thunk it handles, whose clause returns and then eliminates `z`:
--
--   abort z m = handle m () with op p k ↦ (return () ; absurd z)
--
-- `z` is eternal, so the clause may use it under its lock. The
-- clause's grade is `ûₑ · e`, with `e` the latent effect of
-- `absurd z`: local to the clause, bounded above by the clause's
-- grade `op · j` and by nothing below. The example checks that
-- `ûₑ · e` is read as `e`, which is then sent to `op · j`. The
-- clause drops its continuation, but it is typable at every grade
-- only because `absurd z` has any effect; `discard` drops it with
-- no such argument.

abort : RawC ∅ˢ 0
abort = return (lam[ Empty ] (return (lam
          (handle (v₀ · ⋆) `with (λ op → return ⋆ ⨟ absurd v₄) `in (return ⋆)))))

-- It is typable, the clause at the unit

abort-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Empty ⇒ (U⇒U ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ) ‼ ûₑ
abort-D =
  return (lamᵃ Empty (return (lam
    (handle var Hd ok₀ · ⋆
     `with (λ op → coerce (eqₑ ≡̂ₑ-identityˡ)
                     (return ⋆ ⨟ absurd (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))))
                                             (et-ok Emptyₑ))))
     `in (return ⋆)))))

abort-typable : Typable [] abort
abort-typable = closed abort-D refl

-- so inference never refutes it

abort-unrefuted : infer [] abort ≢ untypable
abort-unrefuted = infer-complete [] abort abort-typable

expected-abort : Report
expected-abort = ∀[ 1 , 0 , 1 ] ⊤ ⟹ (Empty ⇒ ((Unit ⇒ α₀ ‼ ε₀) ⇒ Unit ‼ ε₀) ‼ ûₑ) ‼ ûₑ


------------------------------------------------------------------
-- A handler that drops its continuation
--
-- A handler, as a function of the thunk it handles, whose clause
-- returns at once:
--
--   discard m = handle m () with op p k ↦ return ()
--
-- The clause's grade `ûₑ` must be below `op · j` for the rigid `j`,
-- so for every continuation grade: the condition of `discarding` in
-- `Worked/Typing/Core.agda`. It holds where the unit is least
-- (`nothing-fits` at the right-sided grades), and fails at `j = ûₑ`
-- where the unit is not below `op-grade read` (`no-discarding` at
-- the left-sided grades).

discard : RawC ∅ˢ 0
discard = return (lam (handle (v₀ · ⋆) `with (λ _ → return ⋆) `in (return ⋆)))

-- It is typable where the unit is least

discard-D : Is-just uₑ-least? → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (U⇒U ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ
discard-D least =
  return (lam (handle var Hd ok₀ · ⋆
                `with (λ _ → coerce (minₑ least) (return ⋆))
                `in (return ⋆)))

discard-typable : Is-just uₑ-least? → Typable [] discard
discard-typable least = closed (discard-D least) refl

expected-discard : Report
expected-discard = ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((Unit ⇒ α₀ ‼ ε₀) ⇒ Unit ‼ ε₀) ‼ ûₑ

------------------------------------------------------------------
-- A handler that resumes twice
--
-- A handler, as a function of the thunk it handles, whose clause
-- forwards the operation and calls the continuation twice on its
-- result:
--
--   resume-twice m = handle m () with
--     op p k ↦ let a = op p in let k' = unbox k in (k' a ; k' a)
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
  return (lam (handle (v₀ · ⋆) `with resume-twice-clause `in (return ⋆)))

-- It is typable where the unit is the top

resume-twice-D : True (⊤ₑ ≾ₑ? uₑ)
               → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (U⇒U ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ
resume-twice-D top =
  return (lam (handle var Hd ok₀ · ⋆
    `with (λ op →
      coerce (monoₑ ⊩≾̂ₑ-refl twice≾once)
        (perform op (var (Tl-∷ Hd) ok₀)
          (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl _)
            ((var Hd ok₀ · var (Tl-∷ Hd) ok₀)
             ⨟ (var (Tl-∷ (Tl-⟨⟩ Hd)) okʲ · var (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) okʲ)))))
    `in (return ⋆)))
  where
    below-u : ∀ {Θ} {Q : Hyps Θ} {ε} → Q ⊩ ε ≾̂ₑ ûₑ
    below-u = transₑ topₑ (atomₑ (toWitness top))

    twice≾once : ∀ {Θ} {Q : Hyps Θ} {ε} → Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε
    twice≾once = transₑ (monoₑ ⊩≾̂ₑ-refl below-u) (eqₑ ≡̂ₑ-identityʳ)

    okʲ : ∀ {Θ} {Q : Hyps Θ} {A ε} → VarOK Q A (ûᵣ ·̂ᵣ ∣ ε ∣̂ᵉ)
    okʲ = ≾ᵘ-ok (transᵣ (eqᵣ ≡̂ᵣ-identityˡ)
                  (transᵣ (map-mono below-u)
                    (transᵣ (eqᵣ ≡̂ᵣ-map-const) (atomᵣ (≾ᵣ-reflexive map-uᵉ)))))

resume-twice-typable : True (⊤ₑ ≾ₑ? uₑ) → Typable [] resume-twice
resume-twice-typable top = closed (resume-twice-D top) refl

expected-resume-twice : Report
expected-resume-twice = ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((Unit ⇒ α₀ ‼ ε₀) ⇒ Unit ‼ ε₀) ‼ ûₑ
