--------------------------------------------------------------------
-- Inference on handlers                                          --
--                                                                --
-- Handlers without annotations. `relay` and `relay-boxed` leave  --
-- cycles of clause-local unknowns for `Localise`; `discard` and  --
-- `resume-twice` are typable only at some grades; `bound`, `run` --
-- and `run-forward` use a handler as a value. The instances      --
-- under `Handlers/` check each answer by `refl` at four grades.  --
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

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Examples.Handlers (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades
  using (≃ᵣ⇒≾ᵣ; map-uᵉ; EGrade; uₑ; ⊤ₑ; ⊤ᵣ; _≾ₑ?_; mapᵉ)
open Operations Ops using (Op; param; arity; op-grade)

open import PolymorphicCalculus.Syntax.Grades                S
open import PolymorphicCalculus.Syntax.Types                 S
open import PolymorphicCalculus.Syntax.Contexts              S hiding (Scheme; _∷_)
open import PolymorphicCalculus.Syntax.Contexts              S using () renaming (_∷_ to _∷ᶜ_)
open import PolymorphicCalculus.Syntax.GradeSubstitution     S using (idˢ)
open import PolymorphicCalculus.Hypotheses                   S
open import PolymorphicCalculus.Hypotheses.Instances         S using (Satisfiable-∅)
open import PolymorphicCalculus.Typing                       S
open import PolymorphicCalculus.Syntax.Raw                   S
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution S using (_[_]ᴿᶜ)
open import PolymorphicCalculus.Typing.Erasure               S using (⌊_⌋ᶜ)
open import PolymorphicCalculus.Inference.Principality       S
open import PolymorphicCalculus.Inference.SolverImpl         S hints opEnum using (infer-complete)

open import PolymorphicCalculus.Inference.SolverImpl S hints opEnum using (infer) public
open import PolymorphicCalculus.Examples.Scheme S public
open import PolymorphicCalculus.Examples.Variables

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
-- A handler resuming through a helper `h`
--
--   relay m = handle m () with handler {
--     op p k ↦ let a = op p in
--              let h = λ x. x in h (h (λ _. k a)) ()}
--
-- `h`'s argument and result effects form a cycle of clause-local
-- unknowns, collapsed and sent to the rigid `j`.

resume-through : ∀ {Θ n} → Op → RawC (Θ +e) (suc (suc n))
resume-through op =
  perform op v₁ (unbox (var (fsuc fzero))
    (return (lam (return v₀)) ⨟ ((v₀ · lam (v₂ · v₃)) ⨟ ((v₁ · v₀) ⨟ (v₀ · ⋆)))))

relay : RawC ∅ˢ 0
relay = return (lam (handle (v₀ · ⋆) `with handler (return ⋆) resume-through))

-- Typable, `h` at `Unit ⇒ Unit ‼ j`, so never refuted

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
          (unbox (res-var {z = Tl-∷ (Tl-⟨⟩ Hd)}) (eqᵣ ≡̂ᵣ-identityˡ)
            (coerce (eqₑ u³)
              (return H
               ⨟ ((var Hd ok₀ · lam (var (Tl-∷ (Tl-∷ (Tl-⟨⟩ Hd))) ok₁
                                     · var (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))) ok₁))
                  ⨟ ((var (Tl-∷ (Tl-⟨⟩ Hd)) ok₁ · var Hd ok₀)
                     ⨟ (var Hd ok₀ · ⋆)))))))))

relay-typable : Typable [] relay
relay-typable = closed relay-D refl

relay-unrefuted : infer [] relay ≢ untypable
relay-unrefuted = infer-complete [] relay relay-typable

expected-relay : Scheme
expected-relay = ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((Unit ⇒ α₀ ‼ ε₀) ⇒ Unit ‼ ε₀) ‼ ûₑ

------------------------------------------------------------------
-- The helper applied twice to the boxed continuation
--
--   relay-boxed m = handle m () with handler {
--     op p k ↦ let h = λ x. x in let k₁ = h k in let k₂ = h k₁ in
--              let a = op p in unbox k₂ as k' in k' a}
--
-- Two cycles form, of box grades and of latent effects; both collapse
-- to the continuation's type.

through-box : ∀ {Θ n} → Op → RawC (Θ +e) (suc (suc n))
through-box op =
  return (lam (return v₀)) ⨟ ((v₀ · v₁) ⨟ ((v₁ · v₀) ⨟
    perform op v₄ (unbox (var (fsuc fzero)) (v₀ · v₁))))

relay-boxed : RawC ∅ˢ 0
relay-boxed = return (lam (handle (v₀ · ⋆) `with handler (return ⋆) through-box))

-- Typable, `h` at the continuation's type

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
                     (unbox (res-var {z = Tl-∷ (Tl-⟨⟩ Hd)}) (eqᵣ ≡̂ᵣ-identityˡ)
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
--   discard m = handle m () with handler {op p k ↦ return ()}
--
-- Needs `ûₑ ≾ op · j` for the rigid `j`: typable where the unit is
-- least, refuted at the left-sided grades.

discard : RawC ∅ˢ 0
discard = return (lam (handle (v₀ · ⋆) `with handler (return ⋆) (λ _ → return ⋆)))

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
--   resume-twice m = handle m () with handler {
--     op p k ↦ let a = op p in let k' = unbox k in (k' a ; k' a)}
--
-- Needs `op · (j · j) ≾ op · j` and, for the second call, `∣ j ∣ ≾ uᵣ`:
-- typable where the unit is the top, refuted at the right-sided grades.

resume-twice-clause : ∀ {Θ n} → Op → RawC (Θ +e) (suc (suc n))
resume-twice-clause op =
  perform op v₁ (unbox (var (fsuc fzero)) ((v₀ · v₁) ⨟ (v₁ · v₂)))

resume-twice : RawC ∅ˢ 0
resume-twice =
  return (lam (handle (v₀ · ⋆) `with handler (return ⋆) resume-twice-clause))

resume-twice-D : True (⊤ₑ ≾ₑ? uₑ)
               → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (U⇒U ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ
resume-twice-D top =
  return (lam (handle var Hd ok₀ · ⋆
    `with handler (return ⋆) (λ op →
      coerce (monoₑ ⊩≾̂ₑ-refl twice≾once)
        (perform op (var (Tl-∷ Hd) ok₀)
          (unbox (res-var {z = Tl-∷ (Tl-⟨⟩ Hd)}) (eqᵣ ≡̂ᵣ-identityˡ)
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
--   forwarder = handler {return x ↦ return x;
--                        op p k ↦ let a = op p in unbox k as k' in k' a}
--
--   bound m     = let h = forwarder in handle m () with h
--   run h m     = handle m () with h
--   run-forward = run forwarder
--
-- All three are typable over any language.

forward : ∀ {Θ n} → Op → RawC (Θ +e) (suc (suc n))
forward op = perform op v₁ (unbox (var (fsuc fzero)) (v₀ · v₁))

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
      (unbox (res-var {z = Tl-∷ (Tl-⟨⟩ Hd)}) (eqᵣ ≡̂ᵣ-identityˡ)
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

-- The handled effect, then the handler's; sorted the other way round
-- where the product commutes

expected-run : Scheme
expected-run =
  ∀[ 2 , 0 , 2 ] ⊤ ⟹ ((α₁ ‼ ε₁ ⇛ α₀ ‼ ε₀) ⇒ ((Unit ⇒ α₁ ‼ ε₁) ⇒ α₀ ‼ (ε₁ ·̂ₑ ε₀)) ‼ ûₑ) ‼ ûₑ

expected-run-commuted : Scheme
expected-run-commuted =
  ∀[ 2 , 0 , 2 ] ⊤ ⟹ ((α₁ ‼ ε₁ ⇛ α₀ ‼ ε₀) ⇒ ((Unit ⇒ α₁ ‼ ε₁) ⇒ α₀ ‼ (ε₀ ·̂ₑ ε₁)) ‼ ûₑ) ‼ ûₑ

expected-run-forward : Scheme
expected-run-forward = ∀[ 1 , 0 , 1 ] ⊤ ⟹ ((Unit ⇒ α₀ ‼ ε₀) ⇒ α₀ ‼ ε₀) ‼ ûₑ
