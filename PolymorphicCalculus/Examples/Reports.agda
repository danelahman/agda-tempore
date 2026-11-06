------------------------------------------------------------------------
-- Report simplification                                              --
--                                                                    --
-- Two schemes that inference simplifies before reporting them, where --
-- the unit is least.                                                 --
--                                                                    --
-- The examples                                                       --
--   reused-around-claim   a variable used on both sides of a claim;  --
--                         of its two time conditions one entails the --
--                         other, and only that one is reported       --
--   claimed-after-call    a box claimed in a clause built after a    --
--                         call; its grade has the top grade as a     --
--                         factor and is reported as the top          --
--                                                                    --
-- How to read them                                                   --
--   Each program is written above its definition in ordinary syntax. --
--   The modules under `Reports/` run inference at the two            --
--   upper-bound grades and check with `refl` that the simplified     --
--   scheme is reported:                                              --
--     reused-around-claim-reported :                                 --
--       schemeOf (infer [] reused-around-claim) ≡ just …             --
------------------------------------------------------------------------

open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; suc)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Examples.Reports (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades using (⊤ᵣ)
open Operations Ops using (Op)

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

  -- A claim made after exactly the box's grade

  on-time : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → Q ⊩ 𝟏̂ᵣ ·̂ᵣ ρ ≾̂ᵣ ρ
  on-time = eqᵣ ≡̂ᵣ-identityˡ

  -- A variable no time has passed over

  ok₀ : ∀ {Θ} {Q : Hyps Θ} {A : OVType Θ} → Q ⊩ A Et∨≾ᵘ 𝟏̂ᵣ
  ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

U⇒U : ∀ {Θ} → OVType Θ
U⇒U = unit ⇒ unit ! 𝟏̂ₑ

------------------------------------------------------------------
-- A variable used on both sides of a claim
--
--   reused-around-claim a f b = f (); unbox b as g in g a; return a
--
-- `a` owes `eternal α ∨ ∣ ε_f ∣ ≾ 𝟏ᵣ` and
-- `eternal α ∨ ∣ ε_f ∣ · ∣ ε_g ∣ ≾ 𝟏ᵣ`; where the unit is least the
-- second entails the first, which is dropped.

reused-around-claim : RawC ∅ˢ 0
reused-around-claim =
  return (fun (return (fun (return (fun
    ((v₁ · ⋆) ⨟ unbox (var (fsuc fzero)) ((v₀ · v₄) ⨟ return v₅)))))))

reused-around-claim-typed : IsTyped (infer [] reused-around-claim)
reused-around-claim-typed =
  typed-of reused-around-claim
    (closed {C = (unit ⇒ (U⇒U ⇒ ([ ∣ 𝟏̂ₑ ∣̂ᵉ ] U⇒U ⇒ unit ! (𝟏̂ₑ ·̂ₑ (𝟏̂ₑ ·̂ₑ 𝟏̂ₑ))) ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ}
      (return (fun (return (fun (return (fun
        ((var (Tl-∷ Hd) ok₀ · ⋆)
         ⨟ unbox (res-var (Tl-∷ (Tl-⟨⟩ Hd))) on-time
             ((var Hd ok₀ · var (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ Hd))))) (et-ok unitₑ))
              ⨟ return (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ Hd)))))))
                            (et-ok unitₑ))))))))))
      refl) _

expected-reused-around-claim : Conj (scope 3 0 2) → EExp (scope 3 0 2) → Scheme
expected-reused-around-claim C ε =
  ∀[ 3 , 0 , 2 ] C ⟹
    (α₂ ⇒ ((unit ⇒ α₁ ! ε₁) ⇒ ([ ∣ ε₁ ∣̂ᵉ ] (α₂ ⇒ α₀ ! ε₀) ⇒ α₂ ! ε) ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ

------------------------------------------------------------------
-- A box claimed in a clause built after a call
--
--   claimed-after-call f b = f ();
--     return (λ m. handle m () with handler {op p k ↦ unbox b as y in
--                                 let a = op p in unbox k as k' in k' a})
--
-- The box's grade `∣ ε_f ∣ · ⊤ᵣ` is absorbed into the top where the
-- unit is least.

claimed-after-call : RawC ∅ˢ 0
claimed-after-call =
  return (fun (return (fun
    ((v₁ · ⋆) ⨟ return (fun (handle (v₀ · ⋆) `with handler (return ⋆) clause-claim-after))))))
  where
    clause-claim-after : ∀ {Θ n} → Op → RawC (Θ +e) (suc (suc (suc (suc (suc n)))))
    clause-claim-after op =
      unbox (var (fsuc (fsuc (fsuc (fsuc fzero)))))
        (perform op v₂ (unbox (var (fsuc (fsuc fzero))) (v₀ · v₁)))

claimed-after-call-typable : Typable [] claimed-after-call
claimed-after-call-typable =
  closed {C = (U⇒U ⇒ ([ rconst ⊤ᵣ ] unit ⇒ (U⇒U ⇒ unit ! (𝟏̂ₑ ·̂ₑ 𝟏̂ₑ)) ! (𝟏̂ₑ ·̂ₑ 𝟏̂ₑ)) ! 𝟏̂ₑ) ! 𝟏̂ₑ}
    (return (fun (return (fun
      ((var (Tl-∷ Hd) ok₀ · ⋆)
       ⨟ return (fun (handle var Hd ok₀ · ⋆
           `with handler (return ⋆) (λ op →
             unbox (res-var (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ Hd))))))) topᵣ
               (perform op (var (Tl-∷ (Tl-∷ Hd)) ok₀)
                 (unbox (res-var (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd)))) on-time
                   (var Hd ok₀ · var (Tl-∷ Hd) ok₀)))))))))))
    refl

expected-claimed-after-call : RExp (scope 3 0 2) → Scheme
expected-claimed-after-call ρ =
  ∀[ 3 , 0 , 2 ] ⊤ ⟹
    ((unit ⇒ α₂ ! ε₁) ⇒ ([ ρ ] α₀ ⇒ ((unit ⇒ α₁ ! ε₀) ⇒ unit ! ε₀) ! ε₁) ! 𝟏̂ₑ) ! 𝟏̂ₑ
