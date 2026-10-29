------------------------------------------------------------------
-- Report simplification                                        --
--                                                              --
-- Two schemes that the report simplifies.                      --
--                                                              --
-- `reused-around-claim` uses a variable on both sides of a     --
-- box's claim and so owes two var-rule disjunctions,           --
-- `eternal α ∨ ∣ε_f∣ ≾ uᵣ` and `eternal α ∨ ∣ε_f∣·∣ε_g∣ ≾ uᵣ`. --
-- Where the unit is least, the second entails the first, which --
-- is dropped.                                                  --
--                                                              --
-- `claimed-after-call` claims a box in a clause built after a  --
-- call, so the least box grade is `∣ε_f∣ · ⊤ᵣ`, a product with --
-- the top among its factors, which the top absorbs.            --
--                                                              --
-- Both simplifications apply where the unit is least; the      --
-- instances under `Reports/` check them at the right-sided     --
-- grades. At the left-sided grades the schemes are settled     --
-- without them, and there is no instance.                      --
------------------------------------------------------------------

open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; suc)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes
open import OpenCalculus.Inference.SolverImpl.Enum using (OpEnum)

module OpenCalculus.Examples.Reports (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades using (⊤ᵣ)
open Operations Ops using (Op)

open import OpenCalculus.Syntax.Grades          S
open import OpenCalculus.Syntax.Types           S
open import OpenCalculus.Syntax.Contexts        S hiding (Scheme) renaming (_∷_ to _▸_)
open import OpenCalculus.Syntax.Subst           S using (idˢ)
open import OpenCalculus.Hypotheses             S
open import OpenCalculus.Hypotheses.Instances   S using (Satisfiable-∅)
open import OpenCalculus.Typing                 S
open import OpenCalculus.Syntax.Raw             S
open import OpenCalculus.Syntax.Raw.Subst       S using (_[_]ᴿᶜ)
open import OpenCalculus.Typing.Erasure         S using (⌊_⌋ᶜ)
open import OpenCalculus.Inference.Principality S
open import OpenCalculus.Inference.SolverImpl   S hints opEnum
  using (infer-complete; infer-handlerFree)

open import OpenCalculus.Inference.SolverImpl S hints opEnum using (infer) public
open import OpenCalculus.Examples.Scheme S public
open import OpenCalculus.Examples.Variables

------------------------------------------------------------------
-- Verdicts

-- A closed derivation in the empty context is a typing

closed : {M : RawC ∅ˢ 0} {C : OCType ∅ˢ} → (D : ∅ᴴ ∣ [] ⊢C⦂ C)
       → ⌊ D ⌋ᶜ ≡ M [ idˢ ]ᴿᶜ → Typable [] M
closed {C = C} D e = typable ∅ˢ idˢ ∅ᴴ C D e Satisfiable-∅

-- Typable and handler-free: inference answers `typed`

typed-of : (M : RawC ∅ˢ 0) → Typable [] M → HandlerFreeᶜ M → IsTyped (infer [] M)
typed-of M t h with infer [] M | infer-complete [] M t | infer-handlerFree [] M tt h
... | typed p   | _  | _  = is-typed p
... | untypable | nu | _  = ⊥-elim (nu refl)
... | stuck     | _  | ns = ⊥-elim (ns refl)

------------------------------------------------------------------
-- Side conditions

private

  -- A claim made after exactly the box's grade

  on-time : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → Q ⊩ ûᵣ ·̂ᵣ ρ ≾̂ᵣ ρ
  on-time = eqᵣ ≡̂ᵣ-identityˡ

  -- A variable no time has passed over

  ok₀ : ∀ {Θ} {Q : Hyps Θ} {A : OVType Θ} → VarOK Q A ûᵣ
  ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

U⇒U : ∀ {Θ} → OVType Θ
U⇒U = Unit ⇒ Unit ‼ ûₑ

------------------------------------------------------------------
-- A variable used on both sides of a claim
--
--   reused-around-claim a f b = f (); unbox b as g in g a; return a
--
-- `a` is used after `f` and again after `g`, so it owes two var-rule
-- disjunctions, `eternal α ∨ ∣ ε_f ∣ ≾ uᵣ` and
-- `eternal α ∨ ∣ ε_f ∣ · ∣ ε_g ∣ ≾ uᵣ`. Where the unit is least, the
-- second entails the first, which is not reported (checked at the
-- right-sided grades; at the left-sided ones both are settled). The
-- box is claimed after `f`, at the least grade `∣ ε_f ∣`.

reused-around-claim : RawC ∅ˢ 0
reused-around-claim =
  return (lam (return (lam (return (lam
    ((v₁ · ⋆) ⨟ unbox (var (fsuc fzero)) ((v₀ · v₄) ⨟ return v₅)))))))

reused-around-claim-typed : IsTyped (infer [] reused-around-claim)
reused-around-claim-typed =
  typed-of reused-around-claim
    (closed {C = (Unit ⇒ (U⇒U ⇒ ([ ∣ ûₑ ∣̂ᵉ ] U⇒U ⇒ Unit ‼ (ûₑ ·̂ₑ (ûₑ ·̂ₑ ûₑ))) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ}
      (return (lam (return (lam (return (lam
        ((var (Tl-∷ Hd) ok₀ · ⋆)
         ⨟ unbox (res-var {z = Tl-∷ (Tl-⟨⟩ Hd)}) on-time
             ((var Hd ok₀ · var (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ Hd))))) (et-ok Unitₑ))
              ⨟ return (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ Hd)))))))
                            (et-ok Unitₑ))))))))))
      refl) _

expected-reused-around-claim : Conj (scope 3 0 2) → EExp (scope 3 0 2) → Scheme
expected-reused-around-claim C ε =
  ∀[ 3 , 0 , 2 ] C ⟹
    (α₂ ⇒ ((Unit ⇒ α₁ ‼ ε₁) ⇒ ([ ∣ ε₁ ∣̂ᵉ ] (α₂ ⇒ α₀ ‼ ε₀) ⇒ α₂ ‼ ε) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ

------------------------------------------------------------------
-- A box claimed in a clause built after a call
--
--   claimed-after-call f b = f ();
--     return (λ m. handle m () with handler {op p k ↦ unbox b as y in
--                                 let a = op p in unbox k as k' in k' a})
--
-- The clause claims `b` after `f` and behind the clause's lock, so the
-- least box grade is `∣ ε_f ∣ · ⊤ᵣ`: the top where the unit is least,
-- the product with the top being absorbed (checked at the right-sided
-- grades; where the unit is the top, `⊤ᵣ` is the unit).

claimed-after-call : RawC ∅ˢ 0
claimed-after-call =
  return (lam (return (lam
    ((v₁ · ⋆) ⨟ return (lam (handle (v₀ · ⋆) `with handler (return ⋆) clause-claim-after))))))
  where
    clause-claim-after : ∀ {Θ n} → Op → RawC (Θ +e) (suc (suc (suc (suc (suc n)))))
    clause-claim-after op =
      unbox (var (fsuc (fsuc (fsuc (fsuc fzero)))))
        (perform op v₂ (unbox (var (fsuc (fsuc fzero))) (v₀ · v₁)))

claimed-after-call-typable : Typable [] claimed-after-call
claimed-after-call-typable =
  closed {C = (U⇒U ⇒ ([ rconst ⊤ᵣ ] Unit ⇒ (U⇒U ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ) ‼ ûₑ}
    (return (lam (return (lam
      ((var (Tl-∷ Hd) ok₀ · ⋆)
       ⨟ return (lam (handle var Hd ok₀ · ⋆
           `with handler (return ⋆) (λ op →
             unbox (res-var {z = Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ Hd)))))}) topᵣ
               (perform op (var (Tl-∷ (Tl-∷ Hd)) ok₀)
                 (unbox (res-var {z = Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))}) on-time
                   (var Hd ok₀ · var (Tl-∷ Hd) ok₀)))))))))))
    refl

expected-claimed-after-call : RExp (scope 3 0 2) → Scheme
expected-claimed-after-call ρ =
  ∀[ 3 , 0 , 2 ] ⊤ ⟹
    ((Unit ⇒ α₂ ‼ ε₁) ⇒ ([ ρ ] α₀ ⇒ ((Unit ⇒ α₁ ‼ ε₀) ⇒ Unit ‼ ε₀) ‼ ε₁) ‼ ûₑ) ‼ ûₑ
