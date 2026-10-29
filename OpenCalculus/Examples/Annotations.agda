--------------------------------------------------------------------
-- Inference on annotated programs                                --
--                                                                --
-- An annotation fixes a shape: of a value (`⦂ᵛ`) or of a         --
-- computation (`⦂ᶜ`). Each program has one annotation and no     --
-- handler, and is typable at a closed instance, so inference     --
-- answers `typed` for each at every grade (a theorem over an     --
-- arbitrary language); the scheme it reports is the shape the    --
-- annotation forces.                                             --
--------------------------------------------------------------------

open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes
open import OpenCalculus.Inference.SolverImpl.Enum using (OpEnum)

module OpenCalculus.Examples.Annotations (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades using (≃ᵣ⇒≾ᵣ; map-uᵉ)

open import OpenCalculus.Syntax.Grades          S
open import OpenCalculus.Syntax.Types           S
open import OpenCalculus.Syntax.Contexts        S hiding (Scheme; _∷_)
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
-- Typable and handler-free: inference answers `typed`

typed-of : (M : RawC ∅ˢ 0) → Typable [] M → HandlerFreeᶜ M → IsTyped (infer [] M)
typed-of M t h with infer [] M | infer-complete [] M t | infer-handlerFree [] M tt h
... | typed p   | _  | _  = is-typed p
... | untypable | nu | _  = ⊥-elim (nu refl)
... | stuck     | _  | ns = ⊥-elim (ns refl)

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
-- An argument annotation
--
-- The identity at `Bool`, its argument annotated where it is first
-- returned: the argument's type is `Bool`, not a variable.

id-bool : RawC ∅ˢ 0
id-bool = return (lam (return (v₀ ⦂ᵛ Bool) ⨟ return v₁))

id-bool-typed : IsTyped (infer [] id-bool)
id-bool-typed =
  typed-of id-bool
    (closed (return (lam (return (annᵛ Bool (var Hd ok₀))
                          ⨟ return (var (Tl-∷ (Tl-⟨⟩ Hd)) ok₁)))) refl) _

expected-id-bool : Scheme
expected-id-bool = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Bool ⇒ Bool ‼ ûₑ) ‼ ûₑ

------------------------------------------------------------------
-- A computation annotation
--
-- The standard library's `id`, annotated as a computation returning
-- a function on `Unit`: the reported type is the annotation.

id-unit : RawC ∅ˢ 0
id-unit = return (lam (return v₀)) ⦂ᶜ (U⇒U ‼ ûₑ)

id-unit-typed : IsTyped (infer [] id-unit)
id-unit-typed =
  typed-of id-unit (closed (annᶜ (U⇒U ‼ ûₑ) (return (lam (return (var Hd ok₀))))) refl) _

expected-id-unit : Scheme
expected-id-unit = ∀[ 0 , 0 , 0 ] ⊤ ⟹ U⇒U ‼ ûₑ

------------------------------------------------------------------
-- A value annotation at an application's function position
--
-- The standard library's `compose f g x = f (g x)`, with `g`
-- annotated where it is applied as taking no time. `f` is used
-- after `g x` has run, so without the annotation `var` asks for
-- `∣ ε₁ ∣ ≾ uᵣ` (`compose` in `Stdlib`); with it, `g`'s
-- effect is the unit and nothing is asked. `g`'s argument and result
-- are `Unit`, the annotation being closed; `f`'s type stays
-- polymorphic, and the product `ûₑ ·̂ₑ ε₀` is reported as `ε₀`.

compose-g : RawC ∅ˢ 0
compose-g =
  return (lam (return (lam (return (lam
    (((v₁ ⦂ᵛ U⇒U) · v₀) ⨟ (v₃ · v₀)))))))

compose-g-typed : IsTyped (infer [] compose-g)
compose-g-typed =
  typed-of compose-g (closed {C = (U⇒U ⇒ (U⇒U ⇒ (Unit ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ}
    (return (lam (return (lam (return (lam
      ((annᵛ U⇒U (var (Tl-∷ Hd) ok₀) · var Hd ok₀)
       ⨟ (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ Hd)))) ok₁ · var Hd ok₀))))))))
    refl) _

expected-compose-g : Scheme
expected-compose-g =
  ∀[ 1 , 0 , 1 ] ⊤ ⟹
    ((Unit ⇒ α₀ ‼ ε₀) ⇒ (U⇒U ⇒ (Unit ⇒ α₀ ‼ ε₀) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ
