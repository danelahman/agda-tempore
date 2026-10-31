--------------------------------------------------------------------
-- Inference on annotated programs                                --
--                                                                --
-- Annotations of a value (`⦂ᵛ`) and of a computation (`⦂ᶜ`).     --
-- Each program is handler-free and typable, so inference answers --
-- `typed` at every grade, with the shape the annotation forces.  --
--------------------------------------------------------------------

open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Examples.Annotations (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades using (≃ᵣ⇒≾ᵣ; map-𝟏ᵉ)

open import PolymorphicCalculus.Syntax.Grades                S
open import PolymorphicCalculus.Syntax.Types                 S
open import PolymorphicCalculus.Syntax.Contexts              S hiding (Scheme; _∷_)
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
-- Typable and handler-free: `typed`

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

ok₀ : ∀ {Θ} {A : OVType Θ} → ∅ᴴ ⊩ A Et∨≾ᵘ 𝟏̂ᵣ
ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

-- A variable a value's unit effect has passed over

ok₁ : ∀ {Θ} {A : OVType Θ} → ∅ᴴ ⊩ A Et∨≾ᵘ (𝟏̂ᵣ ·̂ᵣ ∣ 𝟏̂ₑ ∣̂ᵉ)
ok₁ = ≾ᵘ-ok (transᵣ (eqᵣ ≡̂ᵣ-identityˡ)
               (transᵣ (eqᵣ ≡̂ᵣ-map-const) (atomᵣ (≃ᵣ⇒≾ᵣ map-𝟏ᵉ))))

U⇒U : ∀ {Θ} → OVType Θ
U⇒U = unit ⇒ unit ! 𝟏̂ₑ

------------------------------------------------------------------
-- An argument annotation: the identity with its argument annotated
-- `bool` where returned, so its type is `bool`, not a variable.

id-bool : RawC ∅ˢ 0
id-bool = return (fun (return (v₀ ⦂ᵛ bool) ⨟ return v₁))

id-bool-typed : IsTyped (infer [] id-bool)
id-bool-typed =
  typed-of id-bool
    (closed (return (fun (return (annᵛ bool (var Hd ok₀))
                          ⨟ return (var (Tl-∷ (Tl-⟨⟩ Hd)) ok₁)))) refl) _

expected-id-bool : Scheme
expected-id-bool = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (bool ⇒ bool ! 𝟏̂ₑ) ! 𝟏̂ₑ

------------------------------------------------------------------
-- A computation annotation: `id` annotated as a function on `unit`,
-- the reported type.

id-unit : RawC ∅ˢ 0
id-unit = return (fun (return v₀)) ⦂ᶜ (U⇒U ! 𝟏̂ₑ)

id-unit-typed : IsTyped (infer [] id-unit)
id-unit-typed =
  typed-of id-unit (closed (annᶜ (U⇒U ! 𝟏̂ₑ) (return (fun (return (var Hd ok₀))))) refl) _

expected-id-unit : Scheme
expected-id-unit = ∀[ 0 , 0 , 0 ] ⊤ ⟹ U⇒U ! 𝟏̂ₑ

------------------------------------------------------------------
-- `compose f g x = f (g x)` with `g` annotated as taking no time where
-- applied: `f`'s use asks nothing, and `f` stays polymorphic.

compose-g : RawC ∅ˢ 0
compose-g =
  return (fun (return (fun (return (fun
    (((v₁ ⦂ᵛ U⇒U) · v₀) ⨟ (v₃ · v₀)))))))

compose-g-typed : IsTyped (infer [] compose-g)
compose-g-typed =
  typed-of compose-g (closed {C = (U⇒U ⇒ (U⇒U ⇒ (unit ⇒ unit ! (𝟏̂ₑ ·̂ₑ 𝟏̂ₑ)) ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ}
    (return (fun (return (fun (return (fun
      ((annᵛ U⇒U (var (Tl-∷ Hd) ok₀) · var Hd ok₀)
       ⨟ (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ Hd)))) ok₁ · var Hd ok₀))))))))
    refl) _

expected-compose-g : Scheme
expected-compose-g =
  ∀[ 1 , 0 , 1 ] ⊤ ⟹
    ((unit ⇒ α₀ ! ε₀) ⇒ (U⇒U ⇒ (unit ⇒ α₀ ! ε₀) ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ
