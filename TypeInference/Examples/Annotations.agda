--------------------------------------------------------------------
-- Inference on annotated programs                                --
--                                                                --
-- An annotation fixes a shape: of a lambda's argument            --
-- (`lam[ A ]`), of a value (`⦂ᵛ`), of a computation (`⦂ᶜ`) or of --
-- an unboxed variable (`unbox[ A ]`). Each typed program has one --
-- annotation and no handler, and is typable at a closed          --
-- instance, so inference answers `typed` for each at every grade --
-- (a theorem over an arbitrary language); the scheme it reports  --
-- is the shape the annotation forces. `unbox-reject` is refuted: --
-- its variable's type is not below the annotation.               --
--------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
import Data.Fin as Fin

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.Examples.Annotations (S : LanguageSpec) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades using (≾ᵣ-reflexive; map-uᵉ)

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
open import TypeInference.SolverImpl           S opEnum
  using (infer-complete; infer-handlerFree)

open import TypeInference.SolverImpl S opEnum using (infer) public
open import TypeInference.Examples.Scheme S public
open import TypeInference.Examples.Variables

------------------------------------------------------------------
-- Typable and handler-free: inference answers `typed`

typed-of : (M : RawC ∅ˢ 0) → Typable [] M → HandlerFreeᶜ M → IsTyped (infer [] M)
typed-of M t h with infer [] M | infer-complete [] M t | infer-handlerFree [] M h
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
               (transᵣ (eqᵣ ≡̂ᵣ-map-const) (atomᵣ (≾ᵣ-reflexive map-uᵉ))))

U⇒U : ∀ {Θ} → OVType Θ
U⇒U = Unit ⇒ Unit ‼ ûₑ

------------------------------------------------------------------
-- An argument annotation
--
-- The identity at `Bool`: the argument's type is `Bool`, not a
-- variable.

id-bool : RawC ∅ˢ 0
id-bool = return (lam[ Bool ] (return v₀))

id-bool-typed : IsTyped (infer [] id-bool)
id-bool-typed =
  typed-of id-bool (closed (return (lamᵃ Bool (return (var Hd ok₀)))) refl) _

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
-- `∣ ε₁ ∣ ≾ uᵣ` (`expected-compose` in `Stdlib`); with it, `g`'s
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

------------------------------------------------------------------
-- An unboxed variable's annotation
--
-- A function unboxing its argument, annotated as a box of `Bool`
-- ready at once: the payload's type, otherwise a type variable, is
-- `Bool`.

unbox-bool : RawC ∅ˢ 0
unbox-bool = return (lam (unbox[ [ ûᵣ ] Bool ] Fin.zero (return v₀)))

unbox-bool-typed : IsTyped (infer [] unbox-bool)
unbox-bool-typed =
  typed-of unbox-bool
    (closed (return (lam (unboxᵃ ([ ûᵣ ] Bool) Hd ⊩≾̂ᵣ-refl (<:̂ᵛ-refl Bool)
                                 (<:̂ᵛ-refl ([ ûᵣ ] Bool)) (return (var Hd ok₀))))) refl) _

expected-unbox-bool : Scheme
expected-unbox-bool = ∀[ 0 , 0 , 0 ] ⊤ ⟹ ([ ûᵣ ] Bool ⇒ Bool ‼ ûₑ) ‼ ûₑ

-- The annotation is checked: a box of `Bool` is not of type `Unit`.

unbox-reject : RawC ∅ˢ 0
unbox-reject = return (lam[ [ ûᵣ ] Bool ] (unbox[ Unit ] Fin.zero (return v₀)))
