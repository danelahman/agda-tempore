------------------------------------------------------------------
-- Inference on annotated programs                                --
--                                                                --
-- An annotation fixes a shape: of a lambda's argument            --
-- (`lam[ A ]`), of a value (`⦂ᵛ`) or of a computation (`⦂ᶜ`).    --
-- The first three programs have one annotation each and no       --
-- handler, and each is typable at a closed instance, so          --
-- inference answers `typed` for each at every grade (a theorem   --
-- over an arbitrary language); the scheme it reports is the      --
-- shape the annotation forces.                                   --
--                                                                --
-- `relay` is a handler whose clause resumes through the          --
-- identity applied to its own result. It is typable              --
-- (`relay-typable`), with no annotation; the instances under     --
-- `Annotations/` check by `refl` that inference types it at the  --
-- four example grades.                                           --
------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (suc)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.Examples.Annotations (S : LanguageSpec) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades using (≾ᵣ-reflexive; map-uᵉ)
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
open import TypeInference.SolverImpl           S opEnum
  using (infer-complete; infer-handlerFree)

open import TypeInference.SolverImpl S opEnum using (infer) public
open import TypeInference.Examples.Report S public
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

expected-id-bool : Report
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

expected-id-unit : Report
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

expected-compose-g : Report
expected-compose-g =
  ∀[ 1 , 0 , 1 ] ⊤ ⟹
    ((Unit ⇒ α₀ ‼ ε₀) ⇒ (U⇒U ⇒ (Unit ⇒ α₀ ‼ ε₀) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ

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
