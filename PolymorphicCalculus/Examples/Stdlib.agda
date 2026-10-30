------------------------------------------------------------------
-- Inference on the prototype's standard library                --
--                                                              --
-- Nine functions of tempore-lang's standard library            --
-- (`src/06-user-interface/core/stdlib.tpe`), written as raw    --
-- terms. None has a handler, and each is typable at a closed   --
-- instance, so at every grade inference neither gets stuck nor --
-- refuses: `infer [] p` is `typed` (`p-typed`), a theorem over --
-- an arbitrary language.                                       --
--                                                              --
-- `expected-p` is the scheme inference reports, written once   --
-- over the language; the instances under `Stdlib/` check it by --
-- `refl` at concrete grades.                                   --
------------------------------------------------------------------

open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Examples.Stdlib (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades using (≃ᵣ⇒≾ᵣ; map-uᵉ)

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
open import PolymorphicCalculus.Inference.SolverImpl         S hints opEnum using (infer-complete; infer-handlerFree)

open import PolymorphicCalculus.Inference.SolverImpl S hints opEnum using (infer) public
open import PolymorphicCalculus.Examples.Scheme S public
open import PolymorphicCalculus.Examples.Variables

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

ok₀ : ∀ {A : OVType ∅ˢ} → VarOK ∅ᴴ A ûᵣ
ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

U⇒U : OVType ∅ˢ
U⇒U = Unit ⇒ Unit ‼ ûₑ

------------------------------------------------------------------
-- let id x = x
-- prototype: [α] α → α
--
-- A type variable, and a value's unit effect.

id : RawC ∅ˢ 0
id = return (lam (return v₀))

id-typed : IsTyped (infer [] id)
id-typed = typed-of id (closed {C = U⇒U ‼ ûₑ} (return (lam (return (var Hd ok₀)))) refl) _

expected-id : Scheme
expected-id = ∀[ 1 , 0 , 0 ] ⊤ ⟹ (α₀ ⇒ α₀ ‼ ûₑ) ‼ ûₑ

------------------------------------------------------------------
-- let ignore _ = ()
-- prototype: [α] α → unit
--
-- An argument nothing constrains.

ignore : RawC ∅ˢ 0
ignore = return (lam (return ⋆))

ignore-typed : IsTyped (infer [] ignore)
ignore-typed = typed-of ignore (closed {C = U⇒U ‼ ûₑ} (return (lam (return ⋆))) refl) _

expected-ignore : Scheme
expected-ignore = ∀[ 1 , 0 , 0 ] ⊤ ⟹ (α₀ ⇒ Unit ‼ ûₑ) ‼ ûₑ

------------------------------------------------------------------
-- let fst (x, _) = x
-- prototype: [α,β] β × α → β
--
-- Matching a pair.

fst : RawC ∅ˢ 0
fst = return (lam (match v₀ `in return v₁))

fst-typed : IsTyped (infer [] fst)
fst-typed =
  typed-of fst (closed {C = (Unit |×| Bool ⇒ Unit ‼ ûₑ) ‼ ûₑ}
    (return (lam (match var Hd ok₀ `in return (var (Tl-∷ Hd) ok₀)))) refl) _

expected-fst : Scheme
expected-fst = ∀[ 2 , 0 , 0 ] ⊤ ⟹ (α₁ |×| α₀ ⇒ α₁ ‼ ûₑ) ‼ ûₑ

------------------------------------------------------------------
-- let snd (_, y) = y
-- prototype: [α,β] β × α → α
--
-- Matching a pair.

snd : RawC ∅ˢ 0
snd = return (lam (match v₀ `in return v₀))

snd-typed : IsTyped (infer [] snd)
snd-typed =
  typed-of snd (closed {C = (Unit |×| Bool ⇒ Bool ‼ ûₑ) ‼ ûₑ}
    (return (lam (match var Hd ok₀ `in return (var Hd ok₀)))) refl) _

expected-snd : Scheme
expected-snd = ∀[ 2 , 0 , 0 ] ⊤ ⟹ (α₁ |×| α₀ ⇒ α₀ ‼ ûₑ) ‼ ûₑ

------------------------------------------------------------------
-- let not x = if x then false else true
-- prototype: bool → bool
--
-- A closed scheme: nothing to generalise.

not : RawC ∅ˢ 0
not = return (lam (if v₀ `then return false `else return true))

not-typed : IsTyped (infer [] not)
not-typed =
  typed-of not (closed {C = (Bool ⇒ Bool ‼ ûₑ) ‼ ûₑ}
    (return (lam (if var Hd ok₀ `then return false `else return true))) refl) _

expected-not : Scheme
expected-not = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Bool ⇒ Bool ‼ ûₑ) ‼ ûₑ

------------------------------------------------------------------
-- let absurd void = (match void with)
-- prototype: [α,β],[ρ₀] α → β # ρ₀
--
-- An effect variable. The argument is `Empty`, the one type `absurd`
-- eliminates.

absurd′ : RawC ∅ˢ 0
absurd′ = return (lam (absurd v₀))

absurd′-typed : IsTyped (infer [] absurd′)
absurd′-typed =
  typed-of absurd′ (closed {C = (Empty ⇒ Unit ‼ ûₑ) ‼ ûₑ}
    (return (lam (absurd (var Hd ok₀)))) refl) _

expected-absurd′ : Scheme
expected-absurd′ = ∀[ 1 , 0 , 1 ] ⊤ ⟹ (Empty ⇒ α₀ ‼ ε₀) ‼ ûₑ

------------------------------------------------------------------
-- let (|>) x f = f x
-- prototype: [α,β],[ρ₀] α → (α → β # ρ₀) → β # ρ₀
--
-- An application has the effect of the function applied.

pipe : RawC ∅ˢ 0
pipe = return (lam (return (lam (v₀ · v₁))))

pipe-typed : IsTyped (infer [] pipe)
pipe-typed =
  typed-of pipe (closed {C = (Unit ⇒ (U⇒U ⇒ Unit ‼ ûₑ) ‼ ûₑ) ‼ ûₑ}
    (return (lam (return (lam (var Hd ok₀ · var (Tl-∷ Hd) ok₀))))) refl) _

expected-pipe : Scheme
expected-pipe = ∀[ 2 , 0 , 1 ] ⊤ ⟹ (α₁ ⇒ ((α₁ ⇒ α₀ ‼ ε₀) ⇒ α₀ ‼ ε₀) ‼ ûₑ) ‼ ûₑ

------------------------------------------------------------------
-- let compose f g x = f (g x)
-- prototype: [α,β,γ],[ρ₀,ρ₁] (β → γ # ρ₁) → (α → β # ρ₀) → α → γ # ρ₀ + ρ₁
--
-- Effects multiply in the order the calls run, `g`'s then `f`'s.
-- The condition: `f` is an ordinary variable, not eternal, used after
-- `g x` has run, so `var` asks that `g` take no time,
-- `∣ ε₁ ∣̂ᵉ ≾ uᵣ`. Where the unit is least and the grade system
-- reflects the order at the unit, the condition forces `ε₁` to the
-- unit: `g` is pure, and the effect is `f`'s (`expected-compose`);
-- the grades where nothing goes stale report no condition.

compose : RawC ∅ˢ 0
compose = return (lam (return (lam (return (lam ((v₁ · v₀) ⨟ (v₃ · v₀)))))))

compose-typed : IsTyped (infer [] compose)
compose-typed =
  typed-of compose (closed {C = (U⇒U ⇒ (U⇒U ⇒ (Unit ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ}
    (return (lam (return (lam (return (lam
      ((var (Tl-∷ Hd) ok₀ · var Hd ok₀)
       ⨟ (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ Hd)))) (≾ᵘ-ok u·u≾u) · var Hd ok₀))))))))
    refl) _
  where
    u·u≾u : ∅ᴴ ⊩ ûᵣ ·̂ᵣ ∣ ûₑ ∣̂ᵉ ≾̂ᵣ ûᵣ
    u·u≾u = transᵣ (eqᵣ ≡̂ᵣ-identityˡ)
              (transᵣ (eqᵣ ≡̂ᵣ-map-const) (atomᵣ (≃ᵣ⇒≾ᵣ map-uᵉ)))

expected-compose : Scheme
expected-compose =
  ∀[ 3 , 0 , 1 ] ⊤ ⟹
    ((α₁ ⇒ α₀ ‼ ε₀) ⇒ ((α₂ ⇒ α₁ ‼ ûₑ) ⇒ (α₂ ⇒ α₀ ‼ ε₀) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ

------------------------------------------------------------------
-- let min x y = if x < y then x else y
-- prototype: [α] α → α → α
--
-- The comparison is passed in as a function, at any type; `cmp`
-- would require an eternal one.
-- The result is a common supertype of `x` and `y` (`α₀ <: α₁`,
-- `α₂ <: α₁`). The conditions: `x` and `y` are used after the
-- comparison has run, so each is eternal or the comparison takes no
-- time, two var-rule disjunctions (the prototype's
-- `{eternal α ∨ ρ <= 0}`).

min : RawC ∅ˢ 0
min = return (lam (return (lam (return (lam
        ((v₂ · ⦉ v₁ , v₀ ⦊) ⨟ (if v₀ `then return v₂ `else return v₁)))))))

min-typed : IsTyped (infer [] min)
min-typed =
  typed-of min (closed {C = ((Unit |×| Unit ⇒ Bool ‼ ûₑ)
                             ⇒ (Unit ⇒ (Unit ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ}
    (return (lam (return (lam (return (lam
      ((var (Tl-∷ (Tl-∷ Hd)) ok₀ · ⦉ var (Tl-∷ Hd) ok₀ , var Hd ok₀ ⦊)
       ⨟ (if var Hd ok₀
            `then return (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) (et-ok Unitₑ))
            `else return (var (Tl-∷ (Tl-⟨⟩ Hd)) (et-ok Unitₑ))))))))))
    refl) _

expected-min : Scheme
expected-min =
  ∀[ 3 , 0 , 1 ] α₂ <: α₁ ∧ α₀ <: α₁
                 ∧ eternal α₀ ∨ ∣ ε₀ ∣̂ᵉ ≾ûᵣ ∧ eternal α₂ ∨ ∣ ε₀ ∣̂ᵉ ≾ûᵣ ⟹
    ((α₂ |×| α₀ ⇒ Bool ‼ ε₀) ⇒ (α₂ ⇒ (α₀ ⇒ α₁ ‼ ε₀) ‼ ûₑ) ‼ ûₑ) ‼ ûₑ
