------------------------------------------------------------------
-- Inference on Tempore's standard library                      --
--                                                              --
-- Nine functions of Tempore's standard library as raw terms.   --
-- Each is handler-free and typable at a closed instance, so    --
-- inference answers `typed` at every grade (`p-typed`).        --
-- `expected-p` is the reported scheme, checked by `refl` at    --
-- the instances under `Stdlib/`.                               --
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
open import PolymorphicCalculus.Inference.SolverImpl         S hints opEnum using (infer-complete; infer-handlerFree)

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

closed : {M : RawC ∅ˢ 0} {C : OCType ∅ˢ} → (D : ∅ᴴ ∣ [] ⊢ᶜ⦂ C)
       → ⌊ D ⌋ᶜ ≡ M [ idˢ ]ᴿᶜ → Typable [] M
closed {C = C} D e = typable ∅ˢ idˢ ∅ᴴ C D e Satisfiable-∅

-- A variable no time has passed over

ok₀ : ∀ {A : OVType ∅ˢ} → ∅ᴴ ⊩ A Et∨≾ᵘ 𝟏̂ᵣ
ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

U⇒U : OVType ∅ˢ
U⇒U = unit ⇒ unit ! 𝟏̂ₑ

------------------------------------------------------------------
-- let id x = x
-- Tempore's scheme: [α] α → α
-- A type variable, and a value's unit effect.

id : RawC ∅ˢ 0
id = return (fun (return v₀))

id-typed : IsTyped (infer [] id)
id-typed = typed-of id (closed {C = U⇒U ! 𝟏̂ₑ} (return (fun (return (var Hd ok₀)))) refl) _

expected-id : Scheme
expected-id = ∀[ 1 , 0 , 0 ] ⊤ ⟹ (α₀ ⇒ α₀ ! 𝟏̂ₑ) ! 𝟏̂ₑ

------------------------------------------------------------------
-- let ignore _ = ()
-- Tempore's scheme: [α] α → unit
-- An argument nothing constrains.

ignore : RawC ∅ˢ 0
ignore = return (fun (return ⋆))

ignore-typed : IsTyped (infer [] ignore)
ignore-typed = typed-of ignore (closed {C = U⇒U ! 𝟏̂ₑ} (return (fun (return ⋆))) refl) _

expected-ignore : Scheme
expected-ignore = ∀[ 1 , 0 , 0 ] ⊤ ⟹ (α₀ ⇒ unit ! 𝟏̂ₑ) ! 𝟏̂ₑ

------------------------------------------------------------------
-- let fst (x, _) = x
-- Tempore's scheme: [α,β] β × α → β

fst : RawC ∅ˢ 0
fst = return (fun (match v₀ `with return v₁))

fst-typed : IsTyped (infer [] fst)
fst-typed =
  typed-of fst (closed {C = (unit |×| bool ⇒ unit ! 𝟏̂ₑ) ! 𝟏̂ₑ}
    (return (fun (match var Hd ok₀ `with return (var (Tl-∷ Hd) ok₀)))) refl) _

expected-fst : Scheme
expected-fst = ∀[ 2 , 0 , 0 ] ⊤ ⟹ (α₁ |×| α₀ ⇒ α₁ ! 𝟏̂ₑ) ! 𝟏̂ₑ

------------------------------------------------------------------
-- let snd (_, y) = y
-- Tempore's scheme: [α,β] β × α → α

snd : RawC ∅ˢ 0
snd = return (fun (match v₀ `with return v₀))

snd-typed : IsTyped (infer [] snd)
snd-typed =
  typed-of snd (closed {C = (unit |×| bool ⇒ bool ! 𝟏̂ₑ) ! 𝟏̂ₑ}
    (return (fun (match var Hd ok₀ `with return (var Hd ok₀)))) refl) _

expected-snd : Scheme
expected-snd = ∀[ 2 , 0 , 0 ] ⊤ ⟹ (α₁ |×| α₀ ⇒ α₀ ! 𝟏̂ₑ) ! 𝟏̂ₑ

------------------------------------------------------------------
-- let not x = if x then false else true
-- Tempore's scheme: bool → bool
-- A closed scheme.

not : RawC ∅ˢ 0
not = return (fun (if v₀ `then return false `else return true))

not-typed : IsTyped (infer [] not)
not-typed =
  typed-of not (closed {C = (bool ⇒ bool ! 𝟏̂ₑ) ! 𝟏̂ₑ}
    (return (fun (if var Hd ok₀ `then return false `else return true))) refl) _

expected-not : Scheme
expected-not = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (bool ⇒ bool ! 𝟏̂ₑ) ! 𝟏̂ₑ

------------------------------------------------------------------
-- let absurd void = (match void with)
-- Tempore's scheme: [α,β],[ρ₀] α → β # ρ₀
-- An effect variable; the argument is `empty`, which `absurd` eliminates.

absurd′ : RawC ∅ˢ 0
absurd′ = return (fun (absurd v₀))

absurd′-typed : IsTyped (infer [] absurd′)
absurd′-typed =
  typed-of absurd′ (closed {C = (empty ⇒ unit ! 𝟏̂ₑ) ! 𝟏̂ₑ}
    (return (fun (absurd (var Hd ok₀)))) refl) _

expected-absurd′ : Scheme
expected-absurd′ = ∀[ 1 , 0 , 1 ] ⊤ ⟹ (empty ⇒ α₀ ! ε₀) ! 𝟏̂ₑ

------------------------------------------------------------------
-- let (|>) x f = f x
-- Tempore's scheme: [α,β],[ρ₀] α → (α → β # ρ₀) → β # ρ₀
-- An application has the effect of the function applied.

pipe : RawC ∅ˢ 0
pipe = return (fun (return (fun (v₀ · v₁))))

pipe-typed : IsTyped (infer [] pipe)
pipe-typed =
  typed-of pipe (closed {C = (unit ⇒ (U⇒U ⇒ unit ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ}
    (return (fun (return (fun (var Hd ok₀ · var (Tl-∷ Hd) ok₀))))) refl) _

expected-pipe : Scheme
expected-pipe = ∀[ 2 , 0 , 1 ] ⊤ ⟹ (α₁ ⇒ ((α₁ ⇒ α₀ ! ε₀) ⇒ α₀ ! ε₀) ! 𝟏̂ₑ) ! 𝟏̂ₑ

------------------------------------------------------------------
-- let compose f g x = f (g x)
-- Tempore's scheme: [α,β,γ],[ρ₀,ρ₁] (β → γ # ρ₁) → (α → β # ρ₀) → α → γ # ρ₀ + ρ₁
-- `f` is used after `g x`, so `var` asks `∣ ε₁ ∣̂ᵉ ≾ 𝟏ᵣ`; where the unit
-- is least this forces `g` pure (`expected-compose`).

compose : RawC ∅ˢ 0
compose = return (fun (return (fun (return (fun ((v₁ · v₀) ⨟ (v₃ · v₀)))))))

compose-typed : IsTyped (infer [] compose)
compose-typed =
  typed-of compose (closed {C = (U⇒U ⇒ (U⇒U ⇒ (unit ⇒ unit ! (𝟏̂ₑ ·̂ₑ 𝟏̂ₑ)) ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ}
    (return (fun (return (fun (return (fun
      ((var (Tl-∷ Hd) ok₀ · var Hd ok₀)
       ⨟ (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ Hd)))) (≾ᵘ-ok 𝟏·𝟏≾𝟏) · var Hd ok₀))))))))
    refl) _
  where
    𝟏·𝟏≾𝟏 : ∅ᴴ ⊩ 𝟏̂ᵣ ·̂ᵣ ∣ 𝟏̂ₑ ∣̂ᵉ ≾̂ᵣ 𝟏̂ᵣ
    𝟏·𝟏≾𝟏 = transᵣ (eqᵣ ≡̂ᵣ-identityˡ)
              (transᵣ (eqᵣ ≡̂ᵣ-map-const) (atomᵣ (≃ᵣ⇒≾ᵣ map-𝟏ᵉ)))

expected-compose : Scheme
expected-compose =
  ∀[ 3 , 0 , 1 ] ⊤ ⟹
    ((α₁ ⇒ α₀ ! ε₀) ⇒ ((α₂ ⇒ α₁ ! 𝟏̂ₑ) ⇒ (α₂ ⇒ α₀ ! ε₀) ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ

------------------------------------------------------------------
-- let min x y = if x < y then x else y
-- Tempore's scheme: [α] α → α → α, with `{eternal α ∨ ρ <= 0}`
-- The comparison is a function argument. The result is a common supertype
-- of `x` and `y`, each used after the comparison: eternal or no time passed.

min : RawC ∅ˢ 0
min = return (fun (return (fun (return (fun
        ((v₂ · ⦉ v₁ , v₀ ⦊) ⨟ (if v₀ `then return v₂ `else return v₁)))))))

min-typed : IsTyped (infer [] min)
min-typed =
  typed-of min (closed {C = ((unit |×| unit ⇒ bool ! 𝟏̂ₑ)
                             ⇒ (unit ⇒ (unit ⇒ unit ! (𝟏̂ₑ ·̂ₑ 𝟏̂ₑ)) ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ}
    (return (fun (return (fun (return (fun
      ((var (Tl-∷ (Tl-∷ Hd)) ok₀ · ⦉ var (Tl-∷ Hd) ok₀ , var Hd ok₀ ⦊)
       ⨟ (if var Hd ok₀
            `then return (var (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) (et-ok unitₑ))
            `else return (var (Tl-∷ (Tl-⟨⟩ Hd)) (et-ok unitₑ))))))))))
    refl) _

expected-min : Scheme
expected-min =
  ∀[ 3 , 0 , 1 ] α₂ <: α₁ ∧ α₀ <: α₁
                 ∧ eternal α₀ ∨ ∣ ε₀ ∣̂ᵉ ≾𝟏̂ᵣ ∧ eternal α₂ ∨ ∣ ε₀ ∣̂ᵉ ≾𝟏̂ᵣ ⟹
    ((α₂ |×| α₀ ⇒ bool ! ε₀) ⇒ (α₂ ⇒ (α₀ ⇒ α₁ ! ε₀) ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ
