------------------------------------------------------------------------
-- Discretely-indexed presheaves over the worlds `W`.                  --
--                                                                    --
-- A presheaf is just a `W`-indexed family of sets — there is *no*     --
-- functorial (monotone) action, because the worlds are treated as a   --
-- discrete index. Consequently a morphism is just a `W`-indexed       --
-- family of functions (no naturality condition), and morphism         --
-- equality is plain propositional equality of such families           --
-- (recovered pointwise via function extensionality).                  --
--                                                                    --
-- The order on worlds is deliberately absent here: it only enters      --
-- through the box and context modalities (see the `Modality`          --
-- submodules), exactly as in the Kripke semantics of modal logic.     --
------------------------------------------------------------------------

open import Syntax.Grades
open import DenotationalSemantics.Model.World

module DenotationalSemantics.Model.Example.PSh.Base (Rg : Grade) (Wld : World Rg) where

open import Util.Equality

open import DenotationalSemantics.Model.Category

open World Wld

-- Discretely-indexed presheaves over the worlds

record PSh : Set₁ where
  constructor psh
  field
    -- object map / carrier of the presheaf, per world
    carrier : W → Set

open PSh public

-- Maps of presheaves: `W`-indexed families of functions. Wrapped in a
-- (single-field) record so that the field `app` has a genuine implicit
-- Pi type, which is what makes the function-extensionality reasoning in
-- `→ᵖ-ext` go through.

record _→ᵖ_ (A B : PSh) : Set where
  constructor pmap
  field
    app : ∀ {w} → carrier A w → carrier B w

open _→ᵖ_ public

infix 20 _→ᵖ_

-- Pointwise-to-propositional extensionality for presheaf maps.

→ᵖ-ext : ∀ {A B} {f g : A →ᵖ B}
       → (∀ {w} (x : carrier A w) → app f x ≡ app g x) → f ≡ g
→ᵖ-ext p = cong pmap (ifun-ext (fun-ext p))

-- Identity and composition of maps

idᵖ : ∀ {A} → A →ᵖ A
idᵖ = pmap (λ x → x)

_∘ᵖ_ : ∀ {A B C} → B →ᵖ C → A →ᵖ B → A →ᵖ C
g ∘ᵖ f = pmap (λ x → app g (app f x))

infixr 9 _∘ᵖ_

-- Packaging presheaves up as a category (all laws hold definitionally)

PShCat : Category
PShCat = record
  { Obj          = PSh
  ; _→ᵐ_         = _→ᵖ_
  ; idᵐ          = idᵖ
  ; _∘ᵐ_         = _∘ᵖ_
  ; ∘ᵐ-identityˡ = λ f → refl
  ; ∘ᵐ-identityʳ = λ f → refl
  ; ∘ᵐ-assoc     = λ h g f → refl
  }
