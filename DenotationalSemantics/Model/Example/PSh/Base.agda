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

module DenotationalSemantics.Model.Example.PSh.Base (GS : GradeSystem) (Wld : World (GradeSystem.RGrade GS)) where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

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

-- Cartesian closed structure — everything pointwise, since the worlds
-- are a discrete index.

-- Terminal object

𝟙ᵖ : PSh
𝟙ᵖ = psh (λ _ → ⊤)

terminalᵖ : ∀ {A} → A →ᵖ 𝟙ᵖ
terminalᵖ = pmap (λ _ → tt)

terminalᵖ-unique : ∀ {A} {f : A →ᵖ 𝟙ᵖ} → f ≡ terminalᵖ
terminalᵖ-unique = →ᵖ-ext (λ x → refl)

-- Initial object

𝟘ᵖ : PSh
𝟘ᵖ = psh (λ _ → ⊥)

initialᵖ : ∀ {A} → 𝟘ᵖ →ᵖ A
initialᵖ = pmap (λ ())

initialᵖ-unique : ∀ {A} {f : 𝟘ᵖ →ᵖ A} → f ≡ initialᵖ
initialᵖ-unique = →ᵖ-ext (λ ())

-- Binary products

infixr 23 _×ᵖ_

_×ᵖ_ : PSh → PSh → PSh
A ×ᵖ B = psh (λ w → carrier A w × carrier B w)

fstᵖ : ∀ {A B} → A ×ᵖ B →ᵖ A
fstᵖ = pmap proj₁

sndᵖ : ∀ {A B} → A ×ᵖ B →ᵖ B
sndᵖ = pmap proj₂

⟨_,_⟩ᵖ : ∀ {A B C} → A →ᵖ B → A →ᵖ C → A →ᵖ B ×ᵖ C
⟨ f , g ⟩ᵖ = pmap (λ x → app f x , app g x)

⟨⟩ᵖ-fstᵖ : ∀ {A B C} → (f : A →ᵖ B) → (g : A →ᵖ C) → fstᵖ ∘ᵖ ⟨ f , g ⟩ᵖ ≡ f
⟨⟩ᵖ-fstᵖ f g = →ᵖ-ext (λ x → refl)

⟨⟩ᵖ-sndᵖ : ∀ {A B C} → (f : A →ᵖ B) → (g : A →ᵖ C) → sndᵖ ∘ᵖ ⟨ f , g ⟩ᵖ ≡ g
⟨⟩ᵖ-sndᵖ f g = →ᵖ-ext (λ x → refl)

⟨⟩ᵖ-unique : ∀ {A B C} → (f : A →ᵖ B) → (g : A →ᵖ C) → (h : A →ᵖ B ×ᵖ C)
           → fstᵖ ∘ᵖ h ≡ f → sndᵖ ∘ᵖ h ≡ g → h ≡ ⟨ f , g ⟩ᵖ
⟨⟩ᵖ-unique f g h p q =
  →ᵖ-ext (λ x → cong₂ _,_ (cong (λ m → app m x) p) (cong (λ m → app m x) q))

-- Exponentials (pointwise, since the index is discrete)

infixr 22 _⇒ᵖ_

_⇒ᵖ_ : PSh → PSh → PSh
A ⇒ᵖ B = psh (λ w → carrier A w → carrier B w)

curryᵖ : ∀ {A B C} → A ×ᵖ B →ᵖ C → A →ᵖ B ⇒ᵖ C
curryᵖ f = pmap (λ a b → app f (a , b))

uncurryᵖ : ∀ {A B C} → A →ᵖ B ⇒ᵖ C → A ×ᵖ B →ᵖ C
uncurryᵖ f = pmap (λ { (a , b) → app f a b })

curryᵖ-nat : ∀ {A B C D} → (f : A →ᵖ B) → (g : B ×ᵖ C →ᵖ D)
           → curryᵖ (g ∘ᵖ ⟨ f ∘ᵖ fstᵖ , idᵖ ∘ᵖ sndᵖ ⟩ᵖ) ≡ curryᵖ g ∘ᵖ f
curryᵖ-nat f g = →ᵖ-ext (λ x → refl)

uncurryᵖ-nat : ∀ {A B C D} → (f : A →ᵖ B) → (g : B →ᵖ C ⇒ᵖ D)
             → uncurryᵖ (g ∘ᵖ f) ≡ uncurryᵖ g ∘ᵖ ⟨ f ∘ᵖ fstᵖ , idᵖ ∘ᵖ sndᵖ ⟩ᵖ
uncurryᵖ-nat f g = →ᵖ-ext (λ { (a , b) → refl })

curryᵖ-uncurryᵖ-iso : ∀ {A B C} → (f : A ×ᵖ B →ᵖ C) → uncurryᵖ (curryᵖ f) ≡ f
curryᵖ-uncurryᵖ-iso f = →ᵖ-ext (λ { (a , b) → refl })

uncurryᵖ-curryᵖ-iso : ∀ {A B C} → (f : A →ᵖ B ⇒ᵖ C) → curryᵖ (uncurryᵖ f) ≡ f
uncurryᵖ-curryᵖ-iso f = →ᵖ-ext (λ a → refl)

-- Packaging presheaves up as a cartesian closed category

PShCat : Category
PShCat = record
  { Obj          = PSh
  ; _→ᵐ_         = _→ᵖ_
  ; idᵐ          = idᵖ
  ; _∘ᵐ_         = _∘ᵖ_
  ; ∘ᵐ-identityˡ = λ f → refl
  ; ∘ᵐ-identityʳ = λ f → refl
  ; ∘ᵐ-assoc     = λ h g f → refl
  ; 𝟙ᵐ           = 𝟙ᵖ
  ; terminalᵐ    = terminalᵖ
  ; terminalᵐ-unique = terminalᵖ-unique
  ; 𝟘ᵐ           = 𝟘ᵖ
  ; initialᵐ     = initialᵖ
  ; initialᵐ-unique = initialᵖ-unique
  ; _×ᵐ_         = _×ᵖ_
  ; fstᵐ         = fstᵖ
  ; sndᵐ         = sndᵖ
  ; ⟨_,_⟩ᵐ       = ⟨_,_⟩ᵖ
  ; ⟨⟩ᵐ-fstᵐ     = ⟨⟩ᵖ-fstᵖ
  ; ⟨⟩ᵐ-sndᵐ     = ⟨⟩ᵖ-sndᵖ
  ; ⟨⟩ᵐ-unique   = ⟨⟩ᵖ-unique
  ; _⇒ᵐ_         = _⇒ᵖ_
  ; curryᵐ       = curryᵖ
  ; curryᵐ-nat   = curryᵖ-nat
  ; uncurryᵐ     = uncurryᵖ
  ; uncurryᵐ-nat = uncurryᵖ-nat
  ; curryᵐ-uncurryᵐ-iso = curryᵖ-uncurryᵖ-iso
  ; uncurryᵐ-curryᵐ-iso = uncurryᵖ-curryᵖ-iso
  }
