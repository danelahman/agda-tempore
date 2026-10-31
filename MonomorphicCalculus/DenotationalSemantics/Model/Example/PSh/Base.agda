---------------------------------------------------------------------------
-- Setoid-valued unit-monotone presheaves over the worlds `W`.           --
--                                                                       --
-- A presheaf is a covariant functor over the preorder of worlds         --
-- `(W, ⊑[ 𝟏ᵣ ])` given by unit-graded accessibility, valued in          --
-- setoids: each world carries a set `carrier` together with a per-      --
-- world equivalence `_≈_`. The functorial `transport` moves elements    --
-- along unit-accessibility, respecting `_≈_` and satisfying the         --
-- reflexivity and transitivity laws up to `_≈_` (a genuine preorder,    --
-- since `𝟏ᵣ ·ᵣ 𝟏ᵣ ≡ 𝟏ᵣ`).                                               --
--                                                                       --
-- A morphism is a natural transformation whose components respect       --
-- `_≈_`. Morphism equality is pointwise target-`_≈_`; every categorical --
-- law is stated up to this equality, which is what lets later           --
-- constructions (a possibility modality realised as a coend) satisfy    --
-- their functor laws.                                                   --
--                                                                       --
-- Because unit-accessibility witnesses are proof irrelevant, transport  --
-- along any witness is determined up to `_≈_` by the source and target  --
-- worlds alone; this discharges the functor laws.                       --
---------------------------------------------------------------------------

open import Grades.Base
open import MonomorphicCalculus.DenotationalSemantics.Model.World

module MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base (GS : GradeSystem) (Wld : World (GradeSystem.RGrade GS)) where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.Category

open GradeSystemInterface GS
open World Wld

-- Composition of unit-accessibility, a genuine preorder since
-- `𝟏ᵣ ·ᵣ 𝟏ᵣ ≡ 𝟏ᵣ`.

⊑ᵘ-trans : ∀ {w w' w''} → w ⊑[ 𝟏ᵣ ] w' → w' ⊑[ 𝟏ᵣ ] w'' → w ⊑[ 𝟏ᵣ ] w''
⊑ᵘ-trans p q = ⊑-mono (≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ 𝟏ᵣ)) (⊑-trans p q)

-- Setoid-valued unit-monotone presheaves over the worlds

record PSh : Set₁ where
  constructor psh
  field
    -- object map / carrier of the presheaf, per world
    carrier    : W → Set
    -- per-world equivalence on the carrier
    _≈_        : ∀ {w} → carrier w → carrier w → Set
    ≈-refl     : ∀ {w} {x : carrier w} → x ≈ x
    ≈-sym      : ∀ {w} {x y : carrier w} → x ≈ y → y ≈ x
    ≈-trans    : ∀ {w} {x y z : carrier w} → x ≈ y → y ≈ z → x ≈ z
    -- functorial transport along unit-accessibility, respecting `_≈_`
    transport  : ∀ {w w'} → w ⊑[ 𝟏ᵣ ] w' → carrier w → carrier w'
    transport-cong  : ∀ {w w'} (p : w ⊑[ 𝟏ᵣ ] w') {x y : carrier w}
                    → x ≈ y → transport p x ≈ transport p y
    transport-refl  : ∀ {w} (x : carrier w) → transport ⊑-refl x ≈ x
    transport-trans : ∀ {w w' w''} (p : w ⊑[ 𝟏ᵣ ] w') (q : w' ⊑[ 𝟏ᵣ ] w'') (x : carrier w)
                    → transport (⊑ᵘ-trans p q) x ≈ transport q (transport p x)

open PSh public

-- Transport is independent of the accessibility witness (up to `≈`),
-- since witnesses are proof irrelevant.

transport-irr : ∀ {A : PSh} {w w'} (p q : w ⊑[ 𝟏ᵣ ] w') (x : carrier A w)
              → _≈_ A (transport A p x) (transport A q x)
transport-irr {A} p q x with ⊑-irrelevant p q
... | refl = ≈-refl A

-- Maps of presheaves: natural transformations respecting `_≈_`.

record _→ᵖ_ (A B : PSh) : Set where
  constructor pmap
  field
    app      : ∀ {w} → carrier A w → carrier B w
    app-cong : ∀ {w} {x y : carrier A w} → _≈_ A x y → _≈_ B (app x) (app y)
    nat      : ∀ {w w'} (p : w ⊑[ 𝟏ᵣ ] w') (x : carrier A w)
             → _≈_ B (app (transport A p x)) (transport B p (app x))

open _→ᵖ_ public

infix 20 _→ᵖ_

-- Equality of presheaf maps is pointwise target-`≈`.

_≈ᵖ_ : ∀ {A B} (f g : A →ᵖ B) → Set
_≈ᵖ_ {A} {B} f g = ∀ {w} (x : carrier A w) → _≈_ B (app f x) (app g x)

infix 4 _≈ᵖ_

≈ᵖ-refl : ∀ {A B} {f : A →ᵖ B} → f ≈ᵖ f
≈ᵖ-refl {B = B} x = ≈-refl B

≈ᵖ-sym : ∀ {A B} {f g : A →ᵖ B} → f ≈ᵖ g → g ≈ᵖ f
≈ᵖ-sym {B = B} p x = ≈-sym B (p x)

≈ᵖ-trans : ∀ {A B} {f g h : A →ᵖ B} → f ≈ᵖ g → g ≈ᵖ h → f ≈ᵖ h
≈ᵖ-trans {B = B} p q x = ≈-trans B (p x) (q x)

-- Identity and composition of maps

idᵖ : ∀ {A} → A →ᵖ A
idᵖ {A} = pmap (λ x → x) (λ e → e) (λ p x → ≈-refl A)

_∘ᵖ_ : ∀ {A B C} → B →ᵖ C → A →ᵖ B → A →ᵖ C
_∘ᵖ_ {A} {B} {C} g f = pmap
  (λ x → app g (app f x))
  (λ e → app-cong g (app-cong f e))
  (λ p x → ≈-trans C (app-cong g (nat f p x)) (nat g p (app f x)))

infixr 9 _∘ᵖ_

∘ᵖ-congˡ : ∀ {A B C} {g g' : B →ᵖ C} {f : A →ᵖ B} → g ≈ᵖ g' → g ∘ᵖ f ≈ᵖ g' ∘ᵖ f
∘ᵖ-congˡ {f = f} p x = p (app f x)

∘ᵖ-congʳ : ∀ {A B C} {g : B →ᵖ C} {f f' : A →ᵖ B} → f ≈ᵖ f' → g ∘ᵖ f ≈ᵖ g ∘ᵖ f'
∘ᵖ-congʳ {g = g} p x = app-cong g (p x)

∘ᵖ-identityˡ : ∀ {A B} (f : A →ᵖ B) → idᵖ ∘ᵖ f ≈ᵖ f
∘ᵖ-identityˡ {B = B} f x = ≈-refl B

∘ᵖ-identityʳ : ∀ {A B} (f : A →ᵖ B) → f ∘ᵖ idᵖ ≈ᵖ f
∘ᵖ-identityʳ {B = B} f x = ≈-refl B

∘ᵖ-assoc : ∀ {A B C D} (h : C →ᵖ D) (g : B →ᵖ C) (f : A →ᵖ B)
         → (h ∘ᵖ g) ∘ᵖ f ≈ᵖ h ∘ᵖ (g ∘ᵖ f)
∘ᵖ-assoc {D = D} h g f x = ≈-refl D

-- Cartesian closed structure

-- Terminal object

𝟙ᵖ : PSh
𝟙ᵖ = record
  { carrier         = λ _ → ⊤
  ; _≈_             = λ _ _ → ⊤
  ; ≈-refl          = tt
  ; ≈-sym           = λ _ → tt
  ; ≈-trans         = λ _ _ → tt
  ; transport       = λ _ _ → tt
  ; transport-cong  = λ _ _ → tt
  ; transport-refl  = λ _ → tt
  ; transport-trans = λ _ _ _ → tt
  }

terminalᵖ : ∀ {A} → A →ᵖ 𝟙ᵖ
terminalᵖ = pmap (λ _ → tt) (λ _ → tt) (λ p x → tt)

terminalᵖ-unique : ∀ {A} {f : A →ᵖ 𝟙ᵖ} → f ≈ᵖ terminalᵖ
terminalᵖ-unique x = tt

-- Initial object

𝟘ᵖ : PSh
𝟘ᵖ = record
  { carrier         = λ _ → ⊥
  ; _≈_             = λ _ _ → ⊥
  ; ≈-refl          = λ {w} {x} → x
  ; ≈-sym           = λ e → e
  ; ≈-trans         = λ e _ → e
  ; transport       = λ _ x → x
  ; transport-cong  = λ _ e → e
  ; transport-refl  = λ x → x
  ; transport-trans = λ _ _ x → x
  }

initialᵖ : ∀ {A} → 𝟘ᵖ →ᵖ A
initialᵖ = pmap (λ ()) (λ ()) (λ p ())

initialᵖ-unique : ∀ {A} {f : 𝟘ᵖ →ᵖ A} → f ≈ᵖ initialᵖ
initialᵖ-unique ()

-- The initial presheaf is strict: its carrier is empty at every world, so an
-- `X →ᵖ 𝟘ᵖ` empties `X`'s carriers too.

𝟘ᵖ-strict : ∀ {X A} → X →ᵖ 𝟘ᵖ → (f g : X →ᵖ A) → f ≈ᵖ g
𝟘ᵖ-strict z f g x = ⊥-elim (app z x)

-- Binary products

infixr 23 _×ᵖ_

_×ᵖ_ : PSh → PSh → PSh
A ×ᵖ B = record
  { carrier         = λ w → carrier A w × carrier B w
  ; _≈_             = λ x y → _≈_ A (proj₁ x) (proj₁ y) × _≈_ B (proj₂ x) (proj₂ y)
  ; ≈-refl          = ≈-refl A , ≈-refl B
  ; ≈-sym           = λ e → ≈-sym A (proj₁ e) , ≈-sym B (proj₂ e)
  ; ≈-trans         = λ e e' → ≈-trans A (proj₁ e) (proj₁ e') , ≈-trans B (proj₂ e) (proj₂ e')
  ; transport       = λ p x → transport A p (proj₁ x) , transport B p (proj₂ x)
  ; transport-cong  = λ p e → transport-cong A p (proj₁ e) , transport-cong B p (proj₂ e)
  ; transport-refl  = λ x → transport-refl A (proj₁ x) , transport-refl B (proj₂ x)
  ; transport-trans = λ p q x → transport-trans A p q (proj₁ x) , transport-trans B p q (proj₂ x)
  }

fstᵖ : ∀ {A B} → A ×ᵖ B →ᵖ A
fstᵖ {A} = pmap proj₁ (λ e → proj₁ e) (λ p x → ≈-refl A)

sndᵖ : ∀ {A B} → A ×ᵖ B →ᵖ B
sndᵖ {A} {B} = pmap proj₂ (λ e → proj₂ e) (λ p x → ≈-refl B)

⟨_,_⟩ᵖ : ∀ {A B C} → A →ᵖ B → A →ᵖ C → A →ᵖ B ×ᵖ C
⟨ f , g ⟩ᵖ = pmap
  (λ x → app f x , app g x)
  (λ e → app-cong f e , app-cong g e)
  (λ p x → nat f p x , nat g p x)

⟨_,_⟩ᵖ-cong : ∀ {A B C} {f f' : A →ᵖ B} {g g' : A →ᵖ C}
            → f ≈ᵖ f' → g ≈ᵖ g' → ⟨ f , g ⟩ᵖ ≈ᵖ ⟨ f' , g' ⟩ᵖ
⟨ pf , pg ⟩ᵖ-cong x = pf x , pg x

⟨⟩ᵖ-fstᵖ : ∀ {A B C} → (f : A →ᵖ B) → (g : A →ᵖ C) → fstᵖ ∘ᵖ ⟨ f , g ⟩ᵖ ≈ᵖ f
⟨⟩ᵖ-fstᵖ {B = B} f g x = ≈-refl B

⟨⟩ᵖ-sndᵖ : ∀ {A B C} → (f : A →ᵖ B) → (g : A →ᵖ C) → sndᵖ ∘ᵖ ⟨ f , g ⟩ᵖ ≈ᵖ g
⟨⟩ᵖ-sndᵖ {C = C} f g x = ≈-refl C

⟨⟩ᵖ-unique : ∀ {A B C} → (f : A →ᵖ B) → (g : A →ᵖ C) → (h : A →ᵖ B ×ᵖ C)
           → fstᵖ ∘ᵖ h ≈ᵖ f → sndᵖ ∘ᵖ h ≈ᵖ g → h ≈ᵖ ⟨ f , g ⟩ᵖ
⟨⟩ᵖ-unique f g h p q x = p x , q x

-- Binary coproducts
--
-- Pointwise disjoint union: elements are related only within one summand, and
-- transport acts summandwise.

_≈⁺_ : ∀ {A B : PSh} {w} → carrier A w ⊎ carrier B w → carrier A w ⊎ carrier B w → Set
_≈⁺_ {A}     (inj₁ x) (inj₁ y) = _≈_ A x y
_≈⁺_ {B = B} (inj₂ x) (inj₂ y) = _≈_ B x y
_≈⁺_         (inj₁ _) (inj₂ _) = ⊥
_≈⁺_         (inj₂ _) (inj₁ _) = ⊥

infixr 22 _+ᵖ_

_+ᵖ_ : PSh → PSh → PSh
A +ᵖ B = record
  { carrier         = λ w → carrier A w ⊎ carrier B w
  ; _≈_             = _≈⁺_ {A} {B}
  ; ≈-refl          = λ {w} {x} → refl⁺ x
  ; ≈-sym           = λ {w} {x} {y} → sym⁺ x y
  ; ≈-trans         = λ {w} {x} {y} {z} → trans⁺ x y z
  ; transport       = tr⁺
  ; transport-cong  = λ p {x} {y} → tr-cong⁺ p x y
  ; transport-refl  = tr-refl⁺
  ; transport-trans = tr-trans⁺
  }
  where
    refl⁺ : ∀ {w} (x : carrier A w ⊎ carrier B w) → _≈⁺_ {A} {B} x x
    refl⁺ (inj₁ x) = ≈-refl A
    refl⁺ (inj₂ x) = ≈-refl B

    sym⁺ : ∀ {w} (x y : carrier A w ⊎ carrier B w)
         → _≈⁺_ {A} {B} x y → _≈⁺_ {A} {B} y x
    sym⁺ (inj₁ x) (inj₁ y) e = ≈-sym A e
    sym⁺ (inj₂ x) (inj₂ y) e = ≈-sym B e

    trans⁺ : ∀ {w} (x y z : carrier A w ⊎ carrier B w)
           → _≈⁺_ {A} {B} x y → _≈⁺_ {A} {B} y z → _≈⁺_ {A} {B} x z
    trans⁺ (inj₁ x) (inj₁ y) (inj₁ z) e e' = ≈-trans A e e'
    trans⁺ (inj₂ x) (inj₂ y) (inj₂ z) e e' = ≈-trans B e e'

    tr⁺ : ∀ {w w'} → w ⊑[ 𝟏ᵣ ] w' → carrier A w ⊎ carrier B w → carrier A w' ⊎ carrier B w'
    tr⁺ p (inj₁ x) = inj₁ (transport A p x)
    tr⁺ p (inj₂ x) = inj₂ (transport B p x)

    tr-cong⁺ : ∀ {w w'} (p : w ⊑[ 𝟏ᵣ ] w') (x y : carrier A w ⊎ carrier B w)
             → _≈⁺_ {A} {B} x y → _≈⁺_ {A} {B} (tr⁺ p x) (tr⁺ p y)
    tr-cong⁺ p (inj₁ x) (inj₁ y) e = transport-cong A p e
    tr-cong⁺ p (inj₂ x) (inj₂ y) e = transport-cong B p e

    tr-refl⁺ : ∀ {w} (x : carrier A w ⊎ carrier B w) → _≈⁺_ {A} {B} (tr⁺ ⊑-refl x) x
    tr-refl⁺ (inj₁ x) = transport-refl A x
    tr-refl⁺ (inj₂ x) = transport-refl B x

    tr-trans⁺ : ∀ {w w' w''} (p : w ⊑[ 𝟏ᵣ ] w') (q : w' ⊑[ 𝟏ᵣ ] w'')
                (x : carrier A w ⊎ carrier B w)
              → _≈⁺_ {A} {B} (tr⁺ (⊑ᵘ-trans p q) x) (tr⁺ q (tr⁺ p x))
    tr-trans⁺ p q (inj₁ x) = transport-trans A p q x
    tr-trans⁺ p q (inj₂ x) = transport-trans B p q x

inlᵖ : ∀ {A B} → A →ᵖ A +ᵖ B
inlᵖ {A} = pmap inj₁ (λ e → e) (λ p x → ≈-refl A)

inrᵖ : ∀ {A B} → B →ᵖ A +ᵖ B
inrᵖ {B = B} = pmap inj₂ (λ e → e) (λ p x → ≈-refl B)

[_,_]ᵖ : ∀ {A B C} → A →ᵖ C → B →ᵖ C → A +ᵖ B →ᵖ C
[_,_]ᵖ {A} {B} {C} f g = pmap
  copair
  (λ {w} {x} {y} → copair-cong x y)
  copair-nat
  where
    copair : ∀ {w} → carrier A w ⊎ carrier B w → carrier C w
    copair (inj₁ x) = app f x
    copair (inj₂ y) = app g y

    copair-cong : ∀ {w} (x y : carrier A w ⊎ carrier B w)
                → _≈⁺_ {A} {B} x y → _≈_ C (copair x) (copair y)
    copair-cong (inj₁ x) (inj₁ y) e = app-cong f e
    copair-cong (inj₂ x) (inj₂ y) e = app-cong g e

    copair-nat : ∀ {w w'} (p : w ⊑[ 𝟏ᵣ ] w') (x : carrier A w ⊎ carrier B w)
               → _≈_ C (copair (transport (A +ᵖ B) p x)) (transport C p (copair x))
    copair-nat p (inj₁ x) = nat f p x
    copair-nat p (inj₂ x) = nat g p x

[_,_]ᵖ-cong : ∀ {A B C} {f f' : A →ᵖ C} {g g' : B →ᵖ C}
            → f ≈ᵖ f' → g ≈ᵖ g' → [ f , g ]ᵖ ≈ᵖ [ f' , g' ]ᵖ
[ pf , pg ]ᵖ-cong (inj₁ x) = pf x
[ pf , pg ]ᵖ-cong (inj₂ x) = pg x

[]ᵖ-inlᵖ : ∀ {A B C} → (f : A →ᵖ C) → (g : B →ᵖ C) → [ f , g ]ᵖ ∘ᵖ inlᵖ ≈ᵖ f
[]ᵖ-inlᵖ {C = C} f g x = ≈-refl C

[]ᵖ-inrᵖ : ∀ {A B C} → (f : A →ᵖ C) → (g : B →ᵖ C) → [ f , g ]ᵖ ∘ᵖ inrᵖ ≈ᵖ g
[]ᵖ-inrᵖ {C = C} f g x = ≈-refl C

[]ᵖ-unique : ∀ {A B C} → (f : A →ᵖ C) → (g : B →ᵖ C) → (h : A +ᵖ B →ᵖ C)
           → h ∘ᵖ inlᵖ ≈ᵖ f → h ∘ᵖ inrᵖ ≈ᵖ g → h ≈ᵖ [ f , g ]ᵖ
[]ᵖ-unique f g h p q (inj₁ x) = p x
[]ᵖ-unique f g h p q (inj₂ x) = q x

-- Boolean object
--
-- The constant presheaf on `Data.Bool`: propositional equality per world and
-- identity transport. Constancy makes the eliminator a presheaf map (its `nat`
-- obligation rewrites the scrutinee away) and makes `𝔹ᵖ` eternal
-- (`Modality.Eternal`).

𝔹ᵖ : PSh
𝔹ᵖ = record
  { carrier         = λ _ → Bool
  ; _≈_             = _≡_
  ; ≈-refl          = refl
  ; ≈-sym           = sym
  ; ≈-trans         = trans
  ; transport       = λ _ x → x
  ; transport-cong  = λ _ e → e
  ; transport-refl  = λ _ → refl
  ; transport-trans = λ _ _ _ → refl
  }

trueᵖ : 𝟙ᵖ →ᵖ 𝔹ᵖ
trueᵖ = pmap (λ _ → true) (λ _ → refl) (λ _ _ → refl)

falseᵖ : 𝟙ᵖ →ᵖ 𝔹ᵖ
falseᵖ = pmap (λ _ → false) (λ _ → refl) (λ _ _ → refl)

-- Both obligations follow the same shape: case on the scrutinee's value
-- through a helper, then move that value along the equation the scrutinee's
-- own `app-cong`/`nat` supplies.

ifᵖ : ∀ {X A} → X →ᵖ 𝔹ᵖ → X →ᵖ A → X →ᵖ A → X →ᵖ A
ifᵖ {X} {A} b f g = pmap
  (λ x → if app b x then app f x else app g x)
  (λ {w} {x} {y} e →
     subst (λ c → _≈_ A (if app b x then app f x else app g x)
                        (if c then app f y else app g y))
           (app-cong b e)
           (go-cong e (app b x)))
  (λ {w} {w'} p x →
     subst (λ c → _≈_ A (if c then app f (transport X p x)
                              else app g (transport X p x))
                        (transport A p (if app b x then app f x else app g x)))
           (sym (nat b p x))
           (go-nat p x (app b x)))
  where
    go-cong : ∀ {w} {x y : carrier X w} → _≈_ X x y → (c : Bool)
            → _≈_ A (if c then app f x else app g x)
                    (if c then app f y else app g y)
    go-cong e true  = app-cong f e
    go-cong e false = app-cong g e

    go-nat : ∀ {w w'} → (p : w ⊑[ 𝟏ᵣ ] w') → (x : carrier X w) → (c : Bool)
           → _≈_ A (if c then app f (transport X p x) else app g (transport X p x))
                   (transport A p (if c then app f x else app g x))
    go-nat p x true  = nat f p x
    go-nat p x false = nat g p x

ifᵖ-cong : ∀ {X A} {b b' : X →ᵖ 𝔹ᵖ} {f f' g g' : X →ᵖ A}
         → b ≈ᵖ b' → f ≈ᵖ f' → g ≈ᵖ g'
         → ifᵖ b f g ≈ᵖ ifᵖ b' f' g'
ifᵖ-cong {X} {A} {b} {b'} {f} {f'} {g} {g'} pb pf pg {w} x =
  subst (λ c → _≈_ A (if app b x then app f x else app g x)
                     (if c then app f' x else app g' x))
        (pb x)
        (go (app b x))
  where
    go : (c : Bool) → _≈_ A (if c then app f x else app g x)
                            (if c then app f' x else app g' x)
    go true  = pf x
    go false = pg x

ifᵖ-true : ∀ {X A} → (f g : X →ᵖ A) → ifᵖ (trueᵖ ∘ᵖ terminalᵖ) f g ≈ᵖ f
ifᵖ-true {A = A} f g x = ≈-refl A

ifᵖ-false : ∀ {X A} → (f g : X →ᵖ A) → ifᵖ (falseᵖ ∘ᵖ terminalᵖ) f g ≈ᵖ g
ifᵖ-false {A = A} f g x = ≈-refl A

ifᵖ-∘ : ∀ {X Y A} → (b : X →ᵖ 𝔹ᵖ) → (f g : X →ᵖ A) → (h : Y →ᵖ X)
      → ifᵖ b f g ∘ᵖ h ≈ᵖ ifᵖ (b ∘ᵖ h) (f ∘ᵖ h) (g ∘ᵖ h)
ifᵖ-∘ {A = A} b f g h x = ≈-refl A

-- A map out of `X ×ᵖ 𝔹ᵖ` is determined by its two instances: at each world the
-- second component is a boolean, so the case split is on that value.

ifᵖ-η : ∀ {X A} → (b : X →ᵖ 𝔹ᵖ) → (m : X ×ᵖ 𝔹ᵖ →ᵖ A)
      → m ∘ᵖ ⟨ idᵖ , b ⟩ᵖ
      ≈ᵖ ifᵖ b (m ∘ᵖ ⟨ idᵖ , trueᵖ  ∘ᵖ terminalᵖ ⟩ᵖ)
               (m ∘ᵖ ⟨ idᵖ , falseᵖ ∘ᵖ terminalᵖ ⟩ᵖ)
ifᵖ-η {X} {A} b m {w} x = go (app b x)
  where
    go : (c : Bool)
       → _≈_ A (app m (x , c))
               (if c then app m (x , true) else app m (x , false))
    go true  = ≈-refl A
    go false = ≈-refl A

-- Natural numbers object
--
-- The constant presheaf on `Data.Nat`, like `𝔹ᵖ`. Iteration recurses on the
-- number at each world; its laws are inductions on it.

ℕᵖ : PSh
ℕᵖ = record
  { carrier         = λ _ → ℕ
  ; _≈_             = _≡_
  ; ≈-refl          = refl
  ; ≈-sym           = sym
  ; ≈-trans         = trans
  ; transport       = λ _ x → x
  ; transport-cong  = λ _ e → e
  ; transport-refl  = λ _ → refl
  ; transport-trans = λ _ _ _ → refl
  }

zeroᵖ : 𝟙ᵖ →ᵖ ℕᵖ
zeroᵖ = pmap (λ _ → zero) (λ _ → refl) (λ _ _ → refl)

succᵖ : ℕᵖ →ᵖ ℕᵖ
succᵖ = pmap suc (cong suc) (λ _ _ → refl)

iterᵖ : ∀ {A} → 𝟙ᵖ →ᵖ A → A →ᵖ A → ℕᵖ →ᵖ A
iterᵖ {A} a f = pmap (λ n → go n) (λ { refl → ≈-refl A }) go-nat
  where
    go : ∀ {w} → ℕ → carrier A w
    go zero    = app a tt
    go (suc n) = app f (go n)

    go-nat : ∀ {w w'} (p : w ⊑[ 𝟏ᵣ ] w') (n : ℕ)
           → _≈_ A (go n) (transport A p (go n))
    go-nat p zero    = nat a p tt
    go-nat p (suc n) = ≈-trans A (app-cong f (go-nat p n)) (nat f p (go n))

iterᵖ-cong : ∀ {A} {a a' : 𝟙ᵖ →ᵖ A} {f f' : A →ᵖ A}
           → a ≈ᵖ a' → f ≈ᵖ f' → iterᵖ a f ≈ᵖ iterᵖ a' f'
iterᵖ-cong {A} {a} {a'} {f} {f'} pa pf zero    = pa tt
iterᵖ-cong {A} {a} {a'} {f} {f'} pa pf (suc n) =
  ≈-trans A (app-cong f (iterᵖ-cong {A} {a} {a'} {f} {f'} pa pf n)) (pf _)

iterᵖ-zero : ∀ {A} → (a : 𝟙ᵖ →ᵖ A) → (f : A →ᵖ A) → iterᵖ a f ∘ᵖ zeroᵖ ≈ᵖ a
iterᵖ-zero {A} a f x = ≈-refl A

iterᵖ-succ : ∀ {A} → (a : 𝟙ᵖ →ᵖ A) → (f : A →ᵖ A)
           → iterᵖ a f ∘ᵖ succᵖ ≈ᵖ f ∘ᵖ iterᵖ a f
iterᵖ-succ {A} a f x = ≈-refl A

iterᵖ-unique : ∀ {A} → (a : 𝟙ᵖ →ᵖ A) → (f : A →ᵖ A) → (h : ℕᵖ →ᵖ A)
             → h ∘ᵖ zeroᵖ ≈ᵖ a → h ∘ᵖ succᵖ ≈ᵖ f ∘ᵖ h → h ≈ᵖ iterᵖ a f
iterᵖ-unique {A} a f h p q zero    = p tt
iterᵖ-unique {A} a f h p q (suc n) =
  ≈-trans A (q n) (app-cong f (iterᵖ-unique a f h p q n))

-- List object
--
-- Pointwise lists: elements related elementwise, transport acting on each
-- element. The fold recurses on the list at each world; its laws are
-- inductions on it.

module _ (A : PSh) where

  _≈ᴸ_ : ∀ {w} → List (carrier A w) → List (carrier A w) → Set
  []       ≈ᴸ []       = ⊤
  (x ∷ xs) ≈ᴸ (y ∷ ys) = _≈_ A x y × xs ≈ᴸ ys
  []       ≈ᴸ (_ ∷ _)  = ⊥
  (_ ∷ _)  ≈ᴸ []       = ⊥

  reflᴸ : ∀ {w} (xs : List (carrier A w)) → xs ≈ᴸ xs
  reflᴸ []       = tt
  reflᴸ (x ∷ xs) = ≈-refl A , reflᴸ xs

  symᴸ : ∀ {w} (xs ys : List (carrier A w)) → xs ≈ᴸ ys → ys ≈ᴸ xs
  symᴸ []       []       e        = tt
  symᴸ (x ∷ xs) (y ∷ ys) (e , es) = ≈-sym A e , symᴸ xs ys es

  transᴸ : ∀ {w} (xs ys zs : List (carrier A w)) → xs ≈ᴸ ys → ys ≈ᴸ zs → xs ≈ᴸ zs
  transᴸ []       []       []       e        e'         = tt
  transᴸ (x ∷ xs) (y ∷ ys) (z ∷ zs) (e , es) (e' , es') =
    ≈-trans A e e' , transᴸ xs ys zs es es'

  trᴸ : ∀ {w w'} → w ⊑[ 𝟏ᵣ ] w' → List (carrier A w) → List (carrier A w')
  trᴸ p = map (transport A p)

  tr-congᴸ : ∀ {w w'} (p : w ⊑[ 𝟏ᵣ ] w') (xs ys : List (carrier A w))
           → xs ≈ᴸ ys → trᴸ p xs ≈ᴸ trᴸ p ys
  tr-congᴸ p []       []       e        = tt
  tr-congᴸ p (x ∷ xs) (y ∷ ys) (e , es) = transport-cong A p e , tr-congᴸ p xs ys es

  tr-reflᴸ : ∀ {w} (xs : List (carrier A w)) → trᴸ ⊑-refl xs ≈ᴸ xs
  tr-reflᴸ []       = tt
  tr-reflᴸ (x ∷ xs) = transport-refl A x , tr-reflᴸ xs

  tr-transᴸ : ∀ {w w' w''} (p : w ⊑[ 𝟏ᵣ ] w') (q : w' ⊑[ 𝟏ᵣ ] w'')
              (xs : List (carrier A w))
            → trᴸ (⊑ᵘ-trans p q) xs ≈ᴸ trᴸ q (trᴸ p xs)
  tr-transᴸ p q []       = tt
  tr-transᴸ p q (x ∷ xs) = transport-trans A p q x , tr-transᴸ p q xs

  Listᵖ : PSh
  Listᵖ = record
    { carrier         = λ w → List (carrier A w)
    ; _≈_             = _≈ᴸ_
    ; ≈-refl          = λ {w} {x} → reflᴸ x
    ; ≈-sym           = λ {w} {x} {y} → symᴸ x y
    ; ≈-trans         = λ {w} {x} {y} {z} → transᴸ x y z
    ; transport       = trᴸ
    ; transport-cong  = λ p {x} {y} → tr-congᴸ p x y
    ; transport-refl  = tr-reflᴸ
    ; transport-trans = tr-transᴸ
    }

nilᵖ : ∀ {A} → 𝟙ᵖ →ᵖ Listᵖ A
nilᵖ = pmap (λ _ → []) (λ _ → tt) (λ _ _ → tt)

consᵖ : ∀ {A} → A ×ᵖ Listᵖ A →ᵖ Listᵖ A
consᵖ {A} = pmap (λ x → proj₁ x ∷ proj₂ x) (λ e → e)
                 (λ p x → ≈-refl A , reflᴸ A (trᴸ A p (proj₂ x)))

foldᵖ : ∀ {A C} → 𝟙ᵖ →ᵖ C → A ×ᵖ C →ᵖ C → Listᵖ A →ᵖ C
foldᵖ {A} {C} a f = pmap go go-cong go-nat
  where
    go : ∀ {w} → List (carrier A w) → carrier C w
    go []       = app a tt
    go (x ∷ xs) = app f (x , go xs)

    go-cong : ∀ {w} {xs ys : List (carrier A w)} → _≈ᴸ_ A xs ys → _≈_ C (go xs) (go ys)
    go-cong {xs = []}     {[]}     e        = ≈-refl C
    go-cong {xs = x ∷ xs} {y ∷ ys} (e , es) = app-cong f (e , go-cong es)

    go-nat : ∀ {w w'} (p : w ⊑[ 𝟏ᵣ ] w') (xs : List (carrier A w))
           → _≈_ C (go (trᴸ A p xs)) (transport C p (go xs))
    go-nat p []       = nat a p tt
    go-nat p (x ∷ xs) = ≈-trans C (app-cong f (≈-refl A , go-nat p xs)) (nat f p (x , go xs))

foldᵖ-cong : ∀ {A C} {a a' : 𝟙ᵖ →ᵖ C} {f f' : A ×ᵖ C →ᵖ C}
           → a ≈ᵖ a' → f ≈ᵖ f' → foldᵖ a f ≈ᵖ foldᵖ a' f'
foldᵖ-cong                         pa pf []       = pa tt
foldᵖ-cong {A} {C} {a} {a'} {f} {f'} pa pf (x ∷ xs) =
  ≈-trans C (app-cong f (≈-refl A , foldᵖ-cong {A} {C} {a} {a'} {f} {f'} pa pf xs)) (pf _)

foldᵖ-nil : ∀ {A C} → (a : 𝟙ᵖ →ᵖ C) → (f : A ×ᵖ C →ᵖ C) → foldᵖ a f ∘ᵖ nilᵖ ≈ᵖ a
foldᵖ-nil {C = C} a f x = ≈-refl C

foldᵖ-cons : ∀ {A C} → (a : 𝟙ᵖ →ᵖ C) → (f : A ×ᵖ C →ᵖ C)
           → foldᵖ a f ∘ᵖ consᵖ ≈ᵖ f ∘ᵖ ⟨ idᵖ ∘ᵖ fstᵖ , foldᵖ a f ∘ᵖ sndᵖ ⟩ᵖ
foldᵖ-cons {C = C} a f x = ≈-refl C

foldᵖ-unique : ∀ {A C} → (a : 𝟙ᵖ →ᵖ C) → (f : A ×ᵖ C →ᵖ C) → (h : Listᵖ A →ᵖ C)
             → h ∘ᵖ nilᵖ ≈ᵖ a → h ∘ᵖ consᵖ ≈ᵖ f ∘ᵖ ⟨ idᵖ ∘ᵖ fstᵖ , h ∘ᵖ sndᵖ ⟩ᵖ
             → h ≈ᵖ foldᵖ a f
foldᵖ-unique {A} {C} a f h p q []       = p tt
foldᵖ-unique {A} {C} a f h p q (x ∷ xs) =
  ≈-trans C (q (x , xs)) (app-cong f (≈-refl A , foldᵖ-unique a f h p q xs))

-- Kripke exponentials
--
-- An element of the exponential `A ⇒ᵖ B` at a world `w` is a Kripke
-- function: a family of maps `carrier A w' → carrier B w'` for every
-- unit-accessible `w'`, respecting `_≈_` and commuting with the
-- transports of `A` and `B` up to `_≈_`. Bundling the congruence and
-- naturality witnesses is what makes `uncurryᵖ` a genuine map of
-- presheaves.

record _⇒ᶜ_ (A B : PSh) (w : W) : Set where
  constructor mk⇒
  field
    fun      : ∀ {w'} → w ⊑[ 𝟏ᵣ ] w' → carrier A w' → carrier B w'
    fun-cong : ∀ {w'} (p : w ⊑[ 𝟏ᵣ ] w') {a a' : carrier A w'}
             → _≈_ A a a' → _≈_ B (fun p a) (fun p a')
    fun-nat  : ∀ {w' w''} (q : w ⊑[ 𝟏ᵣ ] w') (r : w' ⊑[ 𝟏ᵣ ] w'') (a : carrier A w')
             → _≈_ B (fun (⊑ᵘ-trans q r) (transport A r a)) (transport B r (fun q a))

open _⇒ᶜ_ public

infix 20 _⇒ᶜ_

-- The value of a Kripke function is independent of the accessibility
-- witness (up to `≈`), since witnesses are proof irrelevant.

fun-irr : ∀ {A B w w'} (F : (A ⇒ᶜ B) w) (p q : w ⊑[ 𝟏ᵣ ] w') (a : carrier A w')
        → _≈_ B (fun F p a) (fun F q a)
fun-irr {B = B} F p q a with ⊑-irrelevant p q
... | refl = ≈-refl B

infixr 22 _⇒ᵖ_

_⇒ᵖ_ : PSh → PSh → PSh
A ⇒ᵖ B = record
  { carrier         = A ⇒ᶜ B
  ; _≈_             = λ {w} F G → ∀ {w'} (p : w ⊑[ 𝟏ᵣ ] w') (a : carrier A w')
                    → _≈_ B (fun F p a) (fun G p a)
  ; ≈-refl          = λ p a → ≈-refl B
  ; ≈-sym           = λ e p a → ≈-sym B (e p a)
  ; ≈-trans         = λ e e' p a → ≈-trans B (e p a) (e' p a)
  ; transport       = λ p F → mk⇒
                        (λ q a → fun F (⊑ᵘ-trans p q) a)
                        (λ q e → fun-cong F (⊑ᵘ-trans p q) e)
                        (λ q r a → ≈-trans B
                          (fun-irr F (⊑ᵘ-trans p (⊑ᵘ-trans q r)) (⊑ᵘ-trans (⊑ᵘ-trans p q) r) (transport A r a))
                          (fun-nat F (⊑ᵘ-trans p q) r a))
  ; transport-cong  = λ p e q a → e (⊑ᵘ-trans p q) a
  ; transport-refl  = λ F p a → fun-irr F (⊑ᵘ-trans ⊑-refl p) p a
  ; transport-trans = λ p q F r a →
                        fun-irr F (⊑ᵘ-trans (⊑ᵘ-trans p q) r) (⊑ᵘ-trans p (⊑ᵘ-trans q r)) a
  }

curryᵖ : ∀ {A B C} → A ×ᵖ B →ᵖ C → A →ᵖ B ⇒ᵖ C
curryᵖ {A} {B} {C} f = pmap
  (λ a → mk⇒
    (λ p b → app f (transport A p a , b))
    (λ p e → app-cong f (≈-refl A , e))
    (λ q r b → ≈-trans C
      (app-cong f (transport-trans A q r a , ≈-refl B))
      (nat f r (transport A q a , b))))
  (λ e p b → app-cong f (transport-cong A p e , ≈-refl B))
  (λ p a q b → app-cong f (≈-sym A (transport-trans A p q a) , ≈-refl B))

uncurryᵖ : ∀ {A B C} → A →ᵖ B ⇒ᵖ C → A ×ᵖ B →ᵖ C
uncurryᵖ {A} {B} {C} g = pmap
  (λ x → fun (app g (proj₁ x)) ⊑-refl (proj₂ x))
  (λ {w} {x} {y} e → ≈-trans C
    (app-cong g (proj₁ e) ⊑-refl (proj₂ x))
    (fun-cong (app g (proj₁ y)) ⊑-refl (proj₂ e)))
  (λ p → λ { (a , b) → ≈-trans C
    (nat g p a ⊑-refl (transport B p b))
    (≈-trans C
      (fun-irr (app g a) (⊑ᵘ-trans p ⊑-refl) (⊑ᵘ-trans ⊑-refl p) (transport B p b))
      (fun-nat (app g a) ⊑-refl p b)) })

curryᵖ-cong : ∀ {A B C} {f g : A ×ᵖ B →ᵖ C} → f ≈ᵖ g → curryᵖ f ≈ᵖ curryᵖ g
curryᵖ-cong {A} e a p b = e (transport A p a , b)

uncurryᵖ-cong : ∀ {A B C} {f g : A →ᵖ B ⇒ᵖ C} → f ≈ᵖ g → uncurryᵖ f ≈ᵖ uncurryᵖ g
uncurryᵖ-cong e x = e (proj₁ x) ⊑-refl (proj₂ x)

curryᵖ-nat : ∀ {A B C D} → (f : A →ᵖ B) → (g : B ×ᵖ C →ᵖ D)
           → curryᵖ (g ∘ᵖ ⟨ f ∘ᵖ fstᵖ , idᵖ ∘ᵖ sndᵖ ⟩ᵖ) ≈ᵖ curryᵖ g ∘ᵖ f
curryᵖ-nat {C = C} f g a p c = app-cong g (nat f p a , ≈-refl C)

uncurryᵖ-nat : ∀ {A B C D} → (f : A →ᵖ B) → (g : B →ᵖ C ⇒ᵖ D)
             → uncurryᵖ (g ∘ᵖ f) ≈ᵖ uncurryᵖ g ∘ᵖ ⟨ f ∘ᵖ fstᵖ , idᵖ ∘ᵖ sndᵖ ⟩ᵖ
uncurryᵖ-nat {D = D} f g x = ≈-refl D

curryᵖ-uncurryᵖ-iso : ∀ {A B C} → (f : A ×ᵖ B →ᵖ C) → uncurryᵖ (curryᵖ f) ≈ᵖ f
curryᵖ-uncurryᵖ-iso {A} {B} f x = app-cong f (transport-refl A (proj₁ x) , ≈-refl B)

uncurryᵖ-curryᵖ-iso : ∀ {A B C} → (g : A →ᵖ B ⇒ᵖ C) → curryᵖ (uncurryᵖ g) ≈ᵖ g
uncurryᵖ-curryᵖ-iso {C = C} g a p b = ≈-trans C
  (nat g p a ⊑-refl b)
  (fun-irr (app g a) (⊑ᵘ-trans p ⊑-refl) p b)

-- Distributivity of the exponential over the product `A ×ᵖ (B ⇒ᵖ C) →ᵖ B ⇒ᵖ (A ×ᵖ C)`
-- (the exponential's costrength). Defined directly rather than via
-- `curryᵖ`/`uncurryᵖ`, so its normal form is small: the Kripke function it
-- produces transports the `A` component and applies the `B ⇒ᵖ C` one.

expᵖ-str : ∀ {A B C} → A ×ᵖ (B ⇒ᵖ C) →ᵖ (B ⇒ᵖ (A ×ᵖ C))
expᵖ-str {A} {B} {C} = pmap
  (λ { (a , f) → mk⇒
      (λ p b → transport A p a , fun f p b)
      (λ p e → ≈-refl A , fun-cong f p e)
      (λ q r b → transport-trans A q r a , fun-nat f q r b) })
  (λ { (ea , ef) p b → transport-cong A p ea , ef p b })
  (λ { p (a , f) q b → ≈-sym A (transport-trans A p q a) , ≈-refl C })

-- `expᵖ-str` is the costrength `curryᵖ ⟨ fstᵖ ∘ᵖ fstᵖ , uncurryᵖ sndᵖ ⟩ᵖ`
-- (they differ only in that the latter applies the exponential at
-- `⊑ᵘ-trans p ⊑-refl` rather than `p`, reconciled by `fun-irr`).

expᵖ-str-def : ∀ {A B C}
             → expᵖ-str {A} {B} {C} ≈ᵖ curryᵖ ⟨ fstᵖ ∘ᵖ fstᵖ , uncurryᵖ sndᵖ ⟩ᵖ
expᵖ-str-def {A} (a , f) p b = ≈-refl A , fun-irr f p (⊑ᵘ-trans p ⊑-refl) b

-- Packaging presheaves up as a setoid-enriched cartesian closed category

PShCat : Category
PShCat = record
  { Obj          = PSh
  ; _→ᵐ_         = _→ᵖ_
  ; _≈ᵐ_         = _≈ᵖ_
  ; ≈ᵐ-refl      = λ {A} {B} {f} → ≈ᵖ-refl {f = f}
  ; ≈ᵐ-sym       = λ {A} {B} {f} {g} → ≈ᵖ-sym {f = f} {g = g}
  ; ≈ᵐ-trans     = λ {A} {B} {f} {g} {h} → ≈ᵖ-trans {f = f} {g = g} {h = h}
  ; idᵐ          = idᵖ
  ; _∘ᵐ_         = _∘ᵖ_
  ; ∘ᵐ-congˡ     = λ {A} {B} {C} {g} {g'} {f} → ∘ᵖ-congˡ {g = g} {g' = g'} {f = f}
  ; ∘ᵐ-congʳ     = λ {A} {B} {C} {g} {f} {f'} → ∘ᵖ-congʳ {g = g} {f = f} {f' = f'}
  ; ∘ᵐ-identityˡ = ∘ᵖ-identityˡ
  ; ∘ᵐ-identityʳ = ∘ᵖ-identityʳ
  ; ∘ᵐ-assoc     = ∘ᵖ-assoc
  ; 𝟙ᵐ           = 𝟙ᵖ
  ; terminalᵐ    = terminalᵖ
  ; terminalᵐ-unique = λ {A} {f} → terminalᵖ-unique {f = f}
  ; 𝟘ᵐ           = 𝟘ᵖ
  ; initialᵐ     = initialᵖ
  ; initialᵐ-unique = λ {A} {f} → initialᵖ-unique {f = f}
  ; 𝟘ᵐ-strict      = 𝟘ᵖ-strict
  ; _×ᵐ_         = _×ᵖ_
  ; fstᵐ         = fstᵖ
  ; sndᵐ         = sndᵖ
  ; ⟨_,_⟩ᵐ       = ⟨_,_⟩ᵖ
  ; ⟨_,_⟩ᵐ-cong  = λ {A} {B} {C} {f} {f'} {g} {g'} → ⟨_,_⟩ᵖ-cong {f = f} {f' = f'} {g = g} {g' = g'}
  ; ⟨⟩ᵐ-fstᵐ     = ⟨⟩ᵖ-fstᵖ
  ; ⟨⟩ᵐ-sndᵐ     = ⟨⟩ᵖ-sndᵖ
  ; ⟨⟩ᵐ-unique   = ⟨⟩ᵖ-unique
  ; _+ᵐ_         = _+ᵖ_
  ; inlᵐ         = inlᵖ
  ; inrᵐ         = inrᵖ
  ; [_,_]ᵐ       = [_,_]ᵖ
  ; [_,_]ᵐ-cong  = λ {A} {B} {C} {f} {f'} {g} {g'} → [_,_]ᵖ-cong {f = f} {f' = f'} {g = g} {g' = g'}
  ; []ᵐ-inlᵐ     = []ᵖ-inlᵖ
  ; []ᵐ-inrᵐ     = []ᵖ-inrᵖ
  ; []ᵐ-unique   = []ᵖ-unique
  ; ℕᵐ           = ℕᵖ
  ; zeroᵐ        = zeroᵖ
  ; succᵐ        = succᵖ
  ; iterᵐ        = iterᵖ
  ; iterᵐ-cong   = λ {A} {a} {a'} {f} {f'} → iterᵖ-cong {a = a} {a' = a'} {f = f} {f' = f'}
  ; iterᵐ-zero   = iterᵖ-zero
  ; iterᵐ-succ   = iterᵖ-succ
  ; iterᵐ-unique = iterᵖ-unique
  ; Listᵐ        = Listᵖ
  ; nilᵐ         = nilᵖ
  ; consᵐ        = consᵖ
  ; foldᵐ        = foldᵖ
  ; foldᵐ-cong   = λ {A} {C} {a} {a'} {f} {f'} → foldᵖ-cong {a = a} {a' = a'} {f = f} {f' = f'}
  ; foldᵐ-nil    = foldᵖ-nil
  ; foldᵐ-cons   = foldᵖ-cons
  ; foldᵐ-unique = foldᵖ-unique
  ; 𝔹ᵐ           = 𝔹ᵖ
  ; trueᵐ        = trueᵖ
  ; falseᵐ       = falseᵖ
  ; ifᵐ          = ifᵖ
  ; ifᵐ-cong     = λ {X} {A} {b} {b'} {f} {f'} {g} {g'} →
                     ifᵖ-cong {b = b} {b' = b'} {f = f} {f' = f'} {g = g} {g' = g'}
  ; ifᵐ-true     = ifᵖ-true
  ; ifᵐ-false    = ifᵖ-false
  ; ifᵐ-∘        = ifᵖ-∘
  ; ifᵐ-η        = ifᵖ-η
  ; _⇒ᵐ_         = _⇒ᵖ_
  ; curryᵐ       = curryᵖ
  ; curryᵐ-cong  = λ {A} {B} {C} {f} {g} → curryᵖ-cong {f = f} {g = g}
  ; curryᵐ-nat   = curryᵖ-nat
  ; uncurryᵐ     = uncurryᵖ
  ; uncurryᵐ-cong = λ {A} {B} {C} {f} {g} → uncurryᵖ-cong {f = f} {g = g}
  ; uncurryᵐ-nat = uncurryᵖ-nat
  ; curryᵐ-uncurryᵐ-iso = curryᵖ-uncurryᵖ-iso
  ; uncurryᵐ-curryᵐ-iso = uncurryᵖ-curryᵖ-iso
  ; exp-strᵐ     = expᵖ-str
  ; exp-strᵐ-def = λ {A} {B} {C} → expᵖ-str-def {A} {B} {C}
  }
