---------------------------------------------------------------------------
-- Comparisons are morphisms of eternal objects.                         --
--                                                                       --
-- A morphism of eternal objects (`EternalMap`) commutes with the        --
-- eternal extraction at every grade. Such morphisms are closed under    --
-- composition and pairing, and include the projections, the             --
-- injections, copairings and the constructors of the eternal data.      --
-- Every comparison of `Model.Comparison` is one, given that the         --
-- comparisons it is built from are: `lexᵐ`, `holdsᵐ`, the unit's, the   --
-- empty object's, the booleans' and the natural numbers' comparisons,   --
-- and the products', coproducts' and lists'.                            --
--                                                                       --
-- Extraction has no naturality in general, so each is shown through     --
-- its mate: a map commutes with extraction iff it commutes with         --
-- necessitation `necᵉ`. Both sides of the latter are maps out of the    --
-- comparison's own domain, so they are equal once they agree on the     --
-- constructors, by the eliminators' uniqueness, and by iteration and    --
-- folding for the natural numbers and the lists.                        --
---------------------------------------------------------------------------

open import Data.Bool.Base using (true; false)

open import Language.Comparisons using (Cmp; holds; Order; less; equal; greater; compareᴮ)
open import Grades.Base
open import Language.Spec

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundEternal

module MonomorphicCalculus.DenotationalSemantics.Model.ComparisonEternal
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open LanguageSpec S

open Category Cat
open Future Fut using ([_]ᶠ; []-∘ᵐ; []-congᶠ; []-monoidal; []-monoidal-η)
open Past Pst using (⟨_⟩ᶠ; ⟨⟩-idᵐ; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ)
open Adjunction Adj using (η⊣; η⊣-nat)
open GroundEternal GE
open import MonomorphicCalculus.DenotationalSemantics.Model.Comparison Cat
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj
  using (Eternalᵒ; ⟨⟩-mate-≈; ⟨⟩-+-ext)

open Eternalᵒ using (extᵉ; necᵉ)

private
  infixr 3 _∙_
  _∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙_ = ≈ᵐ-trans

------------------------------------------------------------------------
-- Morphisms of eternal objects

-- The outcomes' eternal structure

Ord-eternalᵒ : Eternalᵒ Ordᵐ
Ord-eternalᵒ = +-eternalᵒ 𝟙-eternalᵒ (+-eternalᵒ 𝟙-eternalᵒ 𝟙-eternalᵒ)

-- A morphism of eternal objects commutes with the extraction at every grade.

record EternalMap {A B : Obj} (eA : Eternalᵒ A) (eB : Eternalᵒ B) (f : A →ᵐ B) : Set where
  constructor eternal-map
  field
    extᵉ-nat : ∀ {ρ} → f ∘ᵐ extᵉ eA {ρ} ≈ᵐ extᵉ eB {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ f

open EternalMap public

module _ {A B C : Obj} {eA : Eternalᵒ A} {eB : Eternalᵒ B} {eC : Eternalᵒ C} where

  ∘ᵉ : ∀ {g : B →ᵐ C} {f : A →ᵐ B}
     → EternalMap eB eC g → EternalMap eA eB f → EternalMap eA eC (g ∘ᵐ f)
  ∘ᵉ pg pf = eternal-map (
      ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (extᵉ-nat pf) ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (extᵉ-nat pg)
    ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))

  -- pairing
  ⟨_,_⟩ᵉ : ∀ {f : A →ᵐ B} {g : A →ᵐ C}
         → EternalMap eA eB f → EternalMap eA eC g → EternalMap eA (×-eternalᵒ eB eC) ⟨ f , g ⟩ᵐ
  ⟨_,_⟩ᵉ {f} {g} pf pg = eternal-map (
      ⟨⟩ᵐ-∘ _ _ _ ∙ ⟨ extᵉ-nat pf , extᵉ-nat pg ⟩ᵐ-cong
    ∙ ≈ᵐ-sym ( ∘ᵐ-congˡ (×-eternalᵒ-extᵉ eB eC) ∙ ⟨⟩ᵐ-∘ _ _ _
             ∙ ⟨ comp {e = eB} (⟨⟩ᵐ-fstᵐ f g) , comp {e = eC} (⟨⟩ᵐ-sndᵐ f g) ⟩ᵐ-cong))
    where
      comp : ∀ {E} {e : Eternalᵒ E} {π : B ×ᵐ C →ᵐ E} {h : A →ᵐ E} → π ∘ᵐ ⟨ f , g ⟩ᵐ ≈ᵐ h
           → ∀ {ρ} → (extᵉ e {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ π) ∘ᵐ ⟨ ρ ⟩ᶠ ⟨ f , g ⟩ᵐ ≈ᵐ extᵉ e {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ h
      comp e = ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _) ∙ ⟨⟩-congᶠ e)

  -- copairing
  [_,_]ᵉ : ∀ {f : A →ᵐ C} {g : B →ᵐ C}
         → EternalMap eA eC f → EternalMap eB eC g → EternalMap (+-eternalᵒ eA eB) eC [ f , g ]ᵐ
  [_,_]ᵉ {f} {g} pf pg =
    eternal-map (⟨⟩-+-ext (side (+-eternalᵒ-inl eA eB) ([]ᵐ-inlᵐ f g) pf)
                          (side (+-eternalᵒ-inr eA eB) ([]ᵐ-inrᵐ f g) pg))
    where
      side : ∀ {X} {eX : Eternalᵒ X} {ι : X →ᵐ A +ᵐ B} {h : X →ᵐ C} → ∀ {ρ}
           → extᵉ (+-eternalᵒ eA eB) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ ι ≈ᵐ ι ∘ᵐ extᵉ eX {ρ}
           → [ f , g ]ᵐ ∘ᵐ ι ≈ᵐ h → EternalMap eX eC h
           → ([ f , g ]ᵐ ∘ᵐ extᵉ (+-eternalᵒ eA eB) {ρ}) ∘ᵐ ⟨ ρ ⟩ᶠ ι
             ≈ᵐ (extᵉ eC {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ [ f , g ]ᵐ) ∘ᵐ ⟨ ρ ⟩ᶠ ι
      side law e ph =
          ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ law ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ e ∙ extᵉ-nat ph
        ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym e) ∙ ⟨⟩-∘ᵐ _ _) ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

module _ {A B : Obj} {eA : Eternalᵒ A} {eB : Eternalᵒ B} where

  ≈ᵉ : ∀ {f g : A →ᵐ B} → f ≈ᵐ g → EternalMap eA eB f → EternalMap eA eB g
  ≈ᵉ e p = eternal-map (∘ᵐ-congˡ (≈ᵐ-sym e) ∙ extᵉ-nat p ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ e))

  fstᵉ : EternalMap (×-eternalᵒ eA eB) eA fstᵐ
  fstᵉ = eternal-map (∘ᵐ-congʳ (×-eternalᵒ-extᵉ eA eB) ∙ ⟨⟩ᵐ-fstᵐ _ _)

  sndᵉ : EternalMap (×-eternalᵒ eA eB) eB sndᵐ
  sndᵉ = eternal-map (∘ᵐ-congʳ (×-eternalᵒ-extᵉ eA eB) ∙ ⟨⟩ᵐ-sndᵐ _ _)

  inlᵉ : EternalMap eA (+-eternalᵒ eA eB) inlᵐ
  inlᵉ = eternal-map (≈ᵐ-sym (+-eternalᵒ-inl eA eB))

  inrᵉ : EternalMap eB (+-eternalᵒ eA eB) inrᵐ
  inrᵉ = eternal-map (≈ᵐ-sym (+-eternalᵒ-inr eA eB))

module _ {A : Obj} {eA : Eternalᵒ A} where

  idᵉ : EternalMap eA eA idᵐ
  idᵉ = eternal-map (∘ᵐ-identityˡ _ ∙ ≈ᵐ-sym (∘ᵐ-congʳ ⟨⟩-idᵐ ∙ ∘ᵐ-identityʳ _))

  terminalᵉ : EternalMap eA 𝟙-eternalᵒ terminalᵐ
  terminalᵉ = eternal-map (terminalᵐ-unique ∙ ≈ᵐ-sym terminalᵐ-unique)

  initialᵉ : EternalMap 𝟘-eternalᵒ eA initialᵐ
  initialᵉ = eternal-map (⟨⟩-mate-≈ (initialᵐ-unique ∙ ≈ᵐ-sym initialᵐ-unique))

  -- a global element the extraction recovers
  pointᵉ : ∀ {p : 𝟙ᵐ →ᵐ A}
         → (∀ {ρ} → extᵉ eA {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ p ≈ᵐ p ∘ᵐ terminalᵐ)
         → EternalMap 𝟙-eternalᵒ eA p
  pointᵉ law = eternal-map (∘ᵐ-congʳ terminalᵐ-unique ∙ ≈ᵐ-sym law)

  -- a constant
  constᵉ : ∀ {B} {eB : Eternalᵒ B} {p : 𝟙ᵐ →ᵐ B}
         → EternalMap 𝟙-eternalᵒ eB p → EternalMap eA eB (p ∘ᵐ terminalᵐ)
  constᵉ pp = ∘ᵉ pp terminalᵉ

mapˣᵉ : ∀ {A B C D} {eA : Eternalᵒ A} {eB : Eternalᵒ B} {eC : Eternalᵒ C} {eD : Eternalᵒ D}
      → ∀ {f : A →ᵐ C} {g : B →ᵐ D}
      → EternalMap eA eC f → EternalMap eB eD g
      → EternalMap (×-eternalᵒ eA eB) (×-eternalᵒ eC eD) (mapˣᵐ f g)
mapˣᵉ pf pg = ⟨ ∘ᵉ pf fstᵉ , ∘ᵉ pg sndᵉ ⟩ᵉ

-- the constructors of the eternal data

boolᵉ : (b : _) → EternalMap 𝟙-eternalᵒ 𝔹-eternalᵒ ⌜ b ⌝ᵇ
boolᵉ true  = pointᵉ trueᵐ-eternal
boolᵉ false = pointᵉ falseᵐ-eternal

zeroᵉ : EternalMap 𝟙-eternalᵒ ℕ-eternalᵒ zeroᵐ
zeroᵉ = pointᵉ zeroᵐ-eternal

succᵉ : EternalMap ℕ-eternalᵒ ℕ-eternalᵒ succᵐ
succᵉ = eternal-map (≈ᵐ-sym succᵐ-eternal)

nilᵉ : ∀ {A} {eA : Eternalᵒ A} → EternalMap 𝟙-eternalᵒ (List-eternalᵒ eA) nilᵐ
nilᵉ {eA = eA} = pointᵉ (List-eternalᵒ-nil eA)

consᵉ : ∀ {A} {eA : Eternalᵒ A}
      → EternalMap (×-eternalᵒ eA (List-eternalᵒ eA)) (List-eternalᵒ eA) consᵐ
consᵉ {eA = eA} =
  eternal-map (∘ᵐ-congʳ (×-eternalᵒ-extᵉ _ _) ∙ ≈ᵐ-sym (List-eternalᵒ-cons eA))

outcomeᵉ : (o : Order) → EternalMap 𝟙-eternalᵒ Ord-eternalᵒ ⌜ o ⌝ᵒ
outcomeᵉ less    = inlᵉ
outcomeᵉ equal   = ∘ᵉ inrᵉ inlᵉ
outcomeᵉ greater = ∘ᵉ inrᵉ inrᵉ

------------------------------------------------------------------------
-- The mate: commuting with necessitation

module _ {A B : Obj} (eA : Eternalᵒ A) (eB : Eternalᵒ B) where

  private
    mate-lhs : ∀ {ρ} (f : A →ᵐ B)
             → [ ρ ]ᶠ (f ∘ᵐ extᵉ eA {ρ}) ∘ᵐ η⊣ ≈ᵐ [ ρ ]ᶠ f ∘ᵐ necᵉ eA {ρ}
    mate-lhs f = ∘ᵐ-congˡ ([]-∘ᵐ _ _) ∙ ∘ᵐ-assoc _ _ _

    mate-rhs : ∀ {ρ} (f : A →ᵐ B)
             → [ ρ ]ᶠ (extᵉ eB {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ f) ∘ᵐ η⊣ ≈ᵐ necᵉ eB {ρ} ∘ᵐ f
    mate-rhs f =
        ∘ᵐ-congˡ ([]-∘ᵐ _ _) ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (η⊣-nat f) ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

  -- A morphism of eternal objects commutes with necessitation, and conversely.

  ext→nec : ∀ {f : A →ᵐ B} → EternalMap eA eB f
          → ∀ {ρ} → [ ρ ]ᶠ f ∘ᵐ necᵉ eA {ρ} ≈ᵐ necᵉ eB {ρ} ∘ᵐ f
  ext→nec {f} p = ≈ᵐ-sym (mate-lhs f) ∙ ∘ᵐ-congˡ ([]-congᶠ (extᵉ-nat p)) ∙ mate-rhs f

  nec→ext : ∀ {f : A →ᵐ B} → (∀ {ρ} → [ ρ ]ᶠ f ∘ᵐ necᵉ eA {ρ} ≈ᵐ necᵉ eB {ρ} ∘ᵐ f)
          → EternalMap eA eB f
  nec→ext {f} p = eternal-map (⟨⟩-mate-≈ (mate-lhs f ∙ p ∙ ≈ᵐ-sym (mate-rhs f)))

private
  -- necessitation slides past a morphism of eternal objects
  slide : ∀ {X A B} {eX : Eternalᵒ X} {eA : Eternalᵒ A} {k : X →ᵐ A} → (g : A →ᵐ B)
        → EternalMap eX eA k
        → ∀ {ρ} → [ ρ ]ᶠ (g ∘ᵐ k) ∘ᵐ necᵉ eX {ρ} ≈ᵐ ([ ρ ]ᶠ g ∘ᵐ necᵉ eA {ρ}) ∘ᵐ k
  slide {eX = eX} {eA} g pk =
      ∘ᵐ-congˡ ([]-∘ᵐ _ _) ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (ext→nec eX eA pk) ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

  -- The two sides of the necessitation square of `c` agree after a morphism
  -- of eternal objects `k`, when `c ∘ᵐ k` is one.
  restrict : ∀ {X A B} {eX : Eternalᵒ X} {eA : Eternalᵒ A} {eB : Eternalᵒ B}
           → (c : A →ᵐ B) → {k : X →ᵐ A}
           → EternalMap eX eA k → EternalMap eX eB (c ∘ᵐ k)
           → ∀ {ρ} → ([ ρ ]ᶠ c ∘ᵐ necᵉ eA {ρ}) ∘ᵐ k ≈ᵐ (necᵉ eB {ρ} ∘ᵐ c) ∘ᵐ k
  restrict {eX = eX} {eA} {eB} c pk pck =
      ≈ᵐ-sym (slide c pk) ∙ ext→nec eX eB pck ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

  -- necessitation into a product, and the box of a pairing
  nec× : ∀ {A B} (eA : Eternalᵒ A) (eB : Eternalᵒ B) → ∀ {ρ}
       → necᵉ (×-eternalᵒ eA eB) {ρ} ≈ᵐ []-monoidal ∘ᵐ mapˣᵐ (necᵉ eA {ρ}) (necᵉ eB {ρ})
  nec× eA eB =
      ≈ᵐ-sym (∘ᵐ-identityˡ _) ∙ ∘ᵐ-congˡ (≈ᵐ-sym []-monoidal-η) ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _ ∙ ⟨ ext→nec _ eA fstᵉ , ext→nec _ eB sndᵉ ⟩ᵐ-cong)

  box⟨⟩ : ∀ {X A B ρ} (u : X →ᵐ A) (v : X →ᵐ B)
        → [ ρ ]ᶠ ⟨ u , v ⟩ᵐ ≈ᵐ []-monoidal ∘ᵐ ⟨ [ ρ ]ᶠ u , [ ρ ]ᶠ v ⟩ᵐ
  box⟨⟩ u v =
      ≈ᵐ-sym (∘ᵐ-identityˡ _) ∙ ∘ᵐ-congˡ (≈ᵐ-sym []-monoidal-η) ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _
               ∙ ⟨ ≈ᵐ-sym ([]-∘ᵐ _ _) ∙ []-congᶠ (⟨⟩ᵐ-fstᵐ u v)
                 , ≈ᵐ-sym ([]-∘ᵐ _ _) ∙ []-congᶠ (⟨⟩ᵐ-sndᵐ u v) ⟩ᵐ-cong)

------------------------------------------------------------------------
-- Maps out of the data, determined by the constructors

private
  pre² : ∀ {A B C D E} (m : C ×ᵐ D →ᵐ E) (a : A →ᵐ C) (b : B →ᵐ D)
       → (m ∘ᵐ mapˣᵐ a idᵐ) ∘ᵐ mapˣᵐ idᵐ b ≈ᵐ m ∘ᵐ mapˣᵐ a b
  pre² m a b =
    ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (mapˣᵐ-∘ _ _ _ _ ∙ mapˣᵐ-cong (∘ᵐ-identityʳ a) (∘ᵐ-identityˡ b))

  preˡ : ∀ {A B C D E} (m : C ×ᵐ D →ᵐ E) (a : B →ᵐ C) (b : A →ᵐ B)
       → (m ∘ᵐ mapˣᵐ a idᵐ) ∘ᵐ mapˣᵐ b idᵐ ≈ᵐ m ∘ᵐ mapˣᵐ (a ∘ᵐ b) idᵐ
  preˡ m a b = ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (mapˣᵐ-∘ _ _ _ _ ∙ mapˣᵐ-cong ≈ᵐ-refl (∘ᵐ-identityˡ _))

  -- the second component: coproducts, and their retracts

  ext+ʳ : ∀ {X A B C} {m m' : X ×ᵐ (A +ᵐ B) →ᵐ C}
        → m ∘ᵐ mapˣᵐ idᵐ inlᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ idᵐ inlᵐ
        → m ∘ᵐ mapˣᵐ idᵐ inrᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ idᵐ inrᵐ
        → m ≈ᵐ m'
  ext+ʳ {m = m} {m'} p q =
    copairˣᵐ-unique _ _ m p q ∙ ≈ᵐ-sym (copairˣᵐ-unique _ _ m' ≈ᵐ-refl ≈ᵐ-refl)

  ext-retractʳ : ∀ {X B D C} {e : B →ᵐ D} {r : D →ᵐ B} {m m' : X ×ᵐ D →ᵐ C}
               → e ∘ᵐ r ≈ᵐ idᵐ
               → m ∘ᵐ mapˣᵐ idᵐ e ≈ᵐ m' ∘ᵐ mapˣᵐ idᵐ e → m ≈ᵐ m'
  ext-retractʳ {e = e} {r} {m} {m'} er p = unfold m ∙ ∘ᵐ-congˡ p ∙ ≈ᵐ-sym (unfold m')
    where
      unfold : ∀ n → n ≈ᵐ (n ∘ᵐ mapˣᵐ idᵐ e) ∘ᵐ mapˣᵐ idᵐ r
      unfold n =
          ≈ᵐ-sym (∘ᵐ-identityʳ n)
        ∙ ∘ᵐ-congʳ ( ≈ᵐ-sym mapˣᵐ-idᵐ
                   ∙ mapˣᵐ-cong (≈ᵐ-sym (∘ᵐ-identityˡ _)) (≈ᵐ-sym er)
                   ∙ ≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _))
        ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

  through : ∀ {X A B D C} (m : X ×ᵐ D →ᵐ C) (e : B →ᵐ D) (ι : A →ᵐ B) {j : A →ᵐ D}
          → e ∘ᵐ ι ≈ᵐ j → (m ∘ᵐ mapˣᵐ idᵐ e) ∘ᵐ mapˣᵐ idᵐ ι ≈ᵐ m ∘ᵐ mapˣᵐ idᵐ j
  through m e ι p =
    ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (mapˣᵐ-∘ _ _ _ _ ∙ mapˣᵐ-cong (∘ᵐ-identityˡ _) p)

  extℕʳ : ∀ {X C} {m m' : X ×ᵐ ℕᵐ →ᵐ C}
        → m ∘ᵐ mapˣᵐ idᵐ zeroᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ idᵐ zeroᵐ
        → m ∘ᵐ mapˣᵐ idᵐ succᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ idᵐ succᵐ
        → m ≈ᵐ m'
  extℕʳ {m = m} {m'} p q =
    ext-retractʳ [zero,succ]-predᵐ
      (ext+ʳ (through m _ _ ([]ᵐ-inlᵐ _ _) ∙ p ∙ ≈ᵐ-sym (through m' _ _ ([]ᵐ-inlᵐ _ _)))
             (through m _ _ ([]ᵐ-inrᵐ _ _) ∙ q ∙ ≈ᵐ-sym (through m' _ _ ([]ᵐ-inrᵐ _ _))))

  extLʳ : ∀ {X A C} {m m' : X ×ᵐ Listᵐ A →ᵐ C}
        → m ∘ᵐ mapˣᵐ idᵐ nilᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ idᵐ nilᵐ
        → m ∘ᵐ mapˣᵐ idᵐ consᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ idᵐ consᵐ
        → m ≈ᵐ m'
  extLʳ {m = m} {m'} p q =
    ext-retractʳ [nil,cons]-unconsᵐ
      (ext+ʳ (through m _ _ ([]ᵐ-inlᵐ _ _) ∙ p ∙ ≈ᵐ-sym (through m' _ _ ([]ᵐ-inlᵐ _ _)))
             (through m _ _ ([]ᵐ-inrᵐ _ _) ∙ q ∙ ≈ᵐ-sym (through m' _ _ ([]ᵐ-inrᵐ _ _))))

  ext𝔹ʳ : ∀ {X C} {m m' : X ×ᵐ 𝔹ᵐ →ᵐ C}
        → m ∘ᵐ mapˣᵐ idᵐ trueᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ idᵐ trueᵐ
        → m ∘ᵐ mapˣᵐ idᵐ falseᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ idᵐ falseᵐ
        → m ≈ᵐ m'
  ext𝔹ʳ {m = m} {m'} p q =
      ≈ᵐ-sym (back m) ∙ ifᵐ-η sndᵐ _
    ∙ ifᵐ-cong ≈ᵐ-refl (at m _ ∙ ∘ᵐ-congˡ p ∙ ≈ᵐ-sym (at m' _))
                       (at m _ ∙ ∘ᵐ-congˡ q ∙ ≈ᵐ-sym (at m' _))
    ∙ ≈ᵐ-sym (ifᵐ-η sndᵐ _) ∙ back m'
    where
      back : ∀ n → (n ∘ᵐ mapˣᵐ fstᵐ idᵐ) ∘ᵐ ⟨ idᵐ , sndᵐ ⟩ᵐ ≈ᵐ n
      back n =
          ∘ᵐ-assoc _ _ _
        ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong ∙ ⟨fst,snd⟩ᵐ)
        ∙ ∘ᵐ-identityʳ n

      at : ∀ n (b : 𝟙ᵐ →ᵐ 𝔹ᵐ)
         → (n ∘ᵐ mapˣᵐ fstᵐ idᵐ) ∘ᵐ ⟨ idᵐ , b ∘ᵐ terminalᵐ ⟩ᵐ
         ≈ᵐ (n ∘ᵐ mapˣᵐ idᵐ b) ∘ᵐ ⟨ fstᵐ , terminalᵐ ⟩ᵐ
      at n b =
          ∘ᵐ-assoc _ _ _
        ∙ ∘ᵐ-congʳ ( mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
                   ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
        ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

  -- the first component, through the symmetry

  swap-ext : ∀ {A B C} {m m' : A ×ᵐ B →ᵐ C} → m ∘ᵐ swapᵐ ≈ᵐ m' ∘ᵐ swapᵐ → m ≈ᵐ m'
  swap-ext {m = m} {m'} e =
      ≈ᵐ-sym (∘ᵐ-identityʳ m) ∙ ∘ᵐ-congʳ (≈ᵐ-sym swapᵐ-swapᵐ) ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙ ∘ᵐ-congˡ e ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ swapᵐ-swapᵐ ∙ ∘ᵐ-identityʳ m'

  flip : ∀ {A A' B C} {m m' : B ×ᵐ A →ᵐ C} (ι : A' →ᵐ B)
       → m ∘ᵐ mapˣᵐ ι idᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ ι idᵐ
       → (m ∘ᵐ swapᵐ) ∘ᵐ mapˣᵐ idᵐ ι ≈ᵐ (m' ∘ᵐ swapᵐ) ∘ᵐ mapˣᵐ idᵐ ι
  flip ι p = sw ∙ ∘ᵐ-congˡ p ∙ ≈ᵐ-sym sw
    where
      sw : ∀ {n} → (n ∘ᵐ swapᵐ) ∘ᵐ mapˣᵐ idᵐ ι ≈ᵐ (n ∘ᵐ mapˣᵐ ι idᵐ) ∘ᵐ swapᵐ
      sw = ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (swapᵐ-mapˣᵐ idᵐ ι) ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

  ext+ˡ : ∀ {X A B C} {m m' : (A +ᵐ B) ×ᵐ X →ᵐ C}
        → m ∘ᵐ mapˣᵐ inlᵐ idᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ inlᵐ idᵐ
        → m ∘ᵐ mapˣᵐ inrᵐ idᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ inrᵐ idᵐ
        → m ≈ᵐ m'
  ext+ˡ p q = swap-ext (ext+ʳ (flip inlᵐ p) (flip inrᵐ q))

  ext𝔹ˡ : ∀ {X C} {m m' : 𝔹ᵐ ×ᵐ X →ᵐ C}
        → m ∘ᵐ mapˣᵐ trueᵐ idᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ trueᵐ idᵐ
        → m ∘ᵐ mapˣᵐ falseᵐ idᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ falseᵐ idᵐ
        → m ≈ᵐ m'
  ext𝔹ˡ p q = swap-ext (ext𝔹ʳ (flip trueᵐ p) (flip falseᵐ q))

  -- maps out of pairs of outcomes, booleans and summands

  extOrdˡ : ∀ {X C} {m m' : Ordᵐ ×ᵐ X →ᵐ C}
          → (∀ o → m ∘ᵐ mapˣᵐ ⌜ o ⌝ᵒ idᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ ⌜ o ⌝ᵒ idᵐ)
          → m ≈ᵐ m'
  extOrdˡ {m = m} {m'} h =
    ext+ˡ (h less)
          (ext+ˡ (preˡ m _ _ ∙ h equal ∙ ≈ᵐ-sym (preˡ m' _ _))
                 (preˡ m _ _ ∙ h greater ∙ ≈ᵐ-sym (preˡ m' _ _)))

  ext𝔹² : ∀ {C} {m m' : 𝔹ᵐ ×ᵐ 𝔹ᵐ →ᵐ C}
        → (∀ b b' → m ∘ᵐ mapˣᵐ ⌜ b ⌝ᵇ ⌜ b' ⌝ᵇ ≈ᵐ m' ∘ᵐ mapˣᵐ ⌜ b ⌝ᵇ ⌜ b' ⌝ᵇ)
        → m ≈ᵐ m'
  ext𝔹² {m = m} {m'} h =
    ext𝔹ˡ (ext𝔹ʳ (both true true) (both true false))
          (ext𝔹ʳ (both false true) (both false false))
    where
      both : ∀ b b' → (m ∘ᵐ mapˣᵐ ⌜ b ⌝ᵇ idᵐ) ∘ᵐ mapˣᵐ idᵐ ⌜ b' ⌝ᵇ
                    ≈ᵐ (m' ∘ᵐ mapˣᵐ ⌜ b ⌝ᵇ idᵐ) ∘ᵐ mapˣᵐ idᵐ ⌜ b' ⌝ᵇ
      both b b' = pre² m _ _ ∙ h b b' ∙ ≈ᵐ-sym (pre² m' _ _)

  ext+² : ∀ {A B C} {m m' : (A +ᵐ B) ×ᵐ (A +ᵐ B) →ᵐ C}
        → m ∘ᵐ mapˣᵐ inlᵐ inlᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ inlᵐ inlᵐ
        → m ∘ᵐ mapˣᵐ inlᵐ inrᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ inlᵐ inrᵐ
        → m ∘ᵐ mapˣᵐ inrᵐ inlᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ inrᵐ inlᵐ
        → m ∘ᵐ mapˣᵐ inrᵐ inrᵐ ≈ᵐ m' ∘ᵐ mapˣᵐ inrᵐ inrᵐ
        → m ≈ᵐ m'
  ext+² {m = m} {m'} hll hlr hrl hrr =
    ext+ˡ (ext+ʳ (both hll) (both hlr)) (ext+ʳ (both hrl) (both hrr))
    where
      both : ∀ {A' B'} {a : A' →ᵐ _} {b : B' →ᵐ _}
           → m ∘ᵐ mapˣᵐ a b ≈ᵐ m' ∘ᵐ mapˣᵐ a b
           → (m ∘ᵐ mapˣᵐ a idᵐ) ∘ᵐ mapˣᵐ idᵐ b ≈ᵐ (m' ∘ᵐ mapˣᵐ a idᵐ) ∘ᵐ mapˣᵐ idᵐ b
      both h = pre² m _ _ ∙ h ∙ ≈ᵐ-sym (pre² m' _ _)

  -- the eliminators at a constructor in the second component

  const-∘ : ∀ {X Y A} → (c : 𝟙ᵐ →ᵐ A) → (h : X →ᵐ Y)
          → (c ∘ᵐ terminalᵐ) ∘ᵐ h ≈ᵐ c ∘ᵐ terminalᵐ
  const-∘ c h = ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ terminalᵐ-unique

  fst²-snd : ∀ {Y X S N} → (u : Y →ᵐ X) → (s : Y →ᵐ S) → (n : Y →ᵐ N)
           → ⟨ fstᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ∘ᵐ ⟨ ⟨ u , s ⟩ᵐ , n ⟩ᵐ ≈ᵐ ⟨ u , n ⟩ᵐ
  fst²-snd u s n =
      ⟨⟩ᵐ-∘ _ _ _
    ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ⟨⟩ᵐ-fstᵐ _ _ , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong

  matchℕᵐ-zeroʳ : ∀ {Y X C} → (f : X ×ᵐ ℕᵐ →ᵐ C) → (g : (X ×ᵐ ℕᵐ) ×ᵐ ℕᵐ →ᵐ C)
                → (h : Y →ᵐ X)
                → matchℕᵐ sndᵐ f g ∘ᵐ mapˣᵐ h zeroᵐ ≈ᵐ f ∘ᵐ mapˣᵐ h zeroᵐ
  matchℕᵐ-zeroʳ f g h =
      matchℕᵐ-∘ sndᵐ f g _
    ∙ matchℕᵐ-cong (⟨⟩ᵐ-sndᵐ _ _ ∙ ∘ᵐ-congʳ terminalᵐ-unique) ≈ᵐ-refl ≈ᵐ-refl
    ∙ matchℕᵐ-zero _ _

  matchℕᵐ-succʳ : ∀ {Y X C} → (f : X ×ᵐ ℕᵐ →ᵐ C) → (g : (X ×ᵐ ℕᵐ) ×ᵐ ℕᵐ →ᵐ C)
                → (h : Y →ᵐ X)
                → matchℕᵐ sndᵐ f g ∘ᵐ mapˣᵐ h succᵐ ≈ᵐ g ∘ᵐ ⟨ mapˣᵐ h succᵐ , sndᵐ ⟩ᵐ
  matchℕᵐ-succʳ f g h =
      matchℕᵐ-∘ sndᵐ f g _
    ∙ matchℕᵐ-cong (⟨⟩ᵐ-sndᵐ _ _) ≈ᵐ-refl ≈ᵐ-refl
    ∙ matchℕᵐ-succ sndᵐ _ _
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)

  matchLᵐ-nilʳ : ∀ {Y X A C} → (f : X ×ᵐ Listᵐ A →ᵐ C)
               → (g : ((X ×ᵐ Listᵐ A) ×ᵐ A) ×ᵐ Listᵐ A →ᵐ C) → (h : Y →ᵐ X)
               → matchLᵐ sndᵐ f g ∘ᵐ mapˣᵐ h nilᵐ ≈ᵐ f ∘ᵐ mapˣᵐ h nilᵐ
  matchLᵐ-nilʳ f g h =
      matchLᵐ-∘ sndᵐ f g _
    ∙ matchLᵐ-cong (⟨⟩ᵐ-sndᵐ _ _ ∙ ∘ᵐ-congʳ terminalᵐ-unique) ≈ᵐ-refl ≈ᵐ-refl
    ∙ matchLᵐ-nil _ _

  matchLᵐ-consʳ : ∀ {Y X A C} → (f : X ×ᵐ Listᵐ A →ᵐ C)
                → (g : ((X ×ᵐ Listᵐ A) ×ᵐ A) ×ᵐ Listᵐ A →ᵐ C) → (h : Y →ᵐ X)
                → matchLᵐ sndᵐ f g ∘ᵐ mapˣᵐ h consᵐ
                ≈ᵐ g ∘ᵐ ⟨ ⟨ mapˣᵐ h consᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ
  matchLᵐ-consʳ f g h =
      matchLᵐ-∘ sndᵐ f g _
    ∙ matchLᵐ-cong (⟨⟩ᵐ-sndᵐ _ _ ∙ ∘ᵐ-congʳ sndᵐ-split) ≈ᵐ-refl ≈ᵐ-refl
    ∙ matchLᵐ-cons _ _ _ _
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
               ∙ ⟨ mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
                 , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)

  -- Two maps out of pairs of natural numbers agree if they agree when the
  -- first is zero, are the same constant when only the second is, and are
  -- both invariant under the successor on both sides.

  ℕ²-ext : ∀ {Y} (P Q : ℕᵐ ×ᵐ ℕᵐ →ᵐ Y) (y : 𝟙ᵐ →ᵐ Y)
         → P ∘ᵐ mapˣᵐ zeroᵐ idᵐ ≈ᵐ Q ∘ᵐ mapˣᵐ zeroᵐ idᵐ
         → P ∘ᵐ mapˣᵐ succᵐ zeroᵐ ≈ᵐ y ∘ᵐ terminalᵐ
         → Q ∘ᵐ mapˣᵐ succᵐ zeroᵐ ≈ᵐ y ∘ᵐ terminalᵐ
         → P ∘ᵐ mapˣᵐ succᵐ succᵐ ≈ᵐ P
         → Q ∘ᵐ mapˣᵐ succᵐ succᵐ ≈ᵐ Q
         → P ≈ᵐ Q
  ℕ²-ext {Y} P Q y hz hP hQ sP sQ =
      ≈ᵐ-sym (curryᵐ-uncurryᵐ-iso P)
    ∙ uncurryᵐ-cong (iterᵐ-ext (curryᵐ (P ∘ᵐ mapˣᵐ zeroᵐ idᵐ)) (curryᵐ F) (curryᵐ P) (curryᵐ Q)
                       (≈ᵐ-sym (curryᵐ-nat zeroᵐ P)) (step P hP sP)
                       (≈ᵐ-sym (curryᵐ-nat zeroᵐ Q) ∙ curryᵐ-cong (≈ᵐ-sym hz)) (step Q hQ sQ))
    ∙ curryᵐ-uncurryᵐ-iso Q
    where
      F : (ℕᵐ ⇒ᵐ Y) ×ᵐ ℕᵐ →ᵐ Y
      F = matchℕᵐ sndᵐ (y ∘ᵐ terminalᵐ) (appᵐ ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ)

      step : (R : ℕᵐ ×ᵐ ℕᵐ →ᵐ Y)
           → R ∘ᵐ mapˣᵐ succᵐ zeroᵐ ≈ᵐ y ∘ᵐ terminalᵐ → R ∘ᵐ mapˣᵐ succᵐ succᵐ ≈ᵐ R
           → curryᵐ R ∘ᵐ succᵐ ≈ᵐ curryᵐ F ∘ᵐ curryᵐ R
      step R h s =
          ≈ᵐ-sym (curryᵐ-nat succᵐ R)
        ∙ curryᵐ-cong (extℕʳ (pre² R _ _ ∙ h ∙ ≈ᵐ-sym (pre² F _ _ ∙ matchℕᵐ-zeroʳ _ _ _ ∙ const-∘ _ _))
                             (pre² R _ _ ∙ s ∙ ≈ᵐ-sym (pre² F _ _ ∙ matchℕᵐ-succʳ _ _ _ ∙ apply)))
        ∙ curryᵐ-nat (curryᵐ R) F
        where
          apply : (appᵐ ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ) ∘ᵐ ⟨ mapˣᵐ (curryᵐ R) succᵐ , sndᵐ ⟩ᵐ ≈ᵐ R
          apply =
              ∘ᵐ-assoc _ _ _
            ∙ ∘ᵐ-congʳ (fst²-snd _ _ _ ∙ ⟨ ≈ᵐ-refl , ≈ᵐ-sym (∘ᵐ-identityˡ _) ⟩ᵐ-cong)
            ∙ appᵐ-mapˣᵐ _ ∙ curryᵐ-uncurryᵐ-iso R

  -- Two maps out of pairs of lists agree if they agree when the first is
  -- empty, are the same constant when only the second is, and follow the
  -- same recurrence `K` on two non-empty lists, from the heads and the
  -- value at the tails.

  L²-ext : ∀ {A Y} (P Q : Listᵐ A ×ᵐ Listᵐ A →ᵐ Y) (y : 𝟙ᵐ →ᵐ Y) (K : (A ×ᵐ A) ×ᵐ Y →ᵐ Y)
         → P ∘ᵐ mapˣᵐ nilᵐ idᵐ ≈ᵐ Q ∘ᵐ mapˣᵐ nilᵐ idᵐ
         → P ∘ᵐ mapˣᵐ consᵐ nilᵐ ≈ᵐ y ∘ᵐ terminalᵐ
         → Q ∘ᵐ mapˣᵐ consᵐ nilᵐ ≈ᵐ y ∘ᵐ terminalᵐ
         → P ∘ᵐ mapˣᵐ consᵐ consᵐ ≈ᵐ K ∘ᵐ ⟨ mapˣᵐ fstᵐ fstᵐ , P ∘ᵐ mapˣᵐ sndᵐ sndᵐ ⟩ᵐ
         → Q ∘ᵐ mapˣᵐ consᵐ consᵐ ≈ᵐ K ∘ᵐ ⟨ mapˣᵐ fstᵐ fstᵐ , Q ∘ᵐ mapˣᵐ sndᵐ sndᵐ ⟩ᵐ
         → P ≈ᵐ Q
  L²-ext {A} {Y} P Q y K hn hP hQ cP cQ =
      ≈ᵐ-sym (curryᵐ-uncurryᵐ-iso P)
    ∙ uncurryᵐ-cong (foldᵐ-ext (curryᵐ (P ∘ᵐ mapˣᵐ nilᵐ idᵐ)) (curryᵐ F) (curryᵐ P) (curryᵐ Q)
                       (≈ᵐ-sym (curryᵐ-nat nilᵐ P)) (step P hP cP)
                       (≈ᵐ-sym (curryᵐ-nat nilᵐ Q) ∙ curryᵐ-cong (≈ᵐ-sym hn)) (step Q hQ cQ))
    ∙ curryᵐ-uncurryᵐ-iso Q
    where
      G : (((A ×ᵐ (Listᵐ A ⇒ᵐ Y)) ×ᵐ Listᵐ A) ×ᵐ A) ×ᵐ Listᵐ A →ᵐ Y
      G = K ∘ᵐ ⟨ ⟨ fstᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ fstᵐ ⟩ᵐ
               , appᵐ ∘ᵐ ⟨ sndᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ

      F : (A ×ᵐ (Listᵐ A ⇒ᵐ Y)) ×ᵐ Listᵐ A →ᵐ Y
      F = matchLᵐ sndᵐ (y ∘ᵐ terminalᵐ) G

      step : (R : Listᵐ A ×ᵐ Listᵐ A →ᵐ Y)
           → R ∘ᵐ mapˣᵐ consᵐ nilᵐ ≈ᵐ y ∘ᵐ terminalᵐ
           → R ∘ᵐ mapˣᵐ consᵐ consᵐ ≈ᵐ K ∘ᵐ ⟨ mapˣᵐ fstᵐ fstᵐ , R ∘ᵐ mapˣᵐ sndᵐ sndᵐ ⟩ᵐ
           → curryᵐ R ∘ᵐ consᵐ ≈ᵐ curryᵐ F ∘ᵐ mapˣᵐ idᵐ (curryᵐ R)
      step R h c =
          ≈ᵐ-sym (curryᵐ-nat consᵐ R)
        ∙ curryᵐ-cong (extLʳ (pre² R _ _ ∙ h ∙ ≈ᵐ-sym (pre² F _ _ ∙ matchLᵐ-nilʳ _ _ _ ∙ const-∘ _ _))
                             (pre² R _ _ ∙ c ∙ ≈ᵐ-sym (pre² F _ _ ∙ matchLᵐ-consʳ _ _ _ ∙ apply)))
        ∙ curryᵐ-nat (mapˣᵐ idᵐ (curryᵐ R)) F
        where
          φ = curryᵐ R
          Z = ⟨ ⟨ mapˣᵐ (mapˣᵐ idᵐ φ) consᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ

          third : ∀ {E} → (π : A ×ᵐ (Listᵐ A ⇒ᵐ Y) →ᵐ E)
                → (π ∘ᵐ fstᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ) ∘ᵐ Z ≈ᵐ (π ∘ᵐ mapˣᵐ idᵐ φ) ∘ᵐ fstᵐ
          third π =
              ∘ᵐ-assoc _ _ _
            ∙ ∘ᵐ-congʳ ( ∘ᵐ-assoc _ _ _
                       ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ⟨⟩ᵐ-fstᵐ _ _)
                       ∙ ⟨⟩ᵐ-fstᵐ _ _)
            ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

          apply : G ∘ᵐ Z ≈ᵐ K ∘ᵐ ⟨ mapˣᵐ fstᵐ fstᵐ , R ∘ᵐ mapˣᵐ sndᵐ sndᵐ ⟩ᵐ
          apply =
              ∘ᵐ-assoc _ _ _
            ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _ ∙ ⟨ heads , tails ⟩ᵐ-cong)
            where
              heads : ⟨ fstᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ fstᵐ ⟩ᵐ ∘ᵐ Z ≈ᵐ mapˣᵐ fstᵐ fstᵐ
              heads =
                  ⟨⟩ᵐ-∘ _ _ _
                ∙ ⟨ third fstᵐ ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _ ∙ ∘ᵐ-identityˡ _)
                  , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong

              tails : (appᵐ ∘ᵐ ⟨ sndᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ) ∘ᵐ Z
                    ≈ᵐ R ∘ᵐ mapˣᵐ sndᵐ sndᵐ
              tails =
                  ∘ᵐ-assoc _ _ _
                ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _
                           ∙ ⟨ third sndᵐ ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _) ∙ ∘ᵐ-assoc _ _ _
                             , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong
                           ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
                ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                ∙ ∘ᵐ-congˡ (appᵐ-mapˣᵐ φ ∙ curryᵐ-uncurryᵐ-iso R)

------------------------------------------------------------------------
-- The comparisons

private
  -- a comparison at points, as a map out of `𝟙ᵐ ×ᵐ 𝟙ᵐ`
  pts : ∀ {A} {D : Set} {c : A ×ᵐ A →ᵐ Ordᵐ} (pt : D → 𝟙ᵐ →ᵐ A) (compare : D → D → Order)
      → Compares c pt compare → (x y : D)
      → c ∘ᵐ mapˣᵐ (pt x) (pt y) ≈ᵐ ⌜ compare x y ⌝ᵒ ∘ᵐ terminalᵐ
  pts _ _ h x y =
      ∘ᵐ-congʳ ( ⟨ ∘ᵐ-congʳ terminalᵐ-unique , ∘ᵐ-congʳ terminalᵐ-unique ⟩ᵐ-cong
               ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
    ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (h x y)

-- the truth of a relation on an outcome

holdsᵉ : (⋈ : Cmp) → EternalMap Ord-eternalᵒ 𝔹-eternalᵒ (holdsᵐ ⋈)
holdsᵉ ⋈ = [ boolᵉ (holds ⋈ less) , [ boolᵉ (holds ⋈ equal) , boolᵉ (holds ⋈ greater) ]ᵉ ]ᵉ

-- lexicographic combination

lexᵉ : EternalMap (×-eternalᵒ Ord-eternalᵒ Ord-eternalᵒ) Ord-eternalᵒ lexᵐ
lexᵉ = nec→ext _ _ λ {ρ} →
  extOrdˡ λ o → restrict lexᵐ (mapˣᵉ (outcomeᵉ o) idᵉ) (≈ᵉ (≈ᵐ-sym (lexᵐ-first o)) (first o))
  where
    first : (o : Order)
          → EternalMap (×-eternalᵒ 𝟙-eternalᵒ Ord-eternalᵒ) Ord-eternalᵒ
                       (selᵒ o (⌜ less ⌝ᵒ ∘ᵐ terminalᵐ) sndᵐ (⌜ greater ⌝ᵒ ∘ᵐ terminalᵐ))
    first less    = constᵉ (outcomeᵉ less)
    first equal   = sndᵉ
    first greater = constᵉ (outcomeᵉ greater)

-- the unit, the empty object and the booleans

cmp𝟙ᵉ : EternalMap (×-eternalᵒ 𝟙-eternalᵒ 𝟙-eternalᵒ) Ord-eternalᵒ cmp𝟙ᵐ
cmp𝟙ᵉ = constᵉ (outcomeᵉ equal)

cmp𝟘ᵉ : EternalMap (×-eternalᵒ 𝟘-eternalᵒ 𝟘-eternalᵒ) Ord-eternalᵒ cmp𝟘ᵐ
cmp𝟘ᵉ = ∘ᵉ initialᵉ fstᵉ

cmp𝔹ᵉ : EternalMap (×-eternalᵒ 𝔹-eternalᵒ 𝔹-eternalᵒ) Ord-eternalᵒ cmp𝔹ᵐ
cmp𝔹ᵉ = nec→ext _ _ λ {ρ} →
  ext𝔹² λ b b' →
    restrict cmp𝔹ᵐ (mapˣᵉ (boolᵉ b) (boolᵉ b'))
      (≈ᵉ (≈ᵐ-sym (pts ⌜_⌝ᵇ compareᴮ cmp𝔹ᵐ-pt b b')) (constᵉ (outcomeᵉ (compareᴮ b b'))))

-- the natural numbers

cmpℕᵉ : EternalMap (×-eternalᵒ ℕ-eternalᵒ ℕ-eternalᵒ) Ord-eternalᵒ cmpℕᵐ
cmpℕᵉ = nec→ext _ _ λ {ρ} →
  ℕ²-ext _ _ (necᵉ Ord-eternalᵒ ∘ᵐ ⌜ greater ⌝ᵒ)
    (extℕʳ (pre² _ _ _ ∙ restrict cmpℕᵐ (mapˣᵉ zeroᵉ zeroᵉ)
                           (≈ᵉ (≈ᵐ-sym cmpℕᵐ-zero-zero) (constᵉ (outcomeᵉ equal)))
            ∙ ≈ᵐ-sym (pre² _ _ _))
           (pre² _ _ _ ∙ restrict cmpℕᵐ (mapˣᵉ zeroᵉ succᵉ)
                           (≈ᵉ (≈ᵐ-sym cmpℕᵐ-zero-succ) (constᵉ (outcomeᵉ less)))
            ∙ ≈ᵐ-sym (pre² _ _ _)))
    (restrict cmpℕᵐ (mapˣᵉ succᵉ zeroᵉ) (≈ᵉ (≈ᵐ-sym cmpℕᵐ-succ-zero) (constᵉ (outcomeᵉ greater)))
     ∙ greaterQ)
    greaterQ
    (≈ᵐ-sym (slide cmpℕᵐ (mapˣᵉ succᵉ succᵉ)) ∙ ∘ᵐ-congˡ ([]-congᶠ cmpℕᵐ-succ-succ))
    (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ cmpℕᵐ-succ-succ)
  where
    greaterQ : ∀ {ρ} → (necᵉ Ord-eternalᵒ {ρ} ∘ᵐ cmpℕᵐ) ∘ᵐ mapˣᵐ succᵐ zeroᵐ
             ≈ᵐ (necᵉ Ord-eternalᵒ {ρ} ∘ᵐ ⌜ greater ⌝ᵒ) ∘ᵐ terminalᵐ
    greaterQ = ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ cmpℕᵐ-succ-zero ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- products

cmp×ᵉ : ∀ {A B} {eA : Eternalᵒ A} {eB : Eternalᵒ B}
      → {c : A ×ᵐ A →ᵐ Ordᵐ} {d : B ×ᵐ B →ᵐ Ordᵐ}
      → EternalMap (×-eternalᵒ eA eA) Ord-eternalᵒ c
      → EternalMap (×-eternalᵒ eB eB) Ord-eternalᵒ d
      → EternalMap (×-eternalᵒ (×-eternalᵒ eA eB) (×-eternalᵒ eA eB)) Ord-eternalᵒ (cmp×ᵐ c d)
cmp×ᵉ pc pd = ∘ᵉ lexᵉ ⟨ ∘ᵉ pc (mapˣᵉ fstᵉ fstᵉ) , ∘ᵉ pd (mapˣᵉ sndᵉ sndᵉ) ⟩ᵉ

-- coproducts

cmp+ᵉ : ∀ {A B} {eA : Eternalᵒ A} {eB : Eternalᵒ B}
      → {c : A ×ᵐ A →ᵐ Ordᵐ} {d : B ×ᵐ B →ᵐ Ordᵐ}
      → EternalMap (×-eternalᵒ eA eA) Ord-eternalᵒ c
      → EternalMap (×-eternalᵒ eB eB) Ord-eternalᵒ d
      → EternalMap (×-eternalᵒ (+-eternalᵒ eA eB) (+-eternalᵒ eA eB)) Ord-eternalᵒ (cmp+ᵐ c d)
cmp+ᵉ {c = c} {d} pc pd = nec→ext _ _ λ {ρ} →
  ext+² (restrict (cmp+ᵐ c d) (mapˣᵉ inlᵉ inlᵉ) (≈ᵉ (≈ᵐ-sym (cmp+ᵐ-inl-inlˣ c d)) pc))
        (restrict (cmp+ᵐ c d) (mapˣᵉ inlᵉ inrᵉ)
          (≈ᵉ (≈ᵐ-sym (cmp+ᵐ-inl-inrˣ c d)) (constᵉ (outcomeᵉ less))))
        (restrict (cmp+ᵐ c d) (mapˣᵉ inrᵉ inlᵉ)
          (≈ᵉ (≈ᵐ-sym (cmp+ᵐ-inr-inlˣ c d)) (constᵉ (outcomeᵉ greater))))
        (restrict (cmp+ᵐ c d) (mapˣᵉ inrᵉ inrᵉ) (≈ᵉ (≈ᵐ-sym (cmp+ᵐ-inr-inrˣ c d)) pd))

-- lists

cmpLᵉ : ∀ {A} {eA : Eternalᵒ A} {c : A ×ᵐ A →ᵐ Ordᵐ}
      → EternalMap (×-eternalᵒ eA eA) Ord-eternalᵒ c
      → EternalMap (×-eternalᵒ (List-eternalᵒ eA) (List-eternalᵒ eA)) Ord-eternalᵒ (cmpLᵐ c)
cmpLᵉ {A} {eA} {c} pc = nec→ext _ _ λ {ρ} →
  L²-ext _ _ (necᵉ Ord-eternalᵒ ∘ᵐ ⌜ greater ⌝ᵒ) (K {ρ})
    (extLʳ (pre² _ _ _ ∙ restrict (cmpLᵐ c) (mapˣᵉ nilᵉ nilᵉ)
                           (≈ᵉ (≈ᵐ-sym (cmpLᵐ-nil-nil c)) (constᵉ (outcomeᵉ equal)))
            ∙ ≈ᵐ-sym (pre² _ _ _))
           (pre² _ _ _ ∙ restrict (cmpLᵐ c) (mapˣᵉ nilᵉ consᵉ)
                           (≈ᵉ (≈ᵐ-sym (cmpLᵐ-nil-cons c)) (constᵉ (outcomeᵉ less)))
            ∙ ≈ᵐ-sym (pre² _ _ _)))
    (restrict (cmpLᵐ c) (mapˣᵉ consᵉ nilᵉ)
       (≈ᵉ (≈ᵐ-sym (cmpLᵐ-cons-nil c)) (constᵉ (outcomeᵉ greater)))
     ∙ greaterQ)
    greaterQ
    consP
    consQ
  where
    eL  = List-eternalᵒ eA
    nO  = λ {ρ} → necᵉ Ord-eternalᵒ {ρ}

    -- the recurrence at two non-empty lists, under the box
    K : ∀ {ρ} → (A ×ᵐ A) ×ᵐ _ →ᵐ _
    K {ρ} = [ ρ ]ᶠ lexᵐ ∘ᵐ ([]-monoidal ∘ᵐ mapˣᵐ (nO {ρ} ∘ᵐ c) idᵐ)

    K-at : ∀ {ρ X} (w : X →ᵐ A ×ᵐ A) (t : X →ᵐ _)
         → K {ρ} ∘ᵐ ⟨ w , t ⟩ᵐ ≈ᵐ [ ρ ]ᶠ lexᵐ ∘ᵐ ([]-monoidal ∘ᵐ ⟨ nO ∘ᵐ (c ∘ᵐ w) , t ⟩ᵐ)
    K-at w t =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _
                 ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-assoc _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))

    greaterQ : ∀ {ρ} → (nO {ρ} ∘ᵐ cmpLᵐ c) ∘ᵐ mapˣᵐ consᵐ nilᵐ ≈ᵐ (nO ∘ᵐ ⌜ greater ⌝ᵒ) ∘ᵐ terminalᵐ
    greaterQ = ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (cmpLᵐ-cons-nil c) ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

    consQ : ∀ {ρ} → (nO {ρ} ∘ᵐ cmpLᵐ c) ∘ᵐ mapˣᵐ consᵐ consᵐ
          ≈ᵐ K ∘ᵐ ⟨ mapˣᵐ fstᵐ fstᵐ , (nO ∘ᵐ cmpLᵐ c) ∘ᵐ mapˣᵐ sndᵐ sndᵐ ⟩ᵐ
    consQ =
        ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (cmpLᵐ-cons-cons c)
      ∙ ≈ᵐ-sym ( K-at _ _
               ∙ ∘ᵐ-congʳ ( ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ∘ᵐ-assoc _ _ _ ⟩ᵐ-cong
                                       ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))
                          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                          ∙ ∘ᵐ-congˡ (≈ᵐ-sym (nec× Ord-eternalᵒ Ord-eternalᵒ)))
               ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
               ∙ ∘ᵐ-congˡ (ext→nec _ _ lexᵉ)
               ∙ ∘ᵐ-assoc _ _ _)

    consP : ∀ {ρ} → ([ ρ ]ᶠ (cmpLᵐ c) ∘ᵐ necᵉ (×-eternalᵒ eL eL) {ρ}) ∘ᵐ mapˣᵐ consᵐ consᵐ
          ≈ᵐ K ∘ᵐ ⟨ mapˣᵐ fstᵐ fstᵐ
                  , ([ ρ ]ᶠ (cmpLᵐ c) ∘ᵐ necᵉ (×-eternalᵒ eL eL) {ρ}) ∘ᵐ mapˣᵐ sndᵐ sndᵐ ⟩ᵐ
    consP =
        ≈ᵐ-sym (slide (cmpLᵐ c) (mapˣᵉ consᵉ consᵉ))
      ∙ ∘ᵐ-congˡ ([]-congᶠ (cmpLᵐ-cons-cons c) ∙ []-∘ᵐ _ _ ∙ ∘ᵐ-congʳ (box⟨⟩ _ _))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ ( ∘ᵐ-assoc _ _ _
                 ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _
                            ∙ ⟨ slide c (mapˣᵉ fstᵉ fstᵉ) ∙ ∘ᵐ-congˡ (ext→nec _ _ pc) ∙ ∘ᵐ-assoc _ _ _
                              , slide (cmpLᵐ c) (mapˣᵉ sndᵉ sndᵉ) ⟩ᵐ-cong))
      ∙ ≈ᵐ-sym (K-at _ _)
