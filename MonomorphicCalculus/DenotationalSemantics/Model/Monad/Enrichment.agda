---------------------------------------------------------------------------
-- The `[-]`-strength of the graded monad as a `[-]`-enrichment.         --
--                                                                       --
-- For any graded monad `M` of the model, the graded `[-]`-strength      --
--                                                                       --
--   strᵀ : [ ∣ ε ∣ᵉ ]ᵒ A ×ᵐ Tᵒ B ε →ᵐ Tᵒ (A ×ᵐ B) ε                     --
--                                                                       --
-- corresponds to a graded `[-]`-enrichment                              --
--                                                                       --
--   enrᵀ : [ ∣ ε ∣ᵉ ]ᵒ (A ⇒ᵐ B) →ᵐ Tᵒ A ε ⇒ᵐ Tᵒ B ε                     --
--                                                                       --
-- both boxed by the resource projection `∣ ε ∣ᵉ` of the effect grade.   --
--                                                                       --
-- The two are inter-derivable (`enr-of-str` / `str-of-enr`), these      --
-- translations are mutually inverse on natural ones                     --
-- (`str-of-enr-of-str`, `enr-of-str-of-enr`), and `enr-of-str`          --
-- preserves naturality (`enr-of-str-nat`). The enrichment `enrᵀ`        --
-- derived from the monad's strength is natural (`enrᵀ-nat`) and         --
-- recovers the strength (`str-of-enrᵀ≈strᵀ`).                           --
--                                                                       --
-- The correspondence concerns the strength/enrichment and their         --
-- naturality only: the box is lax, so the further enrichment            --
-- coherence laws (which would need the box's counit/comultiplication    --
-- inverses) are not available.                                          --
---------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes

module MonomorphicCalculus.DenotationalSemantics.Model.Monad.Enrichment
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
       where

-- `begin_`/`_∎` are hidden here so they resolve to the setoid reasoning
-- opened below rather than the propositional `≡-Reasoning`.
open import Util.Equality hiding (begin_; _∎)

open import MonomorphicCalculus.DenotationalSemantics.Model.Monad S Cat Fut Pst Adj GTy

open LanguageSpec S
open GradeSystemInterface Grades

open Category Cat
open Future Fut

-- Equational reasoning on the hom-setoids `(A →ᵐ B , _≈ᵐ_)`.

open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

private
  homSetoid : ∀ {A B} → Setoid 0ℓ 0ℓ
  homSetoid {A} {B} = record
    { Carrier = A →ᵐ B
    ; _≈_ = _≈ᵐ_
    ; isEquivalence = record { refl = ≈ᵐ-refl ; sym = ≈ᵐ-sym ; trans = ≈ᵐ-trans }
    }

module ≈-Reasoning {A B} = SetoidReasoning (homSetoid {A} {B})
open ≈-Reasoning

-- Uncurrying turns the exponential's action on the codomain into
-- ordinary postcomposition.

uncurryᵐ-map⇒ᵐˡ : ∀ {A B C D} → (h : C →ᵐ D) → (e : A →ᵐ B ⇒ᵐ C)
                → uncurryᵐ (map⇒ᵐ idᵐ h ∘ᵐ e) ≈ᵐ h ∘ᵐ uncurryᵐ e
uncurryᵐ-map⇒ᵐˡ h e =
  begin
    uncurryᵐ (map⇒ᵐ idᵐ h ∘ᵐ e)
  ≈⟨ uncurryᵐ-nat e (map⇒ᵐ idᵐ h) ⟩
    uncurryᵐ (map⇒ᵐ idᵐ h) ∘ᵐ mapˣᵐ e idᵐ
  ≈⟨ ∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso (h ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ idᵐ)) ⟩
    (h ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ idᵐ) ∘ᵐ mapˣᵐ e idᵐ
  ≈⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congʳ mapˣᵐ-idᵐ)) ⟩
    (h ∘ᵐ appᵐ ∘ᵐ idᵐ) ∘ᵐ mapˣᵐ e idᵐ
  ≈⟨ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-identityʳ appᵐ)) ⟩
    (h ∘ᵐ appᵐ) ∘ᵐ mapˣᵐ e idᵐ
  ≈⟨ ∘ᵐ-assoc h appᵐ (mapˣᵐ e idᵐ) ⟩
    h ∘ᵐ appᵐ ∘ᵐ mapˣᵐ e idᵐ
  ≈˘⟨ ∘ᵐ-congʳ (uncurryᵐ-nat e idᵐ) ⟩
    h ∘ᵐ uncurryᵐ (idᵐ ∘ᵐ e)
  ≈⟨ ∘ᵐ-congʳ (uncurryᵐ-cong (∘ᵐ-identityˡ e)) ⟩
    h ∘ᵐ uncurryᵐ e
  ∎

------------------------------------------------------------------------
-- The correspondence, for a fixed monad `M`
------------------------------------------------------------------------

module _ (M : Monad) where

  open Monad M

  -- A graded `[-]`-strength and a graded `[-]`-enrichment, as bare
  -- morphism families (the naturality laws are the predicates below).

  Strᵀ : Set₁
  Strᵀ = ∀ {A B ε} → [ ∣ ε ∣ᵉ ]ᵒ A ×ᵐ Tᵒ B ε →ᵐ Tᵒ (A ×ᵐ B) ε

  Enrᵀ : Set₁
  Enrᵀ = ∀ {A B ε} → [ ∣ ε ∣ᵉ ]ᵒ (A ⇒ᵐ B) →ᵐ Tᵒ A ε ⇒ᵐ Tᵒ B ε

  StrNat : Strᵀ → Set₁
  StrNat str = ∀ {A A' B B' ε} → (f : A →ᵐ A') → (g : B →ᵐ B')
             → str {A'} {B'} {ε} ∘ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ f) (Tᶠ g)
             ≈ᵐ Tᶠ (mapˣᵐ f g) ∘ᵐ str {A} {B}

  EnrNat : Enrᵀ → Set₁
  EnrNat enr = ∀ {A B C D ε} → (f : A →ᵐ B) → (g : C →ᵐ D)
             → map⇒ᵐ (Tᶠ f) (Tᶠ g) ∘ᵐ enr {B} {C} {ε}
             ≈ᵐ enr {A} {D} ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (map⇒ᵐ f g)

  -- Enrichment from strength: strengthen `A ⇒ᵐ B` against a `Tᵒ A`, then
  -- evaluate inside the monad and curry.

  enr-of-str : Strᵀ → Enrᵀ
  enr-of-str str {A} {B} {ε} = curryᵐ (Tᶠ appᵐ ∘ᵐ str {A ⇒ᵐ B} {A} {ε})

  -- Strength from enrichment: pack the boxed value into the constant
  -- pairing `A ⇒ᵐ (A ×ᵐ B)`, then enrich the `Tᵒ B` and uncurry.

  str-of-enr : Enrᵀ → Strᵀ
  str-of-enr enr {A} {B} {ε} =
       uncurryᵐ (enr {B} {A ×ᵐ B} {ε})
    ∘ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)) idᵐ

  -- The enrichment derived from the monad's strength.

  enrᵀ : Enrᵀ
  enrᵀ = enr-of-str strᵀ

  ----------------------------------------------------------------------
  -- The translations are mutually inverse
  ----------------------------------------------------------------------

  -- str → enr → str = str

  str-of-enr-of-str : (str : Strᵀ) → StrNat str
                    → ∀ {A B ε} → str-of-enr (enr-of-str str) {A} {B} {ε}
                                ≈ᵐ str {A} {B} {ε}
  str-of-enr-of-str str str-nat {A} {B} {ε} =
    begin
         uncurryᵐ (curryᵐ (Tᶠ appᵐ ∘ᵐ str {B ⇒ᵐ (A ×ᵐ B)} {B} {ε}))
      ∘ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)) idᵐ
    ≈⟨ ∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso (Tᶠ appᵐ ∘ᵐ str)) ⟩
         (Tᶠ appᵐ ∘ᵐ str {B ⇒ᵐ (A ×ᵐ B)} {B} {ε})
      ∘ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)) idᵐ
    ≈⟨ ∘ᵐ-assoc (Tᶠ appᵐ) str (mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)) idᵐ) ⟩
         Tᶠ appᵐ
      ∘ᵐ str {B ⇒ᵐ (A ×ᵐ B)} {B} {ε}
      ∘ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)) idᵐ
    ≈⟨ ∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-cong ≈ᵐ-refl (≈ᵐ-sym T-idᵐ))) ⟩
         Tᶠ appᵐ
      ∘ᵐ str {B ⇒ᵐ (A ×ᵐ B)} {B} {ε}
      ∘ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)) (Tᶠ idᵐ)
    ≈⟨ ∘ᵐ-congʳ (str-nat (curryᵐ idᵐ) idᵐ) ⟩
         Tᶠ appᵐ
      ∘ᵐ Tᶠ (mapˣᵐ (curryᵐ idᵐ) idᵐ)
      ∘ᵐ str {A} {B} {ε}
    ≈˘⟨ ∘ᵐ-assoc (Tᶠ appᵐ) (Tᶠ (mapˣᵐ (curryᵐ idᵐ) idᵐ)) str ⟩
         (Tᶠ appᵐ ∘ᵐ Tᶠ (mapˣᵐ (curryᵐ idᵐ) idᵐ))
      ∘ᵐ str {A} {B} {ε}
    ≈˘⟨ ∘ᵐ-congˡ (T-∘ᵐ appᵐ (mapˣᵐ (curryᵐ idᵐ) idᵐ)) ⟩
         Tᶠ (appᵐ ∘ᵐ mapˣᵐ (curryᵐ idᵐ) idᵐ)
      ∘ᵐ str {A} {B} {ε}
    ≈˘⟨ ∘ᵐ-congˡ (T-congᶠ (uncurryᵐ-nat (curryᵐ idᵐ) idᵐ)) ⟩
         Tᶠ (uncurryᵐ (idᵐ ∘ᵐ curryᵐ idᵐ))
      ∘ᵐ str {A} {B} {ε}
    ≈⟨ ∘ᵐ-congˡ (T-congᶠ (uncurryᵐ-cong (∘ᵐ-identityˡ (curryᵐ idᵐ)))) ⟩
         Tᶠ (uncurryᵐ (curryᵐ idᵐ))
      ∘ᵐ str {A} {B} {ε}
    ≈⟨ ∘ᵐ-congˡ (T-congᶠ (curryᵐ-uncurryᵐ-iso idᵐ)) ⟩
         Tᶠ idᵐ
      ∘ᵐ str {A} {B} {ε}
    ≈⟨ ∘ᵐ-congˡ T-idᵐ ⟩
         idᵐ
      ∘ᵐ str {A} {B} {ε}
    ≈⟨ ∘ᵐ-identityˡ str ⟩
      str {A} {B} {ε}
    ∎

  -- enr → str → enr = enr

  enr-of-str-of-enr : (enr : Enrᵀ) → EnrNat enr
                    → ∀ {A B ε} → enr-of-str (str-of-enr enr) {A} {B} {ε}
                                ≈ᵐ enr {A} {B} {ε}
  enr-of-str-of-enr enr enr-nat {A} {B} {ε} =
    begin
      curryᵐ (   Tᶠ appᵐ
              ∘ᵐ uncurryᵐ (enr {A} {(A ⇒ᵐ B) ×ᵐ A} {ε})
              ∘ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)) idᵐ)
    ≈⟨ curryᵐ-cong
         (≈ᵐ-trans
           (≈ᵐ-sym (∘ᵐ-assoc (Tᶠ appᵐ)
                             (uncurryᵐ (enr {A} {(A ⇒ᵐ B) ×ᵐ A} {ε}))
                             (mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)) idᵐ)))
           (∘ᵐ-congˡ (≈ᵐ-sym (uncurryᵐ-map⇒ᵐˡ (Tᶠ appᵐ) (enr {A} {(A ⇒ᵐ B) ×ᵐ A} {ε}))))) ⟩
      curryᵐ (   uncurryᵐ (map⇒ᵐ idᵐ (Tᶠ appᵐ) ∘ᵐ enr {A} {(A ⇒ᵐ B) ×ᵐ A} {ε})
              ∘ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)) idᵐ)
    ≈⟨ curryᵐ-cong (∘ᵐ-congˡ (uncurryᵐ-cong
         (∘ᵐ-congˡ (map⇒ᵐ-cong (≈ᵐ-sym T-idᵐ) ≈ᵐ-refl)))) ⟩
      curryᵐ (   uncurryᵐ (map⇒ᵐ (Tᶠ idᵐ) (Tᶠ appᵐ) ∘ᵐ enr {A} {(A ⇒ᵐ B) ×ᵐ A} {ε})
              ∘ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)) idᵐ)
    ≈⟨ curryᵐ-cong (∘ᵐ-congˡ (uncurryᵐ-cong (enr-nat idᵐ appᵐ))) ⟩
      curryᵐ (   uncurryᵐ (enr {A} {B} {ε} ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (map⇒ᵐ idᵐ appᵐ))
              ∘ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)) idᵐ)
    ≈˘⟨ curryᵐ-cong (uncurryᵐ-nat ([ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ))
                                  (enr {A} {B} {ε} ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (map⇒ᵐ idᵐ appᵐ))) ⟩
      curryᵐ (uncurryᵐ (   (enr {A} {B} {ε} ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (map⇒ᵐ idᵐ appᵐ))
                        ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)))
    ≈⟨ uncurryᵐ-curryᵐ-iso
         (   (enr {A} {B} {ε} ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (map⇒ᵐ idᵐ appᵐ))
          ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)) ⟩
         (enr {A} {B} {ε} ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (map⇒ᵐ idᵐ appᵐ))
      ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)
    ≈⟨ ∘ᵐ-assoc (enr {A} {B} {ε}) ([ ∣ ε ∣ᵉ ]ᶠ (map⇒ᵐ idᵐ appᵐ)) ([ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)) ⟩
         enr {A} {B} {ε}
      ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (map⇒ᵐ idᵐ appᵐ)
      ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (curryᵐ idᵐ)
    ≈˘⟨ ∘ᵐ-congʳ ([]-∘ᵐ (curryᵐ idᵐ) (map⇒ᵐ idᵐ appᵐ)) ⟩
         enr {A} {B} {ε}
      ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (map⇒ᵐ idᵐ appᵐ ∘ᵐ curryᵐ idᵐ)
    ≈⟨ ∘ᵐ-congʳ ([]-congᶠ (map⇒ᵐ-curryᵐ appᵐ idᵐ)) ⟩
         enr {A} {B} {ε}
      ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (curryᵐ (appᵐ ∘ᵐ idᵐ))
    ≈⟨ ∘ᵐ-congʳ ([]-congᶠ (curryᵐ-cong (∘ᵐ-identityʳ appᵐ))) ⟩
         enr {A} {B} {ε}
      ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (curryᵐ appᵐ)
    ≈⟨ ∘ᵐ-congʳ ([]-congᶠ (uncurryᵐ-curryᵐ-iso idᵐ)) ⟩
         enr {A} {B} {ε}
      ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ idᵐ
    ≈⟨ ∘ᵐ-congʳ []-idᵐ ⟩
         enr {A} {B} {ε}
      ∘ᵐ idᵐ
    ≈⟨ ∘ᵐ-identityʳ (enr {A} {B} {ε}) ⟩
      enr {A} {B} {ε}
    ∎

  ----------------------------------------------------------------------
  -- The derived enrichment is natural, and recovers the strength
  ----------------------------------------------------------------------

  -- Enrichment-from-strength preserves naturality.

  enr-of-str-nat : (str : Strᵀ) → StrNat str → EnrNat (enr-of-str str)
  enr-of-str-nat str str-nat {A} {B} {C} {D} {ε} f g =
    begin
         map⇒ᵐ (Tᶠ f) (Tᶠ g)
      ∘ᵐ curryᵐ (Tᶠ appᵐ ∘ᵐ str {B ⇒ᵐ C} {B} {ε})
    ≈⟨ ≈ᵐ-sym (curryᵐ-nat (curryᵐ (Tᶠ appᵐ ∘ᵐ str {B ⇒ᵐ C} {B} {ε}))
                          (Tᶠ g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ (Tᶠ f))) ⟩
      curryᵐ (   (Tᶠ g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ (Tᶠ f))
              ∘ᵐ mapˣᵐ (curryᵐ (Tᶠ appᵐ ∘ᵐ str {B ⇒ᵐ C} {B} {ε})) idᵐ)
    ≈⟨ curryᵐ-cong (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))) ⟩
      curryᵐ (   Tᶠ g
              ∘ᵐ appᵐ
              ∘ᵐ mapˣᵐ idᵐ (Tᶠ f)
              ∘ᵐ mapˣᵐ (curryᵐ (Tᶠ appᵐ ∘ᵐ str {B ⇒ᵐ C} {B} {ε})) idᵐ)
    ≈⟨ curryᵐ-cong (∘ᵐ-congʳ (∘ᵐ-congʳ
         (≈ᵐ-trans (mapˣᵐ-∘ idᵐ (Tᶠ f) (curryᵐ (Tᶠ appᵐ ∘ᵐ str {B ⇒ᵐ C} {B} {ε})) idᵐ)
         (≈ᵐ-trans (mapˣᵐ-cong (∘ᵐ-identityˡ _) (∘ᵐ-identityʳ _))
         (≈ᵐ-trans (mapˣᵐ-cong (≈ᵐ-sym (∘ᵐ-identityʳ _)) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
                   (≈ᵐ-sym (mapˣᵐ-∘ (curryᵐ (Tᶠ appᵐ ∘ᵐ str {B ⇒ᵐ C} {B} {ε})) idᵐ idᵐ (Tᶠ f)))))))) ⟩
      curryᵐ (   Tᶠ g
              ∘ᵐ appᵐ
              ∘ᵐ mapˣᵐ (curryᵐ (Tᶠ appᵐ ∘ᵐ str {B ⇒ᵐ C} {B} {ε})) idᵐ
              ∘ᵐ mapˣᵐ idᵐ (Tᶠ f))
    ≈⟨ curryᵐ-cong (∘ᵐ-congʳ (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
         (∘ᵐ-congˡ (≈ᵐ-sym (uncurryᵐ-nat _ _))))) ⟩
      curryᵐ (   Tᶠ g
              ∘ᵐ uncurryᵐ (idᵐ ∘ᵐ curryᵐ (Tᶠ appᵐ ∘ᵐ str {B ⇒ᵐ C} {B} {ε}))
              ∘ᵐ mapˣᵐ idᵐ (Tᶠ f))
    ≈⟨ curryᵐ-cong (∘ᵐ-congʳ (∘ᵐ-congˡ (uncurryᵐ-cong (∘ᵐ-identityˡ _)))) ⟩
      curryᵐ (   Tᶠ g
              ∘ᵐ uncurryᵐ (curryᵐ (Tᶠ appᵐ ∘ᵐ str {B ⇒ᵐ C} {B} {ε}))
              ∘ᵐ mapˣᵐ idᵐ (Tᶠ f))
    ≈⟨ curryᵐ-cong (∘ᵐ-congʳ (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _))) ⟩
      curryᵐ (   Tᶠ g
              ∘ᵐ (Tᶠ appᵐ ∘ᵐ str {B ⇒ᵐ C} {B} {ε})
              ∘ᵐ mapˣᵐ idᵐ (Tᶠ f))
    ≈⟨ curryᵐ-cong (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)) ⟩
      curryᵐ (   Tᶠ g
              ∘ᵐ Tᶠ appᵐ
              ∘ᵐ str {B ⇒ᵐ C} {B} {ε}
              ∘ᵐ mapˣᵐ idᵐ (Tᶠ f))
    ≈⟨ curryᵐ-cong (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-cong (≈ᵐ-sym []-idᵐ) ≈ᵐ-refl)))) ⟩
      curryᵐ (   Tᶠ g
              ∘ᵐ Tᶠ appᵐ
              ∘ᵐ str {B ⇒ᵐ C} {B} {ε}
              ∘ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ idᵐ) (Tᶠ f))
    ≈⟨ curryᵐ-cong (∘ᵐ-congʳ (∘ᵐ-congʳ (str-nat idᵐ f))) ⟩
      curryᵐ (   Tᶠ g
              ∘ᵐ Tᶠ appᵐ
              ∘ᵐ Tᶠ (mapˣᵐ idᵐ f)
              ∘ᵐ str {B ⇒ᵐ C} {A} {ε})
    ≈⟨ curryᵐ-cong (≈ᵐ-sym
         (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (T-∘ᵐ _ _) (∘ᵐ-congʳ (T-∘ᵐ _ _))))
         (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))))) ⟩
      curryᵐ (   Tᶠ (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f)
              ∘ᵐ str {B ⇒ᵐ C} {A} {ε})
    ≈⟨ curryᵐ-cong (∘ᵐ-congˡ (T-congᶠ (≈ᵐ-sym (curryᵐ-uncurryᵐ-iso _)))) ⟩
      curryᵐ (   Tᶠ (uncurryᵐ (curryᵐ (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f)))
              ∘ᵐ str {B ⇒ᵐ C} {A} {ε})
    ≈⟨ curryᵐ-cong (∘ᵐ-congˡ (T-congᶠ (uncurryᵐ-cong (≈ᵐ-sym (∘ᵐ-identityˡ _))))) ⟩
      curryᵐ (   Tᶠ (uncurryᵐ (idᵐ ∘ᵐ map⇒ᵐ f g))
              ∘ᵐ str {B ⇒ᵐ C} {A} {ε})
    ≈⟨ curryᵐ-cong (∘ᵐ-congˡ (T-congᶠ (uncurryᵐ-nat _ _))) ⟩
      curryᵐ (   Tᶠ (uncurryᵐ idᵐ ∘ᵐ mapˣᵐ (map⇒ᵐ f g) idᵐ)
              ∘ᵐ str {B ⇒ᵐ C} {A} {ε})
    ≈⟨ curryᵐ-cong (∘ᵐ-congˡ (T-∘ᵐ appᵐ (mapˣᵐ (map⇒ᵐ f g) idᵐ))) ⟩
      curryᵐ (   (Tᶠ appᵐ ∘ᵐ Tᶠ (mapˣᵐ (map⇒ᵐ f g) idᵐ))
              ∘ᵐ str {B ⇒ᵐ C} {A} {ε})
    ≈⟨ curryᵐ-cong (∘ᵐ-assoc _ _ _) ⟩
      curryᵐ (   Tᶠ appᵐ
              ∘ᵐ Tᶠ (mapˣᵐ (map⇒ᵐ f g) idᵐ)
              ∘ᵐ str {B ⇒ᵐ C} {A} {ε})
    ≈˘⟨ curryᵐ-cong (∘ᵐ-congʳ (str-nat (map⇒ᵐ f g) idᵐ)) ⟩
      curryᵐ (   Tᶠ appᵐ
              ∘ᵐ str {A ⇒ᵐ D} {A} {ε}
              ∘ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (map⇒ᵐ f g)) (Tᶠ idᵐ))
    ≈⟨ curryᵐ-cong (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-cong ≈ᵐ-refl T-idᵐ))) ⟩
      curryᵐ (   Tᶠ appᵐ
              ∘ᵐ str {A ⇒ᵐ D} {A} {ε}
              ∘ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (map⇒ᵐ f g)) idᵐ)
    ≈⟨ ≈ᵐ-trans (curryᵐ-cong (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
                (curryᵐ-nat ([ ∣ ε ∣ᵉ ]ᶠ (map⇒ᵐ f g)) (Tᶠ appᵐ ∘ᵐ str {A ⇒ᵐ D} {A} {ε})) ⟩
         curryᵐ (Tᶠ appᵐ ∘ᵐ str {A ⇒ᵐ D} {A} {ε})
      ∘ᵐ [ ∣ ε ∣ᵉ ]ᶠ (map⇒ᵐ f g)
    ∎

  -- Hence the strength's derived enrichment is natural,

  enrᵀ-nat : EnrNat enrᵀ
  enrᵀ-nat = enr-of-str-nat strᵀ strᵀ-nat

  -- and the strength is recovered from it.

  str-of-enrᵀ≈strᵀ : ∀ {A B ε} → str-of-enr enrᵀ {A} {B} {ε} ≈ᵐ strᵀ {A} {B} {ε}
  str-of-enrᵀ≈strᵀ = str-of-enr-of-str strᵀ strᵀ-nat

  -- The round trip through the strength also closes on `enrᵀ`.

  enr-of-str-of-enrᵀ : ∀ {A B ε} → enr-of-str (str-of-enr enrᵀ) {A} {B} {ε} ≈ᵐ enrᵀ {A} {B} {ε}
  enr-of-str-of-enrᵀ = enr-of-str-of-enr enrᵀ enrᵀ-nat
