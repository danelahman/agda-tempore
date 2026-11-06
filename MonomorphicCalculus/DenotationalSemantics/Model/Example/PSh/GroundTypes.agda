---------------------------------------------------------------------------
-- Interpretation of base types in the presheaf model.                   --
--                                                                       --
-- A base type is interpreted by deciding its eternality. An eternal     --
-- base type is interpreted by a constant presheaf `Kᵖ` on a chosen      --
-- setoid, whose constants are elements of that setoid; a noneternal one --
-- is interpreted by an arbitrary presheaf, with arbitrary global        --
-- elements standing for its constants. An eternal base type's order is  --
-- a comparison on its setoid, natural, and commuting with the eternal   --
-- extraction, as it stands on a constant presheaf. `Kᵖ-eternalᵒ` then   --
-- supplies the `GroundEternal` structure for the eternal case, so the   --
-- presheaf model is closed over any choice of base types                --
-- (`PShBaseTypes`).                                                     --
---------------------------------------------------------------------------

open import Language.BaseTypes
open import Grades.Base
open import Language.Spec

open import MonomorphicCalculus.DenotationalSemantics.Model.World

module MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.GroundTypes
         (S : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
       where

open import Level using (0ℓ)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)

open import Language.Comparisons using (Order; less; equal; greater)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)

open LanguageSpec S
open GradeSystemInterface Grades
open BaseTypes BTs
open World Wld using (_⊑[_]_)

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base Grades Wld
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future Grades Wld
  using (PShFut)
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Past Grades Wld
  using (PShPast; ⟨_⟩ᶠ; mk⟨⟩)
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Adjunction Grades Wld
  using (PShAdj)
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Eternal Grades Wld
  using (Kᵖ; Kᵖ-const; Kᵖ-eternalᵒ; 𝟙ᵖ-eternalᵒ; 𝟘ᵖ-eternalᵒ; 𝔹ᵖ-eternalᵒ; ℕᵖ-eternalᵒ; ×ᵖ-eternalᵒ; ×ᵖ-eternalᵒ-extᵉ
        ; +ᵖ-eternalᵒ; Listᵖ-eternalᵒ)

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open Category PShCat using (_≈ᵐ_; _∘ᵐ_; terminalᵐ)
open import MonomorphicCalculus.DenotationalSemantics.Model.Comparison PShCat using (Ordᵐ; ⌜_⌝ᵒ)

open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
       PShCat RGrade PShFut PShPast PShAdj
  using (Eternalᵒ; +ᵐ-eternalᵒ-inl; +ᵐ-eternalᵒ-inr; Listᵐ-eternalᵒ-nil; Listᵐ-eternalᵒ-cons)

open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundEternal

-- The base-type data the presheaf model needs: for each base type, an
-- interpretation split on its eternality, and the constants' denotations
-- to match.

record PShBaseTypes : Set₁ where
  field
    -- an eternal base type's setoid, and its constants as elements of it
    ⟦_⟧ᵉˢ : (b : BaseType) → EternalBaseType b → Setoid 0ℓ 0ℓ
    ⟦_⟧ᵉᶜ : ∀ {b} → (p : EternalBaseType b) → BaseConstants b → Setoid.Carrier (⟦ b ⟧ᵉˢ p)

    -- a noneternal base type's presheaf, and its constants as global elements
    ⟦_⟧ⁿᵖ : (b : BaseType) → ¬ EternalBaseType b → PSh
    ⟦_⟧ⁿᶜ : ∀ {b} → (¬p : ¬ EternalBaseType b) → BaseConstants b → 𝟙ᵖ →ᵖ ⟦ b ⟧ⁿᵖ ¬p

    -- an eternal base type's comparison on its setoid, respecting the
    -- setoid's equality and comparing constants as the signature orders them
    ⟦_⟧ᵉᵒ      : ∀ {b} → (p : EternalBaseType b)
               → (x y : Setoid.Carrier (⟦ b ⟧ᵉˢ p)) → Order
    ⟦_⟧ᵉᵒ-cong : ∀ {b} → (p : EternalBaseType b) → ∀ {x x' y y'}
               → Setoid._≈_ (⟦ b ⟧ᵉˢ p) x x' → Setoid._≈_ (⟦ b ⟧ᵉˢ p) y y'
               → ⟦ p ⟧ᵉᵒ x y ≡ ⟦ p ⟧ᵉᵒ x' y'
    ⟦_⟧ᵉᵒ-const : ∀ {b} → (p : EternalBaseType b) → (c c' : BaseConstants b)
                → ⟦ p ⟧ᵉᵒ (⟦ p ⟧ᵉᶜ c) (⟦ p ⟧ᵉᶜ c') ≡ compareᵇ p c c'

module PShGround (BT : PShBaseTypes) where
  open PShBaseTypes BT

  -- The base type's interpretation, and its constants', indexed by the
  -- eternality decision so that both reduce once it is known.

  interpᵇ : (b : BaseType) → Dec (EternalBaseType b) → PSh
  interpᵇ b (yes p) = Kᵖ (⟦ b ⟧ᵉˢ p)
  interpᵇ b (no ¬p) = ⟦ b ⟧ⁿᵖ ¬p

  constᵇ : ∀ {b} → (d : Dec (EternalBaseType b)) → BaseConstants b → 𝟙ᵖ →ᵖ interpᵇ b d
  constᵇ {b} (yes p) c = Kᵖ-const (⟦ b ⟧ᵉˢ p) (⟦ p ⟧ᵉᶜ c)
  constᵇ (no ¬p) c = ⟦ ¬p ⟧ⁿᶜ c

  -- The eternal structure of an eternal base type's interpretation. The
  -- `no` case contradicts the witness `eb`.

  eternalᵇ : ∀ {b} → (d : Dec (EternalBaseType b)) → .(EternalBaseType b) → Eternalᵒ (interpᵇ b d)
  eternalᵇ {b} (yes p) _  = Kᵖ-eternalᵒ (⟦ b ⟧ᵉˢ p)
  eternalᵇ (no ¬p) eb = ⊥-elim-irr (¬p eb)

  -- An eternal base type's constant is a global element, matched by
  -- `Kᵖ-eternalᵒ`'s extraction; the noneternal case is again vacuous.

  constᵇ-eternal : ∀ {b} → (d : Dec (EternalBaseType b)) → .(eb : EternalBaseType b) → (c : BaseConstants b) → ∀ {ρ}
                 → Eternalᵒ.extᵉ (eternalᵇ d eb) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (constᵇ d c) ≈ᵐ constᵇ d c ∘ᵐ terminalᵐ
  constᵇ-eternal {b} (yes p) _ c = λ _ → Setoid.refl (⟦ b ⟧ᵉˢ p)
  constᵇ-eternal (no ¬p) eb c = ⊥-elim-irr (¬p eb)

  -- An outcome as an element of `Ordᵐ`, constant across worlds

  ordᵖ : ∀ {w} → Order → carrier Ordᵐ w
  ordᵖ less    = inj₁ tt
  ordᵖ equal   = inj₂ (inj₁ tt)
  ordᵖ greater = inj₂ (inj₂ tt)

  ordᵖ-tr : ∀ {w w'} (q : w ⊑[ 𝟏ᵣ ] w') (o : Order)
          → _≈_ Ordᵐ {w'} (ordᵖ {w'} o) (transport Ordᵐ q (ordᵖ {w} o))
  ordᵖ-tr q less    = tt
  ordᵖ-tr q equal   = tt
  ordᵖ-tr q greater = tt

  ordᵖ-pt : ∀ {w} (o : Order) → _≈_ Ordᵐ {w} (ordᵖ {w} o) (app ⌜ o ⌝ᵒ {w} tt)
  ordᵖ-pt less    = tt
  ordᵖ-pt equal   = tt
  ordᵖ-pt greater = tt

  -- An eternal base type's comparison, pointwise on its constant presheaf
  -- (so natural); the noneternal case is vacuous.

  cmpᵇ : ∀ {b} → (d : Dec (EternalBaseType b)) → .(EternalBaseType b)
       → interpᵇ b d ×ᵖ interpᵇ b d →ᵖ Ordᵐ
  cmpᵇ {b} (yes p) _ = pmap
    (λ { (x , y) → ordᵖ (⟦ p ⟧ᵉᵒ x y) })
    (λ { {w} {x = x , y} (e , e') →
           subst (λ o → _≈_ Ordᵐ {w} (ordᵖ {w} (⟦ p ⟧ᵉᵒ x y)) (ordᵖ {w} o))
                 (⟦ p ⟧ᵉᵒ-cong e e') (≈-refl Ordᵐ {x = ordᵖ {w} (⟦ p ⟧ᵉᵒ x y)}) })
    (λ { {w} {w'} q (x , y) → ordᵖ-tr {w} {w'} q (⟦ p ⟧ᵉᵒ x y) })
  cmpᵇ (no ¬p) eb = ⊥-elim-irr (¬p eb)

  cmpᵇ-pt : ∀ {b} → (d : Dec (EternalBaseType b)) → .(eb : EternalBaseType b)
          → (c c' : BaseConstants b)
          → cmpᵇ d eb ∘ᵖ ⟨ constᵇ d c , constᵇ d c' ⟩ᵖ ≈ᵐ ⌜ compareᵇ eb c c' ⌝ᵒ
  cmpᵇ-pt (yes p) _ c c' {w} _ =
    subst (λ o → _≈_ Ordᵐ {w} (ordᵖ {w} (⟦ p ⟧ᵉᵒ (⟦ p ⟧ᵉᶜ c) (⟦ p ⟧ᵉᶜ c')))
                                 (app ⌜ o ⌝ᵒ {w} tt))
          (⟦ p ⟧ᵉᵒ-const c c') (ordᵖ-pt {w} (⟦ p ⟧ᵉᵒ (⟦ p ⟧ᵉᶜ c) (⟦ p ⟧ᵉᶜ c')))
  cmpᵇ-pt (no ¬p) eb c c' = ⊥-elim-irr (¬p eb)

  -- The comparison commutes with the eternal extraction: on a constant
  -- presheaf the extraction leaves the compared values, and the outcome,
  -- unchanged.

  cmpᵇ-eternal : ∀ {b} → (d : Dec (EternalBaseType b)) → .(eb : EternalBaseType b) → ∀ {ρ}
               → cmpᵇ d eb ∘ᵐ Eternalᵒ.extᵉ (×ᵖ-eternalᵒ (eternalᵇ d eb) (eternalᵇ d eb)) {ρ}
               ≈ᵐ Eternalᵒ.extᵉ (+ᵖ-eternalᵒ 𝟙ᵖ-eternalᵒ (+ᵖ-eternalᵒ 𝟙ᵖ-eternalᵒ 𝟙ᵖ-eternalᵒ)) {ρ}
                  ∘ᵐ ⟨ ρ ⟩ᶠ (cmpᵇ d eb)
  cmpᵇ-eternal (yes p) _ (mk⟨⟩ _ (x , y)) with ⟦ p ⟧ᵉᵒ x y
  ... | less    = tt
  ... | equal   = tt
  ... | greater = tt
  cmpᵇ-eternal (no ¬p) eb = ⊥-elim-irr (¬p eb)

  -- The `GroundTypes` and `GroundEternal` structures assembled from a
  -- choice of base types, deciding eternality per base type.

  PShGroundTypes : GroundTypes S PShCat PShFut
  PShGroundTypes = record
    { ⟦_⟧ᵇ  = λ b → interpᵇ b (eternalBaseType? b)
    ; ⟦_⟧ᵇᶜ = λ {b} c → constᵇ (eternalBaseType? b) c
    }

  PShGroundEternal : GroundEternal S PShCat PShFut PShPast PShAdj PShGroundTypes
  PShGroundEternal = record
    { ⟦_⟧ᵇᵉ         = λ b eb → eternalᵇ (eternalBaseType? b) eb
    ; 𝟙-eternalᵒ    = 𝟙ᵖ-eternalᵒ
    ; 𝟘-eternalᵒ    = 𝟘ᵖ-eternalᵒ
    ; 𝔹-eternalᵒ    = 𝔹ᵖ-eternalᵒ
    ; ℕ-eternalᵒ    = ℕᵖ-eternalᵒ
    ; ×-eternalᵒ    = ×ᵖ-eternalᵒ
    ; ×-eternalᵒ-extᵉ = ×ᵖ-eternalᵒ-extᵉ
    ; +-eternalᵒ    = +ᵖ-eternalᵒ
    ; +-eternalᵒ-inl = +ᵐ-eternalᵒ-inl
    ; +-eternalᵒ-inr = +ᵐ-eternalᵒ-inr
    ; List-eternalᵒ = Listᵖ-eternalᵒ
    ; List-eternalᵒ-nil = Listᵐ-eternalᵒ-nil
    ; List-eternalᵒ-cons = Listᵐ-eternalᵒ-cons
    ; ⟦⟧ᵇᶜ-eternal  = λ {b} eb c → constᵇ-eternal (eternalBaseType? b) eb c
    ; cmpᵇᵐ          = λ b eb → cmpᵇ (eternalBaseType? b) eb
    ; cmpᵇᵐ-pt       = λ {b} eb → cmpᵇ-pt (eternalBaseType? b) eb
    ; cmpᵇᵐ-eternal  = λ {b} eb → cmpᵇ-eternal (eternalBaseType? b) eb
    ; trueᵐ-eternal  = λ _ → refl
    ; falseᵐ-eternal = λ _ → refl
    ; zeroᵐ-eternal  = λ _ → refl
    ; succᵐ-eternal  = λ _ → refl
    }
