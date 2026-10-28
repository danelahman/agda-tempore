------------------------------------------------------------------------
-- Zones in counts of a unit, scaled to zones of durations.           --
--                                                                    --
-- A zone of whole steps (`Joint.Zone ℕᵀ`) scales by a positive unit  --
-- `δ` to a zone of the time domain, end by end (`Exact.Grid`). The   --
-- scaling commutes with the operations on zones, and preserves and   --
-- reflects being inhabited, since it preserves and reflects the      --
-- order of ends; so the zones a walk meets, when its letters' ends   --
-- lie on the grid of `δ`, are computed in counts of `δ`.             --
------------------------------------------------------------------------

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Durations.Monus as Monus

module Grades.Exact.Joint.Scale
  {D : Duration} (T : TimeDomain D)
  {δ : Duration.Carrier D} (δ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) δ) where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Util.Equality

open import Grades.Durations.Nat using (ℕᵀ)
open import Grades.Durations.Monus T
import Grades.Durations.Monus ℕᵀ as NM
open import Grades.Durations.Intervals T
import Grades.Durations.Intervals ℕᵀ as N
import Grades.Durations.Intervals.Dense T as DT
import Grades.Durations.Intervals.Dense ℕᵀ as DN
open import Grades.Exact.Grid T using (_×ᴰ_; ×-+; ×-mono; module Scale)
open import Grades.Exact.Joint.Zone T
import Grades.Exact.Joint.Zone ℕᵀ as Z

open Scale δ-pos public
open Equivalence using (to; from)

------------------------------------------------------------------------
-- Zones, scaled

scZ : Z.Zone → Zone
scZ Z = ⟨ scᶜ (Z.loᶻ Z) , scʰ (Z.hiᶻ Z) ⟩ᶻ

------------------------------------------------------------------------
-- Differences of counts

×-∸ : ∀ p q → (p NM.∸ᴰ q) ×ᴰ δ ≡ p ×ᴰ δ ∸ᴰ q ×ᴰ δ
×-∸ p q = case (q NM.≤ᴰ? p)
  where
    case : Dec (q NM.≤ᴰ p) → (p NM.∸ᴰ q) ×ᴰ δ ≡ p ×ᴰ δ ∸ᴰ q ×ᴰ δ
    case (yes q≤p) = sym (∸-unique (trans (sym (×-+ q (p NM.∸ᴰ q) δ)) (cong (_×ᴰ δ) (NM.+-∸ q≤p))))
    case (no ¬q≤p) =
      trans (cong (_×ᴰ δ) (NM.∸-≤ (NM.<⇒≤ ¬q≤p))) (sym (∸-≤ (×-mono δ (NM.<⇒≤ ¬q≤p))))

------------------------------------------------------------------------
-- The larger and smaller ends, chosen by the order

private
  ⊔ᶜ-yes : ∀ {c c′} → c ⊑ c′ → c ⊔ᶜ c′ ≡ c′
  ⊔ᶜ-yes {c} {c′} p with c ⊑? c′
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p p)

  ⊔ᶜ-no : ∀ {c c′} → ¬ (c ⊑ c′) → c ⊔ᶜ c′ ≡ c
  ⊔ᶜ-no {c} {c′} ¬p with c ⊑? c′
  ... | yes p = ⊥-elim (¬p p)
  ... | no _  = refl

  ⊔ᶜ-yesᴺ : ∀ {c c′} → c N.⊑ c′ → c N.⊔ᶜ c′ ≡ c′
  ⊔ᶜ-yesᴺ {c} {c′} p with c N.⊑? c′
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p p)

  ⊔ᶜ-noᴺ : ∀ {c c′} → ¬ (c N.⊑ c′) → c N.⊔ᶜ c′ ≡ c
  ⊔ᶜ-noᴺ {c} {c′} ¬p with c N.⊑? c′
  ... | yes p = ⊥-elim (¬p p)
  ... | no _  = refl

  ⊓ᶜ-yes : ∀ {c c′} → c ⊑ c′ → c ⊓ᶜ c′ ≡ c
  ⊓ᶜ-yes {c} {c′} p with c ⊑? c′
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p p)

  ⊓ᶜ-no : ∀ {c c′} → ¬ (c ⊑ c′) → c ⊓ᶜ c′ ≡ c′
  ⊓ᶜ-no {c} {c′} ¬p with c ⊑? c′
  ... | yes p = ⊥-elim (¬p p)
  ... | no _  = refl

  ⊓ᶜ-yesᴺ : ∀ {c c′} → c N.⊑ c′ → c N.⊓ᶜ c′ ≡ c
  ⊓ᶜ-yesᴺ {c} {c′} p with c N.⊑? c′
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p p)

  ⊓ᶜ-noᴺ : ∀ {c c′} → ¬ (c N.⊑ c′) → c N.⊓ᶜ c′ ≡ c′
  ⊓ᶜ-noᴺ {c} {c′} ¬p with c N.⊑? c′
  ... | yes p = ⊥-elim (¬p p)
  ... | no _  = refl

sc-⊔ᶜ : ∀ c c′ → scᶜ (c N.⊔ᶜ c′) ≡ scᶜ c ⊔ᶜ scᶜ c′
sc-⊔ᶜ c c′ = case (c N.⊑? c′)
  where
    case : Dec (c N.⊑ c′) → scᶜ (c N.⊔ᶜ c′) ≡ scᶜ c ⊔ᶜ scᶜ c′
    case (yes p) = trans (cong scᶜ (⊔ᶜ-yesᴺ p)) (sym (⊔ᶜ-yes (scᶜ-⊑ p)))
    case (no ¬p) = trans (cong scᶜ (⊔ᶜ-noᴺ ¬p)) (sym (⊔ᶜ-no (λ q → ¬p (scᶜ-⊑⁻ q))))

sc-⊓ᶜ : ∀ c c′ → scᶜ (c N.⊓ᶜ c′) ≡ scᶜ c ⊓ᶜ scᶜ c′
sc-⊓ᶜ c c′ = case (c N.⊑? c′)
  where
    case : Dec (c N.⊑ c′) → scᶜ (c N.⊓ᶜ c′) ≡ scᶜ c ⊓ᶜ scᶜ c′
    case (yes p) = trans (cong scᶜ (⊓ᶜ-yesᴺ p)) (sym (⊓ᶜ-yes (scᶜ-⊑ p)))
    case (no ¬p) = trans (cong scᶜ (⊓ᶜ-noᴺ ¬p)) (sym (⊓ᶜ-no (λ q → ¬p (scᶜ-⊑⁻ q))))

sc-⊓ʰ : ∀ h h′ → scʰ (h Z.⊓ʰ h′) ≡ scʰ h ⊓ʰ scʰ h′
sc-⊓ʰ (N.fin c) (N.fin c′) = cong fin (sc-⊓ᶜ c c′)
sc-⊓ʰ (N.fin c) N.∞        = refl
sc-⊓ʰ N.∞       h′         = refl

------------------------------------------------------------------------
-- Being inhabited

sc-◁ : ∀ c h → c N.◁ h → scᶜ c ◁ scʰ h
sc-◁ c (N.fin c′) r q = r (scᶜ-⊑⁻ q)
sc-◁ c N.∞        _   = tt

sc-◁⁻ : ∀ c h → scᶜ c ◁ scʰ h → c N.◁ h
sc-◁⁻ c (N.fin c′) r q = r (scᶜ-⊑ q)
sc-◁⁻ c N.∞        _   = tt

sc-Inh : ∀ Z → Z.Inh Z ⇔ Inh (scZ Z)
sc-Inh Z = mk⇔ (sc-◁ (Z.loᶻ Z) (Z.hiᶻ Z)) (sc-◁⁻ (Z.loᶻ Z) (Z.hiᶻ Z))

private
  raise-yes : ∀ {c h} → c ◁ h → raise c h ≡ ∞
  raise-yes {c} {h} p with c ◁? h
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p p)

  raise-no : ∀ {c h} → ¬ (c ◁ h) → raise c h ≡ h
  raise-no {c} {h} ¬p with c ◁? h
  ... | yes p = ⊥-elim (¬p p)
  ... | no _  = refl

  raise-yesᴺ : ∀ {c h} → c N.◁ h → Z.raise c h ≡ N.∞
  raise-yesᴺ {c} {h} p with c N.◁? h
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p p)

  raise-noᴺ : ∀ {c h} → ¬ (c N.◁ h) → Z.raise c h ≡ h
  raise-noᴺ {c} {h} ¬p with c N.◁? h
  ... | yes p = ⊥-elim (¬p p)
  ... | no _  = refl

sc-raise : ∀ c h → scʰ (Z.raise c h) ≡ raise (scᶜ c) (scʰ h)
sc-raise c h = case (c N.◁? h)
  where
    case : Dec (c N.◁ h) → scʰ (Z.raise c h) ≡ raise (scᶜ c) (scʰ h)
    case (yes p) = trans (cong scʰ (raise-yesᴺ p)) (sym (raise-yes (sc-◁ c h p)))
    case (no ¬p) = trans (cong scʰ (raise-noᴺ ¬p)) (sym (raise-no (λ q → ¬p (sc-◁⁻ c h q))))

------------------------------------------------------------------------
-- The operations

sc-flip : ∀ s → scˢ (DN.flip s) ≡ DT.flip (scˢ s)
sc-flip N.⁻ = refl
sc-flip N.⁺ = refl

sc-−ₗ : ∀ c h → scᶜ (c Z.−ₗ h) ≡ scᶜ c −ₗ scʰ h
sc-−ₗ (p N.∣ s) (N.fin (q N.∣ u)) =
  cong₂ _∣_ (×-∸ p q) (trans (scˢ-∨ s (DN.flip u)) (cong (scˢ s ∨ˢ_) (sc-flip u)))
sc-−ₗ (p N.∣ s) N.∞ = refl

sc-−ₕ : ∀ h c → scʰ (h Z.−ₕ c) ≡ scʰ h −ₕ scᶜ c
sc-−ₕ (N.fin (r N.∣ s′)) (p N.∣ s) =
  cong fin (cong₂ _∣_ (×-∸ r p) (trans (scˢ-∧ s′ (DN.flip s)) (cong (scˢ s′ ∧ˢ_) (sc-flip s))))
sc-−ₕ N.∞ _ = refl

sc-⊕ : ∀ Z W → scZ (Z Z.⊕ᶻ W) ≡ scZ Z ⊕ᶻ scZ W
sc-⊕ Z W = cong₂ ⟨_,_⟩ᶻ (scᶜ-+ˡ (Z.loᶻ Z) (Z.loᶻ W)) (scʰ-+ʰ (Z.hiᶻ Z) (Z.hiᶻ W))

sc-∩ : ∀ Z W → scZ (Z Z.∩ᶻ W) ≡ scZ Z ∩ᶻ scZ W
sc-∩ Z W = cong₂ ⟨_,_⟩ᶻ (sc-⊔ᶜ (Z.loᶻ Z) (Z.loᶻ W)) (sc-⊓ʰ (Z.hiᶻ Z) (Z.hiᶻ W))

sc-⊖ : ∀ C I → scZ (C Z.⊖ᶻ I) ≡ scZ C ⊖ᶻ scZ I
sc-⊖ C I =
  cong₂ ⟨_,_⟩ᶻ (trans (sc-⊔ᶜ N.0⁺ (Z.loᶻ C Z.−ₗ Z.hiᶻ I)) (cong (0⁺ ⊔ᶜ_) (sc-−ₗ (Z.loᶻ C) (Z.hiᶻ I))))
               (sc-−ₕ (Z.hiᶻ C) (Z.loᶻ I))
