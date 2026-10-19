------------------------------------------------------------------------
-- Timed traces along a morphism of durations.                         --
--                                                                    --
-- A monoid morphism `h` between time domains that keeps positive     --
-- durations positive maps traces to traces, delay by delay: the      --
-- delay `d` becomes the delay `h d`. The map is a morphism of the    --
-- trace monoid, sends the pure delay by `τ` to the pure delay by     --
-- `h τ`, scales durations by `h`, and is monotone for the allowance  --
-- and coverage orders, each taken at the costs mapped by `h`.        --
-- Monotonicity of `h`, and its compatibility with the truncated       --
-- difference, follow from it being a morphism of canonically ordered --
-- monoids.                                                           --
--                                                                    --
-- The inclusion `ℕ→ℚ≥0ᴰ` of whole steps into dense time is the       --
-- instance the grade morphisms of `Example.Traces.Timed.Morphism`    --
-- are built on.                                                      --
------------------------------------------------------------------------

open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain; _→ᴰ_)

module Syntax.Grades.Traces.Along
  {D₁ D₂ : Duration} (T₁ : TimeDomain D₁) (T₂ : TimeDomain D₂)
  (h : D₁ →ᴰ D₂)
  (h-pos : (τ : Duration.Carrier D₁)
         → TimeDomain._≤ᴰ_ T₂ (_→ᴰ_.map h τ) (Duration.0ᴰ D₂)
         → TimeDomain._≤ᴰ_ T₁ τ (Duration.0ᴰ D₁))
  (Op : Set) where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)

import Syntax.Durations.Monus as Monus
module M₁ = Monus T₁
module M₂ = Monus T₂

import Syntax.Grades.Traces.Base as Base
module B₁ = Base T₁ Op
module B₂ = Base T₂ Op

open B₁ using (Trace; Trace⁻; ε; operation; delay; ε⁻; operation⁻; inj⁻; prepend)
open B₂ using () renaming (Trace to Trace₂; Trace⁻ to Trace₂⁻)

open _→ᴰ_ h renaming (map to hᴰ; map-0 to h-0; map-+ to h-+)

------------------------------------------------------------------------
-- The arithmetic of `h`

-- it is monotone

h-mono : ∀ {τ κ} → τ M₁.≤ᴰ κ → hᴰ τ M₂.≤ᴰ hᴰ κ
h-mono {τ} p with M₁.diff p
... | d , refl = M₂.≤ᴰ-intro (sym h-+)

-- it keeps positive durations positive

h-<0 : ∀ {τ} → M₁.0ᴰ M₁.<ᴰ τ → M₂.0ᴰ M₂.<ᴰ hᴰ τ
h-<0 {τ} p q = p (h-pos τ q)

-- and it commutes with the difference

h-∸ : ∀ {τ κ} → τ M₁.≤ᴰ κ → hᴰ (κ M₁.∸ᴰ τ) ≡ hᴰ κ M₂.∸ᴰ hᴰ τ
h-∸ {τ} {κ} p = sym (M₂.∸-unique (trans (sym h-+) (cong hᴰ (M₁.+-∸ p))))

------------------------------------------------------------------------
-- Traces

map⁺ : B₁.D⁺ → B₂.D⁺
map⁺ d = B₂.pos⁺ (hᴰ B₁.∣ d ∣⁺) (h-<0 (B₁.∣∣⁺-pos d))

map⁺-+ : (d e : B₁.D⁺) → map⁺ (d B₁.+⁺ e) ≡ map⁺ d B₂.+⁺ map⁺ e
map⁺-+ d e = B₂.∣∣⁺-inj h-+

mutual
  mapᵀ : Trace → Trace₂
  mapᵀ ε               = B₂.ε
  mapᵀ (operation o t) = B₂.operation o (mapᵀ t)
  mapᵀ (delay d t⁻)    = B₂.delay (map⁺ d) (mapᵀ⁻ t⁻)

  mapᵀ⁻ : Trace⁻ → Trace₂⁻
  mapᵀ⁻ ε⁻               = B₂.ε⁻
  mapᵀ⁻ (operation⁻ o t) = B₂.operation⁻ o (mapᵀ t)

mapᵀ-inj⁻ : (t⁻ : Trace⁻) → mapᵀ (inj⁻ t⁻) ≡ B₂.inj⁻ (mapᵀ⁻ t⁻)
mapᵀ-inj⁻ ε⁻               = refl
mapᵀ-inj⁻ (operation⁻ o t) = refl

mapᵀ-prepend : (d : B₁.D⁺) (t : Trace) → mapᵀ (prepend d t) ≡ B₂.prepend (map⁺ d) (mapᵀ t)
mapᵀ-prepend d ε               = refl
mapᵀ-prepend d (operation o t) = refl
mapᵀ-prepend d (delay e t⁻)    = cong (λ x → B₂.delay x (mapᵀ⁻ t⁻)) (map⁺-+ d e)

mapᵀ-∙ : (s t : Trace) → mapᵀ (s B₁.∙ t) ≡ mapᵀ s B₂.∙ mapᵀ t
mapᵀ-∙ ε                          t = refl
mapᵀ-∙ (operation o s)            t = cong (B₂.operation o) (mapᵀ-∙ s t)
mapᵀ-∙ (delay d ε⁻)               t = mapᵀ-prepend d t
mapᵀ-∙ (delay d (operation⁻ o s)) t =
  cong (λ z → B₂.delay (map⁺ d) (B₂.operation⁻ o z)) (mapᵀ-∙ s t)

mapᵀ-⟨⟩ : (τ : Duration.Carrier D₁) → mapᵀ (B₁.⟨ τ ⟩) ≡ B₂.⟨ hᴰ τ ⟩
mapᵀ-⟨⟩ τ = case (M₁.0ᴰ M₁.<ᴰ? τ)
  where
    case : (p : Dec (M₁.0ᴰ M₁.<ᴰ τ)) → mapᵀ (B₁.delay-of τ p) ≡ B₂.⟨ hᴰ τ ⟩
    case (yes p) = sym (trans (B₂.⟨⟩-pos (hᴰ τ) (h-<0 p))
                                (cong (λ x → B₂.delay x B₂.ε⁻) (B₂.∣∣⁺-inj refl)))
    case (no ¬p) =
      sym (B₂.⟨⟩-zero (hᴰ τ)
             (λ q → M₂.<-irrefl (subst (M₂.0ᴰ M₂.<ᴰ_)
                                       (trans (cong hᴰ (M₁.≮0⇒≡0 ¬p)) h-0) q)))

------------------------------------------------------------------------
-- Durations scale by `h`

module Durations (c : Op → Duration.Carrier D₁) where

  open import Syntax.Grades.Traces.Durations T₁ Op using () renaming (module Durations to Dur₁)
  open import Syntax.Grades.Traces.Durations T₂ Op using () renaming (module Durations to Dur₂)

  open Dur₁ c using (duration; duration⁻)
  open Dur₂ (λ o → hᴰ (c o)) using () renaming (duration to duration₂; duration⁻ to duration₂⁻)

  mutual
    duration-mapᵀ : (t : Trace) → duration₂ (mapᵀ t) ≡ hᴰ (duration t)
    duration-mapᵀ ε               = sym h-0
    duration-mapᵀ (operation o t) = trans (cong (hᴰ (c o) M₂.+ᴰ_) (duration-mapᵀ t)) (sym h-+)
    duration-mapᵀ (delay d t⁻)    =
      trans (cong (hᴰ B₁.∣ d ∣⁺ M₂.+ᴰ_) (duration-mapᵀ⁻ t⁻)) (sym h-+)

    duration-mapᵀ⁻ : (t⁻ : Trace⁻) → duration₂⁻ (mapᵀ⁻ t⁻) ≡ hᴰ (duration⁻ t⁻)
    duration-mapᵀ⁻ ε⁻               = sym h-0
    duration-mapᵀ⁻ (operation⁻ o t) = trans (cong (hᴰ (c o) M₂.+ᴰ_) (duration-mapᵀ t)) (sym h-+)

------------------------------------------------------------------------
-- The allowance order

module Allowance (costʰⁱ : Op → Duration.Carrier D₁) where

  open import Syntax.Grades.Traces.Allowance.Core T₁ Op costʰⁱ as A₁
  open import Syntax.Grades.Traces.Allowance.Core T₂ Op (λ o → hᴰ (costʰⁱ o)) as A₂
    using ()

  mapᵀ-≼ᵃ : ∀ {k s t} → s A₁.≼ᵃ[ k ] t → mapᵀ s A₂.≼ᵃ[ hᴰ k ] mapᵀ t
  mapᵀ-≼ᵃ nil = A₂.nil
  mapᵀ-≼ᵃ (keep p) = A₂.keep (A₂.coe h-0 (mapᵀ-≼ᵃ p))
  mapᵀ-≼ᵃ (skip-op p) = A₂.skip-op (mapᵀ-≼ᵃ p)
  mapᵀ-≼ᵃ {k} (bank-delay {e = e} {s = s} {t⁻ = t⁻} p) =
    A₂.bank-delay (subst₂ (λ x y → mapᵀ s A₂.≼ᵃ[ x ] y) h-+ (mapᵀ-inj⁻ t⁻) (mapᵀ-≼ᵃ p))
  mapᵀ-≼ᵃ {k} (use-delay {d = d} {s⁻ = s⁻} le p) =
    A₂.use-delay (h-mono le)
      (subst₂ (λ x y → x A₂.≼ᵃ[ _ ] y) (mapᵀ-inj⁻ s⁻) refl
              (A₂.coe (h-∸ le) (mapᵀ-≼ᵃ p)))
  mapᵀ-≼ᵃ {k} (use-op le p) = A₂.use-op (h-mono le) (A₂.coe (h-∸ le) (mapᵀ-≼ᵃ p))

  mapᵀ-≼ᵃ₀ : ∀ {s t} → s A₁.≼ᵃ t → mapᵀ s A₂.≼ᵃ mapᵀ t
  mapᵀ-≼ᵃ₀ p = A₂.coe h-0 (mapᵀ-≼ᵃ p)

------------------------------------------------------------------------
-- The coverage order

module Coverage (costˡᵒ : Op → Duration.Carrier D₁) where

  open import Syntax.Grades.Traces.Coverage.Core T₁ Op costˡᵒ as C₁
  open import Syntax.Grades.Traces.Coverage.Core T₂ Op (λ o → hᴰ (costˡᵒ o)) as C₂
    using ()

  mapᵀ-≼ᶜ : ∀ {k s t} → s C₁.≼ᶜ[ k ] t → mapᵀ s C₂.≼ᶜ[ hᴰ k ] mapᵀ t
  mapᵀ-≼ᶜ nil = C₂.nil
  mapᵀ-≼ᶜ (keep p) = C₂.keep (C₂.coe h-0 (mapᵀ-≼ᶜ p))
  mapᵀ-≼ᶜ (pay-op p) = C₂.pay-op (C₂.coe h-+ (mapᵀ-≼ᶜ p))
  mapᵀ-≼ᶜ (del-delay {e = e} {s = s} {t⁻ = t⁻} p) =
    C₂.del-delay (subst₂ (λ x y → mapᵀ s C₂.≼ᶜ[ x ] y) h-+ (mapᵀ-inj⁻ t⁻) (mapᵀ-≼ᶜ p))
  mapᵀ-≼ᶜ (use-delay {d = d} {s⁻ = s⁻} le p) =
    C₂.use-delay (h-mono le)
      (subst₂ (λ x y → x C₂.≼ᶜ[ _ ] y) (mapᵀ-inj⁻ s⁻) refl
              (C₂.coe (h-∸ le) (mapᵀ-≼ᶜ p)))

  mapᵀ-≼ᶜ₀ : ∀ {s t} → s C₁.≼ᶜ t → mapᵀ s C₂.≼ᶜ mapᵀ t
  mapᵀ-≼ᶜ₀ p = C₂.coe h-0 (mapᵀ-≼ᶜ p)
