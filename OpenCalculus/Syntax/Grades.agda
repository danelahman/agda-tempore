------------------------------------------------------------------
-- Open resource-grade and effect-grade expressions             --
--                                                              --
-- The closed grades of `Grades.Base` extended with variables   --
-- of a scope, products and binary joins. Resource expressions  --
-- embed effect expressions along the morphism `mapᵉ`; effect   --
-- expressions do not embed resource expressions.               --
------------------------------------------------------------------

open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)

open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (proj₁; proj₂)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (yes; no)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Syntax.Grades (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

-- Grade expressions have a join former and open types do not: `_⊔ₑ_`
-- and `_⊔ᵣ_` are total on closed grades, so a join of two open grade
-- expressions always denotes, whereas a join of open types, such as
-- `α₁ ⊔ᵛ α₂`, is defined only once the shapes are known.

-- Effect grade expressions

data EExp (Θ : Scope) : Set where
  evar   : EVar Θ → EExp Θ                   -- effect grade variable
  econst : E → EExp Θ                        -- closed effect grade
  _·̂ₑ_   : EExp Θ → EExp Θ → EExp Θ          -- multiplication
  _⊔̂ₑ_   : EExp Θ → EExp Θ → EExp Θ          -- binary join

infixl 7 _·̂ₑ_
infixl 6 _⊔̂ₑ_

-- Resource grade expressions

data RExp (Θ : Scope) : Set where
  rvar   : RVar Θ → RExp Θ                   -- resource grade variable
  rconst : R → RExp Θ                        -- closed resource grade
  _·̂ᵣ_   : RExp Θ → RExp Θ → RExp Θ          -- multiplication
  _⊔̂ᵣ_   : RExp Θ → RExp Θ → RExp Θ          -- binary join
  ∣_∣̂ᵉ   : EExp Θ → RExp Θ                   -- image of an effect grade under `mapᵉ`

infixl 7 _·̂ᵣ_
infixl 6 _⊔̂ᵣ_

-- Units (there are no separate unit constructors; the constants subsume them)

ûₑ : ∀ {Θ} → EExp Θ
ûₑ = econst uₑ

ûᵣ : ∀ {Θ} → RExp Θ
ûᵣ = rconst uᵣ

-- Action of the scope extensions on expressions

wkᵗ-e : ∀ {Θ} → EExp Θ → EExp (Θ +ty)
wkᵗ-e {Θ} (evar i)   = evar (wkᵗ-ev Θ i)
wkᵗ-e     (econst ε) = econst ε
wkᵗ-e     (ε ·̂ₑ ε')  = wkᵗ-e ε ·̂ₑ wkᵗ-e ε'
wkᵗ-e     (ε ⊔̂ₑ ε')  = wkᵗ-e ε ⊔̂ₑ wkᵗ-e ε'

wkʳ-e : ∀ {Θ} → EExp Θ → EExp (Θ +r)
wkʳ-e {Θ} (evar i)   = evar (wkʳ-ev Θ i)
wkʳ-e     (econst ε) = econst ε
wkʳ-e     (ε ·̂ₑ ε')  = wkʳ-e ε ·̂ₑ wkʳ-e ε'
wkʳ-e     (ε ⊔̂ₑ ε')  = wkʳ-e ε ⊔̂ₑ wkʳ-e ε'

wkᵉ-e : ∀ {Θ} → EExp Θ → EExp (Θ +e)
wkᵉ-e {Θ} (evar i)   = evar (wkᵉ-ev Θ i)
wkᵉ-e     (econst ε) = econst ε
wkᵉ-e     (ε ·̂ₑ ε')  = wkᵉ-e ε ·̂ₑ wkᵉ-e ε'
wkᵉ-e     (ε ⊔̂ₑ ε')  = wkᵉ-e ε ⊔̂ₑ wkᵉ-e ε'

wkᵗ-r : ∀ {Θ} → RExp Θ → RExp (Θ +ty)
wkᵗ-r {Θ} (rvar i)   = rvar (wkᵗ-rv Θ i)
wkᵗ-r     (rconst ρ) = rconst ρ
wkᵗ-r     (ρ ·̂ᵣ ρ')  = wkᵗ-r ρ ·̂ᵣ wkᵗ-r ρ'
wkᵗ-r     (ρ ⊔̂ᵣ ρ')  = wkᵗ-r ρ ⊔̂ᵣ wkᵗ-r ρ'
wkᵗ-r     ∣ ε ∣̂ᵉ     = ∣ wkᵗ-e ε ∣̂ᵉ

wkʳ-r : ∀ {Θ} → RExp Θ → RExp (Θ +r)
wkʳ-r {Θ} (rvar i)   = rvar (wkʳ-rv Θ i)
wkʳ-r     (rconst ρ) = rconst ρ
wkʳ-r     (ρ ·̂ᵣ ρ')  = wkʳ-r ρ ·̂ᵣ wkʳ-r ρ'
wkʳ-r     (ρ ⊔̂ᵣ ρ')  = wkʳ-r ρ ⊔̂ᵣ wkʳ-r ρ'
wkʳ-r     ∣ ε ∣̂ᵉ     = ∣ wkʳ-e ε ∣̂ᵉ

wkᵉ-r : ∀ {Θ} → RExp Θ → RExp (Θ +e)
wkᵉ-r {Θ} (rvar i)   = rvar (wkᵉ-rv Θ i)
wkᵉ-r     (rconst ρ) = rconst ρ
wkᵉ-r     (ρ ·̂ᵣ ρ')  = wkᵉ-r ρ ·̂ᵣ wkᵉ-r ρ'
wkᵉ-r     (ρ ⊔̂ᵣ ρ')  = wkᵉ-r ρ ⊔̂ᵣ wkᵉ-r ρ'
wkᵉ-r     ∣ ε ∣̂ᵉ     = ∣ wkᵉ-e ε ∣̂ᵉ

-- Sameness of expressions: equal formers, the same variables, and
-- equivalent constants. Decidable, the constants deciding by the grade
-- interface's `_≃?_`.

infix 4 _≅ᵉ_ _≅ʳ_ _≟ᵉ_ _≟ʳ_ _≡ᵉ?_ _≡ʳ?_

data _≅ᵉ_ {Θ} : EExp Θ → EExp Θ → Set where
  evar≅   : ∀ {i} → evar i ≅ᵉ evar i
  econst≅ : ∀ {c c'} → c ≃ₑ c' → econst c ≅ᵉ econst c'
  ·≅      : ∀ {ε₁ ε₁' ε₂ ε₂'} → ε₁ ≅ᵉ ε₁' → ε₂ ≅ᵉ ε₂' → ε₁ ·̂ₑ ε₂ ≅ᵉ ε₁' ·̂ₑ ε₂'
  ⊔≅      : ∀ {ε₁ ε₁' ε₂ ε₂'} → ε₁ ≅ᵉ ε₁' → ε₂ ≅ᵉ ε₂' → ε₁ ⊔̂ₑ ε₂ ≅ᵉ ε₁' ⊔̂ₑ ε₂'

data _≅ʳ_ {Θ} : RExp Θ → RExp Θ → Set where
  rvar≅   : ∀ {i} → rvar i ≅ʳ rvar i
  rconst≅ : ∀ {c c'} → c ≃ᵣ c' → rconst c ≅ʳ rconst c'
  ·≅      : ∀ {ρ₁ ρ₁' ρ₂ ρ₂'} → ρ₁ ≅ʳ ρ₁' → ρ₂ ≅ʳ ρ₂' → ρ₁ ·̂ᵣ ρ₂ ≅ʳ ρ₁' ·̂ᵣ ρ₂'
  ⊔≅      : ∀ {ρ₁ ρ₁' ρ₂ ρ₂'} → ρ₁ ≅ʳ ρ₁' → ρ₂ ≅ʳ ρ₂' → ρ₁ ⊔̂ᵣ ρ₂ ≅ʳ ρ₁' ⊔̂ᵣ ρ₂'
  ∣∣≅     : ∀ {ε ε'} → ε ≅ᵉ ε' → ∣ ε ∣̂ᵉ ≅ʳ ∣ ε' ∣̂ᵉ

≅ᵉ-refl : ∀ {Θ} {ε : EExp Θ} → ε ≅ᵉ ε
≅ᵉ-refl {ε = evar i}   = evar≅
≅ᵉ-refl {ε = econst c} = econst≅ ≃ₑ-refl
≅ᵉ-refl {ε = ε ·̂ₑ ε'}  = ·≅ ≅ᵉ-refl ≅ᵉ-refl
≅ᵉ-refl {ε = ε ⊔̂ₑ ε'}  = ⊔≅ ≅ᵉ-refl ≅ᵉ-refl

≅ʳ-refl : ∀ {Θ} {ρ : RExp Θ} → ρ ≅ʳ ρ
≅ʳ-refl {ρ = rvar i}   = rvar≅
≅ʳ-refl {ρ = rconst c} = rconst≅ ≃ᵣ-refl
≅ʳ-refl {ρ = ρ ·̂ᵣ ρ'}  = ·≅ ≅ʳ-refl ≅ʳ-refl
≅ʳ-refl {ρ = ρ ⊔̂ᵣ ρ'}  = ⊔≅ ≅ʳ-refl ≅ʳ-refl
≅ʳ-refl {ρ = ∣ ε ∣̂ᵉ}   = ∣∣≅ ≅ᵉ-refl

_≟ᵉ_ : ∀ {Θ} → Decidable (_≅ᵉ_ {Θ})
_≟ʳ_ : ∀ {Θ} → Decidable (_≅ʳ_ {Θ})

evar i     ≟ᵉ evar j     with i ≟ᶠ j
... | yes refl = yes evar≅
... | no  ¬p   = no λ { evar≅ → ¬p refl }
econst c   ≟ᵉ econst c'  with c ≃ₑ? c'
... | yes p = yes (econst≅ p)
... | no ¬p = no λ { (econst≅ p) → ¬p p }
(ε₁ ·̂ₑ ε₂) ≟ᵉ (ε₁' ·̂ₑ ε₂') with ε₁ ≟ᵉ ε₁' | ε₂ ≟ᵉ ε₂'
... | yes p   | yes q    = yes (·≅ p q)
... | no  ¬p   | _        = no λ { (·≅ p _) → ¬p p }
... | _        | no ¬q    = no λ { (·≅ _ q) → ¬q q }
(ε₁ ⊔̂ₑ ε₂) ≟ᵉ (ε₁' ⊔̂ₑ ε₂') with ε₁ ≟ᵉ ε₁' | ε₂ ≟ᵉ ε₂'
... | yes p   | yes q    = yes (⊔≅ p q)
... | no  ¬p   | _        = no λ { (⊔≅ p _) → ¬p p }
... | _        | no ¬q    = no λ { (⊔≅ _ q) → ¬q q }
evar _     ≟ᵉ econst _   = no λ ()
evar _     ≟ᵉ (_ ·̂ₑ _)   = no λ ()
evar _     ≟ᵉ (_ ⊔̂ₑ _)   = no λ ()
econst _   ≟ᵉ evar _     = no λ ()
econst _   ≟ᵉ (_ ·̂ₑ _)   = no λ ()
econst _   ≟ᵉ (_ ⊔̂ₑ _)   = no λ ()
(_ ·̂ₑ _)   ≟ᵉ evar _     = no λ ()
(_ ·̂ₑ _)   ≟ᵉ econst _   = no λ ()
(_ ·̂ₑ _)   ≟ᵉ (_ ⊔̂ₑ _)   = no λ ()
(_ ⊔̂ₑ _)   ≟ᵉ evar _     = no λ ()
(_ ⊔̂ₑ _)   ≟ᵉ econst _   = no λ ()
(_ ⊔̂ₑ _)   ≟ᵉ (_ ·̂ₑ _)   = no λ ()

rvar i     ≟ʳ rvar j     with i ≟ᶠ j
... | yes refl = yes rvar≅
... | no  ¬p   = no λ { rvar≅ → ¬p refl }
rconst c   ≟ʳ rconst c'  with c ≃ᵣ? c'
... | yes p = yes (rconst≅ p)
... | no ¬p = no λ { (rconst≅ p) → ¬p p }
(ρ₁ ·̂ᵣ ρ₂) ≟ʳ (ρ₁' ·̂ᵣ ρ₂') with ρ₁ ≟ʳ ρ₁' | ρ₂ ≟ʳ ρ₂'
... | yes p   | yes q    = yes (·≅ p q)
... | no  ¬p   | _        = no λ { (·≅ p _) → ¬p p }
... | _        | no ¬q    = no λ { (·≅ _ q) → ¬q q }
(ρ₁ ⊔̂ᵣ ρ₂) ≟ʳ (ρ₁' ⊔̂ᵣ ρ₂') with ρ₁ ≟ʳ ρ₁' | ρ₂ ≟ʳ ρ₂'
... | yes p   | yes q    = yes (⊔≅ p q)
... | no  ¬p   | _        = no λ { (⊔≅ p _) → ¬p p }
... | _        | no ¬q    = no λ { (⊔≅ _ q) → ¬q q }
∣ ε ∣̂ᵉ     ≟ʳ ∣ ε' ∣̂ᵉ    with ε ≟ᵉ ε'
... | yes p = yes (∣∣≅ p)
... | no ¬p = no λ { (∣∣≅ p) → ¬p p }
rvar _     ≟ʳ rconst _   = no λ ()
rvar _     ≟ʳ (_ ·̂ᵣ _)   = no λ ()
rvar _     ≟ʳ (_ ⊔̂ᵣ _)   = no λ ()
rvar _     ≟ʳ ∣ _ ∣̂ᵉ     = no λ ()
rconst _   ≟ʳ rvar _     = no λ ()
rconst _   ≟ʳ (_ ·̂ᵣ _)   = no λ ()
rconst _   ≟ʳ (_ ⊔̂ᵣ _)   = no λ ()
rconst _   ≟ʳ ∣ _ ∣̂ᵉ     = no λ ()
(_ ·̂ᵣ _)   ≟ʳ rvar _     = no λ ()
(_ ·̂ᵣ _)   ≟ʳ rconst _   = no λ ()
(_ ·̂ᵣ _)   ≟ʳ (_ ⊔̂ᵣ _)   = no λ ()
(_ ·̂ᵣ _)   ≟ʳ ∣ _ ∣̂ᵉ     = no λ ()
(_ ⊔̂ᵣ _)   ≟ʳ rvar _     = no λ ()
(_ ⊔̂ᵣ _)   ≟ʳ rconst _   = no λ ()
(_ ⊔̂ᵣ _)   ≟ʳ (_ ·̂ᵣ _)   = no λ ()
(_ ⊔̂ᵣ _)   ≟ʳ ∣ _ ∣̂ᵉ     = no λ ()
∣ _ ∣̂ᵉ     ≟ʳ rvar _     = no λ ()
∣ _ ∣̂ᵉ     ≟ʳ rconst _   = no λ ()
∣ _ ∣̂ᵉ     ≟ʳ (_ ·̂ᵣ _)   = no λ ()
∣ _ ∣̂ᵉ     ≟ʳ (_ ⊔̂ᵣ _)   = no λ ()

-- Same expressions are equal where they compare no constants

≅ᵉ⇒≡? : ∀ {Θ} {ε ε' : EExp Θ} → ε ≅ᵉ ε' → Maybe (ε ≡ ε')
≅ᵉ⇒≡? evar≅ = just refl
≅ᵉ⇒≡? (econst≅ e) = nothing
≅ᵉ⇒≡? (·≅ p q) with ≅ᵉ⇒≡? p | ≅ᵉ⇒≡? q
... | just refl | just refl = just refl
... | _         | _         = nothing
≅ᵉ⇒≡? (⊔≅ p q) with ≅ᵉ⇒≡? p | ≅ᵉ⇒≡? q
... | just refl | just refl = just refl
... | _         | _         = nothing

≅ʳ⇒≡? : ∀ {Θ} {ρ ρ' : RExp Θ} → ρ ≅ʳ ρ' → Maybe (ρ ≡ ρ')
≅ʳ⇒≡? rvar≅ = just refl
≅ʳ⇒≡? (rconst≅ e) = nothing
≅ʳ⇒≡? (·≅ p q) with ≅ʳ⇒≡? p | ≅ʳ⇒≡? q
... | just refl | just refl = just refl
... | _         | _         = nothing
≅ʳ⇒≡? (⊔≅ p q) with ≅ʳ⇒≡? p | ≅ʳ⇒≡? q
... | just refl | just refl = just refl
... | _         | _         = nothing
≅ʳ⇒≡? (∣∣≅ p) with ≅ᵉ⇒≡? p
... | just refl = just refl
... | nothing   = nothing

_≡ᵉ?_ : ∀ {Θ} → (ε ε' : EExp Θ) → Maybe (ε ≡ ε')
ε ≡ᵉ? ε' with ε ≟ᵉ ε'
... | yes p = ≅ᵉ⇒≡? p
... | no _  = nothing

_≡ʳ?_ : ∀ {Θ} → (ρ ρ' : RExp Θ) → Maybe (ρ ≡ ρ')
ρ ≡ʳ? ρ' with ρ ≟ʳ ρ'
... | yes p = ≅ʳ⇒≡? p
... | no _  = nothing

-- Values of closed grade expressions

valᵉ : EExp ∅ˢ → E
valᵉ (evar ())
valᵉ (econst c) = c
valᵉ (ε ·̂ₑ ε')  = valᵉ ε ·ₑ valᵉ ε'
valᵉ (ε ⊔̂ₑ ε')  = valᵉ ε ⊔ₑ valᵉ ε'

valʳ : RExp ∅ˢ → R
valʳ (rvar ())
valʳ (rconst c) = c
valʳ (ρ ·̂ᵣ ρ')  = valʳ ρ ·ᵣ valʳ ρ'
valʳ (ρ ⊔̂ᵣ ρ')  = valʳ ρ ⊔ᵣ valʳ ρ'
valʳ ∣ ε ∣̂ᵉ     = mapᵉ (valᵉ ε)
