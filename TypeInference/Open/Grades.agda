------------------------------------------------------------------
-- Open resource-grade and effect-grade expressions               --
--                                                                --
-- Grade expressions of the mirrored language: the closed grades  --
-- of `Syntax.Grades` extended with variables drawn from a scope. --
-- Resource expressions may embed effect expressions (the `mapᵉ`  --
-- morphism), but not the other way round.                        --
------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec

open import TypeInference.Scopes

module TypeInference.Open.Grades (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

-- Effect grade expressions

data EExp (Θ : Scope) : Set where
  evar   : EVar Θ → EExp Θ                   -- effect grade variable
  econst : E → EExp Θ                        -- closed effect grade
  _·̂ₑ_   : EExp Θ → EExp Θ → EExp Θ          -- multiplication

infixl 7 _·̂ₑ_

-- Resource grade expressions

data RExp (Θ : Scope) : Set where
  rvar   : RVar Θ → RExp Θ                   -- resource grade variable
  rconst : R → RExp Θ                        -- closed resource grade
  _·̂ᵣ_   : RExp Θ → RExp Θ → RExp Θ          -- multiplication
  ∣_∣̂ᵉ   : EExp Θ → RExp Θ                   -- image of an effect grade under `mapᵉ`

infixl 7 _·̂ᵣ_

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

wkʳ-e : ∀ {Θ} → EExp Θ → EExp (Θ +r)
wkʳ-e {Θ} (evar i)   = evar (wkʳ-ev Θ i)
wkʳ-e     (econst ε) = econst ε
wkʳ-e     (ε ·̂ₑ ε')  = wkʳ-e ε ·̂ₑ wkʳ-e ε'

wkᵉ-e : ∀ {Θ} → EExp Θ → EExp (Θ +e)
wkᵉ-e {Θ} (evar i)   = evar (wkᵉ-ev Θ i)
wkᵉ-e     (econst ε) = econst ε
wkᵉ-e     (ε ·̂ₑ ε')  = wkᵉ-e ε ·̂ₑ wkᵉ-e ε'

wkᵗ-r : ∀ {Θ} → RExp Θ → RExp (Θ +ty)
wkᵗ-r {Θ} (rvar i)   = rvar (wkᵗ-rv Θ i)
wkᵗ-r     (rconst ρ) = rconst ρ
wkᵗ-r     (ρ ·̂ᵣ ρ')  = wkᵗ-r ρ ·̂ᵣ wkᵗ-r ρ'
wkᵗ-r     ∣ ε ∣̂ᵉ     = ∣ wkᵗ-e ε ∣̂ᵉ

wkʳ-r : ∀ {Θ} → RExp Θ → RExp (Θ +r)
wkʳ-r {Θ} (rvar i)   = rvar (wkʳ-rv Θ i)
wkʳ-r     (rconst ρ) = rconst ρ
wkʳ-r     (ρ ·̂ᵣ ρ')  = wkʳ-r ρ ·̂ᵣ wkʳ-r ρ'
wkʳ-r     ∣ ε ∣̂ᵉ     = ∣ wkʳ-e ε ∣̂ᵉ

wkᵉ-r : ∀ {Θ} → RExp Θ → RExp (Θ +e)
wkᵉ-r {Θ} (rvar i)   = rvar (wkᵉ-rv Θ i)
wkᵉ-r     (rconst ρ) = rconst ρ
wkᵉ-r     (ρ ·̂ᵣ ρ')  = wkᵉ-r ρ ·̂ᵣ wkᵉ-r ρ'
wkᵉ-r     ∣ ε ∣̂ᵉ     = ∣ wkᵉ-e ε ∣̂ᵉ
