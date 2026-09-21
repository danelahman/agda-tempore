------------------------------------------------------------------
-- Deciding an entailed ordering of open grade expressions        --
--                                                                --
-- Both sides are put in the product normal form of               --
-- `SolverImpl.Product` and compared atom by atom, the answer     --
-- glued back with `eqᵣ`/`monoᵣ`/`transᵣ`. A left side whose      --
-- atoms all cancel is the unit, and is then below anything by    --
-- `minᵣ`/`minₑ`, provided the corresponding unit-minimality      --
-- option is supplied.                                            --
--                                                                --
-- `⊩-reflectᵣ`/`⊩-reflectₑ` are the closed special case: a       --
-- variable-free expression is convertible to the constant it     --
-- evaluates to, in both directions.                              --
------------------------------------------------------------------

open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.Open.Hyps as H

module TypeInference.SolverImpl.Normal
  (S : LanguageSpec)
  (_≾ᵣ?_ : Decidable (Grade._≾_ (GradeSystem.RGrade (LanguageSpec.Grades S))))
  (_≾ₑ?_ : Decidable (Grade._≾_ (GradeSystem.EGrade (LanguageSpec.Grades S))))
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))              -- optional unit-minimality of `_≾ᵣ_`
  (umin?ₑ : Maybe (H.UnitMinₑ S))              -- optional unit-minimality of `_≾ₑ_`
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.Open.Grades S
open import TypeInference.Open.Hyps   S

open import TypeInference.SolverImpl.Product S public

atom≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
atom≾ₑ (ac c) (ac d) with c ≾ₑ? d
... | yes p = just (atomₑ p)
... | no _  = nothing
atom≾ₑ (av i) (av j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ₑ-refl
... | no _     = nothing
atom≾ₑ _ _ = nothing

list≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (as bs : List (EAtom Θ))
       → Maybe (Q ⊩ ⟦ as ⟧ᵉˢ ≾̂ₑ ⟦ bs ⟧ᵉˢ)
list≾ₑ []       []       = just ⊩≾̂ₑ-refl
list≾ₑ (a ∷ as) (b ∷ bs) with atom≾ₑ a b | list≾ₑ as bs
... | just p | just q = just (monoₑ p q)
... | _      | _      = nothing
list≾ₑ _ _ = nothing

-- A left-hand side whose atoms all cancel is the unit, and the unit is
-- below anything as soon as the option is supplied

min≾ₑ : ∀ {Θ} {Q : Hyps Θ} {ε : EExp Θ} → Maybe UnitMinₑ → (as : List (EAtom Θ))
      → ε ≡̂ₑ ⟦ as ⟧ᵉˢ → (ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
min≾ₑ (just p) []      q ε' = just (transₑ (eqₑ q) (minₑ p))
min≾ₑ _        _       _ _  = nothing

decide≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (ε ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
decide≾ₑ ε ε' with list≾ₑ (nrmₑ ε) (nrmₑ ε')
... | just p  = just (transₑ (eqₑ (nrmₑ-≡ ε)) (transₑ p (eqₑ (≡̂ₑ-sym (nrmₑ-≡ ε')))))
... | nothing = min≾ₑ umin?ₑ (nrmₑ ε) (nrmₑ-≡ ε) ε'

atom≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (a b : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
atom≾ᵣ (rc c) (rc d) with c ≾ᵣ? d
... | yes p = just (atomᵣ p)
... | no _  = nothing
atom≾ᵣ (rv i) (rv j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ᵣ-refl
... | no _     = nothing
atom≾ᵣ (rm i) (rm j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ᵣ-refl
... | no _     = nothing
atom≾ᵣ _ _ = nothing

list≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (as bs : List (RAtom Θ))
       → Maybe (Q ⊩ ⟦ as ⟧ʳˢ ≾̂ᵣ ⟦ bs ⟧ʳˢ)
list≾ᵣ []       []       = just ⊩≾̂ᵣ-refl
list≾ᵣ (a ∷ as) (b ∷ bs) with atom≾ᵣ a b | list≾ᵣ as bs
... | just p | just q = just (monoᵣ p q)
... | _      | _      = nothing
list≾ᵣ _ _ = nothing

min≾ᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → Maybe UnitMinᵣ → (as : List (RAtom Θ))
      → ρ ≡̂ᵣ ⟦ as ⟧ʳˢ → (ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
min≾ᵣ (just p) []      q ρ' = just (transᵣ (eqᵣ q) (minᵣ p))
min≾ᵣ _        _       _ _  = nothing

decide≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (ρ ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
decide≾ᵣ ρ ρ' with list≾ᵣ (nrmᵣ ρ) (nrmᵣ ρ')
... | just p  = just (transᵣ (eqᵣ (nrmᵣ-≡ ρ)) (transᵣ p (eqᵣ (≡̂ᵣ-sym (nrmᵣ-≡ ρ')))))
... | nothing = min≾ᵣ umin?ᵣ (nrmᵣ ρ) (nrmᵣ-≡ ρ) ρ'

evalᵉ : EExp ∅ˢ → E
evalᵉ (evar ())
evalᵉ (econst c) = c
evalᵉ (ε ·̂ₑ ε')  = evalᵉ ε ·ₑ evalᵉ ε'

evalʳ : RExp ∅ˢ → R
evalʳ (rvar ())
evalʳ (rconst c) = c
evalʳ (ρ ·̂ᵣ ρ')  = evalʳ ρ ·ᵣ evalʳ ρ'
evalʳ ∣ ε ∣̂ᵉ     = mapᵉ (evalᵉ ε)

evalᵉ-≡ : (ε : EExp ∅ˢ) → ε ≡̂ₑ econst (evalᵉ ε)
evalᵉ-≡ (evar ())
evalᵉ-≡ (econst c) = ≡̂ₑ-refl
evalᵉ-≡ (ε ·̂ₑ ε')  =
  ≡̂ₑ-trans (≡̂ₑ-cong (evalᵉ-≡ ε) (evalᵉ-≡ ε')) ≡̂ₑ-const-·

evalʳ-≡ : (ρ : RExp ∅ˢ) → ρ ≡̂ᵣ rconst (evalʳ ρ)
evalʳ-≡ (rvar ())
evalʳ-≡ (rconst c) = ≡̂ᵣ-refl
evalʳ-≡ (ρ ·̂ᵣ ρ')  =
  ≡̂ᵣ-trans (≡̂ᵣ-cong (evalʳ-≡ ρ) (evalʳ-≡ ρ')) ≡̂ᵣ-const-·
evalʳ-≡ ∣ ε ∣̂ᵉ     =
  ≡̂ᵣ-trans (≡̂ᵣ-map-cong (evalᵉ-≡ ε)) ≡̂ᵣ-map-const

-- A closed expression and its value entail one another

⊩-reflectᵣ : (ρ : RExp ∅ˢ)
           → (∅ᴴ ⊩ ρ ≾̂ᵣ rconst (evalʳ ρ)) × (∅ᴴ ⊩ rconst (evalʳ ρ) ≾̂ᵣ ρ)
⊩-reflectᵣ ρ = eqᵣ (evalʳ-≡ ρ) , eqᵣ (≡̂ᵣ-sym (evalʳ-≡ ρ))

⊩-reflectₑ : (ε : EExp ∅ˢ)
           → (∅ᴴ ⊩ ε ≾̂ₑ econst (evalᵉ ε)) × (∅ᴴ ⊩ econst (evalᵉ ε) ≾̂ₑ ε)
⊩-reflectₑ ε = eqₑ (evalᵉ-≡ ε) , eqₑ (≡̂ₑ-sym (evalᵉ-≡ ε))
