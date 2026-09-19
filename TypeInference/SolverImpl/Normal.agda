------------------------------------------------------------------
-- Normalisation of open grade expressions                        --
--                                                                --
-- A grade expression is flattened to a list of atoms — constants, --
-- variables, and images of effect variables under `∣_∣̂ᵉ` —        --
-- with adjacent constants multiplied and units dropped. The       --
-- flattening is certified by `≡̂ᵣ`/`≡̂ₑ`, so the entailed ordering  --
-- of two expressions can be decided atom by atom and glued back   --
-- with `eqᵣ`/`monoᵣ`/`transᵣ`. A left side whose atoms all cancel --
-- is the unit, and is then below anything by `minᵣ`/`minₑ`,       --
-- provided the corresponding unit-minimality option is supplied.  --
--                                                                --
-- `⊩-reflectᵣ`/`⊩-reflectₑ` are the closed special case: a        --
-- variable-free expression is convertible to the constant it      --
-- evaluates to, in both directions.                               --
------------------------------------------------------------------

open import Data.Fin using (Fin)
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

data EAtom (Θ : Scope) : Set where
  ac : E → EAtom Θ
  av : EVar Θ → EAtom Θ

⟦_⟧ᵉᵃ : ∀ {Θ} → EAtom Θ → EExp Θ
⟦ ac c ⟧ᵉᵃ = econst c
⟦ av i ⟧ᵉᵃ = evar i

⟦_⟧ᵉˢ : ∀ {Θ} → List (EAtom Θ) → EExp Θ
⟦ [] ⟧ᵉˢ     = ûₑ
⟦ a ∷ as ⟧ᵉˢ = ⟦ a ⟧ᵉᵃ ·̂ₑ ⟦ as ⟧ᵉˢ

-- Consing an atom: constants are merged, units dropped

consₑ : ∀ {Θ} → EAtom Θ → List (EAtom Θ) → List (EAtom Θ)
consₑ (ac c) (ac d ∷ as) = consₑ (ac (c ·ₑ d)) as
consₑ (ac c) as with c ≡ₑ? uₑ
... | yes _ = as
... | no _  = ac c ∷ as
consₑ (av i) as = av i ∷ as

consₑ-≡ : ∀ {Θ} → (a : EAtom Θ) → (as : List (EAtom Θ))
        → ⟦ consₑ a as ⟧ᵉˢ ≡̂ₑ ⟦ a ⟧ᵉᵃ ·̂ₑ ⟦ as ⟧ᵉˢ
consₑ-≡ (ac c) (ac d ∷ as) =
  ≡̂ₑ-trans (consₑ-≡ (ac (c ·ₑ d)) as)
  (≡̂ₑ-trans (≡̂ₑ-cong (≡̂ₑ-sym ≡̂ₑ-const-·) ≡̂ₑ-refl) ≡̂ₑ-assoc)
consₑ-≡ (ac c) [] with c ≡ₑ? uₑ
... | yes refl = ≡̂ₑ-sym ≡̂ₑ-identityˡ
... | no _     = ≡̂ₑ-refl
consₑ-≡ (ac c) (av i ∷ as) with c ≡ₑ? uₑ
... | yes refl = ≡̂ₑ-sym ≡̂ₑ-identityˡ
... | no _     = ≡̂ₑ-refl
consₑ-≡ (av i) as = ≡̂ₑ-refl

appₑ : ∀ {Θ} → List (EAtom Θ) → List (EAtom Θ) → List (EAtom Θ)
appₑ []       ys = ys
appₑ (a ∷ as) ys = consₑ a (appₑ as ys)

appₑ-≡ : ∀ {Θ} → (as bs : List (EAtom Θ))
       → ⟦ appₑ as bs ⟧ᵉˢ ≡̂ₑ ⟦ as ⟧ᵉˢ ·̂ₑ ⟦ bs ⟧ᵉˢ
appₑ-≡ []       bs = ≡̂ₑ-sym ≡̂ₑ-identityˡ
appₑ-≡ (a ∷ as) bs =
  ≡̂ₑ-trans (consₑ-≡ a (appₑ as bs))
  (≡̂ₑ-trans (≡̂ₑ-cong ≡̂ₑ-refl (appₑ-≡ as bs)) (≡̂ₑ-sym ≡̂ₑ-assoc))

nrmₑ : ∀ {Θ} → EExp Θ → List (EAtom Θ)
nrmₑ (evar i)   = av i ∷ []
nrmₑ (econst c) = consₑ (ac c) []
nrmₑ (ε ·̂ₑ ε')  = appₑ (nrmₑ ε) (nrmₑ ε')

nrmₑ-≡ : ∀ {Θ} → (ε : EExp Θ) → ε ≡̂ₑ ⟦ nrmₑ ε ⟧ᵉˢ
nrmₑ-≡ (evar i)   = ≡̂ₑ-sym ≡̂ₑ-identityʳ
nrmₑ-≡ (econst c) = ≡̂ₑ-sym (≡̂ₑ-trans (consₑ-≡ (ac c) []) ≡̂ₑ-identityʳ)
nrmₑ-≡ (ε ·̂ₑ ε')  =
  ≡̂ₑ-trans (≡̂ₑ-cong (nrmₑ-≡ ε) (nrmₑ-≡ ε')) (≡̂ₑ-sym (appₑ-≡ (nrmₑ ε) (nrmₑ ε')))

data RAtom (Θ : Scope) : Set where
  rc : R → RAtom Θ
  rv : RVar Θ → RAtom Θ
  rm : EVar Θ → RAtom Θ

⟦_⟧ʳᵃ : ∀ {Θ} → RAtom Θ → RExp Θ
⟦ rc c ⟧ʳᵃ = rconst c
⟦ rv i ⟧ʳᵃ = rvar i
⟦ rm i ⟧ʳᵃ = ∣ evar i ∣̂ᵉ

⟦_⟧ʳˢ : ∀ {Θ} → List (RAtom Θ) → RExp Θ
⟦ [] ⟧ʳˢ     = ûᵣ
⟦ a ∷ as ⟧ʳˢ = ⟦ a ⟧ʳᵃ ·̂ᵣ ⟦ as ⟧ʳˢ

consᵣ : ∀ {Θ} → RAtom Θ → List (RAtom Θ) → List (RAtom Θ)
consᵣ (rc c) (rc d ∷ as) = consᵣ (rc (c ·ᵣ d)) as
consᵣ (rc c) as with c ≡ᵣ? uᵣ
... | yes _ = as
... | no _  = rc c ∷ as
consᵣ (rv i) as = rv i ∷ as
consᵣ (rm i) as = rm i ∷ as

consᵣ-≡ : ∀ {Θ} → (a : RAtom Θ) → (as : List (RAtom Θ))
        → ⟦ consᵣ a as ⟧ʳˢ ≡̂ᵣ ⟦ a ⟧ʳᵃ ·̂ᵣ ⟦ as ⟧ʳˢ
consᵣ-≡ (rc c) (rc d ∷ as) =
  ≡̂ᵣ-trans (consᵣ-≡ (rc (c ·ᵣ d)) as)
  (≡̂ᵣ-trans (≡̂ᵣ-cong (≡̂ᵣ-sym ≡̂ᵣ-const-·) ≡̂ᵣ-refl) ≡̂ᵣ-assoc)
consᵣ-≡ (rc c) [] with c ≡ᵣ? uᵣ
... | yes refl = ≡̂ᵣ-sym ≡̂ᵣ-identityˡ
... | no _     = ≡̂ᵣ-refl
consᵣ-≡ (rc c) (rv i ∷ as) with c ≡ᵣ? uᵣ
... | yes refl = ≡̂ᵣ-sym ≡̂ᵣ-identityˡ
... | no _     = ≡̂ᵣ-refl
consᵣ-≡ (rc c) (rm i ∷ as) with c ≡ᵣ? uᵣ
... | yes refl = ≡̂ᵣ-sym ≡̂ᵣ-identityˡ
... | no _     = ≡̂ᵣ-refl
consᵣ-≡ (rv i) as = ≡̂ᵣ-refl
consᵣ-≡ (rm i) as = ≡̂ᵣ-refl

appᵣ : ∀ {Θ} → List (RAtom Θ) → List (RAtom Θ) → List (RAtom Θ)
appᵣ []       ys = ys
appᵣ (a ∷ as) ys = consᵣ a (appᵣ as ys)

appᵣ-≡ : ∀ {Θ} → (as bs : List (RAtom Θ))
       → ⟦ appᵣ as bs ⟧ʳˢ ≡̂ᵣ ⟦ as ⟧ʳˢ ·̂ᵣ ⟦ bs ⟧ʳˢ
appᵣ-≡ []       bs = ≡̂ᵣ-sym ≡̂ᵣ-identityˡ
appᵣ-≡ (a ∷ as) bs =
  ≡̂ᵣ-trans (consᵣ-≡ a (appᵣ as bs))
  (≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl (appᵣ-≡ as bs)) (≡̂ᵣ-sym ≡̂ᵣ-assoc))

-- The image of an effect-atom list under `∣_∣̂ᵉ`

imgᵃ : ∀ {Θ} → EAtom Θ → RAtom Θ
imgᵃ (ac c) = rc (mapᵉ c)
imgᵃ (av i) = rm i

img : ∀ {Θ} → List (EAtom Θ) → List (RAtom Θ)
img []       = []
img (a ∷ as) = consᵣ (imgᵃ a) (img as)

imgᵃ-≡ : ∀ {Θ} → (a : EAtom Θ) → ∣ ⟦ a ⟧ᵉᵃ ∣̂ᵉ ≡̂ᵣ ⟦ imgᵃ a ⟧ʳᵃ
imgᵃ-≡ (ac c) = ≡̂ᵣ-map-const
imgᵃ-≡ (av i) = ≡̂ᵣ-refl

img-≡ : ∀ {Θ} → (as : List (EAtom Θ)) → ∣ ⟦ as ⟧ᵉˢ ∣̂ᵉ ≡̂ᵣ ⟦ img as ⟧ʳˢ
img-≡ []       = subst (λ x → ∣ ûₑ ∣̂ᵉ ≡̂ᵣ rconst x) map-uᵉ ≡̂ᵣ-map-const
img-≡ (a ∷ as) =
  ≡̂ᵣ-trans ≡̂ᵣ-map-·
  (≡̂ᵣ-trans (≡̂ᵣ-cong (imgᵃ-≡ a) (img-≡ as)) (≡̂ᵣ-sym (consᵣ-≡ (imgᵃ a) (img as))))

nrmᵣ : ∀ {Θ} → RExp Θ → List (RAtom Θ)
nrmᵣ (rvar i)   = rv i ∷ []
nrmᵣ (rconst c) = consᵣ (rc c) []
nrmᵣ (ρ ·̂ᵣ ρ')  = appᵣ (nrmᵣ ρ) (nrmᵣ ρ')
nrmᵣ ∣ ε ∣̂ᵉ     = img (nrmₑ ε)

nrmᵣ-≡ : ∀ {Θ} → (ρ : RExp Θ) → ρ ≡̂ᵣ ⟦ nrmᵣ ρ ⟧ʳˢ
nrmᵣ-≡ (rvar i)   = ≡̂ᵣ-sym ≡̂ᵣ-identityʳ
nrmᵣ-≡ (rconst c) = ≡̂ᵣ-sym (≡̂ᵣ-trans (consᵣ-≡ (rc c) []) ≡̂ᵣ-identityʳ)
nrmᵣ-≡ (ρ ·̂ᵣ ρ')  =
  ≡̂ᵣ-trans (≡̂ᵣ-cong (nrmᵣ-≡ ρ) (nrmᵣ-≡ ρ')) (≡̂ᵣ-sym (appᵣ-≡ (nrmᵣ ρ) (nrmᵣ ρ')))
nrmᵣ-≡ ∣ ε ∣̂ᵉ     = ≡̂ᵣ-trans (≡̂ᵣ-map-cong (nrmₑ-≡ ε)) (img-≡ (nrmₑ ε))

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
