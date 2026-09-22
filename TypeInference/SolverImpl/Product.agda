------------------------------------------------------------------
-- Product normal form of open grade expressions                  --
--                                                                --
-- A grade expression is flattened to a list of atoms: constants, --
-- variables, and images of effect variables under the morphism,  --
-- with adjacent constants multiplied and units dropped. The      --
-- flattening is certified by `≡̂ᵣ`/`≡̂ₑ`, so one may compare atom  --
-- by atom, or read the list back as an expression.               --
--                                                                --
-- Two read-backs: `⟦_⟧ʳˢ` ends every product in the unit, which  --
-- makes the certificates structural; `⟦_⟧ʳᵖ` drops that trailing --
-- unit, and is what `canonᵣ`/`canonₑ` return, and what a join    --
-- atom stores its operands in.                                   --
------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_)

open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Product (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Hyps   S

-- A join is an atom carrying its two operands in normal form: the
-- product is not distributed over it, but each side is normalised.

data EAtom (Θ : Scope) : Set where
  ac : E → EAtom Θ
  av : EVar Θ → EAtom Θ
  a⊔ : EExp Θ → EExp Θ → EAtom Θ

⟦_⟧ᵉᵃ : ∀ {Θ} → EAtom Θ → EExp Θ
⟦ ac c ⟧ᵉᵃ    = econst c
⟦ av i ⟧ᵉᵃ    = evar i
⟦ a⊔ ε ε' ⟧ᵉᵃ = ε ⊔̂ₑ ε'

⟦_⟧ᵉˢ : ∀ {Θ} → List (EAtom Θ) → EExp Θ
⟦ [] ⟧ᵉˢ     = ûₑ
⟦ a ∷ as ⟧ᵉˢ = ⟦ a ⟧ᵉᵃ ·̂ₑ ⟦ as ⟧ᵉˢ

⟦_⟧ᵉᵖ : ∀ {Θ} → List (EAtom Θ) → EExp Θ
⟦ [] ⟧ᵉᵖ         = ûₑ
⟦ a ∷ [] ⟧ᵉᵖ     = ⟦ a ⟧ᵉᵃ
⟦ a ∷ b ∷ as ⟧ᵉᵖ = ⟦ a ⟧ᵉᵃ ·̂ₑ ⟦ b ∷ as ⟧ᵉᵖ

⟦⟧ᵉᵖ-≡ : ∀ {Θ} → (as : List (EAtom Θ)) → ⟦ as ⟧ᵉˢ ≡̂ₑ ⟦ as ⟧ᵉᵖ
⟦⟧ᵉᵖ-≡ []           = ≡̂ₑ-refl
⟦⟧ᵉᵖ-≡ (a ∷ [])     = ≡̂ₑ-identityʳ
⟦⟧ᵉᵖ-≡ (a ∷ b ∷ as) = ≡̂ₑ-cong ≡̂ₑ-refl (⟦⟧ᵉᵖ-≡ (b ∷ as))

-- Consing an atom: constants are merged, units dropped

consₑ : ∀ {Θ} → EAtom Θ → List (EAtom Θ) → List (EAtom Θ)
consₑ (ac c) (ac d ∷ as) = consₑ (ac (c ·ₑ d)) as
consₑ (ac c) as with c ≡ₑ? uₑ
... | yes _ = as
... | no _  = ac c ∷ as
consₑ (av i) as = av i ∷ as
consₑ (a⊔ ε ε') as = a⊔ ε ε' ∷ as

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
consₑ-≡ (ac c) (a⊔ ε ε' ∷ as) with c ≡ₑ? uₑ
... | yes refl = ≡̂ₑ-sym ≡̂ₑ-identityˡ
... | no _     = ≡̂ₑ-refl
consₑ-≡ (av i) as = ≡̂ₑ-refl
consₑ-≡ (a⊔ ε ε') as = ≡̂ₑ-refl

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
nrmₑ (ε ⊔̂ₑ ε')  = a⊔ ⟦ nrmₑ ε ⟧ᵉᵖ ⟦ nrmₑ ε' ⟧ᵉᵖ ∷ []

nrmₑ-≡ : ∀ {Θ} → (ε : EExp Θ) → ε ≡̂ₑ ⟦ nrmₑ ε ⟧ᵉˢ
nrmₑ-≡ (evar i)   = ≡̂ₑ-sym ≡̂ₑ-identityʳ
nrmₑ-≡ (econst c) = ≡̂ₑ-sym (≡̂ₑ-trans (consₑ-≡ (ac c) []) ≡̂ₑ-identityʳ)
nrmₑ-≡ (ε ·̂ₑ ε')  =
  ≡̂ₑ-trans (≡̂ₑ-cong (nrmₑ-≡ ε) (nrmₑ-≡ ε')) (≡̂ₑ-sym (appₑ-≡ (nrmₑ ε) (nrmₑ ε')))
nrmₑ-≡ (ε ⊔̂ₑ ε')  =
  ≡̂ₑ-trans (≡̂ₑ-cong-⊔ (≡̂ₑ-trans (nrmₑ-≡ ε)  (⟦⟧ᵉᵖ-≡ (nrmₑ ε)))
                      (≡̂ₑ-trans (nrmₑ-≡ ε') (⟦⟧ᵉᵖ-≡ (nrmₑ ε'))))
           (≡̂ₑ-sym ≡̂ₑ-identityʳ)

data RAtom (Θ : Scope) : Set where
  rc : R → RAtom Θ
  rv : RVar Θ → RAtom Θ
  rm : EVar Θ → RAtom Θ
  r⊔ : RExp Θ → RExp Θ → RAtom Θ

⟦_⟧ʳᵃ : ∀ {Θ} → RAtom Θ → RExp Θ
⟦ rc c ⟧ʳᵃ    = rconst c
⟦ rv i ⟧ʳᵃ    = rvar i
⟦ rm i ⟧ʳᵃ    = ∣ evar i ∣̂ᵉ
⟦ r⊔ ρ ρ' ⟧ʳᵃ = ρ ⊔̂ᵣ ρ'

⟦_⟧ʳˢ : ∀ {Θ} → List (RAtom Θ) → RExp Θ
⟦ [] ⟧ʳˢ     = ûᵣ
⟦ a ∷ as ⟧ʳˢ = ⟦ a ⟧ʳᵃ ·̂ᵣ ⟦ as ⟧ʳˢ

⟦_⟧ʳᵖ : ∀ {Θ} → List (RAtom Θ) → RExp Θ
⟦ [] ⟧ʳᵖ         = ûᵣ
⟦ a ∷ [] ⟧ʳᵖ     = ⟦ a ⟧ʳᵃ
⟦ a ∷ b ∷ as ⟧ʳᵖ = ⟦ a ⟧ʳᵃ ·̂ᵣ ⟦ b ∷ as ⟧ʳᵖ

⟦⟧ʳᵖ-≡ : ∀ {Θ} → (as : List (RAtom Θ)) → ⟦ as ⟧ʳˢ ≡̂ᵣ ⟦ as ⟧ʳᵖ
⟦⟧ʳᵖ-≡ []           = ≡̂ᵣ-refl
⟦⟧ʳᵖ-≡ (a ∷ [])     = ≡̂ᵣ-identityʳ
⟦⟧ʳᵖ-≡ (a ∷ b ∷ as) = ≡̂ᵣ-cong ≡̂ᵣ-refl (⟦⟧ʳᵖ-≡ (b ∷ as))

consᵣ : ∀ {Θ} → RAtom Θ → List (RAtom Θ) → List (RAtom Θ)
consᵣ (rc c) (rc d ∷ as) = consᵣ (rc (c ·ᵣ d)) as
consᵣ (rc c) as with c ≡ᵣ? uᵣ
... | yes _ = as
... | no _  = rc c ∷ as
consᵣ (rv i) as = rv i ∷ as
consᵣ (rm i) as = rm i ∷ as
consᵣ (r⊔ ρ ρ') as = r⊔ ρ ρ' ∷ as

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
consᵣ-≡ (rc c) (r⊔ ρ ρ' ∷ as) with c ≡ᵣ? uᵣ
... | yes refl = ≡̂ᵣ-sym ≡̂ᵣ-identityˡ
... | no _     = ≡̂ᵣ-refl
consᵣ-≡ (rv i) as = ≡̂ᵣ-refl
consᵣ-≡ (rm i) as = ≡̂ᵣ-refl
consᵣ-≡ (r⊔ ρ ρ') as = ≡̂ᵣ-refl

appᵣ : ∀ {Θ} → List (RAtom Θ) → List (RAtom Θ) → List (RAtom Θ)
appᵣ []       ys = ys
appᵣ (a ∷ as) ys = consᵣ a (appᵣ as ys)

appᵣ-≡ : ∀ {Θ} → (as bs : List (RAtom Θ))
       → ⟦ appᵣ as bs ⟧ʳˢ ≡̂ᵣ ⟦ as ⟧ʳˢ ·̂ᵣ ⟦ bs ⟧ʳˢ
appᵣ-≡ []       bs = ≡̂ᵣ-sym ≡̂ᵣ-identityˡ
appᵣ-≡ (a ∷ as) bs =
  ≡̂ᵣ-trans (consᵣ-≡ a (appᵣ as bs))
  (≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl (appᵣ-≡ as bs)) (≡̂ᵣ-sym ≡̂ᵣ-assoc))

-- The atoms of `∣ ε ∣̂ᵉ`, read off `ε` directly: the morphism is a
-- monoid map, so it passes through a product and a join alike.

nrmᵐ : ∀ {Θ} → EExp Θ → List (RAtom Θ)
nrmᵐ (evar i)   = rm i ∷ []
nrmᵐ (econst c) = consᵣ (rc (mapᵉ c)) []
nrmᵐ (ε ·̂ₑ ε')  = appᵣ (nrmᵐ ε) (nrmᵐ ε')
nrmᵐ (ε ⊔̂ₑ ε')  = r⊔ ⟦ nrmᵐ ε ⟧ʳᵖ ⟦ nrmᵐ ε' ⟧ʳᵖ ∷ []

nrmᵐ-≡ : ∀ {Θ} → (ε : EExp Θ) → ∣ ε ∣̂ᵉ ≡̂ᵣ ⟦ nrmᵐ ε ⟧ʳˢ
nrmᵐ-≡ (evar i)   = ≡̂ᵣ-sym ≡̂ᵣ-identityʳ
nrmᵐ-≡ (econst c) =
  ≡̂ᵣ-trans ≡̂ᵣ-map-const
           (≡̂ᵣ-sym (≡̂ᵣ-trans (consᵣ-≡ (rc (mapᵉ c)) []) ≡̂ᵣ-identityʳ))
nrmᵐ-≡ (ε ·̂ₑ ε')  =
  ≡̂ᵣ-trans ≡̂ᵣ-map-·
  (≡̂ᵣ-trans (≡̂ᵣ-cong (nrmᵐ-≡ ε) (nrmᵐ-≡ ε')) (≡̂ᵣ-sym (appᵣ-≡ (nrmᵐ ε) (nrmᵐ ε'))))
nrmᵐ-≡ (ε ⊔̂ₑ ε')  =
  ≡̂ᵣ-trans ≡̂ᵣ-map-⊔
  (≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (≡̂ᵣ-trans (nrmᵐ-≡ ε)  (⟦⟧ʳᵖ-≡ (nrmᵐ ε)))
                       (≡̂ᵣ-trans (nrmᵐ-≡ ε') (⟦⟧ʳᵖ-≡ (nrmᵐ ε'))))
            (≡̂ᵣ-sym ≡̂ᵣ-identityʳ))

nrmᵣ : ∀ {Θ} → RExp Θ → List (RAtom Θ)
nrmᵣ (rvar i)   = rv i ∷ []
nrmᵣ (rconst c) = consᵣ (rc c) []
nrmᵣ (ρ ·̂ᵣ ρ')  = appᵣ (nrmᵣ ρ) (nrmᵣ ρ')
nrmᵣ (ρ ⊔̂ᵣ ρ')  = r⊔ ⟦ nrmᵣ ρ ⟧ʳᵖ ⟦ nrmᵣ ρ' ⟧ʳᵖ ∷ []
nrmᵣ ∣ ε ∣̂ᵉ     = nrmᵐ ε

nrmᵣ-≡ : ∀ {Θ} → (ρ : RExp Θ) → ρ ≡̂ᵣ ⟦ nrmᵣ ρ ⟧ʳˢ
nrmᵣ-≡ (rvar i)   = ≡̂ᵣ-sym ≡̂ᵣ-identityʳ
nrmᵣ-≡ (rconst c) = ≡̂ᵣ-sym (≡̂ᵣ-trans (consᵣ-≡ (rc c) []) ≡̂ᵣ-identityʳ)
nrmᵣ-≡ (ρ ·̂ᵣ ρ')  =
  ≡̂ᵣ-trans (≡̂ᵣ-cong (nrmᵣ-≡ ρ) (nrmᵣ-≡ ρ')) (≡̂ᵣ-sym (appᵣ-≡ (nrmᵣ ρ) (nrmᵣ ρ')))
nrmᵣ-≡ (ρ ⊔̂ᵣ ρ')  =
  ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (≡̂ᵣ-trans (nrmᵣ-≡ ρ)  (⟦⟧ʳᵖ-≡ (nrmᵣ ρ)))
                      (≡̂ᵣ-trans (nrmᵣ-≡ ρ') (⟦⟧ʳᵖ-≡ (nrmᵣ ρ'))))
           (≡̂ᵣ-sym ≡̂ᵣ-identityʳ)
nrmᵣ-≡ ∣ ε ∣̂ᵉ     = nrmᵐ-≡ ε

-- The canonical form of an expression: a right-nested product of
-- atoms, the empty product being the unit itself.

canonₑ : ∀ {Θ} → EExp Θ → EExp Θ
canonₑ ε = ⟦ nrmₑ ε ⟧ᵉᵖ

canonᵣ : ∀ {Θ} → RExp Θ → RExp Θ
canonᵣ ρ = ⟦ nrmᵣ ρ ⟧ʳᵖ

canonₑ-≡ : ∀ {Θ} → (ε : EExp Θ) → ε ≡̂ₑ canonₑ ε
canonₑ-≡ ε = ≡̂ₑ-trans (nrmₑ-≡ ε) (⟦⟧ᵉᵖ-≡ (nrmₑ ε))

canonᵣ-≡ : ∀ {Θ} → (ρ : RExp Θ) → ρ ≡̂ᵣ canonᵣ ρ
canonᵣ-≡ ρ = ≡̂ᵣ-trans (nrmᵣ-≡ ρ) (⟦⟧ʳᵖ-≡ (nrmᵣ ρ))
