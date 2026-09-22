------------------------------------------------------------------
-- Sum-of-products normal form of open grade expressions          --
--                                                                --
-- A grade expression is flattened to a sum of alternatives, each  --
-- a product of atoms: constants, variables, and images of effect  --
-- variables under the morphism. Adjacent constants are           --
-- multiplied, units are dropped, a product is distributed over a  --
-- join, and repeated alternatives are merged. A sum with the top  --
-- among its alternatives is the top, `⊤` absorbing the join. A    --
-- sum is nonempty, the join having no unit; a product may be      --
-- empty, and is then the unit itself. The flattening is certified --
-- by `≡̂ᵣ`/`≡̂ₑ`, so one may compare alternative by alternative and --
-- atom by atom, or read the sum back as an expression.            --
--                                                                --
-- Two read-backs at each layer: `⟦_⟧ʳˢ`/`⟦_⟧ʳˢ⁺` end every        --
-- product in the unit, which makes the certificates structural;   --
-- `⟦_⟧ʳᵖ`/`⟦_⟧ʳᵖ⁺` drop that trailing unit and collapse a lone    --
-- alternative, and are what `canonᵣ`/`canonₑ` return.             --
------------------------------------------------------------------

open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Properties using () renaming (≡-dec to ≡-decᴸ)
open import Data.Maybe using (Maybe; just; nothing)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Product (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Hyps   S

------------------------------------------------------------------
-- Alternatives
--
-- The alternatives of a sum, a nonempty list: the join is a least
-- upper bound of two, and has no unit to stand for none.

infixr 5 _∷⁺_

data Alts (X : Set) : Set where
  alt  : X → Alts X
  _∷⁺_ : X → Alts X → Alts X

infixr 5 _⧺_

_⧺_ : ∀ {X} → Alts X → Alts X → Alts X
alt x    ⧺ t = x ∷⁺ t
(x ∷⁺ s) ⧺ t = x ∷⁺ (s ⧺ t)

------------------------------------------------------------------
-- Effect grades

data EAtom (Θ : Scope) : Set where
  ac : E → EAtom Θ
  av : EVar Θ → EAtom Θ

⟦_⟧ᵉᵃ : ∀ {Θ} → EAtom Θ → EExp Θ
⟦ ac c ⟧ᵉᵃ = econst c
⟦ av i ⟧ᵉᵃ = evar i

⟦_⟧ᵉᵖ : ∀ {Θ} → List (EAtom Θ) → EExp Θ
⟦ [] ⟧ᵉᵖ         = ûₑ
⟦ a ∷ [] ⟧ᵉᵖ     = ⟦ a ⟧ᵉᵃ
⟦ a ∷ b ∷ as ⟧ᵉᵖ = ⟦ a ⟧ᵉᵃ ·̂ₑ ⟦ b ∷ as ⟧ᵉᵖ

⟦_⟧ᵉˢ : ∀ {Θ} → List (EAtom Θ) → EExp Θ
⟦ [] ⟧ᵉˢ     = ûₑ
⟦ a ∷ as ⟧ᵉˢ = ⟦ a ⟧ᵉᵃ ·̂ₑ ⟦ as ⟧ᵉˢ

⟦_⟧ᵉᵖ⁺ : ∀ {Θ} → Alts (List (EAtom Θ)) → EExp Θ
⟦ alt P ⟧ᵉᵖ⁺  = ⟦ P ⟧ᵉᵖ
⟦ P ∷⁺ s ⟧ᵉᵖ⁺ = ⟦ P ⟧ᵉᵖ ⊔̂ₑ ⟦ s ⟧ᵉᵖ⁺

⟦_⟧ᵉˢ⁺ : ∀ {Θ} → Alts (List (EAtom Θ)) → EExp Θ
⟦ alt P ⟧ᵉˢ⁺  = ⟦ P ⟧ᵉˢ
⟦ P ∷⁺ s ⟧ᵉˢ⁺ = ⟦ P ⟧ᵉˢ ⊔̂ₑ ⟦ s ⟧ᵉˢ⁺

⟦⟧ᵉᵖ-≡ : ∀ {Θ} → (as : List (EAtom Θ)) → ⟦ as ⟧ᵉˢ ≡̂ₑ ⟦ as ⟧ᵉᵖ
⟦⟧ᵉᵖ-≡ []           = ≡̂ₑ-refl
⟦⟧ᵉᵖ-≡ (a ∷ [])     = ≡̂ₑ-identityʳ
⟦⟧ᵉᵖ-≡ (a ∷ b ∷ as) = ≡̂ₑ-cong ≡̂ₑ-refl (⟦⟧ᵉᵖ-≡ (b ∷ as))

⟦⟧ᵉᵖ⁺-≡ : ∀ {Θ} → (s : Alts (List (EAtom Θ))) → ⟦ s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉᵖ⁺
⟦⟧ᵉᵖ⁺-≡ (alt P)  = ⟦⟧ᵉᵖ-≡ P
⟦⟧ᵉᵖ⁺-≡ (P ∷⁺ s) = ≡̂ₑ-cong-⊔ (⟦⟧ᵉᵖ-≡ P) (⟦⟧ᵉᵖ⁺-≡ s)

-- Consing an atom onto a product: constants are merged, units dropped

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

-- Appending the alternatives of two sums is their join

⧺ₑ-≡ : ∀ {Θ} → (s t : Alts (List (EAtom Θ)))
     → ⟦ s ⧺ t ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺ ⊔̂ₑ ⟦ t ⟧ᵉˢ⁺
⧺ₑ-≡ (alt P)  t = ≡̂ₑ-refl
⧺ₑ-≡ (P ∷⁺ s) t =
  ≡̂ₑ-trans (≡̂ₑ-cong-⊔ ≡̂ₑ-refl (⧺ₑ-≡ s t)) (≡̂ₑ-sym ≡̂ₑ-assoc-⊔)

-- Multiplying sums: every alternative of the one against every
-- alternative of the other, which is where distributivity is spent

mul1ₑ : ∀ {Θ} → List (EAtom Θ) → Alts (List (EAtom Θ)) → Alts (List (EAtom Θ))
mul1ₑ P (alt Q)  = alt (appₑ P Q)
mul1ₑ P (Q ∷⁺ t) = appₑ P Q ∷⁺ mul1ₑ P t

mulₑ : ∀ {Θ} → Alts (List (EAtom Θ)) → Alts (List (EAtom Θ))
     → Alts (List (EAtom Θ))
mulₑ (alt P)  t = mul1ₑ P t
mulₑ (P ∷⁺ s) t = mul1ₑ P t ⧺ mulₑ s t

mul1ₑ-≡ : ∀ {Θ} → (P : List (EAtom Θ)) → (t : Alts (List (EAtom Θ)))
        → ⟦ mul1ₑ P t ⟧ᵉˢ⁺ ≡̂ₑ ⟦ P ⟧ᵉˢ ·̂ₑ ⟦ t ⟧ᵉˢ⁺
mul1ₑ-≡ P (alt Q)  = appₑ-≡ P Q
mul1ₑ-≡ P (Q ∷⁺ t) =
  ≡̂ₑ-trans (≡̂ₑ-cong-⊔ (appₑ-≡ P Q) (mul1ₑ-≡ P t)) (≡̂ₑ-sym ≡̂ₑ-distribˡ-⊔)

mulₑ-≡ : ∀ {Θ} → (s t : Alts (List (EAtom Θ)))
       → ⟦ mulₑ s t ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺ ·̂ₑ ⟦ t ⟧ᵉˢ⁺
mulₑ-≡ (alt P)  t = mul1ₑ-≡ P t
mulₑ-≡ (P ∷⁺ s) t =
  ≡̂ₑ-trans (⧺ₑ-≡ (mul1ₑ P t) (mulₑ s t))
  (≡̂ₑ-trans (≡̂ₑ-cong-⊔ (mul1ₑ-≡ P t) (mulₑ-≡ s t)) (≡̂ₑ-sym ≡̂ₑ-distribʳ-⊔))

-- Merging repeated alternatives, which the join's idempotence,
-- commutativity and associativity licence

_≟ᵃₑ_ : ∀ {Θ} → DecidableEquality (EAtom Θ)
ac c ≟ᵃₑ ac d with c ≡ₑ? d
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
ac c ≟ᵃₑ av j = no λ ()
av i ≟ᵃₑ ac d = no λ ()
av i ≟ᵃₑ av j with i ≟ᶠ j
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }

_≟ᵖₑ_ : ∀ {Θ} → DecidableEquality (List (EAtom Θ))
_≟ᵖₑ_ = ≡-decᴸ _≟ᵃₑ_

nub1ₑ : ∀ {Θ} → List (EAtom Θ) → Alts (List (EAtom Θ)) → Alts (List (EAtom Θ))
nub1ₑ P (alt Q) with P ≟ᵖₑ Q
... | yes _ = alt Q
... | no _  = P ∷⁺ alt Q
nub1ₑ P (Q ∷⁺ t) with P ≟ᵖₑ Q
... | yes _ = Q ∷⁺ t
... | no _  = Q ∷⁺ nub1ₑ P t

nubₑ : ∀ {Θ} → Alts (List (EAtom Θ)) → Alts (List (EAtom Θ))
nubₑ (alt P)  = alt P
nubₑ (P ∷⁺ s) = nub1ₑ P (nubₑ s)

nub1ₑ-≡ : ∀ {Θ} → (P : List (EAtom Θ)) → (s : Alts (List (EAtom Θ)))
        → ⟦ nub1ₑ P s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ P ⟧ᵉˢ ⊔̂ₑ ⟦ s ⟧ᵉˢ⁺
nub1ₑ-≡ P (alt Q) with P ≟ᵖₑ Q
... | yes refl = ≡̂ₑ-sym ≡̂ₑ-idem-⊔
... | no _     = ≡̂ₑ-refl
nub1ₑ-≡ P (Q ∷⁺ t) with P ≟ᵖₑ Q
... | yes refl =
      ≡̂ₑ-trans (≡̂ₑ-sym (≡̂ₑ-cong-⊔ ≡̂ₑ-idem-⊔ ≡̂ₑ-refl)) ≡̂ₑ-assoc-⊔
... | no _ =
      ≡̂ₑ-trans (≡̂ₑ-cong-⊔ ≡̂ₑ-refl (nub1ₑ-≡ P t))
      (≡̂ₑ-trans (≡̂ₑ-sym ≡̂ₑ-assoc-⊔)
      (≡̂ₑ-trans (≡̂ₑ-cong-⊔ ≡̂ₑ-comm-⊔ ≡̂ₑ-refl) ≡̂ₑ-assoc-⊔))

nubₑ-≡ : ∀ {Θ} → (s : Alts (List (EAtom Θ))) → ⟦ nubₑ s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺
nubₑ-≡ (alt P)  = ≡̂ₑ-refl
nubₑ-≡ (P ∷⁺ s) =
  ≡̂ₑ-trans (nub1ₑ-≡ P (nubₑ s)) (≡̂ₑ-cong-⊔ ≡̂ₑ-refl (nubₑ-≡ s))

-- An alternative that is the top: the constant `⊤`, or the empty
-- product when the unit is the top, `consₑ` dropping a constant that
-- is the unit

isTopₑ? : ∀ {Θ} → (P : List (EAtom Θ)) → Maybe (⟦ P ⟧ᵉᵖ ≡ econst ⊤ₑ)
isTopₑ? [] with uₑ ≡ₑ? ⊤ₑ
... | yes p = just (cong econst p)
... | no _  = nothing
isTopₑ? (ac c ∷ []) with c ≡ₑ? ⊤ₑ
... | yes p = just (cong econst p)
... | no _  = nothing
isTopₑ? _ = nothing

isTopₑ-≡ : ∀ {Θ} → (P : List (EAtom Θ)) → ⟦ P ⟧ᵉᵖ ≡ econst ⊤ₑ
         → ⟦ P ⟧ᵉˢ ≡̂ₑ econst ⊤ₑ
isTopₑ-≡ P eq = ≡̂ₑ-trans (⟦⟧ᵉᵖ-≡ P) (subst (⟦ P ⟧ᵉᵖ ≡̂ₑ_) eq ≡̂ₑ-refl)

-- A sum with a top alternative is the top, which absorbs the join

topSumₑ? : ∀ {Θ} → (s : Alts (List (EAtom Θ))) → Maybe (⟦ s ⟧ᵉˢ⁺ ≡̂ₑ econst ⊤ₑ)
topSumₑ? (alt P) with isTopₑ? P
... | just eq = just (isTopₑ-≡ P eq)
... | nothing = nothing
topSumₑ? (P ∷⁺ s) with isTopₑ? P
... | just eq =
      just (≡̂ₑ-trans (≡̂ₑ-cong-⊔ (isTopₑ-≡ P eq) ≡̂ₑ-refl)
                     (≡̂ₑ-trans ≡̂ₑ-comm-⊔ ≡̂ₑ-⊤-⊔))
... | nothing with topSumₑ? s
...   | just q  = just (≡̂ₑ-trans (≡̂ₑ-cong-⊔ ≡̂ₑ-refl q) ≡̂ₑ-⊤-⊔)
...   | nothing = nothing

-- Such a sum is replaced by the normal form of the top itself

absorbₑ : ∀ {Θ} → Alts (List (EAtom Θ)) → Alts (List (EAtom Θ))
absorbₑ s with topSumₑ? s
... | just _  = alt (consₑ (ac ⊤ₑ) [])
... | nothing = s

absorbₑ-≡ : ∀ {Θ} → (s : Alts (List (EAtom Θ))) → ⟦ absorbₑ s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺
absorbₑ-≡ s with topSumₑ? s
... | just q  =
      ≡̂ₑ-trans (consₑ-≡ (ac ⊤ₑ) []) (≡̂ₑ-trans ≡̂ₑ-identityʳ (≡̂ₑ-sym q))
... | nothing = ≡̂ₑ-refl

nrmₑ : ∀ {Θ} → EExp Θ → Alts (List (EAtom Θ))
nrmₑ (evar i)   = alt (av i ∷ [])
nrmₑ (econst c) = alt (consₑ (ac c) [])
nrmₑ (ε ·̂ₑ ε')  = absorbₑ (nubₑ (mulₑ (nrmₑ ε) (nrmₑ ε')))
nrmₑ (ε ⊔̂ₑ ε')  = absorbₑ (nubₑ (nrmₑ ε ⧺ nrmₑ ε'))

nrmₑ-≡ : ∀ {Θ} → (ε : EExp Θ) → ε ≡̂ₑ ⟦ nrmₑ ε ⟧ᵉˢ⁺
nrmₑ-≡ (evar i)   = ≡̂ₑ-sym ≡̂ₑ-identityʳ
nrmₑ-≡ (econst c) = ≡̂ₑ-sym (≡̂ₑ-trans (consₑ-≡ (ac c) []) ≡̂ₑ-identityʳ)
nrmₑ-≡ (ε ·̂ₑ ε')  =
  ≡̂ₑ-trans (≡̂ₑ-cong (nrmₑ-≡ ε) (nrmₑ-≡ ε'))
           (≡̂ₑ-sym (≡̂ₑ-trans (absorbₑ-≡ (nubₑ (mulₑ (nrmₑ ε) (nrmₑ ε'))))
                    (≡̂ₑ-trans (nubₑ-≡ (mulₑ (nrmₑ ε) (nrmₑ ε')))
                              (mulₑ-≡ (nrmₑ ε) (nrmₑ ε')))))
nrmₑ-≡ (ε ⊔̂ₑ ε')  =
  ≡̂ₑ-trans (≡̂ₑ-cong-⊔ (nrmₑ-≡ ε) (nrmₑ-≡ ε'))
           (≡̂ₑ-sym (≡̂ₑ-trans (absorbₑ-≡ (nubₑ (nrmₑ ε ⧺ nrmₑ ε')))
                    (≡̂ₑ-trans (nubₑ-≡ (nrmₑ ε ⧺ nrmₑ ε'))
                              (⧺ₑ-≡ (nrmₑ ε) (nrmₑ ε')))))

------------------------------------------------------------------
-- Resource grades

data RAtom (Θ : Scope) : Set where
  rc : R → RAtom Θ
  rv : RVar Θ → RAtom Θ
  rm : EVar Θ → RAtom Θ

⟦_⟧ʳᵃ : ∀ {Θ} → RAtom Θ → RExp Θ
⟦ rc c ⟧ʳᵃ = rconst c
⟦ rv i ⟧ʳᵃ = rvar i
⟦ rm i ⟧ʳᵃ = ∣ evar i ∣̂ᵉ

⟦_⟧ʳᵖ : ∀ {Θ} → List (RAtom Θ) → RExp Θ
⟦ [] ⟧ʳᵖ         = ûᵣ
⟦ a ∷ [] ⟧ʳᵖ     = ⟦ a ⟧ʳᵃ
⟦ a ∷ b ∷ as ⟧ʳᵖ = ⟦ a ⟧ʳᵃ ·̂ᵣ ⟦ b ∷ as ⟧ʳᵖ

⟦_⟧ʳˢ : ∀ {Θ} → List (RAtom Θ) → RExp Θ
⟦ [] ⟧ʳˢ     = ûᵣ
⟦ a ∷ as ⟧ʳˢ = ⟦ a ⟧ʳᵃ ·̂ᵣ ⟦ as ⟧ʳˢ

⟦_⟧ʳᵖ⁺ : ∀ {Θ} → Alts (List (RAtom Θ)) → RExp Θ
⟦ alt P ⟧ʳᵖ⁺  = ⟦ P ⟧ʳᵖ
⟦ P ∷⁺ s ⟧ʳᵖ⁺ = ⟦ P ⟧ʳᵖ ⊔̂ᵣ ⟦ s ⟧ʳᵖ⁺

⟦_⟧ʳˢ⁺ : ∀ {Θ} → Alts (List (RAtom Θ)) → RExp Θ
⟦ alt P ⟧ʳˢ⁺  = ⟦ P ⟧ʳˢ
⟦ P ∷⁺ s ⟧ʳˢ⁺ = ⟦ P ⟧ʳˢ ⊔̂ᵣ ⟦ s ⟧ʳˢ⁺

⟦⟧ʳᵖ-≡ : ∀ {Θ} → (as : List (RAtom Θ)) → ⟦ as ⟧ʳˢ ≡̂ᵣ ⟦ as ⟧ʳᵖ
⟦⟧ʳᵖ-≡ []           = ≡̂ᵣ-refl
⟦⟧ʳᵖ-≡ (a ∷ [])     = ≡̂ᵣ-identityʳ
⟦⟧ʳᵖ-≡ (a ∷ b ∷ as) = ≡̂ᵣ-cong ≡̂ᵣ-refl (⟦⟧ʳᵖ-≡ (b ∷ as))

⟦⟧ʳᵖ⁺-≡ : ∀ {Θ} → (s : Alts (List (RAtom Θ))) → ⟦ s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳᵖ⁺
⟦⟧ʳᵖ⁺-≡ (alt P)  = ⟦⟧ʳᵖ-≡ P
⟦⟧ʳᵖ⁺-≡ (P ∷⁺ s) = ≡̂ᵣ-cong-⊔ (⟦⟧ʳᵖ-≡ P) (⟦⟧ʳᵖ⁺-≡ s)

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

⧺ᵣ-≡ : ∀ {Θ} → (s t : Alts (List (RAtom Θ)))
     → ⟦ s ⧺ t ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺ ⊔̂ᵣ ⟦ t ⟧ʳˢ⁺
⧺ᵣ-≡ (alt P)  t = ≡̂ᵣ-refl
⧺ᵣ-≡ (P ∷⁺ s) t =
  ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ ≡̂ᵣ-refl (⧺ᵣ-≡ s t)) (≡̂ᵣ-sym ≡̂ᵣ-assoc-⊔)

mul1ᵣ : ∀ {Θ} → List (RAtom Θ) → Alts (List (RAtom Θ)) → Alts (List (RAtom Θ))
mul1ᵣ P (alt Q)  = alt (appᵣ P Q)
mul1ᵣ P (Q ∷⁺ t) = appᵣ P Q ∷⁺ mul1ᵣ P t

mulᵣ : ∀ {Θ} → Alts (List (RAtom Θ)) → Alts (List (RAtom Θ))
     → Alts (List (RAtom Θ))
mulᵣ (alt P)  t = mul1ᵣ P t
mulᵣ (P ∷⁺ s) t = mul1ᵣ P t ⧺ mulᵣ s t

mul1ᵣ-≡ : ∀ {Θ} → (P : List (RAtom Θ)) → (t : Alts (List (RAtom Θ)))
        → ⟦ mul1ᵣ P t ⟧ʳˢ⁺ ≡̂ᵣ ⟦ P ⟧ʳˢ ·̂ᵣ ⟦ t ⟧ʳˢ⁺
mul1ᵣ-≡ P (alt Q)  = appᵣ-≡ P Q
mul1ᵣ-≡ P (Q ∷⁺ t) =
  ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (appᵣ-≡ P Q) (mul1ᵣ-≡ P t)) (≡̂ᵣ-sym ≡̂ᵣ-distribˡ-⊔)

mulᵣ-≡ : ∀ {Θ} → (s t : Alts (List (RAtom Θ)))
       → ⟦ mulᵣ s t ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺ ·̂ᵣ ⟦ t ⟧ʳˢ⁺
mulᵣ-≡ (alt P)  t = mul1ᵣ-≡ P t
mulᵣ-≡ (P ∷⁺ s) t =
  ≡̂ᵣ-trans (⧺ᵣ-≡ (mul1ᵣ P t) (mulᵣ s t))
  (≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (mul1ᵣ-≡ P t) (mulᵣ-≡ s t)) (≡̂ᵣ-sym ≡̂ᵣ-distribʳ-⊔))

_≟ᵃᵣ_ : ∀ {Θ} → DecidableEquality (RAtom Θ)
rc c ≟ᵃᵣ rc d with c ≡ᵣ? d
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
rc c ≟ᵃᵣ rv j = no λ ()
rc c ≟ᵃᵣ rm j = no λ ()
rv i ≟ᵃᵣ rc d = no λ ()
rv i ≟ᵃᵣ rv j with i ≟ᶠ j
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
rv i ≟ᵃᵣ rm j = no λ ()
rm i ≟ᵃᵣ rc d = no λ ()
rm i ≟ᵃᵣ rv j = no λ ()
rm i ≟ᵃᵣ rm j with i ≟ᶠ j
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }

_≟ᵖᵣ_ : ∀ {Θ} → DecidableEquality (List (RAtom Θ))
_≟ᵖᵣ_ = ≡-decᴸ _≟ᵃᵣ_

nub1ᵣ : ∀ {Θ} → List (RAtom Θ) → Alts (List (RAtom Θ)) → Alts (List (RAtom Θ))
nub1ᵣ P (alt Q) with P ≟ᵖᵣ Q
... | yes _ = alt Q
... | no _  = P ∷⁺ alt Q
nub1ᵣ P (Q ∷⁺ t) with P ≟ᵖᵣ Q
... | yes _ = Q ∷⁺ t
... | no _  = Q ∷⁺ nub1ᵣ P t

nubᵣ : ∀ {Θ} → Alts (List (RAtom Θ)) → Alts (List (RAtom Θ))
nubᵣ (alt P)  = alt P
nubᵣ (P ∷⁺ s) = nub1ᵣ P (nubᵣ s)

nub1ᵣ-≡ : ∀ {Θ} → (P : List (RAtom Θ)) → (s : Alts (List (RAtom Θ)))
        → ⟦ nub1ᵣ P s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ P ⟧ʳˢ ⊔̂ᵣ ⟦ s ⟧ʳˢ⁺
nub1ᵣ-≡ P (alt Q) with P ≟ᵖᵣ Q
... | yes refl = ≡̂ᵣ-sym ≡̂ᵣ-idem-⊔
... | no _     = ≡̂ᵣ-refl
nub1ᵣ-≡ P (Q ∷⁺ t) with P ≟ᵖᵣ Q
... | yes refl =
      ≡̂ᵣ-trans (≡̂ᵣ-sym (≡̂ᵣ-cong-⊔ ≡̂ᵣ-idem-⊔ ≡̂ᵣ-refl)) ≡̂ᵣ-assoc-⊔
... | no _ =
      ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ ≡̂ᵣ-refl (nub1ᵣ-≡ P t))
      (≡̂ᵣ-trans (≡̂ᵣ-sym ≡̂ᵣ-assoc-⊔)
      (≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ ≡̂ᵣ-comm-⊔ ≡̂ᵣ-refl) ≡̂ᵣ-assoc-⊔))

nubᵣ-≡ : ∀ {Θ} → (s : Alts (List (RAtom Θ))) → ⟦ nubᵣ s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺
nubᵣ-≡ (alt P)  = ≡̂ᵣ-refl
nubᵣ-≡ (P ∷⁺ s) =
  ≡̂ᵣ-trans (nub1ᵣ-≡ P (nubᵣ s)) (≡̂ᵣ-cong-⊔ ≡̂ᵣ-refl (nubᵣ-≡ s))

isTopᵣ? : ∀ {Θ} → (P : List (RAtom Θ)) → Maybe (⟦ P ⟧ʳᵖ ≡ rconst ⊤ᵣ)
isTopᵣ? [] with uᵣ ≡ᵣ? ⊤ᵣ
... | yes p = just (cong rconst p)
... | no _  = nothing
isTopᵣ? (rc c ∷ []) with c ≡ᵣ? ⊤ᵣ
... | yes p = just (cong rconst p)
... | no _  = nothing
isTopᵣ? _ = nothing

isTopᵣ-≡ : ∀ {Θ} → (P : List (RAtom Θ)) → ⟦ P ⟧ʳᵖ ≡ rconst ⊤ᵣ
         → ⟦ P ⟧ʳˢ ≡̂ᵣ rconst ⊤ᵣ
isTopᵣ-≡ P eq = ≡̂ᵣ-trans (⟦⟧ʳᵖ-≡ P) (subst (⟦ P ⟧ʳᵖ ≡̂ᵣ_) eq ≡̂ᵣ-refl)

topSumᵣ? : ∀ {Θ} → (s : Alts (List (RAtom Θ))) → Maybe (⟦ s ⟧ʳˢ⁺ ≡̂ᵣ rconst ⊤ᵣ)
topSumᵣ? (alt P) with isTopᵣ? P
... | just eq = just (isTopᵣ-≡ P eq)
... | nothing = nothing
topSumᵣ? (P ∷⁺ s) with isTopᵣ? P
... | just eq =
      just (≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (isTopᵣ-≡ P eq) ≡̂ᵣ-refl)
                     (≡̂ᵣ-trans ≡̂ᵣ-comm-⊔ ≡̂ᵣ-⊤-⊔))
... | nothing with topSumᵣ? s
...   | just q  = just (≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ ≡̂ᵣ-refl q) ≡̂ᵣ-⊤-⊔)
...   | nothing = nothing

absorbᵣ : ∀ {Θ} → Alts (List (RAtom Θ)) → Alts (List (RAtom Θ))
absorbᵣ s with topSumᵣ? s
... | just _  = alt (consᵣ (rc ⊤ᵣ) [])
... | nothing = s

absorbᵣ-≡ : ∀ {Θ} → (s : Alts (List (RAtom Θ))) → ⟦ absorbᵣ s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺
absorbᵣ-≡ s with topSumᵣ? s
... | just q  =
      ≡̂ᵣ-trans (consᵣ-≡ (rc ⊤ᵣ) []) (≡̂ᵣ-trans ≡̂ᵣ-identityʳ (≡̂ᵣ-sym q))
... | nothing = ≡̂ᵣ-refl

-- The sum of `∣ ε ∣̂ᵉ`, read off `ε` directly: the morphism is a
-- monoid map, so it passes through a product and a join alike.

nrmᵐ : ∀ {Θ} → EExp Θ → Alts (List (RAtom Θ))
nrmᵐ (evar i)   = alt (rm i ∷ [])
nrmᵐ (econst c) = alt (consᵣ (rc (mapᵉ c)) [])
nrmᵐ (ε ·̂ₑ ε')  = absorbᵣ (nubᵣ (mulᵣ (nrmᵐ ε) (nrmᵐ ε')))
nrmᵐ (ε ⊔̂ₑ ε')  = absorbᵣ (nubᵣ (nrmᵐ ε ⧺ nrmᵐ ε'))

nrmᵐ-≡ : ∀ {Θ} → (ε : EExp Θ) → ∣ ε ∣̂ᵉ ≡̂ᵣ ⟦ nrmᵐ ε ⟧ʳˢ⁺
nrmᵐ-≡ (evar i)   = ≡̂ᵣ-sym ≡̂ᵣ-identityʳ
nrmᵐ-≡ (econst c) =
  ≡̂ᵣ-trans ≡̂ᵣ-map-const
           (≡̂ᵣ-sym (≡̂ᵣ-trans (consᵣ-≡ (rc (mapᵉ c)) []) ≡̂ᵣ-identityʳ))
nrmᵐ-≡ (ε ·̂ₑ ε')  =
  ≡̂ᵣ-trans ≡̂ᵣ-map-·
  (≡̂ᵣ-trans (≡̂ᵣ-cong (nrmᵐ-≡ ε) (nrmᵐ-≡ ε'))
            (≡̂ᵣ-sym (≡̂ᵣ-trans (absorbᵣ-≡ (nubᵣ (mulᵣ (nrmᵐ ε) (nrmᵐ ε'))))
                     (≡̂ᵣ-trans (nubᵣ-≡ (mulᵣ (nrmᵐ ε) (nrmᵐ ε')))
                               (mulᵣ-≡ (nrmᵐ ε) (nrmᵐ ε'))))))
nrmᵐ-≡ (ε ⊔̂ₑ ε')  =
  ≡̂ᵣ-trans ≡̂ᵣ-map-⊔
  (≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (nrmᵐ-≡ ε) (nrmᵐ-≡ ε'))
            (≡̂ᵣ-sym (≡̂ᵣ-trans (absorbᵣ-≡ (nubᵣ (nrmᵐ ε ⧺ nrmᵐ ε')))
                     (≡̂ᵣ-trans (nubᵣ-≡ (nrmᵐ ε ⧺ nrmᵐ ε'))
                               (⧺ᵣ-≡ (nrmᵐ ε) (nrmᵐ ε'))))))

nrmᵣ : ∀ {Θ} → RExp Θ → Alts (List (RAtom Θ))
nrmᵣ (rvar i)   = alt (rv i ∷ [])
nrmᵣ (rconst c) = alt (consᵣ (rc c) [])
nrmᵣ (ρ ·̂ᵣ ρ')  = absorbᵣ (nubᵣ (mulᵣ (nrmᵣ ρ) (nrmᵣ ρ')))
nrmᵣ (ρ ⊔̂ᵣ ρ')  = absorbᵣ (nubᵣ (nrmᵣ ρ ⧺ nrmᵣ ρ'))
nrmᵣ ∣ ε ∣̂ᵉ     = nrmᵐ ε

nrmᵣ-≡ : ∀ {Θ} → (ρ : RExp Θ) → ρ ≡̂ᵣ ⟦ nrmᵣ ρ ⟧ʳˢ⁺
nrmᵣ-≡ (rvar i)   = ≡̂ᵣ-sym ≡̂ᵣ-identityʳ
nrmᵣ-≡ (rconst c) = ≡̂ᵣ-sym (≡̂ᵣ-trans (consᵣ-≡ (rc c) []) ≡̂ᵣ-identityʳ)
nrmᵣ-≡ (ρ ·̂ᵣ ρ')  =
  ≡̂ᵣ-trans (≡̂ᵣ-cong (nrmᵣ-≡ ρ) (nrmᵣ-≡ ρ'))
           (≡̂ᵣ-sym (≡̂ᵣ-trans (absorbᵣ-≡ (nubᵣ (mulᵣ (nrmᵣ ρ) (nrmᵣ ρ'))))
                    (≡̂ᵣ-trans (nubᵣ-≡ (mulᵣ (nrmᵣ ρ) (nrmᵣ ρ')))
                              (mulᵣ-≡ (nrmᵣ ρ) (nrmᵣ ρ')))))
nrmᵣ-≡ (ρ ⊔̂ᵣ ρ')  =
  ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (nrmᵣ-≡ ρ) (nrmᵣ-≡ ρ'))
           (≡̂ᵣ-sym (≡̂ᵣ-trans (absorbᵣ-≡ (nubᵣ (nrmᵣ ρ ⧺ nrmᵣ ρ')))
                    (≡̂ᵣ-trans (nubᵣ-≡ (nrmᵣ ρ ⧺ nrmᵣ ρ'))
                              (⧺ᵣ-≡ (nrmᵣ ρ) (nrmᵣ ρ')))))
nrmᵣ-≡ ∣ ε ∣̂ᵉ     = nrmᵐ-≡ ε

-- The canonical form of an expression: a join of right-nested
-- products of atoms, a lone alternative standing for itself and the
-- empty product for the unit.

canonₑ : ∀ {Θ} → EExp Θ → EExp Θ
canonₑ ε = ⟦ nrmₑ ε ⟧ᵉᵖ⁺

canonᵣ : ∀ {Θ} → RExp Θ → RExp Θ
canonᵣ ρ = ⟦ nrmᵣ ρ ⟧ʳᵖ⁺

canonₑ-≡ : ∀ {Θ} → (ε : EExp Θ) → ε ≡̂ₑ canonₑ ε
canonₑ-≡ ε = ≡̂ₑ-trans (nrmₑ-≡ ε) (⟦⟧ᵉᵖ⁺-≡ (nrmₑ ε))

canonᵣ-≡ : ∀ {Θ} → (ρ : RExp Θ) → ρ ≡̂ᵣ canonᵣ ρ
canonᵣ-≡ ρ = ≡̂ᵣ-trans (nrmᵣ-≡ ρ) (⟦⟧ʳᵖ⁺-≡ (nrmᵣ ρ))
