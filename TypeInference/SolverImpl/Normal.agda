------------------------------------------------------------------
-- Deciding an entailed ordering of open grade expressions        --
--                                                                --
-- Both sides are put in the sum-of-products normal form of       --
-- `SolverImpl.Product` and compared alternative by alternative,  --
-- the answer glued back with `eqᵣ`/`monoᵣ`/`transᵣ`. Two         --
-- alternatives are compared as sequences of atoms in which a     --
-- missing position is the unit: an atom may be matched against   --
-- nothing, on the right when the unit is below it and on the     --
-- left when it is below the unit, and the top on the right       --
-- stands for any run of atoms on the left.                       --
--                                                                --
-- The sums are met by the universal property of the join:        --
-- `⊔-lub` reduces the left side to each of its alternatives in   --
-- turn, and `⊔-ubˡ`/`⊔-ubʳ` pick out an alternative of the right --
-- side for each. So a bounded ∀/∃ over alternatives sits above a --
-- pointwise comparison of products.                              --
--                                                                --
-- `⊩-reflectᵣ`/`⊩-reflectₑ` are the closed special case: a       --
-- variable-free expression is convertible to the constant it     --
-- evaluates to, in both directions.                              --
------------------------------------------------------------------

open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_)
open import Data.Product using (_×_; _,_)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps as H

module TypeInference.SolverImpl.Normal
  (S : LanguageSpec)
  (_≾ᵣ?_ : Decidable (Grade._≾_ (GradeSystem.RGrade (LanguageSpec.Grades S))))
  (_≾ₑ?_ : Decidable (Grade._≾_ (GradeSystem.EGrade (LanguageSpec.Grades S))))
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))              -- optional unit-minimality of `_≾ᵣ_`
  (umin?ₑ : Maybe (H.UnitMinₑ S))              -- optional unit-minimality of `_≾ₑ_`
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.SolverImpl.Product S public

-- The unit is below anything as soon as the option is supplied

min≾ₑ : ∀ {Θ} {Q : Hyps Θ} {ε : EExp Θ} → Maybe UnitMinₑ → Maybe (Q ⊩ ûₑ ≾̂ₑ ε)
min≾ₑ (just p) = just (minₑ p)
min≾ₑ nothing  = nothing

min≾ᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → Maybe UnitMinᵣ → Maybe (Q ⊩ ûᵣ ≾̂ᵣ ρ)
min≾ᵣ (just p) = just (minᵣ p)
min≾ᵣ nothing  = nothing

-- A constant is above anything when the top is below it

ceilₑ : ∀ {Θ} {Q : Hyps Θ} {ε : EExp Θ} → (c : E) → Maybe (Q ⊩ ε ≾̂ₑ econst c)
ceilₑ c with ⊤ₑ ≾ₑ? c
... | yes p = just (transₑ topₑ (atomₑ p))
... | no _  = nothing

ceilᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → (c : R) → Maybe (Q ⊩ ρ ≾̂ᵣ rconst c)
ceilᵣ c with ⊤ᵣ ≾ᵣ? c
... | yes p = just (transᵣ topᵣ (atomᵣ p))
... | no _  = nothing

------------------------------------------------------------------
-- Products
--
-- Two products are compared as sequences whose missing positions
-- are the unit. A step consumes an atom from at least one side:
--
--   * match the two heads, by monotonicity (`atom≾`);
--   * pass over the right head, the unit being below it (`unit≾`);
--   * pass over the left head, it being below the unit (`≾unit`);
--   * absorb the left head into a right head that is the top, the
--     top staying to absorb more, as `a · ⊤ ≾ ⊤`.
--
-- The steps are tried in that order, and a failure falls through to
-- the next, so the search succeeds whenever the two products can be
-- aligned in order: each left atom matched, absorbed or below the
-- unit, each right atom matched, absorbing a run, or above the unit.
-- The order decides only which derivation is found first. Each
-- recursive call has a shorter left side, or the same left side and
-- a shorter right one, so the recursion is structural.
--
-- What it does not find: a constant split across positions, as in
-- `c · d ≾ c · x · d` with the unit below `x`, where the left side is
-- the single atom `c · d`; and anything that needs a hypothesis. Nor
-- does a sum look past its alternatives: a left alternative must be
-- below one right alternative on its own.
--
-- The products are read back with a trailing unit (`⟦_⟧ᵉˢ`), so that
-- each step is one use of `monoₑ`; `prod≾ₑ` converts at the ends.

-- The unit below an atom: a constant by the grade's own order, a
-- variable by unit-minimality

unit≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (b : EAtom Θ) → Maybe (Q ⊩ ûₑ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
unit≾ₑ (ac c) with uₑ ≾ₑ? c
... | yes p = just (atomₑ p)
... | no _  = nothing
unit≾ₑ (av i) = min≾ₑ umin?ₑ

-- An atom below the unit: a constant by the grade's own order, a
-- variable when the unit is the top

≾unitₑ : ∀ {Θ} {Q : Hyps Θ} → (a : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ûₑ)
≾unitₑ (ac c) with c ≾ₑ? uₑ
... | yes p = just (atomₑ p)
... | no _  = nothing
≾unitₑ (av i) = ceilₑ uₑ

-- An atom below an atom: constants by the grade's own order, a
-- variable below itself and below the top

atom≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
atom≾ₑ (ac c) (ac d) with c ≾ₑ? d
... | yes p = just (atomₑ p)
... | no _  = nothing
atom≾ₑ (av i) (ac d) = ceilₑ d
atom≾ₑ (av i) (av j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ₑ-refl
... | no _     = nothing
atom≾ₑ (ac c) (av j) = nothing

-- An atom absorbed into the top

absorbs≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (a b : EAtom Θ)
          → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ·̂ₑ ⟦ b ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
absorbs≾ₑ a (ac d) = ceilₑ d
absorbs≾ₑ a (av j) = nothing

-- The four steps, each given the comparison of what remains

matchₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → (a b : EAtom Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
       → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ·̂ₑ ε ≾̂ₑ ⟦ b ⟧ᵉᵃ ·̂ₑ ε')
matchₑ {Q = Q} a b r with atom≾ₑ {Q = Q} a b
... | nothing = nothing
... | just p with r
...   | just q  = just (monoₑ p q)
...   | nothing = nothing

skipʳₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → (b : EAtom Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
       → Maybe (Q ⊩ ε ≾̂ₑ ⟦ b ⟧ᵉᵃ ·̂ₑ ε')
skipʳₑ {Q = Q} b r with unit≾ₑ {Q = Q} b
... | nothing = nothing
... | just p with r
...   | just q  = just (transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-identityˡ)) (monoₑ p q))
...   | nothing = nothing

skipˡₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → (a : EAtom Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
       → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ·̂ₑ ε ≾̂ₑ ε')
skipˡₑ {Q = Q} a r with ≾unitₑ {Q = Q} a
... | nothing = nothing
... | just p with r
...   | just q  = just (transₑ (monoₑ p q) (eqₑ ≡̂ₑ-identityˡ))
...   | nothing = nothing

intoTopₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → (a b : EAtom Θ)
         → Maybe (Q ⊩ ε ≾̂ₑ ⟦ b ⟧ᵉᵃ ·̂ₑ ε')
         → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ·̂ₑ ε ≾̂ₑ ⟦ b ⟧ᵉᵃ ·̂ₑ ε')
intoTopₑ {Q = Q} a b r with absorbs≾ₑ {Q = Q} a b
... | nothing = nothing
... | just p with r
...   | just q  = just (transₑ (monoₑ ⊩≾̂ₑ-refl q)
                               (transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-assoc)) (monoₑ p ⊩≾̂ₑ-refl)))
...   | nothing = nothing

prodˢ≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (as bs : List (EAtom Θ))
        → Maybe (Q ⊩ ⟦ as ⟧ᵉˢ ≾̂ₑ ⟦ bs ⟧ᵉˢ)
prodˢ≾ₑ []       []       = just ⊩≾̂ₑ-refl
prodˢ≾ₑ []       (b ∷ bs) = skipʳₑ b (prodˢ≾ₑ [] bs)
prodˢ≾ₑ (a ∷ as) []       = skipˡₑ a (prodˢ≾ₑ as [])
prodˢ≾ₑ (a ∷ as) (b ∷ bs) =
  matchₑ a b (prodˢ≾ₑ as bs)
  <∣> skipʳₑ b (prodˢ≾ₑ (a ∷ as) bs)
  <∣> skipˡₑ a (prodˢ≾ₑ as (b ∷ bs))
  <∣> intoTopₑ a b (prodˢ≾ₑ as (b ∷ bs))

prod≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (as bs : List (EAtom Θ))
       → Maybe (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ ⟦ bs ⟧ᵉᵖ)
prod≾ₑ as bs with prodˢ≾ₑ as bs
... | just p  = just (transₑ (eqₑ (≡̂ₑ-sym (⟦⟧ᵉᵖ-≡ as)))
                             (transₑ p (eqₑ (⟦⟧ᵉᵖ-≡ bs))))
... | nothing = nothing

-- One alternative against a whole sum: some alternative of the sum
-- bounds it, and the join is above that one

altSum≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (as : List (EAtom Θ))
         → (t : Alts (List (EAtom Θ)))
         → Maybe (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ ⟦ t ⟧ᵉᵖ⁺)
altSum≾ₑ as (alt P) = prod≾ₑ as P
altSum≾ₑ as (P ∷⁺ t) with prod≾ₑ as P
... | just p  = just (transₑ p ⊔-ubˡₑ)
... | nothing with altSum≾ₑ as t
...   | just q  = just (transₑ q ⊔-ubʳₑ)
...   | nothing = nothing

-- The whole comparison: every alternative of the left side is below
-- the right side, and their join is then below it too

sum≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (s t : Alts (List (EAtom Θ)))
      → Maybe (Q ⊩ ⟦ s ⟧ᵉᵖ⁺ ≾̂ₑ ⟦ t ⟧ᵉᵖ⁺)
sum≾ₑ (alt P)  t = altSum≾ₑ P t
sum≾ₑ (P ∷⁺ s) t with altSum≾ₑ P t | sum≾ₑ s t
... | just p | just q = just (⊔-lubₑ p q)
... | _      | _      = nothing

decide≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (ε ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
decide≾ₑ ε ε' with sum≾ₑ (nrmₑ ε) (nrmₑ ε')
... | just p  = just (transₑ (eqₑ (canonₑ-≡ ε))
                             (transₑ p (eqₑ (≡̂ₑ-sym (canonₑ-≡ ε')))))
... | nothing = nothing

------------------------------------------------------------------
-- Resource grades: the same, with a third kind of atom, the image
-- `∣ x ∣` of an effect variable, which is treated as a variable. The
-- unit is below it by unit-minimality of either sort, the latter
-- carried through the morphism by `map-mono`, as `∣ u ∣ = u`.

∣û∣ₑ : ∀ {Θ} → ûᵣ {Θ} ≡̂ᵣ ∣ ûₑ ∣̂ᵉ
∣û∣ₑ = ≡̂ᵣ-sym (≡̂ᵣ-trans ≡̂ᵣ-map-const
                        (subst (λ c → rconst (mapᵉ uₑ) ≡̂ᵣ rconst c) map-uᵉ ≡̂ᵣ-refl))

unit≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (b : RAtom Θ) → Maybe (Q ⊩ ûᵣ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
unit≾ᵣ (rc c) with uᵣ ≾ᵣ? c
... | yes p = just (atomᵣ p)
... | no _  = nothing
unit≾ᵣ (rv i) = min≾ᵣ umin?ᵣ
unit≾ᵣ {Q = Q} (rm i) with min≾ᵣ {Q = Q} umin?ᵣ | min≾ₑ {Q = Q} {ε = evar i} umin?ₑ
... | just p | _      = just p
... | _      | just q = just (transᵣ (eqᵣ ∣û∣ₑ) (map-mono q))
... | _      | _      = nothing

≾unitᵣ : ∀ {Θ} {Q : Hyps Θ} → (a : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ûᵣ)
≾unitᵣ (rc c) with c ≾ᵣ? uᵣ
... | yes p = just (atomᵣ p)
... | no _  = nothing
≾unitᵣ (rv i) = ceilᵣ uᵣ
≾unitᵣ (rm i) = ceilᵣ uᵣ

atom≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (a b : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
atom≾ᵣ (rc c) (rc d) with c ≾ᵣ? d
... | yes p = just (atomᵣ p)
... | no _  = nothing
atom≾ᵣ (rv i) (rc d) = ceilᵣ d
atom≾ᵣ (rm i) (rc d) = ceilᵣ d
atom≾ᵣ (rv i) (rv j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ᵣ-refl
... | no _     = nothing
atom≾ᵣ (rm i) (rm j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ᵣ-refl
... | no _     = nothing
atom≾ᵣ _ _ = nothing

absorbs≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (a b : RAtom Θ)
          → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ·̂ᵣ ⟦ b ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
absorbs≾ᵣ a (rc d) = ceilᵣ d
absorbs≾ᵣ a (rv j) = nothing
absorbs≾ᵣ a (rm j) = nothing

matchᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → (a b : RAtom Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
       → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ·̂ᵣ ρ ≾̂ᵣ ⟦ b ⟧ʳᵃ ·̂ᵣ ρ')
matchᵣ {Q = Q} a b r with atom≾ᵣ {Q = Q} a b
... | nothing = nothing
... | just p with r
...   | just q  = just (monoᵣ p q)
...   | nothing = nothing

skipʳᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → (b : RAtom Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
       → Maybe (Q ⊩ ρ ≾̂ᵣ ⟦ b ⟧ʳᵃ ·̂ᵣ ρ')
skipʳᵣ {Q = Q} b r with unit≾ᵣ {Q = Q} b
... | nothing = nothing
... | just p with r
...   | just q  = just (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityˡ)) (monoᵣ p q))
...   | nothing = nothing

skipˡᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → (a : RAtom Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
       → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ·̂ᵣ ρ ≾̂ᵣ ρ')
skipˡᵣ {Q = Q} a r with ≾unitᵣ {Q = Q} a
... | nothing = nothing
... | just p with r
...   | just q  = just (transᵣ (monoᵣ p q) (eqᵣ ≡̂ᵣ-identityˡ))
...   | nothing = nothing

intoTopᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → (a b : RAtom Θ)
         → Maybe (Q ⊩ ρ ≾̂ᵣ ⟦ b ⟧ʳᵃ ·̂ᵣ ρ')
         → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ·̂ᵣ ρ ≾̂ᵣ ⟦ b ⟧ʳᵃ ·̂ᵣ ρ')
intoTopᵣ {Q = Q} a b r with absorbs≾ᵣ {Q = Q} a b
... | nothing = nothing
... | just p with r
...   | just q  = just (transᵣ (monoᵣ ⊩≾̂ᵣ-refl q)
                               (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-assoc)) (monoᵣ p ⊩≾̂ᵣ-refl)))
...   | nothing = nothing

prodˢ≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (as bs : List (RAtom Θ))
        → Maybe (Q ⊩ ⟦ as ⟧ʳˢ ≾̂ᵣ ⟦ bs ⟧ʳˢ)
prodˢ≾ᵣ []       []       = just ⊩≾̂ᵣ-refl
prodˢ≾ᵣ []       (b ∷ bs) = skipʳᵣ b (prodˢ≾ᵣ [] bs)
prodˢ≾ᵣ (a ∷ as) []       = skipˡᵣ a (prodˢ≾ᵣ as [])
prodˢ≾ᵣ (a ∷ as) (b ∷ bs) =
  matchᵣ a b (prodˢ≾ᵣ as bs)
  <∣> skipʳᵣ b (prodˢ≾ᵣ (a ∷ as) bs)
  <∣> skipˡᵣ a (prodˢ≾ᵣ as (b ∷ bs))
  <∣> intoTopᵣ a b (prodˢ≾ᵣ as (b ∷ bs))

prod≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (as bs : List (RAtom Θ))
       → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ bs ⟧ʳᵖ)
prod≾ᵣ as bs with prodˢ≾ᵣ as bs
... | just p  = just (transᵣ (eqᵣ (≡̂ᵣ-sym (⟦⟧ʳᵖ-≡ as)))
                             (transᵣ p (eqᵣ (⟦⟧ʳᵖ-≡ bs))))
... | nothing = nothing

altSum≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (as : List (RAtom Θ))
         → (t : Alts (List (RAtom Θ)))
         → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ t ⟧ʳᵖ⁺)
altSum≾ᵣ as (alt P) = prod≾ᵣ as P
altSum≾ᵣ as (P ∷⁺ t) with prod≾ᵣ as P
... | just p  = just (transᵣ p ⊔-ubˡᵣ)
... | nothing with altSum≾ᵣ as t
...   | just q  = just (transᵣ q ⊔-ubʳᵣ)
...   | nothing = nothing

sum≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (s t : Alts (List (RAtom Θ)))
      → Maybe (Q ⊩ ⟦ s ⟧ʳᵖ⁺ ≾̂ᵣ ⟦ t ⟧ʳᵖ⁺)
sum≾ᵣ (alt P)  t = altSum≾ᵣ P t
sum≾ᵣ (P ∷⁺ s) t with altSum≾ᵣ P t | sum≾ᵣ s t
... | just p | just q = just (⊔-lubᵣ p q)
... | _      | _      = nothing

decide≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (ρ ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
decide≾ᵣ ρ ρ' with sum≾ᵣ (nrmᵣ ρ) (nrmᵣ ρ')
... | just p  = just (transᵣ (eqᵣ (canonᵣ-≡ ρ))
                             (transᵣ p (eqᵣ (≡̂ᵣ-sym (canonᵣ-≡ ρ')))))
... | nothing = nothing

evalᵉ : EExp ∅ˢ → E
evalᵉ (evar ())
evalᵉ (econst c) = c
evalᵉ (ε ·̂ₑ ε')  = evalᵉ ε ·ₑ evalᵉ ε'
evalᵉ (ε ⊔̂ₑ ε')  = evalᵉ ε ⊔ₑ evalᵉ ε'

evalʳ : RExp ∅ˢ → R
evalʳ (rvar ())
evalʳ (rconst c) = c
evalʳ (ρ ·̂ᵣ ρ')  = evalʳ ρ ·ᵣ evalʳ ρ'
evalʳ (ρ ⊔̂ᵣ ρ')  = evalʳ ρ ⊔ᵣ evalʳ ρ'
evalʳ ∣ ε ∣̂ᵉ     = mapᵉ (evalᵉ ε)

evalᵉ-≡ : (ε : EExp ∅ˢ) → ε ≡̂ₑ econst (evalᵉ ε)
evalᵉ-≡ (evar ())
evalᵉ-≡ (econst c) = ≡̂ₑ-refl
evalᵉ-≡ (ε ·̂ₑ ε')  =
  ≡̂ₑ-trans (≡̂ₑ-cong (evalᵉ-≡ ε) (evalᵉ-≡ ε')) ≡̂ₑ-const-·
evalᵉ-≡ (ε ⊔̂ₑ ε')  =
  ≡̂ₑ-trans (≡̂ₑ-cong-⊔ (evalᵉ-≡ ε) (evalᵉ-≡ ε')) ≡̂ₑ-const-⊔

evalʳ-≡ : (ρ : RExp ∅ˢ) → ρ ≡̂ᵣ rconst (evalʳ ρ)
evalʳ-≡ (rvar ())
evalʳ-≡ (rconst c) = ≡̂ᵣ-refl
evalʳ-≡ (ρ ·̂ᵣ ρ')  =
  ≡̂ᵣ-trans (≡̂ᵣ-cong (evalʳ-≡ ρ) (evalʳ-≡ ρ')) ≡̂ᵣ-const-·
evalʳ-≡ (ρ ⊔̂ᵣ ρ')  =
  ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (evalʳ-≡ ρ) (evalʳ-≡ ρ')) ≡̂ᵣ-const-⊔
evalʳ-≡ ∣ ε ∣̂ᵉ     =
  ≡̂ᵣ-trans (≡̂ᵣ-map-cong (evalᵉ-≡ ε)) ≡̂ᵣ-map-const

-- A closed expression and its value entail one another

⊩-reflectᵣ : (ρ : RExp ∅ˢ)
           → (∅ᴴ ⊩ ρ ≾̂ᵣ rconst (evalʳ ρ)) × (∅ᴴ ⊩ rconst (evalʳ ρ) ≾̂ᵣ ρ)
⊩-reflectᵣ ρ = eqᵣ (evalʳ-≡ ρ) , eqᵣ (≡̂ᵣ-sym (evalʳ-≡ ρ))

⊩-reflectₑ : (ε : EExp ∅ˢ)
           → (∅ᴴ ⊩ ε ≾̂ₑ econst (evalᵉ ε)) × (∅ᴴ ⊩ econst (evalᵉ ε) ≾̂ₑ ε)
⊩-reflectₑ ε = eqₑ (evalᵉ-≡ ε) , eqₑ (≡̂ₑ-sym (evalᵉ-≡ ε))
