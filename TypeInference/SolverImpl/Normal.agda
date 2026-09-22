------------------------------------------------------------------
-- Deciding an entailed ordering of open grade expressions        --
--                                                                --
-- Both sides are put in the sum-of-products normal form of       --
-- `SolverImpl.Product` and compared alternative by alternative,  --
-- each alternative atom by atom, the answer glued back with      --
-- `eqᵣ`/`monoᵣ`/`transᵣ`. A right alternative that is the top is --
-- above anything, by `topᵣ`/`topₑ`. A left alternative whose     --
-- atoms all cancel is the unit, and is then below anything by    --
-- `minᵣ`/`minₑ`, provided the corresponding unit-minimality      --
-- option is supplied.                                            --
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
open import Data.Maybe using (Maybe; just; nothing)
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

atom≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
atom≾ₑ (ac c) (ac d) with c ≾ₑ? d
... | yes p = just (atomₑ p)
... | no _  = nothing
atom≾ₑ (av i) (av j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ₑ-refl
... | no _     = nothing
atom≾ₑ _ _ = nothing

-- One alternative against another: atom by atom, the empty product
-- on the left being the unit

prod≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (as bs : List (EAtom Θ))
       → Maybe (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ ⟦ bs ⟧ᵉᵖ)
prod≾ₑ [] [] = just ⊩≾̂ₑ-refl
prod≾ₑ [] bs = min≾ₑ umin?ₑ
prod≾ₑ (a ∷ []) (b ∷ []) = atom≾ₑ a b
prod≾ₑ (a ∷ b ∷ as) (c ∷ d ∷ bs)
  with atom≾ₑ a c | prod≾ₑ (b ∷ as) (d ∷ bs)
... | just p | just q = just (monoₑ p q)
... | _      | _      = nothing
prod≾ₑ _ _ = nothing

-- One alternative against another: the top is above anything,
-- and otherwise the products are compared

alt≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (as bs : List (EAtom Θ))
      → Maybe (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ ⟦ bs ⟧ᵉᵖ)
alt≾ₑ {Q = Q} as bs with isTopₑ? bs
... | just eq = just (subst (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ_) (sym eq) topₑ)
... | nothing = prod≾ₑ as bs

-- One alternative against a whole sum: some alternative of the sum
-- bounds it, and the join is above that one

altSum≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (as : List (EAtom Θ))
         → (t : Alts (List (EAtom Θ)))
         → Maybe (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ ⟦ t ⟧ᵉᵖ⁺)
altSum≾ₑ as (alt P) = alt≾ₑ as P
altSum≾ₑ as (P ∷⁺ t) with alt≾ₑ as P
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

prod≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (as bs : List (RAtom Θ))
       → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ bs ⟧ʳᵖ)
prod≾ᵣ [] [] = just ⊩≾̂ᵣ-refl
prod≾ᵣ [] bs = min≾ᵣ umin?ᵣ
prod≾ᵣ (a ∷ []) (b ∷ []) = atom≾ᵣ a b
prod≾ᵣ (a ∷ b ∷ as) (c ∷ d ∷ bs)
  with atom≾ᵣ a c | prod≾ᵣ (b ∷ as) (d ∷ bs)
... | just p | just q = just (monoᵣ p q)
... | _      | _      = nothing
prod≾ᵣ _ _ = nothing

alt≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (as bs : List (RAtom Θ))
      → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ bs ⟧ʳᵖ)
alt≾ᵣ {Q = Q} as bs with isTopᵣ? bs
... | just eq = just (subst (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ_) (sym eq) topᵣ)
... | nothing = prod≾ᵣ as bs

altSum≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (as : List (RAtom Θ))
         → (t : Alts (List (RAtom Θ)))
         → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ t ⟧ʳᵖ⁺)
altSum≾ᵣ as (alt P) = alt≾ᵣ as P
altSum≾ᵣ as (P ∷⁺ t) with alt≾ᵣ as P
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
