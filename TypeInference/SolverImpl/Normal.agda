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
-- A join atom is met by its universal property: a join on the    --
-- left is discharged by `⊔-lub` from both operands, one on the   --
-- right by `⊔-ubˡ`/`⊔-ubʳ` from either. `⊔-lub` is taken first   --
-- because it is invertible, so nothing is lost by not going back --
-- to the upper-bound rules. Since a join stores its operands in  --
-- normal form, each such step passes to an operand of an atom or --
-- to the tail of a product, and the four mutually recursive      --
-- comparisons — product, atom against product, product against   --
-- atom, atom — descend structurally.                             --
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

mutual

  atom≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
  atom≾ₑ (ac c) (ac d) with c ≾ₑ? d
  ... | yes p = just (atomₑ p)
  ... | no _  = nothing
  atom≾ₑ (av i) (av j) with i ≟ᶠ j
  ... | yes refl = just ⊩≾̂ₑ-refl
  ... | no _     = nothing
  atom≾ₑ (a⊔ as bs) b with prodAtom≾ₑ as b | prodAtom≾ₑ bs b
  ... | just p | just q = just (⊔-lubₑ p q)
  ... | _      | _      = nothing
  atom≾ₑ a (a⊔ bs cs) with atomProd≾ₑ a bs | atomProd≾ₑ a cs
  ... | just p  | _      = just (transₑ p ⊔-ubˡₑ)
  ... | nothing | just q = just (transₑ q ⊔-ubʳₑ)
  ... | nothing | nothing = nothing
  atom≾ₑ _ _ = nothing

  prodAtom≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (as : List (EAtom Θ)) → (b : EAtom Θ)
             → Maybe (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
  prodAtom≾ₑ (a ∷ []) b = atom≾ₑ a b
  prodAtom≾ₑ [] b = min≾ₑ umin?ₑ
  prodAtom≾ₑ as (a⊔ bs cs) with prod≾ₑ as bs | prod≾ₑ as cs
  ... | just p  | _      = just (transₑ p ⊔-ubˡₑ)
  ... | nothing | just q = just (transₑ q ⊔-ubʳₑ)
  ... | nothing | nothing = nothing
  prodAtom≾ₑ _ _ = nothing

  atomProd≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (a : EAtom Θ) → (bs : List (EAtom Θ))
             → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ bs ⟧ᵉᵖ)
  atomProd≾ₑ a (b ∷ []) = atom≾ₑ a b
  atomProd≾ₑ (a⊔ as bs) cs with prod≾ₑ as cs | prod≾ₑ bs cs
  ... | just p | just q = just (⊔-lubₑ p q)
  ... | _      | _      = nothing
  atomProd≾ₑ _ _ = nothing

  -- The whole comparison: the empty product on the left is the unit

  prod≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (as bs : List (EAtom Θ))
         → Maybe (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ ⟦ bs ⟧ᵉᵖ)
  prod≾ₑ [] [] = just ⊩≾̂ₑ-refl
  prod≾ₑ [] bs = min≾ₑ umin?ₑ
  prod≾ₑ (a ∷ []) bs = atomProd≾ₑ a bs
  prod≾ₑ as (b ∷ []) = prodAtom≾ₑ as b
  prod≾ₑ (a ∷ b ∷ as) (c ∷ d ∷ bs)
    with atom≾ₑ a c | prod≾ₑ (b ∷ as) (d ∷ bs)
  ... | just p | just q = just (monoₑ p q)
  ... | _      | _      = nothing
  prod≾ₑ _ _ = nothing

decide≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (ε ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
decide≾ₑ ε ε' with prod≾ₑ (nrmₑ ε) (nrmₑ ε')
... | just p  = just (transₑ (eqₑ (canonₑ-≡ ε))
                             (transₑ p (eqₑ (≡̂ₑ-sym (canonₑ-≡ ε')))))
... | nothing = nothing

mutual

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
  atom≾ᵣ (r⊔ as bs) b with prodAtom≾ᵣ as b | prodAtom≾ᵣ bs b
  ... | just p | just q = just (⊔-lubᵣ p q)
  ... | _      | _      = nothing
  atom≾ᵣ a (r⊔ bs cs) with atomProd≾ᵣ a bs | atomProd≾ᵣ a cs
  ... | just p  | _      = just (transᵣ p ⊔-ubˡᵣ)
  ... | nothing | just q = just (transᵣ q ⊔-ubʳᵣ)
  ... | nothing | nothing = nothing
  atom≾ᵣ _ _ = nothing

  prodAtom≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (as : List (RAtom Θ)) → (b : RAtom Θ)
             → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  prodAtom≾ᵣ (a ∷ []) b = atom≾ᵣ a b
  prodAtom≾ᵣ [] b = min≾ᵣ umin?ᵣ
  prodAtom≾ᵣ as (r⊔ bs cs) with prod≾ᵣ as bs | prod≾ᵣ as cs
  ... | just p  | _      = just (transᵣ p ⊔-ubˡᵣ)
  ... | nothing | just q = just (transᵣ q ⊔-ubʳᵣ)
  ... | nothing | nothing = nothing
  prodAtom≾ᵣ _ _ = nothing

  atomProd≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (a : RAtom Θ) → (bs : List (RAtom Θ))
             → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ bs ⟧ʳᵖ)
  atomProd≾ᵣ a (b ∷ []) = atom≾ᵣ a b
  atomProd≾ᵣ (r⊔ as bs) cs with prod≾ᵣ as cs | prod≾ᵣ bs cs
  ... | just p | just q = just (⊔-lubᵣ p q)
  ... | _      | _      = nothing
  atomProd≾ᵣ _ _ = nothing

  prod≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (as bs : List (RAtom Θ))
         → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ bs ⟧ʳᵖ)
  prod≾ᵣ [] [] = just ⊩≾̂ᵣ-refl
  prod≾ᵣ [] bs = min≾ᵣ umin?ᵣ
  prod≾ᵣ (a ∷ []) bs = atomProd≾ᵣ a bs
  prod≾ᵣ as (b ∷ []) = prodAtom≾ᵣ as b
  prod≾ᵣ (a ∷ b ∷ as) (c ∷ d ∷ bs)
    with atom≾ᵣ a c | prod≾ᵣ (b ∷ as) (d ∷ bs)
  ... | just p | just q = just (monoᵣ p q)
  ... | _      | _      = nothing
  prod≾ᵣ _ _ = nothing

decide≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (ρ ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
decide≾ᵣ ρ ρ' with prod≾ᵣ (nrmᵣ ρ) (nrmᵣ ρ')
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
