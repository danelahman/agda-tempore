------------------------------------------------------------------
-- Normal forms of the grade expressions of a report            --
--                                                              --
-- Every grade expression of a reported type and of a reported  --
-- hypothesis set is replaced by its canonical form: the        --
-- sum-of-products normal form, grouped, folded and ordered by  --
-- skeleton, with every alternative that the decider places     --
-- below another dropped. Where the unit is least, a product    --
-- with the top among its factors is replaced by the top, since --
-- `u ≾ x` gives `x · ⊤ = ⊤ = ⊤ · x`, and the top then absorbs  --
-- the join. The canonical form is relative to what the decider --
-- proves, and hence to whether each grade's unit is least and  --
-- whether its multiplication commutes.                         --
--                                                              --
-- In a hypothesis set, an ordering whose left side has two or  --
-- more alternatives becomes one ordering per alternative       --
-- (`splits`, `piecesʳ`, `piecesᵉ`); a right side is never      --
-- split. `Localise` writes a clause's residual in the same     --
-- form.                                                        --
--                                                              --
-- A hypothesis set and its canonical form entail each other;   --
-- the canonical form is the set stored. A type is convertible  --
-- to its canonical form.                                       --
--                                                              --
-- Contract. An expression is convertible to its canonical form --
-- (`canonᵣ-≡`, `canonₑ-≡`; a product with the top to the top,  --
-- by the leastness of the unit, monotonicity and the greatest  --
-- element, `topProdᵣ?`, `topProdₑ?`), a type likewise          --
-- (`canonᵛ-≡̂`, `canonᶜ-≡̂`), and a hypothesis set and its       --
-- canonical form entail each other (`canonᴴ-⊩`, `canonᴴ-⊩⁻`),  --
-- an ordering and its pieces holding at the same instances     --
-- (`Split.back`, `Split.fwd`). That convertible expressions    --
-- have one canonical form is not claimed: it depends on what   --
-- the decider proves.                                          --
------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe using (Is-just)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using ([_,_]′)

open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Canon
  (S : LanguageSpec)
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S

open import TypeInference.SolverImpl.Normal    S
open import TypeInference.SolverImpl.Entail    S using (decideᵣ; decideₑ; derive)

-- Grouping with pruning, two alternatives being compared by the
-- decider at the empty hypothesis set, whose verdict convertibility
-- turns into absorption.
--
-- Pruning subsumes the top's absorption of the join: a top
-- alternative is a constant, so it heads the skeleton order and wins
-- every tie, and the decider places every product below it.

module Mₑ {Θ : Scope} =
  Gₑ.Pruning {Θ} (∅ᴴ ⊩_≾̂ₑ_) ≡̂ₑ-absorb
             (λ P P' → decideₑ derive ∅ᴴ Gₑ.⟦ P ⟧ᵖ Gₑ.⟦ P' ⟧ᵖ)

module Mᵣ {Θ : Scope} =
  Gᵣ.Pruning {Θ} (∅ᴴ ⊩_≾̂ᵣ_) ≡̂ᵣ-absorb
             (λ P P' → decideᵣ derive ∅ᴴ Gᵣ.⟦ P ⟧ᵖ Gᵣ.⟦ P' ⟧ᵖ)

-- At a grade whose unit is least, a product with the top among its
-- factors is the top: it lies below the top, and above the top
-- multiplied by the unit. Such a product is replaced by the top,
-- which then absorbs the join.

⊤-·ₑ : Is-just uₑ-least? → ∀ {Θ} {ε : EExp Θ} → econst ⊤ₑ ·̂ₑ ε ≡̂ₑ econst ⊤ₑ
⊤-·ₑ ij = ≡̂ₑ-antisym-∅ topₑ (transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-identityʳ)) (monoₑ ⊩≾̂ₑ-refl (minₑ ij)))

·-⊤ₑ : Is-just uₑ-least? → ∀ {Θ} {ε : EExp Θ} → ε ·̂ₑ econst ⊤ₑ ≡̂ₑ econst ⊤ₑ
·-⊤ₑ ij = ≡̂ₑ-antisym-∅ topₑ (transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-identityˡ)) (monoₑ (minₑ ij) ⊩≾̂ₑ-refl))

⊤-·ᵣ : Is-just uᵣ-least? → ∀ {Θ} {ρ : RExp Θ} → rconst ⊤ᵣ ·̂ᵣ ρ ≡̂ᵣ rconst ⊤ᵣ
⊤-·ᵣ ij = ≡̂ᵣ-antisym-∅ topᵣ (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityʳ)) (monoᵣ ⊩≾̂ᵣ-refl (minᵣ ij)))

·-⊤ᵣ : Is-just uᵣ-least? → ∀ {Θ} {ρ : RExp Θ} → ρ ·̂ᵣ rconst ⊤ᵣ ≡̂ᵣ rconst ⊤ᵣ
·-⊤ᵣ ij = ≡̂ᵣ-antisym-∅ topᵣ (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityˡ)) (monoᵣ (minᵣ ij) ⊩≾̂ᵣ-refl))

topProdₑ? : ∀ {Θ} → Is-just uₑ-least? → (P : List (EAtom Θ)) → Maybe (⟦ P ⟧ᵉˢ ≡̂ₑ econst ⊤ₑ)
topProdₑ? ij []      = nothing
topProdₑ? ij (a ∷ P) with a ≟ᵃₑ ac ⊤ₑ
... | yes refl = just (⊤-·ₑ ij)
... | no _ with topProdₑ? ij P
...   | just q  = just (≡̂ₑ-trans (≡̂ₑ-cong ≡̂ₑ-refl q) (·-⊤ₑ ij))
...   | nothing = nothing

topProdᵣ? : ∀ {Θ} → Is-just uᵣ-least? → (P : List (RAtom Θ)) → Maybe (⟦ P ⟧ʳˢ ≡̂ᵣ rconst ⊤ᵣ)
topProdᵣ? ij []      = nothing
topProdᵣ? ij (a ∷ P) with a ≟ᵃᵣ rc ⊤ᵣ
... | yes refl = just (⊤-·ᵣ ij)
... | no _ with topProdᵣ? ij P
...   | just q  = just (≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl q) (·-⊤ᵣ ij))
...   | nothing = nothing

absorbProdₑ : ∀ {Θ} → List (EAtom Θ) → List (EAtom Θ)
absorbProdₑ P with Is-just? uₑ-least?
... | nothing = P
... | just ij with topProdₑ? ij P
...   | just _  = consₑ (ac ⊤ₑ) []
...   | nothing = P

absorbProdᵣ : ∀ {Θ} → List (RAtom Θ) → List (RAtom Θ)
absorbProdᵣ P with Is-just? uᵣ-least?
... | nothing = P
... | just ij with topProdᵣ? ij P
...   | just _  = consᵣ (rc ⊤ᵣ) []
...   | nothing = P

absorbProdₑ-≡ : ∀ {Θ} → (P : List (EAtom Θ)) → ⟦ absorbProdₑ P ⟧ᵉˢ ≡̂ₑ ⟦ P ⟧ᵉˢ
absorbProdₑ-≡ P with Is-just? uₑ-least?
... | nothing = ≡̂ₑ-refl
... | just ij with topProdₑ? ij P
...   | just q  = ≡̂ₑ-trans (consₑ-≡ (ac ⊤ₑ) []) (≡̂ₑ-trans ≡̂ₑ-identityʳ (≡̂ₑ-sym q))
...   | nothing = ≡̂ₑ-refl

absorbProdᵣ-≡ : ∀ {Θ} → (P : List (RAtom Θ)) → ⟦ absorbProdᵣ P ⟧ʳˢ ≡̂ᵣ ⟦ P ⟧ʳˢ
absorbProdᵣ-≡ P with Is-just? uᵣ-least?
... | nothing = ≡̂ᵣ-refl
... | just ij with topProdᵣ? ij P
...   | just q  = ≡̂ᵣ-trans (consᵣ-≡ (rc ⊤ᵣ) []) (≡̂ᵣ-trans ≡̂ᵣ-identityʳ (≡̂ᵣ-sym q))
...   | nothing = ≡̂ᵣ-refl

absorbProdsₑ-≡ : ∀ {Θ} → (s : Alts (List (EAtom Θ))) → ⟦ mapᴬ absorbProdₑ s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺
absorbProdsₑ-≡ (alt P)  = absorbProdₑ-≡ P
absorbProdsₑ-≡ (P ∷⁺ s) = ≡̂ₑ-cong-⊔ (absorbProdₑ-≡ P) (absorbProdsₑ-≡ s)

absorbProdsᵣ-≡ : ∀ {Θ} → (s : Alts (List (RAtom Θ))) → ⟦ mapᴬ absorbProdᵣ s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺
absorbProdsᵣ-≡ (alt P)  = absorbProdᵣ-≡ P
absorbProdsᵣ-≡ (P ∷⁺ s) = ≡̂ᵣ-cong-⊔ (absorbProdᵣ-≡ P) (absorbProdsᵣ-≡ s)

canonSumₑ : ∀ {Θ} → Alts (List (EAtom Θ)) → Alts (List (EAtom Θ))
canonSumₑ s = fromProdsₑ (Mₑ.maximal (toProdsₑ (mapᴬ absorbProdₑ s)))

canonSumₑ-≡ : ∀ {Θ} → (s : Alts (List (EAtom Θ))) → ⟦ canonSumₑ s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺
canonSumₑ-≡ s =
  ≡̂ₑ-trans (fromProdsₑ-≡ (Mₑ.maximal (toProdsₑ s')))
  (≡̂ₑ-trans (Mₑ.maximal-≈ (toProdsₑ s')) (≡̂ₑ-trans (toProdsₑ-≡ s') (absorbProdsₑ-≡ s)))
  where s' = mapᴬ absorbProdₑ s

canonSumᵣ : ∀ {Θ} → Alts (List (RAtom Θ)) → Alts (List (RAtom Θ))
canonSumᵣ s = fromProdsᵣ (Mᵣ.maximal (toProdsᵣ (mapᴬ absorbProdᵣ s)))

canonSumᵣ-≡ : ∀ {Θ} → (s : Alts (List (RAtom Θ))) → ⟦ canonSumᵣ s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺
canonSumᵣ-≡ s =
  ≡̂ᵣ-trans (fromProdsᵣ-≡ (Mᵣ.maximal (toProdsᵣ s')))
  (≡̂ᵣ-trans (Mᵣ.maximal-≈ (toProdsᵣ s')) (≡̂ᵣ-trans (toProdsᵣ-≡ s') (absorbProdsᵣ-≡ s)))
  where s' = mapᴬ absorbProdᵣ s

-- The canonical form of an expression: a join of right-nested
-- products of atoms, a lone alternative standing for itself and the
-- empty product for the unit.

canonₑ : ∀ {Θ} → EExp Θ → EExp Θ
canonₑ ε = ⟦ canonSumₑ (nrmₑ ε) ⟧ᵉᵖ⁺

canonᵣ : ∀ {Θ} → RExp Θ → RExp Θ
canonᵣ ρ = ⟦ canonSumᵣ (nrmᵣ ρ) ⟧ʳᵖ⁺

canonₑ-≡ : ∀ {Θ} → (ε : EExp Θ) → ε ≡̂ₑ canonₑ ε
canonₑ-≡ ε =
  ≡̂ₑ-trans (nrmₑ-≡ ε)
  (≡̂ₑ-trans (≡̂ₑ-sym (canonSumₑ-≡ (nrmₑ ε))) (⟦⟧ᵉᵖ⁺-≡ (canonSumₑ (nrmₑ ε))))

canonᵣ-≡ : ∀ {Θ} → (ρ : RExp Θ) → ρ ≡̂ᵣ canonᵣ ρ
canonᵣ-≡ ρ =
  ≡̂ᵣ-trans (nrmᵣ-≡ ρ)
  (≡̂ᵣ-trans (≡̂ᵣ-sym (canonSumᵣ-≡ (nrmᵣ ρ))) (⟦⟧ʳᵖ⁺-≡ (canonSumᵣ (nrmᵣ ρ))))

-- Types: the grade slots are the box grades and the effect grades

canonᵛ : ∀ {Θ} → OVType Θ → OVType Θ
canonᶜ : ∀ {Θ} → OCType Θ → OCType Θ

canonᵛ (tvar α)  = tvar α
canonᵛ (Base b)  = Base b
canonᵛ Unit      = Unit
canonᵛ Bool      = Bool
canonᵛ Nat       = Nat
canonᵛ (A |×| B) = canonᵛ A |×| canonᵛ B
canonᵛ (A |+| B) = canonᵛ A |+| canonᵛ B
canonᵛ Empty     = Empty
canonᵛ (A ⇒ C)   = canonᵛ A ⇒ canonᶜ C
canonᵛ ([ ρ ] A) = [ canonᵣ ρ ] canonᵛ A

canonᶜ (A ‼ ε) = canonᵛ A ‼ canonₑ ε

canonᵛ-≡̂ : ∀ {Θ} → (A : OVType Θ) → A ≡̂ᵛ canonᵛ A
canonᶜ-≡̂ : ∀ {Θ} → (C : OCType Θ) → C ≡̂ᶜ canonᶜ C

canonᵛ-≡̂ (tvar α)  = tvar≡̂
canonᵛ-≡̂ (Base b)  = Base≡̂
canonᵛ-≡̂ Unit      = Unit≡̂
canonᵛ-≡̂ Bool      = Bool≡̂
canonᵛ-≡̂ Nat       = Nat≡̂
canonᵛ-≡̂ (A |×| B) = canonᵛ-≡̂ A |×|≡̂ canonᵛ-≡̂ B
canonᵛ-≡̂ (A |+| B) = canonᵛ-≡̂ A |+|≡̂ canonᵛ-≡̂ B
canonᵛ-≡̂ Empty     = Empty≡̂
canonᵛ-≡̂ (A ⇒ C)   = canonᵛ-≡̂ A ⇒≡̂ canonᶜ-≡̂ C
canonᵛ-≡̂ ([ ρ ] A) = [ canonᵣ-≡ ρ ]≡̂ canonᵛ-≡̂ A

canonᶜ-≡̂ (A ‼ ε) = canonᵛ-≡̂ A ‼≡̂ canonₑ-≡ ε

------------------------------------------------------------------------
-- Splitting an ordering: its left side's alternatives, each below its
-- right side, both sides in canonical form. The join is the least upper
-- bound, so the pieces and the ordering hold at the same instances. A
-- right side is never split.

Ordʳ : ∀ {Ψ Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → RExp Ψ × RExp Ψ → Set
Ordʳ Q δ (ρ , ρ') = Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ

Ordᵉ : ∀ {Ψ Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → EExp Ψ × EExp Ψ → Set
Ordᵉ Q δ (ε , ε') = Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ

-- The orderings an atom is replaced by, equivalent to it at every
-- instance

record Pieces {Ψ} {X : Set} (P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set) (a : X) : Set where
  constructor pieces
  field
    parts : List X
    pback : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → (∀ {b} → b ∈ parts → P Q δ b) → P Q δ a
    pfwd  : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → P Q δ a → ∀ {b} → b ∈ parts → P Q δ b

-- An atom left whole

whole : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set} → (a : X) → Pieces P a
whole a = pieces (a ∷ []) (λ δ k → k (here refl)) (λ δ h → λ { (here refl) → h })

record Split {Ψ} {X : Set} (P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set) (l : List X) : Set where
  constructor split
  field
    out  : List X
    back : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
         → (∀ {b} → b ∈ out → P Q δ b) → ∀ {a} → a ∈ l → P Q δ a
    fwd  : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
         → (∀ {a} → a ∈ l → P Q δ a) → ∀ {b} → b ∈ out → P Q δ b

consˢ : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set} {a : X} {l : List X}
      → Pieces P a → Split P l → Split P (a ∷ l)
consˢ (pieces ps pb pf) (split o bk fw) =
  split (ps ++ o)
        (λ δ k → λ { (here refl) → pb δ (λ m → k (∈-++⁺ˡ m))
                   ; (there m)   → bk δ (λ m' → k (∈-++⁺ʳ ps m')) m })
        (λ δ k m → [ pf δ (k (here refl)) , fw δ (λ m' → k (there m')) ]′ (∈-++⁻ ps m))

splits : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set}
       → ((a : X) → Pieces P a) → (l : List X) → Split P l
splits f []      = split [] (λ δ k → λ ()) (λ δ k → λ ())
splits f (a ∷ l) = consˢ (f a) (splits f l)

-- The images of the entries under `g`, each split

splitsBy : ∀ {Ψ} {X Y : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set}
         → (g : Y → X) → ((a : Y) → Pieces P (g a)) → (l : List Y) → Split P (map g l)
splitsBy g f []      = split [] (λ δ k → λ ()) (λ δ k → λ ())
splitsBy g f (a ∷ l) = consˢ (f a) (splitsBy g f l)

-- The alternatives of a sum, each below the same right side

partsʳ : ∀ {Ψ} → Alts (List (RAtom Ψ)) → RExp Ψ → List (RExp Ψ × RExp Ψ)
partsʳ (alt p)  y = (⟦ p ⟧ʳᵖ , y) ∷ []
partsʳ (p ∷⁺ s) y = (⟦ p ⟧ʳᵖ , y) ∷ partsʳ s y

partsₑ : ∀ {Ψ} → Alts (List (EAtom Ψ)) → EExp Ψ → List (EExp Ψ × EExp Ψ)
partsₑ (alt p)  y = (⟦ p ⟧ᵉᵖ , y) ∷ []
partsₑ (p ∷⁺ s) y = (⟦ p ⟧ᵉᵖ , y) ∷ partsₑ s y

partsʳ-lub : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (s : Alts (List (RAtom Ψ))) → (y : RExp Ψ)
           → (∀ {b} → b ∈ partsʳ s y → Ordʳ Q δ b) → Q ⊩ ⟦ s ⟧ʳᵖ⁺ [ δ ]ʳ ≾̂ᵣ y [ δ ]ʳ
partsʳ-lub (alt p)  y k = k (here refl)
partsʳ-lub (p ∷⁺ s) y k = ⊔-lubᵣ (k (here refl)) (partsʳ-lub s y (λ m → k (there m)))

partsʳ-ub : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (s : Alts (List (RAtom Ψ))) → (y : RExp Ψ)
          → Q ⊩ ⟦ s ⟧ʳᵖ⁺ [ δ ]ʳ ≾̂ᵣ y [ δ ]ʳ → ∀ {b} → b ∈ partsʳ s y → Ordʳ Q δ b
partsʳ-ub (alt p)  y h (here refl) = h
partsʳ-ub (p ∷⁺ s) y h (here refl) = transᵣ ⊔-ubˡᵣ h
partsʳ-ub (p ∷⁺ s) y h (there m)   = partsʳ-ub s y (transᵣ ⊔-ubʳᵣ h) m

partsₑ-lub : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (s : Alts (List (EAtom Ψ))) → (y : EExp Ψ)
           → (∀ {b} → b ∈ partsₑ s y → Ordᵉ Q δ b) → Q ⊩ ⟦ s ⟧ᵉᵖ⁺ [ δ ]ᵉ ≾̂ₑ y [ δ ]ᵉ
partsₑ-lub (alt p)  y k = k (here refl)
partsₑ-lub (p ∷⁺ s) y k = ⊔-lubₑ (k (here refl)) (partsₑ-lub s y (λ m → k (there m)))

partsₑ-ub : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (s : Alts (List (EAtom Ψ))) → (y : EExp Ψ)
          → Q ⊩ ⟦ s ⟧ᵉᵖ⁺ [ δ ]ᵉ ≾̂ₑ y [ δ ]ᵉ → ∀ {b} → b ∈ partsₑ s y → Ordᵉ Q δ b
partsₑ-ub (alt p)  y h (here refl) = h
partsₑ-ub (p ∷⁺ s) y h (here refl) = transₑ ⊔-ubˡₑ h
partsₑ-ub (p ∷⁺ s) y h (there m)   = partsₑ-ub s y (transₑ ⊔-ubʳₑ h) m

-- An ordering: its left side's alternatives, each below its right side

piecesʳ : ∀ {Ψ} → (a : RExp Ψ × RExp Ψ) → Pieces Ordʳ a
piecesʳ (x , y) =
  pieces (partsʳ s (canonᵣ y))
         (λ δ k → transᵣ (eqᵣ (≡̂ᵣ-subst δ (canonᵣ-≡ x)))
                    (transᵣ (partsʳ-lub s (canonᵣ y) k)
                            (eqᵣ (≡̂ᵣ-sym (≡̂ᵣ-subst δ (canonᵣ-≡ y))))))
         (λ δ h → partsʳ-ub s (canonᵣ y)
                    (transᵣ (eqᵣ (≡̂ᵣ-sym (≡̂ᵣ-subst δ (canonᵣ-≡ x))))
                            (transᵣ h (eqᵣ (≡̂ᵣ-subst δ (canonᵣ-≡ y))))))
  where
    s = canonSumᵣ (nrmᵣ x)

piecesᵉ : ∀ {Ψ} → (a : EExp Ψ × EExp Ψ) → Pieces Ordᵉ a
piecesᵉ (x , y) =
  pieces (partsₑ s (canonₑ y))
         (λ δ k → transₑ (eqₑ (≡̂ₑ-subst δ (canonₑ-≡ x)))
                    (transₑ (partsₑ-lub s (canonₑ y) k)
                            (eqₑ (≡̂ₑ-sym (≡̂ₑ-subst δ (canonₑ-≡ y))))))
         (λ δ h → partsₑ-ub s (canonₑ y)
                    (transₑ (eqₑ (≡̂ₑ-sym (≡̂ₑ-subst δ (canonₑ-≡ x))))
                            (transₑ h (eqₑ (≡̂ₑ-subst δ (canonₑ-≡ y))))))
  where
    s = canonSumₑ (nrmₑ x)

-- Hypothesis sets: each ordering split, each disjunction's type and
-- grade in canonical form

canonᴴ : ∀ {Θ} → Hyps Θ → Hyps Θ
canonᴴ Q = hyps (ets Q) (subᵥ Q)
                (Split.out (splits piecesʳ (ordᵣ Q)))
                (Split.out (splits piecesᵉ (ordₑ Q)))
                (map (mapᵈ canonᵛ canonᵣ) (disj Q))

-- A set and its normal form entail each other

private

  ⊩-idʳ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ [ idˢ ]ʳ ≾̂ᵣ ρ' [ idˢ ]ʳ → Q ⊩ ρ ≾̂ᵣ ρ'
  ⊩-idʳ {Q = Q} {ρ} {ρ'} = subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([id]ʳ ρ) ([id]ʳ ρ')

  ⊩-idʳ⁻ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ ≾̂ᵣ ρ' → Q ⊩ ρ [ idˢ ]ʳ ≾̂ᵣ ρ' [ idˢ ]ʳ
  ⊩-idʳ⁻ {Q = Q} {ρ} {ρ'} = subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym ([id]ʳ ρ)) (sym ([id]ʳ ρ'))

  ⊩-idₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε [ idˢ ]ᵉ ≾̂ₑ ε' [ idˢ ]ᵉ → Q ⊩ ε ≾̂ₑ ε'
  ⊩-idₑ {Q = Q} {ε} {ε'} = subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([id]ᵉ ε) ([id]ᵉ ε')

  ⊩-idₑ⁻ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → Q ⊩ ε [ idˢ ]ᵉ ≾̂ₑ ε' [ idˢ ]ᵉ
  ⊩-idₑ⁻ {Q = Q} {ε} {ε'} = subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym ([id]ᵉ ε)) (sym ([id]ᵉ ε'))

canonᴴ-⊩ : ∀ {Θ} → (Q : Hyps Θ) → canonᴴ Q ⊩ᴴ Q
canonᴴ-⊩ Q = mk⊩ᴴ⁼ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) ordR ordE dsj
  where
    ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → canonᴴ Q ⊩ ρ ≾̂ᵣ ρ'
    ordR m = ⊩-idʳ (Split.back (splits piecesʳ (ordᵣ Q)) idˢ (λ m' → ⊩-idʳ⁻ (hypᵣ m')) m)

    ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → canonᴴ Q ⊩ ε ≾̂ₑ ε'
    ordE m = ⊩-idₑ (Split.back (splits piecesᵉ (ordₑ Q)) idˢ (λ m' → ⊩-idₑ⁻ (hypₑ m')) m)

    dsj : ∀ {A ρ} → (A , ρ) ∈ disj Q → VarOK (canonᴴ Q) A ρ
    dsj {A} {ρ} m =
      hyp-ok (∈-map⁺ (mapᵈ canonᵛ canonᵣ) m) (canonᵛ-≡̂ A) (eqᵣ (canonᵣ-≡ ρ))

canonᴴ-⊩⁻ : ∀ {Θ} → (Q : Hyps Θ) → Q ⊩ᴴ canonᴴ Q
canonᴴ-⊩⁻ Q = mk⊩ᴴ⁼ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) ordR ordE dsj
  where
    ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ Split.out (splits piecesʳ (ordᵣ Q)) → Q ⊩ ρ ≾̂ᵣ ρ'
    ordR m = ⊩-idʳ (Split.fwd (splits piecesʳ (ordᵣ Q)) idˢ (λ m' → ⊩-idʳ⁻ (hypᵣ m')) m)

    ordE : ∀ {ε ε'} → (ε , ε') ∈ Split.out (splits piecesᵉ (ordₑ Q)) → Q ⊩ ε ≾̂ₑ ε'
    ordE m = ⊩-idₑ (Split.fwd (splits piecesᵉ (ordₑ Q)) idˢ (λ m' → ⊩-idₑ⁻ (hypₑ m')) m)

    dsj : ∀ {A ρ} → (A , ρ) ∈ map (mapᵈ canonᵛ canonᵣ) (disj Q) → VarOK Q A ρ
    dsj m with ∈-map⁻ (mapᵈ canonᵛ canonᵣ) m
    ... | (A₀ , ρ₀) , m₀ , refl =
          hyp-ok m₀ (≡̂ᵛ-sym (canonᵛ-≡̂ A₀)) (eqᵣ (≡̂ᵣ-sym (canonᵣ-≡ ρ₀)))
