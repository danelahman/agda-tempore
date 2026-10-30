--------------------------------------------------------------------
-- Deferred rigid conditions                                      --
--                                                                --
-- A clause's grade orderings that mix its rigid with outer       --
-- unknowns are deferred as a quantified ordering `∀ᵉ j₁ … jₖ. O` --
-- (`Quantified`), labelled with the clause's operation. One is   --
-- discharged along a substitution when its orderings are, at     --
-- fresh rigids (`_⊩ᴼ_[_]`); the answer returns them as           --
-- quantified hypotheses. Closed witnesses for the rigids are     --
-- drawn from the unit, the top and the hints' `witnesses`        --
-- (`candidates`).                                                --
--                                                                --
-- Contract. A move down (up) keeps an entry whose greater        --
-- (smaller) sides it fixes (`keepᵈ`). Closing an entry over one  --
-- more rigid holds exactly where the entry does at a fresh rigid --
-- (`closeᵈ-sound`, `closeᵈ-princ`). The driver retries the       --
-- entries (`retry`).                                             --
--------------------------------------------------------------------

open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using (List; []; _∷_; map; _++_; concatMap; deduplicate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
import Data.List.Relation.Binary.Pointwise as Pw
open import Data.List.Properties using (≡-dec)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Relation.Binary.Definitions using (Decidable)

open import Grades.Base
open import Grades.Hints using (SystemHints; module SystemHintsInterface)
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.SolverImpl.Deferred (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) where

open LanguageSpec S
open GradeSystemInterface Grades
open SystemHintsInterface hints
open Operations Ops using (Op)

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses               S
open import PolymorphicCalculus.Hypotheses.Instances     S using (_⊩ᴼˢ_[_])

------------------------------------------------------------------------
-- Lifting an ordering of substitutions over the rigids

≾ˢ-↑ᵉ : ∀ {Θ Θ'} {Q : Hyps Θ'} {σ τ : Subst Θ Θ'}
      → Q ⊩ σ ≾ˢ τ → wkᵉ-H Q ⊩ (σ ↑ᵉ) ≾ˢ (τ ↑ᵉ)
≾ˢ-↑ᵉ p = mk≾ˢ (λ i → ⊩-wkᵉᵣ (≾ˢʳ p i))
               (λ { zero → ⊩≾̂ₑ-refl ; (suc i) → ⊩-wkᵉₑ (≾ˢᵉ p i) })

≾ˢ-↑ᵉⁿ : ∀ {Θ Θ'} {Q : Hyps Θ'} {σ τ : Subst Θ Θ'} → (k : ℕ)
       → Q ⊩ σ ≾ˢ τ → wkᵉⁿ-H k Q ⊩ (σ ↑ᵉⁿ k) ≾ˢ (τ ↑ᵉⁿ k)
≾ˢ-↑ᵉⁿ zero    p = p
≾ˢ-↑ᵉⁿ (suc k) p = ≾ˢ-↑ᵉⁿ k (≾ˢ-↑ᵉ p)

------------------------------------------------------------------------
-- Entries

-- An entry over the scope extended by one rigid binds it outermost

bindᵈ : ∀ {Ψ} → QOrd (Ψ +e) → QOrd Ψ
bindᵈ (qord l k o) = qord l (suc k) o

-- A list of entries, discharged member by member

⊩ᴰ→⊩ᴼˢ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (D : List (QOrd Ψ))
       → (∀ {E} → E ∈ D → Q ⊩ᴼ E [ δ ]) → Q ⊩ᴼˢ D [ δ ]
⊩ᴰ→⊩ᴼˢ []      h = []
⊩ᴰ→⊩ᴼˢ (E ∷ D) h = h (here refl) ∷ ⊩ᴰ→⊩ᴼˢ D (λ m → h (there m))

⊩ᴼˢ→⊩ᴰ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (D : List (QOrd Ψ))
       → Q ⊩ᴼˢ D [ δ ] → ∀ {E} → E ∈ D → Q ⊩ᴼ E [ δ ]
⊩ᴼˢ→⊩ᴰ (E ∷ D) (h ∷ hs) (here refl) = h
⊩ᴼˢ→⊩ᴰ (E ∷ D) (h ∷ hs) (there m)   = ⊩ᴼˢ→⊩ᴰ D hs m

------------------------------------------------------------------------
-- Keeping an entry under a move

data Dir : Set where
  dir↓ dir↑ : Dir

-- The move is below (`dir↓`) or above (`dir↑`) the substitution it moves

Moves : ∀ {Ψ Ψ'} → Dir → Hyps Ψ' → Subst Ψ Ψ → Subst Ψ Ψ' → Set
Moves dir↓ Q σ τ = Q ⊩ (σ ⨟ˢ τ) ≾ˢ τ
Moves dir↑ Q σ τ = Q ⊩ τ ≾ˢ (σ ⨟ˢ τ)

-- The side an ordering keeps fixed: the greater under a move down, the smaller
-- under a move up

Fixedʳ : ∀ {Ψ} → Dir → Subst Ψ Ψ → RExp Ψ × RExp Ψ → Set
Fixedʳ dir↓ σ (x , y) = y [ σ ]ʳ ≅ʳ y
Fixedʳ dir↑ σ (x , y) = x [ σ ]ʳ ≅ʳ x

Fixedᵉ : ∀ {Ψ} → Dir → Subst Ψ Ψ → EExp Ψ × EExp Ψ → Set
Fixedᵉ dir↓ σ (x , y) = y [ σ ]ᵉ ≅ᵉ y
Fixedᵉ dir↑ σ (x , y) = x [ σ ]ᵉ ≅ᵉ x

fixedʳ? : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (a : RExp Ψ × RExp Ψ) → Maybe (Fixedʳ d σ a)
fixedʳ? dir↓ σ (x , y) with y [ σ ]ʳ ≟ʳ y
... | yes q = just q
... | no _  = nothing
fixedʳ? dir↑ σ (x , y) with x [ σ ]ʳ ≟ʳ x
... | yes q = just q
... | no _  = nothing

fixedᵉ? : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (a : EExp Ψ × EExp Ψ) → Maybe (Fixedᵉ d σ a)
fixedᵉ? dir↓ σ (x , y) with y [ σ ]ᵉ ≟ᵉ y
... | yes q = just q
... | no _  = nothing
fixedᵉ? dir↑ σ (x , y) with x [ σ ]ᵉ ≟ᵉ x
... | yes q = just q
... | no _  = nothing

allOf : ∀ {X : Set} {P : X → Set} → ((a : X) → Maybe (P a)) → (l : List X)
      → Maybe (∀ {a} → a ∈ l → P a)
allOf f []      = just (λ ())
allOf f (a ∷ l) with f a | allOf f l
... | just p | just g = just (λ { (here refl) → p ; (there m) → g m })
... | _      | _      = nothing

record Still {Ψ} (d : Dir) (σ : Subst Ψ Ψ) (E : QOrd Ψ) : Set where
  constructor still
  field
    stʳ : ∀ {a} → a ∈ ors (body E) → Fixedʳ d (σ ↑ᵉⁿ rigids E) a
    stᵉ : ∀ {a} → a ∈ oes (body E) → Fixedᵉ d (σ ↑ᵉⁿ rigids E) a

still? : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (E : QOrd Ψ) → Maybe (Still d σ E)
still? d σ E with allOf (fixedʳ? d (σ ↑ᵉⁿ rigids E)) (ors (body E))
                | allOf (fixedᵉ? d (σ ↑ᵉⁿ rigids E)) (oes (body E))
... | just r | just e = just (still r e)
... | _      | _      = nothing

stills? : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (D : List (QOrd Ψ))
        → Maybe (∀ {E} → E ∈ D → Still d σ E)
stills? d σ = allOf (still? d σ)

keepᵈ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {σ : Subst Ψ Ψ} {τ : Subst Ψ Ψ'} → (d : Dir) → (E : QOrd Ψ)
      → Still d σ E → Moves d Q σ τ → Q ⊩ᴼ E [ τ ] → Q ⊩ᴼ E [ σ ⨟ˢ τ ]
keepᵈ {Q = Q} {σ} {τ} d (qord l k o) (still sr se) mv h = mk⊩ᵒ (r d sr mv) (e d se mv)
  where
    Q' = wkᵉⁿ-H k Q

    fixr : (y : RExp _) → y [ σ ↑ᵉⁿ k ]ʳ ≅ʳ y → y [ τ ↑ᵉⁿ k ]ʳ ≡̂ᵣ y [ (σ ⨟ˢ τ) ↑ᵉⁿ k ]ʳ
    fixr y q = ≡̂ᵣ-trans (≡̂ᵣ-subst (τ ↑ᵉⁿ k) (≡̂ᵣ-sym (≅ʳ⇒≡̂ q)))
                       (subst (y [ σ ↑ᵉⁿ k ]ʳ [ τ ↑ᵉⁿ k ]ʳ ≡̂ᵣ_)
                              (trans ([⨟]ʳ y (σ ↑ᵉⁿ k) (τ ↑ᵉⁿ k)) ([≐]ʳ (⨟-↑ᵉⁿ σ τ k) y))
                              ≡̂ᵣ-refl)

    fixe : (y : EExp _) → y [ σ ↑ᵉⁿ k ]ᵉ ≅ᵉ y → y [ τ ↑ᵉⁿ k ]ᵉ ≡̂ₑ y [ (σ ⨟ˢ τ) ↑ᵉⁿ k ]ᵉ
    fixe y q = ≡̂ₑ-trans (≡̂ₑ-subst (τ ↑ᵉⁿ k) (≡̂ₑ-sym (≅ᵉ⇒≡̂ q)))
                       (subst (y [ σ ↑ᵉⁿ k ]ᵉ [ τ ↑ᵉⁿ k ]ᵉ ≡̂ₑ_)
                              (trans ([⨟]ᵉ y (σ ↑ᵉⁿ k) (τ ↑ᵉⁿ k)) ([≐]ᵉ (⨟-↑ᵉⁿ σ τ k) y))
                              ≡̂ₑ-refl)

    r : (d : Dir) → (∀ {a} → a ∈ ors o → Fixedʳ d (σ ↑ᵉⁿ k) a) → Moves d Q σ τ
      → ∀ {x y} → (x , y) ∈ ors o → Q' ⊩ x [ (σ ⨟ˢ τ) ↑ᵉⁿ k ]ʳ ≾̂ᵣ y [ (σ ⨟ˢ τ) ↑ᵉⁿ k ]ʳ
    r dir↓ sr mv {x} {y} m =
      transᵣ (mono-substᵣ (≾ˢ-↑ᵉⁿ k mv) x)
             (transᵣ (⊩ors h m) (eqᵣ (fixr y (sr m))))
    r dir↑ sr mv {x} {y} m =
      transᵣ (transᵣ (eqᵣ (≡̂ᵣ-sym (fixr x (sr m)))) (⊩ors h m))
             (mono-substᵣ (≾ˢ-↑ᵉⁿ k mv) y)

    e : (d : Dir) → (∀ {a} → a ∈ oes o → Fixedᵉ d (σ ↑ᵉⁿ k) a) → Moves d Q σ τ
      → ∀ {x y} → (x , y) ∈ oes o → Q' ⊩ x [ (σ ⨟ˢ τ) ↑ᵉⁿ k ]ᵉ ≾̂ₑ y [ (σ ⨟ˢ τ) ↑ᵉⁿ k ]ᵉ
    e dir↓ se mv {x} {y} m =
      transₑ (mono-substₑ (≾ˢ-↑ᵉⁿ k mv) x)
             (transₑ (⊩oes h m) (eqₑ (fixe y (se m))))
    e dir↑ se mv {x} {y} m =
      transₑ (transₑ (eqₑ (≡̂ₑ-sym (fixe x (se m)))) (⊩oes h m))
             (mono-substₑ (≾ˢ-↑ᵉⁿ k mv) y)

------------------------------------------------------------------------
-- The rigids at closed witnesses

-- `κ⟨ b ⟩` sends the newest effect-grade variable to `b`, fixing the rest

κ⟨_⟩ : ∀ {Ψ} → EExp Ψ → Subst (Ψ +e) Ψ
κ⟨ b ⟩ = sub tvar rvar (λ { zero → b ; (suc i) → evar i })

wk-κ : ∀ {Ψ} → (b : EExp Ψ) → (wkˢᵉ {Ψ} ⨟ˢ κ⟨ b ⟩) ≐ˢ idˢ
wk-κ b = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

κ-wkᵛ : ∀ {Ψ} → (b : EExp Ψ) → (A : OVType Ψ) → A [ wkˢᵉ ]ᵛ [ κ⟨ b ⟩ ]ᵛ ≡ A
κ-wkᵛ b A = trans ([⨟]ᵛ A wkˢᵉ κ⟨ b ⟩) (trans ([≐]ᵛ (wk-κ b) A) ([id]ᵛ A))

κ-wkʳ : ∀ {Ψ} → (b : EExp Ψ) → (ρ : RExp Ψ) → ρ [ wkˢᵉ ]ʳ [ κ⟨ b ⟩ ]ʳ ≡ ρ
κ-wkʳ b ρ = trans ([⨟]ʳ ρ wkˢᵉ κ⟨ b ⟩) (trans ([≐]ʳ (wk-κ b) ρ) ([id]ʳ ρ))

κ-wkᵉ : ∀ {Ψ} → (b : EExp Ψ) → (ε : EExp Ψ) → ε [ wkˢᵉ ]ᵉ [ κ⟨ b ⟩ ]ᵉ ≡ ε
κ-wkᵉ b ε = trans ([⨟]ᵉ ε wkˢᵉ κ⟨ b ⟩) (trans ([≐]ᵉ (wk-κ b) ε) ([id]ᵉ ε))

-- Every weakened hypothesis is entailed back by the original set

⊩ᴴ-κ : ∀ {Ψ} {Q : Hyps Ψ} → (b : EExp Ψ) → Q ⊩ᴴ (wkᵉ-H Q) [ κ⟨ b ⟩ ]
⊩ᴴ-κ b = ⊩ᴴ-≐ (mk≐ˢ (λ α → refl) (λ i → refl) (λ { zero → refl ; (suc i) → refl }))
               (⊩ᴴ-wkᵉ-,ᵉ b)

-- A constant commutes with a lift

↑-κ : ∀ {Ψ Ψ'} → (δ : Subst Ψ Ψ') → (c : E)
    → ((δ ↑ᵉ) ⨟ˢ κ⟨ econst c ⟩) ≐ˢ (κ⟨ econst c ⟩ ⨟ˢ δ)
↑-κ δ c =
  mk≐ˢ (λ α → trans (cong (_[ κ⟨ econst c ⟩ ]ᵛ) (sym (wkˢᵉ-v (sTy δ α))))
                    (κ-wkᵛ (econst c) (sTy δ α)))
       (λ i → trans (cong (_[ κ⟨ econst c ⟩ ]ʳ) (sym (wkˢᵉ-r (sR δ i))))
                    (κ-wkʳ (econst c) (sR δ i)))
       (λ { zero    → refl
          ; (suc i) → trans (cong (_[ κ⟨ econst c ⟩ ]ᵉ) (sym (wkˢᵉ-e (sE δ i))))
                            (κ-wkᵉ (econst c) (sE δ i)) })

-- One witness per rigid, outermost first, the unit where none is given

hdᵂ : List E → E
hdᵂ []      = uₑ
hdᵂ (c ∷ _) = c

tlᵂ : List E → List E
tlᵂ []       = []
tlᵂ (_ ∷ cs) = cs

wit : ∀ {Ψ} → (k : ℕ) → List E → Subst (Ψ +eⁿ k) Ψ
wit zero    cs = idˢ
wit (suc k) cs = wit k (tlᵂ cs) ⨟ˢ κ⟨ econst (hdᵂ cs) ⟩

-- Every choice of a candidate of `cs` for each rigid

grid : List E → ℕ → List (List E)
grid cs zero    = [] ∷ []
grid cs (suc k) = concatMap (λ c → map (c ∷_) (grid cs k)) cs

-- The candidates for the rigids of an ordering of degree `d` with constants `rcs`
-- and `ecs`: the unit, the top and the hints' `witnesses`, without repetition

candidates : ℕ → List R → List E → List E
candidates d rcs ecs = deduplicate _≃ₑ?_ (uₑ ∷ ⊤ₑ ∷ witnesses d rcs ecs)

-- The constants of an expression, and its occurrences of the rigids where its
-- ordering can be refuted

constsₑ : ∀ {Ψ} → EExp Ψ → List E
constsₑ (evar _)   = []
constsₑ (econst c) = c ∷ []
constsₑ (a ·̂ₑ b)   = constsₑ a ++ constsₑ b
constsₑ (a ⊔̂ₑ b)   = constsₑ a ++ constsₑ b

_++²_ : List R × List E → List R × List E → List R × List E
(r , e) ++² (r' , e') = r ++ r' , e ++ e'

constsᵣ : ∀ {Ψ} → RExp Ψ → List R × List E
constsᵣ (rvar _)   = [] , []
constsᵣ (rconst c) = c ∷ [] , []
constsᵣ (a ·̂ᵣ b)   = constsᵣ a ++² constsᵣ b
constsᵣ (a ⊔̂ᵣ b)   = constsᵣ a ++² constsᵣ b
constsᵣ ∣ ε ∣̂ᵉ     = [] , constsₑ ε

degreeₑ : ∀ {Ψ} → EExp Ψ → ℕ
degreeₑ (evar _)   = 1
degreeₑ (econst _) = 0
degreeₑ (a ·̂ₑ b)   = degreeₑ a + degreeₑ b
degreeₑ (a ⊔̂ₑ b)   = degreeₑ a + degreeₑ b

degreeᵣ : ∀ {Ψ} → RExp Ψ → ℕ
degreeᵣ (rvar _)   = 0
degreeᵣ (rconst _) = 0
degreeᵣ (a ·̂ᵣ b)   = degreeᵣ a + degreeᵣ b
degreeᵣ (a ⊔̂ᵣ b)   = degreeᵣ a + degreeᵣ b
degreeᵣ ∣ ε ∣̂ᵉ     = degreeₑ ε

-- The candidates for an ordering of either sort

candidatesₑ : ∀ {Ψ} → EExp Ψ → EExp Ψ → List E
candidatesₑ x y = candidates (degreeₑ x ⊔ degreeₑ y) [] (constsₑ x ++ constsₑ y)

candidatesᵣ : ∀ {Ψ} → RExp Ψ → RExp Ψ → List E
candidatesᵣ x y with constsᵣ x ++² constsᵣ y
... | (rcs , ecs) = candidates (degreeᵣ x ⊔ degreeᵣ y) rcs ecs

wit-⨟ : ∀ {Ψ Ψ'} → (δ : Subst Ψ Ψ') → (k : ℕ) → (cs : List E)
      → ((δ ↑ᵉⁿ k) ⨟ˢ wit k cs) ≐ˢ (wit k cs ⨟ˢ δ)
wit-⨟ δ zero    cs = ≐ˢ-trans (⨟-idʳ δ) (≐ˢ-sym (⨟-idˡ δ))
wit-⨟ δ (suc k) cs =
  ≐ˢ-trans (≐ˢ-sym (⨟-assoc ((δ ↑ᵉ) ↑ᵉⁿ k) (wit k (tlᵂ cs)) κ))
  (≐ˢ-trans (⨟-congˡ (wit-⨟ (δ ↑ᵉ) k (tlᵂ cs)) κ)
  (≐ˢ-trans (⨟-assoc (wit k (tlᵂ cs)) (δ ↑ᵉ) κ)
  (≐ˢ-trans (⨟-congʳ (wit k (tlᵂ cs)) (↑-κ δ (hdᵂ cs)))
            (≐ˢ-sym (⨟-assoc (wit k (tlᵂ cs)) κ δ)))))
  where
    κ : ∀ {Φ} → Subst (Φ +e) Φ
    κ = κ⟨ econst (hdᵂ cs) ⟩

-- No hypotheses entail the empty set at the witnesses

⊩ᴴ-wit : ∀ {Ψ} → (k : ℕ) → (cs : List E) → ∅ᴴ ⊩ᴴ wkᵉⁿ-H k (∅ᴴ {Ψ}) [ wit k cs ]
⊩ᴴ-wit {Ψ} k cs = subst (λ H → ∅ᴴ ⊩ᴴ H [ wit k cs ]) (sym (wkᵉⁿ-∅ᴴ {Ψ} k)) ⊩ᴴ-∅

------------------------------------------------------------------------
-- Closing an entry over the newest variable: bound outermost where the entry
-- mentions it, dropped otherwise

-- Orderings the same pair by pair, both sides the same

Pairs : ∀ {X : Set} → (X → X → Set) → X × X → X × X → Set
Pairs _≅_ (x , y) (x' , y') = x ≅ x' × y ≅ y'

pairs? : ∀ {X : Set} {_≅_ : X → X → Set} → Decidable _≅_ → Decidable (Pairs _≅_)
pairs? _≟_ (x , y) (x' , y') = (x ≟ x') ×-dec (y ≟ y')

Sameᴼ : ∀ {Ψ} → Ords Ψ → Ords Ψ → Set
Sameᴼ o o' = Pointwise (Pairs _≅ʳ_) (ors o) (ors o') × Pointwise (Pairs _≅ᵉ_) (oes o) (oes o')

_≟ᴼ_ : ∀ {Ψ} → (o o' : Ords Ψ) → Dec (Sameᴼ o o')
o ≟ᴼ o' = Pw.decidable (pairs? _≟ʳ_) (ors o) (ors o') ×-dec Pw.decidable (pairs? _≟ᵉ_) (oes o) (oes o')

pw-∈ : ∀ {X : Set} {R : X → X → Set} {xs ys y} → Pointwise R xs ys → y ∈ ys
     → Σ[ x ∈ X ] (x ∈ xs × R x y)
pw-∈ (r ∷ rs) (here refl) = _ , here refl , r
pw-∈ (r ∷ rs) (there m) with pw-∈ rs m
... | x , m' , q = x , there m' , q

⊩ᵒ-same : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {o o' : Ords Ψ} {δ : Subst Ψ Ψ'}
        → Sameᴼ o o' → Q ⊩ᵒ o [ δ ] → Q ⊩ᵒ o' [ δ ]
⊩ᵒ-same {Q = Q} {o' = o'} {δ} (pr , pe) h = mk⊩ᵒ r e
  where
    r : ∀ {x y} → (x , y) ∈ ors o' → Q ⊩ x [ δ ]ʳ ≾̂ᵣ y [ δ ]ʳ
    r m with pw-∈ pr m
    ... | _ , m₀ , p , q =
          transᵣ (eqᵣ (≡̂ᵣ-subst δ (≡̂ᵣ-sym (≅ʳ⇒≡̂ p))))
                 (transᵣ (⊩ors h m₀) (eqᵣ (≡̂ᵣ-subst δ (≅ʳ⇒≡̂ q))))

    e : ∀ {x y} → (x , y) ∈ oes o' → Q ⊩ x [ δ ]ᵉ ≾̂ₑ y [ δ ]ᵉ
    e m with pw-∈ pe m
    ... | _ , m₀ , p , q =
          transₑ (eqₑ (≡̂ₑ-subst δ (≡̂ₑ-sym (≅ᵉ⇒≡̂ p))))
                 (transₑ (⊩oes h m₀) (eqₑ (≡̂ₑ-subst δ (≅ᵉ⇒≡̂ q))))

closeᵈ : ∀ {Ψ} → QOrd (Ψ +e) → QOrd Ψ
closeᵈ (qord l k o) with o [ κ⟨ ûₑ ⟩ ↑ᵉⁿ k ]ᴼ [ wkˢᵉ ↑ᵉⁿ k ]ᴼ ≟ᴼ o
... | yes _ = qord l k (o [ κ⟨ ûₑ ⟩ ↑ᵉⁿ k ]ᴼ)
... | no _  = bindᵈ (qord l k o)

closeᵈ-sound : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (E : QOrd (Ψ +e))
             → Q ⊩ᴼ closeᵈ E [ δ ] → wkᵉ-H Q ⊩ᴼ E [ δ ↑ᵉ ]
closeᵈ-sound {Q = Q} {δ} (qord l k o) h with o [ κ⟨ ûₑ ⟩ ↑ᵉⁿ k ]ᴼ [ wkˢᵉ ↑ᵉⁿ k ]ᴼ ≟ᴼ o
... | no _  = h
... | yes q =
      ⊩ᵒ-same q
            (⊩ᵒ-subst⁻ (⊩ᵒ-resp-≐ˢ eq (⊩ᵒ-⨟ (⊩ᴴ-↑ᵉⁿ k ⊩ᴴ-wkᵉ) h)))
  where
    eq : ((δ ↑ᵉⁿ k) ⨟ˢ (wkˢᵉ ↑ᵉⁿ k)) ≐ˢ ((wkˢᵉ ↑ᵉⁿ k) ⨟ˢ ((δ ↑ᵉ) ↑ᵉⁿ k))
    eq = ≐ˢ-trans (⨟-↑ᵉⁿ δ wkˢᵉ k)
         (≐ˢ-trans (≐ˢ-↑ᵉⁿ (≐ˢ-sym (wkˢᵉ-↑ᵉ δ)) k) (≐ˢ-sym (⨟-↑ᵉⁿ wkˢᵉ (δ ↑ᵉ) k)))

closeᵈ-princ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (E : QOrd (Ψ +e))
             → wkᵉ-H Q ⊩ᴼ E [ δ ↑ᵉ ] → Q ⊩ᴼ closeᵈ E [ δ ]
closeᵈ-princ {Q = Q} {δ} (qord l k o) h with o [ κ⟨ ûₑ ⟩ ↑ᵉⁿ k ]ᴼ [ wkˢᵉ ↑ᵉⁿ k ]ᴼ ≟ᴼ o
... | no _  = h
... | yes _ = ⊩ᵒ-subst⁻ (⊩ᵒ-resp-≐ˢ eq (⊩ᵒ-⨟ (⊩ᴴ-↑ᵉⁿ k (⊩ᴴ-κ ûₑ)) h))
  where
    eq : (((δ ↑ᵉ) ↑ᵉⁿ k) ⨟ˢ (κ⟨ ûₑ ⟩ ↑ᵉⁿ k)) ≐ˢ ((κ⟨ ûₑ ⟩ ↑ᵉⁿ k) ⨟ˢ (δ ↑ᵉⁿ k))
    eq = ≐ˢ-trans (⨟-↑ᵉⁿ (δ ↑ᵉ) κ⟨ ûₑ ⟩ k)
         (≐ˢ-trans (≐ˢ-↑ᵉⁿ (↑-κ δ uₑ) k) (≐ˢ-sym (⨟-↑ᵉⁿ κ⟨ ûₑ ⟩ δ k)))
