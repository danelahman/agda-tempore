--------------------------------------------------------------------
-- Entailment of grade orderings from hypotheses                  --
--                                                                --
-- The hypothesis graph of `Q` (`Edgeₑ`, `Edgeᵣ`) has the grade   --
-- expressions of a sort as vertices. Its edges are the orderings --
-- of `Q`, sameness, the order between constants, links to the    --
-- top and from a least unit, the images of effect chains         --
-- (resource side), and factor edges (`Keepₑ`) through atoms      --
-- above the unit (`Aboveₑ`, `Aboveᵣ`: a least fixed point, by    --
-- Kleene iteration).                                             --
--                                                                --
-- A query `e ≾ e'` is decided at a `Strength`: `closed` (no      --
-- variables, by the grade's `_≾?_`), `derive` (the embedding of  --
-- `Normal` along atomic edges), `atomic` (an ordering of `Q`, or --
-- `derive`) or `full` (along chains of the whole graph).         --
--                                                                --
-- Contract. Every edge holds where `Q` does (`edgeₑ-sound`,      --
-- `edgeᵣ-sound`); a `just` is a derivation of `Q ⊩ e ≾̂ e'`, a    --
-- `nothing` claims nothing. `refute≾u` refutes `ρ ≾ u` from      --
-- every satisfiable set (`refute-⊩`). `checkClosed Q` is         --
-- equivalent to `Q` (`checkClosed-⊩`, `checkClosed-⊆`) and fails --
-- only on an unsatisfiable set (`checkClosed-fail`), as a        --
-- failing chain does.                                            --
--------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁻; ∈-map⁻)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (lookup-result)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just; _<∣>_)
open import Data.Maybe using (Is-just; to-witness)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<ᵇ_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star) renaming (ε to ◅-nil; _◅_ to _◅◅_; _◅◅_ to _⋆_)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (does)

open import Grades.Base
open import Grades.Hints using (SystemHints; module SystemHintsInterface)
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.SolverImpl.Entail (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) where

open LanguageSpec S
open GradeSystemInterface Grades
open SystemHintsInterface hints

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses               S
open import PolymorphicCalculus.Hypotheses.Instances     S
  using (Satisfiable; ⊨⇒⊩ᴴ; VarOK-∅; inst-≡̂ᵣ; inst-≾ᵣ; val-≾ᵣ⁻; closed-≾ᵣ; closed-≾ₑ)

open import PolymorphicCalculus.Inference.SolverImpl.Normal S hints
open import PolymorphicCalculus.Inference.SolverImpl.Resid  S using (etDec; etDec-refute)
import PolymorphicCalculus.Inference.SolverImpl.Reach as Reachability

------------------------------------------------------------------------
-- Sides and values

-- The sides of a list of orderings

sidesOf : ∀ {X : Set} → List (X × X) → List X
sidesOf []            = []
sidesOf ((a , b) ∷ l) = a ∷ b ∷ sidesOf l

sidesₑ : ∀ {Θ} → Hyps Θ → List (EExp Θ)
sidesₑ Q = sidesOf (ordₑ Q)

sidesᵣ : ∀ {Θ} → Hyps Θ → List (RExp Θ)
sidesᵣ Q = sidesOf (ordᵣ Q)

-- The value of an expression with no unknowns

valᵉ? : ∀ {Θ} → EExp Θ → Maybe E
valᵉ? (evar i)   = nothing
valᵉ? (econst c) = just c
valᵉ? (ε ·̂ₑ ε') with valᵉ? ε | valᵉ? ε'
... | just c | just c' = just (c ·ₑ c')
... | _      | _       = nothing
valᵉ? (ε ⊔̂ₑ ε') with valᵉ? ε | valᵉ? ε'
... | just c | just c' = just (c ⊔ₑ c')
... | _      | _       = nothing

valʳ? : ∀ {Θ} → RExp Θ → Maybe R
valʳ? (rvar i)   = nothing
valʳ? (rconst c) = just c
valʳ? (ρ ·̂ᵣ ρ') with valʳ? ρ | valʳ? ρ'
... | just c | just c' = just (c ·ᵣ c')
... | _      | _       = nothing
valʳ? (ρ ⊔̂ᵣ ρ') with valʳ? ρ | valʳ? ρ'
... | just c | just c' = just (c ⊔ᵣ c')
... | _      | _       = nothing
valʳ? ∣ ε ∣̂ᵉ with valᵉ? ε
... | just c  = just (mapᵉ c)
... | nothing = nothing

-- An expression with a value is convertible to it

convᵉ : ∀ {Θ} {c : E} → (ε : EExp Θ) → valᵉ? ε ≡ just c → ε ≡̂ₑ econst c
convᵉ (evar i) ()
convᵉ (econst c) refl = ≡̂ₑ-refl
convᵉ (ε ·̂ₑ ε') q with valᵉ? ε in e₁ | valᵉ? ε' in e₂
convᵉ (ε ·̂ₑ ε') refl | just c | just c' =
  ≡̂ₑ-trans (≡̂ₑ-cong (convᵉ ε e₁) (convᵉ ε' e₂)) ≡̂ₑ-const-·
convᵉ (ε ·̂ₑ ε') () | just _  | nothing
convᵉ (ε ·̂ₑ ε') () | nothing | _
convᵉ (ε ⊔̂ₑ ε') q with valᵉ? ε in e₁ | valᵉ? ε' in e₂
convᵉ (ε ⊔̂ₑ ε') refl | just c | just c' =
  ≡̂ₑ-trans (≡̂ₑ-cong-⊔ (convᵉ ε e₁) (convᵉ ε' e₂)) ≡̂ₑ-const-⊔
convᵉ (ε ⊔̂ₑ ε') () | just _  | nothing
convᵉ (ε ⊔̂ₑ ε') () | nothing | _

convʳ : ∀ {Θ} {c : R} → (ρ : RExp Θ) → valʳ? ρ ≡ just c → ρ ≡̂ᵣ rconst c
convʳ (rvar i) ()
convʳ (rconst c) refl = ≡̂ᵣ-refl
convʳ (ρ ·̂ᵣ ρ') q with valʳ? ρ in e₁ | valʳ? ρ' in e₂
convʳ (ρ ·̂ᵣ ρ') refl | just c | just c' =
  ≡̂ᵣ-trans (≡̂ᵣ-cong (convʳ ρ e₁) (convʳ ρ' e₂)) ≡̂ᵣ-const-·
convʳ (ρ ·̂ᵣ ρ') () | just _  | nothing
convʳ (ρ ·̂ᵣ ρ') () | nothing | _
convʳ (ρ ⊔̂ᵣ ρ') q with valʳ? ρ in e₁ | valʳ? ρ' in e₂
convʳ (ρ ⊔̂ᵣ ρ') refl | just c | just c' =
  ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (convʳ ρ e₁) (convʳ ρ' e₂)) ≡̂ᵣ-const-⊔
convʳ (ρ ⊔̂ᵣ ρ') () | just _  | nothing
convʳ (ρ ⊔̂ᵣ ρ') () | nothing | _
convʳ ∣ ε ∣̂ᵉ q with valᵉ? ε in e
convʳ ∣ ε ∣̂ᵉ refl | just c = ≡̂ᵣ-trans (≡̂ᵣ-map-cong (convᵉ ε e)) ≡̂ᵣ-map-const
convʳ ∣ ε ∣̂ᵉ ()   | nothing


-- The unit's image is the unit

∣û∣ₑ : ∀ {Θ} → ûᵣ {Θ} ≡̂ᵣ ∣ ûₑ ∣̂ᵉ
∣û∣ₑ = ≡̂ᵣ-sym (≡̂ᵣ-trans ≡̂ᵣ-map-const (≡̂ᵣ-const map-uᵉ))

------------------------------------------------------------------------
-- The hypothesis graph

mutual

  data Edgeₑ {Θ : Scope} (Q : Hyps Θ) : EExp Θ → EExp Θ → Set where
    hyp    : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Edgeₑ Q ε ε'
    same   : ∀ {ε ε'} → ε ≅ᵉ ε' → Edgeₑ Q ε ε'
    cst    : ∀ {c c'} → c ≾ₑ c' → Edgeₑ Q (econst c) (econst c')
    top    : ∀ {ε} → Edgeₑ Q ε (econst ⊤ₑ)
    unit   : ∀ {ε} → Is-just uₑ-least? → Edgeₑ Q ûₑ ε
    factor : ∀ {ε ε₀ as bs} → ε ∈ sidesₑ Q → nrmₑ ε ≡ alt as → Keepₑ Q as bs
           → ε₀ ≡̂ₑ ⟦ bs ⟧ᵉˢ → Edgeₑ Q ε₀ ε

  -- `bs` is `as` with some atoms above the unit left out

  data Keepₑ {Θ : Scope} (Q : Hyps Θ) : List (EAtom Θ) → List (EAtom Θ) → Set where
    stop : Keepₑ Q [] []
    keep : ∀ {a as bs} → Keepₑ Q as bs → Keepₑ Q (a ∷ as) (a ∷ bs)
    skip : ∀ {a as bs} → Aboveₑ Q a → Keepₑ Q as bs → Keepₑ Q (a ∷ as) bs

  data Aboveₑ {Θ : Scope} (Q : Hyps Θ) : EAtom Θ → Set where
    const   : ∀ {c} → uₑ ≾ₑ c → Aboveₑ Q (ac c)
    least   : ∀ {a} → Is-just uₑ-least? → Aboveₑ Q a
    reached : ∀ {ε c a} → valᵉ? ε ≡ just c → uₑ ≾ₑ c → Star (Edgeₑ Q) ε ⟦ a ⟧ᵉᵃ
            → Aboveₑ Q a

mutual

  data Edgeᵣ {Θ : Scope} (Q : Hyps Θ) : RExp Θ → RExp Θ → Set where
    hyp    : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Edgeᵣ Q ρ ρ'
    same   : ∀ {ρ ρ'} → ρ ≅ʳ ρ' → Edgeᵣ Q ρ ρ'
    cst    : ∀ {c c'} → c ≾ᵣ c' → Edgeᵣ Q (rconst c) (rconst c')
    top    : ∀ {ρ} → Edgeᵣ Q ρ (rconst ⊤ᵣ)
    unit   : ∀ {ρ} → Is-just uᵣ-least? → Edgeᵣ Q ûᵣ ρ
    img    : ∀ {a b} → Star (Edgeₑ Q) ⟦ a ⟧ᵉᵃ ⟦ b ⟧ᵉᵃ → Edgeᵣ Q ⟦ ∣ a ∣ᵃ ⟧ʳᵃ ⟦ ∣ b ∣ᵃ ⟧ʳᵃ
    factor : ∀ {ρ ρ₀ as bs} → ρ ∈ sidesᵣ Q → nrmᵣ ρ ≡ alt as → Keepᵣ Q as bs
           → ρ₀ ≡̂ᵣ ⟦ bs ⟧ʳˢ → Edgeᵣ Q ρ₀ ρ

  data Keepᵣ {Θ : Scope} (Q : Hyps Θ) : List (RAtom Θ) → List (RAtom Θ) → Set where
    stop : Keepᵣ Q [] []
    keep : ∀ {a as bs} → Keepᵣ Q as bs → Keepᵣ Q (a ∷ as) (a ∷ bs)
    skip : ∀ {a as bs} → Aboveᵣ Q a → Keepᵣ Q as bs → Keepᵣ Q (a ∷ as) bs

  data Aboveᵣ {Θ : Scope} (Q : Hyps Θ) : RAtom Θ → Set where
    const   : ∀ {c} → uᵣ ≾ᵣ c → Aboveᵣ Q (rc c)
    least   : ∀ {a} → Is-just uᵣ-least? → Aboveᵣ Q a
    image   : ∀ {i} → Is-just uₑ-least? → Aboveᵣ Q (rm i)
    reached : ∀ {ρ c a} → valʳ? ρ ≡ just c → uᵣ ≾ᵣ c → Star (Edgeᵣ Q) ρ ⟦ a ⟧ʳᵃ
            → Aboveᵣ Q a

-- Every edge holds where the hypotheses do

mutual

  edgeₑ-sound : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Edgeₑ Q ε ε' → Q ⊩ ε ≾̂ₑ ε'
  edgeₑ-sound (hyp m)  = hypₑ m
  edgeₑ-sound (same p) = eqₑ (≅ᵉ⇒≡̂ p)
  edgeₑ-sound (cst p)  = atomₑ p
  edgeₑ-sound top      = topₑ
  edgeₑ-sound (unit q) = minₑ (to-witness q)
  edgeₑ-sound (factor {ε = ε} _ eq k c) =
    transₑ (eqₑ c) (transₑ (keepₑ-sound k)
                           (eqₑ (≡̂ₑ-sym (subst (λ s → ε ≡̂ₑ ⟦ s ⟧ᵉˢ⁺) eq (nrmₑ-≡ ε)))))

  -- `a · u ≾ a · b` where `u ≾ b`

  keepₑ-sound : ∀ {Θ} {Q : Hyps Θ} {as bs} → Keepₑ Q as bs → Q ⊩ ⟦ bs ⟧ᵉˢ ≾̂ₑ ⟦ as ⟧ᵉˢ
  keepₑ-sound stop       = ⊩≾̂ₑ-refl
  keepₑ-sound (keep k)   = monoₑ ⊩≾̂ₑ-refl (keepₑ-sound k)
  keepₑ-sound (skip a k) =
    transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-identityˡ)) (monoₑ (aboveₑ-sound a) (keepₑ-sound k))

  aboveₑ-sound : ∀ {Θ} {Q : Hyps Θ} {a} → Aboveₑ Q a → Q ⊩ ûₑ ≾̂ₑ ⟦ a ⟧ᵉᵃ
  aboveₑ-sound (const p)                  = atomₑ p
  aboveₑ-sound (least q)                  = minₑ (to-witness q)
  aboveₑ-sound (reached {ε = ε} eq p ch) =
    transₑ (atomₑ p) (transₑ (eqₑ (≡̂ₑ-sym (convᵉ ε eq))) (chainₑ-sound ch))

  chainₑ-sound : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Star (Edgeₑ Q) ε ε' → Q ⊩ ε ≾̂ₑ ε'
  chainₑ-sound ◅-nil     = ⊩≾̂ₑ-refl
  chainₑ-sound (e ◅◅ ch) = transₑ (edgeₑ-sound e) (chainₑ-sound ch)

mutual

  edgeᵣ-sound : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Edgeᵣ Q ρ ρ' → Q ⊩ ρ ≾̂ᵣ ρ'
  edgeᵣ-sound (hyp m)  = hypᵣ m
  edgeᵣ-sound (same p) = eqᵣ (≅ʳ⇒≡̂ p)
  edgeᵣ-sound (cst p)  = atomᵣ p
  edgeᵣ-sound top      = topᵣ
  edgeᵣ-sound (unit q) = minᵣ (to-witness q)
  edgeᵣ-sound (img {a} {b} ch) =
    transᵣ (eqᵣ (≡̂ᵣ-sym ∣⟦ a ⟧∣)) (transᵣ (map-mono (chainₑ-sound ch)) (eqᵣ ∣⟦ b ⟧∣))
  edgeᵣ-sound (factor {ρ = ρ} _ eq k c) =
    transᵣ (eqᵣ c) (transᵣ (keepᵣ-sound k)
                           (eqᵣ (≡̂ᵣ-sym (subst (λ s → ρ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺) eq (nrmᵣ-≡ ρ)))))

  keepᵣ-sound : ∀ {Θ} {Q : Hyps Θ} {as bs} → Keepᵣ Q as bs → Q ⊩ ⟦ bs ⟧ʳˢ ≾̂ᵣ ⟦ as ⟧ʳˢ
  keepᵣ-sound stop       = ⊩≾̂ᵣ-refl
  keepᵣ-sound (keep k)   = monoᵣ ⊩≾̂ᵣ-refl (keepᵣ-sound k)
  keepᵣ-sound (skip a k) =
    transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityˡ)) (monoᵣ (aboveᵣ-sound a) (keepᵣ-sound k))

  aboveᵣ-sound : ∀ {Θ} {Q : Hyps Θ} {a} → Aboveᵣ Q a → Q ⊩ ûᵣ ≾̂ᵣ ⟦ a ⟧ʳᵃ
  aboveᵣ-sound (const p)                  = atomᵣ p
  aboveᵣ-sound (least q)                  = minᵣ (to-witness q)
  aboveᵣ-sound (image q)                  = transᵣ (eqᵣ ∣û∣ₑ) (map-mono (minₑ (to-witness q)))
  aboveᵣ-sound (reached {ρ = ρ} eq p ch) =
    transᵣ (atomᵣ p) (transᵣ (eqᵣ (≡̂ᵣ-sym (convʳ ρ eq))) (chainᵣ-sound ch))

  chainᵣ-sound : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Star (Edgeᵣ Q) ρ ρ' → Q ⊩ ρ ≾̂ᵣ ρ'
  chainᵣ-sound ◅-nil     = ⊩≾̂ᵣ-refl
  chainᵣ-sound (e ◅◅ ch) = transᵣ (edgeᵣ-sound e) (chainᵣ-sound ch)

------------------------------------------------------------------------
-- Links and the edges between single atoms
--
-- Two atoms are linked when equal or joined by a `cst` edge. The atomic edges
-- are the `hyp` edges between single atoms and, for resources, their images.

EEdge : ∀ {Θ} → Hyps Θ → Set
EEdge {Θ} Q = Σ[ a ∈ EAtom Θ ] Σ[ b ∈ EAtom Θ ] (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)

REdge : ∀ {Θ} → Hyps Θ → Set
REdge {Θ} Q = Σ[ a ∈ RAtom Θ ] Σ[ b ∈ RAtom Θ ] (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)

AEdgeₑ : ∀ {Θ} → Hyps Θ → Set
AEdgeₑ {Θ} Q = Σ[ a ∈ EAtom Θ ] Σ[ b ∈ EAtom Θ ] Edgeₑ Q ⟦ a ⟧ᵉᵃ ⟦ b ⟧ᵉᵃ

AEdgeᵣ : ∀ {Θ} → Hyps Θ → Set
AEdgeᵣ {Θ} Q = Σ[ a ∈ RAtom Θ ] Σ[ b ∈ RAtom Θ ] Edgeᵣ Q ⟦ a ⟧ʳᵃ ⟦ b ⟧ʳᵃ

atomicₑ : ∀ {Θ} {Q : Hyps Θ} → (l : List (EExp Θ × EExp Θ))
        → (∀ {p} → p ∈ l → p ∈ ordₑ Q) → List (AEdgeₑ Q)
atomicₑ []             k = []
atomicₑ ((ε , ε') ∷ l) k with atomᵉ? ε | atomᵉ? ε'
... | just (a , refl) | just (b , refl) = (a , b , hyp (k (here refl))) ∷ atomicₑ l (λ m → k (there m))
... | _               | _               = atomicₑ l (λ m → k (there m))

atomicᵣ : ∀ {Θ} {Q : Hyps Θ} → (l : List (RExp Θ × RExp Θ))
        → (∀ {p} → p ∈ l → p ∈ ordᵣ Q) → List (AEdgeᵣ Q)
atomicᵣ []             k = []
atomicᵣ ((ρ , ρ') ∷ l) k with atomʳ? ρ | atomʳ? ρ'
... | just (a , refl) | just (b , refl) = (a , b , hyp (k (here refl))) ∷ atomicᵣ l (λ m → k (there m))
... | _               | _               = atomicᵣ l (λ m → k (there m))

readₑ : ∀ {Θ} {Q : Hyps Θ} → AEdgeₑ Q → EEdge Q
readₑ (a , b , e) = a , b , edgeₑ-sound e

readᵣ : ∀ {Θ} {Q : Hyps Θ} → AEdgeᵣ Q → REdge Q
readᵣ (a , b , e) = a , b , edgeᵣ-sound e

-- The image of an edge between effect atoms, between their images

imageᵣ : ∀ {Θ} {Q : Hyps Θ} → AEdgeₑ Q → REdge Q
imageᵣ (a , b , e) = ∣ a ∣ᵃ , ∣ b ∣ᵃ , edgeᵣ-sound (img (e ◅◅ ◅-nil))

edgesₑ : ∀ {Θ} → (Q : Hyps Θ) → List (EEdge Q)
edgesₑ Q = map readₑ (atomicₑ (ordₑ Q) (λ m → m))

edgesᵣ : ∀ {Θ} → (Q : Hyps Θ) → List (REdge Q)
edgesᵣ Q = map readᵣ (atomicᵣ (ordᵣ Q) (λ m → m)) ++ map imageᵣ (atomicₑ (ordₑ Q) (λ m → m))

linkₑ? : ∀ {Θ} {Q : Hyps Θ} → (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
linkₑ? (ac c) (ac d) with c ≾ₑ? d
... | yes p = just (edgeₑ-sound (cst p))
... | no _  = nothing
linkₑ? (av i) (av j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ₑ-refl
... | no _     = nothing
linkₑ? _      _      = nothing

linkᵣ? : ∀ {Θ} {Q : Hyps Θ} → (a b : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
linkᵣ? (rc c) (rc d) with c ≾ᵣ? d
... | yes p = just (edgeᵣ-sound (cst p))
... | no _  = nothing
linkᵣ? (rv i) (rv j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ᵣ-refl
... | no _     = nothing
linkᵣ? (rm i) (rm j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ᵣ-refl
... | no _     = nothing
linkᵣ? _      _      = nothing

-- What the sources of the edges between atoms reach

tableₑ : ∀ {Θ} {Q : Hyps Θ} → (es : List (EEdge Q))
       → Chains.Table (λ a b → Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ) ⊩≾̂ₑ-refl transₑ linkₑ? _≟ᵃₑ_ es
tableₑ es = Chains.table _ ⊩≾̂ₑ-refl transₑ linkₑ? _≟ᵃₑ_ es

tableᵣ : ∀ {Θ} {Q : Hyps Θ} → (es : List (REdge Q))
       → Chains.Table (λ a b → Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ) ⊩≾̂ᵣ-refl transᵣ linkᵣ? _≟ᵃᵣ_ es
tableᵣ es = Chains.table _ ⊩≾̂ᵣ-refl transᵣ linkᵣ? _≟ᵃᵣ_ es

-- The unit below anything, along a `unit` edge

min≾ₑ : ∀ {Θ} {Q : Hyps Θ} {ε : EExp Θ} → Maybe (Is-just uₑ-least?) → Maybe (Q ⊩ ûₑ ≾̂ₑ ε)
min≾ₑ (just q) = just (edgeₑ-sound (unit q))
min≾ₑ nothing  = nothing

min≾ᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → Maybe (Is-just uᵣ-least?) → Maybe (Q ⊩ ûᵣ ≾̂ᵣ ρ)
min≾ᵣ (just q) = just (edgeᵣ-sound (unit q))
min≾ᵣ nothing  = nothing

------------------------------------------------------------------------
-- The strength `derive`: the embedding of `Normal` along chains of atomic
-- edges, alternative by alternative (`⊔-lub`, `⊔-ubˡ`, `⊔-ubʳ`). The right
-- side's groups varying in one slot are folded into one (`foldSumₑ`).

module Searchₑ {Θ} {Q : Hyps Θ} (es : List (EEdge Q))
               (t : Chains.Table (λ a b → Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
                                 ⊩≾̂ₑ-refl transₑ linkₑ? _≟ᵃₑ_ es) where

  reachₑ? : (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
  reachₑ? = Chains.reach? _ ⊩≾̂ₑ-refl transₑ linkₑ? _≟ᵃₑ_ es t

  -- Anything is below an atom that the top reaches

  ceilₑ : ∀ {ε : EExp Θ} → (b : EAtom Θ) → Maybe (Q ⊩ ε ≾̂ₑ ⟦ b ⟧ᵉᵃ)
  ceilₑ b with reachₑ? (ac ⊤ₑ) b
  ... | just p  = just (transₑ (edgeₑ-sound top) p)
  ... | nothing = nothing

  -- An atom below an atom: linked, below an atom the top reaches, or along
  -- the atomic hypotheses

  atom≾ₑ : (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
  atom≾ₑ a b = linkₑ? a b <∣> ceilₑ b <∣> reachₑ? a b

  -- The unit below an atom: the grade's unit being least, or as the atom `uₑ`

  unit≾ₑ : (b : EAtom Θ) → Maybe (Q ⊩ ûₑ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
  unit≾ₑ b = min≾ₑ (Is-just? uₑ-least?) <∣> atom≾ₑ (ac uₑ) b

  -- An atom below the unit, as the constant atom `uₑ`

  ≾unitₑ : (a : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ûₑ)
  ≾unitₑ a = atom≾ₑ a (ac uₑ)

  -- The product comparison, its atom comparisons being these

  constᵉ? : EAtom Θ → Maybe E
  constᵉ? (ac c) = just c
  constᵉ? (av _) = nothing

  module Pₑ = Embedding constᵉ? (λ c → consₑ (ac c)) consₑ-length
                (λ a b → Is-just (atom≾ₑ a b)) (λ a b → is-just? (atom≾ₑ a b))
                (λ b → Is-just (unit≾ₑ b))     (λ b → is-just? (unit≾ₑ b))
                (λ a → Is-just (≾unitₑ a))     (λ a → is-just? (≾unitₑ a))
                (λ b → Is-just (reachₑ? (ac ⊤ₑ) b)) (λ b → is-just? (reachₑ? (ac ⊤ₑ) b))
                (Is-just ·ₑ-comm?) (is-just? ·ₑ-comm?)
  open Pₑ using (Step; match; skipʳ; skipˡ; absorb; mergeʳ; mergeˡ; pick; absorbAt)

  -- Each step is one use of `monoₑ` on products read with a trailing unit

  stepₑ : ∀ {as bs as' bs'} → Step as bs as' bs'
        → Q ⊩ ⟦ as' ⟧ᵉˢ ≾̂ₑ ⟦ bs' ⟧ᵉˢ → Q ⊩ ⟦ as ⟧ᵉˢ ≾̂ₑ ⟦ bs ⟧ᵉˢ
  stepₑ (match p)  q = monoₑ (to-witness p) q
  stepₑ (skipʳ p)  q = transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-identityˡ)) (monoₑ (to-witness p) q)
  stepₑ (skipˡ p)  q = transₑ (monoₑ (to-witness p) q) (eqₑ ≡̂ₑ-identityˡ)
  stepₑ (absorb p) q =
    transₑ (monoₑ ⊩≾̂ₑ-refl q)
           (transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-assoc)) (monoₑ (transₑ (edgeₑ-sound top) (to-witness p)) ⊩≾̂ₑ-refl))
  stepₑ (mergeʳ {a = ac c} {bs = bs} refl p) q =
    transₑ q (transₑ (eqₑ (≡̂ₑ-trans (consₑ-≡ (ac c) bs)
                                    (≡̂ₑ-cong ≡̂ₑ-refl (≡̂ₑ-sym ≡̂ₑ-identityˡ))))
                     (monoₑ ⊩≾̂ₑ-refl (monoₑ (to-witness p) ⊩≾̂ₑ-refl)))
  stepₑ (mergeˡ {a = ac c} {as = as} refl p) q =
    transₑ (monoₑ ⊩≾̂ₑ-refl (monoₑ (to-witness p) ⊩≾̂ₑ-refl))
           (transₑ (eqₑ (≡̂ₑ-trans (≡̂ₑ-cong ≡̂ₑ-refl ≡̂ₑ-identityˡ)
                                  (≡̂ₑ-sym (consₑ-≡ (ac c) as))))
                   q)
  stepₑ (pick c p) q =
    transₑ (monoₑ (to-witness (lookup-result p)) q) (eqₑ (≡̂ₑ-sym (Commuteₑ.remove-≡ c p)))
  stepₑ (absorbAt c p) q =
    transₑ (monoₑ ⊩≾̂ₑ-refl q)
           (transₑ (eqₑ (≡̂ₑ-trans (≡̂ₑ-cong ≡̂ₑ-refl (Commuteₑ.remove-≡ c p)) (≡̂ₑ-sym ≡̂ₑ-assoc)))
                   (transₑ (monoₑ (transₑ (edgeₑ-sound top) (to-witness (lookup-result p))) ⊩≾̂ₑ-refl)
                           (eqₑ (≡̂ₑ-sym (Commuteₑ.remove-≡ c p)))))
  stepₑ (mergeʳ {a = av _} () _) _
  stepₑ (mergeˡ {a = av _} () _) _

  open Pₑ.Sound (λ as bs → Q ⊩ ⟦ as ⟧ᵉˢ ≾̂ₑ ⟦ bs ⟧ᵉˢ) ⊩≾̂ₑ-refl stepₑ using (prodˢ≾)

  prod≾ₑ : (as bs : List (EAtom Θ))
         → Maybe (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ ⟦ bs ⟧ᵉᵖ)
  prod≾ₑ as bs with prodˢ≾ as bs
  ... | just p  = just (transₑ (eqₑ (≡̂ₑ-sym (⟦⟧ᵉᵖ-≡ as)))
                               (transₑ p (eqₑ (⟦⟧ᵉᵖ-≡ bs))))
  ... | nothing = nothing

  -- One alternative below a sum: below one of its alternatives

  altSum≾ₑ : (as : List (EAtom Θ))
           → (t : Alts (List (EAtom Θ)))
           → Maybe (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ ⟦ t ⟧ᵉᵖ⁺)
  altSum≾ₑ as (alt P) = prod≾ₑ as P
  altSum≾ₑ as (P ∷⁺ t) with prod≾ₑ as P
  ... | just p  = just (transₑ p ⊔-ubˡₑ)
  ... | nothing with altSum≾ₑ as t
  ...   | just q  = just (transₑ q ⊔-ubʳₑ)
  ...   | nothing = nothing

  -- Every alternative of the left side below the right side

  sum≾ₑ : (s t : Alts (List (EAtom Θ)))
        → Maybe (Q ⊩ ⟦ s ⟧ᵉᵖ⁺ ≾̂ₑ ⟦ t ⟧ᵉᵖ⁺)
  sum≾ₑ (alt P)  t = altSum≾ₑ P t
  sum≾ₑ (P ∷⁺ s) t with altSum≾ₑ P t | sum≾ₑ s t
  ... | just p | just q = just (⊔-lubₑ p q)
  ... | _      | _      = nothing

-- Each group of the right side varying in one slot, folded into one
-- alternative above its members

foldₑ-≡ᵖ : ∀ {Θ} → (ε : EExp Θ) → ε ≡̂ₑ ⟦ foldSumₑ (nrmₑ ε) ⟧ᵉᵖ⁺
foldₑ-≡ᵖ ε =
  ≡̂ₑ-trans (nrmₑ-≡ ε)
  (≡̂ₑ-trans (≡̂ₑ-sym (foldSumₑ-≡ (nrmₑ ε))) (⟦⟧ᵉᵖ⁺-≡ (foldSumₑ (nrmₑ ε))))

-- The embedding along the chains of a list of edges between atoms

embedₑ : ∀ {Θ} {Q : Hyps Θ} → List (EEdge Q) → (ε ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
embedₑ es ε ε' with Searchₑ.sum≾ₑ es (tableₑ es) (nrmₑ ε) (foldSumₑ (nrmₑ ε'))
... | just p  = just (transₑ (eqₑ (nrmₑ-≡ᵖ ε)) (transₑ p (eqₑ (≡̂ₑ-sym (foldₑ-≡ᵖ ε')))))
... | nothing = nothing

deriveₑ : ∀ {Θ} → (Q : Hyps Θ) → (ε ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
deriveₑ Q = embedₑ (edgesₑ Q)

------------------------------------------------------------------------
-- Resource grades: the same, with the image `∣ x ∣` of an effect variable as
-- a third atom, above the unit when either sort's unit is least (`∣ u ∣ = u`)

module Searchᵣ {Θ} {Q : Hyps Θ} (es : List (REdge Q))
               (t : Chains.Table (λ a b → Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
                                 ⊩≾̂ᵣ-refl transᵣ linkᵣ? _≟ᵃᵣ_ es) where

  reachᵣ? : (a b : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  reachᵣ? = Chains.reach? _ ⊩≾̂ᵣ-refl transᵣ linkᵣ? _≟ᵃᵣ_ es t

  ceilᵣ : ∀ {ρ : RExp Θ} → (b : RAtom Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  ceilᵣ b with reachᵣ? (rc ⊤ᵣ) b
  ... | just p  = just (transᵣ (edgeᵣ-sound top) p)
  ... | nothing = nothing

  atom≾ᵣ : (a b : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  atom≾ᵣ a b = linkᵣ? a b <∣> ceilᵣ b <∣> reachᵣ? a b

  minᵐ : (b : RAtom Θ) → Maybe (Q ⊩ ûᵣ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  minᵐ (rm i) with Is-just? uₑ-least?
  ... | just q  = just (aboveᵣ-sound (image q))
  ... | nothing = nothing
  minᵐ _ = nothing

  unit≾ᵣ : (b : RAtom Θ) → Maybe (Q ⊩ ûᵣ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  unit≾ᵣ b = min≾ᵣ (Is-just? uᵣ-least?) <∣> minᵐ b <∣> atom≾ᵣ (rc uᵣ) b

  ≾unitᵣ : (a : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ûᵣ)
  ≾unitᵣ a = atom≾ᵣ a (rc uᵣ)

  -- The product comparison, its atom comparisons being these

  constʳ? : RAtom Θ → Maybe R
  constʳ? (rc c) = just c
  constʳ? (rv _) = nothing
  constʳ? (rm _) = nothing

  module Pᵣ = Embedding constʳ? (λ c → consᵣ (rc c)) consᵣ-length
                (λ a b → Is-just (atom≾ᵣ a b)) (λ a b → is-just? (atom≾ᵣ a b))
                (λ b → Is-just (unit≾ᵣ b))     (λ b → is-just? (unit≾ᵣ b))
                (λ a → Is-just (≾unitᵣ a))     (λ a → is-just? (≾unitᵣ a))
                (λ b → Is-just (reachᵣ? (rc ⊤ᵣ) b)) (λ b → is-just? (reachᵣ? (rc ⊤ᵣ) b))
                (Is-just ·ᵣ-comm?) (is-just? ·ᵣ-comm?)
  open Pᵣ using (Step; match; skipʳ; skipˡ; absorb; mergeʳ; mergeˡ; pick; absorbAt)

  -- Each step is one use of `monoᵣ` on products read with a trailing unit

  stepᵣ : ∀ {as bs as' bs'} → Step as bs as' bs'
        → Q ⊩ ⟦ as' ⟧ʳˢ ≾̂ᵣ ⟦ bs' ⟧ʳˢ → Q ⊩ ⟦ as ⟧ʳˢ ≾̂ᵣ ⟦ bs ⟧ʳˢ
  stepᵣ (match p)  q = monoᵣ (to-witness p) q
  stepᵣ (skipʳ p)  q = transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityˡ)) (monoᵣ (to-witness p) q)
  stepᵣ (skipˡ p)  q = transᵣ (monoᵣ (to-witness p) q) (eqᵣ ≡̂ᵣ-identityˡ)
  stepᵣ (absorb p) q =
    transᵣ (monoᵣ ⊩≾̂ᵣ-refl q)
           (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-assoc)) (monoᵣ (transᵣ (edgeᵣ-sound top) (to-witness p)) ⊩≾̂ᵣ-refl))
  stepᵣ (mergeʳ {a = rc c} {bs = bs} refl p) q =
    transᵣ q (transᵣ (eqᵣ (≡̂ᵣ-trans (consᵣ-≡ (rc c) bs)
                                    (≡̂ᵣ-cong ≡̂ᵣ-refl (≡̂ᵣ-sym ≡̂ᵣ-identityˡ))))
                     (monoᵣ ⊩≾̂ᵣ-refl (monoᵣ (to-witness p) ⊩≾̂ᵣ-refl)))
  stepᵣ (mergeˡ {a = rc c} {as = as} refl p) q =
    transᵣ (monoᵣ ⊩≾̂ᵣ-refl (monoᵣ (to-witness p) ⊩≾̂ᵣ-refl))
           (transᵣ (eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl ≡̂ᵣ-identityˡ)
                                  (≡̂ᵣ-sym (consᵣ-≡ (rc c) as))))
                   q)
  stepᵣ (pick c p) q =
    transᵣ (monoᵣ (to-witness (lookup-result p)) q) (eqᵣ (≡̂ᵣ-sym (Commuteᵣ.remove-≡ c p)))
  stepᵣ (absorbAt c p) q =
    transᵣ (monoᵣ ⊩≾̂ᵣ-refl q)
           (transᵣ (eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl (Commuteᵣ.remove-≡ c p)) (≡̂ᵣ-sym ≡̂ᵣ-assoc)))
                   (transᵣ (monoᵣ (transᵣ (edgeᵣ-sound top) (to-witness (lookup-result p))) ⊩≾̂ᵣ-refl)
                           (eqᵣ (≡̂ᵣ-sym (Commuteᵣ.remove-≡ c p)))))
  stepᵣ (mergeʳ {a = rv _} () _) _
  stepᵣ (mergeʳ {a = rm _} () _) _
  stepᵣ (mergeˡ {a = rv _} () _) _
  stepᵣ (mergeˡ {a = rm _} () _) _

  open Pᵣ.Sound (λ as bs → Q ⊩ ⟦ as ⟧ʳˢ ≾̂ᵣ ⟦ bs ⟧ʳˢ) ⊩≾̂ᵣ-refl stepᵣ using (prodˢ≾)

  prod≾ᵣ : (as bs : List (RAtom Θ))
         → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ bs ⟧ʳᵖ)
  prod≾ᵣ as bs with prodˢ≾ as bs
  ... | just p  = just (transᵣ (eqᵣ (≡̂ᵣ-sym (⟦⟧ʳᵖ-≡ as)))
                               (transᵣ p (eqᵣ (⟦⟧ʳᵖ-≡ bs))))
  ... | nothing = nothing

  altSum≾ᵣ : (as : List (RAtom Θ))
           → (t : Alts (List (RAtom Θ)))
           → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ t ⟧ʳᵖ⁺)
  altSum≾ᵣ as (alt P) = prod≾ᵣ as P
  altSum≾ᵣ as (P ∷⁺ t) with prod≾ᵣ as P
  ... | just p  = just (transᵣ p ⊔-ubˡᵣ)
  ... | nothing with altSum≾ᵣ as t
  ...   | just q  = just (transᵣ q ⊔-ubʳᵣ)
  ...   | nothing = nothing

  sum≾ᵣ : (s t : Alts (List (RAtom Θ)))
        → Maybe (Q ⊩ ⟦ s ⟧ʳᵖ⁺ ≾̂ᵣ ⟦ t ⟧ʳᵖ⁺)
  sum≾ᵣ (alt P)  t = altSum≾ᵣ P t
  sum≾ᵣ (P ∷⁺ s) t with altSum≾ᵣ P t | sum≾ᵣ s t
  ... | just p | just q = just (⊔-lubᵣ p q)
  ... | _      | _      = nothing

foldᵣ-≡ᵖ : ∀ {Θ} → (ρ : RExp Θ) → ρ ≡̂ᵣ ⟦ foldSumᵣ (nrmᵣ ρ) ⟧ʳᵖ⁺
foldᵣ-≡ᵖ ρ =
  ≡̂ᵣ-trans (nrmᵣ-≡ ρ)
  (≡̂ᵣ-trans (≡̂ᵣ-sym (foldSumᵣ-≡ (nrmᵣ ρ))) (⟦⟧ʳᵖ⁺-≡ (foldSumᵣ (nrmᵣ ρ))))

embedᵣ : ∀ {Θ} {Q : Hyps Θ} → List (REdge Q) → (ρ ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
embedᵣ es ρ ρ' with Searchᵣ.sum≾ᵣ es (tableᵣ es) (nrmᵣ ρ) (foldSumᵣ (nrmᵣ ρ'))
... | just p  = just (transᵣ (eqᵣ (nrmᵣ-≡ᵖ ρ)) (transᵣ p (eqᵣ (≡̂ᵣ-sym (foldᵣ-≡ᵖ ρ')))))
... | nothing = nothing

deriveᵣ : ∀ {Θ} → (Q : Hyps Θ) → (ρ ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
deriveᵣ Q = embedᵣ (edgesᵣ Q)

------------------------------------------------------------------------
-- The strength `full`: the whole graph
--
-- Factor edges start from a product whose co-factors are above the unit; the
-- variables above the unit are found by Kleene iteration. An ordering is
-- decided along chains between atoms (`atomEdgesₑ`), or from a vertex along a
-- chain to one embedding below the right side (`alongₑ`).

-- Each element of a list with its membership

withMem : ∀ {X : Set} → (l : List X) → List (Σ[ x ∈ X ] x ∈ l)
withMem []      = []
withMem (x ∷ l) = (x , here refl) ∷ map (λ { (y , m) → y , there m }) (withMem l)

-- The first element for each key, keys compared by the given test

firsts : ∀ {X K : Set} {_≅_ : K → K → Set} → Decidable _≅_ → (X → K) → List K → List X
       → List X
firsts _≟_ key seen []      = []
firsts _≟_ key seen (x ∷ l) with any (λ k → does (key x ≟ k)) seen
... | true  = firsts _≟_ key seen l
... | false = x ∷ firsts _≟_ key (key x ∷ seen) l

-- A product of constants

prodₑ : List E → E
prodₑ []       = uₑ
prodₑ (c ∷ cs) = c ·ₑ prodₑ cs

prodₑ-≡ : ∀ {Θ} → (cs : List E) → econst {Θ} (prodₑ cs) ≡̂ₑ ⟦ map ac cs ⟧ᵉˢ
prodₑ-≡ []       = ≡̂ₑ-refl
prodₑ-≡ (c ∷ cs) = ≡̂ₑ-trans (≡̂ₑ-sym ≡̂ₑ-const-·) (≡̂ₑ-cong ≡̂ₑ-refl (prodₑ-≡ cs))

prodᵣ : List R → R
prodᵣ []       = uᵣ
prodᵣ (c ∷ cs) = c ·ᵣ prodᵣ cs

prodᵣ-≡ : ∀ {Θ} → (cs : List R) → rconst {Θ} (prodᵣ cs) ≡̂ᵣ ⟦ map rc cs ⟧ʳˢ
prodᵣ-≡ []       = ≡̂ᵣ-refl
prodᵣ-≡ (c ∷ cs) = ≡̂ᵣ-trans (≡̂ᵣ-sym ≡̂ᵣ-const-·) (≡̂ᵣ-cong ≡̂ᵣ-refl (prodᵣ-≡ cs))

------------------------------------------------------------------------
-- Effect grades

GEdgeₑ : ∀ {Θ} → Hyps Θ → Set
GEdgeₑ {Θ} Q = Σ[ ε ∈ EExp Θ ] Σ[ ε' ∈ EExp Θ ] Edgeₑ Q ε ε'

AChainₑ : ∀ {Θ} → Hyps Θ → Set
AChainₑ {Θ} Q = Σ[ a ∈ EAtom Θ ] Σ[ b ∈ EAtom Θ ] Star (Edgeₑ Q) ⟦ a ⟧ᵉᵃ ⟦ b ⟧ᵉᵃ

-- The variables found above the unit

Uₑ : ∀ {Θ} → Hyps Θ → Set
Uₑ {Θ} Q = List (Σ[ i ∈ EVar Θ ] Aboveₑ Q (av i))

lookupₑ : ∀ {Θ} {Q : Hyps Θ} → Uₑ Q → (i : EVar Θ) → Maybe (Aboveₑ Q (av i))
lookupₑ []            i = nothing
lookupₑ ((j , a) ∷ U) i with j ≟ᶠ i
... | yes refl = just a
... | no _     = lookupₑ U i

atomAboveₑ : ∀ {Θ} {Q : Hyps Θ} → Uₑ Q → (a : EAtom Θ) → Maybe (Aboveₑ Q a)
atomAboveₑ U (ac c) with uₑ ≾ₑ? c
... | yes p = just (const p)
... | no _  = nothing
atomAboveₑ U (av i) = lookupₑ U i

above?ₑ : ∀ {Θ} {Q : Hyps Θ} → Uₑ Q → (a : EAtom Θ) → Maybe (Aboveₑ Q a)
above?ₑ U a with Is-just? uₑ-least?
... | just q  = just (least q)
... | nothing = atomAboveₑ U a

-- The sources of factor edges: one atom of a product, the others above the
-- unit; and its constants, its variables above the unit

allAboveₑ : ∀ {Θ} {Q : Hyps Θ} → Uₑ Q → (as : List (EAtom Θ)) → Maybe (Keepₑ Q as [])
allAboveₑ U []       = just stop
allAboveₑ U (a ∷ as) with above?ₑ U a | allAboveₑ U as
... | just b | just k = just (skip b k)
... | _      | _      = nothing

hereₑ : ∀ {Θ} {Q : Hyps Θ} {as} → (a : EAtom Θ) → Maybe (Keepₑ Q as [])
      → List (Σ[ b ∈ EAtom Θ ] Keepₑ Q (a ∷ as) (b ∷ []))
hereₑ a (just k) = (a , keep k) ∷ []
hereₑ a nothing  = []

thereₑ : ∀ {Θ} {Q : Hyps Θ} {a as} → Maybe (Aboveₑ Q a)
       → List (Σ[ b ∈ EAtom Θ ] Keepₑ Q as (b ∷ []))
       → List (Σ[ b ∈ EAtom Θ ] Keepₑ Q (a ∷ as) (b ∷ []))
thereₑ (just x) l = map (λ { (b , k) → b , skip x k }) l
thereₑ nothing  l = []

singlesₑ : ∀ {Θ} {Q : Hyps Θ} → Uₑ Q → (as : List (EAtom Θ))
         → List (Σ[ b ∈ EAtom Θ ] Keepₑ Q as (b ∷ []))
singlesₑ U []       = []
singlesₑ U (a ∷ as) = hereₑ a (allAboveₑ U as) ++ thereₑ (above?ₑ U a) (singlesₑ U as)

constsₑ : ∀ {Θ} {Q : Hyps Θ} → Uₑ Q → (as : List (EAtom Θ))
        → Maybe (Σ[ cs ∈ List E ] Keepₑ Q as (map ac cs))
constsₑ U []           = just ([] , stop)
constsₑ U (ac c ∷ as) with constsₑ U as
... | just (cs , k) = just (c ∷ cs , keep k)
... | nothing       = nothing
constsₑ U (av i ∷ as) with above?ₑ U (av i) | constsₑ U as
... | just x | just (cs , k) = just (cs , skip x k)
... | _      | _             = nothing

productₑ : ∀ {Θ} {Q : Hyps Θ} {ε as} → ε ∈ sidesₑ Q → nrmₑ ε ≡ alt as
         → Maybe (Σ[ cs ∈ List E ] Keepₑ Q as (map ac cs)) → List (GEdgeₑ Q)
productₑ {ε = ε} m eq (just (c ∷ d ∷ cs , k)) =
  (econst (prodₑ (c ∷ d ∷ cs)) , ε , factor m eq k (prodₑ-≡ (c ∷ d ∷ cs))) ∷ []
productₑ m eq _ = []

-- The factor edges into one side

factorsOfₑ : ∀ {Θ} {Q : Hyps Θ} → Uₑ Q → (ε : EExp Θ) → ε ∈ sidesₑ Q → List (GEdgeₑ Q)
factorsOfₑ U ε m with nrmₑ ε in eq
... | alt (a ∷ b ∷ as) =
      map (λ { (c , k) → ⟦ c ⟧ᵉᵃ , ε , factor m eq k (≡̂ₑ-sym ≡̂ₑ-identityʳ) })
          (singlesₑ U (a ∷ b ∷ as))
      ++ productₑ m eq (constsₑ U (a ∷ b ∷ as))
... | _ = []

-- The graph, with the variables `U` above the unit

graphₑ : ∀ {Θ} → (Q : Hyps Θ) → Uₑ Q → List (GEdgeₑ Q)
graphₑ Q U =
  map (λ { ((ε , ε') , m) → ε , ε' , hyp m }) (withMem (ordₑ Q))
  ++ concatMap (λ { (ε , m) → factorsOfₑ U ε m })
               (firsts _≟ᵉ_ (λ { (ε , _) → ε }) [] (withMem (sidesₑ Q)))

-- What an expression reaches along a list of edges

linkˣₑ : ∀ {Θ} {Q : Hyps Θ} → (ε ε' : EExp Θ) → Maybe (Star (Edgeₑ Q) ε ε')
linkˣₑ ε ε' with ε ≟ᵉ ε'
... | yes p = just (same p ◅◅ ◅-nil)
... | no _     = nothing

reachesₑ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeₑ Q) → (ε : EExp Θ)
         → List (Σ[ ε' ∈ EExp Θ ] Star (Edgeₑ Q) ε ε')
reachesₑ es ε =
  Chains.sat _ ◅-nil _⋆_ linkˣₑ _≟ᵉ_ (map (λ { (x , y , e) → x , y , e ◅◅ ◅-nil }) es)
             (length es) ((ε , ◅-nil) ∷ [])

-- The variables reached from a variable-free source above the unit

addVarsₑ : ∀ {Θ} {Q : Hyps Θ} {ε c} → valᵉ? ε ≡ just c → uₑ ≾ₑ c
         → List (Σ[ ε' ∈ EExp Θ ] Star (Edgeₑ Q) ε ε') → Uₑ Q → Uₑ Q
addVarsₑ q p []                   U = U
addVarsₑ q p ((evar i , ch) ∷ l) U with lookupₑ U i
... | just _  = addVarsₑ q p l U
... | nothing = addVarsₑ q p l ((i , reached q p ch) ∷ U)
addVarsₑ q p (_ ∷ l)             U = addVarsₑ q p l U

fromₑ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeₑ Q) → EExp Θ → Uₑ Q → Uₑ Q
fromₑ es ε U with valᵉ? ε in q
... | nothing = U
... | just c with uₑ ≾ₑ? c
...   | yes p = addVarsₑ q p (reachesₑ es ε) U
...   | no _  = U

reachedₑ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeₑ Q) → Uₑ Q
reachedₑ es = go (firsts _≟ᵉ_ (λ ε → ε) [] (map (λ { (ε , _ , _) → ε }) es)) []
  where
    go : List (EExp _) → Uₑ _ → Uₑ _
    go []       U = U
    go (ε ∷ εs) U = go εs (fromₑ es ε U)

iterateₑ : ∀ {Θ} → (Q : Hyps Θ) → ℕ → Uₑ Q → Uₑ Q
iterateₑ Q zero    U = U
iterateₑ Q (suc n) U with reachedₑ (graphₑ Q U)
... | U' with length U <ᵇ length U'
...   | true  = iterateₑ Q n U'
...   | false = U

aboveₑ : ∀ {Θ} → (Q : Hyps Θ) → Uₑ Q
aboveₑ {Θ} Q with Is-just? uₑ-least?
... | just _  = []
... | nothing = iterateₑ Q (suc (nE Θ)) []

fullGraphₑ : ∀ {Θ} → (Q : Hyps Θ) → List (GEdgeₑ Q)
fullGraphₑ Q = graphₑ Q (aboveₑ Q)

-- The chains between atoms

directₑ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeₑ Q) → List (AChainₑ Q)
directₑ []              = []
directₑ ((x , y , e) ∷ l) with atomᵉ? x | atomᵉ? y
... | just (a , refl) | just (b , refl) = (a , b , e ◅◅ ◅-nil) ∷ directₑ l
... | _               | _               = directₑ l

compoundₑ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeₑ Q) → List (GEdgeₑ Q)
compoundₑ []              = []
compoundₑ ((x , y , e) ∷ l) with atomᵉ? x
... | just _  = compoundₑ l
... | nothing = (x , y , e) ∷ compoundₑ l

atomsOfₑ : ∀ {Θ} {Q : Hyps Θ} {w} → (a : EAtom Θ) → Edgeₑ Q ⟦ a ⟧ᵉᵃ w
         → List (Σ[ ε ∈ EExp Θ ] Star (Edgeₑ Q) w ε) → List (AChainₑ Q)
atomsOfₑ a e []             = []
atomsOfₑ a e ((ε , ch) ∷ l) with atomᵉ? ε
... | just (b , refl) = (a , b , e ◅◅ ch) ∷ atomsOfₑ a e l
... | nothing         = atomsOfₑ a e l

throughₑ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeₑ Q) → GEdgeₑ Q → List (AChainₑ Q)
throughₑ cs (x , w , e) with atomᵉ? x | atomᵉ? w
... | just (a , refl) | nothing = atomsOfₑ a e (reachesₑ cs w)
... | _               | _       = []

atomEdgesₑ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeₑ Q) → List (AChainₑ Q)
atomEdgesₑ g = directₑ g ++ concatMap (throughₑ (compoundₑ g)) g

-- Along a chain from the left side to a vertex below the right side

alongₑ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeₑ Q) → List (EEdge Q)
       → (ε ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
alongₑ {Q = Q} g es ε ε' = via (reachesₑ g ε)
  where
    via : List (Σ[ v ∈ EExp _ ] Star (Edgeₑ Q) ε v) → Maybe (Q ⊩ ε ≾̂ₑ ε')
    via []             = nothing
    via ((v , ch) ∷ l) with v ≟ᵉ ε
    ... | yes _ = via l
    ... | no _ with v ≟ᵉ ε'
    ...   | yes p = just (transₑ (chainₑ-sound ch) (eqₑ (≅ᵉ⇒≡̂ p)))
    ...   | no _ with embedₑ es v ε'
    ...     | just p  = just (transₑ (chainₑ-sound ch) p)
    ...     | nothing = via l

fullₑ : ∀ {Θ} → (Q : Hyps Θ) → (ε ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
fullₑ Q ε ε' = embedₑ es ε ε' <∣> alongₑ g es ε ε'
  where
    g  = fullGraphₑ Q
    es = map (λ { (a , b , ch) → a , b , chainₑ-sound ch }) (atomEdgesₑ g)

------------------------------------------------------------------------
-- Resource grades: the same, with the images of effect chains as edges

GEdgeᵣ : ∀ {Θ} → Hyps Θ → Set
GEdgeᵣ {Θ} Q = Σ[ ρ ∈ RExp Θ ] Σ[ ρ' ∈ RExp Θ ] Edgeᵣ Q ρ ρ'

AChainᵣ : ∀ {Θ} → Hyps Θ → Set
AChainᵣ {Θ} Q = Σ[ a ∈ RAtom Θ ] Σ[ b ∈ RAtom Θ ] Star (Edgeᵣ Q) ⟦ a ⟧ʳᵃ ⟦ b ⟧ʳᵃ

Uᵣ : ∀ {Θ} → Hyps Θ → Set
Uᵣ {Θ} Q = List (Σ[ a ∈ RAtom Θ ] Aboveᵣ Q a)

-- Variable atoms, compared by index; `Uᵣ` lists variable atoms only

_≟ᵛᵃᵣ_ : ∀ {Θ} → (a b : RAtom Θ) → Maybe (a ≡ b)
rv i ≟ᵛᵃᵣ rv j with i ≟ᶠ j
... | yes refl = just refl
... | no _     = nothing
rm i ≟ᵛᵃᵣ rm j with i ≟ᶠ j
... | yes refl = just refl
... | no _     = nothing
_    ≟ᵛᵃᵣ _    = nothing

lookupᵣ : ∀ {Θ} {Q : Hyps Θ} → Uᵣ Q → (a : RAtom Θ) → Maybe (Aboveᵣ Q a)
lookupᵣ []            a = nothing
lookupᵣ ((b , x) ∷ U) a with b ≟ᵛᵃᵣ a
... | just refl = just x
... | nothing   = lookupᵣ U a

atomAboveᵣ : ∀ {Θ} {Q : Hyps Θ} → Uᵣ Q → (a : RAtom Θ) → Maybe (Aboveᵣ Q a)
atomAboveᵣ U (rc c) with uᵣ ≾ᵣ? c
... | yes p = just (const p)
... | no _  = nothing
atomAboveᵣ U (rv i) = lookupᵣ U (rv i)
atomAboveᵣ U (rm i) with Is-just? uₑ-least?
... | just q  = just (image q)
... | nothing = lookupᵣ U (rm i)

above?ᵣ : ∀ {Θ} {Q : Hyps Θ} → Uᵣ Q → (a : RAtom Θ) → Maybe (Aboveᵣ Q a)
above?ᵣ U a with Is-just? uᵣ-least?
... | just q  = just (least q)
... | nothing = atomAboveᵣ U a

allAboveᵣ : ∀ {Θ} {Q : Hyps Θ} → Uᵣ Q → (as : List (RAtom Θ)) → Maybe (Keepᵣ Q as [])
allAboveᵣ U []       = just stop
allAboveᵣ U (a ∷ as) with above?ᵣ U a | allAboveᵣ U as
... | just b | just k = just (skip b k)
... | _      | _      = nothing

hereᵣ : ∀ {Θ} {Q : Hyps Θ} {as} → (a : RAtom Θ) → Maybe (Keepᵣ Q as [])
      → List (Σ[ b ∈ RAtom Θ ] Keepᵣ Q (a ∷ as) (b ∷ []))
hereᵣ a (just k) = (a , keep k) ∷ []
hereᵣ a nothing  = []

thereᵣ : ∀ {Θ} {Q : Hyps Θ} {a as} → Maybe (Aboveᵣ Q a)
       → List (Σ[ b ∈ RAtom Θ ] Keepᵣ Q as (b ∷ []))
       → List (Σ[ b ∈ RAtom Θ ] Keepᵣ Q (a ∷ as) (b ∷ []))
thereᵣ (just x) l = map (λ { (b , k) → b , skip x k }) l
thereᵣ nothing  l = []

singlesᵣ : ∀ {Θ} {Q : Hyps Θ} → Uᵣ Q → (as : List (RAtom Θ))
         → List (Σ[ b ∈ RAtom Θ ] Keepᵣ Q as (b ∷ []))
singlesᵣ U []       = []
singlesᵣ U (a ∷ as) = hereᵣ a (allAboveᵣ U as) ++ thereᵣ (above?ᵣ U a) (singlesᵣ U as)

constsᵣ : ∀ {Θ} {Q : Hyps Θ} → Uᵣ Q → (as : List (RAtom Θ))
        → Maybe (Σ[ cs ∈ List R ] Keepᵣ Q as (map rc cs))
constsᵣ U []           = just ([] , stop)
constsᵣ U (rc c ∷ as) with constsᵣ U as
... | just (cs , k) = just (c ∷ cs , keep k)
... | nothing       = nothing
constsᵣ U (rv i ∷ as) with above?ᵣ U (rv i) | constsᵣ U as
... | just x | just (cs , k) = just (cs , skip x k)
... | _      | _             = nothing
constsᵣ U (rm i ∷ as) with above?ᵣ U (rm i) | constsᵣ U as
... | just x | just (cs , k) = just (cs , skip x k)
... | _      | _             = nothing

productᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ as} → ρ ∈ sidesᵣ Q → nrmᵣ ρ ≡ alt as
         → Maybe (Σ[ cs ∈ List R ] Keepᵣ Q as (map rc cs)) → List (GEdgeᵣ Q)
productᵣ {ρ = ρ} m eq (just (c ∷ d ∷ cs , k)) =
  (rconst (prodᵣ (c ∷ d ∷ cs)) , ρ , factor m eq k (prodᵣ-≡ (c ∷ d ∷ cs))) ∷ []
productᵣ m eq _ = []

factorsOfᵣ : ∀ {Θ} {Q : Hyps Θ} → Uᵣ Q → (ρ : RExp Θ) → ρ ∈ sidesᵣ Q → List (GEdgeᵣ Q)
factorsOfᵣ U ρ m with nrmᵣ ρ in eq
... | alt (a ∷ b ∷ as) =
      map (λ { (c , k) → ⟦ c ⟧ʳᵃ , ρ , factor m eq k (≡̂ᵣ-sym ≡̂ᵣ-identityʳ) })
          (singlesᵣ U (a ∷ b ∷ as))
      ++ productᵣ m eq (constsᵣ U (a ∷ b ∷ as))
... | _ = []

graphᵣ : ∀ {Θ} → (Q : Hyps Θ) → Uᵣ Q → List (GEdgeᵣ Q)
graphᵣ Q U =
  map (λ { ((ρ , ρ') , m) → ρ , ρ' , hyp m }) (withMem (ordᵣ Q))
  ++ map (λ { (a , b , ch) → ⟦ ∣ a ∣ᵃ ⟧ʳᵃ , ⟦ ∣ b ∣ᵃ ⟧ʳᵃ , img ch }) (atomEdgesₑ (fullGraphₑ Q))
  ++ concatMap (λ { (ρ , m) → factorsOfᵣ U ρ m })
               (firsts _≟ʳ_ (λ { (ρ , _) → ρ }) [] (withMem (sidesᵣ Q)))

linkˣᵣ : ∀ {Θ} {Q : Hyps Θ} → (ρ ρ' : RExp Θ) → Maybe (Star (Edgeᵣ Q) ρ ρ')
linkˣᵣ ρ ρ' with ρ ≟ʳ ρ'
... | yes p = just (same p ◅◅ ◅-nil)
... | no _     = nothing

reachesᵣ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeᵣ Q) → (ρ : RExp Θ)
         → List (Σ[ ρ' ∈ RExp Θ ] Star (Edgeᵣ Q) ρ ρ')
reachesᵣ es ρ =
  Chains.sat _ ◅-nil _⋆_ linkˣᵣ _≟ʳ_ (map (λ { (x , y , e) → x , y , e ◅◅ ◅-nil }) es)
             (length es) ((ρ , ◅-nil) ∷ [])

addVarᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ c} → valʳ? ρ ≡ just c → uᵣ ≾ᵣ c
        → (a : RAtom Θ) → Star (Edgeᵣ Q) ρ ⟦ a ⟧ʳᵃ → Uᵣ Q → Uᵣ Q
addVarᵣ q p a ch U with lookupᵣ U a
... | just _  = U
... | nothing = (a , reached q p ch) ∷ U

addVarsᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ c} → valʳ? ρ ≡ just c → uᵣ ≾ᵣ c
         → List (Σ[ ρ' ∈ RExp Θ ] Star (Edgeᵣ Q) ρ ρ') → Uᵣ Q → Uᵣ Q
addVarsᵣ q p []                        U = U
addVarsᵣ q p ((rvar i , ch) ∷ l)       U = addVarsᵣ q p l (addVarᵣ q p (rv i) ch U)
addVarsᵣ q p ((∣ evar i ∣̂ᵉ , ch) ∷ l) U = addVarsᵣ q p l (addVarᵣ q p (rm i) ch U)
addVarsᵣ q p (_ ∷ l)                   U = addVarsᵣ q p l U

fromᵣ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeᵣ Q) → RExp Θ → Uᵣ Q → Uᵣ Q
fromᵣ es ρ U with valʳ? ρ in q
... | nothing = U
... | just c with uᵣ ≾ᵣ? c
...   | yes p = addVarsᵣ q p (reachesᵣ es ρ) U
...   | no _  = U

reachedᵣ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeᵣ Q) → Uᵣ Q
reachedᵣ es = go (firsts _≟ʳ_ (λ ρ → ρ) [] (map (λ { (ρ , _ , _) → ρ }) es)) []
  where
    go : List (RExp _) → Uᵣ _ → Uᵣ _
    go []       U = U
    go (ρ ∷ ρs) U = go ρs (fromᵣ es ρ U)

iterateᵣ : ∀ {Θ} → (Q : Hyps Θ) → ℕ → Uᵣ Q → Uᵣ Q
iterateᵣ Q zero    U = U
iterateᵣ Q (suc n) U with reachedᵣ (graphᵣ Q U)
... | U' with length U <ᵇ length U'
...   | true  = iterateᵣ Q n U'
...   | false = U

aboveᵣ : ∀ {Θ} → (Q : Hyps Θ) → Uᵣ Q
aboveᵣ {Θ} Q with Is-just? uᵣ-least?
... | just _  = []
... | nothing = iterateᵣ Q (suc (nR Θ + nE Θ)) []

fullGraphᵣ : ∀ {Θ} → (Q : Hyps Θ) → List (GEdgeᵣ Q)
fullGraphᵣ Q = graphᵣ Q (aboveᵣ Q)

directᵣ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeᵣ Q) → List (AChainᵣ Q)
directᵣ []              = []
directᵣ ((x , y , e) ∷ l) with atomʳ? x | atomʳ? y
... | just (a , refl) | just (b , refl) = (a , b , e ◅◅ ◅-nil) ∷ directᵣ l
... | _               | _               = directᵣ l

compoundᵣ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeᵣ Q) → List (GEdgeᵣ Q)
compoundᵣ []              = []
compoundᵣ ((x , y , e) ∷ l) with atomʳ? x
... | just _  = compoundᵣ l
... | nothing = (x , y , e) ∷ compoundᵣ l

atomsOfᵣ : ∀ {Θ} {Q : Hyps Θ} {w} → (a : RAtom Θ) → Edgeᵣ Q ⟦ a ⟧ʳᵃ w
         → List (Σ[ ρ ∈ RExp Θ ] Star (Edgeᵣ Q) w ρ) → List (AChainᵣ Q)
atomsOfᵣ a e []             = []
atomsOfᵣ a e ((ρ , ch) ∷ l) with atomʳ? ρ
... | just (b , refl) = (a , b , e ◅◅ ch) ∷ atomsOfᵣ a e l
... | nothing         = atomsOfᵣ a e l

throughᵣ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeᵣ Q) → GEdgeᵣ Q → List (AChainᵣ Q)
throughᵣ cs (x , w , e) with atomʳ? x | atomʳ? w
... | just (a , refl) | nothing = atomsOfᵣ a e (reachesᵣ cs w)
... | _               | _       = []

atomEdgesᵣ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeᵣ Q) → List (AChainᵣ Q)
atomEdgesᵣ g = directᵣ g ++ concatMap (throughᵣ (compoundᵣ g)) g

alongᵣ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeᵣ Q) → List (REdge Q)
       → (ρ ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
alongᵣ {Q = Q} g es ρ ρ' = via (reachesᵣ g ρ)
  where
    via : List (Σ[ v ∈ RExp _ ] Star (Edgeᵣ Q) ρ v) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
    via []             = nothing
    via ((v , ch) ∷ l) with v ≟ʳ ρ
    ... | yes _ = via l
    ... | no _ with v ≟ʳ ρ'
    ...   | yes p = just (transᵣ (chainᵣ-sound ch) (eqᵣ (≅ʳ⇒≡̂ p)))
    ...   | no _ with embedᵣ es v ρ'
    ...     | just p  = just (transᵣ (chainᵣ-sound ch) p)
    ...     | nothing = via l

fullᵣ : ∀ {Θ} → (Q : Hyps Θ) → (ρ ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
fullᵣ Q ρ ρ' = embedᵣ es ρ ρ' <∣> alongᵣ g es ρ ρ'
  where
    g  = fullGraphᵣ Q
    es = map (λ { (a , b , ch) → a , b , chainᵣ-sound ch }) (atomEdgesᵣ g)


------------------------------------------------------------------------
-- The strength `closed`: both sides variable-free, compared by the grade's
-- order. One that holds is entailed by every set; one that fails holds at no
-- closed instance.

-- The two outcomes of `closed`

data Closedₑ {Θ : Scope} (ε ε' : EExp Θ) : Set where
  holdsₑ : (∀ {Q : Hyps Θ} → Q ⊩ ε ≾̂ₑ ε') → Closedₑ ε ε'
  failsₑ : ((δ : Subst Θ ∅ˢ) → ¬ (∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ)) → Closedₑ ε ε'

data Closedᵣ {Θ : Scope} (ρ ρ' : RExp Θ) : Set where
  holdsᵣ : (∀ {Q : Hyps Θ} → Q ⊩ ρ ≾̂ᵣ ρ') → Closedᵣ ρ ρ'
  failsᵣ : ((δ : Subst Θ ∅ˢ) → ¬ (∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ)) → Closedᵣ ρ ρ'

closedₑ? : ∀ {Θ} → (ε ε' : EExp Θ) → Maybe (Closedₑ ε ε')
closedₑ? ε ε' with valᵉ? ε in q | valᵉ? ε' in q'
... | just c  | just c' with c ≾ₑ? c'
...   | yes p = just (holdsₑ (transₑ (eqₑ (convᵉ ε q))
                                     (transₑ (edgeₑ-sound (cst p)) (eqₑ (≡̂ₑ-sym (convᵉ ε' q'))))))
...   | no n  = just (failsₑ (λ δ d → n (closed-≾ₑ (convᵉ ε q) (convᵉ ε' q') δ d)))
closedₑ? ε ε' | just _  | nothing = nothing
closedₑ? ε ε' | nothing | _       = nothing

closedᵣ? : ∀ {Θ} → (ρ ρ' : RExp Θ) → Maybe (Closedᵣ ρ ρ')
closedᵣ? ρ ρ' with valʳ? ρ in q | valʳ? ρ' in q'
... | just c  | just c' with c ≾ᵣ? c'
...   | yes p = just (holdsᵣ (transᵣ (eqᵣ (convʳ ρ q))
                                     (transᵣ (edgeᵣ-sound (cst p)) (eqᵣ (≡̂ᵣ-sym (convʳ ρ' q'))))))
...   | no n  = just (failsᵣ (λ δ d → n (closed-≾ᵣ (convʳ ρ q) (convʳ ρ' q') δ d)))
closedᵣ? ρ ρ' | just _  | nothing = nothing
closedᵣ? ρ ρ' | nothing | _       = nothing

------------------------------------------------------------------------
-- Decisions at a strength

data Strength : Set where
  closed derive atomic full : Strength

-- Membership of an ordering in a list, up to the sameness of its sides

Memʳ : ∀ {Θ} → RExp Θ × RExp Θ → List (RExp Θ × RExp Θ) → Set
Memʳ {Θ} (ρ , ρ') l =
  Σ[ ρ₀ ∈ RExp Θ ] Σ[ ρ₀' ∈ RExp Θ ] (ρ₀ , ρ₀') ∈ l × ρ ≅ʳ ρ₀ × ρ₀' ≅ʳ ρ'

memʳ? : ∀ {Θ} → (p : RExp Θ × RExp Θ) → (l : List (RExp Θ × RExp Θ)) → Maybe (Memʳ p l)
memʳ? p []              = nothing
memʳ? (ρ , ρ') ((ρ₀ , ρ₀') ∷ l) with ρ ≟ʳ ρ₀ | ρ₀' ≟ʳ ρ'
... | yes e | yes e' = just (ρ₀ , ρ₀' , here refl , e , e')
... | _     | _      with memʳ? (ρ , ρ') l
...   | just (a , b , m , e , e') = just (a , b , there m , e , e')
...   | nothing                   = nothing

memʳ-⊩ : ∀ {Θ} {Q : Hyps Θ} {l ρ ρ'} → (∀ {a b} → (a , b) ∈ l → Q ⊩ a ≾̂ᵣ b)
       → Memʳ (ρ , ρ') l → Q ⊩ ρ ≾̂ᵣ ρ'
memʳ-⊩ h (_ , _ , m , e , e') = transᵣ (eqᵣ (≅ʳ⇒≡̂ e)) (transᵣ (h m) (eqᵣ (≅ʳ⇒≡̂ e')))

Memᵉ : ∀ {Θ} → EExp Θ × EExp Θ → List (EExp Θ × EExp Θ) → Set
Memᵉ {Θ} (ε , ε') l =
  Σ[ ε₀ ∈ EExp Θ ] Σ[ ε₀' ∈ EExp Θ ] (ε₀ , ε₀') ∈ l × ε ≅ᵉ ε₀ × ε₀' ≅ᵉ ε'

memᵉ? : ∀ {Θ} → (p : EExp Θ × EExp Θ) → (l : List (EExp Θ × EExp Θ)) → Maybe (Memᵉ p l)
memᵉ? p []              = nothing
memᵉ? (ε , ε') ((ε₀ , ε₀') ∷ l) with ε ≟ᵉ ε₀ | ε₀' ≟ᵉ ε'
... | yes e | yes e' = just (ε₀ , ε₀' , here refl , e , e')
... | _     | _      with memᵉ? (ε , ε') l
...   | just (a , b , m , e , e') = just (a , b , there m , e , e')
...   | nothing                   = nothing

memᵉ-⊩ : ∀ {Θ} {Q : Hyps Θ} {l ε ε'} → (∀ {a b} → (a , b) ∈ l → Q ⊩ a ≾̂ₑ b)
       → Memᵉ (ε , ε') l → Q ⊩ ε ≾̂ₑ ε'
memᵉ-⊩ h (_ , _ , m , e , e') = transₑ (eqₑ (≅ᵉ⇒≡̂ e)) (transₑ (h m) (eqₑ (≅ᵉ⇒≡̂ e')))

decideₑ : ∀ {Θ} → Strength → (Q : Hyps Θ) → (ε ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
decideₑ closed Q ε ε' with closedₑ? ε ε'
... | just (holdsₑ p) = just p
... | _               = nothing
decideₑ derive Q ε ε' = deriveₑ Q ε ε'
decideₑ atomic Q ε ε' with memᵉ? (ε , ε') (ordₑ Q)
... | just m  = just (memᵉ-⊩ hypₑ m)
... | nothing = deriveₑ Q ε ε'
decideₑ full Q ε ε' with closedₑ? ε ε'
... | just (holdsₑ p) = just p
... | _               = fullₑ Q ε ε'

decideᵣ : ∀ {Θ} → Strength → (Q : Hyps Θ) → (ρ ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
decideᵣ closed Q ρ ρ' with closedᵣ? ρ ρ'
... | just (holdsᵣ p) = just p
... | _               = nothing
decideᵣ derive Q ρ ρ' = deriveᵣ Q ρ ρ'
decideᵣ atomic Q ρ ρ' with memʳ? (ρ , ρ') (ordᵣ Q)
... | just m  = just (memʳ-⊩ hypᵣ m)
... | nothing = deriveᵣ Q ρ ρ'
decideᵣ full Q ρ ρ' with closedᵣ? ρ ρ'
... | just (holdsᵣ p) = just p
... | _               = fullᵣ Q ρ ρ'

------------------------------------------------------------------------
-- Refutation of `ρ ≾ u` by the zero-product law
--
-- A constant atom not below the unit refutes each alternative it occurs in,
-- and one refuted alternative the sum. It needs a satisfiable set (`hyp-derives`).

-- No closed instance brings the expression below the unit

Refutedᵤ : ∀ {Ω} → RExp Ω → Set
Refutedᵤ {Ω} ρ = (δ : Subst Ω ∅ˢ) → ¬ (valʳ (ρ [ δ ]ʳ) ≾ᵣ uᵣ)

-- A product below the unit has both halves below the unit, so a
-- refutation of either half refutes the product

head-refutes : ∀ {Ω} → (a : RAtom Ω) → (as : List (RAtom Ω))
             → Refutedᵤ ⟦ a ⟧ʳᵃ → Refutedᵤ ⟦ a ∷ as ⟧ʳˢ
head-refutes a as ref δ le = ref δ (≾ᵣ-zero-productˡ le)

tail-refutes : ∀ {Ω} → (a : RAtom Ω) → (as : List (RAtom Ω))
             → Refutedᵤ ⟦ as ⟧ʳˢ → Refutedᵤ ⟦ a ∷ as ⟧ʳˢ
tail-refutes a as ref δ le = ref δ (≾ᵣ-zero-productʳ le)

-- A constant that is not below the unit, and a join one of whose
-- operands is refuted

const-refutes : ∀ {Ω} {c : R} → ¬ (c ≾ᵣ uᵣ) → Refutedᵤ (rconst {Ω} c)
const-refutes ¬p δ le = ¬p le

join-refutesˡ : ∀ {Ω} {ρ ρ' : RExp Ω} → Refutedᵤ ρ → Refutedᵤ (ρ ⊔̂ᵣ ρ')
join-refutesˡ {ρ = ρ} {ρ' = ρ'} ref δ le =
  ref δ (≾ᵣ-trans (⊔ᵣ-ubˡ (valʳ (ρ [ δ ]ʳ)) (valʳ (ρ' [ δ ]ʳ))) le)

join-refutesʳ : ∀ {Ω} {ρ ρ' : RExp Ω} → Refutedᵤ ρ' → Refutedᵤ (ρ ⊔̂ᵣ ρ')
join-refutesʳ {ρ = ρ} {ρ' = ρ'} ref δ le =
  ref δ (≾ᵣ-trans (⊔ᵣ-ubʳ (valʳ (ρ [ δ ]ʳ)) (valʳ (ρ' [ δ ]ʳ))) le)

-- Transported along a convertibility, and so along the certified
-- normalisation

refute-≡̂ᵣ : ∀ {Ω} {ρ ρ' : RExp Ω} → ρ ≡̂ᵣ ρ' → Refutedᵤ ρ' → Refutedᵤ ρ
refute-≡̂ᵣ eq ref δ le = ref δ (≾ᵣ-trans (proj₂ (inst-≡̂ᵣ δ eq)) le)

-- Refutation survives every later instantiation

refute-[]ʳ : ∀ {Ω Ω'} {ρ : RExp Ω} → (σ : Subst Ω Ω')
           → Refutedᵤ ρ → Refutedᵤ (ρ [ σ ]ʳ)
refute-[]ʳ {ρ = ρ} σ ref δ le = ref (σ ⨟ˢ δ) (subst (λ x → valʳ x ≾ᵣ uᵣ) ([⨟]ʳ ρ σ δ) le)

-- A refuted expression is entailed by no satisfiable hypothesis set

refute-⊩ : ∀ {Ω} {ρ : RExp Ω} {Q : Hyps Ω} → Satisfiable Q
         → Refutedᵤ ρ → ¬ (Q ⊩ ρ ≾̂ᵣ ûᵣ)
refute-⊩ (δ , h) ref d = ref δ (inst-≾ᵣ (⊨⇒⊩ᴴ h) d)

-- Satisfiability is needed: a hypothesis may name any ordering

hyp-derives : ∀ {Ω} → (ρ : RExp Ω) → hyps [] [] ((ρ , ûᵣ) ∷ []) [] [] [] ⊩ ρ ≾̂ᵣ ûᵣ
hyp-derives ρ = hypᵣ (here refl)

-- The scan, over the alternatives and their atoms

scan-atom : ∀ {Ω} → (a : RAtom Ω) → Maybe (Refutedᵤ ⟦ a ⟧ʳᵃ)
scan-atom (rv i) = nothing
scan-atom (rm i) = nothing
scan-atom (rc c) with c ≾ᵣ? uᵣ
... | yes _ = nothing
... | no ¬p = just (const-refutes ¬p)

scan-atoms : ∀ {Ω} → (as : List (RAtom Ω)) → Maybe (Refutedᵤ ⟦ as ⟧ʳˢ)
scan-atoms []       = nothing
scan-atoms (a ∷ as) with scan-atom a | scan-atoms as
... | just r  | _      = just (head-refutes a as r)
... | nothing | just r = just (tail-refutes a as r)
... | nothing | nothing = nothing

scan-sum : ∀ {Ω} → (s : Alts (List (RAtom Ω))) → Maybe (Refutedᵤ ⟦ s ⟧ʳˢ⁺)
scan-sum (alt P)  = scan-atoms P
scan-sum (P ∷⁺ t) with scan-atoms P | scan-sum t
... | just r  | _      = just (join-refutesˡ {ρ = ⟦ P ⟧ʳˢ} {ρ' = ⟦ t ⟧ʳˢ⁺} r)
... | nothing | just r = just (join-refutesʳ {ρ = ⟦ P ⟧ʳˢ} {ρ' = ⟦ t ⟧ʳˢ⁺} r)
... | nothing | nothing = nothing

refute≾u : ∀ {Ω} → (ρ : RExp Ω) → Maybe (Refutedᵤ ρ)
refute≾u ρ with scan-sum (nrmᵣ ρ)
... | nothing = nothing
... | just r  = just (refute-≡̂ᵣ (nrmᵣ-≡ ρ) r)

------------------------------------------------------------------------
-- The closed check
--
-- `checkClosed` decides at `closed` the orderings of a set and those between
-- closed sides joined by `hyp` edges (`Transitive`), dropping those that hold
-- and failing on one that does not. A var-rule disjunction whose grade has a
-- value is dropped when below the unit, and fails when its type is refuted
-- eternal (`etDec`).

-- A closed ordering that fails

Falseʳ : ∀ {Θ} → List (RExp Θ × RExp Θ) → Set
Falseʳ {Θ} l = Σ[ ρ ∈ RExp Θ ] Σ[ ρ' ∈ RExp Θ ]
                 ((ρ , ρ') ∈ l × ((δ : Subst Θ ∅ˢ) → ¬ (∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ)))

Falseᵉ : ∀ {Θ} → List (EExp Θ × EExp Θ) → Set
Falseᵉ {Θ} l = Σ[ ε ∈ EExp Θ ] Σ[ ε' ∈ EExp Θ ]
                 ((ε , ε') ∈ l × ((δ : Subst Θ ∅ˢ) → ¬ (∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ)))

-- The orderings left once the closed ones that hold are dropped

record Keptʳ {Θ : Scope} (l : List (RExp Θ × RExp Θ)) : Set where
  constructor keptʳ
  field
    lʳ   : List (RExp Θ × RExp Θ)
    subʳ : ∀ {p} → p ∈ lʳ → p ∈ l
    entʳ : ∀ {Θ'} {Q : Hyps Θ'} → (δ : Subst Θ Θ')
         → (∀ {ρ ρ'} → (ρ , ρ') ∈ lʳ → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ)
         → ∀ {ρ ρ'} → (ρ , ρ') ∈ l → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ

record Keptᵉ {Θ : Scope} (l : List (EExp Θ × EExp Θ)) : Set where
  constructor keptᵉ
  field
    lᵉ   : List (EExp Θ × EExp Θ)
    subᵉ : ∀ {p} → p ∈ lᵉ → p ∈ l
    entᵉ : ∀ {Θ'} {Q : Hyps Θ'} → (δ : Subst Θ Θ')
         → (∀ {ε ε'} → (ε , ε') ∈ lᵉ → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ)
         → ∀ {ε ε'} → (ε , ε') ∈ l → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ

open Keptʳ
open Keptᵉ

consʳ : ∀ {Θ} {l : List (RExp Θ × RExp Θ)} {ρ ρ'} → Keptʳ l → Keptʳ ((ρ , ρ') ∷ l)
consʳ {ρ = ρ} {ρ'} k =
  keptʳ ((ρ , ρ') ∷ lʳ k)
        (λ { (here refl) → here refl ; (there m) → there (subʳ k m) })
        (λ δ f → λ { (here refl) → f (here refl)
                   ; (there m)   → entʳ k δ (λ m' → f (there m')) m })

consᵉ : ∀ {Θ} {l : List (EExp Θ × EExp Θ)} {ε ε'} → Keptᵉ l → Keptᵉ ((ε , ε') ∷ l)
consᵉ {ε = ε} {ε'} k =
  keptᵉ ((ε , ε') ∷ lᵉ k)
        (λ { (here refl) → here refl ; (there m) → there (subᵉ k m) })
        (λ δ f → λ { (here refl) → f (here refl)
                   ; (there m)   → entᵉ k δ (λ m' → f (there m')) m })

dropʳ : ∀ {Θ} {l : List (RExp Θ × RExp Θ)} {ρ ρ'}
      → (∀ {Q : Hyps Θ} → Q ⊩ ρ ≾̂ᵣ ρ') → Keptʳ l → Keptʳ ((ρ , ρ') ∷ l)
dropʳ p k =
  keptʳ (lʳ k) (λ m → there (subʳ k m))
        (λ δ f → λ { (here refl) → ⊩-substᵣ (⊩ᴴ-∅ {σ = δ}) p
                   ; (there m)   → entʳ k δ f m })

dropᵉ : ∀ {Θ} {l : List (EExp Θ × EExp Θ)} {ε ε'}
      → (∀ {Q : Hyps Θ} → Q ⊩ ε ≾̂ₑ ε') → Keptᵉ l → Keptᵉ ((ε , ε') ∷ l)
dropᵉ p k =
  keptᵉ (lᵉ k) (λ m → there (subᵉ k m))
        (λ δ f → λ { (here refl) → ⊩-substₑ (⊩ᴴ-∅ {σ = δ}) p
                   ; (there m)   → entᵉ k δ f m })

thereʳ : ∀ {Θ} {l : List (RExp Θ × RExp Θ)} {p} → Falseʳ l → Falseʳ (p ∷ l)
thereʳ (ρ , ρ' , m , n) = ρ , ρ' , there m , n

thereᵉ : ∀ {Θ} {l : List (EExp Θ × EExp Θ)} {p} → Falseᵉ l → Falseᵉ (p ∷ l)
thereᵉ (ε , ε' , m , n) = ε , ε' , there m , n

closedʳ : ∀ {Θ} → (l : List (RExp Θ × RExp Θ)) → Falseʳ l ⊎ Keptʳ l
closedʳ [] = inj₂ (keptʳ [] (λ ()) (λ δ k → λ ()))
closedʳ ((ρ , ρ') ∷ l) with closedʳ l
... | inj₁ f = inj₁ (thereʳ f)
... | inj₂ k with closedᵣ? ρ ρ'
...   | just (holdsᵣ p) = inj₂ (dropʳ p k)
...   | just (failsᵣ n) = inj₁ (ρ , ρ' , here refl , n)
...   | nothing         = inj₂ (consʳ k)

closedᵉ : ∀ {Θ} → (l : List (EExp Θ × EExp Θ)) → Falseᵉ l ⊎ Keptᵉ l
closedᵉ [] = inj₂ (keptᵉ [] (λ ()) (λ δ k → λ ()))
closedᵉ ((ε , ε') ∷ l) with closedᵉ l
... | inj₁ f = inj₁ (thereᵉ f)
... | inj₂ k with closedₑ? ε ε'
...   | just (holdsₑ p) = inj₂ (dropᵉ p k)
...   | just (failsₑ n) = inj₁ (ε , ε' , here refl , n)
...   | nothing         = inj₂ (consᵉ k)

-- A failing closed ordering holds at no closed instance

falseʳ : ∀ {Θ} {l : List (RExp Θ × RExp Θ)} → Falseʳ l → (δ : Subst Θ ∅ˢ)
       → (∀ {ρ ρ'} → (ρ , ρ') ∈ l → ∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ) → ⊥
falseʳ (ρ , ρ' , m , n) δ k = n δ (k m)

falseᵉ : ∀ {Θ} {l : List (EExp Θ × EExp Θ)} → Falseᵉ l → (δ : Subst Θ ∅ˢ)
       → (∀ {ε ε'} → (ε , ε') ∈ l → ∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ) → ⊥
falseᵉ (ε , ε' , m , n) δ k = n δ (k m)

-- A var-rule disjunction whose grade has a value above the unit, at a type
-- refuted eternal, fails

Falseᵈ : ∀ {Θ} → List (OVType Θ × RExp Θ) → Set
Falseᵈ {Θ} l = Σ[ A ∈ OVType Θ ] Σ[ ρ ∈ RExp Θ ]
                 ((A , ρ) ∈ l × etDec A ≡ nothing
                  × ((δ : Subst Θ ∅ˢ) → ¬ (∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ûᵣ)))

record Keptᵈ {Θ : Scope} (l : List (OVType Θ × RExp Θ)) : Set where
  constructor keptᵈ
  field
    lᵈ   : List (OVType Θ × RExp Θ)
    subᵈ : ∀ {p} → p ∈ lᵈ → p ∈ l
    entᵈ : ∀ {Θ'} {Q : Hyps Θ'} → (δ : Subst Θ Θ')
         → (∀ {A ρ} → (A , ρ) ∈ lᵈ → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ))
         → ∀ {A ρ} → (A , ρ) ∈ l → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ)

open Keptᵈ

consᵈ : ∀ {Θ} {l : List (OVType Θ × RExp Θ)} {A ρ} → Keptᵈ l → Keptᵈ ((A , ρ) ∷ l)
consᵈ {A = A} {ρ} k =
  keptᵈ ((A , ρ) ∷ lᵈ k)
        (λ { (here refl) → here refl ; (there m) → there (subᵈ k m) })
        (λ δ f → λ { (here refl) → f (here refl)
                   ; (there m)   → entᵈ k δ (λ m' → f (there m')) m })

dropᵈ : ∀ {Θ} {l : List (OVType Θ × RExp Θ)} {A ρ}
      → (∀ {Q : Hyps Θ} → Q ⊩ ρ ≾̂ᵣ ûᵣ) → Keptᵈ l → Keptᵈ ((A , ρ) ∷ l)
dropᵈ p k =
  keptᵈ (lᵈ k) (λ m → there (subᵈ k m))
        (λ δ f → λ { (here refl) → ≾ᵘ-ok (⊩-substᵣ (⊩ᴴ-∅ {σ = δ}) p)
                   ; (there m)   → entᵈ k δ f m })

thereᵈ : ∀ {Θ} {l : List (OVType Θ × RExp Θ)} {p} → Falseᵈ l → Falseᵈ (p ∷ l)
thereᵈ (A , ρ , m , e , n) = A , ρ , there m , e , n

closedᵈ : ∀ {Θ} → (l : List (OVType Θ × RExp Θ)) → Falseᵈ l ⊎ Keptᵈ l
closedᵈ [] = inj₂ (keptᵈ [] (λ ()) (λ δ k → λ ()))
closedᵈ ((A , ρ) ∷ l) with closedᵈ l
... | inj₁ f = inj₁ (thereᵈ f)
... | inj₂ k with closedᵣ? ρ ûᵣ
...   | nothing         = inj₂ (consᵈ k)
...   | just (holdsᵣ p) = inj₂ (dropᵈ p k)
...   | just (failsᵣ n) with etDec A in e
...     | nothing = inj₁ (A , ρ , here refl , e , n)
...     | just _  = inj₂ (consᵈ k)

falseᵈ : ∀ {Θ} {l : List (OVType Θ × RExp Θ)} → Falseᵈ l → (δ : Subst Θ ∅ˢ)
       → (∀ {A ρ} → (A , ρ) ∈ l → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ)) → ⊥
falseᵈ (A , ρ , m , e , n) δ k with VarOK-∅ (k m)
... | inj₁ et = etDec-refute A e δ et
... | inj₂ le = n δ (val-≾ᵣ⁻ le)

------------------------------------------------------------------------
-- The orderings a list entails by transitivity
--
-- Pairs of closed sides joined by a chain of two or more edges: the
-- orderings, the `hyp` edges and sameness, closed by `Reach`.

module Transitive {X : Set} {_≅_ : X → X → Set} (_≟_ : Decidable _≅_) (closed? : X → 𝔹)
                  (l : List (X × X)) where

  Edge : X → X → Set
  Edge a b = (a , b) ∈ l ⊎ a ≅ b

  private

    edgesOf : (k : List (X × X)) → (∀ {p} → p ∈ k → p ∈ l)
            → List (Σ[ a ∈ X ] Σ[ b ∈ X ] Edge a b)
    edgesOf []            f = []
    edgesOf ((a , b) ∷ k) f = (a , b , inj₁ (f (here refl))) ∷ edgesOf k (λ m → f (there m))

    same? : (a b : X) → Maybe (Star Edge a b)
    same? a b with a ≟ b
    ... | yes p = just (inj₂ p ◅◅ ◅-nil)
    ... | no _  = nothing

    insert : X → List X → List X
    insert x xs with any (λ y → does (x ≟ y)) xs
    ... | true  = xs
    ... | false = x ∷ xs

    sides : List (X × X) → List X
    sides []            = []
    sides ((a , b) ∷ k) = insert a (insert b (sides k))

  vs : List X
  vs = sides l

  open Reachability Edge same? (edgesOf l (λ m → m)) vs using (Chain; Closure; closure; reach)

  private

    closedOf : (k : List X) → (∀ {x} → x ∈ k → x ∈ vs) → List (Σ[ a ∈ X ] a ∈ vs)
    closedOf []      f = []
    closedOf (a ∷ k) f with closed? a
    ... | true  = (a , f (here refl)) ∷ closedOf k (λ m → f (there m))
    ... | false = closedOf k (λ m → f (there m))

    long : ∀ {a b} → Chain a b → 𝔹
    long (_ ◅◅ _ ◅◅ _) = true
    long _             = false

    from : Closure → List (Σ[ b ∈ X ] b ∈ vs) → Σ[ a ∈ X ] a ∈ vs
         → List (Σ[ a ∈ X ] Σ[ b ∈ X ] Chain a b)
    from C []              _        = []
    from C ((b , mb) ∷ bs) (a , ma) with reach C ma mb
    ... | nothing = from C bs (a , ma)
    ... | just p with long p
    ...   | true  = (a , b , p) ∷ from C bs (a , ma)
    ...   | false = from C bs (a , ma)

    among : Closure → List (Σ[ a ∈ X ] a ∈ vs) → List (Σ[ a ∈ X ] Σ[ b ∈ X ] Chain a b)
    among C cs = concatMap (from C cs) cs

    ends : (Σ[ a ∈ X ] Σ[ b ∈ X ] Chain a b) → X × X
    ends (a , b , _) = a , b

  -- The pairs of closed sides joined by a chain of two or more edges

  chains : List (X × X)
  chains = map ends (among closure (closedOf vs (λ m → m)))

  -- Each holds wherever the orderings do, in a preorder

  chains-⊩ : {Le : X → X → Set} → (∀ {a} → Le a a) → (∀ {a b c} → Le a b → Le b c → Le a c)
           → (∀ {a b} → a ≅ b → Le a b)
           → (∀ {a b} → (a , b) ∈ l → Le a b) → ∀ {a b} → (a , b) ∈ chains → Le a b
  chains-⊩ {Le} r t s e m with ∈-map⁻ ends m
  ... | (a , b , p) , _ , refl = along p
    where
      along : ∀ {a b} → Chain a b → Le a b
      along ◅-nil            = r
      along (inj₁ x ◅◅ xs) = t (e x) (along xs)
      along (inj₂ x ◅◅ xs) = t (s x) (along xs)

-- The resource and effect orderings, with those they entail by
-- transitivity between closed sides

withChainsʳ : ∀ {Θ} → List (RExp Θ × RExp Θ) → List (RExp Θ × RExp Θ)
withChainsʳ l = l ++ Transitive.chains _≟ʳ_ (λ ρ → is-just (valʳ? ρ)) l

withChainsᵉ : ∀ {Θ} → List (EExp Θ × EExp Θ) → List (EExp Θ × EExp Θ)
withChainsᵉ l = l ++ Transitive.chains _≟ᵉ_ (λ ε → is-just (valᵉ? ε)) l

withChainsʳ-⊩ : ∀ {Θ Θ'} {Q : Hyps Θ'} {δ : Subst Θ Θ'} → (l : List (RExp Θ × RExp Θ))
              → (∀ {ρ ρ'} → (ρ , ρ') ∈ l → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ)
              → ∀ {ρ ρ'} → (ρ , ρ') ∈ withChainsʳ l → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
withChainsʳ-⊩ l h m with ∈-++⁻ l m
... | inj₁ m' = h m'
... | inj₂ m' =
  Transitive.chains-⊩ _≟ʳ_ (λ ρ → is-just (valʳ? ρ)) l ⊩≾̂ᵣ-refl transᵣ
                      (λ p → eqᵣ (≡̂ᵣ-subst _ (≅ʳ⇒≡̂ p))) h m'

withChainsᵉ-⊩ : ∀ {Θ Θ'} {Q : Hyps Θ'} {δ : Subst Θ Θ'} → (l : List (EExp Θ × EExp Θ))
              → (∀ {ε ε'} → (ε , ε') ∈ l → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ)
              → ∀ {ε ε'} → (ε , ε') ∈ withChainsᵉ l → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
withChainsᵉ-⊩ l h m with ∈-++⁻ l m
... | inj₁ m' = h m'
... | inj₂ m' =
  Transitive.chains-⊩ _≟ᵉ_ (λ ε → is-just (valᵉ? ε)) l ⊩≾̂ₑ-refl transₑ
                      (λ p → eqₑ (≡̂ₑ-subst _ (≅ᵉ⇒≡̂ p))) h m'

------------------------------------------------------------------------
-- The disjunctions left once those whose grade is below the unit at
-- the strength `full` from a set are dropped

record Followsᵈ {Θ : Scope} (H : Hyps Θ) (l : List (OVType Θ × RExp Θ)) : Set where
  constructor followsᵈ
  field
    lᶠ   : List (OVType Θ × RExp Θ)
    subᶠ : ∀ {p} → p ∈ lᶠ → p ∈ l
    entᶠ : ∀ {A ρ} → (A , ρ) ∈ l → ((A , ρ) ∈ lᶠ) ⊎ (H ⊩ ρ ≾̂ᵣ ûᵣ)

open Followsᵈ

follows? : ∀ {Θ} → (H : Hyps Θ) → (l : List (OVType Θ × RExp Θ)) → Followsᵈ H l
follows? H []            = followsᵈ [] (λ ()) (λ ())
follows? H ((A , ρ) ∷ l) with follows? H l | decideᵣ full H ρ ûᵣ
... | followsᵈ l' s e | just d  =
      followsᵈ l' (λ m → there (s m)) (λ { (here refl) → inj₂ d ; (there m) → e m })
... | followsᵈ l' s e | nothing =
      followsᵈ ((A , ρ) ∷ l') (λ { (here refl) → here refl ; (there m) → there (s m) })
               (λ { (here refl) → inj₁ (here refl)
                  ; (there m) → [ (λ m' → inj₁ (there m')) , inj₂ ]′ (e m) })

-- The orderings of two lists, as a set

ordsᴴ : ∀ {Θ} → List (RExp Θ × RExp Θ) → List (EExp Θ × EExp Θ) → Hyps Θ
ordsᴴ lʳ lᵉ = hyps [] [] lʳ lᵉ [] []

------------------------------------------------------------------------
-- The closed orderings of a hypothesis set decided, then the
-- disjunctions that follow from the orderings left dropped

checkClosed : ∀ {Θ} → Hyps Θ → Maybe (Hyps Θ)
checkClosed Q with closedʳ (withChainsʳ (ordᵣ Q)) | closedᵉ (withChainsᵉ (ordₑ Q)) | closedᵈ (disj Q)
... | inj₂ kʳ | inj₂ kᵉ | inj₂ kᵈ =
      just (hyps (ets Q) (subᵥ Q) (lʳ kʳ) (lᵉ kᵉ) (lᶠ (follows? (ordsᴴ (lʳ kʳ) (lᵉ kᵉ)) (lᵈ kᵈ)))
                 (qhyps Q))
... | _       | _       | _       = nothing

-- It keeps the quantified hypotheses

checkClosed-unq : ∀ {Θ} → (Q : Hyps Θ) → {Q₁ : Hyps Θ} → checkClosed Q ≡ just Q₁ → Unq Q → Unq Q₁
checkClosed-unq Q eq u with closedʳ (withChainsʳ (ordᵣ Q)) | closedᵉ (withChainsᵉ (ordₑ Q)) | closedᵈ (disj Q)
checkClosed-unq Q refl u | inj₂ kʳ | inj₂ kᵉ | inj₂ kᵈ = unq (no-qhyps u)
checkClosed-unq Q () u | inj₁ _ | _      | _
checkClosed-unq Q () u | inj₂ _ | inj₁ _ | _
checkClosed-unq Q () u | inj₂ _ | inj₂ _ | inj₁ _

-- What is left entails the set

checkClosed-⊩ : ∀ {Θ} → (Q : Hyps Θ) → {Q₁ : Hyps Θ} → checkClosed Q ≡ just Q₁ → Q₁ ⊩ᴴ Q [ idˢ ]
checkClosed-⊩ Q eq with closedʳ (withChainsʳ (ordᵣ Q)) | closedᵉ (withChainsᵉ (ordₑ Q)) | closedᵈ (disj Q)
checkClosed-⊩ Q refl | inj₂ kʳ | inj₂ kᵉ | inj₂ kᵈ =
  mk⊩ᴴ (⊩ets r) (⊩subᵥ r) (λ m → entʳ kʳ idˢ (⊩ordᵣ r) (∈-++⁺ˡ m))
       (λ m → entᵉ kᵉ idˢ (⊩ordₑ r) (∈-++⁺ˡ m)) (entᵈ kᵈ idˢ dsj)
       (λ m → ⊩ᴼ-hyp⁼ m)
  where
    H = ordsᴴ (lʳ kʳ) (lᵉ kᵉ)
    F = follows? H (lᵈ kᵈ)
    r = ⊩ᴴ-refl {Q = hyps (ets Q) (subᵥ Q) (lʳ kʳ) (lᵉ kᵉ) (lᶠ F) (qhyps Q)}

    dsj : ∀ {A ρ} → (A , ρ) ∈ lᵈ kᵈ
        → VarOK (hyps (ets Q) (subᵥ Q) (lʳ kʳ) (lᵉ kᵉ) (lᶠ F) (qhyps Q)) (A [ idˢ ]ᵛ) (ρ [ idˢ ]ʳ)
    dsj m with entᶠ F m
    ... | inj₁ m' = ⊩disj r m'
    ... | inj₂ d  = ≾ᵘ-ok (⊩-substᵣ (mk⊩ᴴ (λ ()) (λ ()) (⊩ordᵣ r) (⊩ordₑ r) (λ ()) (λ ())) d)
checkClosed-⊩ Q () | inj₁ _ | _      | _
checkClosed-⊩ Q () | inj₂ _ | inj₁ _ | _
checkClosed-⊩ Q () | inj₂ _ | inj₂ _ | inj₁ _

-- and is entailed wherever the set is, its chains being composed of
-- `hyp` edges

checkClosed-⊆ : ∀ {Θ Θ'} → (Q : Hyps Θ) → {Q₁ : Hyps Θ} → checkClosed Q ≡ just Q₁
              → {Q' : Hyps Θ'} {δ : Subst Θ Θ'} → Q' ⊩ᴴ Q [ δ ] → Q' ⊩ᴴ Q₁ [ δ ]
checkClosed-⊆ Q eq h with closedʳ (withChainsʳ (ordᵣ Q)) | closedᵉ (withChainsᵉ (ordₑ Q)) | closedᵈ (disj Q)
checkClosed-⊆ Q refl h | inj₂ kʳ | inj₂ kᵉ | inj₂ kᵈ =
  mk⊩ᴴ (⊩ets h) (⊩subᵥ h)
       (λ m → withChainsʳ-⊩ (ordᵣ Q) (λ m' → ⊩-substᵣ h (edgeᵣ-sound (hyp m'))) (subʳ kʳ m))
       (λ m → withChainsᵉ-⊩ (ordₑ Q) (λ m' → ⊩-substₑ h (edgeₑ-sound (hyp m'))) (subᵉ kᵉ m))
       (λ m → ⊩disj h (subᵈ kᵈ (subᶠ (follows? (ordsᴴ (lʳ kʳ) (lᵉ kᵉ)) (lᵈ kᵈ)) m)))
       (⊩qhyps h)
checkClosed-⊆ Q () h | inj₁ _ | _      | _
checkClosed-⊆ Q () h | inj₂ _ | inj₁ _ | _
checkClosed-⊆ Q () h | inj₂ _ | inj₂ _ | inj₁ _

-- A failure leaves the set unsatisfiable

checkClosed-fail : ∀ {Θ} → (Q : Hyps Θ) → checkClosed Q ≡ nothing → ¬ Satisfiable Q
checkClosed-fail Q eq (δ , h₀) with closedʳ (withChainsʳ (ordᵣ Q)) | closedᵉ (withChainsᵉ (ordₑ Q)) | closedᵈ (disj Q)
... | inj₁ f | _      | _      =
      falseʳ f δ (withChainsʳ-⊩ (ordᵣ Q) (λ m → ⊩-substᵣ h (edgeᵣ-sound (hyp m))))
  where h = ⊨⇒⊩ᴴ h₀
... | inj₂ _ | inj₁ f | _      =
      falseᵉ f δ (withChainsᵉ-⊩ (ordₑ Q) (λ m → ⊩-substₑ h (edgeₑ-sound (hyp m))))
  where h = ⊨⇒⊩ᴴ h₀
... | inj₂ _ | inj₂ _ | inj₁ f = falseᵈ f δ (⊩disj h)
  where h = ⊨⇒⊩ᴴ h₀
checkClosed-fail Q () (δ , h₀) | inj₂ _ | inj₂ _ | inj₂ _

------------------------------------------------------------------------
-- Failing chains of the whole graph
--
-- A chain, factor edges included, from a variable-free vertex to one it is
-- not below at `closed` leaves `Q` unsatisfiable.

-- The first vertex reached that the source is not below

failsAlongₑ : ∀ {Θ} {Q : Hyps Θ} {ε : EExp Θ}
            → List (Σ[ ε' ∈ EExp Θ ] Star (Edgeₑ Q) ε ε') → Maybe (¬ Satisfiable Q)
failsAlongₑ []                       = nothing
failsAlongₑ {ε = ε} ((ε' , ch) ∷ l) with closedₑ? ε ε'
... | just (failsₑ n) = just (λ { (δ , h) → n δ (⊩-substₑ (⊨⇒⊩ᴴ h) (chainₑ-sound ch)) })
... | _               = failsAlongₑ l

failsAlongᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ}
            → List (Σ[ ρ' ∈ RExp Θ ] Star (Edgeᵣ Q) ρ ρ') → Maybe (¬ Satisfiable Q)
failsAlongᵣ []                       = nothing
failsAlongᵣ {ρ = ρ} ((ρ' , ch) ∷ l) with closedᵣ? ρ ρ'
... | just (failsᵣ n) = just (λ { (δ , h) → n δ (⊩-substᵣ (⊨⇒⊩ᴴ h) (chainᵣ-sound ch)) })
... | _               = failsAlongᵣ l

-- The sources with a value, each followed along the graph

failingₑ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeₑ Q) → List (EExp Θ) → Maybe (¬ Satisfiable Q)
failingₑ g []       = nothing
failingₑ g (ε ∷ εs) with valᵉ? ε
... | just _  = failsAlongₑ (reachesₑ g ε) <∣> failingₑ g εs
... | nothing = failingₑ g εs

failingᵣ : ∀ {Θ} {Q : Hyps Θ} → List (GEdgeᵣ Q) → List (RExp Θ) → Maybe (¬ Satisfiable Q)
failingᵣ g []       = nothing
failingᵣ g (ρ ∷ ρs) with valʳ? ρ
... | just _  = failsAlongᵣ (reachesᵣ g ρ) <∣> failingᵣ g ρs
... | nothing = failingᵣ g ρs

failingChain : ∀ {Θ} → (Q : Hyps Θ) → Maybe (¬ Satisfiable Q)
failingChain Q =
  failingₑ gₑ (firsts _≟ᵉ_ (λ ε → ε) [] (map (λ { (ε , _ , _) → ε }) gₑ))
  <∣> failingᵣ gᵣ (firsts _≟ʳ_ (λ ρ → ρ) [] (map (λ { (ρ , _ , _) → ρ }) gᵣ))
  where
    gₑ = fullGraphₑ Q
    gᵣ = fullGraphᵣ Q
