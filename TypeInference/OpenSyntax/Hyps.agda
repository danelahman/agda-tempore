------------------------------------------------------------------
-- Hypotheses and entailment of the open calculus               --
--                                                              --
-- A hypothesis set `Hyps Θ` consists of eternality atoms on    --
-- type variables, subtyping atoms between type variables,      --
-- orderings between open grade expressions, and var-rule       --
-- disjunctions. Entailment (`_⊩ᵗᵛ_≾_`, `_⊩_≾̂ᵣ_`, `_⊩_≾̂ₑ_`,     --
-- `_⊩ᴱ_`, `_∣_<:̂ᵛ_`, `VarOK`) is inductive, and sound at every --
-- closed instance. Entailed ordering includes the zero-product --
-- laws of the grades: a product below the unit has both        --
-- factors below it.                                            --
--                                                              --
-- The module also defines convertibility of open types         --
-- (`_≡̂ᵛ_`), which `VarOK` uses, and open subtyping with its    --
-- inversion and stability lemmas, both of which occur in       --
-- `_⊩ᴴ_[_]`.                                                   --
--                                                              --
-- Judgements under a hypothesis set are the constrained types  --
-- of HM(X) (Odersky, Sulzmann and Wehr, 1999) and the          --
-- qualified types of Jones (1994); the set plays the role of   --
-- the given constraints of OutsideIn(X) (Vytiniotis et al.,    --
-- JFP 2011).                                                   --
------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe using (Is-just)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to Any-just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (tt)

open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.OpenSyntax.Hyps (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

-- Only the eternal-base-type predicate is imported; the constructors of
-- the closed `Eternal` have open counterparts below.

open import Syntax.Types S using (EternalBaseType)

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S

-- Deciding a `Maybe` carries the trivial witness of `Is-just` along with it

Is-just? : ∀ {A : Set} → (m : Maybe A) → Maybe (Is-just m)
Is-just? (just _) = just (Any-just tt)
Is-just? nothing  = nothing

-- An equation identifying a `Maybe` as `just` carries the same witness

≡-Is-just : ∀ {A : Set} {m : Maybe A} {x : A} → m ≡ just x → Is-just m
≡-Is-just refl = Any-just tt

-- Hypothesis sets

record Hyps (Θ : Scope) : Set where
  constructor hyps
  field
    ets  : List (TyVar Θ)                     -- eternality atoms on type variables
    subᵥ : List (TyVar Θ × TyVar Θ)           -- assumed subtyping between type variables
    ordᵣ : List (RExp Θ × RExp Θ)             -- assumed resource-grade orderings
    ordₑ : List (EExp Θ × EExp Θ)             -- assumed effect-grade orderings
    disj : List (OVType Θ × RExp Θ)           -- assumed var-rule disjunctions

open Hyps public

-- Empty hypothesis set

∅ᴴ : ∀ {Θ} → Hyps Θ
∅ᴴ = hyps [] [] [] [] []

-- Pairwise action of a function on a homogeneous pair

mapᵖ : ∀ {A B : Set} → (A → B) → A × A → B × B
mapᵖ f (x , y) = f x , f y

-- Componentwise action on a type-and-grade pair

mapᵈ : ∀ {Θ Θ'} → (OVType Θ → OVType Θ') → (RExp Θ → RExp Θ')
     → OVType Θ × RExp Θ → OVType Θ' × RExp Θ'
mapᵈ f g (A , ρ) = f A , g ρ

-- Action of the scope extensions on hypothesis sets

wkᵗ-H : ∀ {Θ} → Hyps Θ → Hyps (Θ +ty)
wkᵗ-H {Θ} Q = hyps (map (wkᵗ-tv Θ) (ets Q))
                   (map (mapᵖ (wkᵗ-tv Θ)) (subᵥ Q))
                   (map (mapᵖ wkᵗ-r) (ordᵣ Q))
                   (map (mapᵖ wkᵗ-e) (ordₑ Q))
                   (map (mapᵈ wkᵗ-v wkᵗ-r) (disj Q))

wkʳ-H : ∀ {Θ} → Hyps Θ → Hyps (Θ +r)
wkʳ-H {Θ} Q = hyps (map (wkʳ-tv Θ) (ets Q))
                   (map (mapᵖ (wkʳ-tv Θ)) (subᵥ Q))
                   (map (mapᵖ wkʳ-r) (ordᵣ Q))
                   (map (mapᵖ wkʳ-e) (ordₑ Q))
                   (map (mapᵈ wkʳ-v wkʳ-r) (disj Q))

wkᵉ-H : ∀ {Θ} → Hyps Θ → Hyps (Θ +e)
wkᵉ-H {Θ} Q = hyps (map (wkᵉ-tv Θ) (ets Q))
                   (map (mapᵖ (wkᵉ-tv Θ)) (subᵥ Q))
                   (map (mapᵖ wkᵉ-r) (ordᵣ Q))
                   (map (mapᵖ wkᵉ-e) (ordₑ Q))
                   (map (mapᵈ wkᵉ-v wkᵉ-r) (disj Q))

-- Assumed subtyping between type variables, closed under reflexivity
-- and transitivity

infix 4 _⊩ᵗᵛ_≾_

data _⊩ᵗᵛ_≾_ {Θ : Scope} (Q : Hyps Θ) : TyVar Θ → TyVar Θ → Set where
  reflᵗᵛ  : ∀ {α} → Q ⊩ᵗᵛ α ≾ α
  hypᵗᵛ   : ∀ {α β} → (α , β) ∈ subᵥ Q → Q ⊩ᵗᵛ α ≾ β
  transᵗᵛ : ∀ {α β γ} → Q ⊩ᵗᵛ α ≾ β → Q ⊩ᵗᵛ β ≾ γ → Q ⊩ᵗᵛ α ≾ γ

-- Convertibility: the monoid laws, commutativity of multiplication
-- where the grade declares it, commutativity of the join,
-- distributivity of multiplication over the join, the constants'
-- arithmetic, `∣_∣̂ᵉ` being a monoid morphism, and absorption of a join
-- by an upper bound. Idempotence, the top's absorption, antisymmetry at
-- the empty hypothesis set and associativity of the join are derived
-- below.
--
-- Convertibility carries no hypotheses: the ordering premise of
-- absorption is entailed by the empty set, and convertibility and
-- entailed ordering form one mutual definition, the latter occurring
-- positively.

infix 4 _≡̂ᵣ_ _≡̂ₑ_ _⊩_≾̂ᵣ_ _⊩_≾̂ₑ_

data _≡̂ᵣ_ {Θ : Scope} : RExp Θ → RExp Θ → Set
data _≡̂ₑ_ {Θ : Scope} : EExp Θ → EExp Θ → Set
data _⊩_≾̂ᵣ_ {Θ : Scope} (Q : Hyps Θ) : RExp Θ → RExp Θ → Set
data _⊩_≾̂ₑ_ {Θ : Scope} (Q : Hyps Θ) : EExp Θ → EExp Θ → Set

data _≡̂ᵣ_ {Θ} where
  ≡̂ᵣ-refl       : ∀ {ρ} → ρ ≡̂ᵣ ρ
  ≡̂ᵣ-sym        : ∀ {ρ ρ'} → ρ ≡̂ᵣ ρ' → ρ' ≡̂ᵣ ρ
  ≡̂ᵣ-trans      : ∀ {ρ ρ' ρ''} → ρ ≡̂ᵣ ρ' → ρ' ≡̂ᵣ ρ'' → ρ ≡̂ᵣ ρ''
  ≡̂ᵣ-cong       : ∀ {ρ₁ ρ₁' ρ₂ ρ₂'} → ρ₁ ≡̂ᵣ ρ₁' → ρ₂ ≡̂ᵣ ρ₂'
                → ρ₁ ·̂ᵣ ρ₂ ≡̂ᵣ ρ₁' ·̂ᵣ ρ₂'
  ≡̂ᵣ-assoc      : ∀ {ρ₁ ρ₂ ρ₃} → (ρ₁ ·̂ᵣ ρ₂) ·̂ᵣ ρ₃ ≡̂ᵣ ρ₁ ·̂ᵣ (ρ₂ ·̂ᵣ ρ₃)
  ≡̂ᵣ-identityˡ  : ∀ {ρ} → ûᵣ ·̂ᵣ ρ ≡̂ᵣ ρ
  ≡̂ᵣ-identityʳ  : ∀ {ρ} → ρ ·̂ᵣ ûᵣ ≡̂ᵣ ρ
  ≡̂ᵣ-const-·    : ∀ {ρ ρ'} → rconst ρ ·̂ᵣ rconst ρ' ≡̂ᵣ rconst (ρ ·ᵣ ρ')
  ≡̂ᵣ-comm       : ∀ {ρ₁ ρ₂} → Is-just ·ᵣ-comm? → ρ₁ ·̂ᵣ ρ₂ ≡̂ᵣ ρ₂ ·̂ᵣ ρ₁
  ≡̂ᵣ-cong-⊔     : ∀ {ρ₁ ρ₁' ρ₂ ρ₂'} → ρ₁ ≡̂ᵣ ρ₁' → ρ₂ ≡̂ᵣ ρ₂'
                → ρ₁ ⊔̂ᵣ ρ₂ ≡̂ᵣ ρ₁' ⊔̂ᵣ ρ₂'
  ≡̂ᵣ-const-⊔    : ∀ {ρ ρ'} → rconst ρ ⊔̂ᵣ rconst ρ' ≡̂ᵣ rconst (ρ ⊔ᵣ ρ')
  ≡̂ᵣ-comm-⊔     : ∀ {ρ₁ ρ₂} → ρ₁ ⊔̂ᵣ ρ₂ ≡̂ᵣ ρ₂ ⊔̂ᵣ ρ₁
  ≡̂ᵣ-distribˡ-⊔ : ∀ {ρ ρ₁ ρ₂} → ρ ·̂ᵣ (ρ₁ ⊔̂ᵣ ρ₂) ≡̂ᵣ ρ ·̂ᵣ ρ₁ ⊔̂ᵣ ρ ·̂ᵣ ρ₂
  ≡̂ᵣ-distribʳ-⊔ : ∀ {ρ ρ₁ ρ₂} → (ρ₁ ⊔̂ᵣ ρ₂) ·̂ᵣ ρ ≡̂ᵣ ρ₁ ·̂ᵣ ρ ⊔̂ᵣ ρ₂ ·̂ᵣ ρ
  ≡̂ᵣ-map-·      : ∀ {ε ε'} → ∣ ε ·̂ₑ ε' ∣̂ᵉ ≡̂ᵣ ∣ ε ∣̂ᵉ ·̂ᵣ ∣ ε' ∣̂ᵉ
  ≡̂ᵣ-map-⊔      : ∀ {ε ε'} → ∣ ε ⊔̂ₑ ε' ∣̂ᵉ ≡̂ᵣ ∣ ε ∣̂ᵉ ⊔̂ᵣ ∣ ε' ∣̂ᵉ
  ≡̂ᵣ-map-const  : ∀ {e} → ∣ econst e ∣̂ᵉ ≡̂ᵣ rconst (mapᵉ e)
  ≡̂ᵣ-map-cong   : ∀ {ε ε'} → ε ≡̂ₑ ε' → ∣ ε ∣̂ᵉ ≡̂ᵣ ∣ ε' ∣̂ᵉ
  ≡̂ᵣ-absorb     : ∀ {ρ ρ'} → ∅ᴴ ⊩ ρ ≾̂ᵣ ρ' → ρ ⊔̂ᵣ ρ' ≡̂ᵣ ρ'

data _≡̂ₑ_ {Θ} where
  ≡̂ₑ-refl       : ∀ {ε} → ε ≡̂ₑ ε
  ≡̂ₑ-sym        : ∀ {ε ε'} → ε ≡̂ₑ ε' → ε' ≡̂ₑ ε
  ≡̂ₑ-trans      : ∀ {ε ε' ε''} → ε ≡̂ₑ ε' → ε' ≡̂ₑ ε'' → ε ≡̂ₑ ε''
  ≡̂ₑ-cong       : ∀ {ε₁ ε₁' ε₂ ε₂'} → ε₁ ≡̂ₑ ε₁' → ε₂ ≡̂ₑ ε₂'
                → ε₁ ·̂ₑ ε₂ ≡̂ₑ ε₁' ·̂ₑ ε₂'
  ≡̂ₑ-assoc      : ∀ {ε₁ ε₂ ε₃} → (ε₁ ·̂ₑ ε₂) ·̂ₑ ε₃ ≡̂ₑ ε₁ ·̂ₑ (ε₂ ·̂ₑ ε₃)
  ≡̂ₑ-identityˡ  : ∀ {ε} → ûₑ ·̂ₑ ε ≡̂ₑ ε
  ≡̂ₑ-identityʳ  : ∀ {ε} → ε ·̂ₑ ûₑ ≡̂ₑ ε
  ≡̂ₑ-const-·    : ∀ {ε ε'} → econst ε ·̂ₑ econst ε' ≡̂ₑ econst (ε ·ₑ ε')
  ≡̂ₑ-comm       : ∀ {ε₁ ε₂} → Is-just ·ₑ-comm? → ε₁ ·̂ₑ ε₂ ≡̂ₑ ε₂ ·̂ₑ ε₁
  ≡̂ₑ-cong-⊔     : ∀ {ε₁ ε₁' ε₂ ε₂'} → ε₁ ≡̂ₑ ε₁' → ε₂ ≡̂ₑ ε₂'
                → ε₁ ⊔̂ₑ ε₂ ≡̂ₑ ε₁' ⊔̂ₑ ε₂'
  ≡̂ₑ-const-⊔    : ∀ {ε ε'} → econst ε ⊔̂ₑ econst ε' ≡̂ₑ econst (ε ⊔ₑ ε')
  ≡̂ₑ-comm-⊔     : ∀ {ε₁ ε₂} → ε₁ ⊔̂ₑ ε₂ ≡̂ₑ ε₂ ⊔̂ₑ ε₁
  ≡̂ₑ-distribˡ-⊔ : ∀ {ε ε₁ ε₂} → ε ·̂ₑ (ε₁ ⊔̂ₑ ε₂) ≡̂ₑ ε ·̂ₑ ε₁ ⊔̂ₑ ε ·̂ₑ ε₂
  ≡̂ₑ-distribʳ-⊔ : ∀ {ε ε₁ ε₂} → (ε₁ ⊔̂ₑ ε₂) ·̂ₑ ε ≡̂ₑ ε₁ ·̂ₑ ε ⊔̂ₑ ε₂ ·̂ₑ ε
  ≡̂ₑ-absorb     : ∀ {ε ε'} → ∅ᴴ ⊩ ε ≾̂ₑ ε' → ε ⊔̂ₑ ε' ≡̂ₑ ε'

data _⊩_≾̂ᵣ_ {Θ} Q where
  hypᵣ     : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q ⊩ ρ ≾̂ᵣ ρ'
  atomᵣ    : ∀ {ρ ρ'} → ρ ≾ᵣ ρ' → Q ⊩ rconst ρ ≾̂ᵣ rconst ρ'
  eqᵣ      : ∀ {ρ ρ'} → ρ ≡̂ᵣ ρ' → Q ⊩ ρ ≾̂ᵣ ρ'
  transᵣ   : ∀ {ρ ρ' ρ''} → Q ⊩ ρ ≾̂ᵣ ρ' → Q ⊩ ρ' ≾̂ᵣ ρ'' → Q ⊩ ρ ≾̂ᵣ ρ''
  monoᵣ    : ∀ {ρ₁ ρ₁' ρ₂ ρ₂'} → Q ⊩ ρ₁ ≾̂ᵣ ρ₁' → Q ⊩ ρ₂ ≾̂ᵣ ρ₂'
           → Q ⊩ ρ₁ ·̂ᵣ ρ₂ ≾̂ᵣ ρ₁' ·̂ᵣ ρ₂'
  map-mono : ∀ {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → Q ⊩ ∣ ε ∣̂ᵉ ≾̂ᵣ ∣ ε' ∣̂ᵉ
  -- the join is the least upper bound; monotonicity of `_⊔̂ᵣ_` is derivable
  ⊔-ubˡᵣ   : ∀ {ρ₁ ρ₂} → Q ⊩ ρ₁ ≾̂ᵣ ρ₁ ⊔̂ᵣ ρ₂
  ⊔-ubʳᵣ   : ∀ {ρ₁ ρ₂} → Q ⊩ ρ₂ ≾̂ᵣ ρ₁ ⊔̂ᵣ ρ₂
  ⊔-lubᵣ   : ∀ {ρ₁ ρ₂ ρ} → Q ⊩ ρ₁ ≾̂ᵣ ρ → Q ⊩ ρ₂ ≾̂ᵣ ρ → Q ⊩ ρ₁ ⊔̂ᵣ ρ₂ ≾̂ᵣ ρ
  -- every grade is below the top
  topᵣ     : ∀ {ρ} → Q ⊩ ρ ≾̂ᵣ rconst ⊤ᵣ
  -- the unit is below every grade when the grade declares it least
  minᵣ     : ∀ {ρ} → Is-just uᵣ-least? → Q ⊩ ûᵣ ≾̂ᵣ ρ
  -- zero-product: a product below the unit has both factors below it
  zeroˡᵣ   : ∀ {ρ ρ'} → Q ⊩ ρ ·̂ᵣ ρ' ≾̂ᵣ ûᵣ → Q ⊩ ρ ≾̂ᵣ ûᵣ
  zeroʳᵣ   : ∀ {ρ ρ'} → Q ⊩ ρ ·̂ᵣ ρ' ≾̂ᵣ ûᵣ → Q ⊩ ρ' ≾̂ᵣ ûᵣ
  -- the closure of a grade lies below every grade above it that
  -- absorbs its own iteration
  plusᵣ    : ∀ {c ρ} → (p : Plus _·ᵣ_ _≾ᵣ_ c) → Q ⊩ rconst c ≾̂ᵣ ρ → Q ⊩ ρ ·̂ᵣ ρ ≾̂ᵣ ρ
           → Q ⊩ rconst (Plus.c⁺ p) ≾̂ᵣ ρ

data _⊩_≾̂ₑ_ {Θ} Q where
  hypₑ   : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q ⊩ ε ≾̂ₑ ε'
  atomₑ  : ∀ {ε ε'} → ε ≾ₑ ε' → Q ⊩ econst ε ≾̂ₑ econst ε'
  eqₑ    : ∀ {ε ε'} → ε ≡̂ₑ ε' → Q ⊩ ε ≾̂ₑ ε'
  transₑ : ∀ {ε ε' ε''} → Q ⊩ ε ≾̂ₑ ε' → Q ⊩ ε' ≾̂ₑ ε'' → Q ⊩ ε ≾̂ₑ ε''
  monoₑ  : ∀ {ε₁ ε₁' ε₂ ε₂'} → Q ⊩ ε₁ ≾̂ₑ ε₁' → Q ⊩ ε₂ ≾̂ₑ ε₂'
         → Q ⊩ ε₁ ·̂ₑ ε₂ ≾̂ₑ ε₁' ·̂ₑ ε₂'
  -- the join is the least upper bound; monotonicity of `_⊔̂ₑ_` is derivable
  ⊔-ubˡₑ : ∀ {ε₁ ε₂} → Q ⊩ ε₁ ≾̂ₑ ε₁ ⊔̂ₑ ε₂
  ⊔-ubʳₑ : ∀ {ε₁ ε₂} → Q ⊩ ε₂ ≾̂ₑ ε₁ ⊔̂ₑ ε₂
  ⊔-lubₑ : ∀ {ε₁ ε₂ ε} → Q ⊩ ε₁ ≾̂ₑ ε → Q ⊩ ε₂ ≾̂ₑ ε → Q ⊩ ε₁ ⊔̂ₑ ε₂ ≾̂ₑ ε
  -- every grade is below the top
  topₑ   : ∀ {ε} → Q ⊩ ε ≾̂ₑ econst ⊤ₑ
  -- the unit is below every grade when the grade declares it least
  minₑ   : ∀ {ε} → Is-just uₑ-least? → Q ⊩ ûₑ ≾̂ₑ ε
  -- zero-product: a product below the unit has both factors below it
  zeroˡₑ : ∀ {ε ε'} → Q ⊩ ε ·̂ₑ ε' ≾̂ₑ ûₑ → Q ⊩ ε ≾̂ₑ ûₑ
  zeroʳₑ : ∀ {ε ε'} → Q ⊩ ε ·̂ₑ ε' ≾̂ₑ ûₑ → Q ⊩ ε' ≾̂ₑ ûₑ
  -- the closure of a grade lies below every grade above it that
  -- absorbs its own iteration
  plusₑ  : ∀ {c ε} → (p : Plus _·ₑ_ _≾ₑ_ c) → Q ⊩ econst c ≾̂ₑ ε → Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε
         → Q ⊩ econst (Plus.c⁺ p) ≾̂ₑ ε

-- Entailed ordering is reflexive

⊩≾̂ᵣ-refl : ∀ {Θ} {Q : Hyps Θ} {ρ} → Q ⊩ ρ ≾̂ᵣ ρ
⊩≾̂ᵣ-refl = eqᵣ ≡̂ᵣ-refl

⊩≾̂ₑ-refl : ∀ {Θ} {Q : Hyps Θ} {ε} → Q ⊩ ε ≾̂ₑ ε
⊩≾̂ₑ-refl = eqₑ ≡̂ₑ-refl

-- Idempotence of the join and absorption by the top: instances of
-- absorption, as in `Syntax.Grades`

≡̂ᵣ-idem-⊔ : ∀ {Θ} {ρ : RExp Θ} → ρ ⊔̂ᵣ ρ ≡̂ᵣ ρ
≡̂ᵣ-idem-⊔ = ≡̂ᵣ-absorb ⊩≾̂ᵣ-refl

≡̂ᵣ-⊤-⊔ : ∀ {Θ} {ρ : RExp Θ} → ρ ⊔̂ᵣ rconst ⊤ᵣ ≡̂ᵣ rconst ⊤ᵣ
≡̂ᵣ-⊤-⊔ = ≡̂ᵣ-absorb topᵣ

≡̂ₑ-idem-⊔ : ∀ {Θ} {ε : EExp Θ} → ε ⊔̂ₑ ε ≡̂ₑ ε
≡̂ₑ-idem-⊔ = ≡̂ₑ-absorb ⊩≾̂ₑ-refl

≡̂ₑ-⊤-⊔ : ∀ {Θ} {ε : EExp Θ} → ε ⊔̂ₑ econst ⊤ₑ ≡̂ₑ econst ⊤ₑ
≡̂ₑ-⊤-⊔ = ≡̂ₑ-absorb topₑ

-- Antisymmetry at the empty hypothesis set

≡̂ᵣ-antisym-∅ : ∀ {Θ} {ρ ρ' : RExp Θ}
             → ∅ᴴ ⊩ ρ ≾̂ᵣ ρ' → ∅ᴴ ⊩ ρ' ≾̂ᵣ ρ → ρ ≡̂ᵣ ρ'
≡̂ᵣ-antisym-∅ p q =
  ≡̂ᵣ-trans (≡̂ᵣ-sym (≡̂ᵣ-absorb q)) (≡̂ᵣ-trans ≡̂ᵣ-comm-⊔ (≡̂ᵣ-absorb p))

≡̂ₑ-antisym-∅ : ∀ {Θ} {ε ε' : EExp Θ}
             → ∅ᴴ ⊩ ε ≾̂ₑ ε' → ∅ᴴ ⊩ ε' ≾̂ₑ ε → ε ≡̂ₑ ε'
≡̂ₑ-antisym-∅ p q =
  ≡̂ₑ-trans (≡̂ₑ-sym (≡̂ₑ-absorb q)) (≡̂ₑ-trans ≡̂ₑ-comm-⊔ (≡̂ₑ-absorb p))

-- Associativity of the join

≡̂ᵣ-assoc-⊔ : ∀ {Θ} {ρ₁ ρ₂ ρ₃ : RExp Θ}
           → (ρ₁ ⊔̂ᵣ ρ₂) ⊔̂ᵣ ρ₃ ≡̂ᵣ ρ₁ ⊔̂ᵣ (ρ₂ ⊔̂ᵣ ρ₃)
≡̂ᵣ-assoc-⊔ =
  ≡̂ᵣ-antisym-∅ (⊔-lubᵣ (⊔-lubᵣ ⊔-ubˡᵣ (transᵣ ⊔-ubˡᵣ ⊔-ubʳᵣ)) (transᵣ ⊔-ubʳᵣ ⊔-ubʳᵣ))
               (⊔-lubᵣ (transᵣ ⊔-ubˡᵣ ⊔-ubˡᵣ) (⊔-lubᵣ (transᵣ ⊔-ubʳᵣ ⊔-ubˡᵣ) ⊔-ubʳᵣ))

≡̂ₑ-assoc-⊔ : ∀ {Θ} {ε₁ ε₂ ε₃ : EExp Θ}
           → (ε₁ ⊔̂ₑ ε₂) ⊔̂ₑ ε₃ ≡̂ₑ ε₁ ⊔̂ₑ (ε₂ ⊔̂ₑ ε₃)
≡̂ₑ-assoc-⊔ =
  ≡̂ₑ-antisym-∅ (⊔-lubₑ (⊔-lubₑ ⊔-ubˡₑ (transₑ ⊔-ubˡₑ ⊔-ubʳₑ)) (transₑ ⊔-ubʳₑ ⊔-ubʳₑ))
               (⊔-lubₑ (transₑ ⊔-ubˡₑ ⊔-ubˡₑ) (⊔-lubₑ (transₑ ⊔-ubʳₑ ⊔-ubˡₑ) ⊔-ubʳₑ))

-- Mirrors `Eternal` of `Syntax.Types`, with a rule for `Nat`, plus
-- rules for the eternality atoms of the hypothesis set and for transfer
-- along an assumed subtyping in both directions; as in the original, no
-- rule for `_⇒_` and `[_]_`.

infix 4 _⊩ᴱ_

data _⊩ᴱ_ {Θ : Scope} (Q : Hyps Θ) : OVType Θ → Set where
  et-hyp  : ∀ {α} → α ∈ ets Q → Q ⊩ᴱ tvar α
  et-subˡ : ∀ {α β} → Q ⊩ᵗᵛ α ≾ β → Q ⊩ᴱ tvar β → Q ⊩ᴱ tvar α
  et-subʳ : ∀ {α β} → Q ⊩ᵗᵛ α ≾ β → Q ⊩ᴱ tvar α → Q ⊩ᴱ tvar β
  Baseₑ   : ∀ {b} → .(EternalBaseType b) → Q ⊩ᴱ Base b
  Unitₑ   : Q ⊩ᴱ Unit
  Boolₑ   : Q ⊩ᴱ Bool
  Natₑ    : Q ⊩ᴱ Nat
  _|×|ₑ_  : ∀ {A₁ A₂} → Q ⊩ᴱ A₁ → Q ⊩ᴱ A₂ → Q ⊩ᴱ A₁ |×| A₂
  Emptyₑ  : Q ⊩ᴱ Empty

-- Convertibility of open types: the same shape, the grades related
-- by `_≡̂ᵣ_` and `_≡̂ₑ_`

infix  4  _≡̂ᵛ_ _≡̂ᶜ_
infix  37 [_]≡̂_
infix  32 _|×|≡̂_
infixr 30 _⇒≡̂_
infix  31 _‼≡̂_

data _≡̂ᵛ_ {Θ : Scope} : OVType Θ → OVType Θ → Set
data _≡̂ᶜ_ {Θ : Scope} : OCType Θ → OCType Θ → Set

data _≡̂ᵛ_ {Θ} where
  tvar≡̂   : ∀ {α} → tvar α ≡̂ᵛ tvar α
  Base≡̂   : ∀ {b} → Base b ≡̂ᵛ Base b
  Unit≡̂   : Unit ≡̂ᵛ Unit
  Bool≡̂   : Bool ≡̂ᵛ Bool
  Nat≡̂   : Nat ≡̂ᵛ Nat
  _|×|≡̂_  : ∀ {A A' B B'} → A ≡̂ᵛ A' → B ≡̂ᵛ B' → A |×| B ≡̂ᵛ A' |×| B'
  Empty≡̂  : Empty ≡̂ᵛ Empty
  _⇒≡̂_    : ∀ {A A' C C'} → A ≡̂ᵛ A' → C ≡̂ᶜ C' → A ⇒ C ≡̂ᵛ A' ⇒ C'
  [_]≡̂_   : ∀ {ρ ρ' A A'} → ρ ≡̂ᵣ ρ' → A ≡̂ᵛ A' → [ ρ ] A ≡̂ᵛ [ ρ' ] A'

data _≡̂ᶜ_ {Θ} where
  _‼≡̂_ : ∀ {A A' ε ε'} → A ≡̂ᵛ A' → ε ≡̂ₑ ε' → A ‼ ε ≡̂ᶜ A' ‼ ε'

≡̂ᵛ-refl : ∀ {Θ} → (A : OVType Θ) → A ≡̂ᵛ A
≡̂ᶜ-refl : ∀ {Θ} → (C : OCType Θ) → C ≡̂ᶜ C

≡̂ᵛ-refl (tvar α)  = tvar≡̂
≡̂ᵛ-refl (Base b)  = Base≡̂
≡̂ᵛ-refl Unit      = Unit≡̂
≡̂ᵛ-refl Bool      = Bool≡̂
≡̂ᵛ-refl Nat       = Nat≡̂
≡̂ᵛ-refl (A |×| B) = ≡̂ᵛ-refl A |×|≡̂ ≡̂ᵛ-refl B
≡̂ᵛ-refl Empty     = Empty≡̂
≡̂ᵛ-refl (A ⇒ C)   = ≡̂ᵛ-refl A ⇒≡̂ ≡̂ᶜ-refl C
≡̂ᵛ-refl ([ ρ ] A) = [ ≡̂ᵣ-refl ]≡̂ ≡̂ᵛ-refl A

≡̂ᶜ-refl (A ‼ ε) = ≡̂ᵛ-refl A ‼≡̂ ≡̂ₑ-refl

≡̂ᵛ-sym : ∀ {Θ} {A A' : OVType Θ} → A ≡̂ᵛ A' → A' ≡̂ᵛ A
≡̂ᶜ-sym : ∀ {Θ} {C C' : OCType Θ} → C ≡̂ᶜ C' → C' ≡̂ᶜ C

≡̂ᵛ-sym tvar≡̂       = tvar≡̂
≡̂ᵛ-sym Base≡̂       = Base≡̂
≡̂ᵛ-sym Unit≡̂       = Unit≡̂
≡̂ᵛ-sym Bool≡̂       = Bool≡̂
≡̂ᵛ-sym Nat≡̂       = Nat≡̂
≡̂ᵛ-sym (p |×|≡̂ q)  = ≡̂ᵛ-sym p |×|≡̂ ≡̂ᵛ-sym q
≡̂ᵛ-sym Empty≡̂      = Empty≡̂
≡̂ᵛ-sym (p ⇒≡̂ q)    = ≡̂ᵛ-sym p ⇒≡̂ ≡̂ᶜ-sym q
≡̂ᵛ-sym ([ r ]≡̂ p)  = [ ≡̂ᵣ-sym r ]≡̂ ≡̂ᵛ-sym p

≡̂ᶜ-sym (p ‼≡̂ e) = ≡̂ᵛ-sym p ‼≡̂ ≡̂ₑ-sym e

≡̂ᵛ-trans : ∀ {Θ} {A A' A'' : OVType Θ} → A ≡̂ᵛ A' → A' ≡̂ᵛ A'' → A ≡̂ᵛ A''
≡̂ᶜ-trans : ∀ {Θ} {C C' C'' : OCType Θ} → C ≡̂ᶜ C' → C' ≡̂ᶜ C'' → C ≡̂ᶜ C''

≡̂ᵛ-trans tvar≡̂      tvar≡̂       = tvar≡̂
≡̂ᵛ-trans Base≡̂      Base≡̂       = Base≡̂
≡̂ᵛ-trans Unit≡̂      Unit≡̂       = Unit≡̂
≡̂ᵛ-trans Bool≡̂      Bool≡̂       = Bool≡̂
≡̂ᵛ-trans Nat≡̂      Nat≡̂       = Nat≡̂
≡̂ᵛ-trans (p |×|≡̂ q) (p' |×|≡̂ q') = ≡̂ᵛ-trans p p' |×|≡̂ ≡̂ᵛ-trans q q'
≡̂ᵛ-trans Empty≡̂     Empty≡̂      = Empty≡̂
≡̂ᵛ-trans (p ⇒≡̂ q)   (p' ⇒≡̂ q')   = ≡̂ᵛ-trans p p' ⇒≡̂ ≡̂ᶜ-trans q q'
≡̂ᵛ-trans ([ r ]≡̂ p) ([ r' ]≡̂ p') = [ ≡̂ᵣ-trans r r' ]≡̂ ≡̂ᵛ-trans p p'

≡̂ᶜ-trans (p ‼≡̂ e) (p' ‼≡̂ e') = ≡̂ᵛ-trans p p' ‼≡̂ ≡̂ₑ-trans e e'

-- Eternality ignores the grades, so it transfers along convertibility

⊩ᴱ-≡̂ : ∀ {Θ} {Q : Hyps Θ} {A A'} → A ≡̂ᵛ A' → Q ⊩ᴱ A → Q ⊩ᴱ A'
⊩ᴱ-≡̂ tvar≡̂      et           = et
⊩ᴱ-≡̂ Base≡̂      et           = et
⊩ᴱ-≡̂ Unit≡̂      et           = et
⊩ᴱ-≡̂ Bool≡̂      et           = et
⊩ᴱ-≡̂ Nat≡̂      et           = et
⊩ᴱ-≡̂ (p |×|≡̂ q) (et |×|ₑ et') = ⊩ᴱ-≡̂ p et |×|ₑ ⊩ᴱ-≡̂ q et'
⊩ᴱ-≡̂ Empty≡̂     et           = et

-- The side condition of the `var` rule: `Eternal` is undecided at open
-- types, so the original's `¬ Eternal A → ρ ≾ᵣ uᵣ` becomes a disjunction,
-- met by eternality, by the ordering, or by a `disj` hypothesis at a
-- convertible type and a grade above.

data VarOK {Θ : Scope} (Q : Hyps Θ) (A : OVType Θ) (ρ : RExp Θ) : Set where
  et-ok  : Q ⊩ᴱ A → VarOK Q A ρ
  ≾ᵘ-ok  : Q ⊩ ρ ≾̂ᵣ ûᵣ → VarOK Q A ρ
  hyp-ok : ∀ {A' ρ'} → (A' , ρ') ∈ disj Q → A ≡̂ᵛ A' → Q ⊩ ρ ≾̂ᵣ ρ' → VarOK Q A ρ

-- A `disj` hypothesis met as it stands

hyp-ok₀ : ∀ {Θ} {Q : Hyps Θ} {A ρ} → (A , ρ) ∈ disj Q → VarOK Q A ρ
hyp-ok₀ {A = A} m = hyp-ok m (≡̂ᵛ-refl A) (eqᵣ ≡̂ᵣ-refl)

-- The side condition is closed under convertibility of the type and
-- under lowering the grade

VarOK-≡̂ : ∀ {Θ} {Q : Hyps Θ} {A A' ρ ρ'}
        → A ≡̂ᵛ A' → Q ⊩ ρ ≾̂ᵣ ρ' → VarOK Q A' ρ' → VarOK Q A ρ
VarOK-≡̂ p q (et-ok et)       = et-ok (⊩ᴱ-≡̂ (≡̂ᵛ-sym p) et)
VarOK-≡̂ p q (≾ᵘ-ok le)       = ≾ᵘ-ok (transᵣ q le)
VarOK-≡̂ p q (hyp-ok m p' q') = hyp-ok m (≡̂ᵛ-trans p p') (transᵣ q q')

-- Shape-preserving subtyping of open value and computation types,
-- mirroring `Syntax.Subtyping` former by former, with `Natₛ` for `Nat`:
-- one constructor per pair of matching type formers, no `refl` or
-- `trans` constructor. The grade slots carry entailments from `Q`, and
-- an unknown head is related only by an assumed subtyping.
--
-- Unlike `Syntax.Subtyping`, the relation is proof-relevant, as
-- entailment is.

infix  4  _∣_<:̂ᵛ_ _∣_<:̂ᶜ_
infix  37 [_]ₛ_
infix  32 _|×|ₛ_
infixr 30 _⇒ₛ_
infix  31 _‼ₛ_

data _∣_<:̂ᵛ_ {Θ : Scope} (Q : Hyps Θ) : OVType Θ → OVType Θ → Set
data _∣_<:̂ᶜ_ {Θ : Scope} (Q : Hyps Θ) : OCType Θ → OCType Θ → Set

data _∣_<:̂ᵛ_ {Θ} Q where
  tvarₛ  : ∀ {α β} → Q ⊩ᵗᵛ α ≾ β → Q ∣ tvar α <:̂ᵛ tvar β
  Baseₛ  : ∀ {b b'} → b ≡ b' → Q ∣ Base b <:̂ᵛ Base b'
  Unitₛ  : Q ∣ Unit <:̂ᵛ Unit
  Boolₛ  : Q ∣ Bool <:̂ᵛ Bool
  Natₛ   : Q ∣ Nat <:̂ᵛ Nat
  _|×|ₛ_ : ∀ {A A' B B'} → Q ∣ A <:̂ᵛ A' → Q ∣ B <:̂ᵛ B'
         → Q ∣ (A |×| B) <:̂ᵛ (A' |×| B')
  Emptyₛ : Q ∣ Empty <:̂ᵛ Empty
  _⇒ₛ_   : ∀ {A A' C C'} → Q ∣ A' <:̂ᵛ A → Q ∣ C <:̂ᶜ C'
         → Q ∣ (A ⇒ C) <:̂ᵛ (A' ⇒ C')
  [_]ₛ_  : ∀ {ρ ρ' A A'} → Q ⊩ ρ' ≾̂ᵣ ρ → Q ∣ A <:̂ᵛ A'
         → Q ∣ ([ ρ ] A) <:̂ᵛ ([ ρ' ] A')

data _∣_<:̂ᶜ_ {Θ} Q where
  _‼ₛ_ : ∀ {A A' ε ε'} → Q ∣ A <:̂ᵛ A' → Q ⊩ ε ≾̂ₑ ε'
       → Q ∣ (A ‼ ε) <:̂ᶜ (A' ‼ ε')

-- Reflexivity

<:̂ᵛ-refl : ∀ {Θ} {Q : Hyps Θ} → (A : OVType Θ) → Q ∣ A <:̂ᵛ A
<:̂ᶜ-refl : ∀ {Θ} {Q : Hyps Θ} → (C : OCType Θ) → Q ∣ C <:̂ᶜ C

<:̂ᵛ-refl (tvar α)  = tvarₛ reflᵗᵛ
<:̂ᵛ-refl (Base b)  = Baseₛ refl
<:̂ᵛ-refl Unit      = Unitₛ
<:̂ᵛ-refl Bool      = Boolₛ
<:̂ᵛ-refl Nat       = Natₛ
<:̂ᵛ-refl (A |×| B) = <:̂ᵛ-refl A |×|ₛ <:̂ᵛ-refl B
<:̂ᵛ-refl Empty     = Emptyₛ
<:̂ᵛ-refl (A ⇒ C)   = <:̂ᵛ-refl A ⇒ₛ <:̂ᶜ-refl C
<:̂ᵛ-refl ([ ρ ] A) = [ ⊩≾̂ᵣ-refl ]ₛ <:̂ᵛ-refl A

<:̂ᶜ-refl (A ‼ ε) = <:̂ᵛ-refl A ‼ₛ ⊩≾̂ₑ-refl

-- Transitivity; the contravariant positions compose in the opposite order

<:̂ᵛ-trans : ∀ {Θ} {Q : Hyps Θ} {A B C}
          → Q ∣ A <:̂ᵛ B → Q ∣ B <:̂ᵛ C → Q ∣ A <:̂ᵛ C
<:̂ᶜ-trans : ∀ {Θ} {Q : Hyps Θ} {C₁ C₂ C₃}
          → Q ∣ C₁ <:̂ᶜ C₂ → Q ∣ C₂ <:̂ᶜ C₃ → Q ∣ C₁ <:̂ᶜ C₃

<:̂ᵛ-trans (tvarₛ p)  (tvarₛ q)  = tvarₛ (transᵗᵛ p q)
<:̂ᵛ-trans (Baseₛ p)  (Baseₛ q)  = Baseₛ (trans p q)
<:̂ᵛ-trans Unitₛ      Unitₛ      = Unitₛ
<:̂ᵛ-trans Boolₛ      Boolₛ      = Boolₛ
<:̂ᵛ-trans Natₛ       Natₛ       = Natₛ
<:̂ᵛ-trans (p |×|ₛ r) (q |×|ₛ s) = <:̂ᵛ-trans p q |×|ₛ <:̂ᵛ-trans r s
<:̂ᵛ-trans Emptyₛ     Emptyₛ     = Emptyₛ
<:̂ᵛ-trans (p ⇒ₛ r)   (q ⇒ₛ s)   = <:̂ᵛ-trans q p ⇒ₛ <:̂ᶜ-trans r s
<:̂ᵛ-trans ([ p ]ₛ r) ([ q ]ₛ s) = [ transᵣ q p ]ₛ <:̂ᵛ-trans r s

<:̂ᶜ-trans (p ‼ₛ r) (q ‼ₛ s) = <:̂ᵛ-trans p q ‼ₛ transₑ r s

-- Convertible types are subtypes of each other

≡̂ᵛ-<:̂ : ∀ {Θ} {Q : Hyps Θ} {A A'} → A ≡̂ᵛ A' → Q ∣ A <:̂ᵛ A'
≡̂ᶜ-<:̂ : ∀ {Θ} {Q : Hyps Θ} {C C'} → C ≡̂ᶜ C' → Q ∣ C <:̂ᶜ C'

≡̂ᵛ-<:̂ tvar≡̂      = tvarₛ reflᵗᵛ
≡̂ᵛ-<:̂ Base≡̂      = Baseₛ refl
≡̂ᵛ-<:̂ Unit≡̂      = Unitₛ
≡̂ᵛ-<:̂ Bool≡̂      = Boolₛ
≡̂ᵛ-<:̂ Nat≡̂      = Natₛ
≡̂ᵛ-<:̂ (p |×|≡̂ q) = ≡̂ᵛ-<:̂ p |×|ₛ ≡̂ᵛ-<:̂ q
≡̂ᵛ-<:̂ Empty≡̂     = Emptyₛ
≡̂ᵛ-<:̂ (p ⇒≡̂ q)   = ≡̂ᵛ-<:̂ (≡̂ᵛ-sym p) ⇒ₛ ≡̂ᶜ-<:̂ q
≡̂ᵛ-<:̂ ([ r ]≡̂ p) = [ eqᵣ (≡̂ᵣ-sym r) ]ₛ ≡̂ᵛ-<:̂ p

≡̂ᶜ-<:̂ (p ‼≡̂ e) = ≡̂ᵛ-<:̂ p ‼ₛ eqₑ e

-- Eternality lives on the shared skeleton, so it transfers along
-- `_∣_<:̂ᵛ_` in both directions.

<:̂ᵛ-eternalˡ : ∀ {Θ} {Q : Hyps Θ} {A B} → Q ∣ A <:̂ᵛ B → Q ⊩ᴱ B → Q ⊩ᴱ A
<:̂ᵛ-eternalˡ (tvarₛ p)    et          = et-subˡ p et
<:̂ᵛ-eternalˡ (Baseₛ refl) et          = et
<:̂ᵛ-eternalˡ Unitₛ        et          = et
<:̂ᵛ-eternalˡ Boolₛ        et          = et
<:̂ᵛ-eternalˡ Natₛ         et          = et
<:̂ᵛ-eternalˡ (p |×|ₛ r)   (et |×|ₑ e) = <:̂ᵛ-eternalˡ p et |×|ₑ <:̂ᵛ-eternalˡ r e
<:̂ᵛ-eternalˡ Emptyₛ       et          = et

<:̂ᵛ-eternalʳ : ∀ {Θ} {Q : Hyps Θ} {A B} → Q ∣ A <:̂ᵛ B → Q ⊩ᴱ A → Q ⊩ᴱ B
<:̂ᵛ-eternalʳ (tvarₛ p)    et          = et-subʳ p et
<:̂ᵛ-eternalʳ (Baseₛ refl) et          = et
<:̂ᵛ-eternalʳ Unitₛ        et          = et
<:̂ᵛ-eternalʳ Boolₛ        et          = et
<:̂ᵛ-eternalʳ Natₛ         et          = et
<:̂ᵛ-eternalʳ (p |×|ₛ r)   (et |×|ₑ e) = <:̂ᵛ-eternalʳ p et |×|ₑ <:̂ᵛ-eternalʳ r e
<:̂ᵛ-eternalʳ Emptyₛ       et          = et

-- Inversion at the formers with no proper supertype

<:̂ᵛ-Baseˡ : ∀ {Θ} {Q : Hyps Θ} {b A} → Q ∣ Base b <:̂ᵛ A → A ≡ Base b
<:̂ᵛ-Baseˡ (Baseₛ refl) = refl

<:̂ᵛ-Unitˡ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ∣ Unit <:̂ᵛ A → A ≡ Unit
<:̂ᵛ-Unitˡ Unitₛ = refl

<:̂ᵛ-Boolˡ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ∣ Bool <:̂ᵛ A → A ≡ Bool
<:̂ᵛ-Boolˡ Boolₛ = refl
<:̂ᵛ-Natˡ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ∣ Nat <:̂ᵛ A → A ≡ Nat
<:̂ᵛ-Natˡ Natₛ = refl

-- Inversion at a product: a supertype is a product, componentwise

<:̂ᵛ-×ˡ : ∀ {Θ} {Q : Hyps Θ} {A₁ A₂ B}
       → Q ∣ A₁ |×| A₂ <:̂ᵛ B
       → Σ[ B₁ ∈ OVType Θ ] Σ[ B₂ ∈ OVType Θ ]
           (B ≡ B₁ |×| B₂) × (Q ∣ A₁ <:̂ᵛ B₁) × (Q ∣ A₂ <:̂ᵛ B₂)
<:̂ᵛ-×ˡ (p |×|ₛ q) = _ , _ , refl , p , q

-- Inversion at box type

<:̂ᵛ-box-grade : ∀ {Θ} {Q : Hyps Θ} {ρ ρ' A A'}
              → Q ∣ ([ ρ ] A) <:̂ᵛ ([ ρ' ] A') → Q ⊩ ρ' ≾̂ᵣ ρ
<:̂ᵛ-box-grade ([ q ]ₛ _) = q

<:̂ᵛ-box-type : ∀ {Θ} {Q : Hyps Θ} {ρ ρ' A A'}
             → Q ∣ ([ ρ ] A) <:̂ᵛ ([ ρ' ] A') → Q ∣ A <:̂ᵛ A'
<:̂ᵛ-box-type ([ _ ]ₛ p) = p

-- A subtype of a box type is a box type

<:̂ᵛ-boxʳ : ∀ {Θ} {Q : Hyps Θ} {A ρ B}
         → Q ∣ A <:̂ᵛ [ ρ ] B
         → Σ[ ρ₀ ∈ RExp Θ ] Σ[ A₀ ∈ OVType Θ ]
             (A ≡ [ ρ₀ ] A₀) × (Q ⊩ ρ ≾̂ᵣ ρ₀) × (Q ∣ A₀ <:̂ᵛ B)
<:̂ᵛ-boxʳ ([ q ]ₛ p) = _ , _ , refl , q , p

-- `Q' ⊩ᴴ Q [ σ ]` says `Q'` entails every hypothesis of `Q` transported
-- along `σ`; there is no syntactic action of a substitution on `Hyps`,
-- as `ets` and `subᵥ` hold variables, whose images under `σ` are open
-- types.

infix 4 _⊩ᴴ_[_] _⊩ᴴ_

record _⊩ᴴ_[_] {Θ Θ' : Scope} (Q' : Hyps Θ') (Q : Hyps Θ) (σ : Subst Θ Θ') : Set where
  constructor mk⊩ᴴ
  field
    ⊩ets  : ∀ {α} → α ∈ ets Q → Q' ⊩ᴱ sTy σ α
    ⊩subᵥ : ∀ {α β} → (α , β) ∈ subᵥ Q → Q' ∣ sTy σ α <:̂ᵛ sTy σ β
    ⊩ordᵣ : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q' ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ' [ σ ]ʳ
    ⊩ordₑ : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q' ⊩ ε [ σ ]ᵉ ≾̂ₑ ε' [ σ ]ᵉ
    ⊩disj : ∀ {A ρ} → (A , ρ) ∈ disj Q → VarOK Q' (A [ σ ]ᵛ) (ρ [ σ ]ʳ)

open _⊩ᴴ_[_] public

-- Entailment between hypothesis sets over the same scope

_⊩ᴴ_ : ∀ {Θ} → Hyps Θ → Hyps Θ → Set
Q' ⊩ᴴ Q = Q' ⊩ᴴ Q [ idˢ ]

-- Every set entails the empty one, along any substitution

⊩ᴴ-∅ : ∀ {Θ Θ'} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} → Q' ⊩ᴴ ∅ᴴ [ σ ]
⊩ᴴ-∅ = mk⊩ᴴ (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

-- Convertibility and entailment are stable under substitution, the
-- premise of absorption at the empty set

≡̂ᵣ-subst : ∀ {Θ Θ'} {ρ ρ' : RExp Θ} → (σ : Subst Θ Θ')
         → ρ ≡̂ᵣ ρ' → ρ [ σ ]ʳ ≡̂ᵣ ρ' [ σ ]ʳ
≡̂ₑ-subst : ∀ {Θ Θ'} {ε ε' : EExp Θ} → (σ : Subst Θ Θ')
         → ε ≡̂ₑ ε' → ε [ σ ]ᵉ ≡̂ₑ ε' [ σ ]ᵉ
⊩-substᵣ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {ρ ρ' : RExp Θ}
         → Q' ⊩ᴴ Q [ σ ] → Q ⊩ ρ ≾̂ᵣ ρ' → Q' ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ' [ σ ]ʳ
⊩-substₑ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {ε ε' : EExp Θ}
         → Q' ⊩ᴴ Q [ σ ] → Q ⊩ ε ≾̂ₑ ε' → Q' ⊩ ε [ σ ]ᵉ ≾̂ₑ ε' [ σ ]ᵉ

≡̂ᵣ-subst σ ≡̂ᵣ-refl          = ≡̂ᵣ-refl
≡̂ᵣ-subst σ (≡̂ᵣ-sym p)       = ≡̂ᵣ-sym (≡̂ᵣ-subst σ p)
≡̂ᵣ-subst σ (≡̂ᵣ-trans p q)   = ≡̂ᵣ-trans (≡̂ᵣ-subst σ p) (≡̂ᵣ-subst σ q)
≡̂ᵣ-subst σ (≡̂ᵣ-cong p q)    = ≡̂ᵣ-cong (≡̂ᵣ-subst σ p) (≡̂ᵣ-subst σ q)
≡̂ᵣ-subst σ ≡̂ᵣ-assoc         = ≡̂ᵣ-assoc
≡̂ᵣ-subst σ ≡̂ᵣ-identityˡ     = ≡̂ᵣ-identityˡ
≡̂ᵣ-subst σ ≡̂ᵣ-identityʳ     = ≡̂ᵣ-identityʳ
≡̂ᵣ-subst σ ≡̂ᵣ-const-·       = ≡̂ᵣ-const-·
≡̂ᵣ-subst σ (≡̂ᵣ-comm ij)     = ≡̂ᵣ-comm ij
≡̂ᵣ-subst σ (≡̂ᵣ-cong-⊔ p q)  = ≡̂ᵣ-cong-⊔ (≡̂ᵣ-subst σ p) (≡̂ᵣ-subst σ q)
≡̂ᵣ-subst σ ≡̂ᵣ-const-⊔       = ≡̂ᵣ-const-⊔
≡̂ᵣ-subst σ ≡̂ᵣ-comm-⊔        = ≡̂ᵣ-comm-⊔
≡̂ᵣ-subst σ ≡̂ᵣ-distribˡ-⊔    = ≡̂ᵣ-distribˡ-⊔
≡̂ᵣ-subst σ ≡̂ᵣ-distribʳ-⊔    = ≡̂ᵣ-distribʳ-⊔
≡̂ᵣ-subst σ ≡̂ᵣ-map-·         = ≡̂ᵣ-map-·
≡̂ᵣ-subst σ ≡̂ᵣ-map-⊔         = ≡̂ᵣ-map-⊔
≡̂ᵣ-subst σ ≡̂ᵣ-map-const     = ≡̂ᵣ-map-const
≡̂ᵣ-subst σ (≡̂ᵣ-map-cong p)  = ≡̂ᵣ-map-cong (≡̂ₑ-subst σ p)
≡̂ᵣ-subst σ (≡̂ᵣ-absorb p)    = ≡̂ᵣ-absorb (⊩-substᵣ (⊩ᴴ-∅ {σ = σ}) p)

≡̂ₑ-subst σ ≡̂ₑ-refl          = ≡̂ₑ-refl
≡̂ₑ-subst σ (≡̂ₑ-sym p)       = ≡̂ₑ-sym (≡̂ₑ-subst σ p)
≡̂ₑ-subst σ (≡̂ₑ-trans p q)   = ≡̂ₑ-trans (≡̂ₑ-subst σ p) (≡̂ₑ-subst σ q)
≡̂ₑ-subst σ (≡̂ₑ-cong p q)    = ≡̂ₑ-cong (≡̂ₑ-subst σ p) (≡̂ₑ-subst σ q)
≡̂ₑ-subst σ ≡̂ₑ-assoc         = ≡̂ₑ-assoc
≡̂ₑ-subst σ ≡̂ₑ-identityˡ     = ≡̂ₑ-identityˡ
≡̂ₑ-subst σ ≡̂ₑ-identityʳ     = ≡̂ₑ-identityʳ
≡̂ₑ-subst σ ≡̂ₑ-const-·       = ≡̂ₑ-const-·
≡̂ₑ-subst σ (≡̂ₑ-comm ij)     = ≡̂ₑ-comm ij
≡̂ₑ-subst σ (≡̂ₑ-cong-⊔ p q)  = ≡̂ₑ-cong-⊔ (≡̂ₑ-subst σ p) (≡̂ₑ-subst σ q)
≡̂ₑ-subst σ ≡̂ₑ-const-⊔       = ≡̂ₑ-const-⊔
≡̂ₑ-subst σ ≡̂ₑ-comm-⊔        = ≡̂ₑ-comm-⊔
≡̂ₑ-subst σ ≡̂ₑ-distribˡ-⊔    = ≡̂ₑ-distribˡ-⊔
≡̂ₑ-subst σ ≡̂ₑ-distribʳ-⊔    = ≡̂ₑ-distribʳ-⊔
≡̂ₑ-subst σ (≡̂ₑ-absorb p)    = ≡̂ₑ-absorb (⊩-substₑ (⊩ᴴ-∅ {σ = σ}) p)

⊩-substᵣ            h (hypᵣ m)     = ⊩ordᵣ h m
⊩-substᵣ            h (atomᵣ p)    = atomᵣ p
⊩-substᵣ {σ = σ}    h (eqᵣ p)      = eqᵣ (≡̂ᵣ-subst σ p)
⊩-substᵣ            h (transᵣ p q) = transᵣ (⊩-substᵣ h p) (⊩-substᵣ h q)
⊩-substᵣ            h (monoᵣ p q)  = monoᵣ (⊩-substᵣ h p) (⊩-substᵣ h q)
⊩-substᵣ            h (map-mono p) = map-mono (⊩-substₑ h p)
⊩-substᵣ            h ⊔-ubˡᵣ       = ⊔-ubˡᵣ
⊩-substᵣ            h ⊔-ubʳᵣ       = ⊔-ubʳᵣ
⊩-substᵣ            h (⊔-lubᵣ p q) = ⊔-lubᵣ (⊩-substᵣ h p) (⊩-substᵣ h q)
⊩-substᵣ            h topᵣ         = topᵣ
⊩-substᵣ            h (minᵣ eq)    = minᵣ eq
⊩-substᵣ            h (zeroˡᵣ p)   = zeroˡᵣ (⊩-substᵣ h p)
⊩-substᵣ            h (zeroʳᵣ p)   = zeroʳᵣ (⊩-substᵣ h p)
⊩-substᵣ            h (plusᵣ p q r) = plusᵣ p (⊩-substᵣ h q) (⊩-substᵣ h r)

⊩-substₑ         h (hypₑ m)     = ⊩ordₑ h m
⊩-substₑ         h (atomₑ p)    = atomₑ p
⊩-substₑ {σ = σ} h (eqₑ p)      = eqₑ (≡̂ₑ-subst σ p)
⊩-substₑ         h (transₑ p q) = transₑ (⊩-substₑ h p) (⊩-substₑ h q)
⊩-substₑ         h (monoₑ p q)  = monoₑ (⊩-substₑ h p) (⊩-substₑ h q)
⊩-substₑ         h ⊔-ubˡₑ       = ⊔-ubˡₑ
⊩-substₑ         h ⊔-ubʳₑ       = ⊔-ubʳₑ
⊩-substₑ         h (⊔-lubₑ p q) = ⊔-lubₑ (⊩-substₑ h p) (⊩-substₑ h q)
⊩-substₑ         h topₑ         = topₑ
⊩-substₑ         h (minₑ eq)    = minₑ eq
⊩-substₑ         h (zeroˡₑ p)   = zeroˡₑ (⊩-substₑ h p)
⊩-substₑ         h (zeroʳₑ p)   = zeroʳₑ (⊩-substₑ h p)
⊩-substₑ         h (plusₑ p q r) = plusₑ p (⊩-substₑ h q) (⊩-substₑ h r)

-- A type variable's image is an arbitrary open type, so an assumed
-- subtyping transports to a subtyping derivation at those images.

⊩ᵗᵛ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {α β}
          → Q' ⊩ᴴ Q [ σ ] → Q ⊩ᵗᵛ α ≾ β → Q' ∣ sTy σ α <:̂ᵛ sTy σ β
⊩ᵗᵛ-subst {σ = σ} h (reflᵗᵛ {α})  = <:̂ᵛ-refl (sTy σ α)
⊩ᵗᵛ-subst         h (hypᵗᵛ m)     = ⊩subᵥ h m
⊩ᵗᵛ-subst         h (transᵗᵛ p q) = <:̂ᵛ-trans (⊩ᵗᵛ-subst h p) (⊩ᵗᵛ-subst h q)

⊩ᴱ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {A : OVType Θ}
         → Q' ⊩ᴴ Q [ σ ] → Q ⊩ᴱ A → Q' ⊩ᴱ A [ σ ]ᵛ
⊩ᴱ-subst h (et-hyp m)     = ⊩ets h m
⊩ᴱ-subst h (et-subˡ p et) = <:̂ᵛ-eternalˡ (⊩ᵗᵛ-subst h p) (⊩ᴱ-subst h et)
⊩ᴱ-subst h (et-subʳ p et) = <:̂ᵛ-eternalʳ (⊩ᵗᵛ-subst h p) (⊩ᴱ-subst h et)
⊩ᴱ-subst h (Baseₑ p)      = Baseₑ p
⊩ᴱ-subst h Unitₑ          = Unitₑ
⊩ᴱ-subst h Boolₑ          = Boolₑ
⊩ᴱ-subst h Natₑ           = Natₑ
⊩ᴱ-subst h (et₁ |×|ₑ et₂) = ⊩ᴱ-subst h et₁ |×|ₑ ⊩ᴱ-subst h et₂
⊩ᴱ-subst h Emptyₑ         = Emptyₑ

≡̂ᵛ-subst : ∀ {Θ Θ'} {A A' : OVType Θ} → (σ : Subst Θ Θ') → A ≡̂ᵛ A' → A [ σ ]ᵛ ≡̂ᵛ A' [ σ ]ᵛ
≡̂ᶜ-subst : ∀ {Θ Θ'} {C C' : OCType Θ} → (σ : Subst Θ Θ') → C ≡̂ᶜ C' → C [ σ ]ᶜ ≡̂ᶜ C' [ σ ]ᶜ

≡̂ᵛ-subst σ (tvar≡̂ {α}) = ≡̂ᵛ-refl (sTy σ α)
≡̂ᵛ-subst σ Base≡̂       = Base≡̂
≡̂ᵛ-subst σ Unit≡̂       = Unit≡̂
≡̂ᵛ-subst σ Bool≡̂       = Bool≡̂
≡̂ᵛ-subst σ Nat≡̂       = Nat≡̂
≡̂ᵛ-subst σ (p |×|≡̂ q)  = ≡̂ᵛ-subst σ p |×|≡̂ ≡̂ᵛ-subst σ q
≡̂ᵛ-subst σ Empty≡̂      = Empty≡̂
≡̂ᵛ-subst σ (p ⇒≡̂ q)    = ≡̂ᵛ-subst σ p ⇒≡̂ ≡̂ᶜ-subst σ q
≡̂ᵛ-subst σ ([ r ]≡̂ p)  = [ ≡̂ᵣ-subst σ r ]≡̂ ≡̂ᵛ-subst σ p

≡̂ᶜ-subst σ (p ‼≡̂ e) = ≡̂ᵛ-subst σ p ‼≡̂ ≡̂ₑ-subst σ e

-- Eternality reads only the skeleton, so it moves between the images
-- of a type under two substitutions related by subtyping at every
-- type variable

⊩ᴱ-<:ˢ : ∀ {Θ Θ'} {Q : Hyps Θ'} {σ τ : Subst Θ Θ'}
       → (∀ α → Q ∣ sTy σ α <:̂ᵛ sTy τ α) → (A : OVType Θ)
       → Q ⊩ᴱ A [ τ ]ᵛ → Q ⊩ᴱ A [ σ ]ᵛ
⊩ᴱ-<:ˢ k (tvar α)  et           = <:̂ᵛ-eternalˡ (k α) et
⊩ᴱ-<:ˢ k (Base b)  et           = et
⊩ᴱ-<:ˢ k Unit      et           = et
⊩ᴱ-<:ˢ k Bool      et           = et
⊩ᴱ-<:ˢ k Nat       et           = et
⊩ᴱ-<:ˢ k (A |×| B) (et |×|ₑ et') = ⊩ᴱ-<:ˢ k A et |×|ₑ ⊩ᴱ-<:ˢ k B et'
⊩ᴱ-<:ˢ k Empty     et           = et
⊩ᴱ-<:ˢ k (A ⇒ C)   ()
⊩ᴱ-<:ˢ k ([ ρ ] A) ()

VarOK-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'}
                {A : OVType Θ} {ρ : RExp Θ}
            → Q' ⊩ᴴ Q [ σ ] → VarOK Q A ρ → VarOK Q' (A [ σ ]ᵛ) (ρ [ σ ]ʳ)
VarOK-subst h (et-ok et)  = et-ok (⊩ᴱ-subst h et)
VarOK-subst h (≾ᵘ-ok le)  = ≾ᵘ-ok (⊩-substᵣ h le)
VarOK-subst {σ = σ} h (hyp-ok m p q) = VarOK-≡̂ (≡̂ᵛ-subst σ p) (⊩-substᵣ h q) (⊩disj h m)

<:̂ᵛ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {A A' : OVType Θ}
          → Q' ⊩ᴴ Q [ σ ] → Q ∣ A <:̂ᵛ A' → Q' ∣ A [ σ ]ᵛ <:̂ᵛ A' [ σ ]ᵛ
<:̂ᶜ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {C C' : OCType Θ}
          → Q' ⊩ᴴ Q [ σ ] → Q ∣ C <:̂ᶜ C' → Q' ∣ C [ σ ]ᶜ <:̂ᶜ C' [ σ ]ᶜ

<:̂ᵛ-subst h (tvarₛ p)  = ⊩ᵗᵛ-subst h p
<:̂ᵛ-subst h (Baseₛ p)  = Baseₛ p
<:̂ᵛ-subst h Unitₛ      = Unitₛ
<:̂ᵛ-subst h Boolₛ      = Boolₛ
<:̂ᵛ-subst h Natₛ       = Natₛ
<:̂ᵛ-subst h (p |×|ₛ r) = <:̂ᵛ-subst h p |×|ₛ <:̂ᵛ-subst h r
<:̂ᵛ-subst h Emptyₛ     = Emptyₛ
<:̂ᵛ-subst h (p ⇒ₛ r)   = <:̂ᵛ-subst h p ⇒ₛ <:̂ᶜ-subst h r
<:̂ᵛ-subst h ([ q ]ₛ p) = [ ⊩-substᵣ h q ]ₛ <:̂ᵛ-subst h p

<:̂ᶜ-subst h (p ‼ₛ q) = <:̂ᵛ-subst h p ‼ₛ ⊩-substₑ h q

⊩ᴴ-refl : ∀ {Θ} {Q : Hyps Θ} → Q ⊩ᴴ Q [ idˢ ]
⊩ᴴ-refl {Q = Q} =
  mk⊩ᴴ et-hyp
       (λ m → tvarₛ (hypᵗᵛ m))
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym ([id]ʳ ρ)) (sym ([id]ʳ ρ')) (hypᵣ m))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym ([id]ᵉ ε)) (sym ([id]ᵉ ε')) (hypₑ m))
       (λ {A} {ρ} m →
          subst₂ (VarOK Q) (sym ([id]ᵛ A)) (sym ([id]ʳ ρ)) (hyp-ok₀ m))

-- Entailment between sets over one scope, field by field

mk⊩ᴴ⁼ : ∀ {Θ} {Q Q' : Hyps Θ}
      → (∀ {α} → α ∈ ets Q → Q' ⊩ᴱ tvar α)
      → (∀ {α β} → (α , β) ∈ subᵥ Q → Q' ∣ tvar α <:̂ᵛ tvar β)
      → (∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q' ⊩ ρ ≾̂ᵣ ρ')
      → (∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q' ⊩ ε ≾̂ₑ ε')
      → (∀ {A ρ} → (A , ρ) ∈ disj Q → VarOK Q' A ρ)
      → Q' ⊩ᴴ Q
mk⊩ᴴ⁼ {Q' = Q'} et sb oR oE dj =
  mk⊩ᴴ et sb
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → Q' ⊩ x ≾̂ᵣ y) (sym ([id]ʳ ρ)) (sym ([id]ʳ ρ')) (oR m))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → Q' ⊩ x ≾̂ₑ y) (sym ([id]ᵉ ε)) (sym ([id]ᵉ ε')) (oE m))
       (λ {A} {ρ} m → subst₂ (VarOK Q') (sym ([id]ᵛ A)) (sym ([id]ʳ ρ)) (dj m))

⊩ordᵣ⁼ : ∀ {Θ} {Q Q' : Hyps Θ} → Q' ⊩ᴴ Q
       → ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q' ⊩ ρ ≾̂ᵣ ρ'
⊩ordᵣ⁼ {Q' = Q'} h {ρ} {ρ'} m =
  subst₂ (λ x y → Q' ⊩ x ≾̂ᵣ y) ([id]ʳ ρ) ([id]ʳ ρ') (⊩ordᵣ h m)

⊩ordₑ⁼ : ∀ {Θ} {Q Q' : Hyps Θ} → Q' ⊩ᴴ Q
       → ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q' ⊩ ε ≾̂ₑ ε'
⊩ordₑ⁼ {Q' = Q'} h {ε} {ε'} m =
  subst₂ (λ x y → Q' ⊩ x ≾̂ₑ y) ([id]ᵉ ε) ([id]ᵉ ε') (⊩ordₑ h m)

⊩disj⁼ : ∀ {Θ} {Q Q' : Hyps Θ} → Q' ⊩ᴴ Q
       → ∀ {A ρ} → (A , ρ) ∈ disj Q → VarOK Q' A ρ
⊩disj⁼ {Q' = Q'} h {A} {ρ} m = subst₂ (VarOK Q') ([id]ᵛ A) ([id]ʳ ρ) (⊩disj h m)

-- What a set entails, a set entailing it entails

⊩ᴴ-≾ᵣ : ∀ {Θ} {Q Q' : Hyps Θ} {ρ ρ'} → Q' ⊩ᴴ Q → Q ⊩ ρ ≾̂ᵣ ρ' → Q' ⊩ ρ ≾̂ᵣ ρ'
⊩ᴴ-≾ᵣ {Q' = Q'} {ρ} {ρ'} h p =
  subst₂ (λ x y → Q' ⊩ x ≾̂ᵣ y) ([id]ʳ ρ) ([id]ʳ ρ') (⊩-substᵣ h p)

⊩ᴴ-≾ₑ : ∀ {Θ} {Q Q' : Hyps Θ} {ε ε'} → Q' ⊩ᴴ Q → Q ⊩ ε ≾̂ₑ ε' → Q' ⊩ ε ≾̂ₑ ε'
⊩ᴴ-≾ₑ {Q' = Q'} {ε} {ε'} h p =
  subst₂ (λ x y → Q' ⊩ x ≾̂ₑ y) ([id]ᵉ ε) ([id]ᵉ ε') (⊩-substₑ h p)

⊩ᴴ-VarOK : ∀ {Θ} {Q Q' : Hyps Θ} {A ρ} → Q' ⊩ᴴ Q → VarOK Q A ρ → VarOK Q' A ρ
⊩ᴴ-VarOK {Q' = Q'} {A} {ρ} h ok =
  subst₂ (VarOK Q') ([id]ᵛ A) ([id]ʳ ρ) (VarOK-subst h ok)

-- A set entails each set whose hypotheses it holds

record _⊆ᴴ_ {Θ : Scope} (Q Q' : Hyps Θ) : Set where
  constructor mk⊆ᴴ
  field
    ⊆ets  : ∀ {α} → α ∈ ets Q → α ∈ ets Q'
    ⊆subᵥ : ∀ {p} → p ∈ subᵥ Q → p ∈ subᵥ Q'
    ⊆ordᵣ : ∀ {p} → p ∈ ordᵣ Q → p ∈ ordᵣ Q'
    ⊆ordₑ : ∀ {p} → p ∈ ordₑ Q → p ∈ ordₑ Q'
    ⊆disj : ∀ {p} → p ∈ disj Q → p ∈ disj Q'

open _⊆ᴴ_ public

⊆ᴴ-⊩ : ∀ {Θ} {Q Q' : Hyps Θ} → Q ⊆ᴴ Q' → Q' ⊩ᴴ Q
⊆ᴴ-⊩ s = mk⊩ᴴ⁼ (λ m → et-hyp (⊆ets s m)) (λ m → tvarₛ (hypᵗᵛ (⊆subᵥ s m)))
                (λ m → hypᵣ (⊆ordᵣ s m)) (λ m → hypₑ (⊆ordₑ s m))
                (λ m → hyp-ok₀ (⊆disj s m))

⊩ᴴ-⨟ : ∀ {Θ Θ' Θ''} {Q : Hyps Θ} {Q' : Hyps Θ'} {Q'' : Hyps Θ''}
       {σ : Subst Θ Θ'} {δ : Subst Θ' Θ''}
     → Q'' ⊩ᴴ Q' [ δ ] → Q' ⊩ᴴ Q [ σ ] → Q'' ⊩ᴴ Q [ σ ⨟ˢ δ ]
⊩ᴴ-⨟ {Q'' = Q''} {σ = σ} {δ = δ} h' h =
  mk⊩ᴴ (λ m → ⊩ᴱ-subst h' (⊩ets h m))
       (λ m → <:̂ᵛ-subst h' (⊩subᵥ h m))
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → Q'' ⊩ x ≾̂ᵣ y) ([⨟]ʳ ρ σ δ) ([⨟]ʳ ρ' σ δ)
                 (⊩-substᵣ h' (⊩ordᵣ h m)))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → Q'' ⊩ x ≾̂ₑ y) ([⨟]ᵉ ε σ δ) ([⨟]ᵉ ε' σ δ)
                 (⊩-substₑ h' (⊩ordₑ h m)))
       (λ {A} {ρ} m →
          subst₂ (VarOK Q'') ([⨟]ᵛ A σ δ) ([⨟]ʳ ρ σ δ)
                 (VarOK-subst h' (⊩disj h m)))

⊩ᴴ-trans : ∀ {Θ} {Q Q' Q'' : Hyps Θ} → Q'' ⊩ᴴ Q' → Q' ⊩ᴴ Q → Q'' ⊩ᴴ Q
⊩ᴴ-trans h' h = ⊩ᴴ-⨟ h' h

-- Entailment along a substitution depends only on its images

⊩ᴴ-≐ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ σ' : Subst Θ Θ'}
     → σ ≐ˢ σ' → Q' ⊩ᴴ Q [ σ ] → Q' ⊩ᴴ Q [ σ' ]
⊩ᴴ-≐ {Q' = Q'} p h =
  mk⊩ᴴ (λ {α} m → subst (Q' ⊩ᴱ_) (≐ᵗ p α) (⊩ets h m))
       (λ {α} {β} m → subst₂ (λ x y → Q' ∣ x <:̂ᵛ y) (≐ᵗ p α) (≐ᵗ p β) (⊩subᵥ h m))
       (λ {ρ} {ρ'} m → subst₂ (λ x y → Q' ⊩ x ≾̂ᵣ y) ([≐]ʳ p ρ) ([≐]ʳ p ρ') (⊩ordᵣ h m))
       (λ {ε} {ε'} m → subst₂ (λ x y → Q' ⊩ x ≾̂ₑ y) ([≐]ᵉ p ε) ([≐]ᵉ p ε') (⊩ordₑ h m))
       (λ {A} {ρ} m → subst₂ (VarOK Q') ([≐]ᵛ p A) ([≐]ʳ p ρ) (⊩disj h m))

-- Weakening a hypothesis set is the action of the weakening substitution,
-- so entailment is stable under it.

⊩ᴴ-wkᵗ : ∀ {Θ} {Q : Hyps Θ} → wkᵗ-H Q ⊩ᴴ Q [ wkˢᵗ ]
⊩ᴴ-wkᵗ {Θ} {Q} =
  mk⊩ᴴ (λ m → et-hyp (∈-map⁺ (wkᵗ-tv Θ) m))
       (λ m → tvarₛ (hypᵗᵛ (∈-map⁺ (mapᵖ (wkᵗ-tv Θ)) m)))
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → wkᵗ-H Q ⊩ x ≾̂ᵣ y) (sym (wkˢᵗ-r ρ)) (sym (wkˢᵗ-r ρ'))
                 (hypᵣ (∈-map⁺ (mapᵖ wkᵗ-r) m)))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → wkᵗ-H Q ⊩ x ≾̂ₑ y) (sym (wkˢᵗ-e ε)) (sym (wkˢᵗ-e ε'))
                 (hypₑ (∈-map⁺ (mapᵖ wkᵗ-e) m)))
       (λ {A} {ρ} m →
          subst₂ (VarOK (wkᵗ-H Q)) (sym (wkˢᵗ-v A)) (sym (wkˢᵗ-r ρ))
                 (hyp-ok₀ (∈-map⁺ (mapᵈ wkᵗ-v wkᵗ-r) m)))

⊩ᴴ-wkʳ : ∀ {Θ} {Q : Hyps Θ} → wkʳ-H Q ⊩ᴴ Q [ wkˢʳ ]
⊩ᴴ-wkʳ {Θ} {Q} =
  mk⊩ᴴ (λ m → et-hyp (∈-map⁺ (wkʳ-tv Θ) m))
       (λ m → tvarₛ (hypᵗᵛ (∈-map⁺ (mapᵖ (wkʳ-tv Θ)) m)))
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → wkʳ-H Q ⊩ x ≾̂ᵣ y) (sym (wkˢʳ-r ρ)) (sym (wkˢʳ-r ρ'))
                 (hypᵣ (∈-map⁺ (mapᵖ wkʳ-r) m)))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → wkʳ-H Q ⊩ x ≾̂ₑ y) (sym (wkˢʳ-e ε)) (sym (wkˢʳ-e ε'))
                 (hypₑ (∈-map⁺ (mapᵖ wkʳ-e) m)))
       (λ {A} {ρ} m →
          subst₂ (VarOK (wkʳ-H Q)) (sym (wkˢʳ-v A)) (sym (wkˢʳ-r ρ))
                 (hyp-ok₀ (∈-map⁺ (mapᵈ wkʳ-v wkʳ-r) m)))

⊩ᴴ-wkᵉ : ∀ {Θ} {Q : Hyps Θ} → wkᵉ-H Q ⊩ᴴ Q [ wkˢᵉ ]
⊩ᴴ-wkᵉ {Θ} {Q} =
  mk⊩ᴴ (λ m → et-hyp (∈-map⁺ (wkᵉ-tv Θ) m))
       (λ m → tvarₛ (hypᵗᵛ (∈-map⁺ (mapᵖ (wkᵉ-tv Θ)) m)))
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y) (sym (wkˢᵉ-r ρ)) (sym (wkˢᵉ-r ρ'))
                 (hypᵣ (∈-map⁺ (mapᵖ wkᵉ-r) m)))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y) (sym (wkˢᵉ-e ε)) (sym (wkˢᵉ-e ε'))
                 (hypₑ (∈-map⁺ (mapᵖ wkᵉ-e) m)))
       (λ {A} {ρ} m →
          subst₂ (VarOK (wkᵉ-H Q)) (sym (wkˢᵉ-v A)) (sym (wkˢᵉ-r ρ))
                 (hyp-ok₀ (∈-map⁺ (mapᵈ wkᵉ-v wkᵉ-r) m)))

-- Entailment is preserved by the scope extensions

⊩-wkᵗᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ ≾̂ᵣ ρ' → wkᵗ-H Q ⊩ wkᵗ-r ρ ≾̂ᵣ wkᵗ-r ρ'
⊩-wkᵗᵣ {Q = Q} {ρ} {ρ'} p =
  subst₂ (λ x y → wkᵗ-H Q ⊩ x ≾̂ᵣ y) (wkˢᵗ-r ρ) (wkˢᵗ-r ρ') (⊩-substᵣ ⊩ᴴ-wkᵗ p)

⊩-wkᵗₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → wkᵗ-H Q ⊩ wkᵗ-e ε ≾̂ₑ wkᵗ-e ε'
⊩-wkᵗₑ {Q = Q} {ε} {ε'} p =
  subst₂ (λ x y → wkᵗ-H Q ⊩ x ≾̂ₑ y) (wkˢᵗ-e ε) (wkˢᵗ-e ε') (⊩-substₑ ⊩ᴴ-wkᵗ p)

⊩ᴱ-wkᵗ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ⊩ᴱ A → wkᵗ-H Q ⊩ᴱ wkᵗ-v A
⊩ᴱ-wkᵗ {Q = Q} {A} et =
  subst (λ x → wkᵗ-H Q ⊩ᴱ x) (wkˢᵗ-v A) (⊩ᴱ-subst ⊩ᴴ-wkᵗ et)

<:̂ᵛ-wkᵗ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkᵗ-H Q ∣ wkᵗ-v A <:̂ᵛ wkᵗ-v A'
<:̂ᵛ-wkᵗ {Q = Q} {A} {A'} p =
  subst₂ (wkᵗ-H Q ∣_<:̂ᵛ_) (wkˢᵗ-v A) (wkˢᵗ-v A') (<:̂ᵛ-subst ⊩ᴴ-wkᵗ p)

⊩-wkʳᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ ≾̂ᵣ ρ' → wkʳ-H Q ⊩ wkʳ-r ρ ≾̂ᵣ wkʳ-r ρ'
⊩-wkʳᵣ {Q = Q} {ρ} {ρ'} p =
  subst₂ (λ x y → wkʳ-H Q ⊩ x ≾̂ᵣ y) (wkˢʳ-r ρ) (wkˢʳ-r ρ') (⊩-substᵣ ⊩ᴴ-wkʳ p)

⊩-wkʳₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → wkʳ-H Q ⊩ wkʳ-e ε ≾̂ₑ wkʳ-e ε'
⊩-wkʳₑ {Q = Q} {ε} {ε'} p =
  subst₂ (λ x y → wkʳ-H Q ⊩ x ≾̂ₑ y) (wkˢʳ-e ε) (wkˢʳ-e ε') (⊩-substₑ ⊩ᴴ-wkʳ p)

⊩ᴱ-wkʳ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ⊩ᴱ A → wkʳ-H Q ⊩ᴱ wkʳ-v A
⊩ᴱ-wkʳ {Q = Q} {A} et =
  subst (λ x → wkʳ-H Q ⊩ᴱ x) (wkˢʳ-v A) (⊩ᴱ-subst ⊩ᴴ-wkʳ et)

<:̂ᵛ-wkʳ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkʳ-H Q ∣ wkʳ-v A <:̂ᵛ wkʳ-v A'
<:̂ᵛ-wkʳ {Q = Q} {A} {A'} p =
  subst₂ (wkʳ-H Q ∣_<:̂ᵛ_) (wkˢʳ-v A) (wkˢʳ-v A') (<:̂ᵛ-subst ⊩ᴴ-wkʳ p)

⊩-wkᵉᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ ≾̂ᵣ ρ' → wkᵉ-H Q ⊩ wkᵉ-r ρ ≾̂ᵣ wkᵉ-r ρ'
⊩-wkᵉᵣ {Q = Q} {ρ} {ρ'} p =
  subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y) (wkˢᵉ-r ρ) (wkˢᵉ-r ρ') (⊩-substᵣ ⊩ᴴ-wkᵉ p)

⊩-wkᵉₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → wkᵉ-H Q ⊩ wkᵉ-e ε ≾̂ₑ wkᵉ-e ε'
⊩-wkᵉₑ {Q = Q} {ε} {ε'} p =
  subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y) (wkˢᵉ-e ε) (wkˢᵉ-e ε') (⊩-substₑ ⊩ᴴ-wkᵉ p)

⊩ᴱ-wkᵉ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ⊩ᴱ A → wkᵉ-H Q ⊩ᴱ wkᵉ-v A
⊩ᴱ-wkᵉ {Q = Q} {A} et =
  subst (λ x → wkᵉ-H Q ⊩ᴱ x) (wkˢᵉ-v A) (⊩ᴱ-subst ⊩ᴴ-wkᵉ et)

VarOK-wkᵉ : ∀ {Θ} {Q : Hyps Θ} {A ρ}
          → VarOK Q A ρ → VarOK (wkᵉ-H Q) (wkᵉ-v A) (wkᵉ-r ρ)
VarOK-wkᵉ {Q = Q} {A} {ρ} ok =
  subst₂ (VarOK (wkᵉ-H Q)) (wkˢᵉ-v A) (wkˢᵉ-r ρ) (VarOK-subst ⊩ᴴ-wkᵉ ok)

<:̂ᵛ-wkᵉ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkᵉ-H Q ∣ wkᵉ-v A <:̂ᵛ wkᵉ-v A'
<:̂ᵛ-wkᵉ {Q = Q} {A} {A'} p =
  subst₂ (wkᵉ-H Q ∣_<:̂ᵛ_) (wkˢᵉ-v A) (wkˢᵉ-v A') (<:̂ᵛ-subst ⊩ᴴ-wkᵉ p)

-- Grade expressions are monotone in their variables: every former is,
-- so two substitutions ordered pointwise on the grade variables order
-- the images of every grade expression the same way.

infix 4 _⊩_≾ˢ_

record _⊩_≾ˢ_ {Θ Θ' : Scope} (Q : Hyps Θ') (σ τ : Subst Θ Θ') : Set where
  constructor mk≾ˢ
  field
    ≾ˢʳ : (i : RVar Θ) → Q ⊩ sR σ i ≾̂ᵣ sR τ i
    ≾ˢᵉ : (i : EVar Θ) → Q ⊩ sE σ i ≾̂ₑ sE τ i

open _⊩_≾ˢ_ public

⊩-⊔̂ᵣ-mono : ∀ {Θ} {Q : Hyps Θ} {ρ₁ ρ₁' ρ₂ ρ₂'}
          → Q ⊩ ρ₁ ≾̂ᵣ ρ₁' → Q ⊩ ρ₂ ≾̂ᵣ ρ₂' → Q ⊩ ρ₁ ⊔̂ᵣ ρ₂ ≾̂ᵣ ρ₁' ⊔̂ᵣ ρ₂'
⊩-⊔̂ᵣ-mono p q = ⊔-lubᵣ (transᵣ p ⊔-ubˡᵣ) (transᵣ q ⊔-ubʳᵣ)

⊩-⊔̂ₑ-mono : ∀ {Θ} {Q : Hyps Θ} {ε₁ ε₁' ε₂ ε₂'}
          → Q ⊩ ε₁ ≾̂ₑ ε₁' → Q ⊩ ε₂ ≾̂ₑ ε₂' → Q ⊩ ε₁ ⊔̂ₑ ε₂ ≾̂ₑ ε₁' ⊔̂ₑ ε₂'
⊩-⊔̂ₑ-mono p q = ⊔-lubₑ (transₑ p ⊔-ubˡₑ) (transₑ q ⊔-ubʳₑ)

mono-substₑ : ∀ {Θ Θ'} {Q : Hyps Θ'} {σ τ : Subst Θ Θ'}
            → Q ⊩ σ ≾ˢ τ → (ε : EExp Θ) → Q ⊩ ε [ σ ]ᵉ ≾̂ₑ ε [ τ ]ᵉ
mono-substₑ p (evar i)   = ≾ˢᵉ p i
mono-substₑ p (econst c) = ⊩≾̂ₑ-refl
mono-substₑ p (ε ·̂ₑ ε')  = monoₑ (mono-substₑ p ε) (mono-substₑ p ε')
mono-substₑ p (ε ⊔̂ₑ ε')  = ⊩-⊔̂ₑ-mono (mono-substₑ p ε) (mono-substₑ p ε')

mono-substᵣ : ∀ {Θ Θ'} {Q : Hyps Θ'} {σ τ : Subst Θ Θ'}
            → Q ⊩ σ ≾ˢ τ → (ρ : RExp Θ) → Q ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ [ τ ]ʳ
mono-substᵣ p (rvar i)   = ≾ˢʳ p i
mono-substᵣ p (rconst c) = ⊩≾̂ᵣ-refl
mono-substᵣ p (ρ ·̂ᵣ ρ')  = monoᵣ (mono-substᵣ p ρ) (mono-substᵣ p ρ')
mono-substᵣ p (ρ ⊔̂ᵣ ρ')  = ⊩-⊔̂ᵣ-mono (mono-substᵣ p ρ) (mono-substᵣ p ρ')
mono-substᵣ p ∣ ε ∣̂ᵉ     = map-mono (mono-substₑ p ε)

-- Composing with the identity changes no image

≾ˢ-idˡ : ∀ {Θ Θ'} {Q : Hyps Θ'} {σ τ : Subst Θ Θ'} → Q ⊩ (σ ⨟ˢ idˢ) ≾ˢ τ → Q ⊩ σ ≾ˢ τ
≾ˢ-idˡ {Q = Q} {σ} {τ} p =
  mk≾ˢ (λ i → subst (λ x → Q ⊩ x ≾̂ᵣ sR τ i) ([id]ʳ (sR σ i)) (≾ˢʳ p i))
       (λ i → subst (λ x → Q ⊩ x ≾̂ₑ sE τ i) ([id]ᵉ (sE σ i)) (≾ˢᵉ p i))

≾ˢ-idʳ : ∀ {Θ Θ'} {Q : Hyps Θ'} {σ τ : Subst Θ Θ'} → Q ⊩ τ ≾ˢ (σ ⨟ˢ idˢ) → Q ⊩ τ ≾ˢ σ
≾ˢ-idʳ {Q = Q} {σ} {τ} p =
  mk≾ˢ (λ i → subst (λ x → Q ⊩ sR τ i ≾̂ᵣ x) ([id]ʳ (sR σ i)) (≾ˢʳ p i))
       (λ i → subst (λ x → Q ⊩ sE τ i ≾̂ₑ x) ([id]ᵉ (sE σ i)) (≾ˢᵉ p i))

-- An assignment below (above) the unknown's own value lowers (raises)
-- the substitution pointwise

updᵉ-below : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (k : EVar Ψ) → (b : EExp Ψ) → (τ : Subst Ψ Ψ')
           → Q ⊩ b [ τ ]ᵉ ≾̂ₑ sE τ k → Q ⊩ (updᵉ k b ⨟ˢ τ) ≾ˢ τ
updᵉ-below {Ψ} {Q = Q} k b τ p = mk≾ˢ (λ i → ⊩≾̂ᵣ-refl) e
  where
    e : (i : EVar Ψ) → Q ⊩ sE (updᵉ k b) i [ τ ]ᵉ ≾̂ₑ sE τ i
    e i with i ≟ᶠ k
    ... | yes refl = p
    ... | no _     = ⊩≾̂ₑ-refl

updᵉ-above : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (k : EVar Ψ) → (b : EExp Ψ) → (τ : Subst Ψ Ψ')
           → Q ⊩ sE τ k ≾̂ₑ b [ τ ]ᵉ → Q ⊩ τ ≾ˢ (updᵉ k b ⨟ˢ τ)
updᵉ-above {Ψ} {Q = Q} k b τ p = mk≾ˢ (λ i → ⊩≾̂ᵣ-refl) e
  where
    e : (i : EVar Ψ) → Q ⊩ sE τ i ≾̂ₑ sE (updᵉ k b) i [ τ ]ᵉ
    e i with i ≟ᶠ k
    ... | yes refl = p
    ... | no _     = ⊩≾̂ₑ-refl

updʳ-below : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (k : RVar Ψ) → (b : RExp Ψ) → (τ : Subst Ψ Ψ')
           → Q ⊩ b [ τ ]ʳ ≾̂ᵣ sR τ k → Q ⊩ (updʳ k b ⨟ˢ τ) ≾ˢ τ
updʳ-below {Ψ} {Q = Q} k b τ p = mk≾ˢ r (λ i → ⊩≾̂ₑ-refl)
  where
    r : (i : RVar Ψ) → Q ⊩ sR (updʳ k b) i [ τ ]ʳ ≾̂ᵣ sR τ i
    r i with i ≟ᶠ k
    ... | yes refl = p
    ... | no _     = ⊩≾̂ᵣ-refl

updʳ-above : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (k : RVar Ψ) → (b : RExp Ψ) → (τ : Subst Ψ Ψ')
           → Q ⊩ sR τ k ≾̂ᵣ b [ τ ]ʳ → Q ⊩ τ ≾ˢ (updʳ k b ⨟ˢ τ)
updʳ-above {Ψ} {Q = Q} k b τ p = mk≾ˢ r (λ i → ⊩≾̂ₑ-refl)
  where
    r : (i : RVar Ψ) → Q ⊩ sR τ i ≾̂ᵣ sR (updʳ k b) i [ τ ]ʳ
    r i with i ≟ᶠ k
    ... | yes refl = p
    ... | no _     = ⊩≾̂ᵣ-refl

-- Equality relative to a hypothesis set: entailed ordering both ways

infix 4 _⊩_≡̂ᵣ_ _⊩_≡̂ₑ_

_⊩_≡̂ᵣ_ : ∀ {Θ} → Hyps Θ → RExp Θ → RExp Θ → Set
Q ⊩ ρ ≡̂ᵣ ρ' = (Q ⊩ ρ ≾̂ᵣ ρ') × (Q ⊩ ρ' ≾̂ᵣ ρ)

_⊩_≡̂ₑ_ : ∀ {Θ} → Hyps Θ → EExp Θ → EExp Θ → Set
Q ⊩ ε ≡̂ₑ ε' = (Q ⊩ ε ≾̂ₑ ε') × (Q ⊩ ε' ≾̂ₑ ε)

⊩≡̂ᵣ-refl : ∀ {Θ} {Q : Hyps Θ} {ρ} → Q ⊩ ρ ≡̂ᵣ ρ
⊩≡̂ᵣ-refl = ⊩≾̂ᵣ-refl , ⊩≾̂ᵣ-refl

⊩≡̂ᵣ-sym : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ ≡̂ᵣ ρ' → Q ⊩ ρ' ≡̂ᵣ ρ
⊩≡̂ᵣ-sym (p , q) = q , p

⊩≡̂ᵣ-trans : ∀ {Θ} {Q : Hyps Θ} {ρ ρ' ρ''}
           → Q ⊩ ρ ≡̂ᵣ ρ' → Q ⊩ ρ' ≡̂ᵣ ρ'' → Q ⊩ ρ ≡̂ᵣ ρ''
⊩≡̂ᵣ-trans (p , q) (p' , q') = transᵣ p p' , transᵣ q' q

⊩≡̂ₑ-refl : ∀ {Θ} {Q : Hyps Θ} {ε} → Q ⊩ ε ≡̂ₑ ε
⊩≡̂ₑ-refl = ⊩≾̂ₑ-refl , ⊩≾̂ₑ-refl

⊩≡̂ₑ-sym : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε ≡̂ₑ ε' → Q ⊩ ε' ≡̂ₑ ε
⊩≡̂ₑ-sym (p , q) = q , p

⊩≡̂ₑ-trans : ∀ {Θ} {Q : Hyps Θ} {ε ε' ε''}
           → Q ⊩ ε ≡̂ₑ ε' → Q ⊩ ε' ≡̂ₑ ε'' → Q ⊩ ε ≡̂ₑ ε''
⊩≡̂ₑ-trans (p , q) (p' , q') = transₑ p p' , transₑ q' q

-- Congruence for the formers

⊩≡̂ᵣ-cong : ∀ {Θ} {Q : Hyps Θ} {ρ₁ ρ₁' ρ₂ ρ₂'}
          → Q ⊩ ρ₁ ≡̂ᵣ ρ₁' → Q ⊩ ρ₂ ≡̂ᵣ ρ₂' → Q ⊩ ρ₁ ·̂ᵣ ρ₂ ≡̂ᵣ ρ₁' ·̂ᵣ ρ₂'
⊩≡̂ᵣ-cong (p , q) (p' , q') = monoᵣ p p' , monoᵣ q q'

⊩≡̂ᵣ-cong-⊔ : ∀ {Θ} {Q : Hyps Θ} {ρ₁ ρ₁' ρ₂ ρ₂'}
            → Q ⊩ ρ₁ ≡̂ᵣ ρ₁' → Q ⊩ ρ₂ ≡̂ᵣ ρ₂' → Q ⊩ ρ₁ ⊔̂ᵣ ρ₂ ≡̂ᵣ ρ₁' ⊔̂ᵣ ρ₂'
⊩≡̂ᵣ-cong-⊔ (p , q) (p' , q') = ⊩-⊔̂ᵣ-mono p p' , ⊩-⊔̂ᵣ-mono q q'

⊩≡̂ᵣ-map-cong : ∀ {Θ} {Q : Hyps Θ} {ε ε'}
              → Q ⊩ ε ≡̂ₑ ε' → Q ⊩ ∣ ε ∣̂ᵉ ≡̂ᵣ ∣ ε' ∣̂ᵉ
⊩≡̂ᵣ-map-cong (p , q) = map-mono p , map-mono q

⊩≡̂ₑ-cong : ∀ {Θ} {Q : Hyps Θ} {ε₁ ε₁' ε₂ ε₂'}
          → Q ⊩ ε₁ ≡̂ₑ ε₁' → Q ⊩ ε₂ ≡̂ₑ ε₂' → Q ⊩ ε₁ ·̂ₑ ε₂ ≡̂ₑ ε₁' ·̂ₑ ε₂'
⊩≡̂ₑ-cong (p , q) (p' , q') = monoₑ p p' , monoₑ q q'

⊩≡̂ₑ-cong-⊔ : ∀ {Θ} {Q : Hyps Θ} {ε₁ ε₁' ε₂ ε₂'}
            → Q ⊩ ε₁ ≡̂ₑ ε₁' → Q ⊩ ε₂ ≡̂ₑ ε₂' → Q ⊩ ε₁ ⊔̂ₑ ε₂ ≡̂ₑ ε₁' ⊔̂ₑ ε₂'
⊩≡̂ₑ-cong-⊔ (p , q) (p' , q') = ⊩-⊔̂ₑ-mono p p' , ⊩-⊔̂ₑ-mono q q'

-- Convertibility is equality under any hypotheses

⊩≡̂ᵣ-reflexive : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → ρ ≡̂ᵣ ρ' → Q ⊩ ρ ≡̂ᵣ ρ'
⊩≡̂ᵣ-reflexive p = eqᵣ p , eqᵣ (≡̂ᵣ-sym p)

⊩≡̂ₑ-reflexive : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → ε ≡̂ₑ ε' → Q ⊩ ε ≡̂ₑ ε'
⊩≡̂ₑ-reflexive p = eqₑ p , eqₑ (≡̂ₑ-sym p)

-- Under the empty set, equality is convertibility

⊩≡̂ᵣ-∅ : ∀ {Θ} {ρ ρ' : RExp Θ} → ∅ᴴ ⊩ ρ ≡̂ᵣ ρ' → ρ ≡̂ᵣ ρ'
⊩≡̂ᵣ-∅ (p , q) = ≡̂ᵣ-antisym-∅ p q

⊩≡̂ₑ-∅ : ∀ {Θ} {ε ε' : EExp Θ} → ∅ᴴ ⊩ ε ≡̂ₑ ε' → ε ≡̂ₑ ε'
⊩≡̂ₑ-∅ (p , q) = ≡̂ₑ-antisym-∅ p q
