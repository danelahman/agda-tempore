------------------------------------------------------------------
-- Hypotheses and entailment of the polymorphic calculus        --
--                                                              --
-- A hypothesis set `Hyps Θ` holds eternality atoms and         --
-- subtyping atoms on type variables, orderings between open    --
-- grade expressions, var-rule disjunctions and quantified      --
-- orderings (`Quantified`).                                    --
--                                                              --
-- Grade entailment (`_⊩_≾̂ᵣ_`, `_⊩_≾̂ₑ_`) is semantic          --
-- consequence in the grade system: an ordering holds by value  --
-- at every closed instance satisfying the grade part of the    --
-- set (`_⊨ᵍ_`). Convertibility (`_≡̂ᵣ_`, `_≡̂ₑ_`) is           --
-- entailment both ways from no hypotheses. The rules of grade  --
-- entailment are its properties: the laws of the grade         --
-- algebras and the zero-product laws, instances of quantified  --
-- hypotheses (`instᵣ`, `instₑ`: rule Inst) and of closed       --
-- orderings valid at no hypotheses (`factᵣ`, `factₑ`: rule     --
-- Truth).                                                      --
--                                                              --
-- Eternality, subtyping and the var-rule disjunction (`_⊩ᴱ_`,  --
-- `_∣_<:̂ᵛ_`, `VarOK`) are inductive over grade entailment. A  --
-- quantified ordering is entailed at fresh rigids (`_⊩ᴼ_[_]`:  --
-- rule Gen), which is semantic consequence (`⊩ᴼ⇒⊨ᴼ`, `⊨ᴼ⇒⊩ᴼ`). --
-- Entailment is stable under substitution along an instance    --
-- map (`_⊩ᴵ_[_]`).                                             --
--                                                              --
-- Judgements under a hypothesis set are the constrained types  --
-- of HM(X) (Odersky, Sulzmann and Wehr); the set plays the     --
-- role of the givens of OutsideIn(X).                          --
------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_; map; _++_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_) renaming (map to mapᵛ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe using (Is-just)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to Any-just)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)

open import Algebra.Definitions using (Commutative)
open import Relation.Binary.Definitions using (Minimum)
open import Relation.Nullary using (yes; no)

open import Grades.Base
open import Language.BaseTypes using (module BaseTypes)
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Hypotheses (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

-- The eternal base types

open BaseTypes BTs using (EternalBaseType)

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses.Quantified S public

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
    qhyps : List (QOrd Θ)                     -- assumed quantified orderings

open Hyps public

-- Empty hypothesis set

∅ᴴ : ∀ {Θ} → Hyps Θ
∅ᴴ = hyps [] [] [] [] [] []

-- A set without quantified hypotheses

record Unq {Θ : Scope} (Q : Hyps Θ) : Set where
  constructor unq
  field
    no-qhyps : qhyps Q ≡ []

open Unq public

-- A quantified hypothesis of such a set, absurd

unq-qhyps : ∀ {Θ} {Q : Hyps Θ} {O} {X : Set} → Unq Q → O ∈ qhyps Q → X
unq-qhyps {Q = Q} {O} u m with qhyps Q | no-qhyps u
unq-qhyps u () | _ | refl

-- Componentwise action on a type-and-grade pair

mapᵈ : ∀ {Θ Θ'} → (OVType Θ → OVType Θ') → (RExp Θ → RExp Θ')
     → OVType Θ × RExp Θ → OVType Θ' × RExp Θ'
mapᵈ f g (A , ρ) = f A , g ρ

-- Quantified hypotheses added to a set

infixl 5 _++ᵠ_

_++ᵠ_ : ∀ {Θ} → Hyps Θ → List (QOrd Θ) → Hyps Θ
Q ++ᵠ R = record Q { qhyps = qhyps Q ++ R }

-- Action of the scope extensions on hypothesis sets

wkᵗ-H : ∀ {Θ} → Hyps Θ → Hyps (Θ +ty)
wkᵗ-H {Θ} Q = hyps (map (wkᵗ-tv Θ) (ets Q))
                   (map (mapᵖ (wkᵗ-tv Θ)) (subᵥ Q))
                   (map (mapᵖ wkᵗ-r) (ordᵣ Q))
                   (map (mapᵖ wkᵗ-e) (ordₑ Q))
                   (map (mapᵈ wkᵗ-v wkᵗ-r) (disj Q))
                   (map (_[ wkˢᵗ ]ᵠ) (qhyps Q))

wkʳ-H : ∀ {Θ} → Hyps Θ → Hyps (Θ +r)
wkʳ-H {Θ} Q = hyps (map (wkʳ-tv Θ) (ets Q))
                   (map (mapᵖ (wkʳ-tv Θ)) (subᵥ Q))
                   (map (mapᵖ wkʳ-r) (ordᵣ Q))
                   (map (mapᵖ wkʳ-e) (ordₑ Q))
                   (map (mapᵈ wkʳ-v wkʳ-r) (disj Q))
                   (map (_[ wkˢʳ ]ᵠ) (qhyps Q))

wkᵉ-H : ∀ {Θ} → Hyps Θ → Hyps (Θ +e)
wkᵉ-H {Θ} Q = hyps (map (wkᵉ-tv Θ) (ets Q))
                   (map (mapᵖ (wkᵉ-tv Θ)) (subᵥ Q))
                   (map (mapᵖ wkᵉ-r) (ordᵣ Q))
                   (map (mapᵖ wkᵉ-e) (ordₑ Q))
                   (map (mapᵈ wkᵉ-v wkᵉ-r) (disj Q))
                   (map (_[ wkˢᵉ ]ᵠ) (qhyps Q))

-- Weakening by the rigids of a quantified ordering

wkᵉⁿ-H : ∀ {Θ} → (k : ℕ) → Hyps Θ → Hyps (Θ +eⁿ k)
wkᵉⁿ-H zero    Q = Q
wkᵉⁿ-H (suc k) Q = wkᵉⁿ-H k (wkᵉ-H Q)

-- Assumed subtyping between type variables, closed under reflexivity
-- and transitivity

infix 4 _⊩ᵗᵛ_≾_

data _⊩ᵗᵛ_≾_ {Θ : Scope} (Q : Hyps Θ) : TyVar Θ → TyVar Θ → Set where
  reflᵗᵛ  : ∀ {α} → Q ⊩ᵗᵛ α ≾ α
  hypᵗᵛ   : ∀ {α β} → (α , β) ∈ subᵥ Q → Q ⊩ᵗᵛ α ≾ β
  transᵗᵛ : ∀ {α β γ} → Q ⊩ᵗᵛ α ≾ β → Q ⊩ᵗᵛ β ≾ γ → Q ⊩ᵗᵛ α ≾ γ

------------------------------------------------------------------------
-- Grade entailment: semantic consequence in the grade system

-- A closed instance satisfies grade orderings when each holds by value

infix 4 _⊨ᵒ_ _⊨ᵍ_

record _⊨ᵒ_ {Ψ : Scope} (δ : Subst Ψ ∅ˢ) (o : Ords Ψ) : Set where
  constructor mk⊨ᵒ
  field
    ⊨ᵒʳ : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors o → valʳ (ρ [ δ ]ʳ) ≾ᵣ valʳ (ρ' [ δ ]ʳ)
    ⊨ᵒᵉ : ∀ {ε ε'} → (ε , ε') ∈ oes o → valᵉ (ε [ δ ]ᵉ) ≾ₑ valᵉ (ε' [ δ ]ᵉ)

open _⊨ᵒ_ public

-- A closed instance satisfies the grade part of a set when its
-- orderings hold by value and its quantified orderings at every instance
-- of their rigids

record _⊨ᵍ_ {Θ : Scope} (δ : Subst Θ ∅ˢ) (Q : Hyps Θ) : Set where
  constructor mk⊨ᵍ
  field
    ⊨ᵍʳ : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → valʳ (ρ [ δ ]ʳ) ≾ᵣ valʳ (ρ' [ δ ]ʳ)
    ⊨ᵍᵉ : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → valᵉ (ε [ δ ]ᵉ) ≾ₑ valᵉ (ε' [ δ ]ᵉ)
    ⊨ᵍᵠ : ∀ {O} → O ∈ qhyps Q → (es : Vec (EExp ∅ˢ) (rigids O)) → (δ ,ᵉⁿ es) ⊨ᵒ body O

open _⊨ᵍ_ public

⊨ᵍ-∅ : ∀ {Θ} {δ : Subst Θ ∅ˢ} → δ ⊨ᵍ ∅ᴴ
⊨ᵍ-∅ = mk⊨ᵍ (λ ()) (λ ()) (λ ())

-- Entailed ordering: the ordering holds by value at every closed
-- instance satisfying the grade part of the set

infix 4 _≡̂ᵣ_ _≡̂ₑ_ _⊩_≾̂ᵣ_ _⊩_≾̂ₑ_

record _⊩_≾̂ᵣ_ {Θ : Scope} (Q : Hyps Θ) (ρ ρ' : RExp Θ) : Set where
  constructor semᵣ
  field
    runᵣ : (δ : Subst Θ ∅ˢ) → δ ⊨ᵍ Q → valʳ (ρ [ δ ]ʳ) ≾ᵣ valʳ (ρ' [ δ ]ʳ)

open _⊩_≾̂ᵣ_ public

record _⊩_≾̂ₑ_ {Θ : Scope} (Q : Hyps Θ) (ε ε' : EExp Θ) : Set where
  constructor semₑ
  field
    runₑ : (δ : Subst Θ ∅ˢ) → δ ⊨ᵍ Q → valᵉ (ε [ δ ]ᵉ) ≾ₑ valᵉ (ε' [ δ ]ᵉ)

open _⊩_≾̂ₑ_ public

-- Convertibility: entailment from no hypotheses, both ways

record _≡̂ᵣ_ {Θ : Scope} (ρ ρ' : RExp Θ) : Set where
  constructor mk≡̂ᵣ
  field
    ≡̂ᵣ⇒≾ : ∅ᴴ ⊩ ρ ≾̂ᵣ ρ'
    ≡̂ᵣ⇒≿ : ∅ᴴ ⊩ ρ' ≾̂ᵣ ρ

open _≡̂ᵣ_ public

record _≡̂ₑ_ {Θ : Scope} (ε ε' : EExp Θ) : Set where
  constructor mk≡̂ₑ
  field
    ≡̂ₑ⇒≾ : ∅ᴴ ⊩ ε ≾̂ₑ ε'
    ≡̂ₑ⇒≿ : ∅ᴴ ⊩ ε' ≾̂ₑ ε

open _≡̂ₑ_ public

-- Convertible expressions have equivalent values at every closed
-- instance, and conversely

≡̂ᵣ-run : ∀ {Θ} {ρ ρ' : RExp Θ} → ρ ≡̂ᵣ ρ' → (δ : Subst Θ ∅ˢ)
       → valʳ (ρ [ δ ]ʳ) ≃ᵣ valʳ (ρ' [ δ ]ʳ)
≡̂ᵣ-run p δ = runᵣ (≡̂ᵣ⇒≾ p) δ ⊨ᵍ-∅ , runᵣ (≡̂ᵣ⇒≿ p) δ ⊨ᵍ-∅

≡̂ₑ-run : ∀ {Θ} {ε ε' : EExp Θ} → ε ≡̂ₑ ε' → (δ : Subst Θ ∅ˢ)
       → valᵉ (ε [ δ ]ᵉ) ≃ₑ valᵉ (ε' [ δ ]ᵉ)
≡̂ₑ-run p δ = runₑ (≡̂ₑ⇒≾ p) δ ⊨ᵍ-∅ , runₑ (≡̂ₑ⇒≿ p) δ ⊨ᵍ-∅

≡̂ᵣ-val : ∀ {Θ} {ρ ρ' : RExp Θ}
       → ((δ : Subst Θ ∅ˢ) → valʳ (ρ [ δ ]ʳ) ≃ᵣ valʳ (ρ' [ δ ]ʳ)) → ρ ≡̂ᵣ ρ'
≡̂ᵣ-val f = mk≡̂ᵣ (semᵣ λ δ _ → proj₁ (f δ)) (semᵣ λ δ _ → proj₂ (f δ))

≡̂ₑ-val : ∀ {Θ} {ε ε' : EExp Θ}
       → ((δ : Subst Θ ∅ˢ) → valᵉ (ε [ δ ]ᵉ) ≃ₑ valᵉ (ε' [ δ ]ᵉ)) → ε ≡̂ₑ ε'
≡̂ₑ-val f = mk≡̂ₑ (semₑ λ δ _ → proj₁ (f δ)) (semₑ λ δ _ → proj₂ (f δ))

-- Properties of convertibility: a congruence, the monoid, join and
-- distributivity laws, the constants' arithmetic, `∣_∣̂ᵉ` a monoid morphism

module _ {Θ : Scope} where

  ≡̂ᵣ-refl : ∀ {ρ : RExp Θ} → ρ ≡̂ᵣ ρ
  ≡̂ᵣ-refl = ≡̂ᵣ-val λ _ → ≃ᵣ-refl

  ≡̂ᵣ-sym : ∀ {ρ ρ' : RExp Θ} → ρ ≡̂ᵣ ρ' → ρ' ≡̂ᵣ ρ
  ≡̂ᵣ-sym p = mk≡̂ᵣ (≡̂ᵣ⇒≿ p) (≡̂ᵣ⇒≾ p)

  ≡̂ᵣ-trans : ∀ {ρ ρ' ρ'' : RExp Θ} → ρ ≡̂ᵣ ρ' → ρ' ≡̂ᵣ ρ'' → ρ ≡̂ᵣ ρ''
  ≡̂ᵣ-trans p q = ≡̂ᵣ-val λ δ → ≃ᵣ-trans (≡̂ᵣ-run p δ) (≡̂ᵣ-run q δ)

  ≡̂ᵣ-cong : ∀ {ρ₁ ρ₁' ρ₂ ρ₂' : RExp Θ} → ρ₁ ≡̂ᵣ ρ₁' → ρ₂ ≡̂ᵣ ρ₂'
          → ρ₁ ·̂ᵣ ρ₂ ≡̂ᵣ ρ₁' ·̂ᵣ ρ₂'
  ≡̂ᵣ-cong p q = ≡̂ᵣ-val λ δ → ·ᵣ-cong (≡̂ᵣ-run p δ) (≡̂ᵣ-run q δ)

  ≡̂ᵣ-assoc : ∀ {ρ₁ ρ₂ ρ₃ : RExp Θ} → (ρ₁ ·̂ᵣ ρ₂) ·̂ᵣ ρ₃ ≡̂ᵣ ρ₁ ·̂ᵣ (ρ₂ ·̂ᵣ ρ₃)
  ≡̂ᵣ-assoc = ≡̂ᵣ-val λ _ → ·ᵣ-assoc _ _ _

  ≡̂ᵣ-identityˡ : ∀ {ρ : RExp Θ} → ûᵣ ·̂ᵣ ρ ≡̂ᵣ ρ
  ≡̂ᵣ-identityˡ = ≡̂ᵣ-val λ _ → ·ᵣ-identityˡ _

  ≡̂ᵣ-identityʳ : ∀ {ρ : RExp Θ} → ρ ·̂ᵣ ûᵣ ≡̂ᵣ ρ
  ≡̂ᵣ-identityʳ = ≡̂ᵣ-val λ _ → ·ᵣ-identityʳ _

  ≡̂ᵣ-const : ∀ {ρ ρ'} → ρ ≃ᵣ ρ' → rconst {Θ} ρ ≡̂ᵣ rconst ρ'
  ≡̂ᵣ-const e = ≡̂ᵣ-val λ _ → e

  ≡̂ᵣ-const-· : ∀ {ρ ρ'} → rconst {Θ} ρ ·̂ᵣ rconst ρ' ≡̂ᵣ rconst (ρ ·ᵣ ρ')
  ≡̂ᵣ-const-· = ≡̂ᵣ-val λ _ → ≃ᵣ-refl

  ≡̂ᵣ-comm : ∀ {ρ₁ ρ₂ : RExp Θ} → Commutative _≃ᵣ_ _·ᵣ_ → ρ₁ ·̂ᵣ ρ₂ ≡̂ᵣ ρ₂ ·̂ᵣ ρ₁
  ≡̂ᵣ-comm comm = ≡̂ᵣ-val λ _ → comm _ _

  ≡̂ᵣ-cong-⊔ : ∀ {ρ₁ ρ₁' ρ₂ ρ₂' : RExp Θ} → ρ₁ ≡̂ᵣ ρ₁' → ρ₂ ≡̂ᵣ ρ₂'
            → ρ₁ ⊔̂ᵣ ρ₂ ≡̂ᵣ ρ₁' ⊔̂ᵣ ρ₂'
  ≡̂ᵣ-cong-⊔ p q = ≡̂ᵣ-val λ δ → ⊔ᵣ-cong (≡̂ᵣ-run p δ) (≡̂ᵣ-run q δ)

  ≡̂ᵣ-const-⊔ : ∀ {ρ ρ'} → rconst {Θ} ρ ⊔̂ᵣ rconst ρ' ≡̂ᵣ rconst (ρ ⊔ᵣ ρ')
  ≡̂ᵣ-const-⊔ = ≡̂ᵣ-val λ _ → ≃ᵣ-refl

  ≡̂ᵣ-comm-⊔ : ∀ {ρ₁ ρ₂ : RExp Θ} → ρ₁ ⊔̂ᵣ ρ₂ ≡̂ᵣ ρ₂ ⊔̂ᵣ ρ₁
  ≡̂ᵣ-comm-⊔ = ≡̂ᵣ-val λ _ → ⊔ᵣ-comm _ _

  ≡̂ᵣ-distribˡ-⊔ : ∀ {ρ ρ₁ ρ₂ : RExp Θ} → ρ ·̂ᵣ (ρ₁ ⊔̂ᵣ ρ₂) ≡̂ᵣ ρ ·̂ᵣ ρ₁ ⊔̂ᵣ ρ ·̂ᵣ ρ₂
  ≡̂ᵣ-distribˡ-⊔ = ≡̂ᵣ-val λ _ → ·ᵣ-distribˡ-⊔ᵣ _ _ _

  ≡̂ᵣ-distribʳ-⊔ : ∀ {ρ ρ₁ ρ₂ : RExp Θ} → (ρ₁ ⊔̂ᵣ ρ₂) ·̂ᵣ ρ ≡̂ᵣ ρ₁ ·̂ᵣ ρ ⊔̂ᵣ ρ₂ ·̂ᵣ ρ
  ≡̂ᵣ-distribʳ-⊔ = ≡̂ᵣ-val λ _ → ·ᵣ-distribʳ-⊔ᵣ _ _ _

  ≡̂ᵣ-map-· : ∀ {ε ε' : EExp Θ} → ∣ ε ·̂ₑ ε' ∣̂ᵉ ≡̂ᵣ ∣ ε ∣̂ᵉ ·̂ᵣ ∣ ε' ∣̂ᵉ
  ≡̂ᵣ-map-· = ≡̂ᵣ-val λ _ → map-·ᵉ

  ≡̂ᵣ-map-⊔ : ∀ {ε ε' : EExp Θ} → ∣ ε ⊔̂ₑ ε' ∣̂ᵉ ≡̂ᵣ ∣ ε ∣̂ᵉ ⊔̂ᵣ ∣ ε' ∣̂ᵉ
  ≡̂ᵣ-map-⊔ = ≡̂ᵣ-val λ _ → map-⊔ᵉ

  ≡̂ᵣ-map-const : ∀ {e} → ∣ econst {Θ} e ∣̂ᵉ ≡̂ᵣ rconst (mapᵉ e)
  ≡̂ᵣ-map-const = ≡̂ᵣ-val λ _ → ≃ᵣ-refl

  ≡̂ᵣ-map-cong : ∀ {ε ε' : EExp Θ} → ε ≡̂ₑ ε' → ∣ ε ∣̂ᵉ ≡̂ᵣ ∣ ε' ∣̂ᵉ
  ≡̂ᵣ-map-cong p = ≡̂ᵣ-val λ δ → map-≃ᵉ (≡̂ₑ-run p δ)

  ≡̂ᵣ-absorb : ∀ {ρ ρ' : RExp Θ} → ∅ᴴ ⊩ ρ ≾̂ᵣ ρ' → ρ ⊔̂ᵣ ρ' ≡̂ᵣ ρ'
  ≡̂ᵣ-absorb p = ≡̂ᵣ-val λ δ → ⊔ᵣ-absorb (runᵣ p δ ⊨ᵍ-∅)

  ≡̂ₑ-refl : ∀ {ε : EExp Θ} → ε ≡̂ₑ ε
  ≡̂ₑ-refl = ≡̂ₑ-val λ _ → ≃ₑ-refl

  ≡̂ₑ-sym : ∀ {ε ε' : EExp Θ} → ε ≡̂ₑ ε' → ε' ≡̂ₑ ε
  ≡̂ₑ-sym p = mk≡̂ₑ (≡̂ₑ⇒≿ p) (≡̂ₑ⇒≾ p)

  ≡̂ₑ-trans : ∀ {ε ε' ε'' : EExp Θ} → ε ≡̂ₑ ε' → ε' ≡̂ₑ ε'' → ε ≡̂ₑ ε''
  ≡̂ₑ-trans p q = ≡̂ₑ-val λ δ → ≃ₑ-trans (≡̂ₑ-run p δ) (≡̂ₑ-run q δ)

  ≡̂ₑ-cong : ∀ {ε₁ ε₁' ε₂ ε₂' : EExp Θ} → ε₁ ≡̂ₑ ε₁' → ε₂ ≡̂ₑ ε₂'
          → ε₁ ·̂ₑ ε₂ ≡̂ₑ ε₁' ·̂ₑ ε₂'
  ≡̂ₑ-cong p q = ≡̂ₑ-val λ δ → ·ₑ-cong (≡̂ₑ-run p δ) (≡̂ₑ-run q δ)

  ≡̂ₑ-assoc : ∀ {ε₁ ε₂ ε₃ : EExp Θ} → (ε₁ ·̂ₑ ε₂) ·̂ₑ ε₃ ≡̂ₑ ε₁ ·̂ₑ (ε₂ ·̂ₑ ε₃)
  ≡̂ₑ-assoc = ≡̂ₑ-val λ _ → ·ₑ-assoc _ _ _

  ≡̂ₑ-identityˡ : ∀ {ε : EExp Θ} → ûₑ ·̂ₑ ε ≡̂ₑ ε
  ≡̂ₑ-identityˡ = ≡̂ₑ-val λ _ → ·ₑ-identityˡ _

  ≡̂ₑ-identityʳ : ∀ {ε : EExp Θ} → ε ·̂ₑ ûₑ ≡̂ₑ ε
  ≡̂ₑ-identityʳ = ≡̂ₑ-val λ _ → ·ₑ-identityʳ _

  ≡̂ₑ-const : ∀ {ε ε'} → ε ≃ₑ ε' → econst {Θ} ε ≡̂ₑ econst ε'
  ≡̂ₑ-const e = ≡̂ₑ-val λ _ → e

  ≡̂ₑ-const-· : ∀ {ε ε'} → econst {Θ} ε ·̂ₑ econst ε' ≡̂ₑ econst (ε ·ₑ ε')
  ≡̂ₑ-const-· = ≡̂ₑ-val λ _ → ≃ₑ-refl

  ≡̂ₑ-comm : ∀ {ε₁ ε₂ : EExp Θ} → Commutative _≃ₑ_ _·ₑ_ → ε₁ ·̂ₑ ε₂ ≡̂ₑ ε₂ ·̂ₑ ε₁
  ≡̂ₑ-comm comm = ≡̂ₑ-val λ _ → comm _ _

  ≡̂ₑ-cong-⊔ : ∀ {ε₁ ε₁' ε₂ ε₂' : EExp Θ} → ε₁ ≡̂ₑ ε₁' → ε₂ ≡̂ₑ ε₂'
            → ε₁ ⊔̂ₑ ε₂ ≡̂ₑ ε₁' ⊔̂ₑ ε₂'
  ≡̂ₑ-cong-⊔ p q = ≡̂ₑ-val λ δ → ⊔ₑ-cong (≡̂ₑ-run p δ) (≡̂ₑ-run q δ)

  ≡̂ₑ-const-⊔ : ∀ {ε ε'} → econst {Θ} ε ⊔̂ₑ econst ε' ≡̂ₑ econst (ε ⊔ₑ ε')
  ≡̂ₑ-const-⊔ = ≡̂ₑ-val λ _ → ≃ₑ-refl

  ≡̂ₑ-comm-⊔ : ∀ {ε₁ ε₂ : EExp Θ} → ε₁ ⊔̂ₑ ε₂ ≡̂ₑ ε₂ ⊔̂ₑ ε₁
  ≡̂ₑ-comm-⊔ = ≡̂ₑ-val λ _ → ⊔ₑ-comm _ _

  ≡̂ₑ-distribˡ-⊔ : ∀ {ε ε₁ ε₂ : EExp Θ} → ε ·̂ₑ (ε₁ ⊔̂ₑ ε₂) ≡̂ₑ ε ·̂ₑ ε₁ ⊔̂ₑ ε ·̂ₑ ε₂
  ≡̂ₑ-distribˡ-⊔ = ≡̂ₑ-val λ _ → ·ₑ-distribˡ-⊔ₑ _ _ _

  ≡̂ₑ-distribʳ-⊔ : ∀ {ε ε₁ ε₂ : EExp Θ} → (ε₁ ⊔̂ₑ ε₂) ·̂ₑ ε ≡̂ₑ ε₁ ·̂ₑ ε ⊔̂ₑ ε₂ ·̂ₑ ε
  ≡̂ₑ-distribʳ-⊔ = ≡̂ₑ-val λ _ → ·ₑ-distribʳ-⊔ₑ _ _ _

  ≡̂ₑ-absorb : ∀ {ε ε' : EExp Θ} → ∅ᴴ ⊩ ε ≾̂ₑ ε' → ε ⊔̂ₑ ε' ≡̂ₑ ε'
  ≡̂ₑ-absorb p = ≡̂ₑ-val λ δ → ⊔ₑ-absorb (runₑ p δ ⊨ᵍ-∅)

-- Properties of entailed ordering: hypotheses, constants, convertibility,
-- preorder, monotonicity, joins, top, zero-product laws, quantified
-- hypotheses (rule Inst) and closed orderings (rule Truth)

module _ {Θ : Scope} {Q : Hyps Θ} where

  hypᵣ : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q ⊩ ρ ≾̂ᵣ ρ'
  hypᵣ m = semᵣ λ δ h → ⊨ᵍʳ h m

  atomᵣ : ∀ {ρ ρ'} → ρ ≾ᵣ ρ' → Q ⊩ rconst ρ ≾̂ᵣ rconst ρ'
  atomᵣ p = semᵣ λ _ _ → p

  eqᵣ : ∀ {ρ ρ'} → ρ ≡̂ᵣ ρ' → Q ⊩ ρ ≾̂ᵣ ρ'
  eqᵣ p = semᵣ λ δ _ → runᵣ (≡̂ᵣ⇒≾ p) δ ⊨ᵍ-∅

  transᵣ : ∀ {ρ ρ' ρ''} → Q ⊩ ρ ≾̂ᵣ ρ' → Q ⊩ ρ' ≾̂ᵣ ρ'' → Q ⊩ ρ ≾̂ᵣ ρ''
  transᵣ p q = semᵣ λ δ h → ≾ᵣ-trans (runᵣ p δ h) (runᵣ q δ h)

  monoᵣ : ∀ {ρ₁ ρ₁' ρ₂ ρ₂'} → Q ⊩ ρ₁ ≾̂ᵣ ρ₁' → Q ⊩ ρ₂ ≾̂ᵣ ρ₂'
        → Q ⊩ ρ₁ ·̂ᵣ ρ₂ ≾̂ᵣ ρ₁' ·̂ᵣ ρ₂'
  monoᵣ p q = semᵣ λ δ h → ≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (runᵣ p δ h)) (·ᵣ-monoʳ-≾ᵣ (runᵣ q δ h))

  map-mono : ∀ {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → Q ⊩ ∣ ε ∣̂ᵉ ≾̂ᵣ ∣ ε' ∣̂ᵉ
  map-mono p = semᵣ λ δ h → map-monotoneᵉ (runₑ p δ h)

  ⊔-ubˡᵣ : ∀ {ρ₁ ρ₂} → Q ⊩ ρ₁ ≾̂ᵣ ρ₁ ⊔̂ᵣ ρ₂
  ⊔-ubˡᵣ {ρ₁} {ρ₂} = semᵣ λ δ _ → ⊔ᵣ-ubˡ (valʳ (ρ₁ [ δ ]ʳ)) (valʳ (ρ₂ [ δ ]ʳ))

  ⊔-ubʳᵣ : ∀ {ρ₁ ρ₂} → Q ⊩ ρ₂ ≾̂ᵣ ρ₁ ⊔̂ᵣ ρ₂
  ⊔-ubʳᵣ {ρ₁} {ρ₂} = semᵣ λ δ _ → ⊔ᵣ-ubʳ (valʳ (ρ₁ [ δ ]ʳ)) (valʳ (ρ₂ [ δ ]ʳ))

  ⊔-lubᵣ : ∀ {ρ₁ ρ₂ ρ} → Q ⊩ ρ₁ ≾̂ᵣ ρ → Q ⊩ ρ₂ ≾̂ᵣ ρ → Q ⊩ ρ₁ ⊔̂ᵣ ρ₂ ≾̂ᵣ ρ
  ⊔-lubᵣ p q = semᵣ λ δ h → ⊔ᵣ-lub (runᵣ p δ h) (runᵣ q δ h)

  topᵣ : ∀ {ρ} → Q ⊩ ρ ≾̂ᵣ rconst ⊤ᵣ
  topᵣ {ρ} = semᵣ λ δ _ → ≾-⊤ᵣ (valʳ (ρ [ δ ]ʳ))

  minᵣ : ∀ {ρ} → Minimum _≾ᵣ_ uᵣ → Q ⊩ ûᵣ ≾̂ᵣ ρ
  minᵣ {ρ} least = semᵣ λ δ _ → least (valʳ (ρ [ δ ]ʳ))

  zeroˡᵣ : ∀ {ρ ρ'} → Q ⊩ ρ ·̂ᵣ ρ' ≾̂ᵣ ûᵣ → Q ⊩ ρ ≾̂ᵣ ûᵣ
  zeroˡᵣ p = semᵣ λ δ h → ≾ᵣ-zero-productˡ (runᵣ p δ h)

  zeroʳᵣ : ∀ {ρ ρ'} → Q ⊩ ρ ·̂ᵣ ρ' ≾̂ᵣ ûᵣ → Q ⊩ ρ' ≾̂ᵣ ûᵣ
  zeroʳᵣ p = semᵣ λ δ h → ≾ᵣ-zero-productʳ (runᵣ p δ h)

  plusᵣ : ∀ {c ρ} → (p : Plus _·ᵣ_ _≾ᵣ_ c) → Q ⊩ rconst c ≾̂ᵣ ρ → Q ⊩ ρ ·̂ᵣ ρ ≾̂ᵣ ρ
        → Q ⊩ rconst (Plus.c⁺ p) ≾̂ᵣ ρ
  plusᵣ p q r = semᵣ λ δ h → Plus.c⁺-least p (runᵣ q δ h) (runᵣ r δ h)

  indˡᵣ : ∀ {c ρ} → (p : Plus _·ᵣ_ _≾ᵣ_ c) → Q ⊩ rconst c ·̂ᵣ ρ ≾̂ᵣ ρ
        → Q ⊩ rconst (Plus.c⁺ p) ·̂ᵣ ρ ≾̂ᵣ ρ
  indˡᵣ p q = semᵣ λ δ h → Plus.⁺-indˡ p (runᵣ q δ h)

  indʳᵣ : ∀ {c ρ} → (p : Plus _·ᵣ_ _≾ᵣ_ c) → Q ⊩ ρ ·̂ᵣ rconst c ≾̂ᵣ ρ
        → Q ⊩ ρ ·̂ᵣ rconst (Plus.c⁺ p) ≾̂ᵣ ρ
  indʳᵣ p q = semᵣ λ δ h → Plus.⁺-indʳ p (runᵣ q δ h)

  instᵣ : ∀ {O ρ ρ'} → O ∈ qhyps Q → (ρ , ρ') ∈ ors (body O)
        → (es : Vec (EExp Θ) (rigids O))
        → Q ⊩ ρ [ idˢ ,ᵉⁿ es ]ʳ ≾̂ᵣ ρ' [ idˢ ,ᵉⁿ es ]ʳ
  instᵣ {O} {ρ} {ρ'} m mφ es = semᵣ λ δ h →
    subst₂ _≾ᵣ_ (cong valʳ (eq δ ρ)) (cong valʳ (eq δ ρ'))
           (⊨ᵒʳ (⊨ᵍᵠ h m (mapᵛ (_[ δ ]ᵉ) es)) mφ)
    where
      eq : (δ : Subst Θ ∅ˢ) → (x : RExp (Θ +eⁿ rigids O))
         → x [ δ ,ᵉⁿ mapᵛ (_[ δ ]ᵉ) es ]ʳ ≡ x [ idˢ ,ᵉⁿ es ]ʳ [ δ ]ʳ
      eq δ x = sym (trans ([⨟]ʳ x (idˢ ,ᵉⁿ es) δ) ([≐]ʳ (inst-⨟ es δ) x))

  factᵣ : ∀ {k ρ ρ'} → ∅ᴴ ⊩ ρ ≾̂ᵣ ρ' → (es : Vec (EExp Θ) k)
        → Q ⊩ ρ [ from∅ ,ᵉⁿ es ]ʳ ≾̂ᵣ ρ' [ from∅ ,ᵉⁿ es ]ʳ
  factᵣ {ρ = ρ} {ρ'} H es = semᵣ λ δ _ →
    subst₂ _≾ᵣ_ (cong valʳ (sym ([⨟]ʳ ρ (from∅ ,ᵉⁿ es) δ)))
                (cong valʳ (sym ([⨟]ʳ ρ' (from∅ ,ᵉⁿ es) δ)))
           (runᵣ H ((from∅ ,ᵉⁿ es) ⨟ˢ δ) ⊨ᵍ-∅)

  hypₑ : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q ⊩ ε ≾̂ₑ ε'
  hypₑ m = semₑ λ δ h → ⊨ᵍᵉ h m

  atomₑ : ∀ {ε ε'} → ε ≾ₑ ε' → Q ⊩ econst ε ≾̂ₑ econst ε'
  atomₑ p = semₑ λ _ _ → p

  eqₑ : ∀ {ε ε'} → ε ≡̂ₑ ε' → Q ⊩ ε ≾̂ₑ ε'
  eqₑ p = semₑ λ δ _ → runₑ (≡̂ₑ⇒≾ p) δ ⊨ᵍ-∅

  transₑ : ∀ {ε ε' ε''} → Q ⊩ ε ≾̂ₑ ε' → Q ⊩ ε' ≾̂ₑ ε'' → Q ⊩ ε ≾̂ₑ ε''
  transₑ p q = semₑ λ δ h → ≾ₑ-trans (runₑ p δ h) (runₑ q δ h)

  monoₑ : ∀ {ε₁ ε₁' ε₂ ε₂'} → Q ⊩ ε₁ ≾̂ₑ ε₁' → Q ⊩ ε₂ ≾̂ₑ ε₂'
        → Q ⊩ ε₁ ·̂ₑ ε₂ ≾̂ₑ ε₁' ·̂ₑ ε₂'
  monoₑ p q = semₑ λ δ h → ≾ₑ-trans (·ₑ-monoˡ-≾ₑ (runₑ p δ h)) (·ₑ-monoʳ-≾ₑ (runₑ q δ h))

  ⊔-ubˡₑ : ∀ {ε₁ ε₂} → Q ⊩ ε₁ ≾̂ₑ ε₁ ⊔̂ₑ ε₂
  ⊔-ubˡₑ {ε₁} {ε₂} = semₑ λ δ _ → ⊔ₑ-ubˡ (valᵉ (ε₁ [ δ ]ᵉ)) (valᵉ (ε₂ [ δ ]ᵉ))

  ⊔-ubʳₑ : ∀ {ε₁ ε₂} → Q ⊩ ε₂ ≾̂ₑ ε₁ ⊔̂ₑ ε₂
  ⊔-ubʳₑ {ε₁} {ε₂} = semₑ λ δ _ → ⊔ₑ-ubʳ (valᵉ (ε₁ [ δ ]ᵉ)) (valᵉ (ε₂ [ δ ]ᵉ))

  ⊔-lubₑ : ∀ {ε₁ ε₂ ε} → Q ⊩ ε₁ ≾̂ₑ ε → Q ⊩ ε₂ ≾̂ₑ ε → Q ⊩ ε₁ ⊔̂ₑ ε₂ ≾̂ₑ ε
  ⊔-lubₑ p q = semₑ λ δ h → ⊔ₑ-lub (runₑ p δ h) (runₑ q δ h)

  topₑ : ∀ {ε} → Q ⊩ ε ≾̂ₑ econst ⊤ₑ
  topₑ {ε} = semₑ λ δ _ → ≾-⊤ₑ (valᵉ (ε [ δ ]ᵉ))

  minₑ : ∀ {ε} → Minimum _≾ₑ_ uₑ → Q ⊩ ûₑ ≾̂ₑ ε
  minₑ {ε} least = semₑ λ δ _ → least (valᵉ (ε [ δ ]ᵉ))

  zeroˡₑ : ∀ {ε ε'} → Q ⊩ ε ·̂ₑ ε' ≾̂ₑ ûₑ → Q ⊩ ε ≾̂ₑ ûₑ
  zeroˡₑ p = semₑ λ δ h → ≾ₑ-zero-productˡ (runₑ p δ h)

  zeroʳₑ : ∀ {ε ε'} → Q ⊩ ε ·̂ₑ ε' ≾̂ₑ ûₑ → Q ⊩ ε' ≾̂ₑ ûₑ
  zeroʳₑ p = semₑ λ δ h → ≾ₑ-zero-productʳ (runₑ p δ h)

  plusₑ : ∀ {c ε} → (p : Plus _·ₑ_ _≾ₑ_ c) → Q ⊩ econst c ≾̂ₑ ε → Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε
        → Q ⊩ econst (Plus.c⁺ p) ≾̂ₑ ε
  plusₑ p q r = semₑ λ δ h → Plus.c⁺-least p (runₑ q δ h) (runₑ r δ h)

  indˡₑ : ∀ {c ε} → (p : Plus _·ₑ_ _≾ₑ_ c) → Q ⊩ econst c ·̂ₑ ε ≾̂ₑ ε
        → Q ⊩ econst (Plus.c⁺ p) ·̂ₑ ε ≾̂ₑ ε
  indˡₑ p q = semₑ λ δ h → Plus.⁺-indˡ p (runₑ q δ h)

  indʳₑ : ∀ {c ε} → (p : Plus _·ₑ_ _≾ₑ_ c) → Q ⊩ ε ·̂ₑ econst c ≾̂ₑ ε
        → Q ⊩ ε ·̂ₑ econst (Plus.c⁺ p) ≾̂ₑ ε
  indʳₑ p q = semₑ λ δ h → Plus.⁺-indʳ p (runₑ q δ h)

  instₑ : ∀ {O ε ε'} → O ∈ qhyps Q → (ε , ε') ∈ oes (body O)
        → (es : Vec (EExp Θ) (rigids O))
        → Q ⊩ ε [ idˢ ,ᵉⁿ es ]ᵉ ≾̂ₑ ε' [ idˢ ,ᵉⁿ es ]ᵉ
  instₑ {O} {ε} {ε'} m mφ es = semₑ λ δ h →
    subst₂ _≾ₑ_ (cong valᵉ (eq δ ε)) (cong valᵉ (eq δ ε'))
           (⊨ᵒᵉ (⊨ᵍᵠ h m (mapᵛ (_[ δ ]ᵉ) es)) mφ)
    where
      eq : (δ : Subst Θ ∅ˢ) → (x : EExp (Θ +eⁿ rigids O))
         → x [ δ ,ᵉⁿ mapᵛ (_[ δ ]ᵉ) es ]ᵉ ≡ x [ idˢ ,ᵉⁿ es ]ᵉ [ δ ]ᵉ
      eq δ x = sym (trans ([⨟]ᵉ x (idˢ ,ᵉⁿ es) δ) ([≐]ᵉ (inst-⨟ es δ) x))

  factₑ : ∀ {k ε ε'} → ∅ᴴ ⊩ ε ≾̂ₑ ε' → (es : Vec (EExp Θ) k)
        → Q ⊩ ε [ from∅ ,ᵉⁿ es ]ᵉ ≾̂ₑ ε' [ from∅ ,ᵉⁿ es ]ᵉ
  factₑ {ε = ε} {ε'} H es = semₑ λ δ _ →
    subst₂ _≾ₑ_ (cong valᵉ (sym ([⨟]ᵉ ε (from∅ ,ᵉⁿ es) δ)))
                (cong valᵉ (sym ([⨟]ᵉ ε' (from∅ ,ᵉⁿ es) δ)))
           (runₑ H ((from∅ ,ᵉⁿ es) ⨟ˢ δ) ⊨ᵍ-∅)

-- Entailed ordering is reflexive

⊩≾̂ᵣ-refl : ∀ {Θ} {Q : Hyps Θ} {ρ} → Q ⊩ ρ ≾̂ᵣ ρ
⊩≾̂ᵣ-refl = eqᵣ ≡̂ᵣ-refl

⊩≾̂ₑ-refl : ∀ {Θ} {Q : Hyps Θ} {ε} → Q ⊩ ε ≾̂ₑ ε
⊩≾̂ₑ-refl = eqₑ ≡̂ₑ-refl

-- Same expressions are convertible

≅ᵉ⇒≡̂ : ∀ {Θ} {ε ε' : EExp Θ} → ε ≅ᵉ ε' → ε ≡̂ₑ ε'
≅ᵉ⇒≡̂ evar≅       = ≡̂ₑ-refl
≅ᵉ⇒≡̂ (econst≅ e) = ≡̂ₑ-const e
≅ᵉ⇒≡̂ (·≅ p q)    = ≡̂ₑ-cong (≅ᵉ⇒≡̂ p) (≅ᵉ⇒≡̂ q)
≅ᵉ⇒≡̂ (⊔≅ p q)    = ≡̂ₑ-cong-⊔ (≅ᵉ⇒≡̂ p) (≅ᵉ⇒≡̂ q)

≅ʳ⇒≡̂ : ∀ {Θ} {ρ ρ' : RExp Θ} → ρ ≅ʳ ρ' → ρ ≡̂ᵣ ρ'
≅ʳ⇒≡̂ rvar≅       = ≡̂ᵣ-refl
≅ʳ⇒≡̂ (rconst≅ e) = ≡̂ᵣ-const e
≅ʳ⇒≡̂ (·≅ p q)    = ≡̂ᵣ-cong (≅ʳ⇒≡̂ p) (≅ʳ⇒≡̂ q)
≅ʳ⇒≡̂ (⊔≅ p q)    = ≡̂ᵣ-cong-⊔ (≅ʳ⇒≡̂ p) (≅ʳ⇒≡̂ q)
≅ʳ⇒≡̂ (∣∣≅ p)     = ≡̂ᵣ-map-cong (≅ᵉ⇒≡̂ p)

-- Idempotence of the join and absorption by the top: instances of
-- absorption, as in `Grades.Base`

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
≡̂ᵣ-antisym-∅ = mk≡̂ᵣ

≡̂ₑ-antisym-∅ : ∀ {Θ} {ε ε' : EExp Θ}
             → ∅ᴴ ⊩ ε ≾̂ₑ ε' → ∅ᴴ ⊩ ε' ≾̂ₑ ε → ε ≡̂ₑ ε'
≡̂ₑ-antisym-∅ = mk≡̂ₑ

-- Associativity of the join

≡̂ᵣ-assoc-⊔ : ∀ {Θ} {ρ₁ ρ₂ ρ₃ : RExp Θ}
           → (ρ₁ ⊔̂ᵣ ρ₂) ⊔̂ᵣ ρ₃ ≡̂ᵣ ρ₁ ⊔̂ᵣ (ρ₂ ⊔̂ᵣ ρ₃)
≡̂ᵣ-assoc-⊔ = ≡̂ᵣ-val λ _ → ⊔ᵣ-assoc _ _ _

≡̂ₑ-assoc-⊔ : ∀ {Θ} {ε₁ ε₂ ε₃ : EExp Θ}
           → (ε₁ ⊔̂ₑ ε₂) ⊔̂ₑ ε₃ ≡̂ₑ ε₁ ⊔̂ₑ (ε₂ ⊔̂ₑ ε₃)
≡̂ₑ-assoc-⊔ = ≡̂ₑ-val λ _ → ⊔ₑ-assoc _ _ _

-- Eternality: a rule for each eternal type former, for the eternality
-- atoms of the set, and for transfer along an assumed subtyping

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
  _|+|ₑ_  : ∀ {A₁ A₂} → Q ⊩ᴱ A₁ → Q ⊩ᴱ A₂ → Q ⊩ᴱ A₁ |+| A₂
  |List|ₑ : ∀ {A} → Q ⊩ᴱ A → Q ⊩ᴱ |List| A
  Emptyₑ  : Q ⊩ᴱ Empty

-- Convertibility of open types: the same shape, the grades related
-- by `_≡̂ᵣ_` and `_≡̂ₑ_`

infix  4  _≡̂ᵛ_ _≡̂ᶜ_
infix  37 [_]≡̂_
infix  32 _|×|≡̂_ _|+|≡̂_
infixr 30 _⇒≡̂_ _⇛≡̂_
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
  _|+|≡̂_  : ∀ {A A' B B'} → A ≡̂ᵛ A' → B ≡̂ᵛ B' → A |+| B ≡̂ᵛ A' |+| B'
  |List|≡̂ : ∀ {A A'} → A ≡̂ᵛ A' → |List| A ≡̂ᵛ |List| A'
  Empty≡̂  : Empty ≡̂ᵛ Empty
  _⇒≡̂_    : ∀ {A A' C C'} → A ≡̂ᵛ A' → C ≡̂ᶜ C' → A ⇒ C ≡̂ᵛ A' ⇒ C'
  _⇛≡̂_    : ∀ {C C' D D'} → C ≡̂ᶜ C' → D ≡̂ᶜ D' → C ⇛ D ≡̂ᵛ C' ⇛ D'
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
≡̂ᵛ-refl (A |+| B) = ≡̂ᵛ-refl A |+|≡̂ ≡̂ᵛ-refl B
≡̂ᵛ-refl (|List| A) = |List|≡̂ (≡̂ᵛ-refl A)
≡̂ᵛ-refl Empty     = Empty≡̂
≡̂ᵛ-refl (A ⇒ C)   = ≡̂ᵛ-refl A ⇒≡̂ ≡̂ᶜ-refl C
≡̂ᵛ-refl (C ⇛ D)   = ≡̂ᶜ-refl C ⇛≡̂ ≡̂ᶜ-refl D
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
≡̂ᵛ-sym (p |+|≡̂ q)  = ≡̂ᵛ-sym p |+|≡̂ ≡̂ᵛ-sym q
≡̂ᵛ-sym (|List|≡̂ p) = |List|≡̂ (≡̂ᵛ-sym p)
≡̂ᵛ-sym Empty≡̂      = Empty≡̂
≡̂ᵛ-sym (p ⇒≡̂ q)    = ≡̂ᵛ-sym p ⇒≡̂ ≡̂ᶜ-sym q
≡̂ᵛ-sym (p ⇛≡̂ q)    = ≡̂ᶜ-sym p ⇛≡̂ ≡̂ᶜ-sym q
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
≡̂ᵛ-trans (p |+|≡̂ q) (p' |+|≡̂ q') = ≡̂ᵛ-trans p p' |+|≡̂ ≡̂ᵛ-trans q q'
≡̂ᵛ-trans (|List|≡̂ p) (|List|≡̂ p') = |List|≡̂ (≡̂ᵛ-trans p p')
≡̂ᵛ-trans Empty≡̂     Empty≡̂      = Empty≡̂
≡̂ᵛ-trans (p ⇒≡̂ q)   (p' ⇒≡̂ q')   = ≡̂ᵛ-trans p p' ⇒≡̂ ≡̂ᶜ-trans q q'
≡̂ᵛ-trans (p ⇛≡̂ q)   (p' ⇛≡̂ q')   = ≡̂ᶜ-trans p p' ⇛≡̂ ≡̂ᶜ-trans q q'
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
⊩ᴱ-≡̂ (p |+|≡̂ q) (et |+|ₑ et') = ⊩ᴱ-≡̂ p et |+|ₑ ⊩ᴱ-≡̂ q et'
⊩ᴱ-≡̂ (|List|≡̂ p) (|List|ₑ et) = |List|ₑ (⊩ᴱ-≡̂ p et)
⊩ᴱ-≡̂ Empty≡̂     et           = et

-- Shape-preserving subtyping of open types: a constructor per pair of
-- matching formers, grade slots entailed from `Q`, a type variable
-- related only by an assumed subtyping

infix  4  _∣_<:̂ᵛ_ _∣_<:̂ᶜ_
infix  37 [_]ₛ_
infix  32 _|×|ₛ_ _|+|ₛ_
infixr 30 _⇒ₛ_ _⇛ₛ_
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
  _|+|ₛ_ : ∀ {A A' B B'} → Q ∣ A <:̂ᵛ A' → Q ∣ B <:̂ᵛ B'
         → Q ∣ (A |+| B) <:̂ᵛ (A' |+| B')
  |List|ₛ : ∀ {A A'} → Q ∣ A <:̂ᵛ A' → Q ∣ |List| A <:̂ᵛ |List| A'
  Emptyₛ : Q ∣ Empty <:̂ᵛ Empty
  _⇒ₛ_   : ∀ {A A' C C'} → Q ∣ A' <:̂ᵛ A → Q ∣ C <:̂ᶜ C'
         → Q ∣ (A ⇒ C) <:̂ᵛ (A' ⇒ C')
  _⇛ₛ_   : ∀ {C C' D D'} → Q ∣ C' <:̂ᶜ C → Q ∣ D <:̂ᶜ D'
         → Q ∣ (C ⇛ D) <:̂ᵛ (C' ⇛ D')
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
<:̂ᵛ-refl (A |+| B) = <:̂ᵛ-refl A |+|ₛ <:̂ᵛ-refl B
<:̂ᵛ-refl (|List| A) = |List|ₛ (<:̂ᵛ-refl A)
<:̂ᵛ-refl Empty     = Emptyₛ
<:̂ᵛ-refl (A ⇒ C)   = <:̂ᵛ-refl A ⇒ₛ <:̂ᶜ-refl C
<:̂ᵛ-refl (C ⇛ D)   = <:̂ᶜ-refl C ⇛ₛ <:̂ᶜ-refl D
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
<:̂ᵛ-trans (p |+|ₛ r) (q |+|ₛ s) = <:̂ᵛ-trans p q |+|ₛ <:̂ᵛ-trans r s
<:̂ᵛ-trans (|List|ₛ p) (|List|ₛ q) = |List|ₛ (<:̂ᵛ-trans p q)
<:̂ᵛ-trans Emptyₛ     Emptyₛ     = Emptyₛ
<:̂ᵛ-trans (p ⇒ₛ r)   (q ⇒ₛ s)   = <:̂ᵛ-trans q p ⇒ₛ <:̂ᶜ-trans r s
<:̂ᵛ-trans (p ⇛ₛ r)   (q ⇛ₛ s)   = <:̂ᶜ-trans q p ⇛ₛ <:̂ᶜ-trans r s
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
≡̂ᵛ-<:̂ (p |+|≡̂ q) = ≡̂ᵛ-<:̂ p |+|ₛ ≡̂ᵛ-<:̂ q
≡̂ᵛ-<:̂ (|List|≡̂ p) = |List|ₛ (≡̂ᵛ-<:̂ p)
≡̂ᵛ-<:̂ Empty≡̂     = Emptyₛ
≡̂ᵛ-<:̂ (p ⇒≡̂ q)   = ≡̂ᵛ-<:̂ (≡̂ᵛ-sym p) ⇒ₛ ≡̂ᶜ-<:̂ q
≡̂ᵛ-<:̂ (p ⇛≡̂ q)   = ≡̂ᶜ-<:̂ (≡̂ᶜ-sym p) ⇛ₛ ≡̂ᶜ-<:̂ q
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
<:̂ᵛ-eternalˡ (p |+|ₛ r)   (et |+|ₑ e) = <:̂ᵛ-eternalˡ p et |+|ₑ <:̂ᵛ-eternalˡ r e
<:̂ᵛ-eternalˡ (|List|ₛ p)  (|List|ₑ et) = |List|ₑ (<:̂ᵛ-eternalˡ p et)
<:̂ᵛ-eternalˡ Emptyₛ       et          = et

<:̂ᵛ-eternalʳ : ∀ {Θ} {Q : Hyps Θ} {A B} → Q ∣ A <:̂ᵛ B → Q ⊩ᴱ A → Q ⊩ᴱ B
<:̂ᵛ-eternalʳ (tvarₛ p)    et          = et-subʳ p et
<:̂ᵛ-eternalʳ (Baseₛ refl) et          = et
<:̂ᵛ-eternalʳ Unitₛ        et          = et
<:̂ᵛ-eternalʳ Boolₛ        et          = et
<:̂ᵛ-eternalʳ Natₛ         et          = et
<:̂ᵛ-eternalʳ (p |×|ₛ r)   (et |×|ₑ e) = <:̂ᵛ-eternalʳ p et |×|ₑ <:̂ᵛ-eternalʳ r e
<:̂ᵛ-eternalʳ (p |+|ₛ r)   (et |+|ₑ e) = <:̂ᵛ-eternalʳ p et |+|ₑ <:̂ᵛ-eternalʳ r e
<:̂ᵛ-eternalʳ (|List|ₛ p)  (|List|ₑ et) = |List|ₑ (<:̂ᵛ-eternalʳ p et)
<:̂ᵛ-eternalʳ Emptyₛ       et          = et

-- The side condition of the `var` rule, `VarOK Q A ρ`: `A` is eternal or
-- `ρ ≾ u` at every instance. Met by eternality, by the ordering, or by a
-- `disj` hypothesis at a grade above; closed under subtyping, the
-- eternality-preserving formers and joins, up to lowering the grade

data VarOK {Θ : Scope} (Q : Hyps Θ) : OVType Θ → RExp Θ → Set where
  et-ok     : ∀ {A ρ} → Q ⊩ᴱ A → VarOK Q A ρ
  ≾ᵘ-ok     : ∀ {A ρ} → Q ⊩ ρ ≾̂ᵣ ûᵣ → VarOK Q A ρ
  hyp-ok    : ∀ {A ρ ρ'} → (A , ρ') ∈ disj Q → Q ⊩ ρ ≾̂ᵣ ρ' → VarOK Q A ρ
  subˡ-ok   : ∀ {A B ρ} → Q ∣ A <:̂ᵛ B → VarOK Q B ρ → VarOK Q A ρ
  subʳ-ok   : ∀ {A B ρ} → Q ∣ B <:̂ᵛ A → VarOK Q B ρ → VarOK Q A ρ
  _|×|-ok_  : ∀ {A₁ A₂ ρ} → VarOK Q A₁ ρ → VarOK Q A₂ ρ → VarOK Q (A₁ |×| A₂) ρ
  _|+|-ok_  : ∀ {A₁ A₂ ρ} → VarOK Q A₁ ρ → VarOK Q A₂ ρ → VarOK Q (A₁ |+| A₂) ρ
  |List|-ok : ∀ {A ρ} → VarOK Q A ρ → VarOK Q (|List| A) ρ
  ⊔-ok      : ∀ {A ρ ρ₁ ρ₂} → Q ⊩ ρ ≾̂ᵣ ρ₁ ⊔̂ᵣ ρ₂ → VarOK Q A ρ₁ → VarOK Q A ρ₂
            → VarOK Q A ρ

-- A `disj` hypothesis met as it stands

hyp-ok₀ : ∀ {Θ} {Q : Hyps Θ} {A ρ} → (A , ρ) ∈ disj Q → VarOK Q A ρ
hyp-ok₀ m = hyp-ok m ⊩≾̂ᵣ-refl

-- The side condition is closed under lowering the grade

VarOK-≾ : ∀ {Θ} {Q : Hyps Θ} {A ρ ρ'} → Q ⊩ ρ ≾̂ᵣ ρ' → VarOK Q A ρ' → VarOK Q A ρ
VarOK-≾ q (et-ok et)      = et-ok et
VarOK-≾ q (≾ᵘ-ok le)      = ≾ᵘ-ok (transᵣ q le)
VarOK-≾ q (hyp-ok m q')   = hyp-ok m (transᵣ q q')
VarOK-≾ q (subˡ-ok p ok)  = subˡ-ok p (VarOK-≾ q ok)
VarOK-≾ q (subʳ-ok p ok)  = subʳ-ok p (VarOK-≾ q ok)
VarOK-≾ q (ok₁ |×|-ok ok₂) = VarOK-≾ q ok₁ |×|-ok VarOK-≾ q ok₂
VarOK-≾ q (ok₁ |+|-ok ok₂) = VarOK-≾ q ok₁ |+|-ok VarOK-≾ q ok₂
VarOK-≾ q (|List|-ok ok)  = |List|-ok (VarOK-≾ q ok)
VarOK-≾ q (⊔-ok q' ok₁ ok₂) = ⊔-ok (transᵣ q q') ok₁ ok₂

-- and so under equivalence of the type and lowering the grade

VarOK-≃ : ∀ {Θ} {Q : Hyps Θ} {A A' ρ ρ'}
        → Q ∣ A <:̂ᵛ A' → Q ∣ A' <:̂ᵛ A → Q ⊩ ρ ≾̂ᵣ ρ' → VarOK Q A' ρ' → VarOK Q A ρ
VarOK-≃ p _ q ok = subˡ-ok p (VarOK-≾ q ok)

-- A `disj` hypothesis met at a convertible type

hyp-ok-≡̂ : ∀ {Θ} {Q : Hyps Θ} {A A' ρ ρ'}
         → (A' , ρ') ∈ disj Q → A ≡̂ᵛ A' → Q ⊩ ρ ≾̂ᵣ ρ' → VarOK Q A ρ
hyp-ok-≡̂ m p q = subˡ-ok (≡̂ᵛ-<:̂ p) (hyp-ok m q)

-- The side condition is closed under convertibility

VarOK-≡̂ : ∀ {Θ} {Q : Hyps Θ} {A A' ρ ρ'}
        → A ≡̂ᵛ A' → Q ⊩ ρ ≾̂ᵣ ρ' → VarOK Q A' ρ' → VarOK Q A ρ
VarOK-≡̂ p = VarOK-≃ (≡̂ᵛ-<:̂ p) (≡̂ᵛ-<:̂ (≡̂ᵛ-sym p))

-- Under no `disj` hypothesis the side condition is its two disjuncts

VarOK-split : ∀ {Θ} {Q : Hyps Θ} {A ρ}
            → disj Q ≡ [] → VarOK Q A ρ → (Q ⊩ᴱ A) ⊎ (Q ⊩ ρ ≾̂ᵣ ûᵣ)
VarOK-split e (et-ok et)  = inj₁ et
VarOK-split e (≾ᵘ-ok le)  = inj₂ le
VarOK-split e (hyp-ok m _) with subst (_ ∈_) e m
... | ()
VarOK-split e (subˡ-ok p ok) with VarOK-split e ok
... | inj₁ et = inj₁ (<:̂ᵛ-eternalˡ p et)
... | inj₂ le = inj₂ le
VarOK-split e (subʳ-ok p ok) with VarOK-split e ok
... | inj₁ et = inj₁ (<:̂ᵛ-eternalʳ p et)
... | inj₂ le = inj₂ le
VarOK-split e (ok₁ |×|-ok ok₂) with VarOK-split e ok₁ | VarOK-split e ok₂
... | inj₁ et₁ | inj₁ et₂ = inj₁ (et₁ |×|ₑ et₂)
... | inj₂ le  | _        = inj₂ le
... | inj₁ _   | inj₂ le  = inj₂ le
VarOK-split e (ok₁ |+|-ok ok₂) with VarOK-split e ok₁ | VarOK-split e ok₂
... | inj₁ et₁ | inj₁ et₂ = inj₁ (et₁ |+|ₑ et₂)
... | inj₂ le  | _        = inj₂ le
... | inj₁ _   | inj₂ le  = inj₂ le
VarOK-split e (|List|-ok ok) with VarOK-split e ok
... | inj₁ et = inj₁ (|List|ₑ et)
... | inj₂ le = inj₂ le
VarOK-split e (⊔-ok q ok₁ ok₂) with VarOK-split e ok₁ | VarOK-split e ok₂
... | inj₁ et  | _        = inj₁ et
... | inj₂ _   | inj₁ et  = inj₁ et
... | inj₂ le₁ | inj₂ le₂ = inj₂ (transᵣ q (⊔-lubᵣ le₁ le₂))

VarOK-∅ᴴ : ∀ {Θ} {A : OVType Θ} {ρ} → VarOK ∅ᴴ A ρ → (∅ᴴ ⊩ᴱ A) ⊎ (∅ᴴ ⊩ ρ ≾̂ᵣ ûᵣ)
VarOK-∅ᴴ = VarOK-split refl

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

-- Inversion at a sum: a supertype is a sum, componentwise

<:̂ᵛ-+ˡ : ∀ {Θ} {Q : Hyps Θ} {A₁ A₂ B}
       → Q ∣ A₁ |+| A₂ <:̂ᵛ B
       → Σ[ B₁ ∈ OVType Θ ] Σ[ B₂ ∈ OVType Θ ]
           (B ≡ B₁ |+| B₂) × (Q ∣ A₁ <:̂ᵛ B₁) × (Q ∣ A₂ <:̂ᵛ B₂)
<:̂ᵛ-+ˡ (p |+|ₛ q) = _ , _ , refl , p , q

-- Inversion at a list type: a supertype is a list type

<:̂ᵛ-Listˡ : ∀ {Θ} {Q : Hyps Θ} {A B}
          → Q ∣ |List| A <:̂ᵛ B
          → Σ[ B₁ ∈ OVType Θ ] (B ≡ |List| B₁) × (Q ∣ A <:̂ᵛ B₁)
<:̂ᵛ-Listˡ (|List|ₛ p) = _ , refl , p

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

-- A supertype of a box type is a box type

<:̂ᵛ-boxˡ : ∀ {Θ} {Q : Hyps Θ} {ρ A B}
         → Q ∣ [ ρ ] A <:̂ᵛ B
         → Σ[ ρ₁ ∈ RExp Θ ] Σ[ B₁ ∈ OVType Θ ]
             (B ≡ [ ρ₁ ] B₁) × (Q ⊩ ρ₁ ≾̂ᵣ ρ) × (Q ∣ A <:̂ᵛ B₁)
<:̂ᵛ-boxˡ ([ q ]ₛ p) = _ , _ , refl , q , p

-- Inversion at a handler type: a supertype is a handler type,
-- contravariantly in the handled computation type

<:̂ᵛ-⇛ˡ : ∀ {Θ} {Q : Hyps Θ} {C D B}
       → Q ∣ C ⇛ D <:̂ᵛ B
       → Σ[ C' ∈ OCType Θ ] Σ[ D' ∈ OCType Θ ]
           (B ≡ C' ⇛ D') × (Q ∣ C' <:̂ᶜ C) × (Q ∣ D <:̂ᶜ D')
<:̂ᵛ-⇛ˡ (p ⇛ₛ q) = _ , _ , refl , p , q

------------------------------------------------------------------------
-- Entailment of grade orderings and of quantified orderings

infix 4 _⊩ᵒ_[_] _⊩ᴼ_[_]

record _⊩ᵒ_[_] {Ψ Ψ' : Scope} (Q : Hyps Ψ') (o : Ords Ψ) (δ : Subst Ψ Ψ') : Set where
  constructor mk⊩ᵒ
  field
    ⊩ors : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors o → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    ⊩oes : ∀ {ε ε'} → (ε , ε') ∈ oes o → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ

open _⊩ᵒ_[_] public

⊩ᵒ-resp-≐ˢ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {o : Ords Ψ} {δ δ' : Subst Ψ Ψ'}
           → δ ≐ˢ δ' → Q ⊩ᵒ o [ δ ] → Q ⊩ᵒ o [ δ' ]
⊩ᵒ-resp-≐ˢ {Q = Q} p h =
  mk⊩ᵒ (λ {ρ} {ρ'} m → subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([≐]ʳ p ρ) ([≐]ʳ p ρ') (⊩ors h m))
       (λ {ε} {ε'} m → subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([≐]ᵉ p ε) ([≐]ᵉ p ε') (⊩oes h m))

⊩ᵒ-subst : ∀ {Ψ Ψ₁ Ψ'} {Q : Hyps Ψ'} {o : Ords Ψ} {σ : Subst Ψ Ψ₁} {δ : Subst Ψ₁ Ψ'}
         → Q ⊩ᵒ o [ σ ]ᴼ [ δ ] → Q ⊩ᵒ o [ σ ⨟ˢ δ ]
⊩ᵒ-subst {Q = Q} {σ = σ} {δ} h =
  mk⊩ᵒ (λ {ρ} {ρ'} m → subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([⨟]ʳ ρ σ δ) ([⨟]ʳ ρ' σ δ)
                              (⊩ors h (∈-map⁺ (mapᵖ (_[ σ ]ʳ)) m)))
       (λ {ε} {ε'} m → subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([⨟]ᵉ ε σ δ) ([⨟]ᵉ ε' σ δ)
                              (⊩oes h (∈-map⁺ (mapᵖ (_[ σ ]ᵉ)) m)))

⊩ᵒ-subst⁻ : ∀ {Ψ Ψ₁ Ψ'} {Q : Hyps Ψ'} {o : Ords Ψ} {σ : Subst Ψ Ψ₁} {δ : Subst Ψ₁ Ψ'}
          → Q ⊩ᵒ o [ σ ⨟ˢ δ ] → Q ⊩ᵒ o [ σ ]ᴼ [ δ ]
⊩ᵒ-subst⁻ {Q = Q} {o = o} {σ = σ} {δ} h = mk⊩ᵒ r e
  where
    r : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors (o [ σ ]ᴼ) → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    r m with ∈-map⁻ (mapᵖ (_[ σ ]ʳ)) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
      subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym ([⨟]ʳ ρ₀ σ δ)) (sym ([⨟]ʳ ρ₀' σ δ)) (⊩ors h m₀)

    e : ∀ {ε ε'} → (ε , ε') ∈ oes (o [ σ ]ᴼ) → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
    e m with ∈-map⁻ (mapᵖ (_[ σ ]ᵉ)) m
    ... | (ε₀ , ε₀') , m₀ , refl =
      subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym ([⨟]ᵉ ε₀ σ δ)) (sym ([⨟]ᵉ ε₀' σ δ)) (⊩oes h m₀)

-- A quantified ordering is entailed along a substitution when its
-- orderings are, at fresh rigids, by the hypotheses weakened to them

_⊩ᴼ_[_] : ∀ {Θ Ξ} → Hyps Ξ → QOrd Θ → Subst Θ Ξ → Set
Q ⊩ᴼ O [ δ ] = wkᵉⁿ-H (rigids O) Q ⊩ᵒ body O [ δ ↑ᵉⁿ rigids O ]

⊩ᴼ-resp-≐ˢ : ∀ {Θ Ξ} {Q : Hyps Ξ} {δ δ' : Subst Θ Ξ} → (O : QOrd Θ)
           → δ ≐ˢ δ' → Q ⊩ᴼ O [ δ ] → Q ⊩ᴼ O [ δ' ]
⊩ᴼ-resp-≐ˢ (qord l k o) p h = ⊩ᵒ-resp-≐ˢ (≐ˢ-↑ᵉⁿ p k) h

⊩ᴼ-subst : ∀ {Θ Θ₁ Ξ} {Q : Hyps Ξ} {σ : Subst Θ Θ₁} {δ : Subst Θ₁ Ξ} → (O : QOrd Θ)
         → Q ⊩ᴼ O [ σ ]ᵠ [ δ ] → Q ⊩ᴼ O [ σ ⨟ˢ δ ]
⊩ᴼ-subst {σ = σ} {δ} (qord l k o) h = ⊩ᵒ-resp-≐ˢ (⨟-↑ᵉⁿ σ δ k) (⊩ᵒ-subst h)

⊩ᴼ-subst⁻ : ∀ {Θ Θ₁ Ξ} {Q : Hyps Ξ} {σ : Subst Θ Θ₁} {δ : Subst Θ₁ Ξ} → (O : QOrd Θ)
          → Q ⊩ᴼ O [ σ ⨟ˢ δ ] → Q ⊩ᴼ O [ σ ]ᵠ [ δ ]
⊩ᴼ-subst⁻ {σ = σ} {δ} (qord l k o) h =
  ⊩ᵒ-subst⁻ (⊩ᵒ-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉⁿ σ δ k)) h)

-- `Q' ⊩ᴴ Q [ σ ]`: `Q'` entails every hypothesis of `Q` transported
-- along `σ`, a quantified one at fresh rigids (`_⊩ᴼ_[_]`)

infix 4 _⊩ᴴ_[_] _⊩ᴴ_ _⊩ᴵ_[_] _↪ᴴ_[_]

record _⊩ᴴ_[_] {Θ Θ' : Scope} (Q' : Hyps Θ') (Q : Hyps Θ) (σ : Subst Θ Θ') : Set where
  constructor mk⊩ᴴ
  field
    ⊩ets    : ∀ {α} → α ∈ ets Q → Q' ⊩ᴱ sTy σ α
    ⊩subᵥ   : ∀ {α β} → (α , β) ∈ subᵥ Q → Q' ∣ sTy σ α <:̂ᵛ sTy σ β
    ⊩ordᵣ   : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q' ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ' [ σ ]ʳ
    ⊩ordₑ   : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q' ⊩ ε [ σ ]ᵉ ≾̂ₑ ε' [ σ ]ᵉ
    ⊩disj   : ∀ {A ρ} → (A , ρ) ∈ disj Q → VarOK Q' (A [ σ ]ᵛ) (ρ [ σ ]ʳ)
    ⊩qhyps  : ∀ {O} → O ∈ qhyps Q → Q' ⊩ᴼ O [ σ ]

open _⊩ᴴ_[_] public

-- Entailment between hypothesis sets over the same scope

_⊩ᴴ_ : ∀ {Θ} → Hyps Θ → Hyps Θ → Set
Q' ⊩ᴴ Q = Q' ⊩ᴴ Q [ idˢ ]

-- An instance map: `Q'` entails every hypothesis of `Q` transported
-- along `σ`, a quantified one at every instance of its rigids

record _⊩ᴵ_[_] {Θ Θ' : Scope} (Q' : Hyps Θ') (Q : Hyps Θ) (σ : Subst Θ Θ') : Set where
  constructor mk⊩ᴵ
  field
    ⊩etsᴵ    : ∀ {α} → α ∈ ets Q → Q' ⊩ᴱ sTy σ α
    ⊩subᵥᴵ   : ∀ {α β} → (α , β) ∈ subᵥ Q → Q' ∣ sTy σ α <:̂ᵛ sTy σ β
    ⊩ordᵣᴵ   : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q' ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ' [ σ ]ʳ
    ⊩ordₑᴵ   : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q' ⊩ ε [ σ ]ᵉ ≾̂ₑ ε' [ σ ]ᵉ
    ⊩disjᴵ   : ∀ {A ρ} → (A , ρ) ∈ disj Q → VarOK Q' (A [ σ ]ᵛ) (ρ [ σ ]ʳ)
    ⊩qhypsᴵ  : ∀ {O} → O ∈ qhyps Q → (es : Vec (EExp Θ') (rigids O))
             → Q' ⊩ᵒ body O [ σ ,ᵉⁿ es ]

open _⊩ᴵ_[_] public

-- An embedding: every hypothesis of `Q` transported along `σ` is one of
-- `Q'`

record _↪ᴴ_[_] {Θ Θ' : Scope} (Q : Hyps Θ) (Q' : Hyps Θ') (σ : Subst Θ Θ') : Set where
  constructor mk↪ᴴ
  field
    ↪ets    : ∀ {α} → α ∈ ets Q → Σ[ β ∈ TyVar Θ' ] ((sTy σ α ≡ tvar β) × (β ∈ ets Q'))
    ↪subᵥ   : ∀ {α β} → (α , β) ∈ subᵥ Q
            → Σ[ α' ∈ TyVar Θ' ] Σ[ β' ∈ TyVar Θ' ]
                ((sTy σ α ≡ tvar α') × (sTy σ β ≡ tvar β') × ((α' , β') ∈ subᵥ Q'))
    ↪ordᵣ   : ∀ {p} → p ∈ ordᵣ Q → mapᵖ (_[ σ ]ʳ) p ∈ ordᵣ Q'
    ↪ordₑ   : ∀ {p} → p ∈ ordₑ Q → mapᵖ (_[ σ ]ᵉ) p ∈ ordₑ Q'
    ↪disj   : ∀ {p} → p ∈ disj Q → mapᵈ (_[ σ ]ᵛ) (_[ σ ]ʳ) p ∈ disj Q'
    ↪qhyps  : ∀ {O} → O ∈ qhyps Q → O [ σ ]ᵠ ∈ qhyps Q'

open _↪ᴴ_[_] public

-- Every set entails the empty one, along any substitution

⊩ᴴ-∅ : ∀ {Θ Θ'} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} → Q' ⊩ᴴ ∅ᴴ [ σ ]
⊩ᴴ-∅ = mk⊩ᴴ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

⊩ᴵ-∅ : ∀ {Θ Θ'} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} → Q' ⊩ᴵ ∅ᴴ [ σ ]
⊩ᴵ-∅ = mk⊩ᴵ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

-- The empty set at the fresh rigids

wkᵉⁿ-∅ᴴ : ∀ {Θ} → (k : ℕ) → wkᵉⁿ-H {Θ} k ∅ᴴ ≡ ∅ᴴ
wkᵉⁿ-∅ᴴ zero    = refl
wkᵉⁿ-∅ᴴ (suc k) = wkᵉⁿ-∅ᴴ k

-- A closed expression, weakened into a scope and instantiated back out
-- of it, is itself

private

  from∅-id : from∅ {∅ˢ} ≐ˢ idˢ
  from∅-id = mk≐ˢ (λ ()) (λ ()) (λ ())

  closed-back : ∀ {Θ} → (δ : Subst Θ ∅ˢ) → (e : EExp ∅ˢ) → e [ from∅ {Θ} ]ᵉ [ δ ]ᵉ ≡ e
  closed-back {Θ} δ e = trans ([⨟]ᵉ e (from∅ {Θ}) δ)
                          (trans ([≐]ᵉ (≐ˢ-trans (from∅-⨟ δ) from∅-id) e) ([id]ᵉ e))

  closed-backs : ∀ {Θ k} → (δ : Subst Θ ∅ˢ) → (es : Vec (EExp ∅ˢ) k)
               → mapᵛ (_[ δ ]ᵉ) (mapᵛ (_[ from∅ {Θ} ]ᵉ) es) ≡ es
  closed-backs δ []       = refl
  closed-backs δ (e ∷ es) = cong₂ _∷_ (closed-back δ e) (closed-backs δ es)

-- An instance map carries a closed instance satisfying the grade part
-- of its source back to one satisfying the grade part of its target

⊨ᵍ-⨟ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {δ : Subst Θ' ∅ˢ}
     → Q' ⊩ᴵ Q [ σ ] → δ ⊨ᵍ Q' → (σ ⨟ˢ δ) ⊨ᵍ Q
⊨ᵍ-⨟ {Θ} {Θ'} {Q} {Q'} {σ} {δ} g h = mk⊨ᵍ oR oE qh
  where
    oR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → valʳ (ρ [ σ ⨟ˢ δ ]ʳ) ≾ᵣ valʳ (ρ' [ σ ⨟ˢ δ ]ʳ)
    oR {ρ} {ρ'} m = subst₂ _≾ᵣ_ (cong valʳ ([⨟]ʳ ρ σ δ)) (cong valʳ ([⨟]ʳ ρ' σ δ))
                           (runᵣ (⊩ordᵣᴵ g m) δ h)

    oE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → valᵉ (ε [ σ ⨟ˢ δ ]ᵉ) ≾ₑ valᵉ (ε' [ σ ⨟ˢ δ ]ᵉ)
    oE {ε} {ε'} m = subst₂ _≾ₑ_ (cong valᵉ ([⨟]ᵉ ε σ δ)) (cong valᵉ ([⨟]ᵉ ε' σ δ))
                           (runₑ (⊩ordₑᴵ g m) δ h)

    qh : ∀ {O} → O ∈ qhyps Q → (es : Vec (EExp ∅ˢ) (rigids O))
       → ((σ ⨟ˢ δ) ,ᵉⁿ es) ⊨ᵒ body O
    qh {O} m es = mk⊨ᵒ r e
      where
        es' = mapᵛ (_[ from∅ {Θ'} ]ᵉ) es
        d   = ⊩qhypsᴵ g m es'

        p : ((σ ,ᵉⁿ es') ⨟ˢ δ) ≐ˢ ((σ ⨟ˢ δ) ,ᵉⁿ es)
        p = subst (λ v → ((σ ,ᵉⁿ es') ⨟ˢ δ) ≐ˢ ((σ ⨟ˢ δ) ,ᵉⁿ v)) (closed-backs δ es)
                  (,ᵉⁿ-⨟ σ es' δ)

        eqʳ : (x : RExp (Θ +eⁿ rigids O)) → x [ σ ,ᵉⁿ es' ]ʳ [ δ ]ʳ ≡ x [ (σ ⨟ˢ δ) ,ᵉⁿ es ]ʳ
        eqʳ x = trans ([⨟]ʳ x (σ ,ᵉⁿ es') δ) ([≐]ʳ p x)

        eqᵉ : (x : EExp (Θ +eⁿ rigids O)) → x [ σ ,ᵉⁿ es' ]ᵉ [ δ ]ᵉ ≡ x [ (σ ⨟ˢ δ) ,ᵉⁿ es ]ᵉ
        eqᵉ x = trans ([⨟]ᵉ x (σ ,ᵉⁿ es') δ) ([≐]ᵉ p x)

        r : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors (body O)
          → valʳ (ρ [ (σ ⨟ˢ δ) ,ᵉⁿ es ]ʳ) ≾ᵣ valʳ (ρ' [ (σ ⨟ˢ δ) ,ᵉⁿ es ]ʳ)
        r {ρ} {ρ'} mφ = subst₂ _≾ᵣ_ (cong valʳ (eqʳ ρ)) (cong valʳ (eqʳ ρ'))
                               (runᵣ (⊩ors d mφ) δ h)

        e : ∀ {ε ε'} → (ε , ε') ∈ oes (body O)
          → valᵉ (ε [ (σ ⨟ˢ δ) ,ᵉⁿ es ]ᵉ) ≾ₑ valᵉ (ε' [ (σ ⨟ˢ δ) ,ᵉⁿ es ]ᵉ)
        e {ε} {ε'} mφ = subst₂ _≾ₑ_ (cong valᵉ (eqᵉ ε)) (cong valᵉ (eqᵉ ε'))
                               (runₑ (⊩oes d mφ) δ h)

-- Entailment and convertibility are stable under substitution along an
-- instance map

⊩-substᴵᵣ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {ρ ρ' : RExp Θ}
          → Q' ⊩ᴵ Q [ σ ] → Q ⊩ ρ ≾̂ᵣ ρ' → Q' ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ' [ σ ]ʳ
⊩-substᴵᵣ {σ = σ} {ρ} {ρ'} g p = semᵣ λ δ h →
  subst₂ _≾ᵣ_ (cong valʳ (sym ([⨟]ʳ ρ σ δ))) (cong valʳ (sym ([⨟]ʳ ρ' σ δ)))
         (runᵣ p (σ ⨟ˢ δ) (⊨ᵍ-⨟ g h))

⊩-substᴵₑ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {ε ε' : EExp Θ}
          → Q' ⊩ᴵ Q [ σ ] → Q ⊩ ε ≾̂ₑ ε' → Q' ⊩ ε [ σ ]ᵉ ≾̂ₑ ε' [ σ ]ᵉ
⊩-substᴵₑ {σ = σ} {ε} {ε'} g p = semₑ λ δ h →
  subst₂ _≾ₑ_ (cong valᵉ (sym ([⨟]ᵉ ε σ δ))) (cong valᵉ (sym ([⨟]ᵉ ε' σ δ)))
         (runₑ p (σ ⨟ˢ δ) (⊨ᵍ-⨟ g h))

≡̂ᵣ-subst : ∀ {Θ Θ'} {ρ ρ' : RExp Θ} → (σ : Subst Θ Θ')
         → ρ ≡̂ᵣ ρ' → ρ [ σ ]ʳ ≡̂ᵣ ρ' [ σ ]ʳ
≡̂ᵣ-subst σ p = mk≡̂ᵣ (⊩-substᴵᵣ (⊩ᴵ-∅ {σ = σ}) (≡̂ᵣ⇒≾ p)) (⊩-substᴵᵣ (⊩ᴵ-∅ {σ = σ}) (≡̂ᵣ⇒≿ p))

≡̂ₑ-subst : ∀ {Θ Θ'} {ε ε' : EExp Θ} → (σ : Subst Θ Θ')
         → ε ≡̂ₑ ε' → ε [ σ ]ᵉ ≡̂ₑ ε' [ σ ]ᵉ
≡̂ₑ-subst σ p = mk≡̂ₑ (⊩-substᴵₑ (⊩ᴵ-∅ {σ = σ}) (≡̂ₑ⇒≾ p)) (⊩-substᴵₑ (⊩ᴵ-∅ {σ = σ}) (≡̂ₑ⇒≿ p))

-- A type variable's image is an arbitrary open type, so an assumed
-- subtyping transports to a subtyping derivation at those images.

⊩ᵗᵛ-substᴵ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {α β}
           → Q' ⊩ᴵ Q [ σ ] → Q ⊩ᵗᵛ α ≾ β → Q' ∣ sTy σ α <:̂ᵛ sTy σ β
⊩ᵗᵛ-substᴵ {σ = σ} h (reflᵗᵛ {α})  = <:̂ᵛ-refl (sTy σ α)
⊩ᵗᵛ-substᴵ         h (hypᵗᵛ m)     = ⊩subᵥᴵ h m
⊩ᵗᵛ-substᴵ         h (transᵗᵛ p q) = <:̂ᵛ-trans (⊩ᵗᵛ-substᴵ h p) (⊩ᵗᵛ-substᴵ h q)

⊩ᴱ-substᴵ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {A : OVType Θ}
          → Q' ⊩ᴵ Q [ σ ] → Q ⊩ᴱ A → Q' ⊩ᴱ A [ σ ]ᵛ
⊩ᴱ-substᴵ h (et-hyp m)     = ⊩etsᴵ h m
⊩ᴱ-substᴵ h (et-subˡ p et) = <:̂ᵛ-eternalˡ (⊩ᵗᵛ-substᴵ h p) (⊩ᴱ-substᴵ h et)
⊩ᴱ-substᴵ h (et-subʳ p et) = <:̂ᵛ-eternalʳ (⊩ᵗᵛ-substᴵ h p) (⊩ᴱ-substᴵ h et)
⊩ᴱ-substᴵ h (Baseₑ p)      = Baseₑ p
⊩ᴱ-substᴵ h Unitₑ          = Unitₑ
⊩ᴱ-substᴵ h Boolₑ          = Boolₑ
⊩ᴱ-substᴵ h Natₑ           = Natₑ
⊩ᴱ-substᴵ h (et₁ |×|ₑ et₂) = ⊩ᴱ-substᴵ h et₁ |×|ₑ ⊩ᴱ-substᴵ h et₂
⊩ᴱ-substᴵ h (et₁ |+|ₑ et₂) = ⊩ᴱ-substᴵ h et₁ |+|ₑ ⊩ᴱ-substᴵ h et₂
⊩ᴱ-substᴵ h (|List|ₑ et)   = |List|ₑ (⊩ᴱ-substᴵ h et)
⊩ᴱ-substᴵ h Emptyₑ         = Emptyₑ

≡̂ᵛ-subst : ∀ {Θ Θ'} {A A' : OVType Θ} → (σ : Subst Θ Θ') → A ≡̂ᵛ A' → A [ σ ]ᵛ ≡̂ᵛ A' [ σ ]ᵛ
≡̂ᶜ-subst : ∀ {Θ Θ'} {C C' : OCType Θ} → (σ : Subst Θ Θ') → C ≡̂ᶜ C' → C [ σ ]ᶜ ≡̂ᶜ C' [ σ ]ᶜ

≡̂ᵛ-subst σ (tvar≡̂ {α}) = ≡̂ᵛ-refl (sTy σ α)
≡̂ᵛ-subst σ Base≡̂       = Base≡̂
≡̂ᵛ-subst σ Unit≡̂       = Unit≡̂
≡̂ᵛ-subst σ Bool≡̂       = Bool≡̂
≡̂ᵛ-subst σ Nat≡̂       = Nat≡̂
≡̂ᵛ-subst σ (p |×|≡̂ q)  = ≡̂ᵛ-subst σ p |×|≡̂ ≡̂ᵛ-subst σ q
≡̂ᵛ-subst σ (p |+|≡̂ q)  = ≡̂ᵛ-subst σ p |+|≡̂ ≡̂ᵛ-subst σ q
≡̂ᵛ-subst σ (|List|≡̂ p) = |List|≡̂ (≡̂ᵛ-subst σ p)
≡̂ᵛ-subst σ Empty≡̂      = Empty≡̂
≡̂ᵛ-subst σ (p ⇒≡̂ q)    = ≡̂ᵛ-subst σ p ⇒≡̂ ≡̂ᶜ-subst σ q
≡̂ᵛ-subst σ (p ⇛≡̂ q)    = ≡̂ᶜ-subst σ p ⇛≡̂ ≡̂ᶜ-subst σ q
≡̂ᵛ-subst σ ([ r ]≡̂ p)  = [ ≡̂ᵣ-subst σ r ]≡̂ ≡̂ᵛ-subst σ p

≡̂ᶜ-subst σ (p ‼≡̂ e) = ≡̂ᵛ-subst σ p ‼≡̂ ≡̂ₑ-subst σ e

-- Eternality moves between the images of a type under substitutions
-- related by subtyping at every type variable

⊩ᴱ-<:ˢ : ∀ {Θ Θ'} {Q : Hyps Θ'} {σ τ : Subst Θ Θ'}
       → (∀ α → Q ∣ sTy σ α <:̂ᵛ sTy τ α) → (A : OVType Θ)
       → Q ⊩ᴱ A [ τ ]ᵛ → Q ⊩ᴱ A [ σ ]ᵛ
⊩ᴱ-<:ˢ k (tvar α)  et           = <:̂ᵛ-eternalˡ (k α) et
⊩ᴱ-<:ˢ k (Base b)  et           = et
⊩ᴱ-<:ˢ k Unit      et           = et
⊩ᴱ-<:ˢ k Bool      et           = et
⊩ᴱ-<:ˢ k Nat       et           = et
⊩ᴱ-<:ˢ k (A |×| B) (et |×|ₑ et') = ⊩ᴱ-<:ˢ k A et |×|ₑ ⊩ᴱ-<:ˢ k B et'
⊩ᴱ-<:ˢ k (A |+| B) (et |+|ₑ et') = ⊩ᴱ-<:ˢ k A et |+|ₑ ⊩ᴱ-<:ˢ k B et'
⊩ᴱ-<:ˢ k (|List| A) (|List|ₑ et) = |List|ₑ (⊩ᴱ-<:ˢ k A et)
⊩ᴱ-<:ˢ k Empty     et           = et
⊩ᴱ-<:ˢ k (A ⇒ C)   ()
⊩ᴱ-<:ˢ k (C ⇛ D)   ()
⊩ᴱ-<:ˢ k ([ ρ ] A) ()

<:̂ᵛ-substᴵ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {A A' : OVType Θ}
           → Q' ⊩ᴵ Q [ σ ] → Q ∣ A <:̂ᵛ A' → Q' ∣ A [ σ ]ᵛ <:̂ᵛ A' [ σ ]ᵛ
<:̂ᶜ-substᴵ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {C C' : OCType Θ}
           → Q' ⊩ᴵ Q [ σ ] → Q ∣ C <:̂ᶜ C' → Q' ∣ C [ σ ]ᶜ <:̂ᶜ C' [ σ ]ᶜ

<:̂ᵛ-substᴵ h (tvarₛ p)  = ⊩ᵗᵛ-substᴵ h p
<:̂ᵛ-substᴵ h (Baseₛ p)  = Baseₛ p
<:̂ᵛ-substᴵ h Unitₛ      = Unitₛ
<:̂ᵛ-substᴵ h Boolₛ      = Boolₛ
<:̂ᵛ-substᴵ h Natₛ       = Natₛ
<:̂ᵛ-substᴵ h (p |×|ₛ r) = <:̂ᵛ-substᴵ h p |×|ₛ <:̂ᵛ-substᴵ h r
<:̂ᵛ-substᴵ h (p |+|ₛ r) = <:̂ᵛ-substᴵ h p |+|ₛ <:̂ᵛ-substᴵ h r
<:̂ᵛ-substᴵ h (|List|ₛ p) = |List|ₛ (<:̂ᵛ-substᴵ h p)
<:̂ᵛ-substᴵ h Emptyₛ     = Emptyₛ
<:̂ᵛ-substᴵ h (p ⇒ₛ r)   = <:̂ᵛ-substᴵ h p ⇒ₛ <:̂ᶜ-substᴵ h r
<:̂ᵛ-substᴵ h (p ⇛ₛ r)   = <:̂ᶜ-substᴵ h p ⇛ₛ <:̂ᶜ-substᴵ h r
<:̂ᵛ-substᴵ h ([ q ]ₛ p) = [ ⊩-substᴵᵣ h q ]ₛ <:̂ᵛ-substᴵ h p

<:̂ᶜ-substᴵ h (p ‼ₛ q) = <:̂ᵛ-substᴵ h p ‼ₛ ⊩-substᴵₑ h q

VarOK-substᴵ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'}
                 {A : OVType Θ} {ρ : RExp Θ}
             → Q' ⊩ᴵ Q [ σ ] → VarOK Q A ρ → VarOK Q' (A [ σ ]ᵛ) (ρ [ σ ]ʳ)
VarOK-substᴵ h (et-ok et)         = et-ok (⊩ᴱ-substᴵ h et)
VarOK-substᴵ h (≾ᵘ-ok le)         = ≾ᵘ-ok (⊩-substᴵᵣ h le)
VarOK-substᴵ h (hyp-ok m q)       = VarOK-≾ (⊩-substᴵᵣ h q) (⊩disjᴵ h m)
VarOK-substᴵ h (subˡ-ok p ok)     = subˡ-ok (<:̂ᵛ-substᴵ h p) (VarOK-substᴵ h ok)
VarOK-substᴵ h (subʳ-ok p ok)     = subʳ-ok (<:̂ᵛ-substᴵ h p) (VarOK-substᴵ h ok)
VarOK-substᴵ h (ok₁ |×|-ok ok₂)   = VarOK-substᴵ h ok₁ |×|-ok VarOK-substᴵ h ok₂
VarOK-substᴵ h (ok₁ |+|-ok ok₂)   = VarOK-substᴵ h ok₁ |+|-ok VarOK-substᴵ h ok₂
VarOK-substᴵ h (|List|-ok ok)     = |List|-ok (VarOK-substᴵ h ok)
VarOK-substᴵ h (⊔-ok q ok₁ ok₂)   =
  ⊔-ok (⊩-substᴵᵣ h q) (VarOK-substᴵ h ok₁) (VarOK-substᴵ h ok₂)

⊩ᵒ-⨟ᴵ : ∀ {Ψ Ψ' Ψ''} {Q : Hyps Ψ'} {Q' : Hyps Ψ''} {o : Ords Ψ}
          {δ : Subst Ψ Ψ'} {δ' : Subst Ψ' Ψ''}
      → Q' ⊩ᴵ Q [ δ' ] → Q ⊩ᵒ o [ δ ] → Q' ⊩ᵒ o [ δ ⨟ˢ δ' ]
⊩ᵒ-⨟ᴵ {Q' = Q'} {δ = δ} {δ'} g h =
  mk⊩ᵒ (λ {ρ} {ρ'} m → subst₂ (λ x y → Q' ⊩ x ≾̂ᵣ y) ([⨟]ʳ ρ δ δ') ([⨟]ʳ ρ' δ δ')
                              (⊩-substᴵᵣ g (⊩ors h m)))
       (λ {ε} {ε'} m → subst₂ (λ x y → Q' ⊩ x ≾̂ₑ y) ([⨟]ᵉ ε δ δ') ([⨟]ᵉ ε' δ δ')
                              (⊩-substᴵₑ g (⊩oes h m)))

-- An embedding is an instance map: a quantified hypothesis is
-- instantiated at its image

↪⇒⊩ᴵ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'}
     → Q ↪ᴴ Q' [ σ ] → Q' ⊩ᴵ Q [ σ ]
↪⇒⊩ᴵ {Θ' = Θ'} {Q} {Q'} {σ} e = mk⊩ᴵ et sb oR oE dj qh
  where
    et : ∀ {α} → α ∈ ets Q → Q' ⊩ᴱ sTy σ α
    et m with ↪ets e m
    ... | β , eq , m' = subst (Q' ⊩ᴱ_) (sym eq) (et-hyp m')

    sb : ∀ {α β} → (α , β) ∈ subᵥ Q → Q' ∣ sTy σ α <:̂ᵛ sTy σ β
    sb m with ↪subᵥ e m
    ... | α' , β' , eα , eβ , m' = subst₂ (Q' ∣_<:̂ᵛ_) (sym eα) (sym eβ) (tvarₛ (hypᵗᵛ m'))

    oR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q' ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ' [ σ ]ʳ
    oR m = hypᵣ (↪ordᵣ e m)

    oE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q' ⊩ ε [ σ ]ᵉ ≾̂ₑ ε' [ σ ]ᵉ
    oE m = hypₑ (↪ordₑ e m)

    dj : ∀ {A ρ} → (A , ρ) ∈ disj Q → VarOK Q' (A [ σ ]ᵛ) (ρ [ σ ]ʳ)
    dj m = hyp-ok₀ (↪disj e m)

    qh : ∀ {O} → O ∈ qhyps Q → (es : Vec (EExp Θ') (rigids O))
       → Q' ⊩ᵒ body O [ σ ,ᵉⁿ es ]
    qh {O} m es = mk⊩ᵒ r ε
      where
        k = rigids O

        r : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors (body O) → Q' ⊩ ρ [ σ ,ᵉⁿ es ]ʳ ≾̂ᵣ ρ' [ σ ,ᵉⁿ es ]ʳ
        r {ρ} {ρ'} mφ =
          subst₂ (λ x y → Q' ⊩ x ≾̂ᵣ y)
                 (trans ([⨟]ʳ ρ (σ ↑ᵉⁿ k) (idˢ ,ᵉⁿ es)) ([≐]ʳ (↑-inst σ k es) ρ))
                 (trans ([⨟]ʳ ρ' (σ ↑ᵉⁿ k) (idˢ ,ᵉⁿ es)) ([≐]ʳ (↑-inst σ k es) ρ'))
                 (instᵣ (↪qhyps e m) (∈-map⁺ (mapᵖ (_[ σ ↑ᵉⁿ k ]ʳ)) mφ) es)

        ε : ∀ {ε₁ ε₂} → (ε₁ , ε₂) ∈ oes (body O) → Q' ⊩ ε₁ [ σ ,ᵉⁿ es ]ᵉ ≾̂ₑ ε₂ [ σ ,ᵉⁿ es ]ᵉ
        ε {ε₁} {ε₂} mφ =
          subst₂ (λ x y → Q' ⊩ x ≾̂ₑ y)
                 (trans ([⨟]ᵉ ε₁ (σ ↑ᵉⁿ k) (idˢ ,ᵉⁿ es)) ([≐]ᵉ (↑-inst σ k es) ε₁))
                 (trans ([⨟]ᵉ ε₂ (σ ↑ᵉⁿ k) (idˢ ,ᵉⁿ es)) ([≐]ᵉ (↑-inst σ k es) ε₂))
                 (instₑ (↪qhyps e m) (∈-map⁺ (mapᵖ (_[ σ ↑ᵉⁿ k ]ᵉ)) mφ) es)

-- Embeddings: the identity, composites, weakenings and liftings

↪-refl : ∀ {Θ} {Q : Hyps Θ} → Q ↪ᴴ Q [ idˢ ]
↪-refl {Q = Q} =
  mk↪ᴴ (λ {α} m → α , refl , m)
       (λ {α} {β} m → α , β , refl , refl , m)
       (λ { {x , y} m → subst (_∈ ordᵣ Q) (sym (cong₂ _,_ ([id]ʳ x) ([id]ʳ y))) m })
       (λ { {x , y} m → subst (_∈ ordₑ Q) (sym (cong₂ _,_ ([id]ᵉ x) ([id]ᵉ y))) m })
       (λ { {A , ρ} m → subst (_∈ disj Q) (sym (cong₂ _,_ ([id]ᵛ A) ([id]ʳ ρ))) m })
       (λ {O} m → subst (_∈ qhyps Q) (sym ([id]ᵠ O)) m)

↪-⨟ : ∀ {Θ₀ Θ₁ Θ₂} {Q₀ : Hyps Θ₀} {Q₁ : Hyps Θ₁} {Q₂ : Hyps Θ₂}
        {σ : Subst Θ₀ Θ₁} {τ : Subst Θ₁ Θ₂}
    → Q₀ ↪ᴴ Q₁ [ σ ] → Q₁ ↪ᴴ Q₂ [ τ ] → Q₀ ↪ᴴ Q₂ [ σ ⨟ˢ τ ]
↪-⨟ {Θ₂ = Θ₂} {Q₀} {Q₁} {Q₂} {σ} {τ} e₁ e₂ = mk↪ᴴ et sb oR oE dj qh
  where
    et : ∀ {α} → α ∈ ets Q₀ → Σ[ γ ∈ TyVar Θ₂ ] ((sTy (σ ⨟ˢ τ) α ≡ tvar γ) × (γ ∈ ets Q₂))
    et m with ↪ets e₁ m
    ... | β , eq , m₁ with ↪ets e₂ m₁
    ...   | γ , eq' , m₂ = γ , trans (cong (_[ τ ]ᵛ) eq) eq' , m₂

    sb : ∀ {α β} → (α , β) ∈ subᵥ Q₀ → Σ[ α' ∈ TyVar Θ₂ ] Σ[ β' ∈ TyVar Θ₂ ] ((sTy (σ ⨟ˢ τ) α ≡ tvar α') × (sTy (σ ⨟ˢ τ) β ≡ tvar β') × ((α' , β') ∈ subᵥ Q₂))
    sb m with ↪subᵥ e₁ m
    ... | α' , β' , eα , eβ , m₁ with ↪subᵥ e₂ m₁
    ...   | α'' , β'' , eα' , eβ' , m₂ =
            α'' , β'' , trans (cong (_[ τ ]ᵛ) eα) eα' , trans (cong (_[ τ ]ᵛ) eβ) eβ' , m₂

    oR : ∀ {p} → p ∈ ordᵣ Q₀ → mapᵖ (_[ σ ⨟ˢ τ ]ʳ) p ∈ ordᵣ Q₂
    oR {x , y} m = subst (_∈ ordᵣ Q₂) (cong₂ _,_ ([⨟]ʳ x σ τ) ([⨟]ʳ y σ τ))
                         (↪ordᵣ e₂ (↪ordᵣ e₁ m))

    oE : ∀ {p} → p ∈ ordₑ Q₀ → mapᵖ (_[ σ ⨟ˢ τ ]ᵉ) p ∈ ordₑ Q₂
    oE {x , y} m = subst (_∈ ordₑ Q₂) (cong₂ _,_ ([⨟]ᵉ x σ τ) ([⨟]ᵉ y σ τ))
                         (↪ordₑ e₂ (↪ordₑ e₁ m))

    dj : ∀ {p} → p ∈ disj Q₀ → mapᵈ (_[ σ ⨟ˢ τ ]ᵛ) (_[ σ ⨟ˢ τ ]ʳ) p ∈ disj Q₂
    dj {A , ρ} m = subst (_∈ disj Q₂) (cong₂ _,_ ([⨟]ᵛ A σ τ) ([⨟]ʳ ρ σ τ))
                         (↪disj e₂ (↪disj e₁ m))

    qh : ∀ {O} → O ∈ qhyps Q₀ → O [ σ ⨟ˢ τ ]ᵠ ∈ qhyps Q₂
    qh {O} m = subst (_∈ qhyps Q₂) ([⨟]ᵠ O σ τ) (↪qhyps e₂ (↪qhyps e₁ m))

↪-wkᵗ : ∀ {Θ} {Q : Hyps Θ} → Q ↪ᴴ wkᵗ-H Q [ wkˢᵗ ]
↪-wkᵗ {Θ} {Q} =
  mk↪ᴴ (λ m → _ , refl , ∈-map⁺ (wkᵗ-tv Θ) m)
       (λ m → _ , _ , refl , refl , ∈-map⁺ (mapᵖ (wkᵗ-tv Θ)) m)
       (λ { {x , y} m → subst (_∈ ordᵣ (wkᵗ-H Q)) (sym (cong₂ _,_ (wkˢᵗ-r x) (wkˢᵗ-r y)))
                              (∈-map⁺ (mapᵖ wkᵗ-r) m) })
       (λ { {x , y} m → subst (_∈ ordₑ (wkᵗ-H Q)) (sym (cong₂ _,_ (wkˢᵗ-e x) (wkˢᵗ-e y)))
                              (∈-map⁺ (mapᵖ wkᵗ-e) m) })
       (λ { {A , ρ} m → subst (_∈ disj (wkᵗ-H Q)) (sym (cong₂ _,_ (wkˢᵗ-v A) (wkˢᵗ-r ρ)))
                              (∈-map⁺ (mapᵈ wkᵗ-v wkᵗ-r) m) })
       (λ m → ∈-map⁺ (_[ wkˢᵗ ]ᵠ) m)

↪-wkʳ : ∀ {Θ} {Q : Hyps Θ} → Q ↪ᴴ wkʳ-H Q [ wkˢʳ ]
↪-wkʳ {Θ} {Q} =
  mk↪ᴴ (λ m → _ , refl , ∈-map⁺ (wkʳ-tv Θ) m)
       (λ m → _ , _ , refl , refl , ∈-map⁺ (mapᵖ (wkʳ-tv Θ)) m)
       (λ { {x , y} m → subst (_∈ ordᵣ (wkʳ-H Q)) (sym (cong₂ _,_ (wkˢʳ-r x) (wkˢʳ-r y)))
                              (∈-map⁺ (mapᵖ wkʳ-r) m) })
       (λ { {x , y} m → subst (_∈ ordₑ (wkʳ-H Q)) (sym (cong₂ _,_ (wkˢʳ-e x) (wkˢʳ-e y)))
                              (∈-map⁺ (mapᵖ wkʳ-e) m) })
       (λ { {A , ρ} m → subst (_∈ disj (wkʳ-H Q)) (sym (cong₂ _,_ (wkˢʳ-v A) (wkˢʳ-r ρ)))
                              (∈-map⁺ (mapᵈ wkʳ-v wkʳ-r) m) })
       (λ m → ∈-map⁺ (_[ wkˢʳ ]ᵠ) m)

↪-wkᵉ : ∀ {Θ} {Q : Hyps Θ} → Q ↪ᴴ wkᵉ-H Q [ wkˢᵉ ]
↪-wkᵉ {Θ} {Q} =
  mk↪ᴴ (λ m → _ , refl , ∈-map⁺ (wkᵉ-tv Θ) m)
       (λ m → _ , _ , refl , refl , ∈-map⁺ (mapᵖ (wkᵉ-tv Θ)) m)
       (λ { {x , y} m → subst (_∈ ordᵣ (wkᵉ-H Q)) (sym (cong₂ _,_ (wkˢᵉ-r x) (wkˢᵉ-r y)))
                              (∈-map⁺ (mapᵖ wkᵉ-r) m) })
       (λ { {x , y} m → subst (_∈ ordₑ (wkᵉ-H Q)) (sym (cong₂ _,_ (wkˢᵉ-e x) (wkˢᵉ-e y)))
                              (∈-map⁺ (mapᵖ wkᵉ-e) m) })
       (λ { {A , ρ} m → subst (_∈ disj (wkᵉ-H Q)) (sym (cong₂ _,_ (wkˢᵉ-v A) (wkˢᵉ-r ρ)))
                              (∈-map⁺ (mapᵈ wkᵉ-v wkᵉ-r) m) })
       (λ m → ∈-map⁺ (_[ wkˢᵉ ]ᵠ) m)

↪-wkᵉⁿ : ∀ {Θ} {Q : Hyps Θ} → (k : ℕ) → Q ↪ᴴ wkᵉⁿ-H k Q [ wkˢⁿ k ]
↪-wkᵉⁿ zero    = ↪-refl
↪-wkᵉⁿ (suc k) = ↪-⨟ ↪-wkᵉ (↪-wkᵉⁿ k)

↪-↑ᵉ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'}
     → Q ↪ᴴ Q' [ σ ] → wkᵉ-H Q ↪ᴴ wkᵉ-H Q' [ σ ↑ᵉ ]
↪-↑ᵉ {Θ} {Θ'} {Q} {Q'} {σ} e = mk↪ᴴ et sb oR oE dj qh
  where
    et : ∀ {α} → α ∈ ets (wkᵉ-H Q) → Σ[ β ∈ TyVar (Θ' +e) ] ((sTy (σ ↑ᵉ) α ≡ tvar β) × (β ∈ ets (wkᵉ-H Q')))
    et m with ∈-map⁻ (wkᵉ-tv Θ) m
    ... | α₀ , m₀ , refl with ↪ets e m₀
    ...   | β , eq , m' = wkᵉ-tv Θ' β , cong wkᵉ-v eq , ∈-map⁺ (wkᵉ-tv Θ') m'

    sb : ∀ {α β} → (α , β) ∈ subᵥ (wkᵉ-H Q) → Σ[ α' ∈ TyVar (Θ' +e) ] Σ[ β' ∈ TyVar (Θ' +e) ] ((sTy (σ ↑ᵉ) α ≡ tvar α') × (sTy (σ ↑ᵉ) β ≡ tvar β') × ((α' , β') ∈ subᵥ (wkᵉ-H Q')))
    sb m with ∈-map⁻ (mapᵖ (wkᵉ-tv Θ)) m
    ... | (α₀ , β₀) , m₀ , refl with ↪subᵥ e m₀
    ...   | α' , β' , eα , eβ , m' =
            wkᵉ-tv Θ' α' , wkᵉ-tv Θ' β' , cong wkᵉ-v eα , cong wkᵉ-v eβ ,
            ∈-map⁺ (mapᵖ (wkᵉ-tv Θ')) m'

    oR : ∀ {p} → p ∈ ordᵣ (wkᵉ-H Q) → mapᵖ (_[ σ ↑ᵉ ]ʳ) p ∈ ordᵣ (wkᵉ-H Q')
    oR m with ∈-map⁻ (mapᵖ wkᵉ-r) m
    ... | (x , y) , m₀ , refl =
      subst (_∈ ordᵣ (wkᵉ-H Q')) (sym (cong₂ _,_ (wk-↑ᵉ-r σ x) (wk-↑ᵉ-r σ y)))
            (∈-map⁺ (mapᵖ wkᵉ-r) (↪ordᵣ e m₀))

    oE : ∀ {p} → p ∈ ordₑ (wkᵉ-H Q) → mapᵖ (_[ σ ↑ᵉ ]ᵉ) p ∈ ordₑ (wkᵉ-H Q')
    oE m with ∈-map⁻ (mapᵖ wkᵉ-e) m
    ... | (x , y) , m₀ , refl =
      subst (_∈ ordₑ (wkᵉ-H Q')) (sym (cong₂ _,_ (wk-↑ᵉ-e σ x) (wk-↑ᵉ-e σ y)))
            (∈-map⁺ (mapᵖ wkᵉ-e) (↪ordₑ e m₀))

    dj : ∀ {p} → p ∈ disj (wkᵉ-H Q) → mapᵈ (_[ σ ↑ᵉ ]ᵛ) (_[ σ ↑ᵉ ]ʳ) p ∈ disj (wkᵉ-H Q')
    dj m with ∈-map⁻ (mapᵈ wkᵉ-v wkᵉ-r) m
    ... | (A , ρ) , m₀ , refl =
      subst (_∈ disj (wkᵉ-H Q')) (sym (cong₂ _,_ (wk-↑ᵉ-v σ A) (wk-↑ᵉ-r σ ρ)))
            (∈-map⁺ (mapᵈ wkᵉ-v wkᵉ-r) (↪disj e m₀))

    qh : ∀ {O} → O ∈ qhyps (wkᵉ-H Q) → O [ σ ↑ᵉ ]ᵠ ∈ qhyps (wkᵉ-H Q')
    qh m with ∈-map⁻ (_[ wkˢᵉ ]ᵠ) m
    ... | O₀ , m₀ , refl =
      subst (_∈ qhyps (wkᵉ-H Q'))
            (trans ([⨟]ᵠ O₀ σ wkˢᵉ)
                   (trans (sym ([≐]ᵠ (wkˢᵉ-↑ᵉ σ) O₀)) (sym ([⨟]ᵠ O₀ wkˢᵉ (σ ↑ᵉ)))))
            (∈-map⁺ (_[ wkˢᵉ ]ᵠ) (↪qhyps e m₀))

↪-↑ᵉⁿ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} → (k : ℕ)
      → Q ↪ᴴ Q' [ σ ] → wkᵉⁿ-H k Q ↪ᴴ wkᵉⁿ-H k Q' [ σ ↑ᵉⁿ k ]
↪-↑ᵉⁿ zero    e = e
↪-↑ᵉⁿ (suc k) e = ↪-↑ᵉⁿ k (↪-↑ᵉ e)

-- Instantiating a fresh variable: the weakened set embeds along an
-- extension

↪-,ᵉ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {τ : Subst Θ Θ'} {ε : EExp Θ'}
     → Q ↪ᴴ Q' [ τ ] → wkᵉ-H Q ↪ᴴ Q' [ τ ,ᵉ ε ]
↪-,ᵉ {Θ} {Θ'} {Q} {Q'} {τ} {ε} e = mk↪ᴴ et sb oR oE dj qh
  where
    et : ∀ {α} → α ∈ ets (wkᵉ-H Q) → Σ[ β ∈ TyVar Θ' ] ((sTy (τ ,ᵉ ε) α ≡ tvar β) × (β ∈ ets Q'))
    et m with ∈-map⁻ (wkᵉ-tv Θ) m
    ... | α₀ , m₀ , refl = ↪ets e m₀

    sb : ∀ {α β} → (α , β) ∈ subᵥ (wkᵉ-H Q) → Σ[ α' ∈ TyVar Θ' ] Σ[ β' ∈ TyVar Θ' ] ((sTy (τ ,ᵉ ε) α ≡ tvar α') × (sTy (τ ,ᵉ ε) β ≡ tvar β') × ((α' , β') ∈ subᵥ Q'))
    sb m with ∈-map⁻ (mapᵖ (wkᵉ-tv Θ)) m
    ... | (α₀ , β₀) , m₀ , refl = ↪subᵥ e m₀

    oR : ∀ {p} → p ∈ ordᵣ (wkᵉ-H Q) → mapᵖ (_[ τ ,ᵉ ε ]ʳ) p ∈ ordᵣ Q'
    oR m with ∈-map⁻ (mapᵖ wkᵉ-r) m
    ... | (x , y) , m₀ , refl =
      subst (_∈ ordᵣ Q') (sym (cong₂ _,_ (wk-,ᵉ-r τ ε x) (wk-,ᵉ-r τ ε y))) (↪ordᵣ e m₀)

    oE : ∀ {p} → p ∈ ordₑ (wkᵉ-H Q) → mapᵖ (_[ τ ,ᵉ ε ]ᵉ) p ∈ ordₑ Q'
    oE m with ∈-map⁻ (mapᵖ wkᵉ-e) m
    ... | (x , y) , m₀ , refl =
      subst (_∈ ordₑ Q') (sym (cong₂ _,_ (wk-,ᵉ-e τ ε x) (wk-,ᵉ-e τ ε y))) (↪ordₑ e m₀)

    dj : ∀ {p} → p ∈ disj (wkᵉ-H Q) → mapᵈ (_[ τ ,ᵉ ε ]ᵛ) (_[ τ ,ᵉ ε ]ʳ) p ∈ disj Q'
    dj m with ∈-map⁻ (mapᵈ wkᵉ-v wkᵉ-r) m
    ... | (A , ρ) , m₀ , refl =
      subst (_∈ disj Q') (sym (cong₂ _,_ (wk-,ᵉ-v τ ε A) (wk-,ᵉ-r τ ε ρ))) (↪disj e m₀)

    qh : ∀ {O} → O ∈ qhyps (wkᵉ-H Q) → O [ τ ,ᵉ ε ]ᵠ ∈ qhyps Q'
    qh m with ∈-map⁻ (_[ wkˢᵉ ]ᵠ) m
    ... | O₀ , m₀ , refl =
      subst (_∈ qhyps Q') (sym (trans ([⨟]ᵠ O₀ wkˢᵉ (τ ,ᵉ ε)) ([≐]ᵠ (wkˢᵉ-,ᵉ τ ε) O₀)))
            (↪qhyps e m₀)

-- Instance maps: the identity, and instantiating fresh variables

⊩ᴵ-refl : ∀ {Θ} {Q : Hyps Θ} → Q ⊩ᴵ Q [ idˢ ]
⊩ᴵ-refl = ↪⇒⊩ᴵ ↪-refl

⊩ᴵ-,ᵉ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {τ : Subst Θ Θ'} {ε : EExp Θ'}
      → Q' ⊩ᴵ Q [ τ ] → Q' ⊩ᴵ wkᵉ-H Q [ τ ,ᵉ ε ]
⊩ᴵ-,ᵉ {Θ} {Θ'} {Q} {Q'} {τ} {ε} h = mk⊩ᴵ et sb oR oE dj qh
  where
    et : ∀ {α} → α ∈ ets (wkᵉ-H Q) → Q' ⊩ᴱ sTy (τ ,ᵉ ε) α
    et m with ∈-map⁻ (wkᵉ-tv Θ) m
    ... | α₀ , m₀ , refl = ⊩etsᴵ h m₀

    sb : ∀ {α β} → (α , β) ∈ subᵥ (wkᵉ-H Q) → Q' ∣ sTy (τ ,ᵉ ε) α <:̂ᵛ sTy (τ ,ᵉ ε) β
    sb m with ∈-map⁻ (mapᵖ (wkᵉ-tv Θ)) m
    ... | (α₀ , β₀) , m₀ , refl = ⊩subᵥᴵ h m₀

    oR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ (wkᵉ-H Q) → Q' ⊩ ρ [ τ ,ᵉ ε ]ʳ ≾̂ᵣ ρ' [ τ ,ᵉ ε ]ʳ
    oR m with ∈-map⁻ (mapᵖ wkᵉ-r) m
    ... | (x , y) , m₀ , refl =
      subst₂ (λ a b → Q' ⊩ a ≾̂ᵣ b) (sym (wk-,ᵉ-r τ ε x)) (sym (wk-,ᵉ-r τ ε y)) (⊩ordᵣᴵ h m₀)

    oE : ∀ {ε₁ ε₂} → (ε₁ , ε₂) ∈ ordₑ (wkᵉ-H Q) → Q' ⊩ ε₁ [ τ ,ᵉ ε ]ᵉ ≾̂ₑ ε₂ [ τ ,ᵉ ε ]ᵉ
    oE m with ∈-map⁻ (mapᵖ wkᵉ-e) m
    ... | (x , y) , m₀ , refl =
      subst₂ (λ a b → Q' ⊩ a ≾̂ₑ b) (sym (wk-,ᵉ-e τ ε x)) (sym (wk-,ᵉ-e τ ε y)) (⊩ordₑᴵ h m₀)

    dj : ∀ {A ρ} → (A , ρ) ∈ disj (wkᵉ-H Q) → VarOK Q' (A [ τ ,ᵉ ε ]ᵛ) (ρ [ τ ,ᵉ ε ]ʳ)
    dj m with ∈-map⁻ (mapᵈ wkᵉ-v wkᵉ-r) m
    ... | (A , ρ) , m₀ , refl =
      subst₂ (VarOK Q') (sym (wk-,ᵉ-v τ ε A)) (sym (wk-,ᵉ-r τ ε ρ)) (⊩disjᴵ h m₀)

    qh : ∀ {O} → O ∈ qhyps (wkᵉ-H Q) → (es : Vec (EExp Θ') (rigids O))
       → Q' ⊩ᵒ body O [ (τ ,ᵉ ε) ,ᵉⁿ es ]
    qh m es with ∈-map⁻ (_[ wkˢᵉ ]ᵠ) m
    ... | O₀ , m₀ , refl =
      ⊩ᵒ-subst⁻ (⊩ᵒ-resp-≐ˢ eq (⊩qhypsᴵ h m₀ es))
      where
        k = rigids O₀
        eq : (τ ,ᵉⁿ es) ≐ˢ ((wkˢᵉ ↑ᵉⁿ k) ⨟ˢ ((τ ,ᵉ ε) ,ᵉⁿ es))
        eq = ≐ˢ-sym (≐ˢ-trans (↑ᵉⁿ-,ᵉⁿ wkˢᵉ (τ ,ᵉ ε) k es) (≐ˢ-,ᵉⁿ (wkˢᵉ-,ᵉ τ ε) es))

⊩ᴵ-,ᵉⁿ : ∀ {Θ Θ' k} {Q : Hyps Θ} {Q' : Hyps Θ'} {τ : Subst Θ Θ'}
       → Q' ⊩ᴵ Q [ τ ] → (es : Vec (EExp Θ') k) → Q' ⊩ᴵ wkᵉⁿ-H k Q [ τ ,ᵉⁿ es ]
⊩ᴵ-,ᵉⁿ h []       = h
⊩ᴵ-,ᵉⁿ h (ε ∷ es) = ⊩ᴵ-,ᵉⁿ (⊩ᴵ-,ᵉ h) es

-- Entailment gives an instance map: a quantified hypothesis, entailed
-- at fresh rigids, is instantiated there

⊩ᴴ⇒ᴵ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'}
     → Q' ⊩ᴴ Q [ σ ] → Q' ⊩ᴵ Q [ σ ]
⊩ᴴ⇒ᴵ {σ = σ} h =
  mk⊩ᴵ (⊩ets h) (⊩subᵥ h) (⊩ordᵣ h) (⊩ordₑ h) (⊩disj h)
       (λ {O} m es → ⊩ᵒ-resp-≐ˢ (↑-inst σ (rigids O) es)
                                (⊩ᵒ-⨟ᴵ (⊩ᴵ-,ᵉⁿ ⊩ᴵ-refl es) (⊩qhyps h m)))

-- Substitution along entailment

⊩-substᵣ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {ρ ρ' : RExp Θ}
         → Q' ⊩ᴴ Q [ σ ] → Q ⊩ ρ ≾̂ᵣ ρ' → Q' ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ' [ σ ]ʳ
⊩-substᵣ h = ⊩-substᴵᵣ (⊩ᴴ⇒ᴵ h)

⊩-substₑ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {ε ε' : EExp Θ}
         → Q' ⊩ᴴ Q [ σ ] → Q ⊩ ε ≾̂ₑ ε' → Q' ⊩ ε [ σ ]ᵉ ≾̂ₑ ε' [ σ ]ᵉ
⊩-substₑ h = ⊩-substᴵₑ (⊩ᴴ⇒ᴵ h)

⊩ᵗᵛ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {α β}
          → Q' ⊩ᴴ Q [ σ ] → Q ⊩ᵗᵛ α ≾ β → Q' ∣ sTy σ α <:̂ᵛ sTy σ β
⊩ᵗᵛ-subst h = ⊩ᵗᵛ-substᴵ (⊩ᴴ⇒ᴵ h)

⊩ᴱ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {A : OVType Θ}
         → Q' ⊩ᴴ Q [ σ ] → Q ⊩ᴱ A → Q' ⊩ᴱ A [ σ ]ᵛ
⊩ᴱ-subst h = ⊩ᴱ-substᴵ (⊩ᴴ⇒ᴵ h)

VarOK-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'}
                {A : OVType Θ} {ρ : RExp Θ}
            → Q' ⊩ᴴ Q [ σ ] → VarOK Q A ρ → VarOK Q' (A [ σ ]ᵛ) (ρ [ σ ]ʳ)
VarOK-subst h = VarOK-substᴵ (⊩ᴴ⇒ᴵ h)

<:̂ᵛ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {A A' : OVType Θ}
          → Q' ⊩ᴴ Q [ σ ] → Q ∣ A <:̂ᵛ A' → Q' ∣ A [ σ ]ᵛ <:̂ᵛ A' [ σ ]ᵛ
<:̂ᵛ-subst h = <:̂ᵛ-substᴵ (⊩ᴴ⇒ᴵ h)

<:̂ᶜ-subst : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} {C C' : OCType Θ}
          → Q' ⊩ᴴ Q [ σ ] → Q ∣ C <:̂ᶜ C' → Q' ∣ C [ σ ]ᶜ <:̂ᶜ C' [ σ ]ᶜ
<:̂ᶜ-subst h = <:̂ᶜ-substᴵ (⊩ᴴ⇒ᴵ h)

⊩ᵒ-⨟ : ∀ {Ψ Ψ' Ψ''} {Q : Hyps Ψ'} {Q' : Hyps Ψ''} {o : Ords Ψ}
         {δ : Subst Ψ Ψ'} {δ' : Subst Ψ' Ψ''}
     → Q' ⊩ᴴ Q [ δ' ] → Q ⊩ᵒ o [ δ ] → Q' ⊩ᵒ o [ δ ⨟ˢ δ' ]
⊩ᵒ-⨟ g = ⊩ᵒ-⨟ᴵ (⊩ᴴ⇒ᴵ g)

-- A hypothesis is entailed: a quantified one by its instance at the
-- fresh rigids

⊩ᴼ-hyp : ∀ {Θ Θ'} {Q' : Hyps Θ'} {σ : Subst Θ Θ'} → (O : QOrd Θ)
       → O [ σ ]ᵠ ∈ qhyps Q' → Q' ⊩ᴼ O [ σ ]
⊩ᴼ-hyp {Θ' = Θ'} {Q'} {σ} O m = mk⊩ᵒ r e
  where
    k = rigids O

    m' : O [ σ ⨟ˢ wkˢⁿ k ]ᵠ ∈ qhyps (wkᵉⁿ-H k Q')
    m' = subst (_∈ qhyps (wkᵉⁿ-H k Q')) ([⨟]ᵠ O σ (wkˢⁿ k)) (↪qhyps (↪-wkᵉⁿ k) m)

    eq : (((σ ⨟ˢ wkˢⁿ k) ↑ᵉⁿ k) ⨟ˢ (idˢ ,ᵉⁿ varsⁿ k)) ≐ˢ (σ ↑ᵉⁿ k)
    eq = ≐ˢ-trans (↑-inst (σ ⨟ˢ wkˢⁿ k) k (varsⁿ k)) (↑ᵉⁿ-vars σ k)

    r : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors (body O)
      → wkᵉⁿ-H k Q' ⊩ ρ [ σ ↑ᵉⁿ k ]ʳ ≾̂ᵣ ρ' [ σ ↑ᵉⁿ k ]ʳ
    r {ρ} {ρ'} mφ =
      subst₂ (λ x y → wkᵉⁿ-H k Q' ⊩ x ≾̂ᵣ y)
             (trans ([⨟]ʳ ρ ((σ ⨟ˢ wkˢⁿ k) ↑ᵉⁿ k) (idˢ ,ᵉⁿ varsⁿ k)) ([≐]ʳ eq ρ))
             (trans ([⨟]ʳ ρ' ((σ ⨟ˢ wkˢⁿ k) ↑ᵉⁿ k) (idˢ ,ᵉⁿ varsⁿ k)) ([≐]ʳ eq ρ'))
             (instᵣ m' (∈-map⁺ (mapᵖ (_[ (σ ⨟ˢ wkˢⁿ k) ↑ᵉⁿ k ]ʳ)) mφ) (varsⁿ k))

    e : ∀ {ε ε'} → (ε , ε') ∈ oes (body O)
      → wkᵉⁿ-H k Q' ⊩ ε [ σ ↑ᵉⁿ k ]ᵉ ≾̂ₑ ε' [ σ ↑ᵉⁿ k ]ᵉ
    e {ε} {ε'} mφ =
      subst₂ (λ x y → wkᵉⁿ-H k Q' ⊩ x ≾̂ₑ y)
             (trans ([⨟]ᵉ ε ((σ ⨟ˢ wkˢⁿ k) ↑ᵉⁿ k) (idˢ ,ᵉⁿ varsⁿ k)) ([≐]ᵉ eq ε))
             (trans ([⨟]ᵉ ε' ((σ ⨟ˢ wkˢⁿ k) ↑ᵉⁿ k) (idˢ ,ᵉⁿ varsⁿ k)) ([≐]ᵉ eq ε'))
             (instₑ m' (∈-map⁺ (mapᵖ (_[ (σ ⨟ˢ wkˢⁿ k) ↑ᵉⁿ k ]ᵉ)) mφ) (varsⁿ k))

-- An embedding gives entailment

↪⇒⊩ᴴ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'}
     → Q ↪ᴴ Q' [ σ ] → Q' ⊩ᴴ Q [ σ ]
↪⇒⊩ᴴ e = let h = ↪⇒⊩ᴵ e in
  mk⊩ᴴ (⊩etsᴵ h) (⊩subᵥᴵ h) (⊩ordᵣᴵ h) (⊩ordₑᴵ h) (⊩disjᴵ h)
       (λ {O} m → ⊩ᴼ-hyp O (↪qhyps e m))

⊩ᴴ-refl : ∀ {Θ} {Q : Hyps Θ} → Q ⊩ᴴ Q [ idˢ ]
⊩ᴴ-refl = ↪⇒⊩ᴴ ↪-refl

-- What the empty set entails, every set entails

∅⇒≾ᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → ∅ᴴ ⊩ ρ ≾̂ᵣ ρ' → Q ⊩ ρ ≾̂ᵣ ρ'
∅⇒≾ᵣ {Q = Q} {ρ} {ρ'} p =
  subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([id]ʳ ρ) ([id]ʳ ρ') (⊩-substᴵᵣ (⊩ᴵ-∅ {σ = idˢ}) p)

∅⇒≾ₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → ∅ᴴ ⊩ ε ≾̂ₑ ε' → Q ⊩ ε ≾̂ₑ ε'
∅⇒≾ₑ {Q = Q} {ε} {ε'} p =
  subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([id]ᵉ ε) ([id]ᵉ ε') (⊩-substᴵₑ (⊩ᴵ-∅ {σ = idˢ}) p)

∅⇒⊩ᴱ : ∀ {Θ} {Q : Hyps Θ} {A} → ∅ᴴ ⊩ᴱ A → Q ⊩ᴱ A
∅⇒⊩ᴱ {Q = Q} {A} et = subst (Q ⊩ᴱ_) ([id]ᵛ A) (⊩ᴱ-substᴵ (⊩ᴵ-∅ {σ = idˢ}) et)

∅⇒<:̂ᵛ : ∀ {Θ} {Q : Hyps Θ} {A B} → ∅ᴴ ∣ A <:̂ᵛ B → Q ∣ A <:̂ᵛ B
∅⇒<:̂ᵛ {Q = Q} {A} {B} p =
  subst₂ (Q ∣_<:̂ᵛ_) ([id]ᵛ A) ([id]ᵛ B) (<:̂ᵛ-substᴵ (⊩ᴵ-∅ {σ = idˢ}) p)

∅⇒<:̂ᶜ : ∀ {Θ} {Q : Hyps Θ} {C D} → ∅ᴴ ∣ C <:̂ᶜ D → Q ∣ C <:̂ᶜ D
∅⇒<:̂ᶜ {Q = Q} {C} {D} p =
  subst₂ (Q ∣_<:̂ᶜ_) ([id]ᶜ C) ([id]ᶜ D) (<:̂ᶜ-substᴵ (⊩ᴵ-∅ {σ = idˢ}) p)

∅⇒VarOK : ∀ {Θ} {Q : Hyps Θ} {A ρ} → VarOK ∅ᴴ A ρ → VarOK Q A ρ
∅⇒VarOK {Q = Q} {A} {ρ} ok =
  subst₂ (VarOK Q) ([id]ᵛ A) ([id]ʳ ρ) (VarOK-substᴵ (⊩ᴵ-∅ {σ = idˢ}) ok)

-- A quantified hypothesis of the set itself

⊩ᴼ-hyp⁼ : ∀ {Θ} {Q : Hyps Θ} {O : QOrd Θ} → O ∈ qhyps Q → Q ⊩ᴼ O [ idˢ ]
⊩ᴼ-hyp⁼ {Q = Q} {O} m = ⊩ᴼ-hyp O (subst (_∈ qhyps Q) (sym ([id]ᵠ O)) m)

-- Entailment between sets over one scope, field by field

mk⊩ᴴ⁼ : ∀ {Θ} {Q Q' : Hyps Θ}
      → (∀ {α} → α ∈ ets Q → Q' ⊩ᴱ tvar α)
      → (∀ {α β} → (α , β) ∈ subᵥ Q → Q' ∣ tvar α <:̂ᵛ tvar β)
      → (∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q' ⊩ ρ ≾̂ᵣ ρ')
      → (∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q' ⊩ ε ≾̂ₑ ε')
      → (∀ {A ρ} → (A , ρ) ∈ disj Q → VarOK Q' A ρ)
      → (∀ {O} → O ∈ qhyps Q → Q' ⊩ᴼ O [ idˢ ])
      → Q' ⊩ᴴ Q
mk⊩ᴴ⁼ {Q' = Q'} et sb oR oE dj qh =
  mk⊩ᴴ et sb
       (λ {ρ} {ρ'} m →
          subst₂ (λ x y → Q' ⊩ x ≾̂ᵣ y) (sym ([id]ʳ ρ)) (sym ([id]ʳ ρ')) (oR m))
       (λ {ε} {ε'} m →
          subst₂ (λ x y → Q' ⊩ x ≾̂ₑ y) (sym ([id]ᵉ ε)) (sym ([id]ᵉ ε')) (oE m))
       (λ {A} {ρ} m → subst₂ (VarOK Q') (sym ([id]ᵛ A)) (sym ([id]ʳ ρ)) (dj m))
       qh

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
    ⊆ets    : ∀ {α} → α ∈ ets Q → α ∈ ets Q'
    ⊆subᵥ   : ∀ {p} → p ∈ subᵥ Q → p ∈ subᵥ Q'
    ⊆ordᵣ   : ∀ {p} → p ∈ ordᵣ Q → p ∈ ordᵣ Q'
    ⊆ordₑ   : ∀ {p} → p ∈ ordₑ Q → p ∈ ordₑ Q'
    ⊆disj   : ∀ {p} → p ∈ disj Q → p ∈ disj Q'
    ⊆qhyps  : ∀ {O} → O ∈ qhyps Q → O ∈ qhyps Q'

open _⊆ᴴ_ public

⊆ᴴ-⊩ : ∀ {Θ} {Q Q' : Hyps Θ} → Q ⊆ᴴ Q' → Q' ⊩ᴴ Q
⊆ᴴ-⊩ s = mk⊩ᴴ⁼ (λ m → et-hyp (⊆ets s m)) (λ m → tvarₛ (hypᵗᵛ (⊆subᵥ s m)))
                (λ m → hypᵣ (⊆ordᵣ s m)) (λ m → hypₑ (⊆ordₑ s m))
                (λ m → hyp-ok₀ (⊆disj s m)) (λ m → ⊩ᴼ-hyp⁼ (⊆qhyps s m))

-- Weakening a hypothesis set is the action of the weakening substitution,
-- so entailment is stable under it.

⊩ᴴ-wkᵗ : ∀ {Θ} {Q : Hyps Θ} → wkᵗ-H Q ⊩ᴴ Q [ wkˢᵗ ]
⊩ᴴ-wkᵗ = ↪⇒⊩ᴴ ↪-wkᵗ

⊩ᴴ-wkʳ : ∀ {Θ} {Q : Hyps Θ} → wkʳ-H Q ⊩ᴴ Q [ wkˢʳ ]
⊩ᴴ-wkʳ = ↪⇒⊩ᴴ ↪-wkʳ

⊩ᴴ-wkᵉ : ∀ {Θ} {Q : Hyps Θ} → wkᵉ-H Q ⊩ᴴ Q [ wkˢᵉ ]
⊩ᴴ-wkᵉ = ↪⇒⊩ᴴ ↪-wkᵉ

-- A weakened set, its fresh variable instantiated, is entailed by the
-- set itself

⊩ᴴ-wkᵉ-,ᵉ : ∀ {Θ} {Q : Hyps Θ} → (ε : EExp Θ) → Q ⊩ᴴ wkᵉ-H Q [ idˢ ,ᵉ ε ]
⊩ᴴ-wkᵉ-,ᵉ ε = ↪⇒⊩ᴴ (↪-,ᵉ ↪-refl)

-- Entailment is preserved by the scope extensions

⊩-wkᵗᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ ≾̂ᵣ ρ' → wkᵗ-H Q ⊩ wkᵗ-r ρ ≾̂ᵣ wkᵗ-r ρ'
⊩-wkᵗᵣ {Q = Q} {ρ} {ρ'} p =
  subst₂ (λ x y → wkᵗ-H Q ⊩ x ≾̂ᵣ y) (wkˢᵗ-r ρ) (wkˢᵗ-r ρ') (⊩-substᴵᵣ (↪⇒⊩ᴵ ↪-wkᵗ) p)

⊩-wkᵗₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → wkᵗ-H Q ⊩ wkᵗ-e ε ≾̂ₑ wkᵗ-e ε'
⊩-wkᵗₑ {Q = Q} {ε} {ε'} p =
  subst₂ (λ x y → wkᵗ-H Q ⊩ x ≾̂ₑ y) (wkˢᵗ-e ε) (wkˢᵗ-e ε') (⊩-substᴵₑ (↪⇒⊩ᴵ ↪-wkᵗ) p)

⊩ᴱ-wkᵗ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ⊩ᴱ A → wkᵗ-H Q ⊩ᴱ wkᵗ-v A
⊩ᴱ-wkᵗ {Q = Q} {A} et =
  subst (λ x → wkᵗ-H Q ⊩ᴱ x) (wkˢᵗ-v A) (⊩ᴱ-substᴵ (↪⇒⊩ᴵ ↪-wkᵗ) et)

<:̂ᵛ-wkᵗ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkᵗ-H Q ∣ wkᵗ-v A <:̂ᵛ wkᵗ-v A'
<:̂ᵛ-wkᵗ {Q = Q} {A} {A'} p =
  subst₂ (wkᵗ-H Q ∣_<:̂ᵛ_) (wkˢᵗ-v A) (wkˢᵗ-v A') (<:̂ᵛ-substᴵ (↪⇒⊩ᴵ ↪-wkᵗ) p)

⊩-wkʳᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ ≾̂ᵣ ρ' → wkʳ-H Q ⊩ wkʳ-r ρ ≾̂ᵣ wkʳ-r ρ'
⊩-wkʳᵣ {Q = Q} {ρ} {ρ'} p =
  subst₂ (λ x y → wkʳ-H Q ⊩ x ≾̂ᵣ y) (wkˢʳ-r ρ) (wkˢʳ-r ρ') (⊩-substᴵᵣ (↪⇒⊩ᴵ ↪-wkʳ) p)

⊩-wkʳₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → wkʳ-H Q ⊩ wkʳ-e ε ≾̂ₑ wkʳ-e ε'
⊩-wkʳₑ {Q = Q} {ε} {ε'} p =
  subst₂ (λ x y → wkʳ-H Q ⊩ x ≾̂ₑ y) (wkˢʳ-e ε) (wkˢʳ-e ε') (⊩-substᴵₑ (↪⇒⊩ᴵ ↪-wkʳ) p)

⊩ᴱ-wkʳ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ⊩ᴱ A → wkʳ-H Q ⊩ᴱ wkʳ-v A
⊩ᴱ-wkʳ {Q = Q} {A} et =
  subst (λ x → wkʳ-H Q ⊩ᴱ x) (wkˢʳ-v A) (⊩ᴱ-substᴵ (↪⇒⊩ᴵ ↪-wkʳ) et)

<:̂ᵛ-wkʳ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkʳ-H Q ∣ wkʳ-v A <:̂ᵛ wkʳ-v A'
<:̂ᵛ-wkʳ {Q = Q} {A} {A'} p =
  subst₂ (wkʳ-H Q ∣_<:̂ᵛ_) (wkˢʳ-v A) (wkˢʳ-v A') (<:̂ᵛ-substᴵ (↪⇒⊩ᴵ ↪-wkʳ) p)

⊩-wkᵉᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ ≾̂ᵣ ρ' → wkᵉ-H Q ⊩ wkᵉ-r ρ ≾̂ᵣ wkᵉ-r ρ'
⊩-wkᵉᵣ {Q = Q} {ρ} {ρ'} p =
  subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y) (wkˢᵉ-r ρ) (wkˢᵉ-r ρ') (⊩-substᴵᵣ (↪⇒⊩ᴵ ↪-wkᵉ) p)

⊩-wkᵉₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → wkᵉ-H Q ⊩ wkᵉ-e ε ≾̂ₑ wkᵉ-e ε'
⊩-wkᵉₑ {Q = Q} {ε} {ε'} p =
  subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y) (wkˢᵉ-e ε) (wkˢᵉ-e ε') (⊩-substᴵₑ (↪⇒⊩ᴵ ↪-wkᵉ) p)

⊩ᴱ-wkᵉ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ⊩ᴱ A → wkᵉ-H Q ⊩ᴱ wkᵉ-v A
⊩ᴱ-wkᵉ {Q = Q} {A} et =
  subst (λ x → wkᵉ-H Q ⊩ᴱ x) (wkˢᵉ-v A) (⊩ᴱ-substᴵ (↪⇒⊩ᴵ ↪-wkᵉ) et)

VarOK-wkᵉ : ∀ {Θ} {Q : Hyps Θ} {A ρ}
          → VarOK Q A ρ → VarOK (wkᵉ-H Q) (wkᵉ-v A) (wkᵉ-r ρ)
VarOK-wkᵉ {Q = Q} {A} {ρ} ok =
  subst₂ (VarOK (wkᵉ-H Q)) (wkˢᵉ-v A) (wkˢᵉ-r ρ) (VarOK-substᴵ (↪⇒⊩ᴵ ↪-wkᵉ) ok)

<:̂ᵛ-wkᵉ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkᵉ-H Q ∣ wkᵉ-v A <:̂ᵛ wkᵉ-v A'
<:̂ᵛ-wkᵉ {Q = Q} {A} {A'} p =
  subst₂ (wkᵉ-H Q ∣_<:̂ᵛ_) (wkˢᵉ-v A) (wkˢᵉ-v A') (<:̂ᵛ-substᴵ (↪⇒⊩ᴵ ↪-wkᵉ) p)

-- Entailment is stable under lifting over an effect-grade variable

⊩ᴴ-↑ᵉ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {δ : Subst Θ Θ'}
      → Q' ⊩ᴴ Q [ δ ] → wkᵉ-H Q' ⊩ᴴ (wkᵉ-H Q) [ δ ↑ᵉ ]
⊩ᴴ-↑ᵉ {Θ} {Θ'} {Q} {Q'} {δ} h = mk⊩ᴴ ets↑ subᵥ↑ ordᵣ↑ ordₑ↑ disj↑ qhyps↑
  where
    ets↑ : ∀ {α} → α ∈ ets (wkᵉ-H Q) → wkᵉ-H Q' ⊩ᴱ sTy (δ ↑ᵉ) α
    ets↑ m with ∈-map⁻ (wkᵉ-tv Θ) m
    ... | α₀ , m₀ , refl = ⊩ᴱ-wkᵉ (⊩ets h m₀)

    subᵥ↑ : ∀ {α β} → (α , β) ∈ subᵥ (wkᵉ-H Q)
          → wkᵉ-H Q' ∣ sTy (δ ↑ᵉ) α <:̂ᵛ sTy (δ ↑ᵉ) β
    subᵥ↑ m with ∈-map⁻ (mapᵖ (wkᵉ-tv Θ)) m
    ... | (α₀ , β₀) , m₀ , refl = <:̂ᵛ-wkᵉ (⊩subᵥ h m₀)

    ordᵣ↑ : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ (wkᵉ-H Q)
          → wkᵉ-H Q' ⊩ ρ [ δ ↑ᵉ ]ʳ ≾̂ᵣ ρ' [ δ ↑ᵉ ]ʳ
    ordᵣ↑ m with ∈-map⁻ (mapᵖ wkᵉ-r) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
      subst₂ (λ x y → wkᵉ-H Q' ⊩ x ≾̂ᵣ y)
             (sym (wk-↑ᵉ-r δ ρ₀)) (sym (wk-↑ᵉ-r δ ρ₀'))
             (⊩-wkᵉᵣ (⊩ordᵣ h m₀))

    ordₑ↑ : ∀ {ε ε'} → (ε , ε') ∈ ordₑ (wkᵉ-H Q)
          → wkᵉ-H Q' ⊩ ε [ δ ↑ᵉ ]ᵉ ≾̂ₑ ε' [ δ ↑ᵉ ]ᵉ
    ordₑ↑ m with ∈-map⁻ (mapᵖ wkᵉ-e) m
    ... | (ε₀ , ε₀') , m₀ , refl =
      subst₂ (λ x y → wkᵉ-H Q' ⊩ x ≾̂ₑ y)
             (sym (wk-↑ᵉ-e δ ε₀)) (sym (wk-↑ᵉ-e δ ε₀'))
             (⊩-wkᵉₑ (⊩ordₑ h m₀))

    disj↑ : ∀ {A ρ} → (A , ρ) ∈ disj (wkᵉ-H Q)
          → VarOK (wkᵉ-H Q') (A [ δ ↑ᵉ ]ᵛ) (ρ [ δ ↑ᵉ ]ʳ)
    disj↑ m with ∈-map⁻ (mapᵈ wkᵉ-v wkᵉ-r) m
    ... | (A₀ , ρ₀) , m₀ , refl =
      subst₂ (VarOK (wkᵉ-H Q'))
             (sym (wk-↑ᵉ-v δ A₀)) (sym (wk-↑ᵉ-r δ ρ₀))
             (VarOK-wkᵉ (⊩disj h m₀))

    qhyps↑ : ∀ {O} → O ∈ qhyps (wkᵉ-H Q) → wkᵉ-H Q' ⊩ᴼ O [ δ ↑ᵉ ]
    qhyps↑ m with ∈-map⁻ (_[ wkˢᵉ ]ᵠ) m
    ... | O₀ , m₀ , refl =
      ⊩ᵒ-subst⁻ (⊩ᵒ-resp-≐ˢ eq (⊩ᵒ-⨟ᴵ (↪⇒⊩ᴵ (↪-↑ᵉⁿ k ↪-wkᵉ)) (⊩qhyps h m₀)))
      where
        k = rigids O₀
        eq : ((δ ↑ᵉⁿ k) ⨟ˢ (wkˢᵉ ↑ᵉⁿ k)) ≐ˢ ((wkˢᵉ ↑ᵉⁿ k) ⨟ˢ ((δ ↑ᵉ) ↑ᵉⁿ k))
        eq = ≐ˢ-trans (⨟-↑ᵉⁿ δ wkˢᵉ k)
             (≐ˢ-trans (≐ˢ-↑ᵉⁿ (≐ˢ-sym (wkˢᵉ-↑ᵉ δ)) k)
                       (≐ˢ-sym (⨟-↑ᵉⁿ wkˢᵉ (δ ↑ᵉ) k)))

⊩ᴴ-↑ᵉⁿ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {δ : Subst Θ Θ'} → (k : ℕ)
       → Q' ⊩ᴴ Q [ δ ] → wkᵉⁿ-H k Q' ⊩ᴴ wkᵉⁿ-H k Q [ δ ↑ᵉⁿ k ]
⊩ᴴ-↑ᵉⁿ zero    h = h
⊩ᴴ-↑ᵉⁿ (suc k) h = ⊩ᴴ-↑ᵉⁿ k (⊩ᴴ-↑ᵉ h)

⊩ᴼ-⨟ : ∀ {Θ Ξ Ξ'} {Q : Hyps Ξ} {Q' : Hyps Ξ'} {δ : Subst Θ Ξ} {δ' : Subst Ξ Ξ'}
     → (O : QOrd Θ) → Q' ⊩ᴴ Q [ δ' ] → Q ⊩ᴼ O [ δ ] → Q' ⊩ᴼ O [ δ ⨟ˢ δ' ]
⊩ᴼ-⨟ {δ = δ} {δ'} (qord l k o) g h =
  ⊩ᵒ-resp-≐ˢ (⨟-↑ᵉⁿ δ δ' k) (⊩ᵒ-⨟ (⊩ᴴ-↑ᵉⁿ k g) h)

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
       (λ {O} m → ⊩ᴼ-⨟ O h' (⊩qhyps h m))

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
       (λ {O} m → ⊩ᴼ-resp-≐ˢ O p (⊩qhyps h m))


-- Grade expressions are monotone in their variables

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

-- Rule Gen is semantic consequence: a set entails a quantified ordering
-- along `σ` exactly when it holds at every instance of its rigids

infix 4 _⊨ᴼ_[_]

_⊨ᴼ_[_] : ∀ {Θ Ξ} → Hyps Ξ → QOrd Θ → Subst Θ Ξ → Set
_⊨ᴼ_[_] {Ξ = Ξ} Q O σ = (δ : Subst Ξ ∅ˢ) → δ ⊨ᵍ Q
                      → (es : Vec (EExp ∅ˢ) (rigids O)) → ((σ ⨟ˢ δ) ,ᵉⁿ es) ⊨ᵒ body O

⊩ᴼ⇒⊨ᴼ : ∀ {Θ Ξ} {Q : Hyps Ξ} {σ : Subst Θ Ξ} → (O : QOrd Θ) → Q ⊩ᴼ O [ σ ] → Q ⊨ᴼ O [ σ ]
⊩ᴼ⇒⊨ᴼ {Θ} {Ξ} {Q} {σ} O h δ hδ es = mk⊨ᵒ r e
  where
    k   = rigids O
    es' = mapᵛ (_[ from∅ {Ξ} ]ᵉ) es

    h' : ((idˢ ,ᵉⁿ es') ⨟ˢ δ) ⊨ᵍ wkᵉⁿ-H k Q
    h' = ⊨ᵍ-⨟ (⊩ᴵ-,ᵉⁿ ⊩ᴵ-refl es') hδ

    p : ((σ ↑ᵉⁿ k) ⨟ˢ ((idˢ ,ᵉⁿ es') ⨟ˢ δ)) ≐ˢ ((σ ⨟ˢ δ) ,ᵉⁿ es)
    p = ≐ˢ-trans (⨟-congʳ (σ ↑ᵉⁿ k)
                   (subst (λ v → ((idˢ ,ᵉⁿ es') ⨟ˢ δ) ≐ˢ (δ ,ᵉⁿ v)) (closed-backs δ es)
                          (inst-⨟ es' δ)))
                 (↑ᵉⁿ-,ᵉⁿ σ δ k es)

    r : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors (body O)
      → valʳ (ρ [ (σ ⨟ˢ δ) ,ᵉⁿ es ]ʳ) ≾ᵣ valʳ (ρ' [ (σ ⨟ˢ δ) ,ᵉⁿ es ]ʳ)
    r {ρ} {ρ'} mφ =
      subst₂ _≾ᵣ_ (cong valʳ (trans ([⨟]ʳ ρ (σ ↑ᵉⁿ k) _) ([≐]ʳ p ρ)))
                  (cong valʳ (trans ([⨟]ʳ ρ' (σ ↑ᵉⁿ k) _) ([≐]ʳ p ρ')))
             (runᵣ (⊩ors h mφ) ((idˢ ,ᵉⁿ es') ⨟ˢ δ) h')

    e : ∀ {ε ε'} → (ε , ε') ∈ oes (body O)
      → valᵉ (ε [ (σ ⨟ˢ δ) ,ᵉⁿ es ]ᵉ) ≾ₑ valᵉ (ε' [ (σ ⨟ˢ δ) ,ᵉⁿ es ]ᵉ)
    e {ε} {ε'} mφ =
      subst₂ _≾ₑ_ (cong valᵉ (trans ([⨟]ᵉ ε (σ ↑ᵉⁿ k) _) ([≐]ᵉ p ε)))
                  (cong valᵉ (trans ([⨟]ᵉ ε' (σ ↑ᵉⁿ k) _) ([≐]ᵉ p ε')))
             (runₑ (⊩oes h mφ) ((idˢ ,ᵉⁿ es') ⨟ˢ δ) h')

⊨ᴼ⇒⊩ᴼ : ∀ {Θ Ξ} {Q : Hyps Ξ} {σ : Subst Θ Ξ} → (O : QOrd Θ) → Q ⊨ᴼ O [ σ ] → Q ⊩ᴼ O [ σ ]
⊨ᴼ⇒⊩ᴼ {Θ} {Ξ} {Q} {σ} O H = mk⊩ᵒ r e
  where
    k = rigids O

    -- a closed instance of the scope under the rigids is one of the
    -- scope, extended by one of the rigids
    δ₀ : Subst (Ξ +eⁿ k) ∅ˢ → Subst Ξ ∅ˢ
    δ₀ δ = wkˢⁿ k ⨟ˢ δ

    es : Subst (Ξ +eⁿ k) ∅ˢ → Vec (EExp ∅ˢ) k
    es δ = mapᵛ (_[ δ ]ᵉ) (varsⁿ k)

    s : (δ : Subst (Ξ +eⁿ k) ∅ˢ) → δ ⊨ᵍ wkᵉⁿ-H k Q → ((σ ⨟ˢ δ₀ δ) ,ᵉⁿ es δ) ⊨ᵒ body O
    s δ h = H (δ₀ δ) (⊨ᵍ-⨟ (↪⇒⊩ᴵ (↪-wkᵉⁿ k)) h) (es δ)

    p : (δ : Subst (Ξ +eⁿ k) ∅ˢ) → ((σ ↑ᵉⁿ k) ⨟ˢ δ) ≐ˢ ((σ ⨟ˢ δ₀ δ) ,ᵉⁿ es δ)
    p δ = ≐ˢ-trans (⨟-congʳ (σ ↑ᵉⁿ k) (wkˢⁿ-split k δ)) (↑ᵉⁿ-,ᵉⁿ σ (δ₀ δ) k (es δ))

    r : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors (body O)
      → wkᵉⁿ-H k Q ⊩ ρ [ σ ↑ᵉⁿ k ]ʳ ≾̂ᵣ ρ' [ σ ↑ᵉⁿ k ]ʳ
    r {ρ} {ρ'} mφ = semᵣ λ δ h →
      subst₂ _≾ᵣ_ (cong valʳ (sym (trans ([⨟]ʳ ρ (σ ↑ᵉⁿ k) δ) ([≐]ʳ (p δ) ρ))))
                  (cong valʳ (sym (trans ([⨟]ʳ ρ' (σ ↑ᵉⁿ k) δ) ([≐]ʳ (p δ) ρ'))))
             (⊨ᵒʳ (s δ h) mφ)

    e : ∀ {ε ε'} → (ε , ε') ∈ oes (body O)
      → wkᵉⁿ-H k Q ⊩ ε [ σ ↑ᵉⁿ k ]ᵉ ≾̂ₑ ε' [ σ ↑ᵉⁿ k ]ᵉ
    e {ε} {ε'} mφ = semₑ λ δ h →
      subst₂ _≾ₑ_ (cong valᵉ (sym (trans ([⨟]ᵉ ε (σ ↑ᵉⁿ k) δ) ([≐]ᵉ (p δ) ε))))
                  (cong valᵉ (sym (trans ([⨟]ᵉ ε' (σ ↑ᵉⁿ k) δ) ([≐]ᵉ (p δ) ε'))))
             (⊨ᵒᵉ (s δ h) mφ)
