------------------------------------------------------------------
-- Closed instances of the open system                            --
--                                                                --
-- A closed instance of a scope `Θ` is a substitution             --
-- `δ : Subst Θ ∅ˢ`. Meaning is derivability in the open calculus --
-- at closed instances, each rigid of a clause kept a parameter.  --
-- An obligation `∀ᵉ j₁ … jₖ. Q` is a hypothesis set over the     --
-- scope extended by `k` rigids, and is entailed along a          --
-- substitution when its body is, at fresh rigids, by the         --
-- hypotheses weakened to them (`_⊩ᴼ_[_]`); a hypothesis set is   --
-- the obligation binding none. A closed instance satisfies       --
-- hypotheses and obligations when no hypotheses entail them      --
-- (`_⊨_∣_`). A set entails another semantically, `Q ⊨ᴴ Q'`, when --
-- every closed instance of the one is one of the other; open     --
-- entailment implies it.                                         --
--                                                                --
-- A closed grade expression has a value in the carrier. Entailed --
-- ordering between closed expressions is exactly the carrier's   --
-- ordering of their values, and convertibility is equality of    --
-- values. Closed subtyping, closed eternality and the closed     --
-- var-rule disjunction are decidable.                            --
------------------------------------------------------------------

open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Maybe.Base using (Maybe; nothing)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_)

open import Syntax.BaseTypes
open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.OpenSyntax.Instances (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open BaseTypes BTs using (_≡ᵇ?_; eternalBaseType?)
open Operations Ops using (Op)

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S

------------------------------------------------------------------------
-- Obligations

infixl 30 _+eⁿ_ _↑ᵉⁿ_

-- The rigids are bound outermost first: the scope extended by `k + 1`
-- rigids is the scope extended by one, then by `k`.

_+eⁿ_ : Scope → ℕ → Scope
Θ +eⁿ zero  = Θ
Θ +eⁿ suc k = (Θ +e) +eⁿ k

_↑ᵉⁿ_ : ∀ {Θ Θ'} → Subst Θ Θ' → (k : ℕ) → Subst (Θ +eⁿ k) (Θ' +eⁿ k)
σ ↑ᵉⁿ zero  = σ
σ ↑ᵉⁿ suc k = (σ ↑ᵉ) ↑ᵉⁿ k

wkᵉⁿ-H : ∀ {Θ} → (k : ℕ) → Hyps Θ → Hyps (Θ +eⁿ k)
wkᵉⁿ-H zero    Q = Q
wkᵉⁿ-H (suc k) Q = wkᵉⁿ-H k (wkᵉ-H Q)

≐ˢ-↑ᵉⁿ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → (k : ℕ) → (σ ↑ᵉⁿ k) ≐ˢ (σ' ↑ᵉⁿ k)
≐ˢ-↑ᵉⁿ p zero    = p
≐ˢ-↑ᵉⁿ p (suc k) = ≐ˢ-↑ᵉⁿ (≐ˢ-↑ᵉ p) k

-- A deferred rigid condition `∀ᵉ j₁ … jₖ. Q`, `j₁` outermost, labelled
-- with the operation whose clause left it (for reading only)

record Oblig (Θ : Scope) : Set where
  constructor oblig
  field
    label  : Maybe Op
    rigids : ℕ
    body   : Hyps (Θ +eⁿ rigids)

open Oblig public

Obligs : Scope → Set
Obligs Θ = List (Oblig Θ)

-- A hypothesis set is the obligation binding no rigid

hypᴼ : ∀ {Θ} → Hyps Θ → Oblig Θ
hypᴼ Q = oblig nothing 0 Q

-- Entailment along a substitution: the body, at fresh rigids, by the
-- hypotheses weakened to them

infix 4 _⊩ᴼ_[_] _⊩ᴼˢ_[_] _⊨_∣_

_⊩ᴼ_[_] : ∀ {Θ Ξ} → Hyps Ξ → Oblig Θ → Subst Θ Ξ → Set
Q' ⊩ᴼ O [ δ ] = wkᵉⁿ-H (rigids O) Q' ⊩ᴴ body O [ δ ↑ᵉⁿ rigids O ]

_⊩ᴼˢ_[_] : ∀ {Θ Ξ} → Hyps Ξ → Obligs Θ → Subst Θ Ξ → Set
Q' ⊩ᴼˢ R [ δ ] = All (λ O → Q' ⊩ᴼ O [ δ ]) R

⊩ᴼ-≐ : ∀ {Θ Ξ} {Q' : Hyps Ξ} {O : Oblig Θ} {δ δ' : Subst Θ Ξ}
     → δ ≐ˢ δ' → Q' ⊩ᴼ O [ δ ] → Q' ⊩ᴼ O [ δ' ]
⊩ᴼ-≐ {O = O} p h = ⊩ᴴ-≐ (≐ˢ-↑ᵉⁿ p (rigids O)) h

⊩ᴼˢ-≐ : ∀ {Θ Ξ} {Q' : Hyps Ξ} {R : Obligs Θ} {δ δ' : Subst Θ Ξ}
      → δ ≐ˢ δ' → Q' ⊩ᴼˢ R [ δ ] → Q' ⊩ᴼˢ R [ δ' ]
⊩ᴼˢ-≐ p []       = []
⊩ᴼˢ-≐ {R = O ∷ R} p (h ∷ hs) = ⊩ᴼ-≐ {O = O} p h ∷ ⊩ᴼˢ-≐ p hs

-- Hypotheses and obligations together

infix 4 _⊩_∣_[_]

_⊩_∣_[_] : ∀ {Θ Ξ} → Hyps Ξ → Hyps Θ → Obligs Θ → Subst Θ Ξ → Set
Q' ⊩ Q ∣ R [ δ ] = Q' ⊩ᴼˢ (hypᴼ Q ∷ R) [ δ ]

-- Satisfaction: a closed instance meets hypotheses and obligations
-- when no hypotheses entail them

_⊨_∣_ : ∀ {Θ} → Subst Θ ∅ˢ → Hyps Θ → Obligs Θ → Set
δ ⊨ Q ∣ R = ∅ᴴ ⊩ Q ∣ R [ δ ]

------------------------------------------------------------------------
-- Satisfiability: some closed instance satisfies them

Satisfiable : ∀ {Θ} → Hyps Θ → Obligs Θ → Set
Satisfiable {Θ} Q R = Σ[ δ ∈ Subst Θ ∅ˢ ] (δ ⊨ Q ∣ R)

------------------------------------------------------------------------
-- Values of closed grade expressions

valᵉ : EExp ∅ˢ → E
valᵉ (evar ())
valᵉ (econst c) = c
valᵉ (ε ·̂ₑ ε')  = valᵉ ε ·ₑ valᵉ ε'
valᵉ (ε ⊔̂ₑ ε')  = valᵉ ε ⊔ₑ valᵉ ε'

valʳ : RExp ∅ˢ → R
valʳ (rvar ())
valʳ (rconst c) = c
valʳ (ρ ·̂ᵣ ρ')  = valʳ ρ ·ᵣ valʳ ρ'
valʳ (ρ ⊔̂ᵣ ρ')  = valʳ ρ ⊔ᵣ valʳ ρ'
valʳ ∣ ε ∣̂ᵉ     = mapᵉ (valᵉ ε)

-- A closed expression is convertible to its value

valᵉ-conv : (ε : EExp ∅ˢ) → ε ≡̂ₑ econst (valᵉ ε)
valᵉ-conv (evar ())
valᵉ-conv (econst c) = ≡̂ₑ-refl
valᵉ-conv (ε ·̂ₑ ε')  = ≡̂ₑ-trans (≡̂ₑ-cong (valᵉ-conv ε) (valᵉ-conv ε')) ≡̂ₑ-const-·
valᵉ-conv (ε ⊔̂ₑ ε')  = ≡̂ₑ-trans (≡̂ₑ-cong-⊔ (valᵉ-conv ε) (valᵉ-conv ε')) ≡̂ₑ-const-⊔

valʳ-conv : (ρ : RExp ∅ˢ) → ρ ≡̂ᵣ rconst (valʳ ρ)
valʳ-conv (rvar ())
valʳ-conv (rconst c) = ≡̂ᵣ-refl
valʳ-conv (ρ ·̂ᵣ ρ')  = ≡̂ᵣ-trans (≡̂ᵣ-cong (valʳ-conv ρ) (valʳ-conv ρ')) ≡̂ᵣ-const-·
valʳ-conv (ρ ⊔̂ᵣ ρ')  = ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (valʳ-conv ρ) (valʳ-conv ρ')) ≡̂ᵣ-const-⊔
valʳ-conv ∣ ε ∣̂ᵉ     = ≡̂ᵣ-trans (≡̂ᵣ-map-cong (valᵉ-conv ε)) ≡̂ᵣ-map-const

------------------------------------------------------------------------
-- The key lemma: soundness. Every rule of convertibility and of
-- entailment from no hypotheses is a law of the carrier.

val-≡̂ᵣ : {ρ ρ' : RExp ∅ˢ} → ρ ≡̂ᵣ ρ' → valʳ ρ ≡ valʳ ρ'
val-≡̂ₑ : {ε ε' : EExp ∅ˢ} → ε ≡̂ₑ ε' → valᵉ ε ≡ valᵉ ε'
val-≾ᵣ : {ρ ρ' : RExp ∅ˢ} → ∅ᴴ ⊩ ρ ≾̂ᵣ ρ' → valʳ ρ ≾ᵣ valʳ ρ'
val-≾ₑ : {ε ε' : EExp ∅ˢ} → ∅ᴴ ⊩ ε ≾̂ₑ ε' → valᵉ ε ≾ₑ valᵉ ε'

val-≡̂ᵣ ≡̂ᵣ-refl          = refl
val-≡̂ᵣ (≡̂ᵣ-sym p)       = sym (val-≡̂ᵣ p)
val-≡̂ᵣ (≡̂ᵣ-trans p q)   = trans (val-≡̂ᵣ p) (val-≡̂ᵣ q)
val-≡̂ᵣ (≡̂ᵣ-cong p q)    = cong₂ _·ᵣ_ (val-≡̂ᵣ p) (val-≡̂ᵣ q)
val-≡̂ᵣ ≡̂ᵣ-assoc         = ·ᵣ-assoc _ _ _
val-≡̂ᵣ ≡̂ᵣ-identityˡ     = ·ᵣ-identityˡ _
val-≡̂ᵣ ≡̂ᵣ-identityʳ     = ·ᵣ-identityʳ _
val-≡̂ᵣ ≡̂ᵣ-const-·       = refl
val-≡̂ᵣ (≡̂ᵣ-comm {c} _)  = c _ _
val-≡̂ᵣ (≡̂ᵣ-cong-⊔ p q)  = cong₂ _⊔ᵣ_ (val-≡̂ᵣ p) (val-≡̂ᵣ q)
val-≡̂ᵣ ≡̂ᵣ-const-⊔       = refl
val-≡̂ᵣ ≡̂ᵣ-comm-⊔        = ⊔ᵣ-comm _ _
val-≡̂ᵣ ≡̂ᵣ-distribˡ-⊔    = ·ᵣ-distribˡ-⊔ᵣ _ _ _
val-≡̂ᵣ ≡̂ᵣ-distribʳ-⊔    = ·ᵣ-distribʳ-⊔ᵣ _ _ _
val-≡̂ᵣ ≡̂ᵣ-map-·         = map-·ᵉ
val-≡̂ᵣ ≡̂ᵣ-map-⊔         = map-⊔ᵉ
val-≡̂ᵣ ≡̂ᵣ-map-const     = refl
val-≡̂ᵣ (≡̂ᵣ-map-cong p)  = cong mapᵉ (val-≡̂ₑ p)
val-≡̂ᵣ (≡̂ᵣ-absorb p)    = ⊔ᵣ-absorb (val-≾ᵣ p)

val-≡̂ₑ ≡̂ₑ-refl          = refl
val-≡̂ₑ (≡̂ₑ-sym p)       = sym (val-≡̂ₑ p)
val-≡̂ₑ (≡̂ₑ-trans p q)   = trans (val-≡̂ₑ p) (val-≡̂ₑ q)
val-≡̂ₑ (≡̂ₑ-cong p q)    = cong₂ _·ₑ_ (val-≡̂ₑ p) (val-≡̂ₑ q)
val-≡̂ₑ ≡̂ₑ-assoc         = ·ₑ-assoc _ _ _
val-≡̂ₑ ≡̂ₑ-identityˡ     = ·ₑ-identityˡ _
val-≡̂ₑ ≡̂ₑ-identityʳ     = ·ₑ-identityʳ _
val-≡̂ₑ ≡̂ₑ-const-·       = refl
val-≡̂ₑ (≡̂ₑ-comm {c} _)  = c _ _
val-≡̂ₑ (≡̂ₑ-cong-⊔ p q)  = cong₂ _⊔ₑ_ (val-≡̂ₑ p) (val-≡̂ₑ q)
val-≡̂ₑ ≡̂ₑ-const-⊔       = refl
val-≡̂ₑ ≡̂ₑ-comm-⊔        = ⊔ₑ-comm _ _
val-≡̂ₑ ≡̂ₑ-distribˡ-⊔    = ·ₑ-distribˡ-⊔ₑ _ _ _
val-≡̂ₑ ≡̂ₑ-distribʳ-⊔    = ·ₑ-distribʳ-⊔ₑ _ _ _
val-≡̂ₑ (≡̂ₑ-absorb p)    = ⊔ₑ-absorb (val-≾ₑ p)

val-≾ᵣ (hypᵣ ())
val-≾ᵣ (atomᵣ p)    = p
val-≾ᵣ (eqᵣ p)      = ≾ᵣ-reflexive (val-≡̂ᵣ p)
val-≾ᵣ (transᵣ p q) = ≾ᵣ-trans (val-≾ᵣ p) (val-≾ᵣ q)
val-≾ᵣ (monoᵣ p q)  = ≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (val-≾ᵣ p)) (·ᵣ-monoʳ-≾ᵣ (val-≾ᵣ q))
val-≾ᵣ (map-mono p) = map-monotoneᵉ (val-≾ₑ p)
val-≾ᵣ (⊔-ubˡᵣ {ρ₁} {ρ₂}) = ⊔ᵣ-ubˡ (valʳ ρ₁) (valʳ ρ₂)
val-≾ᵣ (⊔-ubʳᵣ {ρ₁} {ρ₂}) = ⊔ᵣ-ubʳ (valʳ ρ₁) (valʳ ρ₂)
val-≾ᵣ (⊔-lubᵣ p q) = ⊔ᵣ-lub (val-≾ᵣ p) (val-≾ᵣ q)
val-≾ᵣ (topᵣ {ρ})   = ≾-⊤ᵣ (valʳ ρ)
val-≾ᵣ {ρ' = ρ'} (minᵣ p) = p (valʳ ρ')

val-≾ₑ (hypₑ ())
val-≾ₑ (atomₑ p)    = p
val-≾ₑ (eqₑ p)      = ≾ₑ-reflexive (val-≡̂ₑ p)
val-≾ₑ (transₑ p q) = ≾ₑ-trans (val-≾ₑ p) (val-≾ₑ q)
val-≾ₑ (monoₑ p q)  = ≾ₑ-trans (·ₑ-monoˡ-≾ₑ (val-≾ₑ p)) (·ₑ-monoʳ-≾ₑ (val-≾ₑ q))
val-≾ₑ (⊔-ubˡₑ {ε₁} {ε₂}) = ⊔ₑ-ubˡ (valᵉ ε₁) (valᵉ ε₂)
val-≾ₑ (⊔-ubʳₑ {ε₁} {ε₂}) = ⊔ₑ-ubʳ (valᵉ ε₁) (valᵉ ε₂)
val-≾ₑ (⊔-lubₑ p q) = ⊔ₑ-lub (val-≾ₑ p) (val-≾ₑ q)
val-≾ₑ (topₑ {ε})   = ≾-⊤ₑ (valᵉ ε)
val-≾ₑ {ε' = ε'} (minₑ p) = p (valᵉ ε')

------------------------------------------------------------------------
-- The key lemma: completeness, under any closed hypotheses, through
-- the conversions and the constant ordering

val-≾ᵣ⁻ : {Q : Hyps ∅ˢ} {ρ ρ' : RExp ∅ˢ} → valʳ ρ ≾ᵣ valʳ ρ' → Q ⊩ ρ ≾̂ᵣ ρ'
val-≾ᵣ⁻ {ρ = ρ} {ρ'} p =
  transᵣ (eqᵣ (valʳ-conv ρ)) (transᵣ (atomᵣ p) (eqᵣ (≡̂ᵣ-sym (valʳ-conv ρ'))))

val-≾ₑ⁻ : {Q : Hyps ∅ˢ} {ε ε' : EExp ∅ˢ} → valᵉ ε ≾ₑ valᵉ ε' → Q ⊩ ε ≾̂ₑ ε'
val-≾ₑ⁻ {ε = ε} {ε'} p =
  transₑ (eqₑ (valᵉ-conv ε)) (transₑ (atomₑ p) (eqₑ (≡̂ₑ-sym (valᵉ-conv ε'))))

-- Convertibility of closed expressions is equality of values

val-≡̂ᵣ⁻ : {ρ ρ' : RExp ∅ˢ} → valʳ ρ ≡ valʳ ρ' → ρ ≡̂ᵣ ρ'
val-≡̂ᵣ⁻ {ρ} {ρ'} p =
  ≡̂ᵣ-trans (valʳ-conv ρ) (subst (λ c → rconst c ≡̂ᵣ ρ') (sym p) (≡̂ᵣ-sym (valʳ-conv ρ')))

val-≡̂ₑ⁻ : {ε ε' : EExp ∅ˢ} → valᵉ ε ≡ valᵉ ε' → ε ≡̂ₑ ε'
val-≡̂ₑ⁻ {ε} {ε'} p =
  ≡̂ₑ-trans (valᵉ-conv ε) (subst (λ c → econst c ≡̂ₑ ε') (sym p) (≡̂ₑ-sym (valᵉ-conv ε')))

-- and so is equality from no hypotheses, by antisymmetry

val-⊩≡̂ᵣ : {ρ ρ' : RExp ∅ˢ} → ∅ᴴ ⊩ ρ ≡̂ᵣ ρ' → valʳ ρ ≡ valʳ ρ'
val-⊩≡̂ᵣ (p , q) = ≾ᵣ-antisym (val-≾ᵣ p) (val-≾ᵣ q)

val-⊩≡̂ₑ : {ε ε' : EExp ∅ˢ} → ∅ᴴ ⊩ ε ≡̂ₑ ε' → valᵉ ε ≡ valᵉ ε'
val-⊩≡̂ₑ (p , q) = ≾ₑ-antisym (val-≾ₑ p) (val-≾ₑ q)

val-⊩≡̂ᵣ⁻ : {Q : Hyps ∅ˢ} {ρ ρ' : RExp ∅ˢ} → valʳ ρ ≡ valʳ ρ' → Q ⊩ ρ ≡̂ᵣ ρ'
val-⊩≡̂ᵣ⁻ p = val-≾ᵣ⁻ (≾ᵣ-reflexive p) , val-≾ᵣ⁻ (≾ᵣ-reflexive (sym p))

val-⊩≡̂ₑ⁻ : {Q : Hyps ∅ˢ} {ε ε' : EExp ∅ˢ} → valᵉ ε ≡ valᵉ ε' → Q ⊩ ε ≡̂ₑ ε'
val-⊩≡̂ₑ⁻ p = val-≾ₑ⁻ (≾ₑ-reflexive p) , val-≾ₑ⁻ (≾ₑ-reflexive (sym p))

-- Closed orderings and convertibilities are decided by the carrier

infix 4 _≾̂ᵣ?_ _≾̂ₑ?_ _≡̂ᵣ?_ _≡̂ₑ?_

_≾̂ᵣ?_ : (ρ ρ' : RExp ∅ˢ) → Dec (∅ᴴ ⊩ ρ ≾̂ᵣ ρ')
ρ ≾̂ᵣ? ρ' = map′ val-≾ᵣ⁻ val-≾ᵣ (valʳ ρ ≾ᵣ? valʳ ρ')

_≾̂ₑ?_ : (ε ε' : EExp ∅ˢ) → Dec (∅ᴴ ⊩ ε ≾̂ₑ ε')
ε ≾̂ₑ? ε' = map′ val-≾ₑ⁻ val-≾ₑ (valᵉ ε ≾ₑ? valᵉ ε')

_≡̂ᵣ?_ : (ρ ρ' : RExp ∅ˢ) → Dec (ρ ≡̂ᵣ ρ')
ρ ≡̂ᵣ? ρ' = map′ val-≡̂ᵣ⁻ val-≡̂ᵣ (valʳ ρ ≡ᵣ? valʳ ρ')

_≡̂ₑ?_ : (ε ε' : EExp ∅ˢ) → Dec (ε ≡̂ₑ ε')
ε ≡̂ₑ? ε' = map′ val-≡̂ₑ⁻ val-≡̂ₑ (valᵉ ε ≡ₑ? valᵉ ε')

------------------------------------------------------------------------
-- Closed types

-- Eternality

⊩ᴱ? : (A : OVType ∅ˢ) → Dec (∅ᴴ ⊩ᴱ A)
⊩ᴱ? (tvar ())
⊩ᴱ? (Base b) with eternalBaseType? b
... | yes p = yes (Baseₑ p)
... | no ¬p = no λ { (Baseₑ p) → ⊥-elim-irr (¬p p) }
⊩ᴱ? Unit      = yes Unitₑ
⊩ᴱ? Bool      = yes Boolₑ
⊩ᴱ? (A |×| B) =
  map′ (λ (p , q) → p |×|ₑ q) (λ { (p |×|ₑ q) → p , q }) (⊩ᴱ? A ×-dec ⊩ᴱ? B)
⊩ᴱ? Empty     = yes Emptyₑ
⊩ᴱ? (A ⇒ C)   = no λ ()
⊩ᴱ? ([ ρ ] A) = no λ ()

-- The var-rule disjunction: eternality, or a value below the unit

VarOK-∅ : {A : OVType ∅ˢ} {ρ : RExp ∅ˢ}
        → VarOK ∅ᴴ A ρ → (∅ᴴ ⊩ᴱ A) ⊎ (valʳ ρ ≾ᵣ uᵣ)
VarOK-∅ (et-ok et) = inj₁ et
VarOK-∅ (≾ᵘ-ok le) = inj₂ (val-≾ᵣ le)
VarOK-∅ (hyp-ok () _ _)

VarOK-∅⁻ : {A : OVType ∅ˢ} {ρ : RExp ∅ˢ}
         → (∅ᴴ ⊩ᴱ A) ⊎ (valʳ ρ ≾ᵣ uᵣ) → VarOK ∅ᴴ A ρ
VarOK-∅⁻ (inj₁ et) = et-ok et
VarOK-∅⁻ (inj₂ le) = ≾ᵘ-ok (val-≾ᵣ⁻ le)

VarOK? : (A : OVType ∅ˢ) → (ρ : RExp ∅ˢ) → Dec (VarOK ∅ᴴ A ρ)
VarOK? A ρ with ⊩ᴱ? A | valʳ ρ ≾ᵣ? uᵣ
... | yes et | _      = yes (et-ok et)
... | no  _  | yes le = yes (≾ᵘ-ok (val-≾ᵣ⁻ le))
... | no ¬et | no ¬le = no λ ok → [ ¬et , ¬le ]′ (VarOK-∅ ok)

-- Subtyping. Every rule relates types with the same outermost former,
-- so types with different formers are unrelated.

former : ∀ {Θ} → OVType Θ → ℕ
former (tvar _)  = 0
former (Base _)  = 1
former Unit      = 2
former Bool      = 3
former (_ |×| _) = 4
former Empty     = 5
former (_ ⇒ _)   = 6
former ([ _ ] _) = 7

<:̂ᵛ-former : ∀ {Θ} {Q : Hyps Θ} {A B : OVType Θ} → Q ∣ A <:̂ᵛ B → former A ≡ former B
<:̂ᵛ-former (tvarₛ _)  = refl
<:̂ᵛ-former (Baseₛ _)  = refl
<:̂ᵛ-former Unitₛ      = refl
<:̂ᵛ-former Boolₛ      = refl
<:̂ᵛ-former (_ |×|ₛ _) = refl
<:̂ᵛ-former Emptyₛ     = refl
<:̂ᵛ-former (_ ⇒ₛ _)   = refl
<:̂ᵛ-former ([ _ ]ₛ _) = refl

infix 4 _<:̂ᵛ?_ _<:̂ᶜ?_

_<:̂ᵛ?_ : (A B : OVType ∅ˢ) → Dec (∅ᴴ ∣ A <:̂ᵛ B)
_<:̂ᶜ?_ : (C D : OCType ∅ˢ) → Dec (∅ᴴ ∣ C <:̂ᶜ D)

-- Types with the same outermost former
same : (A B : OVType ∅ˢ) → former A ≡ former B → Dec (∅ᴴ ∣ A <:̂ᵛ B)
same (tvar ()) _ _
same (Base b)  (Base b')  refl = map′ Baseₛ (λ { (Baseₛ p) → p }) (b ≡ᵇ? b')
same Unit      Unit       refl = yes Unitₛ
same Bool      Bool       refl = yes Boolₛ
same (A |×| B) (A' |×| B') refl =
  map′ (λ (p , q) → p |×|ₛ q) (λ { (p |×|ₛ q) → p , q }) (A <:̂ᵛ? A' ×-dec B <:̂ᵛ? B')
same Empty     Empty      refl = yes Emptyₛ
same (A ⇒ C)   (A' ⇒ C')  refl =
  map′ (λ (p , q) → p ⇒ₛ q) (λ { (p ⇒ₛ q) → p , q }) (A' <:̂ᵛ? A ×-dec C <:̂ᶜ? C')
same ([ ρ ] A) ([ ρ' ] A') refl =
  map′ (λ (p , q) → [ p ]ₛ q) (λ { ([ p ]ₛ q) → p , q }) (ρ' ≾̂ᵣ? ρ ×-dec A <:̂ᵛ? A')

A <:̂ᵛ? B with former A ≟ℕ former B
... | yes eq = same A B eq
... | no  ne = no λ p → ne (<:̂ᵛ-former p)

(A ‼ ε) <:̂ᶜ? (A' ‼ ε') =
  map′ (λ (p , q) → p ‼ₛ q) (λ { (p ‼ₛ q) → p , q }) (A <:̂ᵛ? A' ×-dec ε ≾̂ₑ? ε')

------------------------------------------------------------------------
-- Instances of hypotheses

-- An instance of a set is an instance of every set it entails

inst-⊩ᴴ : ∀ {Θ} {Q Q' : Hyps Θ} {δ : Subst Θ ∅ˢ}
        → Q ⊩ᴴ Q' → ∅ᴴ ⊩ᴴ Q [ δ ] → ∅ᴴ ⊩ᴴ Q' [ δ ]
inst-⊩ᴴ e h = ⊩ᴴ-⨟ h e

Satisfiable-⊩ᴴ : ∀ {Θ} {Q Q' : Hyps Θ} → Q ⊩ᴴ Q' → Satisfiable Q [] → Satisfiable Q' []
Satisfiable-⊩ᴴ e (δ , h ∷ []) = δ , inst-⊩ᴴ e h ∷ []

-- Semantic entailment: every closed instance of the first set is one
-- of the second

infix 4 _⊨ᴴ_

_⊨ᴴ_ : ∀ {Θ} → Hyps Θ → Hyps Θ → Set
_⊨ᴴ_ {Θ} Q Q' = (δ : Subst Θ ∅ˢ) → ∅ᴴ ⊩ᴼ hypᴼ Q [ δ ] → ∅ᴴ ⊩ᴼ hypᴼ Q' [ δ ]

⊨ᴴ-refl : ∀ {Θ} {Q : Hyps Θ} → Q ⊨ᴴ Q
⊨ᴴ-refl δ h = h

⊨ᴴ-trans : ∀ {Θ} {Q Q' Q'' : Hyps Θ} → Q ⊨ᴴ Q' → Q' ⊨ᴴ Q'' → Q ⊨ᴴ Q''
⊨ᴴ-trans e e' δ h = e' δ (e δ h)

⊩ᴴ-⊨ᴴ : ∀ {Θ} {Q Q' : Hyps Θ} → Q ⊩ᴴ Q' → Q ⊨ᴴ Q'
⊩ᴴ-⊨ᴴ e δ h = inst-⊩ᴴ e h

Satisfiable-⊨ᴴ : ∀ {Θ} {Q Q' : Hyps Θ} → Q ⊨ᴴ Q' → Satisfiable Q [] → Satisfiable Q' []
Satisfiable-⊨ᴴ e (δ , h ∷ []) = δ , e δ h ∷ []

-- Semantic entailment from open entailment of the atoms and, at each
-- instance, of the var-rule disjunctions

mk⊨ᴴ : ∀ {Θ} {Q Q' : Hyps Θ}
     → (∀ {α} → α ∈ ets Q' → Q ⊩ᴱ tvar α)
     → (∀ {α β} → (α , β) ∈ subᵥ Q' → Q ∣ tvar α <:̂ᵛ tvar β)
     → (∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q' → Q ⊩ ρ ≾̂ᵣ ρ')
     → (∀ {ε ε'} → (ε , ε') ∈ ordₑ Q' → Q ⊩ ε ≾̂ₑ ε')
     → ((δ : Subst Θ ∅ˢ) → ∅ᴴ ⊩ᴴ Q [ δ ]
        → ∀ {A ρ} → (A , ρ) ∈ disj Q' → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ))
     → Q ⊨ᴴ Q'
mk⊨ᴴ et sb oR oE dj δ h =
  mk⊩ᴴ (λ m → ⊩ᴱ-subst h (et m)) (λ m → <:̂ᵛ-subst h (sb m))
       (λ m → ⊩-substᵣ h (oR m)) (λ m → ⊩-substₑ h (oE m)) (dj δ h)

-- The closed var-rule disjunction is met at a type eternal whenever
-- the given one is, and at a grade below the given one

VarOK-∅-mono : {A A' : OVType ∅ˢ} {ρ ρ' : RExp ∅ˢ}
             → (∅ᴴ ⊩ᴱ A → ∅ᴴ ⊩ᴱ A') → ∅ᴴ ⊩ ρ' ≾̂ᵣ ρ → VarOK ∅ᴴ A ρ → VarOK ∅ᴴ A' ρ'
VarOK-∅-mono f q (et-ok et)     = et-ok (f et)
VarOK-∅-mono f q (≾ᵘ-ok le)     = ≾ᵘ-ok (transᵣ q le)
VarOK-∅-mono f q (hyp-ok () _ _)

-- What a set entails holds by value at each of its instances

inst-≾ᵣ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} {ρ ρ' : RExp Θ}
        → ∅ᴴ ⊩ᴴ Q [ δ ] → Q ⊩ ρ ≾̂ᵣ ρ' → valʳ (ρ [ δ ]ʳ) ≾ᵣ valʳ (ρ' [ δ ]ʳ)
inst-≾ᵣ h p = val-≾ᵣ (⊩-substᵣ h p)

inst-≾ₑ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} {ε ε' : EExp Θ}
        → ∅ᴴ ⊩ᴴ Q [ δ ] → Q ⊩ ε ≾̂ₑ ε' → valᵉ (ε [ δ ]ᵉ) ≾ₑ valᵉ (ε' [ δ ]ᵉ)
inst-≾ₑ h p = val-≾ₑ (⊩-substₑ h p)

inst-⊩≡̂ᵣ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} {ρ ρ' : RExp Θ}
         → ∅ᴴ ⊩ᴴ Q [ δ ] → Q ⊩ ρ ≡̂ᵣ ρ' → valʳ (ρ [ δ ]ʳ) ≡ valʳ (ρ' [ δ ]ʳ)
inst-⊩≡̂ᵣ h (p , q) = ≾ᵣ-antisym (inst-≾ᵣ h p) (inst-≾ᵣ h q)

inst-⊩≡̂ₑ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} {ε ε' : EExp Θ}
         → ∅ᴴ ⊩ᴴ Q [ δ ] → Q ⊩ ε ≡̂ₑ ε' → valᵉ (ε [ δ ]ᵉ) ≡ valᵉ (ε' [ δ ]ᵉ)
inst-⊩≡̂ₑ h (p , q) = ≾ₑ-antisym (inst-≾ₑ h p) (inst-≾ₑ h q)

inst-≡̂ᵣ : ∀ {Θ} {ρ ρ' : RExp Θ} → (δ : Subst Θ ∅ˢ)
        → ρ ≡̂ᵣ ρ' → valʳ (ρ [ δ ]ʳ) ≡ valʳ (ρ' [ δ ]ʳ)
inst-≡̂ᵣ δ p = val-≡̂ᵣ (≡̂ᵣ-subst δ p)

inst-≡̂ₑ : ∀ {Θ} {ε ε' : EExp Θ} → (δ : Subst Θ ∅ˢ)
        → ε ≡̂ₑ ε' → valᵉ (ε [ δ ]ᵉ) ≡ valᵉ (ε' [ δ ]ᵉ)
inst-≡̂ₑ δ p = val-≡̂ₑ (≡̂ₑ-subst δ p)

inst-VarOK : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} {A : OVType Θ} {ρ : RExp Θ}
           → ∅ᴴ ⊩ᴴ Q [ δ ] → VarOK Q A ρ
           → (∅ᴴ ⊩ᴱ A [ δ ]ᵛ) ⊎ (valʳ (ρ [ δ ]ʳ) ≾ᵣ uᵣ)
inst-VarOK h ok = VarOK-∅ (VarOK-subst h ok)

-- An atom between expressions convertible to constants holds at an
-- instance exactly when it holds by value

closed-≾ᵣ : ∀ {Θ} {ρ ρ' : RExp Θ} {c c' : R}
          → ρ ≡̂ᵣ rconst c → ρ' ≡̂ᵣ rconst c' → (δ : Subst Θ ∅ˢ)
          → ∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ → c ≾ᵣ c'
closed-≾ᵣ q q' δ p = subst₂ _≾ᵣ_ (inst-≡̂ᵣ δ q) (inst-≡̂ᵣ δ q') (val-≾ᵣ p)

closed-≾ᵣ⁻ : ∀ {Θ Θ'} {Q : Hyps Θ'} {ρ ρ' : RExp Θ} {c c' : R}
           → ρ ≡̂ᵣ rconst c → ρ' ≡̂ᵣ rconst c' → (σ : Subst Θ Θ')
           → c ≾ᵣ c' → Q ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ' [ σ ]ʳ
closed-≾ᵣ⁻ q q' σ p =
  transᵣ (eqᵣ (≡̂ᵣ-subst σ q)) (transᵣ (atomᵣ p) (eqᵣ (≡̂ᵣ-sym (≡̂ᵣ-subst σ q'))))

closed-≾ₑ : ∀ {Θ} {ε ε' : EExp Θ} {c c' : E}
          → ε ≡̂ₑ econst c → ε' ≡̂ₑ econst c' → (δ : Subst Θ ∅ˢ)
          → ∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ → c ≾ₑ c'
closed-≾ₑ q q' δ p = subst₂ _≾ₑ_ (inst-≡̂ₑ δ q) (inst-≡̂ₑ δ q') (val-≾ₑ p)

closed-≾ₑ⁻ : ∀ {Θ Θ'} {Q : Hyps Θ'} {ε ε' : EExp Θ} {c c' : E}
           → ε ≡̂ₑ econst c → ε' ≡̂ₑ econst c' → (σ : Subst Θ Θ')
           → c ≾ₑ c' → Q ⊩ ε [ σ ]ᵉ ≾̂ₑ ε' [ σ ]ᵉ
closed-≾ₑ⁻ q q' σ p =
  transₑ (eqₑ (≡̂ₑ-subst σ q)) (transₑ (atomₑ p) (eqₑ (≡̂ₑ-sym (≡̂ₑ-subst σ q'))))
