------------------------------------------------------------------
-- Closed instances of the open calculus                        --
--                                                              --
-- A closed instance of a scope `Θ` is a substitution           --
-- `δ : Subst Θ ∅ˢ`. Meaning is derivability in the open        --
-- calculus at closed instances, each rigid of a clause kept a  --
-- parameter.                                                   --
--                                                              --
-- A closed instance satisfies hypotheses (`_⊨_`) when each     --
-- holds at it, a quantified ordering at every grade for its    --
-- rigids. A satisfying instance is exactly one at which no     --
-- hypotheses entail them (`⊨⇒⊩ᴴ`, `⊩ᴴ⇒⊨`); entailment is       --
-- sound for satisfaction (`sound-≾ᵣ⁰`, `sound-≾ₑ⁰`).          --
-- Semantic entailment `Q ⊨ᴴ Q'` holds when every closed        --
-- instance of `Q` at which no hypotheses entail it is one of   --
-- `Q'`; open entailment implies it.                            --
--                                                              --
-- A closed grade expression has a value in the carrier.        --
-- Entailed ordering between closed expressions, from no        --
-- hypotheses, is the carrier's ordering of their values, and   --
-- convertibility is equivalence of values.                     --
-- Closed subtyping, closed eternality and the closed var-rule  --
-- disjunction are decidable.                                   --
------------------------------------------------------------------

open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; tabulate; lookup)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Maybe.Base using (Maybe; nothing)
open import Data.Maybe using (to-witness)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_)

open import Language.BaseTypes
open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Hypotheses.Instances (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open BaseTypes BTs using (_≡ᵇ?_; eternalBaseType?)
open Operations Ops using (Op)

open import OpenCalculus.Syntax.Grades S
open import OpenCalculus.Syntax.Types  S
open import OpenCalculus.Syntax.Subst  S
open import OpenCalculus.Hypotheses    S

------------------------------------------------------------------------
-- Lists of quantified orderings

_⊩ᴼˢ_[_] : ∀ {Θ Ξ} → Hyps Ξ → QOrds Θ → Subst Θ Ξ → Set
Q' ⊩ᴼˢ R [ δ ] = All (λ O → Q' ⊩ᴼ O [ δ ]) R

⊩ᴼˢ-≐ : ∀ {Θ Ξ} {Q' : Hyps Ξ} {R : QOrds Θ} {δ δ' : Subst Θ Ξ}
      → δ ≐ˢ δ' → Q' ⊩ᴼˢ R [ δ ] → Q' ⊩ᴼˢ R [ δ' ]
⊩ᴼˢ-≐ p []       = []
⊩ᴼˢ-≐ {R = O ∷ R} p (h ∷ hs) = ⊩ᴼ-resp-≐ˢ O p h ∷ ⊩ᴼˢ-≐ p hs

-- Hypotheses and further quantified orderings, held apart

infix 4 _⊩_∣_[_] _⊩ᴼˢ_[_] _⊨_∣_

_⊩_∣_[_] : ∀ {Θ Ξ} → Hyps Ξ → Hyps Θ → QOrds Θ → Subst Θ Ξ → Set
Q' ⊩ Q ∣ R [ δ ] = (Q' ⊩ᴴ Q [ δ ]) × (Q' ⊩ᴼˢ R [ δ ])

-- A set with quantified hypotheses added is entailed exactly when the
-- set and each of them are

++ᵠ⇒ : ∀ {Θ Ξ} {Q' : Hyps Ξ} {Q : Hyps Θ} {R : List (QOrd Θ)} {δ : Subst Θ Ξ}
   → Q' ⊩ᴴ Q ++ᵠ R [ δ ] → Q' ⊩ Q ∣ R [ δ ]
++ᵠ⇒ {Q = Q} {R} h =
  mk⊩ᴴ (⊩ets h) (⊩subᵥ h) (⊩ordᵣ h) (⊩ordₑ h) (⊩disj h)
       (λ m → ⊩qhyps h (∈-++⁺ˡ m)) ,
  tabulate (λ m → ⊩qhyps h (∈-++⁺ʳ (qhyps Q) m))

++ᵠ⇐ : ∀ {Θ Ξ} {Q' : Hyps Ξ} {Q : Hyps Θ} {R : List (QOrd Θ)} {δ : Subst Θ Ξ}
   → Q' ⊩ Q ∣ R [ δ ] → Q' ⊩ᴴ Q ++ᵠ R [ δ ]
++ᵠ⇐ {Q = Q} (h , hs) =
  mk⊩ᴴ (⊩ets h) (⊩subᵥ h) (⊩ordᵣ h) (⊩ordₑ h) (⊩disj h)
       (λ m → [ ⊩qhyps h , lookup hs ]′ (∈-++⁻ (qhyps Q) m))

-- At a closed instance, hypotheses and quantified hypotheses held
-- apart, entailed by no hypotheses

_⊨_∣_ : ∀ {Θ} → Subst Θ ∅ˢ → Hyps Θ → QOrds Θ → Set
δ ⊨ Q ∣ R = ∅ᴴ ⊩ Q ∣ R [ δ ]

------------------------------------------------------------------------
-- Values of closed grade expressions

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
-- The join respects equivalence

-- The key lemma: soundness. Every rule of convertibility and of
-- entailment from no hypotheses is a law of the carrier.

val-≡̂ᵣ : {ρ ρ' : RExp ∅ˢ} → ρ ≡̂ᵣ ρ' → valʳ ρ ≃ᵣ valʳ ρ'
val-≡̂ₑ : {ε ε' : EExp ∅ˢ} → ε ≡̂ₑ ε' → valᵉ ε ≃ₑ valᵉ ε'
val-≾ᵣ : {ρ ρ' : RExp ∅ˢ} → ∅ᴴ ⊩ ρ ≾̂ᵣ ρ' → valʳ ρ ≾ᵣ valʳ ρ'
val-≾ₑ : {ε ε' : EExp ∅ˢ} → ∅ᴴ ⊩ ε ≾̂ₑ ε' → valᵉ ε ≾ₑ valᵉ ε'

val-≡̂ᵣ ≡̂ᵣ-refl          = ≃ᵣ-refl
val-≡̂ᵣ (≡̂ᵣ-sym p)       = ≃ᵣ-sym (val-≡̂ᵣ p)
val-≡̂ᵣ (≡̂ᵣ-trans p q)   = ≃ᵣ-trans (val-≡̂ᵣ p) (val-≡̂ᵣ q)
val-≡̂ᵣ (≡̂ᵣ-cong p q)    = ·ᵣ-cong (val-≡̂ᵣ p) (val-≡̂ᵣ q)
val-≡̂ᵣ ≡̂ᵣ-assoc         = ·ᵣ-assoc _ _ _
val-≡̂ᵣ ≡̂ᵣ-identityˡ     = ·ᵣ-identityˡ _
val-≡̂ᵣ ≡̂ᵣ-identityʳ     = ·ᵣ-identityʳ _
val-≡̂ᵣ (≡̂ᵣ-const e)     = e
val-≡̂ᵣ ≡̂ᵣ-const-·       = ≃ᵣ-refl
val-≡̂ᵣ (≡̂ᵣ-comm ij)     = to-witness ij _ _
val-≡̂ᵣ (≡̂ᵣ-cong-⊔ p q)  = ⊔ᵣ-cong (val-≡̂ᵣ p) (val-≡̂ᵣ q)
val-≡̂ᵣ ≡̂ᵣ-const-⊔       = ≃ᵣ-refl
val-≡̂ᵣ ≡̂ᵣ-comm-⊔        = ⊔ᵣ-comm _ _
val-≡̂ᵣ ≡̂ᵣ-distribˡ-⊔    = ·ᵣ-distribˡ-⊔ᵣ _ _ _
val-≡̂ᵣ ≡̂ᵣ-distribʳ-⊔    = ·ᵣ-distribʳ-⊔ᵣ _ _ _
val-≡̂ᵣ ≡̂ᵣ-map-·         = map-·ᵉ
val-≡̂ᵣ ≡̂ᵣ-map-⊔         = map-⊔ᵉ
val-≡̂ᵣ ≡̂ᵣ-map-const     = ≃ᵣ-refl
val-≡̂ᵣ (≡̂ᵣ-map-cong p)  = map-≃ᵉ (val-≡̂ₑ p)
val-≡̂ᵣ (≡̂ᵣ-absorb p)    = ⊔ᵣ-absorb (val-≾ᵣ p)

val-≡̂ₑ ≡̂ₑ-refl          = ≃ₑ-refl
val-≡̂ₑ (≡̂ₑ-sym p)       = ≃ₑ-sym (val-≡̂ₑ p)
val-≡̂ₑ (≡̂ₑ-trans p q)   = ≃ₑ-trans (val-≡̂ₑ p) (val-≡̂ₑ q)
val-≡̂ₑ (≡̂ₑ-cong p q)    = ·ₑ-cong (val-≡̂ₑ p) (val-≡̂ₑ q)
val-≡̂ₑ ≡̂ₑ-assoc         = ·ₑ-assoc _ _ _
val-≡̂ₑ ≡̂ₑ-identityˡ     = ·ₑ-identityˡ _
val-≡̂ₑ ≡̂ₑ-identityʳ     = ·ₑ-identityʳ _
val-≡̂ₑ (≡̂ₑ-const e)     = e
val-≡̂ₑ ≡̂ₑ-const-·       = ≃ₑ-refl
val-≡̂ₑ (≡̂ₑ-comm ij)     = to-witness ij _ _
val-≡̂ₑ (≡̂ₑ-cong-⊔ p q)  = ⊔ₑ-cong (val-≡̂ₑ p) (val-≡̂ₑ q)
val-≡̂ₑ ≡̂ₑ-const-⊔       = ≃ₑ-refl
val-≡̂ₑ ≡̂ₑ-comm-⊔        = ⊔ₑ-comm _ _
val-≡̂ₑ ≡̂ₑ-distribˡ-⊔    = ·ₑ-distribˡ-⊔ₑ _ _ _
val-≡̂ₑ ≡̂ₑ-distribʳ-⊔    = ·ₑ-distribʳ-⊔ₑ _ _ _
val-≡̂ₑ (≡̂ₑ-absorb p)    = ⊔ₑ-absorb (val-≾ₑ p)

val-≾ᵣ (hypᵣ ())
val-≾ᵣ (atomᵣ p)    = p
val-≾ᵣ (eqᵣ p)      = ≃ᵣ⇒≾ᵣ (val-≡̂ᵣ p)
val-≾ᵣ (transᵣ p q) = ≾ᵣ-trans (val-≾ᵣ p) (val-≾ᵣ q)
val-≾ᵣ (monoᵣ p q)  = ≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (val-≾ᵣ p)) (·ᵣ-monoʳ-≾ᵣ (val-≾ᵣ q))
val-≾ᵣ (map-mono p) = map-monotoneᵉ (val-≾ₑ p)
val-≾ᵣ (⊔-ubˡᵣ {ρ₁} {ρ₂}) = ⊔ᵣ-ubˡ (valʳ ρ₁) (valʳ ρ₂)
val-≾ᵣ (⊔-ubʳᵣ {ρ₁} {ρ₂}) = ⊔ᵣ-ubʳ (valʳ ρ₁) (valʳ ρ₂)
val-≾ᵣ (⊔-lubᵣ p q) = ⊔ᵣ-lub (val-≾ᵣ p) (val-≾ᵣ q)
val-≾ᵣ (topᵣ {ρ})   = ≾-⊤ᵣ (valʳ ρ)
val-≾ᵣ {ρ' = ρ'} (minᵣ ij) = to-witness ij (valʳ ρ')
val-≾ᵣ (zeroˡᵣ p)   = ≾ᵣ-zero-productˡ (val-≾ᵣ p)
val-≾ᵣ (zeroʳᵣ p)   = ≾ᵣ-zero-productʳ (val-≾ᵣ p)
val-≾ᵣ (plusᵣ p q r) = Plus.c⁺-least p (val-≾ᵣ q) (val-≾ᵣ r)
val-≾ᵣ (indˡᵣ p q)  = Plus.⁺-indˡ p (val-≾ᵣ q)
val-≾ᵣ (indʳᵣ p q)  = Plus.⁺-indʳ p (val-≾ᵣ q)
val-≾ᵣ (instᵣ () _ _)
val-≾ᵣ (factᵣ H es) = H es

val-≾ₑ (hypₑ ())
val-≾ₑ (atomₑ p)    = p
val-≾ₑ (eqₑ p)      = ≃ₑ⇒≾ₑ (val-≡̂ₑ p)
val-≾ₑ (transₑ p q) = ≾ₑ-trans (val-≾ₑ p) (val-≾ₑ q)
val-≾ₑ (monoₑ p q)  = ≾ₑ-trans (·ₑ-monoˡ-≾ₑ (val-≾ₑ p)) (·ₑ-monoʳ-≾ₑ (val-≾ₑ q))
val-≾ₑ (⊔-ubˡₑ {ε₁} {ε₂}) = ⊔ₑ-ubˡ (valᵉ ε₁) (valᵉ ε₂)
val-≾ₑ (⊔-ubʳₑ {ε₁} {ε₂}) = ⊔ₑ-ubʳ (valᵉ ε₁) (valᵉ ε₂)
val-≾ₑ (⊔-lubₑ p q) = ⊔ₑ-lub (val-≾ₑ p) (val-≾ₑ q)
val-≾ₑ (topₑ {ε})   = ≾-⊤ₑ (valᵉ ε)
val-≾ₑ {ε' = ε'} (minₑ ij) = to-witness ij (valᵉ ε')
val-≾ₑ (zeroˡₑ p)   = ≾ₑ-zero-productˡ (val-≾ₑ p)
val-≾ₑ (zeroʳₑ p)   = ≾ₑ-zero-productʳ (val-≾ₑ p)
val-≾ₑ (plusₑ p q r) = Plus.c⁺-least p (val-≾ₑ q) (val-≾ₑ r)
val-≾ₑ (indˡₑ p q)  = Plus.⁺-indˡ p (val-≾ₑ q)
val-≾ₑ (indʳₑ p q)  = Plus.⁺-indʳ p (val-≾ₑ q)
val-≾ₑ (instₑ () _ _)
val-≾ₑ (factₑ H es) = H es

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

val-≡̂ᵣ⁻ : {ρ ρ' : RExp ∅ˢ} → valʳ ρ ≃ᵣ valʳ ρ' → ρ ≡̂ᵣ ρ'
val-≡̂ᵣ⁻ {ρ} {ρ'} p =
  ≡̂ᵣ-trans (valʳ-conv ρ) (≡̂ᵣ-trans (≡̂ᵣ-const p) (≡̂ᵣ-sym (valʳ-conv ρ')))

val-≡̂ₑ⁻ : {ε ε' : EExp ∅ˢ} → valᵉ ε ≃ₑ valᵉ ε' → ε ≡̂ₑ ε'
val-≡̂ₑ⁻ {ε} {ε'} p =
  ≡̂ₑ-trans (valᵉ-conv ε) (≡̂ₑ-trans (≡̂ₑ-const p) (≡̂ₑ-sym (valᵉ-conv ε')))

-- and so is equality from no hypotheses, the order's equivalence

val-⊩≡̂ᵣ : {ρ ρ' : RExp ∅ˢ} → ∅ᴴ ⊩ ρ ≡̂ᵣ ρ' → valʳ ρ ≃ᵣ valʳ ρ'
val-⊩≡̂ᵣ (p , q) = val-≾ᵣ p , val-≾ᵣ q

val-⊩≡̂ₑ : {ε ε' : EExp ∅ˢ} → ∅ᴴ ⊩ ε ≡̂ₑ ε' → valᵉ ε ≃ₑ valᵉ ε'
val-⊩≡̂ₑ (p , q) = val-≾ₑ p , val-≾ₑ q

val-⊩≡̂ᵣ⁻ : {Q : Hyps ∅ˢ} {ρ ρ' : RExp ∅ˢ} → valʳ ρ ≃ᵣ valʳ ρ' → Q ⊩ ρ ≡̂ᵣ ρ'
val-⊩≡̂ᵣ⁻ p = val-≾ᵣ⁻ (proj₁ p) , val-≾ᵣ⁻ (proj₂ p)

val-⊩≡̂ₑ⁻ : {Q : Hyps ∅ˢ} {ε ε' : EExp ∅ˢ} → valᵉ ε ≃ₑ valᵉ ε' → Q ⊩ ε ≡̂ₑ ε'
val-⊩≡̂ₑ⁻ p = val-≾ₑ⁻ (proj₁ p) , val-≾ₑ⁻ (proj₂ p)

-- Closed orderings and convertibilities are decided by the carrier

infix 4 _≾̂ᵣ?_ _≾̂ₑ?_ _≡̂ᵣ?_ _≡̂ₑ?_

_≾̂ᵣ?_ : (ρ ρ' : RExp ∅ˢ) → Dec (∅ᴴ ⊩ ρ ≾̂ᵣ ρ')
ρ ≾̂ᵣ? ρ' = map′ val-≾ᵣ⁻ val-≾ᵣ (valʳ ρ ≾ᵣ? valʳ ρ')

_≾̂ₑ?_ : (ε ε' : EExp ∅ˢ) → Dec (∅ᴴ ⊩ ε ≾̂ₑ ε')
ε ≾̂ₑ? ε' = map′ val-≾ₑ⁻ val-≾ₑ (valᵉ ε ≾ₑ? valᵉ ε')

_≡̂ᵣ?_ : (ρ ρ' : RExp ∅ˢ) → Dec (ρ ≡̂ᵣ ρ')
ρ ≡̂ᵣ? ρ' = map′ val-≡̂ᵣ⁻ val-≡̂ᵣ (valʳ ρ ≃ᵣ? valʳ ρ')

_≡̂ₑ?_ : (ε ε' : EExp ∅ˢ) → Dec (ε ≡̂ₑ ε')
ε ≡̂ₑ? ε' = map′ val-≡̂ₑ⁻ val-≡̂ₑ (valᵉ ε ≃ₑ? valᵉ ε')

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
⊩ᴱ? Nat       = yes Natₑ
⊩ᴱ? (A |×| B) =
  map′ (λ (p , q) → p |×|ₑ q) (λ { (p |×|ₑ q) → p , q }) (⊩ᴱ? A ×-dec ⊩ᴱ? B)
⊩ᴱ? (A |+| B) =
  map′ (λ (p , q) → p |+|ₑ q) (λ { (p |+|ₑ q) → p , q }) (⊩ᴱ? A ×-dec ⊩ᴱ? B)
⊩ᴱ? (|List| A) = map′ |List|ₑ (λ { (|List|ₑ p) → p }) (⊩ᴱ? A)
⊩ᴱ? Empty     = yes Emptyₑ
⊩ᴱ? (A ⇒ C)   = no λ ()
⊩ᴱ? (C ⇛ D)   = no λ ()
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
former Nat       = 8
former (_ |+| _) = 9
former (|List| _) = 10
former (_ ⇛ _)   = 11

<:̂ᵛ-former : ∀ {Θ} {Q : Hyps Θ} {A B : OVType Θ} → Q ∣ A <:̂ᵛ B → former A ≡ former B
<:̂ᵛ-former (tvarₛ _)  = refl
<:̂ᵛ-former (Baseₛ _)  = refl
<:̂ᵛ-former Unitₛ      = refl
<:̂ᵛ-former Boolₛ      = refl
<:̂ᵛ-former Natₛ       = refl
<:̂ᵛ-former (_ |×|ₛ _) = refl
<:̂ᵛ-former (_ |+|ₛ _) = refl
<:̂ᵛ-former (|List|ₛ _) = refl
<:̂ᵛ-former Emptyₛ     = refl
<:̂ᵛ-former (_ ⇒ₛ _)   = refl
<:̂ᵛ-former ([ _ ]ₛ _) = refl
<:̂ᵛ-former (_ ⇛ₛ _)   = refl

infix 4 _<:̂ᵛ?_ _<:̂ᶜ?_

_<:̂ᵛ?_ : (A B : OVType ∅ˢ) → Dec (∅ᴴ ∣ A <:̂ᵛ B)
_<:̂ᶜ?_ : (C D : OCType ∅ˢ) → Dec (∅ᴴ ∣ C <:̂ᶜ D)

-- Types with the same outermost former
same : (A B : OVType ∅ˢ) → former A ≡ former B → Dec (∅ᴴ ∣ A <:̂ᵛ B)
same (tvar ()) _ _
same (Base b)  (Base b')  refl = map′ Baseₛ (λ { (Baseₛ p) → p }) (b ≡ᵇ? b')
same Unit      Unit       refl = yes Unitₛ
same Bool      Bool       refl = yes Boolₛ
same Nat       Nat        refl = yes Natₛ
same (A |×| B) (A' |×| B') refl =
  map′ (λ (p , q) → p |×|ₛ q) (λ { (p |×|ₛ q) → p , q }) (A <:̂ᵛ? A' ×-dec B <:̂ᵛ? B')
same (A |+| B) (A' |+| B') refl =
  map′ (λ (p , q) → p |+|ₛ q) (λ { (p |+|ₛ q) → p , q }) (A <:̂ᵛ? A' ×-dec B <:̂ᵛ? B')
same (|List| A) (|List| A') refl =
  map′ |List|ₛ (λ { (|List|ₛ p) → p }) (A <:̂ᵛ? A')
same Empty     Empty      refl = yes Emptyₛ
same (A ⇒ C)   (A' ⇒ C')  refl =
  map′ (λ (p , q) → p ⇒ₛ q) (λ { (p ⇒ₛ q) → p , q }) (A' <:̂ᵛ? A ×-dec C <:̂ᶜ? C')
same (C ⇛ D)   (C' ⇛ D')  refl =
  map′ (λ (p , q) → p ⇛ₛ q) (λ { (p ⇛ₛ q) → p , q }) (C' <:̂ᶜ? C ×-dec D <:̂ᶜ? D')
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

------------------------------------------------------------------------
-- Satisfaction at closed instances: a closed instance satisfies `Q`
-- when each hypothesis holds at it, a quantified one at every instance
-- of its rigids. An instance of the rigids is a vector of closed
-- expressions, every grade being the value of one; a closed ordering
-- holds when no hypotheses entail it, which is the ordering of its
-- values
-- (`val-≾ᵣ`, `val-≾ᵣ⁻`).

infix 4 _⊨_

_⊨_ : ∀ {Θ} → Subst Θ ∅ˢ → Hyps Θ → Set
δ ⊨ Q = ∅ᴴ ⊩ᴵ Q [ δ ]

private

  from∅-id : (from∅ {∅ˢ}) ≐ˢ idˢ
  from∅-id = mk≐ˢ (λ ()) (λ ()) (λ ())

  ⨟-from∅ : ∀ {Θ} → (δ : Subst Θ ∅ˢ) → (δ ⨟ˢ from∅) ≐ˢ δ
  ⨟-from∅ δ = ≐ˢ-trans (⨟-congʳ δ from∅-id) (⨟-idʳ δ)

  from∅-vars : (k : ℕ) → (from∅ ,ᵉⁿ varsⁿ k) ≐ˢ idˢ {∅ˢ +eⁿ k}
  from∅-vars k = ≐ˢ-trans (≐ˢ-,ᵉⁿ (mk≐ˢ (λ ()) (λ ()) (λ ())) (varsⁿ k)) (wkˢⁿ-varsⁿ k)

-- At a satisfying instance no hypotheses entail the set: a quantified
-- hypothesis, holding at every instance of its rigids, is an instance
-- of rule Truth at its image

⊨⇒⊩ᴴ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} → δ ⊨ Q → ∅ᴴ ⊩ᴴ Q [ δ ]
⊨⇒⊩ᴴ {Θ} {Q} {δ} h =
  mk⊩ᴴ (⊩etsᴵ h) (⊩subᵥᴵ h) (⊩ordᵣᴵ h) (⊩ordₑᴵ h) (⊩disjᴵ h) qh
  where
    qh : ∀ {O} → O ∈ qhyps Q → ∅ᴴ ⊩ᴼ O [ δ ]
    qh {O} m = subst (λ H → H ⊩ᵒ body O [ δ ↑ᵉⁿ k ]) (sym (wkᵉⁿ-∅ᴴ k)) (mk⊩ᵒ r e)
      where
        k = rigids O

        inst : (es : Vec (EExp ∅ˢ) k) → ((δ ↑ᵉⁿ k) ⨟ˢ (from∅ ,ᵉⁿ es)) ≐ˢ (δ ,ᵉⁿ es)
        inst es = ≐ˢ-trans (↑ᵉⁿ-,ᵉⁿ δ from∅ k es) (≐ˢ-,ᵉⁿ (⨟-from∅ δ) es)

        eqʳ : (x : RExp (Θ +eⁿ k)) → (es : Vec (EExp ∅ˢ) k)
            → x [ δ ,ᵉⁿ es ]ʳ ≡ x [ δ ↑ᵉⁿ k ]ʳ [ from∅ ,ᵉⁿ es ]ʳ
        eqʳ x es = sym (trans ([⨟]ʳ x (δ ↑ᵉⁿ k) (from∅ ,ᵉⁿ es)) ([≐]ʳ (inst es) x))

        eqᵉ : (x : EExp (Θ +eⁿ k)) → (es : Vec (EExp ∅ˢ) k)
            → x [ δ ,ᵉⁿ es ]ᵉ ≡ x [ δ ↑ᵉⁿ k ]ᵉ [ from∅ ,ᵉⁿ es ]ᵉ
        eqᵉ x es = sym (trans ([⨟]ᵉ x (δ ↑ᵉⁿ k) (from∅ ,ᵉⁿ es)) ([≐]ᵉ (inst es) x))

        idʳ : (x : RExp (∅ˢ +eⁿ k)) → x [ from∅ ,ᵉⁿ varsⁿ k ]ʳ ≡ x
        idʳ x = trans ([≐]ʳ (from∅-vars k) x) ([id]ʳ x)

        idᵉ : (x : EExp (∅ˢ +eⁿ k)) → x [ from∅ ,ᵉⁿ varsⁿ k ]ᵉ ≡ x
        idᵉ x = trans ([≐]ᵉ (from∅-vars k) x) ([id]ᵉ x)

        r : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors (body O) → ∅ᴴ ⊩ ρ [ δ ↑ᵉⁿ k ]ʳ ≾̂ᵣ ρ' [ δ ↑ᵉⁿ k ]ʳ
        r {ρ} {ρ'} mφ =
          subst₂ (λ x y → ∅ᴴ ⊩ x ≾̂ᵣ y) (idʳ (ρ [ δ ↑ᵉⁿ k ]ʳ)) (idʳ (ρ' [ δ ↑ᵉⁿ k ]ʳ))
                 (factᵣ {ρ = ρ [ δ ↑ᵉⁿ k ]ʳ} {ρ' [ δ ↑ᵉⁿ k ]ʳ}
                        (λ es → subst₂ _≾ᵣ_ (cong valʳ (eqʳ ρ es)) (cong valʳ (eqʳ ρ' es))
                                         (val-≾ᵣ (⊩ors (⊩qhypsᴵ h m es) mφ)))
                        (varsⁿ k))

        e : ∀ {ε ε'} → (ε , ε') ∈ oes (body O) → ∅ᴴ ⊩ ε [ δ ↑ᵉⁿ k ]ᵉ ≾̂ₑ ε' [ δ ↑ᵉⁿ k ]ᵉ
        e {ε} {ε'} mφ =
          subst₂ (λ x y → ∅ᴴ ⊩ x ≾̂ₑ y) (idᵉ (ε [ δ ↑ᵉⁿ k ]ᵉ)) (idᵉ (ε' [ δ ↑ᵉⁿ k ]ᵉ))
                 (factₑ {ε = ε [ δ ↑ᵉⁿ k ]ᵉ} {ε' [ δ ↑ᵉⁿ k ]ᵉ}
                        (λ es → subst₂ _≾ₑ_ (cong valᵉ (eqᵉ ε es)) (cong valᵉ (eqᵉ ε' es))
                                         (val-≾ₑ (⊩oes (⊩qhypsᴵ h m es) mφ)))
                        (varsⁿ k))

⊩ᴴ⇒⊨ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} → ∅ᴴ ⊩ᴴ Q [ δ ] → δ ⊨ Q
⊩ᴴ⇒⊨ = ⊩ᴴ⇒ᴵ

-- Soundness of entailment: at a satisfying closed instance, an
-- entailed ordering holds in the carrier

sound-≾ᵣ⁰ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} {ρ ρ' : RExp Θ}
          → Q ⊩ ρ ≾̂ᵣ ρ' → δ ⊨ Q → valʳ (ρ [ δ ]ʳ) ≾ᵣ valʳ (ρ' [ δ ]ʳ)
sound-≾ᵣ⁰ p h = val-≾ᵣ (⊩-substᴵᵣ h p)

sound-≾ₑ⁰ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} {ε ε' : EExp Θ}
          → Q ⊩ ε ≾̂ₑ ε' → δ ⊨ Q → valᵉ (ε [ δ ]ᵉ) ≾ₑ valᵉ (ε' [ δ ]ᵉ)
sound-≾ₑ⁰ p h = val-≾ₑ (⊩-substᴵₑ h p)

------------------------------------------------------------------------
-- Satisfiability: some closed instance satisfies the set

Satisfiable : ∀ {Θ} → Hyps Θ → Set
Satisfiable {Θ} Q = Σ[ δ ∈ Subst Θ ∅ˢ ] (δ ⊨ Q)

-- The empty set is satisfiable, by the ground instance

Satisfiable-∅ : ∀ {Θ} → Satisfiable {Θ} ∅ᴴ
Satisfiable-∅ = groundˢ , ⊩ᴵ-∅

-- Satisfaction of a set with quantified hypotheses added, held apart

⊨++ᵠ⇒ : ∀ {Θ} {Q : Hyps Θ} {R : List (QOrd Θ)} {δ : Subst Θ ∅ˢ} → δ ⊨ Q ++ᵠ R → δ ⊨ Q ∣ R
⊨++ᵠ⇒ h = ++ᵠ⇒ (⊨⇒⊩ᴴ h)

⊨++ᵠ⇐ : ∀ {Θ} {Q : Hyps Θ} {R : List (QOrd Θ)} {δ : Subst Θ ∅ˢ} → δ ⊨ Q ∣ R → δ ⊨ Q ++ᵠ R
⊨++ᵠ⇐ h = ⊩ᴴ⇒⊨ (++ᵠ⇐ h)

-- Semantic entailment: every closed instance of the first set is one
-- of the second

infix 4 _⊨ᴴ_

_⊨ᴴ_ : ∀ {Θ} → Hyps Θ → Hyps Θ → Set
_⊨ᴴ_ {Θ} Q Q' = (δ : Subst Θ ∅ˢ) → ∅ᴴ ⊩ᴴ Q [ δ ] → ∅ᴴ ⊩ᴴ Q' [ δ ]

⊨ᴴ-refl : ∀ {Θ} {Q : Hyps Θ} → Q ⊨ᴴ Q
⊨ᴴ-refl δ h = h

⊨ᴴ-trans : ∀ {Θ} {Q Q' Q'' : Hyps Θ} → Q ⊨ᴴ Q' → Q' ⊨ᴴ Q'' → Q ⊨ᴴ Q''
⊨ᴴ-trans e e' δ h = e' δ (e δ h)

⊩ᴴ-⊨ᴴ : ∀ {Θ} {Q Q' : Hyps Θ} → Q ⊩ᴴ Q' → Q ⊨ᴴ Q'
⊩ᴴ-⊨ᴴ e δ h = ⊩ᴴ-⨟ h e

-- Semantic entailment from open entailment of the atoms and, at each
-- instance, of the var-rule disjunctions

mk⊨ᴴ : ∀ {Θ} {Q Q' : Hyps Θ}
     → (∀ {α} → α ∈ ets Q' → Q ⊩ᴱ tvar α)
     → (∀ {α β} → (α , β) ∈ subᵥ Q' → Q ∣ tvar α <:̂ᵛ tvar β)
     → (∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q' → Q ⊩ ρ ≾̂ᵣ ρ')
     → (∀ {ε ε'} → (ε , ε') ∈ ordₑ Q' → Q ⊩ ε ≾̂ₑ ε')
     → ((δ : Subst Θ ∅ˢ) → ∅ᴴ ⊩ᴴ Q [ δ ]
        → ∀ {A ρ} → (A , ρ) ∈ disj Q' → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ))
     → (∀ {O} → O ∈ qhyps Q' → Q ⊩ᴼ O [ idˢ ])
     → Q ⊨ᴴ Q'
mk⊨ᴴ et sb oR oE dj qh δ h =
  mk⊩ᴴ (λ m → ⊩ᴱ-subst h (et m)) (λ m → <:̂ᵛ-subst h (sb m))
       (λ m → ⊩-substᵣ h (oR m)) (λ m → ⊩-substₑ h (oE m)) (dj δ h)
       (λ {O} m → ⊩ᴼ-resp-≐ˢ O (⨟-idˡ δ) (⊩ᴼ-⨟ O h (qh m)))

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
         → ∅ᴴ ⊩ᴴ Q [ δ ] → Q ⊩ ρ ≡̂ᵣ ρ' → valʳ (ρ [ δ ]ʳ) ≃ᵣ valʳ (ρ' [ δ ]ʳ)
inst-⊩≡̂ᵣ h (p , q) = inst-≾ᵣ h p , inst-≾ᵣ h q

inst-⊩≡̂ₑ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} {ε ε' : EExp Θ}
         → ∅ᴴ ⊩ᴴ Q [ δ ] → Q ⊩ ε ≡̂ₑ ε' → valᵉ (ε [ δ ]ᵉ) ≃ₑ valᵉ (ε' [ δ ]ᵉ)
inst-⊩≡̂ₑ h (p , q) = inst-≾ₑ h p , inst-≾ₑ h q

inst-≡̂ᵣ : ∀ {Θ} {ρ ρ' : RExp Θ} → (δ : Subst Θ ∅ˢ)
        → ρ ≡̂ᵣ ρ' → valʳ (ρ [ δ ]ʳ) ≃ᵣ valʳ (ρ' [ δ ]ʳ)
inst-≡̂ᵣ δ p = val-≡̂ᵣ (≡̂ᵣ-subst δ p)

inst-≡̂ₑ : ∀ {Θ} {ε ε' : EExp Θ} → (δ : Subst Θ ∅ˢ)
        → ε ≡̂ₑ ε' → valᵉ (ε [ δ ]ᵉ) ≃ₑ valᵉ (ε' [ δ ]ᵉ)
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
closed-≾ᵣ q q' δ p =
  ≾ᵣ-trans (proj₂ (inst-≡̂ᵣ δ q)) (≾ᵣ-trans (val-≾ᵣ p) (proj₁ (inst-≡̂ᵣ δ q')))

closed-≾ᵣ⁻ : ∀ {Θ Θ'} {Q : Hyps Θ'} {ρ ρ' : RExp Θ} {c c' : R}
           → ρ ≡̂ᵣ rconst c → ρ' ≡̂ᵣ rconst c' → (σ : Subst Θ Θ')
           → c ≾ᵣ c' → Q ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ' [ σ ]ʳ
closed-≾ᵣ⁻ q q' σ p =
  transᵣ (eqᵣ (≡̂ᵣ-subst σ q)) (transᵣ (atomᵣ p) (eqᵣ (≡̂ᵣ-sym (≡̂ᵣ-subst σ q'))))

closed-≾ₑ : ∀ {Θ} {ε ε' : EExp Θ} {c c' : E}
          → ε ≡̂ₑ econst c → ε' ≡̂ₑ econst c' → (δ : Subst Θ ∅ˢ)
          → ∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ → c ≾ₑ c'
closed-≾ₑ q q' δ p =
  ≾ₑ-trans (proj₂ (inst-≡̂ₑ δ q)) (≾ₑ-trans (val-≾ₑ p) (proj₁ (inst-≡̂ₑ δ q')))

closed-≾ₑ⁻ : ∀ {Θ Θ'} {Q : Hyps Θ'} {ε ε' : EExp Θ} {c c' : E}
           → ε ≡̂ₑ econst c → ε' ≡̂ₑ econst c' → (σ : Subst Θ Θ')
           → c ≾ₑ c' → Q ⊩ ε [ σ ]ᵉ ≾̂ₑ ε' [ σ ]ᵉ
closed-≾ₑ⁻ q q' σ p =
  transₑ (eqₑ (≡̂ₑ-subst σ q)) (transₑ (atomₑ p) (eqₑ (≡̂ₑ-sym (≡̂ₑ-subst σ q'))))
