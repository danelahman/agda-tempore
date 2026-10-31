------------------------------------------------------------------
-- Closed instances of the polymorphic calculus                 --
--                                                              --
-- A closed instance of a scope is a substitution into the      --
-- empty scope. It satisfies a set (`_⊨_`) when each hypothesis --
-- holds at it, a quantified one at every instance of its       --
-- rigids: exactly when no hypotheses entail the set there      --
-- (`⊨⇒⊩ᴴ`, `⊩ᴴ⇒⊨`). Semantic entailment `Q ⊨ᴴ Q'`: every       --
-- closed instance of `Q` is one of `Q'`. Between closed        --
-- expressions, entailment is the carrier's ordering of values; --
-- closed subtyping, eternality and the var-rule disjunction    --
-- are decidable.                                               --
------------------------------------------------------------------

open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; tabulate; lookup)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec) renaming (map to mapᵛ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Maybe.Base using (Maybe; nothing)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_)

open import Language.BaseTypes
open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Hypotheses.Instances (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open BaseTypes BTs using (_≡ᵇ?_; eternalBaseType?)
open Operations Ops using (Op)

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses               S

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

-- Entailing `Q ++ᵠ R` is entailing `Q` and each of `R`

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

-- Satisfaction of the two, held apart

_⊨_∣_ : ∀ {Θ} → Subst Θ ∅ˢ → Hyps Θ → QOrds Θ → Set
δ ⊨ Q ∣ R = ∅ᴴ ⊩ Q ∣ R [ δ ]

------------------------------------------------------------------------
-- Values of closed grade expressions

-- A closed expression is its own closed instance

closed-[]ᵉ : (δ : Subst ∅ˢ ∅ˢ) → (ε : EExp ∅ˢ) → ε [ δ ]ᵉ ≡ ε
closed-[]ᵉ δ ε = trans ([≐]ᵉ (mk≐ˢ (λ ()) (λ ()) (λ ())) ε) ([id]ᵉ ε)

closed-[]ʳ : (δ : Subst ∅ˢ ∅ˢ) → (ρ : RExp ∅ˢ) → ρ [ δ ]ʳ ≡ ρ
closed-[]ʳ δ ρ = trans ([≐]ʳ (mk≐ˢ (λ ()) (λ ()) (λ ())) ρ) ([id]ʳ ρ)

-- Soundness: closed entailment and convertibility hold by value

val-≾ᵣ : {ρ ρ' : RExp ∅ˢ} → ∅ᴴ ⊩ ρ ≾̂ᵣ ρ' → valʳ ρ ≾ᵣ valʳ ρ'
val-≾ᵣ {ρ} {ρ'} p =
  subst₂ _≾ᵣ_ (cong valʳ ([id]ʳ ρ)) (cong valʳ ([id]ʳ ρ')) (runᵣ p idˢ ⊨ᵍ-∅)

val-≾ₑ : {ε ε' : EExp ∅ˢ} → ∅ᴴ ⊩ ε ≾̂ₑ ε' → valᵉ ε ≾ₑ valᵉ ε'
val-≾ₑ {ε} {ε'} p =
  subst₂ _≾ₑ_ (cong valᵉ ([id]ᵉ ε)) (cong valᵉ ([id]ᵉ ε')) (runₑ p idˢ ⊨ᵍ-∅)

val-≡̂ᵣ : {ρ ρ' : RExp ∅ˢ} → ρ ≡̂ᵣ ρ' → valʳ ρ ≃ᵣ valʳ ρ'
val-≡̂ᵣ p = val-≾ᵣ (≡̂ᵣ⇒≾ p) , val-≾ᵣ (≡̂ᵣ⇒≿ p)

val-≡̂ₑ : {ε ε' : EExp ∅ˢ} → ε ≡̂ₑ ε' → valᵉ ε ≃ₑ valᵉ ε'
val-≡̂ₑ p = val-≾ₑ (≡̂ₑ⇒≾ p) , val-≾ₑ (≡̂ₑ⇒≿ p)

-- Completeness, under any closed hypotheses

val-≾ᵣ⁻ : {Q : Hyps ∅ˢ} {ρ ρ' : RExp ∅ˢ} → valʳ ρ ≾ᵣ valʳ ρ' → Q ⊩ ρ ≾̂ᵣ ρ'
val-≾ᵣ⁻ {ρ = ρ} {ρ'} p = semᵣ λ δ _ →
  subst₂ _≾ᵣ_ (cong valʳ (sym (closed-[]ʳ δ ρ))) (cong valʳ (sym (closed-[]ʳ δ ρ'))) p

val-≾ₑ⁻ : {Q : Hyps ∅ˢ} {ε ε' : EExp ∅ˢ} → valᵉ ε ≾ₑ valᵉ ε' → Q ⊩ ε ≾̂ₑ ε'
val-≾ₑ⁻ {ε = ε} {ε'} p = semₑ λ δ _ →
  subst₂ _≾ₑ_ (cong valᵉ (sym (closed-[]ᵉ δ ε))) (cong valᵉ (sym (closed-[]ᵉ δ ε'))) p

val-≡̂ᵣ⁻ : {ρ ρ' : RExp ∅ˢ} → valʳ ρ ≃ᵣ valʳ ρ' → ρ ≡̂ᵣ ρ'
val-≡̂ᵣ⁻ p = mk≡̂ᵣ (val-≾ᵣ⁻ (proj₁ p)) (val-≾ᵣ⁻ (proj₂ p))

val-≡̂ₑ⁻ : {ε ε' : EExp ∅ˢ} → valᵉ ε ≃ₑ valᵉ ε' → ε ≡̂ₑ ε'
val-≡̂ₑ⁻ p = mk≡̂ₑ (val-≾ₑ⁻ (proj₁ p)) (val-≾ₑ⁻ (proj₂ p))

valᵉ-conv : (ε : EExp ∅ˢ) → ε ≡̂ₑ econst (valᵉ ε)
valᵉ-conv ε = val-≡̂ₑ⁻ ≃ₑ-refl

valʳ-conv : (ρ : RExp ∅ˢ) → ρ ≡̂ᵣ rconst (valʳ ρ)
valʳ-conv ρ = val-≡̂ᵣ⁻ ≃ᵣ-refl

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

⊩Et? : (A : OVType ∅ˢ) → Dec (∅ᴴ ⊩Et A)
⊩Et? (tvar ())
⊩Et? (Base b) with eternalBaseType? b
... | yes p = yes (Baseₑ p)
... | no ¬p = no λ { (Baseₑ p) → ⊥-elim-irr (¬p p) }
⊩Et? unit      = yes unitₑ
⊩Et? bool      = yes boolₑ
⊩Et? nat       = yes natₑ
⊩Et? (A |×| B) =
  map′ (λ (p , q) → p |×|ₑ q) (λ { (p |×|ₑ q) → p , q }) (⊩Et? A ×-dec ⊩Et? B)
⊩Et? (A |+| B) =
  map′ (λ (p , q) → p |+|ₑ q) (λ { (p |+|ₑ q) → p , q }) (⊩Et? A ×-dec ⊩Et? B)
⊩Et? (list A)  = map′ listₑ (λ { (listₑ p) → p }) (⊩Et? A)
⊩Et? empty     = yes emptyₑ
⊩Et? (A ⇒ C)   = no λ ()
⊩Et? (C ⇛ D)   = no λ ()
⊩Et? ([ ρ ] A) = no λ ()

-- The var-rule disjunction: eternality, or a value below the unit

VarOK-∅ : {A : OVType ∅ˢ} {ρ : RExp ∅ˢ}
        → VarOK ∅ᴴ A ρ → (∅ᴴ ⊩Et A) ⊎ (valʳ ρ ≾ᵣ 𝟏ᵣ)
VarOK-∅ ok = [ inj₁ , (λ le → inj₂ (val-≾ᵣ le)) ]′ (VarOK-∅ᴴ ok)

VarOK-∅⁻ : {A : OVType ∅ˢ} {ρ : RExp ∅ˢ}
         → (∅ᴴ ⊩Et A) ⊎ (valʳ ρ ≾ᵣ 𝟏ᵣ) → VarOK ∅ᴴ A ρ
VarOK-∅⁻ (inj₁ et) = et-ok et
VarOK-∅⁻ (inj₂ le) = ≾ᵘ-ok (val-≾ᵣ⁻ le)

VarOK? : (A : OVType ∅ˢ) → (ρ : RExp ∅ˢ) → Dec (VarOK ∅ᴴ A ρ)
VarOK? A ρ with ⊩Et? A | valʳ ρ ≾ᵣ? 𝟏ᵣ
... | yes et | _      = yes (et-ok et)
... | no  _  | yes le = yes (≾ᵘ-ok (val-≾ᵣ⁻ le))
... | no ¬et | no ¬le = no λ ok → [ ¬et , ¬le ]′ (VarOK-∅ ok)

-- Subtyping preserves the outermost former

former : ∀ {Θ} → OVType Θ → ℕ
former (tvar _)  = 0
former (Base _)  = 1
former unit      = 2
former bool      = 3
former (_ |×| _) = 4
former empty     = 5
former (_ ⇒ _)   = 6
former ([ _ ] _) = 7
former nat       = 8
former (_ |+| _) = 9
former (list _)  = 10
former (_ ⇛ _)   = 11

<:̂ᵛ-former : ∀ {Θ} {Q : Hyps Θ} {A B : OVType Θ} → Q ∣ A <:̂ᵛ B → former A ≡ former B
<:̂ᵛ-former (tvarₛ _)  = refl
<:̂ᵛ-former (Baseₛ _)  = refl
<:̂ᵛ-former unitₛ      = refl
<:̂ᵛ-former boolₛ      = refl
<:̂ᵛ-former natₛ       = refl
<:̂ᵛ-former (_ |×|ₛ _) = refl
<:̂ᵛ-former (_ |+|ₛ _) = refl
<:̂ᵛ-former (listₛ _)  = refl
<:̂ᵛ-former emptyₛ     = refl
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
same unit      unit       refl = yes unitₛ
same bool      bool       refl = yes boolₛ
same nat       nat        refl = yes natₛ
same (A |×| B) (A' |×| B') refl =
  map′ (λ (p , q) → p |×|ₛ q) (λ { (p |×|ₛ q) → p , q }) (A <:̂ᵛ? A' ×-dec B <:̂ᵛ? B')
same (A |+| B) (A' |+| B') refl =
  map′ (λ (p , q) → p |+|ₛ q) (λ { (p |+|ₛ q) → p , q }) (A <:̂ᵛ? A' ×-dec B <:̂ᵛ? B')
same (list A)  (list A')  refl =
  map′ listₛ (λ { (listₛ p) → p }) (A <:̂ᵛ? A')
same empty     empty      refl = yes emptyₛ
same (A ⇒ C)   (A' ⇒ C')  refl =
  map′ (λ (p , q) → p ⇒ₛ q) (λ { (p ⇒ₛ q) → p , q }) (A' <:̂ᵛ? A ×-dec C <:̂ᶜ? C')
same (C ⇛ D)   (C' ⇛ D')  refl =
  map′ (λ (p , q) → p ⇛ₛ q) (λ { (p ⇛ₛ q) → p , q }) (C' <:̂ᶜ? C ×-dec D <:̂ᶜ? D')
same ([ ρ ] A) ([ ρ' ] A') refl =
  map′ (λ (p , q) → [ p ]ₛ q) (λ { ([ p ]ₛ q) → p , q }) (ρ' ≾̂ᵣ? ρ ×-dec A <:̂ᵛ? A')

A <:̂ᵛ? B with former A ≟ℕ former B
... | yes eq = same A B eq
... | no  ne = no λ p → ne (<:̂ᵛ-former p)

(A ! ε) <:̂ᶜ? (A' ! ε') =
  map′ (λ (p , q) → p !ₛ q) (λ { (p !ₛ q) → p , q }) (A <:̂ᵛ? A' ×-dec ε ≾̂ₑ? ε')

------------------------------------------------------------------------
-- Satisfaction at closed instances: each hypothesis holds, a quantified
-- one at every instance of its rigids

infix 4 _⊨_

_⊨_ : ∀ {Θ} → Subst Θ ∅ˢ → Hyps Θ → Set
δ ⊨ Q = ∅ᴴ ⊩ᴵ Q [ δ ]

⊨⇒⊨ᵍ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} → δ ⊨ Q → δ ⊨ᵍ Q
⊨⇒⊨ᵍ h =
  mk⊨ᵍ (λ m → val-≾ᵣ (⊩ordᵣᴵ h m)) (λ m → val-≾ₑ (⊩ordₑᴵ h m))
       (λ m es → mk⊨ᵒ (λ mφ → val-≾ᵣ (⊩ors (⊩qhypsᴵ h m es) mφ))
                      (λ mφ → val-≾ₑ (⊩oes (⊩qhypsᴵ h m es) mφ)))

-- A closed instance after `δ ↑ᵉⁿ k` instantiates the rigids

↑ᵉⁿ-⨟-closed : ∀ {Θ} → (k : ℕ) → (δ : Subst Θ ∅ˢ) → (δ' : Subst (∅ˢ +eⁿ k) ∅ˢ)
             → ((δ ↑ᵉⁿ k) ⨟ˢ δ') ≐ˢ (δ ,ᵉⁿ mapᵛ (_[ δ' ]ᵉ) (varsⁿ k))
↑ᵉⁿ-⨟-closed k δ δ' =
  ≐ˢ-trans (⨟-congʳ (δ ↑ᵉⁿ k) (wkˢⁿ-split k δ'))
  (≐ˢ-trans (↑ᵉⁿ-,ᵉⁿ δ (wkˢⁿ k ⨟ˢ δ') k es)
            (≐ˢ-,ᵉⁿ (≐ˢ-trans (⨟-congʳ δ (mk≐ˢ (λ ()) (λ ()) (λ ()))) (⨟-idʳ δ)) es))
  where
    es = mapᵛ (_[ δ' ]ᵉ) (varsⁿ k)

-- Satisfaction is entailment from no hypotheses

⊨⇒⊩ᴴ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} → δ ⊨ Q → ∅ᴴ ⊩ᴴ Q [ δ ]
⊨⇒⊩ᴴ {Θ} {Q} {δ} h =
  mk⊩ᴴ (⊩etsᴵ h) (⊩subᵥᴵ h) (⊩ordᵣᴵ h) (⊩ordₑᴵ h) (⊩disjᴵ h) qh
  where
    qh : ∀ {O} → O ∈ qhyps Q → ∅ᴴ ⊩ᴼ O [ δ ]
    qh {O} m = subst (λ H → H ⊩ᵒ body O [ δ ↑ᵉⁿ k ]) (sym (wkᵉⁿ-∅ᴴ k)) (mk⊩ᵒ r e)
      where
        k = rigids O

        s : (δ' : Subst (∅ˢ +eⁿ k) ∅ˢ) → (δ ,ᵉⁿ mapᵛ (_[ δ' ]ᵉ) (varsⁿ k)) ⊨ᵒ body O
        s δ' = ⊨ᵍᵠ (⊨⇒⊨ᵍ h) m (mapᵛ (_[ δ' ]ᵉ) (varsⁿ k))

        eqʳ : (δ' : Subst (∅ˢ +eⁿ k) ∅ˢ) → (x : RExp (Θ +eⁿ k))
            → valʳ (x [ δ ,ᵉⁿ mapᵛ (_[ δ' ]ᵉ) (varsⁿ k) ]ʳ) ≡ valʳ (x [ δ ↑ᵉⁿ k ]ʳ [ δ' ]ʳ)
        eqʳ δ' x = cong valʳ (sym (trans ([⨟]ʳ x (δ ↑ᵉⁿ k) δ') ([≐]ʳ (↑ᵉⁿ-⨟-closed k δ δ') x)))

        eqᵉ : (δ' : Subst (∅ˢ +eⁿ k) ∅ˢ) → (x : EExp (Θ +eⁿ k))
            → valᵉ (x [ δ ,ᵉⁿ mapᵛ (_[ δ' ]ᵉ) (varsⁿ k) ]ᵉ) ≡ valᵉ (x [ δ ↑ᵉⁿ k ]ᵉ [ δ' ]ᵉ)
        eqᵉ δ' x = cong valᵉ (sym (trans ([⨟]ᵉ x (δ ↑ᵉⁿ k) δ') ([≐]ᵉ (↑ᵉⁿ-⨟-closed k δ δ') x)))

        r : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors (body O) → ∅ᴴ ⊩ ρ [ δ ↑ᵉⁿ k ]ʳ ≾̂ᵣ ρ' [ δ ↑ᵉⁿ k ]ʳ
        r {ρ} {ρ'} mφ = semᵣ λ δ' _ → subst₂ _≾ᵣ_ (eqʳ δ' ρ) (eqʳ δ' ρ') (⊨ᵒʳ (s δ') mφ)

        e : ∀ {ε ε'} → (ε , ε') ∈ oes (body O) → ∅ᴴ ⊩ ε [ δ ↑ᵉⁿ k ]ᵉ ≾̂ₑ ε' [ δ ↑ᵉⁿ k ]ᵉ
        e {ε} {ε'} mφ = semₑ λ δ' _ → subst₂ _≾ₑ_ (eqᵉ δ' ε) (eqᵉ δ' ε') (⊨ᵒᵉ (s δ') mφ)

⊩ᴴ⇒⊨ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} → ∅ᴴ ⊩ᴴ Q [ δ ] → δ ⊨ Q
⊩ᴴ⇒⊨ = ⊩ᴴ⇒ᴵ

-- Soundness: entailed orderings hold at satisfying instances

sound-≾ᵣ⁰ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} {ρ ρ' : RExp Θ}
          → Q ⊩ ρ ≾̂ᵣ ρ' → δ ⊨ Q → valʳ (ρ [ δ ]ʳ) ≾ᵣ valʳ (ρ' [ δ ]ʳ)
sound-≾ᵣ⁰ {δ = δ} p h = runᵣ p δ (⊨⇒⊨ᵍ h)

sound-≾ₑ⁰ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} {ε ε' : EExp Θ}
          → Q ⊩ ε ≾̂ₑ ε' → δ ⊨ Q → valᵉ (ε [ δ ]ᵉ) ≾ₑ valᵉ (ε' [ δ ]ᵉ)
sound-≾ₑ⁰ {δ = δ} p h = runₑ p δ (⊨⇒⊨ᵍ h)

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

-- Semantic entailment

infix 4 _⊨ᴴ_

_⊨ᴴ_ : ∀ {Θ} → Hyps Θ → Hyps Θ → Set
_⊨ᴴ_ {Θ} Q Q' = (δ : Subst Θ ∅ˢ) → ∅ᴴ ⊩ᴴ Q [ δ ] → ∅ᴴ ⊩ᴴ Q' [ δ ]

⊨ᴴ-refl : ∀ {Θ} {Q : Hyps Θ} → Q ⊨ᴴ Q
⊨ᴴ-refl δ h = h

⊨ᴴ-trans : ∀ {Θ} {Q Q' Q'' : Hyps Θ} → Q ⊨ᴴ Q' → Q' ⊨ᴴ Q'' → Q ⊨ᴴ Q''
⊨ᴴ-trans e e' δ h = e' δ (e δ h)

⊩ᴴ-⊨ᴴ : ∀ {Θ} {Q Q' : Hyps Θ} → Q ⊩ᴴ Q' → Q ⊨ᴴ Q'
⊩ᴴ-⊨ᴴ e δ h = ⊩ᴴ-⨟ h e

-- From entailment of the atoms and, per instance, the disjunctions

mk⊨ᴴ : ∀ {Θ} {Q Q' : Hyps Θ}
     → (∀ {α} → α ∈ ets Q' → Q ⊩Et tvar α)
     → (∀ {α β} → (α , β) ∈ subᵥ Q' → Q ∣ tvar α <:̂ᵛ tvar β)
     → (∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q' → Q ⊩ ρ ≾̂ᵣ ρ')
     → (∀ {ε ε'} → (ε , ε') ∈ ordₑ Q' → Q ⊩ ε ≾̂ₑ ε')
     → ((δ : Subst Θ ∅ˢ) → ∅ᴴ ⊩ᴴ Q [ δ ]
        → ∀ {A ρ} → (A , ρ) ∈ disj Q' → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ))
     → (∀ {O} → O ∈ qhyps Q' → Q ⊩ᴼ O [ idˢ ])
     → Q ⊨ᴴ Q'
mk⊨ᴴ et sb oR oE dj qh δ h =
  mk⊩ᴴ (λ m → ⊩Et-subst h (et m)) (λ m → <:̂ᵛ-subst h (sb m))
       (λ m → ⊩-substᵣ h (oR m)) (λ m → ⊩-substₑ h (oE m)) (dj δ h)
       (λ {O} m → ⊩ᴼ-resp-≐ˢ O (⨟-idˡ δ) (⊩ᴼ-⨟ O h (qh m)))

VarOK-∅-mono : {A A' : OVType ∅ˢ} {ρ ρ' : RExp ∅ˢ}
             → (∅ᴴ ⊩Et A → ∅ᴴ ⊩Et A') → ∅ᴴ ⊩ ρ' ≾̂ᵣ ρ → VarOK ∅ᴴ A ρ → VarOK ∅ᴴ A' ρ'
VarOK-∅-mono f q ok = [ (λ et → et-ok (f et)) , (λ le → ≾ᵘ-ok (transᵣ q le)) ]′ (VarOK-∅ᴴ ok)

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
           → (∅ᴴ ⊩Et A [ δ ]ᵛ) ⊎ (valʳ (ρ [ δ ]ʳ) ≾ᵣ 𝟏ᵣ)
inst-VarOK h ok = VarOK-∅ (VarOK-subst h ok)

-- An ordering between expressions convertible to constants is theirs

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
