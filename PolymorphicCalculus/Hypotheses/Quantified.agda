------------------------------------------------------------------
-- Quantified orderings                                         --
--                                                              --
-- A quantified ordering `∀ᵉ j₁ … jₖ. O` is a list `O` of grade --
-- orderings over the scope extended by `k` rigid effect-grade  --
-- variables, `j₁` outermost, labelled with the operation whose --
-- handler clause left it (for reading only). Substitution acts --
-- under its rigids; a vector of expressions instantiates them  --
-- (`_,ᵉⁿ_`).                                                   --
------------------------------------------------------------------

open import Data.List.Base using (List; map)
open import Data.List.Properties using (map-∘; map-cong; map-id)
open import Data.Maybe.Base using (Maybe)
open import Data.Fin using (zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Vec.Base using (Vec; []; _∷_) renaming (map to mapᵛ)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Hypotheses.Quantified (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops using (Op)

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.GradeSubstitution S

------------------------------------------------------------------------
-- Rigid binders

infixl 30 _+eⁿ_ _↑ᵉⁿ_

-- The rigids are bound outermost first

_+eⁿ_ : Scope → ℕ → Scope
Θ +eⁿ zero  = Θ
Θ +eⁿ suc k = (Θ +e) +eⁿ k

_↑ᵉⁿ_ : ∀ {Θ Θ'} → Subst Θ Θ' → (k : ℕ) → Subst (Θ +eⁿ k) (Θ' +eⁿ k)
σ ↑ᵉⁿ zero  = σ
σ ↑ᵉⁿ suc k = (σ ↑ᵉ) ↑ᵉⁿ k

≐ˢ-↑ᵉⁿ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → (k : ℕ) → (σ ↑ᵉⁿ k) ≐ˢ (σ' ↑ᵉⁿ k)
≐ˢ-↑ᵉⁿ p zero    = p
≐ˢ-↑ᵉⁿ p (suc k) = ≐ˢ-↑ᵉⁿ (≐ˢ-↑ᵉ p) k

⨟-↑ᵉⁿ : ∀ {Θ Θ₁ Θ₂} → (σ : Subst Θ Θ₁) → (δ : Subst Θ₁ Θ₂) → (k : ℕ)
      → ((σ ↑ᵉⁿ k) ⨟ˢ (δ ↑ᵉⁿ k)) ≐ˢ ((σ ⨟ˢ δ) ↑ᵉⁿ k)
⨟-↑ᵉⁿ σ δ zero    = ≐ˢ-refl
⨟-↑ᵉⁿ σ δ (suc k) = ≐ˢ-trans (⨟-↑ᵉⁿ (σ ↑ᵉ) (δ ↑ᵉ) k) (≐ˢ-↑ᵉⁿ (⨟-↑ᵉ σ δ) k)

-- Instantiating the rigids: the outermost by the head of the vector

infixl 28 _,ᵉⁿ_

_,ᵉⁿ_ : ∀ {Θ Θ' k} → Subst Θ Θ' → Vec (EExp Θ') k → Subst (Θ +eⁿ k) Θ'
σ ,ᵉⁿ []       = σ
σ ,ᵉⁿ (ε ∷ es) = (σ ,ᵉ ε) ,ᵉⁿ es

≐ˢ-,ᵉⁿ : ∀ {Θ Θ' k} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → (es : Vec (EExp Θ') k)
       → (σ ,ᵉⁿ es) ≐ˢ (σ' ,ᵉⁿ es)
≐ˢ-,ᵉⁿ p []       = p
≐ˢ-,ᵉⁿ p (ε ∷ es) = ≐ˢ-,ᵉⁿ (≐ˢ-,ᵉ p ε) es

↑ᵉ-,ᵉ : ∀ {Θ Θ₁ Θ₂} → (σ : Subst Θ Θ₁) → (τ : Subst Θ₁ Θ₂) → (ε : EExp Θ₂)
      → ((σ ↑ᵉ) ⨟ˢ (τ ,ᵉ ε)) ≐ˢ ((σ ⨟ˢ τ) ,ᵉ ε)
↑ᵉ-,ᵉ σ τ ε = mk≐ˢ (λ α → wk-,ᵉ-v τ ε (sTy σ α)) (λ i → wk-,ᵉ-r τ ε (sR σ i))
                   (λ { zero → refl ; (suc i) → wk-,ᵉ-e τ ε (sE σ i) })

↑ᵉⁿ-,ᵉⁿ : ∀ {Θ Θ₁ Θ₂} → (σ : Subst Θ Θ₁) → (τ : Subst Θ₁ Θ₂) → (k : ℕ)
        → (es : Vec (EExp Θ₂) k) → ((σ ↑ᵉⁿ k) ⨟ˢ (τ ,ᵉⁿ es)) ≐ˢ ((σ ⨟ˢ τ) ,ᵉⁿ es)
↑ᵉⁿ-,ᵉⁿ σ τ zero    []       = ≐ˢ-refl
↑ᵉⁿ-,ᵉⁿ σ τ (suc k) (ε ∷ es) =
  ≐ˢ-trans (↑ᵉⁿ-,ᵉⁿ (σ ↑ᵉ) (τ ,ᵉ ε) k es) (≐ˢ-,ᵉⁿ (↑ᵉ-,ᵉ σ τ ε) es)

,ᵉ-⨟ : ∀ {Θ Θ₁ Θ₂} → (σ : Subst Θ Θ₁) → (ε : EExp Θ₁) → (δ : Subst Θ₁ Θ₂)
     → ((σ ,ᵉ ε) ⨟ˢ δ) ≐ˢ ((σ ⨟ˢ δ) ,ᵉ ε [ δ ]ᵉ)
,ᵉ-⨟ σ ε δ = mk≐ˢ (λ α → refl) (λ i → refl) (λ { zero → refl ; (suc i) → refl })

,ᵉⁿ-⨟ : ∀ {Θ Θ₁ Θ₂ k} → (σ : Subst Θ Θ₁) → (es : Vec (EExp Θ₁) k) → (δ : Subst Θ₁ Θ₂)
      → ((σ ,ᵉⁿ es) ⨟ˢ δ) ≐ˢ ((σ ⨟ˢ δ) ,ᵉⁿ mapᵛ (_[ δ ]ᵉ) es)
,ᵉⁿ-⨟ σ []       δ = ≐ˢ-refl
,ᵉⁿ-⨟ σ (ε ∷ es) δ =
  ≐ˢ-trans (,ᵉⁿ-⨟ (σ ,ᵉ ε) es δ) (≐ˢ-,ᵉⁿ (,ᵉ-⨟ σ ε δ) (mapᵛ (_[ δ ]ᵉ) es))

-- Weakening by `k` rigids, and the rigids themselves

wkˢⁿ : ∀ {Θ} → (k : ℕ) → Subst Θ (Θ +eⁿ k)
wkˢⁿ zero    = idˢ
wkˢⁿ (suc k) = wkˢᵉ ⨟ˢ wkˢⁿ k

varsⁿ : ∀ {Θ} → (k : ℕ) → Vec (EExp (Θ +eⁿ k)) k
varsⁿ         zero    = []
varsⁿ {Θ} (suc k) = evar (newᵉ {Θ}) [ wkˢⁿ k ]ᵉ ∷ varsⁿ {Θ +e} k

wkˢᵉ-,ᵉ-new : ∀ {Θ} → (wkˢᵉ {Θ} ,ᵉ evar (newᵉ {Θ})) ≐ˢ idˢ {Θ +e}
wkˢᵉ-,ᵉ-new = mk≐ˢ (λ α → refl) (λ i → refl) (λ { zero → refl ; (suc i) → refl })

wkˢⁿ-varsⁿ : ∀ {Θ} → (k : ℕ) → (wkˢⁿ {Θ} k ,ᵉⁿ varsⁿ k) ≐ˢ idˢ
wkˢⁿ-varsⁿ         zero    = ≐ˢ-refl
wkˢⁿ-varsⁿ {Θ} (suc k) =
  ≐ˢ-trans (≐ˢ-,ᵉⁿ step (varsⁿ k)) (wkˢⁿ-varsⁿ {Θ +e} k)
  where
    step : ((wkˢᵉ {Θ} ⨟ˢ wkˢⁿ k) ,ᵉ evar (newᵉ {Θ}) [ wkˢⁿ k ]ᵉ) ≐ˢ wkˢⁿ {Θ +e} k
    step = ≐ˢ-trans (≐ˢ-sym (,ᵉ-⨟ (wkˢᵉ {Θ}) (evar (newᵉ {Θ})) (wkˢⁿ k)))
                    (≐ˢ-trans (⨟-congˡ (wkˢᵉ-,ᵉ-new {Θ}) (wkˢⁿ {Θ +e} k)) (⨟-idˡ (wkˢⁿ {Θ +e} k)))

-- A substitution under the rigids: its restriction, then their images

wkˢⁿ-split : ∀ {Θ Ψ} → (k : ℕ) → (δ : Subst (Θ +eⁿ k) Ψ)
           → δ ≐ˢ ((wkˢⁿ k ⨟ˢ δ) ,ᵉⁿ mapᵛ (_[ δ ]ᵉ) (varsⁿ k))
wkˢⁿ-split k δ =
  ≐ˢ-trans (≐ˢ-sym (⨟-idˡ δ))
  (≐ˢ-trans (≐ˢ-sym (⨟-congˡ (wkˢⁿ-varsⁿ k) δ)) (,ᵉⁿ-⨟ (wkˢⁿ k) (varsⁿ k) δ))

wkˢⁿ-↑ᵉⁿ : ∀ {Θ Θ'} → (k : ℕ) → (σ : Subst Θ Θ')
         → (wkˢⁿ k ⨟ˢ (σ ↑ᵉⁿ k)) ≐ˢ (σ ⨟ˢ wkˢⁿ k)
wkˢⁿ-↑ᵉⁿ zero    σ = ≐ˢ-trans (⨟-idˡ σ) (≐ˢ-sym (⨟-idʳ σ))
wkˢⁿ-↑ᵉⁿ (suc k) σ =
  ≐ˢ-trans (⨟-assoc wkˢᵉ (wkˢⁿ k) ((σ ↑ᵉ) ↑ᵉⁿ k))
  (≐ˢ-trans (⨟-congʳ wkˢᵉ (wkˢⁿ-↑ᵉⁿ k (σ ↑ᵉ)))
  (≐ˢ-trans (≐ˢ-sym (⨟-assoc wkˢᵉ (σ ↑ᵉ) (wkˢⁿ k)))
  (≐ˢ-trans (⨟-congˡ (wkˢᵉ-↑ᵉ σ) (wkˢⁿ k))
            (⨟-assoc σ wkˢᵉ (wkˢⁿ k)))))

from∅ : ∀ {Θ} → Subst ∅ˢ Θ
from∅ = sub (λ ()) (λ ()) (λ ())

from∅-⨟ : ∀ {Θ Θ'} → (δ : Subst Θ Θ') → (from∅ ⨟ˢ δ) ≐ˢ from∅
from∅-⨟ δ = mk≐ˢ (λ ()) (λ ()) (λ ())

↑-inst : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (k : ℕ) → (es : Vec (EExp Θ') k)
       → ((σ ↑ᵉⁿ k) ⨟ˢ (idˢ ,ᵉⁿ es)) ≐ˢ (σ ,ᵉⁿ es)
↑-inst σ k es = ≐ˢ-trans (↑ᵉⁿ-,ᵉⁿ σ idˢ k es) (≐ˢ-,ᵉⁿ (⨟-idʳ σ) es)

↑ᵉⁿ-vars : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (k : ℕ)
         → ((σ ⨟ˢ wkˢⁿ k) ,ᵉⁿ varsⁿ k) ≐ˢ (σ ↑ᵉⁿ k)
↑ᵉⁿ-vars σ k =
  ≐ˢ-sym (≐ˢ-trans (≐ˢ-sym (⨟-idʳ (σ ↑ᵉⁿ k)))
         (≐ˢ-trans (⨟-congʳ (σ ↑ᵉⁿ k) (≐ˢ-sym (wkˢⁿ-varsⁿ k)))
                   (↑ᵉⁿ-,ᵉⁿ σ (wkˢⁿ k) k (varsⁿ k))))

inst-⨟ : ∀ {Θ Θ' k} → (es : Vec (EExp Θ) k) → (σ : Subst Θ Θ')
       → ((idˢ ,ᵉⁿ es) ⨟ˢ σ) ≐ˢ (σ ,ᵉⁿ mapᵛ (_[ σ ]ᵉ) es)
inst-⨟ es σ = ≐ˢ-trans (,ᵉⁿ-⨟ idˢ es σ) (≐ˢ-,ᵉⁿ (⨟-idˡ σ) (mapᵛ (_[ σ ]ᵉ) es))

fact-⨟ : ∀ {Θ Θ' k} → (es : Vec (EExp Θ) k) → (σ : Subst Θ Θ')
       → ((from∅ ,ᵉⁿ es) ⨟ˢ σ) ≐ˢ (from∅ ,ᵉⁿ mapᵛ (_[ σ ]ᵉ) es)
fact-⨟ es σ = ≐ˢ-trans (,ᵉⁿ-⨟ from∅ es σ) (≐ˢ-,ᵉⁿ (from∅-⨟ σ) (mapᵛ (_[ σ ]ᵉ) es))

------------------------------------------------------------------------
-- Grade orderings

mapᵖ : ∀ {A B : Set} → (A → B) → A × A → B × B
mapᵖ f (x , y) = f x , f y

record Ords (Ψ : Scope) : Set where
  constructor ords
  field
    ors : List (RExp Ψ × RExp Ψ)
    oes : List (EExp Ψ × EExp Ψ)

open Ords public

infixl 50 _[_]ᴼ

_[_]ᴼ : ∀ {Ψ Ψ'} → Ords Ψ → Subst Ψ Ψ' → Ords Ψ'
o [ σ ]ᴼ = ords (map (mapᵖ (_[ σ ]ʳ)) (ors o)) (map (mapᵖ (_[ σ ]ᵉ)) (oes o))

[≐]ᴼ : ∀ {Ψ Ψ'} {σ σ' : Subst Ψ Ψ'} → σ ≐ˢ σ' → (o : Ords Ψ) → o [ σ ]ᴼ ≡ o [ σ' ]ᴼ
[≐]ᴼ p (ords r e) =
  cong₂ ords (map-cong (λ { (x , y) → cong₂ _,_ ([≐]ʳ p x) ([≐]ʳ p y) }) r)
             (map-cong (λ { (x , y) → cong₂ _,_ ([≐]ᵉ p x) ([≐]ᵉ p y) }) e)

[⨟]ᴼ : ∀ {Ψ Ψ₁ Ψ₂} → (o : Ords Ψ) → (σ : Subst Ψ Ψ₁) → (δ : Subst Ψ₁ Ψ₂)
     → o [ σ ]ᴼ [ δ ]ᴼ ≡ o [ σ ⨟ˢ δ ]ᴼ
[⨟]ᴼ (ords r e) σ δ =
  cong₂ ords (trans (sym (map-∘ r))
                    (map-cong (λ { (x , y) → cong₂ _,_ ([⨟]ʳ x σ δ) ([⨟]ʳ y σ δ) }) r))
             (trans (sym (map-∘ e))
                    (map-cong (λ { (x , y) → cong₂ _,_ ([⨟]ᵉ x σ δ) ([⨟]ᵉ y σ δ) }) e))

[id]ᴼ : ∀ {Ψ} → (o : Ords Ψ) → o [ idˢ ]ᴼ ≡ o
[id]ᴼ (ords r e) =
  cong₂ ords (trans (map-cong (λ { (x , y) → cong₂ _,_ ([id]ʳ x) ([id]ʳ y) }) r) (map-id r))
             (trans (map-cong (λ { (x , y) → cong₂ _,_ ([id]ᵉ x) ([id]ᵉ y) }) e) (map-id e))

------------------------------------------------------------------------
-- Quantified orderings

record QOrd (Θ : Scope) : Set where
  constructor qord
  field
    label  : Maybe Op
    rigids : ℕ
    body   : Ords (Θ +eⁿ rigids)

open QOrd public

QOrds : Scope → Set
QOrds Θ = List (QOrd Θ)

infixl 50 _[_]ᵠ

_[_]ᵠ : ∀ {Θ Θ'} → QOrd Θ → Subst Θ Θ' → QOrd Θ'
O [ σ ]ᵠ = qord (label O) (rigids O) (body O [ σ ↑ᵉⁿ rigids O ]ᴼ)

[≐]ᵠ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → (O : QOrd Θ) → O [ σ ]ᵠ ≡ O [ σ' ]ᵠ
[≐]ᵠ p (qord l k o) = cong (qord l k) ([≐]ᴼ (≐ˢ-↑ᵉⁿ p k) o)

[⨟]ᵠ : ∀ {Θ Θ₁ Θ₂} → (O : QOrd Θ) → (σ : Subst Θ Θ₁) → (δ : Subst Θ₁ Θ₂)
      → O [ σ ]ᵠ [ δ ]ᵠ ≡ O [ σ ⨟ˢ δ ]ᵠ
[⨟]ᵠ (qord l k o) σ δ =
  cong (qord l k) (trans ([⨟]ᴼ o (σ ↑ᵉⁿ k) (δ ↑ᵉⁿ k)) ([≐]ᴼ (⨟-↑ᵉⁿ σ δ k) o))

↑ᵉⁿ-id : ∀ {Θ} → (k : ℕ) → (idˢ {Θ} ↑ᵉⁿ k) ≐ˢ idˢ
↑ᵉⁿ-id zero    = ≐ˢ-refl
↑ᵉⁿ-id (suc k) = ≐ˢ-trans (≐ˢ-↑ᵉⁿ ↑ᵉ-id k) (↑ᵉⁿ-id k)

[id]ᵠ : ∀ {Θ} → (O : QOrd Θ) → O [ idˢ ]ᵠ ≡ O
[id]ᵠ (qord l k o) = cong (qord l k) (trans ([≐]ᴼ (↑ᵉⁿ-id k) o) ([id]ᴼ o))
