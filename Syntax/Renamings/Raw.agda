-------------------------------------------------------------
-- Context renamings and their action on well-typed terms  --
--                                                         --
-- Note: These are raw (underlying) renamings that are     --
-- further refined in Syntax.Renamings to respect ctx-time --
-------------------------------------------------------------

module Syntax.Renamings.Raw where

open import Data.Product

open import Relation.Nullary

open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Types

open import Util.Equality
open import Util.Time

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 

-- Subst for time annotations of variables (for convenience)

var-τ-subst : ∀ {Γ A τ τ'} → τ ≡ τ' → A ∈[ τ ] Γ → A ∈[ τ' ] Γ
var-τ-subst refl x = x

-- Variable renamings (an extra condition on ctx-time will be imposed later)

VRen : Ctx → Ctx → Set
VRen Γ Γ' = ∀ {A τ} → A ∈[ τ ] Γ → Σ[ τ' ∈ Time ] (τ ≤ τ' × A ∈[ τ' ] Γ')

-- Identity renaming

id-vren : ∀ {Γ} → VRen Γ Γ
id-vren {Γ} {A} {τ} x = τ , ≤-refl , x

-- Composition of renamings

_∘ᵛʳ_ : ∀ {Γ Γ' Γ''} → VRen Γ' Γ'' → VRen Γ Γ' → VRen Γ Γ''
_∘ᵛʳ_ ρ' ρ x with ρ x
... | τ' , p , y with ρ' y
... | τ'' , q , z = τ'' , ≤-trans p q , z

infixr 20 _∘ᵛʳ_

-- Weakening renaming

wk-vren : ∀ {Γ A} → VRen Γ (Γ ∷ A)
wk-vren {Γ} {A} {B} {τ} x = τ , ≤-refl , Tl-∷ x

-- Variable renaming

var-vren : ∀ {Γ A τ} → A ∈[ τ ] Γ → VRen (Γ ∷ A) Γ
var-vren {Γ} {A} {τ} x Hd =
  τ , z≤n , x
var-vren {Γ} {A} {τ} x (Tl-∷ {τ = τ'} y) =
  τ' , ≤-refl , y

-- Strong monoidal functor renamings

⟨⟩-η-vren : ∀ {Γ} → VRen (Γ ⟨ 0 ⟩) Γ
⟨⟩-η-vren {Γ} (Tl-⟨⟩ {τ' = τ} x) =
  τ , ≤-refl , x

⟨⟩-η⁻¹-vren : ∀ {Γ} → VRen Γ (Γ ⟨ 0 ⟩)
⟨⟩-η⁻¹-vren {Γ} {A} {τ} x =
  τ , ≤-refl , Tl-⟨⟩ x

⟨⟩-μ-vren : ∀ {Γ τ τ'} → VRen (Γ ⟨ τ + τ' ⟩) (Γ ⟨ τ ⟩ ⟨ τ' ⟩)
⟨⟩-μ-vren {Γ} {τ} {τ'} {A} {.(τ + τ' + τ'')} (Tl-⟨⟩ {τ' = τ''} x) =
  τ' + (τ + τ'') ,
  ≤-reflexive
    (trans
      (cong (_+ τ'') (+-comm τ τ'))
      (+-assoc τ' τ τ'')) ,
  Tl-⟨⟩ (Tl-⟨⟩ x)

⟨⟩-μ⁻¹-vren : ∀ {Γ τ τ'} → VRen (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ + τ' ⟩)
⟨⟩-μ⁻¹-vren {Γ} {τ} {τ'} {A} {.(τ' + (τ + _))} (Tl-⟨⟩ (Tl-⟨⟩ {τ' = τ''} x)) =
  τ + τ' + τ'' ,
  ≤-reflexive
    (trans
      (sym (+-assoc τ' τ τ''))
      (cong (_+ τ'') (+-comm τ' τ))) ,
  Tl-⟨⟩ x

⟨⟩-≤-vren : ∀ {Γ τ τ'} → τ ≤ τ' → VRen (Γ ⟨ τ ⟩) (Γ ⟨ τ' ⟩)
⟨⟩-≤-vren {Γ} {.zero} {τ'} z≤n {A} {τ''} (Tl-⟨⟩ x) =
  τ' + τ'' , m≤n+m τ'' τ' , Tl-⟨⟩ x
⟨⟩-≤-vren {Γ} {suc τ} {suc τ'} (s≤s p) {A} (Tl-⟨⟩ x) =
  suc (τ' + _) , +-monoʳ-≤ 1 (+-monoˡ-≤ _ p) , Tl-⟨⟩ x

-- Derived modal weakening renaming

wk-⟨⟩-vren : ∀ {Γ τ} → VRen Γ (Γ ⟨ τ ⟩)
wk-⟨⟩-vren {Γ} {τ} =
      ⟨⟩-≤-vren z≤n
  ∘ᵛʳ ⟨⟩-η⁻¹-vren

-- Congruence renamings

cong-∷-vren : ∀ {Γ Γ' A} → VRen Γ Γ' → VRen (Γ ∷ A) (Γ' ∷ A)
cong-∷-vren {Γ} {Γ'} {A} ρ {.A} {.0} Hd =
  0 , ≤-refl , Hd
cong-∷-vren {Γ} {Γ'} {A} ρ {B} {τ} (Tl-∷ x) with ρ x
... | τ' , p , y =
  τ' , p , Tl-∷ y

cong-⟨⟩-vren : ∀ {Γ Γ' τ} → VRen Γ Γ' → VRen (Γ ⟨ τ ⟩) (Γ' ⟨ τ ⟩)
cong-⟨⟩-vren {Γ} {Γ'} {τ} ρ {A} {.(τ + τ')} (Tl-⟨⟩ {τ' = τ'} x) with ρ x
... | τ'' , p , y =
  τ + τ'' , +-monoʳ-≤ τ p , Tl-⟨⟩ y

-- Interaction between time-indexes of variables and -ᶜ

var-ᶜ : ∀ {Γ A τ τ'} → τ ≤ τ' → A ∈[ τ' ] Γ → A ∈[ τ' ∸ τ ] Γ -ᶜ τ
var-ᶜ {Γ ∷ A} {.A} {zero} {.0} p Hd =
  Hd
var-ᶜ {Γ ∷ B} {A} {zero} {τ'} p (Tl-∷ x) =
  Tl-∷ x
var-ᶜ {Γ ∷ B} {A} {suc τ} {τ'} p (Tl-∷ x) =
  var-ᶜ p x
var-ᶜ {Γ ⟨ τ'' ⟩} {A} {zero} p (Tl-⟨⟩ x) =
  Tl-⟨⟩ x
var-ᶜ {Γ ⟨ τ'' ⟩} {A} {suc τ} {.(τ'' + τ')} p (Tl-⟨⟩ {τ' = τ'} x) with suc τ ≤? τ''
... | yes q =
  var-τ-subst (sym (+-∸-comm _ q)) (Tl-⟨⟩ {τ = τ'' ∸ suc τ} x)
... | no ¬q =
  var-τ-subst
    (sym
      (trans
        (cong (_∸ suc τ) (+-comm τ'' τ') )
        (¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {τ'} {τ''} {suc τ} ¬q
          (m≤n+k⇒m∸k≤n (suc τ) τ' τ''
            (≤-trans
              p
              (≤-reflexive (+-comm τ'' τ')))))))
    (var-ᶜ {τ = suc τ ∸ τ''} (
      (m≤n+k⇒m∸k≤n (suc τ) τ' τ''
        (≤-trans
          p
          (≤-reflexive (+-comm τ'' τ'))))) x)

var-ᶜ-+ : ∀ {Γ A τ τ'} → A ∈[ τ' ] Γ -ᶜ τ → A ∈[ τ' + τ ] Γ
var-ᶜ-+ {Γ} {A} {zero} {τ'} x =
  var-τ-subst (sym (+-identityʳ _)) x
var-ᶜ-+ {Γ ∷ B} {A} {suc τ} {τ'} x =
  Tl-∷ (var-ᶜ-+ x)
var-ᶜ-+ {Γ ⟨ τ'' ⟩} {A} {suc τ} {τ'} x with suc τ ≤? τ''
var-ᶜ-+ {Γ ⟨ τ'' ⟩} {A} {suc τ} {.(τ'' ∸ suc τ + τ')} (Tl-⟨⟩ {τ' = τ'} x) | yes p =
  var-τ-subst
    (sym
      (trans
        (+-assoc (τ'' ∸ suc τ) τ' (suc τ))
        (trans
          (sym (+-∸-comm (τ' + suc τ) p))
          (trans
            (+-∸-assoc τ'' {τ' + suc τ} {suc τ} (m≤n+m (suc τ) τ'))
            (cong (τ'' +_)
              (m+n∸n≡m τ' (suc τ)))))))
    (Tl-⟨⟩ x)
... | no ¬p =
  var-τ-subst
    (trans
      (sym (+-assoc τ'' τ' (suc τ ∸ τ'') ))
      (trans
        (cong (_+ (suc τ ∸ τ'')) (+-comm τ'' τ'))
        (trans
          (+-assoc τ' τ'' (suc τ ∸ τ''))
          (cong (τ' +_)
            (trans
              (sym (+-∸-assoc τ'' (≰⇒≥ ¬p)))
              (trans
                (cong (_∸ τ'') (+-comm τ'' (suc τ)))
                (m+n∸n≡m (suc τ) τ'')))))))
    (Tl-⟨⟩ {τ = τ''} (var-ᶜ-+ {Γ} {A} {suc τ ∸ τ''} {τ'} x))

-- Weakening renaming for the time-travelling operation on contexts

-ᶜ-wk-vren : ∀ {Γ} → (τ : Time) → VRen (Γ -ᶜ τ) Γ
-ᶜ-wk-vren {Γ} zero {A} {τ'} x =
  τ' , ≤-refl , x
-ᶜ-wk-vren {Γ ∷ B} (suc τ) {A} {τ'} x with -ᶜ-wk-vren {Γ} (suc τ) x
... | τ'' , p , y =
  τ'' , p , Tl-∷ y
-ᶜ-wk-vren {Γ ⟨ τ'' ⟩} (suc τ) {A} {τ'} x with suc τ ≤? τ''
-ᶜ-wk-vren {Γ ⟨ τ'' ⟩} (suc τ) {A} {.(τ'' ∸ suc τ + τ''')} (Tl-⟨⟩ {τ' = τ'''} x) | yes p =
  τ'' + τ''' , +-monoˡ-≤ τ''' (m∸n≤m τ'' (suc τ)) , Tl-⟨⟩ x
... | no ¬p with -ᶜ-wk-vren {Γ} (suc τ ∸ τ'') x
... | τ''' , r , y =
  τ'' + τ''' , m≤n⇒m≤o+n τ'' r , Tl-⟨⟩ y

-- Parametric right adjoint (PRA) situation between (-) -ᶜ τ and ⟨ τ ⟩

pra-⟨⟩-vren : ∀ {Γ Γ' τ} → VRen (Γ ⟨ τ ⟩) Γ' → VRen Γ (Γ' -ᶜ τ)
pra-⟨⟩-vren {Γ} {Γ'} {τ} ρ {A} {τ'} x with ρ (Tl-⟨⟩ x)
... | τ'' , p , y =
  τ'' ∸ τ ,
  n+m≤k⇒m≤k∸n τ τ' τ'' p ,
  var-ᶜ {Γ'} {A} {τ} {τ''} (m+n≤o⇒m≤o τ p) y

pra-⟨⟩-vren⁻¹ : ∀ {Γ Γ' τ} → τ ≤ ctx-time Γ' → VRen Γ (Γ' -ᶜ τ) → VRen (Γ ⟨ τ ⟩) Γ'
pra-⟨⟩-vren⁻¹ {Γ} {Γ'} {τ} p ρ {A} {.(τ + τ')} (Tl-⟨⟩ {τ' = τ'} x) with ρ x
... | τ'' , q , y =
  τ'' + τ ,
  ≤-trans
    (≤-reflexive (+-comm τ τ'))
    (+-monoˡ-≤ τ q) ,
  var-ᶜ-+ {Γ'} {A} {τ} y

-- Time-travelling operation on renamings
   
_-ᵛʳ_ : ∀ {Γ Γ'} → VRen Γ Γ' → (τ : Time) → VRen (Γ -ᶜ τ) (Γ' -ᶜ τ)
(ρ -ᵛʳ zero) x =
  ρ x
_-ᵛʳ_ {Γ ∷ A} {Γ'} ρ (suc τ) x =
  _-ᵛʳ_ {Γ} {Γ'} (ρ ∘ᵛʳ wk-vren) (suc τ) x 
_-ᵛʳ_ {Γ ⟨ τ' ⟩} {Γ'} ρ (suc τ) x with suc τ ≤? τ'
_-ᵛʳ_ {Γ ⟨ τ' ⟩} {Γ'} ρ (suc τ) (Tl-⟨⟩ x) | yes p with ρ (Tl-⟨⟩ x)
... | τ' , q , y =
  τ' ∸ suc τ ,
  ≤-trans
    (≤-reflexive (sym (+-∸-comm _ p)))
    (∸-monoˡ-≤ (suc τ) q) ,
  var-ᶜ {τ = suc τ} (≤-trans p (≤-trans (m≤m+n _ _) q)) y
_-ᵛʳ_ {Γ ⟨ τ' ⟩} {Γ'} ρ (suc τ) {A} {τ''} x | no ¬p with (_-ᵛʳ_ {Γ} {Γ' -ᶜ τ'} (pra-⟨⟩-vren ρ) (suc τ ∸ τ')) x
... | τ''' , q , y =
  τ''' ,
  q ,
  subst (λ Γ → A ∈[ τ''' ] Γ)
    (trans
      (sym (++ᶜ-ᶜ-+ {Γ'} {τ'} {suc τ ∸ τ'}))
      (cong (Γ' -ᶜ_) {x = τ' + (suc τ ∸ τ')} {y = suc τ} (m+[n∸m]≡n {τ'} {suc τ} (≰⇒≥ ¬p))))
    y

infixl 30 _-ᵛʳ_

-- Extending a renaming with a variable

extend-vren : ∀ {Γ Γ' A τ} → VRen Γ Γ' → A ∈[ τ ] Γ' → VRen (Γ ∷ A) Γ'
extend-vren ρ x =
  var-vren x ∘ᵛʳ cong-∷-vren ρ

-- Congruence of renamings

cong-vren : ∀ {Γ Γ' Γ''} → VRen Γ Γ' → VRen (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-vren {Γ'' = []} ρ =
  ρ
cong-vren {Γ'' = Γ'' ∷ A} ρ =
  cong-∷-vren (cong-vren ρ)
cong-vren {Γ'' = Γ'' ⟨ τ ⟩} ρ =
  cong-⟨⟩-vren (cong-vren ρ)

-- Weakening by a context renaming

wk-ctx-vren : ∀ {Γ Γ'} → VRen Γ (Γ ++ᶜ Γ')
wk-ctx-vren {Γ' = []} =
  id-vren
wk-ctx-vren {Γ' = Γ' ∷ A} =
  wk-vren ∘ᵛʳ wk-ctx-vren
wk-ctx-vren {Γ' = Γ' ⟨ τ ⟩} =
  wk-⟨⟩-vren ∘ᵛʳ wk-ctx-vren

-- Exchange renamings

exch-vren : ∀ {Γ A B} → VRen (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-vren = extend-vren (extend-vren wk-ctx-vren Hd) (Tl-∷ Hd)

exch-⟨⟩-var-vren : ∀ {Γ A τ} → VRen (Γ ⟨ τ ⟩ ∷ A) ((Γ ∷ A) ⟨ τ ⟩)
exch-⟨⟩-var-vren {A = A} {τ = τ} =
      var-vren (Tl-⟨⟩ Hd)
  ∘ᵛʳ cong-vren {Γ'' = [] ⟨ _ ⟩ ∷ _} wk-vren

-- Contraction renaming

contract-vren : ∀ {Γ A} → VRen (Γ ∷ A ∷ A) (Γ ∷ A)
contract-vren = var-vren Hd

-- VRenaming from an equality of contexts

eq-vren : ∀ {Γ Γ'} → Γ ≡ Γ' → VRen Γ Γ'
eq-vren refl = id-vren

-- VRenaming from an empty context 

empty-vren : ∀ {Γ} → VRen [] Γ 
empty-vren {[]} =
  id-vren
empty-vren {Γ ∷ A} =
  wk-vren ∘ᵛʳ empty-vren
empty-vren {Γ ⟨ τ ⟩} =
  wk-⟨⟩-vren ∘ᵛʳ empty-vren

-- Interaction of var-split and wk-ctx-renᵣ

var-split₁-wk-ctx-vren : ∀ {Γ Γ' A τ}
                       → (x : A ∈[ τ ] Γ)
                       → proj₁ (var-split x)
                       ≡ proj₁ (var-split
                           (proj₂ (proj₂ (wk-ctx-vren {Γ' = Γ'} x))))

var-split₁-wk-ctx-vren {Γ' = []} x =
  refl
var-split₁-wk-ctx-vren {Γ' = Γ' ∷ A} x =
  var-split₁-wk-ctx-vren {Γ' = Γ'} x
var-split₁-wk-ctx-vren {Γ' = Γ' ⟨ τ ⟩} x =
  var-split₁-wk-ctx-vren {Γ' = Γ'} x

var-split₂-wk-ctx-vren : ∀ {Γ Γ' A τ}
                       → (x : A ∈[ τ ] Γ)
                       → proj₁ (proj₂ (var-split x)) ++ᶜ Γ'
                       ≡ proj₁ (proj₂ (var-split
                           (proj₂ (proj₂ (wk-ctx-vren {Γ' = Γ'} x)))))
                          
var-split₂-wk-ctx-vren {Γ' = []} x =
  refl
var-split₂-wk-ctx-vren {Γ' = Γ' ∷ A} x =
  cong (_∷ A) (var-split₂-wk-ctx-vren x)
var-split₂-wk-ctx-vren {Γ' = Γ' ⟨ τ ⟩} x =
  cong (_⟨ τ ⟩) (var-split₂-wk-ctx-vren x)

-- Rename a time modality to a context capturing at least the same amount of time

vren⟨τ⟩-ctx : ∀ {Γ Γ' τ} → τ ≤ ctx-time Γ' → VRen (Γ ⟨ τ ⟩) (Γ ++ᶜ Γ')
vren⟨τ⟩-ctx {Γ} {Γ'} {τ} p =
  pra-⟨⟩-vren⁻¹ {Γ} {Γ ++ᶜ Γ'}
    (≤-trans
      (m≤n⇒m≤o+n (ctx-time Γ) p)
      (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ'))))
    (    eq-vren (++ᶜ-ᶜ {Γ} {Γ'} p)
     ∘ᵛʳ wk-ctx-vren)

-- Identity laws

∘ᵛʳ-identityˡ : ∀ {Γ Γ' A τ}
              → (ρ : VRen Γ Γ')
              → (x : A ∈[ τ ] Γ)
              → (id-vren ∘ᵛʳ ρ) x ≡ ρ x

∘ᵛʳ-identityˡ {Γ} {Γ'} {A} {τ} ρ x =
  dcong₂ _,_ refl (cong₂ _,_ (≤-irrelevant _ _) refl)

∘ᵛʳ-identityʳ : ∀ {Γ Γ' A τ}
              → (ρ : VRen Γ Γ')
              → (x : A ∈[ τ ] Γ)
              → (ρ ∘ᵛʳ id-vren) x ≡ ρ x

∘ᵛʳ-identityʳ {Γ} {Γ'} {A} {τ} ρ x =
  dcong₂ _,_ refl (cong₂ _,_ (≤-irrelevant _ _) refl)

-- Relating congruence renamings with identity renamings (functoriality)

cong-∷-vren-id : ∀ {Γ A B τ}
               → (x : A ∈[ τ ] Γ ∷ B)
               → cong-∷-vren id-vren x ≡ id-vren x

cong-∷-vren-id {Γ} {A} {.A} {.0} Hd = refl
cong-∷-vren-id {Γ} {A} {B} {τ} (Tl-∷ x) with id-vren x
... | τ' , p , y = refl

cong-⟨⟩-vren-id : ∀ {Γ A τ τ'}
                → (x : A ∈[ τ ] Γ ⟨ τ' ⟩)
                → cong-⟨⟩-vren id-vren x ≡ id-vren x

cong-⟨⟩-vren-id {Γ} {A} {.(τ' + _)} {τ'} (Tl-⟨⟩ x) with id-vren x
... | τ'' , p , y =
  dcong₂ _,_ refl (cong₂ _,_ (≤-irrelevant _ _) refl)

cong-vren-id : ∀ {Γ Γ' A τ}
             → (x : A ∈[ τ ] Γ ++ᶜ Γ')
             → cong-vren {Γ'' = Γ'} id-vren x ≡ id-vren x

cong-vren-id {Γ} {[]} {A} {τ} x = refl
cong-vren-id {Γ} {Γ' ∷ B} {A} {τ} x =
  trans
    (cong
      (λ (ρ : VRen (Γ ++ᶜ Γ') (Γ ++ᶜ Γ')) → cong-∷-vren ρ x)
      (ifun-ext (λ {A} → ifun-ext (λ {τ} → fun-ext (λ y →
        cong-vren-id {Γ = Γ} {Γ' = Γ'} y)))))
    (cong-∷-vren-id x)
cong-vren-id {Γ} {Γ' ⟨ τ' ⟩} {A} {τ} x =
  trans
    (cong (λ (ρ : VRen (Γ ++ᶜ Γ') (Γ ++ᶜ Γ')) → cong-⟨⟩-vren ρ x)
      (ifun-ext (λ {A} → ifun-ext (λ {τ} → fun-ext (λ y →
        cong-vren-id {Γ = Γ} {Γ' = Γ'} y)))))
    (cong-⟨⟩-vren-id x)

-- Relating congruence renamings with composition of renamings (functoriality)

cong-∷-vren-fun : ∀ {Γ Γ' Γ'' A B τ}
                → (ρ : VRen Γ Γ')
                → (ρ' : VRen Γ' Γ'')
                → (x : A ∈[ τ ] (Γ ∷ B))
                → cong-∷-vren {A = B} (ρ' ∘ᵛʳ ρ) x
                ≡ (cong-∷-vren ρ' ∘ᵛʳ cong-∷-vren ρ) x
               
cong-∷-vren-fun ρ ρ' Hd =
  refl
cong-∷-vren-fun ρ ρ' (Tl-∷ x) =
  refl

cong-⟨⟩-vren-fun : ∀ {Γ Γ' Γ'' A τ τ'}
                → (ρ : VRen Γ Γ')
                → (ρ' : VRen Γ' Γ'')
                → (x : A ∈[ τ ] (Γ ⟨ τ' ⟩))
                → cong-⟨⟩-vren (ρ' ∘ᵛʳ ρ) x
                ≡ (cong-⟨⟩-vren ρ' ∘ᵛʳ cong-⟨⟩-vren ρ) x
                
cong-⟨⟩-vren-fun ρ ρ' (Tl-⟨⟩ x) with ρ x
... | τ'' , p , y =
  cong (_ ,_) (cong (_, Tl-⟨⟩ (proj₂ (proj₂ (ρ' y)))) (≤-irrelevant _ _))

cong-vren-fun : ∀ {Γ Γ' Γ'' Γ''' A τ}
            → (ρ : VRen Γ Γ')
            → (ρ' : VRen Γ' Γ'')
            → (x : A ∈[ τ ] (Γ ++ᶜ Γ'''))
            → cong-vren (ρ' ∘ᵛʳ ρ) x
            ≡ (cong-vren ρ' ∘ᵛʳ cong-vren ρ) x

cong-vren-fun {Γ} {Γ'} {Γ''} {Γ''' = []} ρ ρ' x =
  refl
cong-vren-fun {Γ} {Γ'} {Γ''} {Γ''' ∷ A} ρ ρ' x =
  trans
    (cong
      (λ (ρ : VRen (Γ ++ᶜ Γ''') (Γ'' ++ᶜ Γ''')) → cong-∷-vren ρ x)
      (ifun-ext λ {A} → ifun-ext (λ {τ} → fun-ext (λ x → cong-vren-fun ρ ρ' x))))
    (cong-∷-vren-fun (cong-vren ρ) (cong-vren ρ') x)
cong-vren-fun {Γ} {Γ'} {Γ''} {Γ''' ⟨ τ ⟩} ρ ρ' x =
  trans
    (cong
      (λ (ρ : VRen (Γ ++ᶜ Γ''') (Γ'' ++ᶜ Γ''')) → cong-⟨⟩-vren ρ x)
      (ifun-ext λ {A} → ifun-ext (λ {τ} → fun-ext (λ x → cong-vren-fun ρ ρ' x))))
    (cong-⟨⟩-vren-fun (cong-vren ρ) (cong-vren ρ') x)
