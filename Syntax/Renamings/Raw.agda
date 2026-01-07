-- {-# OPTIONS --allow-unsolved-metas #-} -- (remove)

--------------------------------------------------------------
-- Context renamings and their action on well-typed terms   --
--                                                          --
-- Note: These are raw (underlying) renamings that are      --
-- further refined in Syntax.Renamings to respect ctx-grade --
--------------------------------------------------------------

open import Syntax.Grades

module Syntax.Renamings.Raw (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Relation.Nullary

open import Syntax.Contexts (Grades)
open import Syntax.Types (Grades)

open import Util.Equality

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 

-- Subst for grade annotations of variables (for convenience)

var-ρ-subst : ∀ {Γ A ρ ρ'} → ρ ≡ ρ' → A ∈[ ρ ] Γ → A ∈[ ρ' ] Γ
var-ρ-subst refl x = x

-- Variable renamings (an extra condition on ctx-grade will be imposed later)

VRen : Ctx → Ctx → Set
VRen Γ Γ' = ∀ {A ρ} → A ∈[ ρ ] Γ → Σ[ ρ' ∈ R ] (ρ ≾ᵣ ρ' × A ∈[ ρ' ] Γ')

-- Identity renaming
id-vren : ∀ {Γ} → VRen Γ Γ
id-vren {Γ} {A} {ρ} x = ρ , ≾ᵣ-refl , x

-- Composition of renamings

_∘ᵛʳ_ : ∀ {Γ Γ' Γ''} → VRen Γ' Γ'' → VRen Γ Γ' → VRen Γ Γ''
_∘ᵛʳ_ r' r x with r x
... | ρ' , rel' , y with r' y
... | ρ'' , rel , z = ρ'' , ≾ᵣ-trans rel' rel , z

infixr 20 _∘ᵛʳ_

-- Weakening renaming

wk-vren : ∀ {Γ A} → VRen Γ (Γ ∷ A)
wk-vren {Γ} {A} {B} {ρ} x = ρ , ≾ᵣ-refl , Tl-∷ x

-- Variable renaming

var-vren : ∀ {Γ A ρ} → A ∈[ ρ ] Γ → VRen (Γ ∷ A) Γ
var-vren {Γ} {A} {ρ} x Hd =
  ρ , uᵣ≾ᵣc , x
var-vren {Γ} {A} {ρ} x (Tl-∷ {ρ = ρ'} y) =
  ρ' , ≾ᵣ-refl , y

-- Strong monoidal functor renamings

⟨⟩-η-vren : ∀ {Γ} → VRen (Γ ⟨ uᵣ ⟩) Γ
⟨⟩-η-vren {Γ} (Tl-⟨⟩ {ρ' = ρ} x) = ρ , ≾ᵣ-reflexive (·ᵣ-identityʳ ρ) , x

⟨⟩-η⁻¹-vren : ∀ {Γ} → VRen Γ (Γ ⟨ uᵣ ⟩)
⟨⟩-η⁻¹-vren {Γ} {A} {ρ} x = ρ ·ᵣ uᵣ , ≾ᵣ-reflexive (sym (·ᵣ-identityʳ ρ)) , Tl-⟨⟩ x

⟨⟩-μ-vren : ∀ {Γ ρ ρ'} → VRen (Γ ⟨ ρ ·ᵣ ρ' ⟩) (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩)
⟨⟩-μ-vren {Γ} {ρ} {ρ'} {A} {.(ρ'' ·ᵣ (ρ ·ᵣ ρ'))} (Tl-⟨⟩ {ρ' = ρ''} x) =
  ρ'' ·ᵣ ρ ·ᵣ ρ' , ≾ᵣ-reflexive (sym (·ᵣ-assoc ρ'' ρ ρ')) , Tl-⟨⟩ (Tl-⟨⟩ x)

⟨⟩-μ⁻¹-vren : ∀ {Γ ρ ρ'} → VRen (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩) (Γ ⟨ ρ ·ᵣ ρ' ⟩)
⟨⟩-μ⁻¹-vren {Γ} {ρ} {ρ'} {A} {.(_ ·ᵣ ρ ·ᵣ ρ')} (Tl-⟨⟩ (Tl-⟨⟩ {ρ' = ρ''} x)) =
  ρ'' ·ᵣ (ρ ·ᵣ ρ') , ≾ᵣ-reflexive (·ᵣ-assoc ρ'' ρ ρ') , Tl-⟨⟩ x

⟨⟩-≾-vren : ∀ {Γ ρ ρ'} → ρ ≾ᵣ ρ' → VRen (Γ ⟨ ρ ⟩) (Γ ⟨ ρ' ⟩)
⟨⟩-≾-vren {Γ} {ρ} {ρ'} rel {A} {.(_ ·ᵣ ρ)} (Tl-⟨⟩ {ρ' = ρ''} x) =
  ρ'' ·ᵣ ρ' , ·ᵣ-monoʳ-≾ᵣ ρ'' rel , Tl-⟨⟩ x

-- Derived modal weakening renaming

wk-⟨⟩-vren : ∀ {Γ ρ} → VRen Γ (Γ ⟨ ρ ⟩)
wk-⟨⟩-vren {Γ} {ρ} = ⟨⟩-≾-vren uᵣ≾ᵣc ∘ᵛʳ ⟨⟩-η⁻¹-vren

-- Congruence renamings

cong-∷-vren : ∀ {Γ Γ' A} → VRen Γ Γ' → VRen (Γ ∷ A) (Γ' ∷ A)
cong-∷-vren {Γ} {Γ'} {A} r {B} {ρ} Hd        = uᵣ , ≾ᵣ-refl , Hd
cong-∷-vren {Γ} {Γ'} {A} r {B} {ρ} (Tl-∷ x) with r x
...| ρ' , rel , y = ρ' , rel , Tl-∷ y

cong-⟨⟩-vren : ∀ {Γ Γ' ρ} → VRen Γ Γ' → VRen (Γ ⟨ ρ ⟩) (Γ' ⟨ ρ ⟩)
cong-⟨⟩-vren {Γ} {Γ'} {ρ} r {A} {.(ρ' ·ᵣ ρ)} (Tl-⟨⟩ {ρ' = ρ'} x) with r x
... | ρ'' , r , y = ρ'' ·ᵣ ρ , ·ᵣ-monoˡ-≾ᵣ ρ r , Tl-⟨⟩ y

-- REMOVE
{-
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
-}

-- Overapproximations (former property involving the minus operation on contexts)

pra-⟨⟩-vren : ∀ {Γ Γ' ρ} → VRen (Γ ⟨ ρ ⟩) Γ' → VRen Γ Γ'
pra-⟨⟩-vren {Γ} {Γ'} {ρ} r {A} {ρ'} x  with r (Tl-⟨⟩ x)
... | ρ'' , rel , y = ρ'' , ≾ᵣ-trans (c≾ᵣc·ᵣd ρ' ρ) rel , y

{- This doesn't hold in the general case without the minus.
pra-⟨⟩-vren⁻¹ : ∀ {Γ Γ' τ} → τ ≤ ctx-grade Γ' → VRen Γ (Γ' -ᶜ τ) → VRen (Γ ⟨ τ ⟩) Γ'
pra-⟨⟩-vren⁻¹ {Γ} {Γ'} {τ} p ρ {A} {.(τ + τ')} (Tl-⟨⟩ {τ' = τ'} x) with ρ x
... | τ'' , q , y =
  τ'' + τ ,
  ≤-trans
    (≤-reflexive (+-comm τ τ'))
    (+-monoˡ-≤ τ q) ,
  var-ᶜ-+ {Γ'} {A} {τ} y
-}

-- Extending a renaming with a variable

extend-vren : ∀ {Γ Γ' A ρ} → VRen Γ Γ' → A ∈[ ρ ] Γ' → VRen (Γ ∷ A) Γ'
extend-vren r x =
  var-vren x ∘ᵛʳ cong-∷-vren r

-- Congruence of renamings

cong-vren : ∀ {Γ Γ' Γ''} → VRen Γ Γ' → VRen (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-vren {Γ'' = []} r =
  r
cong-vren {Γ'' = Γ'' ∷ A} r =
  cong-∷-vren (cong-vren r)
cong-vren {Γ'' = Γ'' ⟨ ρ ⟩} r = 
  cong-⟨⟩-vren (cong-vren r)

-- Weakening by a context renaming

wk-ctx-vren : ∀ {Γ Γ'} → VRen Γ (Γ ++ᶜ Γ')
wk-ctx-vren {Γ' = []} =
  id-vren
wk-ctx-vren {Γ' = Γ' ∷ A} =
  wk-vren ∘ᵛʳ wk-ctx-vren
wk-ctx-vren {Γ' = Γ' ⟨ ρ ⟩} =
  wk-⟨⟩-vren ∘ᵛʳ wk-ctx-vren

-- Exchange renamings

exch-vren : ∀ {Γ A B} → VRen (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-vren = extend-vren (extend-vren wk-ctx-vren Hd) (Tl-∷ Hd)

exch-⟨⟩-var-vren : ∀ {Γ A ρ} → VRen (Γ ⟨ ρ ⟩ ∷ A) ((Γ ∷ A) ⟨ ρ ⟩)
exch-⟨⟩-var-vren {A = A} {ρ = ρ} =
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
empty-vren {Γ ⟨ ρ ⟩} =
  wk-⟨⟩-vren ∘ᵛʳ empty-vren

-- Interaction of var-split and wk-ctx-renᵣ

var-split₁-wk-ctx-vren : ∀ {Γ Γ' A ρ}
                       → (x : A ∈[ ρ ] Γ)
                       → proj₁ (var-split x)
                       ≡ proj₁ (var-split
                           (proj₂ (proj₂ (wk-ctx-vren {Γ' = Γ'} x))))

var-split₁-wk-ctx-vren {Γ' = []} x =
  refl
var-split₁-wk-ctx-vren {Γ' = Γ' ∷ A} x =
  var-split₁-wk-ctx-vren {Γ' = Γ'} x
var-split₁-wk-ctx-vren {Γ' = Γ' ⟨ ρ ⟩} x =
  var-split₁-wk-ctx-vren {Γ' = Γ'} x

var-split₂-wk-ctx-vren : ∀ {Γ Γ' A ρ}
                       → (x : A ∈[ ρ ] Γ)
                       → proj₁ (proj₂ (var-split x)) ++ᶜ Γ'
                       ≡ proj₁ (proj₂ (var-split
                           (proj₂ (proj₂ (wk-ctx-vren {Γ' = Γ'} x)))))
                          
var-split₂-wk-ctx-vren {Γ' = []} x =
  refl
var-split₂-wk-ctx-vren {Γ' = Γ' ∷ A} x =
  cong (_∷ A) (var-split₂-wk-ctx-vren x)
var-split₂-wk-ctx-vren {Γ' = Γ' ⟨ ρ ⟩} x =
  cong (_⟨ ρ ⟩) (var-split₂-wk-ctx-vren x)

{-
-- Rename a grade modality to a context capturing at least the same amount of time

vren⟨ρ⟩-ctx : ∀ {Γ Γ' ρ} → ρ ≾ᵣ ctx-grade Γ' → VRen (Γ ⟨ ρ ⟩) (Γ ++ᶜ Γ')
vren⟨ρ⟩-ctx {Γ} {Γ'} {ρ} r =
  pra-⟨⟩-vren⁻¹ {Γ} {Γ ++ᶜ Γ'}
    (≾ᵣ-trans
      (m≤n⇒m≤o+n (ctx-grade Γ) r)
      (≾ᵣ-reflexive (sym (ctx-grade-++ᶜ Γ Γ'))))
    (    eq-vren (++ᶜ-ᶜ {Γ} {Γ'} r)
     ∘ᵛʳ wk-ctx-vren)
-}

-- Identity laws

∘ᵛʳ-identityˡ : ∀ {Γ Γ' A ρ}
              → (r : VRen Γ Γ')
              → (x : A ∈[ ρ ] Γ)
              → (id-vren ∘ᵛʳ r) x ≡ r x

∘ᵛʳ-identityˡ {Γ} {Γ'} {A} {ρ} r x =
  dcong₂ _,_ refl (cong₂ _,_ (≾ᵣ-irrelevant _ _) refl)

∘ᵛʳ-identityʳ : ∀ {Γ Γ' A ρ}
              → (r : VRen Γ Γ')
              → (x : A ∈[ ρ ] Γ)
              → (r ∘ᵛʳ id-vren) x ≡ r x

∘ᵛʳ-identityʳ {Γ} {Γ'} {A} {ρ} r x =
  dcong₂ _,_ refl (cong₂ _,_ (≾ᵣ-irrelevant _ _) refl)

-- Relating congruence renamings with identity renamings (functoriality)

cong-∷-vren-id : ∀ {Γ A B ρ}
               → (x : A ∈[ ρ ] Γ ∷ B)
               → cong-∷-vren id-vren x ≡ id-vren x
cong-∷-vren-id Hd = refl
cong-∷-vren-id {Γ} {A} {B} {ρ} (Tl-∷ x) = refl

cong-⟨⟩-vren-id : ∀ {Γ A ρ ρ'}
                → (x : A ∈[ ρ ] Γ ⟨ ρ' ⟩)
                → cong-⟨⟩-vren id-vren x ≡ id-vren x

cong-⟨⟩-vren-id {Γ} {A} {.(_ ·ᵣ ρ)} {ρ} (Tl-⟨⟩ x) with id-vren x
... | ρ'' , r , y = dcong₂ _,_ refl (cong₂ _,_ (≾ᵣ-irrelevant (·ᵣ-monoˡ-≾ᵣ ρ ≾ᵣ-refl) ≾ᵣ-refl) refl)

cong-vren-id : ∀ {Γ Γ' A ρ}
             → (x : A ∈[ ρ ] Γ ++ᶜ Γ')
             → cong-vren {Γ'' = Γ'} id-vren x ≡ id-vren x

cong-vren-id {Γ} {[]} {A} {ρ} x = refl
cong-vren-id {Γ} {Γ' ∷ B} {A} {ρ} x =
  trans
    (cong
      (λ (r : VRen (Γ ++ᶜ Γ') (Γ ++ᶜ Γ')) → cong-∷-vren r x)
      (ifun-ext (λ {A} → ifun-ext (λ {ρ} → fun-ext (λ y →
        cong-vren-id {Γ = Γ} {Γ' = Γ'} y)))))
    (cong-∷-vren-id x)
cong-vren-id {Γ} {Γ' ⟨ ρ' ⟩} {A} {ρ} x =
  trans
    (cong (λ (r : VRen (Γ ++ᶜ Γ') (Γ ++ᶜ Γ')) → cong-⟨⟩-vren r x)
      (ifun-ext (λ {A} → ifun-ext (λ {ρ} → fun-ext (λ y →
        cong-vren-id {Γ = Γ} {Γ' = Γ'} y)))))
    (cong-⟨⟩-vren-id x)

-- Relating congruence renamings with composition of renamings (functoriality)

cong-∷-vren-fun : ∀ {Γ Γ' Γ'' A B ρ}
                → (r : VRen Γ Γ')
                → (r' : VRen Γ' Γ'')
                → (x : A ∈[ ρ ] (Γ ∷ B))
                → cong-∷-vren {A = B} (r' ∘ᵛʳ r) x
                ≡ (cong-∷-vren r' ∘ᵛʳ cong-∷-vren r) x
cong-∷-vren-fun r r' Hd =
  dcong₂ _,_ refl (cong₂ _,_ (≾ᵣ-irrelevant ≾ᵣ-refl (≾ᵣ-trans ≾ᵣ-refl ≾ᵣ-refl)) refl)
cong-∷-vren-fun r r' (Tl-∷ x) = refl

cong-⟨⟩-vren-fun : ∀ {Γ Γ' Γ'' A ρ ρ'}
                → (r : VRen Γ Γ')
                → (r' : VRen Γ' Γ'')
                → (x : A ∈[ ρ ] (Γ ⟨ ρ' ⟩))
                → cong-⟨⟩-vren (r' ∘ᵛʳ r) x
                ≡ (cong-⟨⟩-vren r' ∘ᵛʳ cong-⟨⟩-vren r) x
                
cong-⟨⟩-vren-fun r r' (Tl-⟨⟩ x) with r x
... | ρ'' , r , y = cong (_ ,_) (cong (_, Tl-⟨⟩ (proj₂ (proj₂ (r' y)))) (≾ᵣ-irrelevant _ _))

cong-vren-fun : ∀ {Γ Γ' Γ'' Γ''' A ρ}
            → (r : VRen Γ Γ')
            → (r' : VRen Γ' Γ'')
            → (x : A ∈[ ρ ] (Γ ++ᶜ Γ'''))
            → cong-vren (r' ∘ᵛʳ r) x
            ≡ (cong-vren r' ∘ᵛʳ cong-vren r) x

cong-vren-fun {Γ} {Γ'} {Γ''} {Γ''' = []} r r' x =
  refl
cong-vren-fun {Γ} {Γ'} {Γ''} {Γ''' ∷ A} r r' x =
  trans
    (cong
      (λ (r : VRen (Γ ++ᶜ Γ''') (Γ'' ++ᶜ Γ''')) → cong-∷-vren r x)
      (ifun-ext λ {A} → ifun-ext (λ {ρ} → fun-ext (λ x → cong-vren-fun r r' x))))
    (cong-∷-vren-fun (cong-vren r) (cong-vren r') x)
cong-vren-fun {Γ} {Γ'} {Γ''} {Γ''' ⟨ ρ ⟩} r r' x =
  trans
    (cong
      (λ (r : VRen (Γ ++ᶜ Γ''') (Γ'' ++ᶜ Γ''')) → cong-⟨⟩-vren r x)
      (ifun-ext λ {A} → ifun-ext (λ {ρ} → fun-ext (λ x → cong-vren-fun r r' x))))
    (cong-⟨⟩-vren-fun (cong-vren r) (cong-vren r') x)


