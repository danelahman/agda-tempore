-- {-# OPTIONS --allow-unsolved-metas #-} -- (remove)

--------------------------------------------------------------
-- Context renamings                                        --
--                                                          --
-- Note: These are raw (underlying) renamings that are      --
-- further refined in Syntax.Renamings to respect ctx-grade --
--------------------------------------------------------------

open import Syntax.Grades

module Syntax.Renamings.Raw (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Syntax.Contexts (Grades)
open import Syntax.Types (Grades)

open import Util.Equality

open import Relation.Binary.PropositionalEquality as Eq hiding ( [_] ) 

-- Subst for grade annotations of variables (for convenience)

var-ρ-subst : ∀ {Γ A ρ ρ'} → ρ ≡ ρ' → A ∈[ ρ ] Γ → A ∈[ ρ' ] Γ
var-ρ-subst refl x = x

-- Variable renamings (an extra condition on ctx-grade will be imposed later)

VRen : Ctx → Ctx → Set
VRen Γ Γ' = ∀ {A ρ} → A ∈[ ρ ] Γ → Σ[ ρ' ∈ R ] (ρ' ≾ᵣ ρ × A ∈[ ρ' ] Γ')

-- Identity renaming

id-vren : ∀ {Γ} → VRen Γ Γ
id-vren {ρ = ρ} x = ρ , ≾ᵣ-refl , x

-- VRenaming from an equality of contexts

eq-vren : ∀ {Γ Γ'} → Γ ≡ Γ' → VRen Γ Γ'
eq-vren refl = id-vren

-- Composition of renamings

_∘ᵛʳ_ : ∀ {Γ Γ' Γ''} → VRen Γ' Γ'' → VRen Γ Γ' → VRen Γ Γ''
_∘ᵛʳ_ r' r x with r x
... | ρ' , rel' , y with r' y
... | ρ'' , rel , z = ρ'' , ≾ᵣ-trans rel rel' , z

infixr 20 _∘ᵛʳ_

-- Weakening renaming

wk-vren : ∀ {Γ A} → VRen Γ (Γ ∷ A)
wk-vren {ρ = ρ} x = ρ , ≾ᵣ-refl , Tl-∷ x

-- Variable renaming

var-vren : ∀ {Γ A} → A ∈[ uᵣ ] Γ → VRen (Γ ∷ A) Γ
var-vren x Hd =
  uᵣ , ≾ᵣ-refl , x
var-vren x (Tl-∷ {ρ = ρ'} y) =
  ρ' , ≾ᵣ-refl , y

-- Strong monoidal functor renamings

⟨⟩-η-vren : ∀ {Γ} → VRen (Γ ⟨ uᵣ ⟩) Γ
⟨⟩-η-vren (Tl-⟨⟩ {ρ' = ρ} x) = ρ , ≾ᵣ-reflexive (sym (·ᵣ-identityʳ ρ)) , x

⟨⟩-η⁻¹-vren : ∀ {Γ} → VRen Γ (Γ ⟨ uᵣ ⟩)
⟨⟩-η⁻¹-vren {Γ} {A} {ρ} x = ρ ·ᵣ uᵣ , ≾ᵣ-reflexive (·ᵣ-identityʳ ρ) , Tl-⟨⟩ x

⟨⟩-μ-vren : ∀ {Γ ρ ρ'} → VRen (Γ ⟨ ρ ·ᵣ ρ' ⟩) (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩)
⟨⟩-μ-vren {Γ} {ρ} {ρ'} {A} {.(ρ'' ·ᵣ (ρ ·ᵣ ρ'))} (Tl-⟨⟩ {ρ' = ρ''} x) =
  ρ'' ·ᵣ ρ ·ᵣ ρ' , ≾ᵣ-reflexive (·ᵣ-assoc ρ'' ρ ρ') , Tl-⟨⟩ (Tl-⟨⟩ x)

⟨⟩-μ⁻¹-vren : ∀ {Γ ρ ρ'} → VRen (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩) (Γ ⟨ ρ ·ᵣ ρ' ⟩)
⟨⟩-μ⁻¹-vren {Γ} {ρ} {ρ'} {A} {.(_ ·ᵣ ρ ·ᵣ ρ')} (Tl-⟨⟩ (Tl-⟨⟩ {ρ' = ρ''} x)) =
  ρ'' ·ᵣ (ρ ·ᵣ ρ') , ≾ᵣ-reflexive (sym (·ᵣ-assoc ρ'' ρ ρ')) , Tl-⟨⟩ x

⟨⟩-≾-vren : ∀ {Γ ρ ρ'} → ρ' ≾ᵣ ρ → VRen (Γ ⟨ ρ ⟩) (Γ ⟨ ρ' ⟩)
⟨⟩-≾-vren {Γ} {ρ} {ρ'} rel {A} {.(_ ·ᵣ ρ)} (Tl-⟨⟩ {ρ' = ρ''} x) =
  ρ'' ·ᵣ ρ' , ·ᵣ-monoʳ-≾ᵣ rel , Tl-⟨⟩ x

-- Congruence renamings

cong-∷-vren : ∀ {Γ Γ' A} → VRen Γ Γ' → VRen (Γ ∷ A) (Γ' ∷ A)
cong-∷-vren _ Hd = uᵣ , ≾ᵣ-refl , Hd
cong-∷-vren vr (Tl-∷ x) with vr x
... | ρ' , rel , y = ρ' , rel , Tl-∷ y

cong-⟨⟩-vren : ∀ {Γ Γ' ρ} → VRen Γ Γ' → VRen (Γ ⟨ ρ ⟩) (Γ' ⟨ ρ ⟩)
cong-⟨⟩-vren {Γ} {Γ'} {ρ} vr {A} {.(ρ' ·ᵣ ρ)} (Tl-⟨⟩ {ρ' = ρ'} x) with vr x
... | ρ'' , rel , y = ρ'' ·ᵣ ρ , ·ᵣ-monoˡ-≾ᵣ rel , Tl-⟨⟩ y

-- Extending a renaming with a variable

extend-vren : ∀ {Γ Γ' A} → VRen Γ Γ' → A ∈[ uᵣ ] Γ' → VRen (Γ ∷ A) Γ'
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

wk-ctx-vren : ∀ {Γ Γ'} → ctx-grade Γ' ≡ uᵣ → VRen Γ (Γ ++ᶜ Γ')
wk-ctx-vren {Γ' = []}      _   = id-vren
wk-ctx-vren {Γ' = Γ' ∷ A}  rel = wk-vren ∘ᵛʳ wk-ctx-vren rel
wk-ctx-vren {Γ} {Γ' ⟨ ρ ⟩} rel rewrite c·ᵣd≡uᵣ⇒d≡uᵣ rel =
  ⟨⟩-η⁻¹-vren ∘ᵛʳ (wk-ctx-vren {Γ} {Γ'} (c·ᵣd≡uᵣ⇒c≡uᵣ rel))

-- Exchange renamings

exch-vren : ∀ {Γ A B} → VRen (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-vren = extend-vren (extend-vren (wk-ctx-vren refl) Hd) (Tl-∷ Hd)

-- Contraction renaming

contract-vren : ∀ {Γ A} → VRen (Γ ∷ A ∷ A) (Γ ∷ A)
contract-vren = var-vren Hd

-- Interaction of var-split and wk-ctx-renᵣ

var-split₁-wk-ctx-vren : ∀ {Γ Γ' A ρ}
                       → (x : A ∈[ ρ ] Γ)
                       → (rel : ctx-grade Γ' ≡ uᵣ)
                       → proj₁ (var-split x)
                       ≡ proj₁ (var-split
                           (proj₂ (proj₂ (wk-ctx-vren {Γ' = Γ'} rel x))))

var-split₁-wk-ctx-vren {Γ' = []} x rel =
  refl
var-split₁-wk-ctx-vren {Γ' = Γ' ∷ A} x rel =
  var-split₁-wk-ctx-vren {Γ' = Γ'} x rel
var-split₁-wk-ctx-vren {Γ} {Γ' ⟨ ρ' ⟩} {A} {ρ} x rel with c·ᵣd≡uᵣ⇒d≡uᵣ rel
... | refl = var-split₁-wk-ctx-vren {Γ' = Γ'} x (c·ᵣd≡uᵣ⇒c≡uᵣ rel)

var-split₂-wk-ctx-vren : ∀ {Γ Γ' A ρ}
                       → (x : A ∈[ ρ ] Γ)
                       → (rel : ctx-grade Γ' ≡ uᵣ)
                       → proj₁ (proj₂ (var-split x)) ++ᶜ Γ'
                       ≡ proj₁ (proj₂ (var-split
                           (proj₂ (proj₂ (wk-ctx-vren {Γ' = Γ'} rel x )))))
                          
var-split₂-wk-ctx-vren {Γ' = []} x rel =
  refl
var-split₂-wk-ctx-vren {Γ' = Γ' ∷ A} x rel =
  cong (_∷ A) (var-split₂-wk-ctx-vren x rel)
var-split₂-wk-ctx-vren {Γ' = Γ' ⟨ ρ' ⟩} x rel with c·ᵣd≡uᵣ⇒d≡uᵣ rel
... | refl = cong (_⟨ ρ' ⟩) (var-split₂-wk-ctx-vren {Γ' = Γ'} x (c·ᵣd≡uᵣ⇒c≡uᵣ rel))

-- Rename a grade modality to a context capturing at least the same amount of time

vren⟨ρ⟩-ctx : ∀ {Γ Γ' ρ} → ctx-grade Γ' ≾ᵣ ρ → VRen (Γ ⟨ ρ ⟩) (Γ ++ᶜ Γ')
vren⟨ρ⟩-ctx {Γ' = []} rel (Tl-⟨⟩ {ρ' = ρ'} y) =
  ρ' , ≾ᵣ-trans (≾ᵣ-reflexive (sym (·ᵣ-identityʳ ρ'))) (·ᵣ-monoʳ-≾ᵣ rel) , y
vren⟨ρ⟩-ctx {Γ' = Γ' ∷ A} rel (Tl-⟨⟩ {ρ' = ρ'} y) =
  ρ' ·ᵣ (ctx-grade Γ') , ·ᵣ-monoʳ-≾ᵣ rel , Tl-∷ (var-ρ-++ᶜ y)
vren⟨ρ⟩-ctx {Γ' = Γ' ⟨ ρ' ⟩} rel (Tl-⟨⟩ {ρ' = ρ''} y) =
  ρ'' ·ᵣ ctx-grade Γ' ·ᵣ ρ' ,
  ≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-assoc ρ'' (ctx-grade Γ') ρ')) (·ᵣ-monoʳ-≾ᵣ rel) ,
  Tl-⟨⟩ (var-ρ-++ᶜ y)

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
... | ρ'' , r , y = dcong₂ _,_ refl ((cong₂ _,_ (≾ᵣ-irrelevant _ _) refl))

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

cong-∷-vren-fun r r' Hd       = dcong₂ _,_ refl (cong₂ _,_ (≾ᵣ-irrelevant _ _) refl)
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

-- Interaction of context minus with context modalities

{-
-ᶜ-⟨⟩ : ∀ {Γ Γ' A ρ ρ'}
      → Γ -ᶜ ρ ≈ Γ'
      → A ∈[ ρ' ] Γ'
      → A ∈[ ρ' ·ᵣ ρ ] Γ

-ᶜ-⟨⟩ {ρ = ρ} {ρ' = ρ'} -ᶜ-uᵣ x
  rewrite ·ᵣ-identityʳ ρ' =
    x
-ᶜ-⟨⟩ (-ᶜ-∷ p q) x =
  Tl-∷ (-ᶜ-⟨⟩ q x)
-ᶜ-⟨⟩ (-ᶜ-⟨⟩-lt p q) x = {!!}
-ᶜ-⟨⟩ {ρ = ρ} {ρ' = ρ'} (-ᶜ-⟨⟩-gt {ρ = ρ''} {ρ'' = ρ'''} p q r) x = {!!}
--rewrite q | sym (·ᵣ-assoc ρ' ρ'' ρ''') =
--  {!-ᶜ-⟨⟩ r x!} -- TODO: either need commutativity, or some kind of braiding on ρs
-}

--

var-ᶜ : ∀ {Γ Γ' A ρ ρ' ρ''}
      → Γ -ᶜ ρ' ≈ Γ'
      → ρ ≡ ρ'' ·ᵣ ρ'
      → A ∈[ ρ ] Γ
      → A ∈[ ρ'' ] Γ'

var-ᶜ {ρ = ρ} {ρ' = ρ'} {ρ'' = ρ''} (-ᶜ-uᵣ refl) q x
  rewrite ·ᵣ-identityʳ ρ'' | q = x
var-ᶜ (-ᶜ-∷ p q) r Hd =
  ⊥-elim (p (c·ᵣd≡uᵣ⇒d≡uᵣ (sym r)))
var-ᶜ (-ᶜ-∷ p q) r (Tl-∷ x) =
  var-ᶜ q r x
var-ᶜ {Γ} {Γ'} {A} (-ᶜ-⟨⟩-lt {ρ'' = ρ''} p q) r (Tl-⟨⟩ x) = {!!}
var-ᶜ (-ᶜ-⟨⟩-gt p q r) s (Tl-⟨⟩ x) rewrite q =
  var-ᶜ r (trans (sym (·ᵣ-identityʳ _)) (·ᵣ-≡-cancellative (trans (·ᵣ-identityʳ _) (trans s (sym (·ᵣ-assoc _ _ _)))))) x

-- Action of context minus on renamings

vren-ᶜ : ∀ {Γ Γ' Γ'' Γ''' ρ}
       → VRen Γ Γ'
       → Γ -ᶜ ρ ≈ Γ''
       → Γ' -ᶜ ρ ≈ Γ'''
       → VRen Γ'' Γ'''

vren-ᶜ r (-ᶜ-uᵣ refl) q rewrite -ᶜ-u q =
  r
  
vren-ᶜ r (-ᶜ-∷ p q) s =
  vren-ᶜ (r ∘ᵛʳ wk-vren) q s

vren-ᶜ {ρ = ρ} r (-ᶜ-⟨⟩-lt {ρ = ρ'} {ρ'' = ρ''} p q) s (Tl-⟨⟩ x) with r (Tl-⟨⟩ x)
... | ρ''' , t , y = {!!} , {!!} , {!!}

vren-ᶜ {ρ = ρ} r (-ᶜ-⟨⟩-gt {ρ = ρ'} {ρ'' = ρ''} p q s) t = {!!}
