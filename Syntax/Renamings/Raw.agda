{-# OPTIONS --allow-unsolved-metas #-} -- (remove)

--------------------------------------------------------------
-- Context renamings                                        --
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

open import Relation.Binary.PropositionalEquality as Eq hiding ( [_] ) 

-- Subst for grade annotations of variables (for convenience)

var-ρ-subst : ∀ {Γ A ρ ρ'} → ρ ≡ ρ' → A ∈[ ρ ] Γ → A ∈[ ρ' ] Γ
var-ρ-subst refl x = x

-- Variable renamings (an extra condition on ctx-grade will be imposed later)

VRen : Ctx → Ctx → Set
VRen Γ Γ' = ∀ {A ρ} → A ∈[ ρ ] Γ → Σ[ ρ' ∈ R ] (ρ ≡ ρ' × A ∈[ ρ' ] Γ')

-- Identity renaming

id-vren : ∀ {Γ} → VRen Γ Γ
id-vren {ρ = ρ} x = ρ , refl , x

-- VRenaming from an equality of contexts

eq-vren : ∀ {Γ Γ'} → Γ ≡ Γ' → VRen Γ Γ'
eq-vren refl = id-vren

-- Composition of renamings

_∘ᵛʳ_ : ∀ {Γ Γ' Γ''} → VRen Γ' Γ'' → VRen Γ Γ' → VRen Γ Γ''
_∘ᵛʳ_ r' r x with r x
... | ρ' , rel' , y with r' y
... | ρ'' , rel , z = ρ'' , trans rel' rel , z

infixr 20 _∘ᵛʳ_

-- Weakening renaming

wk-vren : ∀ {Γ A} → VRen Γ (Γ ∷ A)
wk-vren {ρ = ρ} x = ρ , refl , Tl-∷ x

-- Variable renaming

var-vren : ∀ {Γ A} → A ∈[ uᵣ ] Γ → VRen (Γ ∷ A) Γ
var-vren {Γ} {A} x Hd =
  uᵣ , refl , x
var-vren {Γ} {A} x (Tl-∷ {ρ = ρ'} y) =
  ρ' , refl , y

-- Strong monoidal functor renamings

⟨⟩-η-vren : ∀ {Γ} → VRen (Γ ⟨ uᵣ ⟩) Γ
⟨⟩-η-vren {Γ} (Tl-⟨⟩ {ρ' = ρ} x) = ρ , ·ᵣ-identityʳ ρ , x

⟨⟩-η⁻¹-vren : ∀ {Γ} → VRen Γ (Γ ⟨ uᵣ ⟩)
⟨⟩-η⁻¹-vren {Γ} {A} {ρ} x = ρ ·ᵣ uᵣ , sym (·ᵣ-identityʳ ρ) , Tl-⟨⟩ x

⟨⟩-μ-vren : ∀ {Γ ρ ρ'} → VRen (Γ ⟨ ρ ·ᵣ ρ' ⟩) (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩)
⟨⟩-μ-vren {Γ} {ρ} {ρ'} {A} {.(ρ'' ·ᵣ (ρ ·ᵣ ρ'))} (Tl-⟨⟩ {ρ' = ρ''} x) =
  ρ'' ·ᵣ ρ ·ᵣ ρ' , sym (·ᵣ-assoc ρ'' ρ ρ') , Tl-⟨⟩ (Tl-⟨⟩ x)

⟨⟩-μ⁻¹-vren : ∀ {Γ ρ ρ'} → VRen (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩) (Γ ⟨ ρ ·ᵣ ρ' ⟩)
⟨⟩-μ⁻¹-vren {Γ} {ρ} {ρ'} {A} {.(_ ·ᵣ ρ ·ᵣ ρ')} (Tl-⟨⟩ (Tl-⟨⟩ {ρ' = ρ''} x)) =
  ρ'' ·ᵣ (ρ ·ᵣ ρ') , ·ᵣ-assoc ρ'' ρ ρ' , Tl-⟨⟩ x

⟨⟩-≡-vren : ∀ {Γ ρ ρ'} → ρ ≡ ρ' → VRen (Γ ⟨ ρ ⟩) (Γ ⟨ ρ' ⟩)
⟨⟩-≡-vren {Γ} {ρ} {ρ'} rel {A} {.(_ ·ᵣ ρ)} (Tl-⟨⟩ {ρ' = ρ''} x) =
  ρ'' ·ᵣ ρ' , cong (ρ'' ·ᵣ_) rel , Tl-⟨⟩ x

-- This shouldn't hold anymore:
{-
-- Derived modal weakening renaming

wk-⟨⟩-vren : ∀ {Γ ρ} → VRen Γ (Γ ⟨ ρ ⟩)
wk-⟨⟩-vren {Γ} {ρ} = ⟨⟩-≾-vren uᵣ≾ᵣc ∘ᵛʳ ⟨⟩-η⁻¹-vren
-}

-- Congruence renamings

cong-∷-vren : ∀ {Γ Γ' A} → VRen Γ Γ' → VRen (Γ ∷ A) (Γ' ∷ A)
cong-∷-vren {Γ} {Γ'} {A} r {B} {ρ} Hd       = uᵣ , refl , Hd
cong-∷-vren {Γ} {Γ'} {A} r {B} {ρ} (Tl-∷ x) with r x
... | ρ' , rel , y = ρ' , rel , Tl-∷ y

cong-⟨⟩-vren : ∀ {Γ Γ' ρ} → VRen Γ Γ' → VRen (Γ ⟨ ρ ⟩) (Γ' ⟨ ρ ⟩)
cong-⟨⟩-vren {Γ} {Γ'} {ρ} r {A} {.(ρ' ·ᵣ ρ)} (Tl-⟨⟩ {ρ' = ρ'} x) with r x
... | ρ'' , r , y = ρ'' ·ᵣ ρ , cong (_·ᵣ ρ) r , Tl-⟨⟩ y

-- This shouldn't hold anymore:
{-
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
-}

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
wk-ctx-vren {Γ} {Γ' ⟨ ρ ⟩} rel with wk-ctx-vren {Γ} {Γ'} (c·ᵣd≡uᵣ⇒c≡uᵣ (ctx-grade Γ') rel)
... | r' = {!!} ∘ᵛʳ r'

{- Previous version: 
-- Weakening by a context renaming

wk-ctx-vren : ∀ {Γ Γ'} → VRen Γ (Γ ++ᶜ Γ')
wk-ctx-vren {Γ' = []} =
  id-vren
wk-ctx-vren {Γ' = Γ' ∷ A} =
  wk-vren ∘ᵛʳ wk-ctx-vren
wk-ctx-vren {Γ' = Γ' ⟨ ρ ⟩} =
  wk-⟨⟩-vren ∘ᵛʳ wk-ctx-vren
-}

-- Exchange renamings

exch-vren : ∀ {Γ A B} → VRen (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-vren = extend-vren (extend-vren (wk-ctx-vren refl) Hd) (Tl-∷ Hd)

-- This shouldn't hold anymore:
{-
exch-⟨⟩-var-vren : ∀ {Γ A ρ} → VRen (Γ ⟨ ρ ⟩ ∷ A) ((Γ ∷ A) ⟨ ρ ⟩)
exch-⟨⟩-var-vren {A = A} {ρ = ρ} =
      var-vren (Tl-⟨⟩ Hd)
  ∘ᵛʳ cong-vren {Γ'' = [] ⟨ _ ⟩ ∷ _} wk-vren
-}

-- Contraction renaming

contract-vren : ∀ {Γ A} → VRen (Γ ∷ A ∷ A) (Γ ∷ A)
contract-vren = var-vren Hd

-- This shouldn't hold anymore:
{-
-- VRenaming from an empty context 

empty-vren : ∀ {Γ} → VRen [] Γ 
empty-vren {[]}      = id-vren
empty-vren {Γ ∷ A}   = wk-vren ∘ᵛʳ empty-vren
empty-vren {Γ ⟨ ρ ⟩} = wk-⟨⟩-vren ∘ᵛʳ empty-vren
-}

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
var-split₁-wk-ctx-vren {Γ} {Γ' ⟨ ρ' ⟩} {A} {ρ} x rel =
  var-split₁-wk-ctx-vren {Γ' = Γ'} x (c·ᵣd≡uᵣ⇒c≡uᵣ {ρ'} (ctx-grade Γ') rel)

--  var-split₁-wk-ctx-vren {Γ} {Γ'} {A} {ρ} x (c·ᵣd≡uᵣ⇒c≡uᵣ {ρ'} (ctx-grade Γ') rel)

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
var-split₂-wk-ctx-vren {Γ' = Γ' ⟨ ρ' ⟩} x rel =
  cong (_⟨ ρ' ⟩) (var-split₂-wk-ctx-vren x (c·ᵣd≡uᵣ⇒c≡uᵣ (ctx-grade Γ') rel))

-- Rename a grade modality to a context capturing at least the same amount of time

vren⟨ρ⟩-ctx : ∀ {Γ Γ' ρ} → ρ ≡ ctx-grade Γ' → VRen (Γ ⟨ ρ ⟩) (Γ ++ᶜ Γ')
vren⟨ρ⟩-ctx {Γ} {Γ'} {ρ} rel = {!!}

-- Identity laws

∘ᵛʳ-identityˡ : ∀ {Γ Γ' A ρ}
              → (r : VRen Γ Γ')
              → (x : A ∈[ ρ ] Γ)
              → (id-vren ∘ᵛʳ r) x ≡ r x

∘ᵛʳ-identityˡ {Γ} {Γ'} {A} {ρ} r x =
  dcong₂ _,_ refl (cong₂ _,_ (trans-reflʳ (r x .proj₂ .proj₁)) refl)

∘ᵛʳ-identityʳ : ∀ {Γ Γ' A ρ}
              → (r : VRen Γ Γ')
              → (x : A ∈[ ρ ] Γ)
              → (r ∘ᵛʳ id-vren) x ≡ r x

∘ᵛʳ-identityʳ {Γ} {Γ'} {A} {ρ} r x = 
  dcong₂ _,_ refl refl

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
... | ρ'' , r , y = dcong₂ _,_ refl refl

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

cong-∷-vren-fun r r' Hd       = dcong₂ _,_ refl refl
cong-∷-vren-fun r r' (Tl-∷ x) = refl

cong-⟨⟩-vren-fun : ∀ {Γ Γ' Γ'' A ρ ρ'}
                → (r : VRen Γ Γ')
                → (r' : VRen Γ' Γ'')
                → (x : A ∈[ ρ ] (Γ ⟨ ρ' ⟩))
                → cong-⟨⟩-vren (r' ∘ᵛʳ r) x
                ≡ (cong-⟨⟩-vren r' ∘ᵛʳ cong-⟨⟩-vren r) x
                
cong-⟨⟩-vren-fun r r' (Tl-⟨⟩ x) with r x
... | ρ'' , r , y = cong (_ ,_) (cong (_, _) {!!})
--... | ρ'' , r , y = cong (_ ,_) (cong (_, Tl-⟨⟩ (proj₂ (proj₂ (r' y)))) (≾ᵣ-irrelevant _ _))

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
