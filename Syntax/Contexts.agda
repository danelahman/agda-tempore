--------------------------------------------
-- Variables and contexts of the language --
--------------------------------------------

open import Syntax.Grades

module Syntax.Contexts (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Empty -- Remove?
open import Data.Product
open import Data.Sum

open import Relation.Binary.Definitions
open import Relation.Nullary

open import Syntax.Types (Grades)

open import Util.Equality
open import Util.Operations (Grades)
open import Util.Time -- Remove

-- Structured contexts

data Ctx : Set where
  []   : Ctx                    -- empty context
  _∷_  : Ctx → VType → Ctx      -- context extension with a variable
  _⟨_⟩ : Ctx → R → Ctx          -- using context after time-passage

infixl 31 _∷_
infix  32 _⟨_⟩

∷ᶜ-injective-ctx : ∀ {Γ Γ' A B} → Γ ∷ A ≡ Γ' ∷ B → Γ ≡ Γ'
∷ᶜ-injective-ctx refl = refl

∷ᶜ-injective-ty : ∀ {Γ Γ' A B} → Γ ∷ A ≡ Γ' ∷ B → A ≡ B
∷ᶜ-injective-ty refl = refl

⟨⟩-injective-ctx : ∀ {Γ Γ' ρ ρ'} → Γ ⟨ ρ ⟩ ≡ Γ' ⟨ ρ' ⟩ → Γ ≡ Γ'
⟨⟩-injective-ctx refl = refl

⟨⟩-injective-rgrade : ∀ {Γ Γ' ρ ρ'} → Γ ⟨ ρ ⟩ ≡ Γ' ⟨ ρ' ⟩ → ρ ≡ ρ'
⟨⟩-injective-rgrade refl = refl

-- Concatenation of contexts

_++ᶜ_ : Ctx → Ctx → Ctx
Γ ++ᶜ []         = Γ
Γ ++ᶜ (Γ' ∷ A)   = (Γ ++ᶜ Γ') ∷ A
Γ ++ᶜ (Γ' ⟨ ρ ⟩) = (Γ ++ᶜ Γ') ⟨ ρ ⟩

infixl 30 _++ᶜ_

-- Identity, associativity, congruence, and injectivity of ++ᶜ

++ᶜ-identityˡ : ∀ {Γ} → [] ++ᶜ Γ ≡ Γ
++ᶜ-identityˡ {[]}      = refl
++ᶜ-identityˡ {Γ ∷ A}   = cong (_∷ A) ++ᶜ-identityˡ
++ᶜ-identityˡ {Γ ⟨ ρ ⟩} = cong (_⟨ ρ ⟩) ++ᶜ-identityˡ

++ᶜ-identityʳ : ∀ {Γ} → Γ ++ᶜ [] ≡ Γ
++ᶜ-identityʳ = refl

++ᶜ-assoc : (Γ Γ' Γ'' : Ctx) → (Γ ++ᶜ Γ') ++ᶜ Γ'' ≡ Γ ++ᶜ (Γ' ++ᶜ Γ'')
++ᶜ-assoc Γ Γ' []          = refl
++ᶜ-assoc Γ Γ' (Γ'' ∷ A)   = cong (_∷ A) (++ᶜ-assoc Γ Γ' Γ'')
++ᶜ-assoc Γ Γ' (Γ'' ⟨ ρ ⟩) = cong (_⟨ ρ ⟩) (++ᶜ-assoc Γ Γ' Γ'')

++ᶜ-congʳ : (Γ Γ' Γ'' : Ctx) → Γ' ≡ Γ'' → (Γ ++ᶜ Γ') ≡ (Γ ++ᶜ Γ'')
++ᶜ-congʳ Γ Γ' Γ'' p = cong (Γ ++ᶜ_) p

++ᶜ-identityˡ-unique : ∀ {Γ Γ'} → Γ ≡ Γ' ++ᶜ Γ → Γ' ≡ []
++ᶜ-identityˡ-unique {[]} {Γ'} p = sym p
++ᶜ-identityˡ-unique {Γ ∷ A} {Γ'} p =
  ++ᶜ-identityˡ-unique (∷ᶜ-injective-ctx p)
++ᶜ-identityˡ-unique {Γ ⟨ ρ ⟩} {Γ'} p =
  ++ᶜ-identityˡ-unique (⟨⟩-injective-ctx p)

++ᶜ-identityʳ-unique : ∀ {Γ Γ'} → Γ ≡ Γ ++ᶜ Γ' → Γ' ≡ []
++ᶜ-identityʳ-unique {Γ} {[]} p =
  refl
++ᶜ-identityʳ-unique {Γ ∷ A} {Γ' ∷ B} p
  with ++ᶜ-identityʳ-unique {Γ} {[] ∷ A ++ᶜ Γ'}
         (trans (∷ᶜ-injective-ctx p) (++ᶜ-assoc Γ ([] ∷ A) Γ'))
++ᶜ-identityʳ-unique {Γ ∷ A} {[] ∷ B} p | ()
++ᶜ-identityʳ-unique {Γ ∷ A} {Γ' ∷ _ ∷ B} p | ()
++ᶜ-identityʳ-unique {Γ ∷ A} {Γ' ⟨ _ ⟩ ∷ B} p | ()
++ᶜ-identityʳ-unique {Γ ⟨ ρ ⟩} {Γ' ⟨ ρ' ⟩} p
  with ++ᶜ-identityʳ-unique {Γ} {[] ⟨ ρ ⟩ ++ᶜ Γ'}
         (trans (⟨⟩-injective-ctx p) (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Γ'))
++ᶜ-identityʳ-unique {Γ ⟨ ρ ⟩} {[] ⟨ ρ' ⟩} p | ()
++ᶜ-identityʳ-unique {Γ ⟨ ρ ⟩} {(Γ' ∷ _) ⟨ ρ' ⟩} p | ()
++ᶜ-identityʳ-unique {Γ ⟨ ρ ⟩} {(Γ' ⟨ _ ⟩) ⟨ ρ' ⟩} p | ()

++ᶜ-inj₁ : ∀ {Γ₁ Γ₂ Γ} → Γ₁ ++ᶜ Γ ≡ Γ₂ ++ᶜ Γ → Γ₁ ≡ Γ₂
++ᶜ-inj₁ {Γ₁} {Γ₂} {[]} p =
  p
++ᶜ-inj₁ {Γ₁} {Γ₂} {Γ ∷ A} p =
  ++ᶜ-inj₁ (∷ᶜ-injective-ctx p)
++ᶜ-inj₁ {Γ₁} {Γ₂} {Γ ⟨ ρ ⟩} p =
  ++ᶜ-inj₁ (⟨⟩-injective-ctx p)

++ᶜ-inj₂ : ∀ {Γ Γ₁ Γ₂} → Γ ++ᶜ Γ₁ ≡ Γ ++ᶜ Γ₂ → Γ₁ ≡ Γ₂
++ᶜ-inj₂ {Γ} {[]} {[]} q =
  refl
++ᶜ-inj₂ {Γ} {[]} {Γ₂ ∷ B} q =
  sym (++ᶜ-identityʳ-unique q)
++ᶜ-inj₂ {Γ} {[]} {Γ₂ ⟨ ρ' ⟩} q =
  sym (++ᶜ-identityʳ-unique q)
++ᶜ-inj₂ {Γ} {Γ₁ ∷ A} {[]} q =
  ++ᶜ-identityʳ-unique (sym q)
++ᶜ-inj₂ {Γ} {Γ₁ ∷ A} {Γ₂ ∷ B} q =
  cong₂ _∷_ (++ᶜ-inj₂ (∷ᶜ-injective-ctx q)) (∷ᶜ-injective-ty q)
++ᶜ-inj₂ {Γ} {Γ₁ ⟨ ρ ⟩} {[]} q =
  ++ᶜ-identityʳ-unique (sym q)
++ᶜ-inj₂ {Γ} {Γ₁ ⟨ ρ ⟩} {Γ₂ ⟨ ρ' ⟩} q =
  cong₂ _⟨_⟩ (++ᶜ-inj₂ (⟨⟩-injective-ctx q)) (⟨⟩-injective-rgrade q)

++ᶜ-left-zero-divisor : ∀ {Γ Γ'} → Γ ++ᶜ Γ' ≡ [] → Γ ≡ []
++ᶜ-left-zero-divisor {Γ} {[]} p = p

++ᶜ-right-zero-divisor : ∀ {Γ Γ'} → Γ ++ᶜ Γ' ≡ [] → Γ' ≡ []
++ᶜ-right-zero-divisor {Γ} {[]} p = refl

-- Amount of time-passage modelled by a context 

ctx-grade : Ctx → R
ctx-grade []        = uᵣ
ctx-grade (Γ ∷ A)   = ctx-grade Γ
ctx-grade (Γ ⟨ ρ ⟩) = ctx-grade Γ ·ᵣ ρ

-- Interaction of time-passage and ++ᶜ

ctx-grade-++ᶜ : (Γ Γ' : Ctx)
              → ctx-grade (Γ ++ᶜ Γ') ≡ (ctx-grade Γ ·ᵣ ctx-grade Γ')
ctx-grade-++ᶜ Γ []         = sym (·ᵣ-identityʳ (ctx-grade Γ))
ctx-grade-++ᶜ Γ (Γ' ∷ x)   = ctx-grade-++ᶜ Γ Γ'
ctx-grade-++ᶜ Γ (Γ' ⟨ ρ ⟩) = trans (cong (_·ᵣ ρ) (ctx-grade-++ᶜ Γ Γ'))
                             (·ᵣ-assoc (ctx-grade Γ) (ctx-grade Γ') ρ)

-- Proof that sub-contexts split a given context

data _,_split_ : (Γ Γ' Γ'' : Ctx) → Set where
  split-[] : ∀ {Γ} → Γ , [] split Γ
  split-∷  : ∀ {Γ Γ' Γ'' A} → Γ , Γ' split Γ'' → Γ , Γ' ∷ A split Γ'' ∷ A
  split-⟨⟩ : ∀ {Γ Γ' Γ'' ρ} → Γ , Γ' split Γ'' → Γ , Γ' ⟨ ρ ⟩ split Γ'' ⟨ ρ ⟩

-- Interaction between context splitting and ++ᶜ 

split-≡ : ∀ {Γ Γ₁ Γ₂} → Γ₁ , Γ₂ split Γ → Γ₁ ++ᶜ Γ₂ ≡ Γ
split-≡ split-[]     = refl
split-≡ (split-∷ c)  = cong (_∷ _) (split-≡ c)
split-≡ (split-⟨⟩ c) = cong (_⟨ _ ⟩) (split-≡ c)

≡-split : ∀ {Γ Γ₁ Γ₂} → Γ₁ ++ᶜ Γ₂ ≡ Γ → Γ₁ , Γ₂ split Γ
≡-split {Γ₂ = []}       refl = split-[]
≡-split {Γ₂ = Γ₂ ∷ A}   refl = split-∷ (≡-split refl)
≡-split {Γ₂ = Γ₂ ⟨ ρ ⟩} refl = split-⟨⟩ (≡-split refl)

split-≡-++ᶜ : ∀ {Γ₁ Γ₂} → Γ₁ , Γ₂ split (Γ₁ ++ᶜ Γ₂)
split-≡-++ᶜ = ≡-split refl

-- Variable in a context (under ρ-amount of time-passage)

data _∈[_]_ (A : VType) : R → Ctx → Set where
  Hd    : ∀ {Γ}      → A ∈[ uᵣ ] Γ ∷ A
  Tl-∷  : ∀ {Γ B ρ}  → A ∈[ ρ ] Γ → A ∈[ ρ ] Γ ∷ B
  Tl-⟨⟩ : ∀ {Γ ρ ρ'} → A ∈[ ρ' ] Γ → A ∈[ ρ' ·ᵣ ρ ] Γ ⟨ ρ ⟩

infix 27 _∈[_]_

-- Context extension does not decrease variable's grade annotation

var-ρ-++ᶜ : ∀ {Γ Γ' A ρ} → A ∈[ ρ ] Γ → A ∈[ ρ ·ᵣ ctx-grade Γ' ] Γ ++ᶜ Γ'
var-ρ-++ᶜ {Γ} {[]} {A} x =
  subst (A ∈[_] Γ) (sym (·ᵣ-identityʳ _)) x
var-ρ-++ᶜ {Γ' = Γ' ∷ B} x =
  Tl-∷ (var-ρ-++ᶜ x)
var-ρ-++ᶜ {Γ} {Γ' ⟨ ρ' ⟩} {A} {ρ} x =
  subst (A ∈[_] (Γ ++ᶜ Γ') ⟨ ρ' ⟩) (·ᵣ-assoc ρ (ctx-grade Γ') ρ') (Tl-⟨⟩ (var-ρ-++ᶜ {Γ} {Γ'} x))

-- Splitting a context according to a variable in it

var-split : ∀ {Γ A ρ}
          → A ∈[ ρ ] Γ
          → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] Γ₁ ∷ A , Γ₂ split Γ × ctx-grade Γ₂ ≡ ρ
var-split (Hd {Γ}) = Γ , [] , split-[] , refl
var-split {Γ ∷ B} (Tl-∷ x) with var-split x
... | Γ₁ , Γ₂ , p₁ , e = Γ₁ , Γ₂ ∷ B , split-∷ p₁ , e
var-split {Γ ⟨ ρ ⟩} (Tl-⟨⟩ x) with var-split x
... | Γ₁ , Γ₂ , p , q =
  Γ₁ , Γ₂ ⟨ ρ ⟩ , split-⟨⟩ p , cong (_·ᵣ ρ) q
  
-- Variable splitting preserves time-passage modelled by a context

split-pres-ctx-grade : ∀ {Γ Γ₁ Γ₂ A}
                    → Γ₁ ∷ A , Γ₂ split Γ
                    → ctx-grade Γ ≡ ctx-grade (Γ₁ ++ᶜ Γ₂)
split-pres-ctx-grade split-[] =
  refl
split-pres-ctx-grade (split-∷ c) =
  split-pres-ctx-grade c
split-pres-ctx-grade (split-⟨⟩ {ρ = ρ} c) =
  cong (_·ᵣ ρ) (split-pres-ctx-grade c) 

-- Variable in context is in one of the two contexts splitting it

var-in-split-proj₁-subst : ∀ {Γ A ρ ρ'}
                         → (x : A ∈[ ρ ] Γ)
                         → (c : ρ ≡ ρ')
                         → proj₁ (var-split x)
                         ≡ proj₁ (var-split (subst (A ∈[_] Γ) c x))

var-in-split-proj₁-subst x refl = refl

var-in-split-proj₂-subst : ∀ {Γ A ρ ρ'}
                         → (x : A ∈[ ρ ] Γ)
                         → (c : ρ ≡ ρ')
                         → proj₁ (proj₂ (var-split x))
                         ≡ proj₁ (proj₂ (var-split (subst (A ∈[_] Γ) c x)))

var-in-split-proj₂-subst x refl = refl

var-in-split : ∀ {Γ Γ₁ Γ₂ A ρ}
             → Γ₁ , Γ₂ split Γ
             → (x : A ∈[ ρ ] Γ)
             → (Σ[ ρ' ∈ R ] (Σ[ y ∈ A ∈[ ρ' ] Γ₁ ]
                   proj₁ (var-split x) ≡ proj₁ (var-split y)
                 × proj₁ (proj₂ (var-split x)) ≡ proj₁ (proj₂ (var-split y)) ++ᶜ Γ₂))
             ⊎ (Σ[ y ∈ A ∈[ ρ ] Γ₂ ]
                   proj₁ (var-split x) ≡ Γ₁ ++ᶜ proj₁ (var-split y)
                 × proj₁ (proj₂ (var-split x)) ≡ proj₁ (proj₂ (var-split y)))

var-in-split {ρ = ρ} split-[] x =
  inj₁ (ρ , x , refl , refl)
var-in-split (split-∷ p) Hd = 
  inj₂ (Hd , sym (split-≡ p) , refl)
var-in-split (split-∷ p) (Tl-∷ {B = B} x) with var-in-split p x
... | inj₁ (ρ' , y , rel , rel') =
  inj₁ (ρ' , y , rel , cong (_∷ B) rel')
... | inj₂ (y , rel , rel') =
  inj₂ (Tl-∷ y , rel , cong (_∷ B) rel')
var-in-split {Γ₂ = Γ₂ ⟨ ρ₂ ⟩} {ρ = ρ} (split-⟨⟩ p) (Tl-⟨⟩ {ρ' = ρ''} x) with var-in-split p x
... | inj₁ (ρ' , y , rel , rel') =
  inj₁ (ρ' , y , rel , cong (_⟨ ρ₂ ⟩) rel')
... | inj₂ (y , rel , rel') =
  inj₂ (Tl-⟨⟩ y , rel , cong (_⟨ ρ₂ ⟩) rel')

split-struct-≡ : ∀ {Γ Γ' Γ'' A ρ₁ ρ₂}
               → (x : A ∈[ ρ₁ ] Γ')
               → (y : A ∈[ ρ₂ ] Γ)
               → proj₁ (var-split y) ≡ proj₁ (var-split x)
               → proj₁ (proj₂ (var-split y)) ≡ proj₁ (proj₂ (var-split x)) ++ᶜ Γ''
               → Γ' ++ᶜ Γ'' ≡ Γ
split-struct-≡ {Γ} {Γ'} {Γ''} {A} x y eq₁ eq₂ =
  begin
    Γ' ++ᶜ Γ''
  ≡⟨ cong (_++ᶜ Γ'') (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x)))))) ⟩
    proj₁ (var-split x) ∷ A ++ᶜ proj₁ (proj₂ (var-split x)) ++ᶜ Γ''
  ≡⟨ ++ᶜ-assoc (proj₁ (var-split x) ∷ A) (proj₁ (proj₂ (var-split x))) Γ'' ⟩
    proj₁ (var-split x) ∷ A ++ᶜ (proj₁ (proj₂ (var-split x)) ++ᶜ Γ'')
  ≡⟨ cong (proj₁ (var-split x) ∷ A ++ᶜ_) (sym eq₂) ⟩ 
    proj₁ (var-split x) ∷ A ++ᶜ ((proj₁ (proj₂ (var-split y))))
  ≡⟨ (cong (_++ᶜ proj₁ (proj₂ (var-split y))) (cong (_∷ A) (sym eq₁))) ⟩
    proj₁ (var-split y) ∷ A ++ᶜ proj₁ (proj₂ (var-split y))
  ≡⟨ split-≡ (proj₁ (proj₂ (proj₂ (var-split y)))) ⟩ 
    Γ
  ∎

-- No variable belongs to the empty context

var-not-in-empty-ctx : ∀ {A} → ¬ (Σ[ ρ ∈ R ] (A ∈[ ρ ] []))
var-not-in-empty-ctx = λ ()

-- If a variable is not in a context Γ and its type doesn't coincide with the type of the head of Γ,
-- then it's not in Γ

var-not-in-ctx-∷ : ∀ {Γ A B}
                 → ¬ (Σ[ ρ ∈ R ] (A ∈[ ρ ] Γ))
                 → ¬ (B ≡ A)
                 → ¬ (Σ[ ρ' ∈ R ] (A ∈[ ρ' ] Γ ∷ B))
var-not-in-ctx-∷ ¬p ¬q (_ , Hd)     = ¬q refl
var-not-in-ctx-∷ ¬p ¬q (_ , Tl-∷ x) = ¬p (_ , x)

-- If a variable is not in a context Γ then it's not in Γ ⟨ ρ ⟩

var-not-in-ctx-⟨⟩ : ∀ {Γ A ρ}
                  → (¬ (Σ[ ρ' ∈ R ] (A ∈[ ρ' ] Γ)))
                  → ¬ (Σ[ ρ'' ∈ R ] (A ∈[ ρ'' ] Γ ⟨ ρ ⟩))
var-not-in-ctx-⟨⟩ {ρ = ρ} ¬p (_ , Tl-⟨⟩ x) = ¬p (_ , x)

-- Checking whether a variable is in the context before the extension

var-in-ctx? : ∀ {Γ Γ' A ρ} → A ∈[ ρ ] Γ → Dec (Σ[ ρ' ∈ R ] (A ∈[ ρ' ] Γ'))
var-in-ctx? {Γ} {[]} x = no var-not-in-empty-ctx
var-in-ctx? {Γ ∷ B} {Γ' ∷ A} Hd with var-in-ctx? {Γ ∷ B} {Γ'} Hd
... | yes (ρ' , y) = yes (ρ' , Tl-∷ y)
... | no ¬p with A ≡ᵥ? B
... | yes refl = yes (uᵣ , Hd)
... | no ¬q = no (var-not-in-ctx-∷ ¬p ¬q)
var-in-ctx? {Γ ∷ B} {Γ' ∷ A} {A = C} (Tl-∷ x) with var-in-ctx? {Γ} {Γ'} x
... | yes (ρ' , y) = yes (ρ' , Tl-∷ y)
... | no ¬p with A ≡ᵥ? C
... | yes refl = yes (uᵣ , Hd)
... | no ¬q = no (var-not-in-ctx-∷ ¬p ¬q)
var-in-ctx? {Γ ⟨ ρ₁ ⟩} {Γ' ∷ A} {A = B} (Tl-⟨⟩ x) with var-in-ctx? {Γ} {Γ'} x
... | yes (ρ' , y) = yes (ρ' , Tl-∷ y)
... | no ¬p with A ≡ᵥ? B
... | yes refl = yes (uᵣ , Hd)
... | no ¬q = no (var-not-in-ctx-∷ ¬p ¬q)
var-in-ctx? {Γ ∷ A} {Γ' ⟨ ρ'' ⟩} Hd with var-in-ctx? {Γ ∷ A} {Γ'} Hd
... | yes (ρ' , y) = yes (ρ' ·ᵣ ρ'' , Tl-⟨⟩ y)
... | no ¬p = no (var-not-in-ctx-⟨⟩ ¬p)
var-in-ctx? {Γ ∷ A} {Γ' ⟨ ρ'' ⟩} (Tl-∷ x) with var-in-ctx? {Γ} {Γ'} x
... | yes (ρ' , y) = yes (ρ' ·ᵣ ρ'' , Tl-⟨⟩ y)
... | no ¬p = no (var-not-in-ctx-⟨⟩ ¬p)
var-in-ctx? {Γ ⟨ ρ₁ ⟩} {Γ' ⟨ ρ'' ⟩} (Tl-⟨⟩ x) with var-in-ctx? {Γ} {Γ'} x
... | yes (ρ' , y) = yes (ρ' ·ᵣ ρ'' , Tl-⟨⟩ y)
... | no ¬p = no (var-not-in-ctx-⟨⟩ ¬p)

-- "Time-travelling" operation on contexts, declaratively

data _-ᶜ_≈_ : Ctx → R → Ctx → Set where

  -ᶜ-uᵣ    : ∀ {Γ ρ}
           → ρ ≡ uᵣ
           -------------
           → Γ -ᶜ ρ ≈ Γ

  -ᶜ-∷     : ∀ {Γ Γ' A ρ}
           → ρ ≢ uᵣ
           → Γ -ᶜ ρ ≈ Γ'
           -----------------
           → Γ ∷ A -ᶜ ρ ≈ Γ'
            
  -ᶜ-⟨⟩-lt : ∀ {Γ ρ ρ' ρ''}
           → ρ' ≢ uᵣ
           → ρ ≡ ρ'' ·ᵣ ρ'
           ---------------------------
           → Γ ⟨ ρ ⟩ -ᶜ ρ' ≈ Γ ⟨ ρ'' ⟩
             
  -ᶜ-⟨⟩-gt : ∀ {Γ Γ' ρ ρ' ρ''}
           → ρ' ≢ uᵣ
           → ¬(Σ[ ρ''' ∈ R ] ρ ≡ ρ''' ·ᵣ ρ')
           → ρ' ≡ ρ'' ·ᵣ ρ
           → Γ -ᶜ ρ'' ≈ Γ'
           --------------------
           → Γ ⟨ ρ ⟩ -ᶜ ρ' ≈ Γ'

infixl 29 _-ᶜ_≈_

-- Action laws for -ᶜ

++ᶜ-ᶜ : ∀ {Γ Γ' Γ'' ρ}
      → Γ' -ᶜ ρ ≈ Γ''
      → (Γ ++ᶜ Γ') -ᶜ ρ ≈ Γ ++ᶜ Γ''

++ᶜ-ᶜ (-ᶜ-uᵣ p) =
  -ᶜ-uᵣ p
++ᶜ-ᶜ (-ᶜ-∷ p q) =
  -ᶜ-∷ p (++ᶜ-ᶜ q)
++ᶜ-ᶜ (-ᶜ-⟨⟩-lt p q) =
  -ᶜ-⟨⟩-lt p q
++ᶜ-ᶜ (-ᶜ-⟨⟩-gt p q r s) =
  -ᶜ-⟨⟩-gt p q r (++ᶜ-ᶜ s)

-ᶜ-u : ∀ {Γ Γ'}
        → Γ -ᶜ uᵣ ≈ Γ'
        → Γ ≡ Γ'

-ᶜ-u (-ᶜ-uᵣ p) = refl
-ᶜ-u (-ᶜ-∷ p q) = ⊥-elim (p refl)
-ᶜ-u (-ᶜ-⟨⟩-lt p q) = ⊥-elim (p refl)
-ᶜ-u (-ᶜ-⟨⟩-gt p q r s) = ⊥-elim (p refl)

-ᶜ-· : ∀ {Γ Γ' Γ'' ρ₁ ρ₂}
        → Γ -ᶜ ρ₂ ≈ Γ'
        → Γ' -ᶜ ρ₁ ≈ Γ''
        → Γ -ᶜ (ρ₁ ·ᵣ ρ₂) ≈ Γ''

-ᶜ-· {ρ₁ = ρ₁} {ρ₂ = ρ₂} (-ᶜ-uᵣ refl) q rewrite ·ᵣ-identityʳ ρ₁ =
  q
-ᶜ-· {ρ₁ = ρ₁} {ρ₂ = ρ₂} (-ᶜ-∷ p q) r =
  -ᶜ-∷ (λ z → p (c·ᵣd≡uᵣ⇒d≡uᵣ z)) (-ᶜ-· q r)
-ᶜ-· {ρ₁ = ρ₁} {ρ₂ = ρ₂} (-ᶜ-⟨⟩-lt {ρ'' = ρ''} p q) (-ᶜ-uᵣ refl) with ρ₂ ≡ᵣ? uᵣ
... | yes refl rewrite q | ·ᵣ-identityʳ ρ'' | ·ᵣ-identityʳ uᵣ =
  -ᶜ-uᵣ refl
... | no ¬r rewrite ·ᵣ-identityˡ ρ₂ =
  -ᶜ-⟨⟩-lt ¬r q
-ᶜ-· {ρ₁ = ρ₁} {ρ₂ = ρ₂} (-ᶜ-⟨⟩-lt p q) (-ᶜ-⟨⟩-lt r s) rewrite q | s =
  -ᶜ-⟨⟩-lt (λ z → r (c·ᵣd≡uᵣ⇒c≡uᵣ z)) (·ᵣ-assoc _ ρ₁ ρ₂)
-ᶜ-· {ρ₁ = ρ₁} {ρ₂ = ρ₂} (-ᶜ-⟨⟩-lt p q) (-ᶜ-⟨⟩-gt r s t u) rewrite q | t =
  -ᶜ-⟨⟩-gt
    (λ z → r (c·ᵣd≡uᵣ⇒c≡uᵣ z))
    (λ { (ρ''' , u) → s (ρ''' , (c·ᵣd≡e·ᵣd⇒c≡e (trans u (sym (·ᵣ-assoc _ _ _))))) })
    (·ᵣ-assoc _ _ ρ₂) u
-ᶜ-· {ρ₁ = ρ₁} {ρ₂ = ρ₂} (-ᶜ-⟨⟩-gt {ρ = ρ} {ρ'' = ρ''} p q r s) t rewrite r =
  -ᶜ-⟨⟩-gt
    (λ z → p (c·ᵣd≡uᵣ⇒d≡uᵣ z))
    (λ { (ρ''' , u) → q (ρ''' ·ᵣ ρ₁ , trans u (sym (·ᵣ-assoc _ _ _))) })
    (sym (·ᵣ-assoc _ _ _))
    (-ᶜ-· s t)

{-
·-ᶜ : ∀ {Γ Γ' ρ ρ' ρ''}
    → ρ'' ≢ uᵣ
    → Γ ⟨ ρ ⟩ ⟨ ρ' ⟩ -ᶜ ρ'' ≈ Γ'
    → Γ ⟨ ρ ·ᵣ ρ' ⟩ -ᶜ ρ'' ≈ Γ'

·-ᶜ p (-ᶜ-uᵣ q) =
  ⊥-elim (p q)
·-ᶜ p (-ᶜ-⟨⟩-lt q r) rewrite r = {!!}
·-ᶜ p (-ᶜ-⟨⟩-gt q r s t) = {!!}
-}

-- "Time-travelling" operation is functional

-ᶜ-functional : ∀ {Γ Γ' Γ'' ρ}
              → Γ -ᶜ ρ ≈ Γ'
              → Γ -ᶜ ρ ≈ Γ''
              → Γ' ≡ Γ''

-ᶜ-functional (-ᶜ-uᵣ p) (-ᶜ-uᵣ q) =
  refl
-ᶜ-functional (-ᶜ-uᵣ p) (-ᶜ-∷ q r) =
  ⊥-elim (q p)
-ᶜ-functional (-ᶜ-uᵣ p) (-ᶜ-⟨⟩-lt q r) =
  ⊥-elim (q p)
-ᶜ-functional (-ᶜ-uᵣ p) (-ᶜ-⟨⟩-gt q r s t) =
  ⊥-elim (q p)
-ᶜ-functional (-ᶜ-∷ p q) (-ᶜ-uᵣ r) =
  ⊥-elim (p r)
-ᶜ-functional (-ᶜ-∷ p q) (-ᶜ-∷ r s) =
  -ᶜ-functional q s
-ᶜ-functional (-ᶜ-⟨⟩-lt p q) (-ᶜ-uᵣ r) =
  ⊥-elim (p r)
-ᶜ-functional (-ᶜ-⟨⟩-lt p q) (-ᶜ-⟨⟩-lt r s)
  rewrite c·ᵣd≡e·ᵣd⇒c≡e (trans (sym q) s) =
    refl
-ᶜ-functional (-ᶜ-⟨⟩-lt p q) (-ᶜ-⟨⟩-gt r s t u) =
  ⊥-elim (s (_ , q))
-ᶜ-functional (-ᶜ-⟨⟩-gt p q r s) (-ᶜ-uᵣ t) =
  ⊥-elim (p t)
-ᶜ-functional (-ᶜ-⟨⟩-gt p q r s) (-ᶜ-⟨⟩-lt t u) =
  ⊥-elim (q (_ , u))
-ᶜ-functional (-ᶜ-⟨⟩-gt p q r s) (-ᶜ-⟨⟩-gt t u v w)
  rewrite c·ᵣd≡e·ᵣd⇒c≡e (trans (sym r) v) =
    -ᶜ-functional s w
