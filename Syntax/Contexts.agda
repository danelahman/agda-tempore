--------------------------------------------
-- Variables and contexts of the language --
--------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Binary.Definitions
open import Relation.Nullary

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

module Syntax.Contexts (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S

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

-- AMBIENT JOIN
--
-- The same concatenation, but recursing on its *left* argument, so that the
-- empty case reduces: `[] ⋈ᶜ Δ` is `Δ` definitionally, where `[] ++ᶜ Δ` is only
-- propositionally so (`++ᶜ` recurses on the right). Renamings are indexed by an
-- ambient context and join it to their local parts with this, which is what
-- keeps everything at the empty ambient — the language's own renamings and all
-- the derived ones — free of transports.

_⋈ᶜ_ : Ctx → Ctx → Ctx
[] ⋈ᶜ Δ        = Δ
(Ξ ∷ A) ⋈ᶜ Δ   = (Ξ ∷ A) ++ᶜ Δ
(Ξ ⟨ ρ ⟩) ⋈ᶜ Δ = (Ξ ⟨ ρ ⟩) ++ᶜ Δ

infixl 30 _⋈ᶜ_

⋈ᶜ-++ᶜ : (Ξ Δ : Ctx) → Ξ ⋈ᶜ Δ ≡ Ξ ++ᶜ Δ
⋈ᶜ-++ᶜ []        Δ = sym ++ᶜ-identityˡ
⋈ᶜ-++ᶜ (Ξ ∷ A)   Δ = refl
⋈ᶜ-++ᶜ (Ξ ⟨ ρ ⟩) Δ = refl

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

∈-ctx-extensionˡ : ∀ {A ρ} → (Γ : Ctx) → (Γ' : Ctx) → A ∈[ ρ ] Γ' → A ∈[ ρ ] Γ ++ᶜ Γ'
∈-ctx-extensionˡ _ _ Hd = Hd
∈-ctx-extensionˡ Γ _ (Tl-∷ x) = Tl-∷ (∈-ctx-extensionˡ Γ _ x)
∈-ctx-extensionˡ Γ _ (Tl-⟨⟩ x) = Tl-⟨⟩ (∈-ctx-extensionˡ Γ _ x)


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

-- Named accessors for the components of `var-split`. Using these
-- avoids the deep `proj₁ (proj₂ (proj₂ ...))` chains at call sites.

split-l : ∀ {Γ A ρ} → A ∈[ ρ ] Γ → Ctx
split-l x = proj₁ (var-split x)

split-r : ∀ {Γ A ρ} → A ∈[ ρ ] Γ → Ctx
split-r x = proj₁ (proj₂ (var-split x))

split-pf : ∀ {Γ A ρ} → (x : A ∈[ ρ ] Γ) → split-l x ∷ A , split-r x split Γ
split-pf x = proj₁ (proj₂ (proj₂ (var-split x)))

split-grade-≡ : ∀ {Γ A ρ} → (x : A ∈[ ρ ] Γ) → ctx-grade (split-r x) ≡ ρ
split-grade-≡ x = proj₂ (proj₂ (proj₂ (var-split x)))
  
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

-- Grade-only contexts

data ⟨⟩-Ctx : Ctx → Set where
  is-[] : ⟨⟩-Ctx []
  is-⟨⟩ : ∀ {Γ ρ} → ⟨⟩-Ctx Γ → ⟨⟩-Ctx (Γ ⟨ ρ ⟩)

-- The concatenation of two grade-only contexts is a grade-only context

++ᶜ-⟨⟩ : ∀ {Γ₁ Γ₂} → ⟨⟩-Ctx Γ₁ → ⟨⟩-Ctx Γ₂ → ⟨⟩-Ctx (Γ₁ ++ᶜ Γ₂)
++ᶜ-⟨⟩ {Γ₂ = []} Γ₁' _ =
  Γ₁'
++ᶜ-⟨⟩ {Γ₂ = Γ₂ ⟨ ρ ⟩} Γ₁' (is-⟨⟩ Γ₂') =
  is-⟨⟩ (++ᶜ-⟨⟩ Γ₁' Γ₂')


-- The left split of a context Γ according to a variable x is the same as
-- the left split of a Γ extended with a context modality.

var-split-≡-var-split-Tl-⟨⟩ : ∀ {Γ A ρ ρ'}
                            → (x : A ∈[ ρ ] Γ)
                            → proj₁ (var-split x) ≡ proj₁ (var-split (Tl-⟨⟩ {ρ = ρ'} x))
var-split-≡-var-split-Tl-⟨⟩ x = refl

-- Eternal restriction of a context: keep only the eternal-typed variables,
-- dropping non-eternal variables and all locks. Eternal values survive
-- arbitrary time-passage (`eternal-val-ext`), so a lock imposes no real
-- constraint on eternal data. The result is therefore lock-free, and every
-- surviving variable sits at grade `uᵣ`.

-- The `∷` clause is routed through a helper taking the decision, rather than
-- being a `with` on it. That keeps `(Γ ∷ A) ᴱ` *reducible* at a variable `A`:
-- it exposes `eternal? A` syntactically, so a `with`/`rewrite` elsewhere can
-- abstract it. As a `with`-function the occurrence sits inside an auxiliary
-- that nothing outside can see, which blocks every proof that must reduce both
-- a term and its clause family's context at the same decision.

ᴱ-∷ : Ctx → (A : VType) → Dec (Eternal A) → Ctx
ᴱ-∷ Γ A (yes _) = Γ ∷ A
ᴱ-∷ Γ A (no  _) = Γ

_ᴱ : Ctx → Ctx
[] ᴱ        = []
(Γ ∷ A) ᴱ   = ᴱ-∷ (Γ ᴱ) A (eternal? A)
(Γ ⟨ ρ ⟩) ᴱ = Γ ᴱ

infix 34 _ᴱ

-- An eternal variable of Γ occurs in the eternal restriction at grade `uᵣ`.

∈-ᴱ : ∀ {Γ A ρ} → Eternal A → A ∈[ ρ ] Γ → A ∈[ uᵣ ] Γ ᴱ
∈-ᴱ {Γ ∷ A} et Hd       with eternal? A
... | yes _  = Hd
... | no ¬et = ⊥-elim (¬et et)
∈-ᴱ {Γ ∷ B} et (Tl-∷ x) with eternal? B
... | yes _  = Tl-∷ (∈-ᴱ et x)
... | no  _  = ∈-ᴱ et x
∈-ᴱ {Γ ⟨ ρ ⟩} et (Tl-⟨⟩ x) = ∈-ᴱ et x

-- The eternal restriction is a homomorphism for context concatenation.

ᴱ-++ᶜ : (Γ Γ' : Ctx) → (Γ ++ᶜ Γ') ᴱ ≡ Γ ᴱ ++ᶜ Γ' ᴱ
ᴱ-++ᶜ Γ []          = refl
ᴱ-++ᶜ Γ (Γ' ∷ A)    with eternal? A
... | yes _ = cong (_∷ A) (ᴱ-++ᶜ Γ Γ')
... | no  _ = ᴱ-++ᶜ Γ Γ'
ᴱ-++ᶜ Γ (Γ' ⟨ ρ ⟩)  = ᴱ-++ᶜ Γ Γ'

-- The same for the ambient join. Recursion on the ambient, so at the empty one
-- this is `refl` and the transports it justifies compute away.

ᴱ-⋈ᶜ : (Ξ Δ : Ctx) → (Ξ ⋈ᶜ Δ) ᴱ ≡ (Ξ ᴱ) ⋈ᶜ (Δ ᴱ)
ᴱ-⋈ᶜ []        Δ = refl
ᴱ-⋈ᶜ (Ξ ∷ A)   Δ =
  trans (ᴱ-++ᶜ (Ξ ∷ A) Δ) (sym (⋈ᶜ-++ᶜ ((Ξ ∷ A) ᴱ) (Δ ᴱ)))
ᴱ-⋈ᶜ (Ξ ⟨ ρ ⟩) Δ =
  trans (ᴱ-++ᶜ (Ξ ⟨ ρ ⟩) Δ) (sym (⋈ᶜ-++ᶜ ((Ξ ⟨ ρ ⟩) ᴱ) (Δ ᴱ)))

-- A variable of the local part is one of the join. At the empty ambient this is
-- the identity, definitionally, which is what keeps the derived renamings there
-- transport-free.

∈-⋈ᶜ : ∀ {Δ A ρ} → (Ξ : Ctx) → A ∈[ ρ ] Δ → A ∈[ ρ ] (Ξ ⋈ᶜ Δ)
∈-⋈ᶜ []        x = x
∈-⋈ᶜ (Ξ ∷ A)   x = ∈-ctx-extensionˡ (Ξ ∷ A) _ x
∈-⋈ᶜ (Ξ ⟨ ρ ⟩) x = ∈-ctx-extensionˡ (Ξ ⟨ ρ ⟩) _ x

-- Reassociating a prefix of the ambient into the local part.

⋈ᶜ-assoc : (Ξ Δ Δ₀ : Ctx) → (Ξ ⋈ᶜ Δ) ⋈ᶜ Δ₀ ≡ Ξ ⋈ᶜ (Δ ++ᶜ Δ₀)
⋈ᶜ-assoc []        Δ Δ₀ = ⋈ᶜ-++ᶜ Δ Δ₀
⋈ᶜ-assoc (Ξ ∷ A)   Δ Δ₀ =
  trans (⋈ᶜ-++ᶜ ((Ξ ∷ A) ++ᶜ Δ) Δ₀) (++ᶜ-assoc (Ξ ∷ A) Δ Δ₀)
⋈ᶜ-assoc (Ξ ⟨ ρ ⟩) Δ Δ₀ =
  trans (⋈ᶜ-++ᶜ ((Ξ ⟨ ρ ⟩) ++ᶜ Δ) Δ₀) (++ᶜ-assoc (Ξ ⟨ ρ ⟩) Δ Δ₀)

-- Restriction drops a non-eternal variable extension.

ᴱ-∷-drop : ∀ {Γ A} → ¬ Eternal A → (Γ ∷ A) ᴱ ≡ Γ ᴱ
ᴱ-∷-drop {A = A} ¬et with eternal? A
... | yes et = ⊥-elim (¬et et)
... | no  _  = refl

-- Restriction keeps an eternal variable extension.

ᴱ-∷-keep : ∀ {Γ A} → Eternal A → (Γ ∷ A) ᴱ ≡ Γ ᴱ ∷ A
ᴱ-∷-keep {A = A} et with eternal? A
... | yes _  = refl
... | no ¬et = ⊥-elim (¬et et)

-- The eternal restriction is idempotent: `Γ ᴱ` is already lock-free with only
-- eternal variables, so restricting it again changes nothing.

ᴱ-idem : (Γ : Ctx) → (Γ ᴱ) ᴱ ≡ Γ ᴱ
ᴱ-idem []        = refl
ᴱ-idem (Γ ∷ A)   with eternal? A
... | yes et rewrite ᴱ-∷-keep {Γ ᴱ} et = cong (_∷ A) (ᴱ-idem Γ)
... | no  _ = ᴱ-idem Γ
ᴱ-idem (Γ ⟨ ρ ⟩) = ᴱ-idem Γ

-- Appending a context on the right of a split.

split-++ʳ : ∀ {Γ Γ₁ Γ₂} → Γ₁ , Γ₂ split Γ → (D : Ctx) → Γ₁ , Γ₂ ++ᶜ D split (Γ ++ᶜ D)
split-++ʳ s []        = s
split-++ʳ s (D ∷ B)   = split-∷ (split-++ʳ s D)
split-++ʳ s (D ⟨ ρ ⟩) = split-⟨⟩ (split-++ʳ s D)

-- Restricting a splitting at an eternal entry: the entry survives, and the two
-- halves become their own eternal restrictions. A lock contributes nothing, and
-- a non-eternal binder drops out of the suffix.

∈-ᴱ-split : ∀ {Γ Γ₁ Γ₂ A} → (et : Eternal A) → (s : Γ₁ ∷ A , Γ₂ split Γ)
          → Γ₁ ᴱ ∷ A , Γ₂ ᴱ split (Γ ᴱ)
∈-ᴱ-split {A = A} et split-[] with eternal? A
... | yes _  = split-[]
... | no ¬et = ⊥-elim (¬et et)
∈-ᴱ-split et (split-∷ {A = B} s) with eternal? B
... | yes _  = split-∷ (∈-ᴱ-split et s)
... | no  _  = ∈-ᴱ-split et s
∈-ᴱ-split et (split-⟨⟩ s) = ∈-ᴱ-split et s

-- The variable a split points at. Its two halves are read back by
-- `split→∈-split-l`/`-r` (Σ-eta makes `split-l`/`split-r` commute through the
-- `Tl` wrappers), so it can be substituted into by `_[_↦_]c`.

split→∈ : ∀ {Γ Γ₁ Γ₂ A} → Γ₁ ∷ A , Γ₂ split Γ → A ∈[ ctx-grade Γ₂ ] Γ
split→∈ split-[]     = Hd
split→∈ (split-∷ s)  = Tl-∷ (split→∈ s)
split→∈ (split-⟨⟩ s) = Tl-⟨⟩ (split→∈ s)

split→∈-split-l : ∀ {Γ Γ₁ Γ₂ A} → (s : Γ₁ ∷ A , Γ₂ split Γ)
                → split-l (split→∈ s) ≡ Γ₁
split→∈-split-l split-[]     = refl
split→∈-split-l (split-∷ s)  = split→∈-split-l s
split→∈-split-l (split-⟨⟩ s) = split→∈-split-l s

split→∈-split-r : ∀ {Γ Γ₁ Γ₂ A} → (s : Γ₁ ∷ A , Γ₂ split Γ)
                → split-r (split→∈ s) ≡ Γ₂
split→∈-split-r split-[]              = refl
split→∈-split-r (split-∷ {A = B} s)   = cong (_∷ B) (split→∈-split-r s)
split→∈-split-r (split-⟨⟩ {ρ = ρ} s)  = cong (_⟨ ρ ⟩) (split→∈-split-r s)

-- When the split variable is *not* eternal, the eternal restriction is
-- unchanged by removing it, i.e. it is the restriction of the two halves.

ᴱ-drop-split : ∀ {Γ Γ₁ Γ₂ A} → ¬ Eternal A → (s : Γ₁ ∷ A , Γ₂ split Γ)
             → Γ ᴱ ≡ (Γ₁ ++ᶜ Γ₂) ᴱ
ᴱ-drop-split {Γ₁ = Γ₁} {Γ₂} {A} ¬et s =
  trans (cong _ᴱ (sym (split-≡ s)))
    (trans (ᴱ-++ᶜ (Γ₁ ∷ A) Γ₂)
      (trans (cong (_++ᶜ Γ₂ ᴱ) (ᴱ-∷-drop {Γ₁} {A} ¬et))
        (sym (ᴱ-++ᶜ Γ₁ Γ₂))))
