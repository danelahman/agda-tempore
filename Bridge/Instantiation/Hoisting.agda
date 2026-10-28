------------------------------------------------------------------
-- Comparisons hoisted out of values                            --
--                                                              --
-- A comparison is a value of the open calculus and a           --
-- computation of the closed one. Instantiation hoists each     --
-- comparison of a computation's values to just before that     --
-- computation, `cmp ⋈ V W` binding its outcome as `_⨟_` binds, --
-- and the value reads the outcome off the bound variable. The  --
-- closed side of this: maps `Γ ≼ Δ` of a context into one with --
-- bound outcomes interleaved, telescopes `Tel Δ Δ'` of hoisted --
-- comparisons, run before a computation by `wrap`, and the     --
-- outcome variables of a value's comparisons (`Envᶜ`); each    --
-- with its raw counterpart, and erasure commuting with them.   --
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Grades.Base
open import Language.Spec
open import Language.Comparisons using (Cmp)

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module Bridge.Instantiation.Hoisting (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Language.Types                  S
open import ClosedCalculus.Syntax.Contexts  S
open import ClosedCalculus.Syntax.Terms     S
open import ClosedCalculus.Syntax.Erasure   S hiding (⌊_⌋ᵛ; ⌊_⌋ᶜ)
import ClosedCalculus.Syntax.Erasure S as CE

open import OpenCalculus.Syntax.Raw S
  using (RawV; succ; ⦉_,_⦊; inl; inr; cons; cmp; _⦂ᵛ_)

------------------------------------------------------------------------
-- Maps of contexts

-- A context extended by the outcome of a comparison, bound as `_⨟_`
-- binds the result of a pure computation

_▷ᵇ : Ctx → Ctx
Δ ▷ᵇ = Δ ⟨ mapᵉ uₑ ⟩ ∷ Bool

infixl 31 _▷ᵇ

-- `Γ ≼ Δ`: the variables of `Γ` among those of `Δ`, which has bound
-- outcomes interleaved. `≼-drop` forgets a lock, which only a variable
-- of eternal type may cross.

data _≼_ : Ctx → Ctx → Set where
  ≼-refl : ∀ {Γ} → Γ ≼ Γ
  ≼-∷    : ∀ {Γ Δ A} → Γ ≼ Δ → Γ ∷ A ≼ Δ ∷ A
  ≼-⟨⟩   : ∀ {Γ Δ ρ} → Γ ≼ Δ → Γ ⟨ ρ ⟩ ≼ Δ ⟨ ρ ⟩
  ≼-▷    : ∀ {Γ Δ} → Γ ≼ Δ → Γ ≼ Δ ▷ᵇ
  ≼-drop : ∀ {Γ Δ ρ} → Γ ≼ Δ → Γ ⟨ ρ ⟩ ≼ Δ

infix 4 _≼_

-- A map forgetting no lock

Full : ∀ {Γ Δ} → Γ ≼ Δ → Set
Full ≼-refl     = ⊤
Full (≼-∷ ι)    = Full ι
Full (≼-⟨⟩ ι)   = Full ι
Full (≼-▷ ι)    = Full ι
Full (≼-drop ι) = ⊥

-- A variable through a map forgetting no lock, at a grade below its own

look : ∀ {Γ Δ A ρ} → (ι : Γ ≼ Δ) → Full ι → A ∈[ ρ ] Γ
     → Σ[ ρ' ∈ R ] (A ∈[ ρ' ] Δ × ρ' ≾ᵣ ρ)
look ≼-refl  f x         = _ , x , ≾ᵣ-refl
look (≼-∷ ι) f Hd        = _ , Hd , ≾ᵣ-refl
look (≼-∷ ι) f (Tl-∷ x)  = proj₁ l , Tl-∷ (proj₁ (proj₂ l)) , proj₂ (proj₂ l)
  where l = look ι f x
look (≼-⟨⟩ ι) f (Tl-⟨⟩ x) =
  proj₁ l ·ᵣ _ , Tl-⟨⟩ (proj₁ (proj₂ l)) , ·ᵣ-monoˡ-≾ᵣ (proj₂ (proj₂ l))
  where l = look ι f x
look (≼-▷ ι) f x =
  proj₁ l ·ᵣ mapᵉ uₑ , Tl-∷ (Tl-⟨⟩ (proj₁ (proj₂ l))) ,
  ≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ (≃ᵣ⇒≾ᵣ map-uᵉ))
    (≾ᵣ-trans (≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ (proj₁ l))) (proj₂ (proj₂ l)))
  where l = look ι f x

-- A variable through any map, its grade not tracked: what a variable of
-- eternal type needs

lookᴱ : ∀ {Γ Δ A ρ} → Γ ≼ Δ → A ∈[ ρ ] Γ → Σ[ ρ' ∈ R ] (A ∈[ ρ' ] Δ)
lookᴱ ≼-refl     x         = _ , x
lookᴱ (≼-∷ ι)    Hd        = _ , Hd
lookᴱ (≼-∷ ι)    (Tl-∷ x)  = _ , Tl-∷ (proj₂ (lookᴱ ι x))
lookᴱ (≼-⟨⟩ ι)   (Tl-⟨⟩ x) = _ , Tl-⟨⟩ (proj₂ (lookᴱ ι x))
lookᴱ (≼-▷ ι)    x         = _ , Tl-∷ (Tl-⟨⟩ (proj₂ (lookᴱ ι x)))
lookᴱ (≼-drop ι) (Tl-⟨⟩ x) = lookᴱ ι x

-- Raw maps: positions of variables, locks counting for nothing

data RMap : Set where
  idᴿ  : RMap
  extᴿ : RMap → RMap
  shᴿ  : RMap → RMap

posᴿ : RMap → ℕ → ℕ
posᴿ idᴿ      n       = n
posᴿ (extᴿ r) zero    = zero
posᴿ (extᴿ r) (suc n) = suc (posᴿ r n)
posᴿ (shᴿ r)  n       = suc (posᴿ r n)

⌊_⌋ᵐ : ∀ {Γ Δ} → Γ ≼ Δ → RMap
⌊ ≼-refl ⌋ᵐ   = idᴿ
⌊ ≼-∷ ι ⌋ᵐ    = extᴿ ⌊ ι ⌋ᵐ
⌊ ≼-⟨⟩ ι ⌋ᵐ   = ⌊ ι ⌋ᵐ
⌊ ≼-▷ ι ⌋ᵐ    = shᴿ ⌊ ι ⌋ᵐ
⌊ ≼-drop ι ⌋ᵐ = ⌊ ι ⌋ᵐ

look-pos : ∀ {Γ Δ A ρ} → (ι : Γ ≼ Δ) → (f : Full ι) → (x : A ∈[ ρ ] Γ)
         → var-pos (proj₁ (proj₂ (look ι f x))) ≡ posᴿ ⌊ ι ⌋ᵐ (var-pos x)
look-pos ≼-refl   f x         = refl
look-pos (≼-∷ ι)  f Hd        = refl
look-pos (≼-∷ ι)  f (Tl-∷ x)  = cong suc (look-pos ι f x)
look-pos (≼-⟨⟩ ι) f (Tl-⟨⟩ x) = look-pos ι f x
look-pos (≼-▷ ι)  f x         = cong suc (look-pos ι f x)

lookᴱ-pos : ∀ {Γ Δ A ρ} → (ι : Γ ≼ Δ) → (x : A ∈[ ρ ] Γ)
          → var-pos (proj₂ (lookᴱ ι x)) ≡ posᴿ ⌊ ι ⌋ᵐ (var-pos x)
lookᴱ-pos ≼-refl     x         = refl
lookᴱ-pos (≼-∷ ι)    Hd        = refl
lookᴱ-pos (≼-∷ ι)    (Tl-∷ x)  = cong suc (lookᴱ-pos ι x)
lookᴱ-pos (≼-⟨⟩ ι)   (Tl-⟨⟩ x) = lookᴱ-pos ι x
lookᴱ-pos (≼-▷ ι)    x         = cong suc (lookᴱ-pos ι x)
lookᴱ-pos (≼-drop ι) (Tl-⟨⟩ x) = lookᴱ-pos ι x

-- A map transported along an equation of its source

Full-subst : ∀ {Γ Γ' Δ} → (e : Γ ≡ Γ') → (ι : Γ ≼ Δ) → Full ι → Full (subst (_≼ Δ) e ι)
Full-subst refl ι f = f

⌊subst⌋ᵐ : ∀ {Γ Γ' Δ} → (e : Γ ≡ Γ') → (ι : Γ ≼ Δ) → ⌊ subst (_≼ Δ) e ι ⌋ᵐ ≡ ⌊ ι ⌋ᵐ
⌊subst⌋ᵐ refl ι = refl

------------------------------------------------------------------------
-- Telescopes of hoisted comparisons

record Cmpᶜ (Δ : Ctx) : Set where
  constructor cmpᶜ
  field
    {B}   : VType
    rel   : Cmp
    left  : Δ ⊢V⦂ B
    right : Δ ⊢V⦂ B
    et    : Eternal B

data Tel (Δ : Ctx) : Ctx → Set where
  []  : Tel Δ Δ
  _▷_ : ∀ {Δ'} → Tel Δ Δ' → Cmpᶜ Δ' → Tel Δ (Δ' ▷ᵇ)

infixl 5 _▷_

_++ᵀ_ : ∀ {Δ Δ' Δ''} → Tel Δ Δ' → Tel Δ' Δ'' → Tel Δ Δ''
T ++ᵀ []       = T
T ++ᵀ (T' ▷ c) = (T ++ᵀ T') ▷ c

infixl 6 _++ᵀ_

-- A map extended along a telescope

_⊕_ : ∀ {Γ Δ Δ'} → Γ ≼ Δ → Tel Δ Δ' → Γ ≼ Δ'
ι ⊕ []      = ι
ι ⊕ (T ▷ c) = ≼-▷ (ι ⊕ T)

infixl 6 _⊕_

Full-⊕ : ∀ {Γ Δ Δ'} → (ι : Γ ≼ Δ) → (T : Tel Δ Δ') → Full ι → Full (ι ⊕ T)
Full-⊕ ι []      f = f
Full-⊕ ι (T ▷ c) f = Full-⊕ ι T f

-- The comparisons of a telescope run in turn, each outcome bound for the
-- rest, before a computation; each binding is pure, so the type is kept

wrap : ∀ {Δ Δ' C} → Tel Δ Δ' → Δ' ⊢C⦂ C → Δ ⊢C⦂ C
wrap []                                    M = M
wrap {C = B ‼ ε} (T ▷ cmpᶜ ⋈ V W et) M =
  wrap T (coerce (≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)) (cmp ⋈ V W et ⨟ M))

-- Raw telescopes

data RCmp : Set where
  cmpᴿ : Cmp → ErV → ErV → RCmp

data RTel : Set where
  []  : RTel
  _▷_ : RTel → RCmp → RTel

_++ᴿ_ : RTel → RTel → RTel
T ++ᴿ []       = T
T ++ᴿ (T' ▷ c) = (T ++ᴿ T') ▷ c

infixl 6 _++ᴿ_

_⊕ᴿ_ : RMap → RTel → RMap
r ⊕ᴿ []      = r
r ⊕ᴿ (T ▷ c) = shᴿ (r ⊕ᴿ T)

infixl 6 _⊕ᴿ_

wrapᴿ : RTel → ErC → ErC
wrapᴿ []                     M = M
wrapᴿ (T ▷ cmpᴿ ⋈ V W) M = wrapᴿ T (cmp ⋈ V W ⨟ M)

⌊_⌋ᵀ : ∀ {Δ Δ'} → Tel Δ Δ' → RTel
⌊ [] ⌋ᵀ                 = []
⌊ T ▷ cmpᶜ ⋈ V W et ⌋ᵀ = ⌊ T ⌋ᵀ ▷ cmpᴿ ⋈ CE.⌊ V ⌋ᵛ CE.⌊ W ⌋ᵛ

-- Erasure commutes with the operations on telescopes

⌊++⌋ᵀ : ∀ {Δ Δ' Δ''} → (T : Tel Δ Δ') → (T' : Tel Δ' Δ'')
      → ⌊ T ++ᵀ T' ⌋ᵀ ≡ ⌊ T ⌋ᵀ ++ᴿ ⌊ T' ⌋ᵀ
⌊++⌋ᵀ T []                   = refl
⌊++⌋ᵀ T (T' ▷ cmpᶜ ⋈ V W et) = cong (_▷ cmpᴿ ⋈ CE.⌊ V ⌋ᵛ CE.⌊ W ⌋ᵛ) (⌊++⌋ᵀ T T')

⌊⊕⌋ᵐ : ∀ {Γ Δ Δ'} → (ι : Γ ≼ Δ) → (T : Tel Δ Δ') → ⌊ ι ⊕ T ⌋ᵐ ≡ ⌊ ι ⌋ᵐ ⊕ᴿ ⌊ T ⌋ᵀ
⌊⊕⌋ᵐ ι []                   = refl
⌊⊕⌋ᵐ ι (T ▷ cmpᶜ ⋈ V W et) = cong shᴿ (⌊⊕⌋ᵐ ι T)

⌊wrap⌋ : ∀ {Δ Δ' C} → (T : Tel Δ Δ') → (M : Δ' ⊢C⦂ C)
       → CE.⌊ wrap T M ⌋ᶜ ≡ wrapᴿ ⌊ T ⌋ᵀ CE.⌊ M ⌋ᶜ
⌊wrap⌋                   []                   M = refl
⌊wrap⌋ {C = B ‼ ε} (T ▷ cmpᶜ ⋈ V W et) M = ⌊wrap⌋ T _

------------------------------------------------------------------------
-- The outcomes of the comparisons of a value, one variable for each
-- comparison outside the value's functions

Envᶜ : ∀ {Θ n} → Ctx → RawV Θ n → Set
Envᶜ Δ (cmp ⋈ V W) = Σ[ ρ ∈ R ] (Bool ∈[ ρ ] Δ)
Envᶜ Δ (succ V)    = Envᶜ Δ V
Envᶜ Δ ⦉ V , W ⦊    = Envᶜ Δ V × Envᶜ Δ W
Envᶜ Δ (inl V)     = Envᶜ Δ V
Envᶜ Δ (inr V)     = Envᶜ Δ V
Envᶜ Δ (cons V W)  = Envᶜ Δ V × Envᶜ Δ W
Envᶜ Δ (V ⦂ᵛ A)    = Envᶜ Δ V
Envᶜ Δ _           = ⊤

-- under one more outcome

wk▷ : ∀ {Θ n Δ} → (V : RawV Θ n) → Envᶜ Δ V → Envᶜ (Δ ▷ᵇ) V
wk▷ (cmp ⋈ V W) (ρ , x)    = _ , Tl-∷ (Tl-⟨⟩ x)
wk▷ (succ V)    e          = wk▷ V e
wk▷ ⦉ V , W ⦊    (e₁ , e₂)  = wk▷ V e₁ , wk▷ W e₂
wk▷ (inl V)     e          = wk▷ V e
wk▷ (inr V)     e          = wk▷ V e
wk▷ (cons V W)  (e₁ , e₂)  = wk▷ V e₁ , wk▷ W e₂
wk▷ (V ⦂ᵛ A)    e          = wk▷ V e
wk▷ (RawV.var i)        e  = tt
wk▷ (RawV.const B c)    e  = tt
wk▷ RawV.⋆              e  = tt
wk▷ RawV.true           e  = tt
wk▷ RawV.false          e  = tt
wk▷ RawV.zero           e  = tt
wk▷ RawV.nil            e  = tt
wk▷ (RawV.lam M)        e  = tt

-- along a telescope

wkᵀ : ∀ {Θ n Δ Δ'} → (V : RawV Θ n) → Tel Δ Δ' → Envᶜ Δ V → Envᶜ Δ' V
wkᵀ V []      e = e
wkᵀ V (T ▷ c) e = wk▷ V (wkᵀ V T e)

-- under a lock

lockᴱ : ∀ {Θ n Δ ρ} → (V : RawV Θ n) → Envᶜ Δ V → Envᶜ (Δ ⟨ ρ ⟩) V
lockᴱ (cmp ⋈ V W) (ρ , x)    = _ , Tl-⟨⟩ x
lockᴱ (succ V)    e          = lockᴱ V e
lockᴱ ⦉ V , W ⦊    (e₁ , e₂)  = lockᴱ V e₁ , lockᴱ W e₂
lockᴱ (inl V)     e          = lockᴱ V e
lockᴱ (inr V)     e          = lockᴱ V e
lockᴱ (cons V W)  (e₁ , e₂)  = lockᴱ V e₁ , lockᴱ W e₂
lockᴱ (V ⦂ᵛ A)    e          = lockᴱ V e
lockᴱ (RawV.var i)        e  = tt
lockᴱ (RawV.const B c)    e  = tt
lockᴱ RawV.⋆              e  = tt
lockᴱ RawV.true           e  = tt
lockᴱ RawV.false          e  = tt
lockᴱ RawV.zero           e  = tt
lockᴱ RawV.nil            e  = tt
lockᴱ (RawV.lam M)        e  = tt

-- Raw outcomes: the positions of the variables

data Envᴿ : Set where
  ∅ᴿ   : Envᴿ
  outᴿ : ℕ → Envᴿ
  _⊗ᴿ_ : Envᴿ → Envᴿ → Envᴿ

leftᴱ : Envᴿ → Envᴿ
leftᴱ (e ⊗ᴿ e') = e
leftᴱ _         = ∅ᴿ

rightᴱ : Envᴿ → Envᴿ
rightᴱ (e ⊗ᴿ e') = e'
rightᴱ _         = ∅ᴿ

⌊_⌋ᴱ : ∀ {Θ n Δ} → (V : RawV Θ n) → Envᶜ Δ V → Envᴿ
⌊ cmp ⋈ V W ⌋ᴱ (ρ , x)    = outᴿ (var-pos x)
⌊ succ V ⌋ᴱ    e          = ⌊ V ⌋ᴱ e
⌊ ⦉ V , W ⦊ ⌋ᴱ  (e₁ , e₂)  = ⌊ V ⌋ᴱ e₁ ⊗ᴿ ⌊ W ⌋ᴱ e₂
⌊ inl V ⌋ᴱ     e          = ⌊ V ⌋ᴱ e
⌊ inr V ⌋ᴱ     e          = ⌊ V ⌋ᴱ e
⌊ cons V W ⌋ᴱ  (e₁ , e₂)  = ⌊ V ⌋ᴱ e₁ ⊗ᴿ ⌊ W ⌋ᴱ e₂
⌊ V ⦂ᵛ A ⌋ᴱ    e          = ⌊ V ⌋ᴱ e
⌊ RawV.var i ⌋ᴱ        e  = ∅ᴿ
⌊ RawV.const B c ⌋ᴱ    e  = ∅ᴿ
⌊ RawV.⋆ ⌋ᴱ            e  = ∅ᴿ
⌊ RawV.true ⌋ᴱ         e  = ∅ᴿ
⌊ RawV.false ⌋ᴱ        e  = ∅ᴿ
⌊ RawV.zero ⌋ᴱ         e  = ∅ᴿ
⌊ RawV.nil ⌋ᴱ          e  = ∅ᴿ
⌊ RawV.lam M ⌋ᴱ        e  = ∅ᴿ

shᴱ : Envᴿ → Envᴿ
shᴱ ∅ᴿ        = ∅ᴿ
shᴱ (outᴿ k)  = outᴿ (suc k)
shᴱ (e ⊗ᴿ e') = shᴱ e ⊗ᴿ shᴱ e'

wkᴿ : RTel → Envᴿ → Envᴿ
wkᴿ []      e = e
wkᴿ (T ▷ c) e = shᴱ (wkᴿ T e)

-- Erasure commutes with weakening and locking

⌊wk▷⌋ : ∀ {Θ n Δ} → (V : RawV Θ n) → (e : Envᶜ Δ V) → ⌊ V ⌋ᴱ (wk▷ V e) ≡ shᴱ (⌊ V ⌋ᴱ e)
⌊wk▷⌋ (cmp ⋈ V W) (ρ , x)    = refl
⌊wk▷⌋ (succ V)    e          = ⌊wk▷⌋ V e
⌊wk▷⌋ ⦉ V , W ⦊    (e₁ , e₂)  = cong₂ _⊗ᴿ_ (⌊wk▷⌋ V e₁) (⌊wk▷⌋ W e₂)
⌊wk▷⌋ (inl V)     e          = ⌊wk▷⌋ V e
⌊wk▷⌋ (inr V)     e          = ⌊wk▷⌋ V e
⌊wk▷⌋ (cons V W)  (e₁ , e₂)  = cong₂ _⊗ᴿ_ (⌊wk▷⌋ V e₁) (⌊wk▷⌋ W e₂)
⌊wk▷⌋ (V ⦂ᵛ A)    e          = ⌊wk▷⌋ V e
⌊wk▷⌋ (RawV.var i)        e  = refl
⌊wk▷⌋ (RawV.const B c)    e  = refl
⌊wk▷⌋ RawV.⋆              e  = refl
⌊wk▷⌋ RawV.true           e  = refl
⌊wk▷⌋ RawV.false          e  = refl
⌊wk▷⌋ RawV.zero           e  = refl
⌊wk▷⌋ RawV.nil            e  = refl
⌊wk▷⌋ (RawV.lam M)        e  = refl

⌊wkᵀ⌋ : ∀ {Θ n Δ Δ'} → (V : RawV Θ n) → (T : Tel Δ Δ') → (e : Envᶜ Δ V)
      → ⌊ V ⌋ᴱ (wkᵀ V T e) ≡ wkᴿ ⌊ T ⌋ᵀ (⌊ V ⌋ᴱ e)
⌊wkᵀ⌋ V []                   e = refl
⌊wkᵀ⌋ V (T ▷ cmpᶜ ⋈ A B et) e = trans (⌊wk▷⌋ V (wkᵀ V T e)) (cong shᴱ (⌊wkᵀ⌋ V T e))

⌊lockᴱ⌋ : ∀ {Θ n Δ ρ} → (V : RawV Θ n) → (e : Envᶜ Δ V)
        → ⌊ V ⌋ᴱ (lockᴱ {ρ = ρ} V e) ≡ ⌊ V ⌋ᴱ e
⌊lockᴱ⌋ (cmp ⋈ V W) (ρ , x)    = refl
⌊lockᴱ⌋ (succ V)    e          = ⌊lockᴱ⌋ V e
⌊lockᴱ⌋ ⦉ V , W ⦊    (e₁ , e₂)  = cong₂ _⊗ᴿ_ (⌊lockᴱ⌋ V e₁) (⌊lockᴱ⌋ W e₂)
⌊lockᴱ⌋ (inl V)     e          = ⌊lockᴱ⌋ V e
⌊lockᴱ⌋ (inr V)     e          = ⌊lockᴱ⌋ V e
⌊lockᴱ⌋ (cons V W)  (e₁ , e₂)  = cong₂ _⊗ᴿ_ (⌊lockᴱ⌋ V e₁) (⌊lockᴱ⌋ W e₂)
⌊lockᴱ⌋ (V ⦂ᵛ A)    e          = ⌊lockᴱ⌋ V e
⌊lockᴱ⌋ (RawV.var i)        e  = refl
⌊lockᴱ⌋ (RawV.const B c)    e  = refl
⌊lockᴱ⌋ RawV.⋆              e  = refl
⌊lockᴱ⌋ RawV.true           e  = refl
⌊lockᴱ⌋ RawV.false          e  = refl
⌊lockᴱ⌋ RawV.zero           e  = refl
⌊lockᴱ⌋ RawV.nil            e  = refl
⌊lockᴱ⌋ (RawV.lam M)        e  = refl

------------------------------------------------------------------------
-- The comparisons hoisted from a value: a telescope, and the outcome
-- variables at its end

record Hoisted {Θ n} (Δ : Ctx) (V : RawV Θ n) : Set where
  constructor hoisted
  field
    {end} : Ctx
    tel   : Tel Δ end
    env   : Envᶜ end V

open Hoisted public

⌊_⌋ʰ : ∀ {Θ n Δ} {V : RawV Θ n} → Hoisted Δ V → RTel × Envᴿ
⌊_⌋ʰ {V = V} h = ⌊ tel h ⌋ᵀ , ⌊ V ⌋ᴱ (env h)
