-----------------------------------
-- Operational Semantics' States --
-----------------------------------

open import Data.Empty
open import Data.Product

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

module OperationalSemantics.State (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.RenActions S
open import Syntax.Renamings  S
open import Syntax.Types      S

-- Definition of state

mutual
  data 𝕊 (Γ : Ctx) : Set where
    ∅     : 𝕊 Γ
    _⟨_⟩ₛ : 𝕊 Γ → (ρ : R) → 𝕊 Γ  
    _∷ₛ_  : ∀ {A ρ} → (S : 𝕊 Γ) → ((Γ ++ᶜ (toCtx S) ⟨ ρ ⟩) ⊢V⦂ A) → 𝕊 Γ

  toCtx : ∀ {Γ} → 𝕊 Γ → Ctx
  toCtx ∅ = []
  toCtx (S ⟨ ρ ⟩ₛ) = (toCtx S) ⟨ ρ ⟩
  toCtx (_∷ₛ_ {A} {ρ} S V) = (toCtx S ∷ [ ρ ] A)

  infixl 31 _∷ₛ_
  infix  32 _⟨_⟩ₛ

-- Operations on state - for better readability in preservation theorem

grade-pass : ∀ {Γ} → (S : 𝕊 Γ) → (ρ : R) → 𝕊 Γ
grade-pass S ρ = S ⟨ ρ ⟩ₛ 

extend-state : ∀ {Γ A ρ} → (S : 𝕊 Γ) → ((Γ ++ᶜ (toCtx S) ⟨ ρ ⟩) ⊢V⦂ A) → 𝕊 Γ
extend-state S V = S ∷ₛ V 

-- Sum of the grade passings in the state

state-grade : ∀ {Γ} → (S : 𝕊 Γ) → R
state-grade ∅ = uᵣ
state-grade (S ⟨ ρ ⟩ₛ) = state-grade S ·ᵣ ρ
state-grade (S ∷ₛ A) = state-grade S

-- State grade is the same as the context grade of toCtx S 

grades-≡ : ∀ {Γ} → (S : 𝕊 Γ) → state-grade S ≡ ctx-grade (toCtx S)
grades-≡ ∅ = refl
grades-≡ (S ⟨ ρ ⟩ₛ) = cong (_·ᵣ ρ) (grades-≡ S)
grades-≡ (S ∷ₛ A) = grades-≡ S

-- A runtime context is built solely from locks and box-typed resources,
-- neither of which is eternal, so its eternal restriction is empty. Hence at
-- the top level a handler's eternal context is trivial: firing at `Γ' := toCtx S`
-- recovers `toCtx S ∷ param ∷ cont` (via `++ᶜ-identityˡ`).

toCtxᴱ-[] : ∀ {Γ} → (S : 𝕊 Γ) → (toCtx S) ᴱ ≡ []
toCtxᴱ-[] ∅            = refl
toCtxᴱ-[] (S ⟨ ρ ⟩ₛ)  = toCtxᴱ-[] S
toCtxᴱ-[] (_∷ₛ_ {A} {ρ} S V) =
  trans (ᴱ-∷-drop {Γ = toCtx S} {A = [ ρ ] A} (λ ())) (toCtxᴱ-[] S)

-- Definition of successor of a state

data _≤ₛ_ : ∀ {Γ Γ'} → 𝕊 Γ → 𝕊 Γ' → Set where
    id-suc : ∀ {Γ} 
            → {S : 𝕊 Γ} 
            -----------
            → S ≤ₛ S

    ⟨⟩-suc : ∀ {Γ Γ'}
            → {S : 𝕊 Γ} 
            → {S' : 𝕊 Γ'} 
            → (ρ'' : R)
            → S ≤ₛ S'
            --------------------------
            → S ≤ₛ (S' ⟨ ρ'' ⟩ₛ)

    ∷-suc : ∀ {Γ Γ' ρ A} 
            → {S : 𝕊 Γ} 
            → {S' : 𝕊 Γ'} 
            → (V : (Γ' ++ᶜ (toCtx S') ⟨ ρ ⟩) ⊢V⦂ A) 
            → S ≤ₛ S' 
            ---------------------------------------
            → S ≤ₛ (S' ∷ₛ V)

-- The grade δ accumulated when passing from a state 𝕊 to a successor state 𝕊',
-- i.e. the δ with state-grade S' ≡ state-grade S ·ᵣ δ (see state-grade-≤ₛ).

≤ₛ-grade : ∀ {Γ Γ'} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'} → S ≤ₛ S' → R
≤ₛ-grade id-suc       = uᵣ
≤ₛ-grade (⟨⟩-suc ρ q) = ≤ₛ-grade q ·ᵣ ρ
≤ₛ-grade (∷-suc V q)  = ≤ₛ-grade q

-- The overall grade of a successor state factors through ≤ₛ-grade.

state-grade-≤ₛ : ∀ {Γ Γ'} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'}
               → (q : S ≤ₛ S')
               → state-grade S' ≡ state-grade S ·ᵣ ≤ₛ-grade q
state-grade-≤ₛ {S = S} id-suc =
  sym (·ᵣ-identityʳ (state-grade S))
state-grade-≤ₛ {S = S} (⟨⟩-suc ρ q) =
  trans (cong (_·ᵣ ρ) (state-grade-≤ₛ q)) (·ᵣ-assoc (state-grade S) (≤ₛ-grade q) ρ)
state-grade-≤ₛ (∷-suc V q) =
  state-grade-≤ₛ q

-- If 𝕊' is a successor of 𝕊 and the grade δ it accumulated stays, together
-- with ρ''', below ρ'', then 𝕊' is a renaming of 𝕊.

suc-comp-ren : ∀ {Γ Γ'}
             → {ρ'' ρ''' : R}
             → {S : 𝕊 Γ}
             → {S' : 𝕊 Γ'}
             → (q : S ≤ₛ S')
             → ≤ₛ-grade q ·ᵣ ρ''' ≾ᵣ ρ''
             → Ren [] (toCtx S ⟨ ρ'' ⟩) (toCtx S' ⟨ ρ''' ⟩)

suc-comp-ren {ρ''' = ρ'''} id-suc δρ'''≾ρ'' =
  ⟨⟩-≤-ren (≾ᵣ-trans (≾ᵣ-reflexive (sym (·ᵣ-identityˡ ρ'''))) δρ'''≾ρ'')
suc-comp-ren {ρ''' = ρ'''} (⟨⟩-suc ρ q) δρ'''≾ρ'' =
  ⟨⟩-μ-ren ∘ʳ suc-comp-ren q (≾ᵣ-trans (≾ᵣ-reflexive (sym (·ᵣ-assoc (≤ₛ-grade q) ρ ρ'''))) δρ'''≾ρ'')
suc-comp-ren (∷-suc V q) δρ'''≾ρ'' =
  cong-⟨⟩-ren wk-ren ∘ʳ suc-comp-ren q δρ'''≾ρ''

-- The cancelled grade-decrease statement (about δ) implies the total one
-- (about the two states' grades), by monotonicity of _·ᵣ_.

cancelled⇒total : ∀ {Γ Γ'} → {a b : R} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'}
                → (q : S ≤ₛ S')
                → ≤ₛ-grade q ·ᵣ a ≾ᵣ b
                → state-grade S' ·ᵣ a ≾ᵣ state-grade S ·ᵣ b
cancelled⇒total {a = a} {S = S} q δa≾b =
  ≾ᵣ-trans
    (≾ᵣ-reflexive (trans (cong (_·ᵣ a) (state-grade-≤ₛ q)) (·ᵣ-assoc (state-grade S) (≤ₛ-grade q) a)))
    (·ᵣ-monoʳ-≾ᵣ δa≾b)

-- Concatenation/composition of states

mutual
  _++ˢ_ : ∀ {Γ} → (S : 𝕊 Γ) → (𝕊 (Γ ++ᶜ toCtx S)) → 𝕊 Γ
  S ++ˢ ∅ =
    S
  S ++ˢ (S' ⟨ ρ ⟩ₛ) =
    (S ++ˢ S') ⟨ ρ ⟩ₛ
  _++ˢ_ {Γ} S (_∷ₛ_ {ρ = ρ} S' V) =
    (S ++ˢ S') ∷ₛ
      V-rename
        (eq-ren
          (cong (_⟨ ρ ⟩) (trans (++ᶜ-assoc Γ (toCtx S) (toCtx S')) (cong (Γ ++ᶜ_) (sym (toCtx-++ˢ S S'))))))
        V

  infixl 30 _++ˢ_

  toCtx-++ˢ : ∀ {Γ}
            → (S : 𝕊 Γ)
            → (S' : 𝕊 (Γ ++ᶜ toCtx S))
            → toCtx (S ++ˢ S') ≡ toCtx S ++ᶜ toCtx S'
   
  toCtx-++ˢ S ∅ =
    refl
  toCtx-++ˢ S (S' ⟨ ρ ⟩ₛ) =
    cong (_⟨ ρ ⟩) (toCtx-++ˢ S S')
  toCtx-++ˢ S (_∷ₛ_ {A = A} {ρ = ρ} S' V) =
    cong (_∷ [ ρ ] A) (toCtx-++ˢ S S')

-- Splitting a state according to a variable/resource in it

mutual 

  split-state-fst : ∀ {Γ A ρ ρ'}
                  → (S : 𝕊 Γ)
                  → [ ρ ] A ∈[ ρ' ] (toCtx S)
                  → 𝕊 Γ
   
  split-state-fst (S ⟨ ρ'' ⟩ₛ) (Tl-⟨⟩ x) =
    split-state-fst S x
  split-state-fst (S ∷ₛ V) Hd =
    S
  split-state-fst (S ∷ₛ V) (Tl-∷ x) =
    split-state-fst S x

  split-state-snd : ∀ {Γ A ρ ρ'}
                  → (S : 𝕊 Γ)
                  → (x : [ ρ ] A ∈[ ρ' ] (toCtx S))
                   → 𝕊 (Γ ++ᶜ toCtx (split-state-fst S x) ∷ [ ρ ] A)
  
  split-state-snd (S ⟨ ρ ⟩ₛ) (Tl-⟨⟩ x) =
    split-state-snd S x ⟨ ρ ⟩ₛ
  split-state-snd (S ∷ₛ V) Hd =
    ∅
  split-state-snd {Γ} (_∷ₛ_ {ρ = ρ} S V) (Tl-∷ x) =
    split-state-snd S x ∷ₛ
    V-rename (eq-ren (cong (_⟨ ρ ⟩)
      (trans
        (sym (cong (Γ ++ᶜ_) (split-state-++ᶜ S x)))
        (sym (++ᶜ-assoc Γ _ (toCtx (split-state-snd S x)))))))
    V

  split-state-++ᶜ : ∀ {Γ A ρ ρ'}
                  → (S : 𝕊 Γ)
                  → (x : [ ρ ] A ∈[ ρ' ] (toCtx S))
                  → toCtx (split-state-fst S x) ∷ [ ρ ] A ++ᶜ toCtx (split-state-snd S x) ≡ toCtx S

  split-state-++ᶜ (S ⟨ ρ ⟩ₛ) (Tl-⟨⟩ x) =
    cong (_⟨ ρ ⟩) (split-state-++ᶜ S x)
  split-state-++ᶜ (_∷ₛ_ {A = A} {ρ = ρ} S V) Hd =
    refl
  split-state-++ᶜ (_∷ₛ_ {A = A} {ρ = ρ} S V) (Tl-∷ x) =
    cong (_∷ [ ρ ] A) (split-state-++ᶜ S x)

-- Relating the splitting of the state to the splitting of the corresponding context 

fst-split-state≡split-ctx : ∀ {Γ A ρ ρ'}
                  → (S : 𝕊 Γ)
                  → (x : [ ρ ] A ∈[ ρ' ] (toCtx S))
                  → toCtx (split-state-fst S x) ≡ split-l x
                  
fst-split-state≡split-ctx (S ⟨ ρ ⟩ₛ) (Tl-⟨⟩ x) = fst-split-state≡split-ctx S x
fst-split-state≡split-ctx (S ∷ₛ V) Hd          = refl
fst-split-state≡split-ctx (S ∷ₛ V) (Tl-∷ x)    = fst-split-state≡split-ctx S x

split-state≡split-ctx : ∀ {Γ A ρ ρ'}
                  → {S : 𝕊 Γ}
                  → {x : [ ρ ] A ∈[ ρ' ] (toCtx S)}
                  → toCtx (split-state-fst S x) ∷ [ ρ ] A ++ᶜ (toCtx (split-state-snd S x))  
                    ≡ 
                    split-l x ∷ [ ρ ] A ++ᶜ (split-r x)
                  
split-state≡split-ctx {S = S} {x = x} = 
  trans
    (split-state-++ᶜ S x) 
    (sym (split-≡ (split-pf x)))

snd-split-state≡split-ctx : ∀ {Γ A ρ ρ'}
                  → (S : 𝕊 Γ)
                  → (x : [ ρ ] A ∈[ ρ' ] (toCtx S))
                  → toCtx (split-state-snd S x) ≡ split-r x
                  
snd-split-state≡split-ctx {A = A} {ρ = ρ} S x = 
  ++ᶜ-inj₂ {Γ = toCtx (split-state-fst S x) ∷ [ ρ ] A}
    (trans
      split-state≡split-ctx
      (cong (_++ᶜ split-r x)
        (cong (_∷ [ ρ ] A) (sym (fst-split-state≡split-ctx S x)))))

snd-split-time≡time-from-head : ∀ {Γ A ρ ρ'}
                  → (S : 𝕊 Γ)
                  → (x : [ ρ ] A ∈[ ρ' ] (toCtx S))
                  → state-grade (split-state-snd S x) ≡ ρ'
                  
snd-split-time≡time-from-head S x = 
  trans (
    trans 
      (grades-≡ (split-state-snd S x)) 
      (cong ctx-grade (snd-split-state≡split-ctx S x))) 
    (split-grade-≡ x)

-- Lemmas about which values can and which can't be in toCtx S (only var can be)

⇒-not-in-toCtx : ∀ {Γ ρ} {S : 𝕊 Γ} {A : VType} {C : CType} → A ⇒ C ∈[ ρ ] toCtx S → ⊥
⇒-not-in-toCtx {S = S ⟨ ρ ⟩ₛ} (Tl-⟨⟩ x) = ⇒-not-in-toCtx x
⇒-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = ⇒-not-in-toCtx x

⦉⦊-not-in-toCtx : ∀ {Γ ρ} {S : 𝕊 Γ} {A B : VType} → A |×| B ∈[ ρ ] toCtx S → ⊥
⦉⦊-not-in-toCtx {S = S ⟨ ρ' ⟩ₛ} (Tl-⟨⟩ x) = ⦉⦊-not-in-toCtx x
⦉⦊-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = ⦉⦊-not-in-toCtx x

Empty-not-in-toCtx : ∀ {Γ ρ} {S : 𝕊 Γ} → Empty ∈[ ρ ] toCtx S → ⊥
Empty-not-in-toCtx {S = S ⟨ ρ' ⟩ₛ} (Tl-⟨⟩ x) = Empty-not-in-toCtx x
Empty-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = Empty-not-in-toCtx x

not-in-empty-ctx : {ρ : R} {A : VType} → A ∈[ ρ ] [] → ⊥
not-in-empty-ctx ()

-- Looking up a resource in the state

resource-lookup : ∀ {Γ ρ ρ' A}
                → (S : 𝕊 Γ)
                → (x : [ ρ ] A ∈[ ρ' ] toCtx S)
                → (Γ ++ᶜ toCtx (split-state-fst S x)) ⟨ ρ ⟩ ⊢V⦂ A
resource-lookup (S ⟨ _ ⟩ₛ) (Tl-⟨⟩ x) = resource-lookup S x
resource-lookup (S ∷ₛ V) Hd          = V
resource-lookup (S ∷ₛ _) (Tl-∷ x)    = resource-lookup S x

≤ₛ-comp : ∀ {Γ} → {S S' : 𝕊 Γ} → S ≤ₛ S' → Σ[ Γ' ∈ Ctx ] toCtx S' ≡ toCtx S ++ᶜ Γ'
≤ₛ-comp id-suc = [] , refl
≤ₛ-comp {S' = S' ⟨ ρ ⟩ₛ} (⟨⟩-suc .ρ S≤ₛS') with ≤ₛ-comp {S' = S'} S≤ₛS'
... | Γ' , eq =
  Γ' ⟨ ρ ⟩ , cong (_⟨ ρ ⟩) eq
≤ₛ-comp {S' = S' ∷ₛ V} (∷-suc .V S≤ₛS') with ≤ₛ-comp {S' = S'} S≤ₛS'
≤ₛ-comp {S = _} {_∷ₛ_ {A} {ρ} S' V} (∷-suc .V S≤ₛS') | Γ' , eq =
  Γ' ∷ [ ρ ] A , cong (_∷ [ ρ ] A) eq
