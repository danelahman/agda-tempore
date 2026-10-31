-----------------------------------
-- Operational Semantics' States --
-----------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.Bool.Base as Bool
import Data.List.Base as List

open import Grades.Base
open import Language.Spec

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.State (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Data            S using (⟪_⟫; ⟪_⟫ˢ)
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming.Action S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Types           S

-- Definition of state

mutual
  data State (Γ : Ctx) : Set where
    ∅     : State Γ
    _⟨_⟩ₛ : State Γ → (ρ : R) → State Γ  
    _∷ₛ_  : ∀ {A ρ} → (𝕊 : State Γ) → ((Γ ++ᶜ (toCtx 𝕊) ⟨ ρ ⟩) ⊢ᵛ⦂ A) → State Γ

  toCtx : ∀ {Γ} → State Γ → Ctx
  toCtx ∅ = []
  toCtx (𝕊 ⟨ ρ ⟩ₛ) = (toCtx 𝕊) ⟨ ρ ⟩
  toCtx (_∷ₛ_ {A} {ρ} 𝕊 V) = (toCtx 𝕊 ∷ [ ρ ] A)

  infixl 31 _∷ₛ_
  infix  32 _⟨_⟩ₛ

-- Named forms of the state constructors

grade-pass : ∀ {Γ} → (𝕊 : State Γ) → (ρ : R) → State Γ
grade-pass 𝕊 ρ = 𝕊 ⟨ ρ ⟩ₛ 

extend-state : ∀ {Γ A ρ} → (𝕊 : State Γ) → ((Γ ++ᶜ (toCtx 𝕊) ⟨ ρ ⟩) ⊢ᵛ⦂ A) → State Γ
extend-state 𝕊 V = 𝕊 ∷ₛ V 

-- Sum of the grade passings in the state

state-grade : ∀ {Γ} → (𝕊 : State Γ) → R
state-grade ∅ = 𝟏ᵣ
state-grade (𝕊 ⟨ ρ ⟩ₛ) = state-grade 𝕊 ·ᵣ ρ
state-grade (𝕊 ∷ₛ A) = state-grade 𝕊

-- State grade is the same as the context grade of toCtx 𝕊 

grades-≡ : ∀ {Γ} → (𝕊 : State Γ) → state-grade 𝕊 ≡ ctx-grade (toCtx 𝕊)
grades-≡ ∅ = refl
grades-≡ (𝕊 ⟨ ρ ⟩ₛ) = cong (_·ᵣ ρ) (grades-≡ 𝕊)
grades-≡ (𝕊 ∷ₛ A) = grades-≡ 𝕊

-- Definition of successor of a state

infix 4 _≤ₛ_

data _≤ₛ_ : ∀ {Γ Γ'} → State Γ → State Γ' → Set where
    ≤ₛ-refl : ∀ {Γ} 
            → {𝕊 : State Γ} 
            -----------
            → 𝕊 ≤ₛ 𝕊

    ≤ₛ-lock : ∀ {Γ Γ'}
            → {𝕊 : State Γ} 
            → {𝕊' : State Γ'} 
            → {ρ : R}
            → 𝕊 ≤ₛ 𝕊'
            --------------------------
            → 𝕊 ≤ₛ (𝕊' ⟨ ρ ⟩ₛ)

    ≤ₛ-res  : ∀ {Γ Γ' ρ A} 
            → {𝕊 : State Γ} 
            → {𝕊' : State Γ'} 
            → {V : (Γ' ++ᶜ (toCtx 𝕊') ⟨ ρ ⟩) ⊢ᵛ⦂ A} 
            → 𝕊 ≤ₛ 𝕊' 
            ---------------------------------------
            → 𝕊 ≤ₛ (𝕊' ∷ₛ V)

-- The grade δ accumulated when passing from a state 𝕊 to a successor state 𝕊':
-- state-grade 𝕊' ≃ᵣ state-grade 𝕊 ·ᵣ δ, by state-grade-≤ₛ.

κₛ : ∀ {Γ Γ'} → {𝕊 : State Γ} → {𝕊' : State Γ'} → 𝕊 ≤ₛ 𝕊' → R
κₛ ≤ₛ-refl             = 𝟏ᵣ
κₛ (≤ₛ-lock {ρ = ρ} q) = κₛ q ·ᵣ ρ
κₛ (≤ₛ-res q)          = κₛ q

-- The overall grade of a successor state factors through κₛ.

state-grade-≤ₛ : ∀ {Γ Γ'} → {𝕊 : State Γ} → {𝕊' : State Γ'}
               → (q : 𝕊 ≤ₛ 𝕊')
               → state-grade 𝕊' ≃ᵣ state-grade 𝕊 ·ᵣ κₛ q
state-grade-≤ₛ {𝕊 = 𝕊} ≤ₛ-refl =
  ≃ᵣ-sym (·ᵣ-identityʳ (state-grade 𝕊))
state-grade-≤ₛ {𝕊 = 𝕊} (≤ₛ-lock {ρ = ρ} q) =
  ≃ᵣ-trans (·ᵣ-cong (state-grade-≤ₛ q) ≃ᵣ-refl) (·ᵣ-assoc (state-grade 𝕊) (κₛ q) ρ)
state-grade-≤ₛ (≤ₛ-res q) =
  state-grade-≤ₛ q

-- If 𝕊' is a successor of 𝕊 and the grade δ it accumulated stays, together
-- with ρ''', below ρ'', then 𝕊' is a renaming of 𝕊.

suc-comp-ren : ∀ {Γ Γ'}
             → {ρ'' ρ''' : R}
             → {𝕊 : State Γ}
             → {𝕊' : State Γ'}
             → (q : 𝕊 ≤ₛ 𝕊')
             → κₛ q ·ᵣ ρ''' ≾ᵣ ρ''
             → Ren [] (toCtx 𝕊' ⟨ ρ''' ⟩) (toCtx 𝕊 ⟨ ρ'' ⟩)

suc-comp-ren {ρ''' = ρ'''} ≤ₛ-refl δρ'''≾ρ'' =
  ⟨⟩-≤-ren (≾ᵣ-trans (≃ᵣ⇒≿ᵣ (·ᵣ-identityˡ ρ''')) δρ'''≾ρ'')
suc-comp-ren {ρ''' = ρ'''} (≤ₛ-lock {ρ = ρ} q) δρ'''≾ρ'' =
  suc-comp-ren q (≾ᵣ-trans (≃ᵣ⇒≿ᵣ (·ᵣ-assoc (κₛ q) ρ ρ''')) δρ'''≾ρ'') ∘ʳ ⟨⟩-μ-ren
suc-comp-ren (≤ₛ-res q) δρ'''≾ρ'' =
  suc-comp-ren q δρ'''≾ρ'' ∘ʳ cong-⟨⟩-ren wk-ren

-- The cancelled grade-decrease statement (about δ) implies the total one
-- (about the two states' grades), by monotonicity of _·ᵣ_.

cancelled⇒total : ∀ {Γ Γ'} → {a b : R} → {𝕊 : State Γ} → {𝕊' : State Γ'}
                → (q : 𝕊 ≤ₛ 𝕊')
                → κₛ q ·ᵣ a ≾ᵣ b
                → state-grade 𝕊' ·ᵣ a ≾ᵣ state-grade 𝕊 ·ᵣ b
cancelled⇒total {a = a} {𝕊 = 𝕊} q δa≾b =
  ≾ᵣ-trans
    (≃ᵣ⇒≾ᵣ (≃ᵣ-trans (·ᵣ-cong (state-grade-≤ₛ q) ≃ᵣ-refl) (·ᵣ-assoc (state-grade 𝕊) (κₛ q) a)))
    (·ᵣ-monoʳ-≾ᵣ δa≾b)

-- Concatenation/composition of states

mutual
  _++ˢ_ : ∀ {Γ} → (𝕊 : State Γ) → (State (Γ ++ᶜ toCtx 𝕊)) → State Γ
  𝕊 ++ˢ ∅ =
    𝕊
  𝕊 ++ˢ (𝕊' ⟨ ρ ⟩ₛ) =
    (𝕊 ++ˢ 𝕊') ⟨ ρ ⟩ₛ
  _++ˢ_ {Γ} 𝕊 (_∷ₛ_ {ρ = ρ} 𝕊' V) =
    (𝕊 ++ˢ 𝕊') ∷ₛ
      V-rename
        (eq-ren
          (cong (_⟨ ρ ⟩) (trans (++ᶜ-assoc Γ (toCtx 𝕊) (toCtx 𝕊')) (cong (Γ ++ᶜ_) (sym (toCtx-++ˢ 𝕊 𝕊'))))))
        V

  infixl 30 _++ˢ_

  toCtx-++ˢ : ∀ {Γ}
            → (𝕊 : State Γ)
            → (𝕊' : State (Γ ++ᶜ toCtx 𝕊))
            → toCtx (𝕊 ++ˢ 𝕊') ≡ toCtx 𝕊 ++ᶜ toCtx 𝕊'
   
  toCtx-++ˢ 𝕊 ∅ =
    refl
  toCtx-++ˢ 𝕊 (𝕊' ⟨ ρ ⟩ₛ) =
    cong (_⟨ ρ ⟩) (toCtx-++ˢ 𝕊 𝕊')
  toCtx-++ˢ 𝕊 (_∷ₛ_ {A = A} {ρ = ρ} 𝕊' V) =
    cong (_∷ [ ρ ] A) (toCtx-++ˢ 𝕊 𝕊')

-- Splitting a state according to a variable/resource in it

mutual 

  split-state-fst : ∀ {Γ A ρ ρ'}
                  → (𝕊 : State Γ)
                  → [ ρ ] A ∈[ ρ' ] (toCtx 𝕊)
                  → State Γ
   
  split-state-fst (𝕊 ⟨ ρ'' ⟩ₛ) (Tl-⟨⟩ x) =
    split-state-fst 𝕊 x
  split-state-fst (𝕊 ∷ₛ V) Hd =
    𝕊
  split-state-fst (𝕊 ∷ₛ V) (Tl-∷ x) =
    split-state-fst 𝕊 x

  split-state-snd : ∀ {Γ A ρ ρ'}
                  → (𝕊 : State Γ)
                  → (x : [ ρ ] A ∈[ ρ' ] (toCtx 𝕊))
                   → State (Γ ++ᶜ toCtx (split-state-fst 𝕊 x) ∷ [ ρ ] A)
  
  split-state-snd (𝕊 ⟨ ρ ⟩ₛ) (Tl-⟨⟩ x) =
    split-state-snd 𝕊 x ⟨ ρ ⟩ₛ
  split-state-snd (𝕊 ∷ₛ V) Hd =
    ∅
  split-state-snd {Γ} (_∷ₛ_ {ρ = ρ} 𝕊 V) (Tl-∷ x) =
    split-state-snd 𝕊 x ∷ₛ
    V-rename (eq-ren (cong (_⟨ ρ ⟩)
      (trans
        (sym (cong (Γ ++ᶜ_) (split-state-++ᶜ 𝕊 x)))
        (sym (++ᶜ-assoc Γ _ (toCtx (split-state-snd 𝕊 x)))))))
    V

  split-state-++ᶜ : ∀ {Γ A ρ ρ'}
                  → (𝕊 : State Γ)
                  → (x : [ ρ ] A ∈[ ρ' ] (toCtx 𝕊))
                  → toCtx (split-state-fst 𝕊 x) ∷ [ ρ ] A ++ᶜ toCtx (split-state-snd 𝕊 x) ≡ toCtx 𝕊

  split-state-++ᶜ (𝕊 ⟨ ρ ⟩ₛ) (Tl-⟨⟩ x) =
    cong (_⟨ ρ ⟩) (split-state-++ᶜ 𝕊 x)
  split-state-++ᶜ (_∷ₛ_ {A = A} {ρ = ρ} 𝕊 V) Hd =
    refl
  split-state-++ᶜ (_∷ₛ_ {A = A} {ρ = ρ} 𝕊 V) (Tl-∷ x) =
    cong (_∷ [ ρ ] A) (split-state-++ᶜ 𝕊 x)

-- Relating the splitting of the state to the splitting of the corresponding context 

fst-split-state≡split-ctx : ∀ {Γ A ρ ρ'}
                  → (𝕊 : State Γ)
                  → (x : [ ρ ] A ∈[ ρ' ] (toCtx 𝕊))
                  → toCtx (split-state-fst 𝕊 x) ≡ split-l x
                  
fst-split-state≡split-ctx (𝕊 ⟨ ρ ⟩ₛ) (Tl-⟨⟩ x) = fst-split-state≡split-ctx 𝕊 x
fst-split-state≡split-ctx (𝕊 ∷ₛ V) Hd          = refl
fst-split-state≡split-ctx (𝕊 ∷ₛ V) (Tl-∷ x)    = fst-split-state≡split-ctx 𝕊 x

split-state≡split-ctx : ∀ {Γ A ρ ρ'}
                  → {𝕊 : State Γ}
                  → {x : [ ρ ] A ∈[ ρ' ] (toCtx 𝕊)}
                  → toCtx (split-state-fst 𝕊 x) ∷ [ ρ ] A ++ᶜ (toCtx (split-state-snd 𝕊 x))  
                    ≡ 
                    split-l x ∷ [ ρ ] A ++ᶜ (split-r x)
                  
split-state≡split-ctx {𝕊 = 𝕊} {x = x} = 
  trans
    (split-state-++ᶜ 𝕊 x) 
    (sym (split-≡ (split-pf x)))

snd-split-state≡split-ctx : ∀ {Γ A ρ ρ'}
                  → (𝕊 : State Γ)
                  → (x : [ ρ ] A ∈[ ρ' ] (toCtx 𝕊))
                  → toCtx (split-state-snd 𝕊 x) ≡ split-r x
                  
snd-split-state≡split-ctx {A = A} {ρ = ρ} 𝕊 x = 
  ++ᶜ-inj₂ {Γ = toCtx (split-state-fst 𝕊 x) ∷ [ ρ ] A}
    (trans
      split-state≡split-ctx
      (cong (_++ᶜ split-r x)
        (cong (_∷ [ ρ ] A) (sym (fst-split-state≡split-ctx 𝕊 x)))))

snd-split-time≡time-from-head : ∀ {Γ A ρ ρ'}
                  → (𝕊 : State Γ)
                  → (x : [ ρ ] A ∈[ ρ' ] (toCtx 𝕊))
                  → state-grade (split-state-snd 𝕊 x) ≡ ρ'
                  
snd-split-time≡time-from-head 𝕊 x = 
  trans (
    trans 
      (grades-≡ (split-state-snd 𝕊 x)) 
      (cong ctx-grade (snd-split-state≡split-ctx 𝕊 x))) 
    (split-grade-≡ x)

-- Lemmas about which values can and which can't be in toCtx 𝕊 (only var can be)

⇒-not-in-toCtx : ∀ {Γ ρ} {𝕊 : State Γ} {A : VType} {C : CType} → A ⇒ C ∈[ ρ ] toCtx 𝕊 → ⊥
⇒-not-in-toCtx {𝕊 = 𝕊 ⟨ ρ ⟩ₛ} (Tl-⟨⟩ x) = ⇒-not-in-toCtx x
⇒-not-in-toCtx {𝕊 = 𝕊 ∷ₛ V} (Tl-∷ x) = ⇒-not-in-toCtx x

⇛-not-in-toCtx : ∀ {Γ ρ} {𝕊 : State Γ} {C D : CType} → C ⇛ D ∈[ ρ ] toCtx 𝕊 → ⊥
⇛-not-in-toCtx {𝕊 = 𝕊 ⟨ ρ ⟩ₛ} (Tl-⟨⟩ x) = ⇛-not-in-toCtx x
⇛-not-in-toCtx {𝕊 = 𝕊 ∷ₛ V} (Tl-∷ x) = ⇛-not-in-toCtx x

⦉⦊-not-in-toCtx : ∀ {Γ ρ} {𝕊 : State Γ} {A B : VType} → A |×| B ∈[ ρ ] toCtx 𝕊 → ⊥
⦉⦊-not-in-toCtx {𝕊 = 𝕊 ⟨ ρ' ⟩ₛ} (Tl-⟨⟩ x) = ⦉⦊-not-in-toCtx x
⦉⦊-not-in-toCtx {𝕊 = 𝕊 ∷ₛ V} (Tl-∷ x) = ⦉⦊-not-in-toCtx x

nat-not-in-toCtx : ∀ {Γ ρ} {𝕊 : State Γ} → nat ∈[ ρ ] toCtx 𝕊 → ⊥
nat-not-in-toCtx {𝕊 = 𝕊 ⟨ ρ' ⟩ₛ} (Tl-⟨⟩ x) = nat-not-in-toCtx x
nat-not-in-toCtx {𝕊 = 𝕊 ∷ₛ V} (Tl-∷ x) = nat-not-in-toCtx x

|+|-not-in-toCtx : ∀ {Γ ρ} {𝕊 : State Γ} {A B : VType} → A |+| B ∈[ ρ ] toCtx 𝕊 → ⊥
|+|-not-in-toCtx {𝕊 = 𝕊 ⟨ ρ' ⟩ₛ} (Tl-⟨⟩ x) = |+|-not-in-toCtx x
|+|-not-in-toCtx {𝕊 = 𝕊 ∷ₛ V} (Tl-∷ x) = |+|-not-in-toCtx x

list-not-in-toCtx : ∀ {Γ ρ} {𝕊 : State Γ} {A : VType} → list A ∈[ ρ ] toCtx 𝕊 → ⊥
list-not-in-toCtx {𝕊 = 𝕊 ⟨ ρ' ⟩ₛ} (Tl-⟨⟩ x) = list-not-in-toCtx x
list-not-in-toCtx {𝕊 = 𝕊 ∷ₛ V} (Tl-∷ x) = list-not-in-toCtx x

empty-not-in-toCtx : ∀ {Γ ρ} {𝕊 : State Γ} → empty ∈[ ρ ] toCtx 𝕊 → ⊥
empty-not-in-toCtx {𝕊 = 𝕊 ⟨ ρ' ⟩ₛ} (Tl-⟨⟩ x) = empty-not-in-toCtx x
empty-not-in-toCtx {𝕊 = 𝕊 ∷ₛ V} (Tl-∷ x) = empty-not-in-toCtx x

bool-not-in-toCtx : ∀ {Γ ρ} {𝕊 : State Γ} → bool ∈[ ρ ] toCtx 𝕊 → ⊥
bool-not-in-toCtx {𝕊 = 𝕊 ⟨ ρ' ⟩ₛ} (Tl-⟨⟩ x) = bool-not-in-toCtx x
bool-not-in-toCtx {𝕊 = 𝕊 ∷ₛ V} (Tl-∷ x) = bool-not-in-toCtx x

not-in-empty-ctx : {ρ : R} {A : VType} → A ∈[ ρ ] [] → ⊥
not-in-empty-ctx ()

-- The two components of a value of product type. Over a state context the
-- value is a pair under a spine of subsumptions, which the recursion peels.

fstᵛ : ∀ {Γ A B} {𝕊 : State Γ} → toCtx 𝕊 ⊢ᵛ⦂ A |×| B → toCtx 𝕊 ⊢ᵛ⦂ A
sndᵛ : ∀ {Γ A B} {𝕊 : State Γ} → toCtx 𝕊 ⊢ᵛ⦂ A |×| B → toCtx 𝕊 ⊢ᵛ⦂ B

fstᵛ (var x _)        = ⊥-elim (⦉⦊-not-in-toCtx x)
fstᵛ ⦉ V , _ ⦊        = V
fstᵛ (subV V (p |×|ₛ _)) = subV (fstᵛ V) p

sndᵛ (var x _)        = ⊥-elim (⦉⦊-not-in-toCtx x)
sndᵛ ⦉ _ , W ⦊        = W
sndᵛ (subV V (_ |×|ₛ q)) = subV (sndᵛ V) q

-- The injection a value of sum type is. Over a state context the value is an
-- injection under a spine of subsumptions, which the recursion pushes onto the
-- payload.

sub⊎ : ∀ {Γ A A₁ B B₁} → A₁ <:ᵛ A → B₁ <:ᵛ B
     → (Γ ⊢ᵛ⦂ A₁) ⊎ (Γ ⊢ᵛ⦂ B₁) → (Γ ⊢ᵛ⦂ A) ⊎ (Γ ⊢ᵛ⦂ B)
sub⊎ p q (inj₁ W) = inj₁ (subV W p)
sub⊎ p q (inj₂ W) = inj₂ (subV W q)

injᵛ : ∀ {Γ A B} {𝕊 : State Γ} → toCtx 𝕊 ⊢ᵛ⦂ A |+| B
     → (toCtx 𝕊 ⊢ᵛ⦂ A) ⊎ (toCtx 𝕊 ⊢ᵛ⦂ B)
injᵛ (var x _)           = ⊥-elim (|+|-not-in-toCtx x)
injᵛ (inl V)             = inj₁ V
injᵛ (inr V)             = inj₂ V
injᵛ (subV V (p |+|ₛ q)) = sub⊎ p q (injᵛ V)

-- and back

uninjᵛ : ∀ {Γ A B} → (Γ ⊢ᵛ⦂ A) ⊎ (Γ ⊢ᵛ⦂ B) → Γ ⊢ᵛ⦂ A |+| B
uninjᵛ (inj₁ W) = inl W
uninjᵛ (inj₂ W) = inr W

-- The canonical decomposition of a list: empty, or a head and a tail. Over a
-- state context the value is `nil` or a `cons` under a spine of subsumptions,
-- which the recursion pushes into the head and the tail.

ListView : Ctx → VType → Set
ListView Γ A = ⊤ ⊎ ((Γ ⊢ᵛ⦂ A) × (Γ ⊢ᵛ⦂ list A))

subL : ∀ {Γ A A₁} → A₁ <:ᵛ A → ListView Γ A₁ → ListView Γ A
subL p (inj₁ tt)      = inj₁ tt
subL p (inj₂ (W , L)) = inj₂ (subV W p , subV L (listₛ p))

listᵛ : ∀ {Γ A} {𝕊 : State Γ} → toCtx 𝕊 ⊢ᵛ⦂ list A → ListView (toCtx 𝕊) A
listᵛ (var x _)             = ⊥-elim (list-not-in-toCtx x)
listᵛ nil                   = inj₁ tt
listᵛ (cons V W)            = inj₂ (V , W)
listᵛ (subV V (listₛ p))    = subL p (listᵛ V)

-- and back

unlistᵛ : ∀ {Γ A} → ListView Γ A → Γ ⊢ᵛ⦂ list A
unlistᵛ (inj₁ tt)      = nil
unlistᵛ (inj₂ (W , L)) = cons W L

-- A state context binds only boxed types, none of them eternal.

eternal-not-in-toCtx : ∀ {Γ ρ A} {𝕊 : State Γ} → Et A → A ∈[ ρ ] toCtx 𝕊 → ⊥
eternal-not-in-toCtx {𝕊 = 𝕊 ⟨ _ ⟩ₛ} et (Tl-⟨⟩ x) = eternal-not-in-toCtx et x
eternal-not-in-toCtx {𝕊 = 𝕊 ∷ₛ _}   () Hd
eternal-not-in-toCtx {𝕊 = 𝕊 ∷ₛ _}   et (Tl-∷ x)  = eternal-not-in-toCtx et x

-- The datum a value of an eternal type is. Over a state context the value is
-- a datum under a spine of subsumptions, which act on the data.

⌊_⌋ᵈ : ∀ {Γ A} {𝕊 : State Γ} → Et A → toCtx 𝕊 ⊢ᵛ⦂ A → ⟪ A ⟫
⌊ et ⌋ᵈ             (var x _)   = ⊥-elim (eternal-not-in-toCtx et x)
⌊ et ⌋ᵈ             (subV V p)  = ⟪ p ⟫ˢ (⌊ <:ᵛ-eternalˡ p et ⌋ᵈ V)
⌊ Baseₑ _ ⌋ᵈ        (const B c) = c
⌊ unitₑ ⌋ᵈ          ⋆           = tt
⌊ boolₑ ⌋ᵈ          true        = Bool.true
⌊ boolₑ ⌋ᵈ          false       = Bool.false
⌊ natₑ ⌋ᵈ           zero        = 0
⌊ natₑ ⌋ᵈ           (succ V)    = suc (⌊ natₑ ⌋ᵈ V)
⌊ et₁ |×|ₑ et₂ ⌋ᵈ   ⦉ V , W ⦊    = ⌊ et₁ ⌋ᵈ V , ⌊ et₂ ⌋ᵈ W
⌊ et₁ |+|ₑ et₂ ⌋ᵈ   (inl V)     = inj₁ (⌊ et₁ ⌋ᵈ V)
⌊ et₁ |+|ₑ et₂ ⌋ᵈ   (inr V)     = inj₂ (⌊ et₂ ⌋ᵈ V)
⌊ listₑ et ⌋ᵈ       nil         = List.[]
⌊ listₑ et ⌋ᵈ       (cons V W)  = ⌊ et ⌋ᵈ V List.∷ ⌊ listₑ et ⌋ᵈ W

-- There is no value of the empty type over a state context.

empty-not-value : ∀ {Γ} {𝕊 : State Γ} → toCtx 𝕊 ⊢ᵛ⦂ empty → ⊥
empty-not-value (var x _)      = empty-not-in-toCtx x
empty-not-value (subV V emptyₛ) = empty-not-value V

-- Looking up a resource in the state

resource-lookup : ∀ {Γ ρ ρ' A}
                → (𝕊 : State Γ)
                → (x : [ ρ ] A ∈[ ρ' ] toCtx 𝕊)
                → (Γ ++ᶜ toCtx (split-state-fst 𝕊 x)) ⟨ ρ ⟩ ⊢ᵛ⦂ A
resource-lookup (𝕊 ⟨ _ ⟩ₛ) (Tl-⟨⟩ x) = resource-lookup 𝕊 x
resource-lookup (𝕊 ∷ₛ V) Hd          = V
resource-lookup (𝕊 ∷ₛ _) (Tl-∷ x)    = resource-lookup 𝕊 x
