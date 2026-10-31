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

-- Named forms of the state constructors

grade-pass : ∀ {Γ} → (S : 𝕊 Γ) → (ρ : R) → 𝕊 Γ
grade-pass S ρ = S ⟨ ρ ⟩ₛ 

extend-state : ∀ {Γ A ρ} → (S : 𝕊 Γ) → ((Γ ++ᶜ (toCtx S) ⟨ ρ ⟩) ⊢V⦂ A) → 𝕊 Γ
extend-state S V = S ∷ₛ V 

-- Sum of the grade passings in the state

state-grade : ∀ {Γ} → (S : 𝕊 Γ) → R
state-grade ∅ = 𝟏ᵣ
state-grade (S ⟨ ρ ⟩ₛ) = state-grade S ·ᵣ ρ
state-grade (S ∷ₛ A) = state-grade S

-- State grade is the same as the context grade of toCtx S 

grades-≡ : ∀ {Γ} → (S : 𝕊 Γ) → state-grade S ≡ ctx-grade (toCtx S)
grades-≡ ∅ = refl
grades-≡ (S ⟨ ρ ⟩ₛ) = cong (_·ᵣ ρ) (grades-≡ S)
grades-≡ (S ∷ₛ A) = grades-≡ S

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

-- The grade δ accumulated when passing from a state 𝕊 to a successor state 𝕊':
-- state-grade S' ≃ᵣ state-grade S ·ᵣ δ, by state-grade-≤ₛ.

≤ₛ-grade : ∀ {Γ Γ'} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'} → S ≤ₛ S' → R
≤ₛ-grade id-suc       = 𝟏ᵣ
≤ₛ-grade (⟨⟩-suc ρ q) = ≤ₛ-grade q ·ᵣ ρ
≤ₛ-grade (∷-suc V q)  = ≤ₛ-grade q

-- The overall grade of a successor state factors through ≤ₛ-grade.

state-grade-≤ₛ : ∀ {Γ Γ'} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'}
               → (q : S ≤ₛ S')
               → state-grade S' ≃ᵣ state-grade S ·ᵣ ≤ₛ-grade q
state-grade-≤ₛ {S = S} id-suc =
  ≃ᵣ-sym (·ᵣ-identityʳ (state-grade S))
state-grade-≤ₛ {S = S} (⟨⟩-suc ρ q) =
  ≃ᵣ-trans (·ᵣ-cong (state-grade-≤ₛ q) ≃ᵣ-refl) (·ᵣ-assoc (state-grade S) (≤ₛ-grade q) ρ)
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
             → Ren [] (toCtx S' ⟨ ρ''' ⟩) (toCtx S ⟨ ρ'' ⟩)

suc-comp-ren {ρ''' = ρ'''} id-suc δρ'''≾ρ'' =
  ⟨⟩-≤-ren (≾ᵣ-trans (≃ᵣ⇒≿ᵣ (·ᵣ-identityˡ ρ''')) δρ'''≾ρ'')
suc-comp-ren {ρ''' = ρ'''} (⟨⟩-suc ρ q) δρ'''≾ρ'' =
  suc-comp-ren q (≾ᵣ-trans (≃ᵣ⇒≿ᵣ (·ᵣ-assoc (≤ₛ-grade q) ρ ρ''')) δρ'''≾ρ'') ∘ʳ ⟨⟩-μ-ren
suc-comp-ren (∷-suc V q) δρ'''≾ρ'' =
  suc-comp-ren q δρ'''≾ρ'' ∘ʳ cong-⟨⟩-ren wk-ren

-- The cancelled grade-decrease statement (about δ) implies the total one
-- (about the two states' grades), by monotonicity of _·ᵣ_.

cancelled⇒total : ∀ {Γ Γ'} → {a b : R} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'}
                → (q : S ≤ₛ S')
                → ≤ₛ-grade q ·ᵣ a ≾ᵣ b
                → state-grade S' ·ᵣ a ≾ᵣ state-grade S ·ᵣ b
cancelled⇒total {a = a} {S = S} q δa≾b =
  ≾ᵣ-trans
    (≃ᵣ⇒≾ᵣ (≃ᵣ-trans (·ᵣ-cong (state-grade-≤ₛ q) ≃ᵣ-refl) (·ᵣ-assoc (state-grade S) (≤ₛ-grade q) a)))
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

⇛-not-in-toCtx : ∀ {Γ ρ} {S : 𝕊 Γ} {C D : CType} → C ⇛ D ∈[ ρ ] toCtx S → ⊥
⇛-not-in-toCtx {S = S ⟨ ρ ⟩ₛ} (Tl-⟨⟩ x) = ⇛-not-in-toCtx x
⇛-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = ⇛-not-in-toCtx x

⦉⦊-not-in-toCtx : ∀ {Γ ρ} {S : 𝕊 Γ} {A B : VType} → A |×| B ∈[ ρ ] toCtx S → ⊥
⦉⦊-not-in-toCtx {S = S ⟨ ρ' ⟩ₛ} (Tl-⟨⟩ x) = ⦉⦊-not-in-toCtx x
⦉⦊-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = ⦉⦊-not-in-toCtx x

Nat-not-in-toCtx : ∀ {Γ ρ} {S : 𝕊 Γ} → Nat ∈[ ρ ] toCtx S → ⊥
Nat-not-in-toCtx {S = S ⟨ ρ' ⟩ₛ} (Tl-⟨⟩ x) = Nat-not-in-toCtx x
Nat-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = Nat-not-in-toCtx x

|+|-not-in-toCtx : ∀ {Γ ρ} {S : 𝕊 Γ} {A B : VType} → A |+| B ∈[ ρ ] toCtx S → ⊥
|+|-not-in-toCtx {S = S ⟨ ρ' ⟩ₛ} (Tl-⟨⟩ x) = |+|-not-in-toCtx x
|+|-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = |+|-not-in-toCtx x

|List|-not-in-toCtx : ∀ {Γ ρ} {S : 𝕊 Γ} {A : VType} → |List| A ∈[ ρ ] toCtx S → ⊥
|List|-not-in-toCtx {S = S ⟨ ρ' ⟩ₛ} (Tl-⟨⟩ x) = |List|-not-in-toCtx x
|List|-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = |List|-not-in-toCtx x

Empty-not-in-toCtx : ∀ {Γ ρ} {S : 𝕊 Γ} → Empty ∈[ ρ ] toCtx S → ⊥
Empty-not-in-toCtx {S = S ⟨ ρ' ⟩ₛ} (Tl-⟨⟩ x) = Empty-not-in-toCtx x
Empty-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = Empty-not-in-toCtx x

Bool-not-in-toCtx : ∀ {Γ ρ} {S : 𝕊 Γ} → Bool ∈[ ρ ] toCtx S → ⊥
Bool-not-in-toCtx {S = S ⟨ ρ' ⟩ₛ} (Tl-⟨⟩ x) = Bool-not-in-toCtx x
Bool-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = Bool-not-in-toCtx x

not-in-empty-ctx : {ρ : R} {A : VType} → A ∈[ ρ ] [] → ⊥
not-in-empty-ctx ()

-- The two components of a value of product type. Over a state context the
-- value is a pair under a spine of subsumptions, which the recursion peels.

fstᵛ : ∀ {Γ A B} {S : 𝕊 Γ} → toCtx S ⊢V⦂ A |×| B → toCtx S ⊢V⦂ A
sndᵛ : ∀ {Γ A B} {S : 𝕊 Γ} → toCtx S ⊢V⦂ A |×| B → toCtx S ⊢V⦂ B

fstᵛ (var _ x)        = ⊥-elim (⦉⦊-not-in-toCtx x)
fstᵛ ⦉ V , _ ⦊        = V
fstᵛ (subV V (p |×|ₛ _)) = subV (fstᵛ V) p

sndᵛ (var _ x)        = ⊥-elim (⦉⦊-not-in-toCtx x)
sndᵛ ⦉ _ , W ⦊        = W
sndᵛ (subV V (_ |×|ₛ q)) = subV (sndᵛ V) q

-- The injection a value of sum type is. Over a state context the value is an
-- injection under a spine of subsumptions, which the recursion pushes onto the
-- payload.

sub⊎ : ∀ {Γ A A₁ B B₁} → A₁ <:ᵛ A → B₁ <:ᵛ B
     → (Γ ⊢V⦂ A₁) ⊎ (Γ ⊢V⦂ B₁) → (Γ ⊢V⦂ A) ⊎ (Γ ⊢V⦂ B)
sub⊎ p q (inj₁ W) = inj₁ (subV W p)
sub⊎ p q (inj₂ W) = inj₂ (subV W q)

injᵛ : ∀ {Γ A B} {S : 𝕊 Γ} → toCtx S ⊢V⦂ A |+| B
     → (toCtx S ⊢V⦂ A) ⊎ (toCtx S ⊢V⦂ B)
injᵛ (var _ x)           = ⊥-elim (|+|-not-in-toCtx x)
injᵛ (inl V)             = inj₁ V
injᵛ (inr V)             = inj₂ V
injᵛ (subV V (p |+|ₛ q)) = sub⊎ p q (injᵛ V)

-- and back

uninjᵛ : ∀ {Γ A B} → (Γ ⊢V⦂ A) ⊎ (Γ ⊢V⦂ B) → Γ ⊢V⦂ A |+| B
uninjᵛ (inj₁ W) = inl W
uninjᵛ (inj₂ W) = inr W

-- The canonical decomposition of a list: empty, or a head and a tail. Over a
-- state context the value is `nil` or a `cons` under a spine of subsumptions,
-- which the recursion pushes into the head and the tail.

ListView : Ctx → VType → Set
ListView Γ A = ⊤ ⊎ ((Γ ⊢V⦂ A) × (Γ ⊢V⦂ |List| A))

subL : ∀ {Γ A A₁} → A₁ <:ᵛ A → ListView Γ A₁ → ListView Γ A
subL p (inj₁ tt)      = inj₁ tt
subL p (inj₂ (W , L)) = inj₂ (subV W p , subV L (|List|ₛ p))

listᵛ : ∀ {Γ A} {S : 𝕊 Γ} → toCtx S ⊢V⦂ |List| A → ListView (toCtx S) A
listᵛ (var _ x)             = ⊥-elim (|List|-not-in-toCtx x)
listᵛ nil                   = inj₁ tt
listᵛ (cons V W)            = inj₂ (V , W)
listᵛ (subV V (|List|ₛ p))  = subL p (listᵛ V)

-- and back

unlistᵛ : ∀ {Γ A} → ListView Γ A → Γ ⊢V⦂ |List| A
unlistᵛ (inj₁ tt)      = nil
unlistᵛ (inj₂ (W , L)) = cons W L

-- A state context binds only boxed types, none of them eternal.

eternal-not-in-toCtx : ∀ {Γ ρ A} {S : 𝕊 Γ} → Eternal A → A ∈[ ρ ] toCtx S → ⊥
eternal-not-in-toCtx {S = S ⟨ _ ⟩ₛ} et (Tl-⟨⟩ x) = eternal-not-in-toCtx et x
eternal-not-in-toCtx {S = S ∷ₛ _}   () Hd
eternal-not-in-toCtx {S = S ∷ₛ _}   et (Tl-∷ x)  = eternal-not-in-toCtx et x

-- The datum a value of an eternal type is. Over a state context the value is
-- a datum under a spine of subsumptions, which act on the data.

⌊_⌋ᵈ : ∀ {Γ A} {S : 𝕊 Γ} → Eternal A → toCtx S ⊢V⦂ A → ⟪ A ⟫
⌊ et ⌋ᵈ             (var _ x)   = ⊥-elim (eternal-not-in-toCtx et x)
⌊ et ⌋ᵈ             (subV V p)  = ⟪ p ⟫ˢ (⌊ <:ᵛ-eternalˡ p et ⌋ᵈ V)
⌊ Baseₑ _ ⌋ᵈ        (const c)   = c
⌊ Unitₑ ⌋ᵈ          ⋆           = tt
⌊ Boolₑ ⌋ᵈ          true        = Bool.true
⌊ Boolₑ ⌋ᵈ          false       = Bool.false
⌊ Natₑ ⌋ᵈ           zero        = 0
⌊ Natₑ ⌋ᵈ           (succ V)    = suc (⌊ Natₑ ⌋ᵈ V)
⌊ et₁ |×|ₑ et₂ ⌋ᵈ   ⦉ V , W ⦊    = ⌊ et₁ ⌋ᵈ V , ⌊ et₂ ⌋ᵈ W
⌊ et₁ |+|ₑ et₂ ⌋ᵈ   (inl V)     = inj₁ (⌊ et₁ ⌋ᵈ V)
⌊ et₁ |+|ₑ et₂ ⌋ᵈ   (inr V)     = inj₂ (⌊ et₂ ⌋ᵈ V)
⌊ |List|ₑ et ⌋ᵈ     nil         = List.[]
⌊ |List|ₑ et ⌋ᵈ     (cons V W)  = ⌊ et ⌋ᵈ V List.∷ ⌊ |List|ₑ et ⌋ᵈ W

-- There is no value of the empty type over a state context.

empty-not-value : ∀ {Γ} {S : 𝕊 Γ} → toCtx S ⊢V⦂ Empty → ⊥
empty-not-value (var _ x)      = Empty-not-in-toCtx x
empty-not-value (subV V Emptyₛ) = empty-not-value V

-- Looking up a resource in the state

resource-lookup : ∀ {Γ ρ ρ' A}
                → (S : 𝕊 Γ)
                → (x : [ ρ ] A ∈[ ρ' ] toCtx S)
                → (Γ ++ᶜ toCtx (split-state-fst S x)) ⟨ ρ ⟩ ⊢V⦂ A
resource-lookup (S ⟨ _ ⟩ₛ) (Tl-⟨⟩ x) = resource-lookup S x
resource-lookup (S ∷ₛ V) Hd          = V
resource-lookup (S ∷ₛ _) (Tl-∷ x)    = resource-lookup S x
