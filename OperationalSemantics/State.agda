open import Syntax.Grades

module OperationalSemantics.State (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Syntax.Contexts (Grades)
open import Syntax.Language (Grades)
open import Syntax.Renamings (Grades)
open import Syntax.RenActions (Grades)
open import Syntax.Types (Grades)

open import Data.Empty
open import Util.Equality
open import Data.Product
open import Util.Time

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

{-
-- Definition of successor of a state

data _≤ₛ_ : ∀ {Γ Γ'} → 𝕊 Γ → 𝕊 Γ' → Set where
    id-suc : ∀ {Γ} 
            → {S : 𝕊 Γ} 
            -----------
            → S ≤ₛ S

    ⟨⟩-suc : ∀ {Γ Γ'}
            → {S : 𝕊 Γ} 
            → {S' : 𝕊 Γ'} 
            → (ρ : R) 
            → S ≤ₛ S' 
            -------------------
            → S ≤ₛ (S' ⟨ ρ ⟩ₛ)

    ∷-suc : ∀ {Γ Γ' ρ A} 
            → {S : 𝕊 Γ} 
            → {S' : 𝕊 Γ'} 
            → (V : (Γ' ++ᶜ (toCtx S') ⟨ ρ ⟩) ⊢V⦂ A) 
            → S ≤ₛ S' 
            ---------------------------------------
            → S ≤ₛ (S' ∷ₛ V)

-- If a state is a successor of another state they can be renamed as contexts

≤ₛ⇒Ren : ∀ {Γ Γ'} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'} → S ≤ₛ S' → Ren (toCtx S) (toCtx S')
≤ₛ⇒Ren id-suc = id-ren
≤ₛ⇒Ren (⟨⟩-suc ρ S≤ₛS') = {!!} --wk-⟨⟩-ren ∘ʳ (≤ₛ⇒Ren S≤ₛS')
≤ₛ⇒Ren (∷-suc V S≤ₛS') = wk-ren ∘ʳ (≤ₛ⇒Ren S≤ₛS')

-- ≤ₛ increases time

S≤ₛS'⇒τ≤τ' : ∀ {Γ Γ'} → {S : 𝕊 Γ} → {S' : 𝕊 Γ'} → S ≤ₛ S' → (state-grade S) ≤ (state-grade S')
S≤ₛS'⇒τ≤τ' {S = S} {S' = .S} id-suc = ≤-refl
S≤ₛS'⇒τ≤τ' {S = S} {S' = .(S' ⟨ τ'' ⟩ₛ)} (⟨⟩-suc {S' = S'} τ'' S≤ₛS') = 
    m≤n⇒m≤n+o τ'' 
        (τ-≤-substᵣ (grades-≡ S')
        (τ-≤-substₗ (sym (grades-≡ S)) 
    ?)) --(Ren.ctx-time-≤ (≤ₛ⇒Ren S≤ₛS'))))
S≤ₛS'⇒τ≤τ' {S = S} {S' = .(S' ∷ₛ V)} (∷-suc {S' = S'} V S≤ₛS') = 
    τ-≤-substᵣ (grades-≡ S') 
    (τ-≤-substₗ (sym (grades-≡ S)) 
    ?) --(Ren.ctx-time-≤ (≤ₛ⇒Ren S≤ₛS')))


-- Lemma: If one state is a successor of another and overall time inreases we 
-- can rename it

suc-comp-ren : ∀ {Γ Γ'} 
        → { τ'' τ''' : Time} 
        → {S : 𝕊 Γ} 
        → {S' : 𝕊 Γ'} 
        → S ≤ₛ S' 
        → state-grade S + τ'' ≤ state-grade S' + τ'''
        → Ren (toCtx S ⟨ τ'' ⟩) (toCtx S' ⟨ τ''' ⟩)
suc-comp-ren {S = S} id-suc q = 
  ⟨⟩-≤-ren (+-cancelˡ-≤ _ _ _ q)
suc-comp-ren {τ'' = τ} {τ'''} (⟨⟩-suc {S' = S'} τ'' S≤ₛS') q = 
  ⟨⟩-μ-ren 
    ∘ʳ suc-comp-ren S≤ₛS' (τ-≤-substᵣ (sym (+-assoc (state-grade S') τ'' τ''')) q)
suc-comp-ren {S = S} (∷-suc V S≤ₛS') q = 
  (cong-⟨⟩-ren wk-ren) 
    ∘ʳ suc-comp-ren S≤ₛS' q

-- Concatenation/composition of states

mutual
  _++ˢ_ : ∀ {Γ} → (S : 𝕊 Γ) → (𝕊 (Γ ++ᶜ toCtx S)) → 𝕊 Γ
  S ++ˢ ∅ =
    S
  S ++ˢ (S' ⟨ τ ⟩ₛ) =
    (S ++ˢ S') ⟨ τ ⟩ₛ
  _++ˢ_ {Γ} S (_∷ₛ_ {τ = τ} S' V) =
    (S ++ˢ S') ∷ₛ
      V-rename (eq-ren (cong (_⟨ τ ⟩)
                       (trans (++ᶜ-assoc Γ (toCtx S) (toCtx S'))
                       (cong (Γ ++ᶜ_) (sym (toCtx-++ˢ S S'))))))
               V

  infixl 30 _++ˢ_

  toCtx-++ˢ : ∀ {Γ}
            → (S : 𝕊 Γ)
            → (S' : 𝕊 (Γ ++ᶜ toCtx S))
            → toCtx (S ++ˢ S') ≡ toCtx S ++ᶜ toCtx S'
   
  toCtx-++ˢ S ∅ =
    refl
  toCtx-++ˢ S (S' ⟨ τ ⟩ₛ) =
    cong (_⟨ τ ⟩) (toCtx-++ˢ S S')
  toCtx-++ˢ S (_∷ₛ_ {A = A} {τ = τ} S' V) =
    cong (_∷ [ τ ] A) (toCtx-++ˢ S S')

-- Splitting a state according to a variable/resource in it

mutual 

  split-state-fst : ∀ {Γ A τ τ'}
                  → (S : 𝕊 Γ)
                  → [ τ ] A ∈[ τ' ] (toCtx S)
                  → 𝕊 Γ
   
  split-state-fst (S ⟨ τ ⟩ₛ) (Tl-⟨⟩ x) =
    split-state-fst S x
  split-state-fst (S ∷ₛ V) Hd =
    S
  split-state-fst (S ∷ₛ V) (Tl-∷ x) =
    split-state-fst S x
   
  split-state-snd : ∀ {Γ A τ τ'}
                  → (S : 𝕊 Γ)
                  → (x : [ τ ] A ∈[ τ' ] (toCtx S))
                  → 𝕊 (Γ ++ᶜ toCtx (split-state-fst S x) ∷ [ τ ] A)
  
  split-state-snd (S ⟨ τ ⟩ₛ) (Tl-⟨⟩ x) =
    split-state-snd S x ⟨ τ ⟩ₛ
  split-state-snd (S ∷ₛ V) Hd =
    ∅
  split-state-snd {Γ} (_∷ₛ_ {τ = τ} S V) (Tl-∷ x) =
    split-state-snd S x ∷ₛ
    V-rename (eq-ren (cong (_⟨ τ ⟩)
      (trans
        (sym (cong (Γ ++ᶜ_) (split-state-++ᶜ S x)))
        (sym (++ᶜ-assoc Γ _ (toCtx (split-state-snd S x)))))))
    V

  split-state-++ᶜ : ∀ {Γ A τ τ'}
                  → (S : 𝕊 Γ)
                  → (x : [ τ ] A ∈[ τ' ] (toCtx S))
                  → toCtx (split-state-fst S x) ∷ [ τ ] A ++ᶜ toCtx (split-state-snd S x) ≡ toCtx S

  split-state-++ᶜ (S ⟨ τ ⟩ₛ) (Tl-⟨⟩ x) =
    cong (_⟨ τ ⟩) (split-state-++ᶜ S x)
  split-state-++ᶜ (_∷ₛ_ {A = A} {τ = τ} S V) Hd =
    refl
  split-state-++ᶜ (_∷ₛ_ {A = A} {τ = τ} S V) (Tl-∷ x) =
    cong (_∷ [ τ ] A) (split-state-++ᶜ S x)

-- Relating the splitting of the state to the splitting of the corresponding context 

fst-split-state≡split-ctx : ∀ {Γ A τ τ'}
                  → (S : 𝕊 Γ)
                  → (x : [ τ ] A ∈[ τ' ] (toCtx S))
                  → toCtx (split-state-fst S x) ≡ proj₁ (var-split x)
                  
fst-split-state≡split-ctx (S ⟨ τ ⟩ₛ) (Tl-⟨⟩ x) = fst-split-state≡split-ctx S x
fst-split-state≡split-ctx (S ∷ₛ V) Hd = refl
fst-split-state≡split-ctx (S ∷ₛ V) (Tl-∷ x) = fst-split-state≡split-ctx S x

split-state≡split-ctx : ∀ {Γ A τ τ'}
                  → {S : 𝕊 Γ}
                  → {x : [ τ ] A ∈[ τ' ] (toCtx S)}
                  → toCtx (split-state-fst S x) ∷ [ τ ] A ++ᶜ (toCtx (split-state-snd S x))  
                  ≡ 
                  proj₁ (var-split x) ∷ [ τ ] A ++ᶜ (proj₁ (proj₂ (var-split x)))
                  
split-state≡split-ctx {S = S} {x = x} = 
  trans
    (split-state-++ᶜ S x) 
    (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))))

snd-split-state≡split-ctx : ∀ {Γ A τ τ'}
                  → (S : 𝕊 Γ)
                  → (x : [ τ ] A ∈[ τ' ] (toCtx S))
                  → toCtx (split-state-snd S x) ≡ proj₁ (proj₂ (var-split x))
                  
snd-split-state≡split-ctx {A = A} {τ = τ} S x = 
  ++ᶜ-inj₂ {Γ = toCtx (split-state-fst S x) ∷ [ τ ] A}
    (trans
      split-state≡split-ctx
      (cong (_++ᶜ proj₁ (proj₂ (var-split x)))
        (cong (_∷ [ τ ] A) (sym (fst-split-state≡split-ctx S x)))))

snd-split-time≡time-from-head : ∀ {Γ A τ τ'}
                  → (S : 𝕊 Γ)
                  → (x : [ τ ] A ∈[ τ' ] (toCtx S))
                  → state-grade (split-state-snd S x) ≡ τ'
                  
snd-split-time≡time-from-head S x = 
  trans (
    trans 
      (grades-≡ (split-state-snd S x)) 
      (cong ctx-time (snd-split-state≡split-ctx S x))) 
    (proj₂ (proj₂ (proj₂ (var-split x))))

-- Returning the second part of state, when the state is successor of another state

mutual
  suc-part-state : ∀ {Γ Γ'}
            → (S : 𝕊 Γ)
            → (S' : 𝕊 Γ')
            → S ≤ₛ S'
            → 𝕊 (Γ' ++ᶜ (toCtx S))
  suc-part-state S .S id-suc = 
    ∅
  suc-part-state S .(S' ⟨ τ'' ⟩ₛ) (⟨⟩-suc {S' = S'} τ'' S≤ₛS') = 
    suc-part-state S S' S≤ₛS' ⟨ τ'' ⟩ₛ
  suc-part-state {Γ' = Γ'} S .(S' ∷ₛ V) (∷-suc {τ = τ} {S' = S'} V S≤ₛS') = 
    let recursive = suc-part-state S S' S≤ₛS' in 
    recursive ∷ₛ 
      V-rename (cong-⟨⟩-ren (eq-ren 
        (trans 
          (cong (Γ' ++ᶜ_) (sym (S++suc-partS≡S' S S' S≤ₛS'))) 
          (sym (++ᶜ-assoc Γ' (toCtx S) (toCtx recursive)))))) 
        V

  S++suc-partS≡S' : ∀ {Γ Γ'} 
          → (S : 𝕊 Γ)
          → (S' : 𝕊 Γ')
          → (p : S ≤ₛ S') 
          → toCtx S ++ᶜ toCtx (suc-part-state S S' p) ≡ toCtx S'
  S++suc-partS≡S' S .S id-suc = 
    refl
  S++suc-partS≡S' S .(S' ⟨ τ'' ⟩ₛ) (⟨⟩-suc {S' = S'} τ'' S≤ₛS') = 
    cong (_⟨ τ'' ⟩) (S++suc-partS≡S' S S' S≤ₛS')
  S++suc-partS≡S' S .(S' ∷ₛ V) (∷-suc {τ = τ} {A = A} {S' = S'} V S≤ₛS') = 
    cong (_∷ [ τ ] A) (S++suc-partS≡S' S S' S≤ₛS')

-- Lemmas about which values can and which can't be in toCtx S (only var can be)

⇒-not-in-toCtx : ∀ {Γ τ} {S : 𝕊 Γ} {A : VType} {C : CType} → A ⇒ C ∈[ τ ] toCtx S → ⊥
⇒-not-in-toCtx {S = S ⟨ τ ⟩ₛ} (Tl-⟨⟩ x) = ⇒-not-in-toCtx x
⇒-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = ⇒-not-in-toCtx x

⦉⦊-not-in-toCtx : ∀ {Γ τ} {S : 𝕊 Γ} {A B : VType} → A |×| B ∈[ τ ] toCtx S → ⊥
⦉⦊-not-in-toCtx {S = S ⟨ τ'' ⟩ₛ} (Tl-⟨⟩ x) = ⦉⦊-not-in-toCtx x
⦉⦊-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = ⦉⦊-not-in-toCtx x

Empty-not-in-toCtx : ∀ {Γ τ} {S : 𝕊 Γ} → Empty ∈[ τ ] toCtx S → ⊥
Empty-not-in-toCtx {S = S ⟨ τ'' ⟩ₛ} (Tl-⟨⟩ x) = Empty-not-in-toCtx x
Empty-not-in-toCtx {S = S ∷ₛ V} (Tl-∷ x) = Empty-not-in-toCtx x

not-in-empty-ctx : {τ : Time} {A : VType} → A ∈[ τ ] [] → ⊥
not-in-empty-ctx ()

var-in-ctx : ∀ { Γ τ' A} → 
            (V : Γ ⊢V⦂ [ τ' ] A) → 
            Σ[ τ'' ∈ Time ] ([ τ' ] A ∈[ τ'' ] Γ )
var-in-ctx (var {τ = τ} x) = τ , x

-- The time of state can't be negative

τ'≤snd-state : ∀ {A τ'} 
        → {S : 𝕊 []}
        → (V : toCtx S -ᶜ τ' ⊢V⦂ [ τ' ] A)
        → τ' ≤
    state-grade (split-state-snd S (var-ᶜ-+ {τ = τ'} (proj₂ (var-in-ctx V))))
τ'≤snd-state {τ' = τ'} {S = S} (var {τ = τ} x) = 
  let y = var-ᶜ-+ {τ = τ'} x in 
  τ-≤-substᵣ (snd-split-time≡time-from-head S y) (m≤n⇒m≤o+n τ ≤-refl)

-- Looking up a resource in the state

resource-lookup : ∀ {Γ τ τ' A}
                → (S : 𝕊 Γ)
                → (x : [ τ ] A ∈[ τ' ] toCtx S)
                → (Γ ++ᶜ toCtx (split-state-fst S x)) ⟨ τ ⟩ ⊢V⦂ A
resource-lookup (S ⟨ τ ⟩ₛ) (Tl-⟨⟩ {τ' = τ'} x) =
  resource-lookup S x
resource-lookup (S ∷ₛ V) Hd =
  V
resource-lookup (S ∷ₛ V) (Tl-∷ {τ = τ} x) =
  resource-lookup S x

-- Renaming of the result of previous lemma to context for state S

resource-pass-to-ctx : ∀ {Γ τ τ' A}
                     → (S : 𝕊 Γ)
                     → (x : [ τ ] A ∈[ τ' ] toCtx S)
                     → (p : τ ≤ ctx-time (toCtx (split-state-snd S x)))
                     → (V : (Γ ++ᶜ toCtx (split-state-fst S x)) ⟨ τ ⟩ ⊢V⦂ A)
                     → Γ ++ᶜ toCtx S ⊢V⦂ A
resource-pass-to-ctx {Γ} {τ} {τ'} {A} S x p V =
  V-rename
    (   eq-ren (cong (Γ ++ᶜ_) (split-state-++ᶜ S x)) 
     ∘ʳ eq-ren (++ᶜ-assoc Γ (toCtx (split-state-fst S x) ∷ [ τ ] A) (toCtx (split-state-snd S x))) 
     ∘ʳ cong-ren wk-ren
     ∘ʳ ren⟨τ⟩-ctx {Γ' = toCtx (split-state-snd S x)} p)
    V
-}
