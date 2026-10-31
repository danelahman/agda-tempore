---------------------------------------------------------------------------
-- Comparison morphisms, derived from the universal structure.           --
--                                                                       --
-- An outcome is a point of `Ordᵐ = 𝟙ᵐ +ᵐ (𝟙ᵐ +ᵐ 𝟙ᵐ)`. A comparison on   --
-- an object `A` is a morphism `A ×ᵐ A →ᵐ Ordᵐ`; the unit, the booleans, --
-- the natural numbers, products, coproducts and lists carry one (the    --
-- latter three given comparisons on the components), built from the     --
-- copairings, `ifᵐ`, iteration, folds and the exponentials. Each comes  --
-- with its laws at points: compared at the points of data, it returns   --
-- the outcome of the structural order on the data                       --
-- (`MonomorphicCalculus.Syntax.Data`).                                  --
---------------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)

open import Language.Comparisons

open import MonomorphicCalculus.DenotationalSemantics.Model.Category

module MonomorphicCalculus.DenotationalSemantics.Model.Comparison (Cat : Category) where

open Category Cat

private
  infixr 3 _∙_
  _∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙_ = ≈ᵐ-trans

  -- the terminal map out of `𝟙ᵐ` is the identity

  !-𝟙 : terminalᵐ {𝟙ᵐ} ≈ᵐ idᵐ
  !-𝟙 = ≈ᵐ-sym terminalᵐ-unique

  -- a point is constant

  pt : ∀ {A} → (p : 𝟙ᵐ →ᵐ A) → p ≈ᵐ p ∘ᵐ terminalᵐ
  pt p = ≈ᵐ-sym (∘ᵐ-congʳ !-𝟙 ∙ ∘ᵐ-identityʳ p)

  -- a constant absorbs a precomposition

  const-∘ : ∀ {X Y A} → (c : 𝟙ᵐ →ᵐ A) → (h : X →ᵐ Y)
          → (c ∘ᵐ terminalᵐ) ∘ᵐ h ≈ᵐ c ∘ᵐ terminalᵐ
  const-∘ c h = ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ terminalᵐ-unique

  -- a constant at a point

  const-pt : ∀ {X A} → (c : 𝟙ᵐ →ᵐ A) → (h : 𝟙ᵐ →ᵐ X)
           → (c ∘ᵐ terminalᵐ) ∘ᵐ h ≈ᵐ c
  const-pt c h = const-∘ c h ∙ ≈ᵐ-sym (pt c)

  -- application of an abstraction, and of an uncurried map, at a pair

  app-curry : ∀ {X Y A B} → (k : X ×ᵐ A →ᵐ B) → (u : Y →ᵐ X) → (v : Y →ᵐ A)
            → appᵐ ∘ᵐ ⟨ curryᵐ k ∘ᵐ u , v ⟩ᵐ ≈ᵐ k ∘ᵐ ⟨ u , v ⟩ᵐ
  app-curry k u v =
      ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ (curryᵐ k) idᵐ u v
                        ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ v ⟩ᵐ-cong))
    ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙ ∘ᵐ-congˡ (appᵐ-curryᵐ k)

  uncurry-⟨⟩ : ∀ {X Y A B} → (h : X →ᵐ A ⇒ᵐ B) → (u : Y →ᵐ X) → (v : Y →ᵐ A)
             → uncurryᵐ h ∘ᵐ ⟨ u , v ⟩ᵐ ≈ᵐ appᵐ ∘ᵐ ⟨ h ∘ᵐ u , v ⟩ᵐ
  uncurry-⟨⟩ h u v =
      ∘ᵐ-congˡ (≈ᵐ-sym (appᵐ-mapˣᵐ h))
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ h idᵐ u v ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ v ⟩ᵐ-cong)

  -- an abstraction applied after a map into its domain

  app-curry-∘ : ∀ {X Y A B} → (k : X ×ᵐ A →ᵐ B) → (h : Y →ᵐ A ⇒ᵐ B)
              → (u : 𝟙ᵐ →ᵐ Y) → (v : 𝟙ᵐ →ᵐ A) → (w : 𝟙ᵐ →ᵐ X)
              → h ∘ᵐ u ≈ᵐ curryᵐ k ∘ᵐ w
              → appᵐ ∘ᵐ ⟨ h ∘ᵐ u , v ⟩ᵐ ≈ᵐ k ∘ᵐ ⟨ w , v ⟩ᵐ
  app-curry-∘ k h u v w e = ∘ᵐ-congʳ ⟨ e , ≈ᵐ-refl ⟩ᵐ-cong ∙ app-curry k w v

  -- projections out of a nested pair

  fst²-snd : ∀ {Y X S N} → (u : Y →ᵐ X) → (s : Y →ᵐ S) → (n : Y →ᵐ N)
           → ⟨ fstᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ∘ᵐ ⟨ ⟨ u , s ⟩ᵐ , n ⟩ᵐ ≈ᵐ ⟨ u , n ⟩ᵐ
  fst²-snd u s n =
      ⟨⟩ᵐ-∘ _ _ _
    ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ⟨⟩ᵐ-fstᵐ _ _ , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong

  -- the eliminators at a constructor in the second component

  match+ᵐ-inl-at : ∀ {Y X A B C} → (f : (X ×ᵐ (A +ᵐ B)) ×ᵐ A →ᵐ C)
                 → (g : (X ×ᵐ (A +ᵐ B)) ×ᵐ B →ᵐ C)
                 → (u : Y →ᵐ X) → (a : Y →ᵐ A)
                 → match+ᵐ sndᵐ f g ∘ᵐ ⟨ u , inlᵐ ∘ᵐ a ⟩ᵐ
                 ≈ᵐ f ∘ᵐ ⟨ ⟨ u , inlᵐ ∘ᵐ a ⟩ᵐ , a ⟩ᵐ
  match+ᵐ-inl-at f g u a =
      match+ᵐ-∘ sndᵐ f g ⟨ u , inlᵐ ∘ᵐ a ⟩ᵐ
    ∙ match+ᵐ-cong (⟨⟩ᵐ-sndᵐ _ _) ≈ᵐ-refl ≈ᵐ-refl
    ∙ match+ᵐ-inl a _ _
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)

  match+ᵐ-inr-at : ∀ {Y X A B C} → (f : (X ×ᵐ (A +ᵐ B)) ×ᵐ A →ᵐ C)
                 → (g : (X ×ᵐ (A +ᵐ B)) ×ᵐ B →ᵐ C)
                 → (u : Y →ᵐ X) → (b : Y →ᵐ B)
                 → match+ᵐ sndᵐ f g ∘ᵐ ⟨ u , inrᵐ ∘ᵐ b ⟩ᵐ
                 ≈ᵐ g ∘ᵐ ⟨ ⟨ u , inrᵐ ∘ᵐ b ⟩ᵐ , b ⟩ᵐ
  match+ᵐ-inr-at f g u b =
      match+ᵐ-∘ sndᵐ f g ⟨ u , inrᵐ ∘ᵐ b ⟩ᵐ
    ∙ match+ᵐ-cong (⟨⟩ᵐ-sndᵐ _ _) ≈ᵐ-refl ≈ᵐ-refl
    ∙ match+ᵐ-inr b _ _
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)

  matchℕᵐ-zero-at : ∀ {X C} → (f : X ×ᵐ ℕᵐ →ᵐ C) → (g : (X ×ᵐ ℕᵐ) ×ᵐ ℕᵐ →ᵐ C)
                  → (u : 𝟙ᵐ →ᵐ X)
                  → matchℕᵐ sndᵐ f g ∘ᵐ ⟨ u , zeroᵐ ⟩ᵐ ≈ᵐ f ∘ᵐ ⟨ u , zeroᵐ ⟩ᵐ
  matchℕᵐ-zero-at f g u =
      matchℕᵐ-∘ sndᵐ f g ⟨ u , zeroᵐ ⟩ᵐ
    ∙ matchℕᵐ-cong (⟨⟩ᵐ-sndᵐ _ _ ∙ pt zeroᵐ) ≈ᵐ-refl ≈ᵐ-refl
    ∙ matchℕᵐ-zero _ _

  matchℕᵐ-succ-at : ∀ {Y X C} → (f : X ×ᵐ ℕᵐ →ᵐ C) → (g : (X ×ᵐ ℕᵐ) ×ᵐ ℕᵐ →ᵐ C)
                  → (u : Y →ᵐ X) → (n : Y →ᵐ ℕᵐ)
                  → matchℕᵐ sndᵐ f g ∘ᵐ ⟨ u , succᵐ ∘ᵐ n ⟩ᵐ
                  ≈ᵐ g ∘ᵐ ⟨ ⟨ u , succᵐ ∘ᵐ n ⟩ᵐ , n ⟩ᵐ
  matchℕᵐ-succ-at f g u n =
      matchℕᵐ-∘ sndᵐ f g ⟨ u , succᵐ ∘ᵐ n ⟩ᵐ
    ∙ matchℕᵐ-cong (⟨⟩ᵐ-sndᵐ _ _) ≈ᵐ-refl ≈ᵐ-refl
    ∙ matchℕᵐ-succ n _ _
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)

  matchLᵐ-nil-at : ∀ {X A C} → (f : X ×ᵐ Listᵐ A →ᵐ C)
                 → (g : ((X ×ᵐ Listᵐ A) ×ᵐ A) ×ᵐ Listᵐ A →ᵐ C)
                 → (u : 𝟙ᵐ →ᵐ X)
                 → matchLᵐ sndᵐ f g ∘ᵐ ⟨ u , nilᵐ ⟩ᵐ ≈ᵐ f ∘ᵐ ⟨ u , nilᵐ ⟩ᵐ
  matchLᵐ-nil-at f g u =
      matchLᵐ-∘ sndᵐ f g ⟨ u , nilᵐ ⟩ᵐ
    ∙ matchLᵐ-cong (⟨⟩ᵐ-sndᵐ _ _ ∙ pt nilᵐ) ≈ᵐ-refl ≈ᵐ-refl
    ∙ matchLᵐ-nil _ _

  matchLᵐ-cons-at : ∀ {Y X A C} → (f : X ×ᵐ Listᵐ A →ᵐ C)
                  → (g : ((X ×ᵐ Listᵐ A) ×ᵐ A) ×ᵐ Listᵐ A →ᵐ C)
                  → (u : Y →ᵐ X) → (v : Y →ᵐ A) → (w : Y →ᵐ Listᵐ A)
                  → matchLᵐ sndᵐ f g ∘ᵐ ⟨ u , consᵐ ∘ᵐ ⟨ v , w ⟩ᵐ ⟩ᵐ
                  ≈ᵐ g ∘ᵐ ⟨ ⟨ ⟨ u , consᵐ ∘ᵐ ⟨ v , w ⟩ᵐ ⟩ᵐ , v ⟩ᵐ , w ⟩ᵐ
  matchLᵐ-cons-at f g u v w =
      matchLᵐ-∘ sndᵐ f g ⟨ u , consᵐ ∘ᵐ ⟨ v , w ⟩ᵐ ⟩ᵐ
    ∙ matchLᵐ-cong (⟨⟩ᵐ-sndᵐ _ _) ≈ᵐ-refl ≈ᵐ-refl
    ∙ matchLᵐ-cons v w _ _
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
               ∙ ⟨ mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
                 , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)

------------------------------------------------------------------------
-- Outcomes

Ordᵐ : Obj
Ordᵐ = 𝟙ᵐ +ᵐ (𝟙ᵐ +ᵐ 𝟙ᵐ)

⌜_⌝ᵒ : Order → 𝟙ᵐ →ᵐ Ordᵐ
⌜ less    ⌝ᵒ = inlᵐ
⌜ equal   ⌝ᵒ = inrᵐ ∘ᵐ inlᵐ
⌜ greater ⌝ᵒ = inrᵐ ∘ᵐ inrᵐ

⌜_⌝ᵇ : 𝔹 → 𝟙ᵐ →ᵐ 𝔹ᵐ
⌜ true  ⌝ᵇ = trueᵐ
⌜ false ⌝ᵇ = falseᵐ

-- Selecting by an outcome

selᵒ : ∀ {ℓ} {X : Set ℓ} → Order → X → X → X → X
selᵒ less    l e g = l
selᵒ equal   l e g = e
selᵒ greater l e g = g

-- Copairing out of the outcomes

[_,_,_]ᵒ : ∀ {C} → 𝟙ᵐ →ᵐ C → 𝟙ᵐ →ᵐ C → 𝟙ᵐ →ᵐ C → Ordᵐ →ᵐ C
[ l , e , g ]ᵒ = [ l , [ e , g ]ᵐ ]ᵐ

[]ᵒ-pt : ∀ {C} → (l e g : 𝟙ᵐ →ᵐ C) → (o : Order)
       → [ l , e , g ]ᵒ ∘ᵐ ⌜ o ⌝ᵒ ≈ᵐ selᵒ o l e g
[]ᵒ-pt l e g less    = []ᵐ-inlᵐ _ _
[]ᵒ-pt l e g equal   =
  ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ ([]ᵐ-inrᵐ _ _) ∙ []ᵐ-inlᵐ _ _
[]ᵒ-pt l e g greater =
  ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ ([]ᵐ-inrᵐ _ _) ∙ []ᵐ-inrᵐ _ _

-- The truth of a relation on an outcome

holdsᵐ : Cmp → Ordᵐ →ᵐ 𝔹ᵐ
holdsᵐ ⋈ = [ ⌜ holds ⋈ less ⌝ᵇ , ⌜ holds ⋈ equal ⌝ᵇ , ⌜ holds ⋈ greater ⌝ᵇ ]ᵒ

holdsᵐ-pt : (⋈ : Cmp) → (o : Order) → holdsᵐ ⋈ ∘ᵐ ⌜ o ⌝ᵒ ≈ᵐ ⌜ holds ⋈ o ⌝ᵇ
holdsᵐ-pt ⋈ less    = []ᵒ-pt _ _ _ less
holdsᵐ-pt ⋈ equal   = []ᵒ-pt _ _ _ equal
holdsᵐ-pt ⋈ greater = []ᵒ-pt _ _ _ greater

-- Lexicographic combination: the first outcome decides unless it is `equal`

lexᵐ : Ordᵐ ×ᵐ Ordᵐ →ᵐ Ordᵐ
lexᵐ = uncurryᵐ [ curryᵐ (⌜ less ⌝ᵒ ∘ᵐ terminalᵐ)
                , curryᵐ sndᵐ
                , curryᵐ (⌜ greater ⌝ᵒ ∘ᵐ terminalᵐ) ]ᵒ

lexᵐ-pt : (o o' : Order) → lexᵐ ∘ᵐ ⟨ ⌜ o ⌝ᵒ , ⌜ o' ⌝ᵒ ⟩ᵐ ≈ᵐ ⌜ lexᵒ o o' ⌝ᵒ
lexᵐ-pt o o' =
    uncurry-⟨⟩ _ ⌜ o ⌝ᵒ ⌜ o' ⌝ᵒ
  ∙ ∘ᵐ-congʳ ⟨ []ᵒ-pt _ _ _ o ∙ ≈ᵐ-sym (∘ᵐ-identityʳ _) , ≈ᵐ-refl ⟩ᵐ-cong
  ∙ go o
  where
    go : (o : Order)
       → appᵐ ∘ᵐ ⟨ selᵒ o (curryᵐ (⌜ less ⌝ᵒ ∘ᵐ terminalᵐ)) (curryᵐ sndᵐ)
                         (curryᵐ (⌜ greater ⌝ᵒ ∘ᵐ terminalᵐ)) ∘ᵐ idᵐ
                 , ⌜ o' ⌝ᵒ ⟩ᵐ
       ≈ᵐ ⌜ lexᵒ o o' ⌝ᵒ
    go less    = app-curry _ idᵐ _ ∙ const-pt _ _
    go equal   = app-curry _ idᵐ _ ∙ ⟨⟩ᵐ-sndᵐ _ _
    go greater = app-curry _ idᵐ _ ∙ const-pt _ _

------------------------------------------------------------------------
-- Comparisons

-- The comparison of a comparison at points: its outcome on two points.

Compares : ∀ {A} {D : Set} → (A ×ᵐ A →ᵐ Ordᵐ) → (D → 𝟙ᵐ →ᵐ A) → (D → D → Order) → Set
Compares {D = D} c ⌜_⌝ compare =
  (x y : D) → c ∘ᵐ ⟨ ⌜ x ⌝ , ⌜ y ⌝ ⟩ᵐ ≈ᵐ ⌜ compare x y ⌝ᵒ

-- the unit: always `equal`

cmp𝟙ᵐ : 𝟙ᵐ ×ᵐ 𝟙ᵐ →ᵐ Ordᵐ
cmp𝟙ᵐ = ⌜ equal ⌝ᵒ ∘ᵐ terminalᵐ

cmp𝟙ᵐ-pt : (u v : 𝟙ᵐ →ᵐ 𝟙ᵐ) → cmp𝟙ᵐ ∘ᵐ ⟨ u , v ⟩ᵐ ≈ᵐ ⌜ equal ⌝ᵒ
cmp𝟙ᵐ-pt u v = const-pt _ _

-- the empty object: vacuous

cmp𝟘ᵐ : 𝟘ᵐ ×ᵐ 𝟘ᵐ →ᵐ Ordᵐ
cmp𝟘ᵐ = initialᵐ ∘ᵐ fstᵐ

-- the booleans: `false` before `true`

private
  cmp𝔹-true cmp𝔹-false : 𝟙ᵐ ×ᵐ 𝔹ᵐ →ᵐ Ordᵐ
  cmp𝔹-true  = ifᵐ sndᵐ (⌜ equal ⌝ᵒ ∘ᵐ terminalᵐ) (⌜ greater ⌝ᵒ ∘ᵐ terminalᵐ)
  cmp𝔹-false = ifᵐ sndᵐ (⌜ less ⌝ᵒ ∘ᵐ terminalᵐ) (⌜ equal ⌝ᵒ ∘ᵐ terminalᵐ)

cmp𝔹ᵐ : 𝔹ᵐ ×ᵐ 𝔹ᵐ →ᵐ Ordᵐ
cmp𝔹ᵐ = uncurryᵐ (ifᵐ idᵐ (curryᵐ cmp𝔹-true ∘ᵐ terminalᵐ) (curryᵐ cmp𝔹-false ∘ᵐ terminalᵐ))

private
  -- `ifᵐ` at a boolean point

  if-at : ∀ {X A} → (b : 𝔹) → {s : X →ᵐ 𝔹ᵐ} → (f g : X →ᵐ A)
        → s ≈ᵐ ⌜ b ⌝ᵇ ∘ᵐ terminalᵐ → ifᵐ s f g ≈ᵐ selᵒ (compareᴮ b true) g f f
  if-at true  f g e = ifᵐ-cong e ≈ᵐ-refl ≈ᵐ-refl ∙ ifᵐ-true f g
  if-at false f g e = ifᵐ-cong e ≈ᵐ-refl ≈ᵐ-refl ∙ ifᵐ-false f g

  -- the inner comparisons at the second point

  inner-pt : ∀ {X} → (b' : 𝔹) → (l e : 𝟙ᵐ →ᵐ Ordᵐ) → (w : 𝟙ᵐ →ᵐ X)
           → ifᵐ sndᵐ (l ∘ᵐ terminalᵐ) (e ∘ᵐ terminalᵐ) ∘ᵐ ⟨ w , ⌜ b' ⌝ᵇ ⟩ᵐ
           ≈ᵐ selᵒ (compareᴮ b' true) e l l
  inner-pt true  l e w =
      ifᵐ-∘ _ _ _ _ ∙ if-at true _ _ (⟨⟩ᵐ-sndᵐ _ _ ∙ pt _) ∙ const-pt l _
  inner-pt false l e w =
      ifᵐ-∘ _ _ _ _ ∙ if-at false _ _ (⟨⟩ᵐ-sndᵐ _ _ ∙ pt _) ∙ const-pt e _

  outer-pt : (b : 𝔹)
           → ifᵐ idᵐ (curryᵐ cmp𝔹-true ∘ᵐ terminalᵐ) (curryᵐ cmp𝔹-false ∘ᵐ terminalᵐ)
             ∘ᵐ ⌜ b ⌝ᵇ
           ≈ᵐ selᵒ (compareᴮ b true) (curryᵐ cmp𝔹-false) (curryᵐ cmp𝔹-true) (curryᵐ cmp𝔹-true)
              ∘ᵐ (terminalᵐ ∘ᵐ ⌜ b ⌝ᵇ)
  outer-pt true  =
    ifᵐ-∘ _ _ _ _ ∙ if-at true _ _ (∘ᵐ-identityˡ _ ∙ pt _) ∙ ∘ᵐ-assoc _ _ _
  outer-pt false =
    ifᵐ-∘ _ _ _ _ ∙ if-at false _ _ (∘ᵐ-identityˡ _ ∙ pt _) ∙ ∘ᵐ-assoc _ _ _

cmp𝔹ᵐ-pt : Compares cmp𝔹ᵐ ⌜_⌝ᵇ compareᴮ
cmp𝔹ᵐ-pt b b' =
    uncurry-⟨⟩ _ ⌜ b ⌝ᵇ ⌜ b' ⌝ᵇ
  ∙ app-curry-∘ _ _ ⌜ b ⌝ᵇ ⌜ b' ⌝ᵇ (terminalᵐ ∘ᵐ ⌜ b ⌝ᵇ) (outer-pt b ∙ go b)
  ∙ fin b b'
  where
    go : (b : 𝔹) → selᵒ (compareᴮ b true) (curryᵐ cmp𝔹-false) (curryᵐ cmp𝔹-true)
                         (curryᵐ cmp𝔹-true) ∘ᵐ (terminalᵐ ∘ᵐ ⌜ b ⌝ᵇ)
                 ≈ᵐ curryᵐ (selᵒ (compareᴮ b true) cmp𝔹-false cmp𝔹-true cmp𝔹-true)
                   ∘ᵐ (terminalᵐ ∘ᵐ ⌜ b ⌝ᵇ)
    go true  = ≈ᵐ-refl
    go false = ≈ᵐ-refl

    fin : (b b' : 𝔹)
        → selᵒ (compareᴮ b true) cmp𝔹-false cmp𝔹-true cmp𝔹-true
          ∘ᵐ ⟨ terminalᵐ ∘ᵐ ⌜ b ⌝ᵇ , ⌜ b' ⌝ᵇ ⟩ᵐ
        ≈ᵐ ⌜ compareᴮ b b' ⌝ᵒ
    fin true  true  = inner-pt true  _ _ _
    fin true  false = inner-pt false _ _ _
    fin false true  = inner-pt true  _ _ _
    fin false false = inner-pt false _ _ _

-- the natural numbers: the usual order, by iteration into `ℕᵐ ⇒ᵐ Ordᵐ`

private
  cmpℕ-zero : 𝟙ᵐ ×ᵐ ℕᵐ →ᵐ Ordᵐ
  cmpℕ-zero = matchℕᵐ sndᵐ (⌜ equal ⌝ᵒ ∘ᵐ terminalᵐ) (⌜ less ⌝ᵒ ∘ᵐ terminalᵐ)

  cmpℕ-succ : (ℕᵐ ⇒ᵐ Ordᵐ) ×ᵐ ℕᵐ →ᵐ Ordᵐ
  cmpℕ-succ = matchℕᵐ sndᵐ (⌜ greater ⌝ᵒ ∘ᵐ terminalᵐ) (appᵐ ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ)

  cmpℕ-curried : ℕᵐ →ᵐ ℕᵐ ⇒ᵐ Ordᵐ
  cmpℕ-curried = iterᵐ (curryᵐ cmpℕ-zero) (curryᵐ cmpℕ-succ)

cmpℕᵐ : ℕᵐ ×ᵐ ℕᵐ →ᵐ Ordᵐ
cmpℕᵐ = uncurryᵐ cmpℕ-curried

⌜_⌝ᴺ : ℕ → 𝟙ᵐ →ᵐ ℕᵐ
⌜ zero  ⌝ᴺ = zeroᵐ
⌜ suc n ⌝ᴺ = succᵐ ∘ᵐ ⌜ n ⌝ᴺ

cmpℕᵐ-pt : Compares cmpℕᵐ ⌜_⌝ᴺ compareᴺ
cmpℕᵐ-pt n m = uncurry-⟨⟩ _ _ _ ∙ go n m
  where
    go : (n m : ℕ) → appᵐ ∘ᵐ ⟨ cmpℕ-curried ∘ᵐ ⌜ n ⌝ᴺ , ⌜ m ⌝ᴺ ⟩ᵐ ≈ᵐ ⌜ compareᴺ n m ⌝ᵒ
    go zero m =
        app-curry-∘ cmpℕ-zero _ _ _ idᵐ (iterᵐ-zero _ _ ∙ ≈ᵐ-sym (∘ᵐ-identityʳ _))
      ∙ at m
      where
        at : (m : ℕ) → cmpℕ-zero ∘ᵐ ⟨ idᵐ , ⌜ m ⌝ᴺ ⟩ᵐ ≈ᵐ ⌜ compareᴺ zero m ⌝ᵒ
        at zero    = matchℕᵐ-zero-at _ _ idᵐ ∙ const-pt _ _
        at (suc m) = matchℕᵐ-succ-at _ _ idᵐ ⌜ m ⌝ᴺ ∙ const-pt _ _
    go (suc n) m =
        app-curry-∘ cmpℕ-succ _ _ _ (cmpℕ-curried ∘ᵐ ⌜ n ⌝ᴺ)
          (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (iterᵐ-succ _ _) ∙ ∘ᵐ-assoc _ _ _)
      ∙ at m
      where
        at : (m : ℕ) → cmpℕ-succ ∘ᵐ ⟨ cmpℕ-curried ∘ᵐ ⌜ n ⌝ᴺ , ⌜ m ⌝ᴺ ⟩ᵐ
                     ≈ᵐ ⌜ compareᴺ (suc n) m ⌝ᵒ
        at zero    = matchℕᵐ-zero-at _ _ _ ∙ const-pt _ _
        at (suc m) =
            matchℕᵐ-succ-at _ _ _ ⌜ m ⌝ᴺ
          ∙ ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (fst²-snd _ _ _)
          ∙ go n m

-- products: lexicographic

cmp×ᵐ : ∀ {A B} → (A ×ᵐ A →ᵐ Ordᵐ) → (B ×ᵐ B →ᵐ Ordᵐ) → (A ×ᵐ B) ×ᵐ (A ×ᵐ B) →ᵐ Ordᵐ
cmp×ᵐ c d = lexᵐ ∘ᵐ ⟨ c ∘ᵐ mapˣᵐ fstᵐ fstᵐ , d ∘ᵐ mapˣᵐ sndᵐ sndᵐ ⟩ᵐ

cmp×ᵐ-⟨⟩ : ∀ {Y A B} → (c : A ×ᵐ A →ᵐ Ordᵐ) → (d : B ×ᵐ B →ᵐ Ordᵐ)
         → (a a' : Y →ᵐ A) → (b b' : Y →ᵐ B)
         → cmp×ᵐ c d ∘ᵐ ⟨ ⟨ a , b ⟩ᵐ , ⟨ a' , b' ⟩ᵐ ⟩ᵐ
         ≈ᵐ lexᵐ ∘ᵐ ⟨ c ∘ᵐ ⟨ a , a' ⟩ᵐ , d ∘ᵐ ⟨ b , b' ⟩ᵐ ⟩ᵐ
cmp×ᵐ-⟨⟩ c d a a' b b' =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _
             ∙ ⟨ ∘ᵐ-assoc _ _ _
                 ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _ , ⟨⟩ᵐ-fstᵐ _ _ ⟩ᵐ-cong)
               , ∘ᵐ-assoc _ _ _
                 ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ⟨⟩ᵐ-sndᵐ _ _ , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong) ⟩ᵐ-cong)

-- coproducts: the left summand first, then within each summand

cmp+ᵐ : ∀ {A B} → (A ×ᵐ A →ᵐ Ordᵐ) → (B ×ᵐ B →ᵐ Ordᵐ) → (A +ᵐ B) ×ᵐ (A +ᵐ B) →ᵐ Ordᵐ
cmp+ᵐ c d =
  uncurryᵐ [ curryᵐ (match+ᵐ sndᵐ (c ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ) (⌜ less ⌝ᵒ ∘ᵐ terminalᵐ))
           , curryᵐ (match+ᵐ sndᵐ (⌜ greater ⌝ᵒ ∘ᵐ terminalᵐ) (d ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ)) ]ᵐ

cmp+ᵐ-inl-inl : ∀ {A B} → (c : A ×ᵐ A →ᵐ Ordᵐ) → (d : B ×ᵐ B →ᵐ Ordᵐ) → (a a' : 𝟙ᵐ →ᵐ A)
              → cmp+ᵐ c d ∘ᵐ ⟨ inlᵐ ∘ᵐ a , inlᵐ ∘ᵐ a' ⟩ᵐ ≈ᵐ c ∘ᵐ ⟨ a , a' ⟩ᵐ
cmp+ᵐ-inl-inl c d a a' =
    uncurry-⟨⟩ _ _ _
  ∙ app-curry-∘ _ _ _ _ a (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ ([]ᵐ-inlᵐ _ _))
  ∙ match+ᵐ-inl-at _ _ a a'
  ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (fst²-snd _ _ _)

cmp+ᵐ-inl-inr : ∀ {A B} → (c : A ×ᵐ A →ᵐ Ordᵐ) → (d : B ×ᵐ B →ᵐ Ordᵐ)
              → (a : 𝟙ᵐ →ᵐ A) → (b : 𝟙ᵐ →ᵐ B)
              → cmp+ᵐ c d ∘ᵐ ⟨ inlᵐ ∘ᵐ a , inrᵐ ∘ᵐ b ⟩ᵐ ≈ᵐ ⌜ less ⌝ᵒ
cmp+ᵐ-inl-inr c d a b =
    uncurry-⟨⟩ _ _ _
  ∙ app-curry-∘ _ _ _ _ a (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ ([]ᵐ-inlᵐ _ _))
  ∙ match+ᵐ-inr-at _ _ a b
  ∙ const-pt _ _

cmp+ᵐ-inr-inl : ∀ {A B} → (c : A ×ᵐ A →ᵐ Ordᵐ) → (d : B ×ᵐ B →ᵐ Ordᵐ)
              → (b : 𝟙ᵐ →ᵐ B) → (a : 𝟙ᵐ →ᵐ A)
              → cmp+ᵐ c d ∘ᵐ ⟨ inrᵐ ∘ᵐ b , inlᵐ ∘ᵐ a ⟩ᵐ ≈ᵐ ⌜ greater ⌝ᵒ
cmp+ᵐ-inr-inl c d b a =
    uncurry-⟨⟩ _ _ _
  ∙ app-curry-∘ _ _ _ _ b (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ ([]ᵐ-inrᵐ _ _))
  ∙ match+ᵐ-inl-at _ _ b a
  ∙ const-pt _ _

cmp+ᵐ-inr-inr : ∀ {A B} → (c : A ×ᵐ A →ᵐ Ordᵐ) → (d : B ×ᵐ B →ᵐ Ordᵐ) → (b b' : 𝟙ᵐ →ᵐ B)
              → cmp+ᵐ c d ∘ᵐ ⟨ inrᵐ ∘ᵐ b , inrᵐ ∘ᵐ b' ⟩ᵐ ≈ᵐ d ∘ᵐ ⟨ b , b' ⟩ᵐ
cmp+ᵐ-inr-inr c d b b' =
    uncurry-⟨⟩ _ _ _
  ∙ app-curry-∘ _ _ _ _ b (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ ([]ᵐ-inrᵐ _ _))
  ∙ match+ᵐ-inr-at _ _ b b'
  ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (fst²-snd _ _ _)

-- lists: lexicographic, the empty list first, by a fold into `Listᵐ A ⇒ᵐ Ordᵐ`

⌜_⌝ᴸ : ∀ {A} {D : Set} → (D → 𝟙ᵐ →ᵐ A) → List D → 𝟙ᵐ →ᵐ Listᵐ A
⌜ point ⌝ᴸ []       = nilᵐ
⌜ point ⌝ᴸ (x ∷ xs) = consᵐ ∘ᵐ ⟨ point x , ⌜ point ⌝ᴸ xs ⟩ᵐ

module _ {A : Obj} (c : A ×ᵐ A →ᵐ Ordᵐ) where

  private
    cmpL-nil : 𝟙ᵐ ×ᵐ Listᵐ A →ᵐ Ordᵐ
    cmpL-nil = matchLᵐ sndᵐ (⌜ equal ⌝ᵒ ∘ᵐ terminalᵐ) (⌜ less ⌝ᵒ ∘ᵐ terminalᵐ)

    -- at a head `x`, the recursive comparison `φ` of the tail, and a list
    cmpL-cons : (A ×ᵐ (Listᵐ A ⇒ᵐ Ordᵐ)) ×ᵐ Listᵐ A →ᵐ Ordᵐ
    cmpL-cons =
      matchLᵐ sndᵐ (⌜ greater ⌝ᵒ ∘ᵐ terminalᵐ)
        (lexᵐ ∘ᵐ ⟨ c ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ , sndᵐ ∘ᵐ fstᵐ ⟩ᵐ
                 , appᵐ ∘ᵐ ⟨ sndᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ)

    cmpL-curried : Listᵐ A →ᵐ Listᵐ A ⇒ᵐ Ordᵐ
    cmpL-curried = foldᵐ (curryᵐ cmpL-nil) (curryᵐ cmpL-cons)

  cmpLᵐ : Listᵐ A ×ᵐ Listᵐ A →ᵐ Ordᵐ
  cmpLᵐ = uncurryᵐ cmpL-curried

  module _ {D : Set} (point : D → 𝟙ᵐ →ᵐ A) (compare : D → D → Order)
           (hc : Compares c point compare) where

    cmpLᵐ-pt : Compares cmpLᵐ ⌜ point ⌝ᴸ (compareᴸ compare)
    cmpLᵐ-pt xs ys = uncurry-⟨⟩ _ _ _ ∙ go xs ys
      where
        go : (xs ys : List D)
           → appᵐ ∘ᵐ ⟨ cmpL-curried ∘ᵐ ⌜ point ⌝ᴸ xs , ⌜ point ⌝ᴸ ys ⟩ᵐ ≈ᵐ ⌜ compareᴸ compare xs ys ⌝ᵒ
        go [] ys =
            app-curry-∘ cmpL-nil _ _ _ idᵐ (foldᵐ-nil _ _ ∙ ≈ᵐ-sym (∘ᵐ-identityʳ _))
          ∙ at ys
          where
            at : (ys : List D) → cmpL-nil ∘ᵐ ⟨ idᵐ , ⌜ point ⌝ᴸ ys ⟩ᵐ
                               ≈ᵐ ⌜ compareᴸ compare [] ys ⌝ᵒ
            at []       = matchLᵐ-nil-at _ _ idᵐ ∙ const-pt _ _
            at (y ∷ ys) = matchLᵐ-cons-at _ _ idᵐ (point y) (⌜ point ⌝ᴸ ys) ∙ const-pt _ _
        go (x ∷ xs) ys =
            app-curry-∘ cmpL-cons _ _ _ w
              (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
               ∙ ∘ᵐ-congˡ (foldᵐ-cons _ _)
               ∙ ∘ᵐ-assoc _ _ _
               ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
          ∙ at ys
          where
            w : 𝟙ᵐ →ᵐ A ×ᵐ (Listᵐ A ⇒ᵐ Ordᵐ)
            w = ⟨ point x , cmpL-curried ∘ᵐ ⌜ point ⌝ᴸ xs ⟩ᵐ

            at : (ys : List D) → cmpL-cons ∘ᵐ ⟨ w , ⌜ point ⌝ᴸ ys ⟩ᵐ
                               ≈ᵐ ⌜ compareᴸ compare (x ∷ xs) ys ⌝ᵒ
            at []       = matchLᵐ-nil-at _ _ w ∙ const-pt _ _
            at (y ∷ ys) =
                matchLᵐ-cons-at _ _ w (point y) (⌜ point ⌝ᴸ ys)
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _
                         ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _ ∙ ⟨ px , py ⟩ᵐ-cong) ∙ hc x y
                           , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _ ∙ ⟨ pφ , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)
                             ∙ go xs ys ⟩ᵐ-cong)
              ∙ lexᵐ-pt (compare x y) (compareᴸ compare xs ys)
              where
                Z : 𝟙ᵐ →ᵐ ((((A ×ᵐ (Listᵐ A ⇒ᵐ Ordᵐ)) ×ᵐ Listᵐ A) ×ᵐ A) ×ᵐ Listᵐ A)
                Z = ⟨ ⟨ ⟨ w , consᵐ ∘ᵐ ⟨ point y , ⌜ point ⌝ᴸ ys ⟩ᵐ ⟩ᵐ , point y ⟩ᵐ , ⌜ point ⌝ᴸ ys ⟩ᵐ

                -- the head of the first list, three pairs down
                w≈ : fstᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ ∘ᵐ Z ≈ᵐ w
                w≈ = ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ⟨⟩ᵐ-fstᵐ _ _) ∙ ⟨⟩ᵐ-fstᵐ _ _

                px : (fstᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ) ∘ᵐ Z ≈ᵐ point x
                px =  ∘ᵐ-assoc _ _ _
                    ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _) ∙ w≈)
                    ∙ ⟨⟩ᵐ-fstᵐ _ _

                pφ : (sndᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ ∘ᵐ fstᵐ) ∘ᵐ Z ≈ᵐ cmpL-curried ∘ᵐ ⌜ point ⌝ᴸ xs
                pφ =  ∘ᵐ-assoc _ _ _
                    ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _) ∙ w≈)
                    ∙ ⟨⟩ᵐ-sndᵐ _ _

                py : (sndᵐ ∘ᵐ fstᵐ) ∘ᵐ Z ≈ᵐ point y
                py = ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ⟨⟩ᵐ-sndᵐ _ _
