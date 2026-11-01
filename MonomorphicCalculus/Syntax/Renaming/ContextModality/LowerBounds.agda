---------------------------------------------------------------------------
-- The context modality when the unit is the greatest grade (`⊤ ≾ 𝟏`),   --
-- as for lower bounds: a parametric right adjoint at every grade        --
-- (`PRA-everywhere`).                                                   --
--                                                                       --
-- `Γ ↑` cuts `Γ` at the rightmost position whose suffix's modalities    --
-- multiply to a grade `≾ ρ`, dropping the suffix whole (`Cut`). When    --
-- `(Γ ↓ L_ρ)` is nonempty, `(Γ ↑ , η)` is initial in it (`initial`),    --
-- and the familial representation                                       --
--   Ren [] Γ (Δ ⟨ ρ ⟩)  ≅  (ctx-grade Γ · 𝟏 ≾ ρ) × Ren [] (Γ ↑) Δ       --
-- holds up to `_≐ʳ_` (`familial`). It is the form                       --
-- `Hom(Γ, L Δ) ≅ Σ (s : Γ → L 1) Hom(E s, Δ)` of                        --
-- `Renaming/ContextModality`: there is at most one `s : Γ → [] ⟨ ρ ⟩`,  --
-- and one exactly when `ctx-grade Γ · 𝟏 ≾ ρ`, so the `Σ` is that        --
-- proposition, and `Γ ↑` plays `E s`. See M. Weber, Familial 2-functors --
-- and parametric right adjoints, Theory Appl. Categ. 18 (2007) 665-732. --
--                                                                       --
-- Every renaming `Y → Y'` lifts to the cuts (`lift`, by induction on    --
-- the renaming) and agrees with the lift on variables (`lift-img`).     --
---------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Base
open import Language.Spec

open import Util.Equality

module MonomorphicCalculus.Syntax.Renaming.ContextModality.LowerBounds (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import MonomorphicCalculus.Syntax.Contexts             S
open import MonomorphicCalculus.Syntax.Renaming             S
open import MonomorphicCalculus.Syntax.Renaming.Equivalence S
open import MonomorphicCalculus.Syntax.Renaming.ContextModality        S

module UnitGreatest (top : ⊤ᵣ ≾ᵣ 𝟏ᵣ) (ρ : R) where

  all≾𝟏 : (σ : R) → σ ≾ᵣ 𝟏ᵣ
  all≾𝟏 σ = ≾ᵣ-trans (≾-⊤ᵣ σ) top

  -- deleting a modality

  del : ∀ {Y σ} → Ren [] (Y ⟨ σ ⟩) Y
  del {σ = σ} = ⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (all≾𝟏 σ)

  ----------------------------------------------------------------------
  -- Cuts. `Cut a Y P`: `P` is the prefix of `Y` left at the rightmost
  -- position whose modalities to the right, times `a`, are `≾ ρ`; `drop`
  -- passes a position that is not.

  mutual

    data Cut : R → Ctx → Ctx → Set where
      stop : ∀ {a Y}   → a ≾ᵣ ρ → Cut a Y Y
      drop : ∀ {a Y P} → ¬ (a ≾ᵣ ρ) → Step a Y P → Cut a Y P

    data Step : R → Ctx → Ctx → Set where
      s-∷  : ∀ {a Y A P} → Cut a Y P → Step a (Y ∷ A) P
      s-⟨⟩ : ∀ {a Y σ P} → Cut (σ ·ᵣ a) Y P → Step a (Y ⟨ σ ⟩) P
      s-[] : ∀ {a} → Step a [] []

  mutual

    cut : (a : R) → (Y : Ctx) → Σ[ P ∈ Ctx ] Cut a Y P
    cut a Y = cut-dec a Y (a ≾ᵣ? ρ)

    cut-dec : (a : R) → (Y : Ctx) → Dec (a ≾ᵣ ρ) → Σ[ P ∈ Ctx ] Cut a Y P
    cut-dec a Y         (yes p) = Y , stop p
    cut-dec a []        (no n)  = [] , drop n s-[]
    cut-dec a (Y ∷ A)   (no n)  = proj₁ (cut a Y) , drop n (s-∷ (proj₂ (cut a Y)))
    cut-dec a (Y ⟨ σ ⟩) (no n)  =
      proj₁ (cut (σ ·ᵣ a) Y) , drop n (s-⟨⟩ (proj₂ (cut (σ ·ᵣ a) Y)))

  _↑ : Ctx → Ctx
  Γ ↑ = proj₁ (cut 𝟏ᵣ Γ)

  -- a cut's prefix sits inside the context: on variables, and as a renaming

  emb : ∀ {a Y P C} → Cut a Y P → Var P C → Var Y C
  emb (stop _)                      w = w
  emb (drop _ (s-∷ c))              w = Var-∷ (emb c w)
  emb (drop _ (s-⟨⟩ {σ = σ} c))     w = Var-⟨⟩ σ (emb c w)
  emb (drop _ s-[])                 w = w

  prefix : ∀ {a Y P} → Cut a Y P → Ren [] Y P
  prefix (stop _)           = id-ren
  prefix (drop _ (s-∷ c))   = prefix c ∘ʳ wk-ren
  prefix (drop _ (s-⟨⟩ c))  = prefix c ∘ʳ del
  prefix (drop _ s-[])      = id-ren

  prefix-img : ∀ {a Y P C} → (c : Cut a Y P) → (w : Var P C)
             → var-img′ (prefix c) w ≡ emb c w
  prefix-img (stop _)          w = refl
  prefix-img (drop _ (s-∷ c))  w = cong Var-∷ (prefix-img c w)
  prefix-img (drop _ (s-⟨⟩ {σ = σ} c)) w = cong (Var-⟨⟩ σ) (prefix-img c w)
  prefix-img (drop _ s-[])     w = refl

  -- a smaller accumulated grade cuts further right

  mono : ∀ {a' a Y P' P} → a' ≾ᵣ a → Cut a' Y P' → Cut a Y P → Ren [] P' P
  mono q (stop _)               c                       = prefix c
  mono q (drop n' _)            (stop p)                = ⊥-elim (n' (≾ᵣ-trans q p))
  mono q (drop _ (s-∷ c'))      (drop _ (s-∷ c))        = mono q c' c
  mono q (drop _ (s-⟨⟩ c'))     (drop _ (s-⟨⟩ c))       = mono (·ᵣ-monoʳ-≾ᵣ q) c' c
  mono q (drop _ s-[])          (drop _ s-[])           = id-ren

  mono-img : ∀ {a' a Y P' P C} → (q : a' ≾ᵣ a) → (c' : Cut a' Y P') → (c : Cut a Y P)
           → (w : Var P C) → emb c' (var-img′ (mono q c' c) w) ≡ emb c w
  mono-img q (stop _)            c                   w = prefix-img c w
  mono-img q (drop n' _)         (stop p)            w = ⊥-elim (n' (≾ᵣ-trans q p))
  mono-img q (drop _ (s-∷ c'))   (drop _ (s-∷ c))    w = cong Var-∷ (mono-img q c' c w)
  mono-img q (drop _ (s-⟨⟩ {σ = σ} c')) (drop _ (s-⟨⟩ c)) w =
    cong (Var-⟨⟩ σ) (mono-img (·ᵣ-monoʳ-≾ᵣ q) c' c w)
  mono-img q (drop _ s-[])       (drop _ s-[])       w = refl

  ----------------------------------------------------------------------
  -- Lifting a renaming to the cuts

  lift : ∀ {a Y Y' P P'} → Ren [] Y Y' → Cut a Y P → Cut a Y' P' → Ren [] P P'
  lift id-ren c c' = mono ≾ᵣ-refl c c'
  lift {a} (_∘ʳ_ {Δ' = Y₁} r₂ r₁) c c' =
    lift r₂ (proj₂ (cut a Y₁)) c' ∘ʳ lift r₁ c (proj₂ (cut a Y₁))
  lift wk-ren (stop p)               c'  = prefix c' ∘ʳ wk-ren
  lift wk-ren (drop n (s-∷ c₀))      c'  = mono ≾ᵣ-refl c₀ c'
  lift (var-ren x ok) c              (drop n' (s-∷ c₀'))  = mono ≾ᵣ-refl c c₀'
  lift (var-ren x ok) (stop p)       (stop p')            = var-ren x ok
  lift (var-ren x ok) (drop n _)     (stop p')            = ⊥-elim (n p')
  lift {a} ⟨⟩-η-ren c                (drop n' (s-⟨⟩ c₀')) =
    mono (≃ᵣ⇒≿ᵣ (·ᵣ-identityˡ a)) c c₀'
  lift ⟨⟩-η-ren (stop p)             (stop p')            = ⟨⟩-η-ren
  lift ⟨⟩-η-ren (drop n _)           (stop p')            = ⊥-elim (n p')
  lift ⟨⟩-η⁻¹-ren (stop p)           c'  = prefix c' ∘ʳ ⟨⟩-η⁻¹-ren
  lift {a} ⟨⟩-η⁻¹-ren (drop n (s-⟨⟩ c₀)) c' = mono (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ a)) c₀ c'
  lift ⟨⟩-μ-ren (stop p)             (stop p')            = ⟨⟩-μ-ren
  lift ⟨⟩-μ-ren (stop p)             (drop n' _)          = ⊥-elim (n' p)
  lift ⟨⟩-μ-ren (drop n _)           (stop p')            = ⊥-elim (n p')
  lift ⟨⟩-μ-ren (drop n (s-⟨⟩ (stop p₁))) (drop n' (s-⟨⟩ c₀')) = prefix c₀' ∘ʳ del
  lift {a} (⟨⟩-μ-ren {ρ = σ} {ρ' = σ'}) (drop n (s-⟨⟩ (drop n₁ (s-⟨⟩ c₂)))) (drop n' (s-⟨⟩ c₀')) =
    mono (≃ᵣ⇒≿ᵣ (·ᵣ-assoc σ σ' a)) c₂ c₀'
  lift (⟨⟩-≤-ren q) (stop p)         (stop p')            = ⟨⟩-≤-ren q
  lift (⟨⟩-≤-ren q) (stop p)         (drop n' _)          = ⊥-elim (n' p)
  lift (⟨⟩-≤-ren q) (drop n _)       (stop p')            = ⊥-elim (n p')
  lift (⟨⟩-≤-ren q) (drop n (s-⟨⟩ c₀)) (drop n' (s-⟨⟩ c₀')) = mono (·ᵣ-monoˡ-≾ᵣ q) c₀ c₀'
  lift (⟨⟩-ext-ctx e ec) (stop p)    c'  = prefix c' ∘ʳ ⟨⟩-ext-ctx e ec
  lift {a} (⟨⟩-ext-ctx {ρ = σ} e ec) (drop n (s-⟨⟩ c₀)) c' =
    mono (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (all≾𝟏 σ)) (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ a))) c₀ c'
  lift (cong-∷-ren r) (stop p)       (stop p')            = cong-∷-ren r
  lift (cong-∷-ren r) (stop p)       (drop n' _)          = ⊥-elim (n' p)
  lift (cong-∷-ren r) (drop n _)     (stop p')            = ⊥-elim (n p')
  lift (cong-∷-ren r) (drop n (s-∷ c₀)) (drop n' (s-∷ c₀')) = lift r c₀ c₀'
  lift (cong-⟨⟩-ren r) (stop p)      (stop p')            = cong-⟨⟩-ren r
  lift (cong-⟨⟩-ren r) (stop p)      (drop n' _)          = ⊥-elim (n' p)
  lift (cong-⟨⟩-ren r) (drop n _)    (stop p')            = ⊥-elim (n p')
  lift (cong-⟨⟩-ren r) (drop n (s-⟨⟩ c₀)) (drop n' (s-⟨⟩ c₀')) = lift r c₀ c₀'

  -- the lift agrees with the renaming on variables

  lift-img : ∀ {a Y Y' P P' C} → (r : Ren [] Y Y') → (c : Cut a Y P) → (c' : Cut a Y' P')
           → (w : Var P' C) → emb c (var-img′ (lift r c c') w) ≡ var-img′ r (emb c' w)
  lift-img id-ren c c' w = mono-img ≾ᵣ-refl c c' w
  lift-img {a} (_∘ʳ_ {Δ' = Y₁} r₂ r₁) c c' w =
    trans (lift-img r₁ c (proj₂ (cut a Y₁)) _)
          (cong (var-img′ r₁) (lift-img r₂ (proj₂ (cut a Y₁)) c' w))
  lift-img wk-ren (stop p)               c'  w = cong Var-∷ (prefix-img c' w)
  lift-img wk-ren (drop n (s-∷ c₀))      c'  w = cong Var-∷ (mono-img ≾ᵣ-refl c₀ c' w)
  lift-img (var-ren x ok) c              (drop n' (s-∷ c₀'))  w = mono-img ≾ᵣ-refl c c₀' w
  lift-img (var-ren x ok) (stop p)       (stop p')            w = refl
  lift-img (var-ren x ok) (drop n _)     (stop p')            w = ⊥-elim (n p')
  lift-img {a} ⟨⟩-η-ren c                (drop n' (s-⟨⟩ c₀')) w =
    mono-img (≃ᵣ⇒≿ᵣ (·ᵣ-identityˡ a)) c c₀' w
  lift-img ⟨⟩-η-ren (stop p)             (stop p')            w = refl
  lift-img ⟨⟩-η-ren (drop n _)           (stop p')            w = ⊥-elim (n p')
  lift-img ⟨⟩-η⁻¹-ren (stop p)           c'  w = cong (var-img′ ⟨⟩-η⁻¹-ren) (prefix-img c' w)
  lift-img {a} ⟨⟩-η⁻¹-ren (drop n (s-⟨⟩ c₀)) c' w =
    cong (Var-⟨⟩ 𝟏ᵣ) (mono-img (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ a)) c₀ c' w)
  lift-img ⟨⟩-μ-ren (stop p)             (stop p')            w = refl
  lift-img ⟨⟩-μ-ren (stop p)             (drop n' _)          w = ⊥-elim (n' p)
  lift-img ⟨⟩-μ-ren (drop n _)           (stop p')            w = ⊥-elim (n p')
  lift-img (⟨⟩-μ-ren {ρ = σ} {ρ' = σ'}) (drop n (s-⟨⟩ (stop p₁))) (drop n' (s-⟨⟩ c₀')) w =
    cong (λ v → Var-⟨⟩ σ' (Var-⟨⟩ σ v)) (prefix-img c₀' w)
  lift-img {a} (⟨⟩-μ-ren {ρ = σ} {ρ' = σ'}) (drop n (s-⟨⟩ (drop n₁ (s-⟨⟩ c₂)))) (drop n' (s-⟨⟩ c₀')) w =
    cong (λ v → Var-⟨⟩ σ' (Var-⟨⟩ σ v)) (mono-img (≃ᵣ⇒≿ᵣ (·ᵣ-assoc σ σ' a)) c₂ c₀' w)
  lift-img (⟨⟩-≤-ren q) (stop p)         (stop p')            w = refl
  lift-img (⟨⟩-≤-ren q) (stop p)         (drop n' _)          w = ⊥-elim (n' p)
  lift-img (⟨⟩-≤-ren q) (drop n _)       (stop p')            w = ⊥-elim (n p')
  lift-img (⟨⟩-≤-ren {ρ' = σ'} q) (drop n (s-⟨⟩ c₀)) (drop n' (s-⟨⟩ c₀')) w =
    cong (Var-⟨⟩ σ') (mono-img (·ᵣ-monoˡ-≾ᵣ q) c₀ c₀' w)
  lift-img (⟨⟩-ext-ctx e ec) (stop p)    c'  w = cong (var-img′ (⟨⟩-ext-ctx e ec)) (prefix-img c' w)
  lift-img {a} (⟨⟩-ext-ctx {ρ = σ} e ec) (drop n (s-⟨⟩ c₀)) c' w =
    cong (Var-⟨⟩ σ)
      (mono-img (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (all≾𝟏 σ)) (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ a))) c₀ c' w)
  lift-img (cong-∷-ren r) (stop p)       (stop p')            w = refl
  lift-img (cong-∷-ren r) (stop p)       (drop n' _)          w = ⊥-elim (n' p)
  lift-img (cong-∷-ren r) (drop n _)     (stop p')            w = ⊥-elim (n p')
  lift-img (cong-∷-ren r) (drop n (s-∷ c₀)) (drop n' (s-∷ c₀')) w = cong Var-∷ (lift-img r c₀ c₀' w)
  lift-img (cong-⟨⟩-ren r) (stop p)      (stop p')            w = refl
  lift-img (cong-⟨⟩-ren r) (stop p)      (drop n' _)          w = ⊥-elim (n' p)
  lift-img (cong-⟨⟩-ren r) (drop n _)    (stop p')            w = ⊥-elim (n p')
  lift-img (cong-⟨⟩-ren {ρ = σ} r) (drop n (s-⟨⟩ c₀)) (drop n' (s-⟨⟩ c₀')) w =
    cong (Var-⟨⟩ σ) (lift-img r c₀ c₀' w)

  ----------------------------------------------------------------------
  -- Unit and counit

  -- renamings do not decrease the elapsed grade (the unit being greatest)

  ren-grade : ∀ {Y Y'} → Ren [] Y Y' → ctx-grade Y ≾ᵣ ctx-grade Y'
  ren-grade id-ren                 = ≾ᵣ-refl
  ren-grade (r₂ ∘ʳ r₁)             = ≾ᵣ-trans (ren-grade r₁) (ren-grade r₂)
  ren-grade wk-ren                 = ≾ᵣ-refl
  ren-grade (var-ren x ok)         = ≾ᵣ-refl
  ren-grade ⟨⟩-η-ren               = ≃ᵣ⇒≿ᵣ (·ᵣ-identityʳ _)
  ren-grade ⟨⟩-η⁻¹-ren             = ≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ _)
  ren-grade ⟨⟩-μ-ren               = ≃ᵣ⇒≾ᵣ (·ᵣ-assoc _ _ _)
  ren-grade (⟨⟩-≤-ren q)           = ·ᵣ-monoʳ-≾ᵣ q
  ren-grade (⟨⟩-ext-ctx {ρ = σ} _ _) =
    ≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ (all≾𝟏 σ)) (≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ _))
  ren-grade (cong-∷-ren r)         = ren-grade r
  ren-grade (cong-⟨⟩-ren r)        = ·ᵣ-monoˡ-≾ᵣ (ren-grade r)

  unitᶜ : ∀ {a Y P} → Cut a Y P → ctx-grade Y ·ᵣ a ≾ᵣ ρ → Ren [] (Y ⟨ a ⟩) (P ⟨ ρ ⟩)
  unitᶜ (stop p)             h = ⟨⟩-≤-ren p
  unitᶜ (drop n (s-∷ c))     h = unitᶜ c h ∘ʳ cong-⟨⟩-ren wk-ren
  unitᶜ {a} {Y ⟨ σ ⟩} (drop n (s-⟨⟩ c)) h =
    unitᶜ c (≾ᵣ-trans (≃ᵣ⇒≿ᵣ (·ᵣ-assoc (ctx-grade Y) σ a)) h) ∘ʳ ⟨⟩-μ-ren
  unitᶜ {a} (drop n s-[])    h = ⊥-elim (n (≾ᵣ-trans (≃ᵣ⇒≿ᵣ (·ᵣ-identityˡ a)) h))

  unitᶜ-img : ∀ {a Y P C} → (c : Cut a Y P) → (h : ctx-grade Y ·ᵣ a ≾ᵣ ρ) → (w : Var P C)
           → var-img′ (unitᶜ c h) (Var-⟨⟩ ρ w) ≡ Var-⟨⟩ a (emb c w)
  unitᶜ-img (stop p)          h w = refl
  unitᶜ-img {a} (drop n (s-∷ c)) h w =
    cong (var-img′ (cong-⟨⟩-ren wk-ren)) (unitᶜ-img c h w)
  unitᶜ-img {a} {Y ⟨ σ ⟩} (drop n (s-⟨⟩ c)) h w =
    cong (var-img′ ⟨⟩-μ-ren)
      (unitᶜ-img c (≾ᵣ-trans (≃ᵣ⇒≿ᵣ (·ᵣ-assoc (ctx-grade Y) σ a)) h) w)
  unitᶜ-img {a} (drop n s-[]) h w = ⊥-elim (n (≾ᵣ-trans (≃ᵣ⇒≿ᵣ (·ᵣ-identityˡ a)) h))

  counit : ∀ {Δ P'} → Cut 𝟏ᵣ (Δ ⟨ ρ ⟩) P' → Ren [] P' Δ
  counit (stop p)                         = del
  counit (drop n (s-⟨⟩ (stop p)))         = id-ren
  counit (drop n (s-⟨⟩ (drop n₁ _)))      = ⊥-elim (n₁ (≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ ρ)))

  counit-img : ∀ {Δ P' C} → (c' : Cut 𝟏ᵣ (Δ ⟨ ρ ⟩) P') → (w : Var Δ C)
             → emb c' (var-img′ (counit c') w) ≡ Var-⟨⟩ ρ w
  counit-img (stop p)                    w = refl
  counit-img (drop n (s-⟨⟩ (stop p)))    w = refl
  counit-img (drop n (s-⟨⟩ (drop n₁ _))) w = ⊥-elim (n₁ (≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ ρ)))

  -- the cut's variable embedding is injective

  Var-∷-inj : ∀ {Y B C} {v v' : Var Y C} → Var-∷ {B = B} v ≡ Var-∷ v' → v ≡ v'
  Var-∷-inj {v = σ , y} {v' = .σ , .y} refl = refl

  un-⟨⟩ : ∀ {Y σ C} → Var (Y ⟨ σ ⟩) C → Var Y C
  un-⟨⟩ (_ , Tl-⟨⟩ y) = _ , y

  Var-⟨⟩-inj : ∀ {Y C σ} {v v' : Var Y C} → Var-⟨⟩ σ v ≡ Var-⟨⟩ σ v' → v ≡ v'
  Var-⟨⟩-inj {Y} {C} {σ} {v} {v'} e = cong (un-⟨⟩ {Y} {σ} {C}) {Var-⟨⟩ σ v} {Var-⟨⟩ σ v'} e

  emb-inj : ∀ {a Y P C} → (c : Cut a Y P) → {v v' : Var P C} → emb c v ≡ emb c v' → v ≡ v'
  emb-inj (stop _)          e = e
  emb-inj (drop _ (s-∷ c))  e = emb-inj c (Var-∷-inj e)
  emb-inj (drop _ (s-⟨⟩ c)) e = emb-inj c (Var-⟨⟩-inj e)
  emb-inj (drop _ s-[])     e = e

  ----------------------------------------------------------------------
  -- The initial object

  module _ {Γ : Ctx} (h : ctx-grade Γ ·ᵣ 𝟏ᵣ ≾ᵣ ρ) where

    cΓ : Cut 𝟏ᵣ Γ (Γ ↑)
    cΓ = proj₂ (cut 𝟏ᵣ Γ)

    ηΓ : Ren [] Γ ((Γ ↑) ⟨ ρ ⟩)
    ηΓ = unitᶜ cΓ h ∘ʳ ⟨⟩-η-ren

    Iᵘ : Comma ρ Γ
    Iᵘ = (Γ ↑) ,ᵒ ηΓ

    -- the composite with the unit, on variables

    through : ∀ {Δ C σ} → (g : Ren [] (Γ ↑) Δ) → (y : C ∈[ σ ] Δ)
            → var-img (cong-⟨⟩-ren g ∘ʳ ηΓ) (Tl-⟨⟩ y) ≡ emb cΓ (var-img g y)
    through g y = cong (var-img′ ⟨⟩-η-ren) (unitᶜ-img cΓ h (var-img g y))

    transpose : ∀ {Δ} → Ren [] Γ (Δ ⟨ ρ ⟩) → Ren [] (Γ ↑) Δ
    transpose {Δ} f = counit c' ∘ʳ lift f cΓ c'
      where c' = proj₂ (cut 𝟏ᵣ (Δ ⟨ ρ ⟩))

    transpose-tri : ∀ {Δ} → (f : Ren [] Γ (Δ ⟨ ρ ⟩))
                  → (cong-⟨⟩-ren (transpose f) ∘ʳ ηΓ) ≐ʳ f
    transpose-tri {Δ} f = mk≐ʳ go
      where
      c' = proj₂ (cut 𝟏ᵣ (Δ ⟨ ρ ⟩))
      go : ∀ {C σ} → (x : C ∈[ σ ] (Δ ⟨ ρ ⟩))
         → var-img (cong-⟨⟩-ren (transpose f) ∘ʳ ηΓ) x ≡ var-img f x
      go (Tl-⟨⟩ y) =
        trans (through (transpose f) y)
          (trans (lift-img f cΓ c' (var-img (counit c') y))
                 (cong (var-img′ f) (counit-img c' (_ , y))))

    transpose-unique : ∀ {Δ} → (f : Ren [] Γ (Δ ⟨ ρ ⟩)) → (g : Ren [] (Γ ↑) Δ)
                     → (cong-⟨⟩-ren g ∘ʳ ηΓ) ≐ʳ f → g ≐ʳ transpose f
    transpose-unique f g e =
      mk≐ʳ (λ y → emb-inj cΓ
        (trans (sym (through g y))
          (trans (at e (Tl-⟨⟩ y))
            (trans (sym (at (transpose-tri f) (Tl-⟨⟩ y))) (through (transpose f) y)))))

    initialᵘ : Initial Iᵘ
    initialᵘ X =
        (transpose (str X) ,ʰ transpose-tri (str X))
      , λ h' → transpose-unique (str X) (map h') (tri h')

  -- an object gives the grade bound

  comma-grade : ∀ {Γ} → Comma ρ Γ → ctx-grade Γ ·ᵣ 𝟏ᵣ ≾ᵣ ρ
  comma-grade {Γ} X =
    ≾ᵣ-trans (≃ᵣ⇒≾ᵣ (·ᵣ-identityʳ (ctx-grade Γ)))
      (≾ᵣ-trans (ren-grade (str X))
        (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (all≾𝟏 (ctx-grade (ctx X))))
          (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ ρ))))

  initial : ∀ {Γ} → Comma ρ Γ → Σ[ I ∈ Comma ρ Γ ] Initial I
  initial X = Iᵘ (comma-grade X) , initialᵘ (comma-grade X)

  is-PRA : PRA ρ
  is-PRA Γ X =
    proj₁ (initial X) , fwd (proj₁ (proj₂ (initial X) X)) here
    , λ Y _ → proj₂ (initial X) Y

  -- the familial representation, over the proposition
  -- `ctx-grade Γ · 𝟏 ≾ ρ`

  familial : ∀ {Γ Δ}
    → Σ[ φ ∈ (Ren [] Γ (Δ ⟨ ρ ⟩) → Σ[ s ∈ ctx-grade Γ ·ᵣ 𝟏ᵣ ≾ᵣ ρ ] Ren [] (Γ ↑) Δ) ]
      Σ[ ψ ∈ (Σ[ s ∈ ctx-grade Γ ·ᵣ 𝟏ᵣ ≾ᵣ ρ ] Ren [] (Γ ↑) Δ → Ren [] Γ (Δ ⟨ ρ ⟩)) ]
        ((∀ f → ψ (φ f) ≐ʳ f) × (∀ s g → proj₂ (φ (ψ (s , g))) ≐ʳ g))
  familial {Γ} {Δ} =
      (λ f → s f , transpose (s f) f)
    , (λ { (s , g) → cong-⟨⟩-ren g ∘ʳ ηΓ s })
    , (λ f → transpose-tri (s f) f)
    , λ s₀ g → ≐ʳ-sym (transpose-unique (s (cong-⟨⟩-ren g ∘ʳ ηΓ s₀))
                         (cong-⟨⟩-ren g ∘ʳ ηΓ s₀) g
                         (subst (λ s₁ → (cong-⟨⟩-ren g ∘ʳ ηΓ s₁) ≐ʳ (cong-⟨⟩-ren g ∘ʳ ηΓ s₀))
                                (≾ᵣ-irrelevant s₀ _) ≐ʳ-refl))
    where
    s : Ren [] Γ (Δ ⟨ ρ ⟩) → ctx-grade Γ ·ᵣ 𝟏ᵣ ≾ᵣ ρ
    s f = comma-grade (Δ ,ᵒ f)

-- when the unit is the greatest grade, the context modality is a parametric
-- right adjoint at every grade

PRA-everywhere : ⊤ᵣ ≾ᵣ 𝟏ᵣ → (ρ : R) → PRA ρ
PRA-everywhere top ρ = UnitGreatest.is-PRA top ρ
