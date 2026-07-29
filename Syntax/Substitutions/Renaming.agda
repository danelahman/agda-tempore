------------------------------------------------------------------------
-- Renaming a prefix commutes with substituting at the variable past it.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions.Renaming (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts      Spec
open import Syntax.Language      Spec
open import Syntax.RenActions    Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

open import Syntax.Renamings.Equivalence    Spec
open import Syntax.Renamings.Coherence      Spec
open import Syntax.Terms.Equivalence        Spec
open import Syntax.Terms.Transport          Spec
open import Syntax.Substitutions.Equivalence Spec
open import Syntax.Substitutions.Variables   Spec
open import Syntax.Substitutions.Weakening   Spec

------------------------------------------------------------------------
-- RENAMING COMMUTES WITH SUBSTITUTION
--
-- Renaming a prefix and substituting at the variable just past it are
-- independent, so they may be done in either order — the value substituted
-- picking up the renaming when it goes second. Stated at an arbitrary suffix,
-- as `sub-wk`, and for the same reason: every binding former grows it.
------------------------------------------------------------------------

-- The three renamings the variable substitution puts in front of its recursive
-- call are natural in a renaming of the prefix.

wk-ren-nat : ∀ {Γ Γ' A} → (r : Ren [] Γ Γ')
           → (cong-∷-ren {A = A} r ∘ʳ wk-ren) ≐ʳ (wk-ren ∘ʳ r)
wk-ren-nat r = mk≐ʳ (λ y → cong-ren-tgt-l r ([] ∷ _) y)

⟨⟩-ren-nat : ∀ {Γ Γ' ρ} → (r : Ren [] Γ Γ')
           → (rn : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩))
           → (∀ {A σ} → (y : A ∈[ σ ] Γ') → var-tgt rn y ≡ Tgt-⟨⟩ ρ (σ , y))
           → (∀ {A σ} → (y : A ∈[ σ ] Γ)  → var-tgt rn y ≡ Tgt-⟨⟩ ρ (σ , y))
           → (cong-⟨⟩-ren r ∘ʳ rn) ≐ʳ (rn ∘ʳ r)
⟨⟩-ren-nat {ρ = ρ} r rn h' h = mk≐ʳ go
  where
    go : ∀ {A σ} → (y : A ∈[ σ ] _) → _
    go y =
      trans (cong (var-tgt′ (cong-⟨⟩-ren r)) (h y))
            (sym (h' (proj₂ (var-tgt r y))))

hit-⟨⟩-tgt : ∀ {Γ A σ ρ} → (p : ρ ≾ᵣ uᵣ) → (y : A ∈[ σ ] Γ)
           → var-tgt (⟨⟩-≤-ren p ∘ʳ ⟨⟩-η⁻¹-ren {Δ = Γ}) y ≡ Tgt-⟨⟩ ρ (σ , y)
hit-⟨⟩-tgt p y = cong (var-tgt′ (⟨⟩-≤-ren p)) (⟨⟩-η⁻¹-tgt y)

-- An eternal extension is natural: it builds only variables, constants, `⋆` and
-- pairs, so a renaming passes through it.

eternal-val-ext-ren : ∀ {Γ Γ' A ρ} → (et : Eternal A) → (r : Ren [] Γ Γ')
                    → (V : Γ ⊢V⦂ A)
                    → V-rename (cong-⟨⟩-ren {ρ = ρ} r) (eternal-val-ext et V)
                    ≐ᵛ eternal-val-ext et (V-rename r V)
eternal-val-ext-ren et             r (var f x)   = var-≐
eternal-val-ext-ren et             r (const c)   = const-≐
eternal-val-ext-ren et             r ⋆           = ⋆-≐
eternal-val-ext-ren (et₁ |×|ₑ et₂) r ⦉ V₁ , V₂ ⦊ =
  pair-≐ (eternal-val-ext-ren et₁ r V₁) (eternal-val-ext-ren et₂ r V₂)

-- THE VARIABLE SUBSTITUTED FOR
--
-- Looking up the variable being replaced returns the value, pushed under the
-- suffix — a push the recursion of `⟨_,_⟩[_↦_]var` builds one layer at a time,
-- and each layer is natural in a renaming of the prefix.

ren-sub-hit : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
            → (f f' : ¬ Eternal B → ctx-grade Θ ≾ᵣ uᵣ)
            → V-rename (cong-ren {Γ'' = Θ} r)
                (castᵛ (castOf {Γ} {B} Θ)
                  (⟨ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) , f
                   ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                      ↦ castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W
                    ]var))
            ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                 (⟨ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ}) , f'
                  ⟩[ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                     ↦ castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                             (V-rename r W)
                   ]var)

ren-sub-hit r [] W f f' = ≐ᵛ-refl _

ren-sub-hit {Γ} {Γ'} {B} r (Θ ∷ C) W f f' =
  ≐ᵛ-trans
    (≡→≐ᵛ (cong (V-rename (cong-∷-ren (cong-ren {Γ'' = Θ} r)))
                (cast-wk-any (castOf {Γ} {B} (Θ ∷ C)) (castOf {Γ} {B} Θ) _)))
    (≐ᵛ-trans (≐ᵛ-sym (V-rename-∘ (cong-∷-ren (cong-ren {Γ'' = Θ} r)) wk-ren _))
      (≐ᵛ-trans (V-rename-≐ (wk-ren-nat (cong-ren {Γ'' = Θ} r)) _)
        (≐ᵛ-trans (V-rename-∘ wk-ren (cong-ren {Γ'' = Θ} r) _)
          (≐ᵛ-trans (V-rename-cong wk-ren (ren-sub-hit r Θ W f f'))
                    (≡→≐ᵛ (sym (cast-wk-any (castOf {Γ'} {B} (Θ ∷ C))
                                            (castOf {Γ'} {B} Θ) _)))))))

ren-sub-hit {Γ} {Γ'} {B} r (Θ ⟨ ρ ⟩) W f f' with eternal? B

... | yes et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cong (V-rename (cong-⟨⟩-ren (cong-ren {Γ'' = Θ} r)))
                (cast-ext-any (castOf {Γ} {B} (Θ ⟨ ρ ⟩))
                              (castOf {Γ} {B} Θ) et _)))
    (≐ᵛ-trans (eternal-val-ext-ren et (cong-ren {Γ'' = Θ} r) _)
      (≐ᵛ-trans (eternal-val-ext-cong et (ren-sub-hit r Θ W _ _))
                (≡→≐ᵛ (sym (cast-ext-any (castOf {Γ'} {B} (Θ ⟨ ρ ⟩))
                                         (castOf {Γ'} {B} Θ) et _)))))

... | no ¬et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cong (V-rename (cong-⟨⟩-ren ρ₀))
                (cast-ren-⟨⟩-any (castOf {Γ} {B} (Θ ⟨ ρ ⟩))
                                 (castOf {Γ} {B} Θ) rn _)))
    (≐ᵛ-trans (≐ᵛ-sym (V-rename-∘ (cong-⟨⟩-ren ρ₀) rn _))
      (≐ᵛ-trans (V-rename-≐ (⟨⟩-ren-nat ρ₀ rn (λ y → hit-⟨⟩-tgt bd y)
                                              (λ y → hit-⟨⟩-tgt bd y)) _)
        (≐ᵛ-trans (V-rename-∘ rn ρ₀ _)
          (≐ᵛ-trans (V-rename-cong rn (ren-sub-hit r Θ W _ _))
            (≐ᵛ-trans (V-rename-≐ (∘ʳ-≐ (⟨⟩-≤-ren-≐ _ _) ≐ʳ-refl) _)
                      (≡→≐ᵛ (sym (cast-ren-⟨⟩-any (castOf {Γ'} {B} (Θ ⟨ ρ ⟩))
                                                  (castOf {Γ'} {B} Θ) rn' _))))))))
  where
    ρ₀ = cong-ren {Γ'' = Θ} r
    bd = ≾ᵣ-zero-productʳ (f ¬et)

    rn : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩)
    rn = ⟨⟩-≤-ren bd ∘ʳ ⟨⟩-η⁻¹-ren

    rn' : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩)
    rn' = ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f' ¬et)) ∘ʳ ⟨⟩-η⁻¹-ren

-- The same, taking both variables as equations: what reaches the substitution
-- on either side is `∈-++ᶜˡ Θ Hd`, which is `split→∈` of the splitting only up
-- to `split→∈-∈-++ᶜˡ`.

ren-sub-hit′ : ∀ {Γ Γ' B σ σ'} → (r : Ren [] Γ Γ') → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
             → (y  : B ∈[ σ  ] ((Γ  ∷ B) ++ᶜ Θ))
             → (y' : B ∈[ σ' ] ((Γ' ∷ B) ++ᶜ Θ))
             → (f  : ¬ Eternal B → σ  ≾ᵣ uᵣ)
             → (f' : ¬ Eternal B → σ' ≾ᵣ uᵣ)
             → _≡_ {A = Tgt ((Γ ∷ B) ++ᶜ Θ) B}
                 (σ , y) (ctx-grade Θ , split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}))
             → _≡_ {A = Tgt ((Γ' ∷ B) ++ᶜ Θ) B}
                 (σ' , y') (ctx-grade Θ , split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ}))
             → V-rename (cong-ren {Γ'' = Θ} r)
                 (castᵛ (castOf {Γ} {B} Θ)
                   (⟨ y , f ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                               ↦ castᵛ (sym (split→∈-split-l
                                               (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]var))
             ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                  (⟨ y' , f' ⟩[ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                                ↦ castᵛ (sym (split→∈-split-l
                                                (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                                        (V-rename r W) ]var)
ren-sub-hit′ r Θ W _ _ f f' refl refl = ren-sub-hit r Θ W f f'

-- A SUFFIX VARIABLE
--
-- Neither the renaming nor the substitution moves it, in either order.

ren-sub-var-r : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → ∀ {A ρ}
              → (z : A ∈[ ρ ] Θ) → (W : Γ ⊢V⦂ B)
              → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
              → V-rename (cong-ren {Γ'' = Θ} r)
                  (castᵛ (castOf {Γ} {B} Θ)
                    (⟨ ∈-++ᶜʳ {Γ = Γ ∷ B} z , f
                     ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                        ↦ castᵛ (sym (split→∈-split-l
                                        (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]var))
              ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                   ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                              (var f' (∈-++ᶜʳ {Γ = Γ ∷ B} z)))
                      [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                        ↦ castᵛ (sym (split→∈-split-l
                                        (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                                (V-rename r W) ]v)

ren-sub-var-r {Γ} {Γ'} {B} r Θ z W f f' =
  ≐ᵛ-trans (V-rename-cong (cong-ren {Γ'' = Θ} r) (sub-var-r Θ z _ f f))
    (≐ᵛ-trans (var-ren-tgt-≐ (cong-ren {Γ'' = Θ} r) (∈-++ᶜʳ {Γ = Γ} z) f
                             (cong-ren-tgt-r r z) f)
      (≐ᵛ-sym
        (≐ᵛ-trans
          (castᵛ-≐ (castOf {Γ'} {B} Θ)
            (sub-≐ᵛ (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})) (≐ᵛ-refl _)
              (var-ren-tgt-≐ (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                             (∈-++ᶜʳ {Γ = Γ ∷ B} z) f'
                             (cong-ren-tgt-r (cong-∷-ren r) z) f')))
          (sub-var-r Θ z _ f' f))))

-- A PREFIX VARIABLE
--
-- The substitution fixes it on either side, and the renaming moves it to its
-- own image, pushed under the suffix.

ren-sub-var-l : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → ∀ {A ρ}
              → (z : A ∈[ ρ ] Γ) → (W : Γ ⊢V⦂ B)
              → (f f' : ¬ Eternal A → grade-++ᶜˡ ρ Θ ≾ᵣ uᵣ)
              → V-rename (cong-ren {Γ'' = Θ} r)
                  (castᵛ (castOf {Γ} {B} Θ)
                    (⟨ ∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Tl-∷ z) , f
                     ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                        ↦ castᵛ (sym (split→∈-split-l
                                        (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]var))
              ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                   ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                              (var f' (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Tl-∷ z))))
                      [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                        ↦ castᵛ (sym (split→∈-split-l
                                        (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                                (V-rename r W) ]v)

ren-sub-var-l {Γ} {Γ'} {B} r Θ z W f f' =
  ≐ᵛ-trans (V-rename-cong (cong-ren {Γ'' = Θ} r) (sub-var-l Θ z _ f f))
    (≐ᵛ-trans (var-ren-tgt-≐ (cong-ren {Γ'' = Θ} r) (∈-++ᶜˡ {Γ = Γ} Θ z) f
                             (cong-ren-tgt-l r Θ z) fr)
      (≐ᵛ-sym
        (≐ᵛ-trans
          (castᵛ-≐ (castOf {Γ'} {B} Θ)
            (sub-≐ᵛ (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})) (≐ᵛ-refl _)
              (var-ren-tgt-≐ (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                             (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Tl-∷ z)) f'
                             (cong-ren-tgt-l (cong-∷-ren r) Θ (Tl-∷ z)) fr)))
          (sub-var-l Θ (proj₂ (var-tgt r z)) _ fr fr))))
  where
    -- a renaming only lowers a variable's grade, and the suffix's contribution
    -- is monotone in it, so the bound survives
    fr = λ ¬et → ≾ᵣ-trans (grade-++ᶜˡ-mono Θ
                            (proj₁ (proj₂ (var-rename r z)) ¬et))
                          (f ¬et)

-- THE VARIABLE BEING REPLACED
--
-- `ren-sub-hit` with the variable presented as `∈-++ᶜˡ Θ Hd`, which is where
-- the splitting leaves it, and the renamed side folded into the same shape.

ren-sub-var-hd : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
               → (f f' : ¬ Eternal B → grade-++ᶜˡ uᵣ Θ ≾ᵣ uᵣ)
               → V-rename (cong-ren {Γ'' = Θ} r)
                   (castᵛ (castOf {Γ} {B} Θ)
                     (⟨ ∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Hd {Γ = Γ}) , f
                      ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                         ↦ castᵛ (sym (split→∈-split-l
                                         (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]var))
               ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                    ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                               (var f' (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Hd {Γ = Γ}))))
                       [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                         ↦ castᵛ (sym (split→∈-split-l
                                         (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                                 (V-rename r W) ]v)

ren-sub-var-hd {Γ} {Γ'} {B} r Θ W f f' =
  ≐ᵛ-trans
    (ren-sub-hit′ r Θ W (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Hd {Γ = Γ}))
                        (∈-++ᶜˡ {Γ = Γ' ∷ B} Θ (Hd {Γ = Γ'})) f f'
                  (sym (split→∈-∈-++ᶜˡ Γ B Θ)) (sym (split→∈-∈-++ᶜˡ Γ' B Θ)))
    (≐ᵛ-sym
      (castᵛ-≐ (castOf {Γ'} {B} Θ)
        (sub-≐ᵛ (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})) (≐ᵛ-refl _)
          (var-ren-tgt-≐ (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                         (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Hd {Γ = Γ})) f'
                         (cong-ren-tgt-l (cong-∷-ren r) Θ (Hd {Γ = Γ})) f'))))

-- THE VARIABLE CASE
--
-- Which of the three applies is what `∈-++ᶜ-split` decides, the prefix's own
-- head being the variable replaced.

ren-sub-var : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → ∀ {A ρ}
            → (y : A ∈[ ρ ] ((Γ ∷ B) ++ᶜ Θ)) → (W : Γ ⊢V⦂ B)
            → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
            → V-rename (cong-ren {Γ'' = Θ} r)
                (castᵛ (castOf {Γ} {B} Θ)
                  (⟨ y , f ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                              ↦ castᵛ (sym (split→∈-split-l
                                              (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]var))
            ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                 ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) (var f' y))
                    [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                      ↦ castᵛ (sym (split→∈-split-l
                                      (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                              (V-rename r W) ]v)

ren-sub-var {Γ} {Γ'} {B} r Θ {A} {ρ} y W f f'
  with ∈-++ᶜ-split (Γ ∷ B) Θ y in eq

... | inj₂ z
  rewrite ∈-++ᶜ-split-inj₂ (Γ ∷ B) Θ y z eq = ren-sub-var-r r Θ z W f f'

... | inj₁ (ρ'' , z) =
  subst (λ t → (fu f'u : ¬ Eternal A → proj₁ t ≾ᵣ uᵣ)
             → V-rename (cong-ren {Γ'' = Θ} r)
                 (castᵛ (castOf {Γ} {B} Θ)
                   (⟨ proj₂ t , fu
                    ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                       ↦ castᵛ (sym (split→∈-split-l
                                       (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]var))
             ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                  ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                             (var f'u (proj₂ t)))
                     [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                       ↦ castᵛ (sym (split→∈-split-l
                                       (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                               (V-rename r W) ]v))
        (sym (∈-++ᶜ-split-inj₁ (Γ ∷ B) Θ y z eq))
        (go z)
        f f'
  where
    go : ∀ {ρ₀} → (z₀ : A ∈[ ρ₀ ] (Γ ∷ B))
       → (fu f'u : ¬ Eternal A → grade-++ᶜˡ ρ₀ Θ ≾ᵣ uᵣ)
       → V-rename (cong-ren {Γ'' = Θ} r)
           (castᵛ (castOf {Γ} {B} Θ)
             (⟨ ∈-++ᶜˡ {Γ = Γ ∷ B} Θ z₀ , fu
              ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                 ↦ castᵛ (sym (split→∈-split-l
                                 (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]var))
       ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
            ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                       (var f'u (∈-++ᶜˡ {Γ = Γ ∷ B} Θ z₀)))
               [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                 ↦ castᵛ (sym (split→∈-split-l
                                 (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                         (V-rename r W) ]v)
    go Hd        fu f'u = ren-sub-var-hd r Θ W fu f'u
    go (Tl-∷ z₀) fu f'u = ren-sub-var-l r Θ z₀ W fu f'u

-- THE CELL AN `unbox` NAMES, RENAMED AND SUBSTITUTED
--
-- `unbox-cell-wk`'s counterpart: the cell survives both orders. The third case
-- a weakening could not reach is here — the cell may *be* the variable
-- replaced, and then it is the one inside the substituted value, which is of
-- box type and so a variable itself.

rvar-hit-ren : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → (Θ : Ctx)
             → (W : Γ ⊢V⦂ [ ρ ] A)
             → var-tgt′ (cong-ren {Γ'' = Θ} r)
                 (Tgt-cast (castOf {Γ} {[ ρ ] A} Θ)
                   (rvar-tgt (split→∈ (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))
                             (split→∈ (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))
                             (castᵛ (sym (split→∈-split-l
                                            (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))) W)))
             ≡ Tgt-cast (castOf {Γ'} {[ ρ ] A} Θ)
                 (rvar-tgt (split→∈ (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ}))
                           (split→∈ (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ}))
                           (castᵛ (sym (split→∈-split-l
                                          (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ})))
                                  (V-rename r W)))

rvar-hit-ren r [] (var f y) = refl

rvar-hit-ren {Γ} {Γ'} {A} {ρ} r (Θ ∷ C) W =
  trans (cong (var-tgt′ (cong-∷-ren (cong-ren {Γ'' = Θ} r)))
              (trans (Tgt-cast-irr (castOf {Γ} {[ ρ ] A} (Θ ∷ C))
                                   (cong (_∷ C) (castOf {Γ} {[ ρ ] A} Θ)) _)
                     (Tgt-cast-∷ (castOf {Γ} {[ ρ ] A} Θ) _)))
    (trans (cong Tgt-∷ (rvar-hit-ren r Θ W))
      (trans (sym (Tgt-cast-∷ (castOf {Γ'} {[ ρ ] A} Θ) _))
             (Tgt-cast-irr (cong (_∷ C) (castOf {Γ'} {[ ρ ] A} Θ))
                           (castOf {Γ'} {[ ρ ] A} (Θ ∷ C)) _)))

rvar-hit-ren {Γ} {Γ'} {A} {ρ} r (Θ ⟨ ρ' ⟩) W =
  trans (cong (var-tgt′ (cong-⟨⟩-ren (cong-ren {Γ'' = Θ} r)))
              (trans (Tgt-cast-irr (castOf {Γ} {[ ρ ] A} (Θ ⟨ ρ' ⟩))
                                   (cong (_⟨ ρ' ⟩) (castOf {Γ} {[ ρ ] A} Θ)) _)
                     (Tgt-cast-⟨⟩ ρ' (castOf {Γ} {[ ρ ] A} Θ) _)))
    (trans (cong (Tgt-⟨⟩ ρ') (rvar-hit-ren r Θ W))
      (trans (sym (Tgt-cast-⟨⟩ ρ' (castOf {Γ'} {[ ρ ] A} Θ) _))
             (Tgt-cast-irr (cong (_⟨ ρ' ⟩) (castOf {Γ'} {[ ρ ] A} Θ))
                           (castOf {Γ'} {[ ρ ] A} (Θ ⟨ ρ' ⟩)) _)))

rvar-hit-ren′ : ∀ {Γ Γ' A ρ σ} → (r : Ren [] Γ Γ') → (Θ : Ctx)
              → (W : Γ ⊢V⦂ [ ρ ] A)
              → (c  : [ ρ ] A ∈[ σ ] ((Γ ∷ [ ρ ] A) ++ᶜ Θ))
              → (t' : Tgt ((Γ' ∷ [ ρ ] A) ++ᶜ Θ) ([ ρ ] A))
              → _≡_ {A = Tgt ((Γ ∷ [ ρ ] A) ++ᶜ Θ) ([ ρ ] A)}
                  (σ , c)
                  (ctx-grade Θ , split→∈ (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))
              → t' ≡ (ctx-grade Θ , split→∈ (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ}))
              → var-tgt′ (cong-ren {Γ'' = Θ} r)
                  (Tgt-cast (castOf {Γ} {[ ρ ] A} Θ)
                    (rvar-tgt c (split→∈ (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))
                              (castᵛ (sym (split→∈-split-l
                                             (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))) W)))
              ≡ Tgt-cast (castOf {Γ'} {[ ρ ] A} Θ)
                  (rvar-tgt (proj₂ t')
                            (split→∈ (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ}))
                            (castᵛ (sym (split→∈-split-l
                                           (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ})))
                                   (V-rename r W)))
rvar-hit-ren′ r Θ W _ _ refl refl = rvar-hit-ren r Θ W

unbox-cell-ren : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → ∀ {A ρ σ}
               → (c : [ ρ ] A ∈[ σ ] ((Γ ∷ B) ++ᶜ Θ)) → (W : Γ ⊢V⦂ B)
               → var-tgt′ (cong-ren {Γ'' = Θ} r)
                   (Tgt-cast (castOf {Γ} {B} Θ)
                     (rvar-tgt c (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}))
                               (castᵛ (sym (split→∈-split-l
                                              (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W)))
               ≡ Tgt-cast (castOf {Γ'} {B} Θ)
                   (rvar-tgt (proj₂ (var-tgt (cong-ren {Γ'' = Θ} (cong-∷-ren r)) c))
                             (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ}))
                             (castᵛ (sym (split→∈-split-l
                                            (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                                    (V-rename r W)))

unbox-cell-ren {Γ} {Γ'} {B} r Θ {A} {ρ} {σ} c W
  with ∈-++ᶜ-split (Γ ∷ B) Θ c in eqc

... | inj₂ c'
  rewrite ∈-++ᶜ-split-inj₂ (Γ ∷ B) Θ c c' eqc =
  trans (cong (var-tgt′ (cong-ren {Γ'' = Θ} r)) (sub-rvar-r Θ c' _))
    (trans (cong-ren-tgt-r r c')
           (sym (sub-rvar-r′ Θ c' _ (cong-ren-tgt-r (cong-∷-ren r) c') _)))

... | inj₁ (σ' , c') =
  subst (λ t → var-tgt′ (cong-ren {Γ'' = Θ} r)
                 (Tgt-cast (castOf {Γ} {B} Θ)
                   (rvar-tgt (proj₂ t) (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}))
                             (castᵛ (sym (split→∈-split-l
                                            (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W)))
             ≡ Tgt-cast (castOf {Γ'} {B} Θ)
                 (rvar-tgt (proj₂ (var-tgt (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                                           (proj₂ t)))
                           (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ}))
                           (castᵛ (sym (split→∈-split-l
                                          (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                                  (V-rename r W))))
        (sym (∈-++ᶜ-split-inj₁ (Γ ∷ B) Θ c c' eqc))
        (go c')
  where
    go : ∀ {σ₀} → (c₀ : [ ρ ] A ∈[ σ₀ ] (Γ ∷ B))
       → var-tgt′ (cong-ren {Γ'' = Θ} r)
           (Tgt-cast (castOf {Γ} {B} Θ)
             (rvar-tgt (∈-++ᶜˡ {Γ = Γ ∷ B} Θ c₀)
                       (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}))
                       (castᵛ (sym (split→∈-split-l
                                      (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W)))
       ≡ Tgt-cast (castOf {Γ'} {B} Θ)
           (rvar-tgt (proj₂ (var-tgt (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                                     (∈-++ᶜˡ {Γ = Γ ∷ B} Θ c₀)))
                     (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ}))
                     (castᵛ (sym (split→∈-split-l
                                    (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                            (V-rename r W)))

    go Hd =
      rvar-hit-ren′ r Θ W (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Hd {Γ = Γ})) _
        (sym (split→∈-∈-++ᶜˡ Γ B Θ))
        (trans (cong-ren-tgt-l (cong-∷-ren r) Θ (Hd {Γ = Γ}))
               (sym (split→∈-∈-++ᶜˡ Γ' B Θ)))

    go (Tl-∷ c₀) =
      trans (cong (var-tgt′ (cong-ren {Γ'' = Θ} r)) (sub-rvar-l Θ c₀ _))
        (trans (cong-ren-tgt-l r Θ c₀)
               (sym (sub-rvar-l′ Θ (proj₂ (var-tgt r c₀)) _
                       (cong-ren-tgt-l (cong-∷-ren r) Θ (Tl-∷ c₀)) _)))


-- The two formers that do not simply distribute: `unbox`, whose boxed value is
-- a variable the substitution relocates, and `handle`, whose clauses see the
-- substitution only through the eternal restriction. Both are stated so that
-- the induction below can hand them its hypothesis at the grown suffix.

-- `unbox`: both orders rebuild the unboxing from the cell the substitution
-- leaves (`sub-unbox`), and `unbox-cell-ren` says the two cells agree. The body
-- is the induction hypothesis at the grown suffix, taken as an argument so that
-- this can stand outside the induction.

ren-sub-unbox
  : ∀ {Γ Γ' B A ρ C Δ} → (r : Ren [] Γ Γ') → (Θ : Ctx)
  → (w : Ren [] (Δ ⟨ ρ ⟩) ((Γ ∷ B) ++ᶜ Θ))
  → (V : Δ ⊢V⦂ [ ρ ] A)
  → (M : (((Γ ∷ B) ++ᶜ Θ) ∷ A) ⊢C⦂ C) → (W : Γ ⊢V⦂ B)
  → (ih : C-rename (cong-ren {Γ'' = Θ ∷ A} r)
            (castᶜ (castOf {Γ} {B} (Θ ∷ A))
              (M [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ ∷ A})
                   ↦ castᵛ (sym (split→∈-split-l
                                   (split-≡-++ᶜ {Γ ∷ B} {Θ ∷ A}))) W ]c))
          ≐ᶜ castᶜ (castOf {Γ'} {B} (Θ ∷ A))
               ((C-rename (cong-ren {Γ'' = Θ ∷ A} (cong-∷-ren r)) M)
                  [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ ∷ A})
                    ↦ castᵛ (sym (split→∈-split-l
                                    (split-≡-++ᶜ {Γ' ∷ B} {Θ ∷ A})))
                            (V-rename r W) ]c))
  → C-rename (cong-ren {Γ'' = Θ} r)
      (castᶜ (castOf {Γ} {B} Θ)
        (unbox w V M [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                       ↦ castᵛ (sym (split→∈-split-l
                                       (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]c))
  ≐ᶜ castᶜ (castOf {Γ'} {B} Θ)
       ((C-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) (unbox w V M))
          [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
            ↦ castᵛ (sym (split→∈-split-l
                            (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                    (V-rename r W) ]c)

ren-sub-unbox {Γ} {Γ'} {B} {A} {ρ} r Θ w V M W ih =
  ≐ᶜ-trans
    (C-rename-cong ρ₀
      (≐ᶜ-trans (castᶜ-≐ (castOf {Γ} {B} Θ) (sub-unbox w V M xL WL relL))
                (≡→≐ᶜ (cast-unbox (castOf {Γ} {B} Θ)))))
    (≐ᶜ-trans
      (unbox-≐ cell
        (≐ᶜ-trans
          (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ∷ A} r))
                      (castᶜ-irr (cong (_∷ A) (castOf {Γ} {B} Θ))
                                 (castOf {Γ} {B} (Θ ∷ A)) _)))
          (≐ᶜ-trans ih
                    (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ∷ A))
                                     (cong (_∷ A) (castOf {Γ'} {B} Θ)) _)))))
      (≐ᶜ-sym
        (≐ᶜ-trans (castᶜ-≐ (castOf {Γ'} {B} Θ)
                    (sub-unbox (ρ' ∘ʳ w) V (C-rename (cong-∷-ren ρ') M)
                               xR WR relR))
                  (≡→≐ᶜ (cast-unbox (castOf {Γ'} {B} Θ))))))
  where
    ρ₀ = cong-ren {Γ'' = Θ} r
    ρ' = cong-ren {Γ'' = Θ} (cong-∷-ren r)

    xL = split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
    xR = split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
    WL = castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W
    WR = castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ' ∷ B} {Θ}))) (V-rename r W)

    cL = proj₂ (unbox-tgt w V)

    relL = ≾ᵣ-trans (proj₂ (proj₂ (⟨ cL ⟩[ xL ↦ WL ]rvar)))
                    (proj₂ (proj₂ (unbox⇒var w V)))

    relR = ≾ᵣ-trans
             (proj₂ (proj₂ (⟨ proj₂ (unbox-tgt (ρ' ∘ʳ w) V) ⟩[ xR ↦ WR ]rvar)))
             (proj₂ (proj₂ (unbox⇒var (ρ' ∘ʳ w) V)))

    hd : ∀ {Γ₀ : Ctx} → (Γ₀ ∷ [ ρ ] A) ⊢V⦂ [ ρ ] A
    hd = var (λ _ → ≾ᵣ-refl) Hd

    vL = proj₂ (rvar-tgt cL xL WL)
    vR = proj₂ (rvar-tgt (proj₂ (unbox-tgt (ρ' ∘ʳ w) V)) xR WR)

    wL = castʳ (castOf {Γ} {B} Θ) (unbox-var-ren vL relL)
    wR = castʳ (castOf {Γ'} {B} Θ) (unbox-var-ren vR relR)

    cell : unbox-tgt (ρ₀ ∘ʳ wL) hd ≡ unbox-tgt wR hd
    cell =
      trans (unbox-tgt-∘ ρ₀ wL hd)
        (trans (cong (var-tgt′ ρ₀)
                 (trans (unbox-tgt-castʳ (castOf {Γ} {B} Θ)
                                          (unbox-var-ren vL relL) hd)
                        (cong (Tgt-cast (castOf {Γ} {B} Θ))
                              (unbox-var-tgt vL relL))))
          (trans (unbox-cell-ren r Θ cL W)
            (trans (cong (λ t → Tgt-cast (castOf {Γ'} {B} Θ)
                                  (rvar-tgt (proj₂ t) xR WR))
                         (sym (unbox-tgt-∘ ρ' w V)))
              (sym (trans (unbox-tgt-castʳ (castOf {Γ'} {B} Θ)
                                            (unbox-var-ren vR relR) hd)
                     (cong (Tgt-cast (castOf {Γ'} {B} Θ))
                           (unbox-var-tgt vR relR)))))))

------------------------------------------------------------------------
-- RESTRICTING A SUFFIX-EXTENDED RENAMING
--
-- Restricting a binder extension: at an eternal binder the restriction
-- keeps it, at a non-eternal one it drops it — in both cases conjugated
-- by `eq-ren`s at the (only propositional) context equalities.
------------------------------------------------------------------------

restrict-∷-et-≐ : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (et : Eternal B)
                → (e₁ : (Γ ∷ B) ᴱ ≡ Γ ᴱ ∷ B)
                → (e₂ : (Γ' ∷ B) ᴱ ≡ Γ' ᴱ ∷ B)
                → restrict-ren {Ξ = []} (cong-∷-ren {A = B} r)
                ≐ʳ (eq-ren (sym e₂)
                    ∘ʳ cong-∷-ren {A = B} (restrict-ren r) ∘ʳ eq-ren e₁)

restrict-∷-et-≐ r et e₁ e₂
  rewrite eternal?-yes et
        | uip {p = e₁} {q = refl} | uip {p = e₂} {q = refl} =
  ≐ʳ-sym (≐ʳ-trans (∘ʳ-identityˡ-≐ _) (∘ʳ-identityʳ-≐ _))

restrict-∷-ne-≐ : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (¬et : ¬ Eternal B)
                → (e₁ : (Γ ∷ B) ᴱ ≡ Γ ᴱ)
                → (e₂ : (Γ' ∷ B) ᴱ ≡ Γ' ᴱ)
                → restrict-ren {Ξ = []} (cong-∷-ren {A = B} r)
                ≐ʳ (eq-ren (sym e₂) ∘ʳ restrict-ren r ∘ʳ eq-ren e₁)

restrict-∷-ne-≐ r ¬et e₁ e₂
  rewrite eternal?-no ¬et
        | uip {p = e₁} {q = refl} | uip {p = e₂} {q = refl} =
  ≐ʳ-sym (≐ʳ-trans (∘ʳ-identityˡ-≐ _) (∘ʳ-identityʳ-≐ _))

------------------------------------------------------------------------
-- SPLITTING UNIQUENESS ACROSS TRANSPORTED HALVES
--
-- `split→∈-unique` requires the two splittings' halves to agree on the
-- nose; here they agree only propositionally, so the halves' equations
-- are matched first and the grade transport rides along.
------------------------------------------------------------------------

split→∈-unique₂ : ∀ {Γ Γ' Γ₁ Γ₁' Γ₂ Γ₂' A}
                → (eΓ₁ : Γ₁ ≡ Γ₁') → (eΓ₂ : Γ₂ ≡ Γ₂') → (e : Γ ≡ Γ')
                → (s : Γ₁ ∷ A , Γ₂ split Γ) → (s' : Γ₁' ∷ A , Γ₂' split Γ')
                → subst (λ Γ₀ → A ∈[ ctx-grade Γ₂' ] Γ₀) e
                    (subst (λ ρ₀ → A ∈[ ρ₀ ] Γ) (cong ctx-grade eΓ₂)
                           (split→∈ s))
                ≡ split→∈ s'
split→∈-unique₂ refl refl e s s' = split→∈-unique e s s'

-- The two halves' equations induced by a grade-and-context transport of
-- the substituted variable.

sl-eq : ∀ {Γ Γ' A ρ ρ'} → (eρ : ρ ≡ ρ') → (e : Γ ≡ Γ')
      → (x : A ∈[ ρ ] Γ) → (y : A ∈[ ρ' ] Γ')
      → subst (λ Γ₀ → A ∈[ ρ' ] Γ₀) e (subst (λ ρ₀ → A ∈[ ρ₀ ] Γ) eρ x) ≡ y
      → split-l x ≡ split-l y
sl-eq refl e x y ey = trans (split-l-cast e x) (cong split-l ey)

sr-eq : ∀ {Γ Γ' A ρ ρ'} → (eρ : ρ ≡ ρ') → (e : Γ ≡ Γ')
      → (x : A ∈[ ρ ] Γ) → (y : A ∈[ ρ' ] Γ')
      → subst (λ Γ₀ → A ∈[ ρ' ] Γ₀) e (subst (λ ρ₀ → A ∈[ ρ₀ ] Γ) eρ x) ≡ y
      → split-r x ≡ split-r y
sr-eq refl e x y ey = trans (split-r-cast e x) (cong split-r ey)

-- `sub-cast-C′` with the substituted variable's grade transported too.

sub-cast-C″ : ∀ {Γ Γ' A C ρ ρ'} → (eρ : ρ ≡ ρ') → (e : Γ ≡ Γ')
            → (M : Γ ⊢C⦂ C)
            → (x : A ∈[ ρ ] Γ) → (y : A ∈[ ρ' ] Γ')
            → (ey : subst (λ Γ₀ → A ∈[ ρ' ] Γ₀) e
                          (subst (λ ρ₀ → A ∈[ ρ₀ ] Γ) eρ x) ≡ y)
            → (U : split-l x ⊢V⦂ A) → (U' : split-l y ⊢V⦂ A)
            → (eU : subst (_⊢V⦂ A) (sl-eq eρ e x y ey) U ≡ U')
            → (subst (_⊢C⦂ C) e M) [ y ↦ U' ]c
            ≡ subst (_⊢C⦂ C) (cong₂ _++ᶜ_ (sl-eq eρ e x y ey)
                                          (sr-eq eρ e x y ey))
                (M [ x ↦ U ]c)
sub-cast-C″ refl e M x y ey U U' eU = sub-cast-C′ e M x y ey U U' eU

------------------------------------------------------------------------
-- VALUE-LEVEL TRANSPORT ALGEBRA
------------------------------------------------------------------------

castᵛ≡subst : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (V : Γ ⊢V⦂ A)
            → castᵛ e V ≡ subst (_⊢V⦂ A) e V
castᵛ≡subst refl V = refl

subst-fuseᵛ : ∀ {Γ₁ Γ₂ Γ₃ A} → (e : Γ₁ ≡ Γ₂) → (e' : Γ₂ ≡ Γ₃) → (V : Γ₁ ⊢V⦂ A)
            → subst (_⊢V⦂ A) e' (subst (_⊢V⦂ A) e V)
            ≡ subst (_⊢V⦂ A) (trans e e') V
subst-fuseᵛ refl refl V = refl

-- Two transport chains out of the same value agree by `uip`.

substᵛ-irr : ∀ {Γ Γ' A} → (e e' : Γ ≡ Γ') → (V : Γ ⊢V⦂ A)
           → subst (_⊢V⦂ A) e V ≡ subst (_⊢V⦂ A) e' V
substᵛ-irr e e' V = cong (λ z → subst (_⊢V⦂ _) z V) (uip {p = e} {q = e'})

-- The eternal restriction of a value respects a context transport.

restrict-castᵛ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (et : Eternal A) → (V : Γ ⊢V⦂ A)
               → eternal-val-restrict et (castᵛ e V)
               ≡ castᵛ (cong _ᴱ e) (eternal-val-restrict et V)
restrict-castᵛ refl et V = refl

------------------------------------------------------------------------
-- THE ETERNAL RESTRICTION IS NATURAL IN RENAMING
--
-- The var case goes through the reflection `∈-ᴱ⁻`: both sides' targets
-- reflect to `var-tgt r x`, so `∈-ᴱ⁻-inj` identifies them.
------------------------------------------------------------------------

eternal-val-restrict-ren : ∀ {Γ Γ' A} → (et : Eternal A)
                         → (r : Ren [] Γ Γ') → (W : Γ ⊢V⦂ A)
                         → eternal-val-restrict et (V-rename r W)
                         ≐ᵛ V-rename (restrict-ren r) (eternal-val-restrict et W)

eternal-val-restrict-ren {Γ} {Γ'} et r (var f x) =
  ≐ᵛ-trans
    (eternal-val-restrict-cong et (var-ren-≐ r x f fet))
    (≐ᵛ-sym (var-ren-tgt-≐ (restrict-ren r) (∈-ᴱ et x) fet
                           (sym tgt-eq) fet))
  where
    fet : ∀ {ρ₀} → ¬ Eternal _ → ρ₀ ≾ᵣ uᵣ
    fet ¬et = ⊥-elim (¬et et)

    tgt-eq : _≡_ {A = Tgt (Γ' ᴱ) _}
                 (uᵣ , ∈-ᴱ et (proj₂ (var-tgt r x)))
                 (var-tgt (restrict-ren r) (∈-ᴱ et x))
    tgt-eq =
      ∈-ᴱ⁻-inj Γ' _ _
        (trans (∈-ᴱ⁻-∈-ᴱ Γ' et (proj₂ (var-tgt r x)))
          (sym (trans (restrict-tgt⁻ r (∈-ᴱ et x))
                      (cong (var-tgt′ r) (∈-ᴱ⁻-∈-ᴱ Γ et x)))))

eternal-val-restrict-ren et r (const c) = ≐ᵛ-refl _
eternal-val-restrict-ren et r ⋆         = ≐ᵛ-refl _
eternal-val-restrict-ren (et₁ |×|ₑ et₂) r ⦉ V₁ , V₂ ⦊ =
  pair-≐ (eternal-val-restrict-ren et₁ r V₁)
         (eternal-val-restrict-ren et₂ r V₂)

------------------------------------------------------------------------
-- THE `ren-sub` STATEMENT, ABBREVIATED
------------------------------------------------------------------------

RenSubC : ∀ {Γ Γ' B C} → Ren [] Γ Γ' → (Θ : Ctx)
        → ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ C → Γ ⊢V⦂ B → Set
RenSubC {Γ} {Γ'} {B} r Θ M W =
  C-rename (cong-ren {Γ'' = Θ} r)
      (castᶜ (castOf {Γ} {B} Θ)
        (M [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
             ↦ castᵛ (sym (split→∈-split-l
                             (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]c))
  ≐ᶜ castᶜ (castOf {Γ'} {B} Θ)
       ((C-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) M)
          [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
            ↦ castᵛ (sym (split→∈-split-l
                            (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                    (V-rename r W) ]c)

-- A clause's two binders, as a suffix.

Dcl : VType → Op → E → Ctx
Dcl D op ε'' =
  [] ∷ type-of-gtype (param op)
     ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ D ‼ ε'')

-- The clause context, relocated to the recursion's canonical contexts.

ren-sub-eTot : ∀ {Γ B} → (Θ : Ctx) → Eternal B → (Δ : Ctx)
             → ((Γ ∷ B) ++ᶜ Θ) ᴱ ++ᶜ Δ ≡ (Γ ᴱ ∷ B) ++ᶜ (Θ ᴱ ++ᶜ Δ)
ren-sub-eTot {Γ} {B} Θ et Δ =
  trans (cong (_++ᶜ Δ)
              (trans (ᴱ-++ᶜ (Γ ∷ B) Θ)
                     (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-keep {Γ} {B} et))))
        (++ᶜ-assoc (Γ ᴱ ∷ B) (Θ ᴱ) Δ)

------------------------------------------------------------------------
-- CONJUGATED DECOMPOSITIONS
--
-- Every renaming this proof decomposes comes out as an `eq-ren`-conjugated
-- core; the two helpers below fuse nested conjugations and turn a
-- conjugation into transports around the core's action.
------------------------------------------------------------------------

infix 4 _≐ʳconj⟨_,_,_⟩

_≐ʳconj⟨_,_,_⟩ : ∀ {Γ₁ Γ₁' Γ₂ Γ₂'} → Ren [] Γ₁ Γ₂'
              → (Γ₁ ≡ Γ₁') → Ren [] Γ₁' Γ₂ → (Γ₂ ≡ Γ₂') → Set
R ≐ʳconj⟨ e , K , e' ⟩ = R ≐ʳ (eq-ren e' ∘ʳ K ∘ʳ eq-ren e)

-- Fusing a conjugation of a conjugation.

conj-fuse : ∀ {Γ₁ Γ₀ Γ₀' Γ₂ Γ₂' Γ₃}
          → {R : Ren [] Γ₀ Γ₂'} → (a : Γ₁ ≡ Γ₀) → (a' : Γ₂' ≡ Γ₃)
          → {K : Ren [] Γ₀' Γ₂} → (b : Γ₀ ≡ Γ₀') → (b' : Γ₂ ≡ Γ₂')
          → R ≐ʳconj⟨ b , K , b' ⟩
          → (eq-ren a' ∘ʳ R ∘ʳ eq-ren a) ≐ʳconj⟨ trans a b , K , trans b' a' ⟩
conj-fuse {R = R} a a' {K = K} b b' h =
  ≐ʳ-trans (∘ʳ-≐ ≐ʳ-refl (∘ʳ-≐ h ≐ʳ-refl))
    (≐ʳ-trans
      (∘ʳ-≐ ≐ʳ-refl (≐ʳ-trans (∘ʳ-assoc-≐ _ _ _)
                              (∘ʳ-≐ ≐ʳ-refl
                                (≐ʳ-trans (∘ʳ-assoc-≐ _ _ _)
                                          (∘ʳ-≐ ≐ʳ-refl (eq-ren-∘-≐ a b))))))
      (≐ʳ-trans (≐ʳ-sym (∘ʳ-assoc-≐ _ _ _))
                (∘ʳ-≐ (eq-ren-∘-≐ b' a') ≐ʳ-refl)))

-- Extending a conjugation by a suffix.

conj-cong-ren : ∀ {Γ₁ Γ₁' Γ₂ Γ₂'} → (Δ : Ctx)
              → {R : Ren [] Γ₁ Γ₂'} → (e : Γ₁ ≡ Γ₁')
              → {K : Ren [] Γ₁' Γ₂} → (e' : Γ₂ ≡ Γ₂')
              → R ≐ʳconj⟨ e , K , e' ⟩
              → cong-ren {Γ'' = Δ} R
                  ≐ʳconj⟨ cong (_++ᶜ Δ) e , cong-ren {Γ'' = Δ} K
                        , cong (_++ᶜ Δ) e' ⟩
conj-cong-ren Δ e e' h =
  ≐ʳ-trans (cong-ren-≐ Δ h)
    (≐ʳ-trans (cong-ren-∘-≐ Δ _ _)
      (∘ʳ-≐ (cong-ren-eq-ren-≐ Δ e')
            (≐ʳ-trans (cong-ren-∘-≐ Δ _ _)
                      (∘ʳ-≐ ≐ʳ-refl (cong-ren-eq-ren-≐ Δ e)))))

-- The action of a conjugated renaming is the core's action between the
-- two transports.

C-rename-conj : ∀ {Γ₁ Γ₁' Γ₂ Γ₂' C}
              → {R : Ren [] Γ₁ Γ₂'} → (e : Γ₁ ≡ Γ₁')
              → {K : Ren [] Γ₁' Γ₂} → (e' : Γ₂ ≡ Γ₂')
              → R ≐ʳconj⟨ e , K , e' ⟩
              → (X : Γ₁ ⊢C⦂ C)
              → C-rename R X
              ≐ᶜ subst (_⊢C⦂ C) e' (C-rename K (subst (_⊢C⦂ C) e X))
C-rename-conj e {K = K} e' h X =
  ≐ᶜ-trans (C-rename-≐ h X)
    (≐ᶜ-trans (C-rename-∘ (eq-ren e') (K ∘ʳ eq-ren e) X)
      (≐ᶜ-trans
        (C-rename-eq-≐ e' ≐ʳ-refl (C-rename (K ∘ʳ eq-ren e) X))
        (substᶜ-≐ e'
          (≐ᶜ-trans (C-rename-∘ K (eq-ren e) X)
                    (C-rename-cong K (C-rename-eq-≐ e ≐ʳ-refl X))))))

------------------------------------------------------------------------
-- THE TWO CLAUSE RENAMINGS, DECOMPOSED
--
-- Both sides of `ren-sub-handle`'s clause comparison rename by
-- `cong-ren {D}` of a restriction of a suffix-extended renaming; both
-- decompose onto the same core over the canonical restricted contexts.
------------------------------------------------------------------------

-- The left side: `restrict-ren (cong-ren {Θ} r)`, extended by the two
-- clause binders.

clause-ren-l-≐ : ∀ {Γ Γ'} → (r : Ren [] Γ Γ') → (Θ Δ : Ctx)
               → cong-ren {Γ'' = Δ}
                   (restrict-ren {Ξ = []} (cong-ren {Γ'' = Θ} r))
               ≐ʳconj⟨ trans (cong (_++ᶜ Δ) (ᴱ-++ᶜ Γ Θ))
                             (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) Δ)
                     , cong-ren {Γ'' = Θ ᴱ ++ᶜ Δ} (restrict-ren {Ξ = []} r)
                     , sym (trans (cong (_++ᶜ Δ) (ᴱ-++ᶜ Γ' Θ))
                                  (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) Δ)) ⟩
clause-ren-l-≐ {Γ} {Γ'} r Θ Δ =
  ≐ʳ-trans
    (conj-cong-ren Δ (ᴱ-++ᶜ Γ Θ) (sym (ᴱ-++ᶜ Γ' Θ))
       (restrict-cong-≐ r Θ (ᴱ-++ᶜ Γ Θ) (ᴱ-++ᶜ Γ' Θ)))
    (≐ʳ-trans
      (conj-fuse (cong (_++ᶜ Δ) (ᴱ-++ᶜ Γ Θ))
                 (cong (_++ᶜ Δ) (sym (ᴱ-++ᶜ Γ' Θ)))
                 (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) Δ)
                 (sym (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) Δ))
                 (cong-ren-assoc-≐ (Θ ᴱ) Δ (restrict-ren {Ξ = []} r)))
      (∘ʳ-≐ (eq-ren-≐ _ _) ≐ʳ-refl))

-- The right side: `restrict-ren (cong-ren {Θ} (cong-∷-ren r))` at an
-- eternal substituted type — the restriction keeps the binder.

clause-ren-r-et-≐ : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (et : Eternal B)
                  → (Θ Δ : Ctx)
                  → cong-ren {Γ'' = Δ}
                      (restrict-ren {Ξ = []}
                        (cong-ren {Γ'' = Θ} (cong-∷-ren {A = B} r)))
                  ≐ʳconj⟨ ren-sub-eTot {Γ} {B} Θ et Δ
                        , cong-ren {Γ'' = Θ ᴱ ++ᶜ Δ}
                            (cong-∷-ren {A = B} (restrict-ren {Ξ = []} r))
                        , sym (ren-sub-eTot {Γ'} {B} Θ et Δ) ⟩
clause-ren-r-et-≐ {Γ} {Γ'} {B} r et Θ Δ =
  ≐ʳ-trans
    (conj-cong-ren Δ _ _
      (≐ʳ-trans
        (restrict-cong-≐ (cong-∷-ren {A = B} r) Θ
           (ᴱ-++ᶜ (Γ ∷ B) Θ) (ᴱ-++ᶜ (Γ' ∷ B) Θ))
        (conj-fuse (ᴱ-++ᶜ (Γ ∷ B) Θ) (sym (ᴱ-++ᶜ (Γ' ∷ B) Θ))
           (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-keep {Γ} {B} et))
           (cong (_++ᶜ Θ ᴱ) (sym (ᴱ-∷-keep {Γ'} {B} et)))
           (conj-cong-ren (Θ ᴱ) (ᴱ-∷-keep {Γ} {B} et)
              (sym (ᴱ-∷-keep {Γ'} {B} et))
              (restrict-∷-et-≐ r et (ᴱ-∷-keep {Γ} {B} et)
                                    (ᴱ-∷-keep {Γ'} {B} et))))))
    (≐ʳ-trans
      (conj-fuse _ _
         (++ᶜ-assoc (Γ ᴱ ∷ B) (Θ ᴱ) Δ)
         (sym (++ᶜ-assoc (Γ' ᴱ ∷ B) (Θ ᴱ) Δ))
         (cong-ren-assoc-≐ (Θ ᴱ) Δ (cong-∷-ren {A = B} (restrict-ren {Ξ = []} r))))
      (∘ʳ-≐ (eq-ren-≐ _ _) ≐ʳ-refl))

-- The same at a non-eternal substituted type — the restriction drops it.

clause-ren-r-ne-≐ : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (¬et : ¬ Eternal B)
                  → (Θ Δ : Ctx)
                  → cong-ren {Γ'' = Δ}
                      (restrict-ren {Ξ = []}
                        (cong-ren {Γ'' = Θ} (cong-∷-ren {A = B} r)))
                  ≐ʳconj⟨ trans (cong (_++ᶜ Δ)
                                  (trans (ᴱ-++ᶜ (Γ ∷ B) Θ)
                                    (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-drop {Γ} {B} ¬et))))
                                (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) Δ)
                        , cong-ren {Γ'' = Θ ᴱ ++ᶜ Δ} (restrict-ren {Ξ = []} r)
                        , sym (trans (cong (_++ᶜ Δ)
                                       (trans (ᴱ-++ᶜ (Γ' ∷ B) Θ)
                                         (cong (_++ᶜ Θ ᴱ)
                                               (ᴱ-∷-drop {Γ'} {B} ¬et))))
                                     (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) Δ)) ⟩
clause-ren-r-ne-≐ {Γ} {Γ'} {B} r ¬et Θ Δ =
  ≐ʳ-trans
    (conj-cong-ren Δ _ _
      (≐ʳ-trans
        (restrict-cong-≐ (cong-∷-ren {A = B} r) Θ
           (ᴱ-++ᶜ (Γ ∷ B) Θ) (ᴱ-++ᶜ (Γ' ∷ B) Θ))
        (conj-fuse (ᴱ-++ᶜ (Γ ∷ B) Θ) (sym (ᴱ-++ᶜ (Γ' ∷ B) Θ))
           (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-drop {Γ} {B} ¬et))
           (cong (_++ᶜ Θ ᴱ) (sym (ᴱ-∷-drop {Γ'} {B} ¬et)))
           (conj-cong-ren (Θ ᴱ) (ᴱ-∷-drop {Γ} {B} ¬et)
              (sym (ᴱ-∷-drop {Γ'} {B} ¬et))
              (restrict-∷-ne-≐ r ¬et (ᴱ-∷-drop {Γ} {B} ¬et)
                                     (ᴱ-∷-drop {Γ'} {B} ¬et))))))
    (≐ʳ-trans
      (conj-fuse _ _
         (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) Δ)
         (sym (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) Δ))
         (cong-ren-assoc-≐ (Θ ᴱ) Δ (restrict-ren {Ξ = []} r)))
      (∘ʳ-≐ (eq-ren-≐ _ _) ≐ʳ-refl))

------------------------------------------------------------------------
-- `handle`, NON-ETERNAL
--
-- Both sides' clause components are the same core renaming
-- `cong-ren {Θ ᴱ ++ᶜ D₀} (restrict-ren r)` of the clause, inside
-- transport chains with the same endpoints, so after both are decomposed
-- (`clause-ren-l-≐`/`clause-ren-r-ne-≐`) `uip` closes the comparison.
------------------------------------------------------------------------

ren-sub-handle-ne : ∀ {Γ Γ' B A B' ε ε'} → (r : Ren [] Γ Γ') → (Θ : Ctx)
                  → (¬et : ¬ Eternal B)
                  → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
                  → (H : (op : Op) → (ε'' : E) →
                           ((Γ ∷ B) ++ᶜ Θ) ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                           ⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                  → (N : ((Γ ∷ B) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B' ‼ ε')
                  → (W : Γ ⊢V⦂ B)
                  → (hM : RenSubC r Θ M W)
                  → (hN : RenSubC r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
                  → RenSubC r Θ (handle M `with H `in N) W

ren-sub-handle-ne {Γ} {Γ'} {B} {A} {B'} {ε} r Θ ¬et M H N W hM hN
  rewrite eternal?-no ¬et =
  ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                       (cast-handle (castOf {Γ} {B} Θ))))
    (≐ᶜ-trans
      (handle-≐ hM (λ op ε'' → clause op ε'')
        (≐ᶜ-trans
          (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ⟨ mapᵉ ε ⟩ ∷ A} r))
                      (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                       (castOf {Γ} {B} Θ))
                                 (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _)))
          (≐ᶜ-trans hN
            (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A))
                             (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                   (castOf {Γ'} {B} Θ)) _)))))
      (≡→≐ᶜ (sym (cast-handle (castOf {Γ'} {B} Θ)))))
  where
    z₀  = split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
    z₀' = split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})

    clause : (op : Op) → (ε'' : E) → _
    clause op ε'' =
      ≐ᶜ-trans
        (C-rename-conj eLL eLL' (clause-ren-l-≐ r Θ D₀) _)
        (≐ᶜ-trans
          (≡→≐ᶜ (cong (λ z → subst (_⊢C⦂ CT) eLL' (C-rename K z)) inner-eq))
          (≐ᶜ-trans
            (≡→≐ᶜ uip²)
            (≐ᶜ-sym
              (≐ᶜ-trans (≡→≐ᶜ r1)
                (≐ᶜ-trans
                  (substᶜ-≐ TRout
                    (C-rename-conj eRR eRR'
                       (clause-ren-r-ne-≐ r ¬et Θ D₀) (H op ε'')))
                  (≡→≐ᶜ (subst-fuseᶜ eRR' TRout _)))))))
      where
        D₀ = [] ∷ type-of-gtype (param op)
                ∷ [ mapᵉ (op-grade op) ]
                    (type-of-gtype (arity op) ⇒ B' ‼ ε'')

        CT = B' ‼ (op-grade op ·ₑ ε'')

        K = cong-ren {Γ'' = Θ ᴱ ++ᶜ D₀} (restrict-ren {Ξ = []} r)

        cDL = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε''))
                   (castOf {Γ} {B} Θ)

        cDR = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε''))
                   (castOf {Γ'} {B} Θ)

        eLL = trans (cong (_++ᶜ D₀) (ᴱ-++ᶜ Γ Θ)) (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) D₀)

        eLL' = sym (trans (cong (_++ᶜ D₀) (ᴱ-++ᶜ Γ' Θ))
                          (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) D₀))

        eRR = trans (cong (_++ᶜ D₀)
                          (trans (ᴱ-++ᶜ (Γ ∷ B) Θ)
                                 (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-drop {Γ} {B} ¬et))))
                    (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) D₀)

        eRR' = sym (trans (cong (_++ᶜ D₀)
                                (trans (ᴱ-++ᶜ (Γ' ∷ B) Θ)
                                       (cong (_++ᶜ Θ ᴱ)
                                             (ᴱ-∷-drop {Γ'} {B} ¬et))))
                          (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) D₀))

        dropL = ᴱ-drop-split ¬et z₀
        dropR = ᴱ-drop-split ¬et z₀'

        TL = trans (trans (cong (_++ᶜ D₀) dropL) cDL) eLL

        TRout = trans (cong (_++ᶜ D₀) dropR) cDR

        inner-eq : subst (_⊢C⦂ CT) eLL
                     (castᶜ cDL
                       (subst (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                                        ∷ [ mapᵉ (op-grade op) ]
                                            (type-of-gtype (arity op)
                                              ⇒ B' ‼ ε'')
                                      ⊢C⦂ CT)
                              dropL (H op ε'')))
                 ≡ subst (_⊢C⦂ CT) TL (H op ε'')
        inner-eq =
          trans (cong (subst (_⊢C⦂ CT) eLL)
                   (trans (cong (castᶜ cDL)
                                (subst-++ᶜʳ D₀ dropL (H op ε'')))
                     (trans (castᶜ≡subst cDL _)
                            (subst-fuseᶜ (cong (_++ᶜ D₀) dropL) cDL
                                         (H op ε'')))))
                (subst-fuseᶜ (trans (cong (_++ᶜ D₀) dropL) cDL) eLL (H op ε''))

        r1 : castᶜ cDR
               (subst (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                                ∷ [ mapᵉ (op-grade op) ]
                                    (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                              ⊢C⦂ CT)
                      dropR
                      (C-rename (cong-∷-ren (cong-∷-ren
                                  (restrict-ren {Ξ = []}
                                    (cong-ren {Γ'' = Θ} (cong-∷-ren r)))))
                                (H op ε'')))
           ≡ subst (_⊢C⦂ CT) TRout
               (C-rename (cong-∷-ren (cong-∷-ren
                           (restrict-ren {Ξ = []}
                             (cong-ren {Γ'' = Θ} (cong-∷-ren r)))))
                         (H op ε''))
        r1 =
          trans (cong (castᶜ cDR) (subst-++ᶜʳ D₀ dropR _))
            (trans (castᶜ≡subst cDR _)
                   (subst-fuseᶜ (cong (_++ᶜ D₀) dropR) cDR _))

        uip² : subst (_⊢C⦂ CT) eLL'
                 (C-rename K (subst (_⊢C⦂ CT) TL (H op ε'')))
             ≡ subst (_⊢C⦂ CT) (trans eRR' TRout)
                 (C-rename K (subst (_⊢C⦂ CT) eRR (H op ε'')))
        uip² =
          trans (cong (λ p → subst (_⊢C⦂ CT) eLL'
                               (C-rename K (subst (_⊢C⦂ CT) p (H op ε''))))
                      (uip {p = TL} {q = eRR}))
                (cong (λ p → subst (_⊢C⦂ CT) p
                               (C-rename K (subst (_⊢C⦂ CT) eRR (H op ε''))))
                      (uip {p = eLL'} {q = trans eRR' TRout}))

------------------------------------------------------------------------
-- `handle`, ETERNAL
--
-- The clause substitutes the restricted value, so the comparison is the
-- recursion (`hH`, `ren-sub-C` at the canonical restricted contexts) with
-- the goal's two substitutions carried over by `sub-cast-C″` — the
-- splittings' halves agree with the canonical ones only propositionally,
-- which `split→∈-unique₂` absorbs — and the value mismatch bridged by
-- `eternal-val-restrict-ren`.
------------------------------------------------------------------------

ren-sub-handle-et : ∀ {Γ Γ' B A B' ε ε'} → (r : Ren [] Γ Γ') → (Θ : Ctx)
                  → (et : Eternal B)
                  → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
                  → (H : (op : Op) → (ε'' : E) →
                           ((Γ ∷ B) ++ᶜ Θ) ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                           ⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                  → (N : ((Γ ∷ B) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B' ‼ ε')
                  → (W : Γ ⊢V⦂ B)
                  → (hM : RenSubC r Θ M W)
                  → (hN : RenSubC r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
                  → (hH : (op : Op) → (ε'' : E)
                        → RenSubC {Γ ᴱ} {Γ' ᴱ} {B}
                            (restrict-ren {Ξ = []} r) (Θ ᴱ ++ᶜ Dcl B' op ε'')
                            (subst (_⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                                   (ren-sub-eTot {Γ} {B} Θ et (Dcl B' op ε''))
                                   (H op ε''))
                            (eternal-val-restrict et W))
                  → RenSubC r Θ (handle M `with H `in N) W

ren-sub-handle-et {Γ} {Γ'} {B} {A} {B'} {ε} r Θ et M H N W hM hN hH =
  ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                       (cast-handle (castOf {Γ} {B} Θ))))
    (≐ᶜ-trans
      (handle-≐ hM (λ op ε'' → clause op ε'')
        (≐ᶜ-trans
          (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ⟨ mapᵉ ε ⟩ ∷ A} r))
                      (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                       (castOf {Γ} {B} Θ))
                                 (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _)))
          (≐ᶜ-trans hN
            (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A))
                             (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                   (castOf {Γ'} {B} Θ)) _)))))
      (≡→≐ᶜ (sym (cast-handle (castOf {Γ'} {B} Θ)))))
  where
    z₀  = split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
    z₀' = split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})

    cWL = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B} {Θ}))
    cWR = sym (split→∈-split-l (split-≡-++ᶜ {Γ' ∷ B} {Θ}))

    clause : (op : Op) → (ε'' : E) → _
    clause op ε'' =
      ≐ᶜ-trans
        (≡→≐ᶜ (cong (λ d → C-rename
                             (cong-∷-ren (cong-∷-ren
                               (restrict-ren {Ξ = []}
                                 (cong-ren {Γ'' = Θ} r))))
                             (castᶜ cDL
                               (⟨ d ⟩[ z₀ ↦ castᵛ cWL W ]cl H op ε'')))
                    (eternal?-yes et)))
        (≐ᶜ-trans
          (C-rename-conj eLL eLL' (clause-ren-l-≐ r Θ D₀) _)
          (≐ᶜ-trans
            (≡→≐ᶜ (cong (λ z → subst (_⊢C⦂ CT) eLL' (C-rename KL z))
                        inner-eq-L))
            (≐ᶜ-trans
              (substᶜ-≐ eLL' (hH op ε''))
              (≐ᶜ-trans (≡→≐ᶜ out-eq)
                (≐ᶜ-sym
                  (≐ᶜ-trans
                    (≡→≐ᶜ (cong (λ d → castᶜ cDR
                                         (⟨ d ⟩[ z₀'
                                               ↦ castᵛ cWR (V-rename r W)
                                               ]cl
                                            (λ op₁ ε₁ →
                                               C-rename
                                                 (cong-∷-ren (cong-∷-ren
                                                   (restrict-ren {Ξ = []}
                                                     (cong-ren {Γ'' = Θ}
                                                       (cong-∷-ren r)))))
                                                 (H op₁ ε₁))
                                            op ε''))
                                (eternal?-yes et)))
                    gr-chain))))))
      where
        D₀ = Dcl B' op ε''

        CT = B' ‼ (op-grade op ·ₑ ε'')

        Θ₀ = Θ ᴱ ++ᶜ D₀

        KL = cong-ren {Γ'' = Θ₀} (restrict-ren {Ξ = []} r)
        KR = cong-ren {Γ'' = Θ₀} (cong-∷-ren {A = B} (restrict-ren {Ξ = []} r))

        eT   = ren-sub-eTot {Γ} {B} Θ et D₀
        eTΓ' = ren-sub-eTot {Γ'} {B} Θ et D₀

        Ĥ  = H op ε''
        H⁺ = subst (_⊢C⦂ CT) eT Ĥ

        sL = split-++ʳ (∈-ᴱ-split et z₀) D₀
        sR = split-++ʳ (∈-ᴱ-split et z₀') D₀

        xL = split→∈ sL
        xR = split→∈ sR

        y₁ = split→∈ (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})
        y₂ = split→∈ (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})

        VL = subst (_⊢V⦂ B) (sym (split→∈-split-l sL))
                   (eternal-val-restrict et (castᵛ cWL W))
        VR = subst (_⊢V⦂ B) (sym (split→∈-split-l sR))
                   (eternal-val-restrict et (castᵛ cWR (V-rename r W)))

        U₁ = castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})))
                   (eternal-val-restrict et W)
        U₂ = castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})))
                   (V-rename (restrict-ren {Ξ = []} r)
                             (eternal-val-restrict et W))

        cDL = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε''))
                   (castOf {Γ} {B} Θ)

        cDR = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε''))
                   (castOf {Γ'} {B} Θ)

        eLL = trans (cong (_++ᶜ D₀) (ᴱ-++ᶜ Γ Θ)) (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) D₀)

        eLL' = sym (trans (cong (_++ᶜ D₀) (ᴱ-++ᶜ Γ' Θ))
                          (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) D₀))

        bigEL = trans (cong₂ _++ᶜ_ (split→∈-split-l sL) (split→∈-split-r sL))
                  (trans (sym (++ᶜ-assoc ((split-l z₀) ᴱ) ((split-r z₀) ᴱ) D₀))
                         (cong (_++ᶜ D₀)
                               (sym (ᴱ-++ᶜ (split-l z₀) (split-r z₀)))))

        bigER = trans (cong₂ _++ᶜ_ (split→∈-split-l sR) (split→∈-split-r sR))
                  (trans (sym (++ᶜ-assoc ((split-l z₀') ᴱ) ((split-r z₀') ᴱ) D₀))
                         (cong (_++ᶜ D₀)
                               (sym (ᴱ-++ᶜ (split-l z₀') (split-r z₀')))))

        -- the left substitution, carried to the canonical contexts

        eΓ₁L = cong _ᴱ (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B} {Θ}))
        eΓ₂L = cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D₀)
                    (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B} {Θ}))

        eρL = cong ctx-grade eΓ₂L

        eyL : subst (λ Γ₀ → B ∈[ ctx-grade Θ₀ ] Γ₀) eT
                (subst (λ ρ₀ → B ∈[ ρ₀ ] (((Γ ∷ B) ++ᶜ Θ) ᴱ ++ᶜ D₀)) eρL xL)
            ≡ y₁
        eyL = split→∈-unique₂ eΓ₁L eΓ₂L eT sL (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})

        slL = sl-eq eρL eT xL y₁ eyL

        eUL : subst (_⊢V⦂ B) slL VL ≡ U₁
        eUL =
          trans (cong (subst (_⊢V⦂ B) slL)
                  (trans (cong (subst (_⊢V⦂ B) (sym (split→∈-split-l sL)))
                               (trans (restrict-castᵛ cWL et W)
                                      (castᵛ≡subst (cong _ᴱ cWL)
                                        (eternal-val-restrict et W))))
                         (subst-fuseᵛ (cong _ᴱ cWL)
                                      (sym (split→∈-split-l sL))
                                      (eternal-val-restrict et W))))
            (trans (subst-fuseᵛ (trans (cong _ᴱ cWL)
                                       (sym (split→∈-split-l sL)))
                                slL (eternal-val-restrict et W))
              (trans (substᵛ-irr (trans (trans (cong _ᴱ cWL)
                                               (sym (split→∈-split-l sL)))
                                        slL)
                        (sym (split→∈-split-l (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})))
                        (eternal-val-restrict et W))
                     (sym (castᵛ≡subst
                             (sym (split→∈-split-l (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})))
                             (eternal-val-restrict et W)))))

        subCL : H⁺ [ y₁ ↦ U₁ ]c
              ≡ subst (_⊢C⦂ CT)
                  (cong₂ _++ᶜ_ slL (sr-eq eρL eT xL y₁ eyL))
                  (Ĥ [ xL ↦ VL ]c)
        subCL = sub-cast-C″ eρL eT Ĥ xL y₁ eyL VL U₁ eUL

        inner-eq-L : subst (_⊢C⦂ CT) eLL
                       (castᶜ cDL (subst (_⊢C⦂ CT) bigEL (Ĥ [ xL ↦ VL ]c)))
                   ≡ castᶜ (castOf {Γ ᴱ} {B} Θ₀) (H⁺ [ y₁ ↦ U₁ ]c)
        inner-eq-L =
          trans (cong (subst (_⊢C⦂ CT) eLL)
                  (trans (castᶜ≡subst cDL _)
                         (subst-fuseᶜ bigEL cDL _)))
            (trans (subst-fuseᶜ (trans bigEL cDL) eLL _)
              (trans (cong (λ p → subst (_⊢C⦂ CT) p (Ĥ [ xL ↦ VL ]c))
                           (uip {p = trans (trans bigEL cDL) eLL}
                                {q = trans (cong₂ _++ᶜ_ slL
                                             (sr-eq eρL eT xL y₁ eyL))
                                           (castOf {Γ ᴱ} {B} Θ₀)}))
                (sym (trans (castᶜ≡subst (castOf {Γ ᴱ} {B} Θ₀) _)
                       (trans (cong (subst (_⊢C⦂ CT) (castOf {Γ ᴱ} {B} Θ₀))
                                    subCL)
                              (subst-fuseᶜ (cong₂ _++ᶜ_ slL
                                             (sr-eq eρL eT xL y₁ eyL))
                                           (castOf {Γ ᴱ} {B} Θ₀) _))))))

        -- the right substitution, likewise

        eΓ₁R = cong _ᴱ (sym (split→∈-split-l (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
        eΓ₂R = cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D₀)
                    (sym (split→∈-split-r (split-≡-++ᶜ {Γ' ∷ B} {Θ})))

        eρR = cong ctx-grade eΓ₂R

        eyR : subst (λ Γ₀ → B ∈[ ctx-grade ((split-r z₀') ᴱ ++ᶜ D₀) ] Γ₀)
                    (sym eTΓ')
                (subst (λ ρ₀ → B ∈[ ρ₀ ] ((Γ' ᴱ ∷ B) ++ᶜ Θ₀)) eρR y₂)
            ≡ xR
        eyR = split→∈-unique₂ eΓ₁R eΓ₂R (sym eTΓ')
                              (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀}) sR

        slR = sl-eq eρR (sym eTΓ') y₂ xR eyR

        VR″ = subst (_⊢V⦂ B) slR U₂

        X₂ = (C-rename KR H⁺) [ y₂ ↦ U₂ ]c

        subCR : (subst (_⊢C⦂ CT) (sym eTΓ') (C-rename KR H⁺)) [ xR ↦ VR″ ]c
              ≡ subst (_⊢C⦂ CT)
                  (cong₂ _++ᶜ_ slR (sr-eq eρR (sym eTΓ') y₂ xR eyR))
                  X₂
        subCR = sub-cast-C″ eρR (sym eTΓ') (C-rename KR H⁺) y₂ xR eyR
                            U₂ VR″ refl

        eVR : VR ≐ᵛ VR″
        eVR =
          ≐ᵛ-trans
            (≡→≐ᵛ (cong (subst (_⊢V⦂ B) (sym (split→∈-split-l sR)))
                        (restrict-castᵛ cWR et (V-rename r W))))
            (≐ᵛ-trans
              (substᵛ-≐ (sym (split→∈-split-l sR))
                 (castᵛ-≐ (cong _ᴱ cWR) (eternal-val-restrict-ren et r W)))
              (≡→≐ᵛ
                (trans (cong (subst (_⊢V⦂ B) (sym (split→∈-split-l sR)))
                             (castᵛ≡subst (cong _ᴱ cWR)
                               (V-rename (restrict-ren {Ξ = []} r)
                                         (eternal-val-restrict et W))))
                  (trans (subst-fuseᵛ (cong _ᴱ cWR)
                                      (sym (split→∈-split-l sR))
                                      (V-rename (restrict-ren {Ξ = []} r)
                                                (eternal-val-restrict et W)))
                    (trans (substᵛ-irr
                              (trans (cong _ᴱ cWR)
                                     (sym (split→∈-split-l sR)))
                              (trans (sym (split→∈-split-l
                                            (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})))
                                     slR)
                              (V-rename (restrict-ren {Ξ = []} r)
                                        (eternal-val-restrict et W)))
                      (sym (trans (cong (subst (_⊢V⦂ B) slR)
                                        (castᵛ≡subst
                                          (sym (split→∈-split-l
                                                 (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})))
                                          (V-rename (restrict-ren {Ξ = []} r)
                                                    (eternal-val-restrict et W))))
                                  (subst-fuseᵛ
                                    (sym (split→∈-split-l
                                           (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})))
                                    slR
                                    (V-rename (restrict-ren {Ξ = []} r)
                                              (eternal-val-restrict et W))))))))))

        TRfin = trans (trans (cong₂ _++ᶜ_ slR
                               (sr-eq eρR (sym eTΓ') y₂ xR eyR))
                             bigER)
                      cDR

        gr-chain : castᶜ cDR
                     (subst (_⊢C⦂ CT) bigER
                       ((C-rename (cong-∷-ren (cong-∷-ren
                                    (restrict-ren {Ξ = []}
                                      (cong-ren {Γ'' = Θ} (cong-∷-ren r)))))
                                  Ĥ)
                          [ xR ↦ VR ]c))
                 ≐ᶜ subst (_⊢C⦂ CT) TRfin X₂
        gr-chain =
          ≐ᶜ-trans
            (castᶜ-≐ cDR (substᶜ-≐ bigER
              (sub-≐ᶜ xR eVR
                 (C-rename-conj eT (sym eTΓ')
                    (clause-ren-r-et-≐ r et Θ D₀) Ĥ))))
            (≐ᶜ-trans
              (≡→≐ᶜ (cong (λ z → castᶜ cDR (subst (_⊢C⦂ CT) bigER z)) subCR))
              (≡→≐ᶜ (trans (cong (castᶜ cDR)
                              (subst-fuseᶜ (cong₂ _++ᶜ_ slR
                                             (sr-eq eρR (sym eTΓ') y₂ xR eyR))
                                           bigER X₂))
                       (trans (castᶜ≡subst cDR _)
                              (subst-fuseᶜ (trans (cong₂ _++ᶜ_ slR
                                                    (sr-eq eρR (sym eTΓ')
                                                           y₂ xR eyR))
                                                  bigER)
                                           cDR X₂)))))

        out-eq : subst (_⊢C⦂ CT) eLL'
                   (castᶜ (castOf {Γ' ᴱ} {B} Θ₀) X₂)
               ≡ subst (_⊢C⦂ CT) TRfin X₂
        out-eq =
          trans (cong (subst (_⊢C⦂ CT) eLL')
                      (castᶜ≡subst (castOf {Γ' ᴱ} {B} Θ₀) X₂))
            (trans (subst-fuseᶜ (castOf {Γ' ᴱ} {B} Θ₀) eLL' X₂)
                   (cong (λ p → subst (_⊢C⦂ CT) p X₂)
                         (uip {p = trans (castOf {Γ' ᴱ} {B} Θ₀) eLL'}
                              {q = TRfin})))

-- The dispatcher: the two halves' own statements each fit the unreduced
-- goal, so a `Dec` argument is matched instead of a `with`.

ren-sub-handle : ∀ {Γ Γ' B A B' ε ε'} → (r : Ren [] Γ Γ') → (Θ : Ctx)
               → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
               → (H : (op : Op) → (ε'' : E) →
                        ((Γ ∷ B) ++ᶜ Θ) ᴱ ∷ type-of-gtype (param op)
                          ∷ [ mapᵉ (op-grade op) ]
                              (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                        ⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
               → (N : ((Γ ∷ B) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B' ‼ ε')
               → (W : Γ ⊢V⦂ B)
               → (hM : RenSubC r Θ M W)
               → (hN : RenSubC r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
               → (hH : (et : Eternal B) → (op : Op) → (ε'' : E)
                     → RenSubC {Γ ᴱ} {Γ' ᴱ} {B}
                         (restrict-ren {Ξ = []} r) (Θ ᴱ ++ᶜ Dcl B' op ε'')
                         (subst (_⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                                (ren-sub-eTot {Γ} {B} Θ et (Dcl B' op ε''))
                                (H op ε''))
                         (eternal-val-restrict et W))
               → RenSubC r Θ (handle M `with H `in N) W

ren-sub-handle {B = B} r Θ M H N W hM hN hH = go (eternal? B)
  where
    go : Dec (Eternal B) → _
    go (yes et) = ren-sub-handle-et r Θ et M H N W hM hN (hH et)
    go (no ¬et) = ren-sub-handle-ne r Θ ¬et M H N W hM hN

-- RENAMING THE PREFIX COMMUTES WITH SUBSTITUTING AT THE VARIABLE PAST IT
--
-- Mutual induction on the term, at an arbitrary suffix, as `sub-wk`: each
-- binding former grows the suffix, `cong-ren {Θ ∷ A} r` *is*
-- `cong-∷-ren (cong-ren {Θ} r)` and the substituted variable at `Θ ∷ A` *is*
-- `Tl-∷` of the one at `Θ`, both definitionally. What is left per case is
-- pushing the two casts through the former.

mutual

  ren-sub-V : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → ∀ {A}
            → (U : ((Γ ∷ B) ++ᶜ Θ) ⊢V⦂ A) → (W : Γ ⊢V⦂ B)
            → V-rename (cong-ren {Γ'' = Θ} r)
                (castᵛ (castOf {Γ} {B} Θ)
                  (U [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                       ↦ castᵛ (sym (split→∈-split-l
                                       (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]v))
            ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                 ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) U)
                    [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                      ↦ castᵛ (sym (split→∈-split-l
                                      (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                              (V-rename r W) ]v)

  ren-sub-V {Γ} {Γ'} {B} r Θ (var f y) W = ren-sub-var r Θ y W f f

  ren-sub-V {Γ} {Γ'} {B} r Θ (const c) W =
    ≐ᵛ-trans (≡→≐ᵛ (cong (V-rename (cong-ren {Γ'' = Θ} r))
                         (cast-const (castOf {Γ} {B} Θ))))
             (≡→≐ᵛ (sym (cast-const (castOf {Γ'} {B} Θ))))

  ren-sub-V {Γ} {Γ'} {B} r Θ ⋆ W =
    ≐ᵛ-trans (≡→≐ᵛ (cong (V-rename (cong-ren {Γ'' = Θ} r))
                         (cast-⋆ (castOf {Γ} {B} Θ))))
             (≡→≐ᵛ (sym (cast-⋆ (castOf {Γ'} {B} Θ))))

  ren-sub-V {Γ} {Γ'} {B} r Θ ⦉ V₁ , V₂ ⦊ W =
    ≐ᵛ-trans (≡→≐ᵛ (cong (V-rename (cong-ren {Γ'' = Θ} r))
                         (cast-pair (castOf {Γ} {B} Θ))))
      (≐ᵛ-trans (pair-≐ (ren-sub-V r Θ V₁ W) (ren-sub-V r Θ V₂ W))
                (≡→≐ᵛ (sym (cast-pair (castOf {Γ'} {B} Θ)))))

  ren-sub-V {Γ} {Γ'} {B} r Θ {A = A ⇒ C} (lam M) W =
    ≐ᵛ-trans (≡→≐ᵛ (cong (V-rename (cong-ren {Γ'' = Θ} r))
                         (cast-lam (castOf {Γ} {B} Θ) _)))
      (≐ᵛ-trans
        (lam-≐ (≐ᶜ-trans
                 (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ∷ A} r))
                             (castᶜ-irr (cong (_∷ A) (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ∷ A)) _)))
                 (≐ᶜ-trans (ren-sub-C r (Θ ∷ A) M W)
                           (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ∷ A))
                                            (cong (_∷ A) (castOf {Γ'} {B} Θ)) _)))))
        (≡→≐ᵛ (sym (cast-lam (castOf {Γ'} {B} Θ) _))))

  ren-sub-C : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → ∀ {C}
            → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ C) → (W : Γ ⊢V⦂ B)
            → C-rename (cong-ren {Γ'' = Θ} r)
                (castᶜ (castOf {Γ} {B} Θ)
                  (M [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                       ↦ castᵛ (sym (split→∈-split-l
                                       (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]c))
            ≐ᶜ castᶜ (castOf {Γ'} {B} Θ)
                 ((C-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) M)
                    [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                      ↦ castᵛ (sym (split→∈-split-l
                                      (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                              (V-rename r W) ]c)

  ren-sub-C {Γ} {Γ'} {B} r Θ (return V) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-ret (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans (return-≐ (ren-sub-V r Θ V W))
                (≡→≐ᶜ (sym (cast-ret (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (_⨟_ {A = A} {ε = ε} M N) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-seq (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans
        (seq-≐ (ren-sub-C r Θ M W)
               (≐ᶜ-trans
                 (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ⟨ mapᵉ ε ⟩ ∷ A} r))
                             (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                              (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _)))
                 (≐ᶜ-trans (ren-sub-C r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
                           (≡→≐ᶜ (castᶜ-irr
                                    (castOf {Γ'} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A))
                                    (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                          (castOf {Γ'} {B} Θ)) _)))))
        (≡→≐ᶜ (sym (cast-seq (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (V₁ · V₂) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-app (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans (app-≐ (ren-sub-V r Θ V₁ W) (ren-sub-V r Θ V₂ W))
                (≡→≐ᶜ (sym (cast-app (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (match_`in_ {A = A} {B = B'} V N) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-match (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans
        (match-≐ (ren-sub-V r Θ V W)
                 (≐ᶜ-trans
                   (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ∷ A ∷ B'} r))
                               (castᶜ-irr (cong (λ Γ₀ → Γ₀ ∷ A ∷ B')
                                                (castOf {Γ} {B} Θ))
                                          (castOf {Γ} {B} (Θ ∷ A ∷ B')) _)))
                   (≐ᶜ-trans (ren-sub-C r (Θ ∷ A ∷ B') N W)
                             (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ∷ A ∷ B'))
                                              (cong (λ Γ₀ → Γ₀ ∷ A ∷ B')
                                                    (castOf {Γ'} {B} Θ)) _)))))
        (≡→≐ᶜ (sym (cast-match (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (absurd V) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-absurd (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans (absurd-≐ (ren-sub-V r Θ V W))
                (≡→≐ᶜ (sym (cast-absurd (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (perform op V M) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-perform (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans
        (perform-≐ (ren-sub-V r Θ V W)
                   (≐ᶜ-trans
                     (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ'} r))
                                 (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                                            ∷ type-of-gtype (arity op))
                                                  (castOf {Γ} {B} Θ))
                                            (castOf {Γ} {B} Θ') _)))
                     (≐ᶜ-trans (ren-sub-C r Θ' M W)
                               (≡→≐ᶜ (castᶜ-irr
                                        (castOf {Γ'} {B} Θ')
                                        (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                                        ∷ type-of-gtype (arity op))
                                              (castOf {Γ'} {B} Θ)) _)))))
        (≡→≐ᶜ (sym (cast-perform (castOf {Γ'} {B} Θ)))))
    where
      Θ' = Θ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)

  ren-sub-C {Γ} {Γ'} {B} r Θ (delay τ M) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-delay (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans
        (delay-≐ (≐ᶜ-trans
                   (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ⟨ of-natʳ τ ⟩} r))
                               (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) (castOf {Γ} {B} Θ))
                                          (castOf {Γ} {B} (Θ ⟨ of-natʳ τ ⟩)) _)))
                   (≐ᶜ-trans (ren-sub-C r (Θ ⟨ of-natʳ τ ⟩) M W)
                             (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ⟨ of-natʳ τ ⟩))
                                              (cong (_⟨ of-natʳ τ ⟩)
                                                    (castOf {Γ'} {B} Θ)) _)))))
        (≡→≐ᶜ (sym (cast-delay (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (box {A = A} {ρ = ρ} V M) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-box (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans
        (box-≐ (≐ᵛ-trans
                 (≡→≐ᵛ (cong (V-rename (cong-ren {Γ'' = Θ ⟨ ρ ⟩} r))
                             (castᵛ-irr (cong (_⟨ ρ ⟩) (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ⟨ ρ ⟩)) _)))
                 (≐ᵛ-trans (ren-sub-V r (Θ ⟨ ρ ⟩) V W)
                           (≡→≐ᵛ (castᵛ-irr (castOf {Γ'} {B} (Θ ⟨ ρ ⟩))
                                            (cong (_⟨ ρ ⟩) (castOf {Γ'} {B} Θ)) _))))
               (≐ᶜ-trans
                 (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ∷ [ ρ ] A} r))
                             (castᶜ-irr (cong (_∷ [ ρ ] A) (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ∷ [ ρ ] A)) _)))
                 (≐ᶜ-trans (ren-sub-C r (Θ ∷ [ ρ ] A) M W)
                           (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ∷ [ ρ ] A))
                                            (cong (_∷ [ ρ ] A)
                                                  (castOf {Γ'} {B} Θ)) _)))))
        (≡→≐ᶜ (sym (cast-box (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (coerce p M) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-coerce (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans (coerce-≐ (ren-sub-C r Θ M W))
                (≡→≐ᶜ (sym (cast-coerce (castOf {Γ'} {B} Θ)))))

  -- the clause hypothesis is the recursion at the canonical restricted
  -- contexts, threaded through `ren-sub-C-cast` so it runs on the bare clause
  ren-sub-C {Γ} {Γ'} {B} r Θ (handle_`with_`in {A = A} {B = B'} {ε = ε} M H N) W =
    ren-sub-handle r Θ M H N W
      (ren-sub-C r Θ M W)
      (ren-sub-C r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
      (λ et op ε'' →
         ren-sub-C-cast (restrict-ren {Ξ = []} r) (Θ ᴱ ++ᶜ Dcl B' op ε'')
                        (ren-sub-eTot {Γ} {B} Θ et (Dcl B' op ε''))
                        (H op ε'') (eternal-val-restrict et W))
  ren-sub-C r Θ (unbox {A = A} w V M)    W =
    ren-sub-unbox r Θ w V M W (ren-sub-C r (Θ ∷ A) M W)

  -- `ren-sub-C` with its context given by an equation, so the `handle` clause
  -- can recurse on the bare clause term (as `sub-wk-C-cast`).

  ren-sub-C-cast : ∀ {Γ Γ' B Γ₀} → (r : Ren [] Γ Γ') → (Θ : Ctx)
                 → ∀ {C} → (e : Γ₀ ≡ (Γ ∷ B) ++ᶜ Θ) → (M : Γ₀ ⊢C⦂ C)
                 → (W : Γ ⊢V⦂ B)
                 → RenSubC r Θ (subst (_⊢C⦂ C) e M) W

  ren-sub-C-cast r Θ refl M W = ren-sub-C r Θ M W

