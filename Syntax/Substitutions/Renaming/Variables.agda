------------------------------------------------------------------------
-- Renaming against substitution on variables and resource variables.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality
module Syntax.Substitutions.Renaming.Variables (Spec : LanguageSpec) where
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

wk-ren-nat : ∀ {Γ Γ' A} → (r : Ren [] Γ' Γ)
           → (wk-ren ∘ʳ cong-∷-ren {A = A} r) ≐ʳ (r ∘ʳ wk-ren)
wk-ren-nat r = mk≐ʳ (λ y → cong-ren-img-l r ([] ∷ _) y)

⟨⟩-ren-nat : ∀ {Γ Γ' ρ} → (r : Ren [] Γ' Γ)
           → (rn : ∀ {Γ₀ : Ctx} → Ren [] (Γ₀ ⟨ ρ ⟩) Γ₀)
           → (∀ {A σ} → (y : A ∈[ σ ] Γ') → var-img rn y ≡ Var-⟨⟩ ρ (σ , y))
           → (∀ {A σ} → (y : A ∈[ σ ] Γ)  → var-img rn y ≡ Var-⟨⟩ ρ (σ , y))
           → (rn ∘ʳ cong-⟨⟩-ren r) ≐ʳ (r ∘ʳ rn)
⟨⟩-ren-nat {ρ = ρ} r rn h' h = mk≐ʳ go
  where
    go : ∀ {A σ} → (y : A ∈[ σ ] _) → _
    go y =
      trans (cong (var-img′ (cong-⟨⟩-ren r)) (h y))
            (sym (h' (proj₂ (var-img r y))))

hit-⟨⟩-img : ∀ {Γ A σ ρ} → (p : ρ ≾ᵣ uᵣ) → (y : A ∈[ σ ] Γ)
           → var-img (⟨⟩-η⁻¹-ren {Δ = Γ} ∘ʳ ⟨⟩-≤-ren p) y ≡ Var-⟨⟩ ρ (σ , y)
hit-⟨⟩-img p y = cong (var-img′ (⟨⟩-≤-ren p)) (⟨⟩-η⁻¹-img y)

-- An eternal extension is natural: it builds only variables, constants, `⋆` and
-- pairs, so a renaming passes through it.

eternal-val-ext-ren : ∀ {Γ Γ' A ρ} → (et : Eternal A) → (r : Ren [] Γ' Γ)
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

ren-sub-hit : ∀ {Γ Γ' B} → (r : Ren [] Γ' Γ) → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
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
    (≐ᵛ-trans (≐ᵛ-sym (V-rename-∘ wk-ren (cong-∷-ren (cong-ren {Γ'' = Θ} r)) _))
      (≐ᵛ-trans (V-rename-≐ (wk-ren-nat (cong-ren {Γ'' = Θ} r)) _)
        (≐ᵛ-trans (V-rename-∘ (cong-ren {Γ'' = Θ} r) wk-ren _)
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
    (≐ᵛ-trans (≐ᵛ-sym (V-rename-∘ rn (cong-⟨⟩-ren ρ₀) _))
      (≐ᵛ-trans (V-rename-≐ (⟨⟩-ren-nat ρ₀ rn (λ y → hit-⟨⟩-img bd y)
                                              (λ y → hit-⟨⟩-img bd y)) _)
        (≐ᵛ-trans (V-rename-∘ ρ₀ rn _)
          (≐ᵛ-trans (V-rename-cong rn (ren-sub-hit r Θ W _ _))
            (≐ᵛ-trans (V-rename-≐ (∘ʳ-≐ ≐ʳ-refl (⟨⟩-≤-ren-≐ _ _)) _)
                      (≡→≐ᵛ (sym (cast-ren-⟨⟩-any (castOf {Γ'} {B} (Θ ⟨ ρ ⟩))
                                                  (castOf {Γ'} {B} Θ) rn' _))))))))
  where
    ρ₀ = cong-ren {Γ'' = Θ} r
    bd = ≾ᵣ-zero-productʳ (f ¬et)

    rn : ∀ {Γ₀ : Ctx} → Ren [] (Γ₀ ⟨ ρ ⟩) Γ₀
    rn = ⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren bd

    rn' : ∀ {Γ₀ : Ctx} → Ren [] (Γ₀ ⟨ ρ ⟩) Γ₀
    rn' = ⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f' ¬et))

-- The same, taking both variables as equations: what reaches the substitution
-- on either side is `∈-++ᶜˡ Θ Hd`, which is `split→∈` of the splitting only up
-- to `split→∈-∈-++ᶜˡ`.

ren-sub-hit′ : ∀ {Γ Γ' B σ σ'} → (r : Ren [] Γ' Γ) → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
             → (y  : B ∈[ σ  ] ((Γ  ∷ B) ++ᶜ Θ))
             → (y' : B ∈[ σ' ] ((Γ' ∷ B) ++ᶜ Θ))
             → (f  : ¬ Eternal B → σ  ≾ᵣ uᵣ)
             → (f' : ¬ Eternal B → σ' ≾ᵣ uᵣ)
             → _≡_ {A = Var ((Γ ∷ B) ++ᶜ Θ) B}
                 (σ , y) (ctx-grade Θ , split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}))
             → _≡_ {A = Var ((Γ' ∷ B) ++ᶜ Θ) B}
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

ren-sub-var-r : ∀ {Γ Γ' B} → (r : Ren [] Γ' Γ) → (Θ : Ctx) → ∀ {A ρ}
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
    (≐ᵛ-trans (var-ren-img-≐ (cong-ren {Γ'' = Θ} r) (∈-++ᶜʳ {Γ = Γ} z) f
                             (cong-ren-img-r r z) f)
      (≐ᵛ-sym
        (≐ᵛ-trans
          (castᵛ-≐ (castOf {Γ'} {B} Θ)
            (sub-≐ᵛ (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})) (≐ᵛ-refl _)
              (var-ren-img-≐ (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                             (∈-++ᶜʳ {Γ = Γ ∷ B} z) f'
                             (cong-ren-img-r (cong-∷-ren r) z) f')))
          (sub-var-r Θ z _ f' f))))

-- A PREFIX VARIABLE
--
-- The substitution fixes it on either side, and the renaming moves it to its
-- own image, pushed under the suffix.

ren-sub-var-l : ∀ {Γ Γ' B} → (r : Ren [] Γ' Γ) → (Θ : Ctx) → ∀ {A ρ}
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
    (≐ᵛ-trans (var-ren-img-≐ (cong-ren {Γ'' = Θ} r) (∈-++ᶜˡ {Γ = Γ} Θ z) f
                             (cong-ren-img-l r Θ z) fr)
      (≐ᵛ-sym
        (≐ᵛ-trans
          (castᵛ-≐ (castOf {Γ'} {B} Θ)
            (sub-≐ᵛ (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})) (≐ᵛ-refl _)
              (var-ren-img-≐ (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                             (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Tl-∷ z)) f'
                             (cong-ren-img-l (cong-∷-ren r) Θ (Tl-∷ z)) fr)))
          (sub-var-l Θ (proj₂ (var-img r z)) _ fr fr))))
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

ren-sub-var-hd : ∀ {Γ Γ' B} → (r : Ren [] Γ' Γ) → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
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
          (var-ren-img-≐ (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                         (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Hd {Γ = Γ})) f'
                         (cong-ren-img-l (cong-∷-ren r) Θ (Hd {Γ = Γ})) f'))))

-- THE VARIABLE CASE
--
-- Which of the three applies is what `∈-++ᶜ-split` decides, the prefix's own
-- head being the variable replaced.

ren-sub-var : ∀ {Γ Γ' B} → (r : Ren [] Γ' Γ) → (Θ : Ctx) → ∀ {A ρ}
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
-- `unbox-resource variable-wk`'s counterpart: the resource variable survives both orders. The third case
-- a weakening could not reach is here — the resource variable may *be* the variable
-- replaced, and then it is the one inside the substituted value, which is of
-- box type and so a variable itself.

rvar-hit-ren : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ' Γ) → (Θ : Ctx)
             → (W : Γ ⊢V⦂ [ ρ ] A)
             → var-img′ (cong-ren {Γ'' = Θ} r)
                 (Var-cast (castOf {Γ} {[ ρ ] A} Θ)
                   (rvar-img (split→∈ (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))
                             (split→∈ (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))
                             (castᵛ (sym (split→∈-split-l
                                            (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))) W)))
             ≡ Var-cast (castOf {Γ'} {[ ρ ] A} Θ)
                 (rvar-img (split→∈ (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ}))
                           (split→∈ (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ}))
                           (castᵛ (sym (split→∈-split-l
                                          (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ})))
                                  (V-rename r W)))

rvar-hit-ren r [] (var f y) = refl

rvar-hit-ren {Γ} {Γ'} {A} {ρ} r (Θ ∷ C) W =
  trans (cong (var-img′ (cong-∷-ren (cong-ren {Γ'' = Θ} r)))
              (trans (Var-cast-irr (castOf {Γ} {[ ρ ] A} (Θ ∷ C))
                                   (cong (_∷ C) (castOf {Γ} {[ ρ ] A} Θ)) _)
                     (Var-cast-∷ (castOf {Γ} {[ ρ ] A} Θ) _)))
    (trans (cong Var-∷ (rvar-hit-ren r Θ W))
      (trans (sym (Var-cast-∷ (castOf {Γ'} {[ ρ ] A} Θ) _))
             (Var-cast-irr (cong (_∷ C) (castOf {Γ'} {[ ρ ] A} Θ))
                           (castOf {Γ'} {[ ρ ] A} (Θ ∷ C)) _)))

rvar-hit-ren {Γ} {Γ'} {A} {ρ} r (Θ ⟨ ρ' ⟩) W =
  trans (cong (var-img′ (cong-⟨⟩-ren (cong-ren {Γ'' = Θ} r)))
              (trans (Var-cast-irr (castOf {Γ} {[ ρ ] A} (Θ ⟨ ρ' ⟩))
                                   (cong (_⟨ ρ' ⟩) (castOf {Γ} {[ ρ ] A} Θ)) _)
                     (Var-cast-⟨⟩ ρ' (castOf {Γ} {[ ρ ] A} Θ) _)))
    (trans (cong (Var-⟨⟩ ρ') (rvar-hit-ren r Θ W))
      (trans (sym (Var-cast-⟨⟩ ρ' (castOf {Γ'} {[ ρ ] A} Θ) _))
             (Var-cast-irr (cong (_⟨ ρ' ⟩) (castOf {Γ'} {[ ρ ] A} Θ))
                           (castOf {Γ'} {[ ρ ] A} (Θ ⟨ ρ' ⟩)) _)))

rvar-hit-ren′ : ∀ {Γ Γ' A ρ σ} → (r : Ren [] Γ' Γ) → (Θ : Ctx)
              → (W : Γ ⊢V⦂ [ ρ ] A)
              → (c  : [ ρ ] A ∈[ σ ] ((Γ ∷ [ ρ ] A) ++ᶜ Θ))
              → (t' : Var ((Γ' ∷ [ ρ ] A) ++ᶜ Θ) ([ ρ ] A))
              → _≡_ {A = Var ((Γ ∷ [ ρ ] A) ++ᶜ Θ) ([ ρ ] A)}
                  (σ , c)
                  (ctx-grade Θ , split→∈ (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))
              → t' ≡ (ctx-grade Θ , split→∈ (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ}))
              → var-img′ (cong-ren {Γ'' = Θ} r)
                  (Var-cast (castOf {Γ} {[ ρ ] A} Θ)
                    (rvar-img c (split→∈ (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))
                              (castᵛ (sym (split→∈-split-l
                                             (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))) W)))
              ≡ Var-cast (castOf {Γ'} {[ ρ ] A} Θ)
                  (rvar-img (proj₂ t')
                            (split→∈ (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ}))
                            (castᵛ (sym (split→∈-split-l
                                           (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ})))
                                   (V-rename r W)))
rvar-hit-ren′ r Θ W _ _ refl refl = rvar-hit-ren r Θ W

unbox-rvar-ren : ∀ {Γ Γ' B} → (r : Ren [] Γ' Γ) → (Θ : Ctx) → ∀ {A ρ σ}
               → (c : [ ρ ] A ∈[ σ ] ((Γ ∷ B) ++ᶜ Θ)) → (W : Γ ⊢V⦂ B)
               → var-img′ (cong-ren {Γ'' = Θ} r)
                   (Var-cast (castOf {Γ} {B} Θ)
                     (rvar-img c (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}))
                               (castᵛ (sym (split→∈-split-l
                                              (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W)))
               ≡ Var-cast (castOf {Γ'} {B} Θ)
                   (rvar-img (proj₂ (var-img (cong-ren {Γ'' = Θ} (cong-∷-ren r)) c))
                             (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ}))
                             (castᵛ (sym (split→∈-split-l
                                            (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                                    (V-rename r W)))

unbox-rvar-ren {Γ} {Γ'} {B} r Θ {A} {ρ} {σ} c W
  with ∈-++ᶜ-split (Γ ∷ B) Θ c in eqc

... | inj₂ c'
  rewrite ∈-++ᶜ-split-inj₂ (Γ ∷ B) Θ c c' eqc =
  trans (cong (var-img′ (cong-ren {Γ'' = Θ} r)) (sub-rvar-r Θ c' _))
    (trans (cong-ren-img-r r c')
           (sym (sub-rvar-r′ Θ c' _ (cong-ren-img-r (cong-∷-ren r) c') _)))

... | inj₁ (σ' , c') =
  subst (λ t → var-img′ (cong-ren {Γ'' = Θ} r)
                 (Var-cast (castOf {Γ} {B} Θ)
                   (rvar-img (proj₂ t) (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}))
                             (castᵛ (sym (split→∈-split-l
                                            (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W)))
             ≡ Var-cast (castOf {Γ'} {B} Θ)
                 (rvar-img (proj₂ (var-img (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                                           (proj₂ t)))
                           (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ}))
                           (castᵛ (sym (split→∈-split-l
                                          (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                                  (V-rename r W))))
        (sym (∈-++ᶜ-split-inj₁ (Γ ∷ B) Θ c c' eqc))
        (go c')
  where
    go : ∀ {σ₀} → (c₀ : [ ρ ] A ∈[ σ₀ ] (Γ ∷ B))
       → var-img′ (cong-ren {Γ'' = Θ} r)
           (Var-cast (castOf {Γ} {B} Θ)
             (rvar-img (∈-++ᶜˡ {Γ = Γ ∷ B} Θ c₀)
                       (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}))
                       (castᵛ (sym (split→∈-split-l
                                      (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W)))
       ≡ Var-cast (castOf {Γ'} {B} Θ)
           (rvar-img (proj₂ (var-img (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                                     (∈-++ᶜˡ {Γ = Γ ∷ B} Θ c₀)))
                     (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ}))
                     (castᵛ (sym (split→∈-split-l
                                    (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                            (V-rename r W)))

    go Hd =
      rvar-hit-ren′ r Θ W (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Hd {Γ = Γ})) _
        (sym (split→∈-∈-++ᶜˡ Γ B Θ))
        (trans (cong-ren-img-l (cong-∷-ren r) Θ (Hd {Γ = Γ}))
               (sym (split→∈-∈-++ᶜˡ Γ' B Θ)))

    go (Tl-∷ c₀) =
      trans (cong (var-img′ (cong-ren {Γ'' = Θ} r)) (sub-rvar-l Θ c₀ _))
        (trans (cong-ren-img-l r Θ c₀)
               (sym (sub-rvar-l′ Θ (proj₂ (var-img r c₀)) _
                       (cong-ren-img-l (cong-∷-ren r) Θ (Tl-∷ c₀)) _)))


-- The two formers that do not simply distribute: `unbox`, whose boxed value is
-- a variable the substitution relocates, and `handle`, whose clauses see the
-- substitution only through the eternal restriction. Both are stated so that
-- the induction below can hand them its hypothesis at the grown suffix.

-- `unbox`: both orders rebuild the unboxing from the resource variable the substitution
-- leaves (`sub-unbox`), and `unbox-rvar-ren` says the two resource variables agree. The body
-- is the induction hypothesis at the grown suffix, taken as an argument so that
-- this can stand outside the induction.

ren-sub-unbox
  : ∀ {Γ Γ' B A ρ C Δ} → (r : Ren [] Γ' Γ) → (Θ : Ctx)
  → (w : Ren [] ((Γ ∷ B) ++ᶜ Θ) (Δ ⟨ ρ ⟩))
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
      (unbox-≐ rvarEq
        (≐ᶜ-trans
          (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ∷ A} r))
                      (castᶜ-irr (cong (_∷ A) (castOf {Γ} {B} Θ))
                                 (castOf {Γ} {B} (Θ ∷ A)) _)))
          (≐ᶜ-trans ih
                    (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ∷ A))
                                     (cong (_∷ A) (castOf {Γ'} {B} Θ)) _)))))
      (≐ᶜ-sym
        (≐ᶜ-trans (castᶜ-≐ (castOf {Γ'} {B} Θ)
                    (sub-unbox (w ∘ʳ ρ') V (C-rename (cong-∷-ren ρ') M)
                               xR WR relR))
                  (≡→≐ᶜ (cast-unbox (castOf {Γ'} {B} Θ))))))
  where
    ρ₀ = cong-ren {Γ'' = Θ} r
    ρ' = cong-ren {Γ'' = Θ} (cong-∷-ren r)

    xL = split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
    xR = split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
    WL = castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W
    WR = castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ' ∷ B} {Θ}))) (V-rename r W)

    cL = proj₂ (unbox-img w V)

    relL = ≾ᵣ-trans (proj₂ (proj₂ (⟨ cL ⟩[ xL ↦ WL ]rvar)))
                    (proj₂ (proj₂ (unbox⇒var w V)))

    relR = ≾ᵣ-trans
             (proj₂ (proj₂ (⟨ proj₂ (unbox-img (w ∘ʳ ρ') V) ⟩[ xR ↦ WR ]rvar)))
             (proj₂ (proj₂ (unbox⇒var (w ∘ʳ ρ') V)))

    hd : ∀ {Γ₀ : Ctx} → (Γ₀ ∷ [ ρ ] A) ⊢V⦂ [ ρ ] A
    hd = var (λ _ → ≾ᵣ-refl) Hd

    vL = proj₂ (rvar-img cL xL WL)
    vR = proj₂ (rvar-img (proj₂ (unbox-img (w ∘ʳ ρ') V)) xR WR)

    wL = castʳ (castOf {Γ} {B} Θ) (unbox-var-ren vL relL)
    wR = castʳ (castOf {Γ'} {B} Θ) (unbox-var-ren vR relR)

    rvarEq : unbox-img (wL ∘ʳ ρ₀) hd ≡ unbox-img wR hd
    rvarEq =
      trans (unbox-img-∘ ρ₀ wL hd)
        (trans (cong (var-img′ ρ₀)
                 (trans (unbox-img-castʳ (castOf {Γ} {B} Θ)
                                          (unbox-var-ren vL relL) hd)
                        (cong (Var-cast (castOf {Γ} {B} Θ))
                              (unbox-var-img vL relL))))
          (trans (unbox-rvar-ren r Θ cL W)
            (trans (cong (λ t → Var-cast (castOf {Γ'} {B} Θ)
                                  (rvar-img (proj₂ t) xR WR))
                         (sym (unbox-img-∘ ρ' w V)))
              (sym (trans (unbox-img-castʳ (castOf {Γ'} {B} Θ)
                                            (unbox-var-ren vR relR) hd)
                     (cong (Var-cast (castOf {Γ'} {B} Θ))
                           (unbox-var-img vR relR)))))))

------------------------------------------------------------------------
