------------------------------------------------------------------------
-- Generating substitutions against renamings.                        --
--                                                                    --
-- Two statements: a renaming acts as the substitution it embeds to,  --
-- and substituting commutes with renaming whenever the two do so on  --
-- variables. The second is what a chain's congruences need: folding  --
-- a congruence along a chain weakens the image at every step, and    --
-- comparing that with weakening once is this interchange.            --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.Syntax.Substitution.Interchange (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming.Action S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Types           S

open import MonomorphicCalculus.Syntax.Renaming.Equivalence  S
open import MonomorphicCalculus.Syntax.Renaming.Coherence    S
open import MonomorphicCalculus.Syntax.Terms.Equivalence     S

open import MonomorphicCalculus.Syntax.Substitution.Base         S
open import MonomorphicCalculus.Syntax.Substitution.Lookup    S
open import MonomorphicCalculus.Syntax.Substitution.Action       S
open import MonomorphicCalculus.Syntax.Substitution.Equivalence  S

-- Where the lock-crossing renaming sends a variable: under the lock, at the
-- grade the lock contributes.

hit-⟨⟩-img : ∀ {Γ A σ ρ} → (p : ρ ≾ᵣ 𝟏ᵣ) → (y : A ∈[ σ ] Γ)
           → var-img (⟨⟩-η⁻¹-ren {Δ = Γ} ∘ʳ ⟨⟩-≤-ren p) y ≡ Var-⟨⟩ ρ (σ , y)
hit-⟨⟩-img p y = cong (var-img′ (⟨⟩-≤-ren p)) (⟨⟩-η⁻¹-img y)

-- An eternal extension is natural: it builds only variables, constants, `⋆`,
-- booleans, pairs and injections, so a renaming passes through it.

eternal-val-ext-ren : ∀ {Γ Γ' A ρ} → (et : Et A) → (r : Ren [] Γ Γ')
                    → (V : Γ' ⊢ᵛ⦂ A)
                    → V-rename (cong-⟨⟩-ren {ρ = ρ} r) (eternal-val-ext et V)
                    ≡ eternal-val-ext et (V-rename r V)
eternal-val-ext-ren et             r (var f x)   = var-≡
eternal-val-ext-ren et             r (const B c) = refl
eternal-val-ext-ren et             r ⋆           = refl
eternal-val-ext-ren et             r true        = refl
eternal-val-ext-ren et             r false       = refl
eternal-val-ext-ren et             r zero        = refl
eternal-val-ext-ren et             r (succ V)    =
  cong succ (eternal-val-ext-ren et r V)
eternal-val-ext-ren (et₁ |×|ₑ et₂) r ⦉ V₁ , V₂ ⦊  =
  cong₂ ⦉_,_⦊ (eternal-val-ext-ren et₁ r V₁) (eternal-val-ext-ren et₂ r V₂)
eternal-val-ext-ren (et₁ |+|ₑ _)   r (inl V)     =
  cong inl (eternal-val-ext-ren et₁ r V)
eternal-val-ext-ren (_ |+|ₑ et₂)   r (inr V)     =
  cong inr (eternal-val-ext-ren et₂ r V)
eternal-val-ext-ren et             r nil         = refl
eternal-val-ext-ren (listₑ et)     r (cons V W)  =
  cong₂ cons (eternal-val-ext-ren et r V) (eternal-val-ext-ren (listₑ et) r W)
eternal-val-ext-ren et             r (subV V p) =
  cong (λ W → subV W p) (eternal-val-ext-ren (<:ᵛ-eternalˡ p et) r V)

-- `cong-sub₀ ⌜ r ⌝` and `⌜ cong-ren r ⌝` are distinct substitutions acting
-- alike; the bridge is stated up to `_≐ˢ₀_` at the binders and closed by
-- `C-sub₀-≐ˢ₀`.

cong-∷-sub-⌜⌝ : ∀ {Γ Γ' A} → {s : Sub₀ [] Γ Γ'} → {r : Ren [] Γ Γ'}
              → s ≐ˢ₀ ⌜ r ⌝ → cong-∷-sub {A = A} s ≐ˢ₀ ⌜ cong-∷-ren r ⌝
cong-∷-sub-⌜⌝ h = mk≐ˢ₀ goᵛ goᵗ
  where
    goᵛ : ∀ {A' ρ'} → (x : A' ∈[ ρ' ] _) → (f : _) → _
    goᵛ Hd       f = var-≡
    goᵛ (Tl-∷ y) f = trans (cong (V-rename wk-ren) (atᵛ h y f)) var-≡

    goᵗ : ∀ {A' ρ ρ'} → (y : [ ρ ] A' ∈[ ρ' ] _) → _
    goᵗ Hd       = refl
    goᵗ (Tl-∷ y) = cong RVar-∷ (atᵗ h y)

cong-⟨⟩-sub-⌜⌝ : ∀ {Γ Γ' ρ} → {s : Sub₀ [] Γ Γ'} → {r : Ren [] Γ Γ'}
               → s ≐ˢ₀ ⌜ r ⌝ → cong-⟨⟩-sub {ρ = ρ} s ≐ˢ₀ ⌜ cong-⟨⟩-ren r ⌝
cong-⟨⟩-sub-⌜⌝ {ρ = ρ} {r = r} h = mk≐ˢ₀ goᵛ goᵗ
  where
    goᵛ : ∀ {A' ρ'} → (x : A' ∈[ ρ' ] _) → (f : _) → _
    goᵛ {A'} (Tl-⟨⟩ y) f with eternal? A'
    ... | yes et =
      trans (cong (eternal-val-ext et) (atᵛ h y _)) var-≡
    ... | no ¬et =
      trans (cong (V-rename (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et))))
                  (atᵛ h y _))
            (var-img-≡ (hit-⟨⟩-img (≾ᵣ-zero-productʳ (f ¬et))
                                   (proj₂ (var-img r y))) _ _)

    goᵗ : ∀ {A' ρ₀ ρ'} → (y : [ ρ₀ ] A' ∈[ ρ' ] _) → _
    goᵗ (Tl-⟨⟩ y) = cong (RVar-⟨⟩ ρ) (atᵗ h y)

cong-sub₀-⌜⌝ : ∀ {Γ Γ'} → (Γ₀ : Ctx) → (r : Ren [] Γ Γ')
             → cong-sub₀ {Γ'' = Γ₀} ⌜ r ⌝ ≐ˢ₀ ⌜ cong-ren {Γ'' = Γ₀} r ⌝
cong-sub₀-⌜⌝ []         r = ≐ˢ₀-refl
cong-sub₀-⌜⌝ (Γ₀ ∷ A)   r = cong-∷-sub-⌜⌝ (cong-sub₀-⌜⌝ Γ₀ r)
cong-sub₀-⌜⌝ (Γ₀ ⟨ ρ ⟩) r = cong-⟨⟩-sub-⌜⌝ (cong-sub₀-⌜⌝ Γ₀ r)

mutual

  V-sub₀-⌜⌝ : ∀ {Γ Γ' A} → (r : Ren [] Γ Γ') → (V : Γ' ⊢ᵛ⦂ A)
            → V-sub₀ ⌜ r ⌝ V ≡ V-rename r V

  V-sub₀-⌜⌝ r (var f x) = refl
  V-sub₀-⌜⌝ r (const B c) = refl
  V-sub₀-⌜⌝ r ⋆         = refl
  V-sub₀-⌜⌝ r true      = refl
  V-sub₀-⌜⌝ r false     = refl
  V-sub₀-⌜⌝ r zero      = refl
  V-sub₀-⌜⌝ r (succ V)  = cong succ (V-sub₀-⌜⌝ r V)
  V-sub₀-⌜⌝ r ⦉ V , W ⦊  = cong₂ ⦉_,_⦊ (V-sub₀-⌜⌝ r V) (V-sub₀-⌜⌝ r W)
  V-sub₀-⌜⌝ r (inl V)   = cong inl (V-sub₀-⌜⌝ r V)
  V-sub₀-⌜⌝ r (inr V)   = cong inr (V-sub₀-⌜⌝ r V)
  V-sub₀-⌜⌝ r nil       = refl
  V-sub₀-⌜⌝ r (cons V W) = cong₂ cons (V-sub₀-⌜⌝ r V) (V-sub₀-⌜⌝ r W)
  V-sub₀-⌜⌝ r (fun M)   =
    cong fun (trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ ([] ∷ _) r) M)
                    (C-sub₀-⌜⌝ (cong-ren r) M))
  V-sub₀-⌜⌝ r (handler N H) =
    handler-≡ (trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ (_ ⟨ _ ⟩ ∷ _) r) N)
                     (C-sub₀-⌜⌝ (cong-ren r) N))
      (λ op ε'' →
         trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ (_ ⟨ _ ⟩ ∷ _ ∷ _) r) (H op ε''))
               (C-sub₀-⌜⌝ (cong-ren r) (H op ε'')))
  V-sub₀-⌜⌝ r (subV V p) = subV-≡ (V-sub₀-⌜⌝ r V)

  C-sub₀-⌜⌝ : ∀ {Γ Γ' C} → (r : Ren [] Γ Γ') → (M : Γ' ⊢ᶜ⦂ C)
            → C-sub₀ ⌜ r ⌝ M ≡ C-rename r M

  C-sub₀-⌜⌝ r (return V) = cong return (V-sub₀-⌜⌝ r V)
  C-sub₀-⌜⌝ r (M ⨟ N) =
    cong₂ _⨟_ (C-sub₀-⌜⌝ r M)
      (trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ (_ ⟨ _ ⟩ ∷ _) r) N)
             (C-sub₀-⌜⌝ (cong-ren r) N))
  C-sub₀-⌜⌝ r (V · W) = cong₂ _·_ (V-sub₀-⌜⌝ r V) (V-sub₀-⌜⌝ r W)
  C-sub₀-⌜⌝ r (match V `with M) =
    cong₂ match_`with_ (V-sub₀-⌜⌝ r V)
      (trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ ([] ∷ _ ∷ _) r) M)
             (C-sub₀-⌜⌝ (cong-ren r) M))
  C-sub₀-⌜⌝ r (absurd V) = cong absurd (V-sub₀-⌜⌝ r V)
  C-sub₀-⌜⌝ r (cmp ⋈ V W et) =
    cong₂ (λ a b → cmp ⋈ a b et) (V-sub₀-⌜⌝ r V) (V-sub₀-⌜⌝ r W)
  C-sub₀-⌜⌝ r (if V `then M `else N) =
    cong₃ if_`then_`else_
      (V-sub₀-⌜⌝ r V) (C-sub₀-⌜⌝ r M) (C-sub₀-⌜⌝ r N)
  C-sub₀-⌜⌝ r (matchℕ V `zero M `succ N) =
    cong₃ matchℕ_`zero_`succ_ (V-sub₀-⌜⌝ r V) (C-sub₀-⌜⌝ r M)
      (trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ ([] ∷ _) r) N)
             (C-sub₀-⌜⌝ (cong-ren r) N))
  C-sub₀-⌜⌝ r (recℕ V M N p) =
    cong₃ (λ a b c → recℕ a b c p) (V-sub₀-⌜⌝ r V) (C-sub₀-⌜⌝ r M)
      (trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ (([] ⟨ _ ⟩ ∷ nat) ⟨ _ ⟩ ∷ _) r) N)
             (C-sub₀-⌜⌝ (cong-ren {Γ''  = (([] ⟨ _ ⟩ ∷ nat) ⟨ _ ⟩ ∷ _)} r) N))
  C-sub₀-⌜⌝ r (matchL V `nil M `cons N) =
    cong₃ matchL_`nil_`cons_ (V-sub₀-⌜⌝ r V) (C-sub₀-⌜⌝ r M)
      (trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ ([] ∷ _ ∷ _) r) N)
             (C-sub₀-⌜⌝ (cong-ren r) N))
  C-sub₀-⌜⌝ r (recL V M N p) =
    cong₃ (λ a b c → recL a b c p) (V-sub₀-⌜⌝ r V) (C-sub₀-⌜⌝ r M)
      (trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ (([] ⟨ _ ⟩ ∷ _ ∷ list _) ⟨ _ ⟩ ∷ _) r) N)
             (C-sub₀-⌜⌝ (cong-ren {Γ'' = (([] ⟨ _ ⟩ ∷ _ ∷ list _) ⟨ _ ⟩ ∷ _)} r) N))
  C-sub₀-⌜⌝ r (match+ V `inl M `inr N) =
    cong₃ match+_`inl_`inr_ (V-sub₀-⌜⌝ r V)
      (trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ ([] ∷ _) r) M)
             (C-sub₀-⌜⌝ (cong-ren r) M))
      (trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ ([] ∷ _) r) N)
             (C-sub₀-⌜⌝ (cong-ren r) N))
  C-sub₀-⌜⌝ r (perform op V M) =
    cong₂ (perform _) (V-sub₀-⌜⌝ r V)
      (trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ (_ ⟨ _ ⟩ ∷ _) r) M)
             (C-sub₀-⌜⌝ (cong-ren r) M))
  C-sub₀-⌜⌝ r (delay τ M) =
    cong (delay _) (trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ ([] ⟨ _ ⟩) r) M)
                          (C-sub₀-⌜⌝ (cong-ren r) M))
  C-sub₀-⌜⌝ r (handle M `with V) =
    cong₂ handle_`with_ (C-sub₀-⌜⌝ r M) (V-sub₀-⌜⌝ r V)
  C-sub₀-⌜⌝ r (unbox x rel q M) =
    unbox-≡ refl
      (trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ ([] ∷ _) r) M)
             (C-sub₀-⌜⌝ (cong-ren r) M))
  C-sub₀-⌜⌝ r (box _ V M) =
    cong₂ (box _) (trans (V-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ ([] ⟨ _ ⟩) r) V)
                     (V-sub₀-⌜⌝ (cong-ren r) V))
              (trans (C-sub₀-≐ˢ₀ (cong-sub₀-⌜⌝ ([] ∷ _) r) M)
                     (C-sub₀-⌜⌝ (cong-ren r) M))
  C-sub₀-⌜⌝ r (subC M p) = subC-≡ (C-sub₀-⌜⌝ r M)

-- Two ways round a square: substitute by `s` then rename by `r'`, or rename
-- by `r` then substitute by `s'`. The premise is that they agree on variables
-- and on resource variables; the theorem is that they then agree on terms.
--
-- The premise is closed under extending the substitution by a binder and by a
-- lock, each closure a variable-level calculation.

record Interchange {Δ Δ' Γ Γ'} (s' : Sub₀ [] Δ Δ') (r : Ren [] Δ' Γ')
                   (r' : Ren [] Δ Γ) (s : Sub₀ [] Γ Γ') : Set where
  constructor mk⋈
  field
    atᵛ : ∀ {A ρ} → (x : A ∈[ ρ ] Γ') → (f : ¬ Et A → ρ ≾ᵣ 𝟏ᵣ)
        → V-sub₀ s' (V-rename r (var f x)) ≡ V-rename r' (V-sub₀ s (var f x))
    atᵗ : ∀ {A ρ ρ'} → (y : [ ρ ] A ∈[ ρ' ] Γ')
        → tgt-img₀ s' (proj₂ (var-img r y)) ≡ rvar-img′ r' (tgt-img₀ s y)

open Interchange public

-- Under one more variable. Weakening the image and renaming under the new
-- binder commute (`wk-ren-nat-≐ʳ`).

⋈-∷ : ∀ {Δ Δ' Γ Γ' B} {s' : Sub₀ [] Δ Δ'} {r : Ren [] Δ' Γ'}
        {r' : Ren [] Δ Γ} {s : Sub₀ [] Γ Γ'}
    → Interchange s' r r' s
    → Interchange (cong-∷-sub {A = B} s') (cong-∷-ren r)
                  (cong-∷-ren r') (cong-∷-sub s)
⋈-∷ {r' = r'} {s = s} h = mk⋈ goᵛ goᵗ
  where
    goᵛ : ∀ {A' ρ'} → (x : A' ∈[ ρ' ] _) → (f : _) → _
    goᵛ Hd       f = var-≡
    goᵛ (Tl-∷ y) f =
      trans (cong (V-rename wk-ren) (atᵛ h y f))
        (trans (sym (V-rename-∘ r' wk-ren (V-sub₀ s (var f y))))
          (trans (V-rename-≡ (≐ʳ-sym (wk-ren-nat-≐ʳ r')) (V-sub₀ s (var f y)))
                 (V-rename-∘ wk-ren (cong-∷-ren r') (V-sub₀ s (var f y)))))

    goᵗ : ∀ {A' ρ ρ'} → (y : [ ρ ] A' ∈[ ρ' ] _) → _
    goᵗ Hd       = refl
    goᵗ (Tl-∷ y) = cong RVar-∷ (atᵗ h y)

-- Under one more lock. At an eternal type both sides extend the image
-- (`eternal-val-ext-ren`); otherwise both weaken along the lock-collapsing
-- renaming, whose image is the variable pushed under the lock.

⋈-⟨⟩ : ∀ {Δ Δ' Γ Γ' ρ} {s' : Sub₀ [] Δ Δ'} {r : Ren [] Δ' Γ'}
         {r' : Ren [] Δ Γ} {s : Sub₀ [] Γ Γ'}
     → Interchange s' r r' s
     → Interchange (cong-⟨⟩-sub {ρ = ρ} s') (cong-⟨⟩-ren r)
                   (cong-⟨⟩-ren r') (cong-⟨⟩-sub s)
⋈-⟨⟩ {ρ = ρ} {s' = s'} {r = r} {r' = r'} {s = s} h = mk⋈ goᵛ goᵗ
  where
    ⟨⟩-nat-≐ʳ : ∀ {Γ₀ Γ₀' ρ₀} → (r₀ : Ren [] Γ₀ Γ₀') → (p p' : ρ₀ ≾ᵣ 𝟏ᵣ)
              → (r₀ ∘ʳ (⟨⟩-η⁻¹-ren {Δ = Γ₀} ∘ʳ ⟨⟩-≤-ren {ρ' = ρ₀} p))
              ≐ʳ ((⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren {ρ' = ρ₀} p') ∘ʳ cong-⟨⟩-ren r₀)
    ⟨⟩-nat-≐ʳ r₀ p p' = mk≐ʳ go
      where
        go : ∀ {A₀ ρ₂} → (v : A₀ ∈[ ρ₂ ] _) → _
        go v = trans (hit-⟨⟩-img p (proj₂ (var-img r₀ v)))
                     (sym (cong (var-img′ (cong-⟨⟩-ren r₀)) (hit-⟨⟩-img p' v)))

    goᵛ : ∀ {A' ρ'} → (x : A' ∈[ ρ' ] _) → (f : _) → _
    goᵛ {A'} (Tl-⟨⟩ y) f with eternal? A'
    ... | yes et =
      trans (cong (eternal-val-ext et)
              (trans (sub-var₀-irr s' _ _ _) (atᵛ h y (et-bound et))))
            (sym (eternal-val-ext-ren et r' (V-sub₀ s (var (et-bound et) y))))
    ... | no ¬et =
      trans (cong (V-rename (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ _)))
              (trans (sub-var₀-irr s' _ _ _)
                     (atᵛ h y (λ ¬et' → ≾ᵣ-zero-productˡ (f ¬et')))))
        (trans (sym (V-rename-∘ r' (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ _))
                                (V-sub₀ s (var _ y))))
          (trans (V-rename-≡ (⟨⟩-nat-≐ʳ r' (≾ᵣ-zero-productʳ _) (≾ᵣ-zero-productʳ _))
                             (V-sub₀ s (var _ y)))
                 (V-rename-∘ (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ _))
                             (cong-⟨⟩-ren r') (V-sub₀ s (var _ y)))))

    goᵗ : ∀ {A' ρ₀ ρ'} → (y : [ ρ₀ ] A' ∈[ ρ' ] _) → _
    goᵗ (Tl-⟨⟩ y) = cong (RVar-⟨⟩ ρ) (atᵗ h y)

-- Under a whole suffix.

⋈-cong : ∀ {Δ Δ' Γ Γ'} {s' : Sub₀ [] Δ Δ'} {r : Ren [] Δ' Γ'}
           {r' : Ren [] Δ Γ} {s : Sub₀ [] Γ Γ'}
       → (Γ₀ : Ctx) → Interchange s' r r' s
       → Interchange (cong-sub₀ {Γ'' = Γ₀} s') (cong-ren {Γ'' = Γ₀} r)
                     (cong-ren {Γ'' = Γ₀} r') (cong-sub₀ {Γ'' = Γ₀} s)
⋈-cong []         h = h
⋈-cong (Γ₀ ∷ A)   h = ⋈-∷ (⋈-cong Γ₀ h)
⋈-cong (Γ₀ ⟨ ρ ⟩) h = ⋈-⟨⟩ (⋈-cong Γ₀ h)

mutual

  V-sub₀-ren : ∀ {Δ Δ' Γ Γ' A} {s' : Sub₀ [] Δ Δ'} {r : Ren [] Δ' Γ'}
                 {r' : Ren [] Δ Γ} {s : Sub₀ [] Γ Γ'}
             → Interchange s' r r' s → (V : Γ' ⊢ᵛ⦂ A)
             → V-sub₀ s' (V-rename r V) ≡ V-rename r' (V-sub₀ s V)

  V-sub₀-ren h (var f x) = atᵛ h x f
  V-sub₀-ren h (const B c) = refl
  V-sub₀-ren h ⋆         = refl
  V-sub₀-ren h true      = refl
  V-sub₀-ren h false     = refl
  V-sub₀-ren h zero      = refl
  V-sub₀-ren h (succ V)  = cong succ (V-sub₀-ren h V)
  V-sub₀-ren h ⦉ V , W ⦊  = cong₂ ⦉_,_⦊ (V-sub₀-ren h V) (V-sub₀-ren h W)
  V-sub₀-ren h (inl V)   = cong inl (V-sub₀-ren h V)
  V-sub₀-ren h (inr V)   = cong inr (V-sub₀-ren h V)
  V-sub₀-ren h nil       = refl
  V-sub₀-ren h (cons V W) = cong₂ cons (V-sub₀-ren h V) (V-sub₀-ren h W)
  V-sub₀-ren h (fun M)   = cong fun (C-sub₀-ren (⋈-cong ([] ∷ _) h) M)
  V-sub₀-ren h (handler N H) =
    handler-≡ (C-sub₀-ren (⋈-cong (_ ⟨ _ ⟩ ∷ _) h) N)
      (λ op ε'' → C-sub₀-ren (⋈-cong (_ ⟨ _ ⟩ ∷ _ ∷ _) h) (H op ε''))
  V-sub₀-ren h (subV V p) = subV-≡ (V-sub₀-ren h V)

  C-sub₀-ren : ∀ {Δ Δ' Γ Γ' C} {s' : Sub₀ [] Δ Δ'} {r : Ren [] Δ' Γ'}
                 {r' : Ren [] Δ Γ} {s : Sub₀ [] Γ Γ'}
             → Interchange s' r r' s → (M : Γ' ⊢ᶜ⦂ C)
             → C-sub₀ s' (C-rename r M) ≡ C-rename r' (C-sub₀ s M)

  C-sub₀-ren h (return V) = cong return (V-sub₀-ren h V)
  C-sub₀-ren h (M ⨟ N) =
    cong₂ _⨟_ (C-sub₀-ren h M) (C-sub₀-ren (⋈-cong (_ ⟨ _ ⟩ ∷ _) h) N)
  C-sub₀-ren h (V · W) = cong₂ _·_ (V-sub₀-ren h V) (V-sub₀-ren h W)
  C-sub₀-ren h (match V `with M) =
    cong₂ match_`with_ (V-sub₀-ren h V) (C-sub₀-ren (⋈-cong ([] ∷ _ ∷ _) h) M)
  C-sub₀-ren h (absurd V) = cong absurd (V-sub₀-ren h V)
  C-sub₀-ren h (cmp ⋈ V W et) =
    cong₂ (λ a b → cmp ⋈ a b et) (V-sub₀-ren h V) (V-sub₀-ren h W)
  C-sub₀-ren h (if V `then M `else N) =
    cong₃ if_`then_`else_
      (V-sub₀-ren h V) (C-sub₀-ren h M) (C-sub₀-ren h N)
  C-sub₀-ren h (matchℕ V `zero M `succ N) =
    cong₃ matchℕ_`zero_`succ_ (V-sub₀-ren h V) (C-sub₀-ren h M)
      (C-sub₀-ren (⋈-cong ([] ∷ _) h) N)
  C-sub₀-ren h (recℕ V M N p) =
    cong₃ (λ a b c → recℕ a b c p) (V-sub₀-ren h V) (C-sub₀-ren h M)
      (C-sub₀-ren (⋈-cong (([] ⟨ _ ⟩ ∷ nat) ⟨ _ ⟩ ∷ _) h) N)
  C-sub₀-ren h (matchL V `nil M `cons N) =
    cong₃ matchL_`nil_`cons_ (V-sub₀-ren h V) (C-sub₀-ren h M)
      (C-sub₀-ren (⋈-cong ([] ∷ _ ∷ _) h) N)
  C-sub₀-ren h (recL V M N p) =
    cong₃ (λ a b c → recL a b c p) (V-sub₀-ren h V) (C-sub₀-ren h M)
      (C-sub₀-ren (⋈-cong (([] ⟨ _ ⟩ ∷ _ ∷ list _) ⟨ _ ⟩ ∷ _) h) N)
  C-sub₀-ren h (match+ V `inl M `inr N) =
    cong₃ match+_`inl_`inr_ (V-sub₀-ren h V)
      (C-sub₀-ren (⋈-cong ([] ∷ _) h) M) (C-sub₀-ren (⋈-cong ([] ∷ _) h) N)
  C-sub₀-ren h (perform op V M) =
    cong₂ (perform _) (V-sub₀-ren h V) (C-sub₀-ren (⋈-cong (_ ⟨ _ ⟩ ∷ _) h) M)
  C-sub₀-ren h (delay τ M) =
    cong (delay _) (C-sub₀-ren (⋈-cong ([] ⟨ _ ⟩) h) M)
  C-sub₀-ren h (handle M `with V) =
    cong₂ handle_`with_ (C-sub₀-ren h M) (V-sub₀-ren h V)
  C-sub₀-ren h (unbox x rel q M) =
    unbox-≡ (atᵗ h x) (C-sub₀-ren (⋈-cong ([] ∷ _) h) M)
  C-sub₀-ren h (box _ V M) =
    cong₂ (box _) (V-sub₀-ren (⋈-cong ([] ⟨ _ ⟩) h) V)
              (C-sub₀-ren (⋈-cong ([] ∷ _) h) M)
  C-sub₀-ren h (subC M p) = subC-≡ (C-sub₀-ren h M)
