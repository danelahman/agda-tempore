------------------------------------------------------------------------
-- When two parallel substitutions act alike.                         --
--                                                                    --
-- Chains of different lengths can act the same way, so `_≐ˢ_` is an  --
-- observation, as `_≐ʳ_` is. Transferring it to terms is the one     --
-- induction over term formers the whole layer needs; the congruences --
-- it uses are chain inductions resting on the interchange.           --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Grades.Base
open import Language.Comparisons using (Cmp)
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.Syntax.Substitution.ChainEquivalence (S : LanguageSpec) where

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
open import MonomorphicCalculus.Syntax.Substitution.Interchange     S
open import MonomorphicCalculus.Syntax.Substitution.Chain        S

-- Where a chain sends a resource variable.

tgt-img : ∀ {Γ Γ' A ρ ρ'} → Sub [] Γ Γ' → [ ρ ] A ∈[ ρ' ] Γ' → RVar Γ
tgt-img σ y =
  let (ρ₀ , A₀ , ρ'' , z , w , g) = sub-tgt σ y in ρ₀ , A₀ , ρ'' , z

infix 4 _≐ˢ_

record _≐ˢ_ {Γ Γ'} (σ σ' : Sub [] Γ Γ') : Set where
  constructor mk≐ˢ
  field
    atᵛ : ∀ {A ρ} → (x : A ∈[ ρ ] Γ') → (f : ¬ Et A → ρ ≾ᵣ 𝟏ᵣ)
        → sub-var σ x f ≡ sub-var σ' x f
    atᵗ : ∀ {A ρ ρ'} → (y : [ ρ ] A ∈[ ρ' ] Γ') → tgt-img σ y ≡ tgt-img σ' y

open _≐ˢ_ public

≐ˢ-refl : ∀ {Γ Γ'} {σ : Sub [] Γ Γ'} → σ ≐ˢ σ
≐ˢ-refl = mk≐ˢ (λ x f → refl) (λ y → refl)

≐ˢ-sym : ∀ {Γ Γ'} {σ σ' : Sub [] Γ Γ'} → σ ≐ˢ σ' → σ' ≐ˢ σ
≐ˢ-sym h = mk≐ˢ (λ x f → sym (atᵛ h x f)) (λ y → sym (atᵗ h y))

≐ˢ-trans : ∀ {Γ Γ'} {σ σ' σ'' : Sub [] Γ Γ'} → σ ≐ˢ σ' → σ' ≐ˢ σ'' → σ ≐ˢ σ''
≐ˢ-trans h h' =
  mk≐ˢ (λ x f → trans (atᵛ h x f) (atᵛ h' x f))
       (λ y → trans (atᵗ h y) (atᵗ h' y))

-- A chain congruence applies its clause at every step, so comparing it with
-- applying it once is exactly an interchange, at the renaming or the eternal
-- operation the clause uses.

⋈-wk : ∀ {Γ Γ' B} → (s : Sub₀ [] Γ Γ')
     → Interchange (cong-∷-sub {A = B} s) wk-ren wk-ren s
⋈-wk s =
  mk⋈ (λ x f → cong (V-rename wk-ren) (sub-var₀-irr s x _ f)) (λ y → refl)

-- An eternal extension passes through a substitution: it builds only
-- variables, constants, `⋆`, booleans, pairs and injections.

V-sub₀-ext : ∀ {Γ Γ' A ρ} → (s : Sub₀ [] Γ Γ') → (et : Et A)
           → (V : Γ' ⊢V⦂ A)
           → V-sub₀ (cong-⟨⟩-sub {ρ = ρ} s) (eternal-val-ext et V)
           ≡ eternal-val-ext et (V-sub₀ s V)
V-sub₀-ext s et (var f x) rewrite eternal?-yes et =
  cong (eternal-val-ext et) (sub-var₀-irr s x _ f)
V-sub₀-ext s et (const c) = refl
V-sub₀-ext s et ⋆         = refl
V-sub₀-ext s et true      = refl
V-sub₀-ext s et false     = refl
V-sub₀-ext s et zero      = refl
V-sub₀-ext s et (succ V)  = cong succ (V-sub₀-ext s et V)
V-sub₀-ext s (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ =
  cong₂ ⦉_,_⦊ (V-sub₀-ext s et₁ V₁) (V-sub₀-ext s et₂ V₂)
V-sub₀-ext s (et₁ |+|ₑ _) (inl V) = cong inl (V-sub₀-ext s et₁ V)
V-sub₀-ext s (_ |+|ₑ et₂) (inr V) = cong inr (V-sub₀-ext s et₂ V)
V-sub₀-ext s et nil       = refl
V-sub₀-ext s (listₑ et) (cons V W) =
  cong₂ cons (V-sub₀-ext s et V) (V-sub₀-ext s (listₑ et) W)
V-sub₀-ext s et (subV V p) =
  cong (λ W → subV W p) (V-sub₀-ext s (<:ᵛ-eternalˡ p et) V)

-- Each is a chain induction: the head step's clause is moved past the tail's
-- accumulated image by the interchange, leaving the image the chain would have
-- produced without the congruence.

-- Under one more variable.

cong-∷-subˢ-Hd : ∀ {Γ Γ' B} → (σ : Sub [] Γ Γ')
               → (f : ¬ Et B → 𝟏ᵣ ≾ᵣ 𝟏ᵣ)
               → sub-var (cong-∷-subˢ {A = B} σ) Hd f ≡ var f Hd
cong-∷-subˢ-Hd []ˢ      f = refl
cong-∷-subˢ-Hd (s ◅ σ) f =
  trans (cong (V-sub₀ (cong-∷-sub s)) (cong-∷-subˢ-Hd σ f)) var-≡

cong-∷-subˢ-Tl : ∀ {Γ Γ' A B ρ} → (σ : Sub [] Γ Γ')
               → (y : A ∈[ ρ ] Γ') → (f : ¬ Et A → ρ ≾ᵣ 𝟏ᵣ)
               → sub-var (cong-∷-subˢ {A = B} σ) (Tl-∷ y) f
               ≡ V-rename wk-ren (sub-var σ y f)
cong-∷-subˢ-Tl []ˢ      y f = var-≡
cong-∷-subˢ-Tl (s ◅ σ) y f =
  trans (cong (V-sub₀ (cong-∷-sub s)) (cong-∷-subˢ-Tl σ y f))
        (V-sub₀-ren (⋈-wk s) (sub-var σ y f))

cong-∷-subˢ-tgt : ∀ {Γ Γ' A B ρ ρ'} → (σ : Sub [] Γ Γ')
                → (y : [ ρ ] A ∈[ ρ' ] Γ')
                → tgt-img (cong-∷-subˢ {A = B} σ) (Tl-∷ y) ≡ RVar-∷ (tgt-img σ y)
cong-∷-subˢ-tgt []ˢ      y = refl
cong-∷-subˢ-tgt (s ◅ σ) y =
  cong (λ t → tgt-img₀ (cong-∷-sub s) (rvar-pos t)) (cong-∷-subˢ-tgt σ y)

cong-∷-subˢ-tgt-Hd : ∀ {Γ Γ' A ρ} → (σ : Sub [] Γ Γ')
                   → tgt-img (cong-∷-subˢ {A = [ ρ ] A} σ) Hd ≡ (ρ , A , 𝟏ᵣ , Hd)
cong-∷-subˢ-tgt-Hd []ˢ      = refl
cong-∷-subˢ-tgt-Hd (s ◅ σ) =
  cong (λ t → tgt-img₀ (cong-∷-sub s) (rvar-pos t)) (cong-∷-subˢ-tgt-Hd σ)

cong-∷-subˢ-≐ˢ : ∀ {Γ Γ' B} {σ σ' : Sub [] Γ Γ'}
               → σ ≐ˢ σ' → cong-∷-subˢ {A = B} σ ≐ˢ cong-∷-subˢ σ'
cong-∷-subˢ-≐ˢ {σ = σ} {σ' = σ'} h = mk≐ˢ goᵛ goᵗ
  where
    goᵛ : ∀ {A' ρ'} → (x : A' ∈[ ρ' ] _) → (f : _) → _
    goᵛ Hd       f = trans (cong-∷-subˢ-Hd σ f) (sym (cong-∷-subˢ-Hd σ' f))
    goᵛ (Tl-∷ y) f =
      trans (cong-∷-subˢ-Tl σ y f)
        (trans (cong (V-rename wk-ren) (atᵛ h y f))
               (sym (cong-∷-subˢ-Tl σ' y f)))

    goᵗ : ∀ {A' ρ ρ'} → (y : [ ρ ] A' ∈[ ρ' ] _) → _
    goᵗ Hd       = trans (cong-∷-subˢ-tgt-Hd σ) (sym (cong-∷-subˢ-tgt-Hd σ'))
    goᵗ (Tl-∷ y) =
      trans (cong-∷-subˢ-tgt σ y)
        (trans (cong RVar-∷ (atᵗ h y)) (sym (cong-∷-subˢ-tgt σ' y)))

-- Under one more lock. An eternal value crosses a lock either way.

eternal-val-ext-≡ : ∀ {Γ A ρ} → (et : Et A) → (p : ρ ≾ᵣ 𝟏ᵣ) → (V : Γ ⊢V⦂ A)
                  → eternal-val-ext et V ≡ V-rename (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren p) V
eternal-val-ext-≡ et p (var f x) = var-img-≡ (sym (hit-⟨⟩-img p x)) _ _
eternal-val-ext-≡ et p (const c) = refl
eternal-val-ext-≡ et p ⋆         = refl
eternal-val-ext-≡ et p true      = refl
eternal-val-ext-≡ et p false     = refl
eternal-val-ext-≡ et p zero      = refl
eternal-val-ext-≡ et p (succ V)  = cong succ (eternal-val-ext-≡ et p V)
eternal-val-ext-≡ (et₁ |×|ₑ et₂) p ⦉ V₁ , V₂ ⦊ =
  cong₂ ⦉_,_⦊ (eternal-val-ext-≡ et₁ p V₁) (eternal-val-ext-≡ et₂ p V₂)
eternal-val-ext-≡ (et₁ |+|ₑ _) p (inl V) = cong inl (eternal-val-ext-≡ et₁ p V)
eternal-val-ext-≡ (_ |+|ₑ et₂) p (inr V) = cong inr (eternal-val-ext-≡ et₂ p V)
eternal-val-ext-≡ et p nil       = refl
eternal-val-ext-≡ (listₑ et) p (cons V W) =
  cong₂ cons (eternal-val-ext-≡ et p V) (eternal-val-ext-≡ (listₑ et) p W)
eternal-val-ext-≡ et p (subV V q) =
  cong (λ W → subV W q) (eternal-val-ext-≡ (<:ᵛ-eternalˡ q et) p V)

⋈-lock : ∀ {Γ Γ' ρ} → (s : Sub₀ [] Γ Γ') → (p p' : ρ ≾ᵣ 𝟏ᵣ)
       → Interchange (cong-⟨⟩-sub {ρ = ρ} s) (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren p)
                     (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren p') s
⋈-lock {Γ} {Γ'} {ρ} s p p' = mk⋈ goᵛ goᵗ
  where
    goᵛ : ∀ {A' ρ'} → (x : A' ∈[ ρ' ] Γ') → (f : ¬ Et A' → ρ' ≾ᵣ 𝟏ᵣ)
        → V-sub₀ (cong-⟨⟩-sub {ρ = ρ} s)
                 (V-rename (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren p) (var f x))
        ≡ V-rename (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren p') (V-sub₀ s (var f x))
    goᵛ {A'} x f with eternal? A'
    ... | yes et =
      trans (cong (eternal-val-ext et) (sub-var₀-irr s x _ f))
            (eternal-val-ext-≡ et p' (sub-var₀ s x f))
    ... | no ¬et =
      trans (cong (V-rename (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ _)))
                  (sub-var₀-irr s x _ f))
            (V-rename-≡ (∘ʳ-≐ʳ ≐ʳ-refl (⟨⟩-≤-ren-≐ʳ _ p')) (sub-var₀ s x f))

    goᵗ : ∀ {A' ρ₀ ρ'} → (y : [ ρ₀ ] A' ∈[ ρ' ] _) → _
    goᵗ y = rvar-≡ (sym (hit-⟨⟩-img p' (rvar-pos (tgt-img₀ s y))))

cong-⟨⟩-subˢ-et : ∀ {Γ Γ' A ρ ρ'} → (σ : Sub [] Γ Γ') → (et : Et A)
                → (y : A ∈[ ρ' ] Γ') → (f : ¬ Et A → ρ' ·ᵣ ρ ≾ᵣ 𝟏ᵣ)
                → sub-var (cong-⟨⟩-subˢ {ρ = ρ} σ) (Tl-⟨⟩ y) f
                ≡ eternal-val-ext et (sub-var σ y (et-bound et))
cong-⟨⟩-subˢ-et []ˢ      et y f = var-≡
cong-⟨⟩-subˢ-et (s ◅ σ) et y f =
  trans (cong (V-sub₀ (cong-⟨⟩-sub s)) (cong-⟨⟩-subˢ-et σ et y f))
        (V-sub₀-ext s et (sub-var σ y (et-bound et)))

cong-⟨⟩-subˢ-ne : ∀ {Γ Γ' A ρ ρ'} → (σ : Sub [] Γ Γ') → (¬et : ¬ Et A)
                → (y : A ∈[ ρ' ] Γ') → (f : ¬ Et A → ρ' ·ᵣ ρ ≾ᵣ 𝟏ᵣ)
                → sub-var (cong-⟨⟩-subˢ {ρ = ρ} σ) (Tl-⟨⟩ y) f
                ≡ V-rename (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et)))
                           (sub-var σ y (λ q → ≾ᵣ-zero-productˡ (f q)))
cong-⟨⟩-subˢ-ne []ˢ      ¬et y f =
  var-img-≡ (sym (hit-⟨⟩-img (≾ᵣ-zero-productʳ (f ¬et)) y)) _ _
cong-⟨⟩-subˢ-ne (s ◅ σ) ¬et y f =
  trans (cong (V-sub₀ (cong-⟨⟩-sub s)) (cong-⟨⟩-subˢ-ne σ ¬et y f))
        (V-sub₀-ren (⋈-lock s (≾ᵣ-zero-productʳ (f ¬et)) (≾ᵣ-zero-productʳ (f ¬et)))
                    (sub-var σ y (λ q → ≾ᵣ-zero-productˡ (f q))))

cong-⟨⟩-subˢ-tgt : ∀ {Γ Γ' A ρ ρ₀ ρ'} → (σ : Sub [] Γ Γ')
                 → (y : [ ρ₀ ] A ∈[ ρ' ] Γ')
                 → tgt-img (cong-⟨⟩-subˢ {ρ = ρ} σ) (Tl-⟨⟩ y)
                 ≡ RVar-⟨⟩ ρ (tgt-img σ y)
cong-⟨⟩-subˢ-tgt []ˢ      y = refl
cong-⟨⟩-subˢ-tgt (s ◅ σ) y =
  cong (λ t → tgt-img₀ (cong-⟨⟩-sub s) (rvar-pos t)) (cong-⟨⟩-subˢ-tgt σ y)

cong-⟨⟩-subˢ-≐ˢ : ∀ {Γ Γ' ρ} {σ σ' : Sub [] Γ Γ'}
                → σ ≐ˢ σ' → cong-⟨⟩-subˢ {ρ = ρ} σ ≐ˢ cong-⟨⟩-subˢ σ'
cong-⟨⟩-subˢ-≐ˢ {Γ} {Γ'} {ρ} {σ} {σ'} h = mk≐ˢ goᵛ goᵗ
  where
    goᵛ : ∀ {A' ρ'} → (x : A' ∈[ ρ' ] (Γ' ⟨ ρ ⟩))
        → (f : ¬ Et A' → ρ' ≾ᵣ 𝟏ᵣ)
        → sub-var (cong-⟨⟩-subˢ {ρ = ρ} σ) x f
        ≡ sub-var (cong-⟨⟩-subˢ σ') x f
    goᵛ {A'} (Tl-⟨⟩ y) f with eternal? A'
    ... | yes et =
      trans (cong-⟨⟩-subˢ-et σ et y f)
        (trans (cong (eternal-val-ext et) (atᵛ h y (et-bound et)))
               (sym (cong-⟨⟩-subˢ-et σ' et y f)))
    ... | no ¬et =
      trans (cong-⟨⟩-subˢ-ne σ ¬et y f)
        (trans (cong (V-rename (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et))))
                     (atᵛ h y (λ q → ≾ᵣ-zero-productˡ (f q))))
               (sym (cong-⟨⟩-subˢ-ne σ' ¬et y f)))

    goᵗ : ∀ {A' ρ₀ ρ'} → (y : [ ρ₀ ] A' ∈[ ρ' ] _) → _
    goᵗ (Tl-⟨⟩ y) =
      trans (cong-⟨⟩-subˢ-tgt σ y)
        (trans (cong (RVar-⟨⟩ ρ) (atᵗ h y)) (sym (cong-⟨⟩-subˢ-tgt σ' y)))

sub-var-irr : ∀ {Γ Γ' A ρ} → (σ : Sub [] Γ Γ') → (x : A ∈[ ρ ] Γ')
            → (f f' : ¬ Et A → ρ ≾ᵣ 𝟏ᵣ)
            → sub-var σ x f ≡ sub-var σ x f'
sub-var-irr σ x f f' = cong (λ g → V-sub σ (var g x)) (bound-irr f f')

-- Under a whole suffix.

cong-subˢ-≐ˢ : ∀ {Γ Γ'} {σ σ' : Sub [] Γ Γ'} → (Γ₀ : Ctx)
             → σ ≐ˢ σ' → cong-subˢ {Γ'' = Γ₀} σ ≐ˢ cong-subˢ σ'
cong-subˢ-≐ˢ []         h = h
cong-subˢ-≐ˢ (Γ₀ ∷ A)   h = cong-∷-subˢ-≐ˢ (cong-subˢ-≐ˢ Γ₀ h)
cong-subˢ-≐ˢ (Γ₀ ⟨ ρ ⟩) h = cong-⟨⟩-subˢ-≐ˢ (cong-subˢ-≐ˢ Γ₀ h)

-- The action folds the chain: reaching under a binder by the matching chain
-- congruence is a chain induction, one per former, the empty chain a `refl`
-- and a step the generator's own clause.

V-sub-const : ∀ {Γ Γ' B} → (σ : Sub [] Γ Γ') → (c : BaseConstants B)
            → V-sub σ (const c) ≡ const c
V-sub-const []ˢ      c = refl
V-sub-const (s ◅ σ) c = cong (V-sub₀ s) (V-sub-const σ c)

V-sub-⋆ : ∀ {Γ Γ'} → (σ : Sub [] Γ Γ') → V-sub σ ⋆ ≡ ⋆
V-sub-⋆ []ˢ      = refl
V-sub-⋆ (s ◅ σ) = cong (V-sub₀ s) (V-sub-⋆ σ)

V-sub-true : ∀ {Γ Γ'} → (σ : Sub [] Γ Γ') → V-sub σ true ≡ true
V-sub-true []ˢ      = refl
V-sub-true (s ◅ σ) = cong (V-sub₀ s) (V-sub-true σ)

V-sub-false : ∀ {Γ Γ'} → (σ : Sub [] Γ Γ') → V-sub σ false ≡ false
V-sub-false []ˢ      = refl
V-sub-false (s ◅ σ) = cong (V-sub₀ s) (V-sub-false σ)

V-sub-zero : ∀ {Γ Γ'} → (σ : Sub [] Γ Γ') → V-sub σ zero ≡ zero
V-sub-zero []ˢ      = refl
V-sub-zero (s ◅ σ) = cong (V-sub₀ s) (V-sub-zero σ)

V-sub-succ : ∀ {Γ Γ'} → (σ : Sub [] Γ Γ') → (V : Γ' ⊢V⦂ nat)
           → V-sub σ (succ V) ≡ succ (V-sub σ V)
V-sub-succ []ˢ      V = refl
V-sub-succ (s ◅ σ) V = cong (V-sub₀ s) (V-sub-succ σ V)

V-sub-⦉⦊ : ∀ {Γ Γ' A B} → (σ : Sub [] Γ Γ')
         → (V : Γ' ⊢V⦂ A) → (W : Γ' ⊢V⦂ B)
         → V-sub σ ⦉ V , W ⦊ ≡ ⦉ V-sub σ V , V-sub σ W ⦊
V-sub-⦉⦊ []ˢ      V W = refl
V-sub-⦉⦊ (s ◅ σ) V W = cong (V-sub₀ s) (V-sub-⦉⦊ σ V W)

V-sub-inl : ∀ {Γ Γ' A B} → (σ : Sub [] Γ Γ') → (V : Γ' ⊢V⦂ A)
          → V-sub σ (inl {B = B} V) ≡ inl (V-sub σ V)
V-sub-inl []ˢ      V = refl
V-sub-inl (s ◅ σ) V = cong (V-sub₀ s) (V-sub-inl σ V)

V-sub-inr : ∀ {Γ Γ' A B} → (σ : Sub [] Γ Γ') → (V : Γ' ⊢V⦂ B)
          → V-sub σ (inr {A = A} V) ≡ inr (V-sub σ V)
V-sub-inr []ˢ      V = refl
V-sub-inr (s ◅ σ) V = cong (V-sub₀ s) (V-sub-inr σ V)

V-sub-nil : ∀ {Γ Γ' A} → (σ : Sub [] Γ Γ') → V-sub σ (nil {A = A}) ≡ nil
V-sub-nil []ˢ      = refl
V-sub-nil (s ◅ σ) = cong (V-sub₀ s) (V-sub-nil σ)

V-sub-cons : ∀ {Γ Γ' A} → (σ : Sub [] Γ Γ') → (V : Γ' ⊢V⦂ A) → (W : Γ' ⊢V⦂ list A)
           → V-sub σ (cons V W) ≡ cons (V-sub σ V) (V-sub σ W)
V-sub-cons []ˢ      V W = refl
V-sub-cons (s ◅ σ) V W = cong (V-sub₀ s) (V-sub-cons σ V W)

V-sub-lam : ∀ {Γ Γ' A C} → (σ : Sub [] Γ Γ') → (M : Γ' ∷ A ⊢C⦂ C)
          → V-sub σ (lam M) ≡ lam (C-sub (cong-∷-subˢ σ) M)
V-sub-lam []ˢ      M = refl
V-sub-lam (s ◅ σ) M = cong (V-sub₀ s) (V-sub-lam σ M)

V-sub-subV : ∀ {Γ Γ' A A'} → (σ : Sub [] Γ Γ') → (p : A <:ᵛ A') → (V : Γ' ⊢V⦂ A)
           → V-sub σ (subV V p) ≡ subV (V-sub σ V) p
V-sub-subV []ˢ      p V = refl
V-sub-subV (s ◅ σ) p V = cong (V-sub₀ s) (V-sub-subV σ p V)

C-sub-return : ∀ {Γ Γ' A} → (σ : Sub [] Γ Γ') → (V : Γ' ⊢V⦂ A)
             → C-sub σ (return V) ≡ return (V-sub σ V)
C-sub-return []ˢ      V = refl
C-sub-return (s ◅ σ) V = cong (C-sub₀ s) (C-sub-return σ V)

C-sub-⨟ : ∀ {Γ Γ' A B ε ε'} → (σ : Sub [] Γ Γ')
        → (M : Γ' ⊢C⦂ A ! ε) → (N : Γ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε')
        → C-sub σ (M ⨟ N)
        ≡ (C-sub σ M ⨟ C-sub (cong-∷-subˢ (cong-⟨⟩-subˢ σ)) N)
C-sub-⨟ []ˢ      M N = refl
C-sub-⨟ (s ◅ σ) M N = cong (C-sub₀ s) (C-sub-⨟ σ M N)

C-sub-· : ∀ {Γ Γ' A C} → (σ : Sub [] Γ Γ')
        → (V : Γ' ⊢V⦂ A ⇒ C) → (W : Γ' ⊢V⦂ A)
        → C-sub σ (V · W) ≡ (V-sub σ V · V-sub σ W)
C-sub-· []ˢ      V W = refl
C-sub-· (s ◅ σ) V W = cong (C-sub₀ s) (C-sub-· σ V W)

C-sub-match : ∀ {Γ Γ' A B C} → (σ : Sub [] Γ Γ')
            → (V : Γ' ⊢V⦂ A |×| B) → (M : Γ' ∷ A ∷ B ⊢C⦂ C)
            → C-sub σ (match V `in M)
            ≡ match V-sub σ V `in C-sub (cong-∷-subˢ (cong-∷-subˢ σ)) M
C-sub-match []ˢ      V M = refl
C-sub-match (s ◅ σ) V M = cong (C-sub₀ s) (C-sub-match σ V M)

C-sub-absurd : ∀ {Γ Γ' C} → (σ : Sub [] Γ Γ') → (V : Γ' ⊢V⦂ empty)
             → C-sub σ (absurd {C = C} V) ≡ absurd (V-sub σ V)
C-sub-absurd []ˢ      V = refl
C-sub-absurd (s ◅ σ) V = cong (C-sub₀ s) (C-sub-absurd σ V)

C-sub-cmp : ∀ {Γ Γ' A} → (σ : Sub [] Γ Γ') → (⋈ : Cmp) → (V W : Γ' ⊢V⦂ A)
          → (et : Et A)
          → C-sub σ (cmp ⋈ V W et) ≡ cmp ⋈ (V-sub σ V) (V-sub σ W) et
C-sub-cmp []ˢ      ⋈ V W et = refl
C-sub-cmp (s ◅ σ) ⋈ V W et = cong (C-sub₀ s) (C-sub-cmp σ ⋈ V W et)

C-sub-if : ∀ {Γ Γ' C} → (σ : Sub [] Γ Γ')
         → (V : Γ' ⊢V⦂ bool) → (M N : Γ' ⊢C⦂ C)
         → C-sub σ (if V `then M `else N)
         ≡ if V-sub σ V `then C-sub σ M `else C-sub σ N
C-sub-if []ˢ      V M N = refl
C-sub-if (s ◅ σ) V M N = cong (C-sub₀ s) (C-sub-if σ V M N)

C-sub-caseℕ : ∀ {Γ Γ' C} → (σ : Sub [] Γ Γ')
            → (V : Γ' ⊢V⦂ nat) → (M : Γ' ⊢C⦂ C) → (N : Γ' ∷ nat ⊢C⦂ C)
            → C-sub σ (caseℕ V `zero M `succ N)
            ≡ caseℕ V-sub σ V `zero C-sub σ M
                              `succ C-sub (cong-∷-subˢ σ) N
C-sub-caseℕ []ˢ      V M N = refl
C-sub-caseℕ (s ◅ σ) V M N = cong (C-sub₀ s) (C-sub-caseℕ σ V M N)

C-sub-recℕ : ∀ {Γ Γ' B ε} → (σ : Sub [] Γ Γ')
           → (V : Γ' ⊢V⦂ nat) → (M : Γ' ⊢C⦂ B ! ε)
           → (N : (Γ' ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε)
           → (p : ε ·ₑ ε ≾ₑ ε)
           → C-sub σ (recℕ V M N p)
           ≡ recℕ (V-sub σ V) (C-sub σ M)
                  (C-sub (cong-∷-subˢ (cong-⟨⟩-subˢ (cong-∷-subˢ (cong-⟨⟩-subˢ σ)))) N) p
C-sub-recℕ []ˢ      V M N p = refl
C-sub-recℕ (s ◅ σ) V M N p = cong (C-sub₀ s) (C-sub-recℕ σ V M N p)

C-sub-case+ : ∀ {Γ Γ' A B C} → (σ : Sub [] Γ Γ')
            → (V : Γ' ⊢V⦂ A |+| B) → (M : Γ' ∷ A ⊢C⦂ C) → (N : Γ' ∷ B ⊢C⦂ C)
            → C-sub σ (case+ V `inl M `inr N)
            ≡ case+ V-sub σ V `inl C-sub (cong-∷-subˢ σ) M
                              `inr C-sub (cong-∷-subˢ σ) N
C-sub-case+ []ˢ      V M N = refl
C-sub-case+ (s ◅ σ) V M N = cong (C-sub₀ s) (C-sub-case+ σ V M N)

C-sub-caseL : ∀ {Γ Γ' A C} → (σ : Sub [] Γ Γ')
            → (V : Γ' ⊢V⦂ list A) → (M : Γ' ⊢C⦂ C) → (N : Γ' ∷ A ∷ list A ⊢C⦂ C)
            → C-sub σ (caseL V `nil M `cons N)
            ≡ caseL V-sub σ V `nil C-sub σ M `cons C-sub (cong-∷-subˢ (cong-∷-subˢ σ)) N
C-sub-caseL []ˢ      V M N = refl
C-sub-caseL (s ◅ σ) V M N = cong (C-sub₀ s) (C-sub-caseL σ V M N)

C-sub-recL : ∀ {Γ Γ' A B ε} → (σ : Sub [] Γ Γ')
           → (V : Γ' ⊢V⦂ list A) → (M : Γ' ⊢C⦂ B ! ε)
           → (N : (Γ' ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε)
           → (p : ε ·ₑ ε ≾ₑ ε)
           → C-sub σ (recL V M N p)
           ≡ recL (V-sub σ V) (C-sub σ M)
                  (C-sub (cong-∷-subˢ (cong-⟨⟩-subˢ (cong-∷-subˢ (cong-∷-subˢ (cong-⟨⟩-subˢ σ))))) N) p
C-sub-recL []ˢ      V M N p = refl
C-sub-recL (s ◅ σ) V M N p = cong (C-sub₀ s) (C-sub-recL σ V M N p)

C-sub-perform : ∀ {Γ Γ' A ε} → (σ : Sub [] Γ Γ') → (op : Op)
              → (V : Γ' ⊢V⦂ ⌜ param op ⌝ᵍ)
              → (M : Γ' ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ A ! ε)
              → C-sub σ (perform op V M)
              ≡ perform op (V-sub σ V) (C-sub (cong-∷-subˢ (cong-⟨⟩-subˢ σ)) M)
C-sub-perform []ˢ      op V M = refl
C-sub-perform (s ◅ σ) op V M = cong (C-sub₀ s) (C-sub-perform σ op V M)

C-sub-delay : ∀ {Γ Γ' A ε} → (σ : Sub [] Γ Γ') → (τ : 𝔻)
            → (M : Γ' ⟨ ιᵣ τ ⟩ ⊢C⦂ A ! ε)
            → C-sub σ (delay τ M) ≡ delay τ (C-sub (cong-⟨⟩-subˢ σ) M)
C-sub-delay []ˢ      τ M = refl
C-sub-delay (s ◅ σ) τ M = cong (C-sub₀ s) (C-sub-delay σ τ M)

V-sub-handler : ∀ {Γ Γ' A B ε ε'} → (σ : Sub [] Γ Γ')
              → (N : Γ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε')
              → (H : (op : Op) → (ε'' : E)
                   → Γ' ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                         ∷ [ ∣ op-grade op ∣ᵉ ]
                             (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                     ⊢C⦂ B ! (op-grade op ·ₑ ε''))
              → V-sub σ (handler N H)
              ≡ handler (C-sub (cong-∷-subˢ (cong-⟨⟩-subˢ σ)) N)
                        (λ op ε'' →
                           C-sub (cong-∷-subˢ (cong-∷-subˢ (cong-⟨⟩-subˢ σ))) (H op ε''))
V-sub-handler []ˢ      N H = refl
V-sub-handler (s ◅ σ) N H = cong (V-sub₀ s) (V-sub-handler σ N H)

C-sub-handle : ∀ {Γ Γ' A B ε ε'} → (σ : Sub [] Γ Γ')
             → (M : Γ' ⊢C⦂ A ! ε) → (V : Γ' ⊢V⦂ (A ! ε) ⇛ (B ! ε'))
             → C-sub σ (handle M `with V) ≡ handle C-sub σ M `with V-sub σ V
C-sub-handle []ˢ      M V = refl
C-sub-handle (s ◅ σ) M V = cong (C-sub₀ s) (C-sub-handle σ M V)

C-sub-unbox : ∀ {Γ Γ' A A₀ C ρ₀ ρ'} → (σ : Sub [] Γ Γ')
            → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ') → (rel : ρ' ≾ᵣ ρ₀) → (p : A₀ <:ᵛ A)
            → (M : Γ' ∷ A ⊢C⦂ C)
            → Σ[ q ∈ (rvar-elapsed (tgt-img σ x) ≾ᵣ rvar-grade (tgt-img σ x)) ]
              Σ[ w ∈ (rvar-type (tgt-img σ x) <:ᵛ A) ]
                (C-sub σ (unbox x rel p M)
                 ≡ unbox (rvar-pos (tgt-img σ x)) q w
                         (C-sub (cong-∷-subˢ σ) M))
C-sub-unbox []ˢ      x rel p M = rel , p , refl
C-sub-unbox (s ◅ σ) x rel p M =
    ≾ᵣ-trans (≾ᵣ-trans (tgt-≾₀ s (rvar-pos (tgt-img σ x)))
                       (proj₁ (C-sub-unbox σ x rel p M)))
             (tgt-grade-≾₀ s (rvar-pos (tgt-img σ x)))
  , <:ᵛ-trans (tgt-type-<:₀ s (rvar-pos (tgt-img σ x)))
              (proj₁ (proj₂ (C-sub-unbox σ x rel p M)))
  , cong (C-sub₀ s) (proj₂ (proj₂ (C-sub-unbox σ x rel p M)))

C-sub-box : ∀ {Γ Γ' A C ρ} → (σ : Sub [] Γ Γ')
          → (V : Γ' ⟨ ρ ⟩ ⊢V⦂ A) → (M : Γ' ∷ [ ρ ] A ⊢C⦂ C)
          → C-sub σ (box _ V M)
          ≡ box _ (V-sub (cong-⟨⟩-subˢ σ) V) (C-sub (cong-∷-subˢ σ) M)
C-sub-box []ˢ      V M = refl
C-sub-box (s ◅ σ) V M = cong (C-sub₀ s) (C-sub-box σ V M)

C-sub-subC : ∀ {Γ Γ' C C'} → (σ : Sub [] Γ Γ') → (p : C <:ᶜ C')
           → (M : Γ' ⊢C⦂ C)
           → C-sub σ (subC M p) ≡ subC (C-sub σ M) p
C-sub-subC []ˢ      p M = refl
C-sub-subC (s ◅ σ) p M = cong (C-sub₀ s) (C-sub-subC σ p M)

-- The one induction over term formers this layer buys: at `var` and `unbox`
-- the whole content is the hypothesis, and at every other former the two sides
-- are opened by the same structural law and closed by a congruence.

mutual

  V-sub-≐ˢ : ∀ {Γ Γ' A} {σ σ' : Sub [] Γ Γ'} → σ ≐ˢ σ'
           → (V : Γ' ⊢V⦂ A) → V-sub σ V ≡ V-sub σ' V

  V-sub-≐ˢ h (var f x) = atᵛ h x f
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h (const c) =
    trans (V-sub-const σ c) (sym (V-sub-const σ' c))
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h ⋆ =
    trans (V-sub-⋆ σ) (sym (V-sub-⋆ σ'))
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h true =
    trans (V-sub-true σ) (sym (V-sub-true σ'))
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h false =
    trans (V-sub-false σ) (sym (V-sub-false σ'))
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h zero =
    trans (V-sub-zero σ) (sym (V-sub-zero σ'))
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h (succ V) =
    trans (V-sub-succ σ V)
      (trans (cong succ (V-sub-≐ˢ h V)) (sym (V-sub-succ σ' V)))
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h ⦉ V , W ⦊ =
    trans (V-sub-⦉⦊ σ V W)
      (trans (cong₂ ⦉_,_⦊ (V-sub-≐ˢ h V) (V-sub-≐ˢ h W))
             (sym (V-sub-⦉⦊ σ' V W)))
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h (inl V) =
    trans (V-sub-inl σ V)
      (trans (cong inl (V-sub-≐ˢ h V)) (sym (V-sub-inl σ' V)))
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h (inr V) =
    trans (V-sub-inr σ V)
      (trans (cong inr (V-sub-≐ˢ h V)) (sym (V-sub-inr σ' V)))
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h nil =
    trans (V-sub-nil σ) (sym (V-sub-nil σ'))
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h (cons V W) =
    trans (V-sub-cons σ V W)
      (trans (cong₂ cons (V-sub-≐ˢ h V) (V-sub-≐ˢ h W)) (sym (V-sub-cons σ' V W)))
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h (lam M) =
    trans (V-sub-lam σ M)
      (trans (cong lam (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ h) M))
             (sym (V-sub-lam σ' M)))
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h (handler N H) =
    trans (V-sub-handler σ N H)
      (trans (handler-≡ (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ (cong-⟨⟩-subˢ-≐ˢ h)) N)
                (λ op ε'' →
                   C-sub-≐ˢ (cong-∷-subˢ-≐ˢ (cong-∷-subˢ-≐ˢ (cong-⟨⟩-subˢ-≐ˢ h)))
                            (H op ε'')))
             (sym (V-sub-handler σ' N H)))
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h (subV V p) =
    trans (V-sub-subV σ p V)
      (trans (subV-≡ (V-sub-≐ˢ h V)) (sym (V-sub-subV σ' p V)))

  C-sub-≐ˢ : ∀ {Γ Γ' C} {σ σ' : Sub [] Γ Γ'} → σ ≐ˢ σ'
           → (M : Γ' ⊢C⦂ C) → C-sub σ M ≡ C-sub σ' M

  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (return V) =
    trans (C-sub-return σ V)
      (trans (cong return (V-sub-≐ˢ h V)) (sym (C-sub-return σ' V)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (M ⨟ N) =
    trans (C-sub-⨟ σ M N)
      (trans (cong₂ _⨟_ (C-sub-≐ˢ h M)
                        (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ (cong-⟨⟩-subˢ-≐ˢ h)) N))
             (sym (C-sub-⨟ σ' M N)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (V · W) =
    trans (C-sub-· σ V W)
      (trans (cong₂ _·_ (V-sub-≐ˢ h V) (V-sub-≐ˢ h W)) (sym (C-sub-· σ' V W)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (match V `in M) =
    trans (C-sub-match σ V M)
      (trans (cong₂ match_`in_ (V-sub-≐ˢ h V)
                    (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ (cong-∷-subˢ-≐ˢ h)) M))
             (sym (C-sub-match σ' V M)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (absurd V) =
    trans (C-sub-absurd σ V)
      (trans (cong absurd (V-sub-≐ˢ h V)) (sym (C-sub-absurd σ' V)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (cmp ⋈ V W et) =
    trans (C-sub-cmp σ ⋈ V W et)
      (trans (cong₂ (λ a b → cmp ⋈ a b et) (V-sub-≐ˢ h V) (V-sub-≐ˢ h W))
             (sym (C-sub-cmp σ' ⋈ V W et)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (if V `then M `else N) =
    trans (C-sub-if σ V M N)
      (trans (cong₃ if_`then_`else_
                (V-sub-≐ˢ h V) (C-sub-≐ˢ h M) (C-sub-≐ˢ h N))
             (sym (C-sub-if σ' V M N)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (caseℕ V `zero M `succ N) =
    trans (C-sub-caseℕ σ V M N)
      (trans (cong₃ caseℕ_`zero_`succ_ (V-sub-≐ˢ h V)
                (C-sub-≐ˢ h M) (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ h) N))
             (sym (C-sub-caseℕ σ' V M N)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (recℕ V M N p) =
    trans (C-sub-recℕ σ V M N p)
      (trans (cong₃ (λ a b c → recℕ a b c p) (V-sub-≐ˢ h V) (C-sub-≐ˢ h M)
                (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ (cong-⟨⟩-subˢ-≐ˢ
                             (cong-∷-subˢ-≐ˢ (cong-⟨⟩-subˢ-≐ˢ h)))) N))
             (sym (C-sub-recℕ σ' V M N p)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (caseL V `nil M `cons N) =
    trans (C-sub-caseL σ V M N)
      (trans (cong₃ caseL_`nil_`cons_ (V-sub-≐ˢ h V) (C-sub-≐ˢ h M)
                    (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ (cong-∷-subˢ-≐ˢ h)) N))
             (sym (C-sub-caseL σ' V M N)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (recL V M N p) =
    trans (C-sub-recL σ V M N p)
      (trans (cong₃ (λ a b c → recL a b c p) (V-sub-≐ˢ h V) (C-sub-≐ˢ h M)
                (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ (cong-⟨⟩-subˢ-≐ˢ
                             (cong-∷-subˢ-≐ˢ (cong-∷-subˢ-≐ˢ (cong-⟨⟩-subˢ-≐ˢ h))))) N))
             (sym (C-sub-recL σ' V M N p)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (case+ V `inl M `inr N) =
    trans (C-sub-case+ σ V M N)
      (trans (cong₃ case+_`inl_`inr_ (V-sub-≐ˢ h V)
                (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ h) M) (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ h) N))
             (sym (C-sub-case+ σ' V M N)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (perform op V M) =
    trans (C-sub-perform σ op V M)
      (trans (cong₂ (perform op) (V-sub-≐ˢ h V)
                    (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ (cong-⟨⟩-subˢ-≐ˢ h)) M))
             (sym (C-sub-perform σ' op V M)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (delay τ M) =
    trans (C-sub-delay σ τ M)
      (trans (cong (delay τ) (C-sub-≐ˢ (cong-⟨⟩-subˢ-≐ˢ h) M))
             (sym (C-sub-delay σ' τ M)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (handle M `with V) =
    trans (C-sub-handle σ M V)
      (trans (cong₂ handle_`with_ (C-sub-≐ˢ h M) (V-sub-≐ˢ h V))
             (sym (C-sub-handle σ' M V)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (unbox x rel p M) =
    trans (proj₂ (proj₂ (C-sub-unbox σ x rel p M)))
      (trans (unbox-≡ (atᵗ h x) (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ h) M))
             (sym (proj₂ (proj₂ (C-sub-unbox σ' x rel p M)))))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (box _ V M) =
    trans (C-sub-box σ V M)
      (trans (cong₂ (box _) (V-sub-≐ˢ (cong-⟨⟩-subˢ-≐ˢ h) V)
                        (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ h) M))
             (sym (C-sub-box σ' V M)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (subC M p) =
    trans (C-sub-subC σ p M)
      (trans (subC-≡ (C-sub-≐ˢ h M)) (sym (C-sub-subC σ' p M)))

-- `⌜_⌝` is faithful for the two observations, and a chain's head may be
-- replaced by one acting alike, dropped when it is identity-like, or left to
-- act on a tail replaced the same way.

⌜⌝-≐ˢ₀ : ∀ {Γ Γ'} {r r' : Ren [] Γ Γ'} → r ≐ʳ r' → ⌜ r ⌝ ≐ˢ₀ ⌜ r' ⌝
⌜⌝-≐ˢ₀ h = mk≐ˢ₀ (λ x f → var-img-≡ (at h x) _ _) (λ y → rvar-≡ (at h y))

◅-≐ˢ₀ : ∀ {Γ Δ Γ'} {s s' : Sub₀ [] Γ Δ} → s ≐ˢ₀ s' → (σ : Sub [] Δ Γ')
      → (s ◅ σ) ≐ˢ (s' ◅ σ)
◅-≐ˢ₀ h σ = mk≐ˢ (λ x f → V-sub₀-≐ˢ₀ h (sub-var σ x f)) (λ y → atᵗ h _)

◅-tail-≐ˢ : ∀ {Γ Δ Γ'} → (s : Sub₀ [] Γ Δ) → {σ σ' : Sub [] Δ Γ'}
          → σ ≐ˢ σ' → (s ◅ σ) ≐ˢ (s ◅ σ')
◅-tail-≐ˢ s h =
  mk≐ˢ (λ x f → cong (V-sub₀ s) (atᵛ h x f))
       (λ y → cong (λ t → tgt-img₀ s (rvar-pos t)) (atᵗ h y))

id-◅-≐ˢ : ∀ {Γ Γ'} {r : Ren [] Γ Γ} → r ≐ʳ id-ren → (σ : Sub [] Γ Γ')
        → (⌜ r ⌝ ◅ σ) ≐ˢ σ
id-◅-≐ˢ {r = r} h σ =
  mk≐ˢ (λ x f → trans (V-sub₀-⌜⌝ r (sub-var σ x f))
                      (V-rename-id-≡ h (sub-var σ x f)))
       (λ y → rvar-≡ (at h (rvar-pos (tgt-img σ y))))

-- A retyping under one more binder, resp. lock, is that binder's congruence
-- applied to the retyping.

eq-ren-∷-≐ˢ₀ : ∀ {Γ₁ Γ₂ B} → (e' : Γ₁ ≡ Γ₂) → (e : Γ₁ ∷ B ≡ Γ₂ ∷ B)
             → ⌜ eq-ren e ⌝ ≐ˢ₀ cong-∷-sub {A = B} ⌜ eq-ren e' ⌝
eq-ren-∷-≐ˢ₀ {B = B} e' e =
  ≐ˢ₀-trans
    (⌜⌝-≐ˢ₀ (≐ʳ-trans (eq-ren-≐ʳ e (cong (_∷ B) e')) (eq-ren-∷-≐ʳ e')))
    (≐ˢ₀-sym (cong-∷-sub-⌜⌝ ≐ˢ₀-refl))

eq-ren-⟨⟩-≐ˢ₀ : ∀ {Γ₁ Γ₂ ρ} → (e' : Γ₁ ≡ Γ₂) → (e : Γ₁ ⟨ ρ ⟩ ≡ Γ₂ ⟨ ρ ⟩)
              → ⌜ eq-ren e ⌝ ≐ˢ₀ cong-⟨⟩-sub {ρ = ρ} ⌜ eq-ren e' ⌝
eq-ren-⟨⟩-≐ˢ₀ {ρ = ρ} e' e =
  ≐ˢ₀-trans
    (⌜⌝-≐ˢ₀ (≐ʳ-trans (eq-ren-≐ʳ e (cong (_⟨ ρ ⟩) e')) (eq-ren-⟨⟩-≐ʳ e')))
    (≐ˢ₀-sym (cong-⟨⟩-sub-⌜⌝ ≐ˢ₀-refl))
