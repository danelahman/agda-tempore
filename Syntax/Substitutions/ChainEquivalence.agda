------------------------------------------------------------------------
-- When two parallel substitutions act alike.                         --
--                                                                    --
-- Chains of different lengths can act the same way, so `_≐ˢ_` is an   --
-- observation, as `_≐ʳ_` is. Transferring it to terms is the one      --
-- induction over term formers the whole layer needs; the congruences  --
-- it uses are chain inductions resting on the interchange.            --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions.ChainEquivalence (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.RenActions S
open import Syntax.Renamings  S
open import Syntax.Types      S

open import Syntax.Renamings.Equivalence S
open import Syntax.Renamings.Coherence   S
open import Syntax.Terms.Equivalence     S

open import Syntax.Substitutions.Base        S
open import Syntax.Substitutions.Lookup   S
open import Syntax.Substitutions.Action      S
open import Syntax.Substitutions.Equivalence S
open import Syntax.Substitutions.Interchange    S
open import Syntax.Substitutions.Chain       S

-- Where a chain sends a resource variable.

tgt-img : ∀ {Γ Γ' A ρ ρ'} → Sub [] Γ Γ' → [ ρ ] A ∈[ ρ' ] Γ' → Var Γ ([ ρ ] A)
tgt-img σ y = proj₁ (sub-tgt σ y) , proj₁ (proj₂ (sub-tgt σ y))

infix 4 _≐ˢ_

record _≐ˢ_ {Γ Γ'} (σ σ' : Sub [] Γ Γ') : Set where
  constructor mk≐ˢ
  field
    atᵛ : ∀ {A ρ} → (x : A ∈[ ρ ] Γ') → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
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
-- variables, constants, `⋆` and pairs.

V-sub₀-ext : ∀ {Γ Γ' A ρ} → (s : Sub₀ [] Γ Γ') → (et : Eternal A)
           → (V : Γ' ⊢V⦂ A)
           → V-sub₀ (cong-⟨⟩-sub {ρ = ρ} s) (eternal-val-ext et V)
           ≡ eternal-val-ext et (V-sub₀ s V)
V-sub₀-ext s et (var f x) rewrite eternal?-yes et =
  cong (eternal-val-ext et) (sub-var₀-irr s x _ f)
V-sub₀-ext s et (const c) = refl
V-sub₀-ext s et ⋆         = refl
V-sub₀-ext s et true      = refl
V-sub₀-ext s et false     = refl
V-sub₀-ext s (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ =
  cong₂ ⦉_,_⦊ (V-sub₀-ext s et₁ V₁) (V-sub₀-ext s et₂ V₂)

-- Each is a chain induction: the head step's clause is moved past the tail's
-- accumulated image by the interchange, leaving the image the chain would have
-- produced without the congruence.

-- Under one more variable.

cong-∷-subˢ-Hd : ∀ {Γ Γ' B} → (σ : Sub [] Γ Γ')
               → (f : ¬ Eternal B → uᵣ ≾ᵣ uᵣ)
               → sub-var (cong-∷-subˢ {A = B} σ) Hd f ≡ var f Hd
cong-∷-subˢ-Hd []ˢ      f = refl
cong-∷-subˢ-Hd (s ◅ σ) f =
  trans (cong (V-sub₀ (cong-∷-sub s)) (cong-∷-subˢ-Hd σ f)) var-≡

cong-∷-subˢ-Tl : ∀ {Γ Γ' A B ρ} → (σ : Sub [] Γ Γ')
               → (y : A ∈[ ρ ] Γ') → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
               → sub-var (cong-∷-subˢ {A = B} σ) (Tl-∷ y) f
               ≡ V-rename wk-ren (sub-var σ y f)
cong-∷-subˢ-Tl []ˢ      y f = var-≡
cong-∷-subˢ-Tl (s ◅ σ) y f =
  trans (cong (V-sub₀ (cong-∷-sub s)) (cong-∷-subˢ-Tl σ y f))
        (V-sub₀-ren (⋈-wk s) (sub-var σ y f))

cong-∷-subˢ-tgt : ∀ {Γ Γ' A B ρ ρ'} → (σ : Sub [] Γ Γ')
                → (y : [ ρ ] A ∈[ ρ' ] Γ')
                → tgt-img (cong-∷-subˢ {A = B} σ) (Tl-∷ y) ≡ Var-∷ (tgt-img σ y)
cong-∷-subˢ-tgt []ˢ      y = refl
cong-∷-subˢ-tgt (s ◅ σ) y =
  cong (λ t → tgt-img₀ (cong-∷-sub s) (proj₂ t)) (cong-∷-subˢ-tgt σ y)

cong-∷-subˢ-tgt-Hd : ∀ {Γ Γ' A ρ} → (σ : Sub [] Γ Γ')
                   → tgt-img (cong-∷-subˢ {A = [ ρ ] A} σ) Hd ≡ (uᵣ , Hd)
cong-∷-subˢ-tgt-Hd []ˢ      = refl
cong-∷-subˢ-tgt-Hd (s ◅ σ) =
  cong (λ t → tgt-img₀ (cong-∷-sub s) (proj₂ t)) (cong-∷-subˢ-tgt-Hd σ)

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
        (trans (cong Var-∷ (atᵗ h y)) (sym (cong-∷-subˢ-tgt σ' y)))

-- Under one more lock. An eternal value crosses a lock either way.

eternal-val-ext-≡ : ∀ {Γ A ρ} → (et : Eternal A) → (p : ρ ≾ᵣ uᵣ) → (V : Γ ⊢V⦂ A)
                  → eternal-val-ext et V ≡ V-rename (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren p) V
eternal-val-ext-≡ et p (var f x) = var-img-≡ (sym (hit-⟨⟩-img p x)) _ _
eternal-val-ext-≡ et p (const c) = refl
eternal-val-ext-≡ et p ⋆         = refl
eternal-val-ext-≡ et p true      = refl
eternal-val-ext-≡ et p false     = refl
eternal-val-ext-≡ (et₁ |×|ₑ et₂) p ⦉ V₁ , V₂ ⦊ =
  cong₂ ⦉_,_⦊ (eternal-val-ext-≡ et₁ p V₁) (eternal-val-ext-≡ et₂ p V₂)

⋈-lock : ∀ {Γ Γ' ρ} → (s : Sub₀ [] Γ Γ') → (p p' : ρ ≾ᵣ uᵣ)
       → Interchange (cong-⟨⟩-sub {ρ = ρ} s) (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren p)
                     (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren p') s
⋈-lock {Γ} {Γ'} {ρ} s p p' = mk⋈ goᵛ goᵗ
  where
    goᵛ : ∀ {A' ρ'} → (x : A' ∈[ ρ' ] Γ') → (f : ¬ Eternal A' → ρ' ≾ᵣ uᵣ)
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
    goᵗ y = sym (hit-⟨⟩-img p' (proj₂ (tgt-img₀ s y)))

cong-⟨⟩-subˢ-et : ∀ {Γ Γ' A ρ ρ'} → (σ : Sub [] Γ Γ') → (et : Eternal A)
                → (y : A ∈[ ρ' ] Γ') → (f : ¬ Eternal A → ρ' ·ᵣ ρ ≾ᵣ uᵣ)
                → sub-var (cong-⟨⟩-subˢ {ρ = ρ} σ) (Tl-⟨⟩ y) f
                ≡ eternal-val-ext et (sub-var σ y (et-bound et))
cong-⟨⟩-subˢ-et []ˢ      et y f = var-≡
cong-⟨⟩-subˢ-et (s ◅ σ) et y f =
  trans (cong (V-sub₀ (cong-⟨⟩-sub s)) (cong-⟨⟩-subˢ-et σ et y f))
        (V-sub₀-ext s et (sub-var σ y (et-bound et)))

cong-⟨⟩-subˢ-ne : ∀ {Γ Γ' A ρ ρ'} → (σ : Sub [] Γ Γ') → (¬et : ¬ Eternal A)
                → (y : A ∈[ ρ' ] Γ') → (f : ¬ Eternal A → ρ' ·ᵣ ρ ≾ᵣ uᵣ)
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
                 ≡ Var-⟨⟩ ρ (tgt-img σ y)
cong-⟨⟩-subˢ-tgt []ˢ      y = refl
cong-⟨⟩-subˢ-tgt (s ◅ σ) y =
  cong (λ t → tgt-img₀ (cong-⟨⟩-sub s) (proj₂ t)) (cong-⟨⟩-subˢ-tgt σ y)

cong-⟨⟩-subˢ-≐ˢ : ∀ {Γ Γ' ρ} {σ σ' : Sub [] Γ Γ'}
                → σ ≐ˢ σ' → cong-⟨⟩-subˢ {ρ = ρ} σ ≐ˢ cong-⟨⟩-subˢ σ'
cong-⟨⟩-subˢ-≐ˢ {Γ} {Γ'} {ρ} {σ} {σ'} h = mk≐ˢ goᵛ goᵗ
  where
    goᵛ : ∀ {A' ρ'} → (x : A' ∈[ ρ' ] (Γ' ⟨ ρ ⟩))
        → (f : ¬ Eternal A' → ρ' ≾ᵣ uᵣ)
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
        (trans (cong (Var-⟨⟩ ρ) (atᵗ h y)) (sym (cong-⟨⟩-subˢ-tgt σ' y)))

sub-var-irr : ∀ {Γ Γ' A ρ} → (σ : Sub [] Γ Γ') → (x : A ∈[ ρ ] Γ')
            → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
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

V-sub-⦉⦊ : ∀ {Γ Γ' A B} → (σ : Sub [] Γ Γ')
         → (V : Γ' ⊢V⦂ A) → (W : Γ' ⊢V⦂ B)
         → V-sub σ ⦉ V , W ⦊ ≡ ⦉ V-sub σ V , V-sub σ W ⦊
V-sub-⦉⦊ []ˢ      V W = refl
V-sub-⦉⦊ (s ◅ σ) V W = cong (V-sub₀ s) (V-sub-⦉⦊ σ V W)

V-sub-lam : ∀ {Γ Γ' A C} → (σ : Sub [] Γ Γ') → (M : Γ' ∷ A ⊢C⦂ C)
          → V-sub σ (lam M) ≡ lam (C-sub (cong-∷-subˢ σ) M)
V-sub-lam []ˢ      M = refl
V-sub-lam (s ◅ σ) M = cong (V-sub₀ s) (V-sub-lam σ M)

C-sub-return : ∀ {Γ Γ' A} → (σ : Sub [] Γ Γ') → (V : Γ' ⊢V⦂ A)
             → C-sub σ (return V) ≡ return (V-sub σ V)
C-sub-return []ˢ      V = refl
C-sub-return (s ◅ σ) V = cong (C-sub₀ s) (C-sub-return σ V)

C-sub-⨟ : ∀ {Γ Γ' A B ε ε'} → (σ : Sub [] Γ Γ')
        → (M : Γ' ⊢C⦂ A ‼ ε) → (N : Γ' ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε')
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

C-sub-absurd : ∀ {Γ Γ' C} → (σ : Sub [] Γ Γ') → (V : Γ' ⊢V⦂ Empty)
             → C-sub σ (absurd {C = C} V) ≡ absurd (V-sub σ V)
C-sub-absurd []ˢ      V = refl
C-sub-absurd (s ◅ σ) V = cong (C-sub₀ s) (C-sub-absurd σ V)

C-sub-if : ∀ {Γ Γ' C} → (σ : Sub [] Γ Γ')
         → (V : Γ' ⊢V⦂ Bool) → (M N : Γ' ⊢C⦂ C)
         → C-sub σ (if V `then M `else N)
         ≡ if V-sub σ V `then C-sub σ M `else C-sub σ N
C-sub-if []ˢ      V M N = refl
C-sub-if (s ◅ σ) V M N = cong (C-sub₀ s) (C-sub-if σ V M N)

C-sub-perform : ∀ {Γ Γ' A ε} → (σ : Sub [] Γ Γ') → (op : Op)
              → (V : Γ' ⊢V⦂ type-of-gtype (param op))
              → (M : Γ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
              → C-sub σ (perform op V M)
              ≡ perform op (V-sub σ V) (C-sub (cong-∷-subˢ (cong-⟨⟩-subˢ σ)) M)
C-sub-perform []ˢ      op V M = refl
C-sub-perform (s ◅ σ) op V M = cong (C-sub₀ s) (C-sub-perform σ op V M)

C-sub-delay : ∀ {Γ Γ' A ε} → (σ : Sub [] Γ Γ') → (τ : ℕ)
            → (M : Γ' ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
            → C-sub σ (delay τ M) ≡ delay τ (C-sub (cong-⟨⟩-subˢ σ) M)
C-sub-delay []ˢ      τ M = refl
C-sub-delay (s ◅ σ) τ M = cong (C-sub₀ s) (C-sub-delay σ τ M)

C-sub-handle : ∀ {Γ Γ' A B ε ε'} → (σ : Sub [] Γ Γ')
             → (M : Γ' ⊢C⦂ A ‼ ε)
             → (H : (op : Op) → (ε'' : E)
                  → Γ' ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε'')
                    ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
             → (N : Γ' ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε')
             → C-sub σ (handle M `with H `in N)
             ≡ handle C-sub σ M
               `with (λ op ε'' →
                        C-sub (cong-∷-subˢ (cong-∷-subˢ (cong-⟨⟩-subˢ σ))) (H op ε''))
               `in (C-sub (cong-∷-subˢ (cong-⟨⟩-subˢ σ)) N)
C-sub-handle []ˢ      M H N = refl
C-sub-handle (s ◅ σ) M H N = cong (C-sub₀ s) (C-sub-handle σ M H N)

C-sub-unbox : ∀ {Γ Γ' A C ρ ρ'} → (σ : Sub [] Γ Γ')
            → (x : [ ρ ] A ∈[ ρ' ] Γ') → (rel : ρ' ≾ᵣ ρ) → (M : Γ' ∷ A ⊢C⦂ C)
            → Σ[ q ∈ (proj₁ (tgt-img σ x) ≾ᵣ ρ) ]
                (C-sub σ (unbox x rel M)
                 ≡ unbox (proj₂ (tgt-img σ x)) q (C-sub (cong-∷-subˢ σ) M))
C-sub-unbox []ˢ      x rel M = rel , refl
C-sub-unbox (s ◅ σ) x rel M =
    ≾ᵣ-trans (proj₂ (proj₂ (sub-tgt₀ s (proj₁ (proj₂ (sub-tgt σ x))))))
             (proj₁ (C-sub-unbox σ x rel M))
  , cong (C-sub₀ s) (proj₂ (C-sub-unbox σ x rel M))

C-sub-box : ∀ {Γ Γ' A C ρ} → (σ : Sub [] Γ Γ')
          → (V : Γ' ⟨ ρ ⟩ ⊢V⦂ A) → (M : Γ' ∷ [ ρ ] A ⊢C⦂ C)
          → C-sub σ (box V M)
          ≡ box (V-sub (cong-⟨⟩-subˢ σ) V) (C-sub (cong-∷-subˢ σ) M)
C-sub-box []ˢ      V M = refl
C-sub-box (s ◅ σ) V M = cong (C-sub₀ s) (C-sub-box σ V M)

C-sub-coerce : ∀ {Γ Γ' A ε ε'} → (σ : Sub [] Γ Γ') → (rel : ε ≾ₑ ε')
             → (M : Γ' ⊢C⦂ A ‼ ε)
             → C-sub σ (coerce rel M) ≡ coerce rel (C-sub σ M)
C-sub-coerce []ˢ      rel M = refl
C-sub-coerce (s ◅ σ) rel M = cong (C-sub₀ s) (C-sub-coerce σ rel M)

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
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h ⦉ V , W ⦊ =
    trans (V-sub-⦉⦊ σ V W)
      (trans (cong₂ ⦉_,_⦊ (V-sub-≐ˢ h V) (V-sub-≐ˢ h W))
             (sym (V-sub-⦉⦊ σ' V W)))
  V-sub-≐ˢ {σ = σ} {σ' = σ'} h (lam M) =
    trans (V-sub-lam σ M)
      (trans (cong lam (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ h) M))
             (sym (V-sub-lam σ' M)))

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
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (if V `then M `else N) =
    trans (C-sub-if σ V M N)
      (trans (cong₃ if_`then_`else_
                (V-sub-≐ˢ h V) (C-sub-≐ˢ h M) (C-sub-≐ˢ h N))
             (sym (C-sub-if σ' V M N)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (perform op V M) =
    trans (C-sub-perform σ op V M)
      (trans (cong₂ (perform op) (V-sub-≐ˢ h V)
                    (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ (cong-⟨⟩-subˢ-≐ˢ h)) M))
             (sym (C-sub-perform σ' op V M)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (delay τ M) =
    trans (C-sub-delay σ τ M)
      (trans (cong (delay τ) (C-sub-≐ˢ (cong-⟨⟩-subˢ-≐ˢ h) M))
             (sym (C-sub-delay σ' τ M)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (handle M `with H `in N) =
    trans (C-sub-handle σ M H N)
      (trans (handle-≡ (C-sub-≐ˢ h M)
                (λ op ε'' →
                   C-sub-≐ˢ (cong-∷-subˢ-≐ˢ (cong-∷-subˢ-≐ˢ (cong-⟨⟩-subˢ-≐ˢ h)))
                            (H op ε''))
                (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ (cong-⟨⟩-subˢ-≐ˢ h)) N))
             (sym (C-sub-handle σ' M H N)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (unbox x rel M) =
    trans (proj₂ (C-sub-unbox σ x rel M))
      (trans (unbox-≡ (atᵗ h x) (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ h) M))
             (sym (proj₂ (C-sub-unbox σ' x rel M))))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (box V M) =
    trans (C-sub-box σ V M)
      (trans (cong₂ box (V-sub-≐ˢ (cong-⟨⟩-subˢ-≐ˢ h) V)
                        (C-sub-≐ˢ (cong-∷-subˢ-≐ˢ h) M))
             (sym (C-sub-box σ' V M)))
  C-sub-≐ˢ {σ = σ} {σ' = σ'} h (coerce rel M) =
    trans (C-sub-coerce σ rel M)
      (trans (coerce-≡ (C-sub-≐ˢ h M)) (sym (C-sub-coerce σ' rel M)))

-- `⌜_⌝` is faithful for the two observations, and a chain's head may be
-- replaced by one acting alike, dropped when it is identity-like, or left to
-- act on a tail replaced the same way.

⌜⌝-≐ˢ₀ : ∀ {Γ Γ'} {r r' : Ren [] Γ Γ'} → r ≐ʳ r' → ⌜ r ⌝ ≐ˢ₀ ⌜ r' ⌝
⌜⌝-≐ˢ₀ h = mk≐ˢ₀ (λ x f → var-img-≡ (at h x) _ _) (λ y → at h y)

◅-≐ˢ₀ : ∀ {Γ Δ Γ'} {s s' : Sub₀ [] Γ Δ} → s ≐ˢ₀ s' → (σ : Sub [] Δ Γ')
      → (s ◅ σ) ≐ˢ (s' ◅ σ)
◅-≐ˢ₀ h σ = mk≐ˢ (λ x f → V-sub₀-≐ˢ₀ h (sub-var σ x f)) (λ y → atᵗ h _)

◅-tail-≐ˢ : ∀ {Γ Δ Γ'} → (s : Sub₀ [] Γ Δ) → {σ σ' : Sub [] Δ Γ'}
          → σ ≐ˢ σ' → (s ◅ σ) ≐ˢ (s ◅ σ')
◅-tail-≐ˢ s h =
  mk≐ˢ (λ x f → cong (V-sub₀ s) (atᵛ h x f))
       (λ y → cong (λ t → tgt-img₀ s (proj₂ t)) (atᵗ h y))

id-◅-≐ˢ : ∀ {Γ Γ'} {r : Ren [] Γ Γ} → r ≐ʳ id-ren → (σ : Sub [] Γ Γ')
        → (⌜ r ⌝ ◅ σ) ≐ˢ σ
id-◅-≐ˢ {r = r} h σ =
  mk≐ˢ (λ x f → trans (V-sub₀-⌜⌝ r (sub-var σ x f))
                      (V-rename-id-≡ h (sub-var σ x f)))
       (λ y → at h (proj₂ (tgt-img σ y)))

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
