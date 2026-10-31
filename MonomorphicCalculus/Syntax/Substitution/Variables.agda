------------------------------------------------------------------------
-- How a single substitution acts on a variable.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.Syntax.Substitution.Variables (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts        Spec
open import MonomorphicCalculus.Syntax.Terms           Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming        Spec
open import MonomorphicCalculus.Syntax.Substitution    Spec
open import MonomorphicCalculus.Syntax.Types           Spec

open import MonomorphicCalculus.Syntax.Renaming.Equivalence     Spec
open import MonomorphicCalculus.Syntax.Renaming.Coherence       Spec
open import MonomorphicCalculus.Syntax.Terms.Equivalence        Spec
open import MonomorphicCalculus.Syntax.Terms.Transport          Spec
open import MonomorphicCalculus.Syntax.Substitution.Base         Spec
open import MonomorphicCalculus.Syntax.Substitution.Lookup       Spec
open import MonomorphicCalculus.Syntax.Substitution.Equivalence  Spec


-- The action is defined under a suffix `Δ`, and a variable of that suffix is
-- one the environment does not close: it is carried along, its position fixed
-- and only its side condition recomputed. `∈-++ᶜʳ` is the injection, and the
-- lemmas below let the recursion see through the casts and the congruence
-- renamings.

-- A cast acts on a variable by relocating it.

castᵛ-var : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ')
          → .(f : A Et∨≾ᵘ ρ) → (x : A ∈[ ρ ] Γ)
          → castᵛ e (var x f) ≡ var (subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x) f
castᵛ-var refl f x = refl

-- The same, taking the relocation as a `Var` equality, which is what the
-- pushing lemmas below have, their grades changing along with their positions.

castᵛ-var-Var : ∀ {Γ Γ' A ρ ρ'} → (e : Γ ≡ Γ')
              → (x : A ∈[ ρ ] Γ) → (x' : A ∈[ ρ' ] Γ')
              → Var-cast e (ρ , x) ≡ (ρ' , x')
              → .(f : A Et∨≾ᵘ ρ) → .(f' : A Et∨≾ᵘ ρ')
              → castᵛ e (var x f) ≡ var x' f'
castᵛ-var-Var refl x _ refl f f' = refl

-- Casting the target of a renaming is prefixing it with an `eq-ren`.

castᵛ-rename : ∀ {Γ Γ' Γ'' A} → (e : Γ' ≡ Γ'') → (r : Ren [] Γ' Γ)
             → (V : Γ ⊢ᵛ⦂ A)
             → castᵛ e (V-rename r V) ≡ V-rename (r ∘ʳ eq-ren e) V
castᵛ-rename refl r V =
  sym (trans (V-rename-∘ r id-ren V) (V-rename-id-≡ ≐ʳ-refl _))

-- Relocating a suffix variable along associativity re-brackets the injection.

∈-++ᶜʳ-assoc : ∀ {A ρ} → (Γ Γ' : Ctx) → {Δ : Ctx} → (x : A ∈[ ρ ] Δ)
             → subst (λ Γ₀ → A ∈[ ρ ] Γ₀) (++ᶜ-assoc Γ Γ' Δ)
                     (∈-++ᶜʳ {Γ = Γ ++ᶜ Γ'} x)
             ≡ ∈-++ᶜʳ {Γ = Γ} (∈-++ᶜʳ {Γ = Γ'} x)

∈-++ᶜʳ-assoc Γ Γ' {Δ ∷ B} Hd       = subst-Hd (++ᶜ-assoc Γ Γ' Δ)
∈-++ᶜʳ-assoc Γ Γ' {Δ ∷ B} (Tl-∷ x) =
  trans (subst-Tl-∷ (++ᶜ-assoc Γ Γ' Δ) (∈-++ᶜʳ x))
        (cong Tl-∷ (∈-++ᶜʳ-assoc Γ Γ' x))
∈-++ᶜʳ-assoc Γ Γ' {Δ ⟨ ρ ⟩} (Tl-⟨⟩ x) =
  trans (subst-Tl-⟨⟩ (++ᶜ-assoc Γ Γ' Δ) (∈-++ᶜʳ x))
        (cong Tl-⟨⟩ (∈-++ᶜʳ-assoc Γ Γ' x))

-- A congruence renaming fixes a suffix variable, up to its grade bound.

cong-ren-img-r : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ' Γ) → {Δ : Ctx} → (x : A ∈[ ρ ] Δ)
               → var-img (cong-ren {Γ'' = Δ} r) (∈-++ᶜʳ {Γ = Γ} x)
               ≡ (ρ , ∈-++ᶜʳ {Γ = Γ'} x)

cong-ren-img-r r Hd        = refl
cong-ren-img-r r (Tl-∷ x)  =
  cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (cong-ren-img-r r x)
cong-ren-img-r r (Tl-⟨⟩ {ρ = ρ₁} x) =
  cong (λ z → proj₁ z ·ᵣ ρ₁ , Tl-⟨⟩ (proj₂ z)) (cong-ren-img-r r x)

-- Renaming a suffix variable along a congruence renaming leaves it where it is.

ren-var-r : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ' Γ) → {Δ : Ctx} → (x : A ∈[ ρ ] Δ)
          → .(f f' : A Et∨≾ᵘ ρ)
          → V-rename (cong-ren {Γ'' = Δ} r) (var (∈-++ᶜʳ {Γ = Γ} x) f)
          ≡ var (∈-++ᶜʳ {Γ = Γ'} x) f'
ren-var-r r x f f' =
  var-ren-img-≡ (cong-ren r) (∈-++ᶜʳ x) f (cong-ren-img-r r x) f'

-- The variable being replaced lies in the prefix, so a suffix variable survives
-- it: what comes back is that variable again, its position fixed and only its
-- side condition recomputed. Induction on the suffix variable, which is also the
-- recursion of `split-≡-++ᶜ = ≡-split refl` and of `⟨_,_⟩[_↦_]var`.

-- Since the substitution reads its result context off the splitting, the two
-- halves are given rather than computed, and no retyping appears at all.

sub-var-r : ∀ {Γ₁ B} → (Γ₂ : Ctx) → ∀ {A ρ}
          → (x : A ∈[ ρ ] Γ₂)
          → (W : Γ₁ ⊢ᵛ⦂ B)
          → .(f f' : A Et∨≾ᵘ ρ)
          → sub-var₀ (sub-atˢ₀ {Γ₁} {B} Γ₂ W) (∈-++ᶜʳ {Γ = Γ₁ ∷ B} x) f
          ≡ var (∈-++ᶜʳ {Γ = Γ₁} x) f'

sub-var-r (Γ₂ ∷ C) Hd W f f' = refl

sub-var-r {Γ₁} (Γ₂ ∷ C) (Tl-∷ x) W f f' =
  trans (V-rename-cong wk-ren (sub-var-r Γ₂ x W f f))
        (var-ren-img-≡ wk-ren (∈-++ᶜʳ {Γ = Γ₁} x) f refl f')

sub-var-r {Γ₁} (Γ₂ ⟨ ρ ⟩) {A = A} (Tl-⟨⟩ x) W f f' with eternal? A

... | yes et =
  eternal-val-ext-cong et (sub-var-r Γ₂ x W _ (et-ok et))

... | no ¬et =
  trans (V-rename-cong rn
           (sub-var-r Γ₂ x W (Et∨≾ᵘ-zero-productˡ f) (Et∨≾ᵘ-zero-productˡ f)))
        (var-ren-img-≡ rn (∈-++ᶜʳ {Γ = Γ₁} x) (Et∨≾ᵘ-zero-productˡ f)
           (cong (var-img′ (⟨⟩-≤-ren (≾ᵣ-zero-productʳ (Et∨≾ᵘ→¬Et⇒≾ f ¬et))))
                 (⟨⟩-η⁻¹-img (∈-++ᶜʳ {Γ = Γ₁} x)))
           f')
  where
    rn : ∀ {Γ₀ : Ctx} → Ren [] (Γ₀ ⟨ ρ ⟩) Γ₀
    rn = ⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (Et∨≾ᵘ→¬Et⇒≾ f ¬et))

-- A variable the splitting sends right is that variable, pushed right.

∈-++ᶜ-split-inj₂ : ∀ {A ρ} → (Δ₁ Δ₂ : Ctx) → (x : A ∈[ ρ ] (Δ₁ ++ᶜ Δ₂))
                 → (y : A ∈[ ρ ] Δ₂)
                 → ∈-++ᶜ-split Δ₁ Δ₂ x ≡ inj₂ y
                 → x ≡ ∈-++ᶜʳ {Γ = Δ₁} y

∈-++ᶜ-split-inj₂ Δ₁ (Δ₂ ∷ B) Hd .Hd refl = refl

∈-++ᶜ-split-inj₂ Δ₁ (Δ₂ ∷ B) (Tl-∷ x) y eq
  with ∈-++ᶜ-split Δ₁ Δ₂ x in eq'
... | inj₁ p  with eq
...   | ()
∈-++ᶜ-split-inj₂ Δ₁ (Δ₂ ∷ B) (Tl-∷ x) y eq
    | inj₂ y' with eq
...   | refl = cong Tl-∷ (∈-++ᶜ-split-inj₂ Δ₁ Δ₂ x y' eq')

∈-++ᶜ-split-inj₂ Δ₁ (Δ₂ ⟨ ρ ⟩) (Tl-⟨⟩ x) y eq
  with ∈-++ᶜ-split Δ₁ Δ₂ x in eq'
... | inj₁ p  with eq
...   | ()
∈-++ᶜ-split-inj₂ Δ₁ (Δ₂ ⟨ ρ ⟩) (Tl-⟨⟩ x) y eq
    | inj₂ y' with eq
...   | refl = cong Tl-⟨⟩ (∈-++ᶜ-split-inj₂ Δ₁ Δ₂ x y' eq')

-- The third possibility: the variable looked up is the one being replaced, so
-- what comes back is the value, pushed under the suffix by `push-ren`, up to
-- the grade bounds `_≐ʳ_` does not see. Non-eternality selects that branch at a
-- lock; at an eternal type the substitution extends the value instead.

sub-var-hit : ∀ {Γ₁ B} → (Γ₂ : Ctx) → ¬ Et B
            → (p : ctx-grade Γ₂ ≾ᵣ 𝟏ᵣ)
            → (W : Γ₁ ⊢ᵛ⦂ B)
            → .(f : B Et∨≾ᵘ ctx-grade Γ₂)
            → sub-var₀ (sub-atˢ₀ {Γ₁} {B} Γ₂ W)
                       (split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})) f
            ≡ V-rename (push-ren Γ₂ p) W

sub-var-hit [] ¬et p W f =
  sym (V-rename-id-≡ ≐ʳ-refl _)

sub-var-hit (Γ₂ ∷ C) ¬et p W f =
  trans (V-rename-cong wk-ren (sub-var-hit Γ₂ ¬et p W f))
        (sym (V-rename-∘ (push-ren Γ₂ p) wk-ren _))

sub-var-hit {B = B} (Γ₂ ⟨ ρ ⟩) ¬et p W f with eternal? B

... | yes et = ⊥-elim (¬et et)

... | no ¬p =
  trans (V-rename-cong rn (sub-var-hit Γ₂ ¬et pᵢ W (Et∨≾ᵘ-zero-productˡ f)))
    (trans (sym (V-rename-∘ (push-ren Γ₂ pᵢ) rn _))
              (V-rename-≡ (∘ʳ-≐ʳ ≐ʳ-refl (∘ʳ-≐ʳ ≐ʳ-refl (⟨⟩-≤-ren-≐ʳ _ _))) _))
  where
    rn : ∀ {Γ₀ : Ctx} → Ren [] (Γ₀ ⟨ ρ ⟩) Γ₀
    rn = ⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (Et∨≾ᵘ→¬Et⇒≾ f ¬p))

    pᵢ = ≾ᵣ-zero-productˡ p

-- The same, taking the looked-up variable as an equation: what reaches the
-- substitution is `∈-++ᶜˡ Γ₂ Hd`, which is `split→∈` of the splitting only up
-- to `split→∈-∈-++ᶜˡ`.

sub-var-hit′ : ∀ {Γ₁ B σ} → (Γ₂ : Ctx) → ¬ Et B
             → (p : ctx-grade Γ₂ ≾ᵣ 𝟏ᵣ)
             → (y : B ∈[ σ ] ((Γ₁ ∷ B) ++ᶜ Γ₂))
             → _≡_ {A = Var ((Γ₁ ∷ B) ++ᶜ Γ₂) B}
                 (σ , y)
                 (ctx-grade Γ₂ , split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}))
             → (W : Γ₁ ⊢ᵛ⦂ B)
             → .(f : B Et∨≾ᵘ σ)
             → sub-var₀ (sub-atˢ₀ {Γ₁} {B} Γ₂ W) y f
             ≡ V-rename (push-ren Γ₂ p) W
sub-var-hit′ Γ₂ ¬et p _ refl W f = sub-var-hit Γ₂ ¬et p W f

-- The `rvar` counterpart of `sub-var-r`: `⟨_⟩[_↦_]rvar` returns the same
-- resource variable when the variable it replaces is a different one.
-- Simpler than the value versions: a box type is never eternal, so there is
-- no `eternal?` split.

-- The cell the boundary substitution puts a resource variable at.

atᴿ : ∀ {Γ B A ρ σ} → (Θ : Ctx) → ([ ρ ] A ∈[ σ ] ((Γ ∷ B) ++ᶜ Θ)) → Γ ⊢ᵛ⦂ B
    → RVar (Γ ++ᶜ Θ)
atᴿ Θ z W = tgt-img₀ (sub-atˢ₀ Θ W) z

sub-rvar-r : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ σ}
           → (z : [ ρ ] A ∈[ σ ] Θ) → (W : Γ ⊢ᵛ⦂ B)
           → atᴿ {Γ} {B} Θ (∈-++ᶜʳ {Γ = Γ ∷ B} z) W ≡ (ρ , A , σ , ∈-++ᶜʳ {Γ = Γ} z)

sub-rvar-r (Θ ∷ C)   Hd       W = refl
sub-rvar-r (Θ ∷ C)   (Tl-∷ z) W = cong RVar-∷ (sub-rvar-r Θ z W)
sub-rvar-r (Θ ⟨ ρ' ⟩) (Tl-⟨⟩ z) W = cong (RVar-⟨⟩ ρ') (sub-rvar-r Θ z W)

sub-rvar-l : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ σ}
           → (z : [ ρ ] A ∈[ σ ] Γ) → (W : Γ ⊢ᵛ⦂ B)
           → atᴿ {Γ} {B} Θ (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Tl-∷ z)) W
           ≡ (ρ , A , grade-++ᶜˡ σ Θ , ∈-++ᶜˡ {Γ = Γ} Θ z)

sub-rvar-l []         z W = refl
sub-rvar-l (Θ ∷ C)    z W = cong RVar-∷ (sub-rvar-l Θ z W)
sub-rvar-l (Θ ⟨ ρ' ⟩) z W = cong (RVar-⟨⟩ ρ') (sub-rvar-l Θ z W)

