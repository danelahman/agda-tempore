------------------------------------------------------------------------
-- How a single substitution acts on a variable.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions.Variables (Spec : LanguageSpec) where

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


------------------------------------------------------------------------
-- SUFFIX VARIABLES
--
-- The action is defined under a suffix `Δ`, and a variable of that suffix is
-- one the environment does not close: it is carried along, its position fixed
-- and only its grade bound recomputed. `∈-++ᶜʳ` is the injection, and the
-- lemmas below are what the recursion needs to see through the casts and the
-- congruence renamings.
------------------------------------------------------------------------

-- A cast acts on a variable by relocating it.

castᵛ-var : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ')
          → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → (x : A ∈[ ρ ] Γ)
          → castᵛ e (var f x) ≡ var f (subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x)
castᵛ-var refl f x = refl

-- The same, taking the relocation as a `Var` equality — which is what the
-- pushing lemmas below have, their grades changing along with their positions.

castᵛ-var-Var : ∀ {Γ Γ' A ρ ρ'} → (e : Γ ≡ Γ')
              → (x : A ∈[ ρ ] Γ) → (x' : A ∈[ ρ' ] Γ')
              → Var-cast e (ρ , x) ≡ (ρ' , x')
              → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → (f' : ¬ Eternal A → ρ' ≾ᵣ uᵣ)
              → castᵛ e (var f x) ≐ᵛ var f' x'
castᵛ-var-Var refl x _ refl f f' = var-≐

-- A cast cancels its own inverse.

castᵛ-sym-cast : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (V : Γ' ⊢V⦂ A)
               → castᵛ e (castᵛ (sym e) V) ≡ V
castᵛ-sym-cast refl V = refl

-- Casting the target of a renaming is prefixing it with an `eq-ren`.

castᵛ-rename : ∀ {Γ Γ' Γ'' A} → (e : Γ' ≡ Γ'') → (r : Ren [] Γ Γ')
             → (V : Γ ⊢V⦂ A)
             → castᵛ e (V-rename r V) ≐ᵛ V-rename (eq-ren e ∘ʳ r) V
castᵛ-rename refl r V =
  ≐ᵛ-sym (≐ᵛ-trans (V-rename-∘ id-ren r V) (V-rename-id-≐ ≐ʳ-refl _))

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

cong-ren-img-r : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → {Δ : Ctx} → (x : A ∈[ ρ ] Δ)
               → var-img (cong-ren {Γ'' = Δ} r) (∈-++ᶜʳ {Γ = Γ} x)
               ≡ (ρ , ∈-++ᶜʳ {Γ = Γ'} x)

cong-ren-img-r r Hd        = refl
cong-ren-img-r r (Tl-∷ x)  =
  cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (cong-ren-img-r r x)
cong-ren-img-r r (Tl-⟨⟩ {ρ = ρ₁} x) =
  cong (λ z → proj₁ z ·ᵣ ρ₁ , Tl-⟨⟩ (proj₂ z)) (cong-ren-img-r r x)

-- Renaming a suffix variable along a congruence renaming leaves it where it is.

ren-var-r : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → {Δ : Ctx} → (x : A ∈[ ρ ] Δ)
          → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
          → V-rename (cong-ren {Γ'' = Δ} r) (var f (∈-++ᶜʳ {Γ = Γ} x))
          ≐ᵛ var f' (∈-++ᶜʳ {Γ = Γ'} x)
ren-var-r r x f f' =
  var-ren-img-≐ (cong-ren r) (∈-++ᶜʳ x) f (cong-ren-img-r r x) f'

-- SUBSTITUTION FIXES A SUFFIX VARIABLE
--
-- The variable being replaced lies in the prefix, so a suffix variable survives
-- it: what comes back is that variable again, its position fixed and only its
-- grade bound recomputed. Induction on the suffix variable, which is also the
-- recursion of `split-≡-++ᶜ = ≡-split refl` and of `⟨_,_⟩[_↦_]var`.

-- Relocating a variable along an equality of *extended* contexts: the equality
-- must have come from one of the smaller contexts, and any two proofs agree.

-- Relocating a variable along a proof that its context is what it is.

subst-var-id : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ') → (x : A ∈[ ρ ] Γ)
             → subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x
             ≡ subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x
subst-var-id e x = refl

subst-Hd-any : ∀ {Γ Γ' A} → (e : Γ ∷ A ≡ Γ' ∷ A)
             → subst (λ Γ₀ → A ∈[ uᵣ ] Γ₀) e Hd ≡ Hd
subst-Hd-any {A = A} e =
  trans (cong (λ z → subst (λ Γ₀ → A ∈[ uᵣ ] Γ₀) z Hd)
              (uip {p = e} {q = cong (_∷ A) (∷ᶜ-injective-ctx e)}))
        (subst-Hd (∷ᶜ-injective-ctx e))

-- A cast commutes with the three things the substitution puts in front of the
-- recursive call: a weakening, an eternal extension, and a lock-crossing
-- renaming. Each is uniform in its context, so matching the equality suffices.

cast-wk-any : ∀ {Γ Γ' A C} → (e : Γ ∷ C ≡ Γ' ∷ C) → (e₀ : Γ ≡ Γ')
            → (V : Γ ⊢V⦂ A)
            → castᵛ e (V-rename (wk-ren {A = C}) V)
            ≡ V-rename wk-ren (castᵛ e₀ V)
cast-wk-any refl e₀ V rewrite uip {p = e₀} {q = refl} = refl

cast-ext-any : ∀ {Γ Γ' A ρ} → (e : Γ ⟨ ρ ⟩ ≡ Γ' ⟨ ρ ⟩) → (e₀ : Γ ≡ Γ')
             → (et : Eternal A) → (V : Γ ⊢V⦂ A)
             → castᵛ e (eternal-val-ext {ρ = ρ} et V)
             ≡ eternal-val-ext et (castᵛ e₀ V)
cast-ext-any refl e₀ et V rewrite uip {p = e₀} {q = refl} = refl

cast-ren-⟨⟩-any : ∀ {Γ Γ' A ρ} → (e : Γ ⟨ ρ ⟩ ≡ Γ' ⟨ ρ ⟩) → (e₀ : Γ ≡ Γ')
                → (r : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩)) → (V : Γ ⊢V⦂ A)
                → castᵛ e (V-rename r V) ≡ V-rename r (castᵛ e₀ V)
cast-ren-⟨⟩-any refl e₀ r V rewrite uip {p = e₀} {q = refl} = refl

-- The context equality the substitution's result is presented along.

castOf : ∀ {Γ₁ B} → (Γ₂ : Ctx)
       → (split-l (split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}))
            ++ᶜ split-r (split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})))
       ≡ (Γ₁ ++ᶜ Γ₂)
castOf {Γ₁} {B} Γ₂ =
  cong₂ _++ᶜ_ (split→∈-split-l (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}))
              (split→∈-split-r (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}))

sub-var-r : ∀ {Γ₁ B} → (Γ₂ : Ctx) → ∀ {A ρ}
          → (x : A ∈[ ρ ] Γ₂)
          → (W : split-l (split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})) ⊢V⦂ B)
          → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
          → castᵛ (castOf {Γ₁} {B} Γ₂)
              (⟨ ∈-++ᶜʳ {Γ = Γ₁ ∷ B} x , f ⟩[ split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})
                                            ↦ W ]var)
          ≐ᵛ var f' (∈-++ᶜʳ {Γ = Γ₁} x)

sub-var-r {Γ₁} {B} (Γ₂ ∷ C) Hd W f f' =
  ≐ᵛ-trans
    (≡→≐ᵛ (trans (castᵛ-var (castOf {Γ₁} {B} (Γ₂ ∷ C)) f Hd)
                 (cong (var f) (subst-Hd-any (castOf {Γ₁} {B} (Γ₂ ∷ C))))))
    var-≐

sub-var-r {Γ₁} {B} (Γ₂ ∷ C) (Tl-∷ x) W f f' =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-wk-any (castOf {Γ₁} {B} (Γ₂ ∷ C)) (castOf {Γ₁} {B} Γ₂) _))
    (≐ᵛ-trans (V-rename-cong wk-ren (sub-var-r Γ₂ x W f f))
              (var-ren-img-≐ wk-ren (∈-++ᶜʳ {Γ = Γ₁} x) f refl f'))

sub-var-r {Γ₁} {B} (Γ₂ ⟨ ρ ⟩) {A = A} (Tl-⟨⟩ x) W f f' with eternal? A

... | yes et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-ext-any (castOf {Γ₁} {B} (Γ₂ ⟨ ρ ⟩)) (castOf {Γ₁} {B} Γ₂) et _))
    (≐ᵛ-trans (eternal-val-ext-cong et
                (sub-var-r Γ₂ x W _ (λ z → ⊥-elim (z et)))) var-≐)

... | no ¬et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-ren-⟨⟩-any (castOf {Γ₁} {B} (Γ₂ ⟨ ρ ⟩)) (castOf {Γ₁} {B} Γ₂) rn _))
    (≐ᵛ-trans (V-rename-cong rn (sub-var-r Γ₂ x W fᵢ fᵢ))
              (var-ren-img-≐ rn (∈-++ᶜʳ {Γ = Γ₁} x) fᵢ
                 (cong (var-img′ (⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et))))
                       (⟨⟩-η⁻¹-img (∈-++ᶜʳ {Γ = Γ₁} x)))
                 f'))
  where
    rn : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩)
    rn = ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et)) ∘ʳ ⟨⟩-η⁻¹-ren

    fᵢ = λ z → ≾ᵣ-zero-productˡ (f z)

-- A variable the splitting sends right *is* that variable, pushed right.

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

-- A variable the splitting sends left is that variable pushed under the suffix.
-- Stated as a `Var` equality, so the grade travels with the position.

∈-++ᶜ-split-inj₁ : ∀ {A ρ ρ'} → (Δ₁ Δ₂ : Ctx) → (x : A ∈[ ρ ] (Δ₁ ++ᶜ Δ₂))
                 → (z : A ∈[ ρ' ] Δ₁)
                 → ∈-++ᶜ-split Δ₁ Δ₂ x ≡ inj₁ (ρ' , z)
                 → (ρ , x) ≡ (grade-++ᶜˡ ρ' Δ₂ , ∈-++ᶜˡ Δ₂ z)

∈-++ᶜ-split-inj₁ Δ₁ []       x .x refl = refl

∈-++ᶜ-split-inj₁ Δ₁ (Δ₂ ∷ B) Hd       z eq with eq
... | ()
∈-++ᶜ-split-inj₁ Δ₁ (Δ₂ ∷ B) (Tl-∷ x) z eq
  with ∈-++ᶜ-split Δ₁ Δ₂ x in eq'
... | inj₂ _  with eq
...   | ()
∈-++ᶜ-split-inj₁ Δ₁ (Δ₂ ∷ B) (Tl-∷ x) z eq
    | inj₁ (ρ'' , z') with eq
...   | refl =
  cong (λ t → proj₁ t , Tl-∷ (proj₂ t)) (∈-++ᶜ-split-inj₁ Δ₁ Δ₂ x z' eq')

∈-++ᶜ-split-inj₁ Δ₁ (Δ₂ ⟨ ρ₁ ⟩) (Tl-⟨⟩ x) z eq
  with ∈-++ᶜ-split Δ₁ Δ₂ x in eq'
... | inj₂ _  with eq
...   | ()
∈-++ᶜ-split-inj₁ Δ₁ (Δ₂ ⟨ ρ₁ ⟩) (Tl-⟨⟩ x) z eq
    | inj₁ (ρ'' , z') with eq
...   | refl =
  cong (λ t → proj₁ t ·ᵣ ρ₁ , Tl-⟨⟩ (proj₂ t))
       (∈-++ᶜ-split-inj₁ Δ₁ Δ₂ x z' eq')
-- SUBSTITUTION FIXES A PREFIX VARIABLE
--
-- The mirror of `sub-var-r`: the variable being replaced is the `B` sitting at
-- the boundary, so a variable of the prefix survives it too, landing at the
-- corresponding position of the shorter prefix. Same induction on the suffix.

sub-var-l : ∀ {Γ₁ B} → (Γ₂ : Ctx) → ∀ {A ρ}
          → (x : A ∈[ ρ ] Γ₁)
          → (W : split-l (split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})) ⊢V⦂ B)
          → (f  : ¬ Eternal A → grade-++ᶜˡ ρ Γ₂ ≾ᵣ uᵣ)
          → (f' : ¬ Eternal A → grade-++ᶜˡ ρ Γ₂ ≾ᵣ uᵣ)
          → castᵛ (castOf {Γ₁} {B} Γ₂)
              (⟨ ∈-++ᶜˡ {Γ = Γ₁ ∷ B} Γ₂ (Tl-∷ x) , f
               ⟩[ split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}) ↦ W ]var)
          ≐ᵛ var f' (∈-++ᶜˡ {Γ = Γ₁} Γ₂ x)

sub-var-l {Γ₁} {B} [] x W f f' =
  ≐ᵛ-trans
    (≡→≐ᵛ (trans (castᵛ-var (castOf {Γ₁} {B} []) f x)
                 (cong (var f) (subst-var-id (castOf {Γ₁} {B} []) x))))
    var-≐

sub-var-l {Γ₁} {B} (Γ₂ ∷ C) x W f f' =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-wk-any (castOf {Γ₁} {B} (Γ₂ ∷ C)) (castOf {Γ₁} {B} Γ₂) _))
    (≐ᵛ-trans (V-rename-cong wk-ren (sub-var-l Γ₂ x W f f))
              (var-ren-img-≐ wk-ren (∈-++ᶜˡ {Γ = Γ₁} Γ₂ x) f refl f'))

sub-var-l {Γ₁} {B} (Γ₂ ⟨ ρ' ⟩) {A = A} x W f f' with eternal? A

... | yes et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-ext-any (castOf {Γ₁} {B} (Γ₂ ⟨ ρ' ⟩)) (castOf {Γ₁} {B} Γ₂) et _))
    (≐ᵛ-trans (eternal-val-ext-cong et
                (sub-var-l Γ₂ x W _ (λ z → ⊥-elim (z et)))) var-≐)

... | no ¬et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-ren-⟨⟩-any (castOf {Γ₁} {B} (Γ₂ ⟨ ρ' ⟩))
                           (castOf {Γ₁} {B} Γ₂) rn _))
    (≐ᵛ-trans (V-rename-cong rn (sub-var-l Γ₂ x W fᵢ fᵢ))
              (var-ren-img-≐ rn (∈-++ᶜˡ {Γ = Γ₁} Γ₂ x) fᵢ
                 (cong (var-img′ (⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et))))
                       (⟨⟩-η⁻¹-img (∈-++ᶜˡ {Γ = Γ₁} Γ₂ x)))
                 f'))
  where
    rn : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ' ⟩)
    rn = ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et)) ∘ʳ ⟨⟩-η⁻¹-ren

    fᵢ = λ z → ≾ᵣ-zero-productˡ (f z)

-- SUBSTITUTION AT THE VARIABLE IT REPLACES
--
-- The third possibility: the variable looked up *is* the one being replaced, so
-- what comes back is the value, pushed under the suffix. The recursion of
-- `⟨_,_⟩[_↦_]var` builds that push one layer at a time — `wk-ren` per binder and
-- `⟨⟩-≤-ren ∘ʳ ⟨⟩-η⁻¹-ren` per lock — which is exactly `push-ren`, up to the
-- grade bounds `_≐ʳ_` does not see. Non-eternality is what selects that branch
-- at a lock; at an eternal type the substitution extends the value instead.

sub-var-hit : ∀ {Γ₁ B} → (Γ₂ : Ctx) → ¬ Eternal B
            → (p : ctx-grade Γ₂ ≾ᵣ uᵣ)
            → (W : split-l (split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})) ⊢V⦂ B)
            → (f : ¬ Eternal B → ctx-grade Γ₂ ≾ᵣ uᵣ)
            → castᵛ (castOf {Γ₁} {B} Γ₂)
                (⟨ split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}) , f
                 ⟩[ split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}) ↦ W ]var)
            ≐ᵛ V-rename (push-ren Γ₂ p)
                 (castᵛ (split→∈-split-l (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})) W)

sub-var-hit {Γ₁} {B} [] ¬et p W f =
  ≐ᵛ-sym (V-rename-id-≐ ≐ʳ-refl _)

sub-var-hit {Γ₁} {B} (Γ₂ ∷ C) ¬et p W f =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-wk-any (castOf {Γ₁} {B} (Γ₂ ∷ C)) (castOf {Γ₁} {B} Γ₂) _))
    (≐ᵛ-trans (V-rename-cong wk-ren (sub-var-hit Γ₂ ¬et p W f))
              (≐ᵛ-sym (V-rename-∘ wk-ren (push-ren Γ₂ p) _)))

sub-var-hit {Γ₁} {B} (Γ₂ ⟨ ρ ⟩) ¬et p W f with eternal? B

... | yes et = ⊥-elim (¬et et)

... | no ¬p =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-ren-⟨⟩-any (castOf {Γ₁} {B} (Γ₂ ⟨ ρ ⟩))
                           (castOf {Γ₁} {B} Γ₂) rn _))
    (≐ᵛ-trans (V-rename-cong rn (sub-var-hit Γ₂ ¬et pᵢ W fᵢ))
      (≐ᵛ-trans (≐ᵛ-sym (V-rename-∘ rn (push-ren Γ₂ pᵢ) _))
                (V-rename-≐ (∘ʳ-≐ (∘ʳ-≐ (⟨⟩-≤-ren-≐ _ _) ≐ʳ-refl) ≐ʳ-refl) _)))
  where
    rn : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩)
    rn = ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬p)) ∘ʳ ⟨⟩-η⁻¹-ren

    pᵢ = ≾ᵣ-zero-productˡ p
    fᵢ = λ z → ≾ᵣ-zero-productˡ (f z)

-- The same, taking the looked-up variable as an equation: what reaches the
-- substitution is `∈-++ᶜˡ Γ₂ Hd`, which is `split→∈` of the splitting only up
-- to `split→∈-∈-++ᶜˡ`.

sub-var-hit′ : ∀ {Γ₁ B σ} → (Γ₂ : Ctx) → ¬ Eternal B
             → (p : ctx-grade Γ₂ ≾ᵣ uᵣ)
             → (y : B ∈[ σ ] ((Γ₁ ∷ B) ++ᶜ Γ₂))
             → _≡_ {A = Var ((Γ₁ ∷ B) ++ᶜ Γ₂) B}
                 (σ , y)
                 (ctx-grade Γ₂ , split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}))
             → (W : split-l (split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})) ⊢V⦂ B)
             → (f : ¬ Eternal B → σ ≾ᵣ uᵣ)
             → castᵛ (castOf {Γ₁} {B} Γ₂)
                 (⟨ y , f ⟩[ split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}) ↦ W ]var)
             ≐ᵛ V-rename (push-ren Γ₂ p)
                  (castᵛ (split→∈-split-l (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})) W)
sub-var-hit′ Γ₂ ¬et p _ refl W f = sub-var-hit Γ₂ ¬et p W f

-- THE CELL `unbox-var` NAMES (what `sub-wk-unbox` needs)
--
-- `unbox-var z rel M` rebuilds an unboxing whose boxed value is the head
-- variable of `split-l z ∷ [ ρ ] A`, so the resource variable it names is `z` itself — the
-- syntactic counterpart of `split-lookup` in
-- `Interpretation.SubstitutionCoherence`. Its renaming is
-- `eq-ren (split-≡ (split-pf z)) ∘ʳ wk-ren-⟨ρ⟩-ctx (split-grade-≡ z) ∘ʳ ⟨⟩-≤-ren rel`,
-- so computing its `var-img` at `Tl-⟨⟩ Hd` needs, in order: `⟨⟩-≤-ren`'s clause,
-- `wk-ren-⟨ρ⟩-ctx-img` (in `GradedReach`, proved), and `eq-ren-img` below. What is left
-- is
--
--   split-lookup-img : (z : [ ρ ] A ∈[ ρ' ] Γ)
--                    → (grade-++ᶜˡ uᵣ (split-r z)
--                      , subst _ (split-≡ (split-pf z))
--                              (∈-++ᶜˡ (split-r z) (Hd {Γ = split-l z})))
--                    ≡ (ρ' , z)
--
-- by induction on `z` — `Hd` is `refl`, and the two `Tl` cases are `subst-Tl-∷`
-- resp. `subst-Tl-⟨⟩` under a `cong`. **State it with `∈-++ᶜˡ`, not
-- `var-ρ-++ᶜ`**: the latter carries a grade `subst` in each of its `[]` and
-- `⟨⟩` clauses, which turns all three cases into `Var`-level transport puzzles,
-- whereas `grade-++ᶜˡ`/`∈-++ᶜˡ` are subst-free by construction. That means
-- restating `wk-ren-⟨ρ⟩-ctx-img` over `∈-++ᶜˡ` too, and so moving
-- `grade-++ᶜˡ`/`∈-++ᶜˡ` into `Syntax.Renamings.Equivalence` beside the other
-- variable-relocation lemmas.

-- SUBSTITUTION FIXES A RESOURCE VARIABLE
--
-- The `rvar` counterparts of `sub-var-r`/`sub-var-l`: `⟨_⟩[_↦_]rvar` returns the
-- same resource variable when the variable it replaces is a different one. Simpler than the
-- value versions — a box type is never eternal, so there is no `eternal?` split.

sub-rvar-r : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ σ}
           → (z : [ ρ ] A ∈[ σ ] Θ)
           → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
           → Var-cast (castOf {Γ} {B} Θ)
               (rvar-img (∈-++ᶜʳ {Γ = Γ ∷ B} z)
                         (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) W)
           ≡ (σ , ∈-++ᶜʳ {Γ = Γ} z)

sub-rvar-r {Γ} {B} (Θ ∷ C) Hd W = Var-cast-Hd (castOf {Γ} {B} (Θ ∷ C))

sub-rvar-r {Γ} {B} (Θ ∷ C) (Tl-∷ z) W =
  trans (Var-cast-irr (castOf {Γ} {B} (Θ ∷ C))
                      (cong (_∷ C) (castOf {Γ} {B} Θ)) _)
    (trans (Var-cast-∷ (castOf {Γ} {B} Θ) _)
           (cong Var-∷ (sub-rvar-r Θ z W)))

sub-rvar-r {Γ} {B} (Θ ⟨ ρ' ⟩) (Tl-⟨⟩ z) W =
  trans (Var-cast-irr (castOf {Γ} {B} (Θ ⟨ ρ' ⟩))
                      (cong (_⟨ ρ' ⟩) (castOf {Γ} {B} Θ)) _)
    (trans (Var-cast-⟨⟩ ρ' (castOf {Γ} {B} Θ) _)
           (cong (Var-⟨⟩ ρ') (sub-rvar-r Θ z W)))

sub-rvar-l : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ σ}
           → (z : [ ρ ] A ∈[ σ ] Γ)
           → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
           → Var-cast (castOf {Γ} {B} Θ)
               (rvar-img (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Tl-∷ z))
                         (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) W)
           ≡ (grade-++ᶜˡ σ Θ , ∈-++ᶜˡ {Γ = Γ} Θ z)

sub-rvar-l {Γ} {B} [] z W = refl

sub-rvar-l {Γ} {B} (Θ ∷ C) z W =
  trans (Var-cast-irr (castOf {Γ} {B} (Θ ∷ C))
                      (cong (_∷ C) (castOf {Γ} {B} Θ)) _)
    (trans (Var-cast-∷ (castOf {Γ} {B} Θ) _)
           (cong Var-∷ (sub-rvar-l Θ z W)))

sub-rvar-l {Γ} {B} (Θ ⟨ ρ' ⟩) z W =
  trans (Var-cast-irr (castOf {Γ} {B} (Θ ⟨ ρ' ⟩))
                      (cong (_⟨ ρ' ⟩) (castOf {Γ} {B} Θ)) _)
    (trans (Var-cast-⟨⟩ ρ' (castOf {Γ} {B} Θ) _)
           (cong (Var-⟨⟩ ρ') (sub-rvar-l Θ z W)))

-- The same, taking the resource variable's location as an equation rather than reading it off
-- with `proj₂` — which is dependent, so `cong proj₂` is not available.

sub-rvar-r′ : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ σ} → (z : [ ρ ] A ∈[ σ ] Θ)
            → (t : Var ((Γ ∷ B) ++ᶜ Θ) ([ ρ ] A))
            → t ≡ (σ , ∈-++ᶜʳ {Γ = Γ ∷ B} z)
            → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
            → Var-cast (castOf {Γ} {B} Θ)
                (rvar-img (proj₂ t) (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) W)
            ≡ (σ , ∈-++ᶜʳ {Γ = Γ} z)
sub-rvar-r′ Θ z t refl W = sub-rvar-r Θ z W

sub-rvar-l′ : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ σ} → (z : [ ρ ] A ∈[ σ ] Γ)
            → (t : Var ((Γ ∷ B) ++ᶜ Θ) ([ ρ ] A))
            → t ≡ (grade-++ᶜˡ σ Θ , ∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Tl-∷ z))
            → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
            → Var-cast (castOf {Γ} {B} Θ)
                (rvar-img (proj₂ t) (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) W)
            ≡ (grade-++ᶜˡ σ Θ , ∈-++ᶜˡ {Γ = Γ} Θ z)
sub-rvar-l′ Θ z t refl W = sub-rvar-l Θ z W

-- The resource variable a weakened-then-substituted `unbox` names is the original one: the
-- renaming pushes it (`cong-ren-img-r`/`-l`, by which side `∈-++ᶜ-split` says it
-- came from) and the substitution puts it back (`sub-rvar-r`/`-l`).

unbox-rvar-wk : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ σ}
              → (c : [ ρ ] A ∈[ σ ] (Γ ++ᶜ Θ))
              → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
              → Var-cast (castOf {Γ} {B} Θ)
                  (rvar-img
                     (proj₂ (var-img (cong-ren {Γ'' = Θ} (wk-ren {A = B})) c))
                     (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) W)
              ≡ (σ , c)

unbox-rvar-wk {Γ} {B} Θ c W with ∈-++ᶜ-split Γ Θ c in eqc

... | inj₂ c'
  rewrite ∈-++ᶜ-split-inj₂ Γ Θ c c' eqc =
  sub-rvar-r′ Θ c' _ (cong-ren-img-r (wk-ren {A = B}) c') W

... | inj₁ (σ' , c') =
  subst (λ t → Var-cast (castOf {Γ} {B} Θ)
                 (rvar-img (proj₂ (var-img (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                                           (proj₂ t)))
                           (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) W)
             ≡ t)
        (sym (∈-++ᶜ-split-inj₁ Γ Θ c c' eqc))
        (sub-rvar-l′ Θ c' _ (cong-ren-img-l (wk-ren {A = B}) Θ c') W)

