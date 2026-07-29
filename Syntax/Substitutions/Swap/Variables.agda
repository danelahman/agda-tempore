------------------------------------------------------------------------
-- The swap on a variable, and on the cell an `unbox` names.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality
module Syntax.Substitutions.Swap.Variables (Spec : LanguageSpec) where
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
open import Syntax.Substitutions.Renaming    Spec
open import Syntax.Substitutions.Swap.Base Spec

-- THE STATEMENT
------------------------------------------------------------------------

SubSwapV : ∀ {Γ B₁ B₂ A} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A
         → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → Set
SubSwapV Θ U W₂ W₁ = outerᵛ Θ U W₂ W₁ ≐ᵛ innerᵛ Θ U W₂ W₁

SubSwapC : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
         → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → Set
SubSwapC Θ M W₂ W₁ = outerᶜ Θ M W₂ W₁ ≐ᶜ innerᶜ Θ M W₂ W₁

------------------------------------------------------------------------
-- THE SWAP
--
-- Mutual induction on the term at an arbitrary suffix, as `sub-wk` and
-- `ren-sub`. Each structural case is: unfold both orders by their former
-- laws, apply the congruence to the induction hypotheses at the grown
-- suffix, fold back.
------------------------------------------------------------------------

-- The action respects the equivalence: each zone is a substitution, and
-- substitution is a congruence.

-- Reading a transport equation in the other direction.

subst-flip : ∀ {a p} {X : Set a} {P : X → Set p} {u v : X}
           → (e : u ≡ v) → (m : P u) → (n : P v)
           → subst P e m ≡ n → subst P (sym e) n ≡ m
subst-flip refl m n q = sym q

sub-atᵛ-≐ : ∀ {Γ' B A} → (Θ : Ctx) → {U U' : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A}
          → (W : Γ' ⊢V⦂ B) → U ≐ᵛ U' → sub-atᵛ Θ U W ≐ᵛ sub-atᵛ Θ U' W
sub-atᵛ-≐ Θ W e = castᵛ-≐ _ (sub-≐ᵛ _ (≐ᵛ-refl _) e)

sub-atᶜ-≐ : ∀ {Γ' B C} → (Θ : Ctx) → {M M' : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C}
          → (W : Γ' ⊢V⦂ B) → M ≐ᶜ M' → sub-atᶜ Θ M W ≐ᶜ sub-atᶜ Θ M' W
sub-atᶜ-≐ Θ W e = castᶜ-≐ _ (sub-≐ᶜ _ (≐ᵛ-refl _) e)

------------------------------------------------------------------------
-- THE VARIABLE CASE
--
-- Four positions: in the suffix, the outer entry `B₂`, the inner entry
-- `B₁`, and the prefix `Γ`. The two entries are the content; both are
-- kept in their *unreduced* hit form, as `ren-sub-hit` does, so no
-- normal form for "the value pushed under the suffix" is needed — and
-- with it none of the eternal/non-eternal case analysis at a lock, which
-- `ren-sub-hit` has already absorbed.
------------------------------------------------------------------------

-- Looking up the replaced entry itself.

hitᵛ : ∀ {Γ' B} → (Θ : Ctx) → Γ' ⊢V⦂ B
     → (f : ¬ Eternal B → ctx-grade Θ ≾ᵣ uᵣ) → (Γ' ++ᶜ Θ) ⊢V⦂ B
hitᵛ {Γ'} {B} Θ W f = sub-atᵛ Θ (var f (bvar B Θ)) W

-- The hit at a concatenated suffix is the hit at the outer part, of the
-- value weakened by the inner one. Induction on the outer part, layer by
-- layer, exactly as `ren-sub-hit`; the lock case splits on eternality,
-- since an eternal value crosses a lock by extension rather than by a
-- renaming.

-- Any proof of the context equation will do; the induction never has to
-- reconcile the one it receives with the one it passes down.

Ehit : ∀ {Γ'} → (B B₀ : VType) → (Θ : Ctx)
     → (split-l (bvar {Γ'} B (([] ∷ B₀) ++ᶜ Θ))
          ++ᶜ split-r (bvar {Γ'} B (([] ∷ B₀) ++ᶜ Θ)))
     ≡ ((Γ' ∷ B₀) ++ᶜ Θ)
Ehit {Γ'} B B₀ Θ =
  trans (castOf {Γ'} {B} (([] ∷ B₀) ++ᶜ Θ)) (sym (++ᶜ-assoc Γ' ([] ∷ B₀) Θ))

hit-∷-++ᶜ : ∀ {Γ' B B₀} → (Θ : Ctx) → (W : Γ' ⊢V⦂ B)
          → (g  : ¬ Eternal B → ctx-grade (([] ∷ B₀) ++ᶜ Θ) ≾ᵣ uᵣ)
          → (g' : ¬ Eternal B → ctx-grade Θ ≾ᵣ uᵣ)
          → (E : (split-l (bvar {Γ'} B (([] ∷ B₀) ++ᶜ Θ))
                    ++ᶜ split-r (bvar {Γ'} B (([] ∷ B₀) ++ᶜ Θ)))
               ≡ ((Γ' ∷ B₀) ++ᶜ Θ))
          → castᵛ E (⟨ bvar B (([] ∷ B₀) ++ᶜ Θ) , g
                     ⟩[ bvar B (([] ∷ B₀) ++ᶜ Θ)
                        ↦ bval (([] ∷ B₀) ++ᶜ Θ) W ]var)
          ≐ᵛ hitᵛ {Γ' ∷ B₀} Θ (V-rename (wk-ren {A = B₀}) W) g'

hit-∷-++ᶜ {Γ'} {B} {B₀} [] W g g' E = ≡→≐ᵛ (castᵛ-irr E refl _)

hit-∷-++ᶜ {Γ'} {B} {B₀} (Θ ∷ C) W g g' E =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-wk-any E (Ehit B B₀ Θ)
             (⟨ bvar B (([] ∷ B₀) ++ᶜ Θ) , g
              ⟩[ bvar B (([] ∷ B₀) ++ᶜ Θ)
                 ↦ bval (([] ∷ B₀) ++ᶜ Θ) W ]var)))
    (≐ᵛ-trans
      (V-rename-cong wk-ren (hit-∷-++ᶜ Θ W g g' (Ehit B B₀ Θ)))
      (≡→≐ᵛ (sym (cast-wk-any (castOf {Γ' ∷ B₀} {B} (Θ ∷ C))
                              (castOf {Γ' ∷ B₀} {B} Θ) _))))

hit-∷-++ᶜ {Γ'} {B} {B₀} (Θ ⟨ ρ ⟩) W g g' E with eternal? B

... | yes et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-ext-any E (Ehit B B₀ Θ) et
             (⟨ bvar B (([] ∷ B₀) ++ᶜ Θ) , _
              ⟩[ bvar B (([] ∷ B₀) ++ᶜ Θ)
                 ↦ bval (([] ∷ B₀) ++ᶜ Θ) W ]var)))
    (≐ᵛ-trans
      (eternal-val-ext-cong et (hit-∷-++ᶜ Θ W _ _ (Ehit B B₀ Θ)))
      (≡→≐ᵛ (sym (cast-ext-any (castOf {Γ' ∷ B₀} {B} (Θ ⟨ ρ ⟩))
                               (castOf {Γ' ∷ B₀} {B} Θ) et _))))

... | no ¬et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-ren-⟨⟩-any E (Ehit B B₀ Θ) rn
             (⟨ bvar B (([] ∷ B₀) ++ᶜ Θ) , _
              ⟩[ bvar B (([] ∷ B₀) ++ᶜ Θ)
                 ↦ bval (([] ∷ B₀) ++ᶜ Θ) W ]var)))
    (≐ᵛ-trans (V-rename-cong rn (hit-∷-++ᶜ Θ W _ _ (Ehit B B₀ Θ)))
      (≐ᵛ-trans (V-rename-≐ (∘ʳ-≐ (⟨⟩-≤-ren-≐ _ _) ≐ʳ-refl) _)
                (≡→≐ᵛ (sym (cast-ren-⟨⟩-any (castOf {Γ' ∷ B₀} {B} (Θ ⟨ ρ ⟩))
                                            (castOf {Γ' ∷ B₀} {B} Θ) rn' _)))))
  where
    rn : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩)
    rn = ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (g ¬et)) ∘ʳ ⟨⟩-η⁻¹-ren

    rn' : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩)
    rn' = ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (g' ¬et)) ∘ʳ ⟨⟩-η⁻¹-ren

-- Grade bounds are proof-irrelevant, so the substitution does not see
-- which one it was handed.

bound-irr : ∀ {A ρ} → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ) → f ≡ f'
bound-irr f f' = fun-ext (λ z → ≾ᵣ-irrelevant _ _)

castᵛ-fuse : ∀ {Γ₁ Γ₂ Γ₃ A} → (e : Γ₁ ≡ Γ₂) → (e' : Γ₂ ≡ Γ₃) → (V : Γ₁ ⊢V⦂ A)
           → castᵛ e' (castᵛ e V) ≡ castᵛ (trans e e') V
castᵛ-fuse refl refl V = refl

Tgt-cast-fuse : ∀ {Γ₁ Γ₂ Γ₃ A} → (e : Γ₁ ≡ Γ₂) → (e' : Γ₂ ≡ Γ₃) → (t : Tgt Γ₁ A)
              → Tgt-cast e' (Tgt-cast e t) ≡ Tgt-cast (trans e e') t
Tgt-cast-fuse refl refl t = refl

-- Relocating a variable along a context transport, at the `Tgt` level so
-- that the grade travels with the position.

castᵛ-var-tgt : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ') → (x : A ∈[ ρ ] Γ)
              → (t : Tgt Γ' A) → Tgt-cast e (ρ , x) ≡ t
              → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
              → (f' : ¬ Eternal A → proj₁ t ≾ᵣ uᵣ)
              → castᵛ e (var f x) ≐ᵛ var f' (proj₂ t)
castᵛ-var-tgt refl x .(_ , x) refl f f' = var-≐

-- The three positions the substitution distinguishes, each taking where
-- the variable sits as a `Tgt` equation.

sub-at-varᵣ : ∀ {Γ' B A ρ} → (Θ : Ctx) → (x : A ∈[ ρ ] Θ)
            → (y : A ∈[ ρ ] ((Γ' ∷ B) ++ᶜ Θ)) → y ≡ ∈-++ᶜʳ {Γ = Γ' ∷ B} x
            → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → (f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
            → (W : Γ' ⊢V⦂ B)
            → sub-atᵛ Θ (var f y) W ≐ᵛ var f' (∈-++ᶜʳ {Γ = Γ'} x)
sub-at-varᵣ Θ x _ refl f f' W = sub-var-r Θ x (bval Θ W) f f'

sub-at-varₗ : ∀ {Γ' B A ρ} → (Θ : Ctx) → (x : A ∈[ ρ ] Γ')
            → (y : A ∈[ grade-++ᶜˡ ρ Θ ] ((Γ' ∷ B) ++ᶜ Θ))
            → y ≡ ∈-++ᶜˡ {Γ = Γ' ∷ B} Θ (Tl-∷ x)
            → (f f' : ¬ Eternal A → grade-++ᶜˡ ρ Θ ≾ᵣ uᵣ) → (W : Γ' ⊢V⦂ B)
            → sub-atᵛ Θ (var f y) W ≐ᵛ var f' (∈-++ᶜˡ {Γ = Γ'} Θ x)
sub-at-varₗ Θ x _ refl f f' W = sub-var-l Θ x (bval Θ W) f f'

sub-at-varₕ : ∀ {Γ' B ρ} → (Θ : Ctx) → (y : B ∈[ ρ ] ((Γ' ∷ B) ++ᶜ Θ))
            → _≡_ {A = Tgt ((Γ' ∷ B) ++ᶜ Θ) B}
                  (ρ , y) (ctx-grade Θ , bvar B Θ)
            → (f : ¬ Eternal B → ρ ≾ᵣ uᵣ)
            → (f' : ¬ Eternal B → ctx-grade Θ ≾ᵣ uᵣ) → (W : Γ' ⊢V⦂ B)
            → sub-atᵛ Θ (var f y) W ≐ᵛ hitᵛ Θ W f'
sub-at-varₕ Θ .(bvar _ Θ) refl f f' W
  rewrite bound-irr f f' = ≐ᵛ-refl _

------------------------------------------------------------------------
-- The four positions.
------------------------------------------------------------------------

swap-var-r : ∀ {Γ B₁ B₂ A ρ} → (Θ : Ctx) → (x : A ∈[ ρ ] Θ)
           → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
           → SubSwapV Θ (var f (∈-++ᶜʳ {Γ = Γ ∷ B₁ ∷ B₂} x)) W₂ W₁
swap-var-r {Γ} {B₁} {B₂} Θ x f W₂ W₁ =
  ≐ᵛ-trans
    (≐ᵛ-trans (sub-atᵛ-≐ Θ W₁ (sub-at-varᵣ Θ x _ refl f f _))
              (sub-at-varᵣ Θ x _ refl f f W₁))
    (≐ᵛ-sym
      (≐ᵛ-trans
        (sub-atᵛ-≐ Θ W₂
          (≐ᵛ-trans
            (castᵛ-≐ (assocᴮ⁻ Γ B₂ Θ)
              (≐ᵛ-trans
                (sub-atᵛ-≐ (([] ∷ B₂) ++ᶜ Θ) W₁
                   (castᵛ-var-tgt (assocᴮ Γ B₁ B₂ Θ) _ _
                      (cong (λ z → _ , z) (∈-++ᶜʳ-assoc (Γ ∷ B₁) ([] ∷ B₂) x))
                      f f))
                (sub-at-varᵣ (([] ∷ B₂) ++ᶜ Θ) (∈-++ᶜʳ {Γ = [] ∷ B₂} x) _
                             refl f f W₁)))
            (castᵛ-var-tgt (assocᴮ⁻ Γ B₂ Θ) _ _
               (cong (λ z → _ , z)
                 (subst-flip (++ᶜ-assoc Γ ([] ∷ B₂) Θ) _ _
                             (∈-++ᶜʳ-assoc Γ ([] ∷ B₂) x)))
               f f)))
        (sub-at-varᵣ Θ x _ refl f f W₂)))

swap-var-l : ∀ {Γ B₁ B₂ A ρ} → (Θ : Ctx) → (v : A ∈[ ρ ] Γ)
           → (f : ¬ Eternal A → grade-++ᶜˡ ρ Θ ≾ᵣ uᵣ)
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
           → SubSwapV Θ (var f (∈-++ᶜˡ {Γ = Γ ∷ B₁ ∷ B₂} Θ (Tl-∷ (Tl-∷ v))))
                        W₂ W₁
swap-var-l {Γ} {B₁} {B₂} Θ v f W₂ W₁ =
  ≐ᵛ-trans
    (≐ᵛ-trans (sub-atᵛ-≐ Θ W₁ (sub-at-varₗ Θ (Tl-∷ v) _ refl f f _))
              (sub-at-varₗ Θ v _ refl f f W₁))
    (≐ᵛ-sym
      (≐ᵛ-trans
        (sub-atᵛ-≐ Θ W₂
          (≐ᵛ-trans
            (castᵛ-≐ (assocᴮ⁻ Γ B₂ Θ)
              (≐ᵛ-trans
                (sub-atᵛ-≐ (([] ∷ B₂) ++ᶜ Θ) W₁
                   (castᵛ-var-tgt (assocᴮ Γ B₁ B₂ Θ) _ _
                      (Tgt-cast-flip⁻ (++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ) _ _
                         (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ (Tl-∷ v)))
                      f fΔ))
                (sub-at-varₗ (([] ∷ B₂) ++ᶜ Θ) v _ refl fΔ fΔ W₁)))
            (castᵛ-var-tgt (assocᴮ⁻ Γ B₂ Θ) _ _
               (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ v) fΔ f)))
        (sub-at-varₗ Θ v _ refl f f W₂)))
  where
    fΔ : ¬ Eternal _ → grade-++ᶜˡ _ (([] ∷ B₂) ++ᶜ Θ) ≾ᵣ uᵣ
    fΔ ¬et = subst (_≾ᵣ uᵣ) (sym (grade-++ᶜˡ-assoc _ ([] ∷ B₂) Θ)) (f ¬et)

swap-var-B₂ : ∀ {Γ B₁ B₂ ρ} → (Θ : Ctx)
            → (f : ¬ Eternal B₂ → ρ ≾ᵣ uᵣ)
            → (y : B₂ ∈[ ρ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
            → _≡_ {A = Tgt ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) B₂}
                  (ρ , y) (grade-++ᶜˡ uᵣ Θ , ∈-++ᶜˡ Θ (Hd {Γ = Γ ∷ B₁}))
            → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
            → SubSwapV Θ (var f y) W₂ W₁
swap-var-B₂ {Γ} {B₁} {B₂} Θ f .(∈-++ᶜˡ Θ Hd) refl W₂ W₁ =
  ≐ᵛ-trans
    (≐ᵛ-trans
      (sub-atᵛ-≐ Θ W₁
        (sub-at-varₕ Θ _ (sym (split→∈-∈-++ᶜˡ (Γ ∷ B₁) B₂ Θ)) f fΘ _))
      (≐ᵛ-trans
        (sub-atᵛ-≐ Θ W₁
          (≐ᵛ-sym (ren-sub-hit (wk-ren {A = B₁}) Θ W₂ fΘ fΘ)))
        (sub-wk-V Θ (hitᵛ Θ W₂ fΘ) (bval Θ W₁))))
    (≐ᵛ-sym
      (≐ᵛ-trans
        (sub-atᵛ-≐ Θ W₂
          (≐ᵛ-trans
            (castᵛ-≐ (assocᴮ⁻ Γ B₂ Θ)
              (≐ᵛ-trans
                (sub-atᵛ-≐ (([] ∷ B₂) ++ᶜ Θ) W₁
                   (castᵛ-var-tgt (assocᴮ Γ B₁ B₂ Θ) _ _
                      (∈-++ᶜˡ-++ᶜʳ (Γ ∷ B₁) ([] ∷ B₂) Θ (Hd {Γ = []}))
                      f f))
                (sub-at-varᵣ (([] ∷ B₂) ++ᶜ Θ)
                             (∈-++ᶜˡ {Γ = [] ∷ B₂} Θ (Hd {Γ = []})) _
                             refl f f W₁)))
            (castᵛ-var-tgt (assocᴮ⁻ Γ B₂ Θ) _ _
               (Tgt-cast-flip (++ᶜ-assoc Γ ([] ∷ B₂) Θ) _ _
                  (∈-++ᶜˡ-++ᶜʳ Γ ([] ∷ B₂) Θ (Hd {Γ = []})))
               f f)))
        (sub-at-varₕ Θ _ (sym (split→∈-∈-++ᶜˡ Γ B₂ Θ)) f fΘ W₂)))
  where
    fΘ : ¬ Eternal B₂ → ctx-grade Θ ≾ᵣ uᵣ
    fΘ ¬et = subst (_≾ᵣ uᵣ) (grade-++ᶜˡ-uᵣ Θ) (f ¬et)

swap-var-B₁ : ∀ {Γ B₁ B₂ ρ} → (Θ : Ctx)
            → (f : ¬ Eternal B₁ → ρ ≾ᵣ uᵣ)
            → (y : B₁ ∈[ ρ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
            → _≡_ {A = Tgt ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) B₁}
                  (ρ , y) (grade-++ᶜˡ uᵣ Θ , ∈-++ᶜˡ Θ (Tl-∷ (Hd {Γ = Γ})))
            → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
            → SubSwapV Θ (var f y) W₂ W₁
swap-var-B₁ {Γ} {B₁} {B₂} Θ f .(∈-++ᶜˡ Θ (Tl-∷ Hd)) refl W₂ W₁ =
  ≐ᵛ-trans
    (≐ᵛ-trans (sub-atᵛ-≐ Θ W₁ (sub-at-varₗ Θ (Hd {Γ = Γ}) _ refl f f _))
              (sub-at-varₕ Θ _ (sym (split→∈-∈-++ᶜˡ Γ B₁ Θ)) f fΘ W₁))
    (≐ᵛ-sym
      (≐ᵛ-trans
        (sub-atᵛ-≐ Θ W₂
          (≐ᵛ-trans
            (castᵛ-≐ (assocᴮ⁻ Γ B₂ Θ)
              (≐ᵛ-trans
                (sub-atᵛ-≐ (([] ∷ B₂) ++ᶜ Θ) W₁
                   (castᵛ-var-tgt (assocᴮ Γ B₁ B₂ Θ) _ _
                      (Tgt-cast-flip⁻ (++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ) _ _
                         (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ (Hd {Γ = Γ})))
                      f fΔ))
                (sub-at-varₕ (([] ∷ B₂) ++ᶜ Θ) _
                   (sym (split→∈-∈-++ᶜˡ Γ B₁ (([] ∷ B₂) ++ᶜ Θ))) fΔ g W₁)))
            (≐ᵛ-trans
              (≡→≐ᵛ (castᵛ-fuse (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))
                                (assocᴮ⁻ Γ B₂ Θ) _))
              (hit-∷-++ᶜ Θ W₁ g fΘ (Ehit B₁ B₂ Θ)))))
        (≐ᵛ-trans
          (sub-atᵛ-≐ Θ W₂ (≐ᵛ-sym (ren-sub-hit (wk-ren {A = B₂}) Θ W₁ fΘ fΘ)))
          (sub-wk-V Θ (hitᵛ Θ W₁ fΘ) (bval Θ W₂)))))
  where
    fΘ : ¬ Eternal B₁ → ctx-grade Θ ≾ᵣ uᵣ
    fΘ ¬et = subst (_≾ᵣ uᵣ) (grade-++ᶜˡ-uᵣ Θ) (f ¬et)

    fΔ : ¬ Eternal B₁ → grade-++ᶜˡ uᵣ (([] ∷ B₂) ++ᶜ Θ) ≾ᵣ uᵣ
    fΔ ¬et = subst (_≾ᵣ uᵣ) (sym (grade-++ᶜˡ-assoc uᵣ ([] ∷ B₂) Θ)) (f ¬et)

    g : ¬ Eternal B₁ → ctx-grade (([] ∷ B₂) ++ᶜ Θ) ≾ᵣ uᵣ
    g ¬et = subst (_≾ᵣ uᵣ) (grade-++ᶜˡ-uᵣ (([] ∷ B₂) ++ᶜ Θ)) (fΔ ¬et)

-- The prefix case, taking the equation in the shape `∈-++ᶜ-split-inj₁`
-- delivers it.

swap-var-l′ : ∀ {Γ B₁ B₂ A ρ ρ'} → (Θ : Ctx) → (v : A ∈[ ρ' ] Γ)
            → (y : A ∈[ ρ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
            → _≡_ {A = Tgt ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) A}
                  (ρ , y) (grade-++ᶜˡ ρ' Θ , ∈-++ᶜˡ Θ (Tl-∷ (Tl-∷ v)))
            → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
            → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
            → SubSwapV Θ (var f y) W₂ W₁
swap-var-l′ Θ v .(∈-++ᶜˡ Θ (Tl-∷ (Tl-∷ v))) refl f W₂ W₁ =
  swap-var-l Θ v f W₂ W₁

swap-var-r′ : ∀ {Γ B₁ B₂ A ρ} → (Θ : Ctx) → (x : A ∈[ ρ ] Θ)
            → (y : A ∈[ ρ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
            → y ≡ ∈-++ᶜʳ {Γ = Γ ∷ B₁ ∷ B₂} x
            → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
            → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
            → SubSwapV Θ (var f y) W₂ W₁
swap-var-r′ Θ x .(∈-++ᶜʳ x) refl f W₂ W₁ = swap-var-r Θ x f W₂ W₁

-- Where the variable sits decides which of the four applies.

sub-swap-var : ∀ {Γ B₁ B₂ A ρ} → (Θ : Ctx)
             → (y : A ∈[ ρ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
             → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
             → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
             → SubSwapV Θ (var f y) W₂ W₁

sub-swap-var {Γ} {B₁} {B₂} Θ y f W₂ W₁
  with ∈-++ᶜ-split (Γ ∷ B₁ ∷ B₂) Θ y in eq

... | inj₂ x =
  swap-var-r′ Θ x y (∈-++ᶜ-split-inj₂ (Γ ∷ B₁ ∷ B₂) Θ y x eq) f W₂ W₁

... | inj₁ (ρ' , Hd) =
  swap-var-B₂ Θ f y (∈-++ᶜ-split-inj₁ (Γ ∷ B₁ ∷ B₂) Θ y Hd eq) W₂ W₁

... | inj₁ (ρ' , Tl-∷ Hd) =
  swap-var-B₁ Θ f y (∈-++ᶜ-split-inj₁ (Γ ∷ B₁ ∷ B₂) Θ y (Tl-∷ Hd) eq) W₂ W₁

... | inj₁ (ρ' , Tl-∷ (Tl-∷ v)) =
  swap-var-l′ Θ v y
    (∈-++ᶜ-split-inj₁ (Γ ∷ B₁ ∷ B₂) Θ y (Tl-∷ (Tl-∷ v)) eq) f W₂ W₁

------------------------------------------------------------------------
-- THE CELL AN `unbox` NAMES
--
-- `sub-unbox` rebuilds an unboxing from the cell the substitution leaves,
-- so the `unbox` case reduces to: the two orders name the same cell. That
-- is the `rvar` counterpart of the variable case, and a simpler one — a
-- box type is never eternal, so `⟨_⟩[_↦_]rvar` has no `eternal?` split
-- and each position is one `Tgt-cast` push.
------------------------------------------------------------------------

-- The cell left by replacing the entry at the boundary.

rcell : ∀ {Γ' B A ρ σ} → (Θ : Ctx)
      → ([ ρ ] A ∈[ σ ] ((Γ' ∷ B) ++ᶜ Θ)) → (W : Γ' ⊢V⦂ B)
      → Tgt (Γ' ++ᶜ Θ) ([ ρ ] A)
rcell {Γ'} {B} Θ c W =
  Tgt-cast (castOf {Γ'} {B} Θ) (rvar-tgt c (bvar B Θ) (bval Θ W))

-- The same at an already-located cell. `Tgt` is a Σ, so `cong` cannot infer
-- the dependent motive from a lambda — this has to be named, exactly as
-- `var-tgt′` is.

rcell′ : ∀ {Γ' B A ρ} → (Θ : Ctx) → Tgt ((Γ' ∷ B) ++ᶜ Θ) ([ ρ ] A)
       → (W : Γ' ⊢V⦂ B) → Tgt (Γ' ++ᶜ Θ) ([ ρ ] A)
rcell′ Θ (σ , c) W = rcell Θ c W

-- and, when the entry replaced *is* the cell, the cell of the value it is
-- replaced by, pushed under the suffix.

hcell : ∀ {Γ' A ρ} → (Θ : Ctx) → (W : Γ' ⊢V⦂ [ ρ ] A) → Tgt (Γ' ++ᶜ Θ) ([ ρ ] A)
hcell {Γ'} {A} {ρ} Θ W = rcell Θ (bvar ([ ρ ] A) Θ) W

-- The cell counterpart of `hit-∷-++ᶜ`, and by the same induction.

rhit-∷-++ᶜ : ∀ {Γ' A ρ B₀} → (Θ : Ctx) → (W : Γ' ⊢V⦂ [ ρ ] A)
           → (E : (split-l (bvar {Γ'} ([ ρ ] A) (([] ∷ B₀) ++ᶜ Θ))
                     ++ᶜ split-r (bvar {Γ'} ([ ρ ] A) (([] ∷ B₀) ++ᶜ Θ)))
                ≡ ((Γ' ∷ B₀) ++ᶜ Θ))
           → Tgt-cast E
               (rvar-tgt (bvar ([ ρ ] A) (([] ∷ B₀) ++ᶜ Θ))
                         (bvar ([ ρ ] A) (([] ∷ B₀) ++ᶜ Θ))
                         (bval (([] ∷ B₀) ++ᶜ Θ) W))
           ≡ hcell {Γ' ∷ B₀} Θ (V-rename (wk-ren {A = B₀}) W)

rhit-∷-++ᶜ {Γ'} {A} {ρ} {B₀} [] (var f y) E =
  Tgt-cast-irr E refl _

rhit-∷-++ᶜ {Γ'} {A} {ρ} {B₀} (Θ ∷ C) W E =
  trans (Tgt-cast-irr E (cong (_∷ C) (Ehit ([ ρ ] A) B₀ Θ)) _)
    (trans (Tgt-cast-∷ (Ehit ([ ρ ] A) B₀ Θ) _)
      (trans (cong Tgt-∷ (rhit-∷-++ᶜ Θ W (Ehit ([ ρ ] A) B₀ Θ)))
        (trans (sym (Tgt-cast-∷ (castOf {Γ' ∷ B₀} {[ ρ ] A} Θ) _))
               (Tgt-cast-irr (cong (_∷ C) (castOf {Γ' ∷ B₀} {[ ρ ] A} Θ))
                             (castOf {Γ' ∷ B₀} {[ ρ ] A} (Θ ∷ C)) _))))

rhit-∷-++ᶜ {Γ'} {A} {ρ} {B₀} (Θ ⟨ ρ' ⟩) W E =
  trans (Tgt-cast-irr E (cong (_⟨ ρ' ⟩) (Ehit ([ ρ ] A) B₀ Θ)) _)
    (trans (Tgt-cast-⟨⟩ ρ' (Ehit ([ ρ ] A) B₀ Θ) _)
      (trans (cong (Tgt-⟨⟩ ρ') (rhit-∷-++ᶜ Θ W (Ehit ([ ρ ] A) B₀ Θ)))
        (trans (sym (Tgt-cast-⟨⟩ ρ' (castOf {Γ' ∷ B₀} {[ ρ ] A} Θ) _))
               (Tgt-cast-irr (cong (_⟨ ρ' ⟩) (castOf {Γ' ∷ B₀} {[ ρ ] A} Θ))
                             (castOf {Γ' ∷ B₀} {[ ρ ] A} (Θ ⟨ ρ' ⟩)) _))))

-- The four positions, at the cell level.

unbox-cell-swap : ∀ {Γ B₁ B₂ A ρ σ} → (Θ : Ctx)
                → (c : [ ρ ] A ∈[ σ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
                → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
                → rcell Θ (proj₂ (rcell Θ c (V-rename (wk-ren {A = B₁}) W₂)))
                          W₁
                ≡ rcell Θ
                    (proj₂ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ)
                             (rcell (([] ∷ B₂) ++ᶜ Θ)
                                (proj₂ (Tgt-cast (assocᴮ Γ B₁ B₂ Θ) (σ , c)))
                                W₁)))
                    W₂

unbox-cell-swap {Γ} {B₁} {B₂} {A} {ρ} {σ} Θ c W₂ W₁
  with ∈-++ᶜ-split (Γ ∷ B₁ ∷ B₂) Θ c in eqc

... | inj₂ c'
  rewrite ∈-++ᶜ-split-inj₂ (Γ ∷ B₁ ∷ B₂) Θ c c' eqc =
  trans (cong (λ t → rcell′ Θ t W₁)
              (sub-rvar-r {Γ = Γ ∷ B₁} {B = B₂} Θ c'
                          (bval Θ (V-rename (wk-ren {A = B₁}) W₂))))
    (trans (sub-rvar-r {Γ = Γ} {B = B₁} Θ c' (bval Θ W₁))
      (sym
        (trans
          (cong (λ t → rcell′ Θ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ) t) W₂)
            (trans
              (cong (λ t → rcell′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                    (cong (λ z → σ , z)
                          (∈-++ᶜʳ-assoc (Γ ∷ B₁) ([] ∷ B₂) c')))
              (sub-rvar-r {Γ = Γ} {B = B₁} (([] ∷ B₂) ++ᶜ Θ)
                          (∈-++ᶜʳ {Γ = [] ∷ B₂} c')
                          (bval (([] ∷ B₂) ++ᶜ Θ) W₁))))
          (trans
            (cong (λ t → rcell′ Θ t W₂)
                  (cong (λ z → σ , z)
                        (subst-flip (++ᶜ-assoc Γ ([] ∷ B₂) Θ) _ _
                                    (∈-++ᶜʳ-assoc Γ ([] ∷ B₂) c'))))
            (sub-rvar-r {Γ = Γ} {B = B₂} Θ c' (bval Θ W₂))))))

... | inj₁ (σ' , c') =
  subst (λ t → rcell Θ (proj₂ (rcell Θ (proj₂ t)
                                (V-rename (wk-ren {A = B₁}) W₂))) W₁
             ≡ rcell Θ
                 (proj₂ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ)
                          (rcell (([] ∷ B₂) ++ᶜ Θ)
                             (proj₂ (Tgt-cast (assocᴮ Γ B₁ B₂ Θ) t)) W₁)))
                 W₂)
        (sym (∈-++ᶜ-split-inj₁ (Γ ∷ B₁ ∷ B₂) Θ c c' eqc))
        (go c')
  where
    go : ∀ {σ₀} → (c₀ : [ ρ ] A ∈[ σ₀ ] (Γ ∷ B₁ ∷ B₂))
       → rcell Θ (proj₂ (rcell Θ (∈-++ᶜˡ {Γ = Γ ∷ B₁ ∷ B₂} Θ c₀)
                          (V-rename (wk-ren {A = B₁}) W₂))) W₁
       ≡ rcell Θ
           (proj₂ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ)
                    (rcell (([] ∷ B₂) ++ᶜ Θ)
                       (proj₂ (Tgt-cast (assocᴮ Γ B₁ B₂ Θ)
                                (_ , ∈-++ᶜˡ {Γ = Γ ∷ B₁ ∷ B₂} Θ c₀)))
                       W₁)))
           W₂

    -- the cell is the outer entry `B₂`: the left order hits it at once and
    -- then cancels the weakening (`unbox-cell-wk`); the right order lets it
    -- survive into the suffix and hits it last
    go Hd =
      trans
        (cong (λ t → rcell′ Θ t W₁)
          (trans (cong (λ t → rcell′ Θ t (V-rename (wk-ren {A = B₁}) W₂))
                       (sym (split→∈-∈-++ᶜˡ (Γ ∷ B₁) B₂ Θ)))
                 (sym (rvar-hit-ren (wk-ren {A = B₁}) Θ W₂))))
        (trans (unbox-cell-wk {Γ = Γ} {B = B₁} Θ (proj₂ (hcell Θ W₂)) (bval Θ W₁))
          (sym
            (trans
              (cong (λ t → rcell′ Θ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ) t) W₂)
                (trans
                  (cong (λ t → rcell′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                        (∈-++ᶜˡ-++ᶜʳ (Γ ∷ B₁) ([] ∷ B₂) Θ (Hd {Γ = []})))
                  (sub-rvar-r {Γ = Γ} {B = B₁} (([] ∷ B₂) ++ᶜ Θ)
                              (∈-++ᶜˡ {Γ = [] ∷ B₂} Θ (Hd {Γ = []}))
                              (bval (([] ∷ B₂) ++ᶜ Θ) W₁))))
              (trans
                (cong (λ t → rcell′ Θ t W₂)
                  (Tgt-cast-flip (++ᶜ-assoc Γ ([] ∷ B₂) Θ) _ _
                     (∈-++ᶜˡ-++ᶜʳ Γ ([] ∷ B₂) Θ (Hd {Γ = []}))))
                (cong (λ t → rcell′ Θ t W₂)
                      (sym (split→∈-∈-++ᶜˡ Γ B₂ Θ)))))))

    -- the cell is the inner entry `B₁`: the left order lets it survive and
    -- then hits it; the right order hits it at the bigger suffix, and
    -- `rhit-∷-++ᶜ` peels the `B₂` layer off again
    go (Tl-∷ Hd) =
      trans
        (cong (λ t → rcell′ Θ t W₁)
              (sub-rvar-l {Γ = Γ ∷ B₁} {B = B₂} Θ (Hd {Γ = Γ})
                          (bval Θ (V-rename (wk-ren {A = B₁}) W₂))))
        (trans
          (cong (λ t → rcell′ Θ t W₁)
                (sym (split→∈-∈-++ᶜˡ Γ B₁ Θ)))
          (sym
            (trans
              (cong (λ t → rcell′ Θ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ) t) W₂)
                (trans
                  (cong (λ t → rcell′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                    (Tgt-cast-flip⁻ (++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ) _ _
                       (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ (Hd {Γ = Γ}))))
                  (cong (λ t → rcell′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                        (sym (split→∈-∈-++ᶜˡ Γ B₁ (([] ∷ B₂) ++ᶜ Θ))))))
              (trans
                (cong (λ t → rcell′ Θ t W₂)
                  (trans (Tgt-cast-fuse (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))
                                        (assocᴮ⁻ Γ B₂ Θ) _)
                         (rhit-∷-++ᶜ Θ W₁ (Ehit B₁ B₂ Θ))))
                (trans
                  (cong (λ t → rcell′ Θ t W₂)
                        (sym (rvar-hit-ren (wk-ren {A = B₂}) Θ W₁)))
                  (unbox-cell-wk {Γ = Γ} {B = B₂} Θ (proj₂ (hcell Θ W₁)) (bval Θ W₂)))))))

    go (Tl-∷ (Tl-∷ c₀)) =
      trans (cong (λ t → rcell′ Θ t W₁)
                  (sub-rvar-l {Γ = Γ ∷ B₁} {B = B₂} Θ (Tl-∷ c₀)
                              (bval Θ (V-rename (wk-ren {A = B₁}) W₂))))
        (trans (sub-rvar-l {Γ = Γ} {B = B₁} Θ c₀ (bval Θ W₁))
          (sym
            (trans
              (cong (λ t → rcell′ Θ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ) t) W₂)
                (trans
                  (cong (λ t → rcell′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                    (Tgt-cast-flip⁻ (++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ) _ _
                       (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ (Tl-∷ c₀))))
                  (sub-rvar-l {Γ = Γ} {B = B₁} (([] ∷ B₂) ++ᶜ Θ) c₀
                              (bval (([] ∷ B₂) ++ᶜ Θ) W₁))))
              (trans
                (cong (λ t → rcell′ Θ t W₂)
                      (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ c₀))
                (sub-rvar-l {Γ = Γ} {B = B₂} Θ c₀ (bval Θ W₂))))))

-- `unbox`: both orders rebuild the unboxing from the cell the substitution
-- leaves (`sub-unbox`), so `unbox-≐` reduces the case to `unbox-cell-swap`
-- for the cell and the induction hypothesis for the body.

sub-swap-unbox : ∀ {Γ B₁ B₂ A C ρ Δ₀} → (Θ : Ctx)
               → (w : Ren [] (Δ₀ ⟨ ρ ⟩) ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
               → (V : Δ₀ ⊢V⦂ [ ρ ] A)
               → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ∷ A ⊢C⦂ C)
               → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
               → SubSwapC (Θ ∷ A) M W₂ W₁
               → SubSwapC Θ (unbox w V M) W₂ W₁

sub-swap-unbox {Γ} {B₁} {B₂} {A} {C} {ρ} {Δ₀} Θ w V M W₂ W₁ ih =
  ≐ᶜ-trans
    (≐ᶜ-trans
      (sub-atᶜ-≐ Θ W₁
        (≐ᶜ-trans (castᶜ-≐ (castOf {Γ ∷ B₁} {B₂} Θ)
                     (sub-unbox w V M x₂ V₂ relA))
                  (≡→≐ᶜ (cast-unbox (castOf {Γ ∷ B₁} {B₂} Θ)))))
      (≐ᶜ-trans (castᶜ-≐ (castOf {Γ} {B₁} Θ)
                   (sub-unbox wA hd bodyA x₁ V₁ relB))
                (≡→≐ᶜ (cast-unbox (castOf {Γ} {B₁} Θ)))))
    (≐ᶜ-trans
      (unbox-≐ cell
        (≐ᶜ-trans
          (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) (castOf {Γ} {B₁} Θ))
                           (castOf {Γ} {B₁} (Θ ∷ A)) _))
          (≐ᶜ-trans
            (sub-atᶜ-≐ (Θ ∷ A) W₁
              (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) (castOf {Γ ∷ B₁} {B₂} Θ))
                               (castOf {Γ ∷ B₁} {B₂} (Θ ∷ A)) _)))
            (≐ᶜ-trans ih
              (≐ᶜ-trans
                (sub-atᶜ-≐ (Θ ∷ A) W₂
                  (≡→≐ᶜ (trans
                    (cong (castᶜ (assocᴮ⁻ Γ B₂ (Θ ∷ A)))
                      (castᶜ-irr (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ (Θ ∷ A)))
                                 (cong (_∷ A)
                                       (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))) _))
                    (castᶜ-irr (assocᴮ⁻ Γ B₂ (Θ ∷ A))
                               (cong (_∷ A) (assocᴮ⁻ Γ B₂ Θ)) _))))
                (≡→≐ᶜ (castᶜ-irr (castOf {Γ} {B₂} (Θ ∷ A))
                                 (cong (_∷ A) (castOf {Γ} {B₂} Θ)) _)))))))
      (≐ᶜ-sym
        (≐ᶜ-trans
          (sub-atᶜ-≐ Θ W₂
            (≐ᶜ-trans
              (castᶜ-≐ (assocᴮ⁻ Γ B₂ Θ)
                (≐ᶜ-trans
                  (sub-atᶜ-≐ (([] ∷ B₂) ++ᶜ Θ) W₁
                    (≡→≐ᶜ (cast-unbox (assocᴮ Γ B₁ B₂ Θ))))
                  (≐ᶜ-trans
                    (castᶜ-≐ (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))
                      (sub-unbox (castʳ (assocᴮ Γ B₁ B₂ Θ) w) V _ y₁ U₁ relC))
                    (≡→≐ᶜ (cast-unbox
                             (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ)))))))
              (≡→≐ᶜ (cast-unbox (assocᴮ⁻ Γ B₂ Θ)))))
          (≐ᶜ-trans
            (castᶜ-≐ (castOf {Γ} {B₂} Θ)
              (sub-unbox (castʳ (assocᴮ⁻ Γ B₂ Θ) wC) hd _ y₂ U₂ relD))
            (≡→≐ᶜ (cast-unbox (castOf {Γ} {B₂} Θ)))))))
  where
    Ŵ₂ = V-rename (wk-ren {A = B₁}) W₂

    x₂ = bvar B₂ Θ
    V₂ = bval Θ Ŵ₂
    x₁ = bvar B₁ Θ
    V₁ = bval Θ W₁
    y₁ = bvar B₁ (([] ∷ B₂) ++ᶜ Θ)
    U₁ = bval (([] ∷ B₂) ++ᶜ Θ) W₁
    y₂ = bvar B₂ Θ
    U₂ = bval Θ W₂

    cW = proj₂ (unbox-tgt w V)

    hd : ∀ {Γ₀ : Ctx} → (Γ₀ ∷ [ ρ ] A) ⊢V⦂ [ ρ ] A
    hd = var (λ _ → ≾ᵣ-refl) Hd

    relA = ≾ᵣ-trans (proj₂ (proj₂ (⟨ cW ⟩[ x₂ ↦ V₂ ]rvar)))
                    (proj₂ (proj₂ (unbox⇒var w V)))

    vA = proj₂ (rvar-tgt cW x₂ V₂)

    wA = castʳ (castOf {Γ ∷ B₁} {B₂} Θ) (unbox-var-ren vA relA)

    bodyA = castᶜ (cong (_∷ A) (castOf {Γ ∷ B₁} {B₂} Θ))
                  (M [ Tl-∷ x₂ ↦ V₂ ]c)

    relB = ≾ᵣ-trans (proj₂ (proj₂ (⟨ proj₂ (unbox-tgt wA hd) ⟩[ x₁ ↦ V₁ ]rvar)))
                    (proj₂ (proj₂ (unbox⇒var wA hd)))

    vB = proj₂ (rvar-tgt (proj₂ (unbox-tgt wA hd)) x₁ V₁)

    wB = castʳ (castOf {Γ} {B₁} Θ) (unbox-var-ren vB relB)

    relC = ≾ᵣ-trans
             (proj₂ (proj₂
               (⟨ proj₂ (unbox-tgt (castʳ (assocᴮ Γ B₁ B₂ Θ) w) V)
                ⟩[ y₁ ↦ U₁ ]rvar)))
             (proj₂ (proj₂ (unbox⇒var (castʳ (assocᴮ Γ B₁ B₂ Θ) w) V)))

    vC = proj₂ (rvar-tgt (proj₂ (unbox-tgt (castʳ (assocᴮ Γ B₁ B₂ Θ) w) V))
                         y₁ U₁)

    wC = castʳ (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ)) (unbox-var-ren vC relC)

    relD = ≾ᵣ-trans
             (proj₂ (proj₂
               (⟨ proj₂ (unbox-tgt (castʳ (assocᴮ⁻ Γ B₂ Θ) wC) hd)
                ⟩[ y₂ ↦ U₂ ]rvar)))
             (proj₂ (proj₂ (unbox⇒var (castʳ (assocᴮ⁻ Γ B₂ Θ) wC) hd)))

    vD = proj₂ (rvar-tgt (proj₂ (unbox-tgt (castʳ (assocᴮ⁻ Γ B₂ Θ) wC) hd))
                         y₂ U₂)

    wD = castʳ (castOf {Γ} {B₂} Θ) (unbox-var-ren vD relD)

    -- each stored renaming is read only through `unbox-tgt`, and there it is
    -- the cell the substitution left; so the two sides' cells are exactly the
    -- two sides of `unbox-cell-swap`
    cellA : unbox-tgt wA hd ≡ rcell Θ cW Ŵ₂
    cellA = trans (unbox-tgt-castʳ (castOf {Γ ∷ B₁} {B₂} Θ)
                                    (unbox-var-ren vA relA) hd)
                  (cong (Tgt-cast (castOf {Γ ∷ B₁} {B₂} Θ))
                        (unbox-var-tgt vA relA))

    cellC : unbox-tgt wC hd
          ≡ rcell (([] ∷ B₂) ++ᶜ Θ)
                  (proj₂ (Tgt-cast (assocᴮ Γ B₁ B₂ Θ) (unbox-tgt w V))) W₁
    cellC =
      trans (unbox-tgt-castʳ (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))
                              (unbox-var-ren vC relC) hd)
        (trans (cong (Tgt-cast (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ)))
                     (unbox-var-tgt vC relC))
               (cong (λ t → rcell′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                     (unbox-tgt-castʳ (assocᴮ Γ B₁ B₂ Θ) w V)))

    cell : unbox-tgt wB hd ≡ unbox-tgt wD hd
    cell =
      trans (unbox-tgt-castʳ (castOf {Γ} {B₁} Θ) (unbox-var-ren vB relB) hd)
        (trans (cong (Tgt-cast (castOf {Γ} {B₁} Θ)) (unbox-var-tgt vB relB))
          (trans (cong (λ t → rcell′ Θ t W₁) cellA)
            (trans (unbox-cell-swap Θ cW W₂ W₁)
              (sym
                (trans (unbox-tgt-castʳ (castOf {Γ} {B₂} Θ)
                                         (unbox-var-ren vD relD) hd)
                  (trans (cong (Tgt-cast (castOf {Γ} {B₂} Θ))
                               (unbox-var-tgt vD relD))
                    (trans
                      (cong (λ t → rcell′ Θ t W₂)
                            (unbox-tgt-castʳ (assocᴮ⁻ Γ B₂ Θ) wC hd))
                      (cong (λ t → rcell′ Θ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ) t) W₂)
                            cellC))))))))

-- `handle`: the scrutinee and the sequel are the induction hypotheses at
-- their own suffixes, so the whole content is the clauses — the same swap
-- at the *restricted* context, where each order reaches them through its
-- own `⟨_⟩[_↦_]cl`.
--
-- That is the one piece still open. It dispatches on `eternal? B₁` and
-- `eternal? B₂` (four combinations, by `cl-cancel`'s Dec-argument
-- pattern, since a `with` would abstract the clause family's own type).
-- Three are cheap: a `⟨ no ¬et ⟩cl` is a transport, so at most one
-- substitution survives on each side and the leftover transports form a
-- loop that `uip` collapses (`sub-wk-handle-ne`'s `collapse`). The
-- both-eternal one is *this lemma again* at the splitting's own halves,
-- threaded through a `sub-swap-C-cast` so the recursion stays on the bare
-- clause — `sub-wk-handle-et`'s shape, and the same reason: only there do
-- the two ways of naming the substituted variable become the same
-- splitting (`split→∈-unique`/`split→∈-unique₂`).

-- The clause action with the eternality decision taken as an argument, so
-- that the four branches can be matched rather than `with`-abstracted —
-- a `with` would abstract the clause family's own type, which mentions
-- `_ᴱ` of the very context being decided about.

sub-atᴴ′ : ∀ {Γ' B D} → Dec (Eternal B) → (Θ : Ctx)
         → Fam D (((Γ' ∷ B) ++ᶜ Θ) ᴱ) → Γ' ⊢V⦂ B → Fam D ((Γ' ++ᶜ Θ) ᴱ)
sub-atᴴ′ {Γ'} {B} dec Θ H W op ε =
  Cl-cast op ε (castOf {Γ'} {B} Θ) (⟨ dec ⟩[ bvar B Θ ↦ bval Θ W ]cl H op ε)

inner₀ᴴ′ : ∀ {Γ B₁ B₂ D} → Dec (Eternal B₁) → (Θ : Ctx)
         → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ) → Γ ⊢V⦂ B₁
         → Fam D (((Γ ∷ B₂) ++ᶜ Θ) ᴱ)
inner₀ᴴ′ {Γ} {B₁} {B₂} dec₁ Θ H W₁ op ε =
  Cl-cast op ε (assocᴮ⁻ Γ B₂ Θ)
    (sub-atᴴ′ dec₁ (([] ∷ B₂) ++ᶜ Θ)
       (λ op' ε' → Cl-cast op' ε' (assocᴮ Γ B₁ B₂ Θ) (H op' ε')) W₁ op ε)

outerᴴ′ : ∀ {Γ B₁ B₂ D} → Dec (Eternal B₁) → Dec (Eternal B₂) → (Θ : Ctx)
        → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ) → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁
        → Fam D ((Γ ++ᶜ Θ) ᴱ)
outerᴴ′ {B₁ = B₁} dec₁ dec₂ Θ H W₂ W₁ =
  sub-atᴴ′ dec₁ Θ (sub-atᴴ′ dec₂ Θ H (V-rename (wk-ren {A = B₁}) W₂)) W₁

innerᴴ′ : ∀ {Γ B₁ B₂ D} → Dec (Eternal B₁) → Dec (Eternal B₂) → (Θ : Ctx)
        → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ) → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁
        → Fam D ((Γ ++ᶜ Θ) ᴱ)
innerᴴ′ dec₁ dec₂ Θ H W₂ W₁ =
  sub-atᴴ′ dec₂ Θ (inner₀ᴴ′ dec₁ Θ H W₁) W₂

ClSwap : ∀ {Γ B₁ B₂ D} → Dec (Eternal B₁) → Dec (Eternal B₂) → (Θ : Ctx)
       → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ) → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁
       → (op : Op) → (ε : E) → Set
ClSwap dec₁ dec₂ Θ H W₂ W₁ op ε =
  outerᴴ′ dec₁ dec₂ Θ H W₂ W₁ op ε ≐ᶜ innerᴴ′ dec₁ dec₂ Θ H W₂ W₁ op ε

------------------------------------------------------------------------
