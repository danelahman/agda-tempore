------------------------------------------------------------------------
-- The swap on a variable, and on the resource variable an `unbox` names.
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
SubSwapV Θ U W₂ W₁ = outerᵛ Θ U W₂ W₁ ≡ innerᵛ Θ U W₂ W₁

SubSwapC : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
         → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → Set
SubSwapC Θ M W₂ W₁ = outerᶜ Θ M W₂ W₁ ≡ innerᶜ Θ M W₂ W₁

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

sub-atᵛ-≡ : ∀ {Γ' B A} → (Θ : Ctx) → {U U' : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A}
          → (W : Γ' ⊢V⦂ B) → U ≡ U' → sub-atᵛ Θ U W ≡ sub-atᵛ Θ U' W
sub-atᵛ-≡ Θ W e = castᵛ-≡ _ (sub-≡ᵛ _ (refl) e)

sub-atᶜ-≡ : ∀ {Γ' B C} → (Θ : Ctx) → {M M' : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C}
          → (W : Γ' ⊢V⦂ B) → M ≡ M' → sub-atᶜ Θ M W ≡ sub-atᶜ Θ M' W
sub-atᶜ-≡ Θ W e = castᶜ-≡ _ (sub-≡ᶜ _ (refl) e)

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
          ≡ hitᵛ {Γ' ∷ B₀} Θ (V-rename (wk-ren {A = B₀}) W) g'

hit-∷-++ᶜ {Γ'} {B} {B₀} [] W g g' E =  (castᵛ-irr E refl _)

hit-∷-++ᶜ {Γ'} {B} {B₀} (Θ ∷ C) W g g' E =
  trans
    ( (cast-wk-any E (Ehit B B₀ Θ)
             (⟨ bvar B (([] ∷ B₀) ++ᶜ Θ) , g
              ⟩[ bvar B (([] ∷ B₀) ++ᶜ Θ)
                 ↦ bval (([] ∷ B₀) ++ᶜ Θ) W ]var)))
    (trans
      (V-rename-cong wk-ren (hit-∷-++ᶜ Θ W g g' (Ehit B B₀ Θ)))
      ( (sym (cast-wk-any (castOf {Γ' ∷ B₀} {B} (Θ ∷ C))
                              (castOf {Γ' ∷ B₀} {B} Θ) _))))

hit-∷-++ᶜ {Γ'} {B} {B₀} (Θ ⟨ ρ ⟩) W g g' E with eternal? B

... | yes et =
  trans
    ( (cast-ext-any E (Ehit B B₀ Θ) et
             (⟨ bvar B (([] ∷ B₀) ++ᶜ Θ) , _
              ⟩[ bvar B (([] ∷ B₀) ++ᶜ Θ)
                 ↦ bval (([] ∷ B₀) ++ᶜ Θ) W ]var)))
    (trans
      (eternal-val-ext-cong et (hit-∷-++ᶜ Θ W _ _ (Ehit B B₀ Θ)))
      ( (sym (cast-ext-any (castOf {Γ' ∷ B₀} {B} (Θ ⟨ ρ ⟩))
                               (castOf {Γ' ∷ B₀} {B} Θ) et _))))

... | no ¬et =
  trans
    ( (cast-ren-⟨⟩-any E (Ehit B B₀ Θ) rn
             (⟨ bvar B (([] ∷ B₀) ++ᶜ Θ) , _
              ⟩[ bvar B (([] ∷ B₀) ++ᶜ Θ)
                 ↦ bval (([] ∷ B₀) ++ᶜ Θ) W ]var)))
    (trans (V-rename-cong rn (hit-∷-++ᶜ Θ W _ _ (Ehit B B₀ Θ)))
      (trans (V-rename-≡ (∘ʳ-≐ʳ ≐ʳ-refl (⟨⟩-≤-ren-≐ʳ _ _)) _)
                ( (sym (cast-ren-⟨⟩-any (castOf {Γ' ∷ B₀} {B} (Θ ⟨ ρ ⟩))
                                            (castOf {Γ' ∷ B₀} {B} Θ) rn' _)))))
  where
    rn : ∀ {Γ₀ : Ctx} → Ren [] (Γ₀ ⟨ ρ ⟩) Γ₀
    rn = ⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (g ¬et))

    rn' : ∀ {Γ₀ : Ctx} → Ren [] (Γ₀ ⟨ ρ ⟩) Γ₀
    rn' = ⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (g' ¬et))

-- Relocating a variable along a context transport, at the `Var` level so
-- that the grade travels with the position.

castᵛ-var-img : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ') → (x : A ∈[ ρ ] Γ)
              → (t : Var Γ' A) → Var-cast e (ρ , x) ≡ t
              → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
              → (f' : ¬ Eternal A → proj₁ t ≾ᵣ uᵣ)
              → castᵛ e (var f x) ≡ var f' (proj₂ t)
castᵛ-var-img refl x .(_ , x) refl f f' = var-≡

-- The three positions the substitution distinguishes, each taking where
-- the variable sits as a `Var` equation.

sub-at-varᵣ : ∀ {Γ' B A ρ} → (Θ : Ctx) → (x : A ∈[ ρ ] Θ)
            → (y : A ∈[ ρ ] ((Γ' ∷ B) ++ᶜ Θ)) → y ≡ ∈-++ᶜʳ {Γ = Γ' ∷ B} x
            → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → (f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
            → (W : Γ' ⊢V⦂ B)
            → sub-atᵛ Θ (var f y) W ≡ var f' (∈-++ᶜʳ {Γ = Γ'} x)
sub-at-varᵣ Θ x _ refl f f' W = sub-var-r Θ x (bval Θ W) f f'

sub-at-varₗ : ∀ {Γ' B A ρ} → (Θ : Ctx) → (x : A ∈[ ρ ] Γ')
            → (y : A ∈[ grade-++ᶜˡ ρ Θ ] ((Γ' ∷ B) ++ᶜ Θ))
            → y ≡ ∈-++ᶜˡ {Γ = Γ' ∷ B} Θ (Tl-∷ x)
            → (f f' : ¬ Eternal A → grade-++ᶜˡ ρ Θ ≾ᵣ uᵣ) → (W : Γ' ⊢V⦂ B)
            → sub-atᵛ Θ (var f y) W ≡ var f' (∈-++ᶜˡ {Γ = Γ'} Θ x)
sub-at-varₗ Θ x _ refl f f' W = sub-var-l Θ x (bval Θ W) f f'

sub-at-varₕ : ∀ {Γ' B ρ} → (Θ : Ctx) → (y : B ∈[ ρ ] ((Γ' ∷ B) ++ᶜ Θ))
            → _≡_ {A = Var ((Γ' ∷ B) ++ᶜ Θ) B}
                  (ρ , y) (ctx-grade Θ , bvar B Θ)
            → (f : ¬ Eternal B → ρ ≾ᵣ uᵣ)
            → (f' : ¬ Eternal B → ctx-grade Θ ≾ᵣ uᵣ) → (W : Γ' ⊢V⦂ B)
            → sub-atᵛ Θ (var f y) W ≡ hitᵛ Θ W f'
sub-at-varₕ Θ .(bvar _ Θ) refl f f' W
  rewrite bound-irr f f' = refl

------------------------------------------------------------------------
-- The four positions.
------------------------------------------------------------------------

swap-var-r : ∀ {Γ B₁ B₂ A ρ} → (Θ : Ctx) → (x : A ∈[ ρ ] Θ)
           → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
           → SubSwapV Θ (var f (∈-++ᶜʳ {Γ = Γ ∷ B₁ ∷ B₂} x)) W₂ W₁
swap-var-r {Γ} {B₁} {B₂} Θ x f W₂ W₁ =
  trans
    (trans (sub-atᵛ-≡ Θ W₁ (sub-at-varᵣ Θ x _ refl f f _))
              (sub-at-varᵣ Θ x _ refl f f W₁))
    (sym
      (trans
        (sub-atᵛ-≡ Θ W₂
          (trans
            (castᵛ-≡ (assocᴮ⁻ Γ B₂ Θ)
              (trans
                (sub-atᵛ-≡ (([] ∷ B₂) ++ᶜ Θ) W₁
                   (castᵛ-var-img (assocᴮ Γ B₁ B₂ Θ) _ _
                      (cong (λ z → _ , z) (∈-++ᶜʳ-assoc (Γ ∷ B₁) ([] ∷ B₂) x))
                      f f))
                (sub-at-varᵣ (([] ∷ B₂) ++ᶜ Θ) (∈-++ᶜʳ {Γ = [] ∷ B₂} x) _
                             refl f f W₁)))
            (castᵛ-var-img (assocᴮ⁻ Γ B₂ Θ) _ _
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
  trans
    (trans (sub-atᵛ-≡ Θ W₁ (sub-at-varₗ Θ (Tl-∷ v) _ refl f f _))
              (sub-at-varₗ Θ v _ refl f f W₁))
    (sym
      (trans
        (sub-atᵛ-≡ Θ W₂
          (trans
            (castᵛ-≡ (assocᴮ⁻ Γ B₂ Θ)
              (trans
                (sub-atᵛ-≡ (([] ∷ B₂) ++ᶜ Θ) W₁
                   (castᵛ-var-img (assocᴮ Γ B₁ B₂ Θ) _ _
                      (Var-cast-flip⁻ (++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ) _ _
                         (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ (Tl-∷ v)))
                      f fΔ))
                (sub-at-varₗ (([] ∷ B₂) ++ᶜ Θ) v _ refl fΔ fΔ W₁)))
            (castᵛ-var-img (assocᴮ⁻ Γ B₂ Θ) _ _
               (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ v) fΔ f)))
        (sub-at-varₗ Θ v _ refl f f W₂)))
  where
    fΔ : ¬ Eternal _ → grade-++ᶜˡ _ (([] ∷ B₂) ++ᶜ Θ) ≾ᵣ uᵣ
    fΔ ¬et = subst (_≾ᵣ uᵣ) (sym (grade-++ᶜˡ-assoc _ ([] ∷ B₂) Θ)) (f ¬et)

swap-var-B₂ : ∀ {Γ B₁ B₂ ρ} → (Θ : Ctx)
            → (f : ¬ Eternal B₂ → ρ ≾ᵣ uᵣ)
            → (y : B₂ ∈[ ρ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
            → _≡_ {A = Var ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) B₂}
                  (ρ , y) (grade-++ᶜˡ uᵣ Θ , ∈-++ᶜˡ Θ (Hd {Γ = Γ ∷ B₁}))
            → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
            → SubSwapV Θ (var f y) W₂ W₁
swap-var-B₂ {Γ} {B₁} {B₂} Θ f .(∈-++ᶜˡ Θ Hd) refl W₂ W₁ =
  trans
    (trans
      (sub-atᵛ-≡ Θ W₁
        (sub-at-varₕ Θ _ (sym (split→∈-∈-++ᶜˡ (Γ ∷ B₁) B₂ Θ)) f fΘ _))
      (trans
        (sub-atᵛ-≡ Θ W₁
          (sym (ren-sub-hit (wk-ren {A = B₁}) Θ W₂ fΘ fΘ)))
        (sub-wk-V Θ (hitᵛ Θ W₂ fΘ) (bval Θ W₁))))
    (sym
      (trans
        (sub-atᵛ-≡ Θ W₂
          (trans
            (castᵛ-≡ (assocᴮ⁻ Γ B₂ Θ)
              (trans
                (sub-atᵛ-≡ (([] ∷ B₂) ++ᶜ Θ) W₁
                   (castᵛ-var-img (assocᴮ Γ B₁ B₂ Θ) _ _
                      (∈-++ᶜˡ-++ᶜʳ (Γ ∷ B₁) ([] ∷ B₂) Θ (Hd {Γ = []}))
                      f f))
                (sub-at-varᵣ (([] ∷ B₂) ++ᶜ Θ)
                             (∈-++ᶜˡ {Γ = [] ∷ B₂} Θ (Hd {Γ = []})) _
                             refl f f W₁)))
            (castᵛ-var-img (assocᴮ⁻ Γ B₂ Θ) _ _
               (Var-cast-flip (++ᶜ-assoc Γ ([] ∷ B₂) Θ) _ _
                  (∈-++ᶜˡ-++ᶜʳ Γ ([] ∷ B₂) Θ (Hd {Γ = []})))
               f f)))
        (sub-at-varₕ Θ _ (sym (split→∈-∈-++ᶜˡ Γ B₂ Θ)) f fΘ W₂)))
  where
    fΘ : ¬ Eternal B₂ → ctx-grade Θ ≾ᵣ uᵣ
    fΘ ¬et = subst (_≾ᵣ uᵣ) (grade-++ᶜˡ-uᵣ Θ) (f ¬et)

swap-var-B₁ : ∀ {Γ B₁ B₂ ρ} → (Θ : Ctx)
            → (f : ¬ Eternal B₁ → ρ ≾ᵣ uᵣ)
            → (y : B₁ ∈[ ρ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
            → _≡_ {A = Var ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) B₁}
                  (ρ , y) (grade-++ᶜˡ uᵣ Θ , ∈-++ᶜˡ Θ (Tl-∷ (Hd {Γ = Γ})))
            → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
            → SubSwapV Θ (var f y) W₂ W₁
swap-var-B₁ {Γ} {B₁} {B₂} Θ f .(∈-++ᶜˡ Θ (Tl-∷ Hd)) refl W₂ W₁ =
  trans
    (trans (sub-atᵛ-≡ Θ W₁ (sub-at-varₗ Θ (Hd {Γ = Γ}) _ refl f f _))
              (sub-at-varₕ Θ _ (sym (split→∈-∈-++ᶜˡ Γ B₁ Θ)) f fΘ W₁))
    (sym
      (trans
        (sub-atᵛ-≡ Θ W₂
          (trans
            (castᵛ-≡ (assocᴮ⁻ Γ B₂ Θ)
              (trans
                (sub-atᵛ-≡ (([] ∷ B₂) ++ᶜ Θ) W₁
                   (castᵛ-var-img (assocᴮ Γ B₁ B₂ Θ) _ _
                      (Var-cast-flip⁻ (++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ) _ _
                         (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ (Hd {Γ = Γ})))
                      f fΔ))
                (sub-at-varₕ (([] ∷ B₂) ++ᶜ Θ) _
                   (sym (split→∈-∈-++ᶜˡ Γ B₁ (([] ∷ B₂) ++ᶜ Θ))) fΔ g W₁)))
            (trans
              ( (castᵛ-fuse (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))
                                (assocᴮ⁻ Γ B₂ Θ) _))
              (hit-∷-++ᶜ Θ W₁ g fΘ (Ehit B₁ B₂ Θ)))))
        (trans
          (sub-atᵛ-≡ Θ W₂ (sym (ren-sub-hit (wk-ren {A = B₂}) Θ W₁ fΘ fΘ)))
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
            → _≡_ {A = Var ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) A}
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
-- Substitution takes an `unbox` to an `unbox` at the resource variable
-- `⟨_⟩[_↦_]rvar` leaves, so the `unbox` case reduces to: the two orders name
-- the same resource variable. That is the `rvar` counterpart of the variable
-- case, and a simpler one — a box type is never eternal, so `⟨_⟩[_↦_]rvar` has
-- no `eternal?` split and each position is one `Var-cast` push.
------------------------------------------------------------------------

-- The resource variable left by replacing the entry at the boundary.

rvar-at : ∀ {Γ' B A ρ σ} → (Θ : Ctx)
      → ([ ρ ] A ∈[ σ ] ((Γ' ∷ B) ++ᶜ Θ)) → (W : Γ' ⊢V⦂ B)
      → Var (Γ' ++ᶜ Θ) ([ ρ ] A)
rvar-at {Γ'} {B} Θ c W =
  Var-cast (castOf {Γ'} {B} Θ) (rvar-img c (bvar B Θ) (bval Θ W))

-- The same at an already-located resource variable. `Var` is a Σ, so `cong` cannot infer
-- the dependent motive from a lambda — this has to be named, exactly as
-- `var-img′` is.

rvar-at′ : ∀ {Γ' B A ρ} → (Θ : Ctx) → Var ((Γ' ∷ B) ++ᶜ Θ) ([ ρ ] A)
       → (W : Γ' ⊢V⦂ B) → Var (Γ' ++ᶜ Θ) ([ ρ ] A)
rvar-at′ Θ (σ , c) W = rvar-at Θ c W

-- and, when the entry replaced *is* the resource variable, the resource variable of the value it is
-- replaced by, pushed under the suffix.

rvar-at-hit : ∀ {Γ' A ρ} → (Θ : Ctx) → (W : Γ' ⊢V⦂ [ ρ ] A) → Var (Γ' ++ᶜ Θ) ([ ρ ] A)
rvar-at-hit {Γ'} {A} {ρ} Θ W = rvar-at Θ (bvar ([ ρ ] A) Θ) W

-- The resource variable counterpart of `hit-∷-++ᶜ`, and by the same induction.

rhit-∷-++ᶜ : ∀ {Γ' A ρ B₀} → (Θ : Ctx) → (W : Γ' ⊢V⦂ [ ρ ] A)
           → (E : (split-l (bvar {Γ'} ([ ρ ] A) (([] ∷ B₀) ++ᶜ Θ))
                     ++ᶜ split-r (bvar {Γ'} ([ ρ ] A) (([] ∷ B₀) ++ᶜ Θ)))
                ≡ ((Γ' ∷ B₀) ++ᶜ Θ))
           → Var-cast E
               (rvar-img (bvar ([ ρ ] A) (([] ∷ B₀) ++ᶜ Θ))
                         (bvar ([ ρ ] A) (([] ∷ B₀) ++ᶜ Θ))
                         (bval (([] ∷ B₀) ++ᶜ Θ) W))
           ≡ rvar-at-hit {Γ' ∷ B₀} Θ (V-rename (wk-ren {A = B₀}) W)

rhit-∷-++ᶜ {Γ'} {A} {ρ} {B₀} [] (var f y) E =
  Var-cast-irr E refl _

rhit-∷-++ᶜ {Γ'} {A} {ρ} {B₀} (Θ ∷ C) W E =
  trans (Var-cast-irr E (cong (_∷ C) (Ehit ([ ρ ] A) B₀ Θ)) _)
    (trans (Var-cast-∷ (Ehit ([ ρ ] A) B₀ Θ) _)
      (trans (cong Var-∷ (rhit-∷-++ᶜ Θ W (Ehit ([ ρ ] A) B₀ Θ)))
        (trans (sym (Var-cast-∷ (castOf {Γ' ∷ B₀} {[ ρ ] A} Θ) _))
               (Var-cast-irr (cong (_∷ C) (castOf {Γ' ∷ B₀} {[ ρ ] A} Θ))
                             (castOf {Γ' ∷ B₀} {[ ρ ] A} (Θ ∷ C)) _))))

rhit-∷-++ᶜ {Γ'} {A} {ρ} {B₀} (Θ ⟨ ρ' ⟩) W E =
  trans (Var-cast-irr E (cong (_⟨ ρ' ⟩) (Ehit ([ ρ ] A) B₀ Θ)) _)
    (trans (Var-cast-⟨⟩ ρ' (Ehit ([ ρ ] A) B₀ Θ) _)
      (trans (cong (Var-⟨⟩ ρ') (rhit-∷-++ᶜ Θ W (Ehit ([ ρ ] A) B₀ Θ)))
        (trans (sym (Var-cast-⟨⟩ ρ' (castOf {Γ' ∷ B₀} {[ ρ ] A} Θ) _))
               (Var-cast-irr (cong (_⟨ ρ' ⟩) (castOf {Γ' ∷ B₀} {[ ρ ] A} Θ))
                             (castOf {Γ' ∷ B₀} {[ ρ ] A} (Θ ⟨ ρ' ⟩)) _))))

-- The four positions, at the resource variable level.

unbox-rvar-swap : ∀ {Γ B₁ B₂ A ρ σ} → (Θ : Ctx)
                → (c : [ ρ ] A ∈[ σ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
                → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
                → rvar-at Θ (proj₂ (rvar-at Θ c (V-rename (wk-ren {A = B₁}) W₂)))
                          W₁
                ≡ rvar-at Θ
                    (proj₂ (Var-cast (assocᴮ⁻ Γ B₂ Θ)
                             (rvar-at (([] ∷ B₂) ++ᶜ Θ)
                                (proj₂ (Var-cast (assocᴮ Γ B₁ B₂ Θ) (σ , c)))
                                W₁)))
                    W₂

unbox-rvar-swap {Γ} {B₁} {B₂} {A} {ρ} {σ} Θ c W₂ W₁
  with ∈-++ᶜ-split (Γ ∷ B₁ ∷ B₂) Θ c in eqc

... | inj₂ c'
  rewrite ∈-++ᶜ-split-inj₂ (Γ ∷ B₁ ∷ B₂) Θ c c' eqc =
  trans (cong (λ t → rvar-at′ Θ t W₁)
              (sub-rvar-r {Γ = Γ ∷ B₁} {B = B₂} Θ c'
                          (bval Θ (V-rename (wk-ren {A = B₁}) W₂))))
    (trans (sub-rvar-r {Γ = Γ} {B = B₁} Θ c' (bval Θ W₁))
      (sym
        (trans
          (cong (λ t → rvar-at′ Θ (Var-cast (assocᴮ⁻ Γ B₂ Θ) t) W₂)
            (trans
              (cong (λ t → rvar-at′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                    (cong (λ z → σ , z)
                          (∈-++ᶜʳ-assoc (Γ ∷ B₁) ([] ∷ B₂) c')))
              (sub-rvar-r {Γ = Γ} {B = B₁} (([] ∷ B₂) ++ᶜ Θ)
                          (∈-++ᶜʳ {Γ = [] ∷ B₂} c')
                          (bval (([] ∷ B₂) ++ᶜ Θ) W₁))))
          (trans
            (cong (λ t → rvar-at′ Θ t W₂)
                  (cong (λ z → σ , z)
                        (subst-flip (++ᶜ-assoc Γ ([] ∷ B₂) Θ) _ _
                                    (∈-++ᶜʳ-assoc Γ ([] ∷ B₂) c'))))
            (sub-rvar-r {Γ = Γ} {B = B₂} Θ c' (bval Θ W₂))))))

... | inj₁ (σ' , c') =
  subst (λ t → rvar-at Θ (proj₂ (rvar-at Θ (proj₂ t)
                                (V-rename (wk-ren {A = B₁}) W₂))) W₁
             ≡ rvar-at Θ
                 (proj₂ (Var-cast (assocᴮ⁻ Γ B₂ Θ)
                          (rvar-at (([] ∷ B₂) ++ᶜ Θ)
                             (proj₂ (Var-cast (assocᴮ Γ B₁ B₂ Θ) t)) W₁)))
                 W₂)
        (sym (∈-++ᶜ-split-inj₁ (Γ ∷ B₁ ∷ B₂) Θ c c' eqc))
        (go c')
  where
    go : ∀ {σ₀} → (c₀ : [ ρ ] A ∈[ σ₀ ] (Γ ∷ B₁ ∷ B₂))
       → rvar-at Θ (proj₂ (rvar-at Θ (∈-++ᶜˡ {Γ = Γ ∷ B₁ ∷ B₂} Θ c₀)
                          (V-rename (wk-ren {A = B₁}) W₂))) W₁
       ≡ rvar-at Θ
           (proj₂ (Var-cast (assocᴮ⁻ Γ B₂ Θ)
                    (rvar-at (([] ∷ B₂) ++ᶜ Θ)
                       (proj₂ (Var-cast (assocᴮ Γ B₁ B₂ Θ)
                                (_ , ∈-++ᶜˡ {Γ = Γ ∷ B₁ ∷ B₂} Θ c₀)))
                       W₁)))
           W₂

    -- the resource variable is the outer entry `B₂`: the left order hits it at once and
    -- then cancels the weakening (`unbox-rvar-wk`); the right order lets it
    -- survive into the suffix and hits it last
    go Hd =
      trans
        (cong (λ t → rvar-at′ Θ t W₁)
          (trans (cong (λ t → rvar-at′ Θ t (V-rename (wk-ren {A = B₁}) W₂))
                       (sym (split→∈-∈-++ᶜˡ (Γ ∷ B₁) B₂ Θ)))
                 (sym (rvar-hit-ren (wk-ren {A = B₁}) Θ W₂))))
        (trans (unbox-rvar-wk {Γ = Γ} {B = B₁} Θ (proj₂ (rvar-at-hit Θ W₂)) (bval Θ W₁))
          (sym
            (trans
              (cong (λ t → rvar-at′ Θ (Var-cast (assocᴮ⁻ Γ B₂ Θ) t) W₂)
                (trans
                  (cong (λ t → rvar-at′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                        (∈-++ᶜˡ-++ᶜʳ (Γ ∷ B₁) ([] ∷ B₂) Θ (Hd {Γ = []})))
                  (sub-rvar-r {Γ = Γ} {B = B₁} (([] ∷ B₂) ++ᶜ Θ)
                              (∈-++ᶜˡ {Γ = [] ∷ B₂} Θ (Hd {Γ = []}))
                              (bval (([] ∷ B₂) ++ᶜ Θ) W₁))))
              (trans
                (cong (λ t → rvar-at′ Θ t W₂)
                  (Var-cast-flip (++ᶜ-assoc Γ ([] ∷ B₂) Θ) _ _
                     (∈-++ᶜˡ-++ᶜʳ Γ ([] ∷ B₂) Θ (Hd {Γ = []}))))
                (cong (λ t → rvar-at′ Θ t W₂)
                      (sym (split→∈-∈-++ᶜˡ Γ B₂ Θ)))))))

    -- the resource variable is the inner entry `B₁`: the left order lets it survive and
    -- then hits it; the right order hits it at the bigger suffix, and
    -- `rhit-∷-++ᶜ` peels the `B₂` layer off again
    go (Tl-∷ Hd) =
      trans
        (cong (λ t → rvar-at′ Θ t W₁)
              (sub-rvar-l {Γ = Γ ∷ B₁} {B = B₂} Θ (Hd {Γ = Γ})
                          (bval Θ (V-rename (wk-ren {A = B₁}) W₂))))
        (trans
          (cong (λ t → rvar-at′ Θ t W₁)
                (sym (split→∈-∈-++ᶜˡ Γ B₁ Θ)))
          (sym
            (trans
              (cong (λ t → rvar-at′ Θ (Var-cast (assocᴮ⁻ Γ B₂ Θ) t) W₂)
                (trans
                  (cong (λ t → rvar-at′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                    (Var-cast-flip⁻ (++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ) _ _
                       (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ (Hd {Γ = Γ}))))
                  (cong (λ t → rvar-at′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                        (sym (split→∈-∈-++ᶜˡ Γ B₁ (([] ∷ B₂) ++ᶜ Θ))))))
              (trans
                (cong (λ t → rvar-at′ Θ t W₂)
                  (trans (Var-cast-fuse (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))
                                        (assocᴮ⁻ Γ B₂ Θ) _)
                         (rhit-∷-++ᶜ Θ W₁ (Ehit B₁ B₂ Θ))))
                (trans
                  (cong (λ t → rvar-at′ Θ t W₂)
                        (sym (rvar-hit-ren (wk-ren {A = B₂}) Θ W₁)))
                  (unbox-rvar-wk {Γ = Γ} {B = B₂} Θ (proj₂ (rvar-at-hit Θ W₁)) (bval Θ W₂)))))))

    go (Tl-∷ (Tl-∷ c₀)) =
      trans (cong (λ t → rvar-at′ Θ t W₁)
                  (sub-rvar-l {Γ = Γ ∷ B₁} {B = B₂} Θ (Tl-∷ c₀)
                              (bval Θ (V-rename (wk-ren {A = B₁}) W₂))))
        (trans (sub-rvar-l {Γ = Γ} {B = B₁} Θ c₀ (bval Θ W₁))
          (sym
            (trans
              (cong (λ t → rvar-at′ Θ (Var-cast (assocᴮ⁻ Γ B₂ Θ) t) W₂)
                (trans
                  (cong (λ t → rvar-at′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                    (Var-cast-flip⁻ (++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ) _ _
                       (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ (Tl-∷ c₀))))
                  (sub-rvar-l {Γ = Γ} {B = B₁} (([] ∷ B₂) ++ᶜ Θ) c₀
                              (bval (([] ∷ B₂) ++ᶜ Θ) W₁))))
              (trans
                (cong (λ t → rvar-at′ Θ t W₂)
                      (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ c₀))
                (sub-rvar-l {Γ = Γ} {B = B₂} Θ c₀ (bval Θ W₂))))))

-- `unbox`: `unbox-≡` reduces the case to `unbox-rvar-swap` for the resource
-- variable and the induction hypothesis for the body.

sub-swap-unbox : ∀ {Γ B₁ B₂ A C ρ σ} → (Θ : Ctx)
               → (c : [ ρ ] A ∈[ σ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
               → (rel : σ ≾ᵣ ρ)
               → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ∷ A ⊢C⦂ C)
               → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
               → SubSwapC (Θ ∷ A) M W₂ W₁
               → SubSwapC Θ (unbox c rel M) W₂ W₁

sub-swap-unbox {Γ} {B₁} {B₂} {A} {C} Θ c rel M W₂ W₁ ih =
  trans
    (trans
      (sub-atᶜ-≡ Θ W₁ ( (cast-unbox (castOf {Γ ∷ B₁} {B₂} Θ))))
      ( (cast-unbox (castOf {Γ} {B₁} Θ))))
    (trans
      (unbox-≡ (unbox-rvar-swap Θ c W₂ W₁)
        (trans
          ( (castᶜ-irr (cong (_∷ A) (castOf {Γ} {B₁} Θ))
                           (castOf {Γ} {B₁} (Θ ∷ A)) _))
          (trans
            (sub-atᶜ-≡ (Θ ∷ A) W₁
              ( (castᶜ-irr (cong (_∷ A) (castOf {Γ ∷ B₁} {B₂} Θ))
                               (castOf {Γ ∷ B₁} {B₂} (Θ ∷ A)) _)))
            (trans ih
              (trans
                (sub-atᶜ-≡ (Θ ∷ A) W₂
                  ( (trans
                    (cong (castᶜ (assocᴮ⁻ Γ B₂ (Θ ∷ A)))
                      (castᶜ-irr (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ (Θ ∷ A)))
                                 (cong (_∷ A)
                                       (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))) _))
                    (castᶜ-irr (assocᴮ⁻ Γ B₂ (Θ ∷ A))
                               (cong (_∷ A) (assocᴮ⁻ Γ B₂ Θ)) _))))
                ( (castᶜ-irr (castOf {Γ} {B₂} (Θ ∷ A))
                                 (cong (_∷ A) (castOf {Γ} {B₂} Θ)) _)))))))
      (sym
        (trans
          (sub-atᶜ-≡ Θ W₂
            (trans
              (castᶜ-≡ (assocᴮ⁻ Γ B₂ Θ)
                (trans
                  (sub-atᶜ-≡ (([] ∷ B₂) ++ᶜ Θ) W₁
                    ( (cast-unbox (assocᴮ Γ B₁ B₂ Θ))))
                  ( (cast-unbox
                           (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))))))
              ( (cast-unbox (assocᴮ⁻ Γ B₂ Θ)))))
          ( (cast-unbox (castOf {Γ} {B₂} Θ))))))

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
  outerᴴ′ dec₁ dec₂ Θ H W₂ W₁ op ε ≡ innerᴴ′ dec₁ dec₂ Θ H W₂ W₁ op ε

------------------------------------------------------------------------
