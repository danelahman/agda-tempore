------------------------------------------------------------------------
-- Substitution against the term equivalence.                         --
--                                                                    --
-- `↝` respects `_≐ᶜ_` (needed for `Val-slice`, see                    --
-- `notes/adequacy-plan.md`) and almost every rule's reduct is a        --
-- substitution, so substitution must be a congruence for it.          --
--                                                                    --
-- The content is in the variable clauses: `⟨_,_⟩[_↦_]var` crosses a    --
-- lock by weakening along a renaming built from the *grade bound*, and --
-- two related terms carry different bounds — so the two sides are      --
-- renamed along different but `_≐ʳ_`-equal renamings.                  --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.SubEquivalence (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts      Spec
open import Syntax.Language      Spec
open import Syntax.RenActions    Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

open import OperationalSemantics.Adequacy.RenEquivalence Spec

-- ETERNAL VALUES
--
-- `eternal-val-ext` and `eternal-val-restrict` recurse on the value, and an
-- eternal type carries no arrow, so the `lam` case is impossible.

eternal-val-ext-cong : ∀ {Γ A ρ} → (et : Eternal A) → {V V' : Γ ⊢V⦂ A}
                     → V ≐ᵛ V'
                     → eternal-val-ext {ρ = ρ} et V ≐ᵛ eternal-val-ext et V'
eternal-val-ext-cong et            var-≐          = var-≐
eternal-val-ext-cong et            const-≐        = const-≐
eternal-val-ext-cong et            ⋆-≐            = ⋆-≐
eternal-val-ext-cong (et₁ |×|ₑ et₂) (pair-≐ e₁ e₂) =
  pair-≐ (eternal-val-ext-cong et₁ e₁) (eternal-val-ext-cong et₂ e₂)
eternal-val-ext-cong et (lam-≐ e) with et
... | ()

eternal-val-restrict-cong : ∀ {Γ A} → (et : Eternal A) → {V V' : Γ ⊢V⦂ A}
                          → V ≐ᵛ V'
                          → eternal-val-restrict et V ≐ᵛ eternal-val-restrict et V'
eternal-val-restrict-cong et            var-≐          = var-≐
eternal-val-restrict-cong et            const-≐        = const-≐
eternal-val-restrict-cong et            ⋆-≐            = ⋆-≐
eternal-val-restrict-cong (et₁ |×|ₑ et₂) (pair-≐ e₁ e₂) =
  pair-≐ (eternal-val-restrict-cong et₁ e₁) (eternal-val-restrict-cong et₂ e₂)
eternal-val-restrict-cong et (lam-≐ e) with et
... | ()

-- SUBSTITUTING INTO A VARIABLE
--
-- Induction on the two variables, mirroring `⟨_,_⟩[_↦_]var`. The lock case is
-- where the bounds enter: on the non-eternal side the two results are renamed
-- along `⟨⟩-≤-ren` at different proofs, related by `⟨⟩-≤-ren-≐` and transported
-- by `V-rename-≐`.

sub-var-≐ : ∀ {Γ A B ρ ρ'}
          → (y : B ∈[ ρ' ] Γ) → (f f' : ¬ Eternal B → ρ' ≾ᵣ uᵣ)
          → (x : A ∈[ ρ ] Γ) → {W W' : split-l x ⊢V⦂ A}
          → W ≐ᵛ W'
          --------------------------------------------------------
          → ⟨ y , f ⟩[ x ↦ W ]var ≐ᵛ ⟨ y , f' ⟩[ x ↦ W' ]var

sub-var-≐ Hd       f f' Hd       eW = eW
sub-var-≐ Hd       f f' (Tl-∷ x) eW = var-≐
sub-var-≐ (Tl-∷ y) f f' Hd       eW = var-≐
sub-var-≐ (Tl-∷ y) f f' (Tl-∷ x) eW =
  V-rename-cong wk-ren (sub-var-≐ y f f' x eW)
sub-var-≐ {B = B} (Tl-⟨⟩ y) f f' (Tl-⟨⟩ x) eW with eternal? B
... | yes p =
  eternal-val-ext-cong p
    (sub-var-≐ y (λ z → ≾ᵣ-zero-productˡ (f (λ _ → z p)))
                 (λ z → ≾ᵣ-zero-productˡ (f' (λ _ → z p))) x eW)
... | no ¬p =
  ≐ᵛ-trans
    (V-rename-≐ (∘ʳ-≐ (⟨⟩-≤-ren-≐ (≾ᵣ-zero-productʳ (f ¬p))
                                  (≾ᵣ-zero-productʳ (f' ¬p)))
                      (≐ʳ-refl {r = ⟨⟩-η⁻¹-ren}))
                ⟨ y , (λ z → ≾ᵣ-zero-productˡ (f z)) ⟩[ x ↦ _ ]var)
    (V-rename-cong (⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f' ¬p)) ∘ʳ ⟨⟩-η⁻¹-ren)
      (sub-var-≐ y (λ z → ≾ᵣ-zero-productˡ (f z))
                   (λ z → ≾ᵣ-zero-productˡ (f' z)) x eW))

-- SUBSTITUTING INTO A RESOURCE VARIABLE
--
-- `⟨_⟩[_↦_]rvar` returns a variable and a grade bound. Only the variable is
-- observable, and it depends on the substituted value solely through
-- `grad-typ⇒var`, which `_≐ᵛ_` pins down (related box-typed values are the same
-- variable).

rvar-tgt : ∀ {Γ A B ρ σ τ}
         → ([ ρ ] B ∈[ σ ] Γ) → (x : A ∈[ τ ] Γ) → split-l x ⊢V⦂ A
         → Tgt (split-l x ++ᶜ split-r x) ([ ρ ] B)
rvar-tgt y x W = proj₁ (⟨ y ⟩[ x ↦ W ]rvar) , proj₁ (proj₂ (⟨ y ⟩[ x ↦ W ]rvar))

sub-rvar-≐ : ∀ {Γ A B ρ σ τ}
           → (y : [ ρ ] B ∈[ σ ] Γ) → (x : A ∈[ τ ] Γ)
           → {W W' : split-l x ⊢V⦂ A} → W ≐ᵛ W'
           ----------------------------------------
           → rvar-tgt y x W ≡ rvar-tgt y x W'

sub-rvar-≐ Hd       Hd       eW with eW
sub-rvar-≐ Hd       Hd       eW | var-≐ = refl
sub-rvar-≐ Hd       (Tl-∷ x) eW = refl
sub-rvar-≐ (Tl-∷ y) Hd       eW = refl
sub-rvar-≐ (Tl-∷ y) (Tl-∷ x) eW =
  cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (sub-rvar-≐ y x eW)
sub-rvar-≐ (Tl-⟨⟩ y) (Tl-⟨⟩ x) eW =
  cong (λ z → proj₁ z ·ᵣ _ , Tl-⟨⟩ (proj₂ z)) (sub-rvar-≐ y x eW)

-- RETYPING AND THE `unbox` SMART CONSTRUCTOR

substᵛ-≐ : ∀ {A Γ₁ Γ₂} → (e : Γ₁ ≡ Γ₂) → {V V' : Γ₁ ⊢V⦂ A}
         → V ≐ᵛ V' → subst (_⊢V⦂ A) e V ≐ᵛ subst (_⊢V⦂ A) e V'
substᵛ-≐ refl eV = eV

substᶜ-≐ : ∀ {C Γ₁ Γ₂} → (e : Γ₁ ≡ Γ₂) → {M M' : Γ₁ ⊢C⦂ C}
         → M ≐ᶜ M' → subst (_⊢C⦂ C) e M ≐ᶜ subst (_⊢C⦂ C) e M'
substᶜ-≐ refl eM = eM

substᶜ-≐′ : (f : Ctx → Ctx) → ∀ {C Γ₁ Γ₂} → (e : Γ₁ ≡ Γ₂) → {M M' : f Γ₁ ⊢C⦂ C}
          → M ≐ᶜ M'
          → subst (λ z → f z ⊢C⦂ C) e M ≐ᶜ subst (λ z → f z ⊢C⦂ C) e M'
substᶜ-≐′ f refl eM = eM

-- `unbox-var` stores its grade bound inside a `⟨⟩-≤-ren`, so it is a congruence
-- at differing bounds.

unbox-var-≐ : ∀ {Γ A C ρ ρ'} → (x : [ ρ ] A ∈[ ρ' ] Γ)
            → (rel rel' : ρ' ≾ᵣ ρ) → {M M' : Γ ∷ A ⊢C⦂ C}
            → M ≐ᶜ M'
            → unbox-var x rel M ≐ᶜ unbox-var x rel' M'
unbox-var-≐ x rel rel' eM =
  unbox-≐ (unbox-tgt-≐
             (∘ʳ-≐ (≐ʳ-refl {r = eq-ren (split-≡ (split-pf x))})
               (∘ʳ-≐ (≐ʳ-refl {r = wk-ren-⟨ρ⟩-ctx (split-grade-≡ x)})
                     (⟨⟩-≤-ren-≐ rel rel')))
             (var (λ _ → ≾ᵣ-refl) Hd))
          eM

------------------------------------------------------------------------
-- SUBSTITUTION IS A CONGRUENCE
--
-- Induction on the relation; the substituted variable and value vary, so the
-- `handle` case can recurse at the clause variable `split→∈ s`.
------------------------------------------------------------------------

mutual

  sub-≐ᵛ : ∀ {Γ A B ρ} → (x : A ∈[ ρ ] Γ) → {W W' : split-l x ⊢V⦂ A}
         → W ≐ᵛ W' → {V V' : Γ ⊢V⦂ B} → V ≐ᵛ V'
         → (V [ x ↦ W ]v) ≐ᵛ (V' [ x ↦ W' ]v)

  sub-≐ᵛ x eW (var-≐ {f = f} {f' = f'} {x = y}) = sub-var-≐ y f f' x eW
  sub-≐ᵛ x eW const-≐          = const-≐
  sub-≐ᵛ x eW ⋆-≐              = ⋆-≐
  sub-≐ᵛ x eW (pair-≐ e₁ e₂)   = pair-≐ (sub-≐ᵛ x eW e₁) (sub-≐ᵛ x eW e₂)
  sub-≐ᵛ x eW (lam-≐ eM)       = lam-≐ (sub-≐ᶜ (Tl-∷ x) eW eM)

  sub-≐ᶜ : ∀ {Γ A C ρ} → (x : A ∈[ ρ ] Γ) → {W W' : split-l x ⊢V⦂ A}
         → W ≐ᵛ W' → {M M' : Γ ⊢C⦂ C} → M ≐ᶜ M'
         → (M [ x ↦ W ]c) ≐ᶜ (M' [ x ↦ W' ]c)

  sub-≐ᶜ x eW (return-≐ eV)     = return-≐ (sub-≐ᵛ x eW eV)
  sub-≐ᶜ x eW (seq-≐ eM eN)     =
    seq-≐ (sub-≐ᶜ x eW eM) (sub-≐ᶜ (Tl-∷ (Tl-⟨⟩ x)) eW eN)
  sub-≐ᶜ x eW (app-≐ eV eU)     = app-≐ (sub-≐ᵛ x eW eV) (sub-≐ᵛ x eW eU)
  sub-≐ᶜ x eW (match-≐ eV eM)   =
    match-≐ (sub-≐ᵛ x eW eV) (sub-≐ᶜ (Tl-∷ (Tl-∷ x)) eW eM)
  sub-≐ᶜ x eW (absurd-≐ eV)     = absurd-≐ (sub-≐ᵛ x eW eV)
  sub-≐ᶜ x eW (perform-≐ eV eM) =
    perform-≐ (sub-≐ᵛ x eW eV) (sub-≐ᶜ (Tl-∷ (Tl-⟨⟩ x)) eW eM)
  sub-≐ᶜ x eW (delay-≐ eM)      = delay-≐ (sub-≐ᶜ (Tl-⟨⟩ x) eW eM)
  sub-≐ᶜ x eW (coerce-≐ eM)     = coerce-≐ (sub-≐ᶜ x eW eM)
  sub-≐ᶜ x eW (box-≐ eV eM)     =
    box-≐ (sub-≐ᵛ (Tl-⟨⟩ x) eW eV) (sub-≐ᶜ (Tl-∷ x) eW eM)

  -- the clauses close over `Γ ᴱ`: if the substituted variable is not eternal it
  -- does not occur there and they are only retyped; if it is, its value
  -- restricts and is substituted into each clause
  sub-≐ᶜ {A = A} x eW (handle-≐ {B = B} eM eH eN) with eternal? A
  ... | no ¬et =
    handle-≐ (sub-≐ᶜ x eW eM)
      (λ op ε'' Γ' →
         substᶜ-≐′
           (λ Γ₀ → Γ₀ ++ᶜ Γ' ∷ type-of-gtype (param op)
                     ∷ [ mapᵉ (op-grade op) ]
                         (type-of-gtype (arity op) ⇒ B ‼ ε''))
           (ᴱ-drop-split ¬et x) (eH op ε'' Γ'))
      (sub-≐ᶜ (Tl-∷ (Tl-⟨⟩ x)) eW eN)
  ... | yes et =
    handle-≐ (sub-≐ᶜ x eW eM)
      (λ op ε'' Γ' →
         substᶜ-≐ _
           (sub-≐ᶜ (split→∈ (split-++ʳ (∈-ᴱ-split et x) _))
                   (substᵛ-≐ _ (eternal-val-restrict-cong et eW))
                   (eH op ε'' Γ')))
      (sub-≐ᶜ (Tl-∷ (Tl-⟨⟩ x)) eW eN)

  -- the underlying resource variable is recovered by `unbox⇒var`, pushed through
  -- `⟨_⟩[_↦_]rvar` and rebuilt by `unbox-var`; only the grade bounds differ
  sub-≐ᶜ x {W} {W'} eW (unbox-≐ {w = w} {w' = w'} {V = V} {V' = V'} hw eM)
    with grad-typ⇒var V | grad-typ⇒var V'
  ... | _ , y , f , refl | _ , y' , f' , refl
    with var-rename w (Tl-⟨⟩ y) | var-rename w' (Tl-⟨⟩ y') | hw
  ...   | _ , _ , z | _ , _ , _ | refl
    with ⟨ z ⟩[ x ↦ W ]rvar | ⟨ z ⟩[ x ↦ W' ]rvar | sub-rvar-≐ z x eW
  ...     | _ , v , p | _ , _ , p' | refl =
    unbox-var-≐ v (≾ᵣ-trans p _) (≾ᵣ-trans p' _) (sub-≐ᶜ (Tl-∷ x) eW eM)
