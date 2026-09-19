------------------------------------------------------------------------
-- Substituting at the prefix boundary.                                --
--                                                                     --
-- Replacing the entry sitting between `Γ'` and a suffix `Θ` by a      --
-- value over `Γ'`, presenting the result over `Γ' ++ᶜ Θ`. This is the --
-- form every consumer of substitution actually uses: the one          --
-- substitution operator at the splitting `split-≡-++ᶜ`.               --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions.At (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.RenActions    S
open import Syntax.Renamings     S
open import Syntax.Substitutions S
open import Syntax.Types         S

open import Syntax.Renamings.Equivalence S
open import Syntax.Renamings.Coherence   S
open import Syntax.Terms.Equivalence     S
open import Syntax.Terms.Transport       S

open import Syntax.Substitutions.Base             S
open import Syntax.Substitutions.Lookup           S
open import Syntax.Substitutions.Action           S
open import Syntax.Substitutions.Equivalence      S
open import Syntax.Substitutions.Interchange      S
open import Syntax.Substitutions.Chain            S
open import Syntax.Substitutions.ChainEquivalence S
open import Syntax.Substitutions.Laws             S
open import Syntax.Substitutions.Variables        S

C-rename-castᶜ : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → (M : Γ ⊢C⦂ C)
               → C-rename (eq-ren e) M ≡ castᶜ e M
C-rename-castᶜ refl M = C-rename-id-≡ ≐ʳ-refl M

-- The boundary is the splitting `split-≡-++ᶜ`, whose halves are the prefix and
-- suffix as given: these four are the one substitution operator, at that
-- splitting.

sub-atᵛ : ∀ {Γ' B A} → (Θ : Ctx) → ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A → Γ' ⊢V⦂ B
        → (Γ' ++ᶜ Θ) ⊢V⦂ A
sub-atᵛ {Γ'} {B} Θ U W = U [ split-≡-++ᶜ {Γ' ∷ B} {Θ} ↦ W ]v

sub-atᶜ : ∀ {Γ' B C} → (Θ : Ctx) → ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C → Γ' ⊢V⦂ B
        → (Γ' ++ᶜ Θ) ⊢C⦂ C
sub-atᶜ {Γ'} {B} Θ M W = M [ split-≡-++ᶜ {Γ' ∷ B} {Θ} ↦ W ]c

sub-atᴿ : ∀ {Γ' B A ρ σ} → (Θ : Ctx)
        → ([ ρ ] A ∈[ σ ] ((Γ' ∷ B) ++ᶜ Θ)) → Γ' ⊢V⦂ B
        → Σ[ σ' ∈ R ] (([ ρ ] A ∈[ σ' ] (Γ' ++ᶜ Θ)) × (σ' ≾ᵣ σ))
sub-atᴿ {Γ'} {B} Θ z W = ⟨ z ⟩[ split-≡-++ᶜ {Γ' ∷ B} {Θ} ↦ W ]rvar

sub-atᴴ : ∀ {Γ' B D} → (Θ : Ctx) → Fam D (((Γ' ∷ B) ++ᶜ Θ) ⟨ ⊤ᵣ ⟩) → Γ' ⊢V⦂ B
        → Fam D ((Γ' ++ᶜ Θ) ⟨ ⊤ᵣ ⟩)
sub-atᴴ {Γ'} {B} Θ H W = H [ split-≡-++ᶜ {Γ' ∷ B} {Θ} ↦ W ]cl

-- Congruences, at that splitting.

sub-atᵛ-≡ : ∀ {Γ' B A} → (Θ : Ctx) → {U U' : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A}
          → (W : Γ' ⊢V⦂ B) → U ≡ U' → sub-atᵛ Θ U W ≡ sub-atᵛ Θ U' W
sub-atᵛ-≡ Θ W e = sub-≡ᵛ split-≡-++ᶜ refl e

sub-atᶜ-≡ : ∀ {Γ' B C} → (Θ : Ctx) → {M M' : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C}
          → (W : Γ' ⊢V⦂ B) → M ≡ M' → sub-atᶜ Θ M W ≡ sub-atᶜ Θ M' W
sub-atᶜ-≡ Θ W e = sub-≡ᶜ split-≡-++ᶜ refl e

sub-atᶜ-≡ᵥ : ∀ {Γ' B C} → (Θ : Ctx) → (X : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C)
           → {W W' : Γ' ⊢V⦂ B} → W ≡ W'
           → sub-atᶜ Θ X W ≡ sub-atᶜ Θ X W'
sub-atᶜ-≡ᵥ Θ X refl = refl

-- `≡-split refl` recurses on the suffix exactly as `cong-sub₀` does, so the
-- substitution at the boundary is `cong-sub₀ (val-sub W)`, by induction.

sub-at-≡ˢ₀ : ∀ {Γ B} → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
           → sub-atˢ₀ {B = B} Θ W ≡ cong-sub₀ {Γ'' = Θ} (val-sub W)
sub-at-≡ˢ₀ []        W = refl
sub-at-≡ˢ₀ (Θ ∷ A)   W = cong cong-∷-sub  (sub-at-≡ˢ₀ Θ W)
sub-at-≡ˢ₀ (Θ ⟨ ρ ⟩) W = cong cong-⟨⟩-sub (sub-at-≡ˢ₀ Θ W)

-- Hence what the boundary substitution does to a term.

sub-at-≡ᵛ : ∀ {Γ B A} → (Θ : Ctx) → (U : ((Γ ∷ B) ++ᶜ Θ) ⊢V⦂ A) → (W : Γ ⊢V⦂ B)
          → U [ split-≡-++ᶜ {Γ ∷ B} {Θ} ↦ W ]v
          ≡ V-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub W)) U
sub-at-≡ᵛ Θ U W = cong (λ s → V-sub₀ s U) (sub-at-≡ˢ₀ Θ W)

sub-at-≡ᶜ : ∀ {Γ B C} → (Θ : Ctx) → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ C) → (W : Γ ⊢V⦂ B)
          → M [ split-≡-++ᶜ {Γ ∷ B} {Θ} ↦ W ]c
          ≡ C-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub W)) M
sub-at-≡ᶜ Θ M W = cong (λ s → C-sub₀ s M) (sub-at-≡ˢ₀ Θ W)

-- `sub-wk`: weakening at the boundary and then substituting there is the
-- identity.

sub-wk-V : ∀ {Γ B} → (Θ : Ctx) → ∀ {A} → (U : (Γ ++ᶜ Θ) ⊢V⦂ A) → (W : Γ ⊢V⦂ B)
         → (V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) U)
             [ split-≡-++ᶜ {Γ ∷ B} {Θ} ↦ W ]v
         ≡ U
sub-wk-V {B = B} Θ U W =
  trans (sub-at-≡ᵛ Θ (V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) U) W)
        (sub-wk-≡ᵛ Θ W U)

sub-wk-C : ∀ {Γ B} → (Θ : Ctx) → ∀ {C} → (M : (Γ ++ᶜ Θ) ⊢C⦂ C) → (W : Γ ⊢V⦂ B)
         → (C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) M)
             [ split-≡-++ᶜ {Γ ∷ B} {Θ} ↦ W ]c
         ≡ M
sub-wk-C {B = B} Θ M W =
  trans (sub-at-≡ᶜ Θ (C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) M) W)
        (sub-wk-≡ᶜ Θ W M)

-- The same with the term's context given by an equation rather than literally.

sub-wk-C-cast : ∀ {Γ B Γ₀} → (Θ : Ctx) → (e : Γ₀ ≡ Γ ++ᶜ Θ) → ∀ {C}
              → (M : Γ₀ ⊢C⦂ C) → (W : Γ ⊢V⦂ B)
              → (C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                   (subst (_⊢C⦂ C) e M))
                  [ split-≡-++ᶜ {Γ ∷ B} {Θ} ↦ W ]c
              ≡ subst (_⊢C⦂ C) e M
sub-wk-C-cast Θ refl M W = sub-wk-C Θ M W

-- `outer` replaces `B₂` (its value weakened past `B₁`) and then `B₁`;
-- `inner` replaces `B₁`, with `B₂` re-bracketed into the suffix, and then
-- `B₂`. The re-bracketing is `++ᶜ-assoc`, so only `inner₀` carries casts.

assocᴮ : (Γ : Ctx) → (B₁ B₂ : VType) → (Θ : Ctx)
       → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ≡ ((Γ ∷ B₁) ++ᶜ (([] ∷ B₂) ++ᶜ Θ))
assocᴮ Γ B₁ B₂ Θ = ++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ

assocᴮ⁻ : (Γ : Ctx) → (B₂ : VType) → (Θ : Ctx)
        → (Γ ++ᶜ (([] ∷ B₂) ++ᶜ Θ)) ≡ ((Γ ∷ B₂) ++ᶜ Θ)
assocᴮ⁻ Γ B₂ Θ = sym (++ᶜ-assoc Γ ([] ∷ B₂) Θ)

outerᶜ : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → (Γ ++ᶜ Θ) ⊢C⦂ C
outerᶜ {Γ} {B₁} {B₂} Θ M W₂ W₁ =
  (M [ split-≡-++ᶜ {Γ ∷ B₁ ∷ B₂} {Θ} ↦ V-rename (wk-ren {A = B₁}) W₂ ]c)
    [ split-≡-++ᶜ {Γ ∷ B₁} {Θ} ↦ W₁ ]c

inner₀ᶜ : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
        → Γ ⊢V⦂ B₁ → ((Γ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
inner₀ᶜ {Γ} {B₁} {B₂} Θ M W₁ =
  castᶜ (assocᴮ⁻ Γ B₂ Θ)
    ((castᶜ (assocᴮ Γ B₁ B₂ Θ) M)
       [ split-≡-++ᶜ {Γ ∷ B₁} {([] ∷ B₂) ++ᶜ Θ} ↦ W₁ ]c)

innerᶜ : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → (Γ ++ᶜ Θ) ⊢C⦂ C
innerᶜ {Γ} {B₂ = B₂} Θ M W₂ W₁ =
  (inner₀ᶜ Θ M W₁) [ split-≡-++ᶜ {Γ ∷ B₂} {Θ} ↦ W₂ ]c

-- `inner₀`'s two casts conjugate the substitution at the re-bracketed suffix
-- into the one under `Θ` alone.

assoc-≐ˢ : ∀ {Γ B₁ B₂} → (Θ : Ctx) → (W₁ : Γ ⊢V⦂ B₁)
         → (⌜ eq-ren (assocᴮ⁻ Γ B₂ Θ) ⌝
            ◅ cong-sub₀ {Γ'' = ([] ∷ B₂) ++ᶜ Θ} (val-sub W₁)
            ◅ ⌜ eq-ren (assocᴮ Γ B₁ B₂ Θ) ⌝
            ◅ []ˢ)
         ≐ˢ [ cong-sub₀ {Γ'' = Θ} (cong-∷-sub {A = B₂} (val-sub W₁)) ]ˢ

assoc-≐ˢ {Γ} {B₁} {B₂} [] W₁ =
  ≐ˢ-trans (◅-tail-≐ˢ _ (◅-tail-≐ˢ _ (id-◅-≐ˢ (eq-ren-≐ʳ _ refl) []ˢ)))
           (id-◅-≐ˢ (eq-ren-≐ʳ _ refl) _)

assoc-≐ˢ {Γ} {B₁} {B₂} (Θ ∷ A) W₁ =
  ≐ˢ-trans
    (≐ˢ-trans (◅-tail-≐ˢ _ (◅-tail-≐ˢ _
                 (◅-≐ˢ₀ (eq-ren-∷-≐ˢ₀ (assocᴮ Γ B₁ B₂ Θ)
                                      (assocᴮ Γ B₁ B₂ (Θ ∷ A))) []ˢ)))
              (◅-≐ˢ₀ (eq-ren-∷-≐ˢ₀ (assocᴮ⁻ Γ B₂ Θ) (assocᴮ⁻ Γ B₂ (Θ ∷ A))) _))
    (cong-∷-subˢ-≐ˢ (assoc-≐ˢ Θ W₁))

assoc-≐ˢ {Γ} {B₁} {B₂} (Θ ⟨ ρ ⟩) W₁ =
  ≐ˢ-trans
    (≐ˢ-trans (◅-tail-≐ˢ _ (◅-tail-≐ˢ _
                 (◅-≐ˢ₀ (eq-ren-⟨⟩-≐ˢ₀ (assocᴮ Γ B₁ B₂ Θ)
                                       (assocᴮ Γ B₁ B₂ (Θ ⟨ ρ ⟩))) []ˢ)))
              (◅-≐ˢ₀ (eq-ren-⟨⟩-≐ˢ₀ (assocᴮ⁻ Γ B₂ Θ)
                                    (assocᴮ⁻ Γ B₂ (Θ ⟨ ρ ⟩))) _))
    (cong-⟨⟩-subˢ-≐ˢ (assoc-≐ˢ Θ W₁))

-- Hence what `inner₀` does to a term.

inner₀-≡ᶜ : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C)
          → (W₁ : Γ ⊢V⦂ B₁)
          → inner₀ᶜ {B₂ = B₂} Θ M W₁
          ≡ C-sub₀ (cong-sub₀ {Γ'' = Θ} (cong-∷-sub {A = B₂} (val-sub W₁))) M
inner₀-≡ᶜ {Γ} {B₁} {B₂} Θ M W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
              (trans (sub-≡ᶜ (split-≡-++ᶜ {Γ ∷ B₁} {([] ∷ B₂) ++ᶜ Θ}) refl
                       (sym (C-rename-castᶜ (assocᴮ Γ B₁ B₂ Θ) M)))
                     (sub-at-≡ᶜ (([] ∷ B₂) ++ᶜ Θ)
                                (C-rename (eq-ren (assocᴮ Γ B₁ B₂ Θ)) M) W₁)))
    (trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
                 (cong (C-sub₀ (cong-sub₀ {Γ'' = ([] ∷ B₂) ++ᶜ Θ} (val-sub W₁)))
                       (sym (C-sub₀-⌜⌝ (eq-ren (assocᴮ Γ B₁ B₂ Θ)) M))))
      (trans (sym (C-rename-castᶜ (assocᴮ⁻ Γ B₂ Θ) _))
        (trans (sym (C-sub₀-⌜⌝ (eq-ren (assocᴮ⁻ Γ B₂ Θ)) _))
               (C-sub-≐ˢ (assoc-≐ˢ Θ W₁) M))))

-- `sub-swap`: both orders are now `cong-sub₀ (val-sub _)` composites; the
-- theorem is `sub-swap-at-≡ᶜ` with the outer value read back by `sub-wk`:
-- substituting `W₁` into `W₂` weakened past `B₁` gives `W₂` again.

SubSwapC : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
         → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → Set
SubSwapC Θ M W₂ W₁ = outerᶜ Θ M W₂ W₁ ≡ innerᶜ Θ M W₂ W₁

sub-swap-C : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C)
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
           → SubSwapC Θ M W₂ W₁
sub-swap-C {Γ} {B₁} {B₂} Θ M W₂ W₁ =
  trans (trans (sub-≡ᶜ (split-≡-++ᶜ {Γ ∷ B₁} {Θ}) refl
                 (sub-at-≡ᶜ Θ M (V-rename (wk-ren {A = B₁}) W₂)))
               (sub-at-≡ᶜ Θ (C-sub₀ (cong-sub₀ {Γ'' = Θ}
                               (val-sub (V-rename (wk-ren {A = B₁}) W₂))) M) W₁))
    (trans (sub-swap-at-≡ᶜ Θ W₁ (V-rename (wk-ren {A = B₁}) W₂) M)
      (trans (cong (λ V → C-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub V))
                                 (C-sub₀ (cong-sub₀ {Γ'' = Θ}
                                            (cong-∷-sub (val-sub W₁))) M))
                   (sub-wk-≡ᵛ [] W₁ W₂))
             (sym (trans (sub-≡ᶜ (split-≡-++ᶜ {Γ ∷ B₂} {Θ}) refl
                            (inner₀-≡ᶜ Θ M W₁))
                         (sub-at-≡ᶜ Θ (C-sub₀ (cong-sub₀ {Γ'' = Θ}
                                         (cong-∷-sub (val-sub W₁))) M) W₂)))))
