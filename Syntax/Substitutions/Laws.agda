------------------------------------------------------------------------
-- The substitution laws, as equations between substitutions.         --
--                                                                    --
-- Each is a `_≐ˢ_` equation between composites, so its proof is a     --
-- calculation on variables; `V-sub-≐ˢ` carries it to terms.           --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions.Laws (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.RenActions S
open import Syntax.Renamings  S
open import Syntax.Subtyping  S
open import Syntax.Types      S

open import Syntax.Renamings.Equivalence S
open import Syntax.Renamings.Coherence   S
open import Syntax.Terms.Equivalence     S

open import Syntax.Substitutions.Base             S
open import Syntax.Substitutions.Lookup           S
open import Syntax.Substitutions.Action           S
open import Syntax.Substitutions.Equivalence      S
open import Syntax.Substitutions.Interchange      S
open import Syntax.Substitutions.Chain            S
open import Syntax.Substitutions.ChainEquivalence S

-- Substituting a value for the variable a suffix `Θ` stands over, and the
-- weakening that introduces that variable.

sub-atˢ : ∀ {Γ B} → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
        → Sub [] (Γ ++ᶜ Θ) ((Γ ∷ B) ++ᶜ Θ)
sub-atˢ Θ W = [ cong-sub₀ {Γ'' = Θ} (val-sub W) ]ˢ

wkˢ : ∀ {Γ B} → (Θ : Ctx) → Sub [] ((Γ ∷ B) ++ᶜ Θ) (Γ ++ᶜ Θ)
wkˢ {B = B} Θ = ⌜ cong-ren {Γ'' = Θ} (wk-ren {A = B}) ⌝ˢ

-- `sub-wk`: weakening and then substituting is the identity. On a variable
-- the weakening lands to the right of the substituted one, so the
-- substitution passes it through.

sub-wk-var : ∀ {Γ B A ρ} → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
           → (x : A ∈[ ρ ] (Γ ++ᶜ Θ))
           → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
           → (f' : ¬ Eternal A
                 → proj₁ (var-img (cong-ren {Γ'' = Θ} (wk-ren {A = B})) x) ≾ᵣ uᵣ)
           → sub-var₀ (cong-sub₀ {Γ'' = Θ} (val-sub W))
                      (proj₂ (var-img (cong-ren {Γ'' = Θ} (wk-ren {A = B})) x)) f'
           ≡ var f x

sub-wk-var []        W x        f f' = var-≡
sub-wk-var (Θ ∷ C)   W Hd       f f' = var-≡
sub-wk-var (Θ ∷ C)   W (Tl-∷ y) f f' =
  trans (cong (V-rename wk-ren) (sub-wk-var Θ W y f _)) var-≡
sub-wk-var {A = A} (Θ ⟨ ρ ⟩) W (Tl-⟨⟩ y) f f' with eternal? A
... | yes et =
  trans (cong (eternal-val-ext et) (sub-wk-var Θ W y (et-bound et) _)) var-≡
... | no ¬et =
  trans (cong (V-rename (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f' ¬et))))
              (sub-wk-var Θ W y (λ q → ≾ᵣ-zero-productˡ (f q)) _))
        (var-img-≡ (hit-⟨⟩-img (≾ᵣ-zero-productʳ (f' ¬et)) y) _ _)

sub-wk-tgt : ∀ {Γ B A ρ ρ'} → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
           → (y : [ ρ ] A ∈[ ρ' ] (Γ ++ᶜ Θ))
           → tgt-img₀ (cong-sub₀ {Γ'' = Θ} (val-sub W))
                      (proj₂ (var-img (cong-ren {Γ'' = Θ} (wk-ren {A = B})) y))
           ≡ (ρ , A , ρ' , y)

sub-wk-tgt []          W y         = refl
sub-wk-tgt (Θ ∷ C)     W Hd        = refl
sub-wk-tgt (Θ ∷ C)     W (Tl-∷ z)  = cong RVar-∷ (sub-wk-tgt Θ W z)
sub-wk-tgt (Θ ⟨ ρ ⟩)   W (Tl-⟨⟩ z) = cong (RVar-⟨⟩ ρ) (sub-wk-tgt Θ W z)

-- The law itself.

sub-wk-≐ˢ : ∀ {Γ B} → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
          → (wkˢ {B = B} Θ ∘ˢ sub-atˢ Θ W) ≐ˢ []ˢ
sub-wk-≐ˢ Θ W = mk≐ˢ (λ x f → sub-wk-var Θ W x f _) (λ y → sub-wk-tgt Θ W y)

-- and what it says about terms.

sub-wk-≡ᵛ : ∀ {Γ B A} → (Θ : Ctx) → (W : Γ ⊢V⦂ B) → (V : (Γ ++ᶜ Θ) ⊢V⦂ A)
          → V-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub W))
                   (V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) V)
          ≡ V
sub-wk-≡ᵛ {B = B} Θ W V =
  trans (cong (V-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub W)))
              (sym (V-sub₀-⌜⌝ (cong-ren {Γ'' = Θ} (wk-ren {A = B})) V)))
        (V-sub-≐ˢ (sub-wk-≐ˢ Θ W) V)

sub-wk-≡ᶜ : ∀ {Γ B C} → (Θ : Ctx) → (W : Γ ⊢V⦂ B) → (M : (Γ ++ᶜ Θ) ⊢C⦂ C)
          → C-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub W))
                   (C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) M)
          ≡ M
sub-wk-≡ᶜ {B = B} Θ W M =
  trans (cong (C-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub W)))
              (sym (C-sub₀-⌜⌝ (cong-ren {Γ'' = Θ} (wk-ren {A = B})) M)))
        (C-sub-≐ˢ (sub-wk-≐ˢ Θ W) M)

-- `ren-sub`: substituting commutes with renaming, an instance of the
-- interchange. At the empty suffix the premise is a two-case check on the
-- substituted variable, and `⋈-cong` carries it under an arbitrary suffix.

-- A box-typed value is a variable up to subsumption, so renaming it is
-- renaming that variable.

val-sub-tgt-ren : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → (W : Γ' ⊢V⦂ [ ρ ] A)
                → tgt-img₀ (val-sub (V-rename r W)) Hd
                ≡ rvar-img′ r (tgt-img₀ (val-sub W) Hd)
val-sub-tgt-ren r (var g z)  = refl
val-sub-tgt-ren r (subV V p) with <:ᵛ-shape p
... | Boxˢ = val-sub-tgt-ren r V

⋈-val : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (W : Γ' ⊢V⦂ B)
      → Interchange (val-sub (V-rename r W)) (cong-∷-ren r) r (val-sub W)
⋈-val {Γ} {Γ'} {B} r W = mk⋈ goᵛ goᵗ
  where
    goᵛ : ∀ {A ρ} → (x : A ∈[ ρ ] (Γ' ∷ B)) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
        → V-sub₀ (val-sub (V-rename r W)) (V-rename (cong-∷-ren r) (var f x))
        ≡ V-rename r (V-sub₀ (val-sub W) (var f x))
    goᵛ Hd       f = refl
    goᵛ (Tl-∷ y) f = var-≡

    goᵗ : ∀ {A ρ ρ'} → (y : [ ρ ] A ∈[ ρ' ] (Γ' ∷ B))
        → tgt-img₀ (val-sub (V-rename r W)) (proj₂ (var-img (cong-∷-ren r) y))
        ≡ rvar-img′ r (tgt-img₀ (val-sub W) y)
    goᵗ Hd       = val-sub-tgt-ren r W
    goᵗ (Tl-∷ z) = refl

ren-sub-≡ᵛ : ∀ {Γ Γ' B A} → (Θ : Ctx) → (r : Ren [] Γ Γ') → (W : Γ' ⊢V⦂ B)
           → (V : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A)
           → V-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub (V-rename r W)))
                    (V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) V)
           ≡ V-rename (cong-ren {Γ'' = Θ} r)
                      (V-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub W)) V)
ren-sub-≡ᵛ Θ r W V = V-sub₀-ren (⋈-cong Θ (⋈-val r W)) V

ren-sub-≡ᶜ : ∀ {Γ Γ' B C} → (Θ : Ctx) → (r : Ren [] Γ Γ') → (W : Γ' ⊢V⦂ B)
           → (M : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C)
           → C-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub (V-rename r W)))
                    (C-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) M)
           ≡ C-rename (cong-ren {Γ'' = Θ} r)
                      (C-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub W)) M)
ren-sub-≡ᶜ Θ r W M = C-sub₀-ren (⋈-cong Θ (⋈-val r W)) M

-- `sub-swap`: substituting for two variables in either order.
--
-- Substituting `W₂` for the top variable and then `W₁` for the one beneath it
-- agrees with substituting `W₁` under the top binder and then `W₂` with `W₁`
-- already put in. Two 2-chains with the same endpoints, so the law is a `≐ˢ`
-- equation.

swap-innerˢ : ∀ {Γ B₁ B₂} → (W₁ : Γ ⊢V⦂ B₁) → (W₂ : Γ ∷ B₁ ⊢V⦂ B₂)
            → Sub [] Γ ((Γ ∷ B₁) ∷ B₂)
swap-innerˢ W₁ W₂ = val-sub W₁ ◅ [ val-sub W₂ ]ˢ

swap-outerˢ : ∀ {Γ B₁ B₂} → (W₁ : Γ ⊢V⦂ B₁) → (W₂ : Γ ∷ B₁ ⊢V⦂ B₂)
            → Sub [] Γ ((Γ ∷ B₁) ∷ B₂)
swap-outerˢ W₁ W₂ =
  val-sub (V-sub₀ (val-sub W₁) W₂) ◅ [ cong-∷-sub (val-sub W₁) ]ˢ

-- The one case with content beyond the variable calculus: the substituted
-- value is of box type, hence a variable up to subsumption, and where that
-- variable goes is decided by whether it is the one `W₁` replaces.

swap-tgt-Hd : ∀ {Γ B₁ A ρ} → (W₁ : Γ ⊢V⦂ B₁) → (W₂ : Γ ∷ B₁ ⊢V⦂ [ ρ ] A)
            → tgt-img₀ (val-sub W₁) (rvar-pos (tgt-img₀ (val-sub W₂) Hd))
            ≡ tgt-img₀ (val-sub (V-sub₀ (val-sub W₁) W₂)) Hd
swap-tgt-Hd W₁ (var g Hd)       = refl
swap-tgt-Hd W₁ (var g (Tl-∷ y)) = refl
swap-tgt-Hd W₁ (subV V p) with <:ᵛ-shape p
... | Boxˢ = swap-tgt-Hd W₁ V

sub-swap-≐ˢ : ∀ {Γ B₁ B₂} → (W₁ : Γ ⊢V⦂ B₁) → (W₂ : Γ ∷ B₁ ⊢V⦂ B₂)
            → swap-innerˢ W₁ W₂ ≐ˢ swap-outerˢ W₁ W₂
sub-swap-≐ˢ {Γ} {B₁} {B₂} W₁ W₂ = mk≐ˢ goᵛ goᵗ
  where
    goᵛ : ∀ {A ρ} → (x : A ∈[ ρ ] ((Γ ∷ B₁) ∷ B₂)) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
        → sub-var (swap-innerˢ W₁ W₂) x f ≡ sub-var (swap-outerˢ W₁ W₂) x f
    goᵛ Hd              f = refl
    goᵛ (Tl-∷ Hd)       f = sym (sub-wk-≡ᵛ [] (V-sub₀ (val-sub W₁) W₂) W₁)
    goᵛ (Tl-∷ (Tl-∷ y)) f = var-≡

    goᵗ : ∀ {A ρ ρ'} → (y : [ ρ ] A ∈[ ρ' ] ((Γ ∷ B₁) ∷ B₂))
        → tgt-img (swap-innerˢ W₁ W₂) y ≡ tgt-img (swap-outerˢ W₁ W₂) y
    goᵗ Hd              = swap-tgt-Hd W₁ W₂
    goᵗ (Tl-∷ Hd)       = refl
    goᵗ (Tl-∷ (Tl-∷ z)) = refl

-- and what it says about terms.

sub-swap-≡ᵛ : ∀ {Γ B₁ B₂ A} → (W₁ : Γ ⊢V⦂ B₁) → (W₂ : Γ ∷ B₁ ⊢V⦂ B₂)
            → (V : (Γ ∷ B₁) ∷ B₂ ⊢V⦂ A)
            → V-sub₀ (val-sub W₁) (V-sub₀ (val-sub W₂) V)
            ≡ V-sub₀ (val-sub (V-sub₀ (val-sub W₁) W₂))
                     (V-sub₀ (cong-∷-sub (val-sub W₁)) V)
sub-swap-≡ᵛ W₁ W₂ V = V-sub-≐ˢ (sub-swap-≐ˢ W₁ W₂) V

sub-swap-≡ᶜ : ∀ {Γ B₁ B₂ C} → (W₁ : Γ ⊢V⦂ B₁) → (W₂ : Γ ∷ B₁ ⊢V⦂ B₂)
            → (M : (Γ ∷ B₁) ∷ B₂ ⊢C⦂ C)
            → C-sub₀ (val-sub W₁) (C-sub₀ (val-sub W₂) M)
            ≡ C-sub₀ (val-sub (V-sub₀ (val-sub W₁) W₂))
                     (C-sub₀ (cong-∷-sub (val-sub W₁)) M)
sub-swap-≡ᶜ W₁ W₂ M = C-sub-≐ˢ (sub-swap-≐ˢ W₁ W₂) M

-- `sub-swap` under a suffix: both orders live under the same suffix `Θ`, so
-- the law at `Θ` is the law at the top two variables with `cong-subˢ Θ`
-- applied to it. `cong-subˢ` distributes over a chain, so nothing about the
-- suffix has to be re-examined.

cong-subˢ-◅ : ∀ {Ξ Δ Δ' Δ''} → (Γ₀ : Ctx)
            → (s₁ : Sub₀ Ξ Δ Δ') → (s₂ : Sub₀ Ξ Δ' Δ'')
            → cong-subˢ {Γ'' = Γ₀} (s₁ ◅ [ s₂ ]ˢ)
            ≡ (cong-sub₀ {Γ'' = Γ₀} s₁ ◅ [ cong-sub₀ {Γ'' = Γ₀} s₂ ]ˢ)
cong-subˢ-◅ []         s₁ s₂ = refl
cong-subˢ-◅ (Γ₀ ∷ A)   s₁ s₂ = cong cong-∷-subˢ (cong-subˢ-◅ Γ₀ s₁ s₂)
cong-subˢ-◅ (Γ₀ ⟨ ρ ⟩) s₁ s₂ = cong cong-⟨⟩-subˢ (cong-subˢ-◅ Γ₀ s₁ s₂)

swap-innerˢ-at : ∀ {Γ B₁ B₂} → (Θ : Ctx)
               → (W₁ : Γ ⊢V⦂ B₁) → (W₂ : Γ ∷ B₁ ⊢V⦂ B₂)
               → Sub [] (Γ ++ᶜ Θ) (((Γ ∷ B₁) ∷ B₂) ++ᶜ Θ)
swap-innerˢ-at Θ W₁ W₂ =
  cong-sub₀ {Γ'' = Θ} (val-sub W₁) ◅ [ cong-sub₀ {Γ'' = Θ} (val-sub W₂) ]ˢ

swap-outerˢ-at : ∀ {Γ B₁ B₂} → (Θ : Ctx)
               → (W₁ : Γ ⊢V⦂ B₁) → (W₂ : Γ ∷ B₁ ⊢V⦂ B₂)
               → Sub [] (Γ ++ᶜ Θ) (((Γ ∷ B₁) ∷ B₂) ++ᶜ Θ)
swap-outerˢ-at Θ W₁ W₂ =
    cong-sub₀ {Γ'' = Θ} (val-sub (V-sub₀ (val-sub W₁) W₂))
  ◅ [ cong-sub₀ {Γ'' = Θ} (cong-∷-sub (val-sub W₁)) ]ˢ

sub-swap-at-≐ˢ : ∀ {Γ B₁ B₂} → (Θ : Ctx)
               → (W₁ : Γ ⊢V⦂ B₁) → (W₂ : Γ ∷ B₁ ⊢V⦂ B₂)
               → swap-innerˢ-at Θ W₁ W₂ ≐ˢ swap-outerˢ-at Θ W₁ W₂
sub-swap-at-≐ˢ Θ W₁ W₂ =
  subst₂ _≐ˢ_ (cong-subˢ-◅ Θ (val-sub W₁) (val-sub W₂))
              (cong-subˢ-◅ Θ (val-sub (V-sub₀ (val-sub W₁) W₂))
                             (cong-∷-sub (val-sub W₁)))
              (cong-subˢ-≐ˢ Θ (sub-swap-≐ˢ W₁ W₂))

-- and what it says about terms.

sub-swap-at-≡ᵛ : ∀ {Γ B₁ B₂ A} → (Θ : Ctx)
               → (W₁ : Γ ⊢V⦂ B₁) → (W₂ : Γ ∷ B₁ ⊢V⦂ B₂)
               → (V : (((Γ ∷ B₁) ∷ B₂) ++ᶜ Θ) ⊢V⦂ A)
               → V-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub W₁))
                        (V-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub W₂)) V)
               ≡ V-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub (V-sub₀ (val-sub W₁) W₂)))
                        (V-sub₀ (cong-sub₀ {Γ'' = Θ} (cong-∷-sub (val-sub W₁))) V)
sub-swap-at-≡ᵛ Θ W₁ W₂ V = V-sub-≐ˢ (sub-swap-at-≐ˢ Θ W₁ W₂) V

sub-swap-at-≡ᶜ : ∀ {Γ B₁ B₂ C} → (Θ : Ctx)
               → (W₁ : Γ ⊢V⦂ B₁) → (W₂ : Γ ∷ B₁ ⊢V⦂ B₂)
               → (M : (((Γ ∷ B₁) ∷ B₂) ++ᶜ Θ) ⊢C⦂ C)
               → C-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub W₁))
                        (C-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub W₂)) M)
               ≡ C-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub (V-sub₀ (val-sub W₁) W₂)))
                        (C-sub₀ (cong-sub₀ {Γ'' = Θ} (cong-∷-sub (val-sub W₁))) M)
sub-swap-at-≡ᶜ Θ W₁ W₂ M = C-sub-≐ˢ (sub-swap-at-≐ˢ Θ W₁ W₂) M
