------------------------------------------------------------------------
-- Substituting at the prefix boundary.                                --
--                                                                     --
-- Replacing the entry sitting between `Γ'` and a suffix `Θ` by a value --
-- over `Γ'`, presenting the result over `Γ' ++ᶜ Θ`. This is the form   --
-- every consumer of substitution actually uses, and the boundary       --
-- variable it names is `cong-sub₀ (val-sub W)` under the retyping      --
-- `castOf` — which is what carries the parallel laws over to it.       --
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
open import Syntax.Substitutions.Restrict         S
open import Syntax.Substitutions.Laws             S
open import Syntax.Substitutions.Variables        S

-- Renaming along an identity-like renaming is the cast (the `castᵛ`/`castᶜ`
-- form of `C-rename-eq-≡`, which is stated with `subst`).

V-rename-castᵛ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (V : Γ ⊢V⦂ A)
               → V-rename (eq-ren e) V ≡ castᵛ e V
V-rename-castᵛ refl V = V-rename-id-≡ ≐ʳ-refl V

C-rename-castᶜ : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → (M : Γ ⊢C⦂ C)
               → C-rename (eq-ren e) M ≡ castᶜ e M
C-rename-castᶜ refl M = C-rename-id-≡ ≐ʳ-refl M

------------------------------------------------------------------------
-- SUBSTITUTING AT THE PREFIX BOUNDARY
------------------------------------------------------------------------

bvar : ∀ {Γ'} → (B : VType) → (Θ : Ctx) → B ∈[ ctx-grade Θ ] ((Γ' ∷ B) ++ᶜ Θ)
bvar {Γ'} B Θ = split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})

bval : ∀ {Γ' B} → (Θ : Ctx) → Γ' ⊢V⦂ B
     → split-l (bvar {Γ'} B Θ) ⊢V⦂ B
bval {Γ'} {B} Θ W =
  castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ' ∷ B} {Θ}))) W

-- The action of `sub-atˢ₀`, i.e. the substitution at the boundary. It lands at
-- `Γ' ++ᶜ Θ` with no retyping, the splitting's halves being given.

sub-atᵛ : ∀ {Γ' B A} → (Θ : Ctx) → ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A → Γ' ⊢V⦂ B
        → (Γ' ++ᶜ Θ) ⊢V⦂ A
sub-atᵛ Θ U W = V-sub₀ (sub-atˢ₀ Θ W) U

sub-atᶜ : ∀ {Γ' B C} → (Θ : Ctx) → ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C → Γ' ⊢V⦂ B
        → (Γ' ++ᶜ Θ) ⊢C⦂ C
sub-atᶜ Θ M W = C-sub₀ (sub-atˢ₀ Θ W) M

-- and on a resource variable, i.e. the cell an `unbox` names

sub-atᴿ : ∀ {Γ' B A ρ σ} → (Θ : Ctx)
        → ([ ρ ] A ∈[ σ ] ((Γ' ∷ B) ++ᶜ Θ)) → Γ' ⊢V⦂ B
        → Σ[ σ' ∈ R ] (([ ρ ] A ∈[ σ' ] (Γ' ++ᶜ Θ)) × (σ' ≾ᵣ σ))
sub-atᴿ Θ z W = sub-tgt₀ (sub-atˢ₀ Θ W) z

-- and on a clause family, where the substitution restricts to the eternal part
-- and is extended by the clause's two binders, as in `_[_↦_]cl`

sub-atᴴ : ∀ {Γ' B D} → (Θ : Ctx) → Fam D (((Γ' ∷ B) ++ᶜ Θ) ᴱ) → Γ' ⊢V⦂ B
        → Fam D ((Γ' ++ᶜ Θ) ᴱ)
sub-atᴴ Θ H W op ε =
  C-sub₀ (cong-∷-sub (cong-∷-sub (restrict-sub₀ (sub-atˢ₀ Θ W)))) (H op ε)

-- Congruences.

sub-atᵛ-≡ : ∀ {Γ' B A} → (Θ : Ctx) → {U U' : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A}
          → (W : Γ' ⊢V⦂ B) → U ≡ U' → sub-atᵛ Θ U W ≡ sub-atᵛ Θ U' W
sub-atᵛ-≡ Θ W e = cong (V-sub₀ (sub-atˢ₀ Θ W)) e

sub-atᵛ-≡ᵥ : ∀ {Γ' B A} → (Θ : Ctx) → (U : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A)
           → {W W' : Γ' ⊢V⦂ B} → W ≡ W'
           → sub-atᵛ Θ U W ≡ sub-atᵛ Θ U W'
sub-atᵛ-≡ᵥ Θ U refl = refl

sub-atᶜ-≡ : ∀ {Γ' B C} → (Θ : Ctx) → {M M' : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C}
          → (W : Γ' ⊢V⦂ B) → M ≡ M' → sub-atᶜ Θ M W ≡ sub-atᶜ Θ M' W
sub-atᶜ-≡ Θ W e = cong (C-sub₀ (sub-atˢ₀ Θ W)) e

sub-atᶜ-≡ᵥ : ∀ {Γ' B C} → (Θ : Ctx) → (X : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C)
           → {W W' : Γ' ⊢V⦂ B} → W ≡ W'
           → sub-atᶜ Θ X W ≡ sub-atᶜ Θ X W'
sub-atᶜ-≡ᵥ Θ X refl = refl

------------------------------------------------------------------------
-- THE BOUNDARY SUBSTITUTION IS `cong-sub₀ (val-sub W)`
--
-- `split-≡-++ᶜ` is `≡-split refl`, which recurses on the suffix exactly as
-- `cong-sub₀` does, so the two agree by induction on it.
------------------------------------------------------------------------

sub-at-≡ˢ₀ : ∀ {Γ B} → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
           → sub-atˢ₀ {B = B} Θ W ≡ cong-sub₀ {Γ'' = Θ} (val-sub W)
sub-at-≡ˢ₀ []        W = refl
sub-at-≡ˢ₀ (Θ ∷ A)   W = cong cong-∷-sub  (sub-at-≡ˢ₀ Θ W)
sub-at-≡ˢ₀ (Θ ⟨ ρ ⟩) W = cong cong-⟨⟩-sub (sub-at-≡ˢ₀ Θ W)

-- Hence what the boundary substitution does to a term.

sub-at-≡ᵛ : ∀ {Γ B A} → (Θ : Ctx) → (U : ((Γ ∷ B) ++ᶜ Θ) ⊢V⦂ A) → (W : Γ ⊢V⦂ B)
          → sub-atᵛ Θ U W ≡ V-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub W)) U
sub-at-≡ᵛ Θ U W = cong (λ s → V-sub₀ s U) (sub-at-≡ˢ₀ Θ W)

sub-at-≡ᶜ : ∀ {Γ B C} → (Θ : Ctx) → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ C) → (W : Γ ⊢V⦂ B)
          → sub-atᶜ Θ M W ≡ C-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub W)) M
sub-at-≡ᶜ Θ M W = cong (λ s → C-sub₀ s M) (sub-at-≡ˢ₀ Θ W)

------------------------------------------------------------------------
-- THE SAME, WRITTEN AT THE BOUNDARY VARIABLE
--
-- `bvar B Θ` is `Hd` under one `Tl` per entry of `Θ`, and its splitting agrees
-- with the boundary's only up to `castOf`, the two halves being read off
-- `var-split` rather than given. Induction on the suffix; each step moves the
-- retyping past one congruence. This is the only place that retyping is paid.
------------------------------------------------------------------------

-- Retyping the result of an action is retyping the substitution it acts by.

cast-V-sub₀ : ∀ {Γ₀ Γ₀' Γ₁ A} → (e : Γ₀ ≡ Γ₀') → (s : Sub₀ [] Γ₀ Γ₁)
            → (U : Γ₁ ⊢V⦂ A)
            → castᵛ e (V-sub₀ s U)
            ≡ V-sub₀ (subst (λ Δ → Sub₀ [] Δ Γ₁) e s) U
cast-V-sub₀ refl s U = refl

cast-C-sub₀ : ∀ {Γ₀ Γ₀' Γ₁ C} → (e : Γ₀ ≡ Γ₀') → (s : Sub₀ [] Γ₀ Γ₁)
            → (M : Γ₁ ⊢C⦂ C)
            → castᶜ e (C-sub₀ s M)
            ≡ C-sub₀ (subst (λ Δ → Sub₀ [] Δ Γ₁) e s) M
cast-C-sub₀ refl s M = refl

cast-Cl-sub₀ : ∀ {Γ₀ Γ₀' Γ₁ D} → (op : Op) → (ε : E)
             → (e : Γ₀ ≡ Γ₀') → (s : Sub₀ [] Γ₀ Γ₁) → (M : Cl D op ε (Γ₁ ᴱ))
             → Cl-cast op ε e
                 (C-sub₀ (cong-∷-sub (cong-∷-sub (restrict-sub₀ s))) M)
             ≡ C-sub₀ (cong-∷-sub (cong-∷-sub
                         (restrict-sub₀ (subst (λ Δ → Sub₀ [] Δ Γ₁) e s)))) M
cast-Cl-sub₀ op ε refl s M = refl

-- The substitution at `bvar B Θ`, retyped along `castOf`, IS the one at the
-- boundary: `sub-split-subst` at the splitting's two halves, the value coming
-- back from `bval` by `castᵛ-sym-cast`.

bvar-sub-≡ : ∀ {Γ B} → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
           → subst (λ Δ → Sub₀ [] Δ ((Γ ∷ B) ++ᶜ Θ)) (castOf {Γ} {B} Θ)
                   (sub-split₀ (split-pf (bvar B Θ)) (bval Θ W))
           ≡ sub-atˢ₀ Θ W
bvar-sub-≡ {Γ} {B} Θ W =
  trans (sub-split-subst (split→∈-split-l t) (split→∈-split-r t)
                         (split-pf (bvar B Θ)) t (bval Θ W))
        (cong (sub-split₀ t)
              (trans (sym (castᵛ≡subst (split→∈-split-l t) _))
                     (castᵛ-sym-cast (split→∈-split-l t) W)))
  where
    t = split-≡-++ᶜ {Γ ∷ B} {Θ}

-- Hence what each of the three actions does, in the `bvar` spelling.

bvar-≡ᵛ : ∀ {Γ B A} → (Θ : Ctx) → (U : ((Γ ∷ B) ++ᶜ Θ) ⊢V⦂ A) → (W : Γ ⊢V⦂ B)
        → castᵛ (castOf {Γ} {B} Θ) (U [ bvar B Θ ↦ bval Θ W ]v)
        ≡ sub-atᵛ Θ U W
bvar-≡ᵛ {Γ} {B} Θ U W =
  trans (cast-V-sub₀ (castOf {Γ} {B} Θ) _ U)
        (cong (λ s → V-sub₀ s U) (bvar-sub-≡ Θ W))

bvar-≡ᶜ : ∀ {Γ B C} → (Θ : Ctx) → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ C) → (W : Γ ⊢V⦂ B)
        → castᶜ (castOf {Γ} {B} Θ) (M [ bvar B Θ ↦ bval Θ W ]c)
        ≡ sub-atᶜ Θ M W
bvar-≡ᶜ {Γ} {B} Θ M W =
  trans (cast-C-sub₀ (castOf {Γ} {B} Θ) _ M)
        (cong (λ s → C-sub₀ s M) (bvar-sub-≡ Θ W))

bvar-≡ᴴ : ∀ {Γ B D} → (Θ : Ctx) → (H : Fam D (((Γ ∷ B) ++ᶜ Θ) ᴱ))
        → (W : Γ ⊢V⦂ B) → (op : Op) → (ε : E)
        → Cl-cast op ε (castOf {Γ} {B} Θ) ((H [ bvar B Θ ↦ bval Θ W ]cl) op ε)
        ≡ sub-atᴴ Θ H W op ε
bvar-≡ᴴ {Γ} {B} Θ H W op ε =
  trans (cast-Cl-sub₀ op ε (castOf {Γ} {B} Θ) _ (H op ε))
        (cong (λ s → C-sub₀ (cong-∷-sub (cong-∷-sub (restrict-sub₀ s))) (H op ε))
              (bvar-sub-≡ Θ W))

------------------------------------------------------------------------
-- `sub-wk`: SUBSTITUTING FOR A VARIABLE NOBODY MENTIONS
--
-- Weakening at the boundary and then substituting there is the identity.
------------------------------------------------------------------------

sub-wk-V : ∀ {Γ B} → (Θ : Ctx) → ∀ {A} → (U : (Γ ++ᶜ Θ) ⊢V⦂ A) → (W : Γ ⊢V⦂ B)
         → sub-atᵛ Θ (V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) U) W ≡ U
sub-wk-V {B = B} Θ U W =
  trans (sub-at-≡ᵛ Θ (V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) U) W)
        (sub-wk-≡ᵛ Θ W U)

sub-wk-C : ∀ {Γ B} → (Θ : Ctx) → ∀ {C} → (M : (Γ ++ᶜ Θ) ⊢C⦂ C) → (W : Γ ⊢V⦂ B)
         → sub-atᶜ Θ (C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) M) W ≡ M
sub-wk-C {B = B} Θ M W =
  trans (sub-at-≡ᶜ Θ (C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) M) W)
        (sub-wk-≡ᶜ Θ W M)

-- The same with the term's context given by an equation rather than literally.

sub-wk-C-cast : ∀ {Γ B Γ₀} → (Θ : Ctx) → (e : Γ₀ ≡ Γ ++ᶜ Θ) → ∀ {C}
              → (M : Γ₀ ⊢C⦂ C) → (W : Γ ⊢V⦂ B)
              → sub-atᶜ Θ (C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                             (subst (_⊢C⦂ C) e M)) W
              ≡ subst (_⊢C⦂ C) e M
sub-wk-C-cast Θ refl M W = sub-wk-C Θ M W

------------------------------------------------------------------------
-- THE TWO ORDERS
--
-- `outer` replaces `B₂` (its value weakened past `B₁`) and then `B₁`;
-- `inner` replaces `B₁`, with `B₂` re-bracketed into the suffix, and then
-- `B₂`. The re-bracketing is `++ᶜ-assoc`, so only `inner₀` carries casts.
------------------------------------------------------------------------

assocᴮ : (Γ : Ctx) → (B₁ B₂ : VType) → (Θ : Ctx)
       → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ≡ ((Γ ∷ B₁) ++ᶜ (([] ∷ B₂) ++ᶜ Θ))
assocᴮ Γ B₁ B₂ Θ = ++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ

assocᴮ⁻ : (Γ : Ctx) → (B₂ : VType) → (Θ : Ctx)
        → (Γ ++ᶜ (([] ∷ B₂) ++ᶜ Θ)) ≡ ((Γ ∷ B₂) ++ᶜ Θ)
assocᴮ⁻ Γ B₂ Θ = sym (++ᶜ-assoc Γ ([] ∷ B₂) Θ)

outerᶜ : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → (Γ ++ᶜ Θ) ⊢C⦂ C
outerᶜ {B₁ = B₁} Θ M W₂ W₁ =
  sub-atᶜ Θ (sub-atᶜ Θ M (V-rename (wk-ren {A = B₁}) W₂)) W₁

inner₀ᶜ : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
        → Γ ⊢V⦂ B₁ → ((Γ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
inner₀ᶜ {Γ} {B₁} {B₂} Θ M W₁ =
  castᶜ (assocᴮ⁻ Γ B₂ Θ)
    (sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) (castᶜ (assocᴮ Γ B₁ B₂ Θ) M) W₁)

inner₀ᴴ : ∀ {Γ B₁ B₂ D} → (Θ : Ctx) → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ)
        → Γ ⊢V⦂ B₁ → Fam D (((Γ ∷ B₂) ++ᶜ Θ) ᴱ)
inner₀ᴴ {Γ} {B₁} {B₂} Θ H W₁ op ε =
  Cl-cast op ε (assocᴮ⁻ Γ B₂ Θ)
    (sub-atᴴ (([] ∷ B₂) ++ᶜ Θ)
       (λ op' ε' → Cl-cast op' ε' (assocᴮ Γ B₁ B₂ Θ) (H op' ε')) W₁ op ε)

innerᶜ : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → (Γ ++ᶜ Θ) ⊢C⦂ C
innerᶜ Θ M W₂ W₁ = sub-atᶜ Θ (inner₀ᶜ Θ M W₁) W₂

outerᴴ : ∀ {Γ B₁ B₂ D} → (Θ : Ctx) → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ)
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → Fam D ((Γ ++ᶜ Θ) ᴱ)
outerᴴ {B₁ = B₁} Θ H W₂ W₁ =
  sub-atᴴ Θ (sub-atᴴ Θ H (V-rename (wk-ren {A = B₁}) W₂)) W₁

innerᴴ : ∀ {Γ B₁ B₂ D} → (Θ : Ctx) → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ)
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → Fam D ((Γ ++ᶜ Θ) ᴱ)
innerᴴ Θ H W₂ W₁ = sub-atᴴ Θ (inner₀ᴴ Θ H W₁) W₂

------------------------------------------------------------------------
-- RE-BRACKETING THE SUFFIX
--
-- `inner₀`'s two casts conjugate the substitution at the re-bracketed suffix
-- into the one under `Θ` alone. Induction on the suffix, each step moving the
-- two retypings past one congruence.
------------------------------------------------------------------------

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
              (trans (sub-atᶜ-≡ (([] ∷ B₂) ++ᶜ Θ) W₁
                       (sym (C-rename-castᶜ (assocᴮ Γ B₁ B₂ Θ) M)))
                     (sub-at-≡ᶜ (([] ∷ B₂) ++ᶜ Θ)
                                (C-rename (eq-ren (assocᴮ Γ B₁ B₂ Θ)) M) W₁)))
    (trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
                 (cong (C-sub₀ (cong-sub₀ {Γ'' = ([] ∷ B₂) ++ᶜ Θ} (val-sub W₁)))
                       (sym (C-sub₀-⌜⌝ (eq-ren (assocᴮ Γ B₁ B₂ Θ)) M))))
      (trans (sym (C-rename-castᶜ (assocᴮ⁻ Γ B₂ Θ) _))
        (trans (sym (C-sub₀-⌜⌝ (eq-ren (assocᴮ⁻ Γ B₂ Θ)) _))
               (C-sub-≐ˢ (assoc-≐ˢ Θ W₁) M))))

------------------------------------------------------------------------
-- `sub-swap`: THE TWO ORDERS AGREE
--
-- Both orders are now `cong-sub₀ (val-sub _)` composites, so the theorem is
-- `sub-swap-at-≡ᶜ` with the outer value read back by `sub-wk`: substituting
-- `W₁` into `W₂` weakened past `B₁` gives `W₂` again.
------------------------------------------------------------------------

SubSwapC : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
         → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → Set
SubSwapC Θ M W₂ W₁ = outerᶜ Θ M W₂ W₁ ≡ innerᶜ Θ M W₂ W₁

sub-swap-C : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C)
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
           → SubSwapC Θ M W₂ W₁
sub-swap-C {Γ} {B₁} {B₂} Θ M W₂ W₁ =
  trans (trans (sub-atᶜ-≡ Θ W₁ (sub-at-≡ᶜ Θ M (V-rename (wk-ren {A = B₁}) W₂)))
               (sub-at-≡ᶜ Θ (C-sub₀ (cong-sub₀ {Γ'' = Θ}
                               (val-sub (V-rename (wk-ren {A = B₁}) W₂))) M) W₁))
    (trans (sub-swap-at-≡ᶜ Θ W₁ (V-rename (wk-ren {A = B₁}) W₂) M)
      (trans (cong (λ V → C-sub₀ (cong-sub₀ {Γ'' = Θ} (val-sub V))
                                 (C-sub₀ (cong-sub₀ {Γ'' = Θ}
                                            (cong-∷-sub (val-sub W₁))) M))
                   (sub-wk-≡ᵛ [] W₁ W₂))
             (sym (trans (sub-atᶜ-≡ Θ W₂ (inner₀-≡ᶜ Θ M W₁))
                         (sub-at-≡ᶜ Θ (C-sub₀ (cong-sub₀ {Γ'' = Θ}
                                         (cong-∷-sub (val-sub W₁))) M) W₂)))))
