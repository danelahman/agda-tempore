------------------------------------------------------------------------
-- Substituting at the prefix boundary, and the former laws.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality
module Syntax.Substitutions.Swap.Base (Spec : LanguageSpec) where
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

------------------------------------------------------------------------
-- SUB-SWAP: TWO ADJACENT PREFIX SUBSTITUTIONS COMMUTE
--
-- Replacing the outer entry (its value weakened past the inner one) and
-- then the inner one agrees with replacing the inner entry, the outer one
-- riding in the suffix, and then the outer one.
--
-- The right-hand order names the *inner* entry `B₁` with the outer one
-- riding in the suffix. Rather than a `split-++ʳ` splitting, that is
-- presented as the ordinary `split-≡-++ᶜ` at the suffix `([] ∷ B₂) ++ᶜ Θ`
-- applied to an associativity-cast term — the two are interchangeable
-- (`sub-cast-C`), and this way `sub-var-r`/`-l`/`-hit` apply verbatim,
-- since `B₂` and `Θ`'s variables are then literally variables of that
-- suffix. The cast pushes through every former for free: the proof
-- `++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) (Θ ∷ A)` *is*
-- `cong (_∷ A) (++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ)`, definitionally.
------------------------------------------------------------------------
------------------------------------------------------------------------
-- SUBSTITUTING AT THE PREFIX BOUNDARY
--
-- The whole development is phrased in this one abbreviation: replace the
-- entry sitting between `Γ'` and the suffix `Θ` by a value over `Γ'`,
-- presenting the result over `Γ' ++ᶜ Θ`.
------------------------------------------------------------------------

bvar : ∀ {Γ'} → (B : VType) → (Θ : Ctx) → B ∈[ ctx-grade Θ ] ((Γ' ∷ B) ++ᶜ Θ)
bvar {Γ'} B Θ = split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})

bval : ∀ {Γ' B} → (Θ : Ctx) → Γ' ⊢V⦂ B
     → split-l (bvar {Γ'} B Θ) ⊢V⦂ B
bval {Γ'} {B} Θ W =
  castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ' ∷ B} {Θ}))) W

sub-atᵛ : ∀ {Γ' B A} → (Θ : Ctx) → ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A → Γ' ⊢V⦂ B
        → (Γ' ++ᶜ Θ) ⊢V⦂ A
sub-atᵛ {Γ'} {B} Θ U W =
  castᵛ (castOf {Γ'} {B} Θ) (U [ bvar B Θ ↦ bval Θ W ]v)

sub-atᶜ : ∀ {Γ' B C} → (Θ : Ctx) → ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C → Γ' ⊢V⦂ B
        → (Γ' ++ᶜ Θ) ⊢C⦂ C
sub-atᶜ {Γ'} {B} Θ M W =
  castᶜ (castOf {Γ'} {B} Θ) (M [ bvar B Θ ↦ bval Θ W ]c)

-- and on a clause family, where the substitution reaches through
-- `⟨_⟩[_↦_]cl` and the transport is `Cl-cast`, i.e. exactly the shape
-- `cast-handle` produces

sub-atᴴ : ∀ {Γ' B D} → (Θ : Ctx) → Fam D (((Γ' ∷ B) ++ᶜ Θ) ᴱ) → Γ' ⊢V⦂ B
        → Fam D ((Γ' ++ᶜ Θ) ᴱ)
sub-atᴴ {Γ'} {B} Θ H W op ε =
  Cl-cast op ε (castOf {Γ'} {B} Θ)
    (⟨ eternal? B ⟩[ bvar B Θ ↦ bval Θ W ]cl H op ε)

------------------------------------------------------------------------
-- THE FORMER LAWS
--
-- One per constructor: the action commutes with it, the suffix growing by
-- the former's own binders. Each is the corresponding `cast-*` lemma, plus
-- `castᶜ-irr`/`castᵛ-irr` wherever a binder makes the two ways of naming
-- the context equality differ (only propositionally).
------------------------------------------------------------------------

sub-at-const : ∀ {Γ' B b} → (Θ : Ctx) → {c : BaseConstants b} → (W : Γ' ⊢V⦂ B)
             → sub-atᵛ Θ (const c) W ≡ const c
sub-at-const {Γ'} {B} Θ W = cast-const (castOf {Γ'} {B} Θ)

sub-at-⋆ : ∀ {Γ' B} → (Θ : Ctx) → (W : Γ' ⊢V⦂ B) → sub-atᵛ Θ ⋆ W ≡ ⋆
sub-at-⋆ {Γ'} {B} Θ W = cast-⋆ (castOf {Γ'} {B} Θ)

sub-at-pair : ∀ {Γ' B A₁ A₂} → (Θ : Ctx)
            → (V₁ : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A₁) → (V₂ : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A₂)
            → (W : Γ' ⊢V⦂ B)
            → sub-atᵛ Θ ⦉ V₁ , V₂ ⦊ W ≡ ⦉ sub-atᵛ Θ V₁ W , sub-atᵛ Θ V₂ W ⦊
sub-at-pair {Γ'} {B} Θ V₁ V₂ W = cast-pair (castOf {Γ'} {B} Θ)

sub-at-lam : ∀ {Γ' B A C} → (Θ : Ctx)
           → (N : ((Γ' ∷ B) ++ᶜ Θ) ∷ A ⊢C⦂ C) → (W : Γ' ⊢V⦂ B)
           → sub-atᵛ Θ (lam N) W ≡ lam (sub-atᶜ (Θ ∷ A) N W)
sub-at-lam {Γ'} {B} {A} Θ N W =
  trans (cast-lam (castOf {Γ'} {B} Θ) _)
        (cong lam (castᶜ-irr (cong (_∷ A) (castOf {Γ'} {B} Θ))
                             (castOf {Γ'} {B} (Θ ∷ A)) _))

sub-at-ret : ∀ {Γ' B A} → (Θ : Ctx) → (V : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A)
           → (W : Γ' ⊢V⦂ B)
           → sub-atᶜ Θ (return V) W ≡ return (sub-atᵛ Θ V W)
sub-at-ret {Γ'} {B} Θ V W = cast-ret (castOf {Γ'} {B} Θ)

sub-at-app : ∀ {Γ' B A C} → (Θ : Ctx)
           → (V : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A ⇒ C) → (U : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A)
           → (W : Γ' ⊢V⦂ B)
           → sub-atᶜ Θ (V · U) W ≡ (sub-atᵛ Θ V W · sub-atᵛ Θ U W)
sub-at-app {Γ'} {B} Θ V U W = cast-app (castOf {Γ'} {B} Θ)

sub-at-absurd : ∀ {Γ' B C} → (Θ : Ctx) → (V : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ Empty)
              → (W : Γ' ⊢V⦂ B)
              → sub-atᶜ {C = C} Θ (absurd V) W ≡ absurd (sub-atᵛ Θ V W)
sub-at-absurd {Γ'} {B} Θ V W = cast-absurd (castOf {Γ'} {B} Θ)

sub-at-coerce : ∀ {Γ' B A ε ε'} → (Θ : Ctx) → {p : ε ≾ₑ ε'}
              → (M : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε) → (W : Γ' ⊢V⦂ B)
              → sub-atᶜ Θ (coerce p M) W ≡ coerce p (sub-atᶜ Θ M W)
sub-at-coerce {Γ'} {B} Θ M W = cast-coerce (castOf {Γ'} {B} Θ)

sub-at-seq : ∀ {Γ' B A A' ε ε'} → (Θ : Ctx)
           → (M : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
           → (N : ((Γ' ∷ B) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ A' ‼ ε')
           → (W : Γ' ⊢V⦂ B)
           → sub-atᶜ Θ (M ⨟ N) W
           ≡ (sub-atᶜ Θ M W ⨟ sub-atᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
sub-at-seq {Γ'} {B} {A} {ε = ε} Θ M N W =
  trans (cast-seq (castOf {Γ'} {B} Θ))
        (cong (_ ⨟_)
              (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (castOf {Γ'} {B} Θ))
                         (castOf {Γ'} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _))

sub-at-match : ∀ {Γ' B A₁ A₂ C} → (Θ : Ctx)
             → (V : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A₁ |×| A₂)
             → (N : ((Γ' ∷ B) ++ᶜ Θ) ∷ A₁ ∷ A₂ ⊢C⦂ C) → (W : Γ' ⊢V⦂ B)
             → sub-atᶜ Θ (match V `in N) W
             ≡ match sub-atᵛ Θ V W `in (sub-atᶜ (Θ ∷ A₁ ∷ A₂) N W)
sub-at-match {Γ'} {B} {A₁} {A₂} Θ V N W =
  trans (cast-match (castOf {Γ'} {B} Θ))
        (cong (match _ `in_)
              (castᶜ-irr (cong (λ Γ₀ → Γ₀ ∷ A₁ ∷ A₂) (castOf {Γ'} {B} Θ))
                         (castOf {Γ'} {B} (Θ ∷ A₁ ∷ A₂)) _))

sub-at-perform : ∀ {Γ' B A ε} → (Θ : Ctx) → {op : Op}
               → (V : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ type-of-gtype (param op))
               → (N : ((Γ' ∷ B) ++ᶜ Θ) ⟨ mapᵉ (op-grade op) ⟩
                        ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
               → (W : Γ' ⊢V⦂ B)
               → sub-atᶜ Θ (perform op V N) W
               ≡ perform op (sub-atᵛ Θ V W)
                   (sub-atᶜ (Θ ⟨ mapᵉ (op-grade op) ⟩
                               ∷ type-of-gtype (arity op)) N W)
sub-at-perform {Γ'} {B} Θ {op = op} V N W =
  trans (cast-perform (castOf {Γ'} {B} Θ))
        (cong (perform op _)
              (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                          ∷ type-of-gtype (arity op))
                               (castOf {Γ'} {B} Θ))
                         (castOf {Γ'} {B} (Θ ⟨ mapᵉ (op-grade op) ⟩
                                             ∷ type-of-gtype (arity op))) _))

sub-at-delay : ∀ {Γ' B A ε τ} → (Θ : Ctx)
             → (M : ((Γ' ∷ B) ++ᶜ Θ) ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε) → (W : Γ' ⊢V⦂ B)
             → sub-atᶜ Θ (delay τ M) W ≡ delay τ (sub-atᶜ (Θ ⟨ of-natʳ τ ⟩) M W)
sub-at-delay {Γ'} {B} {τ = τ} Θ M W =
  trans (cast-delay (castOf {Γ'} {B} Θ))
        (cong (delay τ)
              (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) (castOf {Γ'} {B} Θ))
                         (castOf {Γ'} {B} (Θ ⟨ of-natʳ τ ⟩)) _))

sub-at-box : ∀ {Γ' B A C ρ} → (Θ : Ctx)
           → (V : ((Γ' ∷ B) ++ᶜ Θ) ⟨ ρ ⟩ ⊢V⦂ A)
           → (M : ((Γ' ∷ B) ++ᶜ Θ) ∷ [ ρ ] A ⊢C⦂ C) → (W : Γ' ⊢V⦂ B)
           → sub-atᶜ Θ (box V M) W
           ≡ box (sub-atᵛ (Θ ⟨ ρ ⟩) V W) (sub-atᶜ (Θ ∷ [ ρ ] A) M W)
sub-at-box {Γ'} {B} {A} {ρ = ρ} Θ V M W =
  trans (cast-box (castOf {Γ'} {B} Θ))
        (cong₂ box
          (castᵛ-irr (cong (_⟨ ρ ⟩) (castOf {Γ'} {B} Θ))
                     (castOf {Γ'} {B} (Θ ⟨ ρ ⟩)) _)
          (castᶜ-irr (cong (_∷ [ ρ ] A) (castOf {Γ'} {B} Θ))
                     (castOf {Γ'} {B} (Θ ∷ [ ρ ] A)) _))

sub-at-handle : ∀ {Γ' B A D ε ε'} → (Θ : Ctx)
              → (M : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
              → (H : Fam D (((Γ' ∷ B) ++ᶜ Θ) ᴱ))
              → (N : ((Γ' ∷ B) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ D ‼ ε')
              → (W : Γ' ⊢V⦂ B)
              → sub-atᶜ Θ (handle M `with H `in N) W
              ≡ handle (sub-atᶜ Θ M W)
                 `with sub-atᴴ Θ H W
                 `in (sub-atᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
sub-at-handle {Γ'} {B} {A} {ε = ε} Θ M H N W =
  trans (cast-handle (castOf {Γ'} {B} Θ))
        (cong (λ z → handle _ `with _ `in z)
              (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (castOf {Γ'} {B} Θ))
                         (castOf {Γ'} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _))

------------------------------------------------------------------------
-- THE TWO ORDERS
--
-- `outer-first` replaces `B₂` (its value weakened past `B₁`) and then
-- `B₁`; `inner-first` replaces `B₁`, with `B₂` riding in the suffix, and
-- then `B₂`. The associativity is what re-brackets `B₂` into the suffix;
-- at a grown suffix it is `cong` of itself, definitionally, so it costs
-- nothing at the non-binding formers and one `castᶜ-irr` at the binding
-- ones.
------------------------------------------------------------------------

assocᴮ : (Γ : Ctx) → (B₁ B₂ : VType) → (Θ : Ctx)
       → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ≡ ((Γ ∷ B₁) ++ᶜ (([] ∷ B₂) ++ᶜ Θ))
assocᴮ Γ B₁ B₂ Θ = ++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ

assocᴮ⁻ : (Γ : Ctx) → (B₂ : VType) → (Θ : Ctx)
        → (Γ ++ᶜ (([] ∷ B₂) ++ᶜ Θ)) ≡ ((Γ ∷ B₂) ++ᶜ Θ)
assocᴮ⁻ Γ B₂ Θ = sym (++ᶜ-assoc Γ ([] ∷ B₂) Θ)

outerᵛ : ∀ {Γ B₁ B₂ A} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → (Γ ++ᶜ Θ) ⊢V⦂ A
outerᵛ {B₁ = B₁} Θ U W₂ W₁ =
  sub-atᵛ Θ (sub-atᵛ Θ U (V-rename (wk-ren {A = B₁}) W₂)) W₁

outerᶜ : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → (Γ ++ᶜ Θ) ⊢C⦂ C
outerᶜ {B₁ = B₁} Θ M W₂ W₁ =
  sub-atᶜ Θ (sub-atᶜ Θ M (V-rename (wk-ren {A = B₁}) W₂)) W₁

-- `B₁` alone, with `B₂` re-bracketed into the suffix. Both orders' second
-- step is then an ordinary `sub-atᵛ`/`sub-atᶜ`, so only this operation
-- needs former laws of its own.

inner₀ᵛ : ∀ {Γ B₁ B₂ A} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A
        → Γ ⊢V⦂ B₁ → ((Γ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A
inner₀ᵛ {Γ} {B₁} {B₂} Θ U W₁ =
  castᵛ (assocᴮ⁻ Γ B₂ Θ)
    (sub-atᵛ (([] ∷ B₂) ++ᶜ Θ) (castᵛ (assocᴮ Γ B₁ B₂ Θ) U) W₁)

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

innerᵛ : ∀ {Γ B₁ B₂ A} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → (Γ ++ᶜ Θ) ⊢V⦂ A
innerᵛ Θ U W₂ W₁ = sub-atᵛ Θ (inner₀ᵛ Θ U W₁) W₂

innerᶜ : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → (Γ ++ᶜ Θ) ⊢C⦂ C
innerᶜ Θ M W₂ W₁ = sub-atᶜ Θ (inner₀ᶜ Θ M W₁) W₂

-- and on a clause family

outerᴴ : ∀ {Γ B₁ B₂ D} → (Θ : Ctx) → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ)
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → Fam D ((Γ ++ᶜ Θ) ᴱ)
outerᴴ {B₁ = B₁} Θ H W₂ W₁ =
  sub-atᴴ Θ (sub-atᴴ Θ H (V-rename (wk-ren {A = B₁}) W₂)) W₁

innerᴴ : ∀ {Γ B₁ B₂ D} → (Θ : Ctx) → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ)
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → Fam D ((Γ ++ᶜ Θ) ᴱ)
innerᴴ Θ H W₂ W₁ = sub-atᴴ Θ (inner₀ᴴ Θ H W₁) W₂

------------------------------------------------------------------------
-- `inner₀`'S FORMER LAWS
--
-- Each is `cast-F` (pushing the associativity in), `sub-at-F`, `cast-F`
-- again (pushing the inverse out); the binding formers add one
-- `castᶜ-irr`, since `cong (_∷ A) (sym p)` and `sym (cong (_∷ A) p)`
-- agree only propositionally. Note the associativity itself needs no
-- reconciliation: `++ᶜ-assoc Γ' Δ (Θ ∷ A)` *is* `cong (_∷ A)` of the one
-- at `Θ`, definitionally.
------------------------------------------------------------------------

inner₀-const : ∀ {Γ B₁ B₂ b} → (Θ : Ctx) → {c : BaseConstants b}
             → (W₁ : Γ ⊢V⦂ B₁)
             → inner₀ᵛ {B₂ = B₂} Θ (const c) W₁ ≡ const c
inner₀-const {Γ} {B₁} {B₂} Θ W₁ =
  trans (cong (castᵛ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᵛ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-const (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-const (([] ∷ B₂) ++ᶜ Θ) W₁)))
        (cast-const (assocᴮ⁻ Γ B₂ Θ))

inner₀-⋆ : ∀ {Γ B₁ B₂} → (Θ : Ctx) → (W₁ : Γ ⊢V⦂ B₁)
         → inner₀ᵛ {B₂ = B₂} Θ ⋆ W₁ ≡ ⋆
inner₀-⋆ {Γ} {B₁} {B₂} Θ W₁ =
  trans (cong (castᵛ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᵛ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-⋆ (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-⋆ (([] ∷ B₂) ++ᶜ Θ) W₁)))
        (cast-⋆ (assocᴮ⁻ Γ B₂ Θ))

inner₀-pair : ∀ {Γ B₁ B₂ A₁ A₂} → (Θ : Ctx)
            → (V₁ : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A₁)
            → (V₂ : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A₂) → (W₁ : Γ ⊢V⦂ B₁)
            → inner₀ᵛ Θ ⦉ V₁ , V₂ ⦊ W₁
            ≡ ⦉ inner₀ᵛ Θ V₁ W₁ , inner₀ᵛ Θ V₂ W₁ ⦊
inner₀-pair {Γ} {B₁} {B₂} Θ V₁ V₂ W₁ =
  trans (cong (castᵛ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᵛ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-pair (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-pair (([] ∷ B₂) ++ᶜ Θ)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) V₁)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) V₂) W₁)))
        (cast-pair (assocᴮ⁻ Γ B₂ Θ))

inner₀-lam : ∀ {Γ B₁ B₂ A C} → (Θ : Ctx)
           → (N : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ∷ A ⊢C⦂ C) → (W₁ : Γ ⊢V⦂ B₁)
           → inner₀ᵛ {B₂ = B₂} Θ (lam N) W₁ ≡ lam (inner₀ᶜ (Θ ∷ A) N W₁)
inner₀-lam {Γ} {B₁} {B₂} {A} Θ N W₁ =
  trans (cong (castᵛ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᵛ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-lam (assocᴮ Γ B₁ B₂ Θ) N))
                 (sub-at-lam (([] ∷ B₂) ++ᶜ Θ)
                    (castᶜ (assocᴮ Γ B₁ B₂ (Θ ∷ A)) N) W₁)))
    (trans (cast-lam (assocᴮ⁻ Γ B₂ Θ) _)
           (cong lam (castᶜ-irr (cong (_∷ A) (assocᴮ⁻ Γ B₂ Θ))
                                (assocᴮ⁻ Γ B₂ (Θ ∷ A)) _)))

inner₀-ret : ∀ {Γ B₁ B₂ A} → (Θ : Ctx) → (V : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A)
           → (W₁ : Γ ⊢V⦂ B₁)
           → inner₀ᶜ {B₂ = B₂} Θ (return V) W₁ ≡ return (inner₀ᵛ Θ V W₁)
inner₀-ret {Γ} {B₁} {B₂} Θ V W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-ret (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-ret (([] ∷ B₂) ++ᶜ Θ)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) V) W₁)))
        (cast-ret (assocᴮ⁻ Γ B₂ Θ))

inner₀-app : ∀ {Γ B₁ B₂ A C} → (Θ : Ctx)
           → (V : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A ⇒ C)
           → (U : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A) → (W₁ : Γ ⊢V⦂ B₁)
           → inner₀ᶜ {B₂ = B₂} Θ (V · U) W₁
           ≡ (inner₀ᵛ Θ V W₁ · inner₀ᵛ Θ U W₁)
inner₀-app {Γ} {B₁} {B₂} Θ V U W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-app (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-app (([] ∷ B₂) ++ᶜ Θ)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) V)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) U) W₁)))
        (cast-app (assocᴮ⁻ Γ B₂ Θ))

inner₀-absurd : ∀ {Γ B₁ B₂ C} → (Θ : Ctx)
              → (V : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ Empty) → (W₁ : Γ ⊢V⦂ B₁)
              → inner₀ᶜ {B₂ = B₂} {C = C} Θ (absurd V) W₁
              ≡ absurd (inner₀ᵛ Θ V W₁)
inner₀-absurd {Γ} {B₁} {B₂} Θ V W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-absurd (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-absurd (([] ∷ B₂) ++ᶜ Θ)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) V) W₁)))
        (cast-absurd (assocᴮ⁻ Γ B₂ Θ))

inner₀-coerce : ∀ {Γ B₁ B₂ A ε ε'} → (Θ : Ctx) → {p : ε ≾ₑ ε'}
              → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ A ‼ ε) → (W₁ : Γ ⊢V⦂ B₁)
              → inner₀ᶜ {B₂ = B₂} Θ (coerce p M) W₁
              ≡ coerce p (inner₀ᶜ Θ M W₁)
inner₀-coerce {Γ} {B₁} {B₂} Θ M W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-coerce (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-coerce (([] ∷ B₂) ++ᶜ Θ)
                    (castᶜ (assocᴮ Γ B₁ B₂ Θ) M) W₁)))
        (cast-coerce (assocᴮ⁻ Γ B₂ Θ))

inner₀-seq : ∀ {Γ B₁ B₂ A A' ε ε'} → (Θ : Ctx)
           → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
           → (N : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ A' ‼ ε')
           → (W₁ : Γ ⊢V⦂ B₁)
           → inner₀ᶜ {B₂ = B₂} Θ (M ⨟ N) W₁
           ≡ (inner₀ᶜ Θ M W₁ ⨟ inner₀ᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₁)
inner₀-seq {Γ} {B₁} {B₂} {A} {ε = ε} Θ M N W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                   (trans (cast-seq (assocᴮ Γ B₁ B₂ Θ))
                     (cong (castᶜ (assocᴮ Γ B₁ B₂ Θ) M ⨟_)
                       (castᶜ-irr
                          (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (assocᴮ Γ B₁ B₂ Θ))
                          (assocᴮ Γ B₁ B₂ (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _))))
                 (sub-at-seq (([] ∷ B₂) ++ᶜ Θ)
                    (castᶜ (assocᴮ Γ B₁ B₂ Θ) M)
                    (castᶜ (assocᴮ Γ B₁ B₂ (Θ ⟨ mapᵉ ε ⟩ ∷ A)) N) W₁)))
    (trans (cast-seq (assocᴮ⁻ Γ B₂ Θ))
           (cong (_ ⨟_)
                 (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (assocᴮ⁻ Γ B₂ Θ))
                            (assocᴮ⁻ Γ B₂ (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _)))

inner₀-match : ∀ {Γ B₁ B₂ A₁ A₂ C} → (Θ : Ctx)
             → (V : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A₁ |×| A₂)
             → (N : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ∷ A₁ ∷ A₂ ⊢C⦂ C) → (W₁ : Γ ⊢V⦂ B₁)
             → inner₀ᶜ {B₂ = B₂} Θ (match V `in N) W₁
             ≡ match inner₀ᵛ Θ V W₁ `in (inner₀ᶜ (Θ ∷ A₁ ∷ A₂) N W₁)
inner₀-match {Γ} {B₁} {B₂} {A₁} {A₂} Θ V N W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                   (trans (cast-match (assocᴮ Γ B₁ B₂ Θ))
                     (cong (match castᵛ (assocᴮ Γ B₁ B₂ Θ) V `in_)
                       (castᶜ-irr
                          (cong (λ Γ₀ → Γ₀ ∷ A₁ ∷ A₂) (assocᴮ Γ B₁ B₂ Θ))
                          (assocᴮ Γ B₁ B₂ (Θ ∷ A₁ ∷ A₂)) _))))
                 (sub-at-match (([] ∷ B₂) ++ᶜ Θ)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) V)
                    (castᶜ (assocᴮ Γ B₁ B₂ (Θ ∷ A₁ ∷ A₂)) N) W₁)))
    (trans (cast-match (assocᴮ⁻ Γ B₂ Θ))
           (cong (match _ `in_)
                 (castᶜ-irr (cong (λ Γ₀ → Γ₀ ∷ A₁ ∷ A₂) (assocᴮ⁻ Γ B₂ Θ))
                            (assocᴮ⁻ Γ B₂ (Θ ∷ A₁ ∷ A₂)) _)))

inner₀-perform : ∀ {Γ B₁ B₂ A ε} → (Θ : Ctx) → {op : Op}
               → (V : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ type-of-gtype (param op))
               → (N : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⟨ mapᵉ (op-grade op) ⟩
                        ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
               → (W₁ : Γ ⊢V⦂ B₁)
               → inner₀ᶜ {B₂ = B₂} Θ (perform op V N) W₁
               ≡ perform op (inner₀ᵛ Θ V W₁)
                   (inner₀ᶜ (Θ ⟨ mapᵉ (op-grade op) ⟩
                               ∷ type-of-gtype (arity op)) N W₁)
inner₀-perform {Γ} {B₁} {B₂} Θ {op = op} V N W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                   (trans (cast-perform (assocᴮ Γ B₁ B₂ Θ))
                     (cong (perform op (castᵛ (assocᴮ Γ B₁ B₂ Θ) V))
                       (castᶜ-irr
                          (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                           ∷ type-of-gtype (arity op))
                                (assocᴮ Γ B₁ B₂ Θ))
                          (assocᴮ Γ B₁ B₂ (Θ ⟨ mapᵉ (op-grade op) ⟩
                                             ∷ type-of-gtype (arity op))) _))))
                 (sub-at-perform (([] ∷ B₂) ++ᶜ Θ)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) V)
                    (castᶜ (assocᴮ Γ B₁ B₂ (Θ ⟨ mapᵉ (op-grade op) ⟩
                                              ∷ type-of-gtype (arity op))) N)
                    W₁)))
    (trans (cast-perform (assocᴮ⁻ Γ B₂ Θ))
           (cong (perform op _)
                 (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                             ∷ type-of-gtype (arity op))
                                  (assocᴮ⁻ Γ B₂ Θ))
                            (assocᴮ⁻ Γ B₂ (Θ ⟨ mapᵉ (op-grade op) ⟩
                                             ∷ type-of-gtype (arity op))) _)))

inner₀-delay : ∀ {Γ B₁ B₂ A ε τ} → (Θ : Ctx)
             → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
             → (W₁ : Γ ⊢V⦂ B₁)
             → inner₀ᶜ {B₂ = B₂} Θ (delay τ M) W₁
             ≡ delay τ (inner₀ᶜ (Θ ⟨ of-natʳ τ ⟩) M W₁)
inner₀-delay {Γ} {B₁} {B₂} {τ = τ} Θ M W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-delay (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-delay (([] ∷ B₂) ++ᶜ Θ)
                    (castᶜ (assocᴮ Γ B₁ B₂ (Θ ⟨ of-natʳ τ ⟩)) M) W₁)))
    (trans (cast-delay (assocᴮ⁻ Γ B₂ Θ))
           (cong (delay τ)
                 (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) (assocᴮ⁻ Γ B₂ Θ))
                            (assocᴮ⁻ Γ B₂ (Θ ⟨ of-natʳ τ ⟩)) _)))

inner₀-box : ∀ {Γ B₁ B₂ A C ρ} → (Θ : Ctx)
           → (V : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⟨ ρ ⟩ ⊢V⦂ A)
           → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ∷ [ ρ ] A ⊢C⦂ C) → (W₁ : Γ ⊢V⦂ B₁)
           → inner₀ᶜ {B₂ = B₂} Θ (box V M) W₁
           ≡ box (inner₀ᵛ (Θ ⟨ ρ ⟩) V W₁) (inner₀ᶜ (Θ ∷ [ ρ ] A) M W₁)
inner₀-box {Γ} {B₁} {B₂} {A} {ρ = ρ} Θ V M W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-box (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-box (([] ∷ B₂) ++ᶜ Θ)
                    (castᵛ (assocᴮ Γ B₁ B₂ (Θ ⟨ ρ ⟩)) V)
                    (castᶜ (assocᴮ Γ B₁ B₂ (Θ ∷ [ ρ ] A)) M) W₁)))
    (trans (cast-box (assocᴮ⁻ Γ B₂ Θ))
           (cong₂ box
             (castᵛ-irr (cong (_⟨ ρ ⟩) (assocᴮ⁻ Γ B₂ Θ))
                        (assocᴮ⁻ Γ B₂ (Θ ⟨ ρ ⟩)) _)
             (castᶜ-irr (cong (_∷ [ ρ ] A) (assocᴮ⁻ Γ B₂ Θ))
                        (assocᴮ⁻ Γ B₂ (Θ ∷ [ ρ ] A)) _)))

inner₀-handle : ∀ {Γ B₁ B₂ A D ε ε'} → (Θ : Ctx)
              → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
              → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
              → (N : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ D ‼ ε')
              → (W₁ : Γ ⊢V⦂ B₁)
              → inner₀ᶜ {B₂ = B₂} Θ (handle M `with H `in N) W₁
              ≡ handle (inner₀ᶜ Θ M W₁)
                 `with inner₀ᴴ Θ H W₁
                 `in (inner₀ᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₁)
inner₀-handle {Γ} {B₁} {B₂} {A} {ε = ε} Θ M H N W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                   (trans (cast-handle (assocᴮ Γ B₁ B₂ Θ))
                     (cong (λ z → handle castᶜ (assocᴮ Γ B₁ B₂ Θ) M
                                   `with (λ op' ε' →
                                            Cl-cast op' ε' (assocᴮ Γ B₁ B₂ Θ)
                                              (H op' ε'))
                                   `in z)
                       (castᶜ-irr
                          (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (assocᴮ Γ B₁ B₂ Θ))
                          (assocᴮ Γ B₁ B₂ (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _))))
                 (sub-at-handle (([] ∷ B₂) ++ᶜ Θ)
                    (castᶜ (assocᴮ Γ B₁ B₂ Θ) M)
                    (λ op' ε' → Cl-cast op' ε' (assocᴮ Γ B₁ B₂ Θ) (H op' ε'))
                    (castᶜ (assocᴮ Γ B₁ B₂ (Θ ⟨ mapᵉ ε ⟩ ∷ A)) N) W₁)))
    (trans (cast-handle (assocᴮ⁻ Γ B₂ Θ))
           (cong (λ z → handle _ `with _ `in z)
                 (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (assocᴮ⁻ Γ B₂ Θ))
                            (assocᴮ⁻ Γ B₂ (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _)))

------------------------------------------------------------------------
