------------------------------------------------------------------------
-- Two adjacent prefix substitutions commute.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions.Swap (Spec : LanguageSpec) where

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
                      (sub-unbox (castʳᵉ (assocᴮ Γ B₁ B₂ Θ) w) V _ y₁ U₁ relC))
                    (≡→≐ᶜ (cast-unbox
                             (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ)))))))
              (≡→≐ᶜ (cast-unbox (assocᴮ⁻ Γ B₂ Θ)))))
          (≐ᶜ-trans
            (castᶜ-≐ (castOf {Γ} {B₂} Θ)
              (sub-unbox (castʳᵉ (assocᴮ⁻ Γ B₂ Θ) wC) hd _ y₂ U₂ relD))
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

    wA = castʳᵉ (castOf {Γ ∷ B₁} {B₂} Θ) (unbox-var-ren vA relA)

    bodyA = castᶜ (cong (_∷ A) (castOf {Γ ∷ B₁} {B₂} Θ))
                  (M [ Tl-∷ x₂ ↦ V₂ ]c)

    relB = ≾ᵣ-trans (proj₂ (proj₂ (⟨ proj₂ (unbox-tgt wA hd) ⟩[ x₁ ↦ V₁ ]rvar)))
                    (proj₂ (proj₂ (unbox⇒var wA hd)))

    vB = proj₂ (rvar-tgt (proj₂ (unbox-tgt wA hd)) x₁ V₁)

    wB = castʳᵉ (castOf {Γ} {B₁} Θ) (unbox-var-ren vB relB)

    relC = ≾ᵣ-trans
             (proj₂ (proj₂
               (⟨ proj₂ (unbox-tgt (castʳᵉ (assocᴮ Γ B₁ B₂ Θ) w) V)
                ⟩[ y₁ ↦ U₁ ]rvar)))
             (proj₂ (proj₂ (unbox⇒var (castʳᵉ (assocᴮ Γ B₁ B₂ Θ) w) V)))

    vC = proj₂ (rvar-tgt (proj₂ (unbox-tgt (castʳᵉ (assocᴮ Γ B₁ B₂ Θ) w) V))
                         y₁ U₁)

    wC = castʳᵉ (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ)) (unbox-var-ren vC relC)

    relD = ≾ᵣ-trans
             (proj₂ (proj₂
               (⟨ proj₂ (unbox-tgt (castʳᵉ (assocᴮ⁻ Γ B₂ Θ) wC) hd)
                ⟩[ y₂ ↦ U₂ ]rvar)))
             (proj₂ (proj₂ (unbox⇒var (castʳᵉ (assocᴮ⁻ Γ B₂ Θ) wC) hd)))

    vD = proj₂ (rvar-tgt (proj₂ (unbox-tgt (castʳᵉ (assocᴮ⁻ Γ B₂ Θ) wC) hd))
                         y₂ U₂)

    wD = castʳᵉ (castOf {Γ} {B₂} Θ) (unbox-var-ren vD relD)

    -- each stored renaming is read only through `unbox-tgt`, and there it is
    -- the cell the substitution left; so the two sides' cells are exactly the
    -- two sides of `unbox-cell-swap`
    cellA : unbox-tgt wA hd ≡ rcell Θ cW Ŵ₂
    cellA = trans (unbox-tgt-castʳᵉ (castOf {Γ ∷ B₁} {B₂} Θ)
                                    (unbox-var-ren vA relA) hd)
                  (cong (Tgt-cast (castOf {Γ ∷ B₁} {B₂} Θ))
                        (unbox-var-tgt vA relA))

    cellC : unbox-tgt wC hd
          ≡ rcell (([] ∷ B₂) ++ᶜ Θ)
                  (proj₂ (Tgt-cast (assocᴮ Γ B₁ B₂ Θ) (unbox-tgt w V))) W₁
    cellC =
      trans (unbox-tgt-castʳᵉ (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))
                              (unbox-var-ren vC relC) hd)
        (trans (cong (Tgt-cast (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ)))
                     (unbox-var-tgt vC relC))
               (cong (λ t → rcell′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                     (unbox-tgt-castʳᵉ (assocᴮ Γ B₁ B₂ Θ) w V)))

    cell : unbox-tgt wB hd ≡ unbox-tgt wD hd
    cell =
      trans (unbox-tgt-castʳᵉ (castOf {Γ} {B₁} Θ) (unbox-var-ren vB relB) hd)
        (trans (cong (Tgt-cast (castOf {Γ} {B₁} Θ)) (unbox-var-tgt vB relB))
          (trans (cong (λ t → rcell′ Θ t W₁) cellA)
            (trans (unbox-cell-swap Θ cW W₂ W₁)
              (sym
                (trans (unbox-tgt-castʳᵉ (castOf {Γ} {B₂} Θ)
                                         (unbox-var-ren vD relD) hd)
                  (trans (cong (Tgt-cast (castOf {Γ} {B₂} Θ))
                               (unbox-var-tgt vD relD))
                    (trans
                      (cong (λ t → rcell′ Θ t W₂)
                            (unbox-tgt-castʳᵉ (assocᴮ⁻ Γ B₂ Θ) wC hd))
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
-- BEING A TRANSPORT OF A GIVEN TERM
--
-- Every clause-level step that does not substitute is a transport, of one
-- of two shapes (`Cl-cast`, and `⟨ no ¬et ⟩cl`'s own `subst` at the
-- `_++ᶜ D` motive). Recording "X is some transport of h" makes them
-- compose, and two such records of the same `h` are equal by `uip` —
-- which is the whole of the both-non-eternal branch.
------------------------------------------------------------------------

IsSub : ∀ {Γ₀ Γ₁ C} → Γ₀ ⊢C⦂ C → Γ₁ ⊢C⦂ C → Set
IsSub {Γ₀} {Γ₁} {C} h X = Σ[ e ∈ Γ₀ ≡ Γ₁ ] X ≡ subst (_⊢C⦂ C) e h

isSub-refl : ∀ {Γ₀ C} → (h : Γ₀ ⊢C⦂ C) → IsSub h h
isSub-refl h = refl , refl

isSub-substC : ∀ {Γ₀ Γ₁ Γ₂ C} → {h : Γ₀ ⊢C⦂ C} → (X : Γ₁ ⊢C⦂ C) → (e : Γ₁ ≡ Γ₂)
             → IsSub h X → IsSub h (subst (_⊢C⦂ C) e X)
isSub-substC {C = C} {h = h} X e (e₀ , q) =
  trans e₀ e
  , trans (cong (subst (_⊢C⦂ C) e) q) (subst-fuseᶜ e₀ e h)

isSub-cast : ∀ {Γ₀ Γ₁ Γ₂ C} → {h : Γ₀ ⊢C⦂ C} → (X : Γ₁ ⊢C⦂ C) → (e : Γ₁ ≡ Γ₂)
           → IsSub h X → IsSub h (castᶜ e X)
isSub-cast {C = C} X e p =
  subst (IsSub _) (sym (castᶜ≡subst e X)) (isSub-substC X e p)

-- the two shapes the clause level actually presents

isSub-Cl : ∀ {Γ₀ Γ₁ Γ₂ D} → (op : Op) → (ε : E)
         → {h : Γ₀ ⊢C⦂ D ‼ (op-grade op ·ₑ ε)}
         → (X : Cl D op ε (Γ₁ ᴱ)) → (e : Γ₁ ≡ Γ₂)
         → IsSub h X → IsSub h (Cl-cast op ε e X)
isSub-Cl {D = D} op ε X e p =
  isSub-cast X
    (cong (λ Γ₃ → Γ₃ ᴱ ∷ type-of-gtype (param op)
                     ∷ [ mapᵉ (op-grade op) ]
                         (type-of-gtype (arity op) ⇒ D ‼ ε))
          e)
    p

-- the shape `⟨ no ¬et ⟩[_↦_]cl` transports at
isSub-substD : ∀ {Γ₀ Γ₁ Γ₂ C} → (Dc : Ctx) → {h : Γ₀ ⊢C⦂ C}
             → (X : (Γ₁ ++ᶜ Dc) ⊢C⦂ C) → (e : Γ₁ ≡ Γ₂)
             → IsSub h X
             → IsSub h (subst (λ Γ₃ → (Γ₃ ++ᶜ Dc) ⊢C⦂ C) e X)
isSub-substD Dc X e p =
  subst (IsSub _) (sym (subst-++ᶜʳ Dc e X))
        (isSub-substC X (cong (_++ᶜ Dc) e) p)

-- two transports of one term are transports of each other

isSub-reassoc : ∀ {Γ₀ Γ₁ Γ₂ C} → {h : Γ₀ ⊢C⦂ C} → {X : Γ₁ ⊢C⦂ C} → {Y : Γ₂ ⊢C⦂ C}
              → IsSub h X → IsSub h Y → IsSub Y X
isSub-reassoc {C = C} {h = h} (e , q) (e' , q') =
  trans (sym e') e
  , trans q
      (trans (cong (λ z → subst (_⊢C⦂ C) z h)
                   (uip {p = e} {q = trans e' (trans (sym e') e)}))
        (trans (sym (subst-fuseᶜ e' (trans (sym e') e) h))
               (cong (subst (_⊢C⦂ C) (trans (sym e') e)) (sym q'))))

isSub-trans : ∀ {Γ₀ Γ₁ Γ₂ C} → {h : Γ₀ ⊢C⦂ C} → {X : Γ₁ ⊢C⦂ C} → {Y : Γ₂ ⊢C⦂ C}
            → IsSub h X → IsSub X Y → IsSub h Y
isSub-trans {C = C} {h = h} (e , q) (e' , q') =
  trans e e'
  , trans q' (trans (cong (subst (_⊢C⦂ C) e') q) (subst-fuseᶜ e e' h))

isSub-uniq : ∀ {Γ₀ Γ₁ C} → {h : Γ₀ ⊢C⦂ C} → {X Y : Γ₁ ⊢C⦂ C}
           → IsSub h X → IsSub h Y → X ≡ Y
isSub-uniq {C = C} {h = h} (e , q) (e' , q') =
  trans q (trans (cong (λ z → subst (_⊢C⦂ C) z h) (uip {p = e} {q = e'}))
                 (sym q'))

-- BOTH ENTRIES NON-ETERNAL
--
-- Neither `⟨ no ¬et ⟩cl` substitutes, so each side is a tower of
-- transports over the same clause: four on the left, six on the right.

cl-swap-nn : ∀ {Γ B₁ B₂ D} → (¬et₁ : ¬ Eternal B₁) → (¬et₂ : ¬ Eternal B₂)
           → (Θ : Ctx) → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁) → (op : Op) → (ε : E)
           → ClSwap (no ¬et₁) (no ¬et₂) Θ H W₂ W₁ op ε

cl-swap-nn {Γ} {B₁} {B₂} {D} ¬et₁ ¬et₂ Θ H W₂ W₁ op ε =
  ≡→≐ᶜ (isSub-uniq lhs rhs)
  where
    Dc = Dcl D op ε

    lhs : IsSub (H op ε) (outerᴴ′ (no ¬et₁) (no ¬et₂) Θ H W₂ W₁ op ε)
    lhs =
      isSub-Cl op ε _ (castOf {Γ} {B₁} Θ)
        (isSub-substD Dc _ (ᴱ-drop-split ¬et₁ (bvar B₁ Θ))
          (isSub-Cl op ε _ (castOf {Γ ∷ B₁} {B₂} Θ)
            (isSub-substD Dc _ (ᴱ-drop-split ¬et₂ (bvar B₂ Θ))
              (isSub-refl (H op ε)))))

    rhs : IsSub (H op ε) (innerᴴ′ (no ¬et₁) (no ¬et₂) Θ H W₂ W₁ op ε)
    rhs =
      isSub-Cl op ε _ (castOf {Γ} {B₂} Θ)
        (isSub-substD Dc _ (ᴱ-drop-split ¬et₂ (bvar B₂ Θ))
          (isSub-Cl op ε _ (assocᴮ⁻ Γ B₂ Θ)
            (isSub-Cl op ε _ (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))
              (isSub-substD Dc _
                (ᴱ-drop-split ¬et₁ (bvar B₁ (([] ∷ B₂) ++ᶜ Θ)))
                (isSub-Cl op ε _ (assocᴮ Γ B₁ B₂ Θ)
                          (isSub-refl (H op ε)))))))

-- `sub-atᶜ` is natural in a transport of its prefix, its suffix, its term
-- and its value — which is what the eternal branches need, `cl-yes`
-- landing the two sides at contexts that agree only propositionally.
-- Proved by matching the two context equations; the `IsSub` premise then
-- forces the terms equal, its own equation being a loop.

sub-at-IsSub : ∀ {Γ₁ Γ₂ B C Θ₁ Θ₂} → (eΓ : Γ₁ ≡ Γ₂) → (eΘ : Θ₁ ≡ Θ₂)
             → (X₁ : ((Γ₁ ∷ B) ++ᶜ Θ₁) ⊢C⦂ C)
             → (X₂ : ((Γ₂ ∷ B) ++ᶜ Θ₂) ⊢C⦂ C)
             → IsSub X₁ X₂
             → (V₁ : Γ₁ ⊢V⦂ B) → (V₂ : Γ₂ ⊢V⦂ B)
             → subst (_⊢V⦂ B) eΓ V₁ ≡ V₂
             → IsSub (sub-atᶜ Θ₁ X₁ V₁) (sub-atᶜ Θ₂ X₂ V₂)
sub-at-IsSub refl refl X₁ X₂ (e , q) V .V refl =
  refl , cong (λ z → sub-atᶜ _ z V) (trans q (subst-loopᶜ e X₁))

-- The eternal restriction respects a transport of its context.

restrict-substᵛ : ∀ {Γ₁ Γ₂ A} → (e : Γ₁ ≡ Γ₂) → (et : Eternal A) → (V : Γ₁ ⊢V⦂ A)
                → eternal-val-restrict et (subst (_⊢V⦂ A) e V)
                ≡ subst (_⊢V⦂ A) (cong _ᴱ e) (eternal-val-restrict et V)
restrict-substᵛ refl et V = refl

------------------------------------------------------------------------
-- WHAT `⟨ yes et ⟩[_↦_]cl` REALLY IS
--
-- It is `sub-atᶜ` at the *restricted* contexts — but at the splitting's
-- own halves (`split-l x ᴱ`, `split-r x ᴱ ++ᶜ Dcl`), not at the contexts
-- those are propositionally equal to. That is `sub-wk-handle-et`'s
-- hard-won move, and the reason for it is the same: only there do
-- `split-++ʳ (∈-ᴱ-split et x) Dcl` and `split-≡-++ᶜ` have literally the
-- same halves, so `split→∈-unique` applies on the nose.
--
-- Both `⟨ yes et ⟩cl` and that `sub-atᶜ` are transports of one and the
-- same substituted clause, which is what the two lemmas below record;
-- `isSub-uniq` then identifies them.
------------------------------------------------------------------------

-- the substituted clause both sides are transports of

clBody : ∀ {Γ₀ A ρ D} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀)
       → (W : split-l x ⊢V⦂ A) → (H : Fam D (Γ₀ ᴱ)) → (op : Op) → (ε : E)
       → (split-l (split→∈ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε)))
            ++ᶜ split-r (split→∈ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε))))
         ⊢C⦂ D ‼ (op-grade op ·ₑ ε)
clBody {D = D} et x W H op ε =
  (H op ε) [ split→∈ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε))
             ↦ subst (_⊢V⦂ _)
                 (sym (split→∈-split-l
                        (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε))))
                 (eternal-val-restrict et W) ]c

-- the clause substitution is that, transported (definitionally)

cl-yes-raw : ∀ {Γ₀ A ρ D} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀)
           → (W : split-l x ⊢V⦂ A) → (H : Fam D (Γ₀ ᴱ)) → (op : Op) → (ε : E)
           → IsSub (clBody et x W H op ε) (⟨ yes et ⟩[ x ↦ W ]cl H op ε)
cl-yes-raw et x W H op ε = _ , refl

-- and so is the `sub-atᶜ` at the splitting's own halves

cl-yes-sub : ∀ {Γ₀ A ρ D} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀)
           → (W : split-l x ⊢V⦂ A) → (H : Fam D (Γ₀ ᴱ)) → (op : Op) → (ε : E)
           → (e : (Γ₀ ᴱ ++ᶜ Dcl D op ε)
                ≡ ((split-l x ᴱ ∷ A) ++ᶜ (split-r x ᴱ ++ᶜ Dcl D op ε)))
           → IsSub (clBody et x W H op ε)
                   (sub-atᶜ {split-l x ᴱ} {A} (split-r x ᴱ ++ᶜ Dcl D op ε)
                            (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) e (H op ε))
                            (eternal-val-restrict et W))
cl-yes-sub {Γ₀} {A} {ρ} {D} et x W H op ε e =
  isSub-cast _ (castOf {split-l x ᴱ} {A} (split-r x ᴱ ++ᶜ Dcl D op ε))
    (_ , sub-cast-C′ e (H op ε) v y ey U U' eU)
  where
    Dc = Dcl D op ε
    Γ₀' = split-l x ᴱ
    Θ₀' = split-r x ᴱ ++ᶜ Dc

    s = split-++ʳ (∈-ᴱ-split et x) Dc
    v = split→∈ s
    y = split→∈ (split-≡-++ᶜ {Γ₀' ∷ A} {Θ₀'})

    ey : subst (λ Γ₁ → A ∈[ ctx-grade Θ₀' ] Γ₁) e v ≡ y
    ey = split→∈-unique e s (split-≡-++ᶜ {Γ₀' ∷ A} {Θ₀'})

    U : split-l v ⊢V⦂ A
    U = subst (_⊢V⦂ A) (sym (split→∈-split-l s)) (eternal-val-restrict et W)

    U' : split-l y ⊢V⦂ A
    U' = bval Θ₀' (eternal-val-restrict et W)

    eU : subst (_⊢V⦂ A) (trans (split-l-cast e v) (cong split-l ey)) U ≡ U'
    eU =
      trans (subst-fuseᵛ (sym (split→∈-split-l s))
                         (trans (split-l-cast e v) (cong split-l ey))
                         (eternal-val-restrict et W))
        (trans (substᵛ-irr _
                  (sym (split→∈-split-l (split-≡-++ᶜ {Γ₀' ∷ A} {Θ₀'})))
                  (eternal-val-restrict et W))
               (sym (castᵛ≡subst _ (eternal-val-restrict et W))))

-- hence the clause substitution *is* that `sub-atᶜ`, transported

cl-yes : ∀ {Γ₀ A ρ D} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀)
       → (W : split-l x ⊢V⦂ A) → (H : Fam D (Γ₀ ᴱ)) → (op : Op) → (ε : E)
       → (e : (Γ₀ ᴱ ++ᶜ Dcl D op ε)
            ≡ ((split-l x ᴱ ∷ A) ++ᶜ (split-r x ᴱ ++ᶜ Dcl D op ε)))
       → IsSub (sub-atᶜ {split-l x ᴱ} {A} (split-r x ᴱ ++ᶜ Dcl D op ε)
                        (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) e (H op ε))
                        (eternal-val-restrict et W))
               (⟨ yes et ⟩[ x ↦ W ]cl H op ε)
cl-yes et x W H op ε e =
  isSub-reassoc (cl-yes-raw et x W H op ε) (cl-yes-sub et x W H op ε e)

-- The equation `cl-yes` wants is the splitting's own.

eCl : ∀ {Γ₀ A ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀) → (D : VType)
    → (op : Op) → (ε : E)
    → (Γ₀ ᴱ ++ᶜ Dcl D op ε)
    ≡ ((split-l x ᴱ ∷ A) ++ᶜ (split-r x ᴱ ++ᶜ Dcl D op ε))
eCl et x D op ε =
  sym (split-≡ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε)))

-- ONE ENTRY ETERNAL
--
-- Exactly one side of each order substitutes, and both substitute the
-- same restricted value — but `cl-yes` lands them at contexts that agree
-- only propositionally (`split-r (bvar B₁ Θ) ≡ Θ` against
-- `split-r (bvar B₁ (([] ∷ B₂) ++ᶜ Θ)) ≡ ([] ∷ B₂) ++ᶜ Θ`, whose eternal
-- parts coincide because `B₂` is not eternal). `sub-at-IsSub` aligns
-- them; everything else is transports.

cl-swap-en : ∀ {Γ B₁ B₂ D} → (et₁ : Eternal B₁) → (¬et₂ : ¬ Eternal B₂)
           → (Θ : Ctx) → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁) → (op : Op) → (ε : E)
           → ClSwap (yes et₁) (no ¬et₂) Θ H W₂ W₁ op ε

cl-swap-en {Γ} {B₁} {B₂} {D} et₁ ¬et₂ Θ H W₂ W₁ op ε =
  ≡→≐ᶜ (isSub-uniq lhs rhs)
  where
    Dc = Dcl D op ε
    Δ₂ = [] ∷ B₂
    Ŵ₂ = V-rename (wk-ren {A = B₁}) W₂

    xL = bvar {Γ} B₁ Θ
    xR = bvar {Γ} B₁ (Δ₂ ++ᶜ Θ)

    K : Fam D (((Γ ∷ B₁) ++ᶜ Θ) ᴱ)
    K = sub-atᴴ′ (no ¬et₂) Θ H Ŵ₂

    H' : Fam D (((Γ ∷ B₁) ++ᶜ (Δ₂ ++ᶜ Θ)) ᴱ)
    H' op' ε' = Cl-cast op' ε' (assocᴮ Γ B₁ B₂ Θ) (H op' ε')

    eL = eCl et₁ xL D op ε
    eR = eCl et₁ xR D op ε

    -- both substituted terms are transports of the clause
    isL : IsSub (H op ε) (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eL (K op ε))
    isL =
      isSub-substC _ eL
        (isSub-Cl op ε _ (castOf {Γ ∷ B₁} {B₂} Θ)
          (isSub-substD Dc _ (ᴱ-drop-split ¬et₂ (bvar B₂ Θ))
            (isSub-refl (H op ε))))

    isR : IsSub (H op ε) (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eR (H' op ε))
    isR =
      isSub-substC _ eR
        (isSub-Cl op ε _ (assocᴮ Γ B₁ B₂ Θ) (isSub-refl (H op ε)))

    -- and the two prefixes/suffixes agree
    eΓ : split-l xL ᴱ ≡ split-l xR ᴱ
    eΓ = cong _ᴱ (trans (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₁} {Θ}))
                        (sym (split→∈-split-l
                               (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ}))))

    -- `B₂` is not eternal, so the extra entry disappears from the
    -- restriction and the two suffixes' eternal parts coincide
    eΘᴱ : Θ ᴱ ≡ (Δ₂ ++ᶜ Θ) ᴱ
    eΘᴱ = sym (trans (ᴱ-++ᶜ Δ₂ Θ)
                (trans (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-drop {[]} {B₂} ¬et₂))
                       (++ᶜ-identityˡ {Θ ᴱ})))

    eΘ : (split-r xL ᴱ ++ᶜ Dc) ≡ (split-r xR ᴱ ++ᶜ Dc)
    eΘ = cong (_++ᶜ Dc)
              (trans (cong _ᴱ (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₁} {Θ})))
                (trans eΘᴱ
                       (cong _ᴱ (sym (split→∈-split-r
                                       (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ}))))))

    eV : subst (_⊢V⦂ B₁) eΓ
           (eternal-val-restrict et₁ (bval {Γ} Θ W₁))
       ≡ eternal-val-restrict et₁ (bval {Γ} (Δ₂ ++ᶜ Θ) W₁)
    eV =
      trans (cong (subst (_⊢V⦂ B₁) eΓ)
              (trans (cong (eternal-val-restrict et₁)
                           (castᵛ≡subst _ W₁))
                     (restrict-substᵛ _ et₁ W₁)))
        (trans (subst-fuseᵛ _ eΓ (eternal-val-restrict et₁ W₁))
          (trans (substᵛ-irr _ (cong _ᴱ (sym (split→∈-split-l
                                    (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ}))))
                             (eternal-val-restrict et₁ W₁))
            (trans (sym (restrict-substᵛ _ et₁ W₁))
                   (cong (eternal-val-restrict et₁)
                         (sym (castᵛ≡subst _ W₁))))))

    aligned : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                             (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eL (K op ε))
                             (eternal-val-restrict et₁ (bval Θ W₁)))
                    (sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                             (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eR (H' op ε))
                             (eternal-val-restrict et₁ (bval (Δ₂ ++ᶜ Θ) W₁)))
    aligned = sub-at-IsSub eΓ eΘ _ _ (isSub-reassoc isR isL) _ _ eV

    lhs : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                         (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eL (K op ε))
                         (eternal-val-restrict et₁ (bval Θ W₁)))
                (outerᴴ′ (yes et₁) (no ¬et₂) Θ H W₂ W₁ op ε)
    lhs =
      isSub-trans (cl-yes et₁ xL (bval Θ W₁) K op ε eL)
        (isSub-Cl op ε _ (castOf {Γ} {B₁} Θ) (isSub-refl _))

    rhs : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                         (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eL (K op ε))
                         (eternal-val-restrict et₁ (bval Θ W₁)))
                (innerᴴ′ (yes et₁) (no ¬et₂) Θ H W₂ W₁ op ε)
    rhs =
      isSub-trans aligned
        (isSub-trans (cl-yes et₁ xR (bval (Δ₂ ++ᶜ Θ) W₁) H' op ε eR)
          (isSub-Cl op ε _ (castOf {Γ} {B₂} Θ)
            (isSub-substD Dc _ (ᴱ-drop-split ¬et₂ (bvar B₂ Θ))
              (isSub-Cl op ε _ (assocᴮ⁻ Γ B₂ Θ)
                (isSub-Cl op ε _ (castOf {Γ} {B₁} (Δ₂ ++ᶜ Θ))
                          (isSub-refl _))))))

-- THE VALUE BRIDGE THE TWO REMAINING BRANCHES NEED
--
-- Where the left order weakens the outer value past `B₁` before
-- restricting it and the right order does not, the two agree — at a
-- *non-eternal* `B₁` the restriction of the weakening is the identity
-- (`ren-ᴱ-∷′ B₁ (no ¬et₁)` is `id-ren`), so this is
-- `eternal-val-restrict-ren` followed by `V-rename-id-≐`. Stated against
-- an arbitrary proof of the (only propositional) context equation, so the
-- caller may present it with whichever proof it has; `rewrite` then
-- reduces both `_ᴱ` and `ᴱ-∷-drop`, and `uip` finishes.

-- renaming along an identity-like renaming is the transport (the value
-- counterpart of `C-rename-eq-≐`)

V-rename-eq-≐ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {r : Ren [] Γ Γ'}
              → r ≐ʳ eq-ren e → (V : Γ ⊢V⦂ A)
              → V-rename r V ≐ᵛ subst (_⊢V⦂ A) e V
V-rename-eq-≐ refl h V = V-rename-id-≐ h V

restrict-wk-ne-≐ : ∀ {Γ₀ A B} → (¬et : ¬ Eternal B) → (et : Eternal A)
                 → (V : Γ₀ ⊢V⦂ A) → (e : Γ₀ ᴱ ≡ (Γ₀ ∷ B) ᴱ)
                 → eternal-val-restrict et (V-rename (wk-ren {A = B}) V)
                 ≐ᵛ subst (_⊢V⦂ A) e (eternal-val-restrict et V)
restrict-wk-ne-≐ {Γ₀} {A} {B} ¬et et V e =
  ≐ᵛ-trans (eternal-val-restrict-ren et (wk-ren {A = B}) V)
           (V-rename-eq-≐ e (restrict-wk-≐ ¬et [] e) (eternal-val-restrict et V))

-- and the action respects `_≐ᵛ_` in the value it substitutes

sub-atᶜ-≐ᵥ : ∀ {Γ' B C} → (Θ : Ctx) → (X : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C)
           → {V V' : Γ' ⊢V⦂ B} → V ≐ᵛ V'
           → sub-atᶜ Θ X V ≐ᶜ sub-atᶜ Θ X V'
sub-atᶜ-≐ᵥ Θ X eV = castᶜ-≐ _ (sub-≐ᶜ _ (castᵛ-≐ _ eV) (≐ᶜ-refl X))

-- two transports of `≐ᶜ`-related terms are `≐ᶜ`-related

isSub-≐ : ∀ {Γ₀ Γ₁ C} → {M M' : Γ₀ ⊢C⦂ C} → {X Y : Γ₁ ⊢C⦂ C}
        → IsSub M X → IsSub M' Y → M ≐ᶜ M' → X ≐ᶜ Y
isSub-≐ {C = C} {M' = M'} (e , q) (e' , q') eM =
  ≐ᶜ-trans (≡→≐ᶜ q)
    (≐ᶜ-trans (substᶜ-≐ e eM)
      (≡→≐ᶜ (trans (cong (λ z → subst (_⊢C⦂ C) z M') (uip {p = e} {q = e'}))
                   (sym q'))))

-- THE OUTER ENTRY ETERNAL, THE INNER ONE NOT
--
-- As `cl-swap-en`, except that here the two substituted values differ: the
-- left order restricts `W₂` *weakened past `B₁`*, the right order restricts
-- `W₂` itself. `restrict-wk-ne-≐` bridges them — at a non-eternal `B₁` the
-- restriction of that weakening is the identity — so the two `sub-atᶜ`s
-- agree only up to `_≐ᵛ_`, and the branch is `≐ᶜ` rather than `≡`.

cl-swap-ne : ∀ {Γ B₁ B₂ D} → (¬et₁ : ¬ Eternal B₁) → (et₂ : Eternal B₂)
           → (Θ : Ctx) → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁) → (op : Op) → (ε : E)
           → ClSwap (no ¬et₁) (yes et₂) Θ H W₂ W₁ op ε

cl-swap-ne {Γ} {B₁} {B₂} {D} ¬et₁ et₂ Θ H W₂ W₁ op ε =
  isSub-≐ lhs' rhs valStep
  where
    CT = D ‼ (op-grade op ·ₑ ε)
    Dc = Dcl D op ε
    Δ₂ = [] ∷ B₂
    Ŵ₂ = V-rename (wk-ren {A = B₁}) W₂

    xL = bvar {Γ ∷ B₁} B₂ Θ
    xR = bvar {Γ} B₂ Θ

    G : Fam D (((Γ ∷ B₂) ++ᶜ Θ) ᴱ)
    G = inner₀ᴴ′ (no ¬et₁) Θ H W₁

    eL = eCl et₂ xL D op ε
    eR = eCl et₂ xR D op ε

    VL = eternal-val-restrict et₂ (bval {Γ ∷ B₁} Θ Ŵ₂)
    VR = eternal-val-restrict et₂ (bval {Γ} Θ W₂)

    isL : IsSub (H op ε) (subst (_⊢C⦂ CT) eL (H op ε))
    isL = isSub-substC _ eL (isSub-refl (H op ε))

    isR : IsSub (H op ε) (subst (_⊢C⦂ CT) eR (G op ε))
    isR =
      isSub-substC _ eR
        (isSub-Cl op ε _ (assocᴮ⁻ Γ B₂ Θ)
          (isSub-Cl op ε _ (castOf {Γ} {B₁} (Δ₂ ++ᶜ Θ))
            (isSub-substD Dc _ (ᴱ-drop-split ¬et₁ (bvar B₁ (Δ₂ ++ᶜ Θ)))
              (isSub-Cl op ε _ (assocᴮ Γ B₁ B₂ Θ) (isSub-refl (H op ε))))))

    -- `B₁` is not eternal, so the two prefixes' eternal parts coincide
    eΓ : split-l xL ᴱ ≡ split-l xR ᴱ
    eΓ = trans (cong _ᴱ (split→∈-split-l (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ})))
           (trans (ᴱ-∷-drop {Γ} {B₁} ¬et₁)
                  (cong _ᴱ (sym (split→∈-split-l
                                  (split-≡-++ᶜ {Γ ∷ B₂} {Θ})))))

    eΘ : (split-r xL ᴱ ++ᶜ Dc) ≡ (split-r xR ᴱ ++ᶜ Dc)
    eΘ = cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
              (trans (split→∈-split-r (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ}))
                     (sym (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₂} {Θ}))))

    aligned : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                             (subst (_⊢C⦂ CT) eL (H op ε)) VL)
                    (sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                             (subst (_⊢C⦂ CT) eR (G op ε))
                             (subst (_⊢V⦂ B₂) eΓ VL))
    aligned = sub-at-IsSub eΓ eΘ _ _ (isSub-reassoc isR isL) VL _ refl

    lhs : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                         (subst (_⊢C⦂ CT) eL (H op ε)) VL)
                (outerᴴ′ (no ¬et₁) (yes et₂) Θ H W₂ W₁ op ε)
    lhs =
      isSub-trans (cl-yes et₂ xL (bval Θ Ŵ₂) H op ε eL)
        (isSub-Cl op ε _ (castOf {Γ} {B₁} Θ)
          (isSub-substD Dc _ (ᴱ-drop-split ¬et₁ (bvar B₁ Θ))
            (isSub-Cl op ε _ (castOf {Γ ∷ B₁} {B₂} Θ) (isSub-refl _))))

    rhs : IsSub (sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                         (subst (_⊢C⦂ CT) eR (G op ε)) VR)
                (innerᴴ′ (no ¬et₁) (yes et₂) Θ H W₂ W₁ op ε)
    rhs =
      isSub-trans (cl-yes et₂ xR (bval Θ W₂) G op ε eR)
        (isSub-Cl op ε _ (castOf {Γ} {B₂} Θ) (isSub-refl _))

    cL : (Γ ∷ B₁) ≡ split-l xL
    cL = sym (split→∈-split-l (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ}))

    cR : Γ ≡ split-l xR
    cR = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₂} {Θ}))

    e₀ : Γ ᴱ ≡ (Γ ∷ B₁) ᴱ
    e₀ = sym (ᴱ-∷-drop {Γ} {B₁} ¬et₁)

    eVal : subst (_⊢V⦂ B₂) eΓ VL ≐ᵛ VR
    eVal =
      ≐ᵛ-trans
        (≡→≐ᵛ (cong (subst (_⊢V⦂ B₂) eΓ)
                (trans (cong (eternal-val-restrict et₂) (castᵛ≡subst cL Ŵ₂))
                       (restrict-substᵛ cL et₂ Ŵ₂))))
        (≐ᵛ-trans
          (substᵛ-≐ eΓ (substᵛ-≐ (cong _ᴱ cL)
                                 (restrict-wk-ne-≐ ¬et₁ et₂ W₂ e₀)))
          (≡→≐ᵛ
            (trans (cong (subst (_⊢V⦂ B₂) eΓ)
                     (subst-fuseᵛ e₀ (cong _ᴱ cL)
                                  (eternal-val-restrict et₂ W₂)))
              (trans (subst-fuseᵛ (trans e₀ (cong _ᴱ cL)) eΓ
                                  (eternal-val-restrict et₂ W₂))
                (trans (substᵛ-irr (trans (trans e₀ (cong _ᴱ cL)) eΓ)
                                   (cong _ᴱ cR)
                                   (eternal-val-restrict et₂ W₂))
                  (trans (sym (restrict-substᵛ cR et₂ W₂))
                         (cong (eternal-val-restrict et₂)
                               (sym (castᵛ≡subst cR W₂)))))))))

    valStep : sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eR (G op ε))
                      (subst (_⊢V⦂ B₂) eΓ VL)
            ≐ᶜ sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                       (subst (_⊢C⦂ CT) eR (G op ε)) VR
    valStep = sub-atᶜ-≐ᵥ _ _ eVal

    lhs' : IsSub (sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                          (subst (_⊢C⦂ CT) eR (G op ε))
                          (subst (_⊢V⦂ B₂) eΓ VL))
                 (outerᴴ′ (no ¬et₁) (yes et₂) Θ H W₂ W₁ op ε)
    lhs' = isSub-reassoc lhs aligned

-- The eternal counterpart of `restrict-wk-ne-≐`: at an *eternal* `B` the
-- restriction of the weakening is the weakening again, so restricting a
-- `B`-weakened value is weakening its restriction — which is exactly the
-- value `outerᶜ` hands its inner step.

restrict-wk-et-≐ᵛ : ∀ {Γ₀ A B} → (etB : Eternal B) → (et : Eternal A)
                  → (V : Γ₀ ⊢V⦂ A) → (e : (Γ₀ ∷ B) ᴱ ≡ Γ₀ ᴱ ∷ B)
                  → eternal-val-restrict et (V-rename (wk-ren {A = B}) V)
                  ≐ᵛ subst (_⊢V⦂ A) (sym e)
                       (V-rename (wk-ren {A = B}) (eternal-val-restrict et V))
restrict-wk-et-≐ᵛ {Γ₀} {A} {B} etB et V e =
  ≐ᵛ-trans (eternal-val-restrict-ren et (wk-ren {A = B}) V)
    (≐ᵛ-trans (V-rename-≐ (restrict-wk-et-≐ etB [] refl e)
                          (eternal-val-restrict et V))
      (≐ᵛ-trans (V-rename-∘ (eq-ren (sym e)) (wk-ren ∘ʳ eq-ren refl)
                            (eternal-val-restrict et V))
        (≐ᵛ-trans
          (V-rename-cong (eq-ren (sym e))
            (≐ᵛ-trans (V-rename-∘ (wk-ren {A = B}) (eq-ren refl)
                                  (eternal-val-restrict et V))
                      (V-rename-cong (wk-ren {A = B})
                                     (V-rename-id-≐ ≐ʳ-refl _))))
          (V-rename-eq-≐ (sym e) ≐ʳ-refl _))))

-- The `_≐ᶜ_`-flavoured alignment the both-eternal branch needs. Unlike
-- `sub-at-IsSub` it takes the terms related only up to `_≐ᶜ_` and the
-- values only up to `_≐ᵛ_` — which is what the nested case forces, the
-- inner `sub-atᶜ`s' values being restrictions of *weakened* values, equal
-- to the unweakened ones only up to `restrict-wk-et-≐ᵛ`.

sub-at-≐ : ∀ {Γ₁ Γ₂ B C Θ₁ Θ₂} → (eΓ : Γ₁ ≡ Γ₂) → (eΘ : Θ₁ ≡ Θ₂)
         → (X₁ : ((Γ₁ ∷ B) ++ᶜ Θ₁) ⊢C⦂ C) → (X₂ : ((Γ₂ ∷ B) ++ᶜ Θ₂) ⊢C⦂ C)
         → (e : ((Γ₁ ∷ B) ++ᶜ Θ₁) ≡ ((Γ₂ ∷ B) ++ᶜ Θ₂))
         → X₂ ≐ᶜ subst (_⊢C⦂ C) e X₁
         → (V₁ : Γ₁ ⊢V⦂ B) → (V₂ : Γ₂ ⊢V⦂ B)
         → subst (_⊢V⦂ B) eΓ V₁ ≐ᵛ V₂
         → (e' : (Γ₁ ++ᶜ Θ₁) ≡ (Γ₂ ++ᶜ Θ₂))
         → sub-atᶜ Θ₂ X₂ V₂ ≐ᶜ subst (_⊢C⦂ C) e' (sub-atᶜ Θ₁ X₁ V₁)
sub-at-≐ {C = C} refl refl X₁ X₂ e eX V₁ V₂ eV e'
  rewrite uip {p = e} {q = refl} | uip {p = e'} {q = refl} =
  ≐ᶜ-trans (sub-atᶜ-≐ _ V₂ eX) (sub-atᶜ-≐ᵥ _ X₁ (≐ᵛ-sym eV))

-- The recursion the both-eternal branch makes, with its context given by
-- an equation rather than literally — as `sub-wk-C-cast`, and for the same
-- reason: casting the clause into shape is not structurally smaller, so the
-- termination checker would reject it. Forward-declared here and defined
-- after the induction, which puts it in the same recursive group; the
-- decrease is the clause `H op ε` against the `handle` node.

sub-swap-C-cast : ∀ {Γ B₁ B₂ Γ₀ C} → (Θ : Ctx)
                → (e : Γ₀ ≡ ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
                → (M : Γ₀ ⊢C⦂ C) → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
                → SubSwapC Θ (subst (_⊢C⦂ C) e M) W₂ W₁

-- BOTH ENTRIES ETERNAL
--
-- Both orders substitute twice, so after `cl-yes` on all four
-- substitutions the two sides *are* `outerᶜ` and `innerᶜ` at the
-- restricted contexts — at an eternal `B₁`, `(Γ ∷ B₁) ᴱ` is `Γ ᴱ ∷ B₁`,
-- and at an eternal `B₂` the right order's inner suffix is
-- `([] ∷ B₂) ++ᶜ Θ ᴱ ++ᶜ Dcl`, which is `inner₀ᶜ`'s own re-bracketing up
-- to one `++ᶜ-assoc`. So the branch is `sub-swap-C` at `Θ ᴱ ++ᶜ Dcl`, and
-- the rest is the nested alignment: `sub-at-≐` at the inner level, then
-- again at the outer, on each side.

cl-swap-ee : ∀ {Γ B₁ B₂ D} → (et₁ : Eternal B₁) → (et₂ : Eternal B₂)
           → (Θ : Ctx) → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁) → (op : Op) → (ε : E)
           → ClSwap (yes et₁) (yes et₂) Θ H W₂ W₁ op ε

cl-swap-ee {Γ} {B₁} {B₂} {D} et₁ et₂ Θ H W₂ W₁ op ε =
  ≐ᶜ-trans ee-left
    (≐ᶜ-trans (substᶜ-≐ eLfin (sub-swap-C-cast Θ' eXfull (H op ε) V₂ᴱ V₁ᴱ))
      (≐ᶜ-trans (≡→≐ᶜ (cong (λ z → subst (_⊢C⦂ CT) z (innerᶜ Θ' X V₂ᴱ V₁ᴱ))
                            (uip {p = eLfin} {q = eRfin})))
                (≐ᶜ-sym ee-right)))
  where
    CT = D ‼ (op-grade op ·ₑ ε)
    Dc = Dcl D op ε
    Δ₂ = [] ∷ B₂
    Θ' = Θ ᴱ ++ᶜ Dc
    Ŵ₂ = V-rename (wk-ren {A = B₁}) W₂

    V₁ᴱ = eternal-val-restrict et₁ W₁
    V₂ᴱ = eternal-val-restrict et₂ W₂

    -- the restriction of the doubly-extended context
    eᴱ : (Γ ∷ B₁ ∷ B₂) ᴱ ≡ Γ ᴱ ∷ B₁ ∷ B₂
    eᴱ = trans (ᴱ-∷-keep {Γ ∷ B₁} {B₂} et₂)
               (cong (_∷ B₂) (ᴱ-∷-keep {Γ} {B₁} et₁))

    eXfull : (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ ++ᶜ Dc) ≡ ((Γ ᴱ ∷ B₁ ∷ B₂) ++ᶜ Θ')
    eXfull =
      trans (cong (_++ᶜ Dc)
              (trans (ᴱ-++ᶜ (Γ ∷ B₁ ∷ B₂) Θ) (cong (_++ᶜ Θ ᴱ) eᴱ)))
            (++ᶜ-assoc (Γ ᴱ ∷ B₁ ∷ B₂) (Θ ᴱ) Dc)

    X : ((Γ ᴱ ∷ B₁ ∷ B₂) ++ᶜ Θ') ⊢C⦂ CT
    X = subst (_⊢C⦂ CT) eXfull (H op ε)

    ----------------------------------------------------------------
    -- the left order
    ----------------------------------------------------------------

    xL₁ = bvar {Γ} B₁ Θ
    xL₂ = bvar {Γ ∷ B₁} B₂ Θ

    K : Fam D (((Γ ∷ B₁) ++ᶜ Θ) ᴱ)
    K = sub-atᴴ′ (yes et₂) Θ H Ŵ₂

    eL₂ = eCl et₂ xL₂ D op ε
    eL₁ = eCl et₁ xL₁ D op ε

    VL₂ = eternal-val-restrict et₂ (bval {Γ ∷ B₁} Θ Ŵ₂)
    VL₁ = eternal-val-restrict et₁ (bval {Γ} Θ W₁)

    subatL₂ = sub-atᶜ {split-l xL₂ ᴱ} {B₂} (split-r xL₂ ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eL₂ (H op ε)) VL₂
    subatL₁ = sub-atᶜ {split-l xL₁ ᴱ} {B₁} (split-r xL₁ ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eL₁ (K op ε)) VL₁

    cL₂ : (Γ ∷ B₁) ≡ split-l xL₂
    cL₂ = sym (split→∈-split-l (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ}))

    cL₁ : Γ ≡ split-l xL₁
    cL₁ = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₁} {Θ}))

    eΓL₂ : split-l xL₂ ᴱ ≡ Γ ᴱ ∷ B₁
    eΓL₂ = trans (cong _ᴱ (sym cL₂)) (ᴱ-∷-keep {Γ} {B₁} et₁)

    eΘL₂ : (split-r xL₂ ᴱ ++ᶜ Dc) ≡ Θ'
    eΘL₂ = cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                (split→∈-split-r (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ}))

    eΓL₁ : split-l xL₁ ᴱ ≡ Γ ᴱ
    eΓL₁ = cong _ᴱ (sym cL₁)

    eΘL₁ : (split-r xL₁ ᴱ ++ᶜ Dc) ≡ Θ'
    eΘL₁ = cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₁} {Θ}))

    valL₂ : subst (_⊢V⦂ B₂) eΓL₂ VL₂ ≐ᵛ V-rename (wk-ren {A = B₁}) V₂ᴱ
    valL₂ =
      ≐ᵛ-trans
        (≡→≐ᵛ (cong (subst (_⊢V⦂ B₂) eΓL₂)
                (trans (cong (eternal-val-restrict et₂) (castᵛ≡subst cL₂ Ŵ₂))
                       (restrict-substᵛ cL₂ et₂ Ŵ₂))))
        (≐ᵛ-trans
          (substᵛ-≐ eΓL₂
            (substᵛ-≐ (cong _ᴱ cL₂)
              (restrict-wk-et-≐ᵛ et₁ et₂ W₂ (ᴱ-∷-keep {Γ} {B₁} et₁))))
          (≡→≐ᵛ
            (trans (cong (subst (_⊢V⦂ B₂) eΓL₂)
                     (subst-fuseᵛ (sym (ᴱ-∷-keep {Γ} {B₁} et₁)) (cong _ᴱ cL₂)
                                  (V-rename (wk-ren {A = B₁}) V₂ᴱ)))
              (trans (subst-fuseᵛ _ eΓL₂ (V-rename (wk-ren {A = B₁}) V₂ᴱ))
                     (substᵛ-irr _ refl (V-rename (wk-ren {A = B₁}) V₂ᴱ))))))

    valL₁ : subst (_⊢V⦂ B₁) eΓL₁ VL₁ ≐ᵛ V₁ᴱ
    valL₁ =
      ≡→≐ᵛ
        (trans (cong (subst (_⊢V⦂ B₁) eΓL₁)
                 (trans (cong (eternal-val-restrict et₁) (castᵛ≡subst cL₁ W₁))
                        (restrict-substᵛ cL₁ et₁ W₁)))
          (trans (subst-fuseᵛ (cong _ᴱ cL₁) eΓL₁ V₁ᴱ)
                 (substᵛ-irr _ refl V₁ᴱ)))

    -- the inner alignment
    Oᴵ = sub-atᶜ {Γ ᴱ ∷ B₁} {B₂} Θ' X (V-rename (wk-ren {A = B₁}) V₂ᴱ)

    eIL : ((split-l xL₂ ᴱ ∷ B₂) ++ᶜ (split-r xL₂ ᴱ ++ᶜ Dc))
        ≡ ((Γ ᴱ ∷ B₁ ∷ B₂) ++ᶜ Θ')
    eIL = cong₂ (λ Γ₀ Θ₀ → (Γ₀ ∷ B₂) ++ᶜ Θ₀) eΓL₂ eΘL₂

    eIL' : (split-l xL₂ ᴱ ++ᶜ (split-r xL₂ ᴱ ++ᶜ Dc)) ≡ ((Γ ᴱ ∷ B₁) ++ᶜ Θ')
    eIL' = cong₂ _++ᶜ_ eΓL₂ eΘL₂

    oI : Oᴵ ≐ᶜ subst (_⊢C⦂ CT) eIL' subatL₂
    oI =
      sub-at-≐ eΓL₂ eΘL₂ (subst (_⊢C⦂ CT) eL₂ (H op ε)) X eIL
        (≡→≐ᶜ (sym (trans (subst-fuseᶜ eL₂ eIL (H op ε))
                          (cong (λ z → subst (_⊢C⦂ CT) z (H op ε))
                                (uip {p = trans eL₂ eIL} {q = eXfull})))))
        VL₂ (V-rename (wk-ren {A = B₁}) V₂ᴱ) valL₂ eIL'

    kIs : IsSub subatL₂ (subst (_⊢C⦂ CT) eL₁ (K op ε))
    kIs =
      isSub-substC _ eL₁
        (isSub-Cl op ε _ (castOf {Γ ∷ B₁} {B₂} Θ)
          (cl-yes et₂ xL₂ (bval Θ Ŵ₂) H op ε eL₂))

    eOL : ((split-l xL₁ ᴱ ∷ B₁) ++ᶜ (split-r xL₁ ᴱ ++ᶜ Dc))
        ≡ ((Γ ᴱ ∷ B₁) ++ᶜ Θ')
    eOL = cong₂ (λ Γ₀ Θ₀ → (Γ₀ ∷ B₁) ++ᶜ Θ₀) eΓL₁ eΘL₁

    eOL' : (split-l xL₁ ᴱ ++ᶜ (split-r xL₁ ᴱ ++ᶜ Dc)) ≡ (Γ ᴱ ++ᶜ Θ')
    eOL' = cong₂ _++ᶜ_ eΓL₁ eΘL₁

    termO : Oᴵ ≐ᶜ subst (_⊢C⦂ CT) eOL (subst (_⊢C⦂ CT) eL₁ (K op ε))
    termO =
      ≐ᶜ-trans oI
        (≡→≐ᶜ
          (trans (cong (λ z → subst (_⊢C⦂ CT) z subatL₂)
                       (uip {p = eIL'} {q = trans (proj₁ kIs) eOL}))
            (trans (sym (subst-fuseᶜ (proj₁ kIs) eOL subatL₂))
                   (cong (subst (_⊢C⦂ CT) eOL) (sym (proj₂ kIs))))))

    oO : outerᶜ Θ' X V₂ᴱ V₁ᴱ ≐ᶜ subst (_⊢C⦂ CT) eOL' subatL₁
    oO =
      sub-at-≐ eΓL₁ eΘL₁ (subst (_⊢C⦂ CT) eL₁ (K op ε)) Oᴵ eOL termO
               VL₁ V₁ᴱ valL₁ eOL'

    lIs : IsSub subatL₁ (outerᴴ′ (yes et₁) (yes et₂) Θ H W₂ W₁ op ε)
    lIs =
      isSub-Cl op ε _ (castOf {Γ} {B₁} Θ)
        (cl-yes et₁ xL₁ (bval Θ W₁) K op ε eL₁)

    eLfin : (Γ ᴱ ++ᶜ Θ') ≡ (((Γ ++ᶜ Θ) ᴱ) ++ᶜ Dc)
    eLfin = trans (sym eOL') (proj₁ lIs)

    ee-left : outerᴴ′ (yes et₁) (yes et₂) Θ H W₂ W₁ op ε
            ≐ᶜ subst (_⊢C⦂ CT) eLfin (outerᶜ Θ' X V₂ᴱ V₁ᴱ)
    ee-left =
      ≐ᶜ-trans (≡→≐ᶜ (proj₂ lIs))
        (≐ᶜ-sym
          (≐ᶜ-trans (substᶜ-≐ eLfin oO)
            (≡→≐ᶜ (trans (subst-fuseᶜ eOL' eLfin subatL₁)
                         (cong (λ z → subst (_⊢C⦂ CT) z subatL₁) uip)))))

    ----------------------------------------------------------------
    -- the right order
    ----------------------------------------------------------------

    xR₂ = bvar {Γ} B₂ Θ
    xR₁ = bvar {Γ} B₁ (Δ₂ ++ᶜ Θ)

    H' : Fam D (((Γ ∷ B₁) ++ᶜ (Δ₂ ++ᶜ Θ)) ᴱ)
    H' op' ε' = Cl-cast op' ε' (assocᴮ Γ B₁ B₂ Θ) (H op' ε')

    G : Fam D (((Γ ∷ B₂) ++ᶜ Θ) ᴱ)
    G = inner₀ᴴ′ (yes et₁) Θ H W₁

    eR₁ = eCl et₁ xR₁ D op ε
    eR₂ = eCl et₂ xR₂ D op ε

    VR₁ = eternal-val-restrict et₁ (bval {Γ} (Δ₂ ++ᶜ Θ) W₁)
    VR₂ = eternal-val-restrict et₂ (bval {Γ} Θ W₂)

    subatR₁ = sub-atᶜ {split-l xR₁ ᴱ} {B₁} (split-r xR₁ ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eR₁ (H' op ε)) VR₁
    subatR₂ = sub-atᶜ {split-l xR₂ ᴱ} {B₂} (split-r xR₂ ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eR₂ (G op ε)) VR₂

    cR₁ : Γ ≡ split-l xR₁
    cR₁ = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ}))

    cR₂ : Γ ≡ split-l xR₂
    cR₂ = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₂} {Θ}))

    eΓR₁ : split-l xR₁ ᴱ ≡ Γ ᴱ
    eΓR₁ = cong _ᴱ (sym cR₁)

    eΓR₂ : split-l xR₂ ᴱ ≡ Γ ᴱ
    eΓR₂ = cong _ᴱ (sym cR₂)

    -- at an eternal `B₂` the extra entry survives the restriction, and
    -- one `++ᶜ-assoc` turns it into `inner₀ᶜ`'s own bracketing
    eΘR₁ : (split-r xR₁ ᴱ ++ᶜ Dc) ≡ (Δ₂ ++ᶜ Θ')
    eΘR₁ =
      trans (cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                  (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ})))
        (trans (cong (_++ᶜ Dc)
                 (trans (ᴱ-++ᶜ Δ₂ Θ)
                        (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-keep {[]} {B₂} et₂))))
               (++ᶜ-assoc Δ₂ (Θ ᴱ) Dc))

    eΘR₂ : (split-r xR₂ ᴱ ++ᶜ Dc) ≡ Θ'
    eΘR₂ = cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₂} {Θ}))

    valR₁ : subst (_⊢V⦂ B₁) eΓR₁ VR₁ ≐ᵛ V₁ᴱ
    valR₁ =
      ≡→≐ᵛ
        (trans (cong (subst (_⊢V⦂ B₁) eΓR₁)
                 (trans (cong (eternal-val-restrict et₁) (castᵛ≡subst cR₁ W₁))
                        (restrict-substᵛ cR₁ et₁ W₁)))
          (trans (subst-fuseᵛ (cong _ᴱ cR₁) eΓR₁ V₁ᴱ)
                 (substᵛ-irr _ refl V₁ᴱ)))

    valR₂ : subst (_⊢V⦂ B₂) eΓR₂ VR₂ ≐ᵛ V₂ᴱ
    valR₂ =
      ≡→≐ᵛ
        (trans (cong (subst (_⊢V⦂ B₂) eΓR₂)
                 (trans (cong (eternal-val-restrict et₂) (castᵛ≡subst cR₂ W₂))
                        (restrict-substᵛ cR₂ et₂ W₂)))
          (trans (subst-fuseᵛ (cong _ᴱ cR₂) eΓR₂ V₂ᴱ)
                 (substᵛ-irr _ refl V₂ᴱ)))

    Iᴵ = sub-atᶜ {Γ ᴱ} {B₁} (Δ₂ ++ᶜ Θ')
                 (castᶜ (assocᴮ (Γ ᴱ) B₁ B₂ Θ') X) V₁ᴱ

    eIR : ((split-l xR₁ ᴱ ∷ B₁) ++ᶜ (split-r xR₁ ᴱ ++ᶜ Dc))
        ≡ ((Γ ᴱ ∷ B₁) ++ᶜ (Δ₂ ++ᶜ Θ'))
    eIR = cong₂ (λ Γ₀ Θ₀ → (Γ₀ ∷ B₁) ++ᶜ Θ₀) eΓR₁ eΘR₁

    eIR' : (split-l xR₁ ᴱ ++ᶜ (split-r xR₁ ᴱ ++ᶜ Dc)) ≡ (Γ ᴱ ++ᶜ (Δ₂ ++ᶜ Θ'))
    eIR' = cong₂ _++ᶜ_ eΓR₁ eΘR₁

    iI : Iᴵ ≐ᶜ subst (_⊢C⦂ CT) eIR' subatR₁
    iI =
      sub-at-≐ eΓR₁ eΘR₁ (subst (_⊢C⦂ CT) eR₁ (H' op ε))
               (castᶜ (assocᴮ (Γ ᴱ) B₁ B₂ Θ') X) eIR
        (≡→≐ᶜ
          (trans (castᶜ≡subst (assocᴮ (Γ ᴱ) B₁ B₂ Θ') X)
            (trans (subst-fuseᶜ eXfull (assocᴮ (Γ ᴱ) B₁ B₂ Θ') (H op ε))
              (trans (cong (λ z → subst (_⊢C⦂ CT) z (H op ε))
                           (uip {q = trans (cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                                                 (assocᴮ Γ B₁ B₂ Θ))
                                           (trans eR₁ eIR)}))
                (trans (sym (subst-fuseᶜ (cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                                               (assocᴮ Γ B₁ B₂ Θ))
                                         (trans eR₁ eIR) (H op ε)))
                  (trans (cong (subst (_⊢C⦂ CT) (trans eR₁ eIR))
                               (sym (castᶜ≡subst _ (H op ε))))
                         (sym (subst-fuseᶜ eR₁ eIR (H' op ε)))))))))
        VR₁ V₁ᴱ valR₁ eIR'

    gIs : IsSub subatR₁ (subst (_⊢C⦂ CT) eR₂ (G op ε))
    gIs =
      isSub-substC _ eR₂
        (isSub-Cl op ε _ (assocᴮ⁻ Γ B₂ Θ)
          (isSub-Cl op ε _ (castOf {Γ} {B₁} (Δ₂ ++ᶜ Θ))
            (cl-yes et₁ xR₁ (bval (Δ₂ ++ᶜ Θ) W₁) H' op ε eR₁)))

    eOR : ((split-l xR₂ ᴱ ∷ B₂) ++ᶜ (split-r xR₂ ᴱ ++ᶜ Dc))
        ≡ ((Γ ᴱ ∷ B₂) ++ᶜ Θ')
    eOR = cong₂ (λ Γ₀ Θ₀ → (Γ₀ ∷ B₂) ++ᶜ Θ₀) eΓR₂ eΘR₂

    eOR' : (split-l xR₂ ᴱ ++ᶜ (split-r xR₂ ᴱ ++ᶜ Dc)) ≡ (Γ ᴱ ++ᶜ Θ')
    eOR' = cong₂ _++ᶜ_ eΓR₂ eΘR₂

    termOR : castᶜ (assocᴮ⁻ (Γ ᴱ) B₂ Θ') Iᴵ
           ≐ᶜ subst (_⊢C⦂ CT) eOR (subst (_⊢C⦂ CT) eR₂ (G op ε))
    termOR =
      ≐ᶜ-trans (≡→≐ᶜ (castᶜ≡subst (assocᴮ⁻ (Γ ᴱ) B₂ Θ') Iᴵ))
        (≐ᶜ-trans (substᶜ-≐ (assocᴮ⁻ (Γ ᴱ) B₂ Θ') iI)
          (≡→≐ᶜ
            (trans (subst-fuseᶜ eIR' (assocᴮ⁻ (Γ ᴱ) B₂ Θ') subatR₁)
              (trans (cong (λ z → subst (_⊢C⦂ CT) z subatR₁)
                           (uip {q = trans (proj₁ gIs) eOR}))
                (trans (sym (subst-fuseᶜ (proj₁ gIs) eOR subatR₁))
                       (cong (subst (_⊢C⦂ CT) eOR) (sym (proj₂ gIs))))))))

    iO : innerᶜ Θ' X V₂ᴱ V₁ᴱ ≐ᶜ subst (_⊢C⦂ CT) eOR' subatR₂
    iO =
      sub-at-≐ eΓR₂ eΘR₂ (subst (_⊢C⦂ CT) eR₂ (G op ε))
               (castᶜ (assocᴮ⁻ (Γ ᴱ) B₂ Θ') Iᴵ) eOR termOR
               VR₂ V₂ᴱ valR₂ eOR'

    rIs : IsSub subatR₂ (innerᴴ′ (yes et₁) (yes et₂) Θ H W₂ W₁ op ε)
    rIs =
      isSub-Cl op ε _ (castOf {Γ} {B₂} Θ)
        (cl-yes et₂ xR₂ (bval Θ W₂) G op ε eR₂)

    eRfin : (Γ ᴱ ++ᶜ Θ') ≡ (((Γ ++ᶜ Θ) ᴱ) ++ᶜ Dc)
    eRfin = trans (sym eOR') (proj₁ rIs)

    ee-right : innerᴴ′ (yes et₁) (yes et₂) Θ H W₂ W₁ op ε
             ≐ᶜ subst (_⊢C⦂ CT) eRfin (innerᶜ Θ' X V₂ᴱ V₁ᴱ)
    ee-right =
      ≐ᶜ-trans (≡→≐ᶜ (proj₂ rIs))
        (≐ᶜ-sym
          (≐ᶜ-trans (substᶜ-≐ eRfin iO)
            (≡→≐ᶜ (trans (subst-fuseᶜ eOR' eRfin subatR₂)
                         (cong (λ z → subst (_⊢C⦂ CT) z subatR₂) uip)))))

-- The dispatch. `sub-atᴴ` *is* `sub-atᴴ′ (eternal? B)`, so instantiating
-- the two decisions recovers the statement on the nose.

sub-swap-clause : ∀ {Γ B₁ B₂ D} → (Θ : Ctx)
                → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
                → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
                → (op : Op) → (ε : E)
                → outerᴴ Θ H W₂ W₁ op ε ≐ᶜ innerᴴ Θ H W₂ W₁ op ε

sub-swap-clause {Γ} {B₁} {B₂} Θ H W₂ W₁ op ε =
  go (eternal? B₁) (eternal? B₂)
  where
    go : (dec₁ : Dec (Eternal B₁)) → (dec₂ : Dec (Eternal B₂))
       → ClSwap dec₁ dec₂ Θ H W₂ W₁ op ε
    go (no ¬et₁)  (no ¬et₂)  = cl-swap-nn ¬et₁ ¬et₂ Θ H W₂ W₁ op ε
    go (yes et₁)  (no ¬et₂)  = cl-swap-en et₁  ¬et₂ Θ H W₂ W₁ op ε
    go (no ¬et₁)  (yes et₂)  = cl-swap-ne ¬et₁ et₂  Θ H W₂ W₁ op ε
    go (yes et₁)  (yes et₂)  = cl-swap-ee et₁  et₂  Θ H W₂ W₁ op ε

sub-swap-handle : ∀ {Γ B₁ B₂ A D ε ε'} → (Θ : Ctx)
                → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
                → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
                → (N : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ D ‼ ε')
                → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
                → SubSwapC Θ M W₂ W₁
                → SubSwapC (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₂ W₁
                → SubSwapC Θ (handle M `with H `in N) W₂ W₁

sub-swap-handle {Γ} {B₁} {B₂} {A} {ε = ε} Θ M H N W₂ W₁ ihM ihN =
  ≐ᶜ-trans
    (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁)
                       (sub-at-handle Θ M H N Ŵ₂))
                 (sub-at-handle Θ (sub-atᶜ Θ M Ŵ₂) (sub-atᴴ Θ H Ŵ₂)
                                (sub-atᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N Ŵ₂) W₁)))
    (≐ᶜ-trans
      (handle-≐ ihM (λ op ε'' → sub-swap-clause Θ H W₂ W₁ op ε'') ihN)
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂)
                              (inner₀-handle Θ M H N W₁))
                        (sub-at-handle Θ (inner₀ᶜ Θ M W₁) (inner₀ᴴ Θ H W₁)
                                       (inner₀ᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₁)
                                       W₂)))))
  where
    Ŵ₂ = V-rename (wk-ren {A = B₁}) W₂


sub-swap-V : ∀ {Γ B₁ B₂ A} → (Θ : Ctx) → (U : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A)
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
           → SubSwapV Θ U W₂ W₁

sub-swap-C : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C)
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
           → SubSwapC Θ M W₂ W₁

sub-swap-V Θ (var f y) W₂ W₁ = sub-swap-var Θ y f W₂ W₁

sub-swap-V {Γ} {B₁} {B₂} Θ (const c) W₂ W₁ =
  ≐ᵛ-trans (≡→≐ᵛ (trans (cong (λ z → sub-atᵛ Θ z W₁) (sub-at-const Θ (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-const Θ W₁)))
           (≡→≐ᵛ (sym (trans (cong (λ z → sub-atᵛ Θ z W₂)
                                   (inner₀-const Θ W₁))
                             (sub-at-const Θ W₂))))

sub-swap-V {Γ} {B₁} {B₂} Θ ⋆ W₂ W₁ =
  ≐ᵛ-trans (≡→≐ᵛ (trans (cong (λ z → sub-atᵛ Θ z W₁) (sub-at-⋆ Θ (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-⋆ Θ W₁)))
           (≡→≐ᵛ (sym (trans (cong (λ z → sub-atᵛ Θ z W₂) (inner₀-⋆ Θ W₁))
                             (sub-at-⋆ Θ W₂))))

sub-swap-V {Γ} {B₁} {B₂} Θ ⦉ V₁ , V₂ ⦊ W₂ W₁ =
  ≐ᵛ-trans (≡→≐ᵛ (trans (cong (λ z → sub-atᵛ Θ z W₁) (sub-at-pair Θ V₁ V₂ (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-pair Θ (sub-atᵛ Θ V₁ (V-rename (wk-ren {A = B₁}) W₂))
                                       (sub-atᵛ Θ V₂ (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᵛ-trans (pair-≐ (sub-swap-V Θ V₁ W₂ W₁) (sub-swap-V Θ V₂ W₂ W₁))
      (≡→≐ᵛ (sym (trans (cong (λ z → sub-atᵛ Θ z W₂)
                              (inner₀-pair Θ V₁ V₂ W₁))
                        (sub-at-pair Θ (inner₀ᵛ Θ V₁ W₁)
                                       (inner₀ᵛ Θ V₂ W₁) W₂)))))

sub-swap-V {Γ} {B₁} {B₂} {A ⇒ C} Θ (lam N) W₂ W₁ =
  ≐ᵛ-trans (≡→≐ᵛ (trans (cong (λ z → sub-atᵛ Θ z W₁) (sub-at-lam Θ N (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-lam Θ (sub-atᶜ (Θ ∷ A) N (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᵛ-trans (lam-≐ (sub-swap-C (Θ ∷ A) N W₂ W₁))
      (≡→≐ᵛ (sym (trans (cong (λ z → sub-atᵛ Θ z W₂) (inner₀-lam Θ N W₁))
                        (sub-at-lam Θ (inner₀ᶜ (Θ ∷ A) N W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (return V) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-ret Θ V (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-ret Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (return-≐ (sub-swap-V Θ V W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-ret Θ V W₁))
                        (sub-at-ret Θ (inner₀ᵛ Θ V W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (_⨟_ {A = A} {ε = ε} M N) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-seq Θ M N (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-seq Θ (sub-atᶜ Θ M (V-rename (wk-ren {A = B₁}) W₂))
                                      (sub-atᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (seq-≐ (sub-swap-C Θ M W₂ W₁)
                     (sub-swap-C (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-seq Θ M N W₁))
                        (sub-at-seq Θ (inner₀ᶜ Θ M W₁)
                                      (inner₀ᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (V · U) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-app Θ V U (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-app Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂))
                                      (sub-atᵛ Θ U (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (app-≐ (sub-swap-V Θ V W₂ W₁) (sub-swap-V Θ U W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-app Θ V U W₁))
                        (sub-at-app Θ (inner₀ᵛ Θ V W₁)
                                      (inner₀ᵛ Θ U W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (match_`in_ {A = A₁} {B = A₂} V N) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-match Θ V N (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-match Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂))
                                        (sub-atᶜ (Θ ∷ A₁ ∷ A₂) N (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (match-≐ (sub-swap-V Θ V W₂ W₁)
                       (sub-swap-C (Θ ∷ A₁ ∷ A₂) N W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-match Θ V N W₁))
                        (sub-at-match Θ (inner₀ᵛ Θ V W₁)
                                        (inner₀ᶜ (Θ ∷ A₁ ∷ A₂) N W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (absurd V) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-absurd Θ V (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-absurd Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (absurd-≐ (sub-swap-V Θ V W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-absurd Θ V W₁))
                        (sub-at-absurd Θ (inner₀ᵛ Θ V W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (perform op V N) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-perform Θ V N (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-perform Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂))
                           (sub-atᶜ (Θ ⟨ mapᵉ (op-grade op) ⟩
                                       ∷ type-of-gtype (arity op)) N (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (perform-≐ (sub-swap-V Θ V W₂ W₁)
                         (sub-swap-C (Θ ⟨ mapᵉ (op-grade op) ⟩
                                        ∷ type-of-gtype (arity op)) N W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂)
                              (inner₀-perform Θ V N W₁))
                        (sub-at-perform Θ (inner₀ᵛ Θ V W₁)
                           (inner₀ᶜ (Θ ⟨ mapᵉ (op-grade op) ⟩
                                       ∷ type-of-gtype (arity op)) N W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (delay τ M) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-delay Θ M (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-delay Θ (sub-atᶜ (Θ ⟨ of-natʳ τ ⟩) M (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (delay-≐ (sub-swap-C (Θ ⟨ of-natʳ τ ⟩) M W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-delay Θ M W₁))
                        (sub-at-delay Θ (inner₀ᶜ (Θ ⟨ of-natʳ τ ⟩) M W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (box {A = A} {ρ = ρ} V M) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁)
                              (sub-at-box Θ V M (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-box Θ
                           (sub-atᵛ (Θ ⟨ ρ ⟩) V (V-rename (wk-ren {A = B₁}) W₂))
                           (sub-atᶜ (Θ ∷ [ ρ ] A) M
                                    (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (box-≐ (sub-swap-V (Θ ⟨ ρ ⟩) V W₂ W₁)
                     (sub-swap-C (Θ ∷ [ ρ ] A) M W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-box Θ V M W₁))
                        (sub-at-box Θ (inner₀ᵛ (Θ ⟨ ρ ⟩) V W₁)
                                      (inner₀ᶜ (Θ ∷ [ ρ ] A) M W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (coerce p M) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-coerce Θ M (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-coerce Θ (sub-atᶜ Θ M (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (coerce-≐ (sub-swap-C Θ M W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-coerce Θ M W₁))
                        (sub-at-coerce Θ (inner₀ᶜ Θ M W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (handle_`with_`in {A = A} {ε = ε} M H N) W₂ W₁ =
  sub-swap-handle Θ M H N W₂ W₁
    (sub-swap-C Θ M W₂ W₁) (sub-swap-C (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₂ W₁)

sub-swap-C {Γ} {B₁} {B₂} Θ (unbox {A = A} w V M) W₂ W₁ =
  sub-swap-unbox Θ w V M W₂ W₁ (sub-swap-C (Θ ∷ A) M W₂ W₁)

sub-swap-C-cast Θ refl M W₂ W₁ = sub-swap-C Θ M W₂ W₁

