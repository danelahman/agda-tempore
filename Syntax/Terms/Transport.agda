------------------------------------------------------------------------
-- Retyping a term along a context equality.                          --
--                                                                    --
-- `castᵛ`/`castᶜ` transport a term along an equality of contexts, and --
-- the laws below push that transport through each term former. Being --
-- defined by matching on the proof, a cast computes away at `refl`,   --
-- which is what lets the inversion lemmas match it off.               --
--                                                                    --
-- Up to `_≐ᵛ_` a cast is the renaming action along `eq-ren`           --
-- (`V-rename-eq-≐`), so this family is the action of the subgroupoid  --
-- of context equalities.                                             --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Terms.Transport (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts      Spec
open import Syntax.Language      Spec
open import Syntax.RenActions    Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

open import Syntax.Renamings.Equivalence Spec
open import Syntax.Terms.Equivalence     Spec
open import Syntax.Renamings.Coherence   Spec

-- RETYPING ALONG A CONTEXT EQUALITY

-- Defined by matching on the proof, not as `subst`: the rigid head is what
-- lets the unifier solve the clause-swap metas, and what lets the inversion
-- lemmas match a cast off.

castᵛ : ∀ {Γ Γ' A} → Γ ≡ Γ' → Γ ⊢V⦂ A → Γ' ⊢V⦂ A
castᵛ refl V = V

castᶜ : ∀ {Γ Γ' C} → Γ ≡ Γ' → Γ ⊢C⦂ C → Γ' ⊢C⦂ C
castᶜ refl M = M

-- A cast is irrelevant in its equality proof (UIP), and passes through a
-- binder: the two facts that let the structural laws below be stated with
-- whichever proof each side happens to produce.

castᵛ-irr : ∀ {Γ Γ' A} → (e e' : Γ ≡ Γ') → (V : Γ ⊢V⦂ A) → castᵛ e V ≡ castᵛ e' V
castᵛ-irr e e' V = cong (λ z → castᵛ z V) uip

castᶜ-irr : ∀ {Γ Γ' C} → (e e' : Γ ≡ Γ') → (M : Γ ⊢C⦂ C) → castᶜ e M ≡ castᶜ e' M
castᶜ-irr e e' M = cong (λ z → castᶜ z M) uip

cast-lam : ∀ {Γ Γ' A C} → (e : Γ ≡ Γ') → (M : Γ ∷ A ⊢C⦂ C)
         → castᵛ e (lam M) ≡ lam (castᶜ (cong (_∷ A) e) M)
cast-lam refl M = refl

cast-const : ∀ {Γ Γ' b} → (e : Γ ≡ Γ') → {c : BaseConstants b}
           → castᵛ e (const c) ≡ const c
cast-const refl = refl

cast-⋆ : ∀ {Γ Γ'} → (e : Γ ≡ Γ') → castᵛ e ⋆ ≡ ⋆
cast-⋆ refl = refl

cast-pair : ∀ {Γ Γ' A B} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ A} → {W : Γ ⊢V⦂ B}
          → castᵛ e ⦉ V , W ⦊ ≡ ⦉ castᵛ e V , castᵛ e W ⦊
cast-pair refl = refl

cast-ret : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ A}
         → castᶜ e (return V) ≡ return (castᵛ e V)
cast-ret refl = refl

cast-app : ∀ {Γ Γ' A C} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ A ⇒ C} → {W : Γ ⊢V⦂ A}
         → castᶜ e (V · W) ≡ (castᵛ e V) · (castᵛ e W)
cast-app refl = refl

cast-absurd : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ Empty}
            → castᶜ {C = C} e (absurd V) ≡ absurd (castᵛ e V)
cast-absurd refl = refl

cast-coerce : ∀ {Γ Γ' A ε ε'} → (e : Γ ≡ Γ') → {p : ε ≾ₑ ε'} → {M : Γ ⊢C⦂ A ‼ ε}
            → castᶜ e (coerce p M) ≡ coerce p (castᶜ e M)
cast-coerce refl = refl

-- The binding formers put their body at an *extended* context, so the cast
-- transported there is `cong` of the extension.

cast-delay : ∀ {Γ Γ' A ε τ} → (e : Γ ≡ Γ')
           → {M : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε}
           → castᶜ e (delay τ M) ≡ delay τ (castᶜ (cong (_⟨ of-natʳ τ ⟩) e) M)
cast-delay refl = refl

cast-perform : ∀ {Γ Γ' A ε} → (e : Γ ≡ Γ') → {op : Op}
             → {V : Γ ⊢V⦂ type-of-gtype (param op)}
             → {M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                      ⊢C⦂ A ‼ ε}
             → castᶜ e (perform op V M)
             ≡ perform op (castᵛ e V)
                 (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                         ∷ type-of-gtype (arity op)) e) M)
cast-perform refl = refl

cast-match : ∀ {Γ Γ' A B C} → (e : Γ ≡ Γ')
           → {V : Γ ⊢V⦂ A |×| B} → {M : Γ ∷ A ∷ B ⊢C⦂ C}
           → castᶜ e (match V `in M)
           ≡ match (castᵛ e V) `in (castᶜ (cong (λ Γ₀ → Γ₀ ∷ A ∷ B) e) M)
cast-match refl = refl

cast-box : ∀ {Γ Γ' A C ρ} → (e : Γ ≡ Γ')
         → {V : Γ ⟨ ρ ⟩ ⊢V⦂ A} → {M : Γ ∷ [ ρ ] A ⊢C⦂ C}
         → castᶜ e (box V M)
         ≡ box (castᵛ (cong (_⟨ ρ ⟩) e) V) (castᶜ (cong (_∷ [ ρ ] A) e) M)
cast-box refl = refl

cast-handle : ∀ {Γ Γ' A B ε ε'} → (e : Γ ≡ Γ')
            → {M : Γ ⊢C⦂ A ‼ ε}
            → {H : (op : Op) → (ε'' : E) →
                     Γ ᴱ ∷ type-of-gtype (param op)
                       ∷ [ mapᵉ (op-grade op) ]
                           (type-of-gtype (arity op) ⇒ B ‼ ε'')
                     ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
            → {N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
            → castᶜ e (handle M `with H `in N)
            ≡ handle (castᶜ e M)
              `with (λ op ε'' →
                       castᶜ (cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                                             ∷ [ mapᵉ (op-grade op) ]
                                                 (type-of-gtype (arity op) ⇒ B ‼ ε''))
                              e)
                             (H op ε''))
              `in (castᶜ (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) e) N)
cast-handle refl = refl

-- SUBSTITUTION RESPECTS A CONTEXT TRANSPORT
--
-- Relocating a term's context relocates the variable it is substituted at, and
-- the replacement's own context along with it. All four hold by matching the
-- equality, but they are what lets a substitution be moved across the
-- `ᴱ`/`++ᶜ` transports that `handle`'s eternal clause accumulates.

split-l-cast : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ') → (x : A ∈[ ρ ] Γ)
             → split-l x ≡ split-l (subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x)
split-l-cast refl x = refl

split-r-cast : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ') → (x : A ∈[ ρ ] Γ)
             → split-r x ≡ split-r (subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x)
split-r-cast refl x = refl

sub-cast-C : ∀ {Γ Γ' A C ρ} → (e : Γ ≡ Γ') → (M : Γ ⊢C⦂ C) → (x : A ∈[ ρ ] Γ)
           → (W : split-l x ⊢V⦂ A)
           → subst (_⊢C⦂ C) (cong₂ _++ᶜ_ (split-l-cast e x) (split-r-cast e x))
               (M [ x ↦ W ]c)
           ≡ (subst (_⊢C⦂ C) e M)
               [ subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x
               ↦ subst (_⊢V⦂ A) (split-l-cast e x) W ]c
sub-cast-C refl M x W = refl

sub-cast-V : ∀ {Γ Γ' A B ρ} → (e : Γ ≡ Γ') → (V : Γ ⊢V⦂ B) → (x : A ∈[ ρ ] Γ)
           → (W : split-l x ⊢V⦂ A)
           → subst (_⊢V⦂ B) (cong₂ _++ᶜ_ (split-l-cast e x) (split-r-cast e x))
               (V [ x ↦ W ]v)
           ≡ (subst (_⊢V⦂ B) e V)
               [ subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x
               ↦ subst (_⊢V⦂ A) (split-l-cast e x) W ]v
sub-cast-V refl V x W = refl

-- The same, packaged for a caller that knows where the transport sends the
-- substituted variable and what value it carries there. Both equations are
-- matched, so the two substitutions are literally the same one.

sub-cast-C′ : ∀ {Γ Γ' A C ρ} → (e : Γ ≡ Γ') → (M : Γ ⊢C⦂ C)
            → (x : A ∈[ ρ ] Γ) → (y : A ∈[ ρ ] Γ')
            → (ey : subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x ≡ y)
            → (U : split-l x ⊢V⦂ A) → (U' : split-l y ⊢V⦂ A)
            → subst (_⊢V⦂ A) (trans (split-l-cast e x) (cong split-l ey)) U ≡ U'
            → (subst (_⊢C⦂ C) e M) [ y ↦ U' ]c
            ≡ subst (_⊢C⦂ C)
                (cong₂ _++ᶜ_ (trans (split-l-cast e x) (cong split-l ey))
                             (trans (split-r-cast e x) (cong split-r ey)))
                (M [ x ↦ U ]c)
sub-cast-C′ refl M x .x refl U .U refl = refl

-- Transports along context equalities, all normalised to `subst` so that a
-- chain of them fuses and collapses by `uip`.

castᶜ≡subst : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → (M : Γ ⊢C⦂ C)
            → castᶜ e M ≡ subst (_⊢C⦂ C) e M
castᶜ≡subst refl M = refl

subst-++ᶜʳ : ∀ {Γ Γ' C} → (D : Ctx) → (e : Γ ≡ Γ') → (M : (Γ ++ᶜ D) ⊢C⦂ C)
           → subst (λ Γ₀ → (Γ₀ ++ᶜ D) ⊢C⦂ C) e M
           ≡ subst (_⊢C⦂ C) (cong (_++ᶜ D) e) M
subst-++ᶜʳ D refl M = refl

-- Three transports whose composite is a loop are the identity.

subst-loop₃ : ∀ {Γ₁ Γ₂ Γ₃ C} → (e₁ : Γ₁ ≡ Γ₂) → (e₂ : Γ₂ ≡ Γ₃) → (e₃ : Γ₃ ≡ Γ₁)
            → (M : Γ₁ ⊢C⦂ C)
            → subst (_⊢C⦂ C) e₃ (subst (_⊢C⦂ C) e₂ (subst (_⊢C⦂ C) e₁ M)) ≡ M
subst-loop₃ refl refl e₃ M =
  cong (λ z → subst (_⊢C⦂ _) z M) (uip {p = e₃} {q = refl})

-- Two transports fuse into one; a transport that returns to its own context is
-- the identity. Together they collapse a tower of any height.

subst-fuseᶜ : ∀ {Γ₁ Γ₂ Γ₃ C} → (e : Γ₁ ≡ Γ₂) → (e' : Γ₂ ≡ Γ₃) → (M : Γ₁ ⊢C⦂ C)
            → subst (_⊢C⦂ C) e' (subst (_⊢C⦂ C) e M)
            ≡ subst (_⊢C⦂ C) (trans e e') M
subst-fuseᶜ refl refl M = refl

subst-loopᶜ : ∀ {Γ C} → (e : Γ ≡ Γ) → (M : Γ ⊢C⦂ C) → subst (_⊢C⦂ C) e M ≡ M
subst-loopᶜ {C = C} e M = cong (λ z → subst (_⊢C⦂ C) z M) (uip {p = e} {q = refl})

subst-subst-sym′ : ∀ {a p} {X : Set a} {P : X → Set p} {u v : X}
                 → (e : u ≡ v) → (w : P v)
                 → subst P e (subst P (sym e) w) ≡ w
subst-subst-sym′ refl w = refl

-- Relocating a weakening's two contexts. Renaming algebra, so it belongs
-- upstream with `_≐ʳ_` (see the cleanup list); it is here because nothing else
-- uses it yet. With both equalities matched the conjugating renamings are
-- identity-like, and any two proofs of the (only propositional) context
-- equations agree by `uip`.

cong-ren-wk-cast-≐ : ∀ {B} → (Γ₀ Γ₁ Θ₀ Θ₁ : Ctx) → Γ₀ ≡ Γ₁ → Θ₀ ≡ Θ₁
                   → (e  : Γ₁ ++ᶜ Θ₁ ≡ Γ₀ ++ᶜ Θ₀)
                   → (e' : (Γ₀ ∷ B) ++ᶜ Θ₀ ≡ (Γ₁ ∷ B) ++ᶜ Θ₁)
                   → cong-ren {Γ'' = Θ₁} (wk-ren {A = B})
                   ≐ʳ (eq-ren e ∘ʳ cong-ren {Γ'' = Θ₀} (wk-ren {A = B})
                                ∘ʳ eq-ren e')
cong-ren-wk-cast-≐ {B} Γ₀ Γ₁ Θ₀ Θ₁ refl refl e e' =
  ≐ʳ-sym
    (≐ʳ-trans (∘ʳ-≐ (eq-ren-≐ e refl)
                    (∘ʳ-≐ ≐ʳ-refl (eq-ren-≐ e' refl)))
              (≐ʳ-trans (∘ʳ-identityˡ-≐ _) (∘ʳ-identityʳ-≐ _)))

castʳ : ∀ {Γ Γ' Δ ρ} → Γ ≡ Γ' → Ren [] Γ (Δ ⟨ ρ ⟩) → Ren [] Γ' (Δ ⟨ ρ ⟩)
castʳ refl w = w

cast-unbox : ∀ {Γ Γ' A C ρ Δ} → (e : Γ ≡ Γ')
           → {w : Ren [] Γ (Δ ⟨ ρ ⟩)} → {V : Δ ⊢V⦂ [ ρ ] A} → {M : Γ ∷ A ⊢C⦂ C}
           → castᶜ e (unbox w V M)
           ≡ unbox (castʳ e w) V (castᶜ (cong (_∷ A) e) M)
cast-unbox refl = refl

-- A cast does not move the resource variable an `unbox` names.

unbox-img-castʳ : ∀ {Γ Γ' A ρ Δ} → (e : Γ ≡ Γ') → (w : Ren [] Γ (Δ ⟨ ρ ⟩))
                 → (V : Δ ⊢V⦂ [ ρ ] A)
                 → unbox-img (castʳ e w) V
                 ≡ (proj₁ (unbox-img w V)
                   , subst (λ Γ₀ → [ ρ ] A ∈[ proj₁ (unbox-img w V) ] Γ₀) e
                           (proj₂ (unbox-img w V)))
unbox-img-castʳ refl w V = refl

cast-seq : ∀ {Γ Γ' A B ε ε'} → (e : Γ ≡ Γ')
         → {M : Γ ⊢C⦂ A ‼ ε} → {N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
         → castᶜ e (M ⨟ N)
         ≡ (castᶜ e M) ⨟ (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) e) N)
cast-seq refl = refl

-- A handler clause's typing, and clause families indexed by it.

Cl : (B : VType) → (op : Op) → (ε₃ : E) → Ctx → Set
Cl B op ε₃ Γ₀ =
  Γ₀ ∷ type-of-gtype (param op)
    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₃)
  ⊢C⦂ B ‼ (op-grade op ·ₑ ε₃)

Fam : VType → Ctx → Set
Fam B Γ₀ = (op : Op) → (ε : E) → Cl B op ε Γ₀

-- Relocating a clause along an equality of the context it restricts. Written in
-- exactly the shape `cast-handle` produces, so that the two agree on the nose
-- and no `castᶜ-irr` is needed at any use site.

Cl-cast : ∀ {Γ Γ' B} → (op : Op) → (ε : E) → Γ ≡ Γ'
        → Cl B op ε (Γ ᴱ) → Cl B op ε (Γ' ᴱ)
Cl-cast {B = B} op ε e X =
  castᶜ (cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              e)
        X

-- Transport is a congruence for the term equivalence.

castᶜ-≐ : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → {M M' : Γ ⊢C⦂ C}
        → M ≐ᶜ M' → castᶜ e M ≐ᶜ castᶜ e M'
castᶜ-≐ refl eM = eM

castᵛ-≐ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {V V' : Γ ⊢V⦂ A}
        → V ≐ᵛ V' → castᵛ e V ≐ᵛ castᵛ e V'
castᵛ-≐ refl eV = eV

------------------------------------------------------------------------
-- VALUE-LEVEL TRANSPORT ALGEBRA
------------------------------------------------------------------------

castᵛ≡subst : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (V : Γ ⊢V⦂ A)
            → castᵛ e V ≡ subst (_⊢V⦂ A) e V
castᵛ≡subst refl V = refl

subst-fuseᵛ : ∀ {Γ₁ Γ₂ Γ₃ A} → (e : Γ₁ ≡ Γ₂) → (e' : Γ₂ ≡ Γ₃) → (V : Γ₁ ⊢V⦂ A)
            → subst (_⊢V⦂ A) e' (subst (_⊢V⦂ A) e V)
            ≡ subst (_⊢V⦂ A) (trans e e') V
subst-fuseᵛ refl refl V = refl

-- Two transport chains out of the same value agree by `uip`.

substᵛ-irr : ∀ {Γ Γ' A} → (e e' : Γ ≡ Γ') → (V : Γ ⊢V⦂ A)
           → subst (_⊢V⦂ A) e V ≡ subst (_⊢V⦂ A) e' V
substᵛ-irr e e' V = cong (λ z → subst (_⊢V⦂ _) z V) (uip {p = e} {q = e'})

-- The eternal restriction of a value respects a context transport.

restrict-castᵛ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (et : Eternal A) → (V : Γ ⊢V⦂ A)
               → eternal-val-restrict et (castᵛ e V)
               ≡ castᵛ (cong _ᴱ e) (eternal-val-restrict et V)
restrict-castᵛ refl et V = refl


-- Fusing two transports, on values and on the target of a variable.

castᵛ-fuse : ∀ {Γ₁ Γ₂ Γ₃ A} → (e : Γ₁ ≡ Γ₂) → (e' : Γ₂ ≡ Γ₃) → (V : Γ₁ ⊢V⦂ A)
           → castᵛ e' (castᵛ e V) ≡ castᵛ (trans e e') V
castᵛ-fuse refl refl V = refl

Var-cast-fuse : ∀ {Γ₁ Γ₂ Γ₃ A} → (e : Γ₁ ≡ Γ₂) → (e' : Γ₂ ≡ Γ₃) → (t : Var Γ₁ A)
              → Var-cast e' (Var-cast e t) ≡ Var-cast (trans e e') t
Var-cast-fuse refl refl t = refl
