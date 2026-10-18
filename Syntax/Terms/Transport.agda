------------------------------------------------------------------------
-- Retyping a term along a context equality.                          --
--                                                                    --
-- `castᵛ`/`castᶜ` transport a term along an equality of contexts,    --
-- and the laws below push that transport through each term former.   --
-- Being defined by matching on the proof, a cast computes away at    --
-- `refl`.                                                            --
--                                                                    --
-- A cast is the renaming action along `eq-ren` (`V-rename-eq-≡`),    --
-- so this family is the action of the subgroupoid of context         --
-- equalities.                                                        --
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

-- Defined by matching on the proof, not as `subst`: the head stays rigid for
-- the unifier and for the inversion lemmas below to match off.

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

cast-pair : ∀ {Γ Γ' A B} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ A} → {W : Γ ⊢V⦂ B}
          → castᵛ e ⦉ V , W ⦊ ≡ ⦉ castᵛ e V , castᵛ e W ⦊
cast-pair refl = refl

cast-ret : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ A}
         → castᶜ e (return V) ≡ return (castᵛ e V)
cast-ret refl = refl

cast-app : ∀ {Γ Γ' A C} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ A ⇒ C} → {W : Γ ⊢V⦂ A}
         → castᶜ e (V · W) ≡ (castᵛ e V) · (castᵛ e W)
cast-app refl = refl

cast-subV : ∀ {Γ Γ' A A'} → (e : Γ ≡ Γ') → {p : A <:ᵛ A'} → {V : Γ ⊢V⦂ A}
          → castᵛ e (subV V p) ≡ subV (castᵛ e V) p
cast-subV refl = refl

cast-subC : ∀ {Γ Γ' C C'} → (e : Γ ≡ Γ') → {p : C <:ᶜ C'} → {M : Γ ⊢C⦂ C}
          → castᶜ e (subC M p) ≡ subC (castᶜ e M) p
cast-subC refl = refl

cast-if : ∀ {Γ Γ' C} → (e : Γ ≡ Γ')
        → {V : Γ ⊢V⦂ Bool} → {M N : Γ ⊢C⦂ C}
        → castᶜ e (if V `then M `else N)
        ≡ if (castᵛ e V) `then (castᶜ e M) `else (castᶜ e N)
cast-if refl = refl

cast-cmp : ∀ {Γ Γ' A ⋈} → (e : Γ ≡ Γ')
         → {V W : Γ ⊢V⦂ A} → {et : Eternal A}
         → castᶜ e (cmp ⋈ V W et) ≡ cmp ⋈ (castᵛ e V) (castᵛ e W) et
cast-cmp refl = refl

-- The binding formers put their body at an *extended* context, so the cast
-- transported there is `cong` of the extension.

cast-delay : ∀ {Γ Γ' A ε τ} → (e : Γ ≡ Γ')
           → {M : Γ ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε}
           → castᶜ e (delay τ M) ≡ delay τ (castᶜ (cong (_⟨ of-durʳ τ ⟩) e) M)
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

cast-succ : ∀ {Γ Γ'} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ Nat}
          → castᵛ e (succ V) ≡ succ (castᵛ e V)
cast-succ refl = refl

cast-caseℕ : ∀ {Γ Γ' C} → (e : Γ ≡ Γ')
           → {V : Γ ⊢V⦂ Nat} → {M : Γ ⊢C⦂ C} → {N : Γ ∷ Nat ⊢C⦂ C}
           → castᶜ e (caseℕ V `zero M `succ N)
           ≡ caseℕ (castᵛ e V) `zero (castᶜ e M)
                               `succ (castᶜ (cong (_∷ Nat) e) N)
cast-caseℕ refl = refl

cast-inl : ∀ {Γ Γ' A B} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ A}
         → castᵛ e (inl {B = B} V) ≡ inl (castᵛ e V)
cast-inl refl = refl

cast-inr : ∀ {Γ Γ' A B} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ B}
         → castᵛ e (inr {A = A} V) ≡ inr (castᵛ e V)
cast-inr refl = refl

cast-nil : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → castᵛ e (nil {A = A}) ≡ nil
cast-nil refl = refl

cast-cons : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ A} → {W : Γ ⊢V⦂ |List| A}
          → castᵛ e (cons V W) ≡ cons (castᵛ e V) (castᵛ e W)
cast-cons refl = refl

cast-caseL : ∀ {Γ Γ' A C} → (e : Γ ≡ Γ')
           → {V : Γ ⊢V⦂ |List| A} → {M : Γ ⊢C⦂ C} → {N : Γ ∷ A ∷ |List| A ⊢C⦂ C}
           → castᶜ e (caseL V `nil M `cons N)
           ≡ caseL (castᵛ e V) `nil (castᶜ e M)
                               `cons (castᶜ (cong (λ Δ → Δ ∷ A ∷ |List| A) e) N)
cast-caseL refl = refl

cast-recL : ∀ {Γ Γ' A B ε} → (e : Γ ≡ Γ')
          → {V : Γ ⊢V⦂ |List| A} → {M : Γ ⊢C⦂ B ‼ ε}
          → {N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε}
          → {p : ε ·ₑ ε ≾ₑ ε}
          → castᶜ e (recL V M N p)
          ≡ recL (castᵛ e V) (castᶜ e M)
                 (castᶜ (cong (λ Δ → (Δ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B) e) N) p
cast-recL refl = refl

cast-recℕ : ∀ {Γ Γ' B ε} → (e : Γ ≡ Γ')
          → {V : Γ ⊢V⦂ Nat} → {M : Γ ⊢C⦂ B ‼ ε}
          → {N : (Γ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε}
          → {p : ε ·ₑ ε ≾ₑ ε}
          → castᶜ e (recℕ V M N p)
          ≡ recℕ (castᵛ e V) (castᶜ e M)
                 (castᶜ (cong (λ Δ → (Δ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B) e) N) p
cast-recℕ refl = refl

cast-case+ : ∀ {Γ Γ' A B C} → (e : Γ ≡ Γ')
           → {V : Γ ⊢V⦂ A |+| B} → {M : Γ ∷ A ⊢C⦂ C} → {N : Γ ∷ B ⊢C⦂ C}
           → castᶜ e (case+ V `inl M `inr N)
           ≡ case+ (castᵛ e V) `inl (castᶜ (cong (_∷ A) e) M)
                               `inr (castᶜ (cong (_∷ B) e) N)
cast-case+ refl = refl

cast-box : ∀ {Γ Γ' A C ρ} → (e : Γ ≡ Γ')
         → {V : Γ ⟨ ρ ⟩ ⊢V⦂ A} → {M : Γ ∷ [ ρ ] A ⊢C⦂ C}
         → castᶜ e (box _ V M)
         ≡ box _ (castᵛ (cong (_⟨ ρ ⟩) e) V) (castᶜ (cong (_∷ [ ρ ] A) e) M)
cast-box refl = refl

cast-handle : ∀ {Γ Γ' A B ε ε'} → (e : Γ ≡ Γ')
            → {M : Γ ⊢C⦂ A ‼ ε}
            → {H : (op : Op) → (ε'' : E) →
                     Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                       ∷ [ mapᵉ (op-grade op) ]
                           (type-of-gtype (arity op) ⇒ B ‼ ε'')
                     ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
            → {N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
            → castᶜ e (handle M `with H `in N)
            ≡ handle (castᶜ e M)
              `with (λ op ε'' →
                       castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                                             ∷ [ mapᵉ (op-grade op) ]
                                                 (type-of-gtype (arity op) ⇒ B ‼ ε''))
                              e)
                             (H op ε''))
              `in (castᶜ (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) e) N)
cast-handle refl = refl

-- The same, for a caller that has the transported splitting in hand rather than
-- as a transport. Two splittings of the same context agree (`split-unique`), so
-- no equation relating them is needed.

sub-cast-C′ : ∀ {Γ Γ' Γ₁ Γ₂ A C} → (e : Γ ≡ Γ') → (M : Γ ⊢C⦂ C)
            → (s : Γ₁ ∷ A , Γ₂ split Γ) → (s' : Γ₁ ∷ A , Γ₂ split Γ')
            → (W : Γ₁ ⊢V⦂ A)
            → (subst (_⊢C⦂ C) e M) [ s' ↦ W ]c ≡ M [ s ↦ W ]c
sub-cast-C′ refl M s s' W = cong (λ z → M [ z ↦ W ]c) (split-unique s' s)

-- Transports along context equalities, all normalised to `subst` so that a
-- chain of them fuses and collapses by `uip`.

castᶜ≡subst : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → (M : Γ ⊢C⦂ C)
            → castᶜ e M ≡ subst (_⊢C⦂ C) e M
castᶜ≡subst refl M = refl

subst-++ᶜʳ : ∀ {Γ Γ' C} → (D : Ctx) → (e : Γ ≡ Γ') → (M : (Γ ++ᶜ D) ⊢C⦂ C)
           → subst (λ Γ₀ → (Γ₀ ++ᶜ D) ⊢C⦂ C) e M
           ≡ subst (_⊢C⦂ C) (cong (_++ᶜ D) e) M
subst-++ᶜʳ D refl M = refl

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

castʳ : ∀ {Γ Γ' Δ} → Γ ≡ Γ' → Ren [] Γ Δ → Ren [] Γ' Δ
castʳ refl w = w

-- A cast relocates the resource variable an `unbox` names along `Var-cast`.

cast-unbox : ∀ {Γ Γ' A A₀ C ρ₀ ρ'} → (e : Γ ≡ Γ')
           → {x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ} → {rel : ρ' ≾ᵣ ρ₀} → {p : A₀ <:ᵛ A}
           → {M : Γ ∷ A ⊢C⦂ C}
           → castᶜ e (unbox x rel p M)
           ≡ unbox (proj₂ (Var-cast e (ρ' , x))) rel p
                   (castᶜ (cong (_∷ A) e) M)
cast-unbox refl = refl

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

-- Relocating a clause along an equality of the context it is barred from.
-- Written in exactly the shape `cast-handle` produces, so that the two agree on
-- the nose and no `castᶜ-irr` is needed at any use site.

Cl-cast : ∀ {Γ Γ' B} → (op : Op) → (ε : E) → Γ ≡ Γ'
        → Cl B op ε (Γ ⟨ ⊤ᵣ ⟩) → Cl B op ε (Γ' ⟨ ⊤ᵣ ⟩)
Cl-cast {B = B} op ε e X =
  castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              e)
        X

-- Transport is a congruence for the term equivalence.

castᶜ-≡ : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → {M M' : Γ ⊢C⦂ C}
        → M ≡ M' → castᶜ e M ≡ castᶜ e M'
castᶜ-≡ e = cong (castᶜ e)

castᵛ-≡ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {V V' : Γ ⊢V⦂ A}
        → V ≡ V' → castᵛ e V ≡ castᵛ e V'
castᵛ-≡ e = cong (castᵛ e)

castᵛ≡subst : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (V : Γ ⊢V⦂ A)
            → castᵛ e V ≡ subst (_⊢V⦂ A) e V
castᵛ≡subst refl V = refl

