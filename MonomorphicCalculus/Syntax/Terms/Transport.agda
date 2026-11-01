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

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.Syntax.Terms.Transport (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts        Spec
open import MonomorphicCalculus.Syntax.Terms           Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming        Spec
open import MonomorphicCalculus.Syntax.Substitution    Spec
open import MonomorphicCalculus.Syntax.Types           Spec

open import MonomorphicCalculus.Syntax.Renaming.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Terms.Equivalence     Spec
open import MonomorphicCalculus.Syntax.Renaming.Coherence    Spec

-- Defined by matching on the proof, not as `subst`: the head stays rigid for
-- the unifier and for the inversion lemmas below to match off.

castᵛ : ∀ {Γ Γ' A} → Γ ≡ Γ' → Γ ⊢ᵛ⦂ A → Γ' ⊢ᵛ⦂ A
castᵛ refl V = V

castᶜ : ∀ {Γ Γ' C} → Γ ≡ Γ' → Γ ⊢ᶜ⦂ C → Γ' ⊢ᶜ⦂ C
castᶜ refl M = M

-- A cast is irrelevant in its equality proof (UIP), and passes through a
-- binder: the two facts that let the structural laws below be stated with
-- whichever proof each side happens to produce.

castᵛ-irr : ∀ {Γ Γ' A} → (e e' : Γ ≡ Γ') → (V : Γ ⊢ᵛ⦂ A) → castᵛ e V ≡ castᵛ e' V
castᵛ-irr e e' V = cong (λ z → castᵛ z V) uip

castᶜ-irr : ∀ {Γ Γ' C} → (e e' : Γ ≡ Γ') → (M : Γ ⊢ᶜ⦂ C) → castᶜ e M ≡ castᶜ e' M
castᶜ-irr e e' M = cong (λ z → castᶜ z M) uip

cast-fun : ∀ {Γ Γ' A C} → (e : Γ ≡ Γ') → (M : Γ ∷ A ⊢ᶜ⦂ C)
         → castᵛ e (fun M) ≡ fun (castᶜ (cong (_∷ A) e) M)
cast-fun refl M = refl

cast-pair : ∀ {Γ Γ' A B} → (e : Γ ≡ Γ') → {V : Γ ⊢ᵛ⦂ A} → {W : Γ ⊢ᵛ⦂ B}
          → castᵛ e ⦉ V , W ⦊ ≡ ⦉ castᵛ e V , castᵛ e W ⦊
cast-pair refl = refl

cast-ret : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {V : Γ ⊢ᵛ⦂ A}
         → castᶜ e (return V) ≡ return (castᵛ e V)
cast-ret refl = refl

cast-app : ∀ {Γ Γ' A C} → (e : Γ ≡ Γ') → {V : Γ ⊢ᵛ⦂ A ⇒ C} → {W : Γ ⊢ᵛ⦂ A}
         → castᶜ e (V · W) ≡ (castᵛ e V) · (castᵛ e W)
cast-app refl = refl

cast-subV : ∀ {Γ Γ' A A'} → (e : Γ ≡ Γ') → {p : A <:ᵛ A'} → {V : Γ ⊢ᵛ⦂ A}
          → castᵛ e (subV V p) ≡ subV (castᵛ e V) p
cast-subV refl = refl

cast-subC : ∀ {Γ Γ' C C'} → (e : Γ ≡ Γ') → {p : C <:ᶜ C'} → {M : Γ ⊢ᶜ⦂ C}
          → castᶜ e (subC M p) ≡ subC (castᶜ e M) p
cast-subC refl = refl

cast-if : ∀ {Γ Γ' C} → (e : Γ ≡ Γ')
        → {V : Γ ⊢ᵛ⦂ bool} → {M N : Γ ⊢ᶜ⦂ C}
        → castᶜ e (if V `then M `else N)
        ≡ if (castᵛ e V) `then (castᶜ e M) `else (castᶜ e N)
cast-if refl = refl

-- The binding formers put their body at an extended context, so the cast
-- transported there is `cong` of the extension.

cast-delay : ∀ {Γ Γ' A ε τ} → (e : Γ ≡ Γ')
           → {M : Γ ⟨ ιᵣ τ ⟩ ⊢ᶜ⦂ A ! ε}
           → castᶜ e (delay τ M) ≡ delay τ (castᶜ (cong (_⟨ ιᵣ τ ⟩) e) M)
cast-delay refl = refl

cast-perform : ∀ {Γ Γ' A ε} → (e : Γ ≡ Γ') → {op : Op}
             → {V : Γ ⊢ᵛ⦂ ⌜ param op ⌝ᵍ}
             → {M : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ
                      ⊢ᶜ⦂ A ! ε}
             → castᶜ e (perform op V M)
             ≡ perform op (castᵛ e V)
                 (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ∣ op-grade op ∣ᵉ ⟩
                                         ∷ ⌜ arity op ⌝ᵍ) e) M)
cast-perform refl = refl

cast-match : ∀ {Γ Γ' A B C} → (e : Γ ≡ Γ')
           → {V : Γ ⊢ᵛ⦂ A |×| B} → {M : Γ ∷ A ∷ B ⊢ᶜ⦂ C}
           → castᶜ e (match V `with M)
           ≡ match (castᵛ e V) `with (castᶜ (cong (λ Γ₀ → Γ₀ ∷ A ∷ B) e) M)
cast-match refl = refl

cast-succ : ∀ {Γ Γ'} → (e : Γ ≡ Γ') → {V : Γ ⊢ᵛ⦂ nat}
          → castᵛ e (succ V) ≡ succ (castᵛ e V)
cast-succ refl = refl

cast-matchℕ : ∀ {Γ Γ' C} → (e : Γ ≡ Γ')
            → {V : Γ ⊢ᵛ⦂ nat} → {M : Γ ⊢ᶜ⦂ C} → {N : Γ ∷ nat ⊢ᶜ⦂ C}
            → castᶜ e (matchℕ V `zero M `succ N)
            ≡ matchℕ (castᵛ e V) `zero (castᶜ e M)
                                 `succ (castᶜ (cong (_∷ nat) e) N)
cast-matchℕ refl = refl

cast-inl : ∀ {Γ Γ' A B} → (e : Γ ≡ Γ') → {V : Γ ⊢ᵛ⦂ A}
         → castᵛ e (inl {B = B} V) ≡ inl (castᵛ e V)
cast-inl refl = refl

cast-inr : ∀ {Γ Γ' A B} → (e : Γ ≡ Γ') → {V : Γ ⊢ᵛ⦂ B}
         → castᵛ e (inr {A = A} V) ≡ inr (castᵛ e V)
cast-inr refl = refl

cast-nil : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → castᵛ e (nil {A = A}) ≡ nil
cast-nil refl = refl

cast-cons : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {V : Γ ⊢ᵛ⦂ A} → {W : Γ ⊢ᵛ⦂ list A}
          → castᵛ e (cons V W) ≡ cons (castᵛ e V) (castᵛ e W)
cast-cons refl = refl

cast-cmp : ∀ {Γ Γ' A ⋈} → (e : Γ ≡ Γ')
         → {V W : Γ ⊢ᵛ⦂ A} → {et : Et A}
         → castᵛ e (cmp ⋈ V W et) ≡ cmp ⋈ (castᵛ e V) (castᵛ e W) et
cast-cmp refl = refl

cast-matchL : ∀ {Γ Γ' A C} → (e : Γ ≡ Γ')
            → {V : Γ ⊢ᵛ⦂ list A} → {M : Γ ⊢ᶜ⦂ C} → {N : Γ ∷ A ∷ list A ⊢ᶜ⦂ C}
            → castᶜ e (matchL V `nil M `cons N)
            ≡ matchL (castᵛ e V) `nil (castᶜ e M)
                                 `cons (castᶜ (cong (λ Δ → Δ ∷ A ∷ list A) e) N)
cast-matchL refl = refl

cast-recL : ∀ {Γ Γ' A B ε} → (e : Γ ≡ Γ')
          → {V : Γ ⊢ᵛ⦂ list A} → {M : Γ ⊢ᶜ⦂ B ! ε}
          → {N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
          → {p : ε ·ₑ ε ≾ₑ ε}
          → castᶜ e (recL V M N p)
          ≡ recL (castᵛ e V) (castᶜ e M)
                 (castᶜ (cong (λ Δ → (Δ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B) e) N) p
cast-recL refl = refl

cast-recℕ : ∀ {Γ Γ' B ε} → (e : Γ ≡ Γ')
          → {V : Γ ⊢ᵛ⦂ nat} → {M : Γ ⊢ᶜ⦂ B ! ε}
          → {N : (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
          → {p : ε ·ₑ ε ≾ₑ ε}
          → castᶜ e (recℕ V M N p)
          ≡ recℕ (castᵛ e V) (castᶜ e M)
                 (castᶜ (cong (λ Δ → (Δ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B) e) N) p
cast-recℕ refl = refl

cast-match+ : ∀ {Γ Γ' A B C} → (e : Γ ≡ Γ')
            → {V : Γ ⊢ᵛ⦂ A |+| B} → {M : Γ ∷ A ⊢ᶜ⦂ C} → {N : Γ ∷ B ⊢ᶜ⦂ C}
            → castᶜ e (match+ V `inl M `inr N)
            ≡ match+ (castᵛ e V) `inl (castᶜ (cong (_∷ A) e) M)
                                 `inr (castᶜ (cong (_∷ B) e) N)
cast-match+ refl = refl

cast-box : ∀ {Γ Γ' A C ρ} → (e : Γ ≡ Γ')
         → {V : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A} → {M : Γ ∷ [ ρ ] A ⊢ᶜ⦂ C}
         → castᶜ e (box _ V M)
         ≡ box _ (castᵛ (cong (_⟨ ρ ⟩) e) V) (castᶜ (cong (_∷ [ ρ ] A) e) M)
cast-box refl = refl

cast-handler : ∀ {Γ Γ' A B ε ε'} → (e : Γ ≡ Γ')
             → {N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'}
             → {H : (op : Op) → (ε'' : E) →
                      Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                        ∷ [ ∣ op-grade op ∣ᵉ ]
                            (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                      ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε'')}
             → castᵛ e (handler N H)
             ≡ handler (castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) e) N)
                       (λ op ε'' →
                          castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                                                ∷ [ ∣ op-grade op ∣ᵉ ]
                                                    (⌜ arity op ⌝ᵍ ⇒ B ! ε''))
                                 e)
                                (H op ε''))
cast-handler refl = refl

cast-handle : ∀ {Γ Γ' A B ε ε'} → (e : Γ ≡ Γ')
            → {M : Γ ⊢ᶜ⦂ A ! ε} → {V : Γ ⊢ᵛ⦂ (A ! ε) ⇛ (B ! ε')}
            → castᶜ e (handle M `with V) ≡ handle (castᶜ e M) `with (castᵛ e V)
cast-handle refl = refl

-- The same, for a caller that has the transported splitting in hand rather than
-- as a transport. Two splittings of the same context agree (`split-unique`), so
-- no equation relating them is needed.

sub-cast-C′ : ∀ {Γ Γ' Γ₁ Γ₂ A C} → (e : Γ ≡ Γ') → (M : Γ ⊢ᶜ⦂ C)
            → (s : Γ₁ ∷ A , Γ₂ split Γ) → (s' : Γ₁ ∷ A , Γ₂ split Γ')
            → (W : Γ₁ ⊢ᵛ⦂ A)
            → (subst (_⊢ᶜ⦂ C) e M) [ s' ↦ W ]c ≡ M [ s ↦ W ]c
sub-cast-C′ refl M s s' W = cong (λ z → M [ z ↦ W ]c) (split-unique s' s)

-- Transports along context equalities, all normalised to `subst` so that a
-- chain of them fuses and collapses by `uip`.

castᶜ≡subst : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → (M : Γ ⊢ᶜ⦂ C)
            → castᶜ e M ≡ subst (_⊢ᶜ⦂ C) e M
castᶜ≡subst refl M = refl

subst-++ᶜʳ : ∀ {Γ Γ' C} → (D : Ctx) → (e : Γ ≡ Γ') → (M : (Γ ++ᶜ D) ⊢ᶜ⦂ C)
           → subst (λ Γ₀ → (Γ₀ ++ᶜ D) ⊢ᶜ⦂ C) e M
           ≡ subst (_⊢ᶜ⦂ C) (cong (_++ᶜ D) e) M
subst-++ᶜʳ D refl M = refl

-- Two transports fuse into one; a transport that returns to its own context is
-- the identity. Together they collapse a tower of any height.

subst-fuseᶜ : ∀ {Γ₁ Γ₂ Γ₃ C} → (e : Γ₁ ≡ Γ₂) → (e' : Γ₂ ≡ Γ₃) → (M : Γ₁ ⊢ᶜ⦂ C)
            → subst (_⊢ᶜ⦂ C) e' (subst (_⊢ᶜ⦂ C) e M)
            ≡ subst (_⊢ᶜ⦂ C) (trans e e') M
subst-fuseᶜ refl refl M = refl

subst-loopᶜ : ∀ {Γ C} → (e : Γ ≡ Γ) → (M : Γ ⊢ᶜ⦂ C) → subst (_⊢ᶜ⦂ C) e M ≡ M
subst-loopᶜ {C = C} e M = cong (λ z → subst (_⊢ᶜ⦂ C) z M) (uip {p = e} {q = refl})

subst-subst-sym′ : ∀ {a p} {X : Set a} {P : X → Set p} {u v : X}
                 → (e : u ≡ v) → (w : P v)
                 → subst P e (subst P (sym e) w) ≡ w
subst-subst-sym′ refl w = refl

castʳ : ∀ {Γ Γ' Δ} → Γ ≡ Γ' → Ren [] Γ Δ → Ren [] Γ' Δ
castʳ refl w = w

-- A cast relocates the resource variable an `unbox` names along `Var-cast`.

cast-unbox : ∀ {Γ Γ' A A₀ C ρ₀ ρ'} → (e : Γ ≡ Γ')
           → {x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ} → {rel : ρ' ≾ᵣ ρ₀} → {p : A₀ <:ᵛ A}
           → {M : Γ ∷ A ⊢ᶜ⦂ C}
           → castᶜ e (unbox x rel p M)
           ≡ unbox (proj₂ (Var-cast e (ρ' , x))) rel p
                   (castᶜ (cong (_∷ A) e) M)
cast-unbox refl = refl

cast-seq : ∀ {Γ Γ' A B ε ε'} → (e : Γ ≡ Γ')
         → {M : Γ ⊢ᶜ⦂ A ! ε} → {N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'}
         → castᶜ e (M ⨟ N)
         ≡ (castᶜ e M) ⨟ (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) e) N)
cast-seq refl = refl

-- A handler clause's typing, and clause families indexed by it.

Cl : (B : VType) → (op : Op) → (ε₃ : E) → Ctx → Set
Cl B op ε₃ Γ₀ =
  Γ₀ ∷ ⌜ param op ⌝ᵍ
    ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε₃)
  ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε₃)

Fam : VType → Ctx → Set
Fam B Γ₀ = (op : Op) → (ε : E) → Cl B op ε Γ₀

-- Relocating a clause along an equality of the context it is barred from.
-- Written in exactly the shape `cast-handler` produces, so that the two agree on
-- the nose and no `castᶜ-irr` is needed at any use site.

Cl-cast : ∀ {Γ Γ' B} → (op : Op) → (ε : E) → Γ ≡ Γ'
        → Cl B op ε (Γ ⟨ ⊤ᵣ ⟩) → Cl B op ε (Γ' ⟨ ⊤ᵣ ⟩)
Cl-cast {B = B} op ε e X =
  castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                        ∷ [ ∣ op-grade op ∣ᵉ ]
                            (⌜ arity op ⌝ᵍ ⇒ B ! ε))
              e)
        X

-- Transport is a congruence for the term equivalence.

castᶜ-≡ : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → {M M' : Γ ⊢ᶜ⦂ C}
        → M ≡ M' → castᶜ e M ≡ castᶜ e M'
castᶜ-≡ e = cong (castᶜ e)

castᵛ-≡ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {V V' : Γ ⊢ᵛ⦂ A}
        → V ≡ V' → castᵛ e V ≡ castᵛ e V'
castᵛ-≡ e = cong (castᵛ e)

castᵛ≡subst : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (V : Γ ⊢ᵛ⦂ A)
            → castᵛ e V ≡ subst (_⊢ᵛ⦂ A) e V
castᵛ≡subst refl V = refl

