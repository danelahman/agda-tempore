------------------------------------------------------------------------
-- States up to the term equivalence, and inverting a cast.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
import Data.List.Base as List

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Relation.Nullary using (¬_)

open import Util.Equality

module ClosedCalculus.OperationalSemantics.StateEquivalence.Core (Spec : LanguageSpec) where
open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import ClosedCalculus.OperationalSemantics.Reduction           Spec
open import ClosedCalculus.OperationalSemantics.State               Spec

open import Language.Comparisons using (Cmp; holds)
open import ClosedCalculus.Syntax.Contexts      Spec
open import ClosedCalculus.Syntax.Data          Spec using (⟪_⟫ˢ; compareᵈ; ⌈_⌉ᵇ)
open import ClosedCalculus.Syntax.Terms      Spec
open import ClosedCalculus.Syntax.Renaming.Action Spec
open import ClosedCalculus.Syntax.Renaming      Spec
open import ClosedCalculus.Syntax.Substitution  Spec
open import ClosedCalculus.Syntax.Types Spec

open import ClosedCalculus.Syntax.Renaming.Equivalence  Spec
open import ClosedCalculus.Syntax.Renaming.Coherence    Spec
open import ClosedCalculus.Syntax.Terms.Equivalence     Spec
open import ClosedCalculus.Syntax.Terms.Transport       Spec
open import ClosedCalculus.Syntax.Substitution.Variables  Spec
open import ClosedCalculus.OperationalSemantics.GradedReach Spec
open import ClosedCalculus.Syntax.Substitution.Equivalence  Spec


mutual

  data _≐ˢ_ : 𝕊 [] → 𝕊 [] → Set where

    ∅-≐ˢ  : ∅ ≐ˢ ∅

    ⟨⟩-≐ˢ : ∀ {St St'} → (ρ : R) → (e : St ≐ˢ St')
          → (St ⟨ ρ ⟩ₛ) ≐ˢ (St' ⟨ ρ ⟩ₛ)

    ∷-≐ˢ  : ∀ {A ρ St St'}
          → {V  : ([] ++ᶜ toCtx St  ⟨ ρ ⟩) ⊢V⦂ A}
          → {V' : ([] ++ᶜ toCtx St' ⟨ ρ ⟩) ⊢V⦂ A}
          → (e : St ≐ˢ St')
          → V ≡ castᵛ (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩) (sym (toCtx-≐ˢ e))) V'
          → (St ∷ₛ V) ≐ˢ (St' ∷ₛ V')

  -- Related states have the same context: `toCtx` reads the skeleton only.

  toCtx-≐ˢ : ∀ {St St'} → St ≐ˢ St' → toCtx St ≡ toCtx St'
  toCtx-≐ˢ ∅-≐ˢ                = refl
  toCtx-≐ˢ (⟨⟩-≐ˢ ρ e)          = cong (_⟨ ρ ⟩) (toCtx-≐ˢ e)
  toCtx-≐ˢ (∷-≐ˢ {A} {ρ} e eV) = cong (_∷ [ ρ ] A) (toCtx-≐ˢ e)

-- Reflexivity, with its context equality degenerate.

mutual

  ≐ˢ-refl : (St : 𝕊 []) → St ≐ˢ St
  ≐ˢ-refl ∅           = ∅-≐ˢ
  ≐ˢ-refl (St ⟨ ρ ⟩ₛ)  = ⟨⟩-≐ˢ ρ (≐ˢ-refl St)
  ≐ˢ-refl (St ∷ₛ V)   =
    ∷-≐ˢ (≐ˢ-refl St)
      (subst (λ e → V ≡ castᵛ (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ _ ⟩) (sym e)) V)
             (sym (toCtx-≐ˢ-refl St)) (refl {x = V}))

  toCtx-≐ˢ-refl : (St : 𝕊 []) → toCtx-≐ˢ (≐ˢ-refl St) ≡ refl
  toCtx-≐ˢ-refl ∅          = refl
  toCtx-≐ˢ-refl (St ⟨ ρ ⟩ₛ) = cong (cong (_⟨ ρ ⟩)) (toCtx-≐ˢ-refl St)
  toCtx-≐ˢ-refl (_∷ₛ_ {A} {ρ} St V) =
    cong (cong (_∷ [ ρ ] A)) (toCtx-≐ˢ-refl St)

-- Shifting a cast across the relation, and symmetry of `_≐ˢ_`. Symmetry is
-- needed because `VRed`'s Kripke clauses have to replay an extension of the
-- *other* state (`reach-replay` runs in one direction only).

≡-shift : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (e' : Γ' ≡ Γ)
         → {V : Γ' ⊢V⦂ A} → {W : Γ ⊢V⦂ A}
         → castᵛ e' V ≡ W → V ≡ castᵛ e W
≡-shift refl e' {V} {W} eV
  rewrite uip {p = e'} {q = refl} = eV

≐ˢ-sym : ∀ {St St' : 𝕊 []} → St ≐ˢ St' → St' ≐ˢ St
≐ˢ-sym ∅-≐ˢ         = ∅-≐ˢ
≐ˢ-sym (⟨⟩-≐ˢ ρ e)   = ⟨⟩-≐ˢ ρ (≐ˢ-sym e)
≐ˢ-sym (∷-≐ˢ {A = A} {ρ = ρ} e eV) =
  ∷-≐ˢ (≐ˢ-sym e)
    (≡-shift (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩) (sym (toCtx-≐ˢ (≐ˢ-sym e))))
              (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩) (sym (toCtx-≐ˢ e)))
              (sym eV))

-- The right-hand term's shape has to be read back out of `M ≡ castᶜ e M'`;
-- each inversion is a standalone lemma over abstract contexts, where the
-- equality can be matched.

cast-lam⁻ : ∀ {Γ Γ' A B ε} → (e : Γ' ≡ Γ) → {M : Γ ∷ A ⊢C⦂ B ‼ ε}
       → (V' : Γ' ⊢V⦂ A ⇒ B ‼ ε)
       → lam M ≡ castᵛ e V'
       → Σ[ M' ∈ (Γ' ∷ A ⊢C⦂ B ‼ ε) ]
           (V' ≡ lam M') × (M ≡ castᶜ (cong (_∷ A) e) M')
cast-lam⁻ refl _ refl = _ , refl , refl

cast-pair⁻ : ∀ {Γ Γ' A B} → (e : Γ' ≡ Γ) → {V : Γ ⊢V⦂ A} → {W : Γ ⊢V⦂ B}
        → (U' : Γ' ⊢V⦂ A |×| B)
        → ⦉ V , W ⦊ ≡ castᵛ e U'
        → Σ[ V' ∈ (Γ' ⊢V⦂ A) ] Σ[ W' ∈ (Γ' ⊢V⦂ B) ]
            (U' ≡ ⦉ V' , W' ⦊) × (V ≡ castᵛ e V') × (W ≡ castᵛ e W')
cast-pair⁻ refl _ refl = _ , _ , refl , refl , refl

cast-zero⁻ : ∀ {Γ Γ'} → (e : Γ' ≡ Γ) → (V' : Γ' ⊢V⦂ Nat)
           → zero ≡ castᵛ e V' → V' ≡ zero
cast-zero⁻ refl _ refl = refl

cast-succ⁻ : ∀ {Γ Γ'} → (e : Γ' ≡ Γ) → {V : Γ ⊢V⦂ Nat}
           → (U' : Γ' ⊢V⦂ Nat)
           → succ V ≡ castᵛ e U'
           → Σ[ V' ∈ (Γ' ⊢V⦂ Nat) ] (U' ≡ succ V') × (V ≡ castᵛ e V')
cast-succ⁻ refl _ refl = _ , refl , refl

cast-true⁻ : ∀ {Γ Γ'} → (e : Γ' ≡ Γ) → (V' : Γ' ⊢V⦂ Bool)
        → true ≡ castᵛ e V' → V' ≡ true
cast-true⁻ refl _ refl = refl

cast-false⁻ : ∀ {Γ Γ'} → (e : Γ' ≡ Γ) → (V' : Γ' ⊢V⦂ Bool)
         → false ≡ castᵛ e V' → V' ≡ false
cast-false⁻ refl _ refl = refl

cast-return⁻ : ∀ {Γ Γ' A} → (e : Γ' ≡ Γ) → {V : Γ ⊢V⦂ A}
          → (M' : Γ' ⊢C⦂ A ‼ uₑ)
          → return V ≡ castᶜ e M'
          → Σ[ V' ∈ (Γ' ⊢V⦂ A) ] (M' ≡ return V') × (V ≡ castᵛ e V')
cast-return⁻ refl _ refl = _ , refl , refl

cast-app⁻ : ∀ {Γ Γ' A C} → (e : Γ' ≡ Γ) → {V : Γ ⊢V⦂ A ⇒ C} → {W : Γ ⊢V⦂ A}
       → (M' : Γ' ⊢C⦂ C)
       → (V · W) ≡ castᶜ e M'
       → Σ[ V' ∈ (Γ' ⊢V⦂ A ⇒ C) ] Σ[ W' ∈ (Γ' ⊢V⦂ A) ]
           (M' ≡ V' · W') × (V ≡ castᵛ e V') × (W ≡ castᵛ e W')
cast-app⁻ refl _ refl = _ , _ , refl , refl , refl

cast-seq⁻ : ∀ {Γ Γ' A B ε ε'} → (e : Γ' ≡ Γ)
       → {M : Γ ⊢C⦂ A ‼ ε} → {N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
       → (P' : Γ' ⊢C⦂ B ‼ (ε ·ₑ ε'))
       → (M ⨟ N) ≡ castᶜ e P'
       → Σ[ M' ∈ (Γ' ⊢C⦂ A ‼ ε) ] Σ[ N' ∈ (Γ' ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε') ]
           (P' ≡ (M' ⨟ N')) × (M ≡ castᶜ e M')
         × (N ≡ castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) e) N')
cast-seq⁻ refl _ refl = _ , _ , refl , refl , refl

cast-match⁻ : ∀ {Γ Γ' A B C} → (e : Γ' ≡ Γ)
         → {V : Γ ⊢V⦂ A |×| B} → {M : Γ ∷ A ∷ B ⊢C⦂ C}
         → (P' : Γ' ⊢C⦂ C)
         → (match V `in M) ≡ castᶜ e P'
         → Σ[ V' ∈ (Γ' ⊢V⦂ A |×| B) ] Σ[ M' ∈ (Γ' ∷ A ∷ B ⊢C⦂ C) ]
             (P' ≡ (match V' `in M')) × (V ≡ castᵛ e V')
           × (M ≡ castᶜ (cong (λ Γ₀ → Γ₀ ∷ A ∷ B) e) M')
cast-match⁻ refl _ refl = _ , _ , refl , refl , refl

cast-if⁻ : ∀ {Γ Γ' C} → (e : Γ' ≡ Γ)
      → {V : Γ ⊢V⦂ Bool} → {M N : Γ ⊢C⦂ C}
      → (P' : Γ' ⊢C⦂ C)
      → (if V `then M `else N) ≡ castᶜ e P'
      → Σ[ V' ∈ (Γ' ⊢V⦂ Bool) ] Σ[ M' ∈ (Γ' ⊢C⦂ C) ] Σ[ N' ∈ (Γ' ⊢C⦂ C) ]
          (P' ≡ (if V' `then M' `else N')) × (V ≡ castᵛ e V')
        × (M ≡ castᶜ e M') × (N ≡ castᶜ e N')
cast-if⁻ refl _ refl = _ , _ , _ , refl , refl , refl , refl

cast-cmp⁻ : ∀ {Γ Γ' A ⋈} → (e : Γ' ≡ Γ)
          → {V W : Γ ⊢V⦂ A} → {et : Eternal A}
          → (P' : Γ' ⊢C⦂ Bool ‼ uₑ)
          → cmp ⋈ V W et ≡ castᶜ e P'
          → Σ[ V' ∈ (Γ' ⊢V⦂ A) ] Σ[ W' ∈ (Γ' ⊢V⦂ A) ]
              (P' ≡ cmp ⋈ V' W' et) × (V ≡ castᵛ e V') × (W ≡ castᵛ e W')
cast-cmp⁻ refl _ refl = _ , _ , refl , refl , refl

cast-caseℕ⁻ : ∀ {Γ Γ' C} → (e : Γ' ≡ Γ)
            → {V : Γ ⊢V⦂ Nat} → {M : Γ ⊢C⦂ C} → {N : Γ ∷ Nat ⊢C⦂ C}
            → (P' : Γ' ⊢C⦂ C)
            → (caseℕ V `zero M `succ N) ≡ castᶜ e P'
            → Σ[ V' ∈ (Γ' ⊢V⦂ Nat) ] Σ[ M' ∈ (Γ' ⊢C⦂ C) ]
              Σ[ N' ∈ (Γ' ∷ Nat ⊢C⦂ C) ]
                (P' ≡ (caseℕ V' `zero M' `succ N')) × (V ≡ castᵛ e V')
              × (M ≡ castᶜ e M') × (N ≡ castᶜ (cong (_∷ Nat) e) N')
cast-caseℕ⁻ refl _ refl = _ , _ , _ , refl , refl , refl , refl

cast-recℕ⁻ : ∀ {Γ Γ' B ε} → (e : Γ' ≡ Γ)
           → {V : Γ ⊢V⦂ Nat} → {M : Γ ⊢C⦂ B ‼ ε}
           → {N : (Γ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε}
           → {p : ε ·ₑ ε ≾ₑ ε}
           → (P' : Γ' ⊢C⦂ B ‼ ε)
           → recℕ V M N p ≡ castᶜ e P'
           → Σ[ V' ∈ (Γ' ⊢V⦂ Nat) ] Σ[ M' ∈ (Γ' ⊢C⦂ B ‼ ε) ]
             Σ[ N' ∈ ((Γ' ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε) ]
               (P' ≡ recℕ V' M' N' p) × (V ≡ castᵛ e V')
             × (M ≡ castᶜ e M')
             × (N ≡ castᶜ (cong (λ X → (X ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B) e) N')
cast-recℕ⁻ refl _ refl = _ , _ , _ , refl , refl , refl , refl

-- The successor reduct of a recursion commutes with a context equality.

cast-recℕ-reduct : ∀ {Γ Γ' B ε} → (e : Γ' ≡ Γ)
                 → (V' : Γ' ⊢V⦂ Nat) → (M' : Γ' ⊢C⦂ B ‼ ε)
                 → (N' : (Γ' ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
                 → (p : ε ·ₑ ε ≾ₑ ε)
                 → let N₁ = castᶜ (cong (λ X → (X ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B) e) N' in
                   coerce p (recℕ (castᵛ e V') (castᶜ e M') N₁ p
                             ⨟ recℕ-step (castᵛ e V') N₁)
                   ≡ castᶜ e (coerce p (recℕ V' M' N' p ⨟ recℕ-step V' N'))
cast-recℕ-reduct refl V' M' N' p = refl

cast-caseL⁻ : ∀ {Γ Γ' A C} → (e : Γ' ≡ Γ)
            → {V : Γ ⊢V⦂ |List| A} → {M : Γ ⊢C⦂ C} → {N : Γ ∷ A ∷ |List| A ⊢C⦂ C}
            → (P' : Γ' ⊢C⦂ C)
            → caseL V `nil M `cons N ≡ castᶜ e P'
            → Σ[ V' ∈ (Γ' ⊢V⦂ |List| A) ] Σ[ M' ∈ (Γ' ⊢C⦂ C) ]
              Σ[ N' ∈ (Γ' ∷ A ∷ |List| A ⊢C⦂ C) ]
                (P' ≡ caseL V' `nil M' `cons N') × (V ≡ castᵛ e V')
              × (M ≡ castᶜ e M') × (N ≡ castᶜ (cong (λ X → X ∷ A ∷ |List| A) e) N')
cast-caseL⁻ refl _ refl = _ , _ , _ , refl , refl , refl , refl

cast-recL⁻ : ∀ {Γ Γ' A B ε} → (e : Γ' ≡ Γ)
           → {V : Γ ⊢V⦂ |List| A} → {M : Γ ⊢C⦂ B ‼ ε}
           → {N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε}
           → {p : ε ·ₑ ε ≾ₑ ε}
           → (P' : Γ' ⊢C⦂ B ‼ ε)
           → recL V M N p ≡ castᶜ e P'
           → Σ[ V' ∈ (Γ' ⊢V⦂ |List| A) ] Σ[ M' ∈ (Γ' ⊢C⦂ B ‼ ε) ]
             Σ[ N' ∈ ((Γ' ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε) ]
               (P' ≡ recL V' M' N' p) × (V ≡ castᵛ e V')
             × (M ≡ castᶜ e M')
             × (N ≡ castᶜ (cong (λ X → (X ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B) e) N')
cast-recL⁻ refl _ refl = _ , _ , _ , refl , refl , refl , refl

cast-case+⁻ : ∀ {Γ Γ' A B C} → (e : Γ' ≡ Γ)
            → {V : Γ ⊢V⦂ A |+| B} → {M : Γ ∷ A ⊢C⦂ C} → {N : Γ ∷ B ⊢C⦂ C}
            → (P' : Γ' ⊢C⦂ C)
            → (case+ V `inl M `inr N) ≡ castᶜ e P'
            → Σ[ V' ∈ (Γ' ⊢V⦂ A |+| B) ] Σ[ M' ∈ (Γ' ∷ A ⊢C⦂ C) ]
              Σ[ N' ∈ (Γ' ∷ B ⊢C⦂ C) ]
                (P' ≡ (case+ V' `inl M' `inr N')) × (V ≡ castᵛ e V')
              × (M ≡ castᶜ (cong (_∷ A) e) M') × (N ≡ castᶜ (cong (_∷ B) e) N')
cast-case+⁻ refl _ refl = _ , _ , _ , refl , refl , refl , refl

cast-perform⁻ : ∀ {Γ Γ' A ε} → (e : Γ' ≡ Γ) → {op : Op}
           → {V : Γ ⊢V⦂ type-of-gtype (param op)}
           → {M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
           → (P' : Γ' ⊢C⦂ A ‼ (op-grade op ·ₑ ε))
           → perform op V M ≡ castᶜ e P'
           → Σ[ V' ∈ (Γ' ⊢V⦂ type-of-gtype (param op)) ]
             Σ[ M' ∈ (Γ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                        ⊢C⦂ A ‼ ε) ]
               (P' ≡ perform op V' M') × (V ≡ castᵛ e V')
             × (M ≡ castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                            ∷ type-of-gtype (arity op)) e) M')
cast-perform⁻ refl _ refl = _ , _ , refl , refl , refl

cast-delay⁻ : ∀ {Γ Γ' A ε τ} → (e : Γ' ≡ Γ)
         → {M : Γ ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε}
         → (P' : Γ' ⊢C⦂ A ‼ (of-durᵉ τ ·ₑ ε))
         → delay τ M ≡ castᶜ e P'
         → Σ[ M' ∈ (Γ' ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε) ]
             (P' ≡ delay τ M')
           × (M ≡ castᶜ (cong (_⟨ of-durʳ τ ⟩) e) M')
cast-delay⁻ refl _ refl = _ , refl , refl

cast-box⁻ : ∀ {Γ Γ' A C ρ} → (e : Γ' ≡ Γ)
       → {V : Γ ⟨ ρ ⟩ ⊢V⦂ A} → {M : Γ ∷ [ ρ ] A ⊢C⦂ C}
       → (P' : Γ' ⊢C⦂ C)
       → box _ V M ≡ castᶜ e P'
       → Σ[ V' ∈ (Γ' ⟨ ρ ⟩ ⊢V⦂ A) ] Σ[ M' ∈ (Γ' ∷ [ ρ ] A ⊢C⦂ C) ]
           (P' ≡ box _ V' M') × (V ≡ castᵛ (cong (_⟨ ρ ⟩) e) V')
         × (M ≡ castᶜ (cong (_∷ [ ρ ] A) e) M')
cast-box⁻ refl _ refl = _ , _ , refl , refl , refl

cast-sub⁻ : ∀ {Γ Γ' C C'} → (e : Γ' ≡ Γ) → {p : C <:ᶜ C'}
          → {M : Γ ⊢C⦂ C}
          → (P' : Γ' ⊢C⦂ C')
          → subC M p ≡ castᶜ e P'
          → Σ[ p' ∈ (C <:ᶜ C') ] Σ[ M' ∈ (Γ' ⊢C⦂ C) ]
              (P' ≡ subC M' p') × (M ≡ castᶜ e M')
cast-sub⁻ refl _ refl = _ , _ , refl , refl

cast-subV⁻ : ∀ {Γ Γ' A A'} → (e : Γ' ≡ Γ) → {p : A <:ᵛ A'}
           → {V : Γ ⊢V⦂ A}
           → (W' : Γ' ⊢V⦂ A')
           → subV V p ≡ castᵛ e W'
           → Σ[ p' ∈ (A <:ᵛ A') ] Σ[ V' ∈ (Γ' ⊢V⦂ A) ]
               (W' ≡ subV V' p') × (V ≡ castᵛ e V')
cast-subV⁻ refl _ refl = _ , _ , refl , refl

cast-handle⁻ : ∀ {Γ Γ' A B ε ε'} → (e : Γ' ≡ Γ)
          → {M : Γ ⊢C⦂ A ‼ ε}
          → {H : (op : Op) → (ε'' : E) →
                   Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                     ∷ [ mapᵉ (op-grade op) ]
                         (type-of-gtype (arity op) ⇒ B ‼ ε'')
                   ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
          → {N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
          → (P' : Γ' ⊢C⦂ B ‼ (ε ·ₑ ε'))
          → (handle M `with H `in N) ≡ castᶜ e P'
          → Σ[ M' ∈ (Γ' ⊢C⦂ A ‼ ε) ]
            Σ[ H' ∈ ((op : Op) → (ε'' : E) →
                       Γ' ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε'')
                       ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')) ]
            Σ[ N' ∈ (Γ' ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε') ]
              (P' ≡ (handle M' `with H' `in N'))
            × (M ≡ castᶜ e M')
            × (∀ op ε'' → H op ε''
                 ≡ castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                                          ∷ [ mapᵉ (op-grade op) ]
                                              (type-of-gtype (arity op) ⇒ B ‼ ε''))
                                e)
                          (H' op ε''))
            × (N ≡ castᶜ (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) e) N')
cast-handle⁻ refl _ refl = _ , _ , _ , refl , refl , (λ op ε'' → refl) , refl

cast-unbox⁻ : ∀ {Γ Γ' A A₀ C ρ ρ'} → (e : Γ' ≡ Γ)
         → {x : [ ρ ] A₀ ∈[ ρ' ] Γ} → {rel : ρ' ≾ᵣ ρ} → {p : A₀ <:ᵛ A}
         → {M : Γ ∷ A ⊢C⦂ C}
         → (P' : Γ' ⊢C⦂ C)
         → unbox x rel p M ≡ castᶜ e P'
         → Σ[ ρ'' ∈ R ] Σ[ x' ∈ ([ ρ ] A₀ ∈[ ρ'' ] Γ') ] Σ[ rel' ∈ (ρ'' ≾ᵣ ρ) ]
           Σ[ p' ∈ (A₀ <:ᵛ A) ] Σ[ M' ∈ (Γ' ∷ A ⊢C⦂ C) ]
             (P' ≡ unbox x' rel' p' M')
           × (_≡_ {A = Var Γ ([ ρ ] A₀)} (ρ' , x) (Var-cast e (ρ'' , x')))
           × (M ≡ castᶜ (cong (_∷ A) e) M')
cast-unbox⁻ refl _ refl = _ , _ , _ , _ , _ , refl , refl , refl

-- The reducts are built by renaming, substitution and retyping, each of
-- which commutes with a cast.

cast-app-reduct : ∀ {Γ Γ' A C} → (e : Γ' ≡ Γ)
         → (M' : Γ' ∷ A ⊢C⦂ C) → (W' : Γ' ⊢V⦂ A)
         → (castᶜ (cong (_∷ A) e) M') [ split-[] ↦ castᵛ e W' ]c
         ≡ castᶜ e (M' [ split-[] ↦ W' ]c)
cast-app-reduct refl M' W' = refl

-- The two projections commute with a context equality: a one-clause
-- induction on the value, the variable clause being absurd.

fstᵛ-cast : ∀ {A B} {St St' : 𝕊 []} → (e : toCtx St ≡ toCtx St')
          → (V : toCtx St ⊢V⦂ A |×| B)
          → fstᵛ (castᵛ e V) ≡ castᵛ e (fstᵛ V)
fstᵛ-cast e (var _ x)           = ⊥-elim (⦉⦊-not-in-toCtx x)
fstᵛ-cast e ⦉ V , W ⦊           = cong fstᵛ (cast-pair e {V} {W})
fstᵛ-cast e (subV V (p |×|ₛ _)) =
  trans (cong fstᵛ (cast-subV e {V = V}))
        (trans (cong (λ z → subV z p) (fstᵛ-cast e V))
               (sym (cast-subV e)))

sndᵛ-cast : ∀ {A B} {St St' : 𝕊 []} → (e : toCtx St ≡ toCtx St')
          → (V : toCtx St ⊢V⦂ A |×| B)
          → sndᵛ (castᵛ e V) ≡ castᵛ e (sndᵛ V)
sndᵛ-cast e (var _ x)           = ⊥-elim (⦉⦊-not-in-toCtx x)
sndᵛ-cast e ⦉ V , W ⦊           = cong sndᵛ (cast-pair e {V} {W})
sndᵛ-cast e (subV V (_ |×|ₛ q)) =
  trans (cong sndᵛ (cast-subV e {V = V}))
        (trans (cong (λ z → subV z q) (sndᵛ-cast e V))
               (sym (cast-subV e)))

-- The datum a value of an eternal type is commutes with a context equality,
-- and so does the comparison's reduct: the data, hence the outcome, agree.

cast-closed : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (V : ∀ {Δ} → Δ ⊢V⦂ A) → castᵛ e V ≡ V
cast-closed refl V = refl

⌊⌋ᵈ-cast : ∀ {A} {St St' : 𝕊 []} → (e : toCtx St ≡ toCtx St') → (et : Eternal A)
         → (V : toCtx St ⊢V⦂ A)
         → ⌊_⌋ᵈ {S = St'} et (castᵛ e V) ≡ ⌊_⌋ᵈ {S = St} et V
⌊⌋ᵈ-cast e et (var _ x) = ⊥-elim (eternal-not-in-toCtx et x)
⌊⌋ᵈ-cast {St' = St'} e et (subV V p) =
  trans (cong (⌊_⌋ᵈ {S = St'} et) (cast-subV e {V = V}))
        (cong ⟪ p ⟫ˢ (⌊⌋ᵈ-cast e (<:ᵛ-eternalˡ p et) V))
⌊⌋ᵈ-cast {St' = St'} e et@(Baseₑ _) (const c) =
  cong (⌊_⌋ᵈ {S = St'} et) (cast-closed e (const c))
⌊⌋ᵈ-cast {St' = St'} e Unitₑ ⋆ = cong (⌊_⌋ᵈ {S = St'} Unitₑ) (cast-closed e ⋆)
⌊⌋ᵈ-cast {St' = St'} e Boolₑ true = cong (⌊_⌋ᵈ {S = St'} Boolₑ) (cast-closed e true)
⌊⌋ᵈ-cast {St' = St'} e Boolₑ false = cong (⌊_⌋ᵈ {S = St'} Boolₑ) (cast-closed e false)
⌊⌋ᵈ-cast {St' = St'} e Natₑ zero = cong (⌊_⌋ᵈ {S = St'} Natₑ) (cast-closed e zero)
⌊⌋ᵈ-cast {St' = St'} e Natₑ (succ V) =
  trans (cong (⌊_⌋ᵈ {S = St'} Natₑ) (cast-succ e {V = V}))
        (cong suc (⌊⌋ᵈ-cast e Natₑ V))
⌊⌋ᵈ-cast {St' = St'} e et@(et₁ |×|ₑ et₂) ⦉ V , W ⦊ =
  trans (cong (⌊_⌋ᵈ {S = St'} et) (cast-pair e {V} {W}))
        (cong₂ _,_ (⌊⌋ᵈ-cast e et₁ V) (⌊⌋ᵈ-cast e et₂ W))
⌊⌋ᵈ-cast {St' = St'} e et@(et₁ |+|ₑ et₂) (inl V) =
  trans (cong (⌊_⌋ᵈ {S = St'} et) (cast-inl e {V = V}))
        (cong inj₁ (⌊⌋ᵈ-cast e et₁ V))
⌊⌋ᵈ-cast {St' = St'} e et@(et₁ |+|ₑ et₂) (inr V) =
  trans (cong (⌊_⌋ᵈ {S = St'} et) (cast-inr e {V = V}))
        (cong inj₂ (⌊⌋ᵈ-cast e et₂ V))
⌊⌋ᵈ-cast {St' = St'} e et@(|List|ₑ _) nil =
  cong (⌊_⌋ᵈ {S = St'} et) (cast-nil e)
⌊⌋ᵈ-cast {St' = St'} e et@(|List|ₑ et₁) (cons V W) =
  trans (cong (⌊_⌋ᵈ {S = St'} et) (cast-cons e {V} {W}))
        (cong₂ List._∷_ (⌊⌋ᵈ-cast e et₁ V) (⌊⌋ᵈ-cast e et W))

cast-cmp-reduct : ∀ {A} {St St' : 𝕊 []} → (e : toCtx St' ≡ toCtx St)
                → (⋈ : Cmp) → (V' W' : toCtx St' ⊢V⦂ A) → (et : Eternal A)
                → cmp-reduct {S = St} ⋈ (castᵛ e V') (castᵛ e W') et
                ≡ castᶜ e (cmp-reduct {S = St'} ⋈ V' W' et)
cast-cmp-reduct e ⋈ V' W' et =
  trans (cong₂ (λ a b → return ⌈ holds ⋈ (compareᵈ et a b) ⌉ᵇ)
               (⌊⌋ᵈ-cast e et V') (⌊⌋ᵈ-cast e et W'))
        (sym (trans (cast-ret e) (cong return (cast-closed e ⌈ _ ⌉ᵇ))))

-- The decomposition of a list commutes with a context equality, and so do
-- the reducts the list eliminators build from it.

castL : ∀ {Γ Γ' A} → Γ ≡ Γ' → ListView Γ A → ListView Γ' A
castL e (inj₁ tt)      = inj₁ tt
castL e (inj₂ (W , L)) = inj₂ (castᵛ e W , castᵛ e L)

listᵛ-cast : ∀ {A} {St St' : 𝕊 []} → (e : toCtx St ≡ toCtx St')
           → (V : toCtx St ⊢V⦂ |List| A)
           → listᵛ (castᵛ e V) ≡ castL e (listᵛ V)
listᵛ-cast e (var _ x)            = ⊥-elim (|List|-not-in-toCtx x)
listᵛ-cast e nil                  = cong listᵛ (cast-nil e)
listᵛ-cast e (cons V W)           = cong listᵛ (cast-cons e {V} {W})
listᵛ-cast e (subV V (|List|ₛ p)) =
  trans (cong listᵛ (cast-subV e {V = V}))
        (trans (cong (subL p) (listᵛ-cast e V)) (comm (listᵛ V)))
  where
    comm : ∀ l → subL p (castL e l) ≡ castL e (subL p l)
    comm (inj₁ tt)      = refl
    comm (inj₂ (W , L)) =
      cong₂ (λ a b → inj₂ (a , b)) (sym (cast-subV e)) (sym (cast-subV e))

cast-caseL-reduct : ∀ {Γ Γ' A C} → (e : Γ' ≡ Γ) → (l : ListView Γ' A)
                  → (M' : Γ' ⊢C⦂ C) → (N' : Γ' ∷ A ∷ |List| A ⊢C⦂ C)
                  → caseL-reduct (castL e l) (castᶜ e M')
                                 (castᶜ (cong (λ X → X ∷ A ∷ |List| A) e) N')
                  ≡ castᶜ e (caseL-reduct l M' N')
cast-caseL-reduct refl (inj₁ tt)      M' N' = refl
cast-caseL-reduct refl (inj₂ (W , L)) M' N' = refl

cast-recL-reduct : ∀ {Γ Γ' A B ε} → (e : Γ' ≡ Γ) → (l : ListView Γ' A)
                 → (M' : Γ' ⊢C⦂ B ‼ ε)
                 → (N' : (Γ' ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
                 → (p : ε ·ₑ ε ≾ₑ ε)
                 → recL-reduct (castL e l) (castᶜ e M')
                     (castᶜ (cong (λ X → (X ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B) e) N') p
                 ≡ castᶜ e (recL-reduct l M' N' p)
cast-recL-reduct refl (inj₁ tt)      M' N' p = refl
cast-recL-reduct refl (inj₂ (W , L)) M' N' p = refl

-- The decomposition of a sum commutes with a context equality, and so does
-- the reduct sum elimination builds from it.

cast⊎ : ∀ {Γ Γ' A B} → Γ ≡ Γ' → (Γ ⊢V⦂ A) ⊎ (Γ ⊢V⦂ B) → (Γ' ⊢V⦂ A) ⊎ (Γ' ⊢V⦂ B)
cast⊎ e (inj₁ W) = inj₁ (castᵛ e W)
cast⊎ e (inj₂ W) = inj₂ (castᵛ e W)

injᵛ-cast : ∀ {A B} {St St' : 𝕊 []} → (e : toCtx St ≡ toCtx St')
          → (V : toCtx St ⊢V⦂ A |+| B)
          → injᵛ (castᵛ e V) ≡ cast⊎ e (injᵛ V)
injᵛ-cast e (var _ x)           = ⊥-elim (|+|-not-in-toCtx x)
injᵛ-cast e (inl V)             = cong injᵛ (cast-inl e {V = V})
injᵛ-cast e (inr V)             = cong injᵛ (cast-inr e {V = V})
injᵛ-cast e (subV V (p |+|ₛ q)) =
  trans (cong injᵛ (cast-subV e {V = V}))
        (trans (cong (sub⊎ p q) (injᵛ-cast e V)) (comm (injᵛ V)))
  where
    comm : ∀ s → sub⊎ p q (cast⊎ e s) ≡ cast⊎ e (sub⊎ p q s)
    comm (inj₁ W) = cong inj₁ (sym (cast-subV e))
    comm (inj₂ W) = cong inj₂ (sym (cast-subV e))

cast-case+-reduct : ∀ {Γ Γ' A B C} → (e : Γ' ≡ Γ) → (s : (Γ' ⊢V⦂ A) ⊎ (Γ' ⊢V⦂ B))
                  → (M' : Γ' ∷ A ⊢C⦂ C) → (N' : Γ' ∷ B ⊢C⦂ C)
                  → case+-reduct (cast⊎ e s) (castᶜ (cong (_∷ A) e) M')
                                 (castᶜ (cong (_∷ B) e) N')
                  ≡ castᶜ e (case+-reduct s M' N')
cast-case+-reduct refl (inj₁ W) M' N' = refl
cast-case+-reduct refl (inj₂ W) M' N' = refl

cast-match-reduct : ∀ {Γ Γ' A B C} → (e : Γ' ≡ Γ)
           → (M' : Γ' ∷ A ∷ B ⊢C⦂ C) → (V' : Γ' ⊢V⦂ A) → (W' : Γ' ⊢V⦂ B)
           → ((castᶜ (cong (λ Γ₀ → Γ₀ ∷ A ∷ B) e) M')
                [ split-[] ↦ V-rename wk-ren (castᵛ e W') ]c) [ split-[] ↦ castᵛ e V' ]c
           ≡ castᶜ e ((M' [ split-[] ↦ V-rename wk-ren W' ]c) [ split-[] ↦ V' ]c)
cast-match-reduct refl M' V' W' = refl

cast-seq-ret : ∀ {Γ Γ' A B ε} → (e : Γ' ≡ Γ)
             → (N' : Γ' ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε) → (V' : Γ' ⊢V⦂ A)
             → (C-rename (cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren))
                 (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ uₑ ⟩ ∷ A) e) N'))
                   [ split-[] ↦ castᵛ e V' ]c
             ≡ castᶜ e ((C-rename
                          (cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren))
                          N') [ split-[] ↦ V' ]c)
cast-seq-ret refl N' V' = refl

cast-box-val : ∀ {Γ Γ' A ρ} → (e : Γ' ≡ Γ) → (V' : Γ' ⟨ ρ ⟩ ⊢V⦂ A)
             → V-rename (eq-ren (sym ++ᶜ-identityˡ))
                 (castᵛ (cong (_⟨ ρ ⟩) e) V')
             ≡ castᵛ (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩) e)
                 (V-rename (eq-ren (sym ++ᶜ-identityˡ)) V')
cast-box-val refl V' = refl

