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

module MonomorphicCalculus.OperationalSemantics.StateEquivalence.Core (Spec : LanguageSpec) where
open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           Spec
open import MonomorphicCalculus.OperationalSemantics.State               Spec

open import Language.Comparisons using (Cmp; holds)
open import MonomorphicCalculus.Syntax.Contexts      Spec
open import MonomorphicCalculus.Syntax.Data          Spec using (⟪_⟫ˢ; compareᵈ; ⌈_⌉ᵇ)
open import MonomorphicCalculus.Syntax.Terms      Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming      Spec
open import MonomorphicCalculus.Syntax.Substitution  Spec
open import MonomorphicCalculus.Syntax.Types Spec

open import MonomorphicCalculus.Syntax.Renaming.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Renaming.Coherence    Spec
open import MonomorphicCalculus.Syntax.Terms.Equivalence     Spec
open import MonomorphicCalculus.Syntax.Terms.Transport       Spec
open import MonomorphicCalculus.Syntax.Substitution.Variables  Spec
open import MonomorphicCalculus.OperationalSemantics.GradedReach Spec
open import MonomorphicCalculus.Syntax.Substitution.Equivalence  Spec


mutual

  data _≐ˢ_ : State [] → State [] → Set where

    ∅-≐ˢ  : ∅ ≐ˢ ∅

    ⟨⟩-≐ˢ : ∀ {𝕊 𝕊'} → (ρ : R) → (e : 𝕊 ≐ˢ 𝕊')
          → (𝕊 ⟨ ρ ⟩ₛ) ≐ˢ (𝕊' ⟨ ρ ⟩ₛ)

    ∷-≐ˢ  : ∀ {A ρ 𝕊 𝕊'}
          → {V  : ([] ++ᶜ toCtx 𝕊  ⟨ ρ ⟩) ⊢ᵛ⦂ A}
          → {V' : ([] ++ᶜ toCtx 𝕊' ⟨ ρ ⟩) ⊢ᵛ⦂ A}
          → (e : 𝕊 ≐ˢ 𝕊')
          → V ≡ castᵛ (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩) (sym (toCtx-≐ˢ e))) V'
          → (𝕊 ∷ₛ V) ≐ˢ (𝕊' ∷ₛ V')

  -- Related states have the same context: `toCtx` reads the skeleton only.

  toCtx-≐ˢ : ∀ {𝕊 𝕊'} → 𝕊 ≐ˢ 𝕊' → toCtx 𝕊 ≡ toCtx 𝕊'
  toCtx-≐ˢ ∅-≐ˢ                = refl
  toCtx-≐ˢ (⟨⟩-≐ˢ ρ e)          = cong (_⟨ ρ ⟩) (toCtx-≐ˢ e)
  toCtx-≐ˢ (∷-≐ˢ {A} {ρ} e eV) = cong (_∷ [ ρ ] A) (toCtx-≐ˢ e)

-- Reflexivity, with its context equality degenerate.

mutual

  ≐ˢ-refl : (𝕊 : State []) → 𝕊 ≐ˢ 𝕊
  ≐ˢ-refl ∅           = ∅-≐ˢ
  ≐ˢ-refl (𝕊 ⟨ ρ ⟩ₛ)   = ⟨⟩-≐ˢ ρ (≐ˢ-refl 𝕊)
  ≐ˢ-refl (𝕊 ∷ₛ V)    =
    ∷-≐ˢ (≐ˢ-refl 𝕊)
      (subst (λ e → V ≡ castᵛ (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ _ ⟩) (sym e)) V)
             (sym (toCtx-≐ˢ-refl 𝕊)) (refl {x = V}))

  toCtx-≐ˢ-refl : (𝕊 : State []) → toCtx-≐ˢ (≐ˢ-refl 𝕊) ≡ refl
  toCtx-≐ˢ-refl ∅          = refl
  toCtx-≐ˢ-refl (𝕊 ⟨ ρ ⟩ₛ) = cong (cong (_⟨ ρ ⟩)) (toCtx-≐ˢ-refl 𝕊)
  toCtx-≐ˢ-refl (_∷ₛ_ {A} {ρ} 𝕊 V) =
    cong (cong (_∷ [ ρ ] A)) (toCtx-≐ˢ-refl 𝕊)

-- Shifting a cast across the relation, and symmetry of `_≐ˢ_`. Symmetry is
-- needed because `VRed`'s Kripke clauses have to replay an extension of the
-- other state (`reach-replay` runs in one direction only).

≡-shift : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (e' : Γ' ≡ Γ)
         → {V : Γ' ⊢ᵛ⦂ A} → {W : Γ ⊢ᵛ⦂ A}
         → castᵛ e' V ≡ W → V ≡ castᵛ e W
≡-shift refl e' {V} {W} eV
  rewrite uip {p = e'} {q = refl} = eV

≐ˢ-sym : ∀ {𝕊 𝕊' : State []} → 𝕊 ≐ˢ 𝕊' → 𝕊' ≐ˢ 𝕊
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

cast-fun⁻ : ∀ {Γ Γ' A B ε} → (e : Γ' ≡ Γ) → {M : Γ ∷ A ⊢ᶜ⦂ B ! ε}
       → (V' : Γ' ⊢ᵛ⦂ A ⇒ B ! ε)
       → fun M ≡ castᵛ e V'
       → Σ[ M' ∈ (Γ' ∷ A ⊢ᶜ⦂ B ! ε) ]
           (V' ≡ fun M') × (M ≡ castᶜ (cong (_∷ A) e) M')
cast-fun⁻ refl _ refl = _ , refl , refl

cast-pair⁻ : ∀ {Γ Γ' A B} → (e : Γ' ≡ Γ) → {V : Γ ⊢ᵛ⦂ A} → {W : Γ ⊢ᵛ⦂ B}
        → (U' : Γ' ⊢ᵛ⦂ A |×| B)
        → ⦉ V , W ⦊ ≡ castᵛ e U'
        → Σ[ V' ∈ (Γ' ⊢ᵛ⦂ A) ] Σ[ W' ∈ (Γ' ⊢ᵛ⦂ B) ]
            (U' ≡ ⦉ V' , W' ⦊) × (V ≡ castᵛ e V') × (W ≡ castᵛ e W')
cast-pair⁻ refl _ refl = _ , _ , refl , refl , refl

cast-zero⁻ : ∀ {Γ Γ'} → (e : Γ' ≡ Γ) → (V' : Γ' ⊢ᵛ⦂ nat)
           → zero ≡ castᵛ e V' → V' ≡ zero
cast-zero⁻ refl _ refl = refl

cast-succ⁻ : ∀ {Γ Γ'} → (e : Γ' ≡ Γ) → {V : Γ ⊢ᵛ⦂ nat}
           → (U' : Γ' ⊢ᵛ⦂ nat)
           → succ V ≡ castᵛ e U'
           → Σ[ V' ∈ (Γ' ⊢ᵛ⦂ nat) ] (U' ≡ succ V') × (V ≡ castᵛ e V')
cast-succ⁻ refl _ refl = _ , refl , refl

cast-true⁻ : ∀ {Γ Γ'} → (e : Γ' ≡ Γ) → (V' : Γ' ⊢ᵛ⦂ bool)
        → true ≡ castᵛ e V' → V' ≡ true
cast-true⁻ refl _ refl = refl

cast-false⁻ : ∀ {Γ Γ'} → (e : Γ' ≡ Γ) → (V' : Γ' ⊢ᵛ⦂ bool)
         → false ≡ castᵛ e V' → V' ≡ false
cast-false⁻ refl _ refl = refl

cast-return⁻ : ∀ {Γ Γ' A} → (e : Γ' ≡ Γ) → {V : Γ ⊢ᵛ⦂ A}
          → (M' : Γ' ⊢ᶜ⦂ A ! 𝟏ₑ)
          → return V ≡ castᶜ e M'
          → Σ[ V' ∈ (Γ' ⊢ᵛ⦂ A) ] (M' ≡ return V') × (V ≡ castᵛ e V')
cast-return⁻ refl _ refl = _ , refl , refl

cast-app⁻ : ∀ {Γ Γ' A C} → (e : Γ' ≡ Γ) → {V : Γ ⊢ᵛ⦂ A ⇒ C} → {W : Γ ⊢ᵛ⦂ A}
       → (M' : Γ' ⊢ᶜ⦂ C)
       → (V · W) ≡ castᶜ e M'
       → Σ[ V' ∈ (Γ' ⊢ᵛ⦂ A ⇒ C) ] Σ[ W' ∈ (Γ' ⊢ᵛ⦂ A) ]
           (M' ≡ V' · W') × (V ≡ castᵛ e V') × (W ≡ castᵛ e W')
cast-app⁻ refl _ refl = _ , _ , refl , refl , refl

cast-seq⁻ : ∀ {Γ Γ' A B ε ε'} → (e : Γ' ≡ Γ)
       → {M : Γ ⊢ᶜ⦂ A ! ε} → {N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'}
       → (P' : Γ' ⊢ᶜ⦂ B ! (ε ·ₑ ε'))
       → (M ⨟ N) ≡ castᶜ e P'
       → Σ[ M' ∈ (Γ' ⊢ᶜ⦂ A ! ε) ] Σ[ N' ∈ (Γ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε') ]
           (P' ≡ (M' ⨟ N')) × (M ≡ castᶜ e M')
         × (N ≡ castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) e) N')
cast-seq⁻ refl _ refl = _ , _ , refl , refl , refl

cast-match⁻ : ∀ {Γ Γ' A B C} → (e : Γ' ≡ Γ)
         → {V : Γ ⊢ᵛ⦂ A |×| B} → {M : Γ ∷ A ∷ B ⊢ᶜ⦂ C}
         → (P' : Γ' ⊢ᶜ⦂ C)
         → (match V `with M) ≡ castᶜ e P'
         → Σ[ V' ∈ (Γ' ⊢ᵛ⦂ A |×| B) ] Σ[ M' ∈ (Γ' ∷ A ∷ B ⊢ᶜ⦂ C) ]
             (P' ≡ (match V' `with M')) × (V ≡ castᵛ e V')
           × (M ≡ castᶜ (cong (λ Γ₀ → Γ₀ ∷ A ∷ B) e) M')
cast-match⁻ refl _ refl = _ , _ , refl , refl , refl

cast-if⁻ : ∀ {Γ Γ' C} → (e : Γ' ≡ Γ)
      → {V : Γ ⊢ᵛ⦂ bool} → {M N : Γ ⊢ᶜ⦂ C}
      → (P' : Γ' ⊢ᶜ⦂ C)
      → (if V `then M `else N) ≡ castᶜ e P'
      → Σ[ V' ∈ (Γ' ⊢ᵛ⦂ bool) ] Σ[ M' ∈ (Γ' ⊢ᶜ⦂ C) ] Σ[ N' ∈ (Γ' ⊢ᶜ⦂ C) ]
          (P' ≡ (if V' `then M' `else N')) × (V ≡ castᵛ e V')
        × (M ≡ castᶜ e M') × (N ≡ castᶜ e N')
cast-if⁻ refl _ refl = _ , _ , _ , refl , refl , refl , refl

cast-cmp⁻ : ∀ {Γ Γ' A ⋈} → (e : Γ' ≡ Γ)
          → {V W : Γ ⊢ᵛ⦂ A} → {et : Et A}
          → (P' : Γ' ⊢ᶜ⦂ bool ! 𝟏ₑ)
          → cmp ⋈ V W et ≡ castᶜ e P'
          → Σ[ V' ∈ (Γ' ⊢ᵛ⦂ A) ] Σ[ W' ∈ (Γ' ⊢ᵛ⦂ A) ]
              (P' ≡ cmp ⋈ V' W' et) × (V ≡ castᵛ e V') × (W ≡ castᵛ e W')
cast-cmp⁻ refl _ refl = _ , _ , refl , refl , refl

cast-matchℕ⁻ : ∀ {Γ Γ' C} → (e : Γ' ≡ Γ)
             → {V : Γ ⊢ᵛ⦂ nat} → {M : Γ ⊢ᶜ⦂ C} → {N : Γ ∷ nat ⊢ᶜ⦂ C}
             → (P' : Γ' ⊢ᶜ⦂ C)
             → (matchℕ V `zero M `succ N) ≡ castᶜ e P'
             → Σ[ V' ∈ (Γ' ⊢ᵛ⦂ nat) ] Σ[ M' ∈ (Γ' ⊢ᶜ⦂ C) ]
               Σ[ N' ∈ (Γ' ∷ nat ⊢ᶜ⦂ C) ]
                (P' ≡ (matchℕ V' `zero M' `succ N')) × (V ≡ castᵛ e V')
               × (M ≡ castᶜ e M') × (N ≡ castᶜ (cong (_∷ nat) e) N')
cast-matchℕ⁻ refl _ refl = _ , _ , _ , refl , refl , refl , refl

cast-recℕ⁻ : ∀ {Γ Γ' B ε} → (e : Γ' ≡ Γ)
           → {V : Γ ⊢ᵛ⦂ nat} → {M : Γ ⊢ᶜ⦂ B ! ε}
           → {N : (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
           → {p : ε ·ₑ ε ≾ₑ ε}
           → (P' : Γ' ⊢ᶜ⦂ B ! ε)
           → recℕ V M N p ≡ castᶜ e P'
           → Σ[ V' ∈ (Γ' ⊢ᵛ⦂ nat) ] Σ[ M' ∈ (Γ' ⊢ᶜ⦂ B ! ε) ]
             Σ[ N' ∈ ((Γ' ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε) ]
               (P' ≡ recℕ V' M' N' p) × (V ≡ castᵛ e V')
             × (M ≡ castᶜ e M')
             × (N ≡ castᶜ (cong (λ X → (X ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B) e) N')
cast-recℕ⁻ refl _ refl = _ , _ , _ , refl , refl , refl , refl

-- The successor reduct of a recursion commutes with a context equality.

cast-recℕ-reduct : ∀ {Γ Γ' B ε} → (e : Γ' ≡ Γ)
                 → (V' : Γ' ⊢ᵛ⦂ nat) → (M' : Γ' ⊢ᶜ⦂ B ! ε)
                 → (N' : (Γ' ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε)
                 → (p : ε ·ₑ ε ≾ₑ ε)
                 → let N₁ = castᶜ (cong (λ X → (X ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B) e) N' in
                   coerce p (recℕ (castᵛ e V') (castᶜ e M') N₁ p
                             ⨟ recℕ-step (castᵛ e V') N₁)
                   ≡ castᶜ e (coerce p (recℕ V' M' N' p ⨟ recℕ-step V' N'))
cast-recℕ-reduct refl V' M' N' p = refl

cast-matchL⁻ : ∀ {Γ Γ' A C} → (e : Γ' ≡ Γ)
             → {V : Γ ⊢ᵛ⦂ list A} → {M : Γ ⊢ᶜ⦂ C} → {N : Γ ∷ A ∷ list A ⊢ᶜ⦂ C}
             → (P' : Γ' ⊢ᶜ⦂ C)
             → matchL V `nil M `cons N ≡ castᶜ e P'
             → Σ[ V' ∈ (Γ' ⊢ᵛ⦂ list A) ] Σ[ M' ∈ (Γ' ⊢ᶜ⦂ C) ]
               Σ[ N' ∈ (Γ' ∷ A ∷ list A ⊢ᶜ⦂ C) ]
                (P' ≡ matchL V' `nil M' `cons N') × (V ≡ castᵛ e V')
               × (M ≡ castᶜ e M') × (N ≡ castᶜ (cong (λ X → X ∷ A ∷ list A) e) N')
cast-matchL⁻ refl _ refl = _ , _ , _ , refl , refl , refl , refl

cast-recL⁻ : ∀ {Γ Γ' A B ε} → (e : Γ' ≡ Γ)
           → {V : Γ ⊢ᵛ⦂ list A} → {M : Γ ⊢ᶜ⦂ B ! ε}
           → {N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
           → {p : ε ·ₑ ε ≾ₑ ε}
           → (P' : Γ' ⊢ᶜ⦂ B ! ε)
           → recL V M N p ≡ castᶜ e P'
           → Σ[ V' ∈ (Γ' ⊢ᵛ⦂ list A) ] Σ[ M' ∈ (Γ' ⊢ᶜ⦂ B ! ε) ]
             Σ[ N' ∈ ((Γ' ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε) ]
               (P' ≡ recL V' M' N' p) × (V ≡ castᵛ e V')
             × (M ≡ castᶜ e M')
             × (N ≡ castᶜ (cong (λ X → (X ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B) e) N')
cast-recL⁻ refl _ refl = _ , _ , _ , refl , refl , refl , refl

cast-match+⁻ : ∀ {Γ Γ' A B C} → (e : Γ' ≡ Γ)
             → {V : Γ ⊢ᵛ⦂ A |+| B} → {M : Γ ∷ A ⊢ᶜ⦂ C} → {N : Γ ∷ B ⊢ᶜ⦂ C}
             → (P' : Γ' ⊢ᶜ⦂ C)
             → (match+ V `inl M `inr N) ≡ castᶜ e P'
             → Σ[ V' ∈ (Γ' ⊢ᵛ⦂ A |+| B) ] Σ[ M' ∈ (Γ' ∷ A ⊢ᶜ⦂ C) ]
               Σ[ N' ∈ (Γ' ∷ B ⊢ᶜ⦂ C) ]
                (P' ≡ (match+ V' `inl M' `inr N')) × (V ≡ castᵛ e V')
               × (M ≡ castᶜ (cong (_∷ A) e) M') × (N ≡ castᶜ (cong (_∷ B) e) N')
cast-match+⁻ refl _ refl = _ , _ , _ , refl , refl , refl , refl

cast-perform⁻ : ∀ {Γ Γ' A ε} → (e : Γ' ≡ Γ) → {op : Op}
           → {V : Γ ⊢ᵛ⦂ ⌜ param op ⌝ᵍ}
           → {M : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ A ! ε}
           → (P' : Γ' ⊢ᶜ⦂ A ! (op-grade op ·ₑ ε))
           → perform op V M ≡ castᶜ e P'
           → Σ[ V' ∈ (Γ' ⊢ᵛ⦂ ⌜ param op ⌝ᵍ) ]
             Σ[ M' ∈ (Γ' ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ
                        ⊢ᶜ⦂ A ! ε) ]
               (P' ≡ perform op V' M') × (V ≡ castᵛ e V')
             × (M ≡ castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ∣ op-grade op ∣ᵉ ⟩
                                            ∷ ⌜ arity op ⌝ᵍ) e) M')
cast-perform⁻ refl _ refl = _ , _ , refl , refl , refl

cast-delay⁻ : ∀ {Γ Γ' A ε τ} → (e : Γ' ≡ Γ)
         → {M : Γ ⟨ ιᵣ τ ⟩ ⊢ᶜ⦂ A ! ε}
         → (P' : Γ' ⊢ᶜ⦂ A ! (ιₑ τ ·ₑ ε))
         → delay τ M ≡ castᶜ e P'
         → Σ[ M' ∈ (Γ' ⟨ ιᵣ τ ⟩ ⊢ᶜ⦂ A ! ε) ]
             (P' ≡ delay τ M')
           × (M ≡ castᶜ (cong (_⟨ ιᵣ τ ⟩) e) M')
cast-delay⁻ refl _ refl = _ , refl , refl

cast-box⁻ : ∀ {Γ Γ' A C ρ} → (e : Γ' ≡ Γ)
       → {V : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A} → {M : Γ ∷ [ ρ ] A ⊢ᶜ⦂ C}
       → (P' : Γ' ⊢ᶜ⦂ C)
       → box _ V M ≡ castᶜ e P'
       → Σ[ V' ∈ (Γ' ⟨ ρ ⟩ ⊢ᵛ⦂ A) ] Σ[ M' ∈ (Γ' ∷ [ ρ ] A ⊢ᶜ⦂ C) ]
           (P' ≡ box _ V' M') × (V ≡ castᵛ (cong (_⟨ ρ ⟩) e) V')
         × (M ≡ castᶜ (cong (_∷ [ ρ ] A) e) M')
cast-box⁻ refl _ refl = _ , _ , refl , refl , refl

cast-sub⁻ : ∀ {Γ Γ' C C'} → (e : Γ' ≡ Γ) → {p : C <:ᶜ C'}
          → {M : Γ ⊢ᶜ⦂ C}
          → (P' : Γ' ⊢ᶜ⦂ C')
          → subC M p ≡ castᶜ e P'
          → Σ[ p' ∈ (C <:ᶜ C') ] Σ[ M' ∈ (Γ' ⊢ᶜ⦂ C) ]
              (P' ≡ subC M' p') × (M ≡ castᶜ e M')
cast-sub⁻ refl _ refl = _ , _ , refl , refl

cast-subV⁻ : ∀ {Γ Γ' A A'} → (e : Γ' ≡ Γ) → {p : A <:ᵛ A'}
           → {V : Γ ⊢ᵛ⦂ A}
           → (W' : Γ' ⊢ᵛ⦂ A')
           → subV V p ≡ castᵛ e W'
           → Σ[ p' ∈ (A <:ᵛ A') ] Σ[ V' ∈ (Γ' ⊢ᵛ⦂ A) ]
               (W' ≡ subV V' p') × (V ≡ castᵛ e V')
cast-subV⁻ refl _ refl = _ , _ , refl , refl

-- the same, keeping the coercion

cast-subV-at⁻ : ∀ {Γ Γ' A A'} → (e : Γ' ≡ Γ) → {p : A <:ᵛ A'}
              → {V : Γ ⊢ᵛ⦂ A}
              → (W' : Γ' ⊢ᵛ⦂ A')
              → subV V p ≡ castᵛ e W'
              → Σ[ V' ∈ (Γ' ⊢ᵛ⦂ A) ] (W' ≡ subV V' p) × (V ≡ castᵛ e V')
cast-subV-at⁻ refl _ refl = _ , refl , refl

cast-handle⁻ : ∀ {Γ Γ' A B ε ε'} → (e : Γ' ≡ Γ)
          → {M : Γ ⊢ᶜ⦂ A ! ε} → {V : Γ ⊢ᵛ⦂ (A ! ε) ⇛ (B ! ε')}
          → (P' : Γ' ⊢ᶜ⦂ B ! (ε ·ₑ ε'))
          → (handle M `with V) ≡ castᶜ e P'
          → Σ[ M' ∈ (Γ' ⊢ᶜ⦂ A ! ε) ] Σ[ V' ∈ (Γ' ⊢ᵛ⦂ (A ! ε) ⇛ (B ! ε')) ]
              (P' ≡ (handle M' `with V')) × (M ≡ castᶜ e M') × (V ≡ castᵛ e V')
cast-handle⁻ refl _ refl = _ , _ , refl , refl , refl

cast-handler⁻ : ∀ {Γ Γ' A B ε ε'} → (e : Γ' ≡ Γ)
          → {H : (op : Op) → (ε'' : E) →
                   Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                     ∷ [ ∣ op-grade op ∣ᵉ ]
                         (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                   ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε'')}
          → {N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'}
          → (W' : Γ' ⊢ᵛ⦂ (A ! ε) ⇛ (B ! ε'))
          → handler N H ≡ castᵛ e W'
          → Σ[ H' ∈ ((op : Op) → (ε'' : E) →
                       Γ' ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                         ∷ [ ∣ op-grade op ∣ᵉ ]
                             (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                       ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε'')) ]
            Σ[ N' ∈ (Γ' ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε') ]
              (W' ≡ handler N' H')
            × (∀ op ε'' → H op ε''
                 ≡ castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                                          ∷ [ ∣ op-grade op ∣ᵉ ]
                                              (⌜ arity op ⌝ᵍ ⇒ B ! ε''))
                                e)
                          (H' op ε''))
            × (N ≡ castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A) e) N')
cast-handler⁻ refl _ refl = _ , _ , refl , (λ op ε'' → refl) , refl

cast-unbox⁻ : ∀ {Γ Γ' A A₀ C ρ ρ'} → (e : Γ' ≡ Γ)
         → {x : [ ρ ] A₀ ∈[ ρ' ] Γ} → {rel : ρ' ≾ᵣ ρ} → {p : A₀ <:ᵛ A}
         → {M : Γ ∷ A ⊢ᶜ⦂ C}
         → (P' : Γ' ⊢ᶜ⦂ C)
         → unbox x rel p M ≡ castᶜ e P'
         → Σ[ ρ'' ∈ R ] Σ[ x' ∈ ([ ρ ] A₀ ∈[ ρ'' ] Γ') ] Σ[ rel' ∈ (ρ'' ≾ᵣ ρ) ]
           Σ[ p' ∈ (A₀ <:ᵛ A) ] Σ[ M' ∈ (Γ' ∷ A ⊢ᶜ⦂ C) ]
             (P' ≡ unbox x' rel' p' M')
           × (_≡_ {A = Var Γ ([ ρ ] A₀)} (ρ' , x) (Var-cast e (ρ'' , x')))
           × (M ≡ castᶜ (cong (_∷ A) e) M')
cast-unbox⁻ refl _ refl = _ , _ , _ , _ , _ , refl , refl , refl

-- The reducts are built by renaming, substitution and retyping, each of
-- which commutes with a cast.

cast-app-reduct : ∀ {Γ Γ' A C} → (e : Γ' ≡ Γ)
         → (M' : Γ' ∷ A ⊢ᶜ⦂ C) → (W' : Γ' ⊢ᵛ⦂ A)
         → (castᶜ (cong (_∷ A) e) M') [ split-[] ↦ castᵛ e W' ]c
         ≡ castᶜ e (M' [ split-[] ↦ W' ]c)
cast-app-reduct refl M' W' = refl

-- The two projections commute with a context equality: a one-clause
-- induction on the value, the variable clause being absurd.

fstᵛ-cast : ∀ {A B} {𝕊 𝕊' : State []} → (e : toCtx 𝕊 ≡ toCtx 𝕊')
          → (V : toCtx 𝕊 ⊢ᵛ⦂ A |×| B)
          → fstᵛ (castᵛ e V) ≡ castᵛ e (fstᵛ V)
fstᵛ-cast e (var _ x)           = ⊥-elim (⦉⦊-not-in-toCtx x)
fstᵛ-cast e ⦉ V , W ⦊           = cong fstᵛ (cast-pair e {V} {W})
fstᵛ-cast e (subV V (p |×|ₛ _)) =
  trans (cong fstᵛ (cast-subV e {V = V}))
        (trans (cong (λ z → subV z p) (fstᵛ-cast e V))
               (sym (cast-subV e)))

sndᵛ-cast : ∀ {A B} {𝕊 𝕊' : State []} → (e : toCtx 𝕊 ≡ toCtx 𝕊')
          → (V : toCtx 𝕊 ⊢ᵛ⦂ A |×| B)
          → sndᵛ (castᵛ e V) ≡ castᵛ e (sndᵛ V)
sndᵛ-cast e (var _ x)           = ⊥-elim (⦉⦊-not-in-toCtx x)
sndᵛ-cast e ⦉ V , W ⦊           = cong sndᵛ (cast-pair e {V} {W})
sndᵛ-cast e (subV V (_ |×|ₛ q)) =
  trans (cong sndᵛ (cast-subV e {V = V}))
        (trans (cong (λ z → subV z q) (sndᵛ-cast e V))
               (sym (cast-subV e)))

-- The datum a value of an eternal type is commutes with a context equality,
-- and so does the comparison's reduct: the data, hence the outcome, agree.

cast-closed : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (V : ∀ {Δ} → Δ ⊢ᵛ⦂ A) → castᵛ e V ≡ V
cast-closed refl V = refl

⌊⌋ᵈ-cast : ∀ {A} {𝕊 𝕊' : State []} → (e : toCtx 𝕊 ≡ toCtx 𝕊') → (et : Et A)
         → (V : toCtx 𝕊 ⊢ᵛ⦂ A)
         → ⌊_⌋ᵈ {𝕊 = 𝕊'} et (castᵛ e V) ≡ ⌊_⌋ᵈ {𝕊 = 𝕊} et V
⌊⌋ᵈ-cast e et (var _ x) = ⊥-elim (eternal-not-in-toCtx et x)
⌊⌋ᵈ-cast {𝕊' = 𝕊'} e et (subV V p) =
  trans (cong (⌊_⌋ᵈ {𝕊 = 𝕊'} et) (cast-subV e {V = V}))
        (cong ⟪ p ⟫ˢ (⌊⌋ᵈ-cast e (<:ᵛ-eternalˡ p et) V))
⌊⌋ᵈ-cast {𝕊' = 𝕊'} e et@(Baseₑ _) (const B c) =
  cong (⌊_⌋ᵈ {𝕊 = 𝕊'} et) (cast-closed e (const B c))
⌊⌋ᵈ-cast {𝕊' = 𝕊'} e unitₑ ⋆ = cong (⌊_⌋ᵈ {𝕊 = 𝕊'} unitₑ) (cast-closed e ⋆)
⌊⌋ᵈ-cast {𝕊' = 𝕊'} e boolₑ true = cong (⌊_⌋ᵈ {𝕊 = 𝕊'} boolₑ) (cast-closed e true)
⌊⌋ᵈ-cast {𝕊' = 𝕊'} e boolₑ false = cong (⌊_⌋ᵈ {𝕊 = 𝕊'} boolₑ) (cast-closed e false)
⌊⌋ᵈ-cast {𝕊' = 𝕊'} e natₑ zero = cong (⌊_⌋ᵈ {𝕊 = 𝕊'} natₑ) (cast-closed e zero)
⌊⌋ᵈ-cast {𝕊' = 𝕊'} e natₑ (succ V) =
  trans (cong (⌊_⌋ᵈ {𝕊 = 𝕊'} natₑ) (cast-succ e {V = V}))
        (cong suc (⌊⌋ᵈ-cast e natₑ V))
⌊⌋ᵈ-cast {𝕊' = 𝕊'} e et@(et₁ |×|ₑ et₂) ⦉ V , W ⦊ =
  trans (cong (⌊_⌋ᵈ {𝕊 = 𝕊'} et) (cast-pair e {V} {W}))
        (cong₂ _,_ (⌊⌋ᵈ-cast e et₁ V) (⌊⌋ᵈ-cast e et₂ W))
⌊⌋ᵈ-cast {𝕊' = 𝕊'} e et@(et₁ |+|ₑ et₂) (inl V) =
  trans (cong (⌊_⌋ᵈ {𝕊 = 𝕊'} et) (cast-inl e {V = V}))
        (cong inj₁ (⌊⌋ᵈ-cast e et₁ V))
⌊⌋ᵈ-cast {𝕊' = 𝕊'} e et@(et₁ |+|ₑ et₂) (inr V) =
  trans (cong (⌊_⌋ᵈ {𝕊 = 𝕊'} et) (cast-inr e {V = V}))
        (cong inj₂ (⌊⌋ᵈ-cast e et₂ V))
⌊⌋ᵈ-cast {𝕊' = 𝕊'} e et@(listₑ _) nil =
  cong (⌊_⌋ᵈ {𝕊 = 𝕊'} et) (cast-nil e)
⌊⌋ᵈ-cast {𝕊' = 𝕊'} e et@(listₑ et₁) (cons V W) =
  trans (cong (⌊_⌋ᵈ {𝕊 = 𝕊'} et) (cast-cons e {V} {W}))
        (cong₂ List._∷_ (⌊⌋ᵈ-cast e et₁ V) (⌊⌋ᵈ-cast e et W))

cast-cmp-reduct : ∀ {A} {𝕊 𝕊' : State []} → (e : toCtx 𝕊' ≡ toCtx 𝕊)
                → (⋈ : Cmp) → (V' W' : toCtx 𝕊' ⊢ᵛ⦂ A) → (et : Et A)
                → cmp-reduct {𝕊 = 𝕊} ⋈ (castᵛ e V') (castᵛ e W') et
                ≡ castᶜ e (cmp-reduct {𝕊 = 𝕊'} ⋈ V' W' et)
cast-cmp-reduct e ⋈ V' W' et =
  trans (cong₂ (λ a b → return ⌈ holds ⋈ (compareᵈ et a b) ⌉ᵇ)
               (⌊⌋ᵈ-cast e et V') (⌊⌋ᵈ-cast e et W'))
        (sym (trans (cast-ret e) (cong return (cast-closed e ⌈ _ ⌉ᵇ))))

-- The decomposition of a list commutes with a context equality, and so do
-- the reducts the list eliminators build from it.

castL : ∀ {Γ Γ' A} → Γ ≡ Γ' → ListView Γ A → ListView Γ' A
castL e (inj₁ tt)      = inj₁ tt
castL e (inj₂ (W , L)) = inj₂ (castᵛ e W , castᵛ e L)

listᵛ-cast : ∀ {A} {𝕊 𝕊' : State []} → (e : toCtx 𝕊 ≡ toCtx 𝕊')
           → (V : toCtx 𝕊 ⊢ᵛ⦂ list A)
           → listᵛ (castᵛ e V) ≡ castL e (listᵛ V)
listᵛ-cast e (var _ x)            = ⊥-elim (list-not-in-toCtx x)
listᵛ-cast e nil                  = cong listᵛ (cast-nil e)
listᵛ-cast e (cons V W)           = cong listᵛ (cast-cons e {V} {W})
listᵛ-cast e (subV V (listₛ p))   =
  trans (cong listᵛ (cast-subV e {V = V}))
        (trans (cong (subL p) (listᵛ-cast e V)) (comm (listᵛ V)))
  where
    comm : ∀ l → subL p (castL e l) ≡ castL e (subL p l)
    comm (inj₁ tt)      = refl
    comm (inj₂ (W , L)) =
      cong₂ (λ a b → inj₂ (a , b)) (sym (cast-subV e)) (sym (cast-subV e))

cast-matchL-reduct : ∀ {Γ Γ' A C} → (e : Γ' ≡ Γ) → (l : ListView Γ' A)
                   → (M' : Γ' ⊢ᶜ⦂ C) → (N' : Γ' ∷ A ∷ list A ⊢ᶜ⦂ C)
                   → matchL-reduct (castL e l) (castᶜ e M')
                                   (castᶜ (cong (λ X → X ∷ A ∷ list A) e) N')
                   ≡ castᶜ e (matchL-reduct l M' N')
cast-matchL-reduct refl (inj₁ tt)      M' N' = refl
cast-matchL-reduct refl (inj₂ (W , L)) M' N' = refl

cast-recL-reduct : ∀ {Γ Γ' A B ε} → (e : Γ' ≡ Γ) → (l : ListView Γ' A)
                 → (M' : Γ' ⊢ᶜ⦂ B ! ε)
                 → (N' : (Γ' ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε)
                 → (p : ε ·ₑ ε ≾ₑ ε)
                 → recL-reduct (castL e l) (castᶜ e M')
                     (castᶜ (cong (λ X → (X ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B) e) N') p
                 ≡ castᶜ e (recL-reduct l M' N' p)
cast-recL-reduct refl (inj₁ tt)      M' N' p = refl
cast-recL-reduct refl (inj₂ (W , L)) M' N' p = refl

-- The decomposition of a sum commutes with a context equality, and so does
-- the reduct sum elimination builds from it.

cast⊎ : ∀ {Γ Γ' A B} → Γ ≡ Γ' → (Γ ⊢ᵛ⦂ A) ⊎ (Γ ⊢ᵛ⦂ B) → (Γ' ⊢ᵛ⦂ A) ⊎ (Γ' ⊢ᵛ⦂ B)
cast⊎ e (inj₁ W) = inj₁ (castᵛ e W)
cast⊎ e (inj₂ W) = inj₂ (castᵛ e W)

injᵛ-cast : ∀ {A B} {𝕊 𝕊' : State []} → (e : toCtx 𝕊 ≡ toCtx 𝕊')
          → (V : toCtx 𝕊 ⊢ᵛ⦂ A |+| B)
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

cast-match+-reduct : ∀ {Γ Γ' A B C} → (e : Γ' ≡ Γ) → (s : (Γ' ⊢ᵛ⦂ A) ⊎ (Γ' ⊢ᵛ⦂ B))
                   → (M' : Γ' ∷ A ⊢ᶜ⦂ C) → (N' : Γ' ∷ B ⊢ᶜ⦂ C)
                   → match+-reduct (cast⊎ e s) (castᶜ (cong (_∷ A) e) M')
                                   (castᶜ (cong (_∷ B) e) N')
                   ≡ castᶜ e (match+-reduct s M' N')
cast-match+-reduct refl (inj₁ W) M' N' = refl
cast-match+-reduct refl (inj₂ W) M' N' = refl

cast-match-reduct : ∀ {Γ Γ' A B C} → (e : Γ' ≡ Γ)
           → (M' : Γ' ∷ A ∷ B ⊢ᶜ⦂ C) → (V' : Γ' ⊢ᵛ⦂ A) → (W' : Γ' ⊢ᵛ⦂ B)
           → ((castᶜ (cong (λ Γ₀ → Γ₀ ∷ A ∷ B) e) M')
                [ split-[] ↦ V-rename wk-ren (castᵛ e W') ]c) [ split-[] ↦ castᵛ e V' ]c
           ≡ castᶜ e ((M' [ split-[] ↦ V-rename wk-ren W' ]c) [ split-[] ↦ V' ]c)
cast-match-reduct refl M' V' W' = refl

cast-seq-ret : ∀ {Γ Γ' A B ε} → (e : Γ' ≡ Γ)
             → (N' : Γ' ⟨ ∣ 𝟏ₑ ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε) → (V' : Γ' ⊢ᵛ⦂ A)
             → (C-rename (cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-𝟏ᵉ) ∘ʳ ⟨⟩-η-ren))
                 (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ∣ 𝟏ₑ ∣ᵉ ⟩ ∷ A) e) N'))
                   [ split-[] ↦ castᵛ e V' ]c
             ≡ castᶜ e ((C-rename
                          (cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-𝟏ᵉ) ∘ʳ ⟨⟩-η-ren))
                          N') [ split-[] ↦ V' ]c)
cast-seq-ret refl N' V' = refl

cast-box-val : ∀ {Γ Γ' A ρ} → (e : Γ' ≡ Γ) → (V' : Γ' ⟨ ρ ⟩ ⊢ᵛ⦂ A)
             → V-rename (eq-ren (sym ++ᶜ-identityˡ))
                 (castᵛ (cong (_⟨ ρ ⟩) e) V')
             ≡ castᵛ (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩) e)
                 (V-rename (eq-ren (sym ++ᶜ-identityˡ)) V')
cast-box-val refl V' = refl

