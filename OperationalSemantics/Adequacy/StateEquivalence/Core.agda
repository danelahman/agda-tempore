------------------------------------------------------------------------
-- States up to the term equivalence, and inverting a cast.
------------------------------------------------------------------------

open import Data.Product

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Relation.Nullary using (¬_)

open import Util.Equality

module OperationalSemantics.Adequacy.StateEquivalence.Core (Spec : LanguageSpec) where
open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem Spec
open import OperationalSemantics.State               Spec

open import Syntax.Contexts      Spec
open import Syntax.Language      Spec
open import Syntax.RenActions    Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

open import Syntax.Renamings.Equivalence Spec
open import Syntax.Renamings.Coherence   Spec
open import Syntax.Terms.Equivalence     Spec
open import Syntax.Terms.Transport       Spec
open import Syntax.Substitutions.Variables Spec
open import OperationalSemantics.Adequacy.GradedReach          Spec
open import Syntax.Substitutions.Equivalence Spec


-- STATES UP TO THE EQUIVALENCE

mutual

  data _≐ˢ_ : 𝕊 [] → 𝕊 [] → Set where

    ∅-≐ˢ  : ∅ ≐ˢ ∅

    ⟨⟩-≐ˢ : ∀ {St St'} → (ρ : R) → (e : St ≐ˢ St')
          → (St ⟨ ρ ⟩ₛ) ≐ˢ (St' ⟨ ρ ⟩ₛ)

    ∷-≐ˢ  : ∀ {A ρ St St'}
          → {V  : ([] ++ᶜ toCtx St  ⟨ ρ ⟩) ⊢V⦂ A}
          → {V' : ([] ++ᶜ toCtx St' ⟨ ρ ⟩) ⊢V⦂ A}
          → (e : St ≐ˢ St')
          → V ≐ᵛ castᵛ (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩) (sym (toCtx-≐ˢ e))) V'
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
      (subst (λ e → V ≐ᵛ castᵛ (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ _ ⟩) (sym e)) V)
             (sym (toCtx-≐ˢ-refl St)) (≐ᵛ-refl V))

  toCtx-≐ˢ-refl : (St : 𝕊 []) → toCtx-≐ˢ (≐ˢ-refl St) ≡ refl
  toCtx-≐ˢ-refl ∅          = refl
  toCtx-≐ˢ-refl (St ⟨ ρ ⟩ₛ) = cong (cong (_⟨ ρ ⟩)) (toCtx-≐ˢ-refl St)
  toCtx-≐ˢ-refl (_∷ₛ_ {A} {ρ} St V) =
    cong (cong (_∷ [ ρ ] A)) (toCtx-≐ˢ-refl St)

-- Shifting a cast across the relation, and symmetry of `_≐ˢ_`. Symmetry is
-- needed because `Val`'s Kripke clauses have to replay an extension of the
-- *other* state (`reach-replay` runs in one direction only).

≐ᵛ-shift : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (e' : Γ' ≡ Γ)
         → {V : Γ' ⊢V⦂ A} → {W : Γ ⊢V⦂ A}
         → castᵛ e' V ≐ᵛ W → V ≐ᵛ castᵛ e W
≐ᵛ-shift refl e' {V} {W} eV
  rewrite uip {p = e'} {q = refl} = eV

≐ˢ-sym : ∀ {St St' : 𝕊 []} → St ≐ˢ St' → St' ≐ˢ St
≐ˢ-sym ∅-≐ˢ         = ∅-≐ˢ
≐ˢ-sym (⟨⟩-≐ˢ ρ e)   = ⟨⟩-≐ˢ ρ (≐ˢ-sym e)
≐ˢ-sym (∷-≐ˢ {A = A} {ρ = ρ} e eV) =
  ∷-≐ˢ (≐ˢ-sym e)
    (≐ᵛ-shift (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩) (sym (toCtx-≐ˢ (≐ˢ-sym e))))
              (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩) (sym (toCtx-≐ˢ e)))
              (≐ᵛ-sym eV))

------------------------------------------------------------------------
-- INVERTING A CAST
--
-- The bisimulation cases on the reduction, which fixes the shape of the
-- left-hand term; the shape of the right-hand one has to be read back out of
-- `M ≐ᶜ castᶜ e M'`. A cast along a *neutral* equality does not reduce, so this
-- cannot be done in place — but each inversion is one line as a standalone
-- lemma over abstract contexts, where the equality can be matched.
------------------------------------------------------------------------

≐-lam⁻ : ∀ {Γ Γ' A B ε} → (e : Γ' ≡ Γ) → {M : Γ ∷ A ⊢C⦂ B ‼ ε}
       → (V' : Γ' ⊢V⦂ A ⇒ B ‼ ε)
       → lam M ≐ᵛ castᵛ e V'
       → Σ[ M' ∈ (Γ' ∷ A ⊢C⦂ B ‼ ε) ]
           (V' ≡ lam M') × (M ≐ᶜ castᶜ (cong (_∷ A) e) M')
≐-lam⁻ refl _ (lam-≐ eM) = _ , refl , eM

≐-pair⁻ : ∀ {Γ Γ' A B} → (e : Γ' ≡ Γ) → {V : Γ ⊢V⦂ A} → {W : Γ ⊢V⦂ B}
        → (U' : Γ' ⊢V⦂ A |×| B)
        → ⦉ V , W ⦊ ≐ᵛ castᵛ e U'
        → Σ[ V' ∈ (Γ' ⊢V⦂ A) ] Σ[ W' ∈ (Γ' ⊢V⦂ B) ]
            (U' ≡ ⦉ V' , W' ⦊) × (V ≐ᵛ castᵛ e V') × (W ≐ᵛ castᵛ e W')
≐-pair⁻ refl _ (pair-≐ eV eW) = _ , _ , refl , eV , eW

≐-return⁻ : ∀ {Γ Γ' A} → (e : Γ' ≡ Γ) → {V : Γ ⊢V⦂ A}
          → (M' : Γ' ⊢C⦂ A ‼ uₑ)
          → return V ≐ᶜ castᶜ e M'
          → Σ[ V' ∈ (Γ' ⊢V⦂ A) ] (M' ≡ return V') × (V ≐ᵛ castᵛ e V')
≐-return⁻ refl _ (return-≐ eV) = _ , refl , eV

≐-app⁻ : ∀ {Γ Γ' A C} → (e : Γ' ≡ Γ) → {V : Γ ⊢V⦂ A ⇒ C} → {W : Γ ⊢V⦂ A}
       → (M' : Γ' ⊢C⦂ C)
       → (V · W) ≐ᶜ castᶜ e M'
       → Σ[ V' ∈ (Γ' ⊢V⦂ A ⇒ C) ] Σ[ W' ∈ (Γ' ⊢V⦂ A) ]
           (M' ≡ V' · W') × (V ≐ᵛ castᵛ e V') × (W ≐ᵛ castᵛ e W')
≐-app⁻ refl _ (app-≐ eV eW) = _ , _ , refl , eV , eW

≐-seq⁻ : ∀ {Γ Γ' A B ε ε'} → (e : Γ' ≡ Γ)
       → {M : Γ ⊢C⦂ A ‼ ε} → {N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
       → (P' : Γ' ⊢C⦂ B ‼ (ε ·ₑ ε'))
       → (M ⨟ N) ≐ᶜ castᶜ e P'
       → Σ[ M' ∈ (Γ' ⊢C⦂ A ‼ ε) ] Σ[ N' ∈ (Γ' ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε') ]
           (P' ≡ (M' ⨟ N')) × (M ≐ᶜ castᶜ e M')
         × (N ≐ᶜ castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) e) N')
≐-seq⁻ refl _ (seq-≐ eM eN) = _ , _ , refl , eM , eN

≐-match⁻ : ∀ {Γ Γ' A B C} → (e : Γ' ≡ Γ)
         → {V : Γ ⊢V⦂ A |×| B} → {M : Γ ∷ A ∷ B ⊢C⦂ C}
         → (P' : Γ' ⊢C⦂ C)
         → (match V `in M) ≐ᶜ castᶜ e P'
         → Σ[ V' ∈ (Γ' ⊢V⦂ A |×| B) ] Σ[ M' ∈ (Γ' ∷ A ∷ B ⊢C⦂ C) ]
             (P' ≡ (match V' `in M')) × (V ≐ᵛ castᵛ e V')
           × (M ≐ᶜ castᶜ (cong (λ Γ₀ → Γ₀ ∷ A ∷ B) e) M')
≐-match⁻ refl _ (match-≐ eV eM) = _ , _ , refl , eV , eM

≐-perform⁻ : ∀ {Γ Γ' A ε} → (e : Γ' ≡ Γ) → {op : Op}
           → {V : Γ ⊢V⦂ type-of-gtype (param op)}
           → {M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
           → (P' : Γ' ⊢C⦂ A ‼ (op-grade op ·ₑ ε))
           → perform op V M ≐ᶜ castᶜ e P'
           → Σ[ V' ∈ (Γ' ⊢V⦂ type-of-gtype (param op)) ]
             Σ[ M' ∈ (Γ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                        ⊢C⦂ A ‼ ε) ]
               (P' ≡ perform op V' M') × (V ≐ᵛ castᵛ e V')
             × (M ≐ᶜ castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                            ∷ type-of-gtype (arity op)) e) M')
≐-perform⁻ refl _ (perform-≐ eV eM) = _ , _ , refl , eV , eM

≐-delay⁻ : ∀ {Γ Γ' A ε τ} → (e : Γ' ≡ Γ)
         → {M : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε}
         → (P' : Γ' ⊢C⦂ A ‼ (of-natᵉ τ ·ₑ ε))
         → delay τ M ≐ᶜ castᶜ e P'
         → Σ[ M' ∈ (Γ' ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε) ]
             (P' ≡ delay τ M')
           × (M ≐ᶜ castᶜ (cong (_⟨ of-natʳ τ ⟩) e) M')
≐-delay⁻ refl _ (delay-≐ eM) = _ , refl , eM

≐-box⁻ : ∀ {Γ Γ' A C ρ} → (e : Γ' ≡ Γ)
       → {V : Γ ⟨ ρ ⟩ ⊢V⦂ A} → {M : Γ ∷ [ ρ ] A ⊢C⦂ C}
       → (P' : Γ' ⊢C⦂ C)
       → box V M ≐ᶜ castᶜ e P'
       → Σ[ V' ∈ (Γ' ⟨ ρ ⟩ ⊢V⦂ A) ] Σ[ M' ∈ (Γ' ∷ [ ρ ] A ⊢C⦂ C) ]
           (P' ≡ box V' M') × (V ≐ᵛ castᵛ (cong (_⟨ ρ ⟩) e) V')
         × (M ≐ᶜ castᶜ (cong (_∷ [ ρ ] A) e) M')
≐-box⁻ refl _ (box-≐ eV eM) = _ , _ , refl , eV , eM

≐-coerce⁻ : ∀ {Γ Γ' A ε ε'} → (e : Γ' ≡ Γ) → {p : ε ≾ₑ ε'}
          → {M : Γ ⊢C⦂ A ‼ ε}
          → (P' : Γ' ⊢C⦂ A ‼ ε')
          → coerce p M ≐ᶜ castᶜ e P'
          → Σ[ p' ∈ (ε ≾ₑ ε') ] Σ[ M' ∈ (Γ' ⊢C⦂ A ‼ ε) ]
              (P' ≡ coerce p' M') × (M ≐ᶜ castᶜ e M')
≐-coerce⁻ refl _ (coerce-≐ eM) = _ , _ , refl , eM

≐-handle⁻ : ∀ {Γ Γ' A B ε ε'} → (e : Γ' ≡ Γ)
          → {M : Γ ⊢C⦂ A ‼ ε}
          → {H : (op : Op) → (ε'' : E) →
                   Γ ᴱ ∷ type-of-gtype (param op)
                     ∷ [ mapᵉ (op-grade op) ]
                         (type-of-gtype (arity op) ⇒ B ‼ ε'')
                   ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
          → {N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
          → (P' : Γ' ⊢C⦂ B ‼ (ε ·ₑ ε'))
          → (handle M `with H `in N) ≐ᶜ castᶜ e P'
          → Σ[ M' ∈ (Γ' ⊢C⦂ A ‼ ε) ]
            Σ[ H' ∈ ((op : Op) → (ε'' : E) →
                       Γ' ᴱ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε'')
                       ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')) ]
            Σ[ N' ∈ (Γ' ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε') ]
              (P' ≡ (handle M' `with H' `in N'))
            × (M ≐ᶜ castᶜ e M')
            × (∀ op ε'' → H op ε''
                 ≐ᶜ castᶜ (cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                                          ∷ [ mapᵉ (op-grade op) ]
                                              (type-of-gtype (arity op) ⇒ B ‼ ε''))
                                e)
                          (H' op ε''))
            × (N ≐ᶜ castᶜ (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) e) N')
≐-handle⁻ refl _ (handle-≐ eM eH eN) = _ , _ , _ , refl , eM , eH , eN

≐-unbox⁻ : ∀ {Γ Γ' A C ρ Δ} → (e : Γ' ≡ Γ)
         → {w : Ren [] (Δ ⟨ ρ ⟩) Γ} → {V : Δ ⊢V⦂ [ ρ ] A} → {M : Γ ∷ A ⊢C⦂ C}
         → (P' : Γ' ⊢C⦂ C)
         → unbox w V M ≐ᶜ castᶜ e P'
         → Σ[ Δ' ∈ Ctx ] Σ[ w' ∈ Ren [] (Δ' ⟨ ρ ⟩) Γ' ] Σ[ V' ∈ (Δ' ⊢V⦂ [ ρ ] A) ]
           Σ[ M' ∈ (Γ' ∷ A ⊢C⦂ C) ]
             (P' ≡ unbox w' V' M')
           × (unbox-tgt w V ≡ unbox-tgt (castʳ e w') V')
           × (M ≐ᶜ castᶜ (cong (_∷ A) e) M')
≐-unbox⁻ refl _ (unbox-≐ hw eM) = _ , _ , _ , _ , refl , hw , eM

------------------------------------------------------------------------
-- CASTS AND THE REDUCTS
--
-- Having fired the same rule on the right, its reduct must be related to the
-- left one's. The reducts are built by renaming, substitution and retyping,
-- each of which commutes with a cast — one line per rule at `refl`, stated in
-- exactly the shape the corresponding case needs.
------------------------------------------------------------------------

cast-app-reduct : ∀ {Γ Γ' A C} → (e : Γ' ≡ Γ)
         → (M' : Γ' ∷ A ⊢C⦂ C) → (W' : Γ' ⊢V⦂ A)
         → (castᶜ (cong (_∷ A) e) M') [ Hd ↦ castᵛ e W' ]c
         ≡ castᶜ e (M' [ Hd ↦ W' ]c)
cast-app-reduct refl M' W' = refl

cast-match-reduct : ∀ {Γ Γ' A B C} → (e : Γ' ≡ Γ)
           → (M' : Γ' ∷ A ∷ B ⊢C⦂ C) → (V' : Γ' ⊢V⦂ A) → (W' : Γ' ⊢V⦂ B)
           → ((castᶜ (cong (λ Γ₀ → Γ₀ ∷ A ∷ B) e) M')
                [ Hd ↦ V-rename wk-ren (castᵛ e W') ]c) [ Hd ↦ castᵛ e V' ]c
           ≡ castᶜ e ((M' [ Hd ↦ V-rename wk-ren W' ]c) [ Hd ↦ V' ]c)
cast-match-reduct refl M' V' W' = refl

cast-seq-ret : ∀ {Γ Γ' A B ε} → (e : Γ' ≡ Γ)
             → (N' : Γ' ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε) → (V' : Γ' ⊢V⦂ A)
             → (C-rename (cong-∷-ren (⟨⟩-η-ren ∘ʳ eq-ren (cong (_⟨_⟩ Γ) map-uᵉ)))
                 (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ uₑ ⟩ ∷ A) e) N'))
                   [ Hd ↦ castᵛ e V' ]c
             ≡ castᶜ e ((C-rename
                          (cong-∷-ren (⟨⟩-η-ren ∘ʳ eq-ren (cong (_⟨_⟩ Γ') map-uᵉ)))
                          N') [ Hd ↦ V' ]c)
cast-seq-ret refl N' V' = refl

cast-box-val : ∀ {Γ Γ' A ρ} → (e : Γ' ≡ Γ) → (V' : Γ' ⟨ ρ ⟩ ⊢V⦂ A)
             → V-rename (eq-ren (sym ++ᶜ-identityˡ))
                 (castᵛ (cong (_⟨ ρ ⟩) e) V')
             ≡ castᵛ (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩) e)
                 (V-rename (eq-ren (sym ++ᶜ-identityˡ)) V')
cast-box-val refl V' = refl

