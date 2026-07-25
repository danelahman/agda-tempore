------------------------------------------------------------------------
-- States and configurations up to the term equivalence.              --
--                                                                    --
-- Only `BOX` changes what a store *holds*, so two states related by   --
-- `_≐ᶜ_`-related terms differ only in their cells' values. `toCtx`     --
-- does not look at those values, so related states have the same       --
-- context — propositionally, not definitionally, which is why          --
-- `_≐ˢ_` and `toCtx-≐ˢ` are defined mutually (as `𝕊` and `toCtx`       --
-- themselves are) and the cell clause carries a cast.                  --
------------------------------------------------------------------------

open import Data.Product

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.StateEquivalence (Spec : LanguageSpec) where

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

open import OperationalSemantics.Adequacy.RenEquivalence Spec
open import OperationalSemantics.Adequacy.SubEquivalence Spec

-- Retyping along a context equality.

castᵛ : ∀ {Γ Γ' A} → Γ ≡ Γ' → Γ ⊢V⦂ A → Γ' ⊢V⦂ A
castᵛ refl V = V

castᶜ : ∀ {Γ Γ' C} → Γ ≡ Γ' → Γ ⊢C⦂ C → Γ' ⊢C⦂ C
castᶜ refl M = M

castᶜ-≐ : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → {M M' : Γ ⊢C⦂ C}
        → M ≐ᶜ M' → castᶜ e M ≐ᶜ castᶜ e M'
castᶜ-≐ refl eM = eM

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

-- `unbox` stores a renaming, so its inversion transports that too.

castʳ : ∀ {Γ Γ' Δ ρ} → Γ' ≡ Γ → Ren (Δ ⟨ ρ ⟩) Γ' → Ren (Δ ⟨ ρ ⟩) Γ
castʳ refl w = w

≐-unbox⁻ : ∀ {Γ Γ' A C ρ Δ} → (e : Γ' ≡ Γ)
         → {w : Ren (Δ ⟨ ρ ⟩) Γ} → {V : Δ ⊢V⦂ [ ρ ] A} → {M : Γ ∷ A ⊢C⦂ C}
         → (P' : Γ' ⊢C⦂ C)
         → unbox w V M ≐ᶜ castᶜ e P'
         → Σ[ w' ∈ Ren (Δ ⟨ ρ ⟩) Γ' ] Σ[ M' ∈ (Γ' ∷ A ⊢C⦂ C) ]
             (P' ≡ unbox w' V M')
           × (w ≐ʳ castʳ e w')
           × (M ≐ᶜ castᶜ (cong (_∷ A) e) M')
≐-unbox⁻ refl _ (unbox-≐ hw eM) = _ , _ , refl , hw , eM

------------------------------------------------------------------------
-- LEMMAS TO PROVE
------------------------------------------------------------------------

postulate

  -- THE BISIMULATION. Related configurations step alike: the same rule fires
  -- (`_≐ᶜ_` preserves the head constructor, which is why the grade is
  -- unchanged), and the reduct is related because every rule builds it by
  -- renaming, substitution or retyping — all congruences for `_≐_`
  -- (`Adequacy.RenEquivalence`, `Adequacy.SubEquivalence`).
  --
  -- `BOX` is the only rule that relates *states* rather than reusing one, and
  -- `UNBOX` the only one that consults a stored renaming — through
  -- `unbox-lookup`, hence only up to `_≐ʳ_` (`unbox-tgt-≐`).
  --
  -- Each case reads the right-hand term's shape off the relation with the
  -- inversions above, fires the same rule, and relates the reducts. The reducts
  -- need the casts to commute with what builds them (renaming, substitution,
  -- retyping) — as for the inversions, one line each at `refl`.

  ↝-≐ : ∀ {A ε ε₁} {St St' St₁ : 𝕊 []}
      → (es : St ≐ˢ St')
      → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε}
      → M ≐ᶜ castᶜ (sym (toCtx-≐ˢ es)) M'
      → {N : toCtx St₁ ⊢C⦂ A ‼ ε₁}
      → ⟨ St , M ⟩ ↝ ⟨ St₁ , N ⟩
      -------------------------------------------------------------------
      → Σ[ St₁' ∈ 𝕊 [] ] Σ[ N' ∈ (toCtx St₁' ⊢C⦂ A ‼ ε₁) ]
        Σ[ es₁ ∈ St₁ ≐ˢ St₁' ]
          (⟨ St' , M' ⟩ ↝ ⟨ St₁' , N' ⟩)
        × (N ≐ᶜ castᶜ (sym (toCtx-≐ˢ es₁)) N')

------------------------------------------------------------------------
-- RUNS
------------------------------------------------------------------------

-- The bisimulation extends to runs, step by step.

↝*-≐ : ∀ {A ε ε₁} {St St' St₁ : 𝕊 []}
     → (es : St ≐ˢ St')
     → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε}
     → M ≐ᶜ castᶜ (sym (toCtx-≐ˢ es)) M'
     → {N : toCtx St₁ ⊢C⦂ A ‼ ε₁}
     → ⟨ St , M ⟩ ↝* ⟨ St₁ , N ⟩
     -------------------------------------------------------------------
     → Σ[ St₁' ∈ 𝕊 [] ] Σ[ N' ∈ (toCtx St₁' ⊢C⦂ A ‼ ε₁) ]
       Σ[ es₁ ∈ St₁ ≐ˢ St₁' ]
         (⟨ St' , M' ⟩ ↝* ⟨ St₁' , N' ⟩)
       × (N ≐ᶜ castᶜ (sym (toCtx-≐ˢ es₁)) N')

↝*-≐ {St' = St'} es {M' = M'} eM ε* = St' , M' , es , ε* , eM
↝*-≐ es eM (r ◅ rs) with ↝-≐ es eM r
... | St₂' , N₂' , es₂ , r' , eN₂ with ↝*-≐ es₂ eN₂ rs
...   | St₁' , N' , es₁ , rs' , eN = St₁' , N' , es₁ , r' ◅ rs' , eN
