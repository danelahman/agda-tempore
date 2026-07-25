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

-- Casts are irrelevant in their equality proof, so the two ways of building the
-- reduct's context equality (`sym (cong f e)` and `cong f (sym e)`) agree.

castᵛ-irr : ∀ {Γ Γ' A} → (e e' : Γ ≡ Γ') → (V : Γ ⊢V⦂ A)
          → castᵛ e V ≡ castᵛ e' V
castᵛ-irr e e' V = cong (λ z → castᵛ z V) uip

castᶜ-irr : ∀ {Γ Γ' C} → (e e' : Γ ≡ Γ') → (M : Γ ⊢C⦂ C)
          → castᶜ e M ≡ castᶜ e' M
castᶜ-irr e e' M = cong (λ z → castᶜ z M) uip

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

≐-handle⁻ : ∀ {Γ Γ' A B ε ε'} → (e : Γ' ≡ Γ)
          → {M : Γ ⊢C⦂ A ‼ ε}
          → {H : (op : Op) → (ε'' : E) → (Γ₀ : Ctx) →
                   Γ ᴱ ++ᶜ Γ₀ ∷ type-of-gtype (param op)
                     ∷ [ mapᵉ (op-grade op) ]
                         (type-of-gtype (arity op) ⇒ B ‼ ε'')
                   ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
          → {N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
          → (P' : Γ' ⊢C⦂ B ‼ (ε ·ₑ ε'))
          → (handle M `with H `in N) ≐ᶜ castᶜ e P'
          → Σ[ M' ∈ (Γ' ⊢C⦂ A ‼ ε) ]
            Σ[ H' ∈ ((op : Op) → (ε'' : E) → (Γ₀ : Ctx) →
                       Γ' ᴱ ++ᶜ Γ₀ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε'')
                       ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')) ]
            Σ[ N' ∈ (Γ' ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε') ]
              (P' ≡ (handle M' `with H' `in N'))
            × (M ≐ᶜ castᶜ e M')
            × (∀ op ε'' Γ₀ → H op ε'' Γ₀
                 ≐ᶜ castᶜ (cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ Γ₀ ∷ type-of-gtype (param op)
                                          ∷ [ mapᵉ (op-grade op) ]
                                              (type-of-gtype (arity op) ⇒ B ‼ ε''))
                                e)
                          (H' op ε'' Γ₀))
            × (N ≐ᶜ castᶜ (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) e) N')
≐-handle⁻ refl _ (handle-≐ eM eH eN) = _ , _ , _ , refl , eM , eH , eN

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
-- CASTS AND THE REDUCTS
--
-- Having fired the same rule on the right, its reduct must be related to the
-- left one's. The reducts are built by renaming, substitution and retyping,
-- each of which commutes with a cast — one line per rule at `refl`, stated in
-- exactly the shape the corresponding case needs.
------------------------------------------------------------------------

cast-app : ∀ {Γ Γ' A C} → (e : Γ' ≡ Γ)
         → (M' : Γ' ∷ A ⊢C⦂ C) → (W' : Γ' ⊢V⦂ A)
         → (castᶜ (cong (_∷ A) e) M') [ Hd ↦ castᵛ e W' ]c
         ≡ castᶜ e (M' [ Hd ↦ W' ]c)
cast-app refl M' W' = refl

cast-match : ∀ {Γ Γ' A B C} → (e : Γ' ≡ Γ)
           → (M' : Γ' ∷ A ∷ B ⊢C⦂ C) → (V' : Γ' ⊢V⦂ A) → (W' : Γ' ⊢V⦂ B)
           → ((castᶜ (cong (λ Γ₀ → Γ₀ ∷ A ∷ B) e) M')
                [ Hd ↦ V-rename wk-ren (castᵛ e W') ]c) [ Hd ↦ castᵛ e V' ]c
           ≡ castᶜ e ((M' [ Hd ↦ V-rename wk-ren W' ]c) [ Hd ↦ V' ]c)
cast-match refl M' V' W' = refl

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

------------------------------------------------------------------------
-- STATE EXTENSIONS OF THE SAME SHAPE
--
-- `SEQ-STEP`/`HANDLE-STEP` rename their continuation along
-- `suc-comp-ren (step-extends-state r) c`, so simulating them needs the two
-- derived renamings to agree. They do, because `suc-comp-ren` reads only the
-- *shape* of the extension — its `∷-suc` clause discards the stored value, and
-- the only data it keeps is a `≾ᵣ` proof, invisible to `_≐ʳ_`.
------------------------------------------------------------------------

data _≤≐_ : ∀ {St St₁ St' St₁' : 𝕊 []} → St ≤ₛ St₁ → St' ≤ₛ St₁' → Set where

  id-≤≐ : ∀ {St St' : 𝕊 []} → id-suc {S = St} ≤≐ id-suc {S = St'}

  ⟨⟩-≤≐ : ∀ {St St₁ St' St₁' : 𝕊 []} {q : St ≤ₛ St₁} {q' : St' ≤ₛ St₁'}
        → (ρ : R) → q ≤≐ q' → (⟨⟩-suc ρ q) ≤≐ (⟨⟩-suc ρ q')

  ∷-≤≐  : ∀ {St St₁ St' St₁' : 𝕊 []} {A ρ} {q : St ≤ₛ St₁} {q' : St' ≤ₛ St₁'}
        → {V  : ([] ++ᶜ toCtx St₁  ⟨ ρ ⟩) ⊢V⦂ A}
        → {V' : ([] ++ᶜ toCtx St₁' ⟨ ρ ⟩) ⊢V⦂ A}
        → q ≤≐ q' → (∷-suc V q) ≤≐ (∷-suc V' q')

≤ₛ-grade-≤≐ : ∀ {St St₁ St' St₁' : 𝕊 []} {q : St ≤ₛ St₁} {q' : St' ≤ₛ St₁'}
            → q ≤≐ q' → ≤ₛ-grade q ≡ ≤ₛ-grade q'
≤ₛ-grade-≤≐ id-≤≐        = refl
≤ₛ-grade-≤≐ (⟨⟩-≤≐ ρ h)  = cong (_·ᵣ ρ) (≤ₛ-grade-≤≐ h)
≤ₛ-grade-≤≐ (∷-≤≐ h)     = ≤ₛ-grade-≤≐ h

-- Transporting a renaming along equalities of both its contexts.

castʳ² : ∀ {Γ₁ Γ₂ Γ₁' Γ₂'} → Γ₁' ≡ Γ₁ → Γ₂' ≡ Γ₂ → Ren Γ₁' Γ₂' → Ren Γ₁ Γ₂
castʳ² refl refl r = r

-- The three renamings `suc-comp-ren` is built from, each compared across a cast.
-- Provable because here the contexts are *variables*, so the equalities can be
-- matched; the lemmas are then applied at `toCtx`-equalities.

castʳ²-∘ʳ : ∀ {Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃'}
          → (e₁ : Γ₁' ≡ Γ₁) → (e₂ : Γ₂' ≡ Γ₂) → (e₃ : Γ₃' ≡ Γ₃)
          → (r₂ : Ren Γ₂' Γ₃') → (r₁ : Ren Γ₁' Γ₂')
          → castʳ² e₁ e₃ (r₂ ∘ʳ r₁) ≐ʳ (castʳ² e₂ e₃ r₂ ∘ʳ castʳ² e₁ e₂ r₁)
castʳ²-∘ʳ refl refl refl r₂ r₁ = ≐ʳ-refl

-- Two casts along (necessarily equal) proofs of the same equation agree.

castʳ²-irr : ∀ {Γ₁ Γ₂ Γ₁' Γ₂'} → (e₁ e₁' : Γ₁' ≡ Γ₁) → (e₂ e₂' : Γ₂' ≡ Γ₂)
           → (r : Ren Γ₁' Γ₂')
           → castʳ² e₁ e₂ r ≐ʳ castʳ² e₁' e₂' r
castʳ²-irr e₁ e₁' e₂ e₂' r
  rewrite uip {p = e₁} {q = e₁'} | uip {p = e₂} {q = e₂'} = ≐ʳ-refl

⟨⟩-≤-ren-cast : ∀ {Γ Γ' ρ ρ'} → (e : Γ' ≡ Γ) → (p p' : ρ' ≾ᵣ ρ)
              → ⟨⟩-≤-ren {Γ = Γ} p
              ≐ʳ castʳ² (cong (_⟨ ρ ⟩) e) (cong (_⟨ ρ' ⟩) e) (⟨⟩-≤-ren p')
⟨⟩-≤-ren-cast refl p p' = ⟨⟩-≤-ren-≐ p p'

⟨⟩-μ-ren-cast : ∀ {Γ Γ' ρ ρ'} → (e : Γ' ≡ Γ)
              → ⟨⟩-μ-ren {Γ = Γ} {ρ = ρ} {ρ' = ρ'}
              ≐ʳ castʳ² (cong (_⟨ ρ ·ᵣ ρ' ⟩) e) (cong (λ Γ₀ → Γ₀ ⟨ ρ ⟩ ⟨ ρ' ⟩) e)
                        ⟨⟩-μ-ren
⟨⟩-μ-ren-cast refl = ≐ʳ-refl

cong-⟨⟩-wk-cast : ∀ {Γ Γ' A ρ} → (e : Γ' ≡ Γ)
                → cong-⟨⟩-ren {Γ = Γ} {ρ = ρ} (wk-ren {A = A})
                ≐ʳ castʳ² (cong (_⟨ ρ ⟩) e) (cong (λ Γ₀ → (Γ₀ ∷ A) ⟨ ρ ⟩) e)
                          (cong-⟨⟩-ren wk-ren)
cong-⟨⟩-wk-cast refl = ≐ʳ-refl

-- Extensions of the same shape induce `_≐ʳ_`-equal renamings.

suc-comp-ren-≐ : ∀ {St St₁ St' St₁' : 𝕊 []} {ρ'' ρ''' : R}
               → {q : St ≤ₛ St₁} → {q' : St' ≤ₛ St₁'}
               → (h : q ≤≐ q')
               → (es : St ≐ˢ St') → (es₁ : St₁ ≐ˢ St₁')
               → (c  : ≤ₛ-grade q  ·ᵣ ρ''' ≾ᵣ ρ'')
               → (c' : ≤ₛ-grade q' ·ᵣ ρ''' ≾ᵣ ρ'')
               → suc-comp-ren q c
               ≐ʳ castʳ² (cong (_⟨ ρ'' ⟩)  (sym (toCtx-≐ˢ es)))
                         (cong (_⟨ ρ''' ⟩) (sym (toCtx-≐ˢ es₁)))
                         (suc-comp-ren q' c')

suc-comp-ren-≐ id-≤≐ es es₁ c c' =
  ≐ʳ-trans (⟨⟩-≤-ren-cast (sym (toCtx-≐ˢ es)) _ _)
           (castʳ²-irr _ _ _ _ (⟨⟩-≤-ren _))

suc-comp-ren-≐ {ρ'' = ρ''} {ρ''' = ρ'''} (⟨⟩-≤≐ {q' = q'} ρ h) es
               (⟨⟩-≐ˢ .ρ es₁) c c' =
  ≐ʳ-trans (∘ʳ-≐ (⟨⟩-μ-ren-cast {ρ = ρ} {ρ' = ρ'''} (sym (toCtx-≐ˢ es₁)))
                 (suc-comp-ren-≐ {ρ'' = ρ''} {ρ''' = ρ ·ᵣ ρ'''} h es es₁ _ _))
    (≐ʳ-trans
      (≐ʳ-sym (castʳ²-∘ʳ (cong (_⟨ ρ'' ⟩) (sym (toCtx-≐ˢ es)))
                         (cong (_⟨ ρ ·ᵣ ρ''' ⟩) (sym (toCtx-≐ˢ es₁)))
                         (cong (λ Γ₀ → (Γ₀ ⟨ ρ ⟩) ⟨ ρ''' ⟩) (sym (toCtx-≐ˢ es₁)))
                         ⟨⟩-μ-ren (suc-comp-ren _ _)))
      (castʳ²-irr (cong (_⟨ ρ'' ⟩) (sym (toCtx-≐ˢ es)))
                  (cong (_⟨ ρ'' ⟩) (sym (toCtx-≐ˢ es)))
                  (cong (λ Γ₀ → (Γ₀ ⟨ ρ ⟩) ⟨ ρ''' ⟩) (sym (toCtx-≐ˢ es₁)))
                  (cong (_⟨ ρ''' ⟩) (sym (toCtx-≐ˢ (⟨⟩-≐ˢ ρ es₁))))
                  (suc-comp-ren (⟨⟩-suc ρ q') c')))

suc-comp-ren-≐ {ρ'' = ρ''} {ρ''' = ρ'''}
               (∷-≤≐ {A = A} {ρ = ρ} {q' = q'} {V' = V'} h) es
               (∷-≐ˢ es₁ eV) c c' =
  ≐ʳ-trans (∘ʳ-≐ (cong-⟨⟩-wk-cast {A = [ ρ ] A} {ρ = ρ'''}
                   (sym (toCtx-≐ˢ es₁)))
                 (suc-comp-ren-≐ {ρ'' = ρ''} {ρ''' = ρ'''} h es es₁ _ _))
    (≐ʳ-trans
      (≐ʳ-sym (castʳ²-∘ʳ (cong (_⟨ ρ'' ⟩) (sym (toCtx-≐ˢ es)))
                         (cong (_⟨ ρ''' ⟩) (sym (toCtx-≐ˢ es₁)))
                         (cong (λ Γ₀ → (Γ₀ ∷ [ ρ ] A) ⟨ ρ''' ⟩)
                               (sym (toCtx-≐ˢ es₁)))
                         (cong-⟨⟩-ren wk-ren) (suc-comp-ren _ _)))
      (castʳ²-irr (cong (_⟨ ρ'' ⟩) (sym (toCtx-≐ˢ es)))
                  (cong (_⟨ ρ'' ⟩) (sym (toCtx-≐ˢ es)))
                  (cong (λ Γ₀ → (Γ₀ ∷ [ ρ ] A) ⟨ ρ''' ⟩) (sym (toCtx-≐ˢ es₁)))
                  (cong (_⟨ ρ''' ⟩) (sym (toCtx-≐ˢ (∷-≐ˢ es₁ eV))))
                  (suc-comp-ren (∷-suc V' q') c')))

------------------------------------------------------------------------
-- LEMMA TO PROVE
------------------------------------------------------------------------

postulate

  -- `UNBOX` reads the store; related states hold related values, and the
  -- renaming it consults is seen only up to `_≐ʳ_` (`unbox-tgt-≐`).

  unbox-lookup-≐ : ∀ {A ρ Δ} {St St' : 𝕊 []}
                 → (es : St ≐ˢ St')
                 → {w : Ren (Δ ⟨ ρ ⟩) (toCtx St)} → {w' : Ren (Δ ⟨ ρ ⟩) (toCtx St')}
                 → w ≐ʳ castʳ (sym (toCtx-≐ˢ es)) w'
                 → (V : Δ ⊢V⦂ [ ρ ] A)
                 -------------------------------------------------------
                 → unbox-lookup St w V
                 ≐ᵛ castᵛ (sym (toCtx-≐ˢ es)) (unbox-lookup St' w' V)

------------------------------------------------------------------------
-- THE BISIMULATION, RULE BY RULE
--
-- `Sim es M' r` is what simulating `r` from the related configuration amounts
-- to: a state, a reduct, their relations, the step, and the fact that the two
-- steps extend the state alike. Each rule gets its own lemma, so the assembly
-- below is one line per rule.
------------------------------------------------------------------------

Sim : ∀ {A ε ε₁} {St St' St₁ : 𝕊 []}
    → (es : St ≐ˢ St') → {M : toCtx St ⊢C⦂ A ‼ ε} → (M' : toCtx St' ⊢C⦂ A ‼ ε)
    → {N : toCtx St₁ ⊢C⦂ A ‼ ε₁} → (r : ⟨ St , M ⟩ ↝ ⟨ St₁ , N ⟩) → Set
Sim {A} {ε₁ = ε₁} {St' = St'} {St₁ = St₁} es M' {N} r =
  Σ[ St₁' ∈ 𝕊 [] ] Σ[ N' ∈ (toCtx St₁' ⊢C⦂ A ‼ ε₁) ] Σ[ es₁ ∈ St₁ ≐ˢ St₁' ]
  Σ[ r' ∈ (⟨ St' , M' ⟩ ↝ ⟨ St₁' , N' ⟩) ]
    (step-extends-state r ≤≐ step-extends-state r')
  × (N ≐ᶜ castᶜ (sym (toCtx-≐ˢ es₁)) N')

-- `coerce` is peeled off on both sides.

↝-≐-coerce : ∀ {A ε ε'} {St St' : 𝕊 []} → (es : St ≐ˢ St')
           → {p : ε ≾ₑ ε'} → {M : toCtx St ⊢C⦂ A ‼ ε}
           → (P' : toCtx St' ⊢C⦂ A ‼ ε')
           → coerce p M ≐ᶜ castᶜ (sym (toCtx-≐ˢ es)) P'
           → Sim es P' (COERCE {M = M} {ε≾ε' = p})
↝-≐-coerce es P' eM with ≐-coerce⁻ (sym (toCtx-≐ˢ es)) P' eM
... | p' , M₀' , refl , eM₀ = _ , _ , es , COERCE , id-≤≐ , eM₀

-- application: the function is a lambda on both sides, and the reducts are the
-- same substitution (`sub-≐ᶜ`), the cast commuting with it (`cast-app`).

↝-≐-app : ∀ {A B ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
        → {M₀ : toCtx St ∷ A ⊢C⦂ B ‼ ε} → {V : toCtx St ⊢V⦂ A}
        → (P' : toCtx St' ⊢C⦂ B ‼ ε)
        → (lam M₀ · V) ≐ᶜ castᶜ (sym (toCtx-≐ˢ es)) P'
        → Sim es P' (APP {M = M₀} {V = V})
↝-≐-app es P' eM with ≐-app⁻ (sym (toCtx-≐ˢ es)) P' eM
... | Vf' , W' , refl , eVf , eW with ≐-lam⁻ (sym (toCtx-≐ˢ es)) Vf' eVf
...   | M₀' , refl , eM₀ =
    _ , _ , es , APP , id-≤≐
  , subst (λ z → _ ≐ᶜ z) (cast-app (sym (toCtx-≐ˢ es)) M₀' W')
          (sub-≐ᶜ Hd eW eM₀)

-- a delay moves the lock into the state, so the two states are related by
-- `⟨⟩-≐ˢ` and the extensions by `⟨⟩-≤≐`

↝-≐-delay : ∀ {A ε τ} {St St' : 𝕊 []} → (es : St ≐ˢ St')
          → {M₀ : toCtx St ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε}
          → (P' : toCtx St' ⊢C⦂ A ‼ (of-natᵉ τ ·ₑ ε))
          → delay τ M₀ ≐ᶜ castᶜ (sym (toCtx-≐ˢ es)) P'
          → Sim es P' (DELAY {M = M₀})
↝-≐-delay {τ = τ} es P' eM with ≐-delay⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M₀' , refl , eM₀ =
    _ , _ , ⟨⟩-≐ˢ (of-natʳ τ) es , DELAY , ⟨⟩-≤≐ (of-natʳ τ) id-≤≐
  , subst (λ z → _ ≐ᶜ z) (castᶜ-irr _ _ M₀') eM₀

-- `box` allocates: the two states are related by `∷-≐ˢ` at the stored values
-- (`cast-box-val` moves the cast past the reindexing `_∷ₛ_` applies).

↝-≐-box : ∀ {A B ρ ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
        → {V : toCtx St ⟨ ρ ⟩ ⊢V⦂ A} → {M₀ : toCtx St ∷ [ ρ ] A ⊢C⦂ B ‼ ε}
        → (P' : toCtx St' ⊢C⦂ B ‼ ε)
        → box V M₀ ≐ᶜ castᶜ (sym (toCtx-≐ˢ es)) P'
        → Sim es P' (BOX {V = V} {M = M₀})
↝-≐-box es P' eM with ≐-box⁻ (sym (toCtx-≐ˢ es)) P' eM
... | V' , M₀' , refl , eV , eM₀ =
    _ , _
  , ∷-≐ˢ es (subst (λ z → _ ≐ᵛ z)
                   (cast-box-val (sym (toCtx-≐ˢ es)) V')
                   (V-rename-cong (eq-ren (sym ++ᶜ-identityˡ)) eV))
  , BOX , ∷-≤≐ id-≤≐
  , subst (λ z → _ ≐ᶜ z) (castᶜ-irr _ _ M₀') eM₀

-- matching: the scrutinee is a pair on both sides, and the reduct is the same
-- pair of nested substitutions.

↝-≐-match : ∀ {A B D ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
          → {V : toCtx St ⊢V⦂ A} → {W : toCtx St ⊢V⦂ B}
          → {M₀ : toCtx St ∷ A ∷ B ⊢C⦂ D ‼ ε}
          → (P' : toCtx St' ⊢C⦂ D ‼ ε)
          → (match ⦉ V , W ⦊ `in M₀) ≐ᶜ castᶜ (sym (toCtx-≐ˢ es)) P'
          → Sim es P' (MATCH {V = V} {W = W} {M = M₀})
↝-≐-match es P' eM with ≐-match⁻ (sym (toCtx-≐ˢ es)) P' eM
... | U' , M₀' , refl , eU , eM₀ with ≐-pair⁻ (sym (toCtx-≐ˢ es)) U' eU
...   | V' , W' , refl , eV , eW =
    _ , _ , es , MATCH , id-≤≐
  , subst (λ z → _ ≐ᶜ z) (cast-match (sym (toCtx-≐ˢ es)) M₀' V' W')
      (sub-≐ᶜ Hd eV
        (sub-≐ᶜ Hd (V-rename-cong wk-ren eW) eM₀))

-- sequencing a returned value: the continuation is retyped by a renaming that
-- mentions the context, so `cast-seq-ret` is what moves the cast past it.

↝-≐-seq-ret : ∀ {A B ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
            → {V : toCtx St ⊢V⦂ A} → {N : toCtx St ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε}
            → (P' : toCtx St' ⊢C⦂ B ‼ (uₑ ·ₑ ε))
            → (return V ⨟ N) ≐ᶜ castᶜ (sym (toCtx-≐ˢ es)) P'
            → Sim es P' (SEQ-RET {V = V} {N = N})
↝-≐-seq-ret es P' eM with ≐-seq⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M₁' , N' , refl , eM₁ , eN with ≐-return⁻ (sym (toCtx-≐ˢ es)) M₁' eM₁
...   | V' , refl , eV =
    _ , _ , es , SEQ-RET , id-≤≐
  , subst (λ z → _ ≐ᶜ z) (cast-seq-ret (sym (toCtx-≐ˢ es)) N' V')
      (sub-≐ᶜ Hd eV (C-rename-cong (cong-∷-ren _) eN))

-- handling a returned value: as `SEQ-RET`, with the handler discarded.

↝-≐-handle-ret : ∀ {A B ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
               → {V : toCtx St ⊢V⦂ A}
               → {H : (op : Op) → (ε' : E) → (Γ' : Ctx) →
                        toCtx St ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                          ∷ [ mapᵉ (op-grade op) ]
                              (type-of-gtype (arity op) ⇒ B ‼ ε')
                        ⊢C⦂ B ‼ (op-grade op ·ₑ ε')}
               → {N : toCtx St ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε}
               → (P' : toCtx St' ⊢C⦂ B ‼ (uₑ ·ₑ ε))
               → (handle return V `with H `in N) ≐ᶜ castᶜ (sym (toCtx-≐ˢ es)) P'
               → Sim es P' (HANDLE-RET {V = V} {H = H} {N = N})
↝-≐-handle-ret es P' eM with ≐-handle⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M₁' , H' , N' , refl , eM₁ , eH , eN
  with ≐-return⁻ (sym (toCtx-≐ˢ es)) M₁' eM₁
...   | V' , refl , eV =
    _ , _ , es , HANDLE-RET , id-≤≐
  , subst (λ z → _ ≐ᶜ z) (cast-seq-ret (sym (toCtx-≐ˢ es)) N' V')
      (sub-≐ᶜ Hd eV (C-rename-cong (cong-∷-ren _) eN))

-- unboxing: the store is read at the same cell, so the substituted values are
-- related (`unbox-lookup-≐`).

↝-≐-unbox : ∀ {A D ε ρ Δ} {St St' : 𝕊 []} → (es : St ≐ˢ St')
          → {w : Ren (Δ ⟨ ρ ⟩) (toCtx St)} → {V : Δ ⊢V⦂ [ ρ ] A}
          → {M₀ : toCtx St ∷ A ⊢C⦂ D ‼ ε}
          → (P' : toCtx St' ⊢C⦂ D ‼ ε)
          → unbox w V M₀ ≐ᶜ castᶜ (sym (toCtx-≐ˢ es)) P'
          → Sim es P' (UNBOX {w = w} {V = V} {M = M₀})
↝-≐-unbox {St = St} {St' = St'} es {V = V} P' eM
  with ≐-unbox⁻ (sym (toCtx-≐ˢ es)) P' eM
... | w' , M₀' , refl , hw , eM₀ =
    _ , _ , es , UNBOX , id-≤≐
  , subst (λ z → _ ≐ᶜ z)
      (cast-app (sym (toCtx-≐ˢ es)) M₀' (unbox-lookup St' w' V))
      (sub-≐ᶜ Hd (unbox-lookup-≐ es hw V) eM₀)

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

  -- The simulated step's *extension* has the same shape as the original's
  -- (`_≤≐_`): `SEQ-STEP`/`HANDLE-STEP` rename their continuation along it, so
  -- the recursion has to hand that back (`suc-comp-ren-≐`).

  ↝-≐ : ∀ {A ε ε₁} {St St' St₁ : 𝕊 []}
      → (es : St ≐ˢ St')
      → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε}
      → M ≐ᶜ castᶜ (sym (toCtx-≐ˢ es)) M'
      → {N : toCtx St₁ ⊢C⦂ A ‼ ε₁}
      → (r : ⟨ St , M ⟩ ↝ ⟨ St₁ , N ⟩)
      -------------------------------------------------------------------
      → Σ[ St₁' ∈ 𝕊 [] ] Σ[ N' ∈ (toCtx St₁' ⊢C⦂ A ‼ ε₁) ]
        Σ[ es₁ ∈ St₁ ≐ˢ St₁' ]
        Σ[ r' ∈ (⟨ St' , M' ⟩ ↝ ⟨ St₁' , N' ⟩) ]
          (step-extends-state r ≤≐ step-extends-state r')
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
... | St₂' , N₂' , es₂ , r' , _ , eN₂ with ↝*-≐ es₂ eN₂ rs
...   | St₁' , N' , es₁ , rs' , eN = St₁' , N' , es₁ , r' ◅ rs' , eN
