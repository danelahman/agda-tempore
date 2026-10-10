------------------------------------------------------------------------
-- States up to the term equivalence, and inverting a cast.
------------------------------------------------------------------------

open import Data.Empty
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
       → box V M ≡ castᶜ e P'
       → Σ[ V' ∈ (Γ' ⟨ ρ ⟩ ⊢V⦂ A) ] Σ[ M' ∈ (Γ' ∷ [ ρ ] A ⊢C⦂ C) ]
           (P' ≡ box V' M') × (V ≡ castᵛ (cong (_⟨ ρ ⟩) e) V')
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

cast-match-reduct : ∀ {Γ Γ' A B C} → (e : Γ' ≡ Γ)
           → (M' : Γ' ∷ A ∷ B ⊢C⦂ C) → (V' : Γ' ⊢V⦂ A) → (W' : Γ' ⊢V⦂ B)
           → ((castᶜ (cong (λ Γ₀ → Γ₀ ∷ A ∷ B) e) M')
                [ split-[] ↦ V-rename wk-ren (castᵛ e W') ]c) [ split-[] ↦ castᵛ e V' ]c
           ≡ castᶜ e ((M' [ split-[] ↦ V-rename wk-ren W' ]c) [ split-[] ↦ V' ]c)
cast-match-reduct refl M' V' W' = refl

cast-seq-ret : ∀ {Γ Γ' A B ε} → (e : Γ' ≡ Γ)
             → (N' : Γ' ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε) → (V' : Γ' ⊢V⦂ A)
             → (C-rename (cong-∷-ren (eq-ren (cong (_⟨_⟩ Γ) map-uᵉ) ∘ʳ ⟨⟩-η-ren))
                 (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ uₑ ⟩ ∷ A) e) N'))
                   [ split-[] ↦ castᵛ e V' ]c
             ≡ castᶜ e ((C-rename
                          (cong-∷-ren (eq-ren (cong (_⟨_⟩ Γ') map-uᵉ) ∘ʳ ⟨⟩-η-ren))
                          N') [ split-[] ↦ V' ]c)
cast-seq-ret refl N' V' = refl

cast-box-val : ∀ {Γ Γ' A ρ} → (e : Γ' ≡ Γ) → (V' : Γ' ⟨ ρ ⟩ ⊢V⦂ A)
             → V-rename (eq-ren (sym ++ᶜ-identityˡ))
                 (castᵛ (cong (_⟨ ρ ⟩) e) V')
             ≡ castᵛ (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩) e)
                 (V-rename (eq-ren (sym ++ᶜ-identityˡ)) V')
cast-box-val refl V' = refl

