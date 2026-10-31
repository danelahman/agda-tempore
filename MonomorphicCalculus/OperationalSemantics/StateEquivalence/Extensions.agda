------------------------------------------------------------------------
-- State extensions of the same shape, and reading the store.
------------------------------------------------------------------------

open import Data.Product

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Relation.Nullary using (¬_)

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.StateEquivalence.Extensions (Spec : LanguageSpec) where
open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           Spec
open import MonomorphicCalculus.OperationalSemantics.State               Spec

open import MonomorphicCalculus.Syntax.Contexts        Spec
open import MonomorphicCalculus.Syntax.Terms           Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming        Spec
open import MonomorphicCalculus.Syntax.Substitution    Spec
open import MonomorphicCalculus.Syntax.Types           Spec

open import MonomorphicCalculus.Syntax.Renaming.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Renaming.Coherence    Spec
open import MonomorphicCalculus.Syntax.Terms.Equivalence     Spec
open import MonomorphicCalculus.Syntax.Terms.Transport       Spec
open import MonomorphicCalculus.Syntax.Substitution.Variables  Spec
open import MonomorphicCalculus.OperationalSemantics.GradedReach Spec
open import MonomorphicCalculus.Syntax.Substitution.Equivalence  Spec

open import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Core Spec

-- `SEQ-STEP`/`HANDLE-STEP` rename their continuation along
-- `suc-comp-ren (step-extends-state r) c`; simulating them needs the two
-- derived renamings to agree.

data _≤≐_ : ∀ {𝕊 𝕊₁ 𝕊' 𝕊₁' : State []} → 𝕊 ≤ₛ 𝕊₁ → 𝕊' ≤ₛ 𝕊₁' → Set where

  id-≤≐ : ∀ {𝕊 𝕊' : State []} → ≤ₛ-refl {𝕊 = 𝕊} ≤≐ ≤ₛ-refl {𝕊 = 𝕊'}

  ⟨⟩-≤≐ : ∀ {𝕊 𝕊₁ 𝕊' 𝕊₁' : State []} {q : 𝕊 ≤ₛ 𝕊₁} {q' : 𝕊' ≤ₛ 𝕊₁'}
        → (ρ : R) → q ≤≐ q' → (≤ₛ-lock {ρ = ρ} q) ≤≐ (≤ₛ-lock {ρ = ρ} q')

  ∷-≤≐  : ∀ {𝕊 𝕊₁ 𝕊' 𝕊₁' : State []} {A ρ} {q : 𝕊 ≤ₛ 𝕊₁} {q' : 𝕊' ≤ₛ 𝕊₁'}
        → {V  : ([] ++ᶜ toCtx 𝕊₁  ⟨ ρ ⟩) ⊢V⦂ A}
        → {V' : ([] ++ᶜ toCtx 𝕊₁' ⟨ ρ ⟩) ⊢V⦂ A}
        → q ≤≐ q' → (≤ₛ-res {V = V} q) ≤≐ (≤ₛ-res {V = V'} q')

≤≐-sym : ∀ {𝕊 𝕊₁ 𝕊' 𝕊₁' : State []} {q : 𝕊 ≤ₛ 𝕊₁} {q' : 𝕊' ≤ₛ 𝕊₁'}
       → q ≤≐ q' → q' ≤≐ q
≤≐-sym id-≤≐       = id-≤≐
≤≐-sym (⟨⟩-≤≐ ρ h) = ⟨⟩-≤≐ ρ (≤≐-sym h)
≤≐-sym (∷-≤≐ h)    = ∷-≤≐ (≤≐-sym h)

κₛ-≤≐ : ∀ {𝕊 𝕊₁ 𝕊' 𝕊₁' : State []} {q : 𝕊 ≤ₛ 𝕊₁} {q' : 𝕊' ≤ₛ 𝕊₁'}
      → q ≤≐ q' → κₛ q ≡ κₛ q'
κₛ-≤≐ id-≤≐        = refl
κₛ-≤≐ (⟨⟩-≤≐ ρ h)  = cong (_·ᵣ ρ) (κₛ-≤≐ h)
κₛ-≤≐ (∷-≤≐ h)     = κₛ-≤≐ h

-- Transporting a renaming along equalities of both its contexts.

castʳ² : ∀ {Γ₁ Γ₂ Γ₁' Γ₂'} → Γ₁' ≡ Γ₁ → Γ₂' ≡ Γ₂ → Ren [] Γ₂' Γ₁' → Ren [] Γ₂ Γ₁
castʳ² refl refl r = r

-- The three renamings `suc-comp-ren` is built from, each compared across a cast.
-- Provable because the contexts are variables, so the equalities can be
-- matched; the lemmas are then applied at `toCtx`-equalities.

castʳ²-∘ʳ : ∀ {Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃'}
          → (e₁ : Γ₁' ≡ Γ₁) → (e₂ : Γ₂' ≡ Γ₂) → (e₃ : Γ₃' ≡ Γ₃)
          → (r₂ : Ren [] Γ₂' Γ₃') → (r₁ : Ren [] Γ₁' Γ₂')
          → castʳ² e₃ e₁ (r₂ ∘ʳ r₁) ≐ʳ (castʳ² e₃ e₂ r₂ ∘ʳ castʳ² e₂ e₁ r₁)
castʳ²-∘ʳ refl refl refl r₂ r₁ = ≐ʳ-refl

-- Two casts along (necessarily equal) proofs of the same equation agree.

castʳ²-irr : ∀ {Γ₁ Γ₂ Γ₁' Γ₂'} → (e₁ e₁' : Γ₁' ≡ Γ₁) → (e₂ e₂' : Γ₂' ≡ Γ₂)
           → (r : Ren [] Γ₂' Γ₁')
           → castʳ² e₁ e₂ r ≐ʳ castʳ² e₁' e₂' r
castʳ²-irr e₁ e₁' e₂ e₂' r
  rewrite uip {p = e₁} {q = e₁'} | uip {p = e₂} {q = e₂'} = ≐ʳ-refl

⟨⟩-≤-ren-cast : ∀ {Γ Γ' ρ ρ'} → (e : Γ' ≡ Γ) → (p p' : ρ' ≾ᵣ ρ)
              → ⟨⟩-≤-ren {Δ = Γ} p
              ≐ʳ castʳ² (cong (_⟨ ρ ⟩) e) (cong (_⟨ ρ' ⟩) e) (⟨⟩-≤-ren p')
⟨⟩-≤-ren-cast refl p p' = ⟨⟩-≤-ren-≐ʳ p p'

⟨⟩-μ-ren-cast : ∀ {Γ Γ' ρ ρ'} → (e : Γ' ≡ Γ)
              → ⟨⟩-μ-ren {Δ = Γ} {ρ = ρ} {ρ' = ρ'}
              ≐ʳ castʳ² (cong (_⟨ ρ ·ᵣ ρ' ⟩) e) (cong (λ Γ₀ → Γ₀ ⟨ ρ ⟩ ⟨ ρ' ⟩) e)
                        ⟨⟩-μ-ren
⟨⟩-μ-ren-cast refl = ≐ʳ-refl

cong-⟨⟩-wk-cast : ∀ {Γ Γ' A ρ} → (e : Γ' ≡ Γ)
                → cong-⟨⟩-ren {ρ = ρ} (wk-ren {Δ = Γ} {A = A})
                ≐ʳ castʳ² (cong (_⟨ ρ ⟩) e) (cong (λ Γ₀ → (Γ₀ ∷ A) ⟨ ρ ⟩) e)
                          (cong-⟨⟩-ren wk-ren)
cong-⟨⟩-wk-cast refl = ≐ʳ-refl

-- Extensions of the same shape induce `_≐ʳ_`-equal renamings.

suc-comp-ren-≐ʳ : ∀ {𝕊 𝕊₁ 𝕊' 𝕊₁' : State []} {ρ'' ρ''' : R}
               → {q : 𝕊 ≤ₛ 𝕊₁} → {q' : 𝕊' ≤ₛ 𝕊₁'}
               → (h : q ≤≐ q')
               → (es : 𝕊 ≐ˢ 𝕊') → (es₁ : 𝕊₁ ≐ˢ 𝕊₁')
               → (c  : κₛ q  ·ᵣ ρ''' ≾ᵣ ρ'')
               → (c' : κₛ q' ·ᵣ ρ''' ≾ᵣ ρ'')
               → suc-comp-ren q c
               ≐ʳ castʳ² (cong (_⟨ ρ'' ⟩)  (sym (toCtx-≐ˢ es)))
                         (cong (_⟨ ρ''' ⟩) (sym (toCtx-≐ˢ es₁)))
                         (suc-comp-ren q' c')

suc-comp-ren-≐ʳ id-≤≐ es es₁ c c' =
  ≐ʳ-trans (⟨⟩-≤-ren-cast (sym (toCtx-≐ˢ es)) _ _)
           (castʳ²-irr _ _ _ _ (⟨⟩-≤-ren _))

suc-comp-ren-≐ʳ {ρ'' = ρ''} {ρ''' = ρ'''} (⟨⟩-≤≐ {q' = q'} ρ h) es
               (⟨⟩-≐ˢ .ρ es₁) c c' =
  ≐ʳ-trans (∘ʳ-≐ʳ (suc-comp-ren-≐ʳ {ρ'' = ρ''} {ρ''' = ρ ·ᵣ ρ'''} h es es₁ _ _)
                 (⟨⟩-μ-ren-cast {ρ = ρ} {ρ' = ρ'''} (sym (toCtx-≐ˢ es₁))))
    (≐ʳ-trans
      (≐ʳ-sym (castʳ²-∘ʳ (cong (λ Γ₀ → (Γ₀ ⟨ ρ ⟩) ⟨ ρ''' ⟩) (sym (toCtx-≐ˢ es₁)))
                         (cong (_⟨ ρ ·ᵣ ρ''' ⟩) (sym (toCtx-≐ˢ es₁)))
                         (cong (_⟨ ρ'' ⟩) (sym (toCtx-≐ˢ es)))
                         (suc-comp-ren _ _) ⟨⟩-μ-ren))
      (castʳ²-irr (cong (_⟨ ρ'' ⟩) (sym (toCtx-≐ˢ es)))
                  (cong (_⟨ ρ'' ⟩) (sym (toCtx-≐ˢ es)))
                  (cong (λ Γ₀ → (Γ₀ ⟨ ρ ⟩) ⟨ ρ''' ⟩) (sym (toCtx-≐ˢ es₁)))
                  (cong (_⟨ ρ''' ⟩) (sym (toCtx-≐ˢ (⟨⟩-≐ˢ ρ es₁))))
                  (suc-comp-ren (≤ₛ-lock q') c')))

suc-comp-ren-≐ʳ {ρ'' = ρ''} {ρ''' = ρ'''}
               (∷-≤≐ {A = A} {ρ = ρ} {q' = q'} {V' = V'} h) es
               (∷-≐ˢ es₁ eV) c c' =
  ≐ʳ-trans (∘ʳ-≐ʳ (suc-comp-ren-≐ʳ {ρ'' = ρ''} {ρ''' = ρ'''} h es es₁ _ _)
                 (cong-⟨⟩-wk-cast {A = [ ρ ] A} {ρ = ρ'''}
                   (sym (toCtx-≐ˢ es₁))))
    (≐ʳ-trans
      (≐ʳ-sym (castʳ²-∘ʳ (cong (λ Γ₀ → (Γ₀ ∷ [ ρ ] A) ⟨ ρ''' ⟩)
                               (sym (toCtx-≐ˢ es₁)))
                         (cong (_⟨ ρ''' ⟩) (sym (toCtx-≐ˢ es₁)))
                         (cong (_⟨ ρ'' ⟩) (sym (toCtx-≐ˢ es)))
                         (suc-comp-ren _ _) (cong-⟨⟩-ren wk-ren)))
      (castʳ²-irr (cong (_⟨ ρ'' ⟩) (sym (toCtx-≐ˢ es)))
                  (cong (_⟨ ρ'' ⟩) (sym (toCtx-≐ˢ es)))
                  (cong (λ Γ₀ → (Γ₀ ∷ [ ρ ] A) ⟨ ρ''' ⟩) (sym (toCtx-≐ˢ es₁)))
                  (cong (_⟨ ρ''' ⟩) (sym (toCtx-≐ˢ (∷-≐ˢ es₁ eV))))
                  (suc-comp-ren (≤ₛ-res {V = V'} q') c')))

-- A cell of `𝕊` is a cell of `𝕊'`, split off at related states and holding
-- equal values.

≐ˢ-var : ∀ {A ρ σ} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
       → [ ρ ] A ∈[ σ ] toCtx 𝕊 → [ ρ ] A ∈[ σ ] toCtx 𝕊'
≐ˢ-var {A} {ρ} {σ} es z =
  subst (λ Γ₀ → [ ρ ] A ∈[ σ ] Γ₀) (toCtx-≐ˢ es) z

≐ˢ-fst : ∀ {A ρ σ} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
       → (z : [ ρ ] A ∈[ σ ] toCtx 𝕊)
       → split-state-fst 𝕊 z ≐ˢ split-state-fst 𝕊' (≐ˢ-var es z)

≐ˢ-fst (⟨⟩-≐ˢ ρ' es) (Tl-⟨⟩ z)
  rewrite subst-Tl-⟨⟩ {ρ = ρ'} (toCtx-≐ˢ es) z = ≐ˢ-fst es z
≐ˢ-fst {A} {ρ} (∷-≐ˢ es eV) Hd
  rewrite subst-Hd {A = [ ρ ] A} (toCtx-≐ˢ es) = es
≐ˢ-fst (∷-≐ˢ {A₁} {ρ₁} es eV) (Tl-∷ z)
  rewrite subst-Tl-∷ {B = [ ρ₁ ] A₁} (toCtx-≐ˢ es) z = ≐ˢ-fst es z

≐ˢ-lookup : ∀ {A ρ σ} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
          → (z : [ ρ ] A ∈[ σ ] toCtx 𝕊)
          → resource-lookup 𝕊 z
          ≡ castᵛ (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩)
                         (sym (toCtx-≐ˢ (≐ˢ-fst es z))))
                   (resource-lookup 𝕊' (≐ˢ-var es z))

≐ˢ-lookup (⟨⟩-≐ˢ ρ' es) (Tl-⟨⟩ z)
  rewrite subst-Tl-⟨⟩ {ρ = ρ'} (toCtx-≐ˢ es) z = ≐ˢ-lookup es z
≐ˢ-lookup {A} {ρ} (∷-≐ˢ es eV) Hd
  rewrite subst-Hd {A = [ ρ ] A} (toCtx-≐ˢ es) = eV
≐ˢ-lookup (∷-≐ˢ {A₁} {ρ₁} es eV) (Tl-∷ z)
  rewrite subst-Tl-∷ {B = [ ρ₁ ] A₁} (toCtx-≐ˢ es) z = ≐ˢ-lookup es z

-- The part of the state after the cell corresponds too, as a context.

≐ˢ-snd-ctx : ∀ {A ρ σ} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
           → (z : [ ρ ] A ∈[ σ ] toCtx 𝕊)
           → toCtx (split-state-snd 𝕊' (≐ˢ-var es z))
           ≡ toCtx (split-state-snd 𝕊 z)

≐ˢ-snd-ctx (⟨⟩-≐ˢ ρ' es) (Tl-⟨⟩ z)
  rewrite subst-Tl-⟨⟩ {ρ = ρ'} (toCtx-≐ˢ es) z =
  cong (_⟨ ρ' ⟩) (≐ˢ-snd-ctx es z)
≐ˢ-snd-ctx {A} {ρ} (∷-≐ˢ es eV) Hd
  rewrite subst-Hd {A = [ ρ ] A} (toCtx-≐ˢ es) = refl
≐ˢ-snd-ctx (∷-≐ˢ {A₁} {ρ₁} es eV) (Tl-∷ z)
  rewrite subst-Tl-∷ {B = [ ρ₁ ] A₁} (toCtx-≐ˢ es) z =
  cong (_∷ [ ρ₁ ] A₁) (≐ˢ-snd-ctx es z)

-- The same, presented at the `𝕊'`-side cell the caller has.

≐ˢ-fst₂ : ∀ {A ρ σ} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
        → (z : [ ρ ] A ∈[ σ ] toCtx 𝕊) → (z' : [ ρ ] A ∈[ σ ] toCtx 𝕊')
        → ≐ˢ-var es z ≡ z'
        → split-state-fst 𝕊 z ≐ˢ split-state-fst 𝕊' z'
≐ˢ-fst₂ es z z' refl = ≐ˢ-fst es z

≐ˢ-snd-ctx₂ : ∀ {A ρ σ} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
            → (z : [ ρ ] A ∈[ σ ] toCtx 𝕊) → (z' : [ ρ ] A ∈[ σ ] toCtx 𝕊')
            → ≐ˢ-var es z ≡ z'
            → toCtx (split-state-snd 𝕊' z') ≡ toCtx (split-state-snd 𝕊 z)
≐ˢ-snd-ctx₂ es z z' refl = ≐ˢ-snd-ctx es z

≐ˢ-lookup₂ : ∀ {A ρ σ} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
           → (z : [ ρ ] A ∈[ σ ] toCtx 𝕊) → (z' : [ ρ ] A ∈[ σ ] toCtx 𝕊')
           → (e : ≐ˢ-var es z ≡ z')
           → resource-lookup 𝕊 z
           ≡ castᵛ (cong (λ Γ₀ → ([] ++ᶜ Γ₀) ⟨ ρ ⟩)
                          (sym (toCtx-≐ˢ (≐ˢ-fst₂ es z z' e))))
                    (resource-lookup 𝕊' z')
≐ˢ-lookup₂ es z z' refl = ≐ˢ-lookup es z

-- `UNBOX` reads the store; related states hold related values.

-- Stated on cells, which is what a `VRed` stated on readability needs;
-- `unbox-lookup-≐ˢ` below is the same at an `unbox` node's variable.

lookup-body-≐ˢ : ∀ {A ρ} {𝕊 𝕊' : State []}
               → (es : 𝕊 ≐ˢ 𝕊')
               → (t : Var (toCtx 𝕊) ([ ρ ] A)) → (t' : Var (toCtx 𝕊') ([ ρ ] A))
               → t ≡ Var-cast (sym (toCtx-≐ˢ es)) t'
               → (rel : proj₁ t ≾ᵣ ρ) → (rel' : proj₁ t' ≾ᵣ ρ)
               -------------------------------------------------------
               → lookup-body 𝕊 t rel
               ≡ castᵛ (sym (toCtx-≐ˢ es)) (lookup-body 𝕊' t' rel')

lookup-body-≐ˢ {A} {ρ} {𝕊 = 𝕊} {𝕊' = 𝕊'} es t t' ht rel rel' =
  subst (λ u → u ≡ castᵛ (sym (toCtx-≐ˢ es)) (lookup-body 𝕊' t' rel'))
        (sym (lookup-body-≡ 𝕊 ht rel rel'))
        (lookup-body′-≡
           (sym (toCtx-≐ˢ es))
           (sym (toCtx-≐ˢ (≐ˢ-fst₂ es z z' zz))) (≐ˢ-snd-ctx₂ es z z' zz)
           _ _ _ _ rel' rel' _ _
           (≐ˢ-lookup₂ es z z' zz))
  where
    z' = proj₂ t'

    z = subst (λ Γ₀ → [ ρ ] A ∈[ proj₁ t' ] Γ₀) (sym (toCtx-≐ˢ es)) z'

    zz : ≐ˢ-var es z ≡ z'
    zz = subst-subst-sym (toCtx-≐ˢ es)

unbox-lookup-≐ˢ : ∀ {A ρ ρ' ρ''} {𝕊 𝕊' : State []}
               → (es : 𝕊 ≐ˢ 𝕊')
               → {x : [ ρ ] A ∈[ ρ' ] toCtx 𝕊} → {x' : [ ρ ] A ∈[ ρ'' ] toCtx 𝕊'}
               → {rel : ρ' ≾ᵣ ρ} → {rel' : ρ'' ≾ᵣ ρ}
               → _≡_ {A = Var (toCtx 𝕊) ([ ρ ] A)}
                     (ρ' , x) (Var-cast (sym (toCtx-≐ˢ es)) (ρ'' , x'))
               -------------------------------------------------------
               → unbox-lookup 𝕊 x rel
               ≡ castᵛ (sym (toCtx-≐ˢ es)) (unbox-lookup 𝕊' x' rel')

unbox-lookup-≐ˢ es {x} {x'} {rel} {rel'} h =
  lookup-body-≐ˢ es (_ , x) (_ , x') h rel rel'

