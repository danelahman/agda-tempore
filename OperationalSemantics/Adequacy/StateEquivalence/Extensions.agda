------------------------------------------------------------------------
-- State extensions of the same shape, and reading the store.
------------------------------------------------------------------------

open import Data.Product

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Relation.Nullary using (¬_)

open import Util.Equality

module OperationalSemantics.Adequacy.StateEquivalence.Extensions (Spec : LanguageSpec) where
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

open import OperationalSemantics.Adequacy.StateEquivalence.Core Spec

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

≤≐-sym : ∀ {St St₁ St' St₁' : 𝕊 []} {q : St ≤ₛ St₁} {q' : St' ≤ₛ St₁'}
       → q ≤≐ q' → q' ≤≐ q
≤≐-sym id-≤≐       = id-≤≐
≤≐-sym (⟨⟩-≤≐ ρ h) = ⟨⟩-≤≐ ρ (≤≐-sym h)
≤≐-sym (∷-≤≐ h)    = ∷-≤≐ (≤≐-sym h)

≤ₛ-grade-≤≐ : ∀ {St St₁ St' St₁' : 𝕊 []} {q : St ≤ₛ St₁} {q' : St' ≤ₛ St₁'}
            → q ≤≐ q' → ≤ₛ-grade q ≡ ≤ₛ-grade q'
≤ₛ-grade-≤≐ id-≤≐        = refl
≤ₛ-grade-≤≐ (⟨⟩-≤≐ ρ h)  = cong (_·ᵣ ρ) (≤ₛ-grade-≤≐ h)
≤ₛ-grade-≤≐ (∷-≤≐ h)     = ≤ₛ-grade-≤≐ h

-- Transporting a renaming along equalities of both its contexts.

castʳ² : ∀ {Γ₁ Γ₂ Γ₁' Γ₂'} → Γ₁' ≡ Γ₁ → Γ₂' ≡ Γ₂ → Ren [] Γ₂' Γ₁' → Ren [] Γ₂ Γ₁
castʳ² refl refl r = r

-- The three renamings `suc-comp-ren` is built from, each compared across a cast.
-- Provable because here the contexts are *variables*, so the equalities can be
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

suc-comp-ren-≐ʳ : ∀ {St St₁ St' St₁' : 𝕊 []} {ρ'' ρ''' : R}
               → {q : St ≤ₛ St₁} → {q' : St' ≤ₛ St₁'}
               → (h : q ≤≐ q')
               → (es : St ≐ˢ St') → (es₁ : St₁ ≐ˢ St₁')
               → (c  : ≤ₛ-grade q  ·ᵣ ρ''' ≾ᵣ ρ'')
               → (c' : ≤ₛ-grade q' ·ᵣ ρ''' ≾ᵣ ρ'')
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
                  (suc-comp-ren (⟨⟩-suc ρ q') c')))

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
                  (suc-comp-ren (∷-suc V' q') c')))

------------------------------------------------------------------------
-- RELATED STATES HOLD RELATED VALUES
--
-- A cell of `St` is a cell of `St'`, split off at related states and holding
-- equal values — which at the cell itself is exactly what `∷-≐ˢ`
-- stores. Induction on the relation and the variable together; `toCtx-≐ˢ` is
-- built by `cong`, so relocating the variable is `subst-Hd`/`subst-Tl-*`.
------------------------------------------------------------------------

≐ˢ-var : ∀ {A ρ σ} {St St' : 𝕊 []} → (es : St ≐ˢ St')
       → [ ρ ] A ∈[ σ ] toCtx St → [ ρ ] A ∈[ σ ] toCtx St'
≐ˢ-var {A} {ρ} {σ} es z =
  subst (λ Γ₀ → [ ρ ] A ∈[ σ ] Γ₀) (toCtx-≐ˢ es) z

≐ˢ-fst : ∀ {A ρ σ} {St St' : 𝕊 []} → (es : St ≐ˢ St')
       → (z : [ ρ ] A ∈[ σ ] toCtx St)
       → split-state-fst St z ≐ˢ split-state-fst St' (≐ˢ-var es z)

≐ˢ-fst (⟨⟩-≐ˢ ρ' es) (Tl-⟨⟩ z)
  rewrite subst-Tl-⟨⟩ {ρ = ρ'} (toCtx-≐ˢ es) z = ≐ˢ-fst es z
≐ˢ-fst {A} {ρ} (∷-≐ˢ es eV) Hd
  rewrite subst-Hd {A = [ ρ ] A} (toCtx-≐ˢ es) = es
≐ˢ-fst (∷-≐ˢ {A₁} {ρ₁} es eV) (Tl-∷ z)
  rewrite subst-Tl-∷ {B = [ ρ₁ ] A₁} (toCtx-≐ˢ es) z = ≐ˢ-fst es z

≐ˢ-lookup : ∀ {A ρ σ} {St St' : 𝕊 []} → (es : St ≐ˢ St')
          → (z : [ ρ ] A ∈[ σ ] toCtx St)
          → resource-lookup St z
          ≡ castᵛ (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩)
                         (sym (toCtx-≐ˢ (≐ˢ-fst es z))))
                   (resource-lookup St' (≐ˢ-var es z))

≐ˢ-lookup (⟨⟩-≐ˢ ρ' es) (Tl-⟨⟩ z)
  rewrite subst-Tl-⟨⟩ {ρ = ρ'} (toCtx-≐ˢ es) z = ≐ˢ-lookup es z
≐ˢ-lookup {A} {ρ} (∷-≐ˢ es eV) Hd
  rewrite subst-Hd {A = [ ρ ] A} (toCtx-≐ˢ es) = eV
≐ˢ-lookup (∷-≐ˢ {A₁} {ρ₁} es eV) (Tl-∷ z)
  rewrite subst-Tl-∷ {B = [ ρ₁ ] A₁} (toCtx-≐ˢ es) z = ≐ˢ-lookup es z

-- The part of the state after the cell corresponds too, as a context.

≐ˢ-snd-ctx : ∀ {A ρ σ} {St St' : 𝕊 []} → (es : St ≐ˢ St')
           → (z : [ ρ ] A ∈[ σ ] toCtx St)
           → toCtx (split-state-snd St' (≐ˢ-var es z))
           ≡ toCtx (split-state-snd St z)

≐ˢ-snd-ctx (⟨⟩-≐ˢ ρ' es) (Tl-⟨⟩ z)
  rewrite subst-Tl-⟨⟩ {ρ = ρ'} (toCtx-≐ˢ es) z =
  cong (_⟨ ρ' ⟩) (≐ˢ-snd-ctx es z)
≐ˢ-snd-ctx {A} {ρ} (∷-≐ˢ es eV) Hd
  rewrite subst-Hd {A = [ ρ ] A} (toCtx-≐ˢ es) = refl
≐ˢ-snd-ctx (∷-≐ˢ {A₁} {ρ₁} es eV) (Tl-∷ z)
  rewrite subst-Tl-∷ {B = [ ρ₁ ] A₁} (toCtx-≐ˢ es) z =
  cong (_∷ [ ρ₁ ] A₁) (≐ˢ-snd-ctx es z)

-- The same, presented at the `St'`-side cell the caller actually has.

≐ˢ-fst₂ : ∀ {A ρ σ} {St St' : 𝕊 []} → (es : St ≐ˢ St')
        → (z : [ ρ ] A ∈[ σ ] toCtx St) → (z' : [ ρ ] A ∈[ σ ] toCtx St')
        → ≐ˢ-var es z ≡ z'
        → split-state-fst St z ≐ˢ split-state-fst St' z'
≐ˢ-fst₂ es z z' refl = ≐ˢ-fst es z

≐ˢ-snd-ctx₂ : ∀ {A ρ σ} {St St' : 𝕊 []} → (es : St ≐ˢ St')
            → (z : [ ρ ] A ∈[ σ ] toCtx St) → (z' : [ ρ ] A ∈[ σ ] toCtx St')
            → ≐ˢ-var es z ≡ z'
            → toCtx (split-state-snd St' z') ≡ toCtx (split-state-snd St z)
≐ˢ-snd-ctx₂ es z z' refl = ≐ˢ-snd-ctx es z

≐ˢ-lookup₂ : ∀ {A ρ σ} {St St' : 𝕊 []} → (es : St ≐ˢ St')
           → (z : [ ρ ] A ∈[ σ ] toCtx St) → (z' : [ ρ ] A ∈[ σ ] toCtx St')
           → (e : ≐ˢ-var es z ≡ z')
           → resource-lookup St z
           ≡ castᵛ (cong (λ Γ₀ → ([] ++ᶜ Γ₀) ⟨ ρ ⟩)
                          (sym (toCtx-≐ˢ (≐ˢ-fst₂ es z z' e))))
                    (resource-lookup St' z')
≐ˢ-lookup₂ es z z' refl = ≐ˢ-lookup es z

------------------------------------------------------------------------
-- READING THE STORE, UP TO THE EQUIVALENCE
--
-- `UNBOX` reads the store; related states hold related values. Unfolding both
-- lookups leaves `lookup-body′` at corresponding data, which `lookup-body′-≡`
-- compares.
------------------------------------------------------------------------

-- Stated on cells, which is what a `Val` stated on readability needs;
-- `unbox-lookup-≐ˢ` below is the same at an `unbox` node's variable.

lookup-body-≐ˢ : ∀ {A ρ} {St St' : 𝕊 []}
               → (es : St ≐ˢ St')
               → (t : Var (toCtx St) ([ ρ ] A)) → (t' : Var (toCtx St') ([ ρ ] A))
               → t ≡ Var-cast (sym (toCtx-≐ˢ es)) t'
               → (rel : proj₁ t ≾ᵣ ρ) → (rel' : proj₁ t' ≾ᵣ ρ)
               -------------------------------------------------------
               → lookup-body St t rel
               ≡ castᵛ (sym (toCtx-≐ˢ es)) (lookup-body St' t' rel')

lookup-body-≐ˢ {A} {ρ} {St = St} {St' = St'} es t t' ht rel rel' =
  subst (λ u → u ≡ castᵛ (sym (toCtx-≐ˢ es)) (lookup-body St' t' rel'))
        (sym (lookup-body-≡ St ht rel rel'))
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

unbox-lookup-≐ˢ : ∀ {A ρ ρ' ρ''} {St St' : 𝕊 []}
               → (es : St ≐ˢ St')
               → {x : [ ρ ] A ∈[ ρ' ] toCtx St} → {x' : [ ρ ] A ∈[ ρ'' ] toCtx St'}
               → {rel : ρ' ≾ᵣ ρ} → {rel' : ρ'' ≾ᵣ ρ}
               → _≡_ {A = Var (toCtx St) ([ ρ ] A)}
                     (ρ' , x) (Var-cast (sym (toCtx-≐ˢ es)) (ρ'' , x'))
               -------------------------------------------------------
               → unbox-lookup St x rel
               ≡ castᵛ (sym (toCtx-≐ˢ es)) (unbox-lookup St' x' rel')

unbox-lookup-≐ˢ es {x} {x'} {rel} {rel'} h =
  lookup-body-≐ˢ es (_ , x) (_ , x') h rel rel'

