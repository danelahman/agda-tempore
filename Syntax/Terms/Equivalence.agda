------------------------------------------------------------------------
-- Terms up to irrelevant stored data.                                --
--                                                                    --
-- A term is *not* determined by its shape: `var` stores a grade       --
-- bound, `coerce` an effect ordering, and `unbox` a whole renaming.   --
-- The first two are irrelevant (`≾ᵣ-irrelevant`, `≾ₑ-irrelevant`);    --
-- the third is relevant only up to `_≐ʳ_`, since reduction consults   --
-- it solely through `unbox⇒var`.                                      --
--                                                                    --
-- `_≐ᵛ_`/`_≐ᶜ_` are the congruence that ignores exactly this data.    --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Terms.Equivalence (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   Spec
open import Syntax.Language   Spec
open import Syntax.RenActions Spec
open import Syntax.Renamings  Spec
open import Syntax.Types      Spec
open import Syntax.Renamings.Equivalence Spec

------------------------------------------------------------------------
-- TERMS UP TO IRRELEVANT STORED DATA
--
-- A term is *not* determined by its shape: `var` stores a grade bound,
-- `coerce` an effect ordering, and `unbox` a whole renaming. The first two are
-- irrelevant (`≾ᵣ-irrelevant`, `≾ₑ-irrelevant`); the third is relevant only up
-- to `_≐ʳ_`, since reduction consults it solely through `unbox⇒var`.
--
-- So the laws below cannot be stated at `_≡_`: renaming along `r₂ ∘ʳ r₁`
-- stores that composite in every `unbox` node, where renaming twice stores
-- `r₂ ∘ʳ (r₁ ∘ʳ w)`. The two are `_≐ʳ_`-equal, never equal. `_≐ᵛ_`/`_≐ᶜ_`
-- below are the congruence that ignores exactly this data.
--
-- `EquationalTheory` is insensitive to the `coerce` witness but not to the
-- other two, so it cannot relate those `unbox` nodes either. Aligning the two
-- is on the cleanup list in `notes/adequacy-plan.md`.
------------------------------------------------------------------------

infix 4 _≐ᵛ_
infix 4 _≐ᶜ_

mutual

  data _≐ᵛ_ {Γ : Ctx} : ∀ {A} → Γ ⊢V⦂ A → Γ ⊢V⦂ A → Set where

    var-≐   : ∀ {A ρ} {f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ} {x : A ∈[ ρ ] Γ}
            → var f x ≐ᵛ var f' x

    const-≐ : ∀ {b} {c : BaseConstants b} → const c ≐ᵛ const c

    ⋆-≐     : ⋆ ≐ᵛ ⋆

    pair-≐  : ∀ {A B} {V V' : Γ ⊢V⦂ A} {W W' : Γ ⊢V⦂ B}
            → V ≐ᵛ V' → W ≐ᵛ W' → ⦉ V , W ⦊ ≐ᵛ ⦉ V' , W' ⦊

    lam-≐   : ∀ {A C} {M M' : Γ ∷ A ⊢C⦂ C}
            → M ≐ᶜ M' → lam M ≐ᵛ lam M'

  data _≐ᶜ_ {Γ : Ctx} : ∀ {C} → Γ ⊢C⦂ C → Γ ⊢C⦂ C → Set where

    return-≐  : ∀ {A} {V V' : Γ ⊢V⦂ A}
              → V ≐ᵛ V' → return V ≐ᶜ return V'

    seq-≐     : ∀ {A B ε ε'} {M M' : Γ ⊢C⦂ A ‼ ε}
                  {N N' : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
              → M ≐ᶜ M' → N ≐ᶜ N' → (M ⨟ N) ≐ᶜ (M' ⨟ N')

    app-≐     : ∀ {A C} {V V' : Γ ⊢V⦂ A ⇒ C} {W W' : Γ ⊢V⦂ A}
              → V ≐ᵛ V' → W ≐ᵛ W' → (V · W) ≐ᶜ (V' · W')

    match-≐   : ∀ {A B C} {V V' : Γ ⊢V⦂ A |×| B} {M M' : Γ ∷ A ∷ B ⊢C⦂ C}
              → V ≐ᵛ V' → M ≐ᶜ M'
              → (match V `in M) ≐ᶜ (match V' `in M')

    absurd-≐  : ∀ {C} {V V' : Γ ⊢V⦂ Empty}
              → V ≐ᵛ V' → absurd {C = C} V ≐ᶜ absurd V'

    perform-≐ : ∀ {A ε} {op : Op} {V V' : Γ ⊢V⦂ type-of-gtype (param op)}
                  {M M' : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                            ⊢C⦂ A ‼ ε}
              → V ≐ᵛ V' → M ≐ᶜ M'
              → perform op V M ≐ᶜ perform op V' M'

    delay-≐   : ∀ {A ε} {τ : ℕ} {M M' : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε}
              → M ≐ᶜ M' → delay τ M ≐ᶜ delay τ M'

    handle-≐  : ∀ {A B ε ε'} {M M' : Γ ⊢C⦂ A ‼ ε}
                  {H H' : (op : Op) → (ε'' : E) →
                            Γ ᴱ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ]
                                  (type-of-gtype (arity op) ⇒ B ‼ ε'')
                            ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
                  {N N' : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
              → M ≐ᶜ M'
              → (∀ op ε'' → H op ε'' ≐ᶜ H' op ε'')
              → N ≐ᶜ N'
              → (handle M `with H `in N) ≐ᶜ (handle M' `with H' `in N')

    -- the two nodes storing data that matters only up to equivalence

    -- `unbox` is compared at the *resource variable* it names, not at the renaming and boxed
    -- value it stores: substitution renormalises those (`unbox⇒var` then
    -- `unbox-var`), so demanding they agree would make substitution lemmas false.

    unbox-≐   : ∀ {A C ρ Δ Δ'} {w : Ren [] (Δ ⟨ ρ ⟩) Γ} {w' : Ren [] (Δ' ⟨ ρ ⟩) Γ}
                  {V : Δ ⊢V⦂ [ ρ ] A} {V' : Δ' ⊢V⦂ [ ρ ] A}
                  {M M' : Γ ∷ A ⊢C⦂ C}
              → unbox-img w V ≡ unbox-img w' V' → M ≐ᶜ M'
              → unbox w V M ≐ᶜ unbox w' V' M'

    coerce-≐  : ∀ {A ε ε'} {p p' : ε ≾ₑ ε'} {M M' : Γ ⊢C⦂ A ‼ ε}
              → M ≐ᶜ M' → coerce p M ≐ᶜ coerce p' M'

    box-≐     : ∀ {A C ρ} {V V' : Γ ⟨ ρ ⟩ ⊢V⦂ A} {M M' : Γ ∷ [ ρ ] A ⊢C⦂ C}
              → V ≐ᵛ V' → M ≐ᶜ M' → box V M ≐ᶜ box V' M'

-- Reflexivity, symmetry and transitivity.

mutual

  ≐ᵛ-refl : ∀ {Γ A} → (V : Γ ⊢V⦂ A) → V ≐ᵛ V
  ≐ᵛ-refl (var f x)   = var-≐
  ≐ᵛ-refl (const c)   = const-≐
  ≐ᵛ-refl ⋆           = ⋆-≐
  ≐ᵛ-refl ⦉ V , W ⦊    = pair-≐ (≐ᵛ-refl V) (≐ᵛ-refl W)
  ≐ᵛ-refl (lam M)     = lam-≐ (≐ᶜ-refl M)

  ≐ᶜ-refl : ∀ {Γ C} → (M : Γ ⊢C⦂ C) → M ≐ᶜ M
  ≐ᶜ-refl (return V)              = return-≐ (≐ᵛ-refl V)
  ≐ᶜ-refl (M ⨟ N)                 = seq-≐ (≐ᶜ-refl M) (≐ᶜ-refl N)
  ≐ᶜ-refl (V · W)                 = app-≐ (≐ᵛ-refl V) (≐ᵛ-refl W)
  ≐ᶜ-refl (match V `in M)         = match-≐ (≐ᵛ-refl V) (≐ᶜ-refl M)
  ≐ᶜ-refl (absurd V)              = absurd-≐ (≐ᵛ-refl V)
  ≐ᶜ-refl (perform op V M)        = perform-≐ (≐ᵛ-refl V) (≐ᶜ-refl M)
  ≐ᶜ-refl (delay τ M)             = delay-≐ (≐ᶜ-refl M)
  ≐ᶜ-refl (handle M `with H `in N) =
    handle-≐ (≐ᶜ-refl M) (λ op ε'' → ≐ᶜ-refl (H op ε'')) (≐ᶜ-refl N)
  ≐ᶜ-refl (unbox w V M)           = unbox-≐ refl (≐ᶜ-refl M)
  ≐ᶜ-refl (box V M)               = box-≐ (≐ᵛ-refl V) (≐ᶜ-refl M)
  ≐ᶜ-refl (coerce p M)            = coerce-≐ (≐ᶜ-refl M)

mutual

  ≐ᵛ-trans : ∀ {Γ A} {V V' V'' : Γ ⊢V⦂ A} → V ≐ᵛ V' → V' ≐ᵛ V'' → V ≐ᵛ V''
  ≐ᵛ-trans var-≐            var-≐              = var-≐
  ≐ᵛ-trans const-≐          const-≐            = const-≐
  ≐ᵛ-trans ⋆-≐              ⋆-≐                = ⋆-≐
  ≐ᵛ-trans (pair-≐ eV eW)   (pair-≐ eV' eW')   =
    pair-≐ (≐ᵛ-trans eV eV') (≐ᵛ-trans eW eW')
  ≐ᵛ-trans (lam-≐ eM)       (lam-≐ eM')        = lam-≐ (≐ᶜ-trans eM eM')

  ≐ᶜ-trans : ∀ {Γ C} {M M' M'' : Γ ⊢C⦂ C} → M ≐ᶜ M' → M' ≐ᶜ M'' → M ≐ᶜ M''
  ≐ᶜ-trans (return-≐ eV)      (return-≐ eV')      = return-≐ (≐ᵛ-trans eV eV')
  ≐ᶜ-trans (seq-≐ eM eN)      (seq-≐ eM' eN')     =
    seq-≐ (≐ᶜ-trans eM eM') (≐ᶜ-trans eN eN')
  ≐ᶜ-trans (app-≐ eV eW)      (app-≐ eV' eW')     =
    app-≐ (≐ᵛ-trans eV eV') (≐ᵛ-trans eW eW')
  ≐ᶜ-trans (match-≐ eV eM)    (match-≐ eV' eM')   =
    match-≐ (≐ᵛ-trans eV eV') (≐ᶜ-trans eM eM')
  ≐ᶜ-trans (absurd-≐ eV)      (absurd-≐ eV')      = absurd-≐ (≐ᵛ-trans eV eV')
  ≐ᶜ-trans (perform-≐ eV eM)  (perform-≐ eV' eM') =
    perform-≐ (≐ᵛ-trans eV eV') (≐ᶜ-trans eM eM')
  ≐ᶜ-trans (delay-≐ eM)       (delay-≐ eM')       = delay-≐ (≐ᶜ-trans eM eM')
  ≐ᶜ-trans (handle-≐ eM eH eN) (handle-≐ eM' eH' eN') =
    handle-≐ (≐ᶜ-trans eM eM')
             (λ op ε'' → ≐ᶜ-trans (eH op ε'') (eH' op ε''))
             (≐ᶜ-trans eN eN')
  ≐ᶜ-trans (unbox-≐ hw eM)    (unbox-≐ hw' eM')   =
    unbox-≐ (trans hw hw') (≐ᶜ-trans eM eM')
  ≐ᶜ-trans (coerce-≐ eM)      (coerce-≐ eM')      = coerce-≐ (≐ᶜ-trans eM eM')
  ≐ᶜ-trans (box-≐ eV eM)      (box-≐ eV' eM')     =
    box-≐ (≐ᵛ-trans eV eV') (≐ᶜ-trans eM eM')

mutual

  ≐ᵛ-sym : ∀ {Γ A} {V V' : Γ ⊢V⦂ A} → V ≐ᵛ V' → V' ≐ᵛ V
  ≐ᵛ-sym var-≐            = var-≐
  ≐ᵛ-sym const-≐          = const-≐
  ≐ᵛ-sym ⋆-≐              = ⋆-≐
  ≐ᵛ-sym (pair-≐ eV eW)   = pair-≐ (≐ᵛ-sym eV) (≐ᵛ-sym eW)
  ≐ᵛ-sym (lam-≐ eM)       = lam-≐ (≐ᶜ-sym eM)

  ≐ᶜ-sym : ∀ {Γ C} {M M' : Γ ⊢C⦂ C} → M ≐ᶜ M' → M' ≐ᶜ M
  ≐ᶜ-sym (return-≐ eV)      = return-≐ (≐ᵛ-sym eV)
  ≐ᶜ-sym (seq-≐ eM eN)      = seq-≐ (≐ᶜ-sym eM) (≐ᶜ-sym eN)
  ≐ᶜ-sym (app-≐ eV eW)      = app-≐ (≐ᵛ-sym eV) (≐ᵛ-sym eW)
  ≐ᶜ-sym (match-≐ eV eM)    = match-≐ (≐ᵛ-sym eV) (≐ᶜ-sym eM)
  ≐ᶜ-sym (absurd-≐ eV)      = absurd-≐ (≐ᵛ-sym eV)
  ≐ᶜ-sym (perform-≐ eV eM)  = perform-≐ (≐ᵛ-sym eV) (≐ᶜ-sym eM)
  ≐ᶜ-sym (delay-≐ eM)       = delay-≐ (≐ᶜ-sym eM)
  ≐ᶜ-sym (handle-≐ eM eH eN) =
    handle-≐ (≐ᶜ-sym eM) (λ op ε'' → ≐ᶜ-sym (eH op ε'')) (≐ᶜ-sym eN)
  ≐ᶜ-sym (unbox-≐ hw eM)    = unbox-≐ (sym hw) (≐ᶜ-sym eM)
  ≐ᶜ-sym (coerce-≐ eM)      = coerce-≐ (≐ᶜ-sym eM)
  ≐ᶜ-sym (box-≐ eV eM)      = box-≐ (≐ᵛ-sym eV) (≐ᶜ-sym eM)

-- Propositional equality of terms refines to the equivalence.

≡→≐ᵛ : ∀ {Γ A} {V V' : Γ ⊢V⦂ A} → V ≡ V' → V ≐ᵛ V'
≡→≐ᵛ refl = ≐ᵛ-refl _

≡→≐ᶜ : ∀ {Γ C} {M M' : Γ ⊢C⦂ C} → M ≡ M' → M ≐ᶜ M'
≡→≐ᶜ refl = ≐ᶜ-refl _
