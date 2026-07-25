------------------------------------------------------------------------
-- When two renamings act alike.                                      --
--                                                                    --
-- `Ren` is a free syntactic structure: `id-ren`, `_∘ʳ_` and the      --
-- congruences are constructors, so composition is not associative    --
-- and `cong-ren` does not commute with it on the nose. What is true  --
-- is that renamings agreeing on variables act the same on terms, and --
-- `Val`'s Kripke clauses need that.                                  --
--                                                                    --
-- `_≐ʳ_` compares renamings by where they send variables — grade and --
-- position, not the grade-bound proof, which is irrelevant.          --
--                                                                    --
-- Nothing here is specific to adequacy: this is the equivalence of   --
-- renamings and the coherence laws of the action with respect to it, --
-- and it belongs in `Syntax.Renamings`/`Syntax.RenActions`. It lives --
-- here to keep the work-in-progress out of `Everything.agda`; see    --
-- the cleanup list in `notes/adequacy-plan.md`.                      --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Relation.Nullary using (yes; no)

open import Util.Equality

module OperationalSemantics.Adequacy.RenEquivalence (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   Spec
open import Syntax.Language   Spec
open import Syntax.RenActions Spec
open import Syntax.Renamings  Spec
open import Syntax.Types      Spec

-- Where a renaming sends a variable, forgetting the grade bound.

Tgt : Ctx → VType → Set
Tgt Γ' A = Σ[ ρ' ∈ R ] A ∈[ ρ' ] Γ'

var-tgt : ∀ {Γ Γ' A ρ} → Ren Γ Γ' → A ∈[ ρ ] Γ → Tgt Γ' A
var-tgt r x = proj₁ (var-rename r x) , proj₂ (proj₂ (var-rename r x))

-- The same, at an already-located variable: this is what makes `var-tgt` of a
-- composite the composite of `var-tgt`s, definitionally.

var-tgt′ : ∀ {Γ' Γ'' A} → Ren Γ' Γ'' → Tgt Γ' A → Tgt Γ'' A
var-tgt′ r (ρ' , y) = var-tgt r y

-- ACTING ALIKE

infix 4 _≐ʳ_

-- A record, not a function type: the statements below are used at renamings
-- Agda has to *infer*, which needs the relation to be rigid.

record _≐ʳ_ {Γ Γ'} (r r' : Ren Γ Γ') : Set where
  constructor mk≐ʳ
  field at : ∀ {A ρ} → (x : A ∈[ ρ ] Γ) → var-tgt r x ≡ var-tgt r' x

open _≐ʳ_ public

≐ʳ-refl : ∀ {Γ Γ'} {r : Ren Γ Γ'} → r ≐ʳ r
≐ʳ-refl = mk≐ʳ (λ x → refl)

≐ʳ-sym : ∀ {Γ Γ'} {r r' : Ren Γ Γ'} → r ≐ʳ r' → r' ≐ʳ r
≐ʳ-sym h = mk≐ʳ (λ x → sym (at h x))

≐ʳ-trans : ∀ {Γ Γ'} {r r' r'' : Ren Γ Γ'} → r ≐ʳ r' → r' ≐ʳ r'' → r ≐ʳ r''
≐ʳ-trans h h' = mk≐ʳ (λ x → trans (at h x) (at h' x))

-- COMPOSITION
--
-- `var-rename (r₂ ∘ʳ r₁)` locates the variable with `r₁` and then with `r₂`,
-- so all three laws below hold at the level of `var-tgt` by computation.

∘ʳ-≐ : ∀ {Γ Γ' Γ''} {r₂ r₂' : Ren Γ' Γ''} {r₁ r₁' : Ren Γ Γ'}
     → r₂ ≐ʳ r₂' → r₁ ≐ʳ r₁'
     -------------------------------
     → (r₂ ∘ʳ r₁) ≐ʳ (r₂' ∘ʳ r₁')
∘ʳ-≐ {r₂ = r₂} h₂ h₁ =
  mk≐ʳ (λ x → trans (cong (var-tgt′ r₂) (at h₁ x)) (at h₂ _))

∘ʳ-assoc-≐ : ∀ {Γ Γ' Γ'' Γ'''}
           → (r₃ : Ren Γ'' Γ''') → (r₂ : Ren Γ' Γ'') → (r₁ : Ren Γ Γ')
           ----------------------------------------------------------
           → ((r₃ ∘ʳ r₂) ∘ʳ r₁) ≐ʳ (r₃ ∘ʳ (r₂ ∘ʳ r₁))
∘ʳ-assoc-≐ r₃ r₂ r₁ = mk≐ʳ (λ x → refl)

∘ʳ-identityˡ-≐ : ∀ {Γ Γ'} → (r : Ren Γ Γ') → (id-ren ∘ʳ r) ≐ʳ r
∘ʳ-identityˡ-≐ r = mk≐ʳ (λ x → refl)

∘ʳ-identityʳ-≐ : ∀ {Γ Γ'} → (r : Ren Γ Γ') → (r ∘ʳ id-ren) ≐ʳ r
∘ʳ-identityʳ-≐ r = mk≐ʳ (λ x → refl)

-- GRADE BOUNDS ARE INVISIBLE TO `_≐ʳ_`
--
-- `⟨⟩-≤-ren` stores a `≾ᵣ` proof, but sends a variable to itself at a grade
-- fixed by the renaming's indices, so the proof is not observable.

⟨⟩-≤-ren-≐ : ∀ {Γ ρ ρ'} → (p p' : ρ' ≾ᵣ ρ)
           → ⟨⟩-≤-ren {Γ = Γ} p ≐ʳ ⟨⟩-≤-ren p'
⟨⟩-≤-ren-≐ p p' = mk≐ʳ go
  where
    go : ∀ {A ρ₀} → (x : A ∈[ ρ₀ ] _) → _
    go (Tl-⟨⟩ x) = refl

-- SUFFIX EXTENSION
--
-- `cong-ren` recurses on the suffix, so it respects `_≐ʳ_` and commutes with
-- composition up to it (`cong-∷-ren (r ∘ʳ r')` and `cong-∷-ren r ∘ʳ cong-∷-ren r'`
-- are distinct renamings acting alike).

cong-∷-ren-≐ : ∀ {Γ Γ' A} {r r' : Ren Γ Γ'}
             → r ≐ʳ r' → cong-∷-ren {A = A} r ≐ʳ cong-∷-ren r'
cong-∷-ren-≐ h = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go Hd       = refl
    go (Tl-∷ x) = cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (at h x)

cong-⟨⟩-ren-≐ : ∀ {Γ Γ' ρ} {r r' : Ren Γ Γ'}
              → r ≐ʳ r' → cong-⟨⟩-ren {ρ = ρ} r ≐ʳ cong-⟨⟩-ren r'
cong-⟨⟩-ren-≐ {ρ = ρ} h = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go (Tl-⟨⟩ x) = cong (λ z → proj₁ z ·ᵣ ρ , Tl-⟨⟩ (proj₂ z)) (at h x)

cong-ren-≐ : ∀ {Γ Γ'} {r r' : Ren Γ Γ'} → (Γ₀ : Ctx)
           → r ≐ʳ r' → cong-ren {Γ'' = Γ₀} r ≐ʳ cong-ren r'
cong-ren-≐ []         h = h
cong-ren-≐ (Γ₀ ∷ A)   h = cong-∷-ren-≐ (cong-ren-≐ Γ₀ h)
cong-ren-≐ (Γ₀ ⟨ ρ ⟩) h = cong-⟨⟩-ren-≐ (cong-ren-≐ Γ₀ h)

cong-∷-ren-∘-≐ : ∀ {Γ Γ' Γ'' A} → (r₂ : Ren Γ' Γ'') → (r₁ : Ren Γ Γ')
               → cong-∷-ren {A = A} (r₂ ∘ʳ r₁)
               ≐ʳ (cong-∷-ren r₂ ∘ʳ cong-∷-ren r₁)
cong-∷-ren-∘-≐ r₂ r₁ = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go Hd       = refl
    go (Tl-∷ x) = refl

cong-⟨⟩-ren-∘-≐ : ∀ {Γ Γ' Γ'' ρ} → (r₂ : Ren Γ' Γ'') → (r₁ : Ren Γ Γ')
                → cong-⟨⟩-ren {ρ = ρ} (r₂ ∘ʳ r₁)
                ≐ʳ (cong-⟨⟩-ren r₂ ∘ʳ cong-⟨⟩-ren r₁)
cong-⟨⟩-ren-∘-≐ {ρ = ρ} r₂ r₁ = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go (Tl-⟨⟩ x) = refl

cong-ren-∘-≐ : ∀ {Γ Γ' Γ''} → (Γ₀ : Ctx)
             → (r₂ : Ren Γ' Γ'') → (r₁ : Ren Γ Γ')
             → cong-ren {Γ'' = Γ₀} (r₂ ∘ʳ r₁)
             ≐ʳ (cong-ren {Γ'' = Γ₀} r₂ ∘ʳ cong-ren {Γ'' = Γ₀} r₁)
cong-ren-∘-≐ []         r₂ r₁ = ≐ʳ-refl
cong-ren-∘-≐ (Γ₀ ∷ A)   r₂ r₁ =
  ≐ʳ-trans (cong-∷-ren-≐ (cong-ren-∘-≐ Γ₀ r₂ r₁))
           (cong-∷-ren-∘-≐ (cong-ren {Γ'' = Γ₀} r₂) (cong-ren {Γ'' = Γ₀} r₁))
cong-ren-∘-≐ (Γ₀ ⟨ ρ ⟩) r₂ r₁ =
  ≐ʳ-trans (cong-⟨⟩-ren-≐ (cong-ren-∘-≐ Γ₀ r₂ r₁))
           (cong-⟨⟩-ren-∘-≐ (cong-ren {Γ'' = Γ₀} r₂) (cong-ren {Γ'' = Γ₀} r₁))

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
                  {H H' : (op : Op) → (ε'' : E) → (Γ' : Ctx) →
                            Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ]
                                  (type-of-gtype (arity op) ⇒ B ‼ ε'')
                            ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
                  {N N' : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
              → M ≐ᶜ M'
              → (∀ op ε'' Γ' → H op ε'' Γ' ≐ᶜ H' op ε'' Γ')
              → N ≐ᶜ N'
              → (handle M `with H `in N) ≐ᶜ (handle M' `with H' `in N')

    -- the two nodes storing data that matters only up to equivalence

    unbox-≐   : ∀ {A C ρ Δ} {w w' : Ren (Δ ⟨ ρ ⟩) Γ} {V : Δ ⊢V⦂ [ ρ ] A}
                  {M M' : Γ ∷ A ⊢C⦂ C}
              → w ≐ʳ w' → M ≐ᶜ M'
              → unbox w V M ≐ᶜ unbox w' V M'

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
    handle-≐ (≐ᶜ-refl M) (λ op ε'' Γ' → ≐ᶜ-refl (H op ε'' Γ')) (≐ᶜ-refl N)
  ≐ᶜ-refl (unbox w V M)           = unbox-≐ ≐ʳ-refl (≐ᶜ-refl M)
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
             (λ op ε'' Γ' → ≐ᶜ-trans (eH op ε'' Γ') (eH' op ε'' Γ'))
             (≐ᶜ-trans eN eN')
  ≐ᶜ-trans (unbox-≐ hw eM)    (unbox-≐ hw' eM')   =
    unbox-≐ (≐ʳ-trans hw hw') (≐ᶜ-trans eM eM')
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
    handle-≐ (≐ᶜ-sym eM) (λ op ε'' Γ' → ≐ᶜ-sym (eH op ε'' Γ')) (≐ᶜ-sym eN)
  ≐ᶜ-sym (unbox-≐ hw eM)    = unbox-≐ (≐ʳ-sym hw) (≐ᶜ-sym eM)
  ≐ᶜ-sym (coerce-≐ eM)      = coerce-≐ (≐ᶜ-sym eM)
  ≐ᶜ-sym (box-≐ eV eM)      = box-≐ (≐ᵛ-sym eV) (≐ᶜ-sym eM)

-- The eternal restriction is compositional by definition.

restrict-ren-∘-≐ : ∀ {Γ Γ' Γ''} → (r₂ : Ren Γ' Γ'') → (r₁ : Ren Γ Γ')
                 → restrict-ren (r₂ ∘ʳ r₁)
                 ≐ʳ (restrict-ren r₂ ∘ʳ restrict-ren r₁)
restrict-ren-∘-≐ r₂ r₁ = ≐ʳ-refl

------------------------------------------------------------------------
-- THE ETERNAL RESTRICTION
--
-- `restrict-ren` recurses on the *renaming*, so `restrict-ren-≐` is not a
-- congruence of a function of `var-tgt`. It goes through the *reflection* of a
-- restricted variable, `∈-ᴱ⁻`: restricting commutes with it (`restrict-tgt⁻`),
-- so `var-tgt (restrict-ren r) x` is determined by `var-tgt r` up to
-- injectivity of `∈-ᴱ⁻`.
--
-- Everything is stated in terms of `∈-ᴱ⁻` and never `∈-ᴱ`: both split on
-- `eternal?`, but a goal mentioning `∈-ᴱ` blocks the `with`-abstraction on that
-- scrutinee, whereas `∈-ᴱ⁻`'s own recursion does not.
------------------------------------------------------------------------

-- The variable of `Γ` that a variable of `Γ ᴱ` came from, on `Tgt`s.

∈-ᴱ⁻ : (Γ : Ctx) → ∀ {A ρ} → A ∈[ ρ ] Γ ᴱ → Tgt Γ A
∈-ᴱ⁻ []        x with x
... | ()
∈-ᴱ⁻ (Γ ∷ B)   x with eternal? B
∈-ᴱ⁻ (Γ ∷ B)   Hd       | yes _ = uᵣ , Hd
∈-ᴱ⁻ (Γ ∷ B)   (Tl-∷ y) | yes _ = proj₁ (∈-ᴱ⁻ Γ y) , Tl-∷ (proj₂ (∈-ᴱ⁻ Γ y))
∈-ᴱ⁻ (Γ ∷ B)   x        | no  _ = proj₁ (∈-ᴱ⁻ Γ x) , Tl-∷ (proj₂ (∈-ᴱ⁻ Γ x))
∈-ᴱ⁻ (Γ ⟨ ρ ⟩) x =
  proj₁ (∈-ᴱ⁻ Γ x) ·ᵣ ρ , Tl-⟨⟩ (proj₂ (∈-ᴱ⁻ Γ x))

∈-ᴱ⁻′ : (Γ : Ctx) → ∀ {A} → Tgt (Γ ᴱ) A → Tgt Γ A
∈-ᴱ⁻′ Γ (ρ , x) = ∈-ᴱ⁻ Γ x

-- Forcing a `with eternal?`-defined function to reduce: `rewrite`ing the
-- scrutinee is cleaner than unfold lemmas whose statements are themselves
-- `_ᴱ`-stuck. (Also in `Interpretation.SubstitutionCoherence`; see the cleanup
-- list in `notes/adequacy-plan.md`.)

eternal?-yes : ∀ {A} → (et : Eternal A) → eternal? A ≡ yes et
eternal?-yes {A} et with eternal? A
... | yes et' = cong yes (eternal-irrelevant et' et)
... | no ¬et  = ⊥-elim (¬et et)

-- Reflection undoes `∈-ᴱ`.

∈-ᴱ⁻-∈-ᴱ : (Γ : Ctx) → ∀ {A ρ} → (et : Eternal A) → (z : A ∈[ ρ ] Γ)
         → ∈-ᴱ⁻ Γ (∈-ᴱ et z) ≡ (ρ , z)

∈-ᴱ⁻-∈-ᴱ (Γ ∷ B)   et Hd       rewrite eternal?-yes et = refl
∈-ᴱ⁻-∈-ᴱ (Γ ∷ B)   et (Tl-∷ z) with eternal? B
... | yes _ = cong (λ w → proj₁ w , Tl-∷ (proj₂ w)) (∈-ᴱ⁻-∈-ᴱ Γ et z)
... | no  _ = cong (λ w → proj₁ w , Tl-∷ (proj₂ w)) (∈-ᴱ⁻-∈-ᴱ Γ et z)
∈-ᴱ⁻-∈-ᴱ (Γ ⟨ ρ₀ ⟩) et (Tl-⟨⟩ z) =
  cong (λ w → proj₁ w ·ᵣ ρ₀ , Tl-⟨⟩ (proj₂ w)) (∈-ᴱ⁻-∈-ᴱ Γ et z)

-- It is injective: distinct variables of `Γ ᴱ` come from distinct variables.

∈-ᴱ⁻-inj : (Γ : Ctx) → ∀ {A} → (t t' : Tgt (Γ ᴱ) A)
         → ∈-ᴱ⁻′ Γ t ≡ ∈-ᴱ⁻′ Γ t' → t ≡ t'

∈-ᴱ⁻-inj []        (_ , x) _        e with x
... | ()
∈-ᴱ⁻-inj (Γ ∷ B)   t       t'       e with eternal? B
∈-ᴱ⁻-inj (Γ ∷ B) (_ , Hd)      (_ , Hd)      e | yes _ = refl
∈-ᴱ⁻-inj (Γ ∷ B) (_ , Hd)      (_ , Tl-∷ y') e | yes _ with ∈-ᴱ⁻ Γ y'
... | _ , _ with e
... | ()
∈-ᴱ⁻-inj (Γ ∷ B) (_ , Tl-∷ y) (_ , Hd)       e | yes _ with ∈-ᴱ⁻ Γ y
... | _ , _ with e
... | ()
∈-ᴱ⁻-inj (Γ ∷ B) (ρ , Tl-∷ y) (ρ' , Tl-∷ y') e | yes _ =
  cong (λ z → proj₁ z , Tl-∷ (proj₂ z))
       (∈-ᴱ⁻-inj Γ (ρ , y) (ρ' , y') (∷-inj e))
  where
    ∷-inj : ∀ {A ρ₁ ρ₂} {z₁ : A ∈[ ρ₁ ] Γ} {z₂ : A ∈[ ρ₂ ] Γ}
          → _≡_ {A = Tgt (Γ ∷ B) A} (ρ₁ , Tl-∷ z₁) (ρ₂ , Tl-∷ z₂)
          → _≡_ {A = Tgt Γ A} (ρ₁ , z₁) (ρ₂ , z₂)
    ∷-inj refl = refl
∈-ᴱ⁻-inj (Γ ∷ B) (ρ , x)      (ρ' , x')      e | no _ =
  ∈-ᴱ⁻-inj Γ (ρ , x) (ρ' , x') (∷-inj e)
  where
    ∷-inj : ∀ {A ρ₁ ρ₂} {z₁ : A ∈[ ρ₁ ] Γ} {z₂ : A ∈[ ρ₂ ] Γ}
          → _≡_ {A = Tgt (Γ ∷ B) A} (ρ₁ , Tl-∷ z₁) (ρ₂ , Tl-∷ z₂)
          → _≡_ {A = Tgt Γ A} (ρ₁ , z₁) (ρ₂ , z₂)
    ∷-inj refl = refl
∈-ᴱ⁻-inj (Γ ⟨ ρ₀ ⟩) (ρ , x)   (ρ' , x')      e =
  ∈-ᴱ⁻-inj Γ (ρ , x) (ρ' , x') (⟨⟩-inj e)
  where
    ⟨⟩-inj : ∀ {A ρ₁ ρ₂} {z₁ : A ∈[ ρ₁ ] Γ} {z₂ : A ∈[ ρ₂ ] Γ}
           → _≡_ {A = Tgt (Γ ⟨ ρ₀ ⟩) A} (ρ₁ ·ᵣ ρ₀ , Tl-⟨⟩ z₁) (ρ₂ ·ᵣ ρ₀ , Tl-⟨⟩ z₂)
           → _≡_ {A = Tgt Γ A} (ρ₁ , z₁) (ρ₂ , z₂)
    ⟨⟩-inj refl = refl

-- Restricting commutes with reflection. Induction on the renaming.

restrict-tgt⁻ : ∀ {Γ Γ'} → (r : Ren Γ Γ') → ∀ {A ρ} → (x : A ∈[ ρ ] Γ ᴱ)
              → ∈-ᴱ⁻′ Γ' (var-tgt (restrict-ren r) x)
              ≡ var-tgt′ r (∈-ᴱ⁻ Γ x)

restrict-tgt⁻ id-ren x = refl

restrict-tgt⁻ (r₂ ∘ʳ r₁) x =
  trans (restrict-tgt⁻ r₂ (proj₂ (var-tgt (restrict-ren r₁) x)))
        (cong (var-tgt′ r₂) (restrict-tgt⁻ r₁ x))

restrict-tgt⁻ (wk-ren {A = B}) x with eternal? B
... | yes _ = refl
... | no  _ = refl

restrict-tgt⁻ {Γ' = Γ'} (var-ren {A = B} p z) x with eternal? B
restrict-tgt⁻ {Γ' = Γ'} (var-ren {A = B} p z) Hd       | yes etB =
  ∈-ᴱ⁻-∈-ᴱ Γ' etB z
restrict-tgt⁻ (var-ren {A = B} p z) (Tl-∷ x) | yes _ = refl
restrict-tgt⁻ (var-ren {A = B} p z) x        | no  _ = refl

restrict-tgt⁻ ⟨⟩-η-ren     x = refl
restrict-tgt⁻ ⟨⟩-μ-ren     x = refl
restrict-tgt⁻ (⟨⟩-≤-ren _) x = refl

-- the one renaming whose source carries no lock and whose `var-rename` still
-- splits on the variable, so the reflected variable has to be exposed
restrict-tgt⁻ {Γ = Γ} ⟨⟩-η⁻¹-ren x with ∈-ᴱ⁻ Γ x
... | _ , Hd      = refl
... | _ , Tl-∷ y  = refl
... | _ , Tl-⟨⟩ y = refl

restrict-tgt⁻ (cong-∷-ren {A = B} r) x with eternal? B
restrict-tgt⁻ (cong-∷-ren {A = B} r) Hd       | yes _ = refl
restrict-tgt⁻ (cong-∷-ren {A = B} r) (Tl-∷ x) | yes _ =
  cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (restrict-tgt⁻ r x)
restrict-tgt⁻ (cong-∷-ren {A = B} r) x        | no  _ =
  cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (restrict-tgt⁻ r x)

restrict-tgt⁻ (cong-⟨⟩-ren {ρ = ρ₀} r) x =
  cong (λ z → proj₁ z ·ᵣ ρ₀ , Tl-⟨⟩ (proj₂ z)) (restrict-tgt⁻ r x)

restrict-tgt⁻ (⟨⟩-ext-ren {A = B} etB) x with eternal? B
restrict-tgt⁻ (⟨⟩-ext-ren {A = B} etB) Hd       | yes _ = refl
restrict-tgt⁻ (⟨⟩-ext-ren {A = B} etB) (Tl-∷ x) | yes _ = refl
restrict-tgt⁻ (⟨⟩-ext-ren {A = B} etB) x        | no ¬etB = ⊥-elim (¬etB etB)

-- The eternal restriction respects acting alike.

restrict-ren-≐ : ∀ {Γ Γ'} {r r' : Ren Γ Γ'}
               → r ≐ʳ r' → restrict-ren r ≐ʳ restrict-ren r'

restrict-ren-≐ {Γ} {Γ'} {r} {r'} h = mk≐ʳ go
  where
    go : ∀ {A ρ} → (x : A ∈[ ρ ] Γ ᴱ)
       → var-tgt (restrict-ren r) x ≡ var-tgt (restrict-ren r') x
    go x =
      ∈-ᴱ⁻-inj Γ' _ _
        (trans (restrict-tgt⁻ r x)
          (trans (cong (var-tgt′ r) refl)
            (trans (at-tgt (∈-ᴱ⁻ Γ x)) (sym (restrict-tgt⁻ r' x)))))
      where
        at-tgt : ∀ {A} → (t : Tgt Γ A) → var-tgt′ r t ≡ var-tgt′ r' t
        at-tgt (_ , y) = at h y

-- Renaming a variable is the variable the renaming sends it to: `var-tgt`
-- records the position, and the grade bound it recomputes is invisible to
-- `_≐ᵛ_`. Stated at an arbitrary bound so that the caller may present the
-- result with whichever bound its own typing supplies.

var-ren-≐ : ∀ {Γ Γ' A ρ} → (r : Ren Γ Γ') → (x : A ∈[ ρ ] Γ)
          → (f  : ¬ Eternal A → ρ ≾ᵣ uᵣ)
          → (f' : ¬ Eternal A → proj₁ (var-tgt r x) ≾ᵣ uᵣ)
          → V-rename r (var f x) ≐ᵛ var f' (proj₂ (var-tgt r x))
var-ren-≐ r x f f' with var-rename r x
... | _ , _ , y = var-≐

-- The same with the target supplied, for callers that have computed it.

var-ren-tgt-≐ : ∀ {Γ Γ' A ρ} → (r : Ren Γ Γ') → (x : A ∈[ ρ ] Γ)
              → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → {t : Tgt Γ' A}
              → var-tgt r x ≡ t → (f' : ¬ Eternal A → proj₁ t ≾ᵣ uᵣ)
              → V-rename r (var f x) ≐ᵛ var f' (proj₂ t)
var-ren-tgt-≐ r x f refl f' = var-ren-≐ r x f f'

------------------------------------------------------------------------
-- THE ACTION RESPECTS ACTING ALIKE
--
-- Induction on the term. At `var` the whole content is the hypothesis, the
-- grade bounds being irrelevant; the binding formers use `cong-ren-≐`, `handle`
-- uses `restrict-ren-≐`, and `unbox` stores `r ∘ʳ w`, related by `∘ʳ-≐`.
------------------------------------------------------------------------

mutual

  V-rename-≐ : ∀ {Γ Γ' A} {r r' : Ren Γ Γ'} → r ≐ʳ r'
             → (V : Γ ⊢V⦂ A) → V-rename r V ≐ᵛ V-rename r' V

  V-rename-≐ {r = r} {r' = r'} h (var f x)
    with var-rename r x | var-rename r' x | at h x
  ... | _ | _ | refl = var-≐
  V-rename-≐ h (const c)  = const-≐
  V-rename-≐ h ⋆          = ⋆-≐
  V-rename-≐ h ⦉ V , W ⦊   = pair-≐ (V-rename-≐ h V) (V-rename-≐ h W)
  V-rename-≐ h (lam M)    = lam-≐ (C-rename-≐ (cong-ren-≐ ([] ∷ _) h) M)

  C-rename-≐ : ∀ {Γ Γ' C} {r r' : Ren Γ Γ'} → r ≐ʳ r'
             → (M : Γ ⊢C⦂ C) → C-rename r M ≐ᶜ C-rename r' M

  C-rename-≐ h (return V) = return-≐ (V-rename-≐ h V)
  C-rename-≐ h (M ⨟ N) =
    seq-≐ (C-rename-≐ h M) (C-rename-≐ (cong-ren-≐ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-≐ h (V · W) = app-≐ (V-rename-≐ h V) (V-rename-≐ h W)
  C-rename-≐ h (match V `in M) =
    match-≐ (V-rename-≐ h V) (C-rename-≐ (cong-ren-≐ ([] ∷ _ ∷ _) h) M)
  C-rename-≐ h (absurd V) = absurd-≐ (V-rename-≐ h V)
  C-rename-≐ h (perform op V M) =
    perform-≐ (V-rename-≐ h V) (C-rename-≐ (cong-ren-≐ (_ ⟨ _ ⟩ ∷ _) h) M)
  C-rename-≐ h (delay τ M) =
    delay-≐ (C-rename-≐ (cong-ren-≐ ([] ⟨ _ ⟩) h) M)
  C-rename-≐ h (handle M `with H `in N) =
    handle-≐ (C-rename-≐ h M)
      (λ op ε'' Γ' →
         C-rename-≐ (cong-ren-≐ (_ ∷ _ ∷ _) (restrict-ren-≐ h)) (H op ε'' Γ'))
      (C-rename-≐ (cong-ren-≐ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-≐ h (unbox w V M) =
    unbox-≐ (∘ʳ-≐ h ≐ʳ-refl) (C-rename-≐ (cong-ren-≐ ([] ∷ _) h) M)
  C-rename-≐ h (box V M) =
    box-≐ (V-rename-≐ (cong-ren-≐ ([] ⟨ _ ⟩) h) V)
          (C-rename-≐ (cong-ren-≐ ([] ∷ _) h) M)
  C-rename-≐ h (coerce p M) = coerce-≐ (C-rename-≐ h M)

------------------------------------------------------------------------
-- FUNCTORIALITY
--
-- At the binding formers the two sides rename along `cong-ren (r₂ ∘ʳ r₁)` and
-- `cong-ren r₂ ∘ʳ cong-ren r₁`, at `unbox` along `(r₂ ∘ʳ r₁) ∘ʳ w` and
-- `r₂ ∘ʳ (r₁ ∘ʳ w)`: distinct renamings acting alike, so the statement is at
-- `_≐ᵛ_`/`_≐ᶜ_` and the proof leans on the laws above.
------------------------------------------------------------------------

mutual

  V-rename-∘ : ∀ {Γ Γ' Γ'' A} → (r₂ : Ren Γ' Γ'') → (r₁ : Ren Γ Γ')
             → (V : Γ ⊢V⦂ A)
             → V-rename (r₂ ∘ʳ r₁) V ≐ᵛ V-rename r₂ (V-rename r₁ V)

  V-rename-∘ r₂ r₁ (var f x) with var-rename r₁ x
  ... | _ , _ , y with var-rename r₂ y
  ...   | _ , _ , z = var-≐
  V-rename-∘ r₂ r₁ (const c) = const-≐
  V-rename-∘ r₂ r₁ ⋆         = ⋆-≐
  V-rename-∘ r₂ r₁ ⦉ V , W ⦊  = pair-≐ (V-rename-∘ r₂ r₁ V) (V-rename-∘ r₂ r₁ W)
  V-rename-∘ r₂ r₁ (lam M)   =
    lam-≐ (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ∷ _) r₂ r₁) M)
                    (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))

  C-rename-∘ : ∀ {Γ Γ' Γ'' C} → (r₂ : Ren Γ' Γ'') → (r₁ : Ren Γ Γ')
             → (M : Γ ⊢C⦂ C)
             → C-rename (r₂ ∘ʳ r₁) M ≐ᶜ C-rename r₂ (C-rename r₁ M)

  C-rename-∘ r₂ r₁ (return V) = return-≐ (V-rename-∘ r₂ r₁ V)
  C-rename-∘ r₂ r₁ (M ⨟ N) =
    seq-≐ (C-rename-∘ r₂ r₁ M)
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) N)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) N))
  C-rename-∘ r₂ r₁ (V · W) = app-≐ (V-rename-∘ r₂ r₁ V) (V-rename-∘ r₂ r₁ W)
  C-rename-∘ r₂ r₁ (match V `in M) =
    match-≐ (V-rename-∘ r₂ r₁ V)
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ∷ _ ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (absurd V) = absurd-≐ (V-rename-∘ r₂ r₁ V)
  C-rename-∘ r₂ r₁ (perform op V M) =
    perform-≐ (V-rename-∘ r₂ r₁ V)
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (delay τ M) =
    delay-≐ (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ⟨ _ ⟩) r₂ r₁) M)
                      (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (handle M `with H `in N) =
    handle-≐ (C-rename-∘ r₂ r₁ M)
      (λ op ε'' Γ' →
         ≐ᶜ-trans
           (C-rename-≐
             (≐ʳ-trans (cong-ren-≐ (_ ∷ _ ∷ _) (restrict-ren-∘-≐ r₂ r₁))
                       (cong-ren-∘-≐ (_ ∷ _ ∷ _) (restrict-ren r₂) (restrict-ren r₁)))
             (H op ε'' Γ'))
           (C-rename-∘ (cong-ren (restrict-ren r₂)) (cong-ren (restrict-ren r₁))
                       (H op ε'' Γ')))
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) N)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) N))
  C-rename-∘ r₂ r₁ (unbox w V M) =
    unbox-≐ (∘ʳ-assoc-≐ r₂ r₁ w)
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (box V M) =
    box-≐ (≐ᵛ-trans (V-rename-≐ (cong-ren-∘-≐ ([] ⟨ _ ⟩) r₂ r₁) V)
                    (V-rename-∘ (cong-ren r₂) (cong-ren r₁) V))
          (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ∷ _) r₂ r₁) M)
                    (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (coerce p M) = coerce-≐ (C-rename-∘ r₂ r₁ M)

------------------------------------------------------------------------
-- THE ACTION IS A CONGRUENCE
--
-- Renaming related terms gives related terms. Induction on the relation, not on
-- the term; `unbox` needs `∘ʳ-≐` on the stored renamings.
------------------------------------------------------------------------

mutual

  V-rename-cong : ∀ {Γ Γ' A} → (r : Ren Γ Γ') → {V V' : Γ ⊢V⦂ A}
                → V ≐ᵛ V' → V-rename r V ≐ᵛ V-rename r V'

  V-rename-cong r var-≐            = var-≐
  V-rename-cong r const-≐          = const-≐
  V-rename-cong r ⋆-≐              = ⋆-≐
  V-rename-cong r (pair-≐ eV eW)   =
    pair-≐ (V-rename-cong r eV) (V-rename-cong r eW)
  V-rename-cong r (lam-≐ eM)       = lam-≐ (C-rename-cong (cong-ren r) eM)

  C-rename-cong : ∀ {Γ Γ' C} → (r : Ren Γ Γ') → {M M' : Γ ⊢C⦂ C}
                → M ≐ᶜ M' → C-rename r M ≐ᶜ C-rename r M'

  C-rename-cong r (return-≐ eV)     = return-≐ (V-rename-cong r eV)
  C-rename-cong r (seq-≐ eM eN)     =
    seq-≐ (C-rename-cong r eM) (C-rename-cong (cong-ren r) eN)
  C-rename-cong r (app-≐ eV eW)     =
    app-≐ (V-rename-cong r eV) (V-rename-cong r eW)
  C-rename-cong r (match-≐ eV eM)   =
    match-≐ (V-rename-cong r eV) (C-rename-cong (cong-ren r) eM)
  C-rename-cong r (absurd-≐ eV)     = absurd-≐ (V-rename-cong r eV)
  C-rename-cong r (perform-≐ eV eM) =
    perform-≐ (V-rename-cong r eV) (C-rename-cong (cong-ren r) eM)
  C-rename-cong r (delay-≐ eM)      = delay-≐ (C-rename-cong (cong-ren r) eM)
  C-rename-cong r (handle-≐ eM eH eN) =
    handle-≐ (C-rename-cong r eM)
             (λ op ε'' Γ' → C-rename-cong (cong-ren (restrict-ren r)) (eH op ε'' Γ'))
             (C-rename-cong (cong-ren r) eN)
  C-rename-cong r (unbox-≐ hw eM)   =
    unbox-≐ (∘ʳ-≐ (≐ʳ-refl {r = r}) hw) (C-rename-cong (cong-ren r) eM)
  C-rename-cong r (coerce-≐ eM)     = coerce-≐ (C-rename-cong r eM)
  C-rename-cong r (box-≐ eV eM)     =
    box-≐ (V-rename-cong (cong-ren r) eV) (C-rename-cong (cong-ren r) eM)
