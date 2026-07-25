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

open import Data.Product

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

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

-- Reflexivity and transitivity. (Symmetry is the same recursion, omitted until
-- it is needed.)

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

-- The eternal restriction is compositional by definition.

restrict-ren-∘-≐ : ∀ {Γ Γ' Γ''} → (r₂ : Ren Γ' Γ'') → (r₁ : Ren Γ Γ')
                 → restrict-ren (r₂ ∘ʳ r₁)
                 ≐ʳ (restrict-ren r₂ ∘ʳ restrict-ren r₁)
restrict-ren-∘-≐ r₂ r₁ = ≐ʳ-refl

------------------------------------------------------------------------
-- LEMMAS TO PROVE
------------------------------------------------------------------------

postulate

  -- The eternal restriction respects acting alike. `restrict-ren` recurses on
  -- the *renaming*, so this is not a congruence of a function of `var-tgt`; it
  -- has to be related back through `∈-ᴱ`/`∈-ᴱ⁻`.

  restrict-ren-≐ : ∀ {Γ Γ'} {r r' : Ren Γ Γ'}
                 → r ≐ʳ r' → restrict-ren r ≐ʳ restrict-ren r'

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
