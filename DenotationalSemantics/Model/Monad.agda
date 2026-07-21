------------------------------------------------------------------------
-- The `[-]`-strong graded monad modelling the effects of the calculus. --
--                                                                    --
-- A graded monad `Tᵒ A ε`, graded by the *effect* grades `ε : E`,     --
-- equipped with the algebraic operations of the signature and with    --
-- explicit delays. It is a free-monad-like monad built from those      --
-- operations and delays.                                              --
--                                                                    --
-- The novelty is that the operations, delays, and the strength all     --
-- mention the *box* modality graded by the *resource* projection       --
-- `mapᵉ` of the relevant effect grade — matching the calculus, whose   --
-- effectful formers advance the context by `⟨ mapᵉ ε ⟩`. In            --
-- particular the strength                                              --
--                                                                    --
--   strᵀ : [ mapᵉ ε ]ᵒ A ×ᵐ Tᵒ B ε →ᵐ Tᵒ (A ×ᵐ B) ε                    --
--                                                                    --
-- threads a box `[ mapᵉ ε ] A` along the worlds a grade-`ε`            --
-- computation reaches.                                                --
--                                                                    --
-- On-the-nose grade coercions along the monoid laws of `·ₑ` are        --
-- carried by `ε-substᵀ` (transport along `≡`); genuine sub-effecting   --
-- (the semantics of `coerce`) is `T-≤`, along the effect order `≾ₑ`.   --
--                                                                    --
-- The strength coherence laws are stated for the *lax* box (a counit    --
-- `ε` and comultiplication `δ`, but no inverses `ε⁻¹`/`δ⁻¹`).           --
-- Effect handling folds a handler — a family of clause *morphisms* — into --
-- a `T`-algebra; the clauses being morphisms (natural families) is what   --
-- makes them usable at every world the handled computation reaches.       --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes

module DenotationalSemantics.Model.Monad
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
       where

open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_; proj₁; proj₂; Σ; Σ-syntax)

open import Util.Equality

-- The eternal parameter threaded through effect handling is an `Eternalᵒ`
-- object; its box-coalgebra part (`necᵉ` and its laws) is what crosses locks.
open import DenotationalSemantics.Model.Modality.Eternal
  Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst Adj

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open Category Cat
open Future Fut
open GroundTypes GTy

record Monad : Set₁ where

  field

    -- MONAD STRUCTURE

    -- Functor

    Tᵒ : Obj → E → Obj
    Tᶠ : ∀ {A B ε} → A →ᵐ B → Tᵒ A ε →ᵐ Tᵒ B ε

    -- Unit and multiplication

    ηᵀ : ∀ {A} → A →ᵐ Tᵒ A uₑ
    μᵀ : ∀ {A ε ε'} → Tᵒ (Tᵒ A ε') ε →ᵐ Tᵒ A (ε ·ₑ ε')

    -- On-the-nose grade coercion (transport along ≡)

    ε-substᵀ : ∀ {A ε ε'} → ε ≡ ε' → Tᵒ A ε →ᵐ Tᵒ A ε'
    ε-substᵀ-refl : ∀ {A ε} → ε-substᵀ {A} {ε} refl ≈ᵐ idᵐ
    ε-substᵀ-trans : ∀ {A ε ε' ε''} → (p : ε ≡ ε') → (q : ε' ≡ ε'')
                   → ε-substᵀ q ∘ᵐ ε-substᵀ p ≈ᵐ ε-substᵀ {A} (trans p q)

    -- Sub-effecting — the semantics of `coerce`. Covariant in the effect
    -- grade, and functorial in it (`T-≤-refl` / `T-≤-trans` below), so that
    -- `⟦ coerce p M ⟧ = T-≤ p ⟦ M ⟧` is a genuine coercion: one that the
    -- denotational equality can see through, as it must, since execution
    -- peels coercions off (`⟨ S , coerce p M ⟩ ↝ ⟨ S , M ⟩`).

    T-≤ : ∀ {A ε₁ ε₂} → ε₁ ≾ₑ ε₂ → Tᵒ A ε₁ →ᵐ Tᵒ A ε₂

    -- Functoriality

    T-idᵐ : ∀ {A ε} → Tᶠ {A} {A} {ε} idᵐ ≈ᵐ idᵐ
    T-∘ᵐ : ∀ {A B C ε} → (g : B →ᵐ C) → (f : A →ᵐ B)
         → Tᶠ {A} {C} {ε} (g ∘ᵐ f) ≈ᵐ Tᶠ g ∘ᵐ Tᶠ f

    -- Tᶠ is a congruence

    T-congᶠ : ∀ {A B ε} {f g : A →ᵐ B} → f ≈ᵐ g → Tᶠ {A} {B} {ε} f ≈ᵐ Tᶠ g

    -- Unit and multiplication are natural

    ηᵀ-nat : ∀ {A B} → (f : A →ᵐ B) → ηᵀ ∘ᵐ f ≈ᵐ Tᶠ f ∘ᵐ ηᵀ
    μᵀ-nat : ∀ {A B ε ε'} → (f : A →ᵐ B)
           → μᵀ {ε = ε} {ε' = ε'} ∘ᵐ Tᶠ (Tᶠ f) ≈ᵐ Tᶠ f ∘ᵐ μᵀ

    -- T-≤ is natural (this holds on the nose; no refl/trans laws — see above)

    T-≤-nat : ∀ {A B ε ε'} → (f : A →ᵐ B) → (p : ε ≾ₑ ε')
            → Tᶠ f ∘ᵐ T-≤ {A} p ≈ᵐ T-≤ {B} p ∘ᵐ Tᶠ f

    -- Sub-effecting is functorial in the grade, the on-the-nose coercion
    -- being the special case at a reflexive witness. This is what makes
    -- `T-≤` a coercion rather than extra structure, and it is needed
    -- because reduction removes coercions
    -- (`⟨ S , coerce p M ⟩ ↝ ⟨ S , M ⟩`) and refines effect grades as it
    -- goes, so an equality preserved by reduction cannot see them.

    T-≤-refl : ∀ {A ε} → (p : ε ≾ₑ ε) → T-≤ {A} p ≈ᵐ idᵐ
    T-≤-trans : ∀ {A ε₁ ε₂ ε₃} → (p : ε₁ ≾ₑ ε₂) → (q : ε₂ ≾ₑ ε₃) → (r : ε₁ ≾ₑ ε₃)
              → T-≤ {A} q ∘ᵐ T-≤ {A} p ≈ᵐ T-≤ {A} r
    T-≤-≡ : ∀ {A ε ε'} → (e : ε ≡ ε')
          → ε-substᵀ {A} e ≈ᵐ T-≤ (≾ₑ-reflexive e)

    -- Sub-effecting commutes with the monad multiplication in the outer
    -- grade, and with the strength (which also relaxes the box's grade,
    -- the box being contravariant in it).

    T-≤-μᵀ : ∀ {A ε₁ ε₂ ε'} → (p : ε₁ ≾ₑ ε₂)
           → μᵀ {A} {ε₂} {ε'} ∘ᵐ T-≤ p
           ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ p) ∘ᵐ μᵀ {A} {ε₁} {ε'}


    -- Graded monad laws

    T-μ∘η≡id : ∀ {A ε}
             → μᵀ {A} {uₑ} {ε} ∘ᵐ ηᵀ {Tᵒ A ε}
             ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε))
    T-μ∘Tη≡id : ∀ {A ε}
              → μᵀ {A} {ε} {uₑ} ∘ᵐ Tᶠ (ηᵀ {A})
              ≈ᵐ ε-substᵀ (sym (·ₑ-identityʳ ε))
    T-μ∘μ≡μ∘Tμ : ∀ {A ε ε' ε''}
               → μᵀ {A} {ε} {ε' ·ₑ ε''} ∘ᵐ Tᶠ (μᵀ {A} {ε'} {ε''})
               ≈ᵐ ε-substᵀ (·ₑ-assoc ε ε' ε'') ∘ᵐ μᵀ ∘ᵐ μᵀ

    -- EFFECTS

    -- Operations and delays

    delayᵀ : ∀ {A ε} → (τ : ℕ)
           → [ of-natʳ τ ]ᵒ (Tᵒ A ε) →ᵐ Tᵒ A (of-natᵉ τ ·ₑ ε)

    opᵀ : ∀ {A ε} → (op : Op)
        → ⟦ param op ⟧ᵍ ×ᵐ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ A ε)
        →ᵐ Tᵒ A (op-grade op ·ₑ ε)

    -- Operations and delays are natural

    delayᵀ-nat : ∀ {A B ε} → (τ : ℕ) → (f : A →ᵐ B)
               → delayᵀ {ε = ε} τ ∘ᵐ [ of-natʳ τ ]ᶠ (Tᶠ f)
               ≈ᵐ Tᶠ f ∘ᵐ delayᵀ τ

    -- Sub-effecting the delayed computation is sub-effecting the delay. This is
    -- the *inner*-grade counterpart of `T-≤-μᵀ`, and it is what a multi-step
    -- reduction needs: composing two steps substitutes the target
    -- configuration's coercion *under* the Kleisli bind, and only `DELAY`
    -- produces a transition that is not `ηᵀ`.

    delayᵀ-≤ : ∀ {A ε ε'} → (τ : ℕ) → (p : ε ≾ₑ ε')
             → delayᵀ {A} {ε'} τ ∘ᵐ [ of-natʳ τ ]ᶠ (T-≤ p)
             ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ p) ∘ᵐ delayᵀ {A} {ε} τ

    opᵀ-nat : ∀ {A B ε} → (op : Op) → (f : A →ᵐ B)
            → opᵀ {ε = ε} op ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (Tᶠ f)))
            ≈ᵐ Tᶠ f ∘ᵐ opᵀ op

    -- Sub-effecting the continuation is sub-effecting the operation, the
    -- counterpart of `delayᵀ-≤` for `opᵀ`. Sound because handlers are
    -- ambivalent in the residual grade (`Monoᵀ`): the fold picks the clause by
    -- that grade, so a coercion pushed under an operation is unobservable.

    opᵀ-≤ : ∀ {A ε ε'} → (op : Op) → (p : ε ≾ₑ ε')
          → opᵀ {A} {ε'} op ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ p)))
          ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ p) ∘ᵐ opᵀ {A} {ε} op

    -- Delays *are* the passage of time, not observable nodes: a delay by no
    -- time is no delay, and two consecutive delays are the one delay by the
    -- sum. In the zero case the box `[ of-natʳ 0 ]` is the unit-graded box,
    -- whose counit `ε` extracts; in the sum case the box `[ of-natʳ (τ₁ + τ₂) ]`
    -- splits into the two delays' boxes by the comultiplication `δ`. Both are
    -- stated with the grade relaxation `[]-≤` at the reflexive witness of the
    -- grade algebra's `of-nat` laws, since `of-natʳ` is only *propositionally*
    -- a monoid morphism.

    delayᵀ-zero : ∀ {A ε'}
                → delayᵀ {A} {ε'} 0
                ≈ᵐ ε-substᵀ (sym (trans (cong (_·ₑ ε') of-natᵉ-zero)
                                        (·ₑ-identityˡ ε')))
                  ∘ᵐ ε
                  ∘ᵐ []-≤ (≾ᵣ-reflexive (sym of-natʳ-zero))

    delayᵀ-plus : ∀ {A ε'} → (τ₁ τ₂ : ℕ)
                → delayᵀ {A} {of-natᵉ τ₂ ·ₑ ε'} τ₁
                    ∘ᵐ [ of-natʳ τ₁ ]ᶠ (delayᵀ {A} {ε'} τ₂)
                    ∘ᵐ δ
                    ∘ᵐ []-≤ (≾ᵣ-reflexive (sym of-natʳ-plus))
                ≈ᵐ ε-substᵀ (trans (cong (_·ₑ ε') of-natᵉ-plus)
                                   (·ₑ-assoc (of-natᵉ τ₁) (of-natᵉ τ₂) ε'))
                  ∘ᵐ delayᵀ {A} {ε'} (τ₁ + τ₂)

    -- Operations and delays are algebraic

    delayᵀ-algebraicity : ∀ {A ε' ε''} → (τ : ℕ)
                        → μᵀ {A} {of-natᵉ τ ·ₑ ε'} {ε''} ∘ᵐ delayᵀ {ε = ε'} τ
                        ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε''))
                          ∘ᵐ delayᵀ τ
                          ∘ᵐ [ of-natʳ τ ]ᶠ (μᵀ {A} {ε'} {ε''})

    opᵀ-algebraicity : ∀ {A ε ε'} → (op : Op)
                     → μᵀ {A} {op-grade op ·ₑ ε} {ε'} ∘ᵐ opᵀ {ε = ε} op
                     ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε'))
                       ∘ᵐ opᵀ op
                       ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (μᵀ {A} {ε} {ε'})))

    -- STRENGTH

    -- The [-]-strength: the box on the left is graded by `mapᵉ ε`.

    strᵀ : ∀ {A B ε} → [ mapᵉ ε ]ᵒ A ×ᵐ Tᵒ B ε →ᵐ Tᵒ (A ×ᵐ B) ε

    -- Strength is natural

    strᵀ-nat : ∀ {A A' B B' ε} → (f : A →ᵐ A') → (g : B →ᵐ B')
             → strᵀ {A'} {B'} ∘ᵐ mapˣᵐ ([ mapᵉ ε ]ᶠ f) (Tᶠ g)
             ≈ᵐ Tᶠ (mapˣᵐ f g) ∘ᵐ strᵀ {A} {B}

    -- Strength commutes with sub-effecting. Relaxing the tree's grade also
    -- relaxes the box's, contravariantly (`[]-≤`): a box that is available
    -- `mapᵉ ε'`-far ahead is in particular available `mapᵉ ε`-far ahead.

    strᵀ-≤ : ∀ {A B ε ε'} → (p : ε ≾ₑ ε')
           → strᵀ {A} {B} {ε'} ∘ᵐ mapˣᵐ idᵐ (T-≤ p)
           ≈ᵐ T-≤ p ∘ᵐ strᵀ {A} {B} {ε} ∘ᵐ mapˣᵐ ([]-≤ (map-monotoneᵉ p)) idᵐ

    -- Strength projects away

    strᵀ-sndᵐ : ∀ {A B ε} → Tᶠ sndᵐ ∘ᵐ strᵀ {A} {B} {ε} ≈ᵐ sndᵐ

    -- Strength coherence laws. Because the box is only *lax* (no counit /
    -- comultiplication inverses `ε⁻¹` / `δ⁻¹`), the unit and multiplication
    -- laws keep the box on the *input* and eliminate it on the output via
    -- the counit `ε` (unit law) or split it via the comultiplication `δ`
    -- (multiplication law).

    -- Unit: strength on a returned value extracts the boxed component (at
    -- the reflexive world) and returns the pair. The box grade is `mapᵉ uₑ`,
    -- coerced to `uᵣ` for the counit along `map-uᵉ`.

    strᵀ-ηᵀ : ∀ {A B}
            → strᵀ {A} {B} {uₑ} ∘ᵐ mapˣᵐ idᵐ ηᵀ
            ≈ᵐ ηᵀ {A ×ᵐ B} ∘ᵐ mapˣᵐ (ε ∘ᵐ []-≤ (≾ᵣ-reflexive (sym map-uᵉ))) idᵐ

    -- Multiplication: threading the box through two monad layers agrees with
    -- threading it once at the combined grade, after splitting the box with
    -- `δ` along `map-·ᵉ`.

    strᵀ-μᵀ : ∀ {A B ε ε'}
            → strᵀ {A} {B} {ε ·ₑ ε'} ∘ᵐ mapˣᵐ idᵐ (μᵀ {B} {ε} {ε'})
            ≈ᵐ μᵀ {A ×ᵐ B} {ε} {ε'}
              ∘ᵐ Tᶠ (strᵀ {A} {B} {ε'})
              ∘ᵐ strᵀ {[ mapᵉ ε' ]ᵒ A} {Tᵒ B ε'} {ε}
              ∘ᵐ mapˣᵐ (δ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym map-·ᵉ))) idᵐ

    -- Associativity with the product: box monoidality `[]-monoidal`
    -- distributes the box over the pair.

    strᵀ-assoc : ∀ {A B C ε}
               → Tᶠ ×ᵐ-assoc ∘ᵐ strᵀ {A ×ᵐ B} {C} {ε}
                 ∘ᵐ mapˣᵐ []-monoidal idᵐ ∘ᵐ ×ᵐ-assoc⁻¹
               ≈ᵐ strᵀ {A} {B ×ᵐ C} {ε} ∘ᵐ mapˣᵐ idᵐ (strᵀ {B} {C} {ε})

    -- Operations are algebraic with respect to the strength.

    strᵀ-delayᵀ-algebraicity : ∀ {A B ε} → (τ : ℕ)
      → strᵀ {A} {B} {of-natᵉ τ ·ₑ ε} ∘ᵐ mapˣᵐ idᵐ (delayᵀ {B} {ε} τ)
      ≈ᵐ delayᵀ τ
        ∘ᵐ [ of-natʳ τ ]ᶠ (strᵀ {A} {B} {ε})
        ∘ᵐ []-monoidal
        ∘ᵐ mapˣᵐ (δ ∘ᵐ []-≤ (≾ᵣ-reflexive
             (sym (trans map-·ᵉ (cong (_·ᵣ mapᵉ ε) map-of-natᵉ))))) idᵐ

    -- The operation is algebraic with respect to the strength. The box
    -- `[ mapᵉ (op-grade op) ] A` is split off the strengthened argument and
    -- pushed into the operation's continuation, where it is paired with the
    -- arity value before strengthening the sub-computation.

    strᵀ-opᵀ-algebraicity : ∀ {A B ε} → (op : Op)
      → strᵀ {A} {B} {op-grade op ·ₑ ε} ∘ᵐ mapˣᵐ idᵐ (opᵀ {B} {ε} op)
      ≈ᵐ opᵀ op
        ∘ᵐ mapˣᵐ idᵐ
            ([ mapᵉ (op-grade op) ]ᶠ
               (   map⇒ᵐ idᵐ (strᵀ {A} {B} {ε})
                ∘ᵐ exp-strᵐ)
             ∘ᵐ []-monoidal
             ∘ᵐ mapˣᵐ (δ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym map-·ᵉ))) idᵐ)
        ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ

  -- EFFECT HANDLING

  -- A handler is parameterised by an *eternal* object `P` (the interpretation
  -- of the eternal part `Γ ᴱ` of the ambient context it closes over). It
  -- assigns to every operation `op` and residual effect grade `ε''` a clause:
  -- given `P`, the parameter, and the operation's boxed continuation
  -- `[ mapᵉ (op-grade op) ] (arity ⇒ Tᵒ A ε'')`, it produces a computation.
  -- The clauses are *morphisms* (natural families), hence usable at every
  -- world the handled computation reaches; `P` being eternal (a `Eternalᵒ`,
  -- `necᵉ`) is what lets it be carried *under* the box at `delay`/`op` nodes,
  -- across the passage of time, without moving the handler.

  Clausesᵀ : Obj → Obj → Set
  Clausesᵀ P A = (op : Op) → (ε'' : E)
             → P ×ᵐ (⟦ param op ⟧ᵍ ×ᵐ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ A ε''))
                 →ᵐ Tᵒ A (op-grade op ·ₑ ε'')

  -- A handler's clauses must be *ambivalent* in the residual grade `ε''`:
  -- coercing the boxed continuation's residual equals coercing the clause's
  -- output. The residual grade is fixed by the call site, not inspected by the
  -- clause, so this is exactly the parametricity a handler is meant to have.
  --
  -- It is bundled into the handler rather than assumed law-by-law because the
  -- fold must respect it to be a morphism at all: sub-effecting may be pushed
  -- under an operation, and the fold selects the clause by the residual grade.
  -- It is what makes both the fold and `μ` monotone in the inner grade.

  Monoᵀ : ∀ {P A} → Clausesᵀ P A → Set
  Monoᵀ {P} {A} cl = ∀ (op : Op) {εa εb} → (q : εa ≾ₑ εb)
                   → cl op εb ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ
                         ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q))))
                   ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ cl op εa

  Handlerᵀ : Obj → Obj → Set
  Handlerᵀ P A = Σ[ cl ∈ Clausesᵀ P A ] Monoᵀ cl

  clauseᵀ : ∀ {P A} → Handlerᵀ P A → Clausesᵀ P A
  clauseᵀ = proj₁

  field

    -- Folding a handler into a `T`-algebra parameterised by `P`: reinterpret
    -- every operation of the tree by the corresponding clause, keeping delays
    -- as delays and returning the leaf value (regraded). The parameter `P` is
    -- threaded alongside the tree.

    T-alg-of-handlerᵀ : ∀ {P A ε ε'} → Eternalᵒ P → Handlerᵀ P A
                      → P ×ᵐ Tᵒ (Tᵒ A ε') ε →ᵐ Tᵒ A (ε ·ₑ ε')

    -- It is an algebra for the monad's structure: it computes `η`, `delay`,
    -- and `op` by, respectively, returning (discarding `P`), re-delaying
    -- (carrying `P` under the delay by `necᵉ`), and applying the matching
    -- clause (carrying `P` into the folded continuation by `necᵉ`).

    T-alg-of-handlerᵀ-ηᵀ : ∀ {P A ε'} → (bc : Eternalᵒ P) → (h : Handlerᵀ P A)
                         → T-alg-of-handlerᵀ bc h ∘ᵐ mapˣᵐ idᵐ (ηᵀ {Tᵒ A ε'})
                         ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε')) ∘ᵐ sndᵐ

    T-alg-of-handlerᵀ-delayᵀ : ∀ {P A ε' ε''} → (τ : ℕ) → (bc : Eternalᵒ P) → (h : Handlerᵀ P A)
                             → T-alg-of-handlerᵀ bc h ∘ᵐ mapˣᵐ idᵐ (delayᵀ {Tᵒ A ε''} {ε'} τ)
                             ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε''))
                               ∘ᵐ delayᵀ τ
                               ∘ᵐ [ of-natʳ τ ]ᶠ (T-alg-of-handlerᵀ bc h)
                               ∘ᵐ []-monoidal
                               ∘ᵐ mapˣᵐ (Eternalᵒ.necᵉ bc {of-natʳ τ}) idᵐ

    T-alg-of-handlerᵀ-opᵀ : ∀ {P A ε' ε''} → (op : Op) → (bc : Eternalᵒ P) → (h : Handlerᵀ P A)
                          → T-alg-of-handlerᵀ bc h ∘ᵐ mapˣᵐ idᵐ (opᵀ {Tᵒ A ε''} {ε'} op)
                          ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε' ε''))
                            ∘ᵐ clauseᵀ h op (ε' ·ₑ ε'')
                            ∘ᵐ ⟨ fstᵐ
                               , ⟨ fstᵐ ∘ᵐ sndᵐ
                                 ,   [ mapᵉ (op-grade op) ]ᶠ
                                       (curryᵐ (T-alg-of-handlerᵀ bc h
                                         ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ
                                            , appᵐ ∘ᵐ ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ))
                                   ∘ᵐ []-monoidal
                                   ∘ᵐ mapˣᵐ (Eternalᵒ.necᵉ bc {mapᵉ (op-grade op)}) idᵐ
                                   ∘ᵐ ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ

    -- The fold commutes with sub-effecting in the *outer* grade — the same
    -- shape as `T-≤-μᵀ`, and needed for the same reason: an inductive
    -- hypothesis' coercion has to escape the handling composite.

    T-alg-of-handlerᵀ-≤ : ∀ {P A ε₁ ε₂ ε'} → (bc : Eternalᵒ P) → (h : Handlerᵀ P A) → (p : ε₁ ≾ₑ ε₂)
                        → T-alg-of-handlerᵀ {P} {A} {ε₂} {ε'} bc h ∘ᵐ mapˣᵐ idᵐ (T-≤ p)
                        ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ p) ∘ᵐ T-alg-of-handlerᵀ {P} {A} {ε₁} {ε'} bc h

    -- It also commutes with sub-effecting in the *inner* grade — landing on
    -- `·ₑ-monoʳ`, dual to the outer law's `·ₑ-monoˡ`. No premise is needed: the
    -- handler carries its own ambivalence (`Monoᵀ`), which is what lets the
    -- coercion escape an operation the fold is reinterpreting.

    T-alg-of-handlerᵀ-≤ⁱ : ∀ {P A ε ε₁' ε₂'} → (bc : Eternalᵒ P) → (h : Handlerᵀ P A)
                         → (p : ε₁' ≾ₑ ε₂')
                         → T-alg-of-handlerᵀ {P} {A} {ε} {ε₂'} bc h ∘ᵐ mapˣᵐ idᵐ (Tᶠ (T-≤ p))
                         ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ p) ∘ᵐ T-alg-of-handlerᵀ {P} {A} {ε} {ε₁'} bc h

    -- And it *is* an algebra: folding a two-layer tree is folding the outer
    -- layer after folding each inner one. Threading `P` into the inner folds
    -- uses the monad's strength together with `necᵉ` (to box `P` at the grade
    -- the strength requires); a copy of `P` is kept for the outer fold.

    T-alg-of-handlerᵀ-μᵀ : ∀ {P A ε ε' ε''} → (bc : Eternalᵒ P) → (h : Handlerᵀ P A)
                         → T-alg-of-handlerᵀ {P} {A} {ε ·ₑ ε'} {ε''} bc h
                             ∘ᵐ mapˣᵐ idᵐ (μᵀ {Tᵒ A ε''} {ε} {ε'})
                         ≈ᵐ ε-substᵀ (sym (·ₑ-assoc ε ε' ε''))
                             ∘ᵐ T-alg-of-handlerᵀ {P} {A} {ε} {ε' ·ₑ ε''} bc h
                             ∘ᵐ ⟨ fstᵐ
                                ,   Tᶠ (T-alg-of-handlerᵀ {P} {A} {ε'} {ε''} bc h)
                                  ∘ᵐ strᵀ
                                  ∘ᵐ mapˣᵐ (Eternalᵒ.necᵉ bc {mapᵉ ε}) idᵐ ⟩ᵐ

    -- Naturality in the eternal parameter: reindexing the handler along a
    -- `[_]`-coalgebra morphism `f : P' →ᵐ P` (`[ ρ ]ᶠ f ∘ necᵉ' ≈ necᵉ ∘ f`,
    -- so `f` commutes with the necessitation threaded through the fold) equals
    -- reindexing the fold's parameter by `f`. This is what lets the fold
    -- transport its eternal context along a renaming/substitution — hence it is
    -- what the handler's interpretation needs to be stable under those.

    T-alg-of-handlerᵀ-natᴾ : ∀ {P P' A ε ε'} → (bc : Eternalᵒ P) → (bc' : Eternalᵒ P')
                           → (f : P' →ᵐ P)
                           → (∀ {ρ} → [ ρ ]ᶠ f ∘ᵐ Eternalᵒ.necᵉ bc' {ρ}
                                     ≈ᵐ Eternalᵒ.necᵉ bc {ρ} ∘ᵐ f)
                           → (h : Handlerᵀ P A) → (h' : Handlerᵀ P' A)
                           → (∀ op ε'' → clauseᵀ h' op ε''
                                       ≈ᵐ clauseᵀ h op ε'' ∘ᵐ mapˣᵐ f idᵐ)
                           → T-alg-of-handlerᵀ {P'} {A} {ε} {ε'} bc' h'
                           ≈ᵐ T-alg-of-handlerᵀ {P} {A} {ε} {ε'} bc h ∘ᵐ mapˣᵐ f idᵐ

    -- The fold is a congruence in the handler: pointwise-equal clauses fold to
    -- equal algebras. Needed to rewrite a renamed/substituted handler into the
    -- reindexed form that `natᴾ` consumes.

    T-alg-of-handlerᵀ-cong : ∀ {P A ε ε'} → (bc : Eternalᵒ P) → {h h' : Handlerᵀ P A}
                           → (∀ op ε'' → clauseᵀ h op ε'' ≈ᵐ clauseᵀ h' op ε'')
                           → T-alg-of-handlerᵀ {P} {A} {ε} {ε'} bc h
                           ≈ᵐ T-alg-of-handlerᵀ {P} {A} {ε} {ε'} bc h'

  -- DERIVED PROPERTIES

  -- Naturality of the strength in its boxed component alone (the monadic
  -- component being the identity), which is how the environment-threading
  -- formers push a reindexing through `strᵀ`.

  strᵀ-natˡ : ∀ {A A' B ε} → (f : A →ᵐ A')
            → Tᶠ (mapˣᵐ f (idᵐ {B})) ∘ᵐ strᵀ {A} {B} {ε}
            ≈ᵐ strᵀ {A'} {B} {ε} ∘ᵐ mapˣᵐ ([ mapᵉ ε ]ᶠ f) idᵐ
  strᵀ-natˡ f =
    ≈ᵐ-trans (≈ᵐ-sym (strᵀ-nat f idᵐ))
             (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ∘ᵐ-congˡ T-idᵐ ⟩ᵐ-cong))
