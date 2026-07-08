------------------------------------------------------------------------
-- The `[-]`-strong graded monad modelling the effects of the calculus. --
--                                                                    --
-- A graded monad `Tᵒ A ε`, graded by the *effect* grades `ε : E`,     --
-- equipped with the algebraic operations of the signature and with    --
-- explicit delays. It is the analogue of the free-monad-like monad of  --
-- the earlier (time-graded) formalisation, now graded by effects.      --
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
-- NOTE: effect handling, and the strength coherence laws that in the   --
-- earlier formalisation used the box *inverses* `ε⁻¹`/`δ⁻¹` (our box    --
-- is only lax), are deferred; see the TODO at the end.                 --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.GroundTypes

module DenotationalSemantics.Model.Monad
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S Cat Fut)
       where

open import Data.Nat using (ℕ)

open import Util.Equality

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
    ε-substᵀ-refl : ∀ {A ε} → ε-substᵀ {A} {ε} refl ≡ idᵐ
    ε-substᵀ-trans : ∀ {A ε ε' ε''} → (p : ε ≡ ε') → (q : ε' ≡ ε'')
                   → ε-substᵀ q ∘ᵐ ε-substᵀ p ≡ ε-substᵀ {A} (trans p q)

    -- Sub-effecting — the semantics of `coerce`. Covariant in the effect
    -- grade. It is *not* required to be a graded functor: the equational
    -- theory imposes only that `coerce` be a proof-irrelevant congruence
    -- (`coerce-cong`), and the operational semantics simply *peels it off*
    -- during execution (`⟨ S , coerce p M ⟩ ↝ ⟨ S , M ⟩`, refining the
    -- effect `ε' → ε`). Both are matched by `T-≤` here: peeling coerce
    -- corresponds to the definitional `⟦ coerce p M ⟧ = T-≤ p ⟦ M ⟧`. So
    -- `T-≤` needs only naturality, not `refl`/`trans` laws.

    T-≤ : ∀ {A ε₁ ε₂} → ε₁ ≾ₑ ε₂ → Tᵒ A ε₁ →ᵐ Tᵒ A ε₂

    -- Functoriality

    T-idᵐ : ∀ {A ε} → Tᶠ {A} {A} {ε} idᵐ ≡ idᵐ
    T-∘ᵐ : ∀ {A B C ε} → (g : B →ᵐ C) → (f : A →ᵐ B)
         → Tᶠ {A} {C} {ε} (g ∘ᵐ f) ≡ Tᶠ g ∘ᵐ Tᶠ f

    -- Unit and multiplication are natural

    ηᵀ-nat : ∀ {A B} → (f : A →ᵐ B) → ηᵀ ∘ᵐ f ≡ Tᶠ f ∘ᵐ ηᵀ
    μᵀ-nat : ∀ {A B ε ε'} → (f : A →ᵐ B)
           → μᵀ {ε = ε} {ε' = ε'} ∘ᵐ Tᶠ (Tᶠ f) ≡ Tᶠ f ∘ᵐ μᵀ

    -- T-≤ is natural (this holds on the nose; no refl/trans laws — see above)

    T-≤-nat : ∀ {A B ε ε'} → (f : A →ᵐ B) → (p : ε ≾ₑ ε')
            → Tᶠ f ∘ᵐ T-≤ {A} p ≡ T-≤ {B} p ∘ᵐ Tᶠ f

    -- Graded monad laws

    T-μ∘η≡id : ∀ {A ε}
             → μᵀ {A} {uₑ} {ε} ∘ᵐ ηᵀ {Tᵒ A ε}
             ≡ ε-substᵀ (sym (·ₑ-identityˡ ε))
    T-μ∘Tη≡id : ∀ {A ε}
              → μᵀ {A} {ε} {uₑ} ∘ᵐ Tᶠ (ηᵀ {A})
              ≡ ε-substᵀ (sym (·ₑ-identityʳ ε))
    T-μ∘μ≡μ∘Tμ : ∀ {A ε ε' ε''}
               → μᵀ {A} {ε} {ε' ·ₑ ε''} ∘ᵐ Tᶠ (μᵀ {A} {ε'} {ε''})
               ≡ ε-substᵀ (·ₑ-assoc ε ε' ε'') ∘ᵐ μᵀ ∘ᵐ μᵀ

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
               ≡ Tᶠ f ∘ᵐ delayᵀ τ

    opᵀ-nat : ∀ {A B ε} → (op : Op) → (f : A →ᵐ B)
            → opᵀ {ε = ε} op ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (Tᶠ f)))
            ≡ Tᶠ f ∘ᵐ opᵀ op

    -- Operations and delays are algebraic

    delayᵀ-algebraicity : ∀ {A ε' ε''} → (τ : ℕ)
                        → μᵀ {A} {of-natᵉ τ ·ₑ ε'} {ε''} ∘ᵐ delayᵀ {ε = ε'} τ
                        ≡ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε''))
                          ∘ᵐ delayᵀ τ
                          ∘ᵐ [ of-natʳ τ ]ᶠ (μᵀ {A} {ε'} {ε''})

    opᵀ-algebraicity : ∀ {A ε ε'} → (op : Op)
                     → μᵀ {A} {op-grade op ·ₑ ε} {ε'} ∘ᵐ opᵀ {ε = ε} op
                     ≡ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε'))
                       ∘ᵐ opᵀ op
                       ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (μᵀ {A} {ε} {ε'})))

    -- STRENGTH

    -- The [-]-strength: the box on the left is graded by `mapᵉ ε`.

    strᵀ : ∀ {A B ε} → [ mapᵉ ε ]ᵒ A ×ᵐ Tᵒ B ε →ᵐ Tᵒ (A ×ᵐ B) ε

    -- Strength is natural

    strᵀ-nat : ∀ {A A' B B' ε} → (f : A →ᵐ A') → (g : B →ᵐ B')
             → strᵀ {A'} {B'} ∘ᵐ mapˣᵐ ([ mapᵉ ε ]ᶠ f) (Tᶠ g)
             ≡ Tᶠ (mapˣᵐ f g) ∘ᵐ strᵀ {A} {B}

    -- Strength projects away

    strᵀ-sndᵐ : ∀ {A B ε} → Tᶠ sndᵐ ∘ᵐ strᵀ {A} {B} {ε} ≡ sndᵐ

-- TODO (deferred, see header):
--   * the strength unit / multiplication / associativity laws and the
--     algebraicity-of-operations-wrt-strength laws, reformulated for the
--     lax box (using `ε`, `δ`, `[]-≤`, and box monoidality instead of the
--     inverses `ε⁻¹`, `δ⁻¹` used in the time-graded formalisation);
--   * effect handling (`T-alg-of-handlerᵀ` and its laws).
