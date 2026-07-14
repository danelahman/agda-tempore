open import Data.Product

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.TopLevelPreservationTheorem (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem  S
open import OperationalSemantics.State                S
open import OperationalSemantics.TopLevelOpSemantics  S

open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.RenActions    S
open import Syntax.Renamings     S
open import Syntax.Substitutions S
open import Syntax.Types         S


-- Top-level small-step operational semantics aka Preservation theorem
--
-- Note: This top-level semantics uses the pure semantics of algebraic operations

module PureTopLevelPreservationTheorem (OpSemantics : TopLevelOpSemantics) where

  open TopLevelOpSemantics OpSemantics

  data _⟿_ :  {C D : CType} → Config C → Config D → Set where

    -- Step according to the ordinary small-step semantics
    ↝-STEP : ∀ {A B ε ε'}
           → {S S' : 𝕊 []}
           → {M : (toCtx S ⊢C⦂ A ‼ ε)}
           → {N : (toCtx S' ⊢C⦂ B ‼ ε')}
           → ⟨ S , M ⟩ ↝ ⟨ S' , N ⟩
           → ⟨ S , M ⟩ ⟿ ⟨ S' , N ⟩

    -- Run a top-level implementation of an algebraic operation
    OP-STEP : ∀ {A ε op}
            → {S : 𝕊 []} 
            → {V : (toCtx S) ⊢V⦂ type-of-gtype (param op)} 
            → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε} 
            → ⟨ S , perform op V M ⟩ ⟿
              ⟨ grade-pass S (mapᵉ (op-grade op)) , M [ Hd ↦ op-sem op V ]c ⟩

  -- Reflexive-transitive closure: a run of the top-level machine.

  infixr 5 _◅ᵗ_

  data _⟿*_ : ∀ {A ε ε'} → Config (A ‼ ε) → Config (A ‼ ε') → Set where
    ε*ᵗ  : ∀ {A ε} {cf : Config (A ‼ ε)}
         → cf ⟿* cf
    _◅ᵗ_ : ∀ {A ε₁ ε₂ ε₃}
         → {cf₁ : Config (A ‼ ε₁)} → {cf₂ : Config (A ‼ ε₂)} → {cf₃ : Config (A ‼ ε₃)}
         → cf₁ ⟿ cf₂ → cf₂ ⟿* cf₃ → cf₁ ⟿* cf₃

  -- invariants preserved by the top-level small-step operational semantics
  -- in particular, running a top-level implementation of an algebraic operation
  -- results in an equality S' · ε' ≡ S · ε
  
  top-level-step-invariants : ∀ {A B ε ε'}
                            → {S S' : 𝕊 []}
                            → {M : toCtx S ⊢C⦂ A ‼ ε}
                            → {M' : toCtx S' ⊢C⦂ B ‼ ε'}
                            → ⟨ S , M ⟩ ⟿ ⟨ S' , M' ⟩
                            → A ≡ B
                            × state-grade S' ·ᵣ mapᵉ ε' ≾ᵣ state-grade S ·ᵣ mapᵉ ε

  top-level-step-invariants (↝-STEP step) =
    step-invariants step
  top-level-step-invariants {S = S} OP-STEP =
    refl ,
    ≾ᵣ-reflexive
      (trans
        (·ᵣ-assoc _ _ _)
        (cong (state-grade S ·ᵣ_) (sym map-·ᵉ)))


-- Note: This top-level semantics uses the monadic semantics of algebraic operations
--
-- The runtime monad is graded by the effect grades, so a transition records the
-- time its runtime computation takes. An `↝-STEPₘ` performs no runtime
-- computation and so is graded `uₑ`; an `OP-STEPₘ` runs the operation's
-- implementation, whose grade is `op-grade op` — the same time the rule locks
-- into the state. The two can no longer disagree (`m-top-level-step-time`).

open import Util.Monad

module MonadicTopLevelPreservationTheorem
         {monad : GradedMonad EGrade}
         (MonadicOpSemantics : TopLevelMonadicOpSemantics monad) where

  open GradedMonad monad

  open TopLevelMonadicOpSemantics MonadicOpSemantics

  data _⟿ₘ_ : {δ : E} → {C D : CType} → Config C → T δ (Config D) → Set where

    -- Step according to the ordinary small-step semantics
    ↝-STEPₘ : ∀ {A B ε ε'}
            → {S S' : 𝕊 []}
            → {M : (toCtx S ⊢C⦂ A ‼ ε)}
            → {M' : (toCtx S' ⊢C⦂ B ‼ ε')}
            → ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩
            → ⟨ S , M ⟩ ⟿ₘ returnM (⟨ S' , M' ⟩)

    -- Run a top-level implementation of an algebraic operation
    OP-STEPₘ : ∀ {A ε op}
             → {S : 𝕊 []}
             → {V : (toCtx S) ⊢V⦂ type-of-gtype (param op)}
             → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
             → ⟨ S , perform op V M ⟩ ⟿ₘ
               (mon-op-sem op V >>= λ V' → returnM (⟨ grade-pass S (mapᵉ (op-grade op)) , M [ Hd ↦ V' ]c ⟩))

  -- The grade of a transition: the time its runtime computation takes.

  m-top-level-grade : ∀ {A B ε ε' δ}
                    → {S : 𝕊 []}
                    → {M : toCtx S ⊢C⦂ A ‼ ε}
                    → {tconf : T δ (Config (B ‼ ε'))}
                    → ⟨ S , M ⟩ ⟿ₘ tconf → E
  m-top-level-grade {δ = δ} _ = δ

  -- The time an operation's implementation takes IS the time the rule locks
  -- into the state. This is what grading the runtime monad buys: `op-grade op`
  -- is spent by the implementation, not merely asserted by the rule.
  --
  -- (There is no such law for `↝-STEPₘ`, nor should there be: its runtime
  -- computation is `returnM`, of grade `uₑ`, while the state may still advance
  -- — a `DELAY` passes time without any runtime computation taking it.)

  op-step-time : ∀ {A ε op}
               → {S : 𝕊 []}
               → {V : (toCtx S) ⊢V⦂ type-of-gtype (param op)}
               → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩
                      ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
               → state-grade (grade-pass S (mapᵉ (op-grade op)))
               ≡ state-grade S
                   ·ᵣ mapᵉ (m-top-level-grade (OP-STEPₘ {V = V} {M = M}))
  op-step-time {op = op} {S = S} =
    cong (state-grade S ·ᵣ_)
         (trans (sym (·ᵣ-identityʳ (mapᵉ (op-grade op))))
                (trans (cong (mapᵉ (op-grade op) ·ᵣ_) (sym map-uᵉ))
                       (sym map-·ᵉ)))

  -- Invariants preserved by the monadic top-level small-step operational semantics
  m-top-level-step-invariants : ∀ {A B ε ε' δ}
                              → {S : 𝕊 []}
                              → {M : toCtx S  ⊢C⦂ A ‼ ε}
                              → {tconf : T δ (Config (B ‼ ε'))}
                              → ⟨ S , M ⟩ ⟿ₘ tconf
                              → T δ (A ≡ B
                                     × Σ[ S' ∈ 𝕊 [] ]
                                         (state-grade S' ·ᵣ mapᵉ ε' ≾ᵣ state-grade S ·ᵣ mapᵉ ε))

  m-top-level-step-invariants (↝-STEPₘ {S' = S'} step) =
    let inv = step-invariants step
    in returnM (proj₁ inv , S' , proj₂ inv)
  m-top-level-step-invariants {S = S} (OP-STEPₘ {op = op} {V = V}) =
    mon-op-sem op V >>=
      λ V' → returnM (refl ,
                      grade-pass S (mapᵉ (op-grade op)) , ≾ᵣ-reflexive (trans (·ᵣ-assoc _ _ _) (cong (state-grade S ·ᵣ_) (sym map-·ᵉ))))
