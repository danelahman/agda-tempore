open import Syntax.Grades
open import Util.BaseTypes

module OperationalSemantics.TopLevelPreservationTheorem (Grades : GradeSystem) (BTs : BaseTypes) where

open import OperationalSemantics.TopLevelOpSemantics (Grades) (BTs)

open GradeSystemInterface Grades

open import OperationalSemantics.State (Grades) (BTs)
open import OperationalSemantics.PreservationTheorem (Grades) (BTs)

open import Syntax.Contexts (Grades) (BTs)
open import Syntax.Language (Grades) (BTs)
open import Syntax.Renamings (Grades) (BTs)
open import Syntax.RenActions (Grades) (BTs)
open import Syntax.Substitutions (Grades) (BTs)
open import Syntax.Types (Grades) (BTs)

open import Data.Product

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] )

open import Util.Operations (Grades) (BTs)


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

open import Util.Monad

module MonadicTopLevelPreservationTheorem {monad : Monad} (MonadicOpSemantics : TopLevelMonadicOpSemantics monad) where

  open Monad monad

  open TopLevelMonadicOpSemantics MonadicOpSemantics

  data _⟿ₘ_ :  {C D : CType} → Config C → T (Config D) → Set where

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

  -- Invariants preserved by the monadic top-level small-step operational semantics
  m-top-level-step-invariants : ∀ {A B ε ε'}
                              → {S : 𝕊 []}
                              → {M : toCtx S  ⊢C⦂ A ‼ ε}
                              → {tconf : T (Config (B ‼ ε'))}
                              → ⟨ S , M ⟩ ⟿ₘ tconf
                              → T (A ≡ B
                                  × Σ[ S' ∈ 𝕊 [] ]
                                      (state-grade S' ·ᵣ mapᵉ ε' ≾ᵣ state-grade S ·ᵣ mapᵉ ε))

  m-top-level-step-invariants (↝-STEPₘ {S' = S'} step) =
    let inv = step-invariants step
    in returnM (proj₁ inv , S' , proj₂ inv)
  m-top-level-step-invariants {S = S} (OP-STEPₘ {op = op} {V = V}) =
    mon-op-sem op V >>=
      λ V' → returnM (refl ,
                      grade-pass S (mapᵉ (op-grade op)) , ≾ᵣ-reflexive (trans (·ᵣ-assoc _ _ _) (cong (state-grade S ·ᵣ_) (sym map-·ᵉ))))
