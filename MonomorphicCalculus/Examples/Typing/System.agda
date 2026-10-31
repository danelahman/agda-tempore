------------------------------------------------------------------------
-- The language of the typing examples, over a grade system.          --
--                                                                    --
-- The calculus over the language of the sensor node                  --
-- (`Language.Examples.SensorNode`): the grade system `S` and the     --
-- effect grade `opTime` assigns to each operation vary. `Core` is    --
-- the instance at an identity grade system.                          --
--                                                                    --
-- A `nodeid` variable is usable after any passage of time; a         --
-- `reading` variable only under the bound `ρ ≾ᵣ 𝟏ᵣ` of `var`.        --
--                                                                    --
-- Shared by the instances: the three ways of meeting the bound of    --
-- `var`, the coercion lemma, and the operation clauses passed to     --
-- `handle`, whose typing is the same at every grade.                 --
------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ) renaming (_<_ to _<ℕ_)
import Data.Nat.Properties as ℕₚ
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_; Dec; yes; no)

open import Language.BaseTypes
open import Grades.Durations using (Duration)
open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send; _≟ₒ_)

open import Util.Equality

module MonomorphicCalculus.Examples.Typing.System
  (S : GradeSystem) (opTime : Op → Grade.Carrier (GradeSystem.EGrade S)) where

open import Language.Examples.SensorNode S opTime public

open import MonomorphicCalculus.Syntax.Types    spec public
open import MonomorphicCalculus.Syntax.Contexts spec public
open import MonomorphicCalculus.Syntax.Terms    spec public

------------------------------------------------------------------------
-- Abbreviations

Reading NodeId : VType
Reading = Base reading
NodeId  = Base nodeid

reading-not-eternal : ¬ Et Reading
reading-not-eternal (Baseₑ ())

nodeid-eternal : Et NodeId
nodeid-eternal = Baseₑ tt

------------------------------------------------------------------------
-- Variables
--
-- `var` asks for `ρ ≾ᵣ 𝟏ᵣ` unless the type is eternal, `ρ` being the
-- time that has passed since the variable was bound. The three ways of
-- meeting it: the variable is the most recent binding, so no time has
-- passed; its type is eternal, so the bound is not asked for; or the
-- bound is supplied.

here : ∀ {Γ A} → Γ ∷ A ⊢ᵛ⦂ A
here = var (λ _ → ≾ᵣ-refl) Hd

eternal-var : ∀ {Γ A ρ} → Et A → A ∈[ ρ ] Γ → Γ ⊢ᵛ⦂ A
eternal-var et x = var (λ ¬et → ⊥-elim (¬et et)) x

fresh-var : ∀ {Γ A ρ} → ρ ≾ᵣ 𝟏ᵣ → A ∈[ ρ ] Γ → Γ ⊢ᵛ⦂ A
fresh-var p x = var (λ _ → p) x

------------------------------------------------------------------------
-- Sub-effecting against unboxing
--
-- Sequencing types its continuation under the lock `⟨ ∣ ε ∣ᵉ ⟩`, where
-- `ε` is the grade the first part is typed at, not the time it takes,
-- and `handle`'s `in` part is locked the same way. So a
-- `coerce` on that first part changes what its continuation may claim,
-- and it can only take claims away; the instances exhibit the converse
-- failing.
--
-- An operation's own lock is not subject to any of this: `perform`
-- takes it from the signature, where no coercion reaches it.

coercion-only-closes : ∀ {ρ ρ'} {ε ε' : E}
                     → ε ≾ₑ ε'
                     → ρ' ·ᵣ ∣ ε' ∣ᵉ ≾ᵣ ρ
                     → ρ' ·ᵣ ∣ ε ∣ᵉ  ≾ᵣ ρ
coercion-only-closes sub claim =
  ≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ (map-monotoneᵉ sub)) claim

------------------------------------------------------------------------
-- A context to handle in
--
-- Clauses see the ambient context behind the barrier lock `⟨ ⊤ᵣ ⟩`. In a
-- context holding both base types, the identifier crosses it by being
-- eternal; whether the reading does is a question about `⊤ᵣ`, which each
-- instance answers.

Node : Ctx
Node = [] ∷ NodeId ∷ Reading

------------------------------------------------------------------------
-- Operation clauses
--
-- A clause is typed at `op-grade op ·ₑ ε''`: it has the operation's own
-- grade to spend, and then the grade of the continuation it is given.
-- The continuation is boxed at the operation's grade, since it is what
-- runs once the operation has finished.

-- Perform the operation again and resume. The box is claimed under the
-- very lock the `perform` puts up, so the premise is
-- `𝟏ᵣ ·ᵣ ∣ op-grade op ∣ᵉ ≾ᵣ ∣ op-grade op ∣ᵉ`, which the unit law
-- discharges at every grade.

forwarding : ∀ {Γ B} → (op : Op) → (ε'' : E)
           → Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                 ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
             ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε'')
forwarding op ε'' =
  perform op (fresh-var ≾ᵣ-refl (Tl-∷ Hd))
                                     -- ⟨ op-grade op ⟩ ∷ arity op
    (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _))
           (<:ᵛ-refl _)              -- ∷ arity op ⇒ B ! ε''
      (here · fresh-var ≾ᵣ-refl (Tl-∷ Hd)))

-- Resume, and then answer with the identifier the clause closed over.
-- The identifier is eternal, so it is still in scope after the
-- operation and after everything the continuation did.

identifying : (op : Op) → (ε'' : E)
            → Node ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                    ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ NodeId ! ε'')
              ⊢ᶜ⦂ NodeId ! (op-grade op ·ₑ ε'')
identifying op ε'' =
  ε-≃ (·ₑ-cong ≃ₑ-refl (·ₑ-identityʳ ε''))
    (perform op (fresh-var ≾ᵣ-refl (Tl-∷ Hd))
                                     -- ⟨ op-grade op ⟩ ∷ arity op
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _))
           (<:ᵛ-refl _)              -- ∷ arity op ⇒ NodeId ! ε''
        ((here · fresh-var ≾ᵣ-refl (Tl-∷ Hd))
          ⨟                          -- ⟨ ε'' ⟩ ∷ NodeId
            return (eternal-var nodeid-eternal
                     (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷
                       (Tl-⟨⟩ (Tl-∷ Hd)))))))))))))

-- Resume, and then answer with the reading the clause closed over. A
-- reading is not eternal, so `var` asks for its bound at the barrier
-- and at everything the clause has spent since: the question `Node`
-- leaves to each instance.

reporting : (reading-crosses :
              (op : Op) → (ε'' : E)
              → 𝟏ᵣ ·ᵣ ⊤ᵣ ·ᵣ ∣ op-grade op ∣ᵉ ·ᵣ ∣ ε'' ∣ᵉ ≾ᵣ 𝟏ᵣ)
          → (op : Op) → (ε'' : E)
          → Node ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                  ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ Reading ! ε'')
            ⊢ᶜ⦂ Reading ! (op-grade op ·ₑ ε'')
reporting reading-crosses op ε'' =
  ε-≃ (·ₑ-cong ≃ₑ-refl (·ₑ-identityʳ ε''))
    (perform op (fresh-var ≾ᵣ-refl (Tl-∷ Hd))
                                     -- ⟨ op-grade op ⟩ ∷ arity op
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _))
           (<:ᵛ-refl _)              -- ∷ arity op ⇒ Reading ! ε''
        ((here · fresh-var ≾ᵣ-refl (Tl-∷ Hd))
          ⨟                          -- ⟨ ε'' ⟩ ∷ Reading
            return (fresh-var (reading-crosses op ε'')
                     (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷
                       (Tl-⟨⟩ Hd))))))))))))

-- Drop the continuation and return straight away. The clause still has
-- to be graded at `op-grade op ·ₑ ε''`, and a `return` is graded at
-- `𝟏ₑ`, so it exists exactly when the grade of doing nothing sits below
-- the grade of doing the operation and resuming.

discarding : ∀ {Γ}
           → (nothing-fits : (op : Op) → (ε'' : E) → 𝟏ₑ ≾ₑ op-grade op ·ₑ ε'')
           → (op : Op) → (ε'' : E)
           → Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                 ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ unit ! ε'')
             ⊢ᶜ⦂ unit ! (op-grade op ·ₑ ε'')
discarding nothing-fits op ε'' = coerce (nothing-fits op ε'') (return ⋆)
