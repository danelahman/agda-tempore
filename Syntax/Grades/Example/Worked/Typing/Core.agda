------------------------------------------------------------------------
-- The language the typing examples are written in.                    --
--                                                                     --
-- The sensor node's alphabet, over an identity grade system: effect    --
-- grades and resource grades are the same monoid `G` and `∣_∣ᵉ` is the --
-- identity, so `mapᵉ` reduces away and each rule can be read off       --
-- directly. What varies between the instances is `G` and the grade     --
-- `opTime` gives each operation.                                       --
--                                                                     --
-- There are two base types, and they differ in eternality: a `reading` --
-- is the value of the sensor at the moment it was taken, a `nodeid` is --
-- the node's own identifier. So a `nodeid` variable crosses any amount --
-- of time passage unconditionally, and a `reading` variable only with  --
-- the bound `ρ ≾ᵣ uᵣ` that `var` asks for.                            --
--                                                                     --
-- The example programs are not here: each instance writes its own out  --
-- in full, at its own grades, with every side condition discharged at  --
-- the point the rule imposes it. What this module keeps is what the    --
-- programs are written *with* -- the three ways of meeting `var`'s     --
-- bound, and the operation clauses handed to `handle`, whose typing is --
-- intricate and identical at every grade.                              --
------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.BaseTypes
open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.System.Identity

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; _≟ₒ_)

open import Util.Equality

module Syntax.Grades.Example.Worked.Typing.Core
  (G : Grade) (opTime : Op → Grade.Carrier G) where

------------------------------------------------------------------------
-- The grades

grades : GradeSystem
grades = identityGradeSystem G

open GradeSystemInterface grades public

------------------------------------------------------------------------
-- Base types
--
-- A reading is the sensor's value at the moment it was taken, so it is
-- not eternal; the node's identifier is.

data BT : Set where
  reading : BT
  nodeid  : BT

_≡ᴮ?_ : (b b' : BT) → Dec (b ≡ b')
reading ≡ᴮ? reading = yes refl
reading ≡ᴮ? nodeid  = no λ ()
nodeid  ≡ᴮ? reading = no λ ()
nodeid  ≡ᴮ? nodeid  = yes refl

EternalBT : BT → Set
EternalBT reading = ⊥
EternalBT nodeid  = ⊤

eternalBT? : (b : BT) → Dec (EternalBT b)
eternalBT? reading = no λ ()
eternalBT? nodeid  = yes tt

eternalBT-irrelevant : ∀ {b} → (p q : EternalBT b) → p ≡ q
eternalBT-irrelevant {nodeid} tt tt = refl

baseTypes : BaseTypes
baseTypes = record
  { BaseType                   = BT
  ; _≡ᵇ?_                      = _≡ᴮ?_
  ; EternalBaseType            = EternalBT
  ; eternalBaseType?           = eternalBT?
  ; eternalBaseType-irrelevant = eternalBT-irrelevant
  ; BaseConstants              = λ _ → ℕ
  }

open import Syntax.GroundTypes grades baseTypes

------------------------------------------------------------------------
-- The operation signature
--
-- `read` takes nothing and produces a reading; `write` and `send` each
-- consume one and produce nothing. `opTime` grades them.

operations : Operations grades baseTypes
operations = record
  { Op       = Op
  ; _≟ₒ_     = _≟ₒ_
  ; param    = param'
  ; arity    = arity'
  ; op-grade = opTime
  }
  where
    param' : Op → GType
    param' read  = Unit
    param' write = Base reading
    param' send  = Base reading

    arity' : Op → GType
    arity' read  = Base reading
    arity' write = Unit
    arity' send  = Unit

spec : LanguageSpec
spec = record
  { Grades = grades
  ; BTs    = baseTypes
  ; Ops    = operations
  }

open Operations operations public using (param; arity; op-grade)

open import Syntax.Types    spec public
open import Syntax.Contexts spec public
open import Syntax.Language spec public

------------------------------------------------------------------------
-- Abbreviations

Reading NodeId : VType
Reading = Base reading
NodeId  = Base nodeid

reading-not-eternal : ¬ Eternal Reading
reading-not-eternal (Baseₑ _ ())

nodeid-eternal : Eternal NodeId
nodeid-eternal = Baseₑ nodeid tt

------------------------------------------------------------------------
-- Variables
--
-- `var` asks for `ρ ≾ᵣ uᵣ` unless the type is eternal, `ρ` being the
-- time that has passed since the variable was bound. The three ways of
-- meeting it: the variable is the most recent binding, so no time has
-- passed; its type is eternal, so the bound is not asked for; or the
-- bound is supplied.

here : ∀ {Γ A} → Γ ∷ A ⊢V⦂ A
here = var (λ _ → ≾ᵣ-refl) Hd

eternal-var : ∀ {Γ A ρ} → Eternal A → A ∈[ ρ ] Γ → Γ ⊢V⦂ A
eternal-var et x = var (λ ¬et → ⊥-elim (¬et et)) x

fresh-var : ∀ {Γ A ρ} → ρ ≾ᵣ uᵣ → A ∈[ ρ ] Γ → Γ ⊢V⦂ A
fresh-var p x = var (λ _ → p) x

------------------------------------------------------------------------
-- A context to handle in
--
-- Clauses close over the eternal part of the ambient context. In a
-- context holding both base types, that is the identifier alone, so a
-- clause may mention it and cannot mention the reading.

Node : Ctx
Node = [] ∷ NodeId ∷ Reading

eternal-part : Node ᴱ ≡ [] ∷ NodeId
eternal-part = refl

------------------------------------------------------------------------
-- Operation clauses
--
-- A clause is typed at `op-grade op ·ₑ ε''`: it has the operation's own
-- grade to spend, and then the grade of the continuation it is given.
-- The continuation is boxed at the operation's grade, since it is what
-- runs once the operation has finished.

-- Perform the operation again and resume. The box is claimed under the
-- very lock the `perform` puts up, so the premise is
-- `uᵣ ·ᵣ mapᵉ (op-grade op) ≾ᵣ mapᵉ (op-grade op)`, which the unit law
-- discharges at every grade.

forwarding : ∀ {Γ B} → (op : Op) → (ε'' : E)
           → Γ ᴱ ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
             ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')
forwarding op ε'' =
  perform op (fresh-var ≾ᵣ-refl (Tl-∷ Hd))
    (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≾ᵣ-reflexive (·ᵣ-identityˡ _))
      (here · fresh-var ≾ᵣ-refl (Tl-∷ Hd)))

-- Resume, and then answer with the identifier the clause closed over.
-- The identifier is eternal, so it is still in scope after the
-- operation and after everything the continuation did.

identifying : (op : Op) → (ε'' : E)
            → Node ᴱ ∷ type-of-gtype (param op)
                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ NodeId ‼ ε'')
              ⊢C⦂ NodeId ‼ (op-grade op ·ₑ ε'')
identifying op ε'' =
  ε-subst (cong (op-grade op ·ₑ_) (·ₑ-identityʳ ε''))
    (perform op (fresh-var ≾ᵣ-refl (Tl-∷ Hd))
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≾ᵣ-reflexive (·ᵣ-identityˡ _))
        ((here · fresh-var ≾ᵣ-refl (Tl-∷ Hd))
          ⨟ return (eternal-var nodeid-eternal
                     (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ Hd)))))))))))

-- Drop the continuation and return straight away. The clause still has
-- to be graded at `op-grade op ·ₑ ε''`, and a `return` is graded at
-- `uₑ`, so it exists exactly when the grade of doing nothing sits below
-- the grade of doing the operation and resuming.

discarding : ∀ {Γ}
           → (nothing-fits : (op : Op) → (ε'' : E) → uₑ ≾ₑ op-grade op ·ₑ ε'')
           → (op : Op) → (ε'' : E)
           → Γ ᴱ ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Unit ‼ ε'')
             ⊢C⦂ Unit ‼ (op-grade op ·ₑ ε'')
discarding nothing-fits op ε'' = coerce (nothing-fits op ε'') (return ⋆)
