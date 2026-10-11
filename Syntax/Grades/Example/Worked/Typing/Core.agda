------------------------------------------------------------------------
-- The language of the typing examples.                               --
--                                                                    --
-- The alphabet of the sensor node, over an identity grade system:    --
-- effect grades and resource grades are the same monoid `G` and      --
-- `∣_∣ᵉ` is the identity, so `mapᵉ` reduces away. The instances vary --
-- `G`, the grade `opTime` assigns to each operation, and the         --
-- candidate values `wit` of a rigid.                                 --
--                                                                    --
-- There are two base types, differing in eternality: a `reading` is  --
-- the value of the sensor at the moment it was taken, and a `nodeid` --
-- is the identifier of the node. A `nodeid` variable is usable after --
-- any passage of time; a `reading` variable only under the bound     --
-- `ρ ≾ᵣ uᵣ` of `var`.                                                --
--                                                                    --
-- The example programs are in the instances. This module contains    --
-- the three ways of meeting the bound of `var`, the coercion lemma   --
-- that every instance instantiates, and the operation clauses passed --
-- to `handle`, whose typing is the same at every grade.              --
------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.BaseTypes
open import Syntax.Durations using (Duration)
open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.System.Identity

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; _≟ₒ_)

open import Util.Equality

module Syntax.Grades.Example.Worked.Typing.Core
  {D : Duration} (G : Grade D) (opTime : Op → Grade.Carrier G)
  (wit : ℕ → List (Grade.Carrier G) → List (Grade.Carrier G)) where

------------------------------------------------------------------------
-- The grades, with the candidates `wit` for a rigid

grades : GradeSystem
grades = identityGradeSystem G wit

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

baseTypes : BaseTypes
baseTypes = record
  { BaseType         = BT
  ; _≡ᵇ?_            = _≡ᴮ?_
  ; EternalBaseType  = EternalBT
  ; eternalBaseType? = eternalBT?
  ; BaseConstants    = λ _ → ℕ
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
reading-not-eternal (Baseₑ ())

nodeid-eternal : Eternal NodeId
nodeid-eternal = Baseₑ tt

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
-- Sub-effecting against unboxing
--
-- Sequencing types its continuation under the lock `⟨ mapᵉ ε ⟩`, where
-- `ε` is the grade the first part is *typed at* -- not the time it
-- takes -- and `handle`'s `in` part is locked the same way. So a
-- `coerce` on that first part changes what its continuation may claim,
-- and it can only take claims away; the instances exhibit the converse
-- failing.
--
-- An operation's own lock is not subject to any of this: `perform`
-- takes it from the signature, where no coercion reaches it.

coercion-only-closes : ∀ {ρ ρ'} {ε ε' : E}
                     → ε ≾ₑ ε'
                     → ρ' ·ᵣ mapᵉ ε' ≾ᵣ ρ
                     → ρ' ·ᵣ mapᵉ ε  ≾ᵣ ρ
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
-- `uᵣ ·ᵣ mapᵉ (op-grade op) ≾ᵣ mapᵉ (op-grade op)`, which the unit law
-- discharges at every grade.

forwarding : ∀ {Γ B} → (op : Op) → (ε'' : E)
           → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
             ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')
forwarding op ε'' =
  perform op (fresh-var ≾ᵣ-refl (Tl-∷ Hd))
                                     -- ⟨ op-grade op ⟩ ∷ arity op
    (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≾ᵣ-reflexive (·ᵣ-identityˡ _))
           (<:ᵛ-refl _)              -- ∷ arity op ⇒ B ‼ ε''
      (here · fresh-var ≾ᵣ-refl (Tl-∷ Hd)))

-- Resume, and then answer with the identifier the clause closed over.
-- The identifier is eternal, so it is still in scope after the
-- operation and after everything the continuation did.

identifying : (op : Op) → (ε'' : E)
            → Node ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ NodeId ‼ ε'')
              ⊢C⦂ NodeId ‼ (op-grade op ·ₑ ε'')
identifying op ε'' =
  ε-subst (cong (op-grade op ·ₑ_) (·ₑ-identityʳ ε''))
    (perform op (fresh-var ≾ᵣ-refl (Tl-∷ Hd))
                                     -- ⟨ op-grade op ⟩ ∷ arity op
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≾ᵣ-reflexive (·ᵣ-identityˡ _))
           (<:ᵛ-refl _)              -- ∷ arity op ⇒ NodeId ‼ ε''
        ((here · fresh-var ≾ᵣ-refl (Tl-∷ Hd))
          ⨟                          -- ⟨ ε'' ⟩ ∷ NodeId
            return (eternal-var nodeid-eternal
                     (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷
                       (Tl-⟨⟩ (Tl-∷ Hd)))))))))))))

-- Resume, and then answer with the reading the clause closed over. A
-- reading is not eternal, so `var` asks for its bound at the barrier
-- and at everything the clause has spent since -- the question `Node`
-- leaves to each instance.

reporting : (reading-crosses :
              (op : Op) → (ε'' : E)
              → uᵣ ·ᵣ ⊤ᵣ ·ᵣ mapᵉ (op-grade op) ·ᵣ mapᵉ ε'' ≾ᵣ uᵣ)
          → (op : Op) → (ε'' : E)
          → Node ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                  ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Reading ‼ ε'')
            ⊢C⦂ Reading ‼ (op-grade op ·ₑ ε'')
reporting reading-crosses op ε'' =
  ε-subst (cong (op-grade op ·ₑ_) (·ₑ-identityʳ ε''))
    (perform op (fresh-var ≾ᵣ-refl (Tl-∷ Hd))
                                     -- ⟨ op-grade op ⟩ ∷ arity op
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (≾ᵣ-reflexive (·ᵣ-identityˡ _))
           (<:ᵛ-refl _)              -- ∷ arity op ⇒ Reading ‼ ε''
        ((here · fresh-var ≾ᵣ-refl (Tl-∷ Hd))
          ⨟                          -- ⟨ ε'' ⟩ ∷ Reading
            return (fresh-var (reading-crosses op ε'')
                     (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷
                       (Tl-⟨⟩ Hd))))))))))))

-- Drop the continuation and return straight away. The clause still has
-- to be graded at `op-grade op ·ₑ ε''`, and a `return` is graded at
-- `uₑ`, so it exists exactly when the grade of doing nothing sits below
-- the grade of doing the operation and resuming.

discarding : ∀ {Γ}
           → (nothing-fits : (op : Op) → (ε'' : E) → uₑ ≾ₑ op-grade op ·ₑ ε'')
           → (op : Op) → (ε'' : E)
           → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Unit ‼ ε'')
             ⊢C⦂ Unit ‼ (op-grade op ·ₑ ε'')
discarding nothing-fits op ε'' = coerce (nothing-fits op ε'') (return ⋆)
