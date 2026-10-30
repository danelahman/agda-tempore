------------------------------------------------------------------
-- Finiteness of the operation signature                        --
--                                                              --
-- The solver assumes an enumeration of the operation symbols,  --
-- to discharge the infinitary conjunction `⋀ᵒᵖ`: `All` over    --
-- the list turns the solutions at the listed operations into   --
-- the function `(op : Op) → …` satisfaction requires.          --
------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module PolymorphicCalculus.Inference.SolverImpl.Enum (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops

-- An enumeration of the operation symbols

record OpEnum : Set where
  constructor opEnum
  field
    ops      : List Op
    complete : (op : Op) → op ∈ ops

-- Pointwise witnesses along a list of operation symbols

data AllOp (P : Op → Set) : List Op → Set where
  []  : AllOp P []
  _∷_ : ∀ {op ops} → P op → AllOp P ops → AllOp P (op ∷ ops)

all-lookup : ∀ {P : Op → Set} {ops} → AllOp P ops → ∀ {op} → op ∈ ops → P op
all-lookup (p ∷ ps) (here refl) = p
all-lookup (p ∷ ps) (there m)   = all-lookup ps m

all-build : ∀ {P : Op → Set} → ((op : Op) → Maybe (P op))
          → (ops : List Op) → Maybe (AllOp P ops)
all-build g []       = just []
all-build g (x ∷ xs) with g x | all-build g xs
... | just p  | just ps = just (p ∷ ps)
... | _       | _       = nothing
