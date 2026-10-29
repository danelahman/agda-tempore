------------------------------------------------------------------
-- Checking a program                                           --
--                                                              --
-- Each definition is checked in the program context of those   --
-- before it, by inference for values with a satisfying         --
-- instance (`checkᵛ`), and the program context is extended by  --
-- its principal type scheme. An accepted program carries its   --
-- program judgement; a rejected one names the position of the  --
-- first definition not established.                            --
------------------------------------------------------------------

open import Data.Nat using (ℕ)

open import Language.Spec

open import Util.Equality

open import Grades.Hints using (SystemHints)
open import OpenCalculus.Syntax.Scopes
open import OpenCalculus.Inference.SolverImpl.Enum using (OpEnum)

module OpenCalculus.Programs.Checking (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S) where

open import OpenCalculus.Syntax.Contexts        S
open import OpenCalculus.Inference.Principality S using (module PrincipalSchemeᵛ)
open import OpenCalculus.Inference.Values       S hints opEnum
open import OpenCalculus.Programs.Syntax        S
open import OpenCalculus.Programs.Typing        S

data Checked (P : Program) : Set where
  accepted : (Δ : PCtx) → ⊢ᴾ P ⦂ Δ → Checked P
  rejected : ℕ → Checked P

checkProgram : (P : Program) → Checked P
checkProgram ∅ᴾ = accepted ∅ᵖ ∅ᴾ
checkProgram (P ∷ᴾ V) with checkProgram P
... | rejected k = rejected k
... | accepted Δ t with checkᵛ Δ V
...   | untypable       = rejected (lenᴾ P)
...   | unestablished p = rejected (lenᴾ P)
...   | stuck           = rejected (lenᴾ P)
...   | established p s = accepted (Δ ∷ᵖ _) (t ∷ᴾ accepted p s)
