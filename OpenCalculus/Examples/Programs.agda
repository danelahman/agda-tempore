--------------------------------------------------------------------
-- Checking programs of several top-level definitions             --
--                                                                --
-- Each definition is inferred in the program context of those    --
-- before it and added to it with its principal type scheme       --
-- (`checkProgram`); a later definition uses an earlier one at    --
-- any instance of its scheme whose hypotheses its own entail.    --
--                                                                --
--   keep x  = delay 1; x                                         --
--   twice _ = keep (); keep true                                 --
--   late _  = keep (fun x → x)                                   --
--                                                                --
-- `keep` is used at two instances by `twice`, at `unit` and at   --
-- `bool`, each eternal. Where `keep`'s scheme requires its type  --
-- to be eternal (right-sided time), `late`, which keeps a        --
-- function, is rejected.                                         --
--                                                                --
-- The instances under `Programs/` check the schemes by `refl`.   --
--------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)

open import Grades.Durations using (Stepped)
open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec

open import OpenCalculus.Syntax.Scopes
open import OpenCalculus.Inference.SolverImpl.Enum using (OpEnum)

module OpenCalculus.Examples.Programs (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S)
  (st : Stepped (GradeSystem.Dur (LanguageSpec.Grades S))) where

open LanguageSpec S
open GradeSystemInterface Grades using (𝔻; of-durᵉ)

open import OpenCalculus.Syntax.Grades      S
open import OpenCalculus.Syntax.Types       S
open import OpenCalculus.Syntax.Contexts    S using (PCtx; ∅ᵖ; _∷ᵖ_; Θˢ; Qˢ; Xˢ)
open import OpenCalculus.Syntax.Raw         S
open import OpenCalculus.Programs.Syntax    S
open import OpenCalculus.Programs.Checking  S hints opEnum public

open import OpenCalculus.Examples.Scheme S public
open import OpenCalculus.Examples.Variables

------------------------------------------------------------------
-- The duration of `n` ticks, and its effect grade

⌜_⌝ : ℕ → 𝔻
⌜ n ⌝ = Stepped.fromℕ st n

⌜_⌝ᵉ : ∀ {Θ} → ℕ → EExp Θ
⌜ n ⌝ᵉ = econst (of-durᵉ ⌜ n ⌝)

------------------------------------------------------------------
-- The schemes of an accepted program, the first definition's first

schemes : PCtx → List ValueScheme
schemes ∅ᵖ       = []
schemes (Δ ∷ᵖ s) = schemes Δ ++ ((Θˢ s , Qˢ s , Xˢ s) ∷ [])

schemesOf : ∀ {P} → Checked P → Maybe (List ValueScheme)
schemesOf (accepted Δ _) = forceᵛ (schemes Δ)
schemesOf (rejected _)   = nothing

-- The position of the definition a rejected program fails at

rejectedAt : ∀ {P} → Checked P → Maybe ℕ
rejectedAt (accepted _ _) = nothing
rejectedAt (rejected k)   = just k

------------------------------------------------------------------
-- The definitions; a definition names an earlier one by its
-- position, from the first

keep : RawV ∅ˢ 0
keep = lam (delay ⌜ 1 ⌝ (return v₀))

twice : RawV ∅ˢ 0
twice = lam ((usedef 0 · ⋆) ⨟ (usedef 0 · true))

late : RawV ∅ˢ 0
late = lam (usedef 0 · lam (return v₀))

-- The programs

keep-twice : Program
keep-twice = ∅ᴾ ∷ᴾ keep ∷ᴾ twice

keep-late : Program
keep-late = ∅ᴾ ∷ᴾ keep ∷ᴾ late
