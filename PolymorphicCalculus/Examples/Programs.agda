--------------------------------------------------------------------
-- Checking programs of several top-level definitions             --
--                                                                --
-- Each definition is inferred in the context of those before it  --
-- and added with its principal scheme (`checkProgram`).          --
--                                                                --
--   keep x  = delay 1; x                                         --
--   twice _ = keep (); keep true                                 --
--   late _  = keep (fun x → x)                                   --
--                                                                --
-- `twice` uses `keep` at two instances. Where `keep` requires    --
-- an eternal type, `late` is rejected. The instances under       --
-- `Programs/` check the schemes by `refl`.                       --
--------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)

open import Grades.Durations using (Stepped)
open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Examples.Programs (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S)
  (st : Stepped (GradeSystem.Dur (LanguageSpec.Grades S))) where

open LanguageSpec S
open GradeSystemInterface Grades using (𝔻; ιₑ)

open import PolymorphicCalculus.Syntax.Grades      S
open import PolymorphicCalculus.Syntax.Types       S
open import PolymorphicCalculus.Syntax.Contexts    S using (PCtx; ∅ᵖ; _∷ᵖ_; Θˢ; Qˢ; Xˢ)
open import PolymorphicCalculus.Syntax.Raw         S
open import PolymorphicCalculus.Programs.Syntax    S
open import PolymorphicCalculus.Programs.Checking  S hints opEnum public

open import PolymorphicCalculus.Examples.Scheme S public
open import PolymorphicCalculus.Examples.Variables

------------------------------------------------------------------
-- The duration of `n` ticks, and its effect grade

⌜_⌝ : ℕ → 𝔻
⌜ n ⌝ = Stepped.fromℕ st n

⌜_⌝ᵉ : ∀ {Θ} → ℕ → EExp Θ
⌜ n ⌝ᵉ = econst (ιₑ ⌜ n ⌝)

------------------------------------------------------------------
-- The schemes of an accepted program, in order

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
-- The definitions; `usedef k` names the one at position `k`, from 0

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
