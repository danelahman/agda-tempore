------------------------------------------------------------------------
-- Worked instances of the regular grade of upper bounds.             --
--                                                                    --
-- A grade is a non-empty regular set of runs containing every run of --
-- the computation. Weakening is inclusion; unlike in                 --
-- `Worked.Traces.Subsets.RightSided`, the greatest grade permits     --
-- every run without absorbing products. Literals are extended        --
-- regular expressions, and an empty literal is rejected.             --
--                                                                    --
-- Every claim is established by the decision procedure of the grade. --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Regular.RightSided where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; replicate)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Op : Set where
  read send : Op

code : Op → Fin 2
code read = zero
code send = suc zero

code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
code-injective {read} {read} _ = refl
code-injective {send} {send} _ = refl

open import Relation.Nullary.Decidable using (isYes)
open import Syntax.Grades using (module Grade)
open import Syntax.Grades.Regular.Decide 3 using (nonempty?)
open import Syntax.Grades.Example.Traces.Regular.RightSided Op 2 code code-injective
open Syntax.Grades.Grade right-sided using (_≾?_; _≡?_)

read·tick²≾⊤ : isYes ((operationᴿ read ·ᴿ of-nat 2) ≾? ⊤) ≡ true
read·tick²≾⊤ = refl

send⋠read : isYes (operationᴿ send ≾? operationᴿ read) ≡ false
send⋠read = refl

of-nat-2+3 : isYes ((of-nat 2 ·ᴿ of-nat 3) ≡? of-nat 5) ≡ true
of-nat-2+3 = refl

-- `⊤` is not absorbing

⊤⋠tick·⊤ : isYes (⊤ ≾? (of-nat 1 ·ᴿ ⊤)) ≡ false
⊤⋠tick·⊤ = refl

-- literals

distrib : isYes (⌊ (‵op read ∣ ‵op send) · delay 1 ⌋
                 ≡? ⌊ ‵op read · delay 1 ∣ ‵op send · delay 1 ⌋) ≡ true
distrib = refl

-- the runs that never send

no-send : Expr
no-send = Σ * & ~ (Σ * · ‵op send · Σ *)

reads≾no-send : isYes (⌊ (‵op read · delay 2) * ⌋ ≾? ⌊ no-send ⌋) ≡ true
reads≾no-send = refl

send⋠no-send : isYes (⌊ ‵op read · ‵op send ⌋ ≾? ⌊ no-send ⌋) ≡ false
send⋠no-send = refl

de-morgan : isYes (⌊ ~ (‵op read ∣ ‵op send) ⌋ ≡? ⌊ ~ ‵op read & ~ ‵op send ⌋) ≡ true
de-morgan = refl

-- `‵op send & ~ ‵op send` is empty, so `⌊ ‵op send & ~ ‵op send ⌋` is
-- rejected

empty : isYes (nonempty? (elab (‵op send & ~ ‵op send)) (elab-wf (‵op send & ~ ‵op send)))
      ≡ false
empty = refl
