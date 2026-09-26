--------------------------------------------------------------------------
-- The counters shared by the worked count instances.                   --
--                                                                      --
-- One counter per operation, in the order `read`, `write`, `send`, and --
-- a grade written as its three coordinates.                            --
--------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Counts.Index where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec; []; _∷_)

open import Syntax.Grades.Example.Worked.Operations using (Op; read; write; send)

open import Syntax.Grades.Example.Time.RightSided using (𝕀ᵣ)
open import Syntax.Grades.Example.Time.LeftSided using (𝕀)

import Syntax.Grades.Example.Counts.AtLeast as AtLeast

open AtLeast using (atleast)

index : Op → Fin 3
index read  = zero
index write = suc zero
index send  = suc (suc zero)

-- a grade is written as its three coordinates

Quota : Set
Quota = Vec 𝕀ᵣ 3

⟪_,_,_⟫ᵐ : 𝕀ᵣ → 𝕀ᵣ → 𝕀ᵣ → Quota
⟪ r , w , s ⟫ᵐ = r ∷ w ∷ s ∷ []

Certain : Set
Certain = Vec 𝕀 3

⟪_,_,_⟫ˡ : ℕ → ℕ → ℕ → Certain
⟪ r , w , s ⟫ˡ = atleast r ∷ atleast w ∷ atleast s ∷ []
