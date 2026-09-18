------------------------------------------------------------------
-- Thinning and thickening of variables                          --
--                                                               --
-- `thick i j` renames `j` into the scope with `i` removed, and  --
-- is `nothing` exactly when `i` and `j` are the same variable.   --
-- Its section is the standard library's `punchIn`, which plays   --
-- the role of thinning. The `Maybe`-valued `thick` is used in    --
-- place of `punchOut`, whose disequality argument would have to  --
-- be manufactured at every call site.                            --
--                                                               --
-- The per-sort wrappers read the counter of a `Scope` that the   --
-- corresponding extension bumps; the other two counters are      --
-- untouched, so each wrapper is the bare `Fin` operation and the --
-- three `Fin` lemmas below apply to it verbatim.                 --
--                                                              --
-- Follows McBride's First-Order Unification by Structural      --
-- Recursion (JFP 2003).                                        --
------------------------------------------------------------------

open import Data.Fin.Base using (Fin; zero; suc; punchIn)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Util.Equality

open import Inference.Scopes

module Inference.SolverImpl.Core.Thick where

--------------------------------------------------------------
-- Thickening                                                --
--------------------------------------------------------------

thick : ∀ {n} → Fin (suc n) → Fin (suc n) → Maybe (Fin n)
thick         zero    zero    = nothing
thick         zero    (suc j) = just j
thick {suc n} (suc i) zero    = just zero
thick {suc n} (suc i) (suc j) = map suc (thick i j)

--------------------------------------------------------------
-- Inversion of `map` on `Maybe`                             --
--------------------------------------------------------------

map-just : ∀ {X Y : Set} → (f : X → Y) → (m : Maybe X) → {y : Y}
         → map f m ≡ just y → Σ[ x ∈ X ] ((m ≡ just x) × (f x ≡ y))
map-just f (just x) refl = x , refl , refl

--------------------------------------------------------------
-- The three characterising lemmas                           --
--------------------------------------------------------------

-- A variable is thick at itself

thick-refl : ∀ {n} → (i : Fin (suc n)) → thick i i ≡ nothing
thick-refl         zero    = refl
thick-refl {suc n} (suc i) = cong (map suc) (thick-refl i)

-- Thickening undoes thinning

thick-thin : ∀ {n} → (i : Fin (suc n)) → (j : Fin n) → thick i (punchIn i j) ≡ just j
thick-thin         zero    j       = refl
thick-thin {suc n} (suc i) zero    = refl
thick-thin {suc n} (suc i) (suc j) = cong (map suc) (thick-thin i j)

-- A successful thickening identifies its argument

thick-just : ∀ {n} → (i j : Fin (suc n)) → (k : Fin n)
           → thick i j ≡ just k → j ≡ punchIn i k
thick-just         zero    zero    k ()
thick-just         zero    (suc j) k refl = refl
thick-just {suc n} (suc i) zero    k refl = refl
thick-just {suc n} (suc i) (suc j) k q with map-just suc (thick i j) q
... | k' , q' , refl = cong suc (thick-just i j k' q')

--------------------------------------------------------------
-- Per-sort wrappers                                         --
--------------------------------------------------------------

thinᵗ : ∀ {Θ} → TyVar (Θ +ty) → TyVar Θ → TyVar (Θ +ty)
thinᵗ {Θ} α β = punchIn {nTy Θ} α β

thinʳ : ∀ {Θ} → RVar (Θ +r) → RVar Θ → RVar (Θ +r)
thinʳ {Θ} i j = punchIn {nR Θ} i j

thinᵉ : ∀ {Θ} → EVar (Θ +e) → EVar Θ → EVar (Θ +e)
thinᵉ {Θ} i j = punchIn {nE Θ} i j

thickᵗ : ∀ {Θ} → TyVar (Θ +ty) → TyVar (Θ +ty) → Maybe (TyVar Θ)
thickᵗ {Θ} α β = thick {nTy Θ} α β

thickʳ : ∀ {Θ} → RVar (Θ +r) → RVar (Θ +r) → Maybe (RVar Θ)
thickʳ {Θ} i j = thick {nR Θ} i j

thickᵉ : ∀ {Θ} → EVar (Θ +e) → EVar (Θ +e) → Maybe (EVar Θ)
thickᵉ {Θ} i j = thick {nE Θ} i j
