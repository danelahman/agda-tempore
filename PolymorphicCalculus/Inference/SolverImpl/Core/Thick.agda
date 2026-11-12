------------------------------------------------------------------
-- Thinning and thickening of variables                         --
--                                                              --
-- `thick i j` renames `j` into the scope without `i`, and is   --
-- `nothing` exactly when `j` is `i`; its section, thinning, is --
-- the standard library's `punchIn`. The per-sort wrappers are  --
-- the bare `Fin` operations on the counter of their sort.      --
------------------------------------------------------------------

open import Data.Fin.Base using (Fin; zero; suc; punchIn)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.SolverImpl.Core.Thick where

thick : ∀ {n} → Fin (suc n) → Fin (suc n) → Maybe (Fin n)
thick         zero    zero    = nothing
thick         zero    (suc j) = just j
thick {suc n} (suc i) zero    = just zero
thick {suc n} (suc i) (suc j) = map suc (thick i j)

map-just : ∀ {X Y : Set} → (f : X → Y) → (m : Maybe X) → {y : Y}
         → map f m ≡ just y → Σ[ x ∈ X ] ((m ≡ just x) × (f x ≡ y))
map-just f (just x) refl = x , refl , refl

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
