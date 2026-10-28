------------------------------------------------------------------
-- Single-binding substitutions                                 --
--                                                              --
-- `A forᵗ α` is the substitution that eliminates the type      --
-- variable `α`, sending it to `A` and every other variable of  --
-- its sort to its thickening. It is a `Subst`, subject to the  --
-- substitution algebra of `OpenCalculus.Syntax.Subst`;         --
-- its components at the two other sorts are the variable       --
-- constructors, the extension `_+ty` leaving their counters    --
-- unchanged.                                                   --
------------------------------------------------------------------

open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Inference.SolverImpl.Core.For (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import OpenCalculus.Syntax.Grades S
open import OpenCalculus.Syntax.Types  S
open import OpenCalculus.Syntax.Subst  S

open import OpenCalculus.Inference.SolverImpl.Core.Thick

infix 40 _forᵗ_ _forʳ_ _forᵉ_

_forᵗ_ : ∀ {Θ} → OVType Θ → TyVar (Θ +ty) → Subst (Θ +ty) Θ
_forᵗ_ {Θ} A α = sub (λ β → maybe′ tvar A (thickᵗ {Θ} α β))
                     (λ i → rvar i)
                     (λ i → evar i)

_forʳ_ : ∀ {Θ} → RExp Θ → RVar (Θ +r) → Subst (Θ +r) Θ
_forʳ_ {Θ} ρ i = sub (λ α → tvar α)
                     (λ j → maybe′ rvar ρ (thickʳ {Θ} i j))
                     (λ j → evar j)

_forᵉ_ : ∀ {Θ} → EExp Θ → EVar (Θ +e) → Subst (Θ +e) Θ
_forᵉ_ {Θ} ε i = sub (λ α → tvar α)
                     (λ j → rvar j)
                     (λ j → maybe′ evar ε (thickᵉ {Θ} i j))

for-hitᵗ : ∀ {Θ} → (A : OVType Θ) → (α : TyVar (Θ +ty)) → sTy (A forᵗ α) α ≡ A
for-hitᵗ {Θ} A α = cong (maybe′ tvar A) (thick-refl {nTy Θ} α)

for-hitʳ : ∀ {Θ} → (ρ : RExp Θ) → (i : RVar (Θ +r)) → sR (ρ forʳ i) i ≡ ρ
for-hitʳ {Θ} ρ i = cong (maybe′ rvar ρ) (thick-refl {nR Θ} i)

for-hitᵉ : ∀ {Θ} → (ε : EExp Θ) → (i : EVar (Θ +e)) → sE (ε forᵉ i) i ≡ ε
for-hitᵉ {Θ} ε i = cong (maybe′ evar ε) (thick-refl {nE Θ} i)

for-missᵗ : ∀ {Θ} → (A : OVType Θ) → (α : TyVar (Θ +ty)) → (β : TyVar Θ)
          → sTy (A forᵗ α) (thinᵗ {Θ} α β) ≡ tvar β
for-missᵗ {Θ} A α β = cong (maybe′ tvar A) (thick-thin {nTy Θ} α β)

for-missʳ : ∀ {Θ} → (ρ : RExp Θ) → (i : RVar (Θ +r)) → (j : RVar Θ)
          → sR (ρ forʳ i) (thinʳ {Θ} i j) ≡ rvar j
for-missʳ {Θ} ρ i j = cong (maybe′ rvar ρ) (thick-thin {nR Θ} i j)

for-missᵉ : ∀ {Θ} → (ε : EExp Θ) → (i : EVar (Θ +e)) → (j : EVar Θ)
          → sE (ε forᵉ i) (thinᵉ {Θ} i j) ≡ evar j
for-missᵉ {Θ} ε i j = cong (maybe′ evar ε) (thick-thin {nE Θ} i j)
