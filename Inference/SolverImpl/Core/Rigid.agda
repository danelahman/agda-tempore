------------------------------------------------------------------
-- Strengthening away a rigid effect-grade variable               --
--                                                                --
-- A rigid variable is one the unifier may not bind, so on leaving --
-- the scope that declares it every expression that is to survive  --
-- must be free of it. `str*` are the partial strengthenings that  --
-- check exactly that, thickening at the rigid's position.         --
--                                                                --
-- The rigid is declared as the newest effect-grade variable, but  --
-- the existentials nested inside its scope are allocated on top   --
-- of it, so by the time the scope is left the rigid sits at an    --
-- arbitrary position `j`. `popˢ j` is the substitution that moves  --
-- it back to the newest position and shifts everything else up;   --
-- `str-pop*` say that a successful strengthening is exactly the   --
-- inverse of that move followed by the weakening.                 --
------------------------------------------------------------------

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′) renaming (map to mmap)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import Inference.Scopes

module Inference.SolverImpl.Core.Rigid (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Inference.Open.Grades S
open import Inference.Open.Types  S
open import Inference.Open.Subst  S

open import Inference.SolverImpl.Core.Thick

--------------------------------------------------------------
-- Pairing two partial results                               --
--------------------------------------------------------------

zip₂ : ∀ {X Y Z : Set} → (X → Y → Z) → Maybe X → Maybe Y → Maybe Z
zip₂ f (just x) (just y) = just (f x y)
zip₂ f _        _        = nothing

zip₂-just : ∀ {X Y Z : Set} → (f : X → Y → Z)
          → (m : Maybe X) → (m' : Maybe Y) → {z : Z} → zip₂ f m m' ≡ just z
          → Σ[ x ∈ X ] Σ[ y ∈ Y ] ((m ≡ just x) × (m' ≡ just y) × (f x y ≡ z))
zip₂-just f (just x) (just y) refl = x , y , refl , refl , refl
zip₂-just f (just x) nothing  ()
zip₂-just f nothing  m'       ()

--------------------------------------------------------------
-- The partial strengthenings                                --
--------------------------------------------------------------

strᵉ : ∀ {Ψ} → EVar (Ψ +e) → EExp (Ψ +e) → Maybe (EExp Ψ)
strᵉ {Ψ} j (evar k)   = mmap evar (thickᵉ {Ψ} j k)
strᵉ     j (econst c) = just (econst c)
strᵉ     j (ε ·̂ₑ ε')  = zip₂ _·̂ₑ_ (strᵉ j ε) (strᵉ j ε')

strʳ : ∀ {Ψ} → EVar (Ψ +e) → RExp (Ψ +e) → Maybe (RExp Ψ)
strʳ j (rvar i)   = just (rvar i)
strʳ j (rconst c) = just (rconst c)
strʳ j (ρ ·̂ᵣ ρ')  = zip₂ _·̂ᵣ_ (strʳ j ρ) (strʳ j ρ')
strʳ j ∣ ε ∣̂ᵉ     = mmap ∣_∣̂ᵉ (strᵉ j ε)

mutual

  strᵛ : ∀ {Ψ} → EVar (Ψ +e) → OVType (Ψ +e) → Maybe (OVType Ψ)
  strᵛ j (tvar α)  = just (tvar α)
  strᵛ j (Base b)  = just (Base b)
  strᵛ j Unit      = just Unit
  strᵛ j Bool      = just Bool
  strᵛ j (A |×| B) = zip₂ _|×|_ (strᵛ j A) (strᵛ j B)
  strᵛ j Empty     = just Empty
  strᵛ j (A ⇒ C)   = zip₂ _⇒_ (strᵛ j A) (strᶜ j C)
  strᵛ j ([ ρ ] A) = zip₂ [_]_ (strʳ j ρ) (strᵛ j A)

  strᶜ : ∀ {Ψ} → EVar (Ψ +e) → OCType (Ψ +e) → Maybe (OCType Ψ)
  strᶜ j (A ‼ ε) = zip₂ _‼_ (strᵛ j A) (strᵉ j ε)

--------------------------------------------------------------
-- Moving the rigid back to the newest position              --
--------------------------------------------------------------

popˢ : ∀ {Ψ} → EVar (Ψ +e) → Subst (Ψ +e) (Ψ +e)
popˢ {Ψ} j = sub tvar rvar
                 (λ k → maybe′ (λ k₀ → evar (wkᵉ-ev Ψ k₀))
                               (evar (newᵉ {Ψ}))
                               (thickᵉ {Ψ} j k))

popˢ-hit : ∀ {Ψ} → (j : EVar (Ψ +e)) → sE (popˢ {Ψ} j) j ≡ evar (newᵉ {Ψ})
popˢ-hit {Ψ} j =
  cong (maybe′ (λ k₀ → evar (wkᵉ-ev Ψ k₀)) (evar (newᵉ {Ψ}))) (thick-refl {nE Ψ} j)

--------------------------------------------------------------
-- A successful strengthening inverts the move               --
--------------------------------------------------------------

str-popᵉ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (ε : EExp (Ψ +e)) → {ε₀ : EExp Ψ}
         → strᵉ j ε ≡ just ε₀ → ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀
str-popᵉ {Ψ} j (evar k)   q with map-just evar (thickᵉ {Ψ} j k) q
... | k₀ , qk , refl =
  cong (maybe′ (λ k₁ → evar (wkᵉ-ev Ψ k₁)) (evar (newᵉ {Ψ}))) qk
str-popᵉ     j (econst c) refl = refl
str-popᵉ     j (ε ·̂ₑ ε')  q with zip₂-just _·̂ₑ_ (strᵉ j ε) (strᵉ j ε') q
... | a , b , qa , qb , refl = cong₂ _·̂ₑ_ (str-popᵉ j ε qa) (str-popᵉ j ε' qb)

str-popʳ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (ρ : RExp (Ψ +e)) → {ρ₀ : RExp Ψ}
         → strʳ j ρ ≡ just ρ₀ → ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀
str-popʳ j (rvar i)   refl = refl
str-popʳ j (rconst c) refl = refl
str-popʳ j (ρ ·̂ᵣ ρ')  q with zip₂-just _·̂ᵣ_ (strʳ j ρ) (strʳ j ρ') q
... | a , b , qa , qb , refl = cong₂ _·̂ᵣ_ (str-popʳ j ρ qa) (str-popʳ j ρ' qb)
str-popʳ j ∣ ε ∣̂ᵉ     q with map-just ∣_∣̂ᵉ (strᵉ j ε) q
... | ε₀ , qe , refl = cong ∣_∣̂ᵉ (str-popᵉ j ε qe)

mutual

  str-popᵛ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (A : OVType (Ψ +e)) → {A₀ : OVType Ψ}
           → strᵛ j A ≡ just A₀ → A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀
  str-popᵛ j (tvar α)  refl = refl
  str-popᵛ j (Base b)  refl = refl
  str-popᵛ j Unit      refl = refl
  str-popᵛ j Bool      refl = refl
  str-popᵛ j Empty     refl = refl
  str-popᵛ j (A |×| B) q with zip₂-just _|×|_ (strᵛ j A) (strᵛ j B) q
  ... | a , b , qa , qb , refl = cong₂ _|×|_ (str-popᵛ j A qa) (str-popᵛ j B qb)
  str-popᵛ j (A ⇒ C)   q with zip₂-just _⇒_ (strᵛ j A) (strᶜ j C) q
  ... | a , b , qa , qb , refl = cong₂ _⇒_ (str-popᵛ j A qa) (str-popᶜ j C qb)
  str-popᵛ j ([ ρ ] A) q with zip₂-just [_]_ (strʳ j ρ) (strᵛ j A) q
  ... | a , b , qa , qb , refl = cong₂ [_]_ (str-popʳ j ρ qa) (str-popᵛ j A qb)

  str-popᶜ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (C : OCType (Ψ +e)) → {C₀ : OCType Ψ}
           → strᶜ j C ≡ just C₀ → C [ popˢ j ]ᶜ ≡ wkᵉ-c C₀
  str-popᶜ j (A ‼ ε) q with zip₂-just _‼_ (strᵛ j A) (strᵉ j ε) q
  ... | a , b , qa , qb , refl = cong₂ _‼_ (str-popᵛ j A qa) (str-popᵉ j ε qb)

--------------------------------------------------------------
-- Strengthening undoes the weakening                        --
--------------------------------------------------------------

str-wkᵉ : ∀ {Ψ} → (ε : EExp Ψ) → strᵉ (newᵉ {Ψ}) (wkᵉ-e ε) ≡ just ε
str-wkᵉ (evar i)   = refl
str-wkᵉ (econst c) = refl
str-wkᵉ (ε ·̂ₑ ε')  = cong₂ (zip₂ _·̂ₑ_) (str-wkᵉ ε) (str-wkᵉ ε')

str-wkʳ : ∀ {Ψ} → (ρ : RExp Ψ) → strʳ (newᵉ {Ψ}) (wkᵉ-r ρ) ≡ just ρ
str-wkʳ (rvar i)   = refl
str-wkʳ (rconst c) = refl
str-wkʳ (ρ ·̂ᵣ ρ')  = cong₂ (zip₂ _·̂ᵣ_) (str-wkʳ ρ) (str-wkʳ ρ')
str-wkʳ ∣ ε ∣̂ᵉ     = cong (mmap ∣_∣̂ᵉ) (str-wkᵉ ε)

mutual

  str-wkᵛ : ∀ {Ψ} → (A : OVType Ψ) → strᵛ (newᵉ {Ψ}) (wkᵉ-v A) ≡ just A
  str-wkᵛ (tvar α)  = refl
  str-wkᵛ (Base b)  = refl
  str-wkᵛ Unit      = refl
  str-wkᵛ Bool      = refl
  str-wkᵛ Empty     = refl
  str-wkᵛ (A |×| B) = cong₂ (zip₂ _|×|_) (str-wkᵛ A) (str-wkᵛ B)
  str-wkᵛ (A ⇒ C)   = cong₂ (zip₂ _⇒_) (str-wkᵛ A) (str-wkᶜ C)
  str-wkᵛ ([ ρ ] A) = cong₂ (zip₂ [_]_) (str-wkʳ ρ) (str-wkᵛ A)

  str-wkᶜ : ∀ {Ψ} → (C : OCType Ψ) → strᶜ (newᵉ {Ψ}) (wkᵉ-c C) ≡ just C
  str-wkᶜ (A ‼ ε) = cong₂ (zip₂ _‼_) (str-wkᵛ A) (str-wkᵉ ε)

--------------------------------------------------------------
-- Strengthening a whole substitution                        --
--                                                           --
-- A substitution out of a scope is a function on each of the --
-- three finite sorts, so the pointwise partial results are   --
-- assembled by a finite traversal.                           --
--------------------------------------------------------------

seqFin : ∀ {n} {X : Set} {P : Fin n → X → Set}
       → ((i : Fin n) → Maybe (Σ[ x ∈ X ] P i x))
       → Maybe (Σ[ g ∈ (Fin n → X) ] ((i : Fin n) → P i (g i)))
seqFin {nzero}  f = just ((λ ()) , (λ ()))
seqFin {nsuc n} f with f zero | seqFin (λ i → f (suc i))
... | just (x , p) | just (g , q) =
      just ((λ { zero → x ; (suc i) → g i }) , (λ { zero → p ; (suc i) → q i }))
... | just _       | nothing = nothing
... | nothing      | _       = nothing

strᵛ⁺ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (A : OVType (Ψ +e))
      → Maybe (Σ[ A₀ ∈ OVType Ψ ] (A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀))
strᵛ⁺ j A with strᵛ j A in eq
... | just A₀ = just (A₀ , str-popᵛ j A eq)
... | nothing = nothing

strʳ⁺ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (ρ : RExp (Ψ +e))
      → Maybe (Σ[ ρ₀ ∈ RExp Ψ ] (ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀))
strʳ⁺ j ρ with strʳ j ρ in eq
... | just ρ₀ = just (ρ₀ , str-popʳ j ρ eq)
... | nothing = nothing

strᵉ⁺ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (ε : EExp (Ψ +e))
      → Maybe (Σ[ ε₀ ∈ EExp Ψ ] (ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀))
strᵉ⁺ j ε with strᵉ j ε in eq
... | just ε₀ = just (ε₀ , str-popᵉ j ε eq)
... | nothing = nothing

strSub : ∀ {Θ Ψ} → (j : EVar (Ψ +e)) → (γ : Subst Θ (Ψ +e))
       → Maybe (Σ[ γ₀ ∈ Subst Θ Ψ ] ((γ ⨟ˢ popˢ j) ≐ˢ (γ₀ ⨟ˢ wkˢᵉ)))
strSub j γ with seqFin (λ α → strᵛ⁺ j (sTy γ α))
              | seqFin (λ i → strʳ⁺ j (sR  γ i))
              | seqFin (λ i → strᵉ⁺ j (sE  γ i))
... | just (fT , pT) | just (fR , pR) | just (fE , pE) =
      just (sub fT fR fE ,
            mk≐ˢ (λ α → trans (pT α) (sym (wkˢᵉ-v (fT α))))
                 (λ i → trans (pR i) (sym (wkˢᵉ-r (fR i))))
                 (λ i → trans (pE i) (sym (wkˢᵉ-e (fE i)))))
... | just _         | just _         | nothing        = nothing
... | just _         | nothing        | _              = nothing
... | nothing        | _              | _              = nothing
