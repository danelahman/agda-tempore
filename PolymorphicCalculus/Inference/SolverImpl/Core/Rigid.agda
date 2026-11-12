------------------------------------------------------------------
-- Strengthening away a rigid variable                          --
--                                                              --
-- A rigid effect-grade variable is strengthened away when its  --
-- scope is left; `popˢ` and `unpopˢ` move it to the newest     --
-- position. A failed strengthening refutes every instance      --
-- keeping the rigid an eigenvariable (the escape lemma).       --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′) renaming (map to mmap)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.SolverImpl.Core.Rigid (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S

open import PolymorphicCalculus.Inference.SolverImpl.Core.Thick
open import PolymorphicCalculus.Inference.SolverImpl.Core.Occurs S

-- Decidability helpers

⊥just : ∀ {X Y : Set} {x : X} → nothing ≡ just x → Y
⊥just ()

dec-true : ∀ {P : Set} → (d : Dec P) → P → ⌊ d ⌋ ≡ true
dec-true (yes _) _ = refl
dec-true (no nr) r = ⊥-elim (nr r)

true-dec : ∀ {P : Set} → (d : Dec P) → ⌊ d ⌋ ≡ true → P
true-dec (yes r) q = r
true-dec (no  _) ()

∨-true : (b b' : 𝔹) → (b ∨ b') ≡ true → (b ≡ true) ⊎ (b' ≡ true)
∨-true true  b' q = inj₁ refl
∨-true false b' q = inj₂ q

∨-left : (b b' : 𝔹) → b ≡ true → (b ∨ b') ≡ true
∨-left true  b' q = refl
∨-left false b' ()

∨-right : (b b' : 𝔹) → b' ≡ true → (b ∨ b') ≡ true
∨-right true  b' q = refl
∨-right false b' q = q

-- A partial result that is not `nothing` is a `just`

notNothing : ∀ {X : Set} → (m : Maybe X) → (m ≡ nothing → ⊥) → Σ[ x ∈ X ] (m ≡ just x)
notNothing (just x) h = x , refl
notNothing nothing  h = ⊥-elim (h refl)

zip₂ : ∀ {X Y Z : Set} → (X → Y → Z) → Maybe X → Maybe Y → Maybe Z
zip₂ f (just x) (just y) = just (f x y)
zip₂ f _        _        = nothing

zip₂-just : ∀ {X Y Z : Set} → (f : X → Y → Z)
          → (m : Maybe X) → (m' : Maybe Y) → {z : Z} → zip₂ f m m' ≡ just z
          → Σ[ x ∈ X ] Σ[ y ∈ Y ] ((m ≡ just x) × (m' ≡ just y) × (f x y ≡ z))
zip₂-just f (just x) (just y) refl = x , y , refl , refl , refl
zip₂-just f (just x) nothing  ()
zip₂-just f nothing  m'       ()

zip₂-nothing : ∀ {X Y Z : Set} → (f : X → Y → Z)
             → (m : Maybe X) → (m' : Maybe Y) → zip₂ f m m' ≡ nothing
             → (m ≡ nothing) ⊎ (m' ≡ nothing)
zip₂-nothing f (just x) (just y) ()
zip₂-nothing f (just x) nothing  q = inj₂ refl
zip₂-nothing f nothing  m'       q = inj₁ refl

map-nothing : ∀ {X Y : Set} → (f : X → Y) → (m : Maybe X) → mmap f m ≡ nothing
            → m ≡ nothing
map-nothing f nothing  q = refl
map-nothing f (just x) ()

strᵉ : ∀ {Ω} → EVar (Ω +e) → EExp (Ω +e) → Maybe (EExp Ω)
strᵉ {Ω} j (evar k)   = mmap evar (thickᵉ {Ω} j k)
strᵉ     j (econst c) = just (econst c)
strᵉ     j (ε ·̂ₑ ε')  = zip₂ _·̂ₑ_ (strᵉ j ε) (strᵉ j ε')
strᵉ     j (ε ⊔̂ₑ ε')  = zip₂ _⊔̂ₑ_ (strᵉ j ε) (strᵉ j ε')

strʳ : ∀ {Ω} → EVar (Ω +e) → RExp (Ω +e) → Maybe (RExp Ω)
strʳ j (rvar i)   = just (rvar i)
strʳ j (rconst c) = just (rconst c)
strʳ j (ρ ·̂ᵣ ρ')  = zip₂ _·̂ᵣ_ (strʳ j ρ) (strʳ j ρ')
strʳ j (ρ ⊔̂ᵣ ρ')  = zip₂ _⊔̂ᵣ_ (strʳ j ρ) (strʳ j ρ')
strʳ j ∣ ε ∣̂ᵉ     = mmap ∣_∣̂ᵉ (strᵉ j ε)

mutual

  strᵛ : ∀ {Ω} → EVar (Ω +e) → OVType (Ω +e) → Maybe (OVType Ω)
  strᵛ j (tvar α)  = just (tvar α)
  strᵛ j (Base b)  = just (Base b)
  strᵛ j unit      = just unit
  strᵛ j bool      = just bool
  strᵛ j nat       = just nat
  strᵛ j (A |×| B) = zip₂ _|×|_ (strᵛ j A) (strᵛ j B)
  strᵛ j (A |+| B) = zip₂ _|+|_ (strᵛ j A) (strᵛ j B)
  strᵛ j (list A)  = mmap list (strᵛ j A)
  strᵛ j empty     = just empty
  strᵛ j (A ⇒ C)   = zip₂ _⇒_ (strᵛ j A) (strᶜ j C)
  strᵛ j (C ⇛ D)   = zip₂ _⇛_ (strᶜ j C) (strᶜ j D)
  strᵛ j ([ ρ ] A) = zip₂ [_]_ (strʳ j ρ) (strᵛ j A)

  strᶜ : ∀ {Ω} → EVar (Ω +e) → OCType (Ω +e) → Maybe (OCType Ω)
  strᶜ j (A ! ε) = zip₂ _!_ (strᵛ j A) (strᵉ j ε)

popˢ : ∀ {Ω} → EVar (Ω +e) → Subst (Ω +e) (Ω +e)
popˢ {Ω} j = sub tvar rvar
                 (λ k → maybe′ (λ k₀ → evar (wkᵉ-ev Ω k₀))
                               (evar (newᵉ {Ω}))
                               (thickᵉ {Ω} j k))

popˢ-hit : ∀ {Ω} → (j : EVar (Ω +e)) → sE (popˢ {Ω} j) j ≡ evar (newᵉ {Ω})
popˢ-hit {Ω} j =
  cong (maybe′ (λ k₀ → evar (wkᵉ-ev Ω k₀)) (evar (newᵉ {Ω}))) (thick-refl {nE Ω} j)

str-popᵉ : ∀ {Ω} → (j : EVar (Ω +e)) → (ε : EExp (Ω +e)) → {ε₀ : EExp Ω}
         → strᵉ j ε ≡ just ε₀ → ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀
str-popᵉ {Ω} j (evar k)   q with map-just evar (thickᵉ {Ω} j k) q
... | k₀ , qk , refl =
  cong (maybe′ (λ k₁ → evar (wkᵉ-ev Ω k₁)) (evar (newᵉ {Ω}))) qk
str-popᵉ     j (econst c) refl = refl
str-popᵉ     j (ε ·̂ₑ ε')  q with zip₂-just _·̂ₑ_ (strᵉ j ε) (strᵉ j ε') q
... | a , b , qa , qb , refl = cong₂ _·̂ₑ_ (str-popᵉ j ε qa) (str-popᵉ j ε' qb)
str-popᵉ     j (ε ⊔̂ₑ ε')  q with zip₂-just _⊔̂ₑ_ (strᵉ j ε) (strᵉ j ε') q
... | a , b , qa , qb , refl = cong₂ _⊔̂ₑ_ (str-popᵉ j ε qa) (str-popᵉ j ε' qb)

str-popʳ : ∀ {Ω} → (j : EVar (Ω +e)) → (ρ : RExp (Ω +e)) → {ρ₀ : RExp Ω}
         → strʳ j ρ ≡ just ρ₀ → ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀
str-popʳ j (rvar i)   refl = refl
str-popʳ j (rconst c) refl = refl
str-popʳ j (ρ ·̂ᵣ ρ')  q with zip₂-just _·̂ᵣ_ (strʳ j ρ) (strʳ j ρ') q
... | a , b , qa , qb , refl = cong₂ _·̂ᵣ_ (str-popʳ j ρ qa) (str-popʳ j ρ' qb)
str-popʳ j (ρ ⊔̂ᵣ ρ')  q with zip₂-just _⊔̂ᵣ_ (strʳ j ρ) (strʳ j ρ') q
... | a , b , qa , qb , refl = cong₂ _⊔̂ᵣ_ (str-popʳ j ρ qa) (str-popʳ j ρ' qb)
str-popʳ j ∣ ε ∣̂ᵉ     q with map-just ∣_∣̂ᵉ (strᵉ j ε) q
... | ε₀ , qe , refl = cong ∣_∣̂ᵉ (str-popᵉ j ε qe)

mutual

  str-popᵛ : ∀ {Ω} → (j : EVar (Ω +e)) → (A : OVType (Ω +e)) → {A₀ : OVType Ω}
           → strᵛ j A ≡ just A₀ → A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀
  str-popᵛ j (tvar α)  refl = refl
  str-popᵛ j (Base b)  refl = refl
  str-popᵛ j unit      refl = refl
  str-popᵛ j bool      refl = refl
  str-popᵛ j nat       refl = refl
  str-popᵛ j empty     refl = refl
  str-popᵛ j (A |×| B) q with zip₂-just _|×|_ (strᵛ j A) (strᵛ j B) q
  ... | a , b , qa , qb , refl = cong₂ _|×|_ (str-popᵛ j A qa) (str-popᵛ j B qb)
  str-popᵛ j (A |+| B) q with zip₂-just _|+|_ (strᵛ j A) (strᵛ j B) q
  ... | a , b , qa , qb , refl = cong₂ _|+|_ (str-popᵛ j A qa) (str-popᵛ j B qb)
  str-popᵛ j (list A)  q with map-just list (strᵛ j A) q
  ... | a , qa , refl = cong list (str-popᵛ j A qa)
  str-popᵛ j (A ⇒ C)   q with zip₂-just _⇒_ (strᵛ j A) (strᶜ j C) q
  ... | a , b , qa , qb , refl = cong₂ _⇒_ (str-popᵛ j A qa) (str-popᶜ j C qb)
  str-popᵛ j (C ⇛ D)   q with zip₂-just _⇛_ (strᶜ j C) (strᶜ j D) q
  ... | a , b , qa , qb , refl = cong₂ _⇛_ (str-popᶜ j C qa) (str-popᶜ j D qb)
  str-popᵛ j ([ ρ ] A) q with zip₂-just [_]_ (strʳ j ρ) (strᵛ j A) q
  ... | a , b , qa , qb , refl = cong₂ [_]_ (str-popʳ j ρ qa) (str-popᵛ j A qb)

  str-popᶜ : ∀ {Ω} → (j : EVar (Ω +e)) → (C : OCType (Ω +e)) → {C₀ : OCType Ω}
           → strᶜ j C ≡ just C₀ → C [ popˢ j ]ᶜ ≡ wkᵉ-c C₀
  str-popᶜ j (A ! ε) q with zip₂-just _!_ (strᵛ j A) (strᵉ j ε) q
  ... | a , b , qa , qb , refl = cong₂ _!_ (str-popᵛ j A qa) (str-popᵉ j ε qb)

str-wkᵉ : ∀ {Ω} → (ε : EExp Ω) → strᵉ (newᵉ {Ω}) (wkᵉ-e ε) ≡ just ε
str-wkᵉ (evar i)   = refl
str-wkᵉ (econst c) = refl
str-wkᵉ (ε ·̂ₑ ε')  = cong₂ (zip₂ _·̂ₑ_) (str-wkᵉ ε) (str-wkᵉ ε')
str-wkᵉ (ε ⊔̂ₑ ε')  = cong₂ (zip₂ _⊔̂ₑ_) (str-wkᵉ ε) (str-wkᵉ ε')

str-wkʳ : ∀ {Ω} → (ρ : RExp Ω) → strʳ (newᵉ {Ω}) (wkᵉ-r ρ) ≡ just ρ
str-wkʳ (rvar i)   = refl
str-wkʳ (rconst c) = refl
str-wkʳ (ρ ·̂ᵣ ρ')  = cong₂ (zip₂ _·̂ᵣ_) (str-wkʳ ρ) (str-wkʳ ρ')
str-wkʳ (ρ ⊔̂ᵣ ρ')  = cong₂ (zip₂ _⊔̂ᵣ_) (str-wkʳ ρ) (str-wkʳ ρ')
str-wkʳ ∣ ε ∣̂ᵉ     = cong (mmap ∣_∣̂ᵉ) (str-wkᵉ ε)

mutual

  str-wkᵛ : ∀ {Ω} → (A : OVType Ω) → strᵛ (newᵉ {Ω}) (wkᵉ-v A) ≡ just A
  str-wkᵛ (tvar α)  = refl
  str-wkᵛ (Base b)  = refl
  str-wkᵛ unit      = refl
  str-wkᵛ bool      = refl
  str-wkᵛ nat       = refl
  str-wkᵛ empty     = refl
  str-wkᵛ (A |×| B) = cong₂ (zip₂ _|×|_) (str-wkᵛ A) (str-wkᵛ B)
  str-wkᵛ (A |+| B) = cong₂ (zip₂ _|+|_) (str-wkᵛ A) (str-wkᵛ B)
  str-wkᵛ (list A)  = cong (mmap list) (str-wkᵛ A)
  str-wkᵛ (A ⇒ C)   = cong₂ (zip₂ _⇒_) (str-wkᵛ A) (str-wkᶜ C)
  str-wkᵛ (C ⇛ D)   = cong₂ (zip₂ _⇛_) (str-wkᶜ C) (str-wkᶜ D)
  str-wkᵛ ([ ρ ] A) = cong₂ (zip₂ [_]_) (str-wkʳ ρ) (str-wkᵛ A)

  str-wkᶜ : ∀ {Ω} → (C : OCType Ω) → strᶜ (newᵉ {Ω}) (wkᵉ-c C) ≡ just C
  str-wkᶜ (A ! ε) = cong₂ (zip₂ _!_) (str-wkᵛ A) (str-wkᵉ ε)

-- The pointwise partial results of the three sorts assembled by a finite
-- traversal; the auxiliaries take the scrutinee explicitly

seqFinᵃ : ∀ {n} {X : Set} → (P : Fin (nsuc n) → X → Set)
        → Maybe (Σ[ x ∈ X ] P zero x)
        → Maybe (Σ[ g ∈ (Fin n → X) ] ((i : Fin n) → P (suc i) (g i)))
        → Maybe (Σ[ g ∈ (Fin (nsuc n) → X) ] ((i : Fin (nsuc n)) → P i (g i)))
seqFinᵃ P (just (x , p)) (just (g , q)) =
  just ((λ { zero → x ; (suc i) → g i }) , (λ { zero → p ; (suc i) → q i }))
seqFinᵃ P (just _)       nothing = nothing
seqFinᵃ P nothing        _       = nothing

seqFin : ∀ {n} {X : Set} {P : Fin n → X → Set}
       → ((i : Fin n) → Maybe (Σ[ x ∈ X ] P i x))
       → Maybe (Σ[ g ∈ (Fin n → X) ] ((i : Fin n) → P i (g i)))
seqFin {nzero}  f = just ((λ ()) , (λ ()))
seqFin {nsuc n} {X} {P} f =
  seqFinᵃ P (f zero) (seqFin {P = λ i x → P (suc i) x} (λ i → f (suc i)))

strᵛᵃ : ∀ {Ω} → (j : EVar (Ω +e)) → (A : OVType (Ω +e))
      → (x : Maybe (OVType Ω)) → strᵛ j A ≡ x
      → Maybe (Σ[ A₀ ∈ OVType Ω ] (A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀))
strᵛᵃ j A (just A₀) eq = just (A₀ , str-popᵛ j A eq)
strᵛᵃ j A nothing   eq = nothing

strʳᵃ : ∀ {Ω} → (j : EVar (Ω +e)) → (ρ : RExp (Ω +e))
      → (x : Maybe (RExp Ω)) → strʳ j ρ ≡ x
      → Maybe (Σ[ ρ₀ ∈ RExp Ω ] (ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀))
strʳᵃ j ρ (just ρ₀) eq = just (ρ₀ , str-popʳ j ρ eq)
strʳᵃ j ρ nothing   eq = nothing

strᵉᵃ : ∀ {Ω} → (j : EVar (Ω +e)) → (ε : EExp (Ω +e))
      → (x : Maybe (EExp Ω)) → strᵉ j ε ≡ x
      → Maybe (Σ[ ε₀ ∈ EExp Ω ] (ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀))
strᵉᵃ j ε (just ε₀) eq = just (ε₀ , str-popᵉ j ε eq)
strᵉᵃ j ε nothing   eq = nothing

strᵛ⁺ : ∀ {Ω} → (j : EVar (Ω +e)) → (A : OVType (Ω +e))
      → Maybe (Σ[ A₀ ∈ OVType Ω ] (A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀))
strᵛ⁺ j A = strᵛᵃ j A (strᵛ j A) refl

strʳ⁺ : ∀ {Ω} → (j : EVar (Ω +e)) → (ρ : RExp (Ω +e))
      → Maybe (Σ[ ρ₀ ∈ RExp Ω ] (ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀))
strʳ⁺ j ρ = strʳᵃ j ρ (strʳ j ρ) refl

strᵉ⁺ : ∀ {Ω} → (j : EVar (Ω +e)) → (ε : EExp (Ω +e))
      → Maybe (Σ[ ε₀ ∈ EExp Ω ] (ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀))
strᵉ⁺ j ε = strᵉᵃ j ε (strᵉ j ε) refl

strSubᵃ : ∀ {Θ Ω} → (j : EVar (Ω +e)) → (γ : Subst Θ (Ω +e))
        → Maybe (Σ[ g ∈ (TyVar Θ → OVType Ω) ]
                   ((α : TyVar Θ) → sTy γ α [ popˢ j ]ᵛ ≡ wkᵉ-v (g α)))
        → Maybe (Σ[ g ∈ (RVar Θ → RExp Ω) ]
                   ((i : RVar Θ) → sR γ i [ popˢ j ]ʳ ≡ wkᵉ-r (g i)))
        → Maybe (Σ[ g ∈ (EVar Θ → EExp Ω) ]
                   ((i : EVar Θ) → sE γ i [ popˢ j ]ᵉ ≡ wkᵉ-e (g i)))
        → Maybe (Σ[ γ₀ ∈ Subst Θ Ω ] ((γ ⨟ˢ popˢ j) ≐ˢ (γ₀ ⨟ˢ wkˢᵉ)))
strSubᵃ j γ (just (fT , pT)) (just (fR , pR)) (just (fE , pE)) =
  just (sub fT fR fE ,
        mk≐ˢ (λ α → trans (pT α) (sym (wkˢᵉ-v (fT α))))
             (λ i → trans (pR i) (sym (wkˢᵉ-r (fR i))))
             (λ i → trans (pE i) (sym (wkˢᵉ-e (fE i)))))
strSubᵃ j γ (just _) (just _) nothing = nothing
strSubᵃ j γ (just _) nothing  _       = nothing
strSubᵃ j γ nothing  _        _       = nothing

strSub : ∀ {Θ Ω} → (j : EVar (Ω +e)) → (γ : Subst Θ (Ω +e))
       → Maybe (Σ[ γ₀ ∈ Subst Θ Ω ] ((γ ⨟ˢ popˢ j) ≐ˢ (γ₀ ⨟ˢ wkˢᵉ)))
strSub j γ = strSubᵃ j γ (seqFin (λ α → strᵛ⁺ j (sTy γ α)))
                         (seqFin (λ i → strʳ⁺ j (sR  γ i)))
                         (seqFin (λ i → strᵉ⁺ j (sE  γ i)))

unpopˢ : ∀ {Ω} → EVar (Ω +e) → Subst (Ω +e) (Ω +e)
unpopˢ {Ω} j = sub tvar rvar (λ { zero → evar j ; (suc k) → evar (thinᵉ {Ω} j k) })

-- Thickening is `nothing` only at the variable itself

thick-nothing : ∀ {n} → (i j : Fin (nsuc n)) → thick i j ≡ nothing → j ≡ i
thick-nothing          zero   zero    q = refl
thick-nothing          zero   (suc j) ()
thick-nothing {nsuc n} (suc i) zero   ()
thick-nothing {nsuc n} (suc i) (suc j) q with thick i j in r
... | nothing = cong suc (thick-nothing i j r)

pop-unpop : ∀ {Ω} → (j : EVar (Ω +e)) → (popˢ j ⨟ˢ unpopˢ j) ≐ˢ idˢ
pop-unpop {Ω} j = mk≐ˢ (λ α → refl) (λ i → refl) sE'
  where
    sE' : (k : EVar (Ω +e)) → sE (popˢ {Ω} j ⨟ˢ unpopˢ {Ω} j) k ≡ sE (idˢ {Ω +e}) k
    sE' k with thickᵉ {Ω} j k in r
    ... | just k₀  = cong evar (sym (thick-just {nE Ω} j k k₀ r))
    ... | nothing  = cong evar (sym (thick-nothing {nE Ω} j k r))

-- An occurrence of a variable whose image is a variable is renamed, not
-- removed

escᵉ : ∀ {Φ Ω} → (σ : Subst Φ Ω) → (j : EVar Φ) → (k : EVar Ω) → sE σ j ≡ evar k
     → (ε : EExp Φ) → occᵉ-e j ε ≡ true → occᵉ-e k (ε [ σ ]ᵉ) ≡ true
escᵉ σ j k r (evar l)   q with true-dec (j ≟ᶠ l) q
... | refl = subst (λ x → occᵉ-e k x ≡ true) (sym r) (dec-true (k ≟ᶠ k) refl)
escᵉ σ j k r (econst c) ()
escᵉ σ j k r (ε ·̂ₑ ε')  q with ∨-true (occᵉ-e j ε) (occᵉ-e j ε') q
... | inj₁ s = ∨-left  (occᵉ-e k (ε [ σ ]ᵉ)) (occᵉ-e k (ε' [ σ ]ᵉ)) (escᵉ σ j k r ε s)
... | inj₂ s = ∨-right (occᵉ-e k (ε [ σ ]ᵉ)) (occᵉ-e k (ε' [ σ ]ᵉ)) (escᵉ σ j k r ε' s)
escᵉ σ j k r (ε ⊔̂ₑ ε')  q with ∨-true (occᵉ-e j ε) (occᵉ-e j ε') q
... | inj₁ s = ∨-left  (occᵉ-e k (ε [ σ ]ᵉ)) (occᵉ-e k (ε' [ σ ]ᵉ)) (escᵉ σ j k r ε s)
... | inj₂ s = ∨-right (occᵉ-e k (ε [ σ ]ᵉ)) (occᵉ-e k (ε' [ σ ]ᵉ)) (escᵉ σ j k r ε' s)

escʳ : ∀ {Φ Ω} → (σ : Subst Φ Ω) → (j : EVar Φ) → (k : EVar Ω) → sE σ j ≡ evar k
     → (ρ : RExp Φ) → occᵉ-r j ρ ≡ true → occᵉ-r k (ρ [ σ ]ʳ) ≡ true
escʳ σ j k r (rvar i)   ()
escʳ σ j k r (rconst c) ()
escʳ σ j k r (ρ ·̂ᵣ ρ')  q with ∨-true (occᵉ-r j ρ) (occᵉ-r j ρ') q
... | inj₁ s = ∨-left  (occᵉ-r k (ρ [ σ ]ʳ)) (occᵉ-r k (ρ' [ σ ]ʳ)) (escʳ σ j k r ρ s)
... | inj₂ s = ∨-right (occᵉ-r k (ρ [ σ ]ʳ)) (occᵉ-r k (ρ' [ σ ]ʳ)) (escʳ σ j k r ρ' s)
escʳ σ j k r (ρ ⊔̂ᵣ ρ')  q with ∨-true (occᵉ-r j ρ) (occᵉ-r j ρ') q
... | inj₁ s = ∨-left  (occᵉ-r k (ρ [ σ ]ʳ)) (occᵉ-r k (ρ' [ σ ]ʳ)) (escʳ σ j k r ρ s)
... | inj₂ s = ∨-right (occᵉ-r k (ρ [ σ ]ʳ)) (occᵉ-r k (ρ' [ σ ]ʳ)) (escʳ σ j k r ρ' s)
escʳ σ j k r ∣ ε ∣̂ᵉ     q = escᵉ σ j k r ε q

mutual

  escᵛ : ∀ {Φ Ω} → (σ : Subst Φ Ω) → (j : EVar Φ) → (k : EVar Ω) → sE σ j ≡ evar k
       → (A : OVType Φ) → occᵉ-v j A ≡ true → occᵉ-v k (A [ σ ]ᵛ) ≡ true
  escᵛ σ j k r (tvar α)  ()
  escᵛ σ j k r (Base b)  ()
  escᵛ σ j k r unit      ()
  escᵛ σ j k r bool      ()
  escᵛ σ j k r nat       ()
  escᵛ σ j k r empty     ()
  escᵛ σ j k r (A |×| B) q with ∨-true (occᵉ-v j A) (occᵉ-v j B) q
  ... | inj₁ s = ∨-left  (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-v k (B [ σ ]ᵛ)) (escᵛ σ j k r A s)
  ... | inj₂ s = ∨-right (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-v k (B [ σ ]ᵛ)) (escᵛ σ j k r B s)
  escᵛ σ j k r (A |+| B) q with ∨-true (occᵉ-v j A) (occᵉ-v j B) q
  ... | inj₁ s = ∨-left  (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-v k (B [ σ ]ᵛ)) (escᵛ σ j k r A s)
  ... | inj₂ s = ∨-right (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-v k (B [ σ ]ᵛ)) (escᵛ σ j k r B s)
  escᵛ σ j k r (list A)  q = escᵛ σ j k r A q
  escᵛ σ j k r (A ⇒ C)   q with ∨-true (occᵉ-v j A) (occᵉ-c j C) q
  ... | inj₁ s = ∨-left  (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-c k (C [ σ ]ᶜ)) (escᵛ σ j k r A s)
  ... | inj₂ s = ∨-right (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-c k (C [ σ ]ᶜ)) (escᶜ σ j k r C s)
  escᵛ σ j k r (C ⇛ D)   q with ∨-true (occᵉ-c j C) (occᵉ-c j D) q
  ... | inj₁ s = ∨-left  (occᵉ-c k (C [ σ ]ᶜ)) (occᵉ-c k (D [ σ ]ᶜ)) (escᶜ σ j k r C s)
  ... | inj₂ s = ∨-right (occᵉ-c k (C [ σ ]ᶜ)) (occᵉ-c k (D [ σ ]ᶜ)) (escᶜ σ j k r D s)
  escᵛ σ j k r ([ ρ ] A) q with ∨-true (occᵉ-r j ρ) (occᵉ-v j A) q
  ... | inj₁ s = ∨-left  (occᵉ-r k (ρ [ σ ]ʳ)) (occᵉ-v k (A [ σ ]ᵛ)) (escʳ σ j k r ρ s)
  ... | inj₂ s = ∨-right (occᵉ-r k (ρ [ σ ]ʳ)) (occᵉ-v k (A [ σ ]ᵛ)) (escᵛ σ j k r A s)

  escᶜ : ∀ {Φ Ω} → (σ : Subst Φ Ω) → (j : EVar Φ) → (k : EVar Ω) → sE σ j ≡ evar k
       → (C : OCType Φ) → occᵉ-c j C ≡ true → occᵉ-c k (C [ σ ]ᶜ) ≡ true
  escᶜ σ j k r (A ! ε) q with ∨-true (occᵉ-v j A) (occᵉ-e j ε) q
  ... | inj₁ s = ∨-left  (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-e k (ε [ σ ]ᵉ)) (escᵛ σ j k r A s)
  ... | inj₂ s = ∨-right (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-e k (ε [ σ ]ᵉ)) (escᵉ σ j k r ε s)

occ-wkᵉ : ∀ {Ω} → (ε : EExp Ω) → occᵉ-e (newᵉ {Ω}) (wkᵉ-e ε) ≡ true → ⊥
occ-wkᵉ {Ω} (evar i)   q with true-dec (newᵉ {Ω} ≟ᶠ wkᵉ-ev Ω i) q
... | ()
occ-wkᵉ     (econst c) ()
occ-wkᵉ {Ω} (ε ·̂ₑ ε')  q =
  [ occ-wkᵉ ε , occ-wkᵉ ε' ]′
    (∨-true (occᵉ-e (newᵉ {Ω}) (wkᵉ-e ε)) (occᵉ-e (newᵉ {Ω}) (wkᵉ-e ε')) q)
occ-wkᵉ {Ω} (ε ⊔̂ₑ ε')  q =
  [ occ-wkᵉ ε , occ-wkᵉ ε' ]′
    (∨-true (occᵉ-e (newᵉ {Ω}) (wkᵉ-e ε)) (occᵉ-e (newᵉ {Ω}) (wkᵉ-e ε')) q)

occ-wkʳ : ∀ {Ω} → (ρ : RExp Ω) → occᵉ-r (newᵉ {Ω}) (wkᵉ-r ρ) ≡ true → ⊥
occ-wkʳ     (rvar i)   ()
occ-wkʳ     (rconst c) ()
occ-wkʳ {Ω} (ρ ·̂ᵣ ρ')  q =
  [ occ-wkʳ ρ , occ-wkʳ ρ' ]′
    (∨-true (occᵉ-r (newᵉ {Ω}) (wkᵉ-r ρ)) (occᵉ-r (newᵉ {Ω}) (wkᵉ-r ρ')) q)
occ-wkʳ {Ω} (ρ ⊔̂ᵣ ρ')  q =
  [ occ-wkʳ ρ , occ-wkʳ ρ' ]′
    (∨-true (occᵉ-r (newᵉ {Ω}) (wkᵉ-r ρ)) (occᵉ-r (newᵉ {Ω}) (wkᵉ-r ρ')) q)
occ-wkʳ     ∣ ε ∣̂ᵉ     q = occ-wkᵉ ε q

mutual

  occ-wkᵛ : ∀ {Ω} → (A : OVType Ω) → occᵉ-v (newᵉ {Ω}) (wkᵉ-v A) ≡ true → ⊥
  occ-wkᵛ (tvar α)  ()
  occ-wkᵛ (Base b)  ()
  occ-wkᵛ unit      ()
  occ-wkᵛ bool      ()
  occ-wkᵛ nat       ()
  occ-wkᵛ empty     ()
  occ-wkᵛ {Ω} (A |×| B) q =
    [ occ-wkᵛ A , occ-wkᵛ B ]′
      (∨-true (occᵉ-v (newᵉ {Ω}) (wkᵉ-v A)) (occᵉ-v (newᵉ {Ω}) (wkᵉ-v B)) q)
  occ-wkᵛ {Ω} (A |+| B) q =
    [ occ-wkᵛ A , occ-wkᵛ B ]′
      (∨-true (occᵉ-v (newᵉ {Ω}) (wkᵉ-v A)) (occᵉ-v (newᵉ {Ω}) (wkᵉ-v B)) q)
  occ-wkᵛ {Ω} (list A)  q = occ-wkᵛ A q
  occ-wkᵛ {Ω} (A ⇒ C)   q =
    [ occ-wkᵛ A , occ-wkᶜ C ]′
      (∨-true (occᵉ-v (newᵉ {Ω}) (wkᵉ-v A)) (occᵉ-c (newᵉ {Ω}) (wkᵉ-c C)) q)
  occ-wkᵛ {Ω} (C ⇛ D)   q =
    [ occ-wkᶜ C , occ-wkᶜ D ]′
      (∨-true (occᵉ-c (newᵉ {Ω}) (wkᵉ-c C)) (occᵉ-c (newᵉ {Ω}) (wkᵉ-c D)) q)
  occ-wkᵛ {Ω} ([ ρ ] A) q =
    [ occ-wkʳ ρ , occ-wkᵛ A ]′
      (∨-true (occᵉ-r (newᵉ {Ω}) (wkᵉ-r ρ)) (occᵉ-v (newᵉ {Ω}) (wkᵉ-v A)) q)

  occ-wkᶜ : ∀ {Ω} → (C : OCType Ω) → occᵉ-c (newᵉ {Ω}) (wkᵉ-c C) ≡ true → ⊥
  occ-wkᶜ {Ω} (A ! ε) q =
    [ occ-wkᵛ A , occ-wkᵉ ε ]′
      (∨-true (occᵉ-v (newᵉ {Ω}) (wkᵉ-v A)) (occᵉ-e (newᵉ {Ω}) (wkᵉ-e ε)) q)

str-occᵉ : ∀ {Ω} → (j : EVar (Ω +e)) → (ε : EExp (Ω +e))
         → strᵉ j ε ≡ nothing → occᵉ-e j ε ≡ true
str-occᵉ {Ω} j (evar k)   q =
  dec-true (j ≟ᶠ k) (sym (thick-nothing {nE Ω} j k (map-nothing evar (thickᵉ {Ω} j k) q)))
str-occᵉ     j (econst c) ()
str-occᵉ     j (ε ·̂ₑ ε')  q with zip₂-nothing _·̂ₑ_ (strᵉ j ε) (strᵉ j ε') q
... | inj₁ s = ∨-left  (occᵉ-e j ε) (occᵉ-e j ε') (str-occᵉ j ε s)
... | inj₂ s = ∨-right (occᵉ-e j ε) (occᵉ-e j ε') (str-occᵉ j ε' s)
str-occᵉ     j (ε ⊔̂ₑ ε')  q with zip₂-nothing _⊔̂ₑ_ (strᵉ j ε) (strᵉ j ε') q
... | inj₁ s = ∨-left  (occᵉ-e j ε) (occᵉ-e j ε') (str-occᵉ j ε s)
... | inj₂ s = ∨-right (occᵉ-e j ε) (occᵉ-e j ε') (str-occᵉ j ε' s)

str-occʳ : ∀ {Ω} → (j : EVar (Ω +e)) → (ρ : RExp (Ω +e))
         → strʳ j ρ ≡ nothing → occᵉ-r j ρ ≡ true
str-occʳ j (rvar i)   ()
str-occʳ j (rconst c) ()
str-occʳ j (ρ ·̂ᵣ ρ')  q with zip₂-nothing _·̂ᵣ_ (strʳ j ρ) (strʳ j ρ') q
... | inj₁ s = ∨-left  (occᵉ-r j ρ) (occᵉ-r j ρ') (str-occʳ j ρ s)
... | inj₂ s = ∨-right (occᵉ-r j ρ) (occᵉ-r j ρ') (str-occʳ j ρ' s)
str-occʳ j (ρ ⊔̂ᵣ ρ')  q with zip₂-nothing _⊔̂ᵣ_ (strʳ j ρ) (strʳ j ρ') q
... | inj₁ s = ∨-left  (occᵉ-r j ρ) (occᵉ-r j ρ') (str-occʳ j ρ s)
... | inj₂ s = ∨-right (occᵉ-r j ρ) (occᵉ-r j ρ') (str-occʳ j ρ' s)
str-occʳ j ∣ ε ∣̂ᵉ     q = str-occᵉ j ε (map-nothing ∣_∣̂ᵉ (strᵉ j ε) q)

mutual

  str-occᵛ : ∀ {Ω} → (j : EVar (Ω +e)) → (A : OVType (Ω +e))
           → strᵛ j A ≡ nothing → occᵉ-v j A ≡ true
  str-occᵛ j (tvar α)  ()
  str-occᵛ j (Base b)  ()
  str-occᵛ j unit      ()
  str-occᵛ j bool      ()
  str-occᵛ j nat       ()
  str-occᵛ j empty     ()
  str-occᵛ j (A |×| B) q with zip₂-nothing _|×|_ (strᵛ j A) (strᵛ j B) q
  ... | inj₁ s = ∨-left  (occᵉ-v j A) (occᵉ-v j B) (str-occᵛ j A s)
  ... | inj₂ s = ∨-right (occᵉ-v j A) (occᵉ-v j B) (str-occᵛ j B s)
  str-occᵛ j (A |+| B) q with zip₂-nothing _|+|_ (strᵛ j A) (strᵛ j B) q
  ... | inj₁ s = ∨-left  (occᵉ-v j A) (occᵉ-v j B) (str-occᵛ j A s)
  ... | inj₂ s = ∨-right (occᵉ-v j A) (occᵉ-v j B) (str-occᵛ j B s)
  str-occᵛ j (list A)  q = str-occᵛ j A (map-nothing list (strᵛ j A) q)
  str-occᵛ j (A ⇒ C)   q with zip₂-nothing _⇒_ (strᵛ j A) (strᶜ j C) q
  ... | inj₁ s = ∨-left  (occᵉ-v j A) (occᵉ-c j C) (str-occᵛ j A s)
  ... | inj₂ s = ∨-right (occᵉ-v j A) (occᵉ-c j C) (str-occᶜ j C s)
  str-occᵛ j (C ⇛ D)   q with zip₂-nothing _⇛_ (strᶜ j C) (strᶜ j D) q
  ... | inj₁ s = ∨-left  (occᵉ-c j C) (occᵉ-c j D) (str-occᶜ j C s)
  ... | inj₂ s = ∨-right (occᵉ-c j C) (occᵉ-c j D) (str-occᶜ j D s)
  str-occᵛ j ([ ρ ] A) q with zip₂-nothing [_]_ (strʳ j ρ) (strᵛ j A) q
  ... | inj₁ s = ∨-left  (occᵉ-r j ρ) (occᵉ-v j A) (str-occʳ j ρ s)
  ... | inj₂ s = ∨-right (occᵉ-r j ρ) (occᵉ-v j A) (str-occᵛ j A s)

  str-occᶜ : ∀ {Ω} → (j : EVar (Ω +e)) → (C : OCType (Ω +e))
           → strᶜ j C ≡ nothing → occᵉ-c j C ≡ true
  str-occᶜ j (A ! ε) q with zip₂-nothing _!_ (strᵛ j A) (strᵉ j ε) q
  ... | inj₁ s = ∨-left  (occᵉ-v j A) (occᵉ-e j ε) (str-occᵛ j A s)
  ... | inj₂ s = ∨-right (occᵉ-v j A) (occᵉ-e j ε) (str-occᵉ j ε s)

-- Contrapositive: a failed `strSub` refutes every instance keeping the rigid
-- an eigenvariable

strᵉ-just : ∀ {Ω Ξ} → (j : EVar (Ω +e)) → (ε : EExp (Ω +e))
          → (δ : Subst (Ω +e) (Ξ +e)) → sE δ j ≡ evar (newᵉ {Ξ})
          → (ε₀ : EExp Ξ) → ε [ δ ]ᵉ ≡ wkᵉ-e ε₀
          → Σ[ ε₁ ∈ EExp Ω ] (strᵉ j ε ≡ just ε₁)
strᵉ-just {Ω} {Ξ} j ε δ r ε₀ e =
  notNothing (strᵉ j ε)
    (λ q → occ-wkᵉ ε₀ (subst (λ x → occᵉ-e (newᵉ {Ξ}) x ≡ true) e
                             (escᵉ δ j (newᵉ {Ξ}) r ε (str-occᵉ j ε q))))

strʳ-just : ∀ {Ω Ξ} → (j : EVar (Ω +e)) → (ρ : RExp (Ω +e))
          → (δ : Subst (Ω +e) (Ξ +e)) → sE δ j ≡ evar (newᵉ {Ξ})
          → (ρ₀ : RExp Ξ) → ρ [ δ ]ʳ ≡ wkᵉ-r ρ₀
          → Σ[ ρ₁ ∈ RExp Ω ] (strʳ j ρ ≡ just ρ₁)
strʳ-just {Ω} {Ξ} j ρ δ r ρ₀ e =
  notNothing (strʳ j ρ)
    (λ q → occ-wkʳ ρ₀ (subst (λ x → occᵉ-r (newᵉ {Ξ}) x ≡ true) e
                             (escʳ δ j (newᵉ {Ξ}) r ρ (str-occʳ j ρ q))))

strᵛ-just : ∀ {Ω Ξ} → (j : EVar (Ω +e)) → (A : OVType (Ω +e))
          → (δ : Subst (Ω +e) (Ξ +e)) → sE δ j ≡ evar (newᵉ {Ξ})
          → (A₀ : OVType Ξ) → A [ δ ]ᵛ ≡ wkᵉ-v A₀
          → Σ[ A₁ ∈ OVType Ω ] (strᵛ j A ≡ just A₁)
strᵛ-just {Ω} {Ξ} j A δ r A₀ e =
  notNothing (strᵛ j A)
    (λ q → occ-wkᵛ A₀ (subst (λ x → occᵉ-v (newᵉ {Ξ}) x ≡ true) e
                             (escᵛ δ j (newᵉ {Ξ}) r A (str-occᵛ j A q))))

-- The verdicts, transported through the auxiliaries

strᵛ⁺-just : ∀ {Ω} → (j : EVar (Ω +e)) → (A : OVType (Ω +e)) → {A₁ : OVType Ω}
           → strᵛ j A ≡ just A₁
           → Σ[ y ∈ Σ[ A₀ ∈ OVType Ω ] (A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀) ] (strᵛ⁺ j A ≡ just y)
strᵛ⁺-just {Ω} j A = aux (strᵛ j A) refl
  where
    aux : (x : Maybe (OVType Ω)) → (eq : strᵛ j A ≡ x) → {A₁ : OVType Ω} → x ≡ just A₁
        → Σ[ y ∈ Σ[ A₀ ∈ OVType Ω ] (A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀) ] (strᵛᵃ j A x eq ≡ just y)
    aux (just A₀) eq refl = (A₀ , str-popᵛ j A eq) , refl
    aux nothing   eq ()

strʳ⁺-just : ∀ {Ω} → (j : EVar (Ω +e)) → (ρ : RExp (Ω +e)) → {ρ₁ : RExp Ω}
           → strʳ j ρ ≡ just ρ₁
           → Σ[ y ∈ Σ[ ρ₀ ∈ RExp Ω ] (ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀) ] (strʳ⁺ j ρ ≡ just y)
strʳ⁺-just {Ω} j ρ = aux (strʳ j ρ) refl
  where
    aux : (x : Maybe (RExp Ω)) → (eq : strʳ j ρ ≡ x) → {ρ₁ : RExp Ω} → x ≡ just ρ₁
        → Σ[ y ∈ Σ[ ρ₀ ∈ RExp Ω ] (ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀) ] (strʳᵃ j ρ x eq ≡ just y)
    aux (just ρ₀) eq refl = (ρ₀ , str-popʳ j ρ eq) , refl
    aux nothing   eq ()

strᵉ⁺-just : ∀ {Ω} → (j : EVar (Ω +e)) → (ε : EExp (Ω +e)) → {ε₁ : EExp Ω}
           → strᵉ j ε ≡ just ε₁
           → Σ[ y ∈ Σ[ ε₀ ∈ EExp Ω ] (ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀) ] (strᵉ⁺ j ε ≡ just y)
strᵉ⁺-just {Ω} j ε = aux (strᵉ j ε) refl
  where
    aux : (x : Maybe (EExp Ω)) → (eq : strᵉ j ε ≡ x) → {ε₁ : EExp Ω} → x ≡ just ε₁
        → Σ[ y ∈ Σ[ ε₀ ∈ EExp Ω ] (ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀) ] (strᵉᵃ j ε x eq ≡ just y)
    aux (just ε₀) eq refl = (ε₀ , str-popᵉ j ε eq) , refl
    aux nothing   eq ()

-- A finite traversal all of whose steps succeed

seqFinᵃ-just : ∀ {n} {X : Set} → (P : Fin (nsuc n) → X → Set)
             → (a : Maybe (Σ[ x ∈ X ] P zero x)) → (y : Σ[ x ∈ X ] P zero x) → a ≡ just y
             → (b : Maybe (Σ[ g ∈ (Fin n → X) ] ((i : Fin n) → P (suc i) (g i))))
             → (z : Σ[ g ∈ (Fin n → X) ] ((i : Fin n) → P (suc i) (g i))) → b ≡ just z
             → Σ[ w ∈ Σ[ g ∈ (Fin (nsuc n) → X) ] ((i : Fin (nsuc n)) → P i (g i)) ]
                 (seqFinᵃ P a b ≡ just w)
seqFinᵃ-just P .(just (x , p)) (x , p) refl .(just (g , q)) (g , q) refl =
  _ , refl

seqFin-total : ∀ {n} {X : Set} {P : Fin n → X → Set}
             → (f : (i : Fin n) → Maybe (Σ[ x ∈ X ] P i x))
             → ((i : Fin n) → Σ[ y ∈ Σ[ x ∈ X ] P i x ] (f i ≡ just y))
             → Σ[ z ∈ Σ[ g ∈ (Fin n → X) ] ((i : Fin n) → P i (g i)) ] (seqFin f ≡ just z)
seqFin-total {nzero}  f h = ((λ ()) , (λ ())) , refl
seqFin-total {nsuc n} {X} {P} f h =
  seqFinᵃ-just P (f zero) (proj₁ (h zero)) (proj₂ (h zero))
                 (seqFin {P = λ i x → P (suc i) x} (λ i → f (suc i))) (proj₁ ih) (proj₂ ih)
  where
    ih = seqFin-total {P = λ i x → P (suc i) x} (λ i → f (suc i)) (λ i → h (suc i))

strSubᵃ-just : ∀ {Θ Ω} → (j : EVar (Ω +e)) → (γ : Subst Θ (Ω +e))
             → (a : Maybe (Σ[ g ∈ (TyVar Θ → OVType Ω) ]
                             ((α : TyVar Θ) → sTy γ α [ popˢ j ]ᵛ ≡ wkᵉ-v (g α))))
             → (x : Σ[ g ∈ (TyVar Θ → OVType Ω) ]
                      ((α : TyVar Θ) → sTy γ α [ popˢ j ]ᵛ ≡ wkᵉ-v (g α))) → a ≡ just x
             → (b : Maybe (Σ[ g ∈ (RVar Θ → RExp Ω) ]
                             ((i : RVar Θ) → sR γ i [ popˢ j ]ʳ ≡ wkᵉ-r (g i))))
             → (y : Σ[ g ∈ (RVar Θ → RExp Ω) ]
                      ((i : RVar Θ) → sR γ i [ popˢ j ]ʳ ≡ wkᵉ-r (g i))) → b ≡ just y
             → (c : Maybe (Σ[ g ∈ (EVar Θ → EExp Ω) ]
                             ((i : EVar Θ) → sE γ i [ popˢ j ]ᵉ ≡ wkᵉ-e (g i))))
             → (z : Σ[ g ∈ (EVar Θ → EExp Ω) ]
                      ((i : EVar Θ) → sE γ i [ popˢ j ]ᵉ ≡ wkᵉ-e (g i))) → c ≡ just z
             → Σ[ w ∈ Σ[ γ₀ ∈ Subst Θ Ω ] ((γ ⨟ˢ popˢ j) ≐ˢ (γ₀ ⨟ˢ wkˢᵉ)) ]
                 (strSubᵃ j γ a b c ≡ just w)
strSubᵃ-just j γ .(just (fT , pT)) (fT , pT) refl
                 .(just (fR , pR)) (fR , pR) refl
                 .(just (fE , pE)) (fE , pE) refl = _ , refl

-- The escape check is complete: if it fails, no instance keeping the rigid an
-- eigenvariable frees the images of it

strSub-escape : ∀ {Θ Ω Ξ} → (j : EVar (Ω +e)) → (γ : Subst Θ (Ω +e))
              → (δ : Subst (Ω +e) (Ξ +e)) → sE δ j ≡ evar (newᵉ {Ξ})
              → (γ₀ : Subst Θ Ξ) → (γ ⨟ˢ δ) ≐ˢ (γ₀ ⨟ˢ wkˢᵉ)
              → strSub j γ ≡ nothing → ⊥
strSub-escape {Θ} {Ω} {Ξ} j γ δ r γ₀ p q = ⊥just (trans (sym q) (proj₂ done))
  where
    hT : (α : TyVar Θ)
       → Σ[ y ∈ Σ[ A₀ ∈ OVType Ω ] (sTy γ α [ popˢ j ]ᵛ ≡ wkᵉ-v A₀) ]
           (strᵛ⁺ j (sTy γ α) ≡ just y)
    hT α = strᵛ⁺-just j (sTy γ α)
             (proj₂ (strᵛ-just j (sTy γ α) δ r (sTy γ₀ α)
                       (trans (≐ᵗ p α) (wkˢᵉ-v (sTy γ₀ α)))))

    hR : (i : RVar Θ)
       → Σ[ y ∈ Σ[ ρ₀ ∈ RExp Ω ] (sR γ i [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀) ]
           (strʳ⁺ j (sR γ i) ≡ just y)
    hR i = strʳ⁺-just j (sR γ i)
             (proj₂ (strʳ-just j (sR γ i) δ r (sR γ₀ i)
                       (trans (≐ʳ p i) (wkˢᵉ-r (sR γ₀ i)))))

    hE : (i : EVar Θ)
       → Σ[ y ∈ Σ[ ε₀ ∈ EExp Ω ] (sE γ i [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀) ]
           (strᵉ⁺ j (sE γ i) ≡ just y)
    hE i = strᵉ⁺-just j (sE γ i)
             (proj₂ (strᵉ-just j (sE γ i) δ r (sE γ₀ i)
                       (trans (≐ᵉ p i) (wkˢᵉ-e (sE γ₀ i)))))

    tT = seqFin-total (λ α → strᵛ⁺ j (sTy γ α)) hT
    tR = seqFin-total (λ i → strʳ⁺ j (sR  γ i)) hR
    tE = seqFin-total (λ i → strᵉ⁺ j (sE  γ i)) hE

    done : Σ[ x ∈ Σ[ γ₁ ∈ Subst Θ Ω ] ((γ ⨟ˢ popˢ j) ≐ˢ (γ₁ ⨟ˢ wkˢᵉ)) ]
             (strSub j γ ≡ just x)
    done = strSubᵃ-just j γ _ (proj₁ tT) (proj₂ tT)
                            _ (proj₁ tR) (proj₂ tR)
                            _ (proj₁ tE) (proj₂ tE)

-- With the rigid sent to a constant, an expression strengthens away from it

strᵉ-upd : ∀ {Ω} → (j : EVar (Ω +e)) → (c : E) → (ε : EExp (Ω +e))
         → Σ[ ε₀ ∈ EExp Ω ] (strᵉ j (ε [ updᵉ j (econst c) ]ᵉ) ≡ just ε₀)
strᵉ-upd {Ω} j c (evar k) with k ≟ᶠ j
... | yes refl = econst c , refl
... | no ne with thickᵉ {Ω} j k in r
...   | just k₀ = evar k₀ , refl
...   | nothing = ⊥-elim (ne (thick-nothing j k r))
strᵉ-upd j c (econst c')  = econst c' , refl
strᵉ-upd j c (ε ·̂ₑ ε') with strᵉ-upd j c ε | strᵉ-upd j c ε'
... | a , qa | b , qb = a ·̂ₑ b , cong₂ (zip₂ _·̂ₑ_) qa qb
strᵉ-upd j c (ε ⊔̂ₑ ε') with strᵉ-upd j c ε | strᵉ-upd j c ε'
... | a , qa | b , qb = a ⊔̂ₑ b , cong₂ (zip₂ _⊔̂ₑ_) qa qb

strʳ-upd : ∀ {Ω} → (j : EVar (Ω +e)) → (c : E) → (ρ : RExp (Ω +e))
         → Σ[ ρ₀ ∈ RExp Ω ] (strʳ j (ρ [ updᵉ j (econst c) ]ʳ) ≡ just ρ₀)
strʳ-upd j c (rvar i)   = rvar i , refl
strʳ-upd j c (rconst c') = rconst c' , refl
strʳ-upd j c (ρ ·̂ᵣ ρ') with strʳ-upd j c ρ | strʳ-upd j c ρ'
... | a , qa | b , qb = a ·̂ᵣ b , cong₂ (zip₂ _·̂ᵣ_) qa qb
strʳ-upd j c (ρ ⊔̂ᵣ ρ') with strʳ-upd j c ρ | strʳ-upd j c ρ'
... | a , qa | b , qb = a ⊔̂ᵣ b , cong₂ (zip₂ _⊔̂ᵣ_) qa qb
strʳ-upd j c ∣ ε ∣̂ᵉ with strᵉ-upd j c ε
... | a , qa = ∣ a ∣̂ᵉ , cong (mmap ∣_∣̂ᵉ) qa
