------------------------------------------------------------------
-- Strengthening away a rigid variable                          --
--                                                              --
-- A rigid effect-grade variable is strengthened away when its  --
-- scope is left. `popˢ` and `unpopˢ` move the rigid to the     --
-- newest position. The escape lemma states that a failed       --
-- strengthening refutes every instance that keeps the rigid an --
-- eigenvariable.                                               --
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

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Inference.SolverImpl.Core.Rigid (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import OpenCalculus.Syntax.Grades S
open import OpenCalculus.Syntax.Types  S
open import OpenCalculus.Syntax.Subst  S

open import OpenCalculus.Inference.SolverImpl.Core.Thick
open import OpenCalculus.Inference.SolverImpl.Core.Occurs S

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

strᵉ : ∀ {Ψ} → EVar (Ψ +e) → EExp (Ψ +e) → Maybe (EExp Ψ)
strᵉ {Ψ} j (evar k)   = mmap evar (thickᵉ {Ψ} j k)
strᵉ     j (econst c) = just (econst c)
strᵉ     j (ε ·̂ₑ ε')  = zip₂ _·̂ₑ_ (strᵉ j ε) (strᵉ j ε')
strᵉ     j (ε ⊔̂ₑ ε')  = zip₂ _⊔̂ₑ_ (strᵉ j ε) (strᵉ j ε')

strʳ : ∀ {Ψ} → EVar (Ψ +e) → RExp (Ψ +e) → Maybe (RExp Ψ)
strʳ j (rvar i)   = just (rvar i)
strʳ j (rconst c) = just (rconst c)
strʳ j (ρ ·̂ᵣ ρ')  = zip₂ _·̂ᵣ_ (strʳ j ρ) (strʳ j ρ')
strʳ j (ρ ⊔̂ᵣ ρ')  = zip₂ _⊔̂ᵣ_ (strʳ j ρ) (strʳ j ρ')
strʳ j ∣ ε ∣̂ᵉ     = mmap ∣_∣̂ᵉ (strᵉ j ε)

mutual

  strᵛ : ∀ {Ψ} → EVar (Ψ +e) → OVType (Ψ +e) → Maybe (OVType Ψ)
  strᵛ j (tvar α)  = just (tvar α)
  strᵛ j (Base b)  = just (Base b)
  strᵛ j Unit      = just Unit
  strᵛ j Bool      = just Bool
  strᵛ j Nat       = just Nat
  strᵛ j (A |×| B) = zip₂ _|×|_ (strᵛ j A) (strᵛ j B)
  strᵛ j (A |+| B) = zip₂ _|+|_ (strᵛ j A) (strᵛ j B)
  strᵛ j (|List| A) = mmap |List| (strᵛ j A)
  strᵛ j Empty     = just Empty
  strᵛ j (A ⇒ C)   = zip₂ _⇒_ (strᵛ j A) (strᶜ j C)
  strᵛ j (C ⇛ D)   = zip₂ _⇛_ (strᶜ j C) (strᶜ j D)
  strᵛ j ([ ρ ] A) = zip₂ [_]_ (strʳ j ρ) (strᵛ j A)

  strᶜ : ∀ {Ψ} → EVar (Ψ +e) → OCType (Ψ +e) → Maybe (OCType Ψ)
  strᶜ j (A ‼ ε) = zip₂ _‼_ (strᵛ j A) (strᵉ j ε)

popˢ : ∀ {Ψ} → EVar (Ψ +e) → Subst (Ψ +e) (Ψ +e)
popˢ {Ψ} j = sub tvar rvar
                 (λ k → maybe′ (λ k₀ → evar (wkᵉ-ev Ψ k₀))
                               (evar (newᵉ {Ψ}))
                               (thickᵉ {Ψ} j k))

popˢ-hit : ∀ {Ψ} → (j : EVar (Ψ +e)) → sE (popˢ {Ψ} j) j ≡ evar (newᵉ {Ψ})
popˢ-hit {Ψ} j =
  cong (maybe′ (λ k₀ → evar (wkᵉ-ev Ψ k₀)) (evar (newᵉ {Ψ}))) (thick-refl {nE Ψ} j)

str-popᵉ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (ε : EExp (Ψ +e)) → {ε₀ : EExp Ψ}
         → strᵉ j ε ≡ just ε₀ → ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀
str-popᵉ {Ψ} j (evar k)   q with map-just evar (thickᵉ {Ψ} j k) q
... | k₀ , qk , refl =
  cong (maybe′ (λ k₁ → evar (wkᵉ-ev Ψ k₁)) (evar (newᵉ {Ψ}))) qk
str-popᵉ     j (econst c) refl = refl
str-popᵉ     j (ε ·̂ₑ ε')  q with zip₂-just _·̂ₑ_ (strᵉ j ε) (strᵉ j ε') q
... | a , b , qa , qb , refl = cong₂ _·̂ₑ_ (str-popᵉ j ε qa) (str-popᵉ j ε' qb)
str-popᵉ     j (ε ⊔̂ₑ ε')  q with zip₂-just _⊔̂ₑ_ (strᵉ j ε) (strᵉ j ε') q
... | a , b , qa , qb , refl = cong₂ _⊔̂ₑ_ (str-popᵉ j ε qa) (str-popᵉ j ε' qb)

str-popʳ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (ρ : RExp (Ψ +e)) → {ρ₀ : RExp Ψ}
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

  str-popᵛ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (A : OVType (Ψ +e)) → {A₀ : OVType Ψ}
           → strᵛ j A ≡ just A₀ → A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀
  str-popᵛ j (tvar α)  refl = refl
  str-popᵛ j (Base b)  refl = refl
  str-popᵛ j Unit      refl = refl
  str-popᵛ j Bool      refl = refl
  str-popᵛ j Nat       refl = refl
  str-popᵛ j Empty     refl = refl
  str-popᵛ j (A |×| B) q with zip₂-just _|×|_ (strᵛ j A) (strᵛ j B) q
  ... | a , b , qa , qb , refl = cong₂ _|×|_ (str-popᵛ j A qa) (str-popᵛ j B qb)
  str-popᵛ j (A |+| B) q with zip₂-just _|+|_ (strᵛ j A) (strᵛ j B) q
  ... | a , b , qa , qb , refl = cong₂ _|+|_ (str-popᵛ j A qa) (str-popᵛ j B qb)
  str-popᵛ j (|List| A) q with map-just |List| (strᵛ j A) q
  ... | a , qa , refl = cong |List| (str-popᵛ j A qa)
  str-popᵛ j (A ⇒ C)   q with zip₂-just _⇒_ (strᵛ j A) (strᶜ j C) q
  ... | a , b , qa , qb , refl = cong₂ _⇒_ (str-popᵛ j A qa) (str-popᶜ j C qb)
  str-popᵛ j (C ⇛ D)   q with zip₂-just _⇛_ (strᶜ j C) (strᶜ j D) q
  ... | a , b , qa , qb , refl = cong₂ _⇛_ (str-popᶜ j C qa) (str-popᶜ j D qb)
  str-popᵛ j ([ ρ ] A) q with zip₂-just [_]_ (strʳ j ρ) (strᵛ j A) q
  ... | a , b , qa , qb , refl = cong₂ [_]_ (str-popʳ j ρ qa) (str-popᵛ j A qb)

  str-popᶜ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (C : OCType (Ψ +e)) → {C₀ : OCType Ψ}
           → strᶜ j C ≡ just C₀ → C [ popˢ j ]ᶜ ≡ wkᵉ-c C₀
  str-popᶜ j (A ‼ ε) q with zip₂-just _‼_ (strᵛ j A) (strᵉ j ε) q
  ... | a , b , qa , qb , refl = cong₂ _‼_ (str-popᵛ j A qa) (str-popᵉ j ε qb)

str-wkᵉ : ∀ {Ψ} → (ε : EExp Ψ) → strᵉ (newᵉ {Ψ}) (wkᵉ-e ε) ≡ just ε
str-wkᵉ (evar i)   = refl
str-wkᵉ (econst c) = refl
str-wkᵉ (ε ·̂ₑ ε')  = cong₂ (zip₂ _·̂ₑ_) (str-wkᵉ ε) (str-wkᵉ ε')
str-wkᵉ (ε ⊔̂ₑ ε')  = cong₂ (zip₂ _⊔̂ₑ_) (str-wkᵉ ε) (str-wkᵉ ε')

str-wkʳ : ∀ {Ψ} → (ρ : RExp Ψ) → strʳ (newᵉ {Ψ}) (wkᵉ-r ρ) ≡ just ρ
str-wkʳ (rvar i)   = refl
str-wkʳ (rconst c) = refl
str-wkʳ (ρ ·̂ᵣ ρ')  = cong₂ (zip₂ _·̂ᵣ_) (str-wkʳ ρ) (str-wkʳ ρ')
str-wkʳ (ρ ⊔̂ᵣ ρ')  = cong₂ (zip₂ _⊔̂ᵣ_) (str-wkʳ ρ) (str-wkʳ ρ')
str-wkʳ ∣ ε ∣̂ᵉ     = cong (mmap ∣_∣̂ᵉ) (str-wkᵉ ε)

mutual

  str-wkᵛ : ∀ {Ψ} → (A : OVType Ψ) → strᵛ (newᵉ {Ψ}) (wkᵉ-v A) ≡ just A
  str-wkᵛ (tvar α)  = refl
  str-wkᵛ (Base b)  = refl
  str-wkᵛ Unit      = refl
  str-wkᵛ Bool      = refl
  str-wkᵛ Nat       = refl
  str-wkᵛ Empty     = refl
  str-wkᵛ (A |×| B) = cong₂ (zip₂ _|×|_) (str-wkᵛ A) (str-wkᵛ B)
  str-wkᵛ (A |+| B) = cong₂ (zip₂ _|+|_) (str-wkᵛ A) (str-wkᵛ B)
  str-wkᵛ (|List| A) = cong (mmap |List|) (str-wkᵛ A)
  str-wkᵛ (A ⇒ C)   = cong₂ (zip₂ _⇒_) (str-wkᵛ A) (str-wkᶜ C)
  str-wkᵛ (C ⇛ D)   = cong₂ (zip₂ _⇛_) (str-wkᶜ C) (str-wkᶜ D)
  str-wkᵛ ([ ρ ] A) = cong₂ (zip₂ [_]_) (str-wkʳ ρ) (str-wkᵛ A)

  str-wkᶜ : ∀ {Ψ} → (C : OCType Ψ) → strᶜ (newᵉ {Ψ}) (wkᵉ-c C) ≡ just C
  str-wkᶜ (A ‼ ε) = cong₂ (zip₂ _‼_) (str-wkᵛ A) (str-wkᵉ ε)

-- Assembles the pointwise partial results of the three finite sorts by
-- a finite traversal. The auxiliaries take the scrutinee explicitly.

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

strᵛᵃ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (A : OVType (Ψ +e))
      → (x : Maybe (OVType Ψ)) → strᵛ j A ≡ x
      → Maybe (Σ[ A₀ ∈ OVType Ψ ] (A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀))
strᵛᵃ j A (just A₀) eq = just (A₀ , str-popᵛ j A eq)
strᵛᵃ j A nothing   eq = nothing

strʳᵃ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (ρ : RExp (Ψ +e))
      → (x : Maybe (RExp Ψ)) → strʳ j ρ ≡ x
      → Maybe (Σ[ ρ₀ ∈ RExp Ψ ] (ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀))
strʳᵃ j ρ (just ρ₀) eq = just (ρ₀ , str-popʳ j ρ eq)
strʳᵃ j ρ nothing   eq = nothing

strᵉᵃ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (ε : EExp (Ψ +e))
      → (x : Maybe (EExp Ψ)) → strᵉ j ε ≡ x
      → Maybe (Σ[ ε₀ ∈ EExp Ψ ] (ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀))
strᵉᵃ j ε (just ε₀) eq = just (ε₀ , str-popᵉ j ε eq)
strᵉᵃ j ε nothing   eq = nothing

strᵛ⁺ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (A : OVType (Ψ +e))
      → Maybe (Σ[ A₀ ∈ OVType Ψ ] (A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀))
strᵛ⁺ j A = strᵛᵃ j A (strᵛ j A) refl

strʳ⁺ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (ρ : RExp (Ψ +e))
      → Maybe (Σ[ ρ₀ ∈ RExp Ψ ] (ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀))
strʳ⁺ j ρ = strʳᵃ j ρ (strʳ j ρ) refl

strᵉ⁺ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (ε : EExp (Ψ +e))
      → Maybe (Σ[ ε₀ ∈ EExp Ψ ] (ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀))
strᵉ⁺ j ε = strᵉᵃ j ε (strᵉ j ε) refl

strSubᵃ : ∀ {Θ Ψ} → (j : EVar (Ψ +e)) → (γ : Subst Θ (Ψ +e))
        → Maybe (Σ[ g ∈ (TyVar Θ → OVType Ψ) ]
                   ((α : TyVar Θ) → sTy γ α [ popˢ j ]ᵛ ≡ wkᵉ-v (g α)))
        → Maybe (Σ[ g ∈ (RVar Θ → RExp Ψ) ]
                   ((i : RVar Θ) → sR γ i [ popˢ j ]ʳ ≡ wkᵉ-r (g i)))
        → Maybe (Σ[ g ∈ (EVar Θ → EExp Ψ) ]
                   ((i : EVar Θ) → sE γ i [ popˢ j ]ᵉ ≡ wkᵉ-e (g i)))
        → Maybe (Σ[ γ₀ ∈ Subst Θ Ψ ] ((γ ⨟ˢ popˢ j) ≐ˢ (γ₀ ⨟ˢ wkˢᵉ)))
strSubᵃ j γ (just (fT , pT)) (just (fR , pR)) (just (fE , pE)) =
  just (sub fT fR fE ,
        mk≐ˢ (λ α → trans (pT α) (sym (wkˢᵉ-v (fT α))))
             (λ i → trans (pR i) (sym (wkˢᵉ-r (fR i))))
             (λ i → trans (pE i) (sym (wkˢᵉ-e (fE i)))))
strSubᵃ j γ (just _) (just _) nothing = nothing
strSubᵃ j γ (just _) nothing  _       = nothing
strSubᵃ j γ nothing  _        _       = nothing

strSub : ∀ {Θ Ψ} → (j : EVar (Ψ +e)) → (γ : Subst Θ (Ψ +e))
       → Maybe (Σ[ γ₀ ∈ Subst Θ Ψ ] ((γ ⨟ˢ popˢ j) ≐ˢ (γ₀ ⨟ˢ wkˢᵉ)))
strSub j γ = strSubᵃ j γ (seqFin (λ α → strᵛ⁺ j (sTy γ α)))
                         (seqFin (λ i → strʳ⁺ j (sR  γ i)))
                         (seqFin (λ i → strᵉ⁺ j (sE  γ i)))

unpopˢ : ∀ {Ψ} → EVar (Ψ +e) → Subst (Ψ +e) (Ψ +e)
unpopˢ {Ψ} j = sub tvar rvar (λ { zero → evar j ; (suc k) → evar (thinᵉ {Ψ} j k) })

-- Thickening is `nothing` only at the variable itself

thick-nothing : ∀ {n} → (i j : Fin (nsuc n)) → thick i j ≡ nothing → j ≡ i
thick-nothing          zero   zero    q = refl
thick-nothing          zero   (suc j) ()
thick-nothing {nsuc n} (suc i) zero   ()
thick-nothing {nsuc n} (suc i) (suc j) q with thick i j in r
... | nothing = cong suc (thick-nothing i j r)

pop-unpop : ∀ {Ψ} → (j : EVar (Ψ +e)) → (popˢ j ⨟ˢ unpopˢ j) ≐ˢ idˢ
pop-unpop {Ψ} j = mk≐ˢ (λ α → refl) (λ i → refl) sE'
  where
    sE' : (k : EVar (Ψ +e)) → sE (popˢ {Ψ} j ⨟ˢ unpopˢ {Ψ} j) k ≡ sE (idˢ {Ψ +e}) k
    sE' k with thickᵉ {Ψ} j k in r
    ... | just k₀  = cong evar (sym (thick-just {nE Ψ} j k k₀ r))
    ... | nothing  = cong evar (sym (thick-nothing {nE Ψ} j k r))

-- An occurrence of a variable whose image is again a variable is
-- renamed, not removed — Miller's mixed-prefix discipline (1992), the
-- rigid playing Gentzen's eigenvariable.

escᵉ : ∀ {Φ Ψ} → (σ : Subst Φ Ψ) → (j : EVar Φ) → (k : EVar Ψ) → sE σ j ≡ evar k
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

escʳ : ∀ {Φ Ψ} → (σ : Subst Φ Ψ) → (j : EVar Φ) → (k : EVar Ψ) → sE σ j ≡ evar k
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

  escᵛ : ∀ {Φ Ψ} → (σ : Subst Φ Ψ) → (j : EVar Φ) → (k : EVar Ψ) → sE σ j ≡ evar k
       → (A : OVType Φ) → occᵉ-v j A ≡ true → occᵉ-v k (A [ σ ]ᵛ) ≡ true
  escᵛ σ j k r (tvar α)  ()
  escᵛ σ j k r (Base b)  ()
  escᵛ σ j k r Unit      ()
  escᵛ σ j k r Bool      ()
  escᵛ σ j k r Nat       ()
  escᵛ σ j k r Empty     ()
  escᵛ σ j k r (A |×| B) q with ∨-true (occᵉ-v j A) (occᵉ-v j B) q
  ... | inj₁ s = ∨-left  (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-v k (B [ σ ]ᵛ)) (escᵛ σ j k r A s)
  ... | inj₂ s = ∨-right (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-v k (B [ σ ]ᵛ)) (escᵛ σ j k r B s)
  escᵛ σ j k r (A |+| B) q with ∨-true (occᵉ-v j A) (occᵉ-v j B) q
  ... | inj₁ s = ∨-left  (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-v k (B [ σ ]ᵛ)) (escᵛ σ j k r A s)
  ... | inj₂ s = ∨-right (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-v k (B [ σ ]ᵛ)) (escᵛ σ j k r B s)
  escᵛ σ j k r (|List| A) q = escᵛ σ j k r A q
  escᵛ σ j k r (A ⇒ C)   q with ∨-true (occᵉ-v j A) (occᵉ-c j C) q
  ... | inj₁ s = ∨-left  (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-c k (C [ σ ]ᶜ)) (escᵛ σ j k r A s)
  ... | inj₂ s = ∨-right (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-c k (C [ σ ]ᶜ)) (escᶜ σ j k r C s)
  escᵛ σ j k r (C ⇛ D)   q with ∨-true (occᵉ-c j C) (occᵉ-c j D) q
  ... | inj₁ s = ∨-left  (occᵉ-c k (C [ σ ]ᶜ)) (occᵉ-c k (D [ σ ]ᶜ)) (escᶜ σ j k r C s)
  ... | inj₂ s = ∨-right (occᵉ-c k (C [ σ ]ᶜ)) (occᵉ-c k (D [ σ ]ᶜ)) (escᶜ σ j k r D s)
  escᵛ σ j k r ([ ρ ] A) q with ∨-true (occᵉ-r j ρ) (occᵉ-v j A) q
  ... | inj₁ s = ∨-left  (occᵉ-r k (ρ [ σ ]ʳ)) (occᵉ-v k (A [ σ ]ᵛ)) (escʳ σ j k r ρ s)
  ... | inj₂ s = ∨-right (occᵉ-r k (ρ [ σ ]ʳ)) (occᵉ-v k (A [ σ ]ᵛ)) (escᵛ σ j k r A s)

  escᶜ : ∀ {Φ Ψ} → (σ : Subst Φ Ψ) → (j : EVar Φ) → (k : EVar Ψ) → sE σ j ≡ evar k
       → (C : OCType Φ) → occᵉ-c j C ≡ true → occᵉ-c k (C [ σ ]ᶜ) ≡ true
  escᶜ σ j k r (A ‼ ε) q with ∨-true (occᵉ-v j A) (occᵉ-e j ε) q
  ... | inj₁ s = ∨-left  (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-e k (ε [ σ ]ᵉ)) (escᵛ σ j k r A s)
  ... | inj₂ s = ∨-right (occᵉ-v k (A [ σ ]ᵛ)) (occᵉ-e k (ε [ σ ]ᵉ)) (escᵉ σ j k r ε s)

occ-wkᵉ : ∀ {Ψ} → (ε : EExp Ψ) → occᵉ-e (newᵉ {Ψ}) (wkᵉ-e ε) ≡ true → ⊥
occ-wkᵉ {Ψ} (evar i)   q with true-dec (newᵉ {Ψ} ≟ᶠ wkᵉ-ev Ψ i) q
... | ()
occ-wkᵉ     (econst c) ()
occ-wkᵉ {Ψ} (ε ·̂ₑ ε')  q =
  [ occ-wkᵉ ε , occ-wkᵉ ε' ]′
    (∨-true (occᵉ-e (newᵉ {Ψ}) (wkᵉ-e ε)) (occᵉ-e (newᵉ {Ψ}) (wkᵉ-e ε')) q)
occ-wkᵉ {Ψ} (ε ⊔̂ₑ ε')  q =
  [ occ-wkᵉ ε , occ-wkᵉ ε' ]′
    (∨-true (occᵉ-e (newᵉ {Ψ}) (wkᵉ-e ε)) (occᵉ-e (newᵉ {Ψ}) (wkᵉ-e ε')) q)

occ-wkʳ : ∀ {Ψ} → (ρ : RExp Ψ) → occᵉ-r (newᵉ {Ψ}) (wkᵉ-r ρ) ≡ true → ⊥
occ-wkʳ     (rvar i)   ()
occ-wkʳ     (rconst c) ()
occ-wkʳ {Ψ} (ρ ·̂ᵣ ρ')  q =
  [ occ-wkʳ ρ , occ-wkʳ ρ' ]′
    (∨-true (occᵉ-r (newᵉ {Ψ}) (wkᵉ-r ρ)) (occᵉ-r (newᵉ {Ψ}) (wkᵉ-r ρ')) q)
occ-wkʳ {Ψ} (ρ ⊔̂ᵣ ρ')  q =
  [ occ-wkʳ ρ , occ-wkʳ ρ' ]′
    (∨-true (occᵉ-r (newᵉ {Ψ}) (wkᵉ-r ρ)) (occᵉ-r (newᵉ {Ψ}) (wkᵉ-r ρ')) q)
occ-wkʳ     ∣ ε ∣̂ᵉ     q = occ-wkᵉ ε q

mutual

  occ-wkᵛ : ∀ {Ψ} → (A : OVType Ψ) → occᵉ-v (newᵉ {Ψ}) (wkᵉ-v A) ≡ true → ⊥
  occ-wkᵛ (tvar α)  ()
  occ-wkᵛ (Base b)  ()
  occ-wkᵛ Unit      ()
  occ-wkᵛ Bool      ()
  occ-wkᵛ Nat       ()
  occ-wkᵛ Empty     ()
  occ-wkᵛ {Ψ} (A |×| B) q =
    [ occ-wkᵛ A , occ-wkᵛ B ]′
      (∨-true (occᵉ-v (newᵉ {Ψ}) (wkᵉ-v A)) (occᵉ-v (newᵉ {Ψ}) (wkᵉ-v B)) q)
  occ-wkᵛ {Ψ} (A |+| B) q =
    [ occ-wkᵛ A , occ-wkᵛ B ]′
      (∨-true (occᵉ-v (newᵉ {Ψ}) (wkᵉ-v A)) (occᵉ-v (newᵉ {Ψ}) (wkᵉ-v B)) q)
  occ-wkᵛ {Ψ} (|List| A) q = occ-wkᵛ A q
  occ-wkᵛ {Ψ} (A ⇒ C)   q =
    [ occ-wkᵛ A , occ-wkᶜ C ]′
      (∨-true (occᵉ-v (newᵉ {Ψ}) (wkᵉ-v A)) (occᵉ-c (newᵉ {Ψ}) (wkᵉ-c C)) q)
  occ-wkᵛ {Ψ} (C ⇛ D)   q =
    [ occ-wkᶜ C , occ-wkᶜ D ]′
      (∨-true (occᵉ-c (newᵉ {Ψ}) (wkᵉ-c C)) (occᵉ-c (newᵉ {Ψ}) (wkᵉ-c D)) q)
  occ-wkᵛ {Ψ} ([ ρ ] A) q =
    [ occ-wkʳ ρ , occ-wkᵛ A ]′
      (∨-true (occᵉ-r (newᵉ {Ψ}) (wkᵉ-r ρ)) (occᵉ-v (newᵉ {Ψ}) (wkᵉ-v A)) q)

  occ-wkᶜ : ∀ {Ψ} → (C : OCType Ψ) → occᵉ-c (newᵉ {Ψ}) (wkᵉ-c C) ≡ true → ⊥
  occ-wkᶜ {Ψ} (A ‼ ε) q =
    [ occ-wkᵛ A , occ-wkᵉ ε ]′
      (∨-true (occᵉ-v (newᵉ {Ψ}) (wkᵉ-v A)) (occᵉ-e (newᵉ {Ψ}) (wkᵉ-e ε)) q)

str-occᵉ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (ε : EExp (Ψ +e))
         → strᵉ j ε ≡ nothing → occᵉ-e j ε ≡ true
str-occᵉ {Ψ} j (evar k)   q =
  dec-true (j ≟ᶠ k) (sym (thick-nothing {nE Ψ} j k (map-nothing evar (thickᵉ {Ψ} j k) q)))
str-occᵉ     j (econst c) ()
str-occᵉ     j (ε ·̂ₑ ε')  q with zip₂-nothing _·̂ₑ_ (strᵉ j ε) (strᵉ j ε') q
... | inj₁ s = ∨-left  (occᵉ-e j ε) (occᵉ-e j ε') (str-occᵉ j ε s)
... | inj₂ s = ∨-right (occᵉ-e j ε) (occᵉ-e j ε') (str-occᵉ j ε' s)
str-occᵉ     j (ε ⊔̂ₑ ε')  q with zip₂-nothing _⊔̂ₑ_ (strᵉ j ε) (strᵉ j ε') q
... | inj₁ s = ∨-left  (occᵉ-e j ε) (occᵉ-e j ε') (str-occᵉ j ε s)
... | inj₂ s = ∨-right (occᵉ-e j ε) (occᵉ-e j ε') (str-occᵉ j ε' s)

str-occʳ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (ρ : RExp (Ψ +e))
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

  str-occᵛ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (A : OVType (Ψ +e))
           → strᵛ j A ≡ nothing → occᵉ-v j A ≡ true
  str-occᵛ j (tvar α)  ()
  str-occᵛ j (Base b)  ()
  str-occᵛ j Unit      ()
  str-occᵛ j Bool      ()
  str-occᵛ j Nat       ()
  str-occᵛ j Empty     ()
  str-occᵛ j (A |×| B) q with zip₂-nothing _|×|_ (strᵛ j A) (strᵛ j B) q
  ... | inj₁ s = ∨-left  (occᵉ-v j A) (occᵉ-v j B) (str-occᵛ j A s)
  ... | inj₂ s = ∨-right (occᵉ-v j A) (occᵉ-v j B) (str-occᵛ j B s)
  str-occᵛ j (A |+| B) q with zip₂-nothing _|+|_ (strᵛ j A) (strᵛ j B) q
  ... | inj₁ s = ∨-left  (occᵉ-v j A) (occᵉ-v j B) (str-occᵛ j A s)
  ... | inj₂ s = ∨-right (occᵉ-v j A) (occᵉ-v j B) (str-occᵛ j B s)
  str-occᵛ j (|List| A) q = str-occᵛ j A (map-nothing |List| (strᵛ j A) q)
  str-occᵛ j (A ⇒ C)   q with zip₂-nothing _⇒_ (strᵛ j A) (strᶜ j C) q
  ... | inj₁ s = ∨-left  (occᵉ-v j A) (occᵉ-c j C) (str-occᵛ j A s)
  ... | inj₂ s = ∨-right (occᵉ-v j A) (occᵉ-c j C) (str-occᶜ j C s)
  str-occᵛ j (C ⇛ D)   q with zip₂-nothing _⇛_ (strᶜ j C) (strᶜ j D) q
  ... | inj₁ s = ∨-left  (occᵉ-c j C) (occᵉ-c j D) (str-occᶜ j C s)
  ... | inj₂ s = ∨-right (occᵉ-c j C) (occᵉ-c j D) (str-occᶜ j D s)
  str-occᵛ j ([ ρ ] A) q with zip₂-nothing [_]_ (strʳ j ρ) (strᵛ j A) q
  ... | inj₁ s = ∨-left  (occᵉ-r j ρ) (occᵉ-v j A) (str-occʳ j ρ s)
  ... | inj₂ s = ∨-right (occᵉ-r j ρ) (occᵉ-v j A) (str-occᵛ j A s)

  str-occᶜ : ∀ {Ψ} → (j : EVar (Ψ +e)) → (C : OCType (Ψ +e))
           → strᶜ j C ≡ nothing → occᵉ-c j C ≡ true
  str-occᶜ j (A ‼ ε) q with zip₂-nothing _‼_ (strᵛ j A) (strᵉ j ε) q
  ... | inj₁ s = ∨-left  (occᵉ-v j A) (occᵉ-e j ε) (str-occᵛ j A s)
  ... | inj₂ s = ∨-right (occᵉ-v j A) (occᵉ-e j ε) (str-occᵉ j ε s)

-- Contrapositive: a `strSub` that fails refutes every instance that
-- keeps the rigid an eigenvariable.

strᵉ-just : ∀ {Ψ Ξ} → (j : EVar (Ψ +e)) → (ε : EExp (Ψ +e))
          → (δ : Subst (Ψ +e) (Ξ +e)) → sE δ j ≡ evar (newᵉ {Ξ})
          → (ε₀ : EExp Ξ) → ε [ δ ]ᵉ ≡ wkᵉ-e ε₀
          → Σ[ ε₁ ∈ EExp Ψ ] (strᵉ j ε ≡ just ε₁)
strᵉ-just {Ψ} {Ξ} j ε δ r ε₀ e =
  notNothing (strᵉ j ε)
    (λ q → occ-wkᵉ ε₀ (subst (λ x → occᵉ-e (newᵉ {Ξ}) x ≡ true) e
                             (escᵉ δ j (newᵉ {Ξ}) r ε (str-occᵉ j ε q))))

strʳ-just : ∀ {Ψ Ξ} → (j : EVar (Ψ +e)) → (ρ : RExp (Ψ +e))
          → (δ : Subst (Ψ +e) (Ξ +e)) → sE δ j ≡ evar (newᵉ {Ξ})
          → (ρ₀ : RExp Ξ) → ρ [ δ ]ʳ ≡ wkᵉ-r ρ₀
          → Σ[ ρ₁ ∈ RExp Ψ ] (strʳ j ρ ≡ just ρ₁)
strʳ-just {Ψ} {Ξ} j ρ δ r ρ₀ e =
  notNothing (strʳ j ρ)
    (λ q → occ-wkʳ ρ₀ (subst (λ x → occᵉ-r (newᵉ {Ξ}) x ≡ true) e
                             (escʳ δ j (newᵉ {Ξ}) r ρ (str-occʳ j ρ q))))

strᵛ-just : ∀ {Ψ Ξ} → (j : EVar (Ψ +e)) → (A : OVType (Ψ +e))
          → (δ : Subst (Ψ +e) (Ξ +e)) → sE δ j ≡ evar (newᵉ {Ξ})
          → (A₀ : OVType Ξ) → A [ δ ]ᵛ ≡ wkᵉ-v A₀
          → Σ[ A₁ ∈ OVType Ψ ] (strᵛ j A ≡ just A₁)
strᵛ-just {Ψ} {Ξ} j A δ r A₀ e =
  notNothing (strᵛ j A)
    (λ q → occ-wkᵛ A₀ (subst (λ x → occᵉ-v (newᵉ {Ξ}) x ≡ true) e
                             (escᵛ δ j (newᵉ {Ξ}) r A (str-occᵛ j A q))))

-- The verdicts, transported through the auxiliaries

strᵛ⁺-just : ∀ {Ψ} → (j : EVar (Ψ +e)) → (A : OVType (Ψ +e)) → {A₁ : OVType Ψ}
           → strᵛ j A ≡ just A₁
           → Σ[ y ∈ Σ[ A₀ ∈ OVType Ψ ] (A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀) ] (strᵛ⁺ j A ≡ just y)
strᵛ⁺-just {Ψ} j A = aux (strᵛ j A) refl
  where
    aux : (x : Maybe (OVType Ψ)) → (eq : strᵛ j A ≡ x) → {A₁ : OVType Ψ} → x ≡ just A₁
        → Σ[ y ∈ Σ[ A₀ ∈ OVType Ψ ] (A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀) ] (strᵛᵃ j A x eq ≡ just y)
    aux (just A₀) eq refl = (A₀ , str-popᵛ j A eq) , refl
    aux nothing   eq ()

strʳ⁺-just : ∀ {Ψ} → (j : EVar (Ψ +e)) → (ρ : RExp (Ψ +e)) → {ρ₁ : RExp Ψ}
           → strʳ j ρ ≡ just ρ₁
           → Σ[ y ∈ Σ[ ρ₀ ∈ RExp Ψ ] (ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀) ] (strʳ⁺ j ρ ≡ just y)
strʳ⁺-just {Ψ} j ρ = aux (strʳ j ρ) refl
  where
    aux : (x : Maybe (RExp Ψ)) → (eq : strʳ j ρ ≡ x) → {ρ₁ : RExp Ψ} → x ≡ just ρ₁
        → Σ[ y ∈ Σ[ ρ₀ ∈ RExp Ψ ] (ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀) ] (strʳᵃ j ρ x eq ≡ just y)
    aux (just ρ₀) eq refl = (ρ₀ , str-popʳ j ρ eq) , refl
    aux nothing   eq ()

strᵉ⁺-just : ∀ {Ψ} → (j : EVar (Ψ +e)) → (ε : EExp (Ψ +e)) → {ε₁ : EExp Ψ}
           → strᵉ j ε ≡ just ε₁
           → Σ[ y ∈ Σ[ ε₀ ∈ EExp Ψ ] (ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀) ] (strᵉ⁺ j ε ≡ just y)
strᵉ⁺-just {Ψ} j ε = aux (strᵉ j ε) refl
  where
    aux : (x : Maybe (EExp Ψ)) → (eq : strᵉ j ε ≡ x) → {ε₁ : EExp Ψ} → x ≡ just ε₁
        → Σ[ y ∈ Σ[ ε₀ ∈ EExp Ψ ] (ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀) ] (strᵉᵃ j ε x eq ≡ just y)
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

strSubᵃ-just : ∀ {Θ Ψ} → (j : EVar (Ψ +e)) → (γ : Subst Θ (Ψ +e))
             → (a : Maybe (Σ[ g ∈ (TyVar Θ → OVType Ψ) ]
                             ((α : TyVar Θ) → sTy γ α [ popˢ j ]ᵛ ≡ wkᵉ-v (g α))))
             → (x : Σ[ g ∈ (TyVar Θ → OVType Ψ) ]
                      ((α : TyVar Θ) → sTy γ α [ popˢ j ]ᵛ ≡ wkᵉ-v (g α))) → a ≡ just x
             → (b : Maybe (Σ[ g ∈ (RVar Θ → RExp Ψ) ]
                             ((i : RVar Θ) → sR γ i [ popˢ j ]ʳ ≡ wkᵉ-r (g i))))
             → (y : Σ[ g ∈ (RVar Θ → RExp Ψ) ]
                      ((i : RVar Θ) → sR γ i [ popˢ j ]ʳ ≡ wkᵉ-r (g i))) → b ≡ just y
             → (c : Maybe (Σ[ g ∈ (EVar Θ → EExp Ψ) ]
                             ((i : EVar Θ) → sE γ i [ popˢ j ]ᵉ ≡ wkᵉ-e (g i))))
             → (z : Σ[ g ∈ (EVar Θ → EExp Ψ) ]
                      ((i : EVar Θ) → sE γ i [ popˢ j ]ᵉ ≡ wkᵉ-e (g i))) → c ≡ just z
             → Σ[ w ∈ Σ[ γ₀ ∈ Subst Θ Ψ ] ((γ ⨟ˢ popˢ j) ≐ˢ (γ₀ ⨟ˢ wkˢᵉ)) ]
                 (strSubᵃ j γ a b c ≡ just w)
strSubᵃ-just j γ .(just (fT , pT)) (fT , pT) refl
                 .(just (fR , pR)) (fR , pR) refl
                 .(just (fE , pE)) (fE , pE) refl = _ , refl

-- The escape check, complete: if the check fails, no instance that
-- keeps the rigid an eigenvariable can free the images of it

strSub-escape : ∀ {Θ Ψ Ξ} → (j : EVar (Ψ +e)) → (γ : Subst Θ (Ψ +e))
              → (δ : Subst (Ψ +e) (Ξ +e)) → sE δ j ≡ evar (newᵉ {Ξ})
              → (γ₀ : Subst Θ Ξ) → (γ ⨟ˢ δ) ≐ˢ (γ₀ ⨟ˢ wkˢᵉ)
              → strSub j γ ≡ nothing → ⊥
strSub-escape {Θ} {Ψ} {Ξ} j γ δ r γ₀ p q = ⊥just (trans (sym q) (proj₂ done))
  where
    hT : (α : TyVar Θ)
       → Σ[ y ∈ Σ[ A₀ ∈ OVType Ψ ] (sTy γ α [ popˢ j ]ᵛ ≡ wkᵉ-v A₀) ]
           (strᵛ⁺ j (sTy γ α) ≡ just y)
    hT α = strᵛ⁺-just j (sTy γ α)
             (proj₂ (strᵛ-just j (sTy γ α) δ r (sTy γ₀ α)
                       (trans (≐ᵗ p α) (wkˢᵉ-v (sTy γ₀ α)))))

    hR : (i : RVar Θ)
       → Σ[ y ∈ Σ[ ρ₀ ∈ RExp Ψ ] (sR γ i [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀) ]
           (strʳ⁺ j (sR γ i) ≡ just y)
    hR i = strʳ⁺-just j (sR γ i)
             (proj₂ (strʳ-just j (sR γ i) δ r (sR γ₀ i)
                       (trans (≐ʳ p i) (wkˢᵉ-r (sR γ₀ i)))))

    hE : (i : EVar Θ)
       → Σ[ y ∈ Σ[ ε₀ ∈ EExp Ψ ] (sE γ i [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀) ]
           (strᵉ⁺ j (sE γ i) ≡ just y)
    hE i = strᵉ⁺-just j (sE γ i)
             (proj₂ (strᵉ-just j (sE γ i) δ r (sE γ₀ i)
                       (trans (≐ᵉ p i) (wkˢᵉ-e (sE γ₀ i)))))

    tT = seqFin-total (λ α → strᵛ⁺ j (sTy γ α)) hT
    tR = seqFin-total (λ i → strʳ⁺ j (sR  γ i)) hR
    tE = seqFin-total (λ i → strᵉ⁺ j (sE  γ i)) hE

    done : Σ[ x ∈ Σ[ γ₁ ∈ Subst Θ Ψ ] ((γ ⨟ˢ popˢ j) ≐ˢ (γ₁ ⨟ˢ wkˢᵉ)) ]
             (strSub j γ ≡ just x)
    done = strSubᵃ-just j γ _ (proj₁ tT) (proj₂ tT)
                            _ (proj₁ tR) (proj₂ tR)
                            _ (proj₁ tE) (proj₂ tE)

-- With the rigid sent to a constant, an expression strengthens away
-- from it

strᵉ-upd : ∀ {Ψ} → (j : EVar (Ψ +e)) → (c : E) → (ε : EExp (Ψ +e))
         → Σ[ ε₀ ∈ EExp Ψ ] (strᵉ j (ε [ updᵉ j (econst c) ]ᵉ) ≡ just ε₀)
strᵉ-upd {Ψ} j c (evar k) with k ≟ᶠ j
... | yes refl = econst c , refl
... | no ne with thickᵉ {Ψ} j k in r
...   | just k₀ = evar k₀ , refl
...   | nothing = ⊥-elim (ne (thick-nothing j k r))
strᵉ-upd j c (econst c')  = econst c' , refl
strᵉ-upd j c (ε ·̂ₑ ε') with strᵉ-upd j c ε | strᵉ-upd j c ε'
... | a , qa | b , qb = a ·̂ₑ b , cong₂ (zip₂ _·̂ₑ_) qa qb
strᵉ-upd j c (ε ⊔̂ₑ ε') with strᵉ-upd j c ε | strᵉ-upd j c ε'
... | a , qa | b , qb = a ⊔̂ₑ b , cong₂ (zip₂ _⊔̂ₑ_) qa qb

strʳ-upd : ∀ {Ψ} → (j : EVar (Ψ +e)) → (c : E) → (ρ : RExp (Ψ +e))
         → Σ[ ρ₀ ∈ RExp Ψ ] (strʳ j (ρ [ updᵉ j (econst c) ]ʳ) ≡ just ρ₀)
strʳ-upd j c (rvar i)   = rvar i , refl
strʳ-upd j c (rconst c') = rconst c' , refl
strʳ-upd j c (ρ ·̂ᵣ ρ') with strʳ-upd j c ρ | strʳ-upd j c ρ'
... | a , qa | b , qb = a ·̂ᵣ b , cong₂ (zip₂ _·̂ᵣ_) qa qb
strʳ-upd j c (ρ ⊔̂ᵣ ρ') with strʳ-upd j c ρ | strʳ-upd j c ρ'
... | a , qa | b , qb = a ⊔̂ᵣ b , cong₂ (zip₂ _⊔̂ᵣ_) qa qb
strʳ-upd j c ∣ ε ∣̂ᵉ with strᵉ-upd j c ε
... | a , qa = ∣ a ∣̂ᵉ , cong (mmap ∣_∣̂ᵉ) qa
