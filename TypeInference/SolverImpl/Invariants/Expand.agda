------------------------------------------------------------------
-- An expansion is a good substitution                            --
--                                                                --
-- `expandSub` sends a type variable to a decoration, whose every --
-- grade is a fresh unknown, or to a type variable, and a grade   --
-- unknown to an unknown. So each of its images is good against   --
-- any substitution.                                              --
------------------------------------------------------------------

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; tabulate)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Invariants.Expand (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S

open import TypeInference.SolverImpl.Core.Skel      S using (Skel; svar?)
open import TypeInference.SolverImpl.Core.SkelUnify S using (unifyᵏ; ⟦_⟧ᴷ)
open import TypeInference.SolverImpl.Core.Decorate  S
open import TypeInference.SolverImpl.Invariants.Outer S

-- A substitution sending variables to variables

record Ren {Ψ Ψ'} (σ : Subst Ψ Ψ') : Set where
  constructor mkRen
  field
    renᵗ : ∀ α → Σ[ β ∈ TyVar Ψ' ] (sTy σ α ≡ tvar β)
    renʳ : ∀ i → Σ[ j ∈ RVar Ψ' ] (sR σ i ≡ rvar j)
    renᵉ : ∀ i → Σ[ j ∈ EVar Ψ' ] (sE σ i ≡ evar j)

open Ren public

ren-id : ∀ {Ψ} → Ren (idˢ {Ψ})
ren-id = mkRen (λ α → α , refl) (λ i → i , refl) (λ i → i , refl)

ren-wkᵗ : ∀ {Ψ} → Ren (wkˢᵗ {Ψ})
ren-wkᵗ {Ψ} = mkRen (λ α → wkᵗ-tv Ψ α , refl) (λ i → i , refl) (λ i → i , refl)

ren-wkʳ : ∀ {Ψ} → Ren (wkˢʳ {Ψ})
ren-wkʳ {Ψ} = mkRen (λ α → α , refl) (λ i → wkʳ-rv Ψ i , refl) (λ i → i , refl)

ren-wkᵉ : ∀ {Ψ} → Ren (wkˢᵉ {Ψ})
ren-wkᵉ {Ψ} = mkRen (λ α → α , refl) (λ i → i , refl) (λ i → wkᵉ-ev Ψ i , refl)

ren-⨟ : ∀ {Ψ Ψ' Ψ''} {σ : Subst Ψ Ψ'} {τ : Subst Ψ' Ψ''} → Ren σ → Ren τ → Ren (σ ⨟ˢ τ)
ren-⨟ {Ψ'' = Ψ''} {σ = σ} {τ} r q = mkRen t rr e
  where
    t : ∀ α → Σ[ β ∈ TyVar Ψ'' ] (sTy σ α [ τ ]ᵛ ≡ tvar β)
    t α with sTy σ α | renᵗ r α
    ... | .(tvar β) | β , refl = renᵗ q β

    rr : ∀ i → Σ[ j ∈ RVar Ψ'' ] (sR σ i [ τ ]ʳ ≡ rvar j)
    rr i with sR σ i | renʳ r i
    ... | .(rvar j) | j , refl = renʳ q j

    e : ∀ i → Σ[ j ∈ EVar Ψ'' ] (sE σ i [ τ ]ᵉ ≡ evar j)
    e i with sE σ i | renᵉ r i
    ... | .(evar j) | j , refl = renᵉ q j

-- A type every grade of which is an unknown

mutual

  Wholeᵛ : ∀ {Ψ} → OVType Ψ → Set
  Wholeᵛ (tvar α)  = ⊤
  Wholeᵛ (Base b)  = ⊤
  Wholeᵛ Unit      = ⊤
  Wholeᵛ Bool      = ⊤
  Wholeᵛ Empty     = ⊤
  Wholeᵛ (A |×| B) = Wholeᵛ A × Wholeᵛ B
  Wholeᵛ (A ⇒ C)   = Wholeᵛ A × Wholeᶜ C
  Wholeᵛ {Ψ} ([ ρ ] A) = (Σ[ k ∈ RVar Ψ ] (ρ ≡ rvar k)) × Wholeᵛ A

  Wholeᶜ : ∀ {Ψ} → OCType Ψ → Set
  Wholeᶜ {Ψ} (A ‼ ε) = Wholeᵛ A × (Σ[ k ∈ EVar Ψ ] (ε ≡ evar k))

module _ {Θ Ψ} {P : Subst Θ Ψ} where

  mutual

    whole-goodᵛ : ∀ A → Wholeᵛ A → TyGoodᵛ P A
    whole-goodᵛ (tvar α)  w       = tt
    whole-goodᵛ (Base b)  w       = tt
    whole-goodᵛ Unit      w       = tt
    whole-goodᵛ Bool      w       = tt
    whole-goodᵛ Empty     w       = tt
    whole-goodᵛ (A |×| B) (u , v) = whole-goodᵛ A u , whole-goodᵛ B v
    whole-goodᵛ (A ⇒ C)   (u , v) = whole-goodᵛ A u , whole-goodᶜ C v
    whole-goodᵛ ([ .(rvar k) ] A) ((k , refl) , v) = whole k , whole-goodᵛ A v

    whole-goodᶜ : ∀ C → Wholeᶜ C → TyGoodᶜ P C
    whole-goodᶜ (A ‼ .(evar k)) (u , (k , refl)) = whole-goodᵛ A u , whole k

module _ {Ψ Ψ'} {σ : Subst Ψ Ψ'} (r : Ren σ) where

  mutual

    whole-renᵛ : ∀ A → Wholeᵛ A → Wholeᵛ (A [ σ ]ᵛ)
    whole-renᵛ (tvar α)  w with sTy σ α | renᵗ r α
    ... | .(tvar β) | β , refl = tt
    whole-renᵛ (Base b)  w       = tt
    whole-renᵛ Unit      w       = tt
    whole-renᵛ Bool      w       = tt
    whole-renᵛ Empty     w       = tt
    whole-renᵛ (A |×| B) (u , v) = whole-renᵛ A u , whole-renᵛ B v
    whole-renᵛ (A ⇒ C)   (u , v) = whole-renᵛ A u , whole-renᶜ C v
    whole-renᵛ ([ .(rvar k) ] A) ((k , refl) , v) = renʳ r k , whole-renᵛ A v

    whole-renᶜ : ∀ C → Wholeᶜ C → Wholeᶜ (C [ σ ]ᶜ)
    whole-renᶜ (A ‼ .(evar k)) (u , (k , refl)) = whole-renᵛ A u , renᵉ r k

-- A decoration: renamed old scope, whole type

decorate-good : ∀ {m} → (Ψ : Scope) → (t : Skel m)
              → Ren (proj₁ (proj₂ (decorate Ψ t))) × Wholeᵛ (proj₂ (proj₂ (decorate Ψ t)))
decorate-good Ψ (Skel.svar γ)  = ren-wkᵗ , tt
decorate-good Ψ (Skel.sBase b) = ren-id , tt
decorate-good Ψ Skel.sUnit     = ren-id , tt
decorate-good Ψ Skel.sBool     = ren-id , tt
decorate-good Ψ Skel.sEmpty    = ren-id , tt
decorate-good Ψ (t Skel.s× u) with decorate Ψ t | decorate-good Ψ t
... | Ψ₁ , w₁ , A | r₁ , h₁ with decorate Ψ₁ u | decorate-good Ψ₁ u
...   | Ψ₂ , w₂ , B | r₂ , h₂ = ren-⨟ r₁ r₂ , whole-renᵛ r₂ A h₁ , h₂
decorate-good Ψ (t Skel.s⇒ u) with decorate Ψ t | decorate-good Ψ t
... | Ψ₁ , w₁ , A | r₁ , h₁ with decorate Ψ₁ u | decorate-good Ψ₁ u
...   | Ψ₂ , w₂ , B | r₂ , h₂ =
        ren-⨟ (ren-⨟ r₁ r₂) ren-wkᵉ ,
        subst Wholeᵛ (wkˢᵉ-v (A [ w₂ ]ᵛ)) (whole-renᵛ ren-wkᵉ (A [ w₂ ]ᵛ) (whole-renᵛ r₂ A h₁)) ,
        subst Wholeᵛ (wkˢᵉ-v B) (whole-renᵛ ren-wkᵉ B h₂) , (_ , refl)
decorate-good Ψ (Skel.sBox t) with decorate Ψ t | decorate-good Ψ t
... | Ψ₁ , w₁ , A | r₁ , h₁ =
      ren-⨟ r₁ ren-wkʳ , (_ , refl) , subst Wholeᵛ (wkˢʳ-v A) (whole-renᵛ ren-wkʳ A h₁)

-- A vector of them

JustWhole : ∀ {Ψ} → Maybe (OVType Ψ) → Set
JustWhole (just A) = Wholeᵛ A
JustWhole nothing  = ⊤

decorate*-good : ∀ {m k} → (Ψ : Scope) → (ts : Vec (Skel m) k)
               → Ren (proj₁ (proj₂ (decorate* Ψ ts)))
               × (∀ i → JustWhole (lookup (proj₂ (proj₂ (decorate* Ψ ts))) i))
decorate*-good Ψ []       = ren-id , λ ()
decorate*-good Ψ (t ∷ ts) with svar? t
... | just γ with decorate* Ψ ts | decorate*-good Ψ ts
...   | Ψ' , w , As | r , h = r , λ { zero → tt ; (suc i) → h i }
decorate*-good Ψ (t ∷ ts) | nothing with decorate Ψ t | decorate-good Ψ t
... | Ψ₁ , w₁ , A | r₁ , h₁ with decorate* Ψ₁ ts | decorate*-good Ψ₁ ts
...   | Ψ₂ , w₂ , As | r₂ , h₂ =
        ren-⨟ r₁ r₂ , λ { zero → whole-renᵛ r₂ A h₁ ; (suc i) → h₂ i }

-- The expansion

expandᵏ-good : ∀ {m Θ} → (Ψ : Scope) → (σ : Fin (nTy Ψ) → Skel m)
             → {P : Subst Θ (proj₁ (expandᵏ Ψ σ))} → GV P (proj₂ (expandᵏ Ψ σ))
expandᵏ-good Ψ σ {P} with decorate* Ψ (tabulate σ) | decorate*-good Ψ (tabulate σ)
... | Ψ' , w , As | r , h = mkGV t rr e
  where
    t : ∀ α → TyGoodᵛ P (maybe′ (λ A → A) (sTy w α) (lookup As α))
    t α with lookup As α | h α
    ... | just A  | hA = whole-goodᵛ A hA
    ... | nothing | _  with sTy w α | renᵗ r α
    ...   | .(tvar β) | β , refl = tt

    rr : ∀ i → Goodᵣ P (sR w i)
    rr i with sR w i | renʳ r i
    ... | .(rvar j) | j , refl = whole j

    e : ∀ i → Goodₑ P (sE w i)
    e i with sE w i | renᵉ r i
    ... | .(evar j) | j , refl = whole j

⊥just : ∀ {X Y : Set} {x : X} → nothing ≡ just x → Y
⊥just ()

expandSub-good : ∀ {Θ Ψ} → (l : List (OVType Ψ × OVType Ψ)) → ∀ {Ψ'} {δ : Subst Ψ Ψ'}
               → expandSub l ≡ just (Ψ' , δ) → {P : Subst Θ Ψ'} → GV P δ
expandSub-good {Ψ = Ψ} l eq with unifyᵏ (skelEqns l)
... | nothing = ⊥just eq
... | just (m , τ) with eq
...   | refl = expandᵏ-good Ψ ⟦ τ ⟧ᴷ
