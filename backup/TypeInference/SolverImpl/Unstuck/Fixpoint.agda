------------------------------------------------------------------
-- `localise` ends with no local unknown, for a predicate every   --
-- stage keeps that leaves none at a fixed point                  --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _+_; _≤_; _<_; z≤n; s≤s) renaming (zero to nzero; suc to nsuc)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; n≤0⇒n≡0)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Unstuck.Fixpoint (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Subst  S

open import TypeInference.SolverImpl.Core.Rigid  S using (∨-true; ∨-left; dec-true)
open import TypeInference.SolverImpl.Resid    S
open import TypeInference.SolverImpl.Localise S
open import TypeInference.SolverImpl.Unstuck.Rounds S

private
  ≟-self : ∀ {n} (k : Fin n) → ⌊ k ≟ᶠ k ⌋ ≡ true
  ≟-self k = dec-true (k ≟ᶠ k) refl

  nj : ∀ {A : Set} {a : A} → nothing ≡ just a → ⊥
  nj ()

  ≤-<-trans : ∀ {a b c} → a ≤ b → b < c → a < c
  ≤-<-trans p (s≤s q) = s≤s (≤-trans p q)

  <-≤-trans : ∀ {a b c} → a < b → b ≤ c → a < c
  <-≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

  pred-≤ : ∀ {a n} → a < nsuc n → a ≤ n
  pred-≤ (s≤s p) = p

module _ {Θ Φ} (O : Subst (Θ +e) Φ) (R : Resid Φ) (Pu : Resid Φ → Set) (K : Keeps? O R Pu) where

  open Keeps? K
  open Run O R Pu K
  open Left

  -- a raised set

  raiseL-left : ∀ (L : Localised O R) (P : Subst Φ Φ) → AllIn P (lR L) → Pu (lR L) → ∀ {L'} → raiseL O R L ≡ just L'
              → Σ[ P₁ ∈ Subst Φ Φ ] (AllIn P₁ (lR L') × Pu (lR L') × (cnt O P₁ < cnt O P))
  raiseL-left L P ai pu e with evar? (sE O (newᵉ {Θ}))
  ... | nothing = ⊥-elim (nj e)
  ... | just (j , eqj) with Find.raise? O (lR L) j in er
  ...   | nothing = ⊥-elim (nj e)
  ...   | just (raised l rc ue ur cl sd fx (m , l' , refl)) with e
  ...     | refl = P ⨟ˢ tops l , allIn-⨟ P _ ai , pu-raise (lR L) j er pu , dropped (m , l' , refl) rc
    where
      dropped : Σ[ m' ∈ Mem Φ ] Σ[ l'' ∈ List (Mem Φ) ] (l ≡ m' ∷ l'') → Reach (lR L) j l
         → cnt O (P ⨟ˢ tops l) < cnt O P
      dropped (eᵐ k , l'' , refl) (reachᵉ mx _ _) =
        drops-<ᵉ (drops-tops {P = P} l) O k (memLocalᵉ l O fx hk) (proj₂ (ai-es ai mx) (≟-self k)) hk
        where hk = ∨-left ⌊ k ≟ᶠ k ⌋ (inᴱ k l'') (≟-self k)
      dropped (rᵐ k , l'' , refl) (reachʳ mx _ _) =
        drops-<ʳ (drops-tops {P = P} l) O k (memLocalʳ l O fx hk) (proj₂ (proj₂ (ai-rs ai mx)) (≟-self k)) hk
        where hk = ∨-left ⌊ k ≟ᶠ k ⌋ (inᴿ k l'') (≟-self k)

  -- the start of a round: normal forms, settled where a join was split

  pre : ∀ b (L : Localised O R) (P : Subst Φ Φ) → AllIn P (lR L) → Pu (lR L)
      → AllIn P (lR (resettle O R b (loc-normal L))) × Pu (lR (resettle O R b (loc-normal L)))
  pre true  L P ai pu =
    allIn-settle (loc-normal L) (allIn-normal L ai) , pu-settle (loc-normal L) (pu-normal L pu)
  pre false L P ai pu = allIn-normal L ai , pu-normal L pu

  -- The rounds, with at most `n` local unknowns free in `P`

  rounds-ok : ∀ n (L : Localised O R) (P : Subst Φ Φ) → AllIn P (lR L) → Pu (lR L) → cnt O P ≤ n
            → AllIn O (lR (rounds O R n L))
  rounds-ok nzero L P ai pu le = allIn-⊆ (cnt-0 O P (n≤0⇒n≡0 le)) ai
  rounds-ok (nsuc n) L P ai pu le
    with pre (joined (lR L)) L P ai pu
  ... | ai₀ , pu₀
    with collapseᵉL O R (nE Φ) (resettle O R (joined (lR L)) (loc-normal L))
       | collapseᵉL-left (nE Φ) (resettle O R (joined (lR L)) (loc-normal L)) P ai₀ pu₀
  ... | L₁ , c₁ | left P₁ ai₁ pu₁ le₁ lt₁ , _
    with collapseʳL O R (nR Φ) L₁ | collapseʳL-left (nR Φ) L₁ P₁ ai₁ pu₁
  ... | L₂ , c₂ | left P₂ ai₂ pu₂ le₂ lt₂ , _
    with passᵉ O R (misses (λ k → freeᵉ k O)) L₂ | passᵉ-left (misses (λ k → freeᵉ k O)) L₂ P₂ ai₂ pu₂
  ... | L₃ , c₃ | left P₃ ai₃ pu₃ le₃ lt₃ , fx₃
    with passʳ O R (misses (λ k → freeʳ k O)) L₃ | passʳ-left (misses (λ k → freeʳ k O)) L₃ P₃ ai₃ pu₃
  ... | L₄ , c₄ | left P₄ ai₄ pu₄ le₄ lt₄ , fx₄
    with ((c₁ ∨ c₂) ∨ c₃) ∨ c₄ in eb
  ... | true = rounds-ok n (loc-settle L₄) P₄ (allIn-settle L₄ ai₄) (pu-settle L₄ pu₄) (pred-≤ (<-≤-trans dec le))
    where
      dec : cnt O P₄ < cnt O P
      dec with ∨-true ((c₁ ∨ c₂) ∨ c₃) c₄ eb
      ... | inj₂ t = <-≤-trans (lt₄ t) (≤-trans le₃ (≤-trans le₂ le₁))
      ... | inj₁ t with ∨-true (c₁ ∨ c₂) c₃ t
      ...   | inj₂ t' = ≤-<-trans le₄ (<-≤-trans (lt₃ t') (≤-trans le₂ le₁))
      ...   | inj₁ t' with ∨-true c₁ c₂ t'
      ...     | inj₂ t'' = ≤-<-trans le₄ (≤-<-trans le₃ (<-≤-trans (lt₂ t'') le₁))
      ...     | inj₁ t'' = ≤-<-trans le₄ (≤-<-trans le₃ (≤-<-trans le₂ (lt₁ t'')))
  ... | false with raiseL O R L₄ in er
  ...   | just L'' with raiseL-left L₄ P₄ ai₄ pu₄ er
  ...     | P₅ , ai₅ , pu₅ , lt₅ =
            rounds-ok n (loc-settle L'') P₅ (allIn-settle L'' ai₅) (pu-settle L'' pu₅)
                      (pred-≤ (<-≤-trans lt₅ (≤-trans le₄ (≤-trans le₃ (≤-trans le₂ (≤-trans le₁ le))))))
  rounds-ok (nsuc n) L P ai pu le | ai₀ , pu₀ | L₁ , c₁ | _ | L₂ , c₂ | _
    | L₃ , c₃ | left P₃ ai₃ pu₃ le₃ lt₃ , fx₃ | L₄ , c₄ | left P₄ ai₄ pu₄ le₄ lt₄ , fx₄ | false | nothing
    with ∨-false ((c₁ ∨ c₂) ∨ c₃) c₄ eb
  ... | f₁₂₃ , f₄ with ∨-false (c₁ ∨ c₂) c₃ f₁₂₃
  ...   | _ , f₃ with fx₃ f₃ | fx₄ f₄
  ...     | refl , st₃ | refl , st₄ =
            pu-fixed (lR L₄) pu₄
              (λ k q → st₃ (proj₂ (misses-∈ (λ k' → freeᵉ k' O) q)))
              (λ k q → st₄ (proj₂ (misses-∈ (λ k' → freeʳ k' O) q)))

  -- The whole of `localise`

  localise-allIn : Pu R → AllIn O (lR (localise O R))
  localise-allIn pu =
    allIn-settle (rounds O R (nE Φ + nR Φ) L₀)
      (rounds-ok (nE Φ + nR Φ) L₀ idˢ (allIn-settle (loc-id {O = O} {R = R}) (allIn-id R)) (pu-settle loc-id pu) (cnt-max O idˢ))
    where L₀ = loc-settle (loc-id {O = O} {R = R})
