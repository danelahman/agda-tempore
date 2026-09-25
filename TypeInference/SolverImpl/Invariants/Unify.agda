------------------------------------------------------------------
-- A most general unifier of good types is a good substitution   --
--                                                                --
-- The unifier binds a variable to a subterm of the equations, the --
-- store's earlier bindings applied: a type whose grades are good, --
-- or a good grade. Each binding is then good against the images  --
-- the bindings before it leave, and so is their composite.       --
------------------------------------------------------------------

open import Data.Bool.Base using (if_then_else_; _∨_; true; false) renaming (Bool to 𝔹)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′; _>>=_; _<∣>_)
  renaming (map to mmap)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Invariants.Unify (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (_≡ᵇ?_)

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S

open import TypeInference.SolverImpl.Core.Thick
open import TypeInference.SolverImpl.Core.For    S
open import TypeInference.SolverImpl.Core.AList  S
open import TypeInference.SolverImpl.Core.Eqn    S
open import TypeInference.SolverImpl.Core.Occurs S
open import TypeInference.SolverImpl.Core.Size   S
open import TypeInference.SolverImpl.Core.Unify  S
open import TypeInference.SolverImpl.Core.Rigid  S using (∨-left; ∨-right; true-dec)
open import TypeInference.SolverImpl.Localise    S using (Outerₑ; Outerᵣ; freeᵉ; freeʳ)
open import TypeInference.SolverImpl.Invariants.Outer S

------------------------------------------------------------------------
-- A good store: each binding good against the images before it

GoodAL : ∀ {Θ₀ Θ Θ'} → Subst Θ₀ Θ → AList Θ Θ' → Set
GoodAL P anil         = ⊤
GoodAL P (X /ᵗ α ∷ τ) = TyGoodᵛ (P ⨟ˢ (X forᵗ α)) X × GoodAL (P ⨟ˢ (X forᵗ α)) τ
GoodAL P (X /ʳ i ∷ τ) = Goodᵣ (P ⨟ˢ (X forʳ i)) X × GoodAL (P ⨟ˢ (X forʳ i)) τ
GoodAL P (X /ᵉ i ∷ τ) = Goodₑ (P ⨟ˢ (X forᵉ i)) X × GoodAL (P ⨟ˢ (X forᵉ i)) τ

GoodRes : ∀ {Θ₀ Θ} → Subst Θ₀ Θ → Maybe (Sol Θ) → Set
GoodRes {Θ = Θ} P m = ∀ {Θ''} {ρ'' : AList Θ Θ''} → m ≡ just (Θ'' , ρ'') → GoodAL P ρ''

-- A single binding

GV-forᵗ : ∀ {Θ₀ Θ} {Q : Subst Θ₀ Θ} {X : OVType Θ} {α : TyVar (Θ +ty)}
        → TyGoodᵛ Q X → GV Q (X forᵗ α)
GV-forᵗ {Θ = Θ} {Q} {X} {α} g = mkGV t (λ i → whole i) (λ i → whole i)
  where
    t : ∀ β → TyGoodᵛ Q (sTy (X forᵗ α) β)
    t β with thickᵗ {Θ} α β
    ... | just _  = tt
    ... | nothing = g

GV-forʳ : ∀ {Θ₀ Θ} {Q : Subst Θ₀ Θ} {X : RExp Θ} {i : RVar (Θ +r)}
        → Goodᵣ Q X → GV Q (X forʳ i)
GV-forʳ {Θ = Θ} {Q} {X} {i} g = mkGV (λ α → tt) r (λ j → whole j)
  where
    r : ∀ j → Goodᵣ Q (sR (X forʳ i) j)
    r j with thickʳ {Θ} i j
    ... | just k  = whole k
    ... | nothing = g

GV-forᵉ : ∀ {Θ₀ Θ} {Q : Subst Θ₀ Θ} {X : EExp Θ} {i : EVar (Θ +e)}
        → Goodₑ Q X → GV Q (X forᵉ i)
GV-forᵉ {Θ = Θ} {Q} {X} {i} g = mkGV (λ α → tt) (λ j → whole j) e
  where
    e : ∀ j → Goodₑ Q (sE (X forᵉ i) j)
    e j with thickᵉ {Θ} i j
    ... | just k  = whole k
    ... | nothing = g

GoodAL→GV : ∀ {Θ₀ Θ Θ'} → (P : Subst Θ₀ Θ) → (ρ : AList Θ Θ') → GoodAL P ρ
          → GV (P ⨟ˢ ⟦ ρ ⟧ᴬ) ⟦ ρ ⟧ᴬ
GoodAL→GV P anil         g        = GV-id
GoodAL→GV P (X /ᵗ α ∷ τ) (gX , gτ) =
  GV-⊆ (≐→⊆ᶠ (⨟-assoc P (X forᵗ α) ⟦ τ ⟧ᴬ))
       (GV-⨟ {P = P ⨟ˢ (X forᵗ α)} (GV-forᵗ {X = X} {α = α} gX) (GoodAL→GV (P ⨟ˢ (X forᵗ α)) τ gτ))
GoodAL→GV P (X /ʳ i ∷ τ) (gX , gτ) =
  GV-⊆ (≐→⊆ᶠ (⨟-assoc P (X forʳ i) ⟦ τ ⟧ᴬ))
       (GV-⨟ {P = P ⨟ˢ (X forʳ i)} (GV-forʳ {X = X} {i = i} gX) (GoodAL→GV (P ⨟ˢ (X forʳ i)) τ gτ))
GoodAL→GV P (X /ᵉ i ∷ τ) (gX , gτ) =
  GV-⊆ (≐→⊆ᶠ (⨟-assoc P (X forᵉ i) ⟦ τ ⟧ᴬ))
       (GV-⨟ {P = P ⨟ˢ (X forᵉ i)} (GV-forᵉ {X = X} {i = i} gX) (GoodAL→GV (P ⨟ˢ (X forᵉ i)) τ gτ))

-- Binding a variable to a subterm with it removed: the removal sends it
-- to a closed term, which leaves no more free unknowns than the binding

module _ {Θ₀ Θ} (P : Subst Θ₀ (Θ +ty)) (α : TyVar (Θ +ty)) (X : OVType Θ) where

  forᵗ-⊆ : (P ⨟ˢ (Unit forᵗ α)) ⊆ᶠ (P ⨟ˢ (X forᵗ α))
  forᵗ-⊆ = mk⊆ᶠ e r
    where
      tyᵉ : ∀ {k} β → occᵉ-v k (sTy (Unit forᵗ α) β) ≡ true → ∀ {Y : Set} → Y
      tyᵉ β q with thickᵗ {Θ} α β
      tyᵉ β () | just _
      tyᵉ β () | nothing

      tyʳ : ∀ {k} β → occʳ-v k (sTy (Unit forᵗ α) β) ≡ true → ∀ {Y : Set} → Y
      tyʳ β q with thickᵗ {Θ} α β
      tyʳ β () | just _
      tyʳ β () | nothing

      e : ∀ {k} → freeᵉ k (P ⨟ˢ (Unit forᵗ α)) ≡ true → freeᵉ k (P ⨟ˢ (X forᵗ α)) ≡ true
      e q with freeᵉ-⨟⁻ P (Unit forᵗ α) q
      ... | inj₁ (β , s) = tyᵉ β s
      ... | inj₂ (inj₁ (i , p , ()))
      ... | inj₂ (inj₂ (i , p , s)) = freeᵉ-⨟ P (X forᵗ α) p s

      r : ∀ {k} → freeʳ k (P ⨟ˢ (Unit forᵗ α)) ≡ true → freeʳ k (P ⨟ˢ (X forᵗ α)) ≡ true
      r q with freeʳ-⨟⁻ P (Unit forᵗ α) q
      ... | inj₁ (β , s) = tyʳ β s
      ... | inj₂ (i , p , s) = freeʳ-⨟ P (X forᵗ α) p s

module _ {Θ₀ Θ} (P : Subst Θ₀ (Θ +r)) (i : RVar (Θ +r)) (X : RExp Θ) where

  forʳ-⊆ : (P ⨟ˢ (ûᵣ forʳ i)) ⊆ᶠ (P ⨟ˢ (X forʳ i))
  forʳ-⊆ = mk⊆ᶠ e r
    where
      e : ∀ {k} → freeᵉ k (P ⨟ˢ (ûᵣ forʳ i)) ≡ true → freeᵉ k (P ⨟ˢ (X forʳ i)) ≡ true
      e q with freeᵉ-⨟⁻ P (ûᵣ forʳ i) q
      ... | inj₁ (β , ())
      ... | inj₂ (inj₂ (j , p , s)) = freeᵉ-⨟ P (X forʳ i) p s
      ... | inj₂ (inj₁ (j , p , s)) with thickʳ {Θ} i j
      e q | inj₂ (inj₁ (j , p , ())) | just _
      e q | inj₂ (inj₁ (j , p , ())) | nothing

      r : ∀ {k} → freeʳ k (P ⨟ˢ (ûᵣ forʳ i)) ≡ true → freeʳ k (P ⨟ˢ (X forʳ i)) ≡ true
      r q with freeʳ-⨟⁻ P (ûᵣ forʳ i) q
      ... | inj₁ (β , ())
      ... | inj₂ (j , p , s) = freeʳ-⨟ P (X forʳ i) p (same j s)
        where
          same : ∀ {k} j → occʳ-r k (sR (ûᵣ forʳ i) j) ≡ true → occʳ-r k (sR (X forʳ i) j) ≡ true
          same j s with thickʳ {Θ} i j
          same j s  | just _  = s
          same j () | nothing

module _ {Θ₀ Θ} (P : Subst Θ₀ (Θ +e)) (i : EVar (Θ +e)) (X : EExp Θ) where

  forᵉ-⊆ : (P ⨟ˢ (ûₑ forᵉ i)) ⊆ᶠ (P ⨟ˢ (X forᵉ i))
  forᵉ-⊆ = mk⊆ᶠ e r
    where
      e : ∀ {k} → freeᵉ k (P ⨟ˢ (ûₑ forᵉ i)) ≡ true → freeᵉ k (P ⨟ˢ (X forᵉ i)) ≡ true
      e q with freeᵉ-⨟⁻ P (ûₑ forᵉ i) q
      ... | inj₁ (β , ())
      ... | inj₂ (inj₁ (j , p , ()))
      ... | inj₂ (inj₂ (j , p , s)) = freeᵉ-⨟ P (X forᵉ i) p (same j s)
        where
          same : ∀ {k} j → occᵉ-e k (sE (ûₑ forᵉ i) j) ≡ true → occᵉ-e k (sE (X forᵉ i) j) ≡ true
          same j s with thickᵉ {Θ} i j
          same j s  | just _  = s
          same j () | nothing

      r : ∀ {k} → freeʳ k (P ⨟ˢ (ûₑ forᵉ i)) ≡ true → freeʳ k (P ⨟ˢ (X forᵉ i)) ≡ true
      r q with freeʳ-⨟⁻ P (ûₑ forᵉ i) q
      ... | inj₁ (β , ())
      ... | inj₂ (j , p , s) = freeʳ-⨟ P (X forᵉ i) p s

------------------------------------------------------------------------
-- The unifier's steps

module _ {Θ₀ Θ} (P : Subst Θ₀ Θ) where

  keep-good : GoodRes P (just (Θ , anil))
  keep-good refl = tt

  const-good : ∀ {X : Set} → (d : Dec X) → GoodRes P (if ⌊ d ⌋ then just (Θ , anil) else nothing)
  const-good (yes _) refl = tt
  const-good (no _)  ()

  seq-good : (m : Maybe (Sol Θ)) → (f : Sol Θ → Maybe (Sol Θ)) → GoodRes P m
           → (∀ {Θ₁} → (st₁ : AList Θ Θ₁) → GoodAL P st₁ → GoodRes P (f (Θ₁ , st₁)))
           → GoodRes P (m >>= f)
  seq-good (just (Θ₁ , st₁)) f g h eq = h st₁ (g refl) eq
  seq-good nothing           f g h ()

  alt-good : (m m' : Maybe (Sol Θ)) → GoodRes P m → GoodRes P m' → GoodRes P (m <∣> m')
  alt-good (just _) m' g h eq = g eq
  alt-good nothing  m' g h eq = h eq

descᵗ-good : ∀ {Θ₀ Θ} {P : Subst Θ₀ (Θ +ty)} (X : OVType Θ) (α : TyVar (Θ +ty))
           → TyGoodᵛ (P ⨟ˢ (X forᵗ α)) X → {m : Maybe (Sol Θ)}
           → GoodRes (P ⨟ˢ (X forᵗ α)) m → GoodRes P (mmap (consᵗ X α) m)
descᵗ-good X α g {just (Θ'' , ρ'')} h refl = g , h refl
descᵗ-good X α g {nothing}          h ()

descʳ-good : ∀ {Θ₀ Θ} {P : Subst Θ₀ (Θ +r)} (X : RExp Θ) (i : RVar (Θ +r))
           → Goodᵣ (P ⨟ˢ (X forʳ i)) X → {m : Maybe (Sol Θ)}
           → GoodRes (P ⨟ˢ (X forʳ i)) m → GoodRes P (mmap (consʳ X i) m)
descʳ-good X i g {just (Θ'' , ρ'')} h refl = g , h refl
descʳ-good X i g {nothing}          h ()

descᵉ-good : ∀ {Θ₀ Θ} {P : Subst Θ₀ (Θ +e)} (X : EExp Θ) (i : EVar (Θ +e))
           → Goodₑ (P ⨟ˢ (X forᵉ i)) X → {m : Maybe (Sol Θ)}
           → GoodRes (P ⨟ˢ (X forᵉ i)) m → GoodRes P (mmap (consᵉ X i) m)
descᵉ-good X i g {just (Θ'' , ρ'')} h refl = g , h refl
descᵉ-good X i g {nothing}          h ()

-- Binding a variable

flexᵗ-good : ∀ {Θ₀ Θ} → (P : Subst Θ₀ Θ) → (α : TyVar Θ) → (A : OVType Θ) → TyGoodᵛ P A
           → GoodRes P (flexᵗ α A)
flexᵗ-good {Θ = scope zero    nr ne} P () A g
flexᵗ-good {Θ = scope (suc nt) nr ne} P α A g with occᵗ-v α A
... | true  = λ ()
... | false = λ { refl →
      tygoodᵛ-⊆ (forᵗ-⊆ P α A') A' (tygoodᵛ-⨟ {P = P} (GV-forᵗ {X = Unit} {α = α} tt) A g) , tt }
  where
    A' = A [ Unit forᵗ α ]ᵛ

flexʳ-good : ∀ {Θ₀ Θ} → (P : Subst Θ₀ Θ) → (i : RVar Θ) → (ρ : RExp Θ) → Goodᵣ P ρ
           → GoodRes P (flexʳ i ρ)
flexʳ-good {Θ = scope nt zero    ne} P () ρ g
flexʳ-good {Θ = scope nt (suc nr) ne} P i ρ g with occʳ-r i ρ
... | true  = λ ()
... | false = λ { refl →
      goodᵣ-⊆ (forʳ-⊆ P i ρ') (goodᵣ-⨟ {P = P} (GV-forʳ {X = ûᵣ} {i = i} (outer ((λ ()) , (λ ())))) g) , tt }
  where
    ρ' = ρ [ ûᵣ forʳ i ]ʳ

flexᵉ-good : ∀ {Θ₀ Θ} → (P : Subst Θ₀ Θ) → (rg : Rig Θ) → (i : EVar Θ) → (ε : EExp Θ) → Goodₑ P ε
           → GoodRes P (flexᵉ rg i ε)
flexᵉ-good {Θ = scope nt nr zero}    P rg () ε g
flexᵉ-good {Θ = scope nt nr (suc ne)} P rg i ε g with i ∈ᶠ rg | occᵉ-e i ε
... | true  | _     = λ ()
... | false | true  = λ ()
... | false | false = λ { refl →
      goodₑ-⊆ (forᵉ-⊆ P i ε') (goodₑ-⨟ {P = P} (GV-forᵉ {X = ûₑ} {i = i} (outer (λ ()))) g) , tt }
  where
    ε' = ε [ ûₑ forᵉ i ]ᵉ

flexFlexᵗ-good : ∀ {Θ₀ Θ} → (P : Subst Θ₀ Θ) → (α β : TyVar Θ) → GoodRes P (flexFlexᵗ α β)
flexFlexᵗ-good P α β with α ≟ᶠ β
... | yes _ = keep-good P
... | no _  = flexᵗ-good P α (tvar β) tt

flexFlexʳ-good : ∀ {Θ₀ Θ} → (P : Subst Θ₀ Θ) → (i j : RVar Θ) → GoodRes P (flexFlexʳ i j)
flexFlexʳ-good P i j with i ≟ᶠ j
... | yes _ = keep-good P
... | no _  = flexʳ-good P i (rvar j) (whole j)

flexFlexᵉ-good : ∀ {Θ₀ Θ} → (P : Subst Θ₀ Θ) → (rg : Rig Θ) → (i j : EVar Θ)
               → GoodRes P (flexFlexᵉ rg i j)
flexFlexᵉ-good P rg i j with i ≟ᶠ j
... | yes _ = keep-good P
... | no _  = alt-good P (flexᵉ rg i (evar j)) (flexᵉ rg j (evar i))
                (flexᵉ-good P rg i (evar j) (whole j)) (flexᵉ-good P rg j (evar i) (whole i))

-- The parts of a good compound grade

module _ {Θ₀ Θ} {P : Subst Θ₀ Θ} where

  good·₁ : ∀ {a b : EExp Θ} → Goodₑ P (a ·̂ₑ b) → Goodₑ P a
  good·₁ {a} (outer o) = outer (λ {k} r → o (∨-left (occᵉ-e k a) _ r))
  good·₂ : ∀ {a b : EExp Θ} → Goodₑ P (a ·̂ₑ b) → Goodₑ P b
  good·₂ {a} (outer o) = outer (λ {k} r → o (∨-right (occᵉ-e k a) _ r))
  good⊔₁ : ∀ {a b : EExp Θ} → Goodₑ P (a ⊔̂ₑ b) → Goodₑ P a
  good⊔₁ {a} (outer o) = outer (λ {k} r → o (∨-left (occᵉ-e k a) _ r))
  good⊔₂ : ∀ {a b : EExp Θ} → Goodₑ P (a ⊔̂ₑ b) → Goodₑ P b
  good⊔₂ {a} (outer o) = outer (λ {k} r → o (∨-right (occᵉ-e k a) _ r))

  goodʳ·₁ : ∀ {a b : RExp Θ} → Goodᵣ P (a ·̂ᵣ b) → Goodᵣ P a
  goodʳ·₁ {a} (outer (oe , or)) = outer ((λ {k} r → oe (∨-left (occᵉ-r k a) _ r)) , (λ {k} r → or (∨-left (occʳ-r k a) _ r)))
  goodʳ·₂ : ∀ {a b : RExp Θ} → Goodᵣ P (a ·̂ᵣ b) → Goodᵣ P b
  goodʳ·₂ {a} (outer (oe , or)) = outer ((λ {k} r → oe (∨-right (occᵉ-r k a) _ r)) , (λ {k} r → or (∨-right (occʳ-r k a) _ r)))
  goodʳ⊔₁ : ∀ {a b : RExp Θ} → Goodᵣ P (a ⊔̂ᵣ b) → Goodᵣ P a
  goodʳ⊔₁ {a} (outer (oe , or)) = outer ((λ {k} r → oe (∨-left (occᵉ-r k a) _ r)) , (λ {k} r → or (∨-left (occʳ-r k a) _ r)))
  goodʳ⊔₂ : ∀ {a b : RExp Θ} → Goodᵣ P (a ⊔̂ᵣ b) → Goodᵣ P b
  goodʳ⊔₂ {a} (outer (oe , or)) = outer ((λ {k} r → oe (∨-right (occᵉ-r k a) _ r)) , (λ {k} r → or (∨-right (occʳ-r k a) _ r)))

  goodʳ∣∣ : ∀ {a : EExp Θ} → Goodᵣ P ∣ a ∣̂ᵉ → Goodₑ P a
  goodʳ∣∣ (outer (oe , or)) = outer oe

------------------------------------------------------------------------
-- The unifier, clause by clause as `UnifyMGU` follows it

mutual

  amguᵛ-good : ∀ {Θ₀ Θ Θ'} → (P : Subst Θ₀ Θ) → (k : ℕ) → (p : Sz Θ ≡ k) → (rg : Rig Θ)
             → (A B : OVType Θ) → (ρ : AList Θ Θ') → TyGoodᵛ P A → TyGoodᵛ P B → GoodAL P ρ
             → GoodRes P (amguᵛ k p rg A B (Θ' , ρ))

  amguᶜ-good : ∀ {Θ₀ Θ Θ'} → (P : Subst Θ₀ Θ) → (k : ℕ) → (p : Sz Θ ≡ k) → (rg : Rig Θ)
             → (C D : OCType Θ) → (ρ : AList Θ Θ') → TyGoodᶜ P C → TyGoodᶜ P D → GoodAL P ρ
             → GoodRes P (amguᶜ k p rg C D (Θ' , ρ))

  amguʳ-good : ∀ {Θ₀ Θ Θ'} → (P : Subst Θ₀ Θ) → (k : ℕ) → (p : Sz Θ ≡ k) → (rg : Rig Θ)
             → (ρ₀ ρ₁ : RExp Θ) → (ρ : AList Θ Θ') → Goodᵣ P ρ₀ → Goodᵣ P ρ₁ → GoodAL P ρ
             → GoodRes P (amguʳ k p rg ρ₀ ρ₁ (Θ' , ρ))

  amguᵉ-good : ∀ {Θ₀ Θ Θ'} → (P : Subst Θ₀ Θ) → (k : ℕ) → (p : Sz Θ ≡ k) → (rg : Rig Θ)
             → (ε ε' : EExp Θ) → (ρ : AList Θ Θ') → Goodₑ P ε → Goodₑ P ε' → GoodAL P ρ
             → GoodRes P (amguᵉ k p rg ε ε' (Θ' , ρ))

  amguᵛ-good P (suc k) p rg A B (X /ᵗ α ∷ τ) gL gR (gX , gτ) =
    descᵗ-good {P = P} X α gX
      (amguᵛ-good (P ⨟ˢ (X forᵗ α)) k (szᵗ τ p) rg (A [ X forᵗ α ]ᵛ) (B [ X forᵗ α ]ᵛ) τ
        (tygoodᵛ-⨟ {P = P} (GV-forᵗ {X = X} {α = α} gX) A gL) (tygoodᵛ-⨟ {P = P} (GV-forᵗ {X = X} {α = α} gX) B gR) gτ)
  amguᵛ-good P (suc k) p rg A B (X /ʳ i ∷ τ) gL gR (gX , gτ) =
    descʳ-good {P = P} X i gX
      (amguᵛ-good (P ⨟ˢ (X forʳ i)) k (szʳ τ p) rg (A [ X forʳ i ]ᵛ) (B [ X forʳ i ]ᵛ) τ
        (tygoodᵛ-⨟ {P = P} (GV-forʳ {X = X} {i = i} gX) A gL) (tygoodᵛ-⨟ {P = P} (GV-forʳ {X = X} {i = i} gX) B gR) gτ)
  amguᵛ-good P (suc k) p rg A B (X /ᵉ i ∷ τ) gL gR (gX , gτ) =
    descᵉ-good {P = P} X i gX
      (amguᵛ-good (P ⨟ˢ (X forᵉ i)) k (szᵉ τ p) (popʳᵍ τ i rg) (A [ X forᵉ i ]ᵛ) (B [ X forᵉ i ]ᵛ) τ
        (tygoodᵛ-⨟ {P = P} (GV-forᵉ {X = X} {i = i} gX) A gL) (tygoodᵛ-⨟ {P = P} (GV-forᵉ {X = X} {i = i} gX) B gR) gτ)
  amguᵛ-good P zero p rg A B (X /ᵗ α ∷ τ) gL gR (gX , gτ) =
    sz0ᵗ τ p
  amguᵛ-good P zero p rg A B (X /ʳ i ∷ τ) gL gR (gX , gτ) =
    sz0ʳ τ p
  amguᵛ-good P zero p rg A B (X /ᵉ i ∷ τ) gL gR (gX , gτ) =
    sz0ᵉ τ p
  amguᵛ-good P (suc k) p rg (tvar α) (tvar β) anil gL gR _ =
    flexFlexᵗ-good P α β
  amguᵛ-good P (suc k) p rg (tvar α) (Base b') anil gL gR _ =
    flexᵗ-good P α (Base b') gR
  amguᵛ-good P (suc k) p rg (tvar α) Unit anil gL gR _ =
    flexᵗ-good P α Unit gR
  amguᵛ-good P (suc k) p rg (tvar α) Bool anil gL gR _ =
    flexᵗ-good P α Bool gR
  amguᵛ-good P (suc k) p rg (tvar α) (B |×| B') anil gL gR _ =
    flexᵗ-good P α (B |×| B') gR
  amguᵛ-good P (suc k) p rg (tvar α) Empty anil gL gR _ =
    flexᵗ-good P α Empty gR
  amguᵛ-good P (suc k) p rg (tvar α) (B ⇒ D) anil gL gR _ =
    flexᵗ-good P α (B ⇒ D) gR
  amguᵛ-good P (suc k) p rg (tvar α) ([ ρ' ] B) anil gL gR _ =
    flexᵗ-good P α ([ ρ' ] B) gR
  amguᵛ-good P (suc k) p rg (Base b) (tvar β) anil gL gR _ =
    flexᵗ-good P β (Base b) gL
  amguᵛ-good P (suc k) p rg Unit (tvar β) anil gL gR _ =
    flexᵗ-good P β Unit gL
  amguᵛ-good P (suc k) p rg Bool (tvar β) anil gL gR _ =
    flexᵗ-good P β Bool gL
  amguᵛ-good P (suc k) p rg (A |×| A') (tvar β) anil gL gR _ =
    flexᵗ-good P β (A |×| A') gL
  amguᵛ-good P (suc k) p rg Empty (tvar β) anil gL gR _ =
    flexᵗ-good P β Empty gL
  amguᵛ-good P (suc k) p rg (A ⇒ C) (tvar β) anil gL gR _ =
    flexᵗ-good P β (A ⇒ C) gL
  amguᵛ-good P (suc k) p rg ([ ρ ] A) (tvar β) anil gL gR _ =
    flexᵗ-good P β ([ ρ ] A) gL
  amguᵛ-good P (suc k) p rg (Base b) (Base b') anil gL gR _ =
    const-good P (b ≡ᵇ? b')
  amguᵛ-good P (suc k) p rg Unit Unit anil gL gR _ =
    keep-good P
  amguᵛ-good P (suc k) p rg Bool Bool anil gL gR _ =
    keep-good P
  amguᵛ-good P (suc k) p rg Empty Empty anil gL gR _ =
    keep-good P
  amguᵛ-good {Θ = Θ} P (suc k) p rg (A |×| A') (B |×| B') anil gL gR _ =
    seq-good P (amguᵛ (suc k) p rg A B (Θ , anil)) (amguᵛ (suc k) p rg A' B')
      (amguᵛ-good P (suc k) p rg A B anil (proj₁ gL) (proj₁ gR) tt)
      (λ st₁ g₁ → amguᵛ-good P (suc k) p rg A' B' st₁ (proj₂ gL) (proj₂ gR) g₁)
  amguᵛ-good {Θ = Θ} P (suc k) p rg (A ⇒ C) (B ⇒ D) anil gL gR _ =
    seq-good P (amguᵛ (suc k) p rg A B (Θ , anil)) (amguᶜ (suc k) p rg C D)
      (amguᵛ-good P (suc k) p rg A B anil (proj₁ gL) (proj₁ gR) tt)
      (λ st₁ g₁ → amguᶜ-good P (suc k) p rg C D st₁ (proj₂ gL) (proj₂ gR) g₁)
  amguᵛ-good {Θ = Θ} P (suc k) p rg ([ ρ ] A) ([ ρ' ] B) anil gL gR _ =
    seq-good P (amguʳ (suc k) p rg ρ ρ' (Θ , anil)) (amguᵛ (suc k) p rg A B)
      (amguʳ-good P (suc k) p rg ρ ρ' anil (proj₁ gL) (proj₁ gR) tt)
      (λ st₁ g₁ → amguᵛ-good P (suc k) p rg A B st₁ (proj₂ gL) (proj₂ gR) g₁)
  amguᵛ-good P zero p rg (tvar α) (tvar β) anil gL gR _ =
    flexFlexᵗ-good P α β
  amguᵛ-good P zero p rg (tvar α) (Base b') anil gL gR _ =
    flexᵗ-good P α (Base b') gR
  amguᵛ-good P zero p rg (tvar α) Unit anil gL gR _ =
    flexᵗ-good P α Unit gR
  amguᵛ-good P zero p rg (tvar α) Bool anil gL gR _ =
    flexᵗ-good P α Bool gR
  amguᵛ-good P zero p rg (tvar α) (B |×| B') anil gL gR _ =
    flexᵗ-good P α (B |×| B') gR
  amguᵛ-good P zero p rg (tvar α) Empty anil gL gR _ =
    flexᵗ-good P α Empty gR
  amguᵛ-good P zero p rg (tvar α) (B ⇒ D) anil gL gR _ =
    flexᵗ-good P α (B ⇒ D) gR
  amguᵛ-good P zero p rg (tvar α) ([ ρ' ] B) anil gL gR _ =
    flexᵗ-good P α ([ ρ' ] B) gR
  amguᵛ-good P zero p rg (Base b) (tvar β) anil gL gR _ =
    flexᵗ-good P β (Base b) gL
  amguᵛ-good P zero p rg Unit (tvar β) anil gL gR _ =
    flexᵗ-good P β Unit gL
  amguᵛ-good P zero p rg Bool (tvar β) anil gL gR _ =
    flexᵗ-good P β Bool gL
  amguᵛ-good P zero p rg (A |×| A') (tvar β) anil gL gR _ =
    flexᵗ-good P β (A |×| A') gL
  amguᵛ-good P zero p rg Empty (tvar β) anil gL gR _ =
    flexᵗ-good P β Empty gL
  amguᵛ-good P zero p rg (A ⇒ C) (tvar β) anil gL gR _ =
    flexᵗ-good P β (A ⇒ C) gL
  amguᵛ-good P zero p rg ([ ρ ] A) (tvar β) anil gL gR _ =
    flexᵗ-good P β ([ ρ ] A) gL
  amguᵛ-good P zero p rg (Base b) (Base b') anil gL gR _ =
    const-good P (b ≡ᵇ? b')
  amguᵛ-good P zero p rg Unit Unit anil gL gR _ =
    keep-good P
  amguᵛ-good P zero p rg Bool Bool anil gL gR _ =
    keep-good P
  amguᵛ-good P zero p rg Empty Empty anil gL gR _ =
    keep-good P
  amguᵛ-good {Θ = Θ} P zero p rg (A |×| A') (B |×| B') anil gL gR _ =
    seq-good P (amguᵛ zero p rg A B (Θ , anil)) (amguᵛ zero p rg A' B')
      (amguᵛ-good P zero p rg A B anil (proj₁ gL) (proj₁ gR) tt)
      (λ st₁ g₁ → amguᵛ-good P zero p rg A' B' st₁ (proj₂ gL) (proj₂ gR) g₁)
  amguᵛ-good {Θ = Θ} P zero p rg (A ⇒ C) (B ⇒ D) anil gL gR _ =
    seq-good P (amguᵛ zero p rg A B (Θ , anil)) (amguᶜ zero p rg C D)
      (amguᵛ-good P zero p rg A B anil (proj₁ gL) (proj₁ gR) tt)
      (λ st₁ g₁ → amguᶜ-good P zero p rg C D st₁ (proj₂ gL) (proj₂ gR) g₁)
  amguᵛ-good {Θ = Θ} P zero p rg ([ ρ ] A) ([ ρ' ] B) anil gL gR _ =
    seq-good P (amguʳ zero p rg ρ ρ' (Θ , anil)) (amguᵛ zero p rg A B)
      (amguʳ-good P zero p rg ρ ρ' anil (proj₁ gL) (proj₁ gR) tt)
      (λ st₁ g₁ → amguᵛ-good P zero p rg A B st₁ (proj₂ gL) (proj₂ gR) g₁)
  amguᵛ-good P (suc k) p rg (Base b) Unit anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (Base b) Unit anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (Base b) Bool anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (Base b) Bool anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (Base b) (B |×| B') anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (Base b) (B |×| B') anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (Base b) Empty anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (Base b) Empty anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (Base b) (B ⇒ D) anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (Base b) (B ⇒ D) anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (Base b) ([ ρ' ] B) anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (Base b) ([ ρ' ] B) anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Unit (Base b') anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Unit (Base b') anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Unit Bool anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Unit Bool anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Unit (B |×| B') anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Unit (B |×| B') anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Unit Empty anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Unit Empty anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Unit (B ⇒ D) anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Unit (B ⇒ D) anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Unit ([ ρ' ] B) anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Unit ([ ρ' ] B) anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Bool (Base b') anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Bool (Base b') anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Bool Unit anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Bool Unit anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Bool (B |×| B') anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Bool (B |×| B') anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Bool Empty anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Bool Empty anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Bool (B ⇒ D) anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Bool (B ⇒ D) anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Bool ([ ρ' ] B) anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Bool ([ ρ' ] B) anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (A |×| A') (Base b') anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (A |×| A') (Base b') anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (A |×| A') Unit anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (A |×| A') Unit anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (A |×| A') Bool anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (A |×| A') Bool anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (A |×| A') Empty anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (A |×| A') Empty anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (A |×| A') (B ⇒ D) anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (A |×| A') (B ⇒ D) anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (A |×| A') ([ ρ' ] B) anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (A |×| A') ([ ρ' ] B) anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Empty (Base b') anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Empty (Base b') anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Empty Unit anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Empty Unit anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Empty Bool anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Empty Bool anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Empty (B |×| B') anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Empty (B |×| B') anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Empty (B ⇒ D) anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Empty (B ⇒ D) anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg Empty ([ ρ' ] B) anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg Empty ([ ρ' ] B) anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (A ⇒ C) (Base b') anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (A ⇒ C) (Base b') anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (A ⇒ C) Unit anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (A ⇒ C) Unit anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (A ⇒ C) Bool anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (A ⇒ C) Bool anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (A ⇒ C) (B |×| B') anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (A ⇒ C) (B |×| B') anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (A ⇒ C) Empty anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (A ⇒ C) Empty anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg (A ⇒ C) ([ ρ' ] B) anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg (A ⇒ C) ([ ρ' ] B) anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg ([ ρ ] A) (Base b') anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg ([ ρ ] A) (Base b') anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg ([ ρ ] A) Unit anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg ([ ρ ] A) Unit anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg ([ ρ ] A) Bool anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg ([ ρ ] A) Bool anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg ([ ρ ] A) (B |×| B') anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg ([ ρ ] A) (B |×| B') anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg ([ ρ ] A) Empty anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg ([ ρ ] A) Empty anil gL gR _ =
    λ ()
  amguᵛ-good P (suc k) p rg ([ ρ ] A) (B ⇒ D) anil gL gR _ =
    λ ()
  amguᵛ-good P zero p rg ([ ρ ] A) (B ⇒ D) anil gL gR _ =
    λ ()
  amguᶜ-good P (suc k) p rg C D (X /ᵗ α ∷ τ) gL gR (gX , gτ) =
    descᵗ-good {P = P} X α gX
      (amguᶜ-good (P ⨟ˢ (X forᵗ α)) k (szᵗ τ p) rg (C [ X forᵗ α ]ᶜ) (D [ X forᵗ α ]ᶜ) τ
        (tygoodᶜ-⨟ {P = P} (GV-forᵗ {X = X} {α = α} gX) C gL) (tygoodᶜ-⨟ {P = P} (GV-forᵗ {X = X} {α = α} gX) D gR) gτ)
  amguᶜ-good P (suc k) p rg C D (X /ʳ i ∷ τ) gL gR (gX , gτ) =
    descʳ-good {P = P} X i gX
      (amguᶜ-good (P ⨟ˢ (X forʳ i)) k (szʳ τ p) rg (C [ X forʳ i ]ᶜ) (D [ X forʳ i ]ᶜ) τ
        (tygoodᶜ-⨟ {P = P} (GV-forʳ {X = X} {i = i} gX) C gL) (tygoodᶜ-⨟ {P = P} (GV-forʳ {X = X} {i = i} gX) D gR) gτ)
  amguᶜ-good P (suc k) p rg C D (X /ᵉ i ∷ τ) gL gR (gX , gτ) =
    descᵉ-good {P = P} X i gX
      (amguᶜ-good (P ⨟ˢ (X forᵉ i)) k (szᵉ τ p) (popʳᵍ τ i rg) (C [ X forᵉ i ]ᶜ) (D [ X forᵉ i ]ᶜ) τ
        (tygoodᶜ-⨟ {P = P} (GV-forᵉ {X = X} {i = i} gX) C gL) (tygoodᶜ-⨟ {P = P} (GV-forᵉ {X = X} {i = i} gX) D gR) gτ)
  amguᶜ-good P zero p rg C D (X /ᵗ α ∷ τ) gL gR (gX , gτ) =
    sz0ᵗ τ p
  amguᶜ-good P zero p rg C D (X /ʳ i ∷ τ) gL gR (gX , gτ) =
    sz0ʳ τ p
  amguᶜ-good P zero p rg C D (X /ᵉ i ∷ τ) gL gR (gX , gτ) =
    sz0ᵉ τ p
  amguᶜ-good {Θ = Θ} P (suc k) p rg (A ‼ ε) (B ‼ ε') anil gL gR _ =
    seq-good P (amguᵛ (suc k) p rg A B (Θ , anil)) (amguᵉ (suc k) p rg ε ε')
      (amguᵛ-good P (suc k) p rg A B anil (proj₁ gL) (proj₁ gR) tt)
      (λ st₁ g₁ → amguᵉ-good P (suc k) p rg ε ε' st₁ (proj₂ gL) (proj₂ gR) g₁)
  amguᶜ-good {Θ = Θ} P zero p rg (A ‼ ε) (B ‼ ε') anil gL gR _ =
    seq-good P (amguᵛ zero p rg A B (Θ , anil)) (amguᵉ zero p rg ε ε')
      (amguᵛ-good P zero p rg A B anil (proj₁ gL) (proj₁ gR) tt)
      (λ st₁ g₁ → amguᵉ-good P zero p rg ε ε' st₁ (proj₂ gL) (proj₂ gR) g₁)
  amguʳ-good P (suc k) p rg ρ₀ ρ₁ (X /ᵗ α ∷ τ) gL gR (gX , gτ) =
    descᵗ-good {P = P} X α gX
      (amguʳ-good (P ⨟ˢ (X forᵗ α)) k (szᵗ τ p) rg (ρ₀ [ X forᵗ α ]ʳ) (ρ₁ [ X forᵗ α ]ʳ) τ
        (goodᵣ-⨟ {P = P} (GV-forᵗ {X = X} {α = α} gX) gL) (goodᵣ-⨟ {P = P} (GV-forᵗ {X = X} {α = α} gX) gR) gτ)
  amguʳ-good P (suc k) p rg ρ₀ ρ₁ (X /ʳ i ∷ τ) gL gR (gX , gτ) =
    descʳ-good {P = P} X i gX
      (amguʳ-good (P ⨟ˢ (X forʳ i)) k (szʳ τ p) rg (ρ₀ [ X forʳ i ]ʳ) (ρ₁ [ X forʳ i ]ʳ) τ
        (goodᵣ-⨟ {P = P} (GV-forʳ {X = X} {i = i} gX) gL) (goodᵣ-⨟ {P = P} (GV-forʳ {X = X} {i = i} gX) gR) gτ)
  amguʳ-good P (suc k) p rg ρ₀ ρ₁ (X /ᵉ i ∷ τ) gL gR (gX , gτ) =
    descᵉ-good {P = P} X i gX
      (amguʳ-good (P ⨟ˢ (X forᵉ i)) k (szᵉ τ p) (popʳᵍ τ i rg) (ρ₀ [ X forᵉ i ]ʳ) (ρ₁ [ X forᵉ i ]ʳ) τ
        (goodᵣ-⨟ {P = P} (GV-forᵉ {X = X} {i = i} gX) gL) (goodᵣ-⨟ {P = P} (GV-forᵉ {X = X} {i = i} gX) gR) gτ)
  amguʳ-good P zero p rg ρ₀ ρ₁ (X /ᵗ α ∷ τ) gL gR (gX , gτ) =
    sz0ᵗ τ p
  amguʳ-good P zero p rg ρ₀ ρ₁ (X /ʳ i ∷ τ) gL gR (gX , gτ) =
    sz0ʳ τ p
  amguʳ-good P zero p rg ρ₀ ρ₁ (X /ᵉ i ∷ τ) gL gR (gX , gτ) =
    sz0ᵉ τ p
  amguʳ-good P (suc k) p rg (rvar i) (rvar j) anil gL gR _ =
    flexFlexʳ-good P i j
  amguʳ-good P (suc k) p rg (rvar i) (rconst d) anil gL gR _ =
    flexʳ-good P i (rconst d) gR
  amguʳ-good P (suc k) p rg (rvar i) (ρ₁' ·̂ᵣ ρ₂') anil gL gR _ =
    flexʳ-good P i (ρ₁' ·̂ᵣ ρ₂') gR
  amguʳ-good P (suc k) p rg (rvar i) (ρ₁' ⊔̂ᵣ ρ₂') anil gL gR _ =
    flexʳ-good P i (ρ₁' ⊔̂ᵣ ρ₂') gR
  amguʳ-good P (suc k) p rg (rvar i) ∣ ε' ∣̂ᵉ anil gL gR _ =
    flexʳ-good P i ∣ ε' ∣̂ᵉ gR
  amguʳ-good P (suc k) p rg (rconst c) (rvar j) anil gL gR _ =
    flexʳ-good P j (rconst c) gL
  amguʳ-good P (suc k) p rg (ρ₁ ·̂ᵣ ρ₂) (rvar j) anil gL gR _ =
    flexʳ-good P j (ρ₁ ·̂ᵣ ρ₂) gL
  amguʳ-good P (suc k) p rg (ρ₁ ⊔̂ᵣ ρ₂) (rvar j) anil gL gR _ =
    flexʳ-good P j (ρ₁ ⊔̂ᵣ ρ₂) gL
  amguʳ-good P (suc k) p rg ∣ ε ∣̂ᵉ (rvar j) anil gL gR _ =
    flexʳ-good P j ∣ ε ∣̂ᵉ gL
  amguʳ-good P (suc k) p rg (rconst c) (rconst d) anil gL gR _ =
    const-good P (c ≡ᵣ? d)
  amguʳ-good {Θ = Θ} P (suc k) p rg (ρ₁ ·̂ᵣ ρ₂) (ρ₁' ·̂ᵣ ρ₂') anil gL gR _ =
    seq-good P (amguʳ (suc k) p rg ρ₁ ρ₁' (Θ , anil)) (amguʳ (suc k) p rg ρ₂ ρ₂')
      (amguʳ-good P (suc k) p rg ρ₁ ρ₁' anil (goodʳ·₁ gL) (goodʳ·₁ gR) tt)
      (λ st₁ g₁ → amguʳ-good P (suc k) p rg ρ₂ ρ₂' st₁ (goodʳ·₂ gL) (goodʳ·₂ gR) g₁)
  amguʳ-good {Θ = Θ} P (suc k) p rg (ρ₁ ⊔̂ᵣ ρ₂) (ρ₁' ⊔̂ᵣ ρ₂') anil gL gR _ =
    seq-good P (amguʳ (suc k) p rg ρ₁ ρ₁' (Θ , anil)) (amguʳ (suc k) p rg ρ₂ ρ₂')
      (amguʳ-good P (suc k) p rg ρ₁ ρ₁' anil (goodʳ⊔₁ gL) (goodʳ⊔₁ gR) tt)
      (λ st₁ g₁ → amguʳ-good P (suc k) p rg ρ₂ ρ₂' st₁ (goodʳ⊔₂ gL) (goodʳ⊔₂ gR) g₁)
  amguʳ-good P (suc k) p rg ∣ ε ∣̂ᵉ ∣ ε' ∣̂ᵉ anil gL gR _ =
    amguᵉ-good P (suc k) p rg ε ε' anil (goodʳ∣∣ gL) (goodʳ∣∣ gR) tt
  amguʳ-good P zero p rg (rvar i) (rvar j) anil gL gR _ =
    flexFlexʳ-good P i j
  amguʳ-good P zero p rg (rvar i) (rconst d) anil gL gR _ =
    flexʳ-good P i (rconst d) gR
  amguʳ-good P zero p rg (rvar i) (ρ₁' ·̂ᵣ ρ₂') anil gL gR _ =
    flexʳ-good P i (ρ₁' ·̂ᵣ ρ₂') gR
  amguʳ-good P zero p rg (rvar i) (ρ₁' ⊔̂ᵣ ρ₂') anil gL gR _ =
    flexʳ-good P i (ρ₁' ⊔̂ᵣ ρ₂') gR
  amguʳ-good P zero p rg (rvar i) ∣ ε' ∣̂ᵉ anil gL gR _ =
    flexʳ-good P i ∣ ε' ∣̂ᵉ gR
  amguʳ-good P zero p rg (rconst c) (rvar j) anil gL gR _ =
    flexʳ-good P j (rconst c) gL
  amguʳ-good P zero p rg (ρ₁ ·̂ᵣ ρ₂) (rvar j) anil gL gR _ =
    flexʳ-good P j (ρ₁ ·̂ᵣ ρ₂) gL
  amguʳ-good P zero p rg (ρ₁ ⊔̂ᵣ ρ₂) (rvar j) anil gL gR _ =
    flexʳ-good P j (ρ₁ ⊔̂ᵣ ρ₂) gL
  amguʳ-good P zero p rg ∣ ε ∣̂ᵉ (rvar j) anil gL gR _ =
    flexʳ-good P j ∣ ε ∣̂ᵉ gL
  amguʳ-good P zero p rg (rconst c) (rconst d) anil gL gR _ =
    const-good P (c ≡ᵣ? d)
  amguʳ-good {Θ = Θ} P zero p rg (ρ₁ ·̂ᵣ ρ₂) (ρ₁' ·̂ᵣ ρ₂') anil gL gR _ =
    seq-good P (amguʳ zero p rg ρ₁ ρ₁' (Θ , anil)) (amguʳ zero p rg ρ₂ ρ₂')
      (amguʳ-good P zero p rg ρ₁ ρ₁' anil (goodʳ·₁ gL) (goodʳ·₁ gR) tt)
      (λ st₁ g₁ → amguʳ-good P zero p rg ρ₂ ρ₂' st₁ (goodʳ·₂ gL) (goodʳ·₂ gR) g₁)
  amguʳ-good {Θ = Θ} P zero p rg (ρ₁ ⊔̂ᵣ ρ₂) (ρ₁' ⊔̂ᵣ ρ₂') anil gL gR _ =
    seq-good P (amguʳ zero p rg ρ₁ ρ₁' (Θ , anil)) (amguʳ zero p rg ρ₂ ρ₂')
      (amguʳ-good P zero p rg ρ₁ ρ₁' anil (goodʳ⊔₁ gL) (goodʳ⊔₁ gR) tt)
      (λ st₁ g₁ → amguʳ-good P zero p rg ρ₂ ρ₂' st₁ (goodʳ⊔₂ gL) (goodʳ⊔₂ gR) g₁)
  amguʳ-good P zero p rg ∣ ε ∣̂ᵉ ∣ ε' ∣̂ᵉ anil gL gR _ =
    amguᵉ-good P zero p rg ε ε' anil (goodʳ∣∣ gL) (goodʳ∣∣ gR) tt
  amguʳ-good P (suc k) p rg (rconst c) (ρ₁' ·̂ᵣ ρ₂') anil gL gR _ =
    λ ()
  amguʳ-good P zero p rg (rconst c) (ρ₁' ·̂ᵣ ρ₂') anil gL gR _ =
    λ ()
  amguʳ-good P (suc k) p rg (rconst c) (ρ₁' ⊔̂ᵣ ρ₂') anil gL gR _ =
    λ ()
  amguʳ-good P zero p rg (rconst c) (ρ₁' ⊔̂ᵣ ρ₂') anil gL gR _ =
    λ ()
  amguʳ-good P (suc k) p rg (rconst c) ∣ ε' ∣̂ᵉ anil gL gR _ =
    λ ()
  amguʳ-good P zero p rg (rconst c) ∣ ε' ∣̂ᵉ anil gL gR _ =
    λ ()
  amguʳ-good P (suc k) p rg (ρ₁ ·̂ᵣ ρ₂) (rconst d) anil gL gR _ =
    λ ()
  amguʳ-good P zero p rg (ρ₁ ·̂ᵣ ρ₂) (rconst d) anil gL gR _ =
    λ ()
  amguʳ-good P (suc k) p rg (ρ₁ ·̂ᵣ ρ₂) (ρ₁' ⊔̂ᵣ ρ₂') anil gL gR _ =
    λ ()
  amguʳ-good P zero p rg (ρ₁ ·̂ᵣ ρ₂) (ρ₁' ⊔̂ᵣ ρ₂') anil gL gR _ =
    λ ()
  amguʳ-good P (suc k) p rg (ρ₁ ·̂ᵣ ρ₂) ∣ ε' ∣̂ᵉ anil gL gR _ =
    λ ()
  amguʳ-good P zero p rg (ρ₁ ·̂ᵣ ρ₂) ∣ ε' ∣̂ᵉ anil gL gR _ =
    λ ()
  amguʳ-good P (suc k) p rg (ρ₁ ⊔̂ᵣ ρ₂) (rconst d) anil gL gR _ =
    λ ()
  amguʳ-good P zero p rg (ρ₁ ⊔̂ᵣ ρ₂) (rconst d) anil gL gR _ =
    λ ()
  amguʳ-good P (suc k) p rg (ρ₁ ⊔̂ᵣ ρ₂) (ρ₁' ·̂ᵣ ρ₂') anil gL gR _ =
    λ ()
  amguʳ-good P zero p rg (ρ₁ ⊔̂ᵣ ρ₂) (ρ₁' ·̂ᵣ ρ₂') anil gL gR _ =
    λ ()
  amguʳ-good P (suc k) p rg (ρ₁ ⊔̂ᵣ ρ₂) ∣ ε' ∣̂ᵉ anil gL gR _ =
    λ ()
  amguʳ-good P zero p rg (ρ₁ ⊔̂ᵣ ρ₂) ∣ ε' ∣̂ᵉ anil gL gR _ =
    λ ()
  amguʳ-good P (suc k) p rg ∣ ε ∣̂ᵉ (rconst d) anil gL gR _ =
    λ ()
  amguʳ-good P zero p rg ∣ ε ∣̂ᵉ (rconst d) anil gL gR _ =
    λ ()
  amguʳ-good P (suc k) p rg ∣ ε ∣̂ᵉ (ρ₁' ·̂ᵣ ρ₂') anil gL gR _ =
    λ ()
  amguʳ-good P zero p rg ∣ ε ∣̂ᵉ (ρ₁' ·̂ᵣ ρ₂') anil gL gR _ =
    λ ()
  amguʳ-good P (suc k) p rg ∣ ε ∣̂ᵉ (ρ₁' ⊔̂ᵣ ρ₂') anil gL gR _ =
    λ ()
  amguʳ-good P zero p rg ∣ ε ∣̂ᵉ (ρ₁' ⊔̂ᵣ ρ₂') anil gL gR _ =
    λ ()
  amguᵉ-good P (suc k) p rg ε ε' (X /ᵗ α ∷ τ) gL gR (gX , gτ) =
    descᵗ-good {P = P} X α gX
      (amguᵉ-good (P ⨟ˢ (X forᵗ α)) k (szᵗ τ p) rg (ε [ X forᵗ α ]ᵉ) (ε' [ X forᵗ α ]ᵉ) τ
        (goodₑ-⨟ {P = P} (GV-forᵗ {X = X} {α = α} gX) gL) (goodₑ-⨟ {P = P} (GV-forᵗ {X = X} {α = α} gX) gR) gτ)
  amguᵉ-good P (suc k) p rg ε ε' (X /ʳ i ∷ τ) gL gR (gX , gτ) =
    descʳ-good {P = P} X i gX
      (amguᵉ-good (P ⨟ˢ (X forʳ i)) k (szʳ τ p) rg (ε [ X forʳ i ]ᵉ) (ε' [ X forʳ i ]ᵉ) τ
        (goodₑ-⨟ {P = P} (GV-forʳ {X = X} {i = i} gX) gL) (goodₑ-⨟ {P = P} (GV-forʳ {X = X} {i = i} gX) gR) gτ)
  amguᵉ-good P (suc k) p rg ε ε' (X /ᵉ i ∷ τ) gL gR (gX , gτ) =
    descᵉ-good {P = P} X i gX
      (amguᵉ-good (P ⨟ˢ (X forᵉ i)) k (szᵉ τ p) (popʳᵍ τ i rg) (ε [ X forᵉ i ]ᵉ) (ε' [ X forᵉ i ]ᵉ) τ
        (goodₑ-⨟ {P = P} (GV-forᵉ {X = X} {i = i} gX) gL) (goodₑ-⨟ {P = P} (GV-forᵉ {X = X} {i = i} gX) gR) gτ)
  amguᵉ-good P zero p rg ε ε' (X /ᵗ α ∷ τ) gL gR (gX , gτ) =
    sz0ᵗ τ p
  amguᵉ-good P zero p rg ε ε' (X /ʳ i ∷ τ) gL gR (gX , gτ) =
    sz0ʳ τ p
  amguᵉ-good P zero p rg ε ε' (X /ᵉ i ∷ τ) gL gR (gX , gτ) =
    sz0ᵉ τ p
  amguᵉ-good P (suc k) p rg (evar i) (evar j) anil gL gR _ =
    flexFlexᵉ-good P rg i j
  amguᵉ-good P (suc k) p rg (evar i) (econst d) anil gL gR _ =
    flexᵉ-good P rg i (econst d) gR
  amguᵉ-good P (suc k) p rg (evar i) (ε₁' ·̂ₑ ε₂') anil gL gR _ =
    flexᵉ-good P rg i (ε₁' ·̂ₑ ε₂') gR
  amguᵉ-good P (suc k) p rg (evar i) (ε₁' ⊔̂ₑ ε₂') anil gL gR _ =
    flexᵉ-good P rg i (ε₁' ⊔̂ₑ ε₂') gR
  amguᵉ-good P (suc k) p rg (econst c) (evar j) anil gL gR _ =
    flexᵉ-good P rg j (econst c) gL
  amguᵉ-good P (suc k) p rg (ε₁ ·̂ₑ ε₂) (evar j) anil gL gR _ =
    flexᵉ-good P rg j (ε₁ ·̂ₑ ε₂) gL
  amguᵉ-good P (suc k) p rg (ε₁ ⊔̂ₑ ε₂) (evar j) anil gL gR _ =
    flexᵉ-good P rg j (ε₁ ⊔̂ₑ ε₂) gL
  amguᵉ-good P (suc k) p rg (econst c) (econst d) anil gL gR _ =
    const-good P (c ≡ₑ? d)
  amguᵉ-good {Θ = Θ} P (suc k) p rg (ε₁ ·̂ₑ ε₂) (ε₁' ·̂ₑ ε₂') anil gL gR _ =
    seq-good P (amguᵉ (suc k) p rg ε₁ ε₁' (Θ , anil)) (amguᵉ (suc k) p rg ε₂ ε₂')
      (amguᵉ-good P (suc k) p rg ε₁ ε₁' anil (good·₁ gL) (good·₁ gR) tt)
      (λ st₁ g₁ → amguᵉ-good P (suc k) p rg ε₂ ε₂' st₁ (good·₂ gL) (good·₂ gR) g₁)
  amguᵉ-good {Θ = Θ} P (suc k) p rg (ε₁ ⊔̂ₑ ε₂) (ε₁' ⊔̂ₑ ε₂') anil gL gR _ =
    seq-good P (amguᵉ (suc k) p rg ε₁ ε₁' (Θ , anil)) (amguᵉ (suc k) p rg ε₂ ε₂')
      (amguᵉ-good P (suc k) p rg ε₁ ε₁' anil (good⊔₁ gL) (good⊔₁ gR) tt)
      (λ st₁ g₁ → amguᵉ-good P (suc k) p rg ε₂ ε₂' st₁ (good⊔₂ gL) (good⊔₂ gR) g₁)
  amguᵉ-good P zero p rg (evar i) (evar j) anil gL gR _ =
    flexFlexᵉ-good P rg i j
  amguᵉ-good P zero p rg (evar i) (econst d) anil gL gR _ =
    flexᵉ-good P rg i (econst d) gR
  amguᵉ-good P zero p rg (evar i) (ε₁' ·̂ₑ ε₂') anil gL gR _ =
    flexᵉ-good P rg i (ε₁' ·̂ₑ ε₂') gR
  amguᵉ-good P zero p rg (evar i) (ε₁' ⊔̂ₑ ε₂') anil gL gR _ =
    flexᵉ-good P rg i (ε₁' ⊔̂ₑ ε₂') gR
  amguᵉ-good P zero p rg (econst c) (evar j) anil gL gR _ =
    flexᵉ-good P rg j (econst c) gL
  amguᵉ-good P zero p rg (ε₁ ·̂ₑ ε₂) (evar j) anil gL gR _ =
    flexᵉ-good P rg j (ε₁ ·̂ₑ ε₂) gL
  amguᵉ-good P zero p rg (ε₁ ⊔̂ₑ ε₂) (evar j) anil gL gR _ =
    flexᵉ-good P rg j (ε₁ ⊔̂ₑ ε₂) gL
  amguᵉ-good P zero p rg (econst c) (econst d) anil gL gR _ =
    const-good P (c ≡ₑ? d)
  amguᵉ-good {Θ = Θ} P zero p rg (ε₁ ·̂ₑ ε₂) (ε₁' ·̂ₑ ε₂') anil gL gR _ =
    seq-good P (amguᵉ zero p rg ε₁ ε₁' (Θ , anil)) (amguᵉ zero p rg ε₂ ε₂')
      (amguᵉ-good P zero p rg ε₁ ε₁' anil (good·₁ gL) (good·₁ gR) tt)
      (λ st₁ g₁ → amguᵉ-good P zero p rg ε₂ ε₂' st₁ (good·₂ gL) (good·₂ gR) g₁)
  amguᵉ-good {Θ = Θ} P zero p rg (ε₁ ⊔̂ₑ ε₂) (ε₁' ⊔̂ₑ ε₂') anil gL gR _ =
    seq-good P (amguᵉ zero p rg ε₁ ε₁' (Θ , anil)) (amguᵉ zero p rg ε₂ ε₂')
      (amguᵉ-good P zero p rg ε₁ ε₁' anil (good⊔₁ gL) (good⊔₁ gR) tt)
      (λ st₁ g₁ → amguᵉ-good P zero p rg ε₂ ε₂' st₁ (good⊔₂ gL) (good⊔₂ gR) g₁)
  amguᵉ-good P (suc k) p rg (econst c) (ε₁' ·̂ₑ ε₂') anil gL gR _ =
    λ ()
  amguᵉ-good P zero p rg (econst c) (ε₁' ·̂ₑ ε₂') anil gL gR _ =
    λ ()
  amguᵉ-good P (suc k) p rg (econst c) (ε₁' ⊔̂ₑ ε₂') anil gL gR _ =
    λ ()
  amguᵉ-good P zero p rg (econst c) (ε₁' ⊔̂ₑ ε₂') anil gL gR _ =
    λ ()

-- The unifier of one equation between good types

unify-good : ∀ {Θ₀ Ψ} {P : Subst Θ₀ Ψ} → (rg : Rig Ψ) → (A B : OVType Ψ)
           → TyGoodᵛ P A → TyGoodᵛ P B
           → ∀ {Ψ⁺} {ρ : AList Ψ Ψ⁺} → unify rg (eqᵛ A B ∷ []) ≡ just (Ψ⁺ , ρ)
           → GV (P ⨟ˢ ⟦ ρ ⟧ᴬ) ⟦ ρ ⟧ᴬ
unify-good {Ψ = Ψ} {P} rg A B gA gB {ρ = ρ} eq =
  GoodAL→GV P ρ
    (seq-good P (amguᵛ (Sz Ψ) refl rg A B (Ψ , anil)) (unifyᴬ rg [])
              (amguᵛ-good P (Sz Ψ) refl rg A B anil gA gB tt)
              (λ st₁ g₁ → λ { refl → g₁ }) eq)
