------------------------------------------------------------------
-- Localisation keeps the invariants                              --
--                                                                --
-- `localise` assigns local unknowns only, which occur in no      --
-- image of the protected unknowns, so a greater side over        --
-- protected unknowns is left alone and the deferred entries      --
-- keep theirs. A whole greater side is sent to the value of its  --
-- unknown: a good one, except for lowering, whose join of lower  --
-- bounds is above each ordering it bounds. Within a round the    --
-- residual is kept in a weaker form: every greater side is good, --
-- or is a join among whose members is the ordering's smaller     --
-- side. Such an ordering holds at every instance and the decider --
-- finds it, so the settling that ends each round drops it.       --
-- Canonical forms keep good sides good.                          --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to isJust)
open import Data.Nat.Base using (ℕ; _+_) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Invariants.Localise (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S using (Hyps; ∅ᴴ; mapᵖ; mapᵈ; Is-just?)

open import TypeInference.SolverImpl.Core.Occurs S
  using (occᵉ-e; occᵉ-r; occᵉ-v; occᵉ-c; occʳ-r; occʳ-v; occʳ-c)
open import TypeInference.SolverImpl.Core.Rigid S using (∨-true; ∨-left; ∨-right; dec-true; true-dec)
open import TypeInference.SolverImpl.Deferred S using (Dfr; _[_]ᵈ; stills?; dir↓; dir↑)
open import TypeInference.SolverImpl.Resid    S
open import TypeInference.SolverImpl.Eliminate S using (joinₑ; joinᵣ)
open import TypeInference.SolverImpl.Normal   S using (decide≾ᵣ; decide≾ₑ)
open import TypeInference.SolverImpl.Canon    S using (canonᵣ; canonₑ)
open import TypeInference.SolverImpl.Product  S using (alt; _∷⁺_)
open import TypeInference.SolverImpl.Localise S
open import TypeInference.SolverImpl.Invariants.Outer    S
open import TypeInference.SolverImpl.Invariants.Residual S
open import TypeInference.SolverImpl.Invariants.Join     S using (join-decideₑ; join-decideᵣ)
open import TypeInference.SolverImpl.Invariants.Canon    S
  using (canonₑ-var; canonᵣ-var; canonₑ-occ; canonᵣ-occʳ; canonᵣ-occᵉ)

------------------------------------------------------------------------
-- A greater side that is a join with the smaller side among its members

JoinAltₑ : ∀ {Ψ} → EExp Ψ → EExp Ψ → Set
JoinAltₑ x y = Σ[ x₀ ∈ _ ] Σ[ xs ∈ _ ] ((y ≡ joinₑ x₀ xs) × (x ∈ x₀ ∷ xs))

JoinAltᵣ : ∀ {Ψ} → RExp Ψ → RExp Ψ → Set
JoinAltᵣ x y = Σ[ x₀ ∈ _ ] Σ[ xs ∈ _ ] ((y ≡ joinᵣ x₀ xs) × (x ∈ x₀ ∷ xs))

-- it is one at every substitution

joinₑ-subst : ∀ {Ψ Ψ'} (σ : Subst Ψ Ψ') (x₀ : EExp Ψ) xs
            → joinₑ x₀ xs [ σ ]ᵉ ≡ joinₑ (x₀ [ σ ]ᵉ) (map (_[ σ ]ᵉ) xs)
joinₑ-subst σ x₀ []       = refl
joinₑ-subst σ x₀ (x ∷ xs) = joinₑ-subst σ (x₀ ⊔̂ₑ x) xs

joinᵣ-subst : ∀ {Ψ Ψ'} (σ : Subst Ψ Ψ') (x₀ : RExp Ψ) xs
            → joinᵣ x₀ xs [ σ ]ʳ ≡ joinᵣ (x₀ [ σ ]ʳ) (map (_[ σ ]ʳ) xs)
joinᵣ-subst σ x₀ []       = refl
joinᵣ-subst σ x₀ (x ∷ xs) = joinᵣ-subst σ (x₀ ⊔̂ᵣ x) xs

joinAltₑ-subst : ∀ {Ψ Ψ'} (σ : Subst Ψ Ψ') {x y} → JoinAltₑ x y → JoinAltₑ (x [ σ ]ᵉ) (y [ σ ]ᵉ)
joinAltₑ-subst σ (x₀ , xs , refl , m) =
  x₀ [ σ ]ᵉ , map (_[ σ ]ᵉ) xs , joinₑ-subst σ x₀ xs , ∈-map⁺ (_[ σ ]ᵉ) m

joinAltᵣ-subst : ∀ {Ψ Ψ'} (σ : Subst Ψ Ψ') {x y} → JoinAltᵣ x y → JoinAltᵣ (x [ σ ]ʳ) (y [ σ ]ʳ)
joinAltᵣ-subst σ (x₀ , xs , refl , m) =
  x₀ [ σ ]ʳ , map (_[ σ ]ʳ) xs , joinᵣ-subst σ x₀ xs , ∈-map⁺ (_[ σ ]ʳ) m

-- ... it mentions the smaller side's unknowns

joinₑ-occ : ∀ {Ψ} {k : EVar Ψ} (x₀ : EExp Ψ) xs {x} → x ∈ x₀ ∷ xs → occᵉ-e k x ≡ true
          → occᵉ-e k (joinₑ x₀ xs) ≡ true
joinₑ-occ x₀ []        (here refl)         q = q
joinₑ-occ {k = k} x₀ (x₁ ∷ xs) (here refl) q =
  joinₑ-occ (x₀ ⊔̂ₑ x₁) xs (here refl) (∨-left (occᵉ-e k x₀) _ q)
joinₑ-occ {k = k} x₀ (x₁ ∷ xs) (there (here refl)) q =
  joinₑ-occ (x₀ ⊔̂ₑ x₁) xs (here refl) (∨-right (occᵉ-e k x₀) _ q)
joinₑ-occ x₀ (x₁ ∷ xs) (there (there m)) q = joinₑ-occ (x₀ ⊔̂ₑ x₁) xs (there m) q

joinᵣ-occ : ∀ {Ψ} {k : RVar Ψ} (x₀ : RExp Ψ) xs {x} → x ∈ x₀ ∷ xs → occʳ-r k x ≡ true
          → occʳ-r k (joinᵣ x₀ xs) ≡ true
joinᵣ-occ x₀ []        (here refl)         q = q
joinᵣ-occ {k = k} x₀ (x₁ ∷ xs) (here refl) q =
  joinᵣ-occ (x₀ ⊔̂ᵣ x₁) xs (here refl) (∨-left (occʳ-r k x₀) _ q)
joinᵣ-occ {k = k} x₀ (x₁ ∷ xs) (there (here refl)) q =
  joinᵣ-occ (x₀ ⊔̂ᵣ x₁) xs (here refl) (∨-right (occʳ-r k x₀) _ q)
joinᵣ-occ x₀ (x₁ ∷ xs) (there (there m)) q = joinᵣ-occ (x₀ ⊔̂ᵣ x₁) xs (there m) q

-- ... and settled

settledₑ-join : ∀ {Ψ} {x y : EExp Ψ} → JoinAltₑ x y → Is-just (settledᵉ (x , y))
settledₑ-join {x = x} {y} (x₀ , xs , refl , m) with decide≾ₑ {Q = ∅ᴴ} x (joinₑ x₀ xs) | join-decideₑ {Q = ∅ᴴ} x₀ xs m
... | just _ | _ = isJust tt

settledᵣ-join : ∀ {Ψ} {x y : RExp Ψ} → JoinAltᵣ x y → Is-just (settledʳ (x , y))
settledᵣ-join {x = x} {y} (x₀ , xs , refl , m) with decide≾ᵣ {Q = ∅ᴴ} x (joinᵣ x₀ xs) | join-decideᵣ {Q = ∅ᴴ} x₀ xs m
... | just _ | _ = isJust tt

------------------------------------------------------------------------
-- The invariant within a round

record LInv {Θ Ψ} (P : Subst Θ Ψ) (R : Resid Ψ) : Set where
  constructor mkLInv
  field
    l-ss  : ∀ {A B} → (A , B) ∈ ss R → TyGoodᵛ P A × TyGoodᵛ P B
    l-rs  : ∀ {x y} → (x , y) ∈ rs R → Goodᵣ P y ⊎ JoinAltᵣ x y
    l-es  : ∀ {x y} → (x , y) ∈ es R → Goodₑ P y ⊎ JoinAltₑ x y
    l-dfs : ∀ {E} → E ∈ dfs R → Great P E

open LInv

linv : ∀ {Θ Ψ} {P : Subst Θ Ψ} {R : Resid Ψ} → ResInv P R → LInv P R
linv r = mkLInv (inv-ss r) (λ m → inj₁ (I1′ʳ r m)) (λ m → inj₁ (I1′ᵉ r m)) (I5 r)

------------------------------------------------------------------------
-- Settled atoms, pieces, and refined disjunctions

first-inv : ∀ {X : Set} (m₁ m₂ : Maybe X) {v} → first m₁ m₂ ≡ just v → (m₁ ≡ just v) ⊎ (m₂ ≡ just v)
first-inv (just x) m₂ e = inj₁ e
first-inv nothing  m₂ e = inj₂ e

kept-unset : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set}
           → (set : (a : X) → Maybe (Every P a)) → (l : List X)
           → ∀ {a} → a ∈ Unsettled.kept (unsettled set l) → Is-just (set a) → ⊥
kept-unset set (a ∷ l) m j with set a in e
... | just p = kept-unset set l m j
... | nothing with m
...   | here refl = nothing-just e j
  where
    nothing-just : ∀ {Y : Set} {x : Maybe Y} → x ≡ nothing → Is-just x → ⊥
    nothing-just refl ()
...   | there m' = kept-unset set l m' j

split-src : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set}
          → (f : (a : X) → Pieces P a) → (l : List X)
          → ∀ {b} → b ∈ Split.out (splits f l) → Σ[ a ∈ X ] ((a ∈ l) × (b ∈ Pieces.parts (f a)))
split-src f (a ∷ l) m with ∈-++⁻ (Pieces.parts (f a)) m
... | inj₁ m' = a , here refl , m'
... | inj₂ m' with split-src f l m'
...   | a' , ma , mb = a' , there ma , mb

partsʳ-rhs : ∀ {Ψ} s (y : RExp Ψ) {x y'} → (x , y') ∈ partsʳ s y → y' ≡ y
partsʳ-rhs (alt p)  y (here refl) = refl
partsʳ-rhs (p ∷⁺ s) y (here refl) = refl
partsʳ-rhs (p ∷⁺ s) y (there m)   = partsʳ-rhs s y m

partsₑ-rhs : ∀ {Ψ} s (y : EExp Ψ) {x y'} → (x , y') ∈ partsₑ s y → y' ≡ y
partsₑ-rhs (alt p)  y (here refl) = refl
partsₑ-rhs (p ∷⁺ s) y (here refl) = refl
partsₑ-rhs (p ∷⁺ s) y (there m)   = partsₑ-rhs s y m

------------------------------------------------------------------------
-- Canonical forms keep a side good

canon-goodₑ : ∀ {Θ Ψ} {P : Subst Θ Ψ} {y : EExp Ψ} → Goodₑ P y → Goodₑ P (canonₑ y)
canon-goodₑ {P = P} (whole k) = subst (Goodₑ P) (sym (canonₑ-var k)) (whole k)
canon-goodₑ {y = y} (outer o) = outer (λ q → o (canonₑ-occ y q))

canon-goodᵣ : ∀ {Θ Ψ} {P : Subst Θ Ψ} {y : RExp Ψ} → Goodᵣ P y → Goodᵣ P (canonᵣ y)
canon-goodᵣ {P = P} (whole k) = subst (Goodᵣ P) (sym (canonᵣ-var k)) (whole k)
canon-goodᵣ {y = y} (outer (oe , or)) = outer ((λ q → oe (canonᵣ-occᵉ y q)) , (λ q → or (canonᵣ-occʳ y q)))

------------------------------------------------------------------------
-- A member of a set sent to the top is hit wherever it occurs

module _ {Φ} (l : List (Mem Φ)) where

  hitₑ-occ : ∀ {i} → inᴱ i l ≡ true → (ε : EExp Φ) → occᵉ-e i ε ≡ true → hitₑ l ε ≡ true
  hitₑ-occ {i} p (evar j)   q = subst (λ z → inᴱ z l ≡ true) (true-dec (i ≟ᶠ j) q) p
  hitₑ-occ     p (econst c) ()
  hitₑ-occ {i} p (a ·̂ₑ b)   q with ∨-true (occᵉ-e i a) _ q
  ... | inj₁ q' = ∨-left (hitₑ l a) _ (hitₑ-occ p a q')
  ... | inj₂ q' = ∨-right (hitₑ l a) _ (hitₑ-occ p b q')
  hitₑ-occ {i} p (a ⊔̂ₑ b)   q with ∨-true (occᵉ-e i a) _ q
  ... | inj₁ q' = ∨-left (hitₑ l a) _ (hitₑ-occ p a q')
  ... | inj₂ q' = ∨-right (hitₑ l a) _ (hitₑ-occ p b q')

  hitᵣ-occᵉ : ∀ {i} → inᴱ i l ≡ true → (ρ : RExp Φ) → occᵉ-r i ρ ≡ true → hitᵣ l ρ ≡ true
  hitᵣ-occᵉ     p (rvar j)   ()
  hitᵣ-occᵉ     p (rconst c) ()
  hitᵣ-occᵉ {i} p (a ·̂ᵣ b)   q with ∨-true (occᵉ-r i a) _ q
  ... | inj₁ q' = ∨-left (hitᵣ l a) _ (hitᵣ-occᵉ p a q')
  ... | inj₂ q' = ∨-right (hitᵣ l a) _ (hitᵣ-occᵉ p b q')
  hitᵣ-occᵉ {i} p (a ⊔̂ᵣ b)   q with ∨-true (occᵉ-r i a) _ q
  ... | inj₁ q' = ∨-left (hitᵣ l a) _ (hitᵣ-occᵉ p a q')
  ... | inj₂ q' = ∨-right (hitᵣ l a) _ (hitᵣ-occᵉ p b q')
  hitᵣ-occᵉ     p ∣ ε ∣̂ᵉ     q = hitₑ-occ p ε q

  hitᵣ-occʳ : ∀ {i} → inᴿ i l ≡ true → (ρ : RExp Φ) → occʳ-r i ρ ≡ true → hitᵣ l ρ ≡ true
  hitᵣ-occʳ {i} p (rvar j)   q = subst (λ z → inᴿ z l ≡ true) (true-dec (i ≟ᶠ j) q) p
  hitᵣ-occʳ     p (rconst c) ()
  hitᵣ-occʳ {i} p (a ·̂ᵣ b)   q with ∨-true (occʳ-r i a) _ q
  ... | inj₁ q' = ∨-left (hitᵣ l a) _ (hitᵣ-occʳ p a q')
  ... | inj₂ q' = ∨-right (hitᵣ l a) _ (hitᵣ-occʳ p b q')
  hitᵣ-occʳ {i} p (a ⊔̂ᵣ b)   q with ∨-true (occʳ-r i a) _ q
  ... | inj₁ q' = ∨-left (hitᵣ l a) _ (hitᵣ-occʳ p a q')
  ... | inj₂ q' = ∨-right (hitᵣ l a) _ (hitᵣ-occʳ p b q')
  hitᵣ-occʳ     p ∣ ε ∣̂ᵉ     ()

  mutual

    hitᵥ-occᵉ : ∀ {i} → inᴱ i l ≡ true → (A : OVType Φ) → occᵉ-v i A ≡ true → hitᵥ l A ≡ true
    hitᵥ-occᵉ     p (tvar α)  ()
    hitᵥ-occᵉ     p (Base b)  ()
    hitᵥ-occᵉ     p Unit      ()
    hitᵥ-occᵉ     p Bool      ()
    hitᵥ-occᵉ     p Empty     ()
    hitᵥ-occᵉ {i} p (A |×| B) q with ∨-true (occᵉ-v i A) _ q
    ... | inj₁ q' = ∨-left (hitᵥ l A) _ (hitᵥ-occᵉ p A q')
    ... | inj₂ q' = ∨-right (hitᵥ l A) _ (hitᵥ-occᵉ p B q')
    hitᵥ-occᵉ {i} p (A ⇒ C)   q with ∨-true (occᵉ-v i A) _ q
    ... | inj₁ q' = ∨-left (hitᵥ l A) _ (hitᵥ-occᵉ p A q')
    ... | inj₂ q' = ∨-right (hitᵥ l A) _ (hitᶜ-occᵉ p C q')
    hitᵥ-occᵉ {i} p ([ ρ ] A) q with ∨-true (occᵉ-r i ρ) _ q
    ... | inj₁ q' = ∨-left (hitᵣ l ρ) _ (hitᵣ-occᵉ p ρ q')
    ... | inj₂ q' = ∨-right (hitᵣ l ρ) _ (hitᵥ-occᵉ p A q')

    hitᶜ-occᵉ : ∀ {i} → inᴱ i l ≡ true → (C : OCType Φ) → occᵉ-c i C ≡ true → hitᶜ l C ≡ true
    hitᶜ-occᵉ {i} p (A ‼ ε) q with ∨-true (occᵉ-v i A) _ q
    ... | inj₁ q' = ∨-left (hitᵥ l A) _ (hitᵥ-occᵉ p A q')
    ... | inj₂ q' = ∨-right (hitᵥ l A) _ (hitₑ-occ p ε q')

  mutual

    hitᵥ-occʳ : ∀ {i} → inᴿ i l ≡ true → (A : OVType Φ) → occʳ-v i A ≡ true → hitᵥ l A ≡ true
    hitᵥ-occʳ     p (tvar α)  ()
    hitᵥ-occʳ     p (Base b)  ()
    hitᵥ-occʳ     p Unit      ()
    hitᵥ-occʳ     p Bool      ()
    hitᵥ-occʳ     p Empty     ()
    hitᵥ-occʳ {i} p (A |×| B) q with ∨-true (occʳ-v i A) _ q
    ... | inj₁ q' = ∨-left (hitᵥ l A) _ (hitᵥ-occʳ p A q')
    ... | inj₂ q' = ∨-right (hitᵥ l A) _ (hitᵥ-occʳ p B q')
    hitᵥ-occʳ {i} p (A ⇒ C)   q with ∨-true (occʳ-v i A) _ q
    ... | inj₁ q' = ∨-left (hitᵥ l A) _ (hitᵥ-occʳ p A q')
    ... | inj₂ q' = ∨-right (hitᵥ l A) _ (hitᶜ-occʳ p C q')
    hitᵥ-occʳ {i} p ([ ρ ] A) q with ∨-true (occʳ-r i ρ) _ q
    ... | inj₁ q' = ∨-left (hitᵣ l ρ) _ (hitᵣ-occʳ p ρ q')
    ... | inj₂ q' = ∨-right (hitᵣ l ρ) _ (hitᵥ-occʳ p A q')

    hitᶜ-occʳ : ∀ {i} → inᴿ i l ≡ true → (C : OCType Φ) → occʳ-c i C ≡ true → hitᶜ l C ≡ true
    hitᶜ-occʳ p (A ‼ ε) q = ∨-left (hitᵥ l A) _ (hitᵥ-occʳ p A q)

  -- so an unknown free in an image of `O` is no member, where no
  -- member occurs in one

  notMemᵉ : ∀ {Θ} {O : Subst Θ Φ} {i} → freeᴹ l O ≡ false → freeᵉ i O ≡ true → inᴱ i l ≡ false
  notMemᵉ {O = O} {i} fx q with inᴱ i l in e
  ... | false = refl
  ... | true  = ⊥-elim (f≢t (trans (sym fx) hit))
    where
      f≢t : false ≡ true → ⊥
      f≢t ()

      hit : freeᴹ l O ≡ true
      hit with ∨-true (anyᶠ (λ α → occᵉ-v i (sTy O α))) _ q
      ... | inj₁ qt with anyᶠ-true (λ α → occᵉ-v i (sTy O α)) qt
      ...   | α , r = ∨-left (anyᶠ (λ α' → hitᵥ l (sTy O α'))) _
                        (anyᶠ-intro (λ α' → hitᵥ l (sTy O α')) α (hitᵥ-occᵉ e (sTy O α) r))
      hit | inj₂ q' with ∨-true (anyᶠ (λ j → occᵉ-r i (sR O j))) _ q'
      ...   | inj₁ qr with anyᶠ-true (λ j → occᵉ-r i (sR O j)) qr
      ...     | j , r = ∨-right (anyᶠ (λ α' → hitᵥ l (sTy O α'))) _
                          (∨-left (anyᶠ (λ j' → hitᵣ l (sR O j'))) _
                            (anyᶠ-intro (λ j' → hitᵣ l (sR O j')) j (hitᵣ-occᵉ e (sR O j) r)))
      hit | inj₂ q' | inj₂ qe with anyᶠ-true (λ j → occᵉ-e i (sE O j)) qe
      ...     | j , r = ∨-right (anyᶠ (λ α' → hitᵥ l (sTy O α'))) _
                          (∨-right (anyᶠ (λ j' → hitᵣ l (sR O j'))) _
                            (anyᶠ-intro (λ j' → hitₑ l (sE O j')) j (hitₑ-occ e (sE O j) r)))

  notMemʳ : ∀ {Θ} {O : Subst Θ Φ} {i} → freeᴹ l O ≡ false → freeʳ i O ≡ true → inᴿ i l ≡ false
  notMemʳ {O = O} {i} fx q with inᴿ i l in e
  ... | false = refl
  ... | true  = ⊥-elim (f≢t (trans (sym fx) hit))
    where
      f≢t : false ≡ true → ⊥
      f≢t ()

      hit : freeᴹ l O ≡ true
      hit with ∨-true (anyᶠ (λ α → occʳ-v i (sTy O α))) _ q
      ... | inj₁ qt with anyᶠ-true (λ α → occʳ-v i (sTy O α)) qt
      ...   | α , r = ∨-left (anyᶠ (λ α' → hitᵥ l (sTy O α'))) _
                        (anyᶠ-intro (λ α' → hitᵥ l (sTy O α')) α (hitᵥ-occʳ e (sTy O α) r))
      hit | inj₂ qr with anyᶠ-true (λ j → occʳ-r i (sR O j)) qr
      ...   | j , r = ∨-right (anyᶠ (λ α' → hitᵥ l (sTy O α'))) _
                        (∨-left (anyᶠ (λ j' → hitᵣ l (sR O j'))) _
                          (anyᶠ-intro (λ j' → hitᵣ l (sR O j')) j (hitᵣ-occʳ e (sR O j) r)))

------------------------------------------------------------------------
-- The steps, for the unknowns local to a scope

module Steps {Θ₀ Θ Φ} (O : Subst (Θ +e) Φ) (P : Subst Θ₀ Φ) (inc : P ⊆ᶠ O) where

  -- local unknowns are free in no image of `P`

  localᵉ : ∀ {k} → freeᵉ k O ≡ false → freeᵉ k P ≡ false
  localᵉ {k} q with freeᵉ k P in e
  ... | false = refl
  ... | true  = trans (sym (⊆ᵉ inc e)) q

  localʳ : ∀ {k} → freeʳ k O ≡ false → freeʳ k P ≡ false
  localʳ {k} q with freeʳ k P in e
  ... | false = refl
  ... | true  = trans (sym (⊆ʳ inc e)) q

  -- A substitution fixing every unknown free in an image of `P`

  record Fixes (σ : Subst Φ Φ) : Set where
    constructor mkFixes
    field
      fixᵗ : ∀ α → sTy σ α ≡ tvar α
      fixᵉ : ∀ i → freeᵉ i P ≡ true → sE σ i ≡ evar i
      fixʳ : ∀ i → freeʳ i P ≡ true → sR σ i ≡ rvar i

  open Fixes

  module _ {σ : Subst Φ Φ} (fx : Fixes σ) where

    outer-fixₑ : ∀ (y : EExp Φ) → Outerₑ P y → y [ σ ]ᵉ ≡ y
    outer-fixₑ (evar i)   o = fixᵉ fx i (o (dec-true (i ≟ᶠ i) refl))
    outer-fixₑ (econst c) o = refl
    outer-fixₑ (a ·̂ₑ b)   o = cong₂ _·̂ₑ_ (outer-fixₑ a (λ q → o (∨-left _ _ q)))
                                          (outer-fixₑ b (λ {k} q → o (∨-right (occᵉ-e k a) _ q)))
    outer-fixₑ (a ⊔̂ₑ b)   o = cong₂ _⊔̂ₑ_ (outer-fixₑ a (λ q → o (∨-left _ _ q)))
                                          (outer-fixₑ b (λ {k} q → o (∨-right (occᵉ-e k a) _ q)))

    outer-fixᵣ : ∀ (y : RExp Φ) → Outerᵣ P y → y [ σ ]ʳ ≡ y
    outer-fixᵣ (rvar i)   (oe , or) = fixʳ fx i (or (dec-true (i ≟ᶠ i) refl))
    outer-fixᵣ (rconst c) o         = refl
    outer-fixᵣ (a ·̂ᵣ b)   (oe , or) =
      cong₂ _·̂ᵣ_ (outer-fixᵣ a ((λ q → oe (∨-left _ _ q)) , (λ q → or (∨-left _ _ q))))
                 (outer-fixᵣ b ((λ {k} q → oe (∨-right (occᵉ-r k a) _ q)) ,
                                (λ {k} q → or (∨-right (occʳ-r k a) _ q))))
    outer-fixᵣ (a ⊔̂ᵣ b)   (oe , or) =
      cong₂ _⊔̂ᵣ_ (outer-fixᵣ a ((λ q → oe (∨-left _ _ q)) , (λ q → or (∨-left _ _ q))))
                 (outer-fixᵣ b ((λ {k} q → oe (∨-right (occᵉ-r k a) _ q)) ,
                                (λ {k} q → or (∨-right (occʳ-r k a) _ q))))
    outer-fixᵣ ∣ ε ∣̂ᵉ     (oe , or) = cong ∣_∣̂ᵉ (outer-fixₑ ε oe)

    fix-⊆ : (P ⨟ˢ σ) ⊆ᶠ P
    fix-⊆ = mk⊆ᶠ e r
      where
        e : ∀ {k} → freeᵉ k (P ⨟ˢ σ) ≡ true → freeᵉ k P ≡ true
        e {k} q with freeᵉ-⨟⁻ P σ q
        ... | inj₁ (α , o) with sTy σ α | fixᵗ fx α
        ...   | _ | refl = ⊥-elim (false≢true o)
          where
            false≢true : false ≡ true → ⊥
            false≢true ()
        e {k} q | inj₂ (inj₁ (i , p , o)) with sR σ i | fixʳ fx i p
        ...   | _ | refl = ⊥-elim (false≢true o)
          where
            false≢true : false ≡ true → ⊥
            false≢true ()
        e {k} q | inj₂ (inj₂ (i , p , o)) with sE σ i | fixᵉ fx i p
        ...   | _ | refl = subst (λ z → freeᵉ z P ≡ true) (sym (true-dec (k ≟ᶠ i) o)) p

        r : ∀ {k} → freeʳ k (P ⨟ˢ σ) ≡ true → freeʳ k P ≡ true
        r {k} q with freeʳ-⨟⁻ P σ q
        ... | inj₁ (α , o) with sTy σ α | fixᵗ fx α
        ...   | _ | refl = ⊥-elim (false≢true o)
          where
            false≢true : false ≡ true → ⊥
            false≢true ()
        r {k} q | inj₂ (i , p , o) with sR σ i | fixʳ fx i p
        ...   | _ | refl = subst (λ z → freeʳ z P ≡ true) (sym (true-dec (k ≟ᶠ i) o)) p

    -- the invariant kept, given what the whole greater sides become

    subst-inv : ∀ {R : Resid Φ}
              → (∀ {x i} → (x , evar i) ∈ es R → Goodₑ P (sE σ i) ⊎ JoinAltₑ (x [ σ ]ᵉ) (sE σ i))
              → (∀ {x i} → (x , rvar i) ∈ rs R → Goodᵣ P (sR σ i) ⊎ JoinAltᵣ (x [ σ ]ʳ) (sR σ i))
              → (∀ {A B} → (A , B) ∈ ss R → TyGoodᵛ P (A [ σ ]ᵛ) × TyGoodᵛ P (B [ σ ]ᵛ))
              → LInv P R → LInv P (R [ σ ]ᴿ)
    subst-inv {R} he hr hs i = mkLInv sᵢ rᵢ eᵢ dᵢ
      where
        sᵢ : ∀ {A B} → (A , B) ∈ ss (R [ σ ]ᴿ) → TyGoodᵛ P A × TyGoodᵛ P B
        sᵢ m with ∈-map⁻ (mapᵖ (_[ σ ]ᵛ)) m
        ... | (A₀ , B₀) , m₀ , refl = hs m₀

        rᵢ : ∀ {x y} → (x , y) ∈ rs (R [ σ ]ᴿ) → Goodᵣ P y ⊎ JoinAltᵣ x y
        rᵢ m with ∈-map⁻ (mapᵖ (_[ σ ]ʳ)) m
        ... | (x₀ , y₀) , m₀ , refl with l-rs i m₀
        ...   | inj₂ ja            = inj₂ (joinAltᵣ-subst σ ja)
        ...   | inj₁ (whole k)     = hr m₀
        ...   | inj₁ (outer {ρ} o) = inj₁ (outer (subst (Outerᵣ P) (sym (outer-fixᵣ ρ o)) o))

        eᵢ : ∀ {x y} → (x , y) ∈ es (R [ σ ]ᴿ) → Goodₑ P y ⊎ JoinAltₑ x y
        eᵢ m with ∈-map⁻ (mapᵖ (_[ σ ]ᵉ)) m
        ... | (x₀ , y₀) , m₀ , refl with l-es i m₀
        ...   | inj₂ ja            = inj₂ (joinAltₑ-subst σ ja)
        ...   | inj₁ (whole k)     = he m₀
        ...   | inj₁ (outer {ε} o) = inj₁ (outer (subst (Outerₑ P) (sym (outer-fixₑ ε o)) o))

        dᵢ : ∀ {E} → E ∈ dfs (R [ σ ]ᴿ) → Great P E
        dᵢ m with ∈-map⁻ (_[ σ ]ᵈ) m
        ... | E₀ , m₀ , refl = great-⊆ fix-⊆ (E₀ [ σ ]ᵈ) (great-⨟ P σ E₀ (l-dfs i m₀))

    -- the subtyping demands, where the images are good

    ss-gv : ∀ {R : Resid Φ} → GV (P ⨟ˢ σ) σ → LInv P R
          → ∀ {A B} → (A , B) ∈ ss R → TyGoodᵛ P (A [ σ ]ᵛ) × TyGoodᵛ P (B [ σ ]ᵛ)
    ss-gv g i {A} {B} m =
      tygoodᵛ-⊆ fix-⊆ (A [ σ ]ᵛ) (tygoodᵛ-⨟ {P = P} g A (proj₁ (l-ss i m))) ,
      tygoodᵛ-⊆ fix-⊆ (B [ σ ]ᵛ) (tygoodᵛ-⨟ {P = P} g B (proj₂ (l-ss i m)))

  ----------------------------------------------------------------------
  -- One unknown sent to a value

  false≢true : false ≡ true → ⊥
  false≢true ()

  nothing≢just : ∀ {X : Set} {x : X} → nothing ≡ just x → ⊥
  nothing≢just ()

  neq-false : ∀ {n} {i k : Fin n} → ¬ (i ≡ k) → ⌊ k ≟ᶠ i ⌋ ≡ false
  neq-false {i = i} {k} ¬p with k ≟ᶠ i
  ... | yes refl = ⊥-elim (¬p refl)
  ... | no _     = refl

  ValE : EVar Φ → EExp Φ → Resid Φ → Set
  ValE k b R = ∀ {x} → (x , evar k) ∈ es R → Goodₑ P b ⊎ JoinAltₑ (x [ updᵉ k b ]ᵉ) b

  ValR : RVar Φ → RExp Φ → Resid Φ → Set
  ValR k b R = ∀ {x} → (x , rvar k) ∈ rs R → Goodᵣ P b ⊎ JoinAltᵣ (x [ updʳ k b ]ʳ) b

  SSok : Subst Φ Φ → Resid Φ → Set
  SSok σ R = ∀ {A B} → (A , B) ∈ ss R → TyGoodᵛ P (A [ σ ]ᵛ) × TyGoodᵛ P (B [ σ ]ᵛ)

  module _ {k : EVar Φ} (lk : freeᵉ k O ≡ false) (b : EExp Φ) where

    fixes-updᵉ : Fixes (updᵉ k b)
    fixes-updᵉ = mkFixes (λ α → refl) fe (λ i _ → refl)
      where
        fe : ∀ i → freeᵉ i P ≡ true → sE (updᵉ k b) i ≡ evar i
        fe i p with k ≟ᶠ i
        ... | yes refl = ⊥-elim (false≢true (trans (sym (localᵉ lk)) p))
        ... | no ¬q    = updᵉ-miss k b i (neq-false (λ e → ¬q (sym e)))

    updᵉ-inv : ∀ {R} → ValE k b R → SSok (updᵉ k b) R → LInv P R → LInv P (R [ updᵉ k b ]ᴿ)
    updᵉ-inv {R} v hs i = subst-inv fixes-updᵉ hitE (λ m → inj₁ (whole _)) hs i
      where
        hitE : ∀ {x j} → (x , evar j) ∈ es R → Goodₑ P (sE (updᵉ k b) j) ⊎ JoinAltₑ (x [ updᵉ k b ]ᵉ) (sE (updᵉ k b) j)
        hitE {x} {j} m with j ≟ᶠ k
        ... | yes refl = v m
        ... | no ¬p    = inj₁ (whole j)

    ss-cleanᵉ : ∀ {R} → Cleanᵉ k R → LInv P R → SSok (updᵉ k b) R
    ss-cleanᵉ cl i {A} {B} m with ∨-false (occᵉ-v k A) (occᵉ-v k B) (Cleanᵉ.css cl m)
    ... | qA , qB = subst (TyGoodᵛ P) (sym (updᵉ-v k b A qA)) (proj₁ (l-ss i m)) ,
                    subst (TyGoodᵛ P) (sym (updᵉ-v k b B qB)) (proj₂ (l-ss i m))

  module _ {k : RVar Φ} (lk : freeʳ k O ≡ false) (b : RExp Φ) where

    fixes-updʳ : Fixes (updʳ k b)
    fixes-updʳ = mkFixes (λ α → refl) (λ i _ → refl) fr
      where
        fr : ∀ i → freeʳ i P ≡ true → sR (updʳ k b) i ≡ rvar i
        fr i p with k ≟ᶠ i
        ... | yes refl = ⊥-elim (false≢true (trans (sym (localʳ lk)) p))
        ... | no ¬q    = updʳ-miss k b i (neq-false (λ e → ¬q (sym e)))

    updʳ-inv : ∀ {R} → ValR k b R → SSok (updʳ k b) R → LInv P R → LInv P (R [ updʳ k b ]ᴿ)
    updʳ-inv {R} v hs i = subst-inv fixes-updʳ (λ m → inj₁ (whole _)) hitR hs i
      where
        hitR : ∀ {x j} → (x , rvar j) ∈ rs R → Goodᵣ P (sR (updʳ k b) j) ⊎ JoinAltᵣ (x [ updʳ k b ]ʳ) (sR (updʳ k b) j)
        hitR {x} {j} m with j ≟ᶠ k
        ... | yes refl = v m
        ... | no ¬p    = inj₁ (whole j)

    ss-cleanʳ : ∀ {R} → Cleanʳ k R → LInv P R → SSok (updʳ k b) R
    ss-cleanʳ cl i {A} {B} m with ∨-false (occʳ-v k A) (occʳ-v k B) (Cleanʳ.css cl m)
    ... | qA , qB = subst (TyGoodᵛ P) (sym (updʳ-v k b A qA)) (proj₁ (l-ss i m)) ,
                    subst (TyGoodᵛ P) (sym (updʳ-v k b B qB)) (proj₂ (l-ss i m))

  ----------------------------------------------------------------------
  -- The four rules for an effect unknown: the value is good at every
  -- whole greater side it replaces, or a join of that ordering's
  -- smaller side and others

  module _ {k : EVar Φ} {R : Resid Φ} (cl : Cleanᵉ k R) where

    lowerᵉ-val : ∀ ml mf {b} {st : Keeps (updᵉ k b) R} → lowerᵉ? k R cl ml mf ≡ just (b , st) → ValE k b R
    lowerᵉ-val (just (Bᵉ.lows (x ∷ xs) c s f)) (just fr) e
      with stills? dir↓ (updᵉ k (joinₑ x xs)) (dfs R)
    ... | nothing = ⊥-elim (nothing≢just e)
    ... | just sd with e
    ...   | refl = v
      where
        v : ValE k (joinₑ x xs) R
        v {x'} m with c m
        ... | inj₁ (inj₁ refl) = inj₂ (joinₑ x xs , [] , refl , here (updᵉ-hit k (joinₑ x xs)))
        ... | inj₁ (inj₂ q)    = ⊥-elim (false≢true (trans (sym q) (dec-true (k ≟ᶠ k) refl)))
        ... | inj₂ (_ , mx)    =
              inj₂ (x , xs , refl , subst (_∈ x ∷ xs) (sym (updᵉ-e k (joinₑ x xs) x' (f mx))) mx)
    lowerᵉ-val (just (Bᵉ.lows [] c s f))       _         ()
    lowerᵉ-val (just (Bᵉ.lows (x ∷ xs) c s f)) nothing   ()
    lowerᵉ-val nothing                         _         ()

    raise-valᵉ : LInv P R → (up : Bᵉ.Ups k (es R)) → ValE k (Bᵉ.cap up) R
    raise-valᵉ i up m with l-es i (Bᵉ.srcᵘ up)
    ... | inj₁ g = inj₁ g
    ... | inj₂ (x₀ , xs , e , w) =
          ⊥-elim (false≢true (trans (sym (Bᵉ.cfree up))
                   (subst (λ z → occᵉ-e k z ≡ true) (sym e) (joinₑ-occ x₀ xs w (dec-true (k ≟ᶠ k) refl)))))

    raiseᵉ-val : LInv P R → ∀ mu mfl mdf {b} {st : Keeps (updᵉ k b) R} → raiseᵉ? k R cl mu mfl mdf ≡ just (b , st) → ValE k b R
    raiseᵉ-val i (just up) (just fl) (just df) e with stills? dir↑ (updᵉ k (Bᵉ.cap up)) (dfs R)
    ... | nothing = ⊥-elim (nothing≢just e)
    ... | just sd with e
    ...   | refl = raise-valᵉ i up
    raiseᵉ-val i nothing   _         _         ()
    raiseᵉ-val i (just _)  nothing   _         ()
    raiseᵉ-val i (just _)  (just _)  nothing   ()

    unitᵉ-val : ∀ mi ml mf o {b} {st : Keeps (updᵉ k b) R} → unitᵉ? k R cl mi ml mf o ≡ just (b , st) → ValE k b R
    unitᵉ-val (just ij) (just (Bᵉ.lows [] c s f)) (just fr) true e with stills? dir↓ (updᵉ k ûₑ) (dfs R)
    ... | nothing = ⊥-elim (nothing≢just e)
    ... | just sd with e
    ...   | refl = λ m → inj₁ (outer (λ ()))
    unitᵉ-val nothing  _                               _        _     ()
    unitᵉ-val (just _) nothing                         _        _     ()
    unitᵉ-val (just _) (just (Bᵉ.lows (_ ∷ _) _ _ _))  _        _     ()
    unitᵉ-val (just _) (just (Bᵉ.lows [] _ _ _))      nothing  _     ()
    unitᵉ-val (just _) (just (Bᵉ.lows [] _ _ _))      (just _) false ()

    topᵉ-val : ∀ mfe mfl mdf o {b} {st : Keeps (updᵉ k b) R} → topᵉ? k R cl mfe mfl mdf o ≡ just (b , st) → ValE k b R
    topᵉ-val (just fe) (just fl) (just df) true e with stills? dir↑ (updᵉ k (econst ⊤ₑ)) (dfs R)
    ... | nothing = ⊥-elim (nothing≢just e)
    ... | just sd with e
    ...   | refl = λ m → inj₁ (outer (λ ()))
    topᵉ-val nothing  _        _        _     ()
    topᵉ-val (just _) nothing  _        _     ()
    topᵉ-val (just _) (just _) nothing  _     ()
    topᵉ-val (just _) (just _) (just _) false ()

  stepᵉ-inv : ∀ {k} → freeᵉ k O ≡ false → ∀ {R b} {st : Keeps (updᵉ k b) R} → LInv P R → stepᵉ k R ≡ just (b , st)
            → LInv P (R [ updᵉ k b ]ᴿ)
  stepᵉ-inv {k} lk {R} {b} i e with cleanᵉ? k R
  ... | nothing = ⊥-elim (nothing≢just e)
  ... | just cl = updᵉ-inv lk b val (ss-cleanᵉ lk b cl i) i
    where
      Lo = lowerᵉ? k R cl (Bᵉ.lowsOf {Φ} k (es R)) (Bᵉʳ.freeRs {Φ} k (rs R))
      Ra = raiseᵉ? k R cl (Bᵉ.upsOf {Φ} k (es R)) (Bᵉʳ.freeLs {Φ} k (rs R)) (dfreeᵉ? k R)
      Un = unitᵉ? k R cl (Is-just? uₑ-least?) (Bᵉ.lowsOf {Φ} k (es R))
                  (Bᵉʳ.freeRs {Φ} k (rs R)) (occursᵉ k R)
      To = topᵉ? k R cl (Bᵉ.freeLs {Φ} k (es R)) (Bᵉʳ.freeLs {Φ} k (rs R)) (dfreeᵉ? k R)
                 (occursᵉ⁺ k R)

      val : ValE k b R
      val with first-inv Lo (first Ra (first Un To)) e
      ... | inj₁ e₁ = lowerᵉ-val cl (Bᵉ.lowsOf {Φ} k (es R)) (Bᵉʳ.freeRs {Φ} k (rs R)) e₁
      ... | inj₂ e₂ with first-inv Ra (first Un To) e₂
      ...   | inj₁ e₃ = raiseᵉ-val cl i (Bᵉ.upsOf {Φ} k (es R)) (Bᵉʳ.freeLs {Φ} k (rs R)) (dfreeᵉ? k R) e₃
      ...   | inj₂ e₄ with first-inv Un To e₄
      ...     | inj₁ e₅ = unitᵉ-val cl (Is-just? uₑ-least?) (Bᵉ.lowsOf {Φ} k (es R)) (Bᵉʳ.freeRs {Φ} k (rs R)) (occursᵉ k R) e₅
      ...     | inj₂ e₆ = topᵉ-val cl (Bᵉ.freeLs {Φ} k (es R)) (Bᵉʳ.freeLs {Φ} k (rs R)) (dfreeᵉ? k R) (occursᵉ⁺ k R) e₆

  ----------------------------------------------------------------------
  -- ... and for a resource unknown

  module _ {k : RVar Φ} {R : Resid Φ} (cl : Cleanʳ k R) where

    lowerʳ-val : ∀ ml {b} {st : Keeps (updʳ k b) R} → lowerʳ? k R cl ml ≡ just (b , st) → ValR k b R
    lowerʳ-val (just (Bʳ.lows (x ∷ xs) c s f)) e
      with stills? dir↓ (updʳ k (joinᵣ x xs)) (dfs R)
    ... | nothing = ⊥-elim (nothing≢just e)
    ... | just sd with e
    ...   | refl = v
      where
        v : ValR k (joinᵣ x xs) R
        v {x'} m with c m
        ... | inj₁ (inj₁ refl) = inj₂ (joinᵣ x xs , [] , refl , here (updʳ-hit k (joinᵣ x xs)))
        ... | inj₁ (inj₂ q)    = ⊥-elim (false≢true (trans (sym q) (dec-true (k ≟ᶠ k) refl)))
        ... | inj₂ (_ , mx)    =
              inj₂ (x , xs , refl , subst (_∈ x ∷ xs) (sym (updʳ-r k (joinᵣ x xs) x' (f mx))) mx)
    lowerʳ-val (just (Bʳ.lows [] c s f)) ()
    lowerʳ-val nothing                   ()

    raise-valʳ : LInv P R → (up : Bʳ.Ups k (rs R)) → ValR k (Bʳ.cap up) R
    raise-valʳ i up m with l-rs i (Bʳ.srcᵘ up)
    ... | inj₁ g = inj₁ g
    ... | inj₂ (x₀ , xs , e , w) =
          ⊥-elim (false≢true (trans (sym (Bʳ.cfree up))
                   (subst (λ z → occʳ-r k z ≡ true) (sym e) (joinᵣ-occ x₀ xs w (dec-true (k ≟ᶠ k) refl)))))

    raiseʳ-val : LInv P R → ∀ mu mdf {b} {st : Keeps (updʳ k b) R} → raiseʳ? k R cl mu mdf ≡ just (b , st) → ValR k b R
    raiseʳ-val i (just up) (just df) e with stills? dir↑ (updʳ k (Bʳ.cap up)) (dfs R)
    ... | nothing = ⊥-elim (nothing≢just e)
    ... | just sd with e
    ...   | refl = raise-valʳ i up
    raiseʳ-val i nothing   _       ()
    raiseʳ-val i (just _)  nothing ()

    unitʳ-val : ∀ mi ml o {b} {st : Keeps (updʳ k b) R} → unitʳ? k R cl mi ml o ≡ just (b , st) → ValR k b R
    unitʳ-val (just ij) (just (Bʳ.lows [] c s f)) true e with stills? dir↓ (updʳ k ûᵣ) (dfs R)
    ... | nothing = ⊥-elim (nothing≢just e)
    ... | just sd with e
    ...   | refl = λ m → inj₁ (outer ((λ ()) , (λ ())))
    unitʳ-val nothing  _                              _     ()
    unitʳ-val (just _) nothing                        _     ()
    unitʳ-val (just _) (just (Bʳ.lows (_ ∷ _) _ _ _)) _     ()
    unitʳ-val (just _) (just (Bʳ.lows [] _ _ _))      false ()

    topʳ-val : ∀ mfl mdf o {b} {st : Keeps (updʳ k b) R} → topʳ? k R cl mfl mdf o ≡ just (b , st) → ValR k b R
    topʳ-val (just fl) (just df) true e with stills? dir↑ (updʳ k (rconst ⊤ᵣ)) (dfs R)
    ... | nothing = ⊥-elim (nothing≢just e)
    ... | just sd with e
    ...   | refl = λ m → inj₁ (outer ((λ ()) , (λ ())))
    topʳ-val nothing  _        _     ()
    topʳ-val (just _) nothing  _     ()
    topʳ-val (just _) (just _) false ()

  stepʳ-inv : ∀ {k} → freeʳ k O ≡ false → ∀ {R b} {st : Keeps (updʳ k b) R} → LInv P R → stepʳ k R ≡ just (b , st)
            → LInv P (R [ updʳ k b ]ᴿ)
  stepʳ-inv {k} lk {R} {b} i e with cleanʳ? k R
  ... | nothing = ⊥-elim (nothing≢just e)
  ... | just cl = updʳ-inv lk b val (ss-cleanʳ lk b cl i) i
    where
      Lo = lowerʳ? k R cl (Bʳ.lowsOf {Φ} k (rs R))
      Ra = raiseʳ? k R cl (Bʳ.upsOf {Φ} k (rs R)) (dfreeʳ? k R)
      Un = unitʳ? k R cl (Is-just? uᵣ-least?) (Bʳ.lowsOf {Φ} k (rs R)) (occursʳ k R)
      To = topʳ? k R cl (Bʳ.freeLs {Φ} k (rs R)) (dfreeʳ? k R) (occursʳ⁺ k R)

      val : ValR k b R
      val with first-inv Lo (first Ra (first Un To)) e
      ... | inj₁ e₁ = lowerʳ-val cl (Bʳ.lowsOf {Φ} k (rs R)) e₁
      ... | inj₂ e₂ with first-inv Ra (first Un To) e₂
      ...   | inj₁ e₃ = raiseʳ-val cl i (Bʳ.upsOf {Φ} k (rs R)) (dfreeʳ? k R) e₃
      ...   | inj₂ e₄ with first-inv Un To e₄
      ...     | inj₁ e₅ = unitʳ-val cl (Is-just? uᵣ-least?) (Bʳ.lowsOf {Φ} k (rs R)) (occursʳ k R) e₅
      ...     | inj₂ e₆ = topʳ-val cl (Bʳ.freeLs {Φ} k (rs R)) (dfreeʳ? k R) (occursʳ⁺ k R) e₆

  ----------------------------------------------------------------------
  -- Identifying two unknowns, and sending a set to the top: every image
  -- is a whole unknown or a constant

  gv-updᵉ : ∀ k r → GV (P ⨟ˢ updᵉ k (evar r)) (updᵉ k (evar r))
  gv-updᵉ k r = mkGV (λ α → tt) (λ j → whole j) e
    where
      e : ∀ j → Goodₑ (P ⨟ˢ updᵉ k (evar r)) (sE (updᵉ k (evar r)) j)
      e j with j ≟ᶠ k
      ... | yes _ = whole r
      ... | no _  = whole j

  gv-updʳ : ∀ k r → GV (P ⨟ˢ updʳ k (rvar r)) (updʳ k (rvar r))
  gv-updʳ k r = mkGV (λ α → tt) rr (λ j → whole j)
    where
      rr : ∀ j → Goodᵣ (P ⨟ˢ updʳ k (rvar r)) (sR (updʳ k (rvar r)) j)
      rr j with j ≟ᶠ k
      ... | yes _ = whole r
      ... | no _  = whole j

  collapseᵉ-inv : ∀ {k} r → freeᵉ k O ≡ false → ∀ {R} → LInv P R → LInv P (R [ updᵉ k (evar r) ]ᴿ)
  collapseᵉ-inv {k} r lk i =
    updᵉ-inv lk (evar r) (λ m → inj₁ (whole r)) (ss-gv (fixes-updᵉ lk (evar r)) (gv-updᵉ k r) i) i

  collapseʳ-inv : ∀ {k} r → freeʳ k O ≡ false → ∀ {R} → LInv P R → LInv P (R [ updʳ k (rvar r) ]ᴿ)
  collapseʳ-inv {k} r lk i =
    updʳ-inv lk (rvar r) (λ m → inj₁ (whole r)) (ss-gv (fixes-updʳ lk (rvar r)) (gv-updʳ k r) i) i

  module _ (l : List (Mem Φ)) (fx : freeᴹ l O ≡ false) where

    fixes-tops : Fixes (tops l)
    fixes-tops = mkFixes (λ α → refl) fe fr
      where
        fe : ∀ i → freeᵉ i P ≡ true → sE (tops l) i ≡ evar i
        fe i p = cong (λ b → topE b i) (notMemᵉ l {O = O} fx (⊆ᵉ inc p))

        fr : ∀ i → freeʳ i P ≡ true → sR (tops l) i ≡ rvar i
        fr i p = cong (λ b → topR b i) (notMemʳ l {O = O} fx (⊆ʳ inc p))

    gv-tops : GV (P ⨟ˢ tops l) (tops l)
    gv-tops = mkGV (λ α → tt) rr e
      where
        e : ∀ j → Goodₑ (P ⨟ˢ tops l) (sE (tops l) j)
        e j with inᴱ j l
        ... | true  = outer (λ ())
        ... | false = whole j

        rr : ∀ j → Goodᵣ (P ⨟ˢ tops l) (sR (tops l) j)
        rr j with inᴿ j l
        ... | true  = outer ((λ ()) , (λ ()))
        ... | false = whole j

    tops-inv : ∀ {R} → LInv P R → LInv P (R [ tops l ]ᴿ)
    tops-inv {R} i = subst-inv fixes-tops hitE hitR (ss-gv fixes-tops gv-tops i) i
      where
        hitE : ∀ {x j} → (x , evar j) ∈ es R → Goodₑ P (sE (tops l) j) ⊎ JoinAltₑ (x [ tops l ]ᵉ) (sE (tops l) j)
        hitE {j = j} m with inᴱ j l
        ... | true  = inj₁ (outer (λ ()))
        ... | false = inj₁ (whole j)

        hitR : ∀ {x j} → (x , rvar j) ∈ rs R → Goodᵣ P (sR (tops l) j) ⊎ JoinAltᵣ (x [ tops l ]ʳ) (sR (tops l) j)
        hitR {j = j} m with inᴿ j l
        ... | true  = inj₁ (outer ((λ ()) , (λ ())))
        ... | false = inj₁ (whole j)

  ----------------------------------------------------------------------
  -- The stages of `localise`

  module _ {R₀ : Resid Φ} where

    passᵉ-inv : ∀ ks (L : Localised O R₀) → LInv P (lR L) → LInv P (lR (proj₁ (passᵉ O R₀ ks L)))
    passᵉ-inv []             L i = i
    passᵉ-inv ((k , q) ∷ ks) L i with stepᵉ k (lR L) in e
    ... | nothing      = passᵉ-inv ks L i
    ... | just (b , st) = passᵉ-inv ks _ (stepᵉ-inv q i e)

    passʳ-inv : ∀ ks (L : Localised O R₀) → LInv P (lR L) → LInv P (lR (proj₁ (passʳ O R₀ ks L)))
    passʳ-inv []             L i = i
    passʳ-inv ((k , q) ∷ ks) L i with stepʳ k (lR L) in e
    ... | nothing      = passʳ-inv ks L i
    ... | just (b , st) = passʳ-inv ks _ (stepʳ-inv q i e)

    collapseᵉL-inv : ∀ n (L : Localised O R₀) → LInv P (lR L) → LInv P (lR (proj₁ (collapseᵉL O R₀ n L)))
    collapseᵉL-inv nzero    L i = i
    collapseᵉL-inv (nsuc n) L i with collapseᵉ? O (lR L)
    ... | nothing                = i
    ... | just (k , r , q , st , _) = collapseᵉL-inv n _ (collapseᵉ-inv r q i)

    collapseʳL-inv : ∀ n (L : Localised O R₀) → LInv P (lR L) → LInv P (lR (proj₁ (collapseʳL O R₀ n L)))
    collapseʳL-inv nzero    L i = i
    collapseʳL-inv (nsuc n) L i with collapseʳ? O (lR L)
    ... | nothing                = i
    ... | just (k , r , q , st , _) = collapseʳL-inv n _ (collapseʳ-inv r q i)

    raiseL-inv : ∀ (L : Localised O R₀) {L'} → raiseL O R₀ L ≡ just L' → LInv P (lR L) → LInv P (lR L')
    raiseL-inv L e i with evar? (sE O (newᵉ {Θ}))
    ... | nothing = ⊥-elim (nothing≢just e)
    ... | just (j , eqj) with Find.raise? O (lR L) j
    ...   | nothing = ⊥-elim (nothing≢just e)
    ...   | just (raised l rc ue ur cl sd fx _) with e
    ...     | refl = tops-inv l fx i

    -- normal forms keep the invariant

    normal-inv : ∀ (L : Localised O R₀) → ResInv P (lR L) → ResInv P (lR (loc-normal L))
    normal-inv L r = mkResInv (inv-ss r) rᵢ eᵢ (I5 r)
      where
        rᵢ : ∀ {x y} → (x , y) ∈ rs (lR (loc-normal L)) → Goodᵣ P y
        rᵢ m with split-src piecesʳ (rs (lR L)) m
        ... | (x₀ , y₀) , ma , mb =
              subst (Goodᵣ P) (sym (partsʳ-rhs _ (canonᵣ y₀) mb)) (canon-goodᵣ (I1′ʳ r ma))

        eᵢ : ∀ {x y} → (x , y) ∈ es (lR (loc-normal L)) → Goodₑ P y
        eᵢ m with split-src piecesᵉ (es (lR L)) m
        ... | (x₀ , y₀) , ma , mb =
              subst (Goodₑ P) (sym (partsₑ-rhs _ (canonₑ y₀) mb)) (canon-goodₑ (I1′ᵉ r ma))

    -- settling drops the joins

    settle-inv : ∀ (L : Localised O R₀) → LInv P (lR L) → ResInv P (lR (loc-settle L))
    settle-inv L i = mkResInv (l-ss i) rᵢ eᵢ (l-dfs i)
      where
        R₁ = lR L
        Uʳ = unsettled settledʳ (rs R₁)
        Uᵉ = unsettled settledᵉ (es R₁)
        F  = refine (Unsettled.kept (unsettled settledᵈ (ds R₁)))

        rᵢ : ∀ {x y} → (x , y) ∈ rs (lR (loc-settle L)) → Goodᵣ P y
        rᵢ m with ∈-++⁻ (Unsettled.kept Uʳ) m
        ... | inj₂ mo = subst (Goodᵣ P) (sym (Refined.ordsᵘ F mo)) (outer ((λ ()) , (λ ())))
        ... | inj₁ mk with l-rs i (Unsettled.kept⊆ Uʳ mk)
        ...   | inj₁ g  = g
        ...   | inj₂ ja = ⊥-elim (kept-unset settledʳ (rs R₁) mk (settledᵣ-join ja))

        eᵢ : ∀ {x y} → (x , y) ∈ es (lR (loc-settle L)) → Goodₑ P y
        eᵢ m with l-es i (Unsettled.kept⊆ Uᵉ m)
        ... | inj₁ g  = g
        ... | inj₂ ja = ⊥-elim (kept-unset settledᵉ (es R₁) m (settledₑ-join ja))

    resettle-inv : ∀ b (L : Localised O R₀) → ResInv P (lR L) → ResInv P (lR (resettle O R₀ b L))
    resettle-inv true  L r = settle-inv L (linv r)
    resettle-inv false L r = r

    -- the rounds, each stage given the rounds that follow it

    More : (Localised O R₀ → Localised O R₀) → Set
    More more = ∀ L → ResInv P (lR L) → LInv P (lR (more L))

    next₂-inv : ∀ more → More more → ∀ L b → LInv P (lR L) → LInv P (lR (next₂ O R₀ more (L , b)))
    next₂-inv more K L true  i = K _ (settle-inv L i)
    next₂-inv more K L false i with raiseL O R₀ L in e
    ... | just L'' = K _ (settle-inv L'' (raiseL-inv L e i))
    ... | nothing  = i

    next-inv : ∀ more → More more → ∀ L b → LInv P (lR L) → LInv P (lR (next O R₀ more (L , b)))
    next-inv more K L b i
      with passʳ O R₀ (misses (λ k → freeʳ k O)) L | passʳ-inv (misses (λ k → freeʳ k O)) L i
    ... | L'' , b' | i' = next₂-inv more K L'' (b ∨ b') i'

    values-inv : ∀ more → More more → ∀ L b → LInv P (lR L) → LInv P (lR (values O R₀ more (L , b)))
    values-inv more K L b i
      with passᵉ O R₀ (misses (λ k → freeᵉ k O)) L | passᵉ-inv (misses (λ k → freeᵉ k O)) L i
    ... | L'' , b' | i' = next-inv more K L'' (b ∨ b') i'

    cycles-inv : ∀ more → More more → ∀ L b → LInv P (lR L) → LInv P (lR (cycles O R₀ more (L , b)))
    cycles-inv more K L b i
      with collapseʳL O R₀ (nR Φ) L | collapseʳL-inv (nR Φ) L i
    ... | L'' , b' | i' = values-inv more K L'' (b ∨ b') i'

    rounds-inv : ∀ n → More (rounds O R₀ n)
    rounds-inv nzero    L r = linv r
    rounds-inv (nsuc n) L r
      with collapseᵉL O R₀ (nE Φ) (resettle O R₀ (joined (lR L)) (loc-normal L))
         | collapseᵉL-inv (nE Φ) (resettle O R₀ (joined (lR L)) (loc-normal L))
             (linv (resettle-inv (joined (lR L)) (loc-normal L) (normal-inv L r)))
    ... | L' , b | i' = cycles-inv (rounds O R₀ n) (rounds-inv n) L' b i'

------------------------------------------------------------------------
-- `localise` keeps I1′ and I5 for the unknowns the scope was entered
-- with

localise-good : ∀ {Θ₀ Θ Φ} → (O : Subst (Θ +e) Φ) → (P : Subst Θ₀ Φ) → (R : Resid Φ)
              → P ⊆ᶠ O → ResInv P R → ResInv P (lR (localise O R))
localise-good {Φ = Φ} O P R inc r =
  settle-inv {R₀ = R} (rounds O R (nE Φ + nR Φ) (loc-settle loc-id))
    (rounds-inv {R₀ = R} (nE Φ + nR Φ) (loc-settle loc-id) (settle-inv {R₀ = R} loc-id (linv r)))
  where
    open Steps O P inc
