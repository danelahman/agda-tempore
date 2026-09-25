------------------------------------------------------------------
-- Principal values for the unknowns local to a rigid scope     --
--                                                              --
-- An unknown is local to a scope when it is free in the image  --
-- of none of the unknowns the scope was entered with; the      --
-- rigid is one of those, so it is never local and never        --
-- assigned.                                                    --
--                                                              --
-- Each round first rewrites the atoms into equivalent ones:    --
--   * an ordering whose left side has two or more alternatives --
--     in normal form becomes one ordering per alternative, the --
--     join being the least upper bound; a right side is never  --
--     split (`loc-joins`);                                     --
--   * local unknowns that bound each other along orderings     --
--     whose sides are whole unknowns are identified: each is   --
--     sent to another member, an outer unknown where the cycle --
--     has one, else the least local. The members are equal at  --
--     every instance, grades being antisymmetric, so the       --
--     instance is kept (`collapseᵉ-⊩`); a member sent occurs   --
--     in no type.                                              --
--                                                              --
-- Then, before the atoms of the scope are split, each local    --
-- unknown with a principal value is sent to it:                --
--   * the join of its lower bounds, where it occurs on a right --
--     side only as the whole side (Pottier's condition);       --
--   * dually, its one upper bound, where it occurs on a left   --
--     side only as the whole side;                             --
--   * the unit, where it has no bound below and the unit is    --
--     least, the unit being then the join of no bounds;        --
--   * the top, where it occurs on no left side.                --
-- In every case it occurs in no type of the residual. The      --
-- grade of a disjunction is the left side of an ordering below --
-- the unit: the first and third steps keep it, the others ask  --
-- it to be free of the unknown. A value may mention the        --
-- rigid, so the value over the rigid is one expression,        --
-- uniform in it.                                               --
--                                                              --
-- Where no local unknown has such a value, a set of them is    --
-- sent to the top at once. Each member is reached from the     --
-- rigid: it is bounded below by an expression decided to be    --
-- the top once the rigid and the members reached before it     --
-- are. Each ordering with a member on its left has on its      --
-- right an expression decided to be the top once the members   --
-- are, or one that mentions only outer unknowns other than the --
-- rigid. No member occurs in a type or in a disjunction's      --
-- grade.                                                       --
--                                                              --
-- In the deferred conditions of inner scopes, an unknown may   --
-- be lowered where it is on no greater side, and raised where  --
-- it is on no smaller side: a lower smaller side or a higher   --
-- greater side keeps a condition. It occurs where it is in one.--
--                                                              --
-- Before the first round, between rounds and after the last,   --
-- the settled atoms are dropped: an ordering decided true      --
-- against no hypotheses, and a var-rule disjunction with a     --
-- side so decided (the type eternal, or the grade below the    --
-- unit). They hold at every instance and bound nothing. A      --
-- disjunction whose type is eternal at no instance becomes its --
-- grade side, which is what it means at every instance solving --
-- the scope from no hypotheses, the rigid a parameter.         --
--                                                              --
-- Every grade former is monotone, so each value keeps every    --
-- instance that satisfied the residual (`lowerᵉ-⊩` and its     --
-- five siblings). Raising a set keeps every instance entering  --
-- the scope, one that takes the rigid to a fresh eigenvariable --
-- (`raise-⊩`): with the eigenvariable at the top as well, the  --
-- instance stays one and every member is at the top, and the   --
-- raised instance lies between the two.                        --
--                                                              --
-- Each step assigns grade unknowns only, so subtyping demands  --
-- between type variables stay so (`latom`).                    --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; _∧_; not; true; false) renaming (Bool to 𝔹)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe using (Is-just)
open import Data.Nat.Base using (ℕ; _+_) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Localise
  (S : LanguageSpec)
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.SolverImpl.Core.Occurs S
  using (occᵉ-e; occᵉ-r; occᵉ-v; occᵉ-c; occʳ-r; occʳ-v; occʳ-c)
open import TypeInference.SolverImpl.Core.Rigid S
  using (∨-true; ∨-left; ∨-right; dec-true; true-dec)

open import TypeInference.SolverImpl.Deferred  S
  using (Dfr; dfr; _⊩ᵈ_[_]; mk⊩ᵒ; ⊩ors; ⊩oes; ≾ˢ-↑ᵉⁿ; Dir; dir↓; dir↑; Still; stills?;
         keepᵈ; allOf; κ⟨_⟩; wk-κ; κ-wkᵛ; κ-wkʳ; κ-wkᵉ; ⊩ᴴ-κ)
open import TypeInference.SolverImpl.Resid     S
open import TypeInference.SolverImpl.Eliminate S
  using (joinₑ; joinᵣ; joinₑ-ub⊩; joinₑ-lub⊩; joinᵣ-ub⊩; joinᵣ-lub⊩)
open import TypeInference.SolverImpl.Normal    S using (decide≾ᵣ; decide≾ₑ)
open import TypeInference.SolverImpl.Product   S
  using (Alts; alt; _∷⁺_; RAtom; EAtom; ⟦_⟧ʳᵖ; ⟦_⟧ʳᵖ⁺; ⟦_⟧ᵉᵖ; ⟦_⟧ᵉᵖ⁺;
         nrmᵣ; nrmₑ; nrmᵣ-≡ᵖ; nrmₑ-≡ᵖ)

------------------------------------------------------------------------
-- Booleans and finite enumerations

∨-false : (b b' : 𝔹) → b ∨ b' ≡ false → (b ≡ false) × (b' ≡ false)
∨-false false b' q = refl , q
∨-false true  b' ()

isFalse : (b : 𝔹) → Maybe (b ≡ false)
isFalse false = just refl
isFalse true  = nothing

anyᶠ : ∀ {n} → (Fin n → 𝔹) → 𝔹
anyᶠ {nzero}  f = false
anyᶠ {nsuc n} f = f zero ∨ anyᶠ (λ i → f (suc i))

anyᶠ-false : ∀ {n} → (f : Fin n → 𝔹) → anyᶠ f ≡ false → (i : Fin n) → f i ≡ false
anyᶠ-false {nsuc n} f q zero    = proj₁ (∨-false (f zero) _ q)
anyᶠ-false {nsuc n} f q (suc i) =
  anyᶠ-false (λ i' → f (suc i')) (proj₂ (∨-false (f zero) _ q)) i

anyᶠ-true : ∀ {n} → (f : Fin n → 𝔹) → anyᶠ f ≡ true → Σ[ i ∈ Fin n ] (f i ≡ true)
anyᶠ-true {nsuc n} f q with f zero in r
... | true  = zero , r
... | false with anyᶠ-true (λ i → f (suc i)) q
...   | i , r' = suc i , r'

-- The elements of `Fin n` at which a test fails, with the failure

misses : ∀ {n} → (f : Fin n → 𝔹) → List (Σ[ i ∈ Fin n ] (f i ≡ false))
misses {nzero}  f = []
misses {nsuc n} f = head (isFalse (f zero)) (shift (misses (λ i → f (suc i))))
  where
    head : Maybe (f zero ≡ false) → List (Σ[ i ∈ Fin (nsuc n) ] (f i ≡ false))
         → List (Σ[ i ∈ Fin (nsuc n) ] (f i ≡ false))
    head (just q) l = (zero , q) ∷ l
    head nothing  l = l

    shift : List (Σ[ i ∈ Fin n ] (f (suc i) ≡ false))
          → List (Σ[ i ∈ Fin (nsuc n) ] (f i ≡ false))
    shift []             = []
    shift ((i , q) ∷ l) = (suc i , q) ∷ shift l

anyL : ∀ {X : Set} → (X → 𝔹) → List X → 𝔹
anyL f []      = false
anyL f (x ∷ l) = f x ∨ anyL f l

------------------------------------------------------------------------
-- An assignment leaves alone what the assigned unknown does not occur in

updᵉ-e : ∀ {Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → (ε : EExp Ψ)
       → occᵉ-e k ε ≡ false → ε [ updᵉ k b ]ᵉ ≡ ε
updᵉ-e k b (evar i)   q = updᵉ-miss k b i q
updᵉ-e k b (econst c) q = refl
updᵉ-e k b (ε ·̂ₑ ε')  q with ∨-false (occᵉ-e k ε) (occᵉ-e k ε') q
... | q₁ , q₂ = cong₂ _·̂ₑ_ (updᵉ-e k b ε q₁) (updᵉ-e k b ε' q₂)
updᵉ-e k b (ε ⊔̂ₑ ε')  q with ∨-false (occᵉ-e k ε) (occᵉ-e k ε') q
... | q₁ , q₂ = cong₂ _⊔̂ₑ_ (updᵉ-e k b ε q₁) (updᵉ-e k b ε' q₂)

updᵉ-r : ∀ {Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → (ρ : RExp Ψ)
       → occᵉ-r k ρ ≡ false → ρ [ updᵉ k b ]ʳ ≡ ρ
updᵉ-r k b (rvar i)   q = refl
updᵉ-r k b (rconst c) q = refl
updᵉ-r k b (ρ ·̂ᵣ ρ')  q with ∨-false (occᵉ-r k ρ) (occᵉ-r k ρ') q
... | q₁ , q₂ = cong₂ _·̂ᵣ_ (updᵉ-r k b ρ q₁) (updᵉ-r k b ρ' q₂)
updᵉ-r k b (ρ ⊔̂ᵣ ρ')  q with ∨-false (occᵉ-r k ρ) (occᵉ-r k ρ') q
... | q₁ , q₂ = cong₂ _⊔̂ᵣ_ (updᵉ-r k b ρ q₁) (updᵉ-r k b ρ' q₂)
updᵉ-r k b ∣ ε ∣̂ᵉ     q = cong ∣_∣̂ᵉ (updᵉ-e k b ε q)

mutual

  updᵉ-v : ∀ {Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → (A : OVType Ψ)
         → occᵉ-v k A ≡ false → A [ updᵉ k b ]ᵛ ≡ A
  updᵉ-v k b (tvar α)  q = refl
  updᵉ-v k b (Base c)  q = refl
  updᵉ-v k b Unit      q = refl
  updᵉ-v k b Bool      q = refl
  updᵉ-v k b Empty     q = refl
  updᵉ-v k b (A |×| B) q with ∨-false (occᵉ-v k A) (occᵉ-v k B) q
  ... | q₁ , q₂ = cong₂ _|×|_ (updᵉ-v k b A q₁) (updᵉ-v k b B q₂)
  updᵉ-v k b (A ⇒ C)   q with ∨-false (occᵉ-v k A) (occᵉ-c k C) q
  ... | q₁ , q₂ = cong₂ _⇒_ (updᵉ-v k b A q₁) (updᵉ-c k b C q₂)
  updᵉ-v k b ([ ρ ] A) q with ∨-false (occᵉ-r k ρ) (occᵉ-v k A) q
  ... | q₁ , q₂ = cong₂ [_]_ (updᵉ-r k b ρ q₁) (updᵉ-v k b A q₂)

  updᵉ-c : ∀ {Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → (C : OCType Ψ)
         → occᵉ-c k C ≡ false → C [ updᵉ k b ]ᶜ ≡ C
  updᵉ-c k b (A ‼ ε) q with ∨-false (occᵉ-v k A) (occᵉ-e k ε) q
  ... | q₁ , q₂ = cong₂ _‼_ (updᵉ-v k b A q₁) (updᵉ-e k b ε q₂)

updʳ-r : ∀ {Ψ} → (k : RVar Ψ) → (b : RExp Ψ) → (ρ : RExp Ψ)
       → occʳ-r k ρ ≡ false → ρ [ updʳ k b ]ʳ ≡ ρ
updʳ-r k b (rvar i)   q = updʳ-miss k b i q
updʳ-r k b (rconst c) q = refl
updʳ-r k b (ρ ·̂ᵣ ρ')  q with ∨-false (occʳ-r k ρ) (occʳ-r k ρ') q
... | q₁ , q₂ = cong₂ _·̂ᵣ_ (updʳ-r k b ρ q₁) (updʳ-r k b ρ' q₂)
updʳ-r k b (ρ ⊔̂ᵣ ρ')  q with ∨-false (occʳ-r k ρ) (occʳ-r k ρ') q
... | q₁ , q₂ = cong₂ _⊔̂ᵣ_ (updʳ-r k b ρ q₁) (updʳ-r k b ρ' q₂)
updʳ-r k b ∣ ε ∣̂ᵉ     q = cong ∣_∣̂ᵉ (updʳ-e k b ε)

mutual

  updʳ-v : ∀ {Ψ} → (k : RVar Ψ) → (b : RExp Ψ) → (A : OVType Ψ)
         → occʳ-v k A ≡ false → A [ updʳ k b ]ᵛ ≡ A
  updʳ-v k b (tvar α)  q = refl
  updʳ-v k b (Base c)  q = refl
  updʳ-v k b Unit      q = refl
  updʳ-v k b Bool      q = refl
  updʳ-v k b Empty     q = refl
  updʳ-v k b (A |×| B) q with ∨-false (occʳ-v k A) (occʳ-v k B) q
  ... | q₁ , q₂ = cong₂ _|×|_ (updʳ-v k b A q₁) (updʳ-v k b B q₂)
  updʳ-v k b (A ⇒ C)   q with ∨-false (occʳ-v k A) (occʳ-c k C) q
  ... | q₁ , q₂ = cong₂ _⇒_ (updʳ-v k b A q₁) (updʳ-c k b C q₂)
  updʳ-v k b ([ ρ ] A) q with ∨-false (occʳ-r k ρ) (occʳ-v k A) q
  ... | q₁ , q₂ = cong₂ [_]_ (updʳ-r k b ρ q₁) (updʳ-v k b A q₂)

  updʳ-c : ∀ {Ψ} → (k : RVar Ψ) → (b : RExp Ψ) → (C : OCType Ψ)
         → occʳ-c k C ≡ false → C [ updʳ k b ]ᶜ ≡ C
  updʳ-c k b (A ‼ ε) q = cong₂ _‼_ (updʳ-v k b A q) (updʳ-e k b ε)

-- ... and so does a later substitution

updᵉ-⨟e : ∀ {Ψ Ψ'} → (k : EVar Ψ) → (b : EExp Ψ) → (τ : Subst Ψ Ψ') → (ε : EExp Ψ)
        → occᵉ-e k ε ≡ false → ε [ updᵉ k b ⨟ˢ τ ]ᵉ ≡ ε [ τ ]ᵉ
updᵉ-⨟e k b τ ε q = trans (sym ([⨟]ᵉ ε (updᵉ k b) τ)) (cong (_[ τ ]ᵉ) (updᵉ-e k b ε q))

updᵉ-⨟r : ∀ {Ψ Ψ'} → (k : EVar Ψ) → (b : EExp Ψ) → (τ : Subst Ψ Ψ') → (ρ : RExp Ψ)
        → occᵉ-r k ρ ≡ false → ρ [ updᵉ k b ⨟ˢ τ ]ʳ ≡ ρ [ τ ]ʳ
updᵉ-⨟r k b τ ρ q = trans (sym ([⨟]ʳ ρ (updᵉ k b) τ)) (cong (_[ τ ]ʳ) (updᵉ-r k b ρ q))

updᵉ-⨟v : ∀ {Ψ Ψ'} → (k : EVar Ψ) → (b : EExp Ψ) → (τ : Subst Ψ Ψ') → (A : OVType Ψ)
        → occᵉ-v k A ≡ false → A [ updᵉ k b ⨟ˢ τ ]ᵛ ≡ A [ τ ]ᵛ
updᵉ-⨟v k b τ A q = trans (sym ([⨟]ᵛ A (updᵉ k b) τ)) (cong (_[ τ ]ᵛ) (updᵉ-v k b A q))

updʳ-⨟e : ∀ {Ψ Ψ'} → (k : RVar Ψ) → (b : RExp Ψ) → (τ : Subst Ψ Ψ') → (ε : EExp Ψ)
        → ε [ updʳ k b ⨟ˢ τ ]ᵉ ≡ ε [ τ ]ᵉ
updʳ-⨟e k b τ ε = trans (sym ([⨟]ᵉ ε (updʳ k b) τ)) (cong (_[ τ ]ᵉ) (updʳ-e k b ε))

updʳ-⨟r : ∀ {Ψ Ψ'} → (k : RVar Ψ) → (b : RExp Ψ) → (τ : Subst Ψ Ψ') → (ρ : RExp Ψ)
        → occʳ-r k ρ ≡ false → ρ [ updʳ k b ⨟ˢ τ ]ʳ ≡ ρ [ τ ]ʳ
updʳ-⨟r k b τ ρ q = trans (sym ([⨟]ʳ ρ (updʳ k b) τ)) (cong (_[ τ ]ʳ) (updʳ-r k b ρ q))

updʳ-⨟v : ∀ {Ψ Ψ'} → (k : RVar Ψ) → (b : RExp Ψ) → (τ : Subst Ψ Ψ') → (A : OVType Ψ)
        → occʳ-v k A ≡ false → A [ updʳ k b ⨟ˢ τ ]ᵛ ≡ A [ τ ]ᵛ
updʳ-⨟v k b τ A q = trans (sym ([⨟]ᵛ A (updʳ k b) τ)) (cong (_[ τ ]ᵛ) (updʳ-v k b A q))

------------------------------------------------------------------------
-- Locality: free in the image of no unknown the scope was entered with

freeᵉ : ∀ {Θ Φ} → EVar Φ → Subst Θ Φ → 𝔹
freeᵉ k O = anyᶠ (λ α → occᵉ-v k (sTy O α))
          ∨ (anyᶠ (λ i → occᵉ-r k (sR O i)) ∨ anyᶠ (λ i → occᵉ-e k (sE O i)))

freeʳ : ∀ {Θ Φ} → RVar Φ → Subst Θ Φ → 𝔹
freeʳ k O = anyᶠ (λ α → occʳ-v k (sTy O α)) ∨ anyᶠ (λ i → occʳ-r k (sR O i))

freeᵉ-fix : ∀ {Θ Φ} → (k : EVar Φ) → (O : Subst Θ Φ) → freeᵉ k O ≡ false
          → (b : EExp Φ) → (O ⨟ˢ updᵉ k b) ≐ˢ O
freeᵉ-fix k O q b with ∨-false (anyᶠ (λ α → occᵉ-v k (sTy O α))) _ q
... | qT , q' with ∨-false (anyᶠ (λ i → occᵉ-r k (sR O i))) _ q'
...   | qR , qE =
        mk≐ˢ (λ α → updᵉ-v k b (sTy O α) (anyᶠ-false (λ α' → occᵉ-v k (sTy O α')) qT α))
             (λ i → updᵉ-r k b (sR O i) (anyᶠ-false (λ i' → occᵉ-r k (sR O i')) qR i))
             (λ i → updᵉ-e k b (sE O i) (anyᶠ-false (λ i' → occᵉ-e k (sE O i')) qE i))

freeʳ-fix : ∀ {Θ Φ} → (k : RVar Φ) → (O : Subst Θ Φ) → freeʳ k O ≡ false
          → (b : RExp Φ) → (O ⨟ˢ updʳ k b) ≐ˢ O
freeʳ-fix k O q b with ∨-false (anyᶠ (λ α → occʳ-v k (sTy O α))) _ q
... | qT , qR =
      mk≐ˢ (λ α → updʳ-v k b (sTy O α) (anyᶠ-false (λ α' → occʳ-v k (sTy O α')) qT α))
           (λ i → updʳ-r k b (sR O i) (anyᶠ-false (λ i' → occʳ-r k (sR O i')) qR i))
           (λ i → updʳ-e k b (sE O i))

------------------------------------------------------------------------
-- Expressions over the unknowns a substitution's images mention

Outerₑ : ∀ {Θ Φ} → Subst Θ Φ → EExp Φ → Set
Outerₑ O ε = ∀ {k} → occᵉ-e k ε ≡ true → freeᵉ k O ≡ true

Outerᵣ : ∀ {Θ Φ} → Subst Θ Φ → RExp Φ → Set
Outerᵣ O ρ = (∀ {k} → occᵉ-r k ρ ≡ true → freeᵉ k O ≡ true)
           × (∀ {k} → occʳ-r k ρ ≡ true → freeʳ k O ≡ true)

∨-elim : ∀ {P : Set} {b b' : 𝔹} → (b ≡ true → P) → (b' ≡ true → P) → b ∨ b' ≡ true → P
∨-elim {b = b} {b'} f g q with ∨-true b b' q
... | inj₁ r = f r
... | inj₂ r = g r

outerₑ? : ∀ {Θ Φ} → (O : Subst Θ Φ) → (ε : EExp Φ) → Maybe (Outerₑ O ε)
outerₑ? O (evar i) with freeᵉ i O in q
... | true  = just (λ {k} r → subst (λ x → freeᵉ x O ≡ true) (sym (true-dec (k ≟ᶠ i) r)) q)
... | false = nothing
outerₑ? O (econst c) = just (λ ())
outerₑ? O (ε ·̂ₑ ε') with outerₑ? O ε | outerₑ? O ε'
... | just f | just g = just (∨-elim f g)
... | _      | _      = nothing
outerₑ? O (ε ⊔̂ₑ ε') with outerₑ? O ε | outerₑ? O ε'
... | just f | just g = just (∨-elim f g)
... | _      | _      = nothing

outerᵣ? : ∀ {Θ Φ} → (O : Subst Θ Φ) → (ρ : RExp Φ) → Maybe (Outerᵣ O ρ)
outerᵣ? O (rvar i) with freeʳ i O in q
... | true  = just ((λ ()) ,
                    λ {k} r → subst (λ x → freeʳ x O ≡ true) (sym (true-dec (k ≟ᶠ i) r)) q)
... | false = nothing
outerᵣ? O (rconst c) = just ((λ ()) , (λ ()))
outerᵣ? O (ρ ·̂ᵣ ρ') with outerᵣ? O ρ | outerᵣ? O ρ'
... | just (f , f') | just (g , g') = just (∨-elim f g , ∨-elim f' g')
... | _             | _             = nothing
outerᵣ? O (ρ ⊔̂ᵣ ρ') with outerᵣ? O ρ | outerᵣ? O ρ'
... | just (f , f') | just (g , g') = just (∨-elim f g , ∨-elim f' g')
... | _             | _             = nothing
outerᵣ? O ∣ ε ∣̂ᵉ with outerₑ? O ε
... | just f  = just (f , (λ ()))
... | nothing = nothing

-- A variable, with the equation that names it: a pattern-matching
-- wrapper, so that a case analysis on it stays visible to a proof

evar? : ∀ {Φ} → (ε : EExp Φ) → Maybe (Σ[ j ∈ EVar Φ ] (ε ≡ evar j))
evar? (evar j)   = just (j , refl)
evar? (econst c) = nothing
evar? (ε ·̂ₑ ε')  = nothing
evar? (ε ⊔̂ₑ ε')  = nothing

------------------------------------------------------------------------
-- The eigenvariable of a rigid scope

-- `κ⟨ b ⟩` (`Deferred`) sends the newest effect-grade variable to `b`,
-- fixing the rest; being a substitution, entailment survives it. The
-- eigenvariable is sent to the unit (`κᵉ`), and to the top (`κ⊤`)
-- where an ordering is kept at the top rigid.

κᵉ : ∀ {Ψ} → Subst (Ψ +e) Ψ
κᵉ = κ⟨ ûₑ ⟩

κ⊤ : ∀ {Ψ} → Subst (Ψ +e) Ψ
κ⊤ = κ⟨ econst ⊤ₑ ⟩

⊩ᴴ-κᵉ : ∀ {Ψ} {Q : Hyps Ψ} → Q ⊩ᴴ (wkᵉ-H Q) [ κᵉ ]
⊩ᴴ-κᵉ = ⊩ᴴ-κ ûₑ

-- The unit is below the top, so sending the eigenvariable there
-- instead raises every instance

κᵉ≾κ⊤ : ∀ {Ψ} {Q : Hyps Ψ} → Q ⊩ κᵉ ≾ˢ κ⊤
κᵉ≾κ⊤ = mk≾ˢ (λ i → ⊩≾̂ᵣ-refl) (λ { zero → topₑ ; (suc i) → ⊩≾̂ₑ-refl })


-- `ω` sends it to the top and fixes the rest. It raises every image,
-- and leaves a weakened hypothesis set entailed.

ω : ∀ {Ψ} → Subst (Ψ +e) (Ψ +e)
ω = κ⊤ ⨟ˢ wkˢᵉ

wk-ω : ∀ {Ψ} → (wkˢᵉ {Ψ} ⨟ˢ ω) ≐ˢ wkˢᵉ
wk-ω = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

id≾ω : ∀ {Ψ} {Q : Hyps (Ψ +e)} → Q ⊩ idˢ ≾ˢ ω
id≾ω = mk≾ˢ (λ i → ⊩≾̂ᵣ-refl) (λ { zero → topₑ ; (suc i) → ⊩≾̂ₑ-refl })

⊩ᴴ-ω : ∀ {Ψ} {Q : Hyps Ψ} → wkᵉ-H Q ⊩ᴴ (wkᵉ-H Q) [ ω ]
⊩ᴴ-ω = ⊩ᴴ-⨟ ⊩ᴴ-wkᵉ (⊩ᴴ-κ (econst ⊤ₑ))

------------------------------------------------------------------------
-- Two substitutions agree after `X` on the unknowns `O` mentions

Agree : ∀ {Θ Φ Ψ Ψ'} → Subst Θ Φ → Subst Φ Ψ → Subst Ψ Ψ' → Subst Ψ Ψ' → Set
Agree O X σ₁ σ₂ = (∀ {k} → freeᵉ k O ≡ true → sE X k [ σ₁ ]ᵉ ≡ sE X k [ σ₂ ]ᵉ)
                × (∀ {k} → freeʳ k O ≡ true → sR X k [ σ₁ ]ʳ ≡ sR X k [ σ₂ ]ʳ)

-- An expression mentioning only such unknowns reads the same too

module _ {Θ Φ Ψ Ψ'} {O : Subst Θ Φ} {X : Subst Φ Ψ} {σ₁ σ₂ : Subst Ψ Ψ'}
         (u : Agree O X σ₁ σ₂) where

  agreeₑ : (ε : EExp Φ) → Outerₑ O ε → ε [ X ⨟ˢ σ₁ ]ᵉ ≡ ε [ X ⨟ˢ σ₂ ]ᵉ
  agreeₑ (evar i)   o = proj₁ u (o (dec-true (i ≟ᶠ i) refl))
  agreeₑ (econst c) o = refl
  agreeₑ (ε ·̂ₑ ε')  o = cong₂ _·̂ₑ_ (agreeₑ ε (λ q → o (∨-left _ _ q)))
                                   (agreeₑ ε' (λ q → o (∨-right _ _ q)))
  agreeₑ (ε ⊔̂ₑ ε')  o = cong₂ _⊔̂ₑ_ (agreeₑ ε (λ q → o (∨-left _ _ q)))
                                   (agreeₑ ε' (λ q → o (∨-right _ _ q)))

  agreeᵣ : (ρ : RExp Φ) → Outerᵣ O ρ → ρ [ X ⨟ˢ σ₁ ]ʳ ≡ ρ [ X ⨟ˢ σ₂ ]ʳ
  agreeᵣ (rvar i)   (oe , or) = proj₂ u (or (dec-true (i ≟ᶠ i) refl))
  agreeᵣ (rconst c) o         = refl
  agreeᵣ (ρ ·̂ᵣ ρ')  (oe , or) =
    cong₂ _·̂ᵣ_ (agreeᵣ ρ  ((λ q → oe (∨-left _ _ q)) , (λ q → or (∨-left _ _ q))))
               (agreeᵣ ρ' ((λ q → oe (∨-right _ _ q)) , (λ q → or (∨-right _ _ q))))
  agreeᵣ (ρ ⊔̂ᵣ ρ')  (oe , or) =
    cong₂ _⊔̂ᵣ_ (agreeᵣ ρ  ((λ q → oe (∨-left _ _ q)) , (λ q → or (∨-left _ _ q))))
               (agreeᵣ ρ' ((λ q → oe (∨-right _ _ q)) , (λ q → or (∨-right _ _ q))))
  agreeᵣ ∣ ε ∣̂ᵉ     (oe , or) = cong ∣_∣̂ᵉ (agreeₑ ε oe)

-- Conversely, an image that reads the same does so at every unknown
-- occurring in it: the formers are injective

·̂ₑ-inj : ∀ {Ψ} {a b c d : EExp Ψ} → a ·̂ₑ b ≡ c ·̂ₑ d → (a ≡ c) × (b ≡ d)
·̂ₑ-inj refl = refl , refl

⊔̂ₑ-inj : ∀ {Ψ} {a b c d : EExp Ψ} → a ⊔̂ₑ b ≡ c ⊔̂ₑ d → (a ≡ c) × (b ≡ d)
⊔̂ₑ-inj refl = refl , refl

·̂ᵣ-inj : ∀ {Ψ} {a b c d : RExp Ψ} → a ·̂ᵣ b ≡ c ·̂ᵣ d → (a ≡ c) × (b ≡ d)
·̂ᵣ-inj refl = refl , refl

⊔̂ᵣ-inj : ∀ {Ψ} {a b c d : RExp Ψ} → a ⊔̂ᵣ b ≡ c ⊔̂ᵣ d → (a ≡ c) × (b ≡ d)
⊔̂ᵣ-inj refl = refl , refl

∣∣-inj : ∀ {Ψ} {a b : EExp Ψ} → ∣ a ∣̂ᵉ ≡ ∣ b ∣̂ᵉ → a ≡ b
∣∣-inj refl = refl

|×|-inj : ∀ {Ψ} {A B C D : OVType Ψ} → A |×| B ≡ C |×| D → (A ≡ C) × (B ≡ D)
|×|-inj refl = refl , refl

⇒-inj : ∀ {Ψ} {A B : OVType Ψ} {C D : OCType Ψ} → A ⇒ C ≡ B ⇒ D → (A ≡ B) × (C ≡ D)
⇒-inj refl = refl , refl

[]-inj : ∀ {Ψ} {ρ ρ' : RExp Ψ} {A B : OVType Ψ} → [ ρ ] A ≡ [ ρ' ] B → (ρ ≡ ρ') × (A ≡ B)
[]-inj refl = refl , refl

‼-inj : ∀ {Ψ} {A B : OVType Ψ} {ε ε' : EExp Ψ} → A ‼ ε ≡ B ‼ ε' → (A ≡ B) × (ε ≡ ε')
‼-inj refl = refl , refl

module _ {Φ Ψ Ψ'} (X : Subst Φ Ψ) (σ₁ σ₂ : Subst Ψ Ψ') where

  -- at an effect-grade unknown

  subᵉ-e : ∀ {k} → (x : EExp Φ) → occᵉ-e k x ≡ true
         → x [ X ]ᵉ [ σ₁ ]ᵉ ≡ x [ X ]ᵉ [ σ₂ ]ᵉ → sE X k [ σ₁ ]ᵉ ≡ sE X k [ σ₂ ]ᵉ
  subᵉ-e {k} (evar i) r e =
    subst (λ k' → sE X k' [ σ₁ ]ᵉ ≡ sE X k' [ σ₂ ]ᵉ) (sym (true-dec (k ≟ᶠ i) r)) e
  subᵉ-e {k} (a ·̂ₑ b) r e with ∨-true (occᵉ-e k a) (occᵉ-e k b) r
  ... | inj₁ r' = subᵉ-e a r' (proj₁ (·̂ₑ-inj e))
  ... | inj₂ r' = subᵉ-e b r' (proj₂ (·̂ₑ-inj e))
  subᵉ-e {k} (a ⊔̂ₑ b) r e with ∨-true (occᵉ-e k a) (occᵉ-e k b) r
  ... | inj₁ r' = subᵉ-e a r' (proj₁ (⊔̂ₑ-inj e))
  ... | inj₂ r' = subᵉ-e b r' (proj₂ (⊔̂ₑ-inj e))

  subᵉ-r : ∀ {k} → (x : RExp Φ) → occᵉ-r k x ≡ true
         → x [ X ]ʳ [ σ₁ ]ʳ ≡ x [ X ]ʳ [ σ₂ ]ʳ → sE X k [ σ₁ ]ᵉ ≡ sE X k [ σ₂ ]ᵉ
  subᵉ-r {k} (a ·̂ᵣ b) r e with ∨-true (occᵉ-r k a) (occᵉ-r k b) r
  ... | inj₁ r' = subᵉ-r a r' (proj₁ (·̂ᵣ-inj e))
  ... | inj₂ r' = subᵉ-r b r' (proj₂ (·̂ᵣ-inj e))
  subᵉ-r {k} (a ⊔̂ᵣ b) r e with ∨-true (occᵉ-r k a) (occᵉ-r k b) r
  ... | inj₁ r' = subᵉ-r a r' (proj₁ (⊔̂ᵣ-inj e))
  ... | inj₂ r' = subᵉ-r b r' (proj₂ (⊔̂ᵣ-inj e))
  subᵉ-r {k} ∣ a ∣̂ᵉ r e = subᵉ-e a r (∣∣-inj e)

  subᵉ-v : ∀ {k} → (x : OVType Φ) → occᵉ-v k x ≡ true
         → x [ X ]ᵛ [ σ₁ ]ᵛ ≡ x [ X ]ᵛ [ σ₂ ]ᵛ → sE X k [ σ₁ ]ᵉ ≡ sE X k [ σ₂ ]ᵉ
  subᵉ-c : ∀ {k} → (x : OCType Φ) → occᵉ-c k x ≡ true
         → x [ X ]ᶜ [ σ₁ ]ᶜ ≡ x [ X ]ᶜ [ σ₂ ]ᶜ → sE X k [ σ₁ ]ᵉ ≡ sE X k [ σ₂ ]ᵉ

  subᵉ-v {k} (A |×| B) r e with ∨-true (occᵉ-v k A) (occᵉ-v k B) r
  ... | inj₁ r' = subᵉ-v A r' (proj₁ (|×|-inj e))
  ... | inj₂ r' = subᵉ-v B r' (proj₂ (|×|-inj e))
  subᵉ-v {k} (A ⇒ C) r e with ∨-true (occᵉ-v k A) (occᵉ-c k C) r
  ... | inj₁ r' = subᵉ-v A r' (proj₁ (⇒-inj e))
  ... | inj₂ r' = subᵉ-c C r' (proj₂ (⇒-inj e))
  subᵉ-v {k} ([ ρ ] A) r e with ∨-true (occᵉ-r k ρ) (occᵉ-v k A) r
  ... | inj₁ r' = subᵉ-r ρ r' (proj₁ ([]-inj e))
  ... | inj₂ r' = subᵉ-v A r' (proj₂ ([]-inj e))

  subᵉ-c {k} (A ‼ ε) r e with ∨-true (occᵉ-v k A) (occᵉ-e k ε) r
  ... | inj₁ r' = subᵉ-v A r' (proj₁ (‼-inj e))
  ... | inj₂ r' = subᵉ-e ε r' (proj₂ (‼-inj e))

  -- at a resource-grade unknown

  subʳ-r : ∀ {k} → (x : RExp Φ) → occʳ-r k x ≡ true
         → x [ X ]ʳ [ σ₁ ]ʳ ≡ x [ X ]ʳ [ σ₂ ]ʳ → sR X k [ σ₁ ]ʳ ≡ sR X k [ σ₂ ]ʳ
  subʳ-r {k} (rvar i) r e =
    subst (λ k' → sR X k' [ σ₁ ]ʳ ≡ sR X k' [ σ₂ ]ʳ) (sym (true-dec (k ≟ᶠ i) r)) e
  subʳ-r {k} (a ·̂ᵣ b) r e with ∨-true (occʳ-r k a) (occʳ-r k b) r
  ... | inj₁ r' = subʳ-r a r' (proj₁ (·̂ᵣ-inj e))
  ... | inj₂ r' = subʳ-r b r' (proj₂ (·̂ᵣ-inj e))
  subʳ-r {k} (a ⊔̂ᵣ b) r e with ∨-true (occʳ-r k a) (occʳ-r k b) r
  ... | inj₁ r' = subʳ-r a r' (proj₁ (⊔̂ᵣ-inj e))
  ... | inj₂ r' = subʳ-r b r' (proj₂ (⊔̂ᵣ-inj e))

  subʳ-v : ∀ {k} → (x : OVType Φ) → occʳ-v k x ≡ true
         → x [ X ]ᵛ [ σ₁ ]ᵛ ≡ x [ X ]ᵛ [ σ₂ ]ᵛ → sR X k [ σ₁ ]ʳ ≡ sR X k [ σ₂ ]ʳ
  subʳ-c : ∀ {k} → (x : OCType Φ) → occʳ-c k x ≡ true
         → x [ X ]ᶜ [ σ₁ ]ᶜ ≡ x [ X ]ᶜ [ σ₂ ]ᶜ → sR X k [ σ₁ ]ʳ ≡ sR X k [ σ₂ ]ʳ

  subʳ-v {k} (A |×| B) r e with ∨-true (occʳ-v k A) (occʳ-v k B) r
  ... | inj₁ r' = subʳ-v A r' (proj₁ (|×|-inj e))
  ... | inj₂ r' = subʳ-v B r' (proj₂ (|×|-inj e))
  subʳ-v {k} (A ⇒ C) r e with ∨-true (occʳ-v k A) (occʳ-c k C) r
  ... | inj₁ r' = subʳ-v A r' (proj₁ (⇒-inj e))
  ... | inj₂ r' = subʳ-c C r' (proj₂ (⇒-inj e))
  subʳ-v {k} ([ ρ ] A) r e with ∨-true (occʳ-r k ρ) (occʳ-v k A) r
  ... | inj₁ r' = subʳ-r ρ r' (proj₁ ([]-inj e))
  ... | inj₂ r' = subʳ-v A r' (proj₂ ([]-inj e))

  subʳ-c (A ‼ ε) r e = subʳ-v A r (proj₁ (‼-inj e))

-- The images of the unknowns `O` mentions are all of the form `y [ w ]`,
-- on which the two agree

agree-out : ∀ {Θ Φ Ψ Ψ' Ψ₀} → (O : Subst Θ Φ) → (X : Subst Φ Ψ) → (σ₁ σ₂ : Subst Ψ Ψ')
          → (w : Subst Ψ₀ Ψ) → (δ₀ : Subst Θ Ψ₀)
          → (∀ y → y [ w ]ᵛ [ σ₁ ]ᵛ ≡ y [ w ]ᵛ [ σ₂ ]ᵛ)
          → (∀ y → y [ w ]ʳ [ σ₁ ]ʳ ≡ y [ w ]ʳ [ σ₂ ]ʳ)
          → (∀ y → y [ w ]ᵉ [ σ₁ ]ᵉ ≡ y [ w ]ᵉ [ σ₂ ]ᵉ)
          → (O ⨟ˢ X) ≐ˢ (δ₀ ⨟ˢ w) → Agree O X σ₁ σ₂
agree-out {Ψ₀ = Ψ₀} O X σ₁ σ₂ w δ₀ fv fr fe tr = ue , ur
  where
    flatᵛ : ∀ {x} → (y : OVType Ψ₀) → x ≡ y [ w ]ᵛ → x [ σ₁ ]ᵛ ≡ x [ σ₂ ]ᵛ
    flatᵛ y e = trans (cong (_[ σ₁ ]ᵛ) e) (trans (fv y) (sym (cong (_[ σ₂ ]ᵛ) e)))

    flatʳ : ∀ {x} → (y : RExp Ψ₀) → x ≡ y [ w ]ʳ → x [ σ₁ ]ʳ ≡ x [ σ₂ ]ʳ
    flatʳ y e = trans (cong (_[ σ₁ ]ʳ) e) (trans (fr y) (sym (cong (_[ σ₂ ]ʳ) e)))

    flatᵉ : ∀ {x} → (y : EExp Ψ₀) → x ≡ y [ w ]ᵉ → x [ σ₁ ]ᵉ ≡ x [ σ₂ ]ᵉ
    flatᵉ y e = trans (cong (_[ σ₁ ]ᵉ) e) (trans (fe y) (sym (cong (_[ σ₂ ]ᵉ) e)))

    ue : ∀ {k} → freeᵉ k O ≡ true → sE X k [ σ₁ ]ᵉ ≡ sE X k [ σ₂ ]ᵉ
    ue {k} q with ∨-true (anyᶠ (λ α → occᵉ-v k (sTy O α))) _ q
    ... | inj₁ qt with anyᶠ-true (λ α → occᵉ-v k (sTy O α)) qt
    ...   | α , r = subᵉ-v X σ₁ σ₂ (sTy O α) r (flatᵛ (sTy δ₀ α) (≐ᵗ tr α))
    ue {k} q | inj₂ q' with ∨-true (anyᶠ (λ i → occᵉ-r k (sR O i))) _ q'
    ...   | inj₁ qr with anyᶠ-true (λ i → occᵉ-r k (sR O i)) qr
    ...     | i , r = subᵉ-r X σ₁ σ₂ (sR O i) r (flatʳ (sR δ₀ i) (≐ʳ tr i))
    ue {k} q | inj₂ q' | inj₂ qe with anyᶠ-true (λ i → occᵉ-e k (sE O i)) qe
    ...     | i , r = subᵉ-e X σ₁ σ₂ (sE O i) r (flatᵉ (sE δ₀ i) (≐ᵉ tr i))

    ur : ∀ {k} → freeʳ k O ≡ true → sR X k [ σ₁ ]ʳ ≡ sR X k [ σ₂ ]ʳ
    ur {k} q with ∨-true (anyᶠ (λ α → occʳ-v k (sTy O α))) _ q
    ... | inj₁ qt with anyᶠ-true (λ α → occʳ-v k (sTy O α)) qt
    ...   | α , r = subʳ-v X σ₁ σ₂ (sTy O α) r (flatᵛ (sTy δ₀ α) (≐ᵗ tr α))
    ur {k} q | inj₂ qr with anyᶠ-true (λ i → occʳ-r k (sR O i)) qr
    ...   | i , r = subʳ-r X σ₁ σ₂ (sR O i) r (flatʳ (sR δ₀ i) (≐ʳ tr i))

-- An instance entering a rigid scope: the scope's own unknowns go to an
-- instance of the enclosing scope, the rigid to a fresh eigenvariable.
-- The images of the outer unknowns other than the rigid do not depend
-- on the eigenvariable.

Entry : ∀ {Θ Φ Ψ''} → Subst (Θ +e) Φ → Subst Φ (Ψ'' +e) → Set
Entry {Θ} {Ψ'' = Ψ''} O τ = Σ[ δ₀ ∈ Subst Θ Ψ'' ] ((O ⨟ˢ τ) ≐ˢ (δ₀ ↑ᵉ))

stable-out : ∀ {Θ Φ Ψ''} → (O : Subst (Θ +e) Φ) → (τ : Subst Φ (Ψ'' +e)) → Entry O τ
           → Agree (wkˢᵉ {Θ} ⨟ˢ O) τ ω idˢ
stable-out O τ (δ₀ , en) =
  agree-out (wkˢᵉ ⨟ˢ O) τ ω idˢ wkˢᵉ δ₀
    (λ y → trans ([⨟]ᵛ y wkˢᵉ ω) (trans ([≐]ᵛ wk-ω y) (sym ([id]ᵛ (y [ wkˢᵉ ]ᵛ)))))
    (λ y → trans ([⨟]ʳ y wkˢᵉ ω) (trans ([≐]ʳ wk-ω y) (sym ([id]ʳ (y [ wkˢᵉ ]ʳ)))))
    (λ y → trans ([⨟]ᵉ y wkˢᵉ ω) (trans ([≐]ᵉ wk-ω y) (sym ([id]ᵉ (y [ wkˢᵉ ]ᵉ)))))
    (≐ˢ-trans (⨟-assoc wkˢᵉ O τ) (≐ˢ-trans (⨟-congʳ wkˢᵉ en) (wkˢᵉ-↑ᵉ δ₀)))

------------------------------------------------------------------------
-- How an unknown `v` occurs in a list of orderings, over either sort of
-- grade expression

module Sides {X : Set} (_≟_ : Decidable (_≡_ {A = X})) (occ : X → 𝔹) where

  -- an ordering holds at every instance, or the unknown is absent from
  -- its right (left) side

  FreeR : X × X → Set
  FreeR (x , x') = (x ≡ x') ⊎ (occ x' ≡ false)

  FreeL : X × X → Set
  FreeL (x , x') = (x ≡ x') ⊎ (occ x ≡ false)

  freeRs : (l : List (X × X)) → Maybe (∀ {a} → a ∈ l → FreeR a)
  freeRs []             = just (λ ())
  freeRs ((x , x') ∷ l) = go (freeRs l) (x ≟ x') (isFalse (occ x'))
    where
      go : Maybe (∀ {a} → a ∈ l → FreeR a) → _ → Maybe (occ x' ≡ false)
         → Maybe (∀ {a} → a ∈ (x , x') ∷ l → FreeR a)
      go nothing  _        _        = nothing
      go (just f) (yes e)  _        = just (λ { (here refl) → inj₁ e ; (there m) → f m })
      go (just f) (no _)   (just q) = just (λ { (here refl) → inj₂ q ; (there m) → f m })
      go (just f) (no _)   nothing  = nothing

  freeLs : (l : List (X × X)) → Maybe (∀ {a} → a ∈ l → FreeL a)
  freeLs []             = just (λ ())
  freeLs ((x , x') ∷ l) = go (freeLs l) (x ≟ x') (isFalse (occ x))
    where
      go : Maybe (∀ {a} → a ∈ l → FreeL a) → _ → Maybe (occ x ≡ false)
         → Maybe (∀ {a} → a ∈ (x , x') ∷ l → FreeL a)
      go nothing  _        _        = nothing
      go (just f) (yes e)  _        = just (λ { (here refl) → inj₁ e ; (there m) → f m })
      go (just f) (no _)   (just q) = just (λ { (here refl) → inj₂ q ; (there m) → f m })
      go (just f) (no _)   nothing  = nothing

module Bounds {X : Set} (_≟_ : Decidable (_≡_ {A = X})) (occ : X → 𝔹) (v : X) where

  open Sides _≟_ occ public

  -- `v` occurs on a right side only as the whole side, below a bound in
  -- `L`

  LowAt : List X → X × X → Set
  LowAt L (x , x') = FreeR (x , x') ⊎ ((x' ≡ v) × (x ∈ L))

  -- `v` occurs on a left side only as the whole side, below `U`

  UpAt : X → X × X → Set
  UpAt U (x , x') = FreeL (x , x') ⊎ ((x ≡ v) × (x' ≡ U))

  record Lows (l : List (X × X)) : Set where
    constructor lows
    field
      bnds : List X
      cls  : ∀ {a} → a ∈ l → LowAt bnds a
      src  : ∀ {x} → x ∈ bnds → (x , v) ∈ l

  open Lows public

  record Ups (l : List (X × X)) : Set where
    constructor ups
    field
      cap  : X
      clsᵘ : ∀ {a} → a ∈ l → UpAt cap a
      srcᵘ : (v , cap) ∈ l

  open Ups public

  -- The lower bounds, none of them mentioning `v`

  lowsOf : (l : List (X × X)) → Maybe (Lows l)
  lowsOf []             = just (lows [] (λ ()) (λ ()))
  lowsOf ((x , x') ∷ l) = go (lowsOf l) (x' ≟ v) (isFalse (occ x)) (x ≟ x') (isFalse (occ x'))
    where
      wk : ∀ {L a} → LowAt L a → LowAt (x ∷ L) a
      wk (inj₁ f)            = inj₁ f
      wk (inj₂ (e , m))      = inj₂ (e , there m)

      go : Maybe (Lows l) → _ → Maybe (occ x ≡ false) → _ → Maybe (occ x' ≡ false)
         → Maybe (Lows ((x , x') ∷ l))
      go nothing                _        _        _       _        = nothing
      go (just (lows L c s))    (yes e)  (just _) _       _        =
        just (lows (x ∷ L) (λ { (here refl) → inj₂ (e , here refl) ; (there m) → wk (c m) })
                           (λ { (here refl) → here (cong (x ,_) (sym e)) ; (there m) → there (s m) }))
      go (just (lows L c s))    _        _        (yes e) _        =
        just (lows L (λ { (here refl) → inj₁ (inj₁ e) ; (there m) → c m }) (λ m → there (s m)))
      go (just (lows L c s))    _        _        (no _)  (just q) =
        just (lows L (λ { (here refl) → inj₁ (inj₂ q) ; (there m) → c m }) (λ m → there (s m)))
      go (just (lows L c s))    _        _        (no _)  nothing  = nothing

  -- The one upper bound: the first found, every other one equal to it

  capOf : (l : List (X × X)) → Maybe (Σ[ U ∈ X ] ((v , U) ∈ l))
  capOf []             = nothing
  capOf ((x , x') ∷ l) = go (x ≟ v) (isFalse (occ x')) (capOf l)
    where
      go : _ → Maybe (occ x' ≡ false) → Maybe (Σ[ U ∈ X ] ((v , U) ∈ l))
         → Maybe (Σ[ U ∈ X ] ((v , U) ∈ (x , x') ∷ l))
      go (yes e)    (just _) _              = just (x' , here (cong (_, x') (sym e)))
      go _          _        (just (U , m)) = just (U , there m)
      go _          _        nothing        = nothing

  upsAt : (U : X) → (l : List (X × X)) → Maybe (∀ {a} → a ∈ l → UpAt U a)
  upsAt U []             = just (λ ())
  upsAt U ((x , x') ∷ l) = go (upsAt U l) (x ≟ x') (isFalse (occ x)) (x ≟ v) (x' ≟ U)
    where
      go : Maybe (∀ {a} → a ∈ l → UpAt U a) → _ → Maybe (occ x ≡ false) → _ → _
         → Maybe (∀ {a} → a ∈ (x , x') ∷ l → UpAt U a)
      go nothing  _       _        _       _       = nothing
      go (just f) (yes e) _        _       _       =
        just (λ { (here refl) → inj₁ (inj₁ e) ; (there m) → f m })
      go (just f) (no _)  (just q) _       _       =
        just (λ { (here refl) → inj₁ (inj₂ q) ; (there m) → f m })
      go (just f) (no _)  nothing  (yes e) (yes e') =
        just (λ { (here refl) → inj₂ (e , e') ; (there m) → f m })
      go (just f) (no _)  nothing  _       _       = nothing

  upsOf : (l : List (X × X)) → Maybe (Ups l)
  upsOf l with capOf l
  ... | nothing      = nothing
  ... | just (U , m) with upsAt U l
  ...   | nothing = nothing
  ...   | just f  = just (ups U f m)

allFalse : ∀ {Y : Set} → (f : Y → 𝔹) → (l : List Y) → Maybe (∀ {y} → y ∈ l → f y ≡ false)
allFalse f []      = just (λ ())
allFalse f (y ∷ l) with isFalse (f y) | allFalse f l
... | just q  | just g  = just (λ { (here refl) → q ; (there m) → g m })
... | just _  | nothing = nothing
... | nothing | _       = nothing

module Bᵉ {Ψ} (k : EVar Ψ) = Bounds (_≟ᵉ_ {Ψ}) (occᵉ-e {Ψ} k) (evar k)
module Bᵉʳ {Ψ} (k : EVar Ψ) = Sides (_≟ʳ_ {Ψ}) (occᵉ-r {Ψ} k)
module Bʳ {Ψ} (k : RVar Ψ) = Bounds (_≟ʳ_ {Ψ}) (occʳ-r {Ψ} k) (rvar k)

-- An unknown absent from every type of a residual. A disjunction's
-- grade is the left side of an ordering below the unit, so it is kept
-- by lowering, and asked to be free of the unknown only for raising.

record Cleanᵉ {Ψ} (k : EVar Ψ) (R : Resid Ψ) : Set where
  constructor cleanᵉ
  field
    cts : ∀ {A}   → A ∈ ts R       → occᵉ-v k A ≡ false
    css : ∀ {A B} → (A , B) ∈ ss R → (occᵉ-v k A ∨ occᵉ-v k B) ≡ false
    cds : ∀ {A ρ} → (A , ρ) ∈ ds R → occᵉ-v k A ≡ false

record Cleanʳ {Ψ} (k : RVar Ψ) (R : Resid Ψ) : Set where
  constructor cleanʳ
  field
    cts : ∀ {A}   → A ∈ ts R       → occʳ-v k A ≡ false
    css : ∀ {A B} → (A , B) ∈ ss R → (occʳ-v k A ∨ occʳ-v k B) ≡ false
    cds : ∀ {A ρ} → (A , ρ) ∈ ds R → occʳ-v k A ≡ false

cleanᵉ? : ∀ {Ψ} → (k : EVar Ψ) → (R : Resid Ψ) → Maybe (Cleanᵉ k R)
cleanᵉ? k R with allFalse (occᵉ-v k) (ts R)
                | allFalse (λ { (A , B) → occᵉ-v k A ∨ occᵉ-v k B }) (ss R)
                | allFalse (λ { (A , ρ) → occᵉ-v k A }) (ds R)
... | just t  | just s  | just d  = just (cleanᵉ t s d)
... | _       | _       | _       = nothing

cleanʳ? : ∀ {Ψ} → (k : RVar Ψ) → (R : Resid Ψ) → Maybe (Cleanʳ k R)
cleanʳ? k R with allFalse (occʳ-v k) (ts R)
                | allFalse (λ { (A , B) → occʳ-v k A ∨ occʳ-v k B }) (ss R)
                | allFalse (λ { (A , ρ) → occʳ-v k A }) (ds R)
... | just t  | just s  | just d  = just (cleanʳ t s d)
... | _       | _       | _       = nothing

-- The unknown absent from every disjunction's grade

DFreeᵉ : ∀ {Ψ} → EVar Ψ → Resid Ψ → Set
DFreeᵉ k R = ∀ {A ρ} → (A , ρ) ∈ ds R → occᵉ-r k ρ ≡ false

DFreeʳ : ∀ {Ψ} → RVar Ψ → Resid Ψ → Set
DFreeʳ k R = ∀ {A ρ} → (A , ρ) ∈ ds R → occʳ-r k ρ ≡ false

dfreeᵉ? : ∀ {Ψ} → (k : EVar Ψ) → (R : Resid Ψ) → Maybe (DFreeᵉ k R)
dfreeᵉ? k R with allFalse (λ { (A , ρ) → occᵉ-r k ρ }) (ds R)
... | just f  = just (λ m → f m)
... | nothing = nothing

dfreeʳ? : ∀ {Ψ} → (k : RVar Ψ) → (R : Resid Ψ) → Maybe (DFreeʳ k R)
dfreeʳ? k R with allFalse (λ { (A , ρ) → occʳ-r k ρ }) (ds R)
... | just f  = just (λ m → f m)
... | nothing = nothing

------------------------------------------------------------------------
-- The lowering lemma and its siblings: an assignment the conditions
-- license keeps every instance that satisfied the residual

-- the types, where the unknown does not occur, are left as they were

cleanᵉ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : EVar Ψ} {R : Resid Ψ}
         → Cleanᵉ k R → (b : EExp Ψ) → (τ : Subst Ψ Ψ') → Q ⊩ᴿ R [ τ ]
         → (∀ {A ρ} → (A , ρ) ∈ ds R → Q ⊩ ρ [ updᵉ k b ⨟ˢ τ ]ʳ ≾̂ᵣ ρ [ τ ]ʳ)
         → (∀ {A} → A ∈ ts R → Q ⊩ᴱ A [ updᵉ k b ⨟ˢ τ ]ᵛ)
         × (∀ {A B} → (A , B) ∈ ss R → Q ∣ A [ updᵉ k b ⨟ˢ τ ]ᵛ <:̂ᵛ B [ updᵉ k b ⨟ˢ τ ]ᵛ)
         × (∀ {A ρ} → (A , ρ) ∈ ds R
              → VarOK Q (A [ updᵉ k b ⨟ˢ τ ]ᵛ) (ρ [ updᵉ k b ⨟ˢ τ ]ʳ))
cleanᵉ-⊩ {Q = Q} {k} {R} (cleanᵉ ct cs cd) b τ h g = ts' , ss' , ds'
  where
    ts' : ∀ {A} → A ∈ ts R → Q ⊩ᴱ A [ updᵉ k b ⨟ˢ τ ]ᵛ
    ts' {A} m = subst (Q ⊩ᴱ_) (sym (updᵉ-⨟v k b τ A (ct m))) (⊩ts h m)

    ss' : ∀ {A B} → (A , B) ∈ ss R → Q ∣ A [ updᵉ k b ⨟ˢ τ ]ᵛ <:̂ᵛ B [ updᵉ k b ⨟ˢ τ ]ᵛ
    ss' {A} {B} m with ∨-false (occᵉ-v k A) (occᵉ-v k B) (cs m)
    ... | qA , qB = subst₂ (Q ∣_<:̂ᵛ_) (sym (updᵉ-⨟v k b τ A qA)) (sym (updᵉ-⨟v k b τ B qB))
                           (⊩ss h m)

    ds' : ∀ {A ρ} → (A , ρ) ∈ ds R → VarOK Q (A [ updᵉ k b ⨟ˢ τ ]ᵛ) (ρ [ updᵉ k b ⨟ˢ τ ]ʳ)
    ds' {A} {ρ} m =
      subst (λ X → VarOK Q X (ρ [ updᵉ k b ⨟ˢ τ ]ʳ)) (sym (updᵉ-⨟v k b τ A (cd m)))
            (VarOK-≡̂ (≡̂ᵛ-refl (A [ τ ]ᵛ)) (g m) (⊩ds h m))

cleanʳ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : RVar Ψ} {R : Resid Ψ}
         → Cleanʳ k R → (b : RExp Ψ) → (τ : Subst Ψ Ψ') → Q ⊩ᴿ R [ τ ]
         → (∀ {A ρ} → (A , ρ) ∈ ds R → Q ⊩ ρ [ updʳ k b ⨟ˢ τ ]ʳ ≾̂ᵣ ρ [ τ ]ʳ)
         → (∀ {A} → A ∈ ts R → Q ⊩ᴱ A [ updʳ k b ⨟ˢ τ ]ᵛ)
         × (∀ {A B} → (A , B) ∈ ss R → Q ∣ A [ updʳ k b ⨟ˢ τ ]ᵛ <:̂ᵛ B [ updʳ k b ⨟ˢ τ ]ᵛ)
         × (∀ {A ρ} → (A , ρ) ∈ ds R
              → VarOK Q (A [ updʳ k b ⨟ˢ τ ]ᵛ) (ρ [ updʳ k b ⨟ˢ τ ]ʳ))
cleanʳ-⊩ {Q = Q} {k} {R} (cleanʳ ct cs cd) b τ h g = ts' , ss' , ds'
  where
    ts' : ∀ {A} → A ∈ ts R → Q ⊩ᴱ A [ updʳ k b ⨟ˢ τ ]ᵛ
    ts' {A} m = subst (Q ⊩ᴱ_) (sym (updʳ-⨟v k b τ A (ct m))) (⊩ts h m)

    ss' : ∀ {A B} → (A , B) ∈ ss R → Q ∣ A [ updʳ k b ⨟ˢ τ ]ᵛ <:̂ᵛ B [ updʳ k b ⨟ˢ τ ]ᵛ
    ss' {A} {B} m with ∨-false (occʳ-v k A) (occʳ-v k B) (cs m)
    ... | qA , qB = subst₂ (Q ∣_<:̂ᵛ_) (sym (updʳ-⨟v k b τ A qA)) (sym (updʳ-⨟v k b τ B qB))
                           (⊩ss h m)

    ds' : ∀ {A ρ} → (A , ρ) ∈ ds R → VarOK Q (A [ updʳ k b ⨟ˢ τ ]ᵛ) (ρ [ updʳ k b ⨟ˢ τ ]ʳ)
    ds' {A} {ρ} m =
      subst (λ X → VarOK Q X (ρ [ updʳ k b ⨟ˢ τ ]ʳ)) (sym (updʳ-⨟v k b τ A (cd m)))
            (VarOK-≡̂ (≡̂ᵛ-refl (A [ τ ]ᵛ)) (g m) (⊩ds h m))

-- Lowering an effect unknown below its value, to a bound above each of
-- its lower bounds

lowerᵉ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : EVar Ψ} {R : Resid Ψ}
         → (lw : Bᵉ.Lows {Ψ} k (es R))
         → (∀ {a} → a ∈ rs R → Bᵉʳ.FreeR {Ψ} k a)
         → Cleanᵉ k R
         → (b : EExp Ψ) → (∀ {E} → E ∈ dfs R → Still dir↓ (updᵉ k b) E)
         → (τ : Subst Ψ Ψ')
         → Q ⊩ b [ τ ]ᵉ ≾̂ₑ sE τ k
         → (∀ {x} → x ∈ Bᵉ.bnds lw → Q ⊩ x [ τ ]ᵉ ≾̂ₑ b [ τ ]ᵉ)
         → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updᵉ k b ⨟ˢ τ ]
lowerᵉ-⊩ {Q = Q} {k} {R} lw fr cl b sd τ below ub h =
  mk⊩ᴿ rs' es' (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↓ E (sd m) le (⊩dfs h m))
  where
    τ₁ = updᵉ k b ⨟ˢ τ

    le : Q ⊩ τ₁ ≾ˢ τ
    le = updᵉ-below k b τ below

    c = cleanᵉ-⊩ cl b τ h (λ {A} {ρ} m → mono-substᵣ le ρ)

    es' : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ τ₁ ]ᵉ ≾̂ₑ ε' [ τ₁ ]ᵉ
    es' {ε} {ε'} m with Bᵉ.cls lw m
    ... | inj₁ (inj₁ refl) = ⊩≾̂ₑ-refl
    ... | inj₁ (inj₂ q)    =
          transₑ (mono-substₑ le ε)
                 (subst (λ x → Q ⊩ ε [ τ ]ᵉ ≾̂ₑ x) (sym (updᵉ-⨟e k b τ ε' q)) (⊩es h m))
    ... | inj₂ (refl , mx) =
          transₑ (mono-substₑ le ε)
                 (subst (λ x → Q ⊩ ε [ τ ]ᵉ ≾̂ₑ x [ τ ]ᵉ) (sym (updᵉ-hit k b)) (ub mx))

    rs' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ τ₁ ]ʳ ≾̂ᵣ ρ' [ τ₁ ]ʳ
    rs' {ρ} {ρ'} m with fr m
    ... | inj₁ refl = ⊩≾̂ᵣ-refl
    ... | inj₂ q    =
          transᵣ (mono-substᵣ le ρ)
                 (subst (λ x → Q ⊩ ρ [ τ ]ʳ ≾̂ᵣ x) (sym (updᵉ-⨟r k b τ ρ' q)) (⊩rs h m))

-- Raising an effect unknown to its one upper bound

raiseᵉ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : EVar Ψ} {R : Resid Ψ}
         → (up : Bᵉ.Ups {Ψ} k (es R))
         → (∀ {a} → a ∈ rs R → Bᵉʳ.FreeL {Ψ} k a)
         → Cleanᵉ k R → DFreeᵉ k R
         → (∀ {E} → E ∈ dfs R → Still dir↑ (updᵉ k (Bᵉ.cap up)) E)
         → (τ : Subst Ψ Ψ')
         → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updᵉ k (Bᵉ.cap up) ⨟ˢ τ ]
raiseᵉ-⊩ {Q = Q} {k} {R} up fl cl df sd τ h =
  mk⊩ᴿ rs' es' (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↑ E (sd m) ge (⊩dfs h m))
  where
    U  = Bᵉ.cap up
    τ₁ = updᵉ k U ⨟ˢ τ

    ge : Q ⊩ τ ≾ˢ τ₁
    ge = updᵉ-above k U τ (⊩es h (Bᵉ.srcᵘ up))

    c = cleanᵉ-⊩ cl U τ h
          (λ {A} {ρ} m → subst (λ x → Q ⊩ x ≾̂ᵣ ρ [ τ ]ʳ) (sym (updᵉ-⨟r k U τ ρ (df m))) ⊩≾̂ᵣ-refl)

    es' : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ τ₁ ]ᵉ ≾̂ₑ ε' [ τ₁ ]ᵉ
    es' {ε} {ε'} m with Bᵉ.clsᵘ up m
    ... | inj₁ (inj₁ refl) = ⊩≾̂ₑ-refl
    ... | inj₁ (inj₂ q)    =
          transₑ (subst (λ x → Q ⊩ x ≾̂ₑ ε' [ τ ]ᵉ) (sym (updᵉ-⨟e k U τ ε q)) (⊩es h m))
                 (mono-substₑ ge ε')
    ... | inj₂ (refl , refl) =
          subst (λ x → Q ⊩ x [ τ ]ᵉ ≾̂ₑ U [ τ₁ ]ᵉ) (sym (updᵉ-hit k U)) (mono-substₑ ge U)

    rs' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ τ₁ ]ʳ ≾̂ᵣ ρ' [ τ₁ ]ʳ
    rs' {ρ} {ρ'} m with fl m
    ... | inj₁ refl = ⊩≾̂ᵣ-refl
    ... | inj₂ q    =
          transᵣ (subst (λ x → Q ⊩ x ≾̂ᵣ ρ' [ τ ]ʳ) (sym (updᵉ-⨟r k U τ ρ q)) (⊩rs h m))
                 (mono-substᵣ ge ρ')

-- The same two for a resource unknown, which no effect ordering mentions

lowerʳ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : RVar Ψ} {R : Resid Ψ}
         → (lw : Bʳ.Lows {Ψ} k (rs R))
         → Cleanʳ k R
         → (b : RExp Ψ) → (∀ {E} → E ∈ dfs R → Still dir↓ (updʳ k b) E)
         → (τ : Subst Ψ Ψ')
         → Q ⊩ b [ τ ]ʳ ≾̂ᵣ sR τ k
         → (∀ {x} → x ∈ Bʳ.bnds lw → Q ⊩ x [ τ ]ʳ ≾̂ᵣ b [ τ ]ʳ)
         → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updʳ k b ⨟ˢ τ ]
lowerʳ-⊩ {Q = Q} {k} {R} lw cl b sd τ below ub h =
  mk⊩ᴿ rs' es' (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↓ E (sd m) le (⊩dfs h m))
  where
    τ₁ = updʳ k b ⨟ˢ τ

    le : Q ⊩ τ₁ ≾ˢ τ
    le = updʳ-below k b τ below

    c = cleanʳ-⊩ cl b τ h (λ {A} {ρ} m → mono-substᵣ le ρ)

    rs' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ τ₁ ]ʳ ≾̂ᵣ ρ' [ τ₁ ]ʳ
    rs' {ρ} {ρ'} m with Bʳ.cls lw m
    ... | inj₁ (inj₁ refl) = ⊩≾̂ᵣ-refl
    ... | inj₁ (inj₂ q)    =
          transᵣ (mono-substᵣ le ρ)
                 (subst (λ x → Q ⊩ ρ [ τ ]ʳ ≾̂ᵣ x) (sym (updʳ-⨟r k b τ ρ' q)) (⊩rs h m))
    ... | inj₂ (refl , mx) =
          transᵣ (mono-substᵣ le ρ)
                 (subst (λ x → Q ⊩ ρ [ τ ]ʳ ≾̂ᵣ x [ τ ]ʳ) (sym (updʳ-hit k b)) (ub mx))

    es' : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ τ₁ ]ᵉ ≾̂ₑ ε' [ τ₁ ]ᵉ
    es' {ε} {ε'} m =
      subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym (updʳ-⨟e k b τ ε)) (sym (updʳ-⨟e k b τ ε')) (⊩es h m)

raiseʳ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : RVar Ψ} {R : Resid Ψ}
         → (up : Bʳ.Ups {Ψ} k (rs R))
         → Cleanʳ k R → DFreeʳ k R
         → (∀ {E} → E ∈ dfs R → Still dir↑ (updʳ k (Bʳ.cap up)) E)
         → (τ : Subst Ψ Ψ')
         → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updʳ k (Bʳ.cap up) ⨟ˢ τ ]
raiseʳ-⊩ {Q = Q} {k} {R} up cl df sd τ h =
  mk⊩ᴿ rs' es' (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↑ E (sd m) ge (⊩dfs h m))
  where
    U  = Bʳ.cap up
    τ₁ = updʳ k U ⨟ˢ τ

    ge : Q ⊩ τ ≾ˢ τ₁
    ge = updʳ-above k U τ (⊩rs h (Bʳ.srcᵘ up))

    c = cleanʳ-⊩ cl U τ h
          (λ {A} {ρ} m → subst (λ x → Q ⊩ x ≾̂ᵣ ρ [ τ ]ʳ) (sym (updʳ-⨟r k U τ ρ (df m))) ⊩≾̂ᵣ-refl)

    rs' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ τ₁ ]ʳ ≾̂ᵣ ρ' [ τ₁ ]ʳ
    rs' {ρ} {ρ'} m with Bʳ.clsᵘ up m
    ... | inj₁ (inj₁ refl) = ⊩≾̂ᵣ-refl
    ... | inj₁ (inj₂ q)    =
          transᵣ (subst (λ x → Q ⊩ x ≾̂ᵣ ρ' [ τ ]ʳ) (sym (updʳ-⨟r k U τ ρ q)) (⊩rs h m))
                 (mono-substᵣ ge ρ')
    ... | inj₂ (refl , refl) =
          subst (λ x → Q ⊩ x [ τ ]ʳ ≾̂ᵣ U [ τ₁ ]ʳ) (sym (updʳ-hit k U)) (mono-substᵣ ge U)

    es' : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ τ₁ ]ᵉ ≾̂ₑ ε' [ τ₁ ]ᵉ
    es' {ε} {ε'} m =
      subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym (updʳ-⨟e k U τ ε)) (sym (updʳ-⨟e k U τ ε')) (⊩es h m)

-- Raising an unknown absent from every left side to the top

topᵉ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : EVar Ψ} {R : Resid Ψ}
       → (∀ {a} → a ∈ es R → Bᵉ.FreeL {Ψ} k a)
       → (∀ {a} → a ∈ rs R → Bᵉʳ.FreeL {Ψ} k a)
       → Cleanᵉ k R → DFreeᵉ k R
       → (∀ {E} → E ∈ dfs R → Still dir↑ (updᵉ k (econst ⊤ₑ)) E)
       → (τ : Subst Ψ Ψ')
       → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updᵉ k (econst ⊤ₑ) ⨟ˢ τ ]
topᵉ-⊩ {Q = Q} {k} {R} fe fl cl df sd τ h =
  mk⊩ᴿ rs' es' (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↑ E (sd m) ge (⊩dfs h m))
  where
    τ₁ = updᵉ k (econst ⊤ₑ) ⨟ˢ τ

    ge : Q ⊩ τ ≾ˢ τ₁
    ge = updᵉ-above k (econst ⊤ₑ) τ topₑ

    c = cleanᵉ-⊩ cl (econst ⊤ₑ) τ h
          (λ {A} {ρ} m → subst (λ x → Q ⊩ x ≾̂ᵣ ρ [ τ ]ʳ)
                               (sym (updᵉ-⨟r k (econst ⊤ₑ) τ ρ (df m))) ⊩≾̂ᵣ-refl)

    es' : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ τ₁ ]ᵉ ≾̂ₑ ε' [ τ₁ ]ᵉ
    es' {ε} {ε'} m with fe m
    ... | inj₁ refl = ⊩≾̂ₑ-refl
    ... | inj₂ q    =
          transₑ (subst (λ x → Q ⊩ x ≾̂ₑ ε' [ τ ]ᵉ) (sym (updᵉ-⨟e k (econst ⊤ₑ) τ ε q)) (⊩es h m))
                 (mono-substₑ ge ε')

    rs' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ τ₁ ]ʳ ≾̂ᵣ ρ' [ τ₁ ]ʳ
    rs' {ρ} {ρ'} m with fl m
    ... | inj₁ refl = ⊩≾̂ᵣ-refl
    ... | inj₂ q    =
          transᵣ (subst (λ x → Q ⊩ x ≾̂ᵣ ρ' [ τ ]ʳ) (sym (updᵉ-⨟r k (econst ⊤ₑ) τ ρ q)) (⊩rs h m))
                 (mono-substᵣ ge ρ')

topʳ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : RVar Ψ} {R : Resid Ψ}
       → (∀ {a} → a ∈ rs R → Bʳ.FreeL {Ψ} k a)
       → Cleanʳ k R → DFreeʳ k R
       → (∀ {E} → E ∈ dfs R → Still dir↑ (updʳ k (rconst ⊤ᵣ)) E)
       → (τ : Subst Ψ Ψ')
       → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updʳ k (rconst ⊤ᵣ) ⨟ˢ τ ]
topʳ-⊩ {Q = Q} {k} {R} fl cl df sd τ h =
  mk⊩ᴿ rs' es' (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↑ E (sd m) ge (⊩dfs h m))
  where
    τ₁ = updʳ k (rconst ⊤ᵣ) ⨟ˢ τ

    ge : Q ⊩ τ ≾ˢ τ₁
    ge = updʳ-above k (rconst ⊤ᵣ) τ topᵣ

    c = cleanʳ-⊩ cl (rconst ⊤ᵣ) τ h
          (λ {A} {ρ} m → subst (λ x → Q ⊩ x ≾̂ᵣ ρ [ τ ]ʳ)
                               (sym (updʳ-⨟r k (rconst ⊤ᵣ) τ ρ (df m))) ⊩≾̂ᵣ-refl)

    rs' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ τ₁ ]ʳ ≾̂ᵣ ρ' [ τ₁ ]ʳ
    rs' {ρ} {ρ'} m with fl m
    ... | inj₁ refl = ⊩≾̂ᵣ-refl
    ... | inj₂ q    =
          transᵣ (subst (λ x → Q ⊩ x ≾̂ᵣ ρ' [ τ ]ʳ) (sym (updʳ-⨟r k (rconst ⊤ᵣ) τ ρ q)) (⊩rs h m))
                 (mono-substᵣ ge ρ')

    es' : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ τ₁ ]ᵉ ≾̂ₑ ε' [ τ₁ ]ᵉ
    es' {ε} {ε'} m =
      subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym (updʳ-⨟e k (rconst ⊤ᵣ) τ ε))
             (sym (updʳ-⨟e k (rconst ⊤ᵣ) τ ε')) (⊩es h m)

------------------------------------------------------------------------
-- One step: the value an unknown is sent to, with the proof that every
-- instance survives it

Keeps : ∀ {Ψ} → Subst Ψ Ψ → Resid Ψ → Set
Keeps {Ψ} σ R = ∀ {Ψ'} → (τ : Subst Ψ Ψ') → (Q : Hyps Ψ') → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ σ ⨟ˢ τ ]

first : ∀ {X : Set} → Maybe X → Maybe X → Maybe X
first (just x) _ = just x
first nothing  y = y

-- Whether an unknown occurs in the deferred conditions on a greater
-- side (`dir↓`) or a smaller one (`dir↑`): sent to the top, it moves
-- that side

failed : ∀ {X : Set} → Maybe X → 𝔹
failed (just _) = false
failed nothing  = true

inDfsᵉ : ∀ {Ψ} → Dir → EVar Ψ → Resid Ψ → 𝔹
inDfsᵉ d k R = failed (stills? d (updᵉ k (econst ⊤ₑ)) (dfs R))

inDfsʳ : ∀ {Ψ} → Dir → RVar Ψ → Resid Ψ → 𝔹
inDfsʳ d k R = failed (stills? d (updʳ k (rconst ⊤ᵣ)) (dfs R))

-- The unit, for an unknown with no bound that does occur

occursᵉ : ∀ {Ψ} → EVar Ψ → Resid Ψ → 𝔹
occursᵉ k R = anyL (λ { (ε , _) → occᵉ-e k ε }) (es R) ∨ anyL (λ { (ρ , _) → occᵉ-r k ρ }) (rs R)
            ∨ anyL (λ { (_ , ρ) → occᵉ-r k ρ }) (ds R) ∨ inDfsᵉ dir↑ k R ∨ inDfsᵉ dir↓ k R

occursʳ : ∀ {Ψ} → RVar Ψ → Resid Ψ → 𝔹
occursʳ k R = anyL (λ { (ρ , _) → occʳ-r k ρ }) (rs R) ∨ anyL (λ { (_ , ρ) → occʳ-r k ρ }) (ds R)
            ∨ inDfsʳ dir↑ k R ∨ inDfsʳ dir↓ k R

-- The top, for an unknown with no bound above that does occur

occursᵉ⁺ : ∀ {Ψ} → EVar Ψ → Resid Ψ → 𝔹
occursᵉ⁺ k R = anyL (λ { (_ , ε') → occᵉ-e k ε' }) (es R) ∨ anyL (λ { (_ , ρ') → occᵉ-r k ρ' }) (rs R)
             ∨ inDfsᵉ dir↓ k R

occursʳ⁺ : ∀ {Ψ} → RVar Ψ → Resid Ψ → 𝔹
occursʳ⁺ k R = anyL (λ { (_ , ρ') → occʳ-r k ρ' }) (rs R) ∨ inDfsʳ dir↓ k R

stepᵉ : ∀ {Ψ} → (k : EVar Ψ) → (R : Resid Ψ) → Maybe (Σ[ b ∈ EExp Ψ ] Keeps (updᵉ k b) R)
stepᵉ {Ψ} k R with cleanᵉ? k R
... | nothing = nothing
... | just cl =
      first (lower (Bᵉ.lowsOf {Ψ} k (es R)) (Bᵉʳ.freeRs {Ψ} k (rs R)))
            (first (raise (Bᵉ.upsOf {Ψ} k (es R)) (Bᵉʳ.freeLs {Ψ} k (rs R)) (dfreeᵉ? k R))
            (first (unit (Is-just? uₑ-least?) (Bᵉ.lowsOf {Ψ} k (es R)) (Bᵉʳ.freeRs {Ψ} k (rs R)) (occursᵉ k R))
                   (top (Bᵉ.freeLs {Ψ} k (es R)) (Bᵉʳ.freeLs {Ψ} k (rs R)) (dfreeᵉ? k R)
                        (occursᵉ⁺ k R))))
  where
    lower : Maybe (Bᵉ.Lows {Ψ} k (es R)) → Maybe (∀ {a} → a ∈ rs R → Bᵉʳ.FreeR {Ψ} k a)
          → Maybe (Σ[ b ∈ EExp _ ] Keeps (updᵉ k b) R)
    lower (just lw@(Bᵉ.lows (x ∷ xs) c s)) (just fr)
      with stills? dir↓ (updᵉ k (joinₑ x xs)) (dfs R)
    ... | just sd =
          just (joinₑ x xs ,
                λ τ Q h → lowerᵉ-⊩ lw fr cl (joinₑ x xs) sd τ
                            (joinₑ-lub⊩ τ x xs (λ m → ⊩es h (s m)))
                            (joinₑ-ub⊩ τ x xs) h)
    ... | nothing = nothing
    lower _ _ = nothing

    raise : Maybe (Bᵉ.Ups {Ψ} k (es R)) → Maybe (∀ {a} → a ∈ rs R → Bᵉʳ.FreeL {Ψ} k a)
          → Maybe (DFreeᵉ k R) → Maybe (Σ[ b ∈ EExp _ ] Keeps (updᵉ k b) R)
    raise (just up) (just fl) (just df) with stills? dir↑ (updᵉ k (Bᵉ.cap up)) (dfs R)
    ... | just sd = just (Bᵉ.cap up , λ τ Q h → raiseᵉ-⊩ up fl cl df sd τ h)
    ... | nothing = nothing
    raise _         _         _         = nothing

    unit : Maybe (Is-just uₑ-least?) → Maybe (Bᵉ.Lows {Ψ} k (es R))
         → Maybe (∀ {a} → a ∈ rs R → Bᵉʳ.FreeR {Ψ} k a) → 𝔹
         → Maybe (Σ[ b ∈ EExp _ ] Keeps (updᵉ k b) R)
    unit (just ij) (just lw@(Bᵉ.lows [] c s)) (just fr) true
      with stills? dir↓ (updᵉ k ûₑ) (dfs R)
    ... | just sd = just (ûₑ , λ τ Q h → lowerᵉ-⊩ lw fr cl ûₑ sd τ (minₑ ij) (λ ()) h)
    ... | nothing = nothing
    unit _ _ _ _ = nothing

    top : Maybe (∀ {a} → a ∈ es R → Bᵉ.FreeL {Ψ} k a)
        → Maybe (∀ {a} → a ∈ rs R → Bᵉʳ.FreeL {Ψ} k a) → Maybe (DFreeᵉ k R) → 𝔹
        → Maybe (Σ[ b ∈ EExp _ ] Keeps (updᵉ k b) R)
    top (just fe) (just fl) (just df) true with stills? dir↑ (updᵉ k (econst ⊤ₑ)) (dfs R)
    ... | just sd = just (econst ⊤ₑ , λ τ Q h → topᵉ-⊩ fe fl cl df sd τ h)
    ... | nothing = nothing
    top _         _         _         _    = nothing

stepʳ : ∀ {Ψ} → (k : RVar Ψ) → (R : Resid Ψ) → Maybe (Σ[ b ∈ RExp Ψ ] Keeps (updʳ k b) R)
stepʳ {Ψ} k R with cleanʳ? k R
... | nothing = nothing
... | just cl =
      first (lower (Bʳ.lowsOf {Ψ} k (rs R)))
            (first (raise (Bʳ.upsOf {Ψ} k (rs R)) (dfreeʳ? k R))
            (first (unit (Is-just? uᵣ-least?) (Bʳ.lowsOf {Ψ} k (rs R)) (occursʳ k R))
                   (top (Bʳ.freeLs {Ψ} k (rs R)) (dfreeʳ? k R) (occursʳ⁺ k R))))
  where
    lower : Maybe (Bʳ.Lows {Ψ} k (rs R)) → Maybe (Σ[ b ∈ RExp _ ] Keeps (updʳ k b) R)
    lower (just lw@(Bʳ.lows (x ∷ xs) c s)) with stills? dir↓ (updʳ k (joinᵣ x xs)) (dfs R)
    ... | just sd =
          just (joinᵣ x xs ,
                λ τ Q h → lowerʳ-⊩ lw cl (joinᵣ x xs) sd τ
                            (joinᵣ-lub⊩ τ x xs (λ m → ⊩rs h (s m)))
                            (joinᵣ-ub⊩ τ x xs) h)
    ... | nothing = nothing
    lower _ = nothing

    raise : Maybe (Bʳ.Ups {Ψ} k (rs R)) → Maybe (DFreeʳ k R)
          → Maybe (Σ[ b ∈ RExp _ ] Keeps (updʳ k b) R)
    raise (just up) (just df) with stills? dir↑ (updʳ k (Bʳ.cap up)) (dfs R)
    ... | just sd = just (Bʳ.cap up , λ τ Q h → raiseʳ-⊩ up cl df sd τ h)
    ... | nothing = nothing
    raise _         _         = nothing

    unit : Maybe (Is-just uᵣ-least?) → Maybe (Bʳ.Lows {Ψ} k (rs R)) → 𝔹
         → Maybe (Σ[ b ∈ RExp _ ] Keeps (updʳ k b) R)
    unit (just ij) (just lw@(Bʳ.lows [] c s)) true with stills? dir↓ (updʳ k ûᵣ) (dfs R)
    ... | just sd = just (ûᵣ , λ τ Q h → lowerʳ-⊩ lw cl ûᵣ sd τ (minᵣ ij) (λ ()) h)
    ... | nothing = nothing
    unit _ _ _ = nothing

    top : Maybe (∀ {a} → a ∈ rs R → Bʳ.FreeL {Ψ} k a) → Maybe (DFreeʳ k R) → 𝔹
        → Maybe (Σ[ b ∈ RExp _ ] Keeps (updʳ k b) R)
    top (just fl) (just df) true with stills? dir↑ (updʳ k (rconst ⊤ᵣ)) (dfs R)
    ... | just sd = just (rconst ⊤ᵣ , λ τ Q h → topʳ-⊩ fl cl df sd τ h)
    ... | nothing = nothing
    top _         _         _    = nothing

------------------------------------------------------------------------
-- Settled atoms: an ordering, or a disjunction with a side, decided true
-- against no hypotheses holds at every instance and bounds nothing

Every : ∀ {Ψ} {X : Set} → (∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set) → X → Set
Every P a = ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst _ Ψ') → P Q δ a

Ordʳ : ∀ {Ψ Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → RExp Ψ × RExp Ψ → Set
Ordʳ Q δ (ρ , ρ') = Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ

Ordᵉ : ∀ {Ψ Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → EExp Ψ × EExp Ψ → Set
Ordᵉ Q δ (ε , ε') = Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ

Disj : ∀ {Ψ Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → OVType Ψ × RExp Ψ → Set
Disj Q δ (A , ρ) = VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ)

settledʳ : ∀ {Ψ} → (a : RExp Ψ × RExp Ψ) → Maybe (Every Ordʳ a)
settledʳ (ρ , ρ') with decide≾ᵣ {Q = ∅ᴴ} ρ ρ'
... | just p  = just (λ δ → ⊩-substᵣ ∅ᴴ-⊩ᴴ p)
... | nothing = nothing

settledᵉ : ∀ {Ψ} → (a : EExp Ψ × EExp Ψ) → Maybe (Every Ordᵉ a)
settledᵉ (ε , ε') with decide≾ₑ {Q = ∅ᴴ} ε ε'
... | just p  = just (λ δ → ⊩-substₑ ∅ᴴ-⊩ᴴ p)
... | nothing = nothing

settledᵈ : ∀ {Ψ} → (a : OVType Ψ × RExp Ψ) → Maybe (Every Disj a)
settledᵈ (A , ρ) with decide≾ᵣ {Q = ∅ᴴ} ρ ûᵣ
... | just p  = just (λ δ → ≾ᵘ-ok (⊩-substᵣ ∅ᴴ-⊩ᴴ p))
... | nothing with etDec A in e
...   | just [] = just (λ δ → et-ok (⊩ᴱ-subst ∅ᴴ-⊩ᴴ (etDec-sound {Q = ∅ᴴ} A e (λ ()))))
...   | just (_ ∷ _) = nothing
...   | nothing      = nothing

-- The entries of a list that are not settled

record Unsettled {Ψ} {X : Set} (P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set)
                 (l : List X) : Set where
  constructor unset
  field
    kept  : List X
    kept⊆ : ∀ {a} → a ∈ kept → a ∈ l
    back  : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
          → (∀ {a} → a ∈ kept → P Q δ a) → ∀ {a} → a ∈ l → P Q δ a

unsettled : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set}
          → ((a : X) → Maybe (Every P a)) → (l : List X) → Unsettled P l
unsettled set []      = unset [] (λ ()) (λ δ k → λ ())
unsettled {P = P} set (a ∷ l) = go (set a) (unsettled set l)
  where
    go : Maybe (Every P a) → Unsettled P l → Unsettled P (a ∷ l)
    go (just p) (unset l' sb bk) =
      unset l' (λ m → there (sb m))
            (λ δ k → λ { (here refl) → p δ ; (there m) → bk δ k m })
    go nothing  (unset l' sb bk) =
      unset (a ∷ l')
            (λ { (here refl) → here refl ; (there m) → there (sb m) })
            (λ δ k → λ { (here refl) → k (here refl)
                       ; (there m)   → bk δ (λ m' → k (there m')) m })

------------------------------------------------------------------------
-- A disjunction whose type is eternal at no instance (`etDec` refutes
-- it) is met, from no hypotheses, exactly by its grade side

record Refined {Ψ} (l : List (OVType Ψ × RExp Ψ)) : Set where
  constructor refined
  field
    rest  : List (OVType Ψ × RExp Ψ)
    ords  : List (RExp Ψ × RExp Ψ)
    rest⊆ : ∀ {a} → a ∈ rest → a ∈ l
    back  : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
          → (∀ {a} → a ∈ rest → Disj Q δ a) → (∀ {a} → a ∈ ords → Ordʳ Q δ a)
          → ∀ {a} → a ∈ l → Disj Q δ a
    fwd   : ∀ {Ψ'} → (δ : Subst Ψ Ψ')
          → (∀ {a} → a ∈ l → Disj ∅ᴴ δ a) → ∀ {a} → a ∈ ords → Ordʳ ∅ᴴ δ a
    restᴱ : ∀ {A ρ} → (A , ρ) ∈ rest → Σ[ αs ∈ List (TyVar Ψ) ] (etDec A ≡ just αs)

grade-side : ∀ {Ψ Ψ'} → (A : OVType Ψ) → etDec A ≡ nothing → {ρ : RExp Ψ} → (δ : Subst Ψ Ψ')
           → Disj ∅ᴴ δ (A , ρ) → Ordʳ ∅ᴴ δ (ρ , ûᵣ)
grade-side A e δ (et-ok et)      = ⊥-elim (etDec-refute A e δ et)
grade-side A e δ (≾ᵘ-ok le)      = le
grade-side A e δ (hyp-ok () _ _)

refine : ∀ {Ψ} → (l : List (OVType Ψ × RExp Ψ)) → Refined l
refine []            = refined [] [] (λ ()) (λ δ k o ()) (λ δ k ()) (λ ())
refine ((A , ρ) ∷ l) with etDec A in e | refine l
... | nothing | refined r os sb bk fw re =
      refined r ((ρ , ûᵣ) ∷ os) (λ m → there (sb m))
        (λ δ k o → λ { (here refl) → ≾ᵘ-ok (o (here refl))
                     ; (there m)   → bk δ k (λ m' → o (there m')) m })
        (λ δ k → λ { (here refl) → grade-side A e {ρ} δ (k (here refl))
                   ; (there m)   → fw δ (λ m' → k (there m')) m })
        re
... | just αs | refined r os sb bk fw re =
      refined ((A , ρ) ∷ r) os
        (λ { (here refl) → here refl ; (there m) → there (sb m) })
        (λ δ k o → λ { (here refl) → k (here refl)
                     ; (there m)   → bk δ (λ m' → k (there m')) o m })
        (λ δ k → fw δ (λ m → k (there m)))
        (λ { (here refl) → αs , e ; (there m) → re m })

------------------------------------------------------------------------
-- A set of unknowns sent to the top at once

data Mem (Φ : Scope) : Set where
  eᵐ : EVar Φ → Mem Φ
  rᵐ : RVar Φ → Mem Φ

inᴱ : ∀ {Φ} → EVar Φ → List (Mem Φ) → 𝔹
inᴱ k []             = false
inᴱ k (eᵐ k' ∷ l) = ⌊ k ≟ᶠ k' ⌋ ∨ inᴱ k l
inᴱ k (rᵐ _  ∷ l) = inᴱ k l

inᴿ : ∀ {Φ} → RVar Φ → List (Mem Φ) → 𝔹
inᴿ k []             = false
inᴿ k (eᵐ _  ∷ l) = inᴿ k l
inᴿ k (rᵐ k' ∷ l) = ⌊ k ≟ᶠ k' ⌋ ∨ inᴿ k l

topE : ∀ {Φ} → 𝔹 → EVar Φ → EExp Φ
topE true  k = econst ⊤ₑ
topE false k = evar k

topR : ∀ {Φ} → 𝔹 → RVar Φ → RExp Φ
topR true  k = rconst ⊤ᵣ
topR false k = rvar k

tops : ∀ {Φ} → List (Mem Φ) → Subst Φ Φ
tops l = sub tvar (λ k → topR (inᴿ k l) k) (λ k → topE (inᴱ k l) k)

-- Whether a member occurs

hitₑ : ∀ {Φ} → List (Mem Φ) → EExp Φ → 𝔹
hitₑ l (evar k)   = inᴱ k l
hitₑ l (econst c) = false
hitₑ l (ε ·̂ₑ ε')  = hitₑ l ε ∨ hitₑ l ε'
hitₑ l (ε ⊔̂ₑ ε')  = hitₑ l ε ∨ hitₑ l ε'

hitᵣ : ∀ {Φ} → List (Mem Φ) → RExp Φ → 𝔹
hitᵣ l (rvar k)   = inᴿ k l
hitᵣ l (rconst c) = false
hitᵣ l (ρ ·̂ᵣ ρ')  = hitᵣ l ρ ∨ hitᵣ l ρ'
hitᵣ l (ρ ⊔̂ᵣ ρ')  = hitᵣ l ρ ∨ hitᵣ l ρ'
hitᵣ l ∣ ε ∣̂ᵉ     = hitₑ l ε

hitᵥ : ∀ {Φ} → List (Mem Φ) → OVType Φ → 𝔹
hitᶜ : ∀ {Φ} → List (Mem Φ) → OCType Φ → 𝔹
hitᵥ l (tvar α)  = false
hitᵥ l (Base b)  = false
hitᵥ l Unit      = false
hitᵥ l Bool      = false
hitᵥ l Empty     = false
hitᵥ l (A |×| B) = hitᵥ l A ∨ hitᵥ l B
hitᵥ l (A ⇒ C)   = hitᵥ l A ∨ hitᶜ l C
hitᵥ l ([ ρ ] A) = hitᵣ l ρ ∨ hitᵥ l A
hitᶜ l (A ‼ ε)   = hitᵥ l A ∨ hitₑ l ε

-- What no member occurs in is left alone

tops-e : ∀ {Φ} → (l : List (Mem Φ)) → (ε : EExp Φ) → hitₑ l ε ≡ false → ε [ tops l ]ᵉ ≡ ε
tops-e l (evar k)   q = cong (λ b → topE b k) q
tops-e l (econst c) q = refl
tops-e l (ε ·̂ₑ ε')  q with ∨-false (hitₑ l ε) (hitₑ l ε') q
... | q₁ , q₂ = cong₂ _·̂ₑ_ (tops-e l ε q₁) (tops-e l ε' q₂)
tops-e l (ε ⊔̂ₑ ε')  q with ∨-false (hitₑ l ε) (hitₑ l ε') q
... | q₁ , q₂ = cong₂ _⊔̂ₑ_ (tops-e l ε q₁) (tops-e l ε' q₂)

tops-r : ∀ {Φ} → (l : List (Mem Φ)) → (ρ : RExp Φ) → hitᵣ l ρ ≡ false → ρ [ tops l ]ʳ ≡ ρ
tops-r l (rvar k)   q = cong (λ b → topR b k) q
tops-r l (rconst c) q = refl
tops-r l (ρ ·̂ᵣ ρ')  q with ∨-false (hitᵣ l ρ) (hitᵣ l ρ') q
... | q₁ , q₂ = cong₂ _·̂ᵣ_ (tops-r l ρ q₁) (tops-r l ρ' q₂)
tops-r l (ρ ⊔̂ᵣ ρ')  q with ∨-false (hitᵣ l ρ) (hitᵣ l ρ') q
... | q₁ , q₂ = cong₂ _⊔̂ᵣ_ (tops-r l ρ q₁) (tops-r l ρ' q₂)
tops-r l ∣ ε ∣̂ᵉ     q = cong ∣_∣̂ᵉ (tops-e l ε q)

tops-v : ∀ {Φ} → (l : List (Mem Φ)) → (A : OVType Φ) → hitᵥ l A ≡ false → A [ tops l ]ᵛ ≡ A
tops-c : ∀ {Φ} → (l : List (Mem Φ)) → (C : OCType Φ) → hitᶜ l C ≡ false → C [ tops l ]ᶜ ≡ C
tops-v l (tvar α)  q = refl
tops-v l (Base b)  q = refl
tops-v l Unit      q = refl
tops-v l Bool      q = refl
tops-v l Empty     q = refl
tops-v l (A |×| B) q with ∨-false (hitᵥ l A) (hitᵥ l B) q
... | q₁ , q₂ = cong₂ _|×|_ (tops-v l A q₁) (tops-v l B q₂)
tops-v l (A ⇒ C)   q with ∨-false (hitᵥ l A) (hitᶜ l C) q
... | q₁ , q₂ = cong₂ _⇒_ (tops-v l A q₁) (tops-c l C q₂)
tops-v l ([ ρ ] A) q with ∨-false (hitᵣ l ρ) (hitᵥ l A) q
... | q₁ , q₂ = cong₂ [_]_ (tops-r l ρ q₁) (tops-v l A q₂)
tops-c l (A ‼ ε)   q with ∨-false (hitᵥ l A) (hitₑ l ε) q
... | q₁ , q₂ = cong₂ _‼_ (tops-v l A q₁) (tops-e l ε q₂)

-- ... and so does a later substitution

tops-⨟e : ∀ {Φ Ψ'} → (l : List (Mem Φ)) → (τ : Subst Φ Ψ') → (ε : EExp Φ)
        → hitₑ l ε ≡ false → ε [ tops l ⨟ˢ τ ]ᵉ ≡ ε [ τ ]ᵉ
tops-⨟e l τ ε q = trans (sym ([⨟]ᵉ ε (tops l) τ)) (cong (_[ τ ]ᵉ) (tops-e l ε q))

tops-⨟r : ∀ {Φ Ψ'} → (l : List (Mem Φ)) → (τ : Subst Φ Ψ') → (ρ : RExp Φ)
        → hitᵣ l ρ ≡ false → ρ [ tops l ⨟ˢ τ ]ʳ ≡ ρ [ τ ]ʳ
tops-⨟r l τ ρ q = trans (sym ([⨟]ʳ ρ (tops l) τ)) (cong (_[ τ ]ʳ) (tops-r l ρ q))

tops-⨟v : ∀ {Φ Ψ'} → (l : List (Mem Φ)) → (τ : Subst Φ Ψ') → (A : OVType Φ)
        → hitᵥ l A ≡ false → A [ tops l ⨟ˢ τ ]ᵛ ≡ A [ τ ]ᵛ
tops-⨟v l τ A q = trans (sym ([⨟]ᵛ A (tops l) τ)) (cong (_[ τ ]ᵛ) (tops-v l A q))

-- The members occur in no image of `O`

freeᴹ : ∀ {Θ Φ} → List (Mem Φ) → Subst Θ Φ → 𝔹
freeᴹ l O = anyᶠ (λ α → hitᵥ l (sTy O α))
          ∨ (anyᶠ (λ i → hitᵣ l (sR O i)) ∨ anyᶠ (λ i → hitₑ l (sE O i)))

freeᴹ-fix : ∀ {Θ Φ} → (l : List (Mem Φ)) → (O : Subst Θ Φ) → freeᴹ l O ≡ false
          → (O ⨟ˢ tops l) ≐ˢ O
freeᴹ-fix l O q with ∨-false (anyᶠ (λ α → hitᵥ l (sTy O α))) _ q
... | qT , q' with ∨-false (anyᶠ (λ i → hitᵣ l (sR O i))) _ q'
...   | qR , qE =
        mk≐ˢ (λ α → tops-v l (sTy O α) (anyᶠ-false (λ α' → hitᵥ l (sTy O α')) qT α))
             (λ i → tops-r l (sR O i) (anyᶠ-false (λ i' → hitᵣ l (sR O i')) qR i))
             (λ i → tops-e l (sE O i) (anyᶠ-false (λ i' → hitₑ l (sE O i')) qE i))

-- Pointwise, the members sent to the top lie above, and below any
-- substitution that is at the top on them

tops-above : ∀ {Φ Ψ'} {Q : Hyps Ψ'} → (l : List (Mem Φ)) → (τ : Subst Φ Ψ')
           → Q ⊩ τ ≾ˢ (tops l ⨟ˢ τ)
tops-above {Φ} {Q = Q} l τ = mk≾ˢ (λ k → r (inᴿ k l) k) (λ k → e (inᴱ k l) k)
  where
    r : (b : 𝔹) → (k : RVar Φ) → Q ⊩ sR τ k ≾̂ᵣ topR b k [ τ ]ʳ
    r true  k = topᵣ
    r false k = ⊩≾̂ᵣ-refl

    e : (b : 𝔹) → (k : EVar Φ) → Q ⊩ sE τ k ≾̂ₑ topE b k [ τ ]ᵉ
    e true  k = topₑ
    e false k = ⊩≾̂ₑ-refl

tops-below : ∀ {Φ Ψ'} {Q : Hyps Ψ'} → (l : List (Mem Φ)) → (τ T : Subst Φ Ψ')
           → (∀ {k} → inᴱ k l ≡ true → Q ⊩ econst ⊤ₑ ≾̂ₑ sE T k)
           → (∀ {k} → inᴿ k l ≡ true → Q ⊩ rconst ⊤ᵣ ≾̂ᵣ sR T k)
           → Q ⊩ τ ≾ˢ T → Q ⊩ (tops l ⨟ˢ τ) ≾ˢ T
tops-below {Φ} {Q = Q} l τ T fe fr le =
  mk≾ˢ (λ k → r k (inᴿ k l) refl) (λ k → e k (inᴱ k l) refl)
  where
    r : (k : RVar Φ) → (b : 𝔹) → inᴿ k l ≡ b → Q ⊩ topR b k [ τ ]ʳ ≾̂ᵣ sR T k
    r k true  q = fr q
    r k false q = ≾ˢʳ le k

    e : (k : EVar Φ) → (b : 𝔹) → inᴱ k l ≡ b → Q ⊩ topE b k [ τ ]ᵉ ≾̂ₑ sE T k
    e k true  q = fe q
    e k false q = ≾ˢᵉ le k

≾ˢ-refl : ∀ {Φ Ψ'} {Q : Hyps Ψ'} {τ : Subst Φ Ψ'} → Q ⊩ τ ≾ˢ τ
≾ˢ-refl = mk≾ˢ (λ i → ⊩≾̂ᵣ-refl) (λ i → ⊩≾̂ₑ-refl)

-- The members, each reached from the rigid `j`: bounded below by an
-- expression decided to be the top once `j` and the members reached
-- before it are.

data Reach {Φ} (R : Resid Φ) (j : EVar Φ) : List (Mem Φ) → Set where
  reach[] : Reach R j []
  reachᵉ  : ∀ {k x l} → (x , evar k) ∈ es R
          → ∅ᴴ ⊩ econst ⊤ₑ ≾̂ₑ x [ tops (eᵐ j ∷ l) ]ᵉ
          → Reach R j l → Reach R j (eᵐ k ∷ l)
  reachʳ  : ∀ {k x l} → (x , rvar k) ∈ rs R
          → ∅ᴴ ⊩ rconst ⊤ᵣ ≾̂ᵣ x [ tops (eᵐ j ∷ l) ]ʳ
          → Reach R j l → Reach R j (rᵐ k ∷ l)

-- At an instance with `j` at the top, so is every member

reach-top : ∀ {Φ Ψ'} {Q : Hyps Ψ'} {R : Resid Φ} {j : EVar Φ} {l : List (Mem Φ)}
          → Reach R j l → (T : Subst Φ Ψ') → Q ⊩ᴿ R [ T ] → Q ⊩ econst ⊤ₑ ≾̂ₑ sE T j
          → (∀ {k} → inᴱ k l ≡ true → Q ⊩ econst ⊤ₑ ≾̂ₑ sE T k)
          × (∀ {k} → inᴿ k l ≡ true → Q ⊩ rconst ⊤ᵣ ≾̂ᵣ sR T k)
reach-top reach[] T h tj = (λ ()) , (λ ())
reach-top {Q = Q} {j = j} (reachᵉ {k} {x} {l} m p rc) T h tj = fe , proj₂ ih
  where
    ih = reach-top rc T h tj

    fj : ∀ {k'} → inᴱ k' (eᵐ j ∷ l) ≡ true → Q ⊩ econst ⊤ₑ ≾̂ₑ sE T k'
    fj {k'} q with ∨-true ⌊ k' ≟ᶠ j ⌋ (inᴱ k' l) q
    ... | inj₁ r = subst (λ z → Q ⊩ econst ⊤ₑ ≾̂ₑ sE T z) (sym (true-dec (k' ≟ᶠ j) r)) tj
    ... | inj₂ r = proj₁ ih r

    new : Q ⊩ econst ⊤ₑ ≾̂ₑ sE T k
    new = transₑ (subst (λ z → Q ⊩ econst ⊤ₑ ≾̂ₑ z) ([⨟]ᵉ x (tops (eᵐ j ∷ l)) T)
                        (⊩-substₑ ∅ᴴ-⊩ᴴ p))
                 (transₑ (mono-substₑ (tops-below (eᵐ j ∷ l) T T fj (proj₂ ih) ≾ˢ-refl) x)
                         (⊩es h m))

    fe : ∀ {k'} → inᴱ k' (eᵐ k ∷ l) ≡ true → Q ⊩ econst ⊤ₑ ≾̂ₑ sE T k'
    fe {k'} q with ∨-true ⌊ k' ≟ᶠ k ⌋ (inᴱ k' l) q
    ... | inj₁ r = subst (λ z → Q ⊩ econst ⊤ₑ ≾̂ₑ sE T z) (sym (true-dec (k' ≟ᶠ k) r)) new
    ... | inj₂ r = proj₁ ih r
reach-top {Q = Q} {j = j} (reachʳ {k} {x} {l} m p rc) T h tj = proj₁ ih , fr
  where
    ih = reach-top rc T h tj

    fj : ∀ {k'} → inᴱ k' (eᵐ j ∷ l) ≡ true → Q ⊩ econst ⊤ₑ ≾̂ₑ sE T k'
    fj {k'} q with ∨-true ⌊ k' ≟ᶠ j ⌋ (inᴱ k' l) q
    ... | inj₁ r = subst (λ z → Q ⊩ econst ⊤ₑ ≾̂ₑ sE T z) (sym (true-dec (k' ≟ᶠ j) r)) tj
    ... | inj₂ r = proj₁ ih r

    new : Q ⊩ rconst ⊤ᵣ ≾̂ᵣ sR T k
    new = transᵣ (subst (λ z → Q ⊩ rconst ⊤ᵣ ≾̂ᵣ z) ([⨟]ʳ x (tops (eᵐ j ∷ l)) T)
                        (⊩-substᵣ ∅ᴴ-⊩ᴴ p))
                 (transᵣ (mono-substᵣ (tops-below (eᵐ j ∷ l) T T fj (proj₂ ih) ≾ˢ-refl) x)
                         (⊩rs h m))

    fr : ∀ {k'} → inᴿ k' (rᵐ k ∷ l) ≡ true → Q ⊩ rconst ⊤ᵣ ≾̂ᵣ sR T k'
    fr {k'} q with ∨-true ⌊ k' ≟ᶠ k ⌋ (inᴿ k' l) q
    ... | inj₁ r = subst (λ z → Q ⊩ rconst ⊤ᵣ ≾̂ᵣ sR T z) (sym (true-dec (k' ≟ᶠ k) r)) new
    ... | inj₂ r = proj₂ ih r

-- An ordering whose left side mentions a member has, on its right, an
-- expression decided to be the top once the members are, or one that
-- mentions only outer unknowns other than the rigid (`O'`) and no
-- member

data UpAtₑ {Θ Φ} (O' : Subst Θ Φ) (l : List (Mem Φ)) : EExp Φ × EExp Φ → Set where
  up-free  : ∀ {x y} → hitₑ l x ≡ false → UpAtₑ O' l (x , y)
  up-top   : ∀ {x y} → ∅ᴴ ⊩ econst ⊤ₑ ≾̂ₑ y [ tops l ]ᵉ → UpAtₑ O' l (x , y)
  up-outer : ∀ {x y} → Outerₑ O' y → hitₑ l y ≡ false → UpAtₑ O' l (x , y)

data UpAtᵣ {Θ Φ} (O' : Subst Θ Φ) (l : List (Mem Φ)) : RExp Φ × RExp Φ → Set where
  up-free  : ∀ {x y} → hitᵣ l x ≡ false → UpAtᵣ O' l (x , y)
  up-top   : ∀ {x y} → ∅ᴴ ⊩ rconst ⊤ᵣ ≾̂ᵣ y [ tops l ]ʳ → UpAtᵣ O' l (x , y)
  up-outer : ∀ {x y} → Outerᵣ O' y → hitᵣ l y ≡ false → UpAtᵣ O' l (x , y)

-- The members occur in no type of the residual and in no grade of a
-- disjunction

record CleanM {Φ} (l : List (Mem Φ)) (R : Resid Φ) : Set where
  constructor cleanM
  field
    mts : ∀ {A}   → A ∈ ts R       → hitᵥ l A ≡ false
    mss : ∀ {A B} → (A , B) ∈ ss R → (hitᵥ l A ∨ hitᵥ l B) ≡ false
    mds : ∀ {A ρ} → (A , ρ) ∈ ds R → (hitᵥ l A ∨ hitᵣ l ρ) ≡ false

-- Raising the members keeps every instance entering the scope. Send the
-- eigenvariable to the top as well (`ω`): the instance stays one, the
-- hypotheses being free of it, and there every member is at the top.
-- The raised instance lies between the two.

raise-⊩ : ∀ {Θ Φ Ψ''} {Q₀ : Hyps Ψ''} {R : Resid Φ} → (O : Subst (Θ +e) Φ)
        → {j : EVar Φ} → sE O (newᵉ {Θ}) ≡ evar j → (l : List (Mem Φ)) → Reach R j l
        → (∀ {a} → a ∈ es R → UpAtₑ (wkˢᵉ {Θ} ⨟ˢ O) l a)
        → (∀ {a} → a ∈ rs R → UpAtᵣ (wkˢᵉ {Θ} ⨟ˢ O) l a)
        → CleanM l R
        → (∀ {E} → E ∈ dfs R → Still dir↑ (tops l) E)
        → (τ : Subst Φ (Ψ'' +e)) → Entry O τ
        → wkᵉ-H Q₀ ⊩ᴿ R [ τ ] → wkᵉ-H Q₀ ⊩ᴿ R [ tops l ⨟ˢ τ ]
raise-⊩ {Θ} {Ψ'' = Ψ''} {Q₀ = Q₀} {R} O {j} eqj l rc ue ur (cleanM ct cs cd) sd τ en h =
  mk⊩ᴿ rs' es' ts' ss' ds' (λ {E} m → keepᵈ dir↑ E (sd m) lo (⊩dfs h m))
  where
    Q  = wkᵉ-H Q₀
    T  = τ ⨟ˢ ω
    τ₁ = tops l ⨟ˢ τ

    hT : Q ⊩ᴿ R [ T ]
    hT = ⊩ᴿ-⨟ ⊩ᴴ-ω h

    τj : sE τ j ≡ evar (newᵉ {Ψ''})
    τj = trans (sym (cong (_[ τ ]ᵉ) eqj)) (≐ᵉ (proj₂ en) (newᵉ {Θ}))

    Tj : Q ⊩ econst ⊤ₑ ≾̂ₑ sE T j
    Tj = subst (λ z → Q ⊩ econst ⊤ₑ ≾̂ₑ z [ ω ]ᵉ) (sym τj) ⊩≾̂ₑ-refl

    tp = reach-top rc T hT Tj

    idT : Q ⊩ τ ≾ˢ T
    idT = mk≾ˢ (λ i → subst (λ z → Q ⊩ z ≾̂ᵣ sR τ i [ ω ]ʳ) ([id]ʳ (sR τ i))
                            (mono-substᵣ id≾ω (sR τ i)))
               (λ i → subst (λ z → Q ⊩ z ≾̂ₑ sE τ i [ ω ]ᵉ) ([id]ᵉ (sE τ i))
                            (mono-substₑ id≾ω (sE τ i)))

    lo : Q ⊩ τ ≾ˢ τ₁
    lo = tops-above l τ

    hi : Q ⊩ τ₁ ≾ˢ T
    hi = tops-below l τ T (proj₁ tp) (proj₂ tp) idT

    st : Agree (wkˢᵉ {Θ} ⨟ˢ O) τ ω idˢ
    st = stable-out O τ en

    es' : ∀ {x y} → (x , y) ∈ es R → Q ⊩ x [ τ₁ ]ᵉ ≾̂ₑ y [ τ₁ ]ᵉ
    es' {x} {y} m with ue m
    ... | up-free q =
          subst (λ z → Q ⊩ z ≾̂ₑ y [ τ₁ ]ᵉ) (sym (tops-⨟e l τ x q))
                (transₑ (⊩es h m) (mono-substₑ lo y))
    ... | up-top p =
          transₑ topₑ (subst (λ z → Q ⊩ econst ⊤ₑ ≾̂ₑ z) ([⨟]ᵉ y (tops l) τ)
                             (⊩-substₑ ∅ᴴ-⊩ᴴ p))
    ... | up-outer o q =
          transₑ (mono-substₑ hi x)
                 (subst (λ z → Q ⊩ x [ T ]ᵉ ≾̂ₑ z)
                        (trans (agreeₑ {O = wkˢᵉ {Θ} ⨟ˢ O} {X = τ} {σ₁ = ω} {σ₂ = idˢ} st y o)
                        (trans (sym ([⨟]ᵉ y τ idˢ))
                        (trans ([id]ᵉ (y [ τ ]ᵉ)) (sym (tops-⨟e l τ y q)))))
                        (⊩es hT m))

    rs' : ∀ {x y} → (x , y) ∈ rs R → Q ⊩ x [ τ₁ ]ʳ ≾̂ᵣ y [ τ₁ ]ʳ
    rs' {x} {y} m with ur m
    ... | up-free q =
          subst (λ z → Q ⊩ z ≾̂ᵣ y [ τ₁ ]ʳ) (sym (tops-⨟r l τ x q))
                (transᵣ (⊩rs h m) (mono-substᵣ lo y))
    ... | up-top p =
          transᵣ topᵣ (subst (λ z → Q ⊩ rconst ⊤ᵣ ≾̂ᵣ z) ([⨟]ʳ y (tops l) τ)
                             (⊩-substᵣ ∅ᴴ-⊩ᴴ p))
    ... | up-outer o q =
          transᵣ (mono-substᵣ hi x)
                 (subst (λ z → Q ⊩ x [ T ]ʳ ≾̂ᵣ z)
                        (trans (agreeᵣ {O = wkˢᵉ {Θ} ⨟ˢ O} {X = τ} {σ₁ = ω} {σ₂ = idˢ} st y o)
                        (trans (sym ([⨟]ʳ y τ idˢ))
                        (trans ([id]ʳ (y [ τ ]ʳ)) (sym (tops-⨟r l τ y q)))))
                        (⊩rs hT m))

    ts' : ∀ {A} → A ∈ ts R → Q ⊩ᴱ A [ τ₁ ]ᵛ
    ts' {A} m = subst (Q ⊩ᴱ_) (sym (tops-⨟v l τ A (ct m))) (⊩ts h m)

    ss' : ∀ {A B} → (A , B) ∈ ss R → Q ∣ A [ τ₁ ]ᵛ <:̂ᵛ B [ τ₁ ]ᵛ
    ss' {A} {B} m with ∨-false (hitᵥ l A) (hitᵥ l B) (cs m)
    ... | qA , qB = subst₂ (Q ∣_<:̂ᵛ_) (sym (tops-⨟v l τ A qA)) (sym (tops-⨟v l τ B qB))
                           (⊩ss h m)

    ds' : ∀ {A ρ} → (A , ρ) ∈ ds R → VarOK Q (A [ τ₁ ]ᵛ) (ρ [ τ₁ ]ʳ)
    ds' {A} {ρ} m with ∨-false (hitᵥ l A) (hitᵣ l ρ) (cd m)
    ... | qA , qρ = subst₂ (VarOK Q) (sym (tops-⨟v l τ A qA)) (sym (tops-⨟r l τ ρ qρ))
                           (⊩ds h m)

-- Finding the set: reach from the rigid among the candidates, drop the
-- members that break a condition, and start again

withMem : ∀ {X : Set} → (l : List X) → List (Σ[ a ∈ X ] (a ∈ l))
withMem []      = []
withMem (a ∷ l) = (a , here refl) ∷ map (λ { (b , m) → b , there m }) (withMem l)

rvar? : ∀ {Φ} → (ρ : RExp Φ) → Maybe (Σ[ k ∈ RVar Φ ] (ρ ≡ rvar k))
rvar? (rvar k)   = just (k , refl)
rvar? (rconst c) = nothing
rvar? (ρ ·̂ᵣ ρ')  = nothing
rvar? (ρ ⊔̂ᵣ ρ')  = nothing
rvar? ∣ ε ∣̂ᵉ     = nothing

upAtₑ? : ∀ {Θ Φ} → (O' : Subst Θ Φ) → (l : List (Mem Φ)) → (a : EExp Φ × EExp Φ)
       → Maybe (UpAtₑ O' l a)
upAtₑ? O' l (x , y) with isFalse (hitₑ l x)
... | just q  = just (up-free q)
... | nothing with decide≾ₑ {Q = ∅ᴴ} (econst ⊤ₑ) (y [ tops l ]ᵉ)
...   | just p  = just (up-top p)
...   | nothing with outerₑ? O' y | isFalse (hitₑ l y)
...     | just o | just q = just (up-outer o q)
...     | _      | _      = nothing

upAtᵣ? : ∀ {Θ Φ} → (O' : Subst Θ Φ) → (l : List (Mem Φ)) → (a : RExp Φ × RExp Φ)
       → Maybe (UpAtᵣ O' l a)
upAtᵣ? O' l (x , y) with isFalse (hitᵣ l x)
... | just q  = just (up-free q)
... | nothing with decide≾ᵣ {Q = ∅ᴴ} (rconst ⊤ᵣ) (y [ tops l ]ʳ)
...   | just p  = just (up-top p)
...   | nothing with outerᵣ? O' y | isFalse (hitᵣ l y)
...     | just o | just q = just (up-outer o q)
...     | _      | _      = nothing

cleanM? : ∀ {Φ} → (l : List (Mem Φ)) → (R : Resid Φ) → Maybe (CleanM l R)
cleanM? l R with allFalse (hitᵥ l) (ts R)
                | allFalse (λ { (A , B) → hitᵥ l A ∨ hitᵥ l B }) (ss R)
                | allFalse (λ { (A , ρ) → hitᵥ l A ∨ hitᵣ l ρ }) (ds R)
... | just t  | just s  | just d  = just (cleanM t s d)
... | _       | _       | _       = nothing

record Raised {Θ Φ} (O : Subst (Θ +e) Φ) (R : Resid Φ) (j : EVar Φ) : Set where
  constructor raised
  field
    mems : List (Mem Φ)
    mrch : Reach R j mems
    mupe : ∀ {a} → a ∈ es R → UpAtₑ (wkˢᵉ {Θ} ⨟ˢ O) mems a
    mupr : ∀ {a} → a ∈ rs R → UpAtᵣ (wkˢᵉ {Θ} ⨟ˢ O) mems a
    mcln : CleanM mems R
    msti : ∀ {E} → E ∈ dfs R → Still dir↑ (tops mems) E
    mfix : freeᴹ mems O ≡ false

module Find {Θ Φ} (O : Subst (Θ +e) Φ) (R : Resid Φ) (j : EVar Φ) where

  O' : Subst Θ Φ
  O' = wkˢᵉ {Θ} ⨟ˢ O

  -- a candidate reached from `j` and the members so far

  findᵉ : (EVar Φ → 𝔹) → (l : List (Mem Φ))
        → Maybe (Σ[ k ∈ EVar Φ ] Σ[ x ∈ EExp Φ ]
                   (((x , evar k) ∈ es R) × (∅ᴴ ⊩ econst ⊤ₑ ≾̂ₑ x [ tops (eᵐ j ∷ l) ]ᵉ)))
  findᵉ ok l = go (withMem (es R))
    where
      go : List (Σ[ a ∈ EExp Φ × EExp Φ ] (a ∈ es R))
         → Maybe (Σ[ k ∈ EVar Φ ] Σ[ x ∈ EExp Φ ]
                    (((x , evar k) ∈ es R) × (∅ᴴ ⊩ econst ⊤ₑ ≾̂ₑ x [ tops (eᵐ j ∷ l) ]ᵉ)))
      go []                  = nothing
      go (((x , y) , m) ∷ as) with evar? y
      ... | nothing = go as
      ... | just (k , refl) with ok k ∧ not (inᴱ k l) ∧ hitₑ (eᵐ j ∷ l) x
      ...   | false = go as
      ...   | true with decide≾ₑ {Q = ∅ᴴ} (econst ⊤ₑ) (x [ tops (eᵐ j ∷ l) ]ᵉ)
      ...     | just p  = just (k , x , m , p)
      ...     | nothing = go as

  findʳ : (RVar Φ → 𝔹) → (l : List (Mem Φ))
        → Maybe (Σ[ k ∈ RVar Φ ] Σ[ x ∈ RExp Φ ]
                   (((x , rvar k) ∈ rs R) × (∅ᴴ ⊩ rconst ⊤ᵣ ≾̂ᵣ x [ tops (eᵐ j ∷ l) ]ʳ)))
  findʳ ok l = go (withMem (rs R))
    where
      go : List (Σ[ a ∈ RExp Φ × RExp Φ ] (a ∈ rs R))
         → Maybe (Σ[ k ∈ RVar Φ ] Σ[ x ∈ RExp Φ ]
                    (((x , rvar k) ∈ rs R) × (∅ᴴ ⊩ rconst ⊤ᵣ ≾̂ᵣ x [ tops (eᵐ j ∷ l) ]ʳ)))
      go []                  = nothing
      go (((x , y) , m) ∷ as) with rvar? y
      ... | nothing = go as
      ... | just (k , refl) with ok k ∧ not (inᴿ k l) ∧ hitᵣ (eᵐ j ∷ l) x
      ...   | false = go as
      ...   | true with decide≾ᵣ {Q = ∅ᴴ} (rconst ⊤ᵣ) (x [ tops (eᵐ j ∷ l) ]ʳ)
      ...     | just p  = just (k , x , m , p)
      ...     | nothing = go as

  grow : (EVar Φ → 𝔹) → (RVar Φ → 𝔹) → ℕ → (l : List (Mem Φ)) → Reach R j l
       → Σ[ l' ∈ List (Mem Φ) ] Reach R j l'
  grow oe or nzero    l rc = l , rc
  grow oe or (nsuc n) l rc with findᵉ oe l
  ... | just (k , x , m , p) = grow oe or n (eᵐ k ∷ l) (reachᵉ m p rc)
  ... | nothing with findʳ or l
  ...   | just (k , x , m , p) = grow oe or n (rᵐ k ∷ l) (reachʳ m p rc)
  ...   | nothing              = l , rc

  -- the orderings that meet no condition

  failsₑ : List (Mem Φ) → List (EExp Φ × EExp Φ) → List (EExp Φ × EExp Φ)
  failsₑ l []       = []
  failsₑ l (a ∷ as) with upAtₑ? O' l a
  ... | just _  = failsₑ l as
  ... | nothing = a ∷ failsₑ l as

  failsᵣ : List (Mem Φ) → List (RExp Φ × RExp Φ) → List (RExp Φ × RExp Φ)
  failsᵣ l []       = []
  failsᵣ l (a ∷ as) with upAtᵣ? O' l a
  ... | just _  = failsᵣ l as
  ... | nothing = a ∷ failsᵣ l as

  -- a member is dropped when it is on the left of a failing ordering,
  -- or occurs in a type or a disjunction's grade

  badᵉ : List (Mem Φ) → EVar Φ → 𝔹
  badᵉ l k = inᴱ k l ∧ (anyL (λ { (x , _) → occᵉ-e k x }) (failsₑ l (es R))
                       ∨ anyL (λ { (x , _) → occᵉ-r k x }) (failsᵣ l (rs R))
                       ∨ anyL (occᵉ-v k) (ts R)
                       ∨ anyL (λ { (A , B) → occᵉ-v k A ∨ occᵉ-v k B }) (ss R)
                       ∨ anyL (λ { (A , ρ) → occᵉ-v k A ∨ occᵉ-r k ρ }) (ds R)
                       ∨ inDfsᵉ dir↑ k R)

  badʳ : List (Mem Φ) → RVar Φ → 𝔹
  badʳ l k = inᴿ k l ∧ (anyL (λ { (x , _) → occʳ-r k x }) (failsᵣ l (rs R))
                       ∨ anyL (occʳ-v k) (ts R)
                       ∨ anyL (λ { (A , B) → occʳ-v k A ∨ occʳ-v k B }) (ss R)
                       ∨ anyL (λ { (A , ρ) → occʳ-v k A ∨ occʳ-r k ρ }) (ds R)
                       ∨ inDfsʳ dir↑ k R)

  check : (l : List (Mem Φ)) → Reach R j l → Maybe (Raised O R j)
  check []      rc = nothing
  check (m ∷ l) rc with allOf (upAtₑ? O' (m ∷ l)) (es R) | allOf (upAtᵣ? O' (m ∷ l)) (rs R)
                      | cleanM? (m ∷ l) R | stills? dir↑ (tops (m ∷ l)) (dfs R)
                      | isFalse (freeᴹ (m ∷ l) O)
  ... | just ue | just ur | just cl | just sd | just fx = just (raised (m ∷ l) rc ue ur cl sd fx)
  ... | _       | _       | _       | _       | _       = nothing

  select : ℕ → (EVar Φ → 𝔹) → (RVar Φ → 𝔹) → Maybe (Raised O R j)
  select nzero    oe or = nothing
  select (nsuc n) oe or with grow oe or (nE Φ + nR Φ) [] reach[]
  ... | l , rc with check l rc
  ...   | just r  = just r
  ...   | nothing with anyᶠ (badᵉ l) ∨ anyᶠ (badʳ l)
  ...     | false = nothing
  ...     | true  = select n (λ k → oe k ∧ not (badᵉ l k)) (λ k → or k ∧ not (badʳ l k))

  raise? : Maybe (Raised O R j)
  raise? = select (nsuc (nE Φ + nR Φ)) (λ k → not (freeᵉ k O)) (λ k → not (freeʳ k O))

------------------------------------------------------------------------
-- Joins on a left side: an ordering whose left side has two or more
-- alternatives in normal form is one ordering per alternative, the
-- join being the least upper bound

hasJoinₑ : ∀ {Ψ} → EExp Ψ → 𝔹
hasJoinₑ (evar i)   = false
hasJoinₑ (econst c) = false
hasJoinₑ (ε ·̂ₑ ε')  = hasJoinₑ ε ∨ hasJoinₑ ε'
hasJoinₑ (ε ⊔̂ₑ ε')  = true

hasJoinᵣ : ∀ {Ψ} → RExp Ψ → 𝔹
hasJoinᵣ (rvar i)   = false
hasJoinᵣ (rconst c) = false
hasJoinᵣ (ρ ·̂ᵣ ρ')  = hasJoinᵣ ρ ∨ hasJoinᵣ ρ'
hasJoinᵣ (ρ ⊔̂ᵣ ρ')  = true
hasJoinᵣ ∣ ε ∣̂ᵉ     = hasJoinₑ ε

-- The orderings an atom is replaced by, equivalent to it at every
-- instance

record Pieces {Ψ} {X : Set} (P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set) (a : X) : Set where
  constructor pieces
  field
    parts : List X
    pback : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → (∀ {b} → b ∈ parts → P Q δ b) → P Q δ a
    pfwd  : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → P Q δ a → ∀ {b} → b ∈ parts → P Q δ b

whole : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set} {a : X} → Pieces P a
whole = pieces (_ ∷ []) (λ δ k → k (here refl)) (λ δ p → λ { (here refl) → p })

record Split {Ψ} {X : Set} (P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set) (l : List X) : Set where
  constructor split
  field
    out  : List X
    back : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
         → (∀ {b} → b ∈ out → P Q δ b) → ∀ {a} → a ∈ l → P Q δ a
    fwd  : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
         → (∀ {a} → a ∈ l → P Q δ a) → ∀ {b} → b ∈ out → P Q δ b

splits : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set}
       → ((a : X) → Pieces P a) → (l : List X) → Split P l
splits f []      = split [] (λ δ k → λ ()) (λ δ k → λ ())
splits {P = P} f (a ∷ l) = go (f a) (splits f l)
  where
    go : Pieces P a → Split P l → Split P (a ∷ l)
    go (pieces ps pb pf) (split o bk fw) =
      split (ps ++ o)
            (λ δ k → λ { (here refl) → pb δ (λ m → k (∈-++⁺ˡ m))
                       ; (there m)   → bk δ (λ m' → k (∈-++⁺ʳ ps m')) m })
            (λ δ k m → [ pf δ (k (here refl)) , fw δ (λ m' → k (there m')) ]′ (∈-++⁻ ps m))

-- The alternatives of a sum, each below the same right side

partsʳ : ∀ {Ψ} → Alts (List (RAtom Ψ)) → RExp Ψ → List (RExp Ψ × RExp Ψ)
partsʳ (alt p)  y = (⟦ p ⟧ʳᵖ , y) ∷ []
partsʳ (p ∷⁺ s) y = (⟦ p ⟧ʳᵖ , y) ∷ partsʳ s y

partsₑ : ∀ {Ψ} → Alts (List (EAtom Ψ)) → EExp Ψ → List (EExp Ψ × EExp Ψ)
partsₑ (alt p)  y = (⟦ p ⟧ᵉᵖ , y) ∷ []
partsₑ (p ∷⁺ s) y = (⟦ p ⟧ᵉᵖ , y) ∷ partsₑ s y

partsʳ-lub : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (s : Alts (List (RAtom Ψ))) → (y : RExp Ψ)
           → (∀ {b} → b ∈ partsʳ s y → Ordʳ Q δ b) → Q ⊩ ⟦ s ⟧ʳᵖ⁺ [ δ ]ʳ ≾̂ᵣ y [ δ ]ʳ
partsʳ-lub (alt p)  y k = k (here refl)
partsʳ-lub (p ∷⁺ s) y k = ⊔-lubᵣ (k (here refl)) (partsʳ-lub s y (λ m → k (there m)))

partsʳ-ub : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (s : Alts (List (RAtom Ψ))) → (y : RExp Ψ)
          → Q ⊩ ⟦ s ⟧ʳᵖ⁺ [ δ ]ʳ ≾̂ᵣ y [ δ ]ʳ → ∀ {b} → b ∈ partsʳ s y → Ordʳ Q δ b
partsʳ-ub (alt p)  y h (here refl) = h
partsʳ-ub (p ∷⁺ s) y h (here refl) = transᵣ ⊔-ubˡᵣ h
partsʳ-ub (p ∷⁺ s) y h (there m)   = partsʳ-ub s y (transᵣ ⊔-ubʳᵣ h) m

partsₑ-lub : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (s : Alts (List (EAtom Ψ))) → (y : EExp Ψ)
           → (∀ {b} → b ∈ partsₑ s y → Ordᵉ Q δ b) → Q ⊩ ⟦ s ⟧ᵉᵖ⁺ [ δ ]ᵉ ≾̂ₑ y [ δ ]ᵉ
partsₑ-lub (alt p)  y k = k (here refl)
partsₑ-lub (p ∷⁺ s) y k = ⊔-lubₑ (k (here refl)) (partsₑ-lub s y (λ m → k (there m)))

partsₑ-ub : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (s : Alts (List (EAtom Ψ))) → (y : EExp Ψ)
          → Q ⊩ ⟦ s ⟧ᵉᵖ⁺ [ δ ]ᵉ ≾̂ₑ y [ δ ]ᵉ → ∀ {b} → b ∈ partsₑ s y → Ordᵉ Q δ b
partsₑ-ub (alt p)  y h (here refl) = h
partsₑ-ub (p ∷⁺ s) y h (here refl) = transₑ ⊔-ubˡₑ h
partsₑ-ub (p ∷⁺ s) y h (there m)   = partsₑ-ub s y (transₑ ⊔-ubʳₑ h) m

-- An ordering is split where its left side has a join and more than
-- one alternative, and is otherwise kept as it is

piecesʳ : ∀ {Ψ} → (a : RExp Ψ × RExp Ψ) → Pieces Ordʳ a
piecesʳ (x , y) with hasJoinᵣ x
... | false = whole
... | true  = go (nrmᵣ x) (nrmᵣ-≡ᵖ x)
  where
    go : (s : Alts (List (RAtom _))) → x ≡̂ᵣ ⟦ s ⟧ʳᵖ⁺ → Pieces Ordʳ (x , y)
    go (alt p)    e = whole
    go s@(_ ∷⁺ _) e =
      pieces (partsʳ s y)
             (λ δ k → transᵣ (eqᵣ (≡̂ᵣ-subst δ e)) (partsʳ-lub s y k))
             (λ δ h → partsʳ-ub s y (transᵣ (eqᵣ (≡̂ᵣ-sym (≡̂ᵣ-subst δ e))) h))

piecesᵉ : ∀ {Ψ} → (a : EExp Ψ × EExp Ψ) → Pieces Ordᵉ a
piecesᵉ (x , y) with hasJoinₑ x
... | false = whole
... | true  = go (nrmₑ x) (nrmₑ-≡ᵖ x)
  where
    go : (s : Alts (List (EAtom _))) → x ≡̂ₑ ⟦ s ⟧ᵉᵖ⁺ → Pieces Ordᵉ (x , y)
    go (alt p)    e = whole
    go s@(_ ∷⁺ _) e =
      pieces (partsₑ s y)
             (λ δ k → transₑ (eqₑ (≡̂ₑ-subst δ e)) (partsₑ-lub s y k))
             (λ δ h → partsₑ-ub s y (transₑ (eqₑ (≡̂ₑ-sym (≡̂ₑ-subst δ e))) h))

------------------------------------------------------------------------
-- Unknowns that bound each other: along a chain of orderings whose
-- sides are whole unknowns, each is below the next at every instance
-- satisfying them

-- Equality of indices as a boolean, for the searches that need no
-- proof of it

_==ᶠ_ : ∀ {n} → Fin n → Fin n → 𝔹
zero  ==ᶠ zero  = true
suc i ==ᶠ suc j = i ==ᶠ j
zero  ==ᶠ suc j = false
suc i ==ᶠ zero  = false

module Chains {V : Set} (_≟_ : Decidable (_≡_ {A = V})) (_==_ : V → V → 𝔹)
              (Edge : V → V → Set) (E : List (Σ[ a ∈ V ] Σ[ b ∈ V ] Edge a b)) where

  data Chain : V → V → Set where
    done : ∀ {a} → Chain a a
    link : ∀ {a b c} → Edge a b → Chain b c → Chain a c

  snoc : ∀ {a b c} → Chain a b → Edge b c → Chain a c
  snoc done        e = link e done
  snoc (link e' c) e = link e' (snoc c e)

  fold : ∀ {Rel : V → V → Set} → (∀ {a} → Rel a a)
       → (∀ {a b c} → Edge a b → Rel b c → Rel a c) → ∀ {a b} → Chain a b → Rel a b
  fold r t done       = r
  fold r t (link e c) = t e (fold r t c)

  lookupᶜ : ∀ {P : V → Set} → (v : V) → List (Σ[ w ∈ V ] P w) → Maybe (P v)
  lookupᶜ v []            = nothing
  lookupᶜ v ((w , p) ∷ l) with v == w
  ... | false = lookupᶜ v l
  ... | true with v ≟ w
  ...   | yes refl = just p
  ...   | no _     = lookupᶜ v l

  known : ∀ {P : V → Set} → V → List (Σ[ w ∈ V ] P w) → 𝔹
  known v l = anyL (λ { (w , _) → v == w }) l

  -- the unknowns reached from `a`, and those reaching it, each with a
  -- chain: one more is added while an ordering leads to (from) one
  -- not yet found

  nextFrom : ∀ {a} → List (Σ[ w ∈ V ] Chain a w) → Maybe (Σ[ w ∈ V ] Chain a w)
  nextFrom {a} S = go E
    where
      go : List (Σ[ u ∈ V ] Σ[ w ∈ V ] Edge u w) → Maybe (Σ[ w ∈ V ] Chain a w)
      go []               = nothing
      go ((u , w , e) ∷ l) with known w S
      ... | true  = go l
      ... | false with lookupᶜ u S
      ...   | just c  = just (w , snoc c e)
      ...   | nothing = go l

  nextTo : ∀ {a} → List (Σ[ w ∈ V ] Chain w a) → Maybe (Σ[ w ∈ V ] Chain w a)
  nextTo {a} S = go E
    where
      go : List (Σ[ u ∈ V ] Σ[ w ∈ V ] Edge u w) → Maybe (Σ[ w ∈ V ] Chain w a)
      go []               = nothing
      go ((u , w , e) ∷ l) with known u S
      ... | true  = go l
      ... | false with lookupᶜ w S
      ...   | just c  = just (u , link e c)
      ...   | nothing = go l

  growFrom : ∀ {a} → ℕ → List (Σ[ w ∈ V ] Chain a w) → List (Σ[ w ∈ V ] Chain a w)
  growFrom nzero    S = S
  growFrom (nsuc n) S with nextFrom S
  ... | just x  = growFrom n (x ∷ S)
  ... | nothing = S

  growTo : ∀ {a} → ℕ → List (Σ[ w ∈ V ] Chain w a) → List (Σ[ w ∈ V ] Chain w a)
  growTo nzero    S = S
  growTo (nsuc n) S with nextTo S
  ... | just x  = growTo n (x ∷ S)
  ... | nothing = S

  -- each ordering adds at most one

  size : ℕ
  size = go E
    where
      go : List (Σ[ u ∈ V ] Σ[ w ∈ V ] Edge u w) → ℕ
      go []      = nzero
      go (_ ∷ l) = nsuc (go l)

  reachFrom : (a : V) → List (Σ[ w ∈ V ] Chain a w)
  reachFrom a = growFrom size ((a , done) ∷ [])

  reachTo : (a : V) → List (Σ[ w ∈ V ] Chain w a)
  reachTo a = growTo size ((a , done) ∷ [])

  source : V → 𝔹
  source v = anyL (λ { (u , _ , _) → u == v }) E

-- The orderings between two whole unknowns

edgesᵉ : ∀ {Ψ} → (l : List (EExp Ψ × EExp Ψ))
       → List (Σ[ a ∈ EVar Ψ ] Σ[ b ∈ EVar Ψ ] ((evar a , evar b) ∈ l))
edgesᵉ {Ψ} l = go (withMem l)
  where
    go : List (Σ[ p ∈ EExp Ψ × EExp Ψ ] (p ∈ l))
       → List (Σ[ a ∈ EVar Ψ ] Σ[ b ∈ EVar Ψ ] ((evar a , evar b) ∈ l))
    go []                  = []
    go (((x , y) , m) ∷ ps) with evar? x | evar? y
    ... | just (a , refl) | just (b , refl) = (a , b , m) ∷ go ps
    ... | _               | _               = go ps

edgesʳ : ∀ {Ψ} → (l : List (RExp Ψ × RExp Ψ))
       → List (Σ[ a ∈ RVar Ψ ] Σ[ b ∈ RVar Ψ ] ((rvar a , rvar b) ∈ l))
edgesʳ {Ψ} l = go (withMem l)
  where
    go : List (Σ[ p ∈ RExp Ψ × RExp Ψ ] (p ∈ l))
       → List (Σ[ a ∈ RVar Ψ ] Σ[ b ∈ RVar Ψ ] ((rvar a , rvar b) ∈ l))
    go []                  = []
    go (((x , y) , m) ∷ ps) with rvar? x | rvar? y
    ... | just (a , refl) | just (b , refl) = (a , b , m) ∷ go ps
    ... | _               | _               = go ps

-- The orderings that may lie on a cycle: while one has a smaller side
-- that is no greater side, or a greater side that is no smaller side,
-- it is dropped

cyclic : ∀ {V : Set} {Edge : V → V → Set} → (V → V → 𝔹)
       → List (Σ[ a ∈ V ] Σ[ b ∈ V ] Edge a b) → List (Σ[ a ∈ V ] Σ[ b ∈ V ] Edge a b)
cyclic {V} {Edge} _==_ l₀ = go l₀ l₀
  where
    T : Set
    T = Σ[ a ∈ V ] Σ[ b ∈ V ] Edge a b

    into : List T → V → 𝔹
    into l v = anyL (λ { (_ , b , _) → b == v }) l

    outOf : List T → V → 𝔹
    outOf l v = anyL (λ { (a , _ , _) → a == v }) l

    pass : List T → List T × 𝔹
    pass l = sweep l
      where
        sweep : List T → List T × 𝔹
        sweep []                  = [] , false
        sweep (e@(a , b , _) ∷ r) with into l a ∧ outOf l b | sweep r
        ... | true  | r' , d = e ∷ r' , d
        ... | false | r' , d = r' , true

    go : List T → List T → List T
    go []      l = l
    go (_ ∷ f) l with pass l
    ... | l' , true  = go f l'
    ... | l' , false = l'

-- A deferred condition survives a substitution equivalent to the one
-- it moves

keep⇕ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {σ : Subst Ψ Ψ} {τ : Subst Ψ Ψ'} → (E : Dfr Ψ)
      → Q ⊩ (σ ⨟ˢ τ) ≾ˢ τ → Q ⊩ τ ≾ˢ (σ ⨟ˢ τ) → Q ⊩ᵈ E [ τ ] → Q ⊩ᵈ E [ σ ⨟ˢ τ ]
keep⇕ (dfr l k o) le ge h =
  mk⊩ᵒ (λ {x} {y} m → transᵣ (mono-substᵣ (≾ˢ-↑ᵉⁿ k le) x)
                             (transᵣ (⊩ors h m) (mono-substᵣ (≾ˢ-↑ᵉⁿ k ge) y)))
       (λ {x} {y} m → transₑ (mono-substₑ (≾ˢ-↑ᵉⁿ k le) x)
                             (transₑ (⊩oes h m) (mono-substₑ (≾ˢ-↑ᵉⁿ k ge) y)))

-- Sending an unknown to one equal to it at an instance keeps the
-- instance: every grade former is monotone, so each side moves by as
-- little in either direction

collapseᵉ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k r : EVar Ψ} {R : Resid Ψ}
            → Cleanᵉ k R → (τ : Subst Ψ Ψ') → Q ⊩ᴿ R [ τ ]
            → Q ⊩ sE τ k ≾̂ₑ sE τ r → Q ⊩ sE τ r ≾̂ₑ sE τ k
            → Q ⊩ᴿ R [ updᵉ k (evar r) ⨟ˢ τ ]
collapseᵉ-⊩ {Q = Q} {k} {r} {R} cl τ h kr rk =
  mk⊩ᴿ rs' es' (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c)) (λ {E} m → keep⇕ {σ = updᵉ k (evar r)} E le ge (⊩dfs h m))
  where
    τ₁ = updᵉ k (evar r) ⨟ˢ τ

    le : Q ⊩ τ₁ ≾ˢ τ
    le = updᵉ-below k (evar r) τ rk

    ge : Q ⊩ τ ≾ˢ τ₁
    ge = updᵉ-above k (evar r) τ kr

    c = cleanᵉ-⊩ cl (evar r) τ h (λ {A} {ρ} m → mono-substᵣ le ρ)

    es' : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ τ₁ ]ᵉ ≾̂ₑ ε' [ τ₁ ]ᵉ
    es' {ε} {ε'} m = transₑ (mono-substₑ le ε) (transₑ (⊩es h m) (mono-substₑ ge ε'))

    rs' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ τ₁ ]ʳ ≾̂ᵣ ρ' [ τ₁ ]ʳ
    rs' {ρ} {ρ'} m = transᵣ (mono-substᵣ le ρ) (transᵣ (⊩rs h m) (mono-substᵣ ge ρ'))

collapseʳ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k r : RVar Ψ} {R : Resid Ψ}
            → Cleanʳ k R → (τ : Subst Ψ Ψ') → Q ⊩ᴿ R [ τ ]
            → Q ⊩ sR τ k ≾̂ᵣ sR τ r → Q ⊩ sR τ r ≾̂ᵣ sR τ k
            → Q ⊩ᴿ R [ updʳ k (rvar r) ⨟ˢ τ ]
collapseʳ-⊩ {Q = Q} {k} {r} {R} cl τ h kr rk =
  mk⊩ᴿ rs' es' (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c)) (λ {E} m → keep⇕ {σ = updʳ k (rvar r)} E le ge (⊩dfs h m))
  where
    τ₁ = updʳ k (rvar r) ⨟ˢ τ

    le : Q ⊩ τ₁ ≾ˢ τ
    le = updʳ-below k (rvar r) τ rk

    ge : Q ⊩ τ ≾ˢ τ₁
    ge = updʳ-above k (rvar r) τ kr

    c = cleanʳ-⊩ cl (rvar r) τ h (λ {A} {ρ} m → mono-substᵣ le ρ)

    rs' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ τ₁ ]ʳ ≾̂ᵣ ρ' [ τ₁ ]ʳ
    rs' {ρ} {ρ'} m = transᵣ (mono-substᵣ le ρ) (transᵣ (⊩rs h m) (mono-substᵣ ge ρ'))

    es' : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ τ₁ ]ᵉ ≾̂ₑ ε' [ τ₁ ]ᵉ
    es' {ε} {ε'} m =
      subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym (updʳ-⨟e k (rvar r) τ ε)) (sym (updʳ-⨟e k (rvar r) τ ε'))
             (⊩es h m)

-- A local unknown and another it bounds each other with: the other is
-- an outer unknown where one is in the cycle, else the least local.
-- The local one is absent from every type.

module _ {Θ Φ} (O : Subst (Θ +e) Φ) where

  Collapseᵉ : Resid Φ → Set
  Collapseᵉ R = Σ[ k ∈ EVar Φ ] Σ[ r ∈ EVar Φ ] ((freeᵉ k O ≡ false) × Keeps (updᵉ k (evar r)) R)

  Collapseʳ : Resid Φ → Set
  Collapseʳ R = Σ[ k ∈ RVar Φ ] Σ[ r ∈ RVar Φ ] ((freeʳ k O ≡ false) × Keeps (updʳ k (rvar r)) R)

  -- the candidates for the other, among the unknowns with an ordering
  -- above them: outer unknowns first, each by index

  keepL : ∀ {X : Set} → (X → 𝔹) → List X → List X
  keepL f []      = []
  keepL f (x ∷ l) with f x
  ... | true  = x ∷ keepL f l
  ... | false = keepL f l

  outerFirst : ∀ {X : Set} → (X → 𝔹) → List X → List X
  outerFirst {X} f l = go (map (λ x → x , f x) l)
    where
      go : List (X × 𝔹) → List X
      go ps = map proj₁ (keepL proj₂ ps) ++ map proj₁ (keepL (λ p → not (proj₂ p)) ps)

  collapseᵉ? : (R : Resid Φ) → Maybe (Collapseᵉ R)
  collapseᵉ? R = start (cyclic _==ᶠ_ (edgesᵉ (es R)))
    where
      start : List (Σ[ a ∈ EVar Φ ] Σ[ b ∈ EVar Φ ] ((evar a , evar b) ∈ es R))
            → Maybe (Collapseᵉ R)
      start []      = nothing
      start E@(_ ∷ _) =
        over (outerFirst (λ r → freeᵉ r O) (map proj₁ (misses (λ r → not (source r)))))
        where
          open Chains _≟ᶠ_ _==ᶠ_ (λ a b → (evar a , evar b) ∈ es R) E

          below : ∀ {Ψ'} {Q : Hyps Ψ'} {τ : Subst Φ Ψ'} → Q ⊩ᴿ R [ τ ]
                → ∀ {a b} → Chain a b → Q ⊩ sE τ a ≾̂ₑ sE τ b
          below h = fold ⊩≾̂ₑ-refl (λ m p → transₑ (⊩es h m) p)

          pick : (r : EVar Φ) → List (Σ[ w ∈ EVar Φ ] Chain w r)
               → List (Σ[ w ∈ EVar Φ ] Chain r w) → Maybe (Collapseᵉ R)
          pick r B []             = nothing
          pick r B ((k , c) ∷ ks) with k ==ᶠ r
          ... | true  = pick r B ks
          ... | false with lookupᶜ k B
          ...   | nothing = pick r B ks
          ...   | just c' with isFalse (freeᵉ k O)
          ...     | nothing = pick r B ks
          ...     | just q with cleanᵉ? k R
          ...       | nothing = pick r B ks
          ...       | just cl =
                      just (k , r , q , λ τ Q h → collapseᵉ-⊩ cl τ h (below h c') (below h c))

          over : List (EVar Φ) → Maybe (Collapseᵉ R)
          over []      = nothing
          over (r ∷ l) = first (pick r (reachTo r) (reachFrom r)) (over l)

  collapseʳ? : (R : Resid Φ) → Maybe (Collapseʳ R)
  collapseʳ? R = start (cyclic _==ᶠ_ (edgesʳ (rs R)))
    where
      start : List (Σ[ a ∈ RVar Φ ] Σ[ b ∈ RVar Φ ] ((rvar a , rvar b) ∈ rs R))
            → Maybe (Collapseʳ R)
      start []      = nothing
      start E@(_ ∷ _) =
        over (outerFirst (λ r → freeʳ r O) (map proj₁ (misses (λ r → not (source r)))))
        where
          open Chains _≟ᶠ_ _==ᶠ_ (λ a b → (rvar a , rvar b) ∈ rs R) E

          below : ∀ {Ψ'} {Q : Hyps Ψ'} {τ : Subst Φ Ψ'} → Q ⊩ᴿ R [ τ ]
                → ∀ {a b} → Chain a b → Q ⊩ sR τ a ≾̂ᵣ sR τ b
          below h = fold ⊩≾̂ᵣ-refl (λ m p → transᵣ (⊩rs h m) p)

          pick : (r : RVar Φ) → List (Σ[ w ∈ RVar Φ ] Chain w r)
               → List (Σ[ w ∈ RVar Φ ] Chain r w) → Maybe (Collapseʳ R)
          pick r B []             = nothing
          pick r B ((k , c) ∷ ks) with k ==ᶠ r
          ... | true  = pick r B ks
          ... | false with lookupᶜ k B
          ...   | nothing = pick r B ks
          ...   | just c' with isFalse (freeʳ k O)
          ...     | nothing = pick r B ks
          ...     | just q with cleanʳ? k R
          ...       | nothing = pick r B ks
          ...       | just cl =
                      just (k , r , q , λ τ Q h → collapseʳ-⊩ cl τ h (below h c') (below h c))

          over : List (RVar Φ) → Maybe (Collapseʳ R)
          over []      = nothing
          over (r ∷ l) = first (pick r (reachTo r) (reachFrom r)) (over l)

------------------------------------------------------------------------
-- Localisation: the steps iterated over the local unknowns, the
-- settled atoms dropped around every round

record Localised {Θ Φ} (O : Subst (Θ +e) Φ) (R : Resid Φ) : Set where
  constructor loc
  field
    lσ   : Subst Φ Φ
    lR   : Resid Φ
    lfix : (O ⨟ˢ lσ) ≐ˢ O
    lsnd : ∀ {Ψ'} → (δ : Subst Φ Ψ') → (Q : Hyps Ψ') → Q ⊩ᴿ lR [ δ ] → Q ⊩ᴿ R [ lσ ⨟ˢ δ ]
    lcpl : ∀ {Ψ''} → (τ : Subst Φ (Ψ'' +e)) → Entry O τ
         → ∅ᴴ ⊩ᴿ R [ τ ] → ∅ᴴ ⊩ᴿ lR [ τ ]
    latom : Atomicˢ (ss R) → Atomicˢ (ss lR)

open Localised public

-- A step that keeps the instances entering the scope

KeepsAt : ∀ {Θ Φ} → Subst (Θ +e) Φ → Subst Φ Φ → Resid Φ → Set
KeepsAt {Φ = Φ} O σ R = ∀ {Ψ''} → (τ : Subst Φ (Ψ'' +e)) → Entry O τ
                      → ∅ᴴ ⊩ᴿ R [ τ ] → ∅ᴴ ⊩ᴿ R [ σ ⨟ˢ τ ]

-- Nothing assigned

loc-id : ∀ {Θ Φ} {O : Subst (Θ +e) Φ} {R : Resid Φ} → Localised O R
loc-id {O = O} {R} =
  loc idˢ R (⨟-idʳ O) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) h) (λ τ en h → h) (λ a → a)

-- The settled atoms dropped, and each disjunction whose type is never
-- eternal replaced by its grade side: the instances from no
-- hypotheses are unchanged

loc-settle : ∀ {Θ Φ} {O : Subst (Θ +e) Φ} {R : Resid Φ} → Localised O R → Localised O R
loc-settle (loc σ R₀ fx sn cp la) =
  loc σ (resid (Unsettled.kept Uʳ ++ Refined.ords F) (Unsettled.kept Uᵉ) (ts R₀) (ss R₀)
               (Refined.rest F) (dfs R₀)) fx
      (λ δ Q h → sn δ Q (mk⊩ᴿ (Unsettled.back Uʳ δ (λ m → ⊩rs h (∈-++⁺ˡ m)))
                              (Unsettled.back Uᵉ δ (⊩es h)) (⊩ts h) (⊩ss h)
                              (Unsettled.back Uᵈ δ
                                (Refined.back F δ (⊩ds h)
                                  (λ m → ⊩rs h (∈-++⁺ʳ (Unsettled.kept Uʳ) m))))
                              (⊩dfs h)))
      (λ τ en h → let h' = cp τ en h in
                 mk⊩ᴿ (λ m → [ (λ m' → ⊩rs h' (Unsettled.kept⊆ Uʳ m'))
                             , Refined.fwd F τ (λ m' → ⊩ds h' (Unsettled.kept⊆ Uᵈ m')) ]′
                               (∈-++⁻ (Unsettled.kept Uʳ) m))
                      (λ m → ⊩es h' (Unsettled.kept⊆ Uᵉ m))
                      (⊩ts h') (⊩ss h')
                      (λ m → ⊩ds h' (Unsettled.kept⊆ Uᵈ (Refined.rest⊆ F m)))
                      (⊩dfs h'))
      la
  where
    Uʳ = unsettled settledʳ (rs R₀)
    Uᵉ = unsettled settledᵉ (es R₀)
    Uᵈ = unsettled settledᵈ (ds R₀)
    F  = refine (Unsettled.kept Uᵈ)

-- Whether a left side has a join

joined : ∀ {Ψ} → Resid Ψ → 𝔹
joined R = anyL (λ { (x , _) → hasJoinᵣ x }) (rs R) ∨ anyL (λ { (x , _) → hasJoinₑ x }) (es R)

-- Each ordering with a join of alternatives on its left replaced by
-- one ordering per alternative: the instances are unchanged

loc-joins : ∀ {Θ Φ} {O : Subst (Θ +e) Φ} {R : Resid Φ} → Localised O R → Localised O R
loc-joins (loc σ R₀ fx sn cp la) =
  loc σ (resid (Split.out Sʳ) (Split.out Sᵉ) (ts R₀) (ss R₀) (ds R₀) (dfs R₀)) fx
      (λ δ Q h → sn δ Q (mk⊩ᴿ (Split.back Sʳ δ (⊩rs h)) (Split.back Sᵉ δ (⊩es h))
                              (⊩ts h) (⊩ss h) (⊩ds h) (⊩dfs h)))
      (λ τ en h → let h' = cp τ en h in
                 mk⊩ᴿ (Split.fwd Sʳ τ (⊩rs h')) (Split.fwd Sᵉ τ (⊩es h'))
                      (⊩ts h') (⊩ss h') (⊩ds h') (⊩dfs h'))
      la
  where
    Sʳ = splits piecesʳ (rs R₀)
    Sᵉ = splits piecesᵉ (es R₀)

loc-ext : ∀ {Θ Φ} {O : Subst (Θ +e) Φ} {R : Resid Φ} → (L : Localised O R)
        → (σ : Subst Φ Φ) → (O ⨟ˢ σ) ≐ˢ O → KeepsAt O σ (lR L)
        → (∀ α → sTy σ α ≡ tvar α) → Localised O R
loc-ext {O = O} {R} (loc σ₀ R₀ fx sn cp la) σ fσ st ty =
  loc (σ₀ ⨟ˢ σ) (R₀ [ σ ]ᴿ)
      (≐ˢ-trans (≐ˢ-sym (⨟-assoc O σ₀ σ)) (≐ˢ-trans (⨟-congˡ fx σ) fσ))
      (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-assoc σ₀ σ δ)) (sn (σ ⨟ˢ δ) Q (⊩ᴿ-subst h)))
      (λ τ en h → ⊩ᴿ-subst⁻ (st τ en (cp τ en h)))
      (λ a → atomic-subst σ ty (la a))

module _ {Θ Φ} (O : Subst (Θ +e) Φ) (R : Resid Φ) where

  passᵉ : List (Σ[ k ∈ EVar Φ ] (freeᵉ k O ≡ false)) → Localised O R → Localised O R × 𝔹
  passᵉ []             L = L , false
  passᵉ ((k , q) ∷ ks) L with stepᵉ k (lR L)
  ... | nothing      = passᵉ ks L
  ... | just (b , st) = proj₁ (passᵉ ks (loc-ext L (updᵉ k b) (freeᵉ-fix k O q b) (λ τ en → st τ ∅ᴴ) (λ α → refl))) , true

  passʳ : List (Σ[ k ∈ RVar Φ ] (freeʳ k O ≡ false)) → Localised O R → Localised O R × 𝔹
  passʳ []             L = L , false
  passʳ ((k , q) ∷ ks) L with stepʳ k (lR L)
  ... | nothing      = passʳ ks L
  ... | just (b , st) = proj₁ (passʳ ks (loc-ext L (updʳ k b) (freeʳ-fix k O q b) (λ τ en → st τ ∅ᴴ) (λ α → refl))) , true

  -- Local unknowns bounding each other identified, one at a time

  collapseᵉL : ℕ → Localised O R → Localised O R × 𝔹
  collapseᵉL nzero    L = L , false
  collapseᵉL (nsuc n) L with collapseᵉ? O (lR L)
  ... | nothing              = L , false
  ... | just (k , r , q , st) =
        proj₁ (collapseᵉL n (loc-ext L (updᵉ k (evar r)) (freeᵉ-fix k O q (evar r))
                                     (λ τ en → st τ ∅ᴴ) (λ α → refl))) , true

  collapseʳL : ℕ → Localised O R → Localised O R × 𝔹
  collapseʳL nzero    L = L , false
  collapseʳL (nsuc n) L with collapseʳ? O (lR L)
  ... | nothing              = L , false
  ... | just (k , r , q , st) =
        proj₁ (collapseʳL n (loc-ext L (updʳ k (rvar r)) (freeʳ-fix k O q (rvar r))
                                     (λ τ en → st τ ∅ᴴ) (λ α → refl))) , true

  -- Where no unknown has a principal value of its own, a set of them
  -- bounded below by the rigid is sent to the top

  raiseL : Localised O R → Maybe (Localised O R)
  raiseL L with evar? (sE O (newᵉ {Θ}))
  ... | nothing        = nothing
  ... | just (j , eqj) with Find.raise? O (lR L) j
  ...   | nothing = nothing
  ...   | just (raised l rc ue ur cl sd fx) =
          just (loc-ext L (tops l) (freeᴹ-fix l O fx)
                        (λ τ en h → raise-⊩ {Q₀ = ∅ᴴ} O eqj l rc ue ur cl sd τ en h)
                        (λ α → refl))

  -- A round splits the joins on left sides, identifies the unknowns in
  -- cycles, then gives values. Each round that changes something
  -- settles an unknown for good, so as many rounds as there are
  -- unknowns reach the fixed point.

  rounds : ℕ → Localised O R → Localised O R
  rounds nzero    L = L
  rounds (nsuc n) L = cycles (collapseᵉL (nE Φ) (resettle (joined (lR L)) (loc-joins L)))
    where
      resettle : 𝔹 → Localised O R → Localised O R
      resettle true  L' = loc-settle L'
      resettle false L' = L'

      next₂ : Localised O R × 𝔹 → Localised O R
      next₂ (L' , true)  = rounds n (loc-settle L')
      next₂ (L' , false) with raiseL L'
      ... | just L'' = rounds n (loc-settle L'')
      ... | nothing  = L'

      next : Localised O R × 𝔹 → Localised O R
      next (L' , changed) with passʳ (misses (λ k → freeʳ k O)) L'
      ... | L'' , changed' = next₂ (L'' , (changed ∨ changed'))

      values : Localised O R × 𝔹 → Localised O R
      values (L' , changed) with passᵉ (misses (λ k → freeᵉ k O)) L'
      ... | L'' , changed' = next (L'' , (changed ∨ changed'))

      cycles : Localised O R × 𝔹 → Localised O R
      cycles (L' , changed) with collapseʳL (nR Φ) L'
      ... | L'' , changed' = values (L'' , (changed ∨ changed'))

localise : ∀ {Θ Φ} → (O : Subst (Θ +e) Φ) → (R : Resid Φ) → Localised O R
localise {Φ = Φ} O R = loc-settle (rounds O R (nE Φ + nR Φ) (loc-settle loc-id))

-- After localisation, the type of each disjunction left is eternal at
-- some instance

localise-ds : ∀ {Θ Φ} → (O : Subst (Θ +e) Φ) → (R : Resid Φ)
            → ∀ {A ρ} → (A , ρ) ∈ ds (lR (localise O R))
            → Σ[ αs ∈ List (TyVar Φ) ] (etDec A ≡ just αs)
localise-ds {Φ = Φ} O R =
  Refined.restᴱ (refine (Unsettled.kept (unsettled settledᵈ (ds (lR (rounds O R (nE Φ + nR Φ) (loc-settle loc-id)))))))

-- An assignment the later substitution already agrees with is absorbed

updᵉ-absorb : ∀ {Ψ Ψ'} → (k : EVar Ψ) → (b : EExp Ψ) → (Y : Subst Ψ Ψ')
            → sE Y k ≡ b [ Y ]ᵉ → (updᵉ k b ⨟ˢ Y) ≐ˢ Y
updᵉ-absorb {Ψ} k b Y q = mk≐ˢ (λ α → refl) (λ i → refl) e
  where
    e : (i : EVar Ψ) → sE (updᵉ k b) i [ Y ]ᵉ ≡ sE Y i
    e i with i ≟ᶠ k
    ... | yes refl = sym q
    ... | no _     = refl
