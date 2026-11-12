------------------------------------------------------------------
-- Values for the unknowns local to a rigid scope               --
--                                                              --
-- An unknown is local to a scope when no image of the unknowns --
-- the scope was entered with mentions it; the rigid never is.  --
-- A round writes the atoms in normal form (`loc-normal`),      --
-- identifies each cycle of whole unknowns (`collapse`), and    --
-- sends each local unknown a rule of `Values` applies to to    --
-- its value: the join of its lower bounds, an upper bound,     --
-- the unit, or the top. Where none applies, a set reached      --
-- from the rigid goes to the top (`raiseL`). Settled atoms     --
-- are dropped around every round (`loc-settle`).               --
--                                                              --
-- Contract (`Localised`): outer unknowns are fixed (`lfix`), a --
-- discharge of the new residual is one of the old (`lsnd`), an --
-- instance entering the scope keeps discharging it (`lcpl`),   --
-- and atomic subtyping demands stay atomic (`latom`). The      --
-- lowering values are principal (`LowToₑ`, `LowToᵣ`); the      --
-- others only keep instances. A local unknown no step          --
-- resolves leaves the scope stuck, as `a` in                   --
-- `j · a ≾ a ≾ c · j`, `j` the rigid and `c` outer.            --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; _∧_; not; true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as Maybe
open import Data.Maybe using (Is-just; to-witness)
open import Data.Nat.Base using (ℕ; _+_) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; fold) renaming (ε to ε⋆)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Grades.Base
open import Grades.Hints using (SystemHints; module SystemHintsInterface)
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.SolverImpl.Localise
  (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S))
  where

open LanguageSpec S
open GradeSystemInterface Grades
open SystemHintsInterface hints

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses               S

open import PolymorphicCalculus.Inference.SolverImpl.Core.Occurs S
  using (occᵉ-e; occᵉ-r; occᵉ-v; occᵉ-c; occʳ-r; occʳ-v; occʳ-c)
open import PolymorphicCalculus.Inference.SolverImpl.Core.Rigid S
  using (∨-true; ∨-left; ∨-right; dec-true; true-dec)

open import PolymorphicCalculus.Inference.SolverImpl.Deferred  S hints
  using (≾ˢ-↑ᵉⁿ; Dir; dir↓; dir↑; Still; stills?; keepᵈ; allOf; κ⟨_⟩; wk-κ; κ-wkᵛ; κ-wkʳ; κ-wkᵉ; ⊩ᴴ-κ)
open import PolymorphicCalculus.Inference.SolverImpl.Resid  S
open import PolymorphicCalculus.Inference.SolverImpl.Values S hints
  using (module Vᵉ; module Vʳ; module Vⁱ; isFalse; equal-keeps; updᵉ-e; updᵉ-r; updʳ-r;
         joinₑ; joinᵣ; joinₑ-ub⊩; joinₑ-lub⊩; joinᵣ-ub⊩; joinᵣ-lub⊩; module LowToₑ; module LowToᵣ)
open import PolymorphicCalculus.Inference.SolverImpl.Vars      S
  using (Vars; vᵉ; vʳ; Fixes; mkFixes; fvᵛ; fvʳ; fvᵉ; ⊆-refl; fix-v; fix-r; fix-e)
import PolymorphicCalculus.Inference.SolverImpl.Reach as Reachability
open import PolymorphicCalculus.Inference.SolverImpl.Entail S hints using (decideᵣ; decideₑ; full)
open import PolymorphicCalculus.Inference.SolverImpl.Canon  S hints
  using (canonᵣ; canonᵣ-≡; Ordʳ; Ordᵉ; Pieces; pieces; Split; splits; piecesʳ; piecesᵉ)

-- Equal unknowns, joined by the empty chain

sameᶠ? : ∀ {n} {E : Fin n → Fin n → Set} → (a b : Fin n) → Maybe (Star E a b)
sameᶠ? a b with a ≟ᶠ b
... | yes refl = just ε⋆
... | no _     = nothing

------------------------------------------------------------------------
-- Booleans and finite enumerations

∨-false : (b b' : 𝔹) → b ∨ b' ≡ false → (b ≡ false) × (b' ≡ false)
∨-false false b' q = refl , q
∨-false true  b' ()

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

both : ∀ {X Y : Set} → Maybe X → Maybe Y → Maybe (X × Y)
both (just x) (just y) = just (x , y)
both _        _        = nothing

∉[] : ∀ {X : Set} {x : X} → x ∈ [] → ⊥
∉[] ()

------------------------------------------------------------------------
-- An assignment leaves alone what the assigned unknown does not occur in

mutual

  updᵉ-v : ∀ {Ω} → (k : EVar Ω) → (b : EExp Ω) → (A : OVType Ω)
         → occᵉ-v k A ≡ false → A [ updᵉ k b ]ᵛ ≡ A
  updᵉ-v k b (tvar α)  q = refl
  updᵉ-v k b (Base c)  q = refl
  updᵉ-v k b unit      q = refl
  updᵉ-v k b bool      q = refl
  updᵉ-v k b nat       q = refl
  updᵉ-v k b empty     q = refl
  updᵉ-v k b (A |×| B) q with ∨-false (occᵉ-v k A) (occᵉ-v k B) q
  ... | q₁ , q₂ = cong₂ _|×|_ (updᵉ-v k b A q₁) (updᵉ-v k b B q₂)
  updᵉ-v k b (A |+| B) q with ∨-false (occᵉ-v k A) (occᵉ-v k B) q
  ... | q₁ , q₂ = cong₂ _|+|_ (updᵉ-v k b A q₁) (updᵉ-v k b B q₂)
  updᵉ-v k b (list A)  q = cong list (updᵉ-v k b A q)
  updᵉ-v k b (A ⇒ C)   q with ∨-false (occᵉ-v k A) (occᵉ-c k C) q
  ... | q₁ , q₂ = cong₂ _⇒_ (updᵉ-v k b A q₁) (updᵉ-c k b C q₂)
  updᵉ-v k b (C ⇛ D)   q with ∨-false (occᵉ-c k C) (occᵉ-c k D) q
  ... | q₁ , q₂ = cong₂ _⇛_ (updᵉ-c k b C q₁) (updᵉ-c k b D q₂)
  updᵉ-v k b ([ ρ ] A) q with ∨-false (occᵉ-r k ρ) (occᵉ-v k A) q
  ... | q₁ , q₂ = cong₂ [_]_ (updᵉ-r k b ρ q₁) (updᵉ-v k b A q₂)

  updᵉ-c : ∀ {Ω} → (k : EVar Ω) → (b : EExp Ω) → (C : OCType Ω)
         → occᵉ-c k C ≡ false → C [ updᵉ k b ]ᶜ ≡ C
  updᵉ-c k b (A ! ε) q with ∨-false (occᵉ-v k A) (occᵉ-e k ε) q
  ... | q₁ , q₂ = cong₂ _!_ (updᵉ-v k b A q₁) (updᵉ-e k b ε q₂)

mutual

  updʳ-v : ∀ {Ω} → (k : RVar Ω) → (b : RExp Ω) → (A : OVType Ω)
         → occʳ-v k A ≡ false → A [ updʳ k b ]ᵛ ≡ A
  updʳ-v k b (tvar α)  q = refl
  updʳ-v k b (Base c)  q = refl
  updʳ-v k b unit      q = refl
  updʳ-v k b bool      q = refl
  updʳ-v k b nat       q = refl
  updʳ-v k b empty     q = refl
  updʳ-v k b (A |×| B) q with ∨-false (occʳ-v k A) (occʳ-v k B) q
  ... | q₁ , q₂ = cong₂ _|×|_ (updʳ-v k b A q₁) (updʳ-v k b B q₂)
  updʳ-v k b (A |+| B) q with ∨-false (occʳ-v k A) (occʳ-v k B) q
  ... | q₁ , q₂ = cong₂ _|+|_ (updʳ-v k b A q₁) (updʳ-v k b B q₂)
  updʳ-v k b (list A)  q = cong list (updʳ-v k b A q)
  updʳ-v k b (A ⇒ C)   q with ∨-false (occʳ-v k A) (occʳ-c k C) q
  ... | q₁ , q₂ = cong₂ _⇒_ (updʳ-v k b A q₁) (updʳ-c k b C q₂)
  updʳ-v k b (C ⇛ D)   q with ∨-false (occʳ-c k C) (occʳ-c k D) q
  ... | q₁ , q₂ = cong₂ _⇛_ (updʳ-c k b C q₁) (updʳ-c k b D q₂)
  updʳ-v k b ([ ρ ] A) q with ∨-false (occʳ-r k ρ) (occʳ-v k A) q
  ... | q₁ , q₂ = cong₂ [_]_ (updʳ-r k b ρ q₁) (updʳ-v k b A q₂)

  updʳ-c : ∀ {Ω} → (k : RVar Ω) → (b : RExp Ω) → (C : OCType Ω)
         → occʳ-c k C ≡ false → C [ updʳ k b ]ᶜ ≡ C
  updʳ-c k b (A ! ε) q = cong₂ _!_ (updʳ-v k b A q) (updʳ-e k b ε)

-- ... and so does a later substitution

updᵉ-⨟e : ∀ {Ω Ω'} → (k : EVar Ω) → (b : EExp Ω) → (τ : Subst Ω Ω') → (ε : EExp Ω)
        → occᵉ-e k ε ≡ false → ε [ updᵉ k b ⨟ˢ τ ]ᵉ ≡ ε [ τ ]ᵉ
updᵉ-⨟e k b τ ε q = trans (sym ([⨟]ᵉ ε (updᵉ k b) τ)) (cong (_[ τ ]ᵉ) (updᵉ-e k b ε q))

updᵉ-⨟r : ∀ {Ω Ω'} → (k : EVar Ω) → (b : EExp Ω) → (τ : Subst Ω Ω') → (ρ : RExp Ω)
        → occᵉ-r k ρ ≡ false → ρ [ updᵉ k b ⨟ˢ τ ]ʳ ≡ ρ [ τ ]ʳ
updᵉ-⨟r k b τ ρ q = trans (sym ([⨟]ʳ ρ (updᵉ k b) τ)) (cong (_[ τ ]ʳ) (updᵉ-r k b ρ q))

updᵉ-⨟v : ∀ {Ω Ω'} → (k : EVar Ω) → (b : EExp Ω) → (τ : Subst Ω Ω') → (A : OVType Ω)
        → occᵉ-v k A ≡ false → A [ updᵉ k b ⨟ˢ τ ]ᵛ ≡ A [ τ ]ᵛ
updᵉ-⨟v k b τ A q = trans (sym ([⨟]ᵛ A (updᵉ k b) τ)) (cong (_[ τ ]ᵛ) (updᵉ-v k b A q))

updʳ-⨟e : ∀ {Ω Ω'} → (k : RVar Ω) → (b : RExp Ω) → (τ : Subst Ω Ω') → (ε : EExp Ω)
        → ε [ updʳ k b ⨟ˢ τ ]ᵉ ≡ ε [ τ ]ᵉ
updʳ-⨟e k b τ ε = trans (sym ([⨟]ᵉ ε (updʳ k b) τ)) (cong (_[ τ ]ᵉ) (updʳ-e k b ε))

updʳ-⨟r : ∀ {Ω Ω'} → (k : RVar Ω) → (b : RExp Ω) → (τ : Subst Ω Ω') → (ρ : RExp Ω)
        → occʳ-r k ρ ≡ false → ρ [ updʳ k b ⨟ˢ τ ]ʳ ≡ ρ [ τ ]ʳ
updʳ-⨟r k b τ ρ q = trans (sym ([⨟]ʳ ρ (updʳ k b) τ)) (cong (_[ τ ]ʳ) (updʳ-r k b ρ q))

updʳ-⨟v : ∀ {Ω Ω'} → (k : RVar Ω) → (b : RExp Ω) → (τ : Subst Ω Ω') → (A : OVType Ω)
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

-- A variable, with the equation that names it

evar? : ∀ {Φ} → (ε : EExp Φ) → Maybe (Σ[ j ∈ EVar Φ ] (ε ≡ evar j))
evar? (evar j)   = just (j , refl)
evar? (econst c) = nothing
evar? (ε ·̂ₑ ε')  = nothing
evar? (ε ⊔̂ₑ ε')  = nothing

------------------------------------------------------------------------
-- The eigenvariable of a rigid scope

-- `κ⟨ b ⟩` (`Deferred`) sends the newest effect-grade variable to `b`.
-- The eigenvariable goes to the unit (`κᵉ`), or to the top (`κ⊤`).

κᵉ : ∀ {Ω} → Subst (Ω +e) Ω
κᵉ = κ⟨ 𝟏̂ₑ ⟩

κ⊤ : ∀ {Ω} → Subst (Ω +e) Ω
κ⊤ = κ⟨ econst ⊤ₑ ⟩

⊩ᴴ-κᵉ : ∀ {Ω} {Q : Hyps Ω} → Q ⊩ᴴ (wkᵉ-H Q) [ κᵉ ]
⊩ᴴ-κᵉ = ⊩ᴴ-κ 𝟏̂ₑ

-- Sending the eigenvariable to the top rather than the unit raises every instance

κᵉ≾κ⊤ : ∀ {Ω} {Q : Hyps Ω} → Q ⊩ κᵉ ≾ˢ κ⊤
κᵉ≾κ⊤ = mk≾ˢ (λ i → ⊩≾̂ᵣ-refl) (λ { zero → topₑ ; (suc i) → ⊩≾̂ₑ-refl })


-- `ω` sends it to the top and fixes the rest. It raises every image,
-- and leaves a weakened hypothesis set entailed.

ω : ∀ {Ω} → Subst (Ω +e) (Ω +e)
ω = κ⊤ ⨟ˢ wkˢᵉ

wk-ω : ∀ {Ω} → (wkˢᵉ {Ω} ⨟ˢ ω) ≐ˢ wkˢᵉ
wk-ω = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

id≾ω : ∀ {Ω} {Q : Hyps (Ω +e)} → Q ⊩ idˢ ≾ˢ ω
id≾ω = mk≾ˢ (λ i → ⊩≾̂ᵣ-refl) (λ { zero → topₑ ; (suc i) → ⊩≾̂ₑ-refl })

⊩ᴴ-ω : ∀ {Ω} {Q : Hyps Ω} → wkᵉ-H Q ⊩ᴴ (wkᵉ-H Q) [ ω ]
⊩ᴴ-ω = ⊩ᴴ-⨟ ⊩ᴴ-wkᵉ (⊩ᴴ-κ (econst ⊤ₑ))

------------------------------------------------------------------------
-- Two substitutions agree after `X` on the unknowns `O` mentions

Agree : ∀ {Θ Φ Ω Ω'} → Subst Θ Φ → Subst Φ Ω → Subst Ω Ω' → Subst Ω Ω' → Set
Agree O X σ₁ σ₂ = (∀ {k} → freeᵉ k O ≡ true → sE X k [ σ₁ ]ᵉ ≡ sE X k [ σ₂ ]ᵉ)
                × (∀ {k} → freeʳ k O ≡ true → sR X k [ σ₁ ]ʳ ≡ sR X k [ σ₂ ]ʳ)

-- An expression mentioning only such unknowns reads the same too

module _ {Θ Φ Ω Ω'} {O : Subst Θ Φ} {X : Subst Φ Ω} {σ₁ σ₂ : Subst Ω Ω'}
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

·̂ₑ-inj : ∀ {Ω} {a b c d : EExp Ω} → a ·̂ₑ b ≡ c ·̂ₑ d → (a ≡ c) × (b ≡ d)
·̂ₑ-inj refl = refl , refl

⊔̂ₑ-inj : ∀ {Ω} {a b c d : EExp Ω} → a ⊔̂ₑ b ≡ c ⊔̂ₑ d → (a ≡ c) × (b ≡ d)
⊔̂ₑ-inj refl = refl , refl

·̂ᵣ-inj : ∀ {Ω} {a b c d : RExp Ω} → a ·̂ᵣ b ≡ c ·̂ᵣ d → (a ≡ c) × (b ≡ d)
·̂ᵣ-inj refl = refl , refl

⊔̂ᵣ-inj : ∀ {Ω} {a b c d : RExp Ω} → a ⊔̂ᵣ b ≡ c ⊔̂ᵣ d → (a ≡ c) × (b ≡ d)
⊔̂ᵣ-inj refl = refl , refl

∣∣-inj : ∀ {Ω} {a b : EExp Ω} → ∣ a ∣̂ᵉ ≡ ∣ b ∣̂ᵉ → a ≡ b
∣∣-inj refl = refl

|×|-inj : ∀ {Ω} {A B C D : OVType Ω} → A |×| B ≡ C |×| D → (A ≡ C) × (B ≡ D)
|×|-inj refl = refl , refl

|+|-inj : ∀ {Ω} {A B C D : OVType Ω} → A |+| B ≡ C |+| D → (A ≡ C) × (B ≡ D)
|+|-inj refl = refl , refl

list-inj : ∀ {Ω} {A B : OVType Ω} → list A ≡ list B → A ≡ B
list-inj refl = refl

⇒-inj : ∀ {Ω} {A B : OVType Ω} {C D : OCType Ω} → A ⇒ C ≡ B ⇒ D → (A ≡ B) × (C ≡ D)
⇒-inj refl = refl , refl

⇛-inj : ∀ {Ω} {C C' D D' : OCType Ω} → C ⇛ D ≡ C' ⇛ D' → (C ≡ C') × (D ≡ D')
⇛-inj refl = refl , refl

[]-inj : ∀ {Ω} {ρ ρ' : RExp Ω} {A B : OVType Ω} → [ ρ ] A ≡ [ ρ' ] B → (ρ ≡ ρ') × (A ≡ B)
[]-inj refl = refl , refl

!-inj : ∀ {Ω} {A B : OVType Ω} {ε ε' : EExp Ω} → A ! ε ≡ B ! ε' → (A ≡ B) × (ε ≡ ε')
!-inj refl = refl , refl

module _ {Φ Ω Ω'} (X : Subst Φ Ω) (σ₁ σ₂ : Subst Ω Ω') where

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
  subᵉ-v {k} (A |+| B) r e with ∨-true (occᵉ-v k A) (occᵉ-v k B) r
  ... | inj₁ r' = subᵉ-v A r' (proj₁ (|+|-inj e))
  ... | inj₂ r' = subᵉ-v B r' (proj₂ (|+|-inj e))
  subᵉ-v {k} (list A) r e = subᵉ-v A r (list-inj e)
  subᵉ-v {k} (A ⇒ C) r e with ∨-true (occᵉ-v k A) (occᵉ-c k C) r
  ... | inj₁ r' = subᵉ-v A r' (proj₁ (⇒-inj e))
  ... | inj₂ r' = subᵉ-c C r' (proj₂ (⇒-inj e))
  subᵉ-v {k} (C ⇛ D) r e with ∨-true (occᵉ-c k C) (occᵉ-c k D) r
  ... | inj₁ r' = subᵉ-c C r' (proj₁ (⇛-inj e))
  ... | inj₂ r' = subᵉ-c D r' (proj₂ (⇛-inj e))
  subᵉ-v {k} ([ ρ ] A) r e with ∨-true (occᵉ-r k ρ) (occᵉ-v k A) r
  ... | inj₁ r' = subᵉ-r ρ r' (proj₁ ([]-inj e))
  ... | inj₂ r' = subᵉ-v A r' (proj₂ ([]-inj e))

  subᵉ-c {k} (A ! ε) r e with ∨-true (occᵉ-v k A) (occᵉ-e k ε) r
  ... | inj₁ r' = subᵉ-v A r' (proj₁ (!-inj e))
  ... | inj₂ r' = subᵉ-e ε r' (proj₂ (!-inj e))

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
  subʳ-v {k} (A |+| B) r e with ∨-true (occʳ-v k A) (occʳ-v k B) r
  ... | inj₁ r' = subʳ-v A r' (proj₁ (|+|-inj e))
  ... | inj₂ r' = subʳ-v B r' (proj₂ (|+|-inj e))
  subʳ-v {k} (list A) r e = subʳ-v A r (list-inj e)
  subʳ-v {k} (A ⇒ C) r e with ∨-true (occʳ-v k A) (occʳ-c k C) r
  ... | inj₁ r' = subʳ-v A r' (proj₁ (⇒-inj e))
  ... | inj₂ r' = subʳ-c C r' (proj₂ (⇒-inj e))
  subʳ-v {k} (C ⇛ D) r e with ∨-true (occʳ-c k C) (occʳ-c k D) r
  ... | inj₁ r' = subʳ-c C r' (proj₁ (⇛-inj e))
  ... | inj₂ r' = subʳ-c D r' (proj₂ (⇛-inj e))
  subʳ-v {k} ([ ρ ] A) r e with ∨-true (occʳ-r k ρ) (occʳ-v k A) r
  ... | inj₁ r' = subʳ-r ρ r' (proj₁ ([]-inj e))
  ... | inj₂ r' = subʳ-v A r' (proj₂ ([]-inj e))

  subʳ-c (A ! ε) r e = subʳ-v A r (proj₁ (!-inj e))

-- The images of the unknowns `O` mentions are all of the form `y [ w ]`,
-- on which the two agree

agree-out : ∀ {Θ Φ Ω Ω' Ω₀} → (O : Subst Θ Φ) → (X : Subst Φ Ω) → (σ₁ σ₂ : Subst Ω Ω')
          → (w : Subst Ω₀ Ω) → (δ₀ : Subst Θ Ω₀)
          → (∀ y → y [ w ]ᵛ [ σ₁ ]ᵛ ≡ y [ w ]ᵛ [ σ₂ ]ᵛ)
          → (∀ y → y [ w ]ʳ [ σ₁ ]ʳ ≡ y [ w ]ʳ [ σ₂ ]ʳ)
          → (∀ y → y [ w ]ᵉ [ σ₁ ]ᵉ ≡ y [ w ]ᵉ [ σ₂ ]ᵉ)
          → (O ⨟ˢ X) ≐ˢ (δ₀ ⨟ˢ w) → Agree O X σ₁ σ₂
agree-out {Ω₀ = Ω₀} O X σ₁ σ₂ w δ₀ fv fr fe tr = ue , ur
  where
    flatᵛ : ∀ {x} → (y : OVType Ω₀) → x ≡ y [ w ]ᵛ → x [ σ₁ ]ᵛ ≡ x [ σ₂ ]ᵛ
    flatᵛ y e = trans (cong (_[ σ₁ ]ᵛ) e) (trans (fv y) (sym (cong (_[ σ₂ ]ᵛ) e)))

    flatʳ : ∀ {x} → (y : RExp Ω₀) → x ≡ y [ w ]ʳ → x [ σ₁ ]ʳ ≡ x [ σ₂ ]ʳ
    flatʳ y e = trans (cong (_[ σ₁ ]ʳ) e) (trans (fr y) (sym (cong (_[ σ₂ ]ʳ) e)))

    flatᵉ : ∀ {x} → (y : EExp Ω₀) → x ≡ y [ w ]ᵉ → x [ σ₁ ]ᵉ ≡ x [ σ₂ ]ᵉ
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

-- An instance entering a rigid scope: its own unknowns go to an instance of the
-- enclosing scope, the rigid to a fresh eigenvariable no other outer image mentions

Entry : ∀ {Θ Φ Ω''} → Subst (Θ +e) Φ → Subst Φ (Ω'' +e) → Set
Entry {Θ} {Ω'' = Ω''} O τ = Σ[ δ₀ ∈ Subst Θ Ω'' ] ((O ⨟ˢ τ) ≐ˢ (δ₀ ↑ᵉ))

stable-out : ∀ {Θ Φ Ω''} → (O : Subst (Θ +e) Φ) → (τ : Subst Φ (Ω'' +e)) → Entry O τ
           → Agree (wkˢᵉ {Θ} ⨟ˢ O) τ ω idˢ
stable-out O τ (δ₀ , en) =
  agree-out (wkˢᵉ ⨟ˢ O) τ ω idˢ wkˢᵉ δ₀
    (λ y → trans ([⨟]ᵛ y wkˢᵉ ω) (trans ([≐]ᵛ wk-ω y) (sym ([id]ᵛ (y [ wkˢᵉ ]ᵛ)))))
    (λ y → trans ([⨟]ʳ y wkˢᵉ ω) (trans ([≐]ʳ wk-ω y) (sym ([id]ʳ (y [ wkˢᵉ ]ʳ)))))
    (λ y → trans ([⨟]ᵉ y wkˢᵉ ω) (trans ([≐]ᵉ wk-ω y) (sym ([id]ᵉ (y [ wkˢᵉ ]ᵉ)))))
    (≐ˢ-trans (⨟-assoc wkˢᵉ O τ) (≐ˢ-trans (⨟-congʳ wkˢᵉ en) (wkˢᵉ-↑ᵉ δ₀)))

allFalse : ∀ {Y : Set} → (f : Y → 𝔹) → (l : List Y) → Maybe (∀ {y} → y ∈ l → f y ≡ false)
allFalse f []      = just (λ ())
allFalse f (y ∷ l) with isFalse (f y) | allFalse f l
... | just q  | just g  = just (λ { (here refl) → q ; (there m) → g m })
... | just _  | nothing = nothing
... | nothing | _       = nothing

-- An unknown absent from every type of a residual; a disjunction's grade, a
-- smaller side, need be free of it only for raising

record Cleanᵉ {Ω} (k : EVar Ω) (R : Resid Ω) : Set where
  constructor cleanᵉ
  field
    cts : ∀ {A}   → A ∈ ts R       → occᵉ-v k A ≡ false
    css : ∀ {A B} → (A , B) ∈ ss R → (occᵉ-v k A ∨ occᵉ-v k B) ≡ false
    cds : ∀ {A ρ} → (A , ρ) ∈ ds R → occᵉ-v k A ≡ false

record Cleanʳ {Ω} (k : RVar Ω) (R : Resid Ω) : Set where
  constructor cleanʳ
  field
    cts : ∀ {A}   → A ∈ ts R       → occʳ-v k A ≡ false
    css : ∀ {A B} → (A , B) ∈ ss R → (occʳ-v k A ∨ occʳ-v k B) ≡ false
    cds : ∀ {A ρ} → (A , ρ) ∈ ds R → occʳ-v k A ≡ false

cleanᵉ? : ∀ {Ω} → (k : EVar Ω) → (R : Resid Ω) → Maybe (Cleanᵉ k R)
cleanᵉ? k R with allFalse (occᵉ-v k) (ts R)
                | allFalse (λ { (A , B) → occᵉ-v k A ∨ occᵉ-v k B }) (ss R)
                | allFalse (λ { (A , ρ) → occᵉ-v k A }) (ds R)
... | just t  | just s  | just d  = just (cleanᵉ t s d)
... | _       | _       | _       = nothing

cleanʳ? : ∀ {Ω} → (k : RVar Ω) → (R : Resid Ω) → Maybe (Cleanʳ k R)
cleanʳ? k R with allFalse (occʳ-v k) (ts R)
                | allFalse (λ { (A , B) → occʳ-v k A ∨ occʳ-v k B }) (ss R)
                | allFalse (λ { (A , ρ) → occʳ-v k A }) (ds R)
... | just t  | just s  | just d  = just (cleanʳ t s d)
... | _       | _       | _       = nothing

-- The unknown absent from every disjunction's grade

DFreeᵉ : ∀ {Ω} → EVar Ω → Resid Ω → Set
DFreeᵉ k R = ∀ {A ρ} → (A , ρ) ∈ ds R → occᵉ-r k ρ ≡ false

DFreeʳ : ∀ {Ω} → RVar Ω → Resid Ω → Set
DFreeʳ k R = ∀ {A ρ} → (A , ρ) ∈ ds R → occʳ-r k ρ ≡ false

dfreeᵉ? : ∀ {Ω} → (k : EVar Ω) → (R : Resid Ω) → Maybe (DFreeᵉ k R)
dfreeᵉ? k R with allFalse (λ { (A , ρ) → occᵉ-r k ρ }) (ds R)
... | just f  = just (λ m → f m)
... | nothing = nothing

dfreeʳ? : ∀ {Ω} → (k : RVar Ω) → (R : Resid Ω) → Maybe (DFreeʳ k R)
dfreeʳ? k R with allFalse (λ { (A , ρ) → occʳ-r k ρ }) (ds R)
... | just f  = just (λ m → f m)
... | nothing = nothing

------------------------------------------------------------------------
-- The lowering lemma and its siblings: an assignment the conditions
-- license keeps every instance that satisfied the residual

-- The types, free of the unknown, are left as they were

cleanᵉ-⊩ : ∀ {Ω Ω'} {Q : Hyps Ω'} {k : EVar Ω} {R : Resid Ω}
         → Cleanᵉ k R → (b : EExp Ω) → (τ : Subst Ω Ω') → Q ⊩ᴿ R [ τ ]
         → (∀ {A ρ} → (A , ρ) ∈ ds R → Q ⊩ ρ [ updᵉ k b ⨟ˢ τ ]ʳ ≾̂ᵣ ρ [ τ ]ʳ)
         → (∀ {A} → A ∈ ts R → Q ⊩Et A [ updᵉ k b ⨟ˢ τ ]ᵛ)
         × (∀ {A B} → (A , B) ∈ ss R → Q ⊩ A [ updᵉ k b ⨟ˢ τ ]ᵛ <:̂ᵛ B [ updᵉ k b ⨟ˢ τ ]ᵛ)
         × (∀ {A ρ} → (A , ρ) ∈ ds R
              → Q ⊩ A [ updᵉ k b ⨟ˢ τ ]ᵛ Et∨≾ᵘ ρ [ updᵉ k b ⨟ˢ τ ]ʳ)
cleanᵉ-⊩ {Q = Q} {k} {R} (cleanᵉ ct cs cd) b τ h g = ts' , ss' , ds'
  where
    ts' : ∀ {A} → A ∈ ts R → Q ⊩Et A [ updᵉ k b ⨟ˢ τ ]ᵛ
    ts' {A} m = subst (Q ⊩Et_) (sym (updᵉ-⨟v k b τ A (ct m))) (⊩ts h m)

    ss' : ∀ {A B} → (A , B) ∈ ss R → Q ⊩ A [ updᵉ k b ⨟ˢ τ ]ᵛ <:̂ᵛ B [ updᵉ k b ⨟ˢ τ ]ᵛ
    ss' {A} {B} m with ∨-false (occᵉ-v k A) (occᵉ-v k B) (cs m)
    ... | qA , qB = subst₂ (Q ⊩_<:̂ᵛ_) (sym (updᵉ-⨟v k b τ A qA)) (sym (updᵉ-⨟v k b τ B qB))
                           (⊩ss h m)

    ds' : ∀ {A ρ} → (A , ρ) ∈ ds R → Q ⊩ A [ updᵉ k b ⨟ˢ τ ]ᵛ Et∨≾ᵘ ρ [ updᵉ k b ⨟ˢ τ ]ʳ
    ds' {A} {ρ} m =
      subst (λ X → Q ⊩ X Et∨≾ᵘ ρ [ updᵉ k b ⨟ˢ τ ]ʳ) (sym (updᵉ-⨟v k b τ A (cd m)))
            (Et∨≾ᵘ-≡̂ (≡̂ᵛ-refl (A [ τ ]ᵛ)) (g m) (⊩ds h m))

cleanʳ-⊩ : ∀ {Ω Ω'} {Q : Hyps Ω'} {k : RVar Ω} {R : Resid Ω}
         → Cleanʳ k R → (b : RExp Ω) → (τ : Subst Ω Ω') → Q ⊩ᴿ R [ τ ]
         → (∀ {A ρ} → (A , ρ) ∈ ds R → Q ⊩ ρ [ updʳ k b ⨟ˢ τ ]ʳ ≾̂ᵣ ρ [ τ ]ʳ)
         → (∀ {A} → A ∈ ts R → Q ⊩Et A [ updʳ k b ⨟ˢ τ ]ᵛ)
         × (∀ {A B} → (A , B) ∈ ss R → Q ⊩ A [ updʳ k b ⨟ˢ τ ]ᵛ <:̂ᵛ B [ updʳ k b ⨟ˢ τ ]ᵛ)
         × (∀ {A ρ} → (A , ρ) ∈ ds R
              → Q ⊩ A [ updʳ k b ⨟ˢ τ ]ᵛ Et∨≾ᵘ ρ [ updʳ k b ⨟ˢ τ ]ʳ)
cleanʳ-⊩ {Q = Q} {k} {R} (cleanʳ ct cs cd) b τ h g = ts' , ss' , ds'
  where
    ts' : ∀ {A} → A ∈ ts R → Q ⊩Et A [ updʳ k b ⨟ˢ τ ]ᵛ
    ts' {A} m = subst (Q ⊩Et_) (sym (updʳ-⨟v k b τ A (ct m))) (⊩ts h m)

    ss' : ∀ {A B} → (A , B) ∈ ss R → Q ⊩ A [ updʳ k b ⨟ˢ τ ]ᵛ <:̂ᵛ B [ updʳ k b ⨟ˢ τ ]ᵛ
    ss' {A} {B} m with ∨-false (occʳ-v k A) (occʳ-v k B) (cs m)
    ... | qA , qB = subst₂ (Q ⊩_<:̂ᵛ_) (sym (updʳ-⨟v k b τ A qA)) (sym (updʳ-⨟v k b τ B qB))
                           (⊩ss h m)

    ds' : ∀ {A ρ} → (A , ρ) ∈ ds R → Q ⊩ A [ updʳ k b ⨟ˢ τ ]ᵛ Et∨≾ᵘ ρ [ updʳ k b ⨟ˢ τ ]ʳ
    ds' {A} {ρ} m =
      subst (λ X → Q ⊩ X Et∨≾ᵘ ρ [ updʳ k b ⨟ˢ τ ]ʳ) (sym (updʳ-⨟v k b τ A (cd m)))
            (Et∨≾ᵘ-≡̂ (≡̂ᵛ-refl (A [ τ ]ᵛ)) (g m) (⊩ds h m))

-- A resource assignment leaves every effect ordering as it was

effects-fixed : ∀ {Ω Ω'} {Q : Hyps Ω'} {R : Resid Ω} → (k : RVar Ω) → (b : RExp Ω)
              → (τ : Subst Ω Ω') → Q ⊩ᴿ R [ τ ]
              → ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ updʳ k b ⨟ˢ τ ]ᵉ ≾̂ₑ ε' [ updʳ k b ⨟ˢ τ ]ᵉ
effects-fixed {Q = Q} k b τ h {ε} {ε'} m =
  subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym (updʳ-⨟e k b τ ε)) (sym (updʳ-⨟e k b τ ε')) (⊩es h m)

-- The orderings of either sort read at an instance, before and after an
-- assignment (`Values`)

module Atᵉ {Ω Ω'} (Q : Hyps Ω') (k : EVar Ω) (b : EExp Ω) (τ : Subst Ω Ω') where
  open Vᵉ.Keep {Ω} k (Q ⊩_≾̂ₑ_) ⊩≾̂ₑ-refl transₑ (_[ τ ]ᵉ) (_[ updᵉ k b ⨟ˢ τ ]ᵉ)
               (λ {x} → updᵉ-⨟e k b τ x) (λ p → ⊩-substₑ ∅ᴴ-⊩ᴴ p) public
  module R = Vⁱ.Keep {Ω} k (Q ⊩_≾̂ᵣ_) ⊩≾̂ᵣ-refl transᵣ (_[ τ ]ʳ) (_[ updᵉ k b ⨟ˢ τ ]ʳ)
                      (λ {x} → updᵉ-⨟r k b τ x) (λ p → ⊩-substᵣ ∅ᴴ-⊩ᴴ p)

module Atʳ {Ω Ω'} (Q : Hyps Ω') (k : RVar Ω) (b : RExp Ω) (τ : Subst Ω Ω') where
  open Vʳ.Keep {Ω} k (Q ⊩_≾̂ᵣ_) ⊩≾̂ᵣ-refl transᵣ (_[ τ ]ʳ) (_[ updʳ k b ⨟ˢ τ ]ʳ)
               (λ {x} → updʳ-⨟r k b τ x) (λ p → ⊩-substᵣ ∅ᴴ-⊩ᴴ p) public

-- A cycle `x ≾ k` decided to hold once `k` is `b` holds at every
-- instance after the assignment

closeᵉ : ∀ {Ω Ω'} {Q : Hyps Ω'} → (k : EVar Ω) → (b : EExp Ω) → (τ : Subst Ω Ω')
       → ∀ {x} → ∅ᴴ ⊩ x [ updᵉ k b ]ᵉ ≾̂ₑ b → Q ⊩ x [ updᵉ k b ⨟ˢ τ ]ᵉ ≾̂ₑ evar k [ updᵉ k b ⨟ˢ τ ]ᵉ
closeᵉ {Q = Q} k b τ {x} d =
  subst₂ (λ y z → Q ⊩ y ≾̂ₑ z) ([⨟]ᵉ x (updᵉ k b) τ) (cong (_[ τ ]ᵉ) (sym (updᵉ-hit k b)))
         (⊩-substₑ ∅ᴴ-⊩ᴴ d)

closeʳ : ∀ {Ω Ω'} {Q : Hyps Ω'} → (k : RVar Ω) → (b : RExp Ω) → (τ : Subst Ω Ω')
       → ∀ {x} → ∅ᴴ ⊩ x [ updʳ k b ]ʳ ≾̂ᵣ b → Q ⊩ x [ updʳ k b ⨟ˢ τ ]ʳ ≾̂ᵣ rvar k [ updʳ k b ⨟ˢ τ ]ʳ
closeʳ {Q = Q} k b τ {x} d =
  subst₂ (λ y z → Q ⊩ y ≾̂ᵣ z) ([⨟]ʳ x (updʳ k b) τ) (cong (_[ τ ]ʳ) (sym (updʳ-hit k b)))
         (⊩-substᵣ ∅ᴴ-⊩ᴴ d)

-- Lowering an effect unknown below its value, to a bound above each of
-- its lower bounds at which its cycles hold

lowerᵉ-⊩ : ∀ {Ω Ω'} {Q : Hyps Ω'} {k : EVar Ω} {R : Resid Ω}
         → (lw : Vᵉ.Lows {Ω} k (es R))
         → (∀ {a} → a ∈ rs R → Vⁱ.FreeR {Ω} k a)
         → Cleanᵉ k R
         → (b : EExp Ω) → (∀ {E} → E ∈ dfs R → Still dir↓ (updᵉ k b) E)
         → Vᵉ.Closes {Ω} k (es R) lw b
         → (τ : Subst Ω Ω')
         → Q ⊩ b [ τ ]ᵉ ≾̂ₑ sE τ k
         → (∀ {x} → x ∈ Vᵉ.bnds lw → Q ⊩ x [ τ ]ᵉ ≾̂ₑ b [ τ ]ᵉ)
         → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updᵉ k b ⨟ˢ τ ]
lowerᵉ-⊩ {Q = Q} {k} {R} lw fr cl b sd cy τ below ub h =
  mk⊩ᴿ (Atᵉ.R.lower-free Q k b τ fr (mono-substᵣ le) (⊩rs h))
       (Atᵉ.lower-keeps Q k b τ lw (mono-substₑ le)
          (λ {x} mx → subst (λ z → Q ⊩ x [ τ ]ᵉ ≾̂ₑ z [ τ ]ᵉ) (sym (updᵉ-hit k b)) (ub mx))
          (λ {x} mc → closeᵉ k b τ {x} (cy mc))
          (⊩es h))
       (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↓ E (sd m) le (⊩dfs h m))
  where
    le : Q ⊩ (updᵉ k b ⨟ˢ τ) ≾ˢ τ
    le = updᵉ-below k b τ below

    c = cleanᵉ-⊩ cl b τ h (λ {A} {ρ} m → mono-substᵣ le ρ)

-- Raising an effect unknown to its upper bound below the others

raiseᵉ-⊩ : ∀ {Ω Ω'} {Q : Hyps Ω'} {k : EVar Ω} {R : Resid Ω}
         → (up : Vᵉ.Ups {Ω} k (es R))
         → (∀ {a} → a ∈ rs R → Vⁱ.FreeL {Ω} k a)
         → Cleanᵉ k R → DFreeᵉ k R
         → (∀ {E} → E ∈ dfs R → Still dir↑ (updᵉ k (Vᵉ.cap up)) E)
         → (τ : Subst Ω Ω')
         → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updᵉ k (Vᵉ.cap up) ⨟ˢ τ ]
raiseᵉ-⊩ {Q = Q} {k} {R} up fl cl df sd τ h =
  mk⊩ᴿ (Atᵉ.R.raise-free Q k U τ fl (mono-substᵣ ge) (⊩rs h))
       (Atᵉ.raise-keeps Q k U τ up (mono-substₑ ge) hit (⊩es h))
       (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↑ E (sd m) ge (⊩dfs h m))
  where
    U  = Vᵉ.cap up
    τ₁ = updᵉ k U ⨟ˢ τ

    ge : Q ⊩ τ ≾ˢ τ₁
    ge = updᵉ-above k U τ (⊩es h (Vᵉ.srcᵘ up))

    c = cleanᵉ-⊩ cl U τ h
          (λ {A} {ρ} m → subst (λ x → Q ⊩ x ≾̂ᵣ ρ [ τ ]ʳ) (sym (updᵉ-⨟r k U τ ρ (df m))) ⊩≾̂ᵣ-refl)

    hit : Q ⊩ evar k [ τ₁ ]ᵉ ≾̂ₑ U [ τ₁ ]ᵉ
    hit = subst (λ x → Q ⊩ x [ τ ]ᵉ ≾̂ₑ U [ τ₁ ]ᵉ) (sym (updᵉ-hit k U)) (mono-substₑ ge U)

-- The same two for a resource unknown, which no effect ordering mentions

lowerʳ-⊩ : ∀ {Ω Ω'} {Q : Hyps Ω'} {k : RVar Ω} {R : Resid Ω}
         → (lw : Vʳ.Lows {Ω} k (rs R))
         → Cleanʳ k R
         → (b : RExp Ω) → (∀ {E} → E ∈ dfs R → Still dir↓ (updʳ k b) E)
         → Vʳ.Closes {Ω} k (rs R) lw b
         → (τ : Subst Ω Ω')
         → Q ⊩ b [ τ ]ʳ ≾̂ᵣ sR τ k
         → (∀ {x} → x ∈ Vʳ.bnds lw → Q ⊩ x [ τ ]ʳ ≾̂ᵣ b [ τ ]ʳ)
         → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updʳ k b ⨟ˢ τ ]
lowerʳ-⊩ {Q = Q} {k} {R} lw cl b sd cy τ below ub h =
  mk⊩ᴿ (Atʳ.lower-keeps Q k b τ lw (mono-substᵣ le)
          (λ {x} mx → subst (λ z → Q ⊩ x [ τ ]ʳ ≾̂ᵣ z [ τ ]ʳ) (sym (updʳ-hit k b)) (ub mx))
          (λ {x} mc → closeʳ k b τ {x} (cy mc))
          (⊩rs h))
       (effects-fixed k b τ h)
       (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↓ E (sd m) le (⊩dfs h m))
  where
    le : Q ⊩ (updʳ k b ⨟ˢ τ) ≾ˢ τ
    le = updʳ-below k b τ below

    c = cleanʳ-⊩ cl b τ h (λ {A} {ρ} m → mono-substᵣ le ρ)

raiseʳ-⊩ : ∀ {Ω Ω'} {Q : Hyps Ω'} {k : RVar Ω} {R : Resid Ω}
         → (up : Vʳ.Ups {Ω} k (rs R))
         → Cleanʳ k R → DFreeʳ k R
         → (∀ {E} → E ∈ dfs R → Still dir↑ (updʳ k (Vʳ.cap up)) E)
         → (τ : Subst Ω Ω')
         → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updʳ k (Vʳ.cap up) ⨟ˢ τ ]
raiseʳ-⊩ {Q = Q} {k} {R} up cl df sd τ h =
  mk⊩ᴿ (Atʳ.raise-keeps Q k U τ up (mono-substᵣ ge) hit (⊩rs h))
       (effects-fixed k U τ h)
       (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↑ E (sd m) ge (⊩dfs h m))
  where
    U  = Vʳ.cap up
    τ₁ = updʳ k U ⨟ˢ τ

    ge : Q ⊩ τ ≾ˢ τ₁
    ge = updʳ-above k U τ (⊩rs h (Vʳ.srcᵘ up))

    c = cleanʳ-⊩ cl U τ h
          (λ {A} {ρ} m → subst (λ x → Q ⊩ x ≾̂ᵣ ρ [ τ ]ʳ) (sym (updʳ-⨟r k U τ ρ (df m))) ⊩≾̂ᵣ-refl)

    hit : Q ⊩ rvar k [ τ₁ ]ʳ ≾̂ᵣ U [ τ₁ ]ʳ
    hit = subst (λ x → Q ⊩ x [ τ ]ʳ ≾̂ᵣ U [ τ₁ ]ʳ) (sym (updʳ-hit k U)) (mono-substᵣ ge U)

-- Raising an unknown absent from every left side to the top

topᵉ-⊩ : ∀ {Ω Ω'} {Q : Hyps Ω'} {k : EVar Ω} {R : Resid Ω}
       → (∀ {a} → a ∈ es R → Vᵉ.UnderTop {Ω} k a)
       → (∀ {a} → a ∈ rs R → Vⁱ.FreeL {Ω} k a)
       → Cleanᵉ k R → DFreeᵉ k R
       → (∀ {E} → E ∈ dfs R → Still dir↑ (updᵉ k (econst ⊤ₑ)) E)
       → (τ : Subst Ω Ω')
       → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updᵉ k (econst ⊤ₑ) ⨟ˢ τ ]
topᵉ-⊩ {Q = Q} {k} {R} fe fl cl df sd τ h =
  mk⊩ᴿ (Atᵉ.R.raise-free Q k (econst ⊤ₑ) τ fl (mono-substᵣ ge) (⊩rs h))
       (Atᵉ.top-keeps Q k (econst ⊤ₑ) τ fe (mono-substₑ ge)
          (λ y → subst (λ z → Q ⊩ y [ updᵉ k (econst ⊤ₑ) ⨟ˢ τ ]ᵉ ≾̂ₑ z [ τ ]ᵉ)
                       (sym (updᵉ-hit k (econst ⊤ₑ))) topₑ)
          (⊩es h))
       (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↑ E (sd m) ge (⊩dfs h m))
  where
    ge : Q ⊩ τ ≾ˢ (updᵉ k (econst ⊤ₑ) ⨟ˢ τ)
    ge = updᵉ-above k (econst ⊤ₑ) τ topₑ

    c = cleanᵉ-⊩ cl (econst ⊤ₑ) τ h
          (λ {A} {ρ} m → subst (λ x → Q ⊩ x ≾̂ᵣ ρ [ τ ]ʳ)
                               (sym (updᵉ-⨟r k (econst ⊤ₑ) τ ρ (df m))) ⊩≾̂ᵣ-refl)

topʳ-⊩ : ∀ {Ω Ω'} {Q : Hyps Ω'} {k : RVar Ω} {R : Resid Ω}
       → (∀ {a} → a ∈ rs R → Vʳ.UnderTop {Ω} k a)
       → Cleanʳ k R → DFreeʳ k R
       → (∀ {E} → E ∈ dfs R → Still dir↑ (updʳ k (rconst ⊤ᵣ)) E)
       → (τ : Subst Ω Ω')
       → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updʳ k (rconst ⊤ᵣ) ⨟ˢ τ ]
topʳ-⊩ {Q = Q} {k} {R} fl cl df sd τ h =
  mk⊩ᴿ (Atʳ.top-keeps Q k (rconst ⊤ᵣ) τ fl (mono-substᵣ ge)
          (λ y → subst (λ z → Q ⊩ y [ updʳ k (rconst ⊤ᵣ) ⨟ˢ τ ]ʳ ≾̂ᵣ z [ τ ]ʳ)
                       (sym (updʳ-hit k (rconst ⊤ᵣ))) topᵣ)
          (⊩rs h))
       (effects-fixed k (rconst ⊤ᵣ) τ h)
       (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↑ E (sd m) ge (⊩dfs h m))
  where
    ge : Q ⊩ τ ≾ˢ (updʳ k (rconst ⊤ᵣ) ⨟ˢ τ)
    ge = updʳ-above k (rconst ⊤ᵣ) τ topᵣ

    c = cleanʳ-⊩ cl (rconst ⊤ᵣ) τ h
          (λ {A} {ρ} m → subst (λ x → Q ⊩ x ≾̂ᵣ ρ [ τ ]ʳ)
                               (sym (updʳ-⨟r k (rconst ⊤ᵣ) τ ρ (df m))) ⊩≾̂ᵣ-refl)

------------------------------------------------------------------------
-- Settled atoms bound nothing: an ordering decided true from no hypotheses, a
-- disjunction whose type is always eternal or whose grade is below the unit

Every : ∀ {Ω} {X : Set} → (∀ {Ω'} → Hyps Ω' → Subst Ω Ω' → X → Set) → X → Set
Every P a = ∀ {Ω'} {Q : Hyps Ω'} → (δ : Subst _ Ω') → P Q δ a

Disj : ∀ {Ω Ω'} → Hyps Ω' → Subst Ω Ω' → OVType Ω × RExp Ω → Set
Disj Q δ (A , ρ) = Q ⊩ A [ δ ]ᵛ Et∨≾ᵘ ρ [ δ ]ʳ

settledʳ : ∀ {Ω} → (a : RExp Ω × RExp Ω) → Maybe (Every Ordʳ a)
settledʳ (ρ , ρ') with decideᵣ full ∅ᴴ ρ ρ'
... | just p  = just (λ δ → ⊩-substᵣ ∅ᴴ-⊩ᴴ p)
... | nothing = nothing

settledᵉ : ∀ {Ω} → (a : EExp Ω × EExp Ω) → Maybe (Every Ordᵉ a)
settledᵉ (ε , ε') with decideₑ full ∅ᴴ ε ε'
... | just p  = just (λ δ → ⊩-substₑ ∅ᴴ-⊩ᴴ p)
... | nothing = nothing

-- A disjunction settled from hypotheses `H`: its grade below the unit
-- at the strength `full`, or its type eternal at every instance

Under : ∀ {Ω} {X : Set} → Hyps Ω → (∀ {Ω'} → Hyps Ω' → Subst Ω Ω' → X → Set)
      → ∀ {Ω'} → Hyps Ω' → Subst Ω Ω' → X → Set
Under H P Q δ a = Q ⊩ᴴ H [ δ ] → P Q δ a

settledᵈ : ∀ {Ω} → (H : Hyps Ω) → (a : OVType Ω × RExp Ω) → Maybe (Every (Under H Disj) a)
settledᵈ H (A , ρ) with decideᵣ full H ρ 𝟏̂ᵣ
... | just p  = just (λ δ h → ≾ᵘ-ok (⊩-substᵣ h p))
... | nothing with etDec A in e
...   | just [] = just (λ δ _ → et-ok (⊩Et-subst ∅ᴴ-⊩ᴴ (etDec-sound {Q = ∅ᴴ} A e (λ ()))))
...   | just (_ ∷ _) = nothing
...   | nothing      = nothing

-- The entries of a list that are not settled

record Unsettled {Ω} {X : Set} (P : ∀ {Ω'} → Hyps Ω' → Subst Ω Ω' → X → Set)
                 (l : List X) : Set where
  constructor unset
  field
    kept  : List X
    kept⊆ : ∀ {a} → a ∈ kept → a ∈ l
    back  : ∀ {Ω'} {Q : Hyps Ω'} → (δ : Subst Ω Ω')
          → (∀ {a} → a ∈ kept → P Q δ a) → ∀ {a} → a ∈ l → P Q δ a

-- An entry settled, or kept

consᵘ : ∀ {Ω} {X : Set} {P : ∀ {Ω'} → Hyps Ω' → Subst Ω Ω' → X → Set} {a : X} {l : List X}
      → Maybe (Every P a) → Unsettled P l → Unsettled P (a ∷ l)
consᵘ (just p) (unset l' sb bk) =
  unset l' (λ m → there (sb m))
        (λ δ k → λ { (here refl) → p δ ; (there m) → bk δ k m })
consᵘ {a = a} nothing (unset l' sb bk) =
  unset (a ∷ l')
        (λ { (here refl) → here refl ; (there m) → there (sb m) })
        (λ δ k → λ { (here refl) → k (here refl)
                   ; (there m)   → bk δ (λ m' → k (there m')) m })

unsettled : ∀ {Ω} {X : Set} {P : ∀ {Ω'} → Hyps Ω' → Subst Ω Ω' → X → Set}
          → ((a : X) → Maybe (Every P a)) → (l : List X) → Unsettled P l
unsettled set []      = unset [] (λ ()) (λ δ k → λ ())
unsettled set (a ∷ l) = consᵘ (set a) (unsettled set l)

-- The entries a test marks, each settled, the others kept

when : ∀ {Y : Set} → (b : 𝔹) → (b ≡ true → Y) → Maybe Y
when true  f = just (f refl)
when false f = nothing

dropping : ∀ {Ω} {X : Set} {P : ∀ {Ω'} → Hyps Ω' → Subst Ω Ω' → X → Set}
         → (d : X → 𝔹) → (l : List X) → (∀ {a} → a ∈ l → d a ≡ true → Every P a)
         → Unsettled P l
dropping d []      h = unset [] (λ ()) (λ δ k → λ ())
dropping d (a ∷ l) h = consᵘ (when (d a) (h (here refl))) (dropping d l (λ m → h (there m)))

allKept : ∀ {Ω} {X : Set} {P : ∀ {Ω'} → Hyps Ω' → Subst Ω Ω' → X → Set} {l : List X}
        → Unsettled P l
allKept {l = l} = unset l (λ m → m) (λ δ k → k)

------------------------------------------------------------------------
-- One step: the value an unknown is sent to, with the proof that every
-- instance survives it, and the orderings it settles

Keeps : ∀ {Ω} → Subst Ω Ω → Resid Ω → Set
Keeps {Ω} σ R = ∀ {Ω'} → (τ : Subst Ω Ω') → (Q : Hyps Ω') → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ σ ⨟ˢ τ ]

-- The orderings an assignment `σ` leaves open; each other one holds at
-- every instance once `σ` is made

record Drops {Ω} (σ : Subst Ω Ω) (R : Resid Ω) : Set where
  constructor drops
  field
    dropsʳ : Unsettled (λ Q δ → Ordʳ Q (σ ⨟ˢ δ)) (rs R)
    dropsᵉ : Unsettled (λ Q δ → Ordᵉ Q (σ ⨟ˢ δ)) (es R)

keepAll : ∀ {Ω} {σ : Subst Ω Ω} {R : Resid Ω} → Drops σ R
keepAll = drops allKept allKept

-- The residual the open orderings leave

left : ∀ {Ω} {σ : Subst Ω Ω} {R : Resid Ω} → Drops σ R → Resid Ω
left {R = R} (drops Dʳ Dᵉ) = record R { rs = Unsettled.kept Dʳ ; es = Unsettled.kept Dᵉ }

-- Lowering settles the orderings of its sort with the unknown on the
-- greater side (`lower-drops`)

loweredᵉ : ∀ {Ω} {k : EVar Ω} {R : Resid Ω} → (lw : Vᵉ.Lows {Ω} k (es R)) → (b : EExp Ω)
         → (∀ {Ω'} {Q : Hyps Ω'} → (δ : Subst Ω Ω') → ∀ {x} → x ∈ Vᵉ.bnds lw
            → Q ⊩ x [ δ ]ᵉ ≾̂ₑ b [ δ ]ᵉ)
         → Vᵉ.Closes {Ω} k (es R) lw b
         → Drops (updᵉ k b) R
loweredᵉ {k = k} {R} lw b ub cy =
  drops allKept
        (dropping (λ a → occᵉ-e k (proj₂ a)) (es R)
                  (λ m q {Ω'} {Q} δ → Atᵉ.lower-drops Q k b δ lw (hit δ)
                                        (λ {x} mc → closeᵉ k b δ {x} (cy mc)) m q))
  where
    hit : ∀ {Ω'} {Q : Hyps Ω'} → (δ : Subst _ Ω') → ∀ {x} → x ∈ Vᵉ.bnds lw
        → Q ⊩ x [ δ ]ᵉ ≾̂ₑ evar k [ updᵉ k b ⨟ˢ δ ]ᵉ
    hit {Q = Q} δ {x} mx = subst (λ z → Q ⊩ x [ δ ]ᵉ ≾̂ₑ z [ δ ]ᵉ) (sym (updᵉ-hit k b)) (ub δ mx)

loweredʳ : ∀ {Ω} {k : RVar Ω} {R : Resid Ω} → (lw : Vʳ.Lows {Ω} k (rs R)) → (b : RExp Ω)
         → (∀ {Ω'} {Q : Hyps Ω'} → (δ : Subst Ω Ω') → ∀ {x} → x ∈ Vʳ.bnds lw
            → Q ⊩ x [ δ ]ʳ ≾̂ᵣ b [ δ ]ʳ)
         → Vʳ.Closes {Ω} k (rs R) lw b
         → Drops (updʳ k b) R
loweredʳ {k = k} {R} lw b ub cy =
  drops (dropping (λ a → occʳ-r k (proj₂ a)) (rs R)
                  (λ m q {Ω'} {Q} δ → Atʳ.lower-drops Q k b δ lw (hit δ)
                                        (λ {x} mc → closeʳ k b δ {x} (cy mc)) m q))
        allKept
  where
    hit : ∀ {Ω'} {Q : Hyps Ω'} → (δ : Subst _ Ω') → ∀ {x} → x ∈ Vʳ.bnds lw
        → Q ⊩ x [ δ ]ʳ ≾̂ᵣ rvar k [ updʳ k b ⨟ˢ δ ]ʳ
    hit {Q = Q} δ {x} mx = subst (λ z → Q ⊩ x [ δ ]ʳ ≾̂ᵣ z [ δ ]ʳ) (sym (updʳ-hit k b)) (ub δ mx)

first : ∀ {X : Set} → Maybe X → Maybe X → Maybe X
first (just x) _ = just x
first nothing  y = y

-- Whether an unknown occurs in the deferred conditions on a greater side
-- (`dir↓`) or a smaller one (`dir↑`), which sending it to the top would move

failed : ∀ {X : Set} → Maybe X → 𝔹
failed (just _) = false
failed nothing  = true

inDfsᵉ : ∀ {Ω} → Dir → EVar Ω → Resid Ω → 𝔹
inDfsᵉ d k R = failed (stills? d (updᵉ k (econst ⊤ₑ)) (dfs R))

inDfsʳ : ∀ {Ω} → Dir → RVar Ω → Resid Ω → 𝔹
inDfsʳ d k R = failed (stills? d (updʳ k (rconst ⊤ᵣ)) (dfs R))

-- The unit, for an unknown with no bound that does occur

occursᵉ : ∀ {Ω} → EVar Ω → Resid Ω → 𝔹
occursᵉ k R = anyL (λ { (ε , _) → occᵉ-e k ε }) (es R) ∨ anyL (λ { (ρ , _) → occᵉ-r k ρ }) (rs R)
            ∨ anyL (λ { (_ , ρ) → occᵉ-r k ρ }) (ds R) ∨ inDfsᵉ dir↑ k R ∨ inDfsᵉ dir↓ k R

occursʳ : ∀ {Ω} → RVar Ω → Resid Ω → 𝔹
occursʳ k R = anyL (λ { (ρ , _) → occʳ-r k ρ }) (rs R) ∨ anyL (λ { (_ , ρ) → occʳ-r k ρ }) (ds R)
            ∨ inDfsʳ dir↑ k R ∨ inDfsʳ dir↓ k R

-- The top, for an unknown with no bound above that does occur

occursᵉ⁺ : ∀ {Ω} → EVar Ω → Resid Ω → 𝔹
occursᵉ⁺ k R = anyL (λ { (_ , ε') → occᵉ-e k ε' }) (es R) ∨ anyL (λ { (_ , ρ') → occᵉ-r k ρ' }) (rs R)
             ∨ inDfsᵉ dir↓ k R

occursʳ⁺ : ∀ {Ω} → RVar Ω → Resid Ω → 𝔹
occursʳ⁺ k R = anyL (λ { (_ , ρ') → occʳ-r k ρ' }) (rs R) ∨ inDfsʳ dir↓ k R

-- A value: every instance survives it, and it names the orderings it
-- settles

Step : ∀ {Ω} → Subst Ω Ω → Resid Ω → Set
Step σ R = Keeps σ R × Drops σ R

-- The oracle of an effect unknown: resource orderings and deferred conditions
-- kept; for raising, the disjunctions' grades free of it

oracleᵉ : ∀ {Ω} → (k : EVar Ω) → (R : Resid Ω) → Vᵉ.Oracle {Ω} k
oracleᵉ {Ω} k R = record
  { Lower  = λ b → (∀ {a} → a ∈ rs R → Vⁱ.FreeR {Ω} k a)
                 × (∀ {E} → E ∈ dfs R → Still dir↓ (updᵉ k b) E)
  ; lower? = λ b → both (Vⁱ.freeRs {Ω} k (rs R)) (stills? dir↓ (updᵉ k b) (dfs R))
  ; Raise  = λ b → (∀ {a} → a ∈ rs R → Vⁱ.FreeL {Ω} k a) × DFreeᵉ k R
                 × (∀ {E} → E ∈ dfs R → Still dir↑ (updᵉ k b) E)
  ; raise? = λ b → both (Vⁱ.freeLs {Ω} k (rs R))
                        (both (dfreeᵉ? k R) (stills? dir↑ (updᵉ k b) (dfs R)))
  }

oracleʳ : ∀ {Ω} → (k : RVar Ω) → (R : Resid Ω) → Vʳ.Oracle {Ω} k
oracleʳ {Ω} k R = record
  { Lower  = λ b → ∀ {E} → E ∈ dfs R → Still dir↓ (updʳ k b) E
  ; lower? = λ b → stills? dir↓ (updʳ k b) (dfs R)
  ; Raise  = λ b → DFreeʳ k R × (∀ {E} → E ∈ dfs R → Still dir↑ (updʳ k b) E)
  ; raise? = λ b → both (dfreeʳ? k R) (stills? dir↑ (updʳ k b) (dfs R))
  }

-- The rules of `Values` in order: lowering, raising, the unit for an unknown
-- that occurs, the top for one that occurs on a greater side

stepᵉ : ∀ {Ω} → (k : EVar Ω) → (R : Resid Ω) → Maybe (Σ[ b ∈ EExp Ω ] Step (updᵉ k b) R)
stepᵉ {Ω} k R with cleanᵉ? k R
... | nothing = nothing
... | just cl =
      first (Maybe.map lower (Vᵉ.lower {Ω} k o (es R)))
      (first (Maybe.map raise (Vᵉ.raise {Ω} k o (es R)))
      (first (if occursᵉ k R then Maybe.map least (Vᵉ.least {Ω} k o (es R)) else nothing)
             (if occursᵉ⁺ k R then Maybe.map top (Vᵉ.topOf {Ω} k o (es R)) else nothing)))
  where
    o = oracleᵉ k R

    lower : Vᵉ.ByLower {Ω} k o (es R) → Σ[ b ∈ EExp Ω ] Step (updᵉ k b) R
    lower (Vᵉ.byLower lw x xs e b to (fr , sd)) =
      b ,
      (λ τ Q h → lowerᵉ-⊩ lw fr cl b sd (Vᵉ.lowTo-closes {Ω} k to) τ
                   (LowToₑ.Join.below k lw e to τ (⊩es h)) (LowToₑ.Join.above k lw e to τ) h) ,
      loweredᵉ lw b (λ δ m → LowToₑ.Join.above k lw e to δ m) (Vᵉ.lowTo-closes {Ω} k to)

    raise : Vᵉ.ByRaise {Ω} k o (es R) → Σ[ b ∈ EExp Ω ] Step (updᵉ k b) R
    raise (Vᵉ.byRaise up (fl , df , sd)) =
      Vᵉ.cap up , (λ τ Q h → raiseᵉ-⊩ up fl cl df sd τ h) , keepAll

    least : Vᵉ.ByLeast {Ω} k o (es R) → Σ[ b ∈ EExp Ω ] Step (updᵉ k b) R
    least (Vᵉ.byLeast lw nob ij b to (fr , sd)) =
      b , (λ τ Q h → lowerᵉ-⊩ lw fr cl b sd (Vᵉ.lowTo-closes {Ω} k to) τ
                       (LowToₑ.least k lw to τ (minₑ (to-witness ij)) (⊩es h))
                       (λ m → ⊥-elim (∉[] (subst (_ ∈_) nob m))) h) ,
      loweredᵉ lw b (λ δ m → ⊥-elim (∉[] (subst (_ ∈_) nob m))) (Vᵉ.lowTo-closes {Ω} k to)

    top : Vᵉ.ByTop {Ω} k o (es R) → Σ[ b ∈ EExp Ω ] Step (updᵉ k b) R
    top (Vᵉ.byTop fe (fl , df , sd)) =
      econst ⊤ₑ , (λ τ Q h → topᵉ-⊩ fe fl cl df sd τ h) , keepAll

stepʳ : ∀ {Ω} → (k : RVar Ω) → (R : Resid Ω) → Maybe (Σ[ b ∈ RExp Ω ] Step (updʳ k b) R)
stepʳ {Ω} k R with cleanʳ? k R
... | nothing = nothing
... | just cl =
      first (Maybe.map lower (Vʳ.lower {Ω} k o (rs R)))
      (first (Maybe.map raise (Vʳ.raise {Ω} k o (rs R)))
      (first (if occursʳ k R then Maybe.map least (Vʳ.least {Ω} k o (rs R)) else nothing)
             (if occursʳ⁺ k R then Maybe.map top (Vʳ.topOf {Ω} k o (rs R)) else nothing)))
  where
    o = oracleʳ k R

    lower : Vʳ.ByLower {Ω} k o (rs R) → Σ[ b ∈ RExp Ω ] Step (updʳ k b) R
    lower (Vʳ.byLower lw x xs e b to sd) =
      b ,
      (λ τ Q h → lowerʳ-⊩ lw cl b sd (Vʳ.lowTo-closes {Ω} k to) τ
                   (LowToᵣ.Join.below k lw e to τ (⊩rs h)) (LowToᵣ.Join.above k lw e to τ) h) ,
      loweredʳ lw b (λ δ m → LowToᵣ.Join.above k lw e to δ m) (Vʳ.lowTo-closes {Ω} k to)

    raise : Vʳ.ByRaise {Ω} k o (rs R) → Σ[ b ∈ RExp Ω ] Step (updʳ k b) R
    raise (Vʳ.byRaise up (df , sd)) =
      Vʳ.cap up , (λ τ Q h → raiseʳ-⊩ up cl df sd τ h) , keepAll

    least : Vʳ.ByLeast {Ω} k o (rs R) → Σ[ b ∈ RExp Ω ] Step (updʳ k b) R
    least (Vʳ.byLeast lw nob ij b to sd) =
      b , (λ τ Q h → lowerʳ-⊩ lw cl b sd (Vʳ.lowTo-closes {Ω} k to) τ
                       (LowToᵣ.least k lw to τ (minᵣ (to-witness ij)) (⊩rs h))
                       (λ m → ⊥-elim (∉[] (subst (_ ∈_) nob m))) h) ,
      loweredʳ lw b (λ δ m → ⊥-elim (∉[] (subst (_ ∈_) nob m))) (Vʳ.lowTo-closes {Ω} k to)

    top : Vʳ.ByTop {Ω} k o (rs R) → Σ[ b ∈ RExp Ω ] Step (updʳ k b) R
    top (Vʳ.byTop fl (df , sd)) =
      rconst ⊤ᵣ , (λ τ Q h → topʳ-⊩ fl cl df sd τ h) , keepAll

------------------------------------------------------------------------
-- A disjunction whose type is eternal at no instance (`etDec` refutes
-- it) is met, from no hypotheses, exactly by its grade side

record Refined {Ω} (l : List (OVType Ω × RExp Ω)) : Set where
  constructor refined
  field
    rest  : List (OVType Ω × RExp Ω)
    orders : List (RExp Ω × RExp Ω)
    rest⊆ : ∀ {a} → a ∈ rest → a ∈ l
    back  : ∀ {Ω'} {Q : Hyps Ω'} → (δ : Subst Ω Ω')
          → (∀ {a} → a ∈ rest → Disj Q δ a) → (∀ {a} → a ∈ orders → Ordʳ Q δ a)
          → ∀ {a} → a ∈ l → Disj Q δ a
    fwd   : ∀ {Ω'} → (δ : Subst Ω Ω')
          → (∀ {a} → a ∈ l → Disj ∅ᴴ δ a) → ∀ {a} → a ∈ orders → Ordʳ ∅ᴴ δ a
    restᴱ : ∀ {A ρ} → (A , ρ) ∈ rest → Σ[ αs ∈ List (TyVar Ω) ] (etDec A ≡ just αs)

-- One disjunction, by the verdict of `etDec` on its type

consᴿ : ∀ {Ω} {l : List (OVType Ω × RExp Ω)} → (A : OVType Ω) → (ρ : RExp Ω)
      → (x : Maybe (List (TyVar Ω))) → etDec A ≡ x → Refined l → Refined ((A , ρ) ∷ l)
consᴿ A ρ nothing e (refined r os sb bk fw re) =
  refined r ((ρ , 𝟏̂ᵣ) ∷ os) (λ m → there (sb m))
    (λ δ k o → λ { (here refl) → ≾ᵘ-ok (o (here refl))
                 ; (there m)   → bk δ k (λ m' → o (there m')) m })
    (λ δ k → λ { (here refl) → etDec-grade A e δ (k (here refl))
               ; (there m)   → fw δ (λ m' → k (there m')) m })
    re
consᴿ A ρ (just αs) e (refined r os sb bk fw re) =
  refined ((A , ρ) ∷ r) os
    (λ { (here refl) → here refl ; (there m) → there (sb m) })
    (λ δ k o → λ { (here refl) → k (here refl)
                 ; (there m)   → bk δ (λ m' → k (there m')) o m })
    (λ δ k → fw δ (λ m → k (there m)))
    (λ { (here refl) → αs , e ; (there m) → re m })

refine : ∀ {Ω} → (l : List (OVType Ω × RExp Ω)) → Refined l
refine []            = refined [] [] (λ ()) (λ δ k o ()) (λ δ k ()) (λ ())
refine ((A , ρ) ∷ l) = consᴿ A ρ (etDec A) refl (refine l)

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
hitᵥ l unit      = false
hitᵥ l bool      = false
hitᵥ l nat       = false
hitᵥ l empty     = false
hitᵥ l (A |×| B) = hitᵥ l A ∨ hitᵥ l B
hitᵥ l (A |+| B) = hitᵥ l A ∨ hitᵥ l B
hitᵥ l (list A)  = hitᵥ l A
hitᵥ l (A ⇒ C)   = hitᵥ l A ∨ hitᶜ l C
hitᵥ l (C ⇛ D)   = hitᶜ l C ∨ hitᶜ l D
hitᵥ l ([ ρ ] A) = hitᵣ l ρ ∨ hitᵥ l A
hitᶜ l (A ! ε)   = hitᵥ l A ∨ hitₑ l ε

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
tops-v l unit      q = refl
tops-v l bool      q = refl
tops-v l nat       q = refl
tops-v l empty     q = refl
tops-v l (A |×| B) q with ∨-false (hitᵥ l A) (hitᵥ l B) q
... | q₁ , q₂ = cong₂ _|×|_ (tops-v l A q₁) (tops-v l B q₂)
tops-v l (A |+| B) q with ∨-false (hitᵥ l A) (hitᵥ l B) q
... | q₁ , q₂ = cong₂ _|+|_ (tops-v l A q₁) (tops-v l B q₂)
tops-v l (list A)  q = cong list (tops-v l A q)
tops-v l (A ⇒ C)   q with ∨-false (hitᵥ l A) (hitᶜ l C) q
... | q₁ , q₂ = cong₂ _⇒_ (tops-v l A q₁) (tops-c l C q₂)
tops-v l (C ⇛ D)   q with ∨-false (hitᶜ l C) (hitᶜ l D) q
... | q₁ , q₂ = cong₂ _⇛_ (tops-c l C q₁) (tops-c l D q₂)
tops-v l ([ ρ ] A) q with ∨-false (hitᵣ l ρ) (hitᵥ l A) q
... | q₁ , q₂ = cong₂ [_]_ (tops-r l ρ q₁) (tops-v l A q₂)
tops-c l (A ! ε)   q with ∨-false (hitᵥ l A) (hitₑ l ε) q
... | q₁ , q₂ = cong₂ _!_ (tops-v l A q₁) (tops-e l ε q₂)

-- ... and so does a later substitution

tops-⨟e : ∀ {Φ Ω'} → (l : List (Mem Φ)) → (τ : Subst Φ Ω') → (ε : EExp Φ)
        → hitₑ l ε ≡ false → ε [ tops l ⨟ˢ τ ]ᵉ ≡ ε [ τ ]ᵉ
tops-⨟e l τ ε q = trans (sym ([⨟]ᵉ ε (tops l) τ)) (cong (_[ τ ]ᵉ) (tops-e l ε q))

tops-⨟r : ∀ {Φ Ω'} → (l : List (Mem Φ)) → (τ : Subst Φ Ω') → (ρ : RExp Φ)
        → hitᵣ l ρ ≡ false → ρ [ tops l ⨟ˢ τ ]ʳ ≡ ρ [ τ ]ʳ
tops-⨟r l τ ρ q = trans (sym ([⨟]ʳ ρ (tops l) τ)) (cong (_[ τ ]ʳ) (tops-r l ρ q))

tops-⨟v : ∀ {Φ Ω'} → (l : List (Mem Φ)) → (τ : Subst Φ Ω') → (A : OVType Φ)
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

tops-above : ∀ {Φ Ω'} {Q : Hyps Ω'} → (l : List (Mem Φ)) → (τ : Subst Φ Ω')
           → Q ⊩ τ ≾ˢ (tops l ⨟ˢ τ)
tops-above {Φ} {Q = Q} l τ = mk≾ˢ (λ k → r (inᴿ k l) k) (λ k → e (inᴱ k l) k)
  where
    r : (b : 𝔹) → (k : RVar Φ) → Q ⊩ sR τ k ≾̂ᵣ topR b k [ τ ]ʳ
    r true  k = topᵣ
    r false k = ⊩≾̂ᵣ-refl

    e : (b : 𝔹) → (k : EVar Φ) → Q ⊩ sE τ k ≾̂ₑ topE b k [ τ ]ᵉ
    e true  k = topₑ
    e false k = ⊩≾̂ₑ-refl

tops-below : ∀ {Φ Ω'} {Q : Hyps Ω'} → (l : List (Mem Φ)) → (τ T : Subst Φ Ω')
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

≾ˢ-refl : ∀ {Φ Ω'} {Q : Hyps Ω'} {τ : Subst Φ Ω'} → Q ⊩ τ ≾ˢ τ
≾ˢ-refl = mk≾ˢ (λ i → ⊩≾̂ᵣ-refl) (λ i → ⊩≾̂ₑ-refl)

-- The members, each bounded below by an expression decided to be the top once
-- the rigid `j` and the members before it are

data Reach {Φ} (R : Resid Φ) (j : EVar Φ) : List (Mem Φ) → Set where
  reach[] : Reach R j []
  reachᵉ  : ∀ {k x l} → (x , evar k) ∈ es R
          → ∅ᴴ ⊩ econst ⊤ₑ ≾̂ₑ x [ tops (eᵐ j ∷ l) ]ᵉ
          → Reach R j l → Reach R j (eᵐ k ∷ l)
  reachʳ  : ∀ {k x l} → (x , rvar k) ∈ rs R
          → ∅ᴴ ⊩ rconst ⊤ᵣ ≾̂ᵣ x [ tops (eᵐ j ∷ l) ]ʳ
          → Reach R j l → Reach R j (rᵐ k ∷ l)

-- At an instance with `j` at the top, so is every member

reach-top : ∀ {Φ Ω'} {Q : Hyps Ω'} {R : Resid Φ} {j : EVar Φ} {l : List (Mem Φ)}
          → Reach R j l → (T : Subst Φ Ω') → Q ⊩ᴿ R [ T ] → Q ⊩ econst ⊤ₑ ≾̂ₑ sE T j
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

-- An ordering whose left side mentions a member has on its right an expression
-- that is the top once the members are, or one over outer unknowns (`O'`) only

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

-- Raising the members keeps every instance entering the scope: it lies between
-- the instance and its copy with the eigenvariable at the top (`ω`)

raise-⊩ : ∀ {Θ Φ Ω''} {Q₀ : Hyps Ω''} {R : Resid Φ} → (O : Subst (Θ +e) Φ)
        → {j : EVar Φ} → sE O (newᵉ {Θ}) ≡ evar j → (l : List (Mem Φ)) → Reach R j l
        → (∀ {a} → a ∈ es R → UpAtₑ (wkˢᵉ {Θ} ⨟ˢ O) l a)
        → (∀ {a} → a ∈ rs R → UpAtᵣ (wkˢᵉ {Θ} ⨟ˢ O) l a)
        → CleanM l R
        → (∀ {E} → E ∈ dfs R → Still dir↑ (tops l) E)
        → (τ : Subst Φ (Ω'' +e)) → Entry O τ
        → wkᵉ-H Q₀ ⊩ᴿ R [ τ ] → wkᵉ-H Q₀ ⊩ᴿ R [ tops l ⨟ˢ τ ]
raise-⊩ {Θ} {Ω'' = Ω''} {Q₀ = Q₀} {R} O {j} eqj l rc ue ur (cleanM ct cs cd) sd τ en h =
  mk⊩ᴿ rs' es' ts' ss' ds' (λ {E} m → keepᵈ dir↑ E (sd m) lo (⊩dfs h m))
  where
    Q  = wkᵉ-H Q₀
    T  = τ ⨟ˢ ω
    τ₁ = tops l ⨟ˢ τ

    hT : Q ⊩ᴿ R [ T ]
    hT = ⊩ᴿ-⨟ ⊩ᴴ-ω h

    τj : sE τ j ≡ evar (newᵉ {Ω''})
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

    ts' : ∀ {A} → A ∈ ts R → Q ⊩Et A [ τ₁ ]ᵛ
    ts' {A} m = subst (Q ⊩Et_) (sym (tops-⨟v l τ A (ct m))) (⊩ts h m)

    ss' : ∀ {A B} → (A , B) ∈ ss R → Q ⊩ A [ τ₁ ]ᵛ <:̂ᵛ B [ τ₁ ]ᵛ
    ss' {A} {B} m with ∨-false (hitᵥ l A) (hitᵥ l B) (cs m)
    ... | qA , qB = subst₂ (Q ⊩_<:̂ᵛ_) (sym (tops-⨟v l τ A qA)) (sym (tops-⨟v l τ B qB))
                           (⊩ss h m)

    ds' : ∀ {A ρ} → (A , ρ) ∈ ds R → Q ⊩ A [ τ₁ ]ᵛ Et∨≾ᵘ ρ [ τ₁ ]ʳ
    ds' {A} {ρ} m with ∨-false (hitᵥ l A) (hitᵣ l ρ) (cd m)
    ... | qA , qρ = subst₂ (Q ⊩_Et∨≾ᵘ_) (sym (tops-⨟v l τ A qA)) (sym (tops-⨟r l τ ρ qρ))
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
... | nothing with decideₑ full ∅ᴴ (econst ⊤ₑ) (y [ tops l ]ᵉ)
...   | just p  = just (up-top p)
...   | nothing with outerₑ? O' y | isFalse (hitₑ l y)
...     | just o | just q = just (up-outer o q)
...     | _      | _      = nothing

upAtᵣ? : ∀ {Θ Φ} → (O' : Subst Θ Φ) → (l : List (Mem Φ)) → (a : RExp Φ × RExp Φ)
       → Maybe (UpAtᵣ O' l a)
upAtᵣ? O' l (x , y) with isFalse (hitᵣ l x)
... | just q  = just (up-free q)
... | nothing with decideᵣ full ∅ᴴ (rconst ⊤ᵣ) (y [ tops l ]ʳ)
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
      ...   | true with decideₑ full ∅ᴴ (econst ⊤ₑ) (x [ tops (eᵐ j ∷ l) ]ᵉ)
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
      ...   | true with decideᵣ full ∅ᴴ (rconst ⊤ᵣ) (x [ tops (eᵐ j ∷ l) ]ʳ)
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
-- Normal forms (`piecesʳ`, `piecesᵉ` of `Canon`): both sides canonical, one
-- ordering per alternative of a left side; a right side is never split

-- Whether a left side has a join, as it must to have several alternatives

hasJoinₑ : ∀ {Ω} → EExp Ω → 𝔹
hasJoinₑ (evar i)   = false
hasJoinₑ (econst c) = false
hasJoinₑ (ε ·̂ₑ ε')  = hasJoinₑ ε ∨ hasJoinₑ ε'
hasJoinₑ (ε ⊔̂ₑ ε')  = true

hasJoinᵣ : ∀ {Ω} → RExp Ω → 𝔹
hasJoinᵣ (rvar i)   = false
hasJoinᵣ (rconst c) = false
hasJoinᵣ (ρ ·̂ᵣ ρ')  = hasJoinᵣ ρ ∨ hasJoinᵣ ρ'
hasJoinᵣ (ρ ⊔̂ᵣ ρ')  = true
hasJoinᵣ ∣ ε ∣̂ᵉ     = hasJoinₑ ε

-- A disjunction: its grade in canonical form

piecesᵈ : ∀ {Ω} → (a : OVType Ω × RExp Ω) → Pieces Disj a
piecesᵈ (A , ρ) =
  pieces ((A , canonᵣ ρ) ∷ [])
         (λ δ k → Et∨≾ᵘ-≡̂ (≡̂ᵛ-refl _) (eqᵣ (≡̂ᵣ-subst δ (canonᵣ-≡ ρ))) (k (here refl)))
         (λ δ ok → λ { (here refl) →
            Et∨≾ᵘ-≡̂ (≡̂ᵛ-refl _) (eqᵣ (≡̂ᵣ-sym (≡̂ᵣ-subst δ (canonᵣ-≡ ρ)))) ok })

------------------------------------------------------------------------
-- Each strongly connected component of the orderings between whole unknowns
-- is one unknown, its members equal at every instance

-- The orderings between two whole unknowns

edgesᵉ : ∀ {Ω} → (l : List (EExp Ω × EExp Ω))
       → List (Σ[ a ∈ EVar Ω ] Σ[ b ∈ EVar Ω ] ((evar a , evar b) ∈ l))
edgesᵉ {Ω} l = go (withMem l)
  where
    go : List (Σ[ p ∈ EExp Ω × EExp Ω ] (p ∈ l))
       → List (Σ[ a ∈ EVar Ω ] Σ[ b ∈ EVar Ω ] ((evar a , evar b) ∈ l))
    go []                  = []
    go (((x , y) , m) ∷ ps) with evar? x | evar? y
    ... | just (a , refl) | just (b , refl) = (a , b , m) ∷ go ps
    ... | _               | _               = go ps

edgesʳ : ∀ {Ω} → (l : List (RExp Ω × RExp Ω))
       → List (Σ[ a ∈ RVar Ω ] Σ[ b ∈ RVar Ω ] ((rvar a , rvar b) ∈ l))
edgesʳ {Ω} l = go (withMem l)
  where
    go : List (Σ[ p ∈ RExp Ω × RExp Ω ] (p ∈ l))
       → List (Σ[ a ∈ RVar Ω ] Σ[ b ∈ RVar Ω ] ((rvar a , rvar b) ∈ l))
    go []                  = []
    go (((x , y) , m) ∷ ps) with rvar? x | rvar? y
    ... | just (a , refl) | just (b , refl) = (a , b , m) ∷ go ps
    ... | _               | _               = go ps


-- A deferred condition survives a substitution equivalent to the one
-- it moves

keep⇕ : ∀ {Ω Ω'} {Q : Hyps Ω'} {σ : Subst Ω Ω} {τ : Subst Ω Ω'} → (E : QOrd Ω)
      → Q ⊩ (σ ⨟ˢ τ) ≾ˢ τ → Q ⊩ τ ≾ˢ (σ ⨟ˢ τ) → Q ⊩ᴼ E [ τ ] → Q ⊩ᴼ E [ σ ⨟ˢ τ ]
keep⇕ (qord l k o) le ge h =
  mk⊩ᵒ (λ {x} {y} m → transᵣ (mono-substᵣ (≾ˢ-↑ᵉⁿ k le) x)
                             (transᵣ (⊩ors h m) (mono-substᵣ (≾ˢ-↑ᵉⁿ k ge) y)))
       (λ {x} {y} m → transₑ (mono-substₑ (≾ˢ-↑ᵉⁿ k le) x)
                             (transₑ (⊩oes h m) (mono-substₑ (≾ˢ-↑ᵉⁿ k ge) y)))


-- Sending each unknown to one equal to it at an instance keeps the instance
-- where the types are fixed, every grade former being monotone

record TypesFixed {Ω} (σ : Subst Ω Ω) (R : Resid Ω) : Set where
  constructor typesFixed
  field
    fts : ∀ {A}   → A ∈ ts R       → A [ σ ]ᵛ ≡ A
    fss : ∀ {A B} → (A , B) ∈ ss R → (A [ σ ]ᵛ ≡ A) × (B [ σ ]ᵛ ≡ B)
    fds : ∀ {A ρ} → (A , ρ) ∈ ds R → A [ σ ]ᵛ ≡ A

equal-⊩ : ∀ {Ω Ω'} {Q : Hyps Ω'} {σ : Subst Ω Ω} {R : Resid Ω}
        → TypesFixed σ R → (τ : Subst Ω Ω') → Q ⊩ᴿ R [ τ ]
        → Q ⊩ (σ ⨟ˢ τ) ≾ˢ τ → Q ⊩ τ ≾ˢ (σ ⨟ˢ τ) → Q ⊩ᴿ R [ σ ⨟ˢ τ ]
equal-⊩ {Q = Q} {σ} (typesFixed ft fs fd) τ h le ge =
  mk⊩ᴿ (equal-keeps {_⊑_ = Q ⊩_≾̂ᵣ_} transᵣ (mono-substᵣ le) (mono-substᵣ ge) (⊩rs h))
       (equal-keeps {_⊑_ = Q ⊩_≾̂ₑ_} transₑ (mono-substₑ le) (mono-substₑ ge) (⊩es h))
       (λ {A} m → subst (Q ⊩Et_) (ty A (ft m)) (⊩ts h m))
       (λ {A} {B} m → subst₂ (Q ⊩_<:̂ᵛ_) (ty A (proj₁ (fs m))) (ty B (proj₂ (fs m))) (⊩ss h m))
       (λ {A} {ρ} m → subst (λ X → Q ⊩ X Et∨≾ᵘ ρ [ σ ⨟ˢ τ ]ʳ) (ty A (fd m))
                            (Et∨≾ᵘ-≡̂ (≡̂ᵛ-refl (A [ τ ]ᵛ)) (mono-substᵣ le ρ) (⊩ds h m)))
       (λ {E} m → keep⇕ {σ = σ} E le ge (⊩dfs h m))
  where
    ty : ∀ A → A [ σ ]ᵛ ≡ A → A [ τ ]ᵛ ≡ A [ σ ⨟ˢ τ ]ᵛ
    ty A e = trans (cong (_[ τ ]ᵛ) (sym e)) ([⨟]ᵛ A σ τ)

nonempty : ∀ {X : Set} → List X → 𝔹
nonempty []      = false
nonempty (_ ∷ _) = true

-- The unknowns of one sort with an ordering between whole ones on each
-- side: only they lie on a cycle

bothEnds : ∀ {n} {Edge : Fin n → Fin n → Set}
         → List (Σ[ a ∈ Fin n ] Σ[ b ∈ Fin n ] Edge a b) → List (Fin n)
bothEnds E = map proj₁ (misses (λ i → not (anyL (λ { (a , _ , _) → ⌊ a ≟ᶠ i ⌋ }) E
                                         ∧ anyL (λ { (_ , b , _) → ⌊ b ≟ᶠ i ⌋ }) E)))

-- A local unknown occurs in no image of `O`

localᵉ : ∀ {Θ Φ} {k : EVar Φ} → (O : Subst Θ Φ) → freeᵉ k O ≡ false
       → (∀ α → occᵉ-v k (sTy O α) ≡ false) × (∀ i → occᵉ-r k (sR O i) ≡ false)
       × (∀ i → occᵉ-e k (sE O i) ≡ false)
localᵉ {k = k} O q with ∨-false (anyᶠ (λ α → occᵉ-v k (sTy O α))) _ q
... | qT , q' with ∨-false (anyᶠ (λ i → occᵉ-r k (sR O i))) _ q'
...   | qR , qE = anyᶠ-false (λ α → occᵉ-v k (sTy O α)) qT
                , anyᶠ-false (λ i → occᵉ-r k (sR O i)) qR
                , anyᶠ-false (λ i → occᵉ-e k (sE O i)) qE

localʳ : ∀ {Θ Φ} {k : RVar Φ} → (O : Subst Θ Φ) → freeʳ k O ≡ false
       → (∀ α → occʳ-v k (sTy O α) ≡ false) × (∀ i → occʳ-r k (sR O i) ≡ false)
localʳ {k = k} O q with ∨-false (anyᶠ (λ α → occʳ-v k (sTy O α))) _ q
... | qT , qR = anyᶠ-false (λ α → occʳ-v k (sTy O α)) qT , anyᶠ-false (λ i → occʳ-r k (sR O i)) qR

clash : ∀ {b} → b ≡ true → b ≡ false → ⊥
clash refl ()

-- The local unknowns of both sorts identified: `cσ` sends each movable one
-- (local, absent from every type) to its representative, keeping every instance

record Collapse {Θ Φ} (O : Subst (Θ +e) Φ) (R : Resid Φ) : Set where
  constructor collapsed
  field
    cσ    : Subst Φ Φ
    cmove : 𝔹
    cty   : ∀ α → sTy cσ α ≡ tvar α
    cfix  : (O ⨟ˢ cσ) ≐ˢ O
    ckeep : Keeps cσ R

module _ {Θ Φ} (O : Subst (Θ +e) Φ) (R : Resid Φ) where

  Mvᵉ : EVar Φ → Set
  Mvᵉ k = (freeᵉ k O ≡ false) × Cleanᵉ k R

  Mvʳ : RVar Φ → Set
  Mvʳ k = (freeʳ k O ≡ false) × Cleanʳ k R

  -- Each sort's components (`Reach`): outer unknowns preferred as
  -- representatives, the local ones absent from every type movable

  module Cᵉ = Reachability.Collapse (λ a b → (evar a , evar b) ∈ es R) sameᶠ? (edgesᵉ (es R))
                (bothEnds (edgesᵉ (es R))) _≟ᶠ_ (λ k → freeᵉ k O) Mvᵉ
                (λ k → both (isFalse (freeᵉ k O)) (cleanᵉ? k R))
  module Cʳ = Reachability.Collapse (λ a b → (rvar a , rvar b) ∈ rs R) sameᶠ? (edgesʳ (rs R))
                (bothEnds (edgesʳ (rs R))) _≟ᶠ_ (λ k → freeʳ k O) Mvʳ
                (λ k → both (isFalse (freeʳ k O)) (cleanʳ? k R))

  collapse : Collapse O R
  collapse = from Cᵉ.moves Cʳ.moves
    where
      from : Cᵉ.Moves → Cʳ.Moves → Collapse O R
      from me mr = collapsed σ (nonempty me ∨ nonempty mr) (λ α → refl) fixO keeps
        where
          σ : Subst Φ Φ
          σ = sub tvar (λ k → rvar (Cʳ.target mr k)) (λ k → evar (Cᵉ.target me k))

          -- a set of unknowns containing none that may move
          fixes : ∀ {W : Vars Φ} → (∀ k → Mvᵉ k → vᵉ W k ≡ false) → (∀ k → Mvʳ k → vʳ W k ≡ false)
                → Fixes W σ
          fixes fe fr =
            mkFixes (λ _ _ → refl)
                    (λ i o → [ cong rvar , (λ q → ⊥-elim (clash o (fr i q))) ]′ (Cʳ.stays mr i))
                    (λ i o → [ cong evar , (λ q → ⊥-elim (clash o (fe i q))) ]′ (Cᵉ.stays me i))

          fixO : (O ⨟ˢ σ) ≐ˢ O
          fixO =
            mk≐ˢ (λ α → fix-v (fixes {fvᵛ (sTy O α)} (λ k q → proj₁ (localᵉ O (proj₁ q)) α)
                                                     (λ k q → proj₁ (localʳ O (proj₁ q)) α))
                              (sTy O α) ⊆-refl)
                 (λ i → fix-r (fixes {fvʳ (sR O i)} (λ k q → proj₁ (proj₂ (localᵉ O (proj₁ q))) i)
                                                    (λ k q → proj₂ (localʳ O (proj₁ q)) i))
                              (sR O i) ⊆-refl)
                 (λ i → fix-e (fixes {fvᵉ (sE O i)} (λ k q → proj₂ (proj₂ (localᵉ O (proj₁ q))) i)
                                                    (λ k q → refl))
                              (sE O i) ⊆-refl)

          tf : TypesFixed σ R
          tf = typesFixed
                 (λ {A} m → fix-v (fixes {fvᵛ A} (λ k q → Cleanᵉ.cts (proj₂ q) m)
                                                 (λ k q → Cleanʳ.cts (proj₂ q) m)) A ⊆-refl)
                 (λ {A} {B} m →
                    fix-v (fixes {fvᵛ A} (λ k q → proj₁ (∨-false (occᵉ-v k A) _ (Cleanᵉ.css (proj₂ q) m)))
                                         (λ k q → proj₁ (∨-false (occʳ-v k A) _ (Cleanʳ.css (proj₂ q) m))))
                          A ⊆-refl ,
                    fix-v (fixes {fvᵛ B} (λ k q → proj₂ (∨-false (occᵉ-v k A) _ (Cleanᵉ.css (proj₂ q) m)))
                                         (λ k q → proj₂ (∨-false (occʳ-v k A) _ (Cleanʳ.css (proj₂ q) m))))
                          B ⊆-refl)
                 (λ {A} m → fix-v (fixes {fvᵛ A} (λ k q → Cleanᵉ.cds (proj₂ q) m)
                                                 (λ k q → Cleanʳ.cds (proj₂ q) m)) A ⊆-refl)

          keeps : Keeps σ R
          keeps τ Q h = equal-⊩ tf τ h le ge
            where
              eᵉ = Cᵉ.equal (λ a b → Q ⊩ sE τ a ≾̂ₑ sE τ b) ⊩≾̂ₑ-refl (λ m p → transₑ (⊩es h m) p) me
              eʳ = Cʳ.equal (λ a b → Q ⊩ sR τ a ≾̂ᵣ sR τ b) ⊩≾̂ᵣ-refl (λ m p → transᵣ (⊩rs h m) p) mr

              le : Q ⊩ (σ ⨟ˢ τ) ≾ˢ τ
              le = mk≾ˢ (λ i → proj₁ (eʳ i)) (λ i → proj₁ (eᵉ i))

              ge : Q ⊩ τ ≾ˢ (σ ⨟ˢ τ)
              ge = mk≾ˢ (λ i → proj₂ (eʳ i)) (λ i → proj₂ (eᵉ i))

------------------------------------------------------------------------
-- Localisation: the steps iterated over the local unknowns, the
-- settled atoms dropped around every round

record Localised {Θ Φ} (O : Subst (Θ +e) Φ) (R : Resid Φ) : Set where
  constructor loc
  field
    lσ   : Subst Φ Φ
    lR   : Resid Φ
    lfix : (O ⨟ˢ lσ) ≐ˢ O
    lsnd : ∀ {Ω'} → (δ : Subst Φ Ω') → (Q : Hyps Ω') → Q ⊩ᴿ lR [ δ ] → Q ⊩ᴿ R [ lσ ⨟ˢ δ ]
    lcpl : ∀ {Ω''} → (τ : Subst Φ (Ω'' +e)) → Entry O τ
         → ∅ᴴ ⊩ᴿ R [ τ ] → ∅ᴴ ⊩ᴿ lR [ τ ]
    latom : Atomicˢ (ss R) → Atomicˢ (ss lR)

open Localised public

-- A step that keeps the instances entering the scope

KeepsAt : ∀ {Θ Φ} → Subst (Θ +e) Φ → Subst Φ Φ → Resid Φ → Set
KeepsAt {Φ = Φ} O σ R = ∀ {Ω''} → (τ : Subst Φ (Ω'' +e)) → Entry O τ
                      → ∅ᴴ ⊩ᴿ R [ τ ] → ∅ᴴ ⊩ᴿ R [ σ ⨟ˢ τ ]

-- Nothing assigned

loc-id : ∀ {Θ Φ} {O : Subst (Θ +e) Φ} {R : Resid Φ} → Localised O R
loc-id {O = O} {R} =
  loc idˢ R (⨟-idʳ O) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) h) (λ τ en h → h) (λ a → a)

-- A localisation for one outer substitution is one for any pointwise equal

loc-≐ : ∀ {Θ Φ} {O O' : Subst (Θ +e) Φ} {R : Resid Φ} → O ≐ˢ O' → Localised O R → Localised O' R
loc-≐ p (loc σ R' fx sn cp la) =
  loc σ R' (≐ˢ-trans (⨟-congˡ (≐ˢ-sym p) σ) (≐ˢ-trans fx p)) sn
      (λ τ en h → cp τ (proj₁ en , ≐ˢ-trans (⨟-congˡ p τ) (proj₂ en)) h) la

-- The orderings of a residual left once the settled ones are dropped,
-- as hypotheses

settleᴴ : ∀ {Ω} → Resid Ω → Hyps Ω
settleᴴ R = hyps [] [] (Unsettled.kept (unsettled settledʳ (rs R)))
                       (Unsettled.kept (unsettled settledᵉ (es R))) [] []

-- The settled atoms dropped, a disjunction whose type is never eternal replaced
-- by its grade side; the instances from no hypotheses are unchanged

loc-settle : ∀ {Θ Φ} {O : Subst (Θ +e) Φ} {R : Resid Φ} → Localised O R → Localised O R
loc-settle (loc σ R₀ fx sn cp la) =
  loc σ (resid (Unsettled.kept Uʳ ++ Refined.orders F) (Unsettled.kept Uᵉ) (ts R₀) (ss R₀)
               (Refined.rest F) (dfs R₀)) fx
      (λ δ Q h → sn δ Q (mk⊩ᴿ (Unsettled.back Uʳ δ (λ m → ⊩rs h (∈-++⁺ˡ m)))
                              (Unsettled.back Uᵉ δ (⊩es h)) (⊩ts h) (⊩ss h)
                              (λ m → Unsettled.back Uᵈ δ
                                       (λ m' _ → Refined.back F δ (⊩ds h)
                                                   (λ m'' → ⊩rs h (∈-++⁺ʳ (Unsettled.kept Uʳ) m''))
                                                   m')
                                       m
                                       (mk⊩ᴴ (λ ()) (λ ()) (λ m' → ⊩rs h (∈-++⁺ˡ m')) (⊩es h) (λ ()) (λ ())))
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
    Uᵈ = unsettled (settledᵈ (settleᴴ R₀)) (ds R₀)
    F  = refine (Unsettled.kept Uᵈ)

-- Whether a left side has a join: only then may an ordering split

joined : ∀ {Ω} → Resid Ω → 𝔹
joined R = anyL (λ { (x , _) → hasJoinᵣ x }) (rs R) ∨ anyL (λ { (x , _) → hasJoinₑ x }) (es R)

-- Each atom in normal form, a join on a left side split into one ordering per
-- alternative; the instances are unchanged

loc-normal : ∀ {Θ Φ} {O : Subst (Θ +e) Φ} {R : Resid Φ} → Localised O R → Localised O R
loc-normal (loc σ R₀ fx sn cp la) =
  loc σ (resid (Split.out Sʳ) (Split.out Sᵉ) (ts R₀) (ss R₀) (Split.out Sᵈ) (dfs R₀)) fx
      (λ δ Q h → sn δ Q (mk⊩ᴿ (Split.back Sʳ δ (⊩rs h)) (Split.back Sᵉ δ (⊩es h))
                              (⊩ts h) (⊩ss h) (Split.back Sᵈ δ (⊩ds h)) (⊩dfs h)))
      (λ τ en h → let h' = cp τ en h in
                 mk⊩ᴿ (Split.fwd Sʳ τ (⊩rs h')) (Split.fwd Sᵉ τ (⊩es h'))
                      (⊩ts h') (⊩ss h') (Split.fwd Sᵈ τ (⊩ds h')) (⊩dfs h'))
      la
  where
    Sʳ = splits piecesʳ (rs R₀)
    Sᵉ = splits piecesᵉ (es R₀)
    Sᵈ = splits piecesᵈ (ds R₀)

-- A step: the residual left by the orderings it keeps open, moved by
-- its assignment

loc-ext : ∀ {Θ Φ} {O : Subst (Θ +e) Φ} {R : Resid Φ} → (L : Localised O R)
        → (σ : Subst Φ Φ) → (O ⨟ˢ σ) ≐ˢ O → KeepsAt O σ (lR L) → Drops σ (lR L)
        → (∀ α → sTy σ α ≡ tvar α) → Localised O R
loc-ext {O = O} {R} (loc σ₀ R₀ fx sn cp la) σ fσ st D@(drops Dʳ Dᵉ) ty =
  loc (σ₀ ⨟ˢ σ) (left D [ σ ]ᴿ)
      (≐ˢ-trans (≐ˢ-sym (⨟-assoc O σ₀ σ)) (≐ˢ-trans (⨟-congˡ fx σ) fσ))
      (λ δ Q h → let h' = ⊩ᴿ-subst {R = left D} {σ = σ} h in
                 ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-assoc σ₀ σ δ))
                   (sn (σ ⨟ˢ δ) Q (mk⊩ᴿ (Unsettled.back Dʳ δ (⊩rs h')) (Unsettled.back Dᵉ δ (⊩es h'))
                                        (⊩ts h') (⊩ss h') (⊩ds h') (⊩dfs h'))))
      (λ τ en h → let h' = st τ en (cp τ en h) in
                  ⊩ᴿ-subst⁻ (mk⊩ᴿ (λ m → ⊩rs h' (Unsettled.kept⊆ Dʳ m))
                                  (λ m → ⊩es h' (Unsettled.kept⊆ Dᵉ m))
                                  (⊩ts h') (⊩ss h') (⊩ds h') (⊩dfs h')))
      (λ a → atomic-subst σ ty (la a))

module _ {Θ Φ} (O : Subst (Θ +e) Φ) (R : Resid Φ) where

  passᵉ : List (Σ[ k ∈ EVar Φ ] (freeᵉ k O ≡ false)) → Localised O R → Localised O R × 𝔹
  passᵉ []             L = L , false
  passᵉ ((k , q) ∷ ks) L with stepᵉ k (lR L)
  ... | nothing      = passᵉ ks L
  ... | just (b , st , dr) =
        proj₁ (passᵉ ks (loc-ext L (updᵉ k b) (freeᵉ-fix k O q b) (λ τ en → st τ ∅ᴴ) dr (λ α → refl))) , true

  passʳ : List (Σ[ k ∈ RVar Φ ] (freeʳ k O ≡ false)) → Localised O R → Localised O R × 𝔹
  passʳ []             L = L , false
  passʳ ((k , q) ∷ ks) L with stepʳ k (lR L)
  ... | nothing      = passʳ ks L
  ... | just (b , st , dr) =
        proj₁ (passʳ ks (loc-ext L (updʳ k b) (freeʳ-fix k O q b) (λ τ en → st τ ∅ᴴ) dr (λ α → refl))) , true

  -- The local unknowns of each component identified at once

  collapseL : Localised O R → Localised O R × 𝔹
  collapseL L = go (collapse O (lR L))
    where
      go : Collapse O (lR L) → Localised O R × 𝔹
      go (collapsed σ false ty fx st) = L , false
      go (collapsed σ true  ty fx st) = loc-ext L σ fx (λ τ en → st τ ∅ᴴ) keepAll ty , true

  -- Where no step gives an unknown a value of its own, a set of them
  -- bounded below by the rigid is sent to the top

  raiseL : Localised O R → Maybe (Localised O R)
  raiseL L with evar? (sE O (newᵉ {Θ}))
  ... | nothing        = nothing
  ... | just (j , eqj) with Find.raise? O (lR L) j
  ...   | nothing = nothing
  ...   | just (raised l rc ue ur cl sd fx) =
          just (loc-ext L (tops l) (freeᴹ-fix l O fx)
                        (λ τ en h → raise-⊩ {Q₀ = ∅ᴴ} O eqj l rc ue ur cl sd τ en h)
                        keepAll (λ α → refl))

  -- A round: normal form, cycles identified, values given. Each round that
  -- changes something settles an unknown; the fuel is one round per unknown.

  rounds : ℕ → Localised O R → Localised O R
  rounds nzero    L = L
  rounds (nsuc n) L = values (collapseL (resettle (joined (lR L)) (loc-normal L)))
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

-- The rounds, with the settled atoms dropped before and after, the
-- images of `O` read from `memo O`

localise : ∀ {Θ Φ} → (O : Subst (Θ +e) Φ) → (R : Resid Φ) → Localised O R
localise {Φ = Φ} O R =
  loc-≐ (memo-≐ O) (loc-settle (rounds (memo O) R (nE Φ + nR Φ) (loc-settle loc-id)))

-- After localisation, the type of each disjunction left is eternal at
-- some instance

localise-ds : ∀ {Θ Φ} → (O : Subst (Θ +e) Φ) → (R : Resid Φ)
            → ∀ {A ρ} → (A , ρ) ∈ ds (lR (localise O R))
            → Σ[ αs ∈ List (TyVar Φ) ] (etDec A ≡ just αs)
localise-ds {Φ = Φ} O R =
  Refined.restᴱ (refine (Unsettled.kept (unsettled (settledᵈ (settleᴴ R')) (ds R'))))
  where
    R' = lR (rounds (memo O) R (nE Φ + nR Φ) (loc-settle loc-id))

-- An assignment the later substitution already agrees with is absorbed

updᵉ-absorb : ∀ {Ω Ω'} → (k : EVar Ω) → (b : EExp Ω) → (Y : Subst Ω Ω')
            → sE Y k ≡ b [ Y ]ᵉ → (updᵉ k b ⨟ˢ Y) ≐ˢ Y
updᵉ-absorb {Ω} k b Y q = mk≐ˢ (λ α → refl) (λ i → refl) e
  where
    e : (i : EVar Ω) → sE (updᵉ k b) i [ Y ]ᵉ ≡ sE Y i
    e i with i ≟ᶠ k
    ... | yes refl = sym q
    ... | no _     = refl
