------------------------------------------------------------------
-- The rounds of `localise` reach a fixed point or leave no local --
-- unknown                                                        --
--                                                                --
-- Every unknown of an ordering, of a disjunction's grade and of  --
-- a deferred entry is free in some `P`; a step sends a local     --
-- unknown free in `P` to a value over `P`'s other unknowns, and  --
-- so moves `P` to one free in fewer local unknowns. A round that --
-- changes nothing, and finds no set to raise, is a fixed point:  --
-- no step applies to any local unknown. The rounds are as many   --
-- as the unknowns, so they end at a fixed point, or with `P`     --
-- free in no local unknown.                                      --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; _∧_; not; true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; _+_; _≤_; _<_; z≤n; s≤s) renaming (zero to nzero; suc to nsuc)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-mono-≤; +-mono-<-≤; +-mono-≤-<; n≤1+n)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Unstuck.Rounds (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S using (Hyps; ∅ᴴ; mapᵖ; mapᵈ; Is-just?)
open import TypeInference.OpenSyntax.Instances S using (_↑ᵉⁿ_; _+eⁿ_)

open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-e; occᵉ-r; occʳ-r)
open import TypeInference.SolverImpl.Core.Rigid  S using (∨-true; ∨-left; ∨-right; dec-true; true-dec)
open import TypeInference.SolverImpl.Deferred S
  using (Dfr; Ords; nb; body; ors; oes; _[_]ᵈ; _[_]ᴼ; allOf; Dir; dir↓; dir↑; still?; stills?; fixedʳ?; fixedᵉ?)
open import TypeInference.SolverImpl.Resid    S
open import TypeInference.SolverImpl.Localise S
open import TypeInference.SolverImpl.Eliminate S using (joinₑ; joinᵣ)
open import TypeInference.SolverImpl.Canon S using (canonₑ; canonᵣ; canonSumₑ; canonSumᵣ)
open import TypeInference.SolverImpl.Product S using (Alts; alt; _∷⁺_; EAtom; RAtom; ⟦_⟧ᵉᵖ; ⟦_⟧ᵉᵖ⁺; ⟦_⟧ʳᵖ; ⟦_⟧ʳᵖ⁺; nrmₑ; nrmᵣ)
open import TypeInference.SolverImpl.Invariants.Canon S using (canonₑ-occ; canonᵣ-occʳ; canonᵣ-occᵉ)
open import TypeInference.SolverImpl.Invariants.Outer S

------------------------------------------------------------------------
-- Counting

c : 𝔹 → ℕ
c true  = 1
c false = 0

count : ∀ {n} → (Fin n → 𝔹) → ℕ
count {nzero}  f = 0
count {nsuc n} f = c (f zero) + count (λ i → f (suc i))

private

  c-≤ : ∀ {a b} → (a ≡ true → b ≡ true) → c a ≤ c b
  c-≤ {false} {b}     h = z≤n
  c-≤ {true}  {true}  h = ≤-refl
  c-≤ {true}  {false} h with h refl
  ... | ()

count-≤ : ∀ {n} → (f g : Fin n → 𝔹) → (∀ i → f i ≡ true → g i ≡ true) → count f ≤ count g
count-≤ {nzero}  f g h = z≤n
count-≤ {nsuc n} f g h =
  +-mono-≤ (c-≤ {f zero} {g zero} (h zero)) (count-≤ (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))

count-< : ∀ {n} → (f g : Fin n → 𝔹) → (∀ i → f i ≡ true → g i ≡ true)
        → (k : Fin n) → g k ≡ true → f k ≡ false → count f < count g
count-< {nsuc n} f g h zero    gk fk with f zero | g zero
... | false | true  = +-mono-<-≤ (s≤s z≤n) (count-≤ (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))
... | true  | _     with fk
...   | ()
count-< {nsuc n} f g h zero    () fk | false | false
count-< {nsuc n} f g h (suc k) gk fk =
  +-mono-≤-< (c-≤ {f zero} {g zero} (h zero)) (count-< (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)) k gk fk)

count-max : ∀ {n} → (f : Fin n → 𝔹) → count f ≤ n
count-max {nzero}  f = z≤n
count-max {nsuc n} f with f zero
... | true  = s≤s (count-max (λ i → f (suc i)))
... | false = ≤-trans (count-max (λ i → f (suc i))) (n≤1+n n)

count-0 : ∀ {n} → (f : Fin n → 𝔹) → count f ≡ 0 → ∀ i → f i ≡ false
count-0 {nsuc n} f q zero    with f zero | q
... | false | q' = refl
count-0 {nsuc n} f q (suc i) with f zero | q
... | false | q' = count-0 (λ i → f (suc i)) q' i

------------------------------------------------------------------------
-- The unknowns of a residual's orderings, disjunctions' grades and
-- deferred entries are among those free in `P`

record OuterO {Θ Ψ} (P : Subst Θ Ψ) (o : Ords Ψ) : Set where
  constructor outerO
  field
    oo-rs : ∀ {x y} → (x , y) ∈ ors o → Outerᵣ P x × Outerᵣ P y
    oo-es : ∀ {x y} → (x , y) ∈ oes o → Outerₑ P x × Outerₑ P y

open OuterO public

record AllIn {Θ Ψ} (P : Subst Θ Ψ) (R : Resid Ψ) : Set where
  constructor allIn
  field
    ai-rs  : ∀ {x y} → (x , y) ∈ rs R → Outerᵣ P x × Outerᵣ P y
    ai-es  : ∀ {x y} → (x , y) ∈ es R → Outerₑ P x × Outerₑ P y
    ai-ds  : ∀ {A ρ} → (A , ρ) ∈ ds R → Outerᵣ P ρ
    ai-dfs : ∀ {E} → E ∈ dfs R → OuterO (P ↑ᵉⁿ nb E) (body E)

open AllIn public

outerO-⊆ : ∀ {Θ Θ' Ψ} {P : Subst Θ Ψ} {P' : Subst Θ' Ψ} {o : Ords Ψ}
         → P ⊆ᶠ P' → OuterO P o → OuterO P' o
outerO-⊆ i (outerO r e) =
  outerO (λ {x} {y} m → outerᵣ-⊆ {ρ = x} i (proj₁ (r m)) , outerᵣ-⊆ {ρ = y} i (proj₂ (r m)))
         (λ {x} {y} m → outerₑ-⊆ {ε = x} i (proj₁ (e m)) , outerₑ-⊆ {ε = y} i (proj₂ (e m)))

allIn-⊆ : ∀ {Θ Θ' Ψ} {P : Subst Θ Ψ} {P' : Subst Θ' Ψ} {R : Resid Ψ}
        → P ⊆ᶠ P' → AllIn P R → AllIn P' R
allIn-⊆ i (allIn r e d f) =
  allIn (λ {x} {y} m → outerᵣ-⊆ {ρ = x} i (proj₁ (r m)) , outerᵣ-⊆ {ρ = y} i (proj₂ (r m)))
        (λ {x} {y} m → outerₑ-⊆ {ε = x} i (proj₁ (e m)) , outerₑ-⊆ {ε = y} i (proj₂ (e m)))
        (λ {A} {ρ} m → outerᵣ-⊆ {ρ = ρ} i (d m))
        (λ {E} m → outerO-⊆ (⊆ᶠ-↑ᵉⁿ (nb E) i) (f m))

outerO-⨟ : ∀ {Θ Ψ Ψ'} (P : Subst Θ Ψ) (σ : Subst Ψ Ψ') {o : Ords Ψ}
         → OuterO P o → OuterO (P ⨟ˢ σ) (o [ σ ]ᴼ)
outerO-⨟ P σ {o} (outerO r e) = outerO r' e'
  where
    r' : ∀ {x y} → (x , y) ∈ ors (o [ σ ]ᴼ) → Outerᵣ (P ⨟ˢ σ) x × Outerᵣ (P ⨟ˢ σ) y
    r' m with ∈-map⁻ (mapᵖ (_[ σ ]ʳ)) m
    ... | (x₀ , y₀) , m₀ , refl = outerᵣ-⨟ P σ {x₀} (proj₁ (r m₀)) , outerᵣ-⨟ P σ {y₀} (proj₂ (r m₀))

    e' : ∀ {x y} → (x , y) ∈ oes (o [ σ ]ᴼ) → Outerₑ (P ⨟ˢ σ) x × Outerₑ (P ⨟ˢ σ) y
    e' m with ∈-map⁻ (mapᵖ (_[ σ ]ᵉ)) m
    ... | (x₀ , y₀) , m₀ , refl = outerₑ-⨟ P σ {x₀} (proj₁ (e m₀)) , outerₑ-⨟ P σ {y₀} (proj₂ (e m₀))

allIn-⨟ : ∀ {Θ Ψ Ψ'} (P : Subst Θ Ψ) (σ : Subst Ψ Ψ') {R : Resid Ψ}
        → AllIn P R → AllIn (P ⨟ˢ σ) (R [ σ ]ᴿ)
allIn-⨟ P σ {R} (allIn r e d f) = allIn r' e' d' f'
  where
    r' : ∀ {x y} → (x , y) ∈ rs (R [ σ ]ᴿ) → Outerᵣ (P ⨟ˢ σ) x × Outerᵣ (P ⨟ˢ σ) y
    r' m with ∈-map⁻ (mapᵖ (_[ σ ]ʳ)) m
    ... | (x₀ , y₀) , m₀ , refl = outerᵣ-⨟ P σ {x₀} (proj₁ (r m₀)) , outerᵣ-⨟ P σ {y₀} (proj₂ (r m₀))

    e' : ∀ {x y} → (x , y) ∈ es (R [ σ ]ᴿ) → Outerₑ (P ⨟ˢ σ) x × Outerₑ (P ⨟ˢ σ) y
    e' m with ∈-map⁻ (mapᵖ (_[ σ ]ᵉ)) m
    ... | (x₀ , y₀) , m₀ , refl = outerₑ-⨟ P σ {x₀} (proj₁ (e m₀)) , outerₑ-⨟ P σ {y₀} (proj₂ (e m₀))

    d' : ∀ {A ρ} → (A , ρ) ∈ ds (R [ σ ]ᴿ) → Outerᵣ (P ⨟ˢ σ) ρ
    d' m with ∈-map⁻ (mapᵈ (_[ σ ]ᵛ) (_[ σ ]ʳ)) m
    ... | (A₀ , ρ₀) , m₀ , refl = outerᵣ-⨟ P σ {ρ₀} (d m₀)

    f' : ∀ {E} → E ∈ dfs (R [ σ ]ᴿ) → OuterO ((P ⨟ˢ σ) ↑ᵉⁿ nb E) (body E)
    f' m with ∈-map⁻ (_[ σ ]ᵈ) m
    ... | E₀ , m₀ , refl =
          outerO-⊆ (≐→⊆ᶠ (⨟-↑ᵉⁿ P σ (nb E₀))) (outerO-⨟ (P ↑ᵉⁿ nb E₀) (σ ↑ᵉⁿ nb E₀) (f m₀))
      where open import TypeInference.SolverImpl.Deferred S using (⨟-↑ᵉⁿ)

-- Every unknown is free in the identity

freeᵉ-id : ∀ {Ψ} → (k : EVar Ψ) → freeᵉ k (idˢ {Ψ}) ≡ true
freeᵉ-id {Ψ} k =
  ∨-right (anyᶠ (λ α → occᵉ-v k (sTy (idˢ {Ψ}) α))) _
    (∨-right (anyᶠ (λ i → occᵉ-r k (sR (idˢ {Ψ}) i))) _
      (anyᶠ-intro (λ i → occᵉ-e k (sE (idˢ {Ψ}) i)) k (dec-true (k ≟ᶠ k) refl)))
  where open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-v)

freeʳ-id : ∀ {Ψ} → (k : RVar Ψ) → freeʳ k (idˢ {Ψ}) ≡ true
freeʳ-id {Ψ} k =
  ∨-right (anyᶠ (λ α → occʳ-v k (sTy (idˢ {Ψ}) α))) _
    (anyᶠ-intro (λ i → occʳ-r k (sR (idˢ {Ψ}) i)) k (dec-true (k ≟ᶠ k) refl))
  where open import TypeInference.SolverImpl.Core.Occurs S using (occʳ-v)

↑ᵉⁿ-id : ∀ {Ψ} → (n : ℕ) → (idˢ {Ψ} ↑ᵉⁿ n) ≐ˢ idˢ
↑ᵉⁿ-id nzero    = ≐ˢ-refl
↑ᵉⁿ-id (nsuc n) = ≐ˢ-trans (≐ˢ-↑ᵉⁿ ↑ᵉ-id n) (↑ᵉⁿ-id n)
  where open import TypeInference.OpenSyntax.Instances S using (≐ˢ-↑ᵉⁿ)

allIn-id : ∀ {Ψ} → (R : Resid Ψ) → AllIn (idˢ {Ψ}) R
allIn-id {Ψ} R =
  allIn (λ {x} {y} _ → all-r x , all-r y) (λ {x} {y} _ → all-e x , all-e y) (λ {A} {ρ} _ → all-r ρ)
        (λ {E} _ → allO (nb E))
  where
    all-e : ∀ {Ψ'} (ε : EExp Ψ') → Outerₑ (idˢ {Ψ'}) ε
    all-e {Ψ'} ε {k} _ = freeᵉ-id {Ψ'} k
    all-r : ∀ {Ψ'} (ρ : RExp Ψ') → Outerᵣ (idˢ {Ψ'}) ρ
    all-r {Ψ'} ρ = (λ {k} _ → freeᵉ-id {Ψ'} k) , (λ {k} _ → freeʳ-id {Ψ'} k)
    allO : (n : ℕ) → {o : Ords (Ψ +eⁿ n)} → OuterO (idˢ {Ψ} ↑ᵉⁿ n) o
    allO n = outerO-⊆ (≐→⊆ᶠ (≐ˢ-sym (↑ᵉⁿ-id n)))
                      (outerO (λ {x} {y} _ → all-r x , all-r y) (λ {x} {y} _ → all-e x , all-e y))

------------------------------------------------------------------------
-- The local unknowns free in `P`, counted

module _ {Θ Θ' Ψ} (O : Subst Θ Ψ) (P : Subst Θ' Ψ) where

  localᵉ : EVar Ψ → 𝔹
  localᵉ i = not (freeᵉ i O) ∧ freeᵉ i P

  localʳ : RVar Ψ → 𝔹
  localʳ i = not (freeʳ i O) ∧ freeʳ i P

  cnt : ℕ
  cnt = count localᵉ + count localʳ

cnt-max : ∀ {Θ Θ' Ψ} (O : Subst Θ Ψ) (P : Subst Θ' Ψ) → cnt O P ≤ nE Ψ + nR Ψ
cnt-max O P = +-mono-≤ (count-max (localᵉ O P)) (count-max (localʳ O P))

-- with none counted, every unknown free in `P` is one the scope was
-- entered with

cnt-0 : ∀ {Θ Θ' Ψ} (O : Subst Θ Ψ) (P : Subst Θ' Ψ) → cnt O P ≡ 0 → P ⊆ᶠ O
cnt-0 O P q = mk⊆ᶠ e r
  where
    open import Data.Nat.Properties using (m+n≡0⇒m≡0; m+n≡0⇒n≡0)

    e : ∀ {k} → freeᵉ k P ≡ true → freeᵉ k O ≡ true
    e {k} p with freeᵉ k O in eo | count-0 (localᵉ O P) (m+n≡0⇒m≡0 _ q) k
    ... | true  | _ = refl
    ... | false | z with freeᵉ k P | p
    ...   | true | refl with z
    ...     | ()

    r : ∀ {k} → freeʳ k P ≡ true → freeʳ k O ≡ true
    r {k} p with freeʳ k O in eo | count-0 (localʳ O P) (m+n≡0⇒n≡0 (count (localᵉ O P)) q) k
    ... | true  | _ = refl
    ... | false | z with freeʳ k P | p
    ...   | true | refl with z
    ...     | ()

------------------------------------------------------------------------
-- A substitution that sends the unknowns free in `P` to expressions
-- over those unknowns other than the ones it drops

record Drops {Θ Ψ} (P : Subst Θ Ψ) (σ : Subst Ψ Ψ) (dE : EVar Ψ → 𝔹) (dR : RVar Ψ → 𝔹) : Set where
  constructor drops
  field
    dr-ty : ∀ α → sTy σ α ≡ tvar α
    dr-e  : ∀ {i k} → freeᵉ i P ≡ true → occᵉ-e k (sE σ i) ≡ true → (freeᵉ k P ≡ true) × (dE k ≡ false)
    dr-re : ∀ {i k} → freeʳ i P ≡ true → occᵉ-r k (sR σ i) ≡ true → (freeᵉ k P ≡ true) × (dE k ≡ false)
    dr-r  : ∀ {i k} → freeʳ i P ≡ true → occʳ-r k (sR σ i) ≡ true → (freeʳ k P ≡ true) × (dR k ≡ false)

module _ {Θ Ψ} {P : Subst Θ Ψ} {σ : Subst Ψ Ψ} {dE : EVar Ψ → 𝔹} {dR : RVar Ψ → 𝔹}
         (d : Drops P σ dE dR) where

  open Drops d
  open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-v; occʳ-v)

  private
    noTyᵉ : ∀ {α k} → occᵉ-v k (sTy σ α) ≡ true → ⊥
    noTyᵉ {α} q with sTy σ α | dr-ty α
    ... | .(tvar α) | refl with q
    ...   | ()

    noTyʳ : ∀ {α k} → occʳ-v k (sTy σ α) ≡ true → ⊥
    noTyʳ {α} q with sTy σ α | dr-ty α
    ... | .(tvar α) | refl with q
    ...   | ()

  dropsᵉ : ∀ {k} → freeᵉ k (P ⨟ˢ σ) ≡ true → (freeᵉ k P ≡ true) × (dE k ≡ false)
  dropsᵉ q with freeᵉ-⨟⁻ P σ q
  ... | inj₁ (α , r)             = ⊥-elim (noTyᵉ r)
  ... | inj₂ (inj₁ (i , p , s')) = dr-re p s'
  ... | inj₂ (inj₂ (i , p , s')) = dr-e p s'

  dropsʳ : ∀ {k} → freeʳ k (P ⨟ˢ σ) ≡ true → (freeʳ k P ≡ true) × (dR k ≡ false)
  dropsʳ q with freeʳ-⨟⁻ P σ q
  ... | inj₁ (α , r)       = ⊥-elim (noTyʳ r)
  ... | inj₂ (i , p , s')  = dr-r p s'

  drops-⊆ : (P ⨟ˢ σ) ⊆ᶠ P
  drops-⊆ = mk⊆ᶠ (λ q → proj₁ (dropsᵉ q)) (λ q → proj₁ (dropsʳ q))

  -- dropping a local unknown free in `P` counts one fewer

  drops-<ᵉ : ∀ {Θ₀} (O : Subst Θ₀ Ψ) → (k : EVar Ψ) → freeᵉ k O ≡ false → freeᵉ k P ≡ true → dE k ≡ true
           → cnt O (P ⨟ˢ σ) < cnt O P
  drops-<ᵉ O k lk fk dk =
    +-mono-<-≤ (count-< (localᵉ O (P ⨟ˢ σ)) (localᵉ O P) le k lP lS)
               (count-≤ (localʳ O (P ⨟ˢ σ)) (localʳ O P) lr)
    where
      le : ∀ i → localᵉ O (P ⨟ˢ σ) i ≡ true → localᵉ O P i ≡ true
      le i q with freeᵉ i O | freeᵉ i (P ⨟ˢ σ) in e
      ... | false | true = proj₁ (dropsᵉ e)
      ... | true  | _    with q
      ...   | ()
      le i () | false | false

      lr : ∀ i → localʳ O (P ⨟ˢ σ) i ≡ true → localʳ O P i ≡ true
      lr i q with freeʳ i O | freeʳ i (P ⨟ˢ σ) in e
      ... | false | true = proj₁ (dropsʳ e)
      ... | true  | _    with q
      ...   | ()
      lr i () | false | false

      lP : localᵉ O P k ≡ true
      lP rewrite lk | fk = refl

      lS : localᵉ O (P ⨟ˢ σ) k ≡ false
      lS with freeᵉ k (P ⨟ˢ σ) in e
      ... | false rewrite lk = refl
      ... | true with trans (sym dk) (proj₂ (dropsᵉ e))
      ...   | ()

  drops-<ʳ : ∀ {Θ₀} (O : Subst Θ₀ Ψ) → (k : RVar Ψ) → freeʳ k O ≡ false → freeʳ k P ≡ true → dR k ≡ true
           → cnt O (P ⨟ˢ σ) < cnt O P
  drops-<ʳ O k lk fk dk =
    +-mono-≤-< (count-≤ (localᵉ O (P ⨟ˢ σ)) (localᵉ O P) le)
               (count-< (localʳ O (P ⨟ˢ σ)) (localʳ O P) lr k lP lS)
    where
      le : ∀ i → localᵉ O (P ⨟ˢ σ) i ≡ true → localᵉ O P i ≡ true
      le i q with freeᵉ i O | freeᵉ i (P ⨟ˢ σ) in e
      ... | false | true = proj₁ (dropsᵉ e)
      ... | true  | _    with q
      ...   | ()
      le i () | false | false

      lr : ∀ i → localʳ O (P ⨟ˢ σ) i ≡ true → localʳ O P i ≡ true
      lr i q with freeʳ i O | freeʳ i (P ⨟ˢ σ) in e
      ... | false | true = proj₁ (dropsʳ e)
      ... | true  | _    with q
      ...   | ()
      lr i () | false | false

      lP : localʳ O P k ≡ true
      lP rewrite lk | fk = refl

      lS : localʳ O (P ⨟ˢ σ) k ≡ false
      lS with freeʳ k (P ⨟ˢ σ) in e
      ... | false rewrite lk = refl
      ... | true with trans (sym dk) (proj₂ (dropsʳ e))
      ...   | ()

------------------------------------------------------------------------
-- The assignments of `Localise` drop what they assign

private
  tf : true ≡ false → ⊥
  tf ()

  ≟-self : ∀ {n} (k : Fin n) → ⌊ k ≟ᶠ k ⌋ ≡ true
  ≟-self k = dec-true (k ≟ᶠ k) refl

  occ-var : ∀ {n} {k i : Fin n} → ⌊ k ≟ᶠ i ⌋ ≡ true → k ≡ i
  occ-var {k = k} {i} q with k ≟ᶠ i
  ... | yes e = e
  ... | no _  with q
  ...   | ()

drops-updᵉ : ∀ {Θ Ψ} {P : Subst Θ Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → Outerₑ P b → occᵉ-e k b ≡ false
           → Drops P (updᵉ k b) (λ i → ⌊ i ≟ᶠ k ⌋) (λ _ → false)
drops-updᵉ {Ψ = Ψ} {P = P} k b ob nb = drops (λ α → refl) e (λ {i} _ ()) r
  where
    e : ∀ {i k'} → freeᵉ i P ≡ true → occᵉ-e k' (sE (updᵉ k b) i) ≡ true
      → (freeᵉ k' P ≡ true) × (⌊ k' ≟ᶠ k ⌋ ≡ false)
    e {i} {k'} fi q with i ≟ᶠ k
    ... | yes refl = ob q , ne
      where
        ne : ⌊ k' ≟ᶠ k ⌋ ≡ false
        ne with k' ≟ᶠ k
        ... | no _     = refl
        ... | yes refl = ⊥-elim (tf (trans (sym q) nb))
    ... | no i≠k with occ-var {k = k'} {i} q
    ...   | refl = fi , ne
      where
        ne : ⌊ k' ≟ᶠ k ⌋ ≡ false
        ne with k' ≟ᶠ k
        ... | no _  = refl
        ... | yes e' = ⊥-elim (i≠k e')

    r : ∀ {i k'} → freeʳ i P ≡ true → occʳ-r k' (rvar {Ψ} i) ≡ true → (freeʳ k' P ≡ true) × (false ≡ false)
    r {i} {k'} fi q with occ-var {k = k'} {i} q
    ... | refl = fi , refl

drops-updʳ : ∀ {Θ Ψ} {P : Subst Θ Ψ} → (k : RVar Ψ) → (b : RExp Ψ) → Outerᵣ P b → occʳ-r k b ≡ false
           → Drops P (updʳ k b) (λ _ → false) (λ i → ⌊ i ≟ᶠ k ⌋)
drops-updʳ {Ψ = Ψ} {P = P} k b (obe , obr) nb = drops (λ α → refl) e re r
  where
    e : ∀ {i k'} → freeᵉ i P ≡ true → occᵉ-e k' (evar {Ψ} i) ≡ true → (freeᵉ k' P ≡ true) × (false ≡ false)
    e {i} {k'} fi q with occ-var {k = k'} {i} q
    ... | refl = fi , refl

    re : ∀ {i k'} → freeʳ i P ≡ true → occᵉ-r k' (sR (updʳ k b) i) ≡ true
       → (freeᵉ k' P ≡ true) × (false ≡ false)
    re {i} {k'} fi q with i ≟ᶠ k
    ... | yes refl = obe q , refl
    ... | no _     with q
    ...   | ()

    r : ∀ {i k'} → freeʳ i P ≡ true → occʳ-r k' (sR (updʳ k b) i) ≡ true
      → (freeʳ k' P ≡ true) × (⌊ k' ≟ᶠ k ⌋ ≡ false)
    r {i} {k'} fi q with i ≟ᶠ k
    ... | yes refl = obr q , ne
      where
        ne : ⌊ k' ≟ᶠ k ⌋ ≡ false
        ne with k' ≟ᶠ k
        ... | no _     = refl
        ... | yes refl = ⊥-elim (tf (trans (sym q) nb))
    ... | no i≠k with occ-var {k = k'} {i} q
    ...   | refl = fi , ne
      where
        ne : ⌊ k' ≟ᶠ k ⌋ ≡ false
        ne with k' ≟ᶠ k
        ... | no _  = refl
        ... | yes e' = ⊥-elim (i≠k e')

drops-tops : ∀ {Θ Ψ} {P : Subst Θ Ψ} → (l : List (Mem Ψ))
           → Drops P (tops l) (λ i → inᴱ i l) (λ i → inᴿ i l)
drops-tops {P = P} l = drops (λ α → refl) e (λ {i} {k'} → re {i} {k'}) r
  where
    e : ∀ {i k'} → freeᵉ i P ≡ true → occᵉ-e k' (topE (inᴱ i l) i) ≡ true
      → (freeᵉ k' P ≡ true) × (inᴱ k' l ≡ false)
    e {i} {k'} fi q with inᴱ i l in ei
    ... | true  with q
    ...   | ()
    e {i} {k'} fi q | false with occ-var {k = k'} {i} q
    ...   | refl = fi , ei

    re : ∀ {i k'} → freeʳ i P ≡ true → occᵉ-r k' (topR (inᴿ i l) i) ≡ true
       → (freeᵉ k' P ≡ true) × (inᴱ k' l ≡ false)
    re {i} {k'} fi q with inᴿ i l
    ... | true  with q
    ...   | ()
    re {i} {k'} fi q | false with q
    ...   | ()

    r : ∀ {i k'} → freeʳ i P ≡ true → occʳ-r k' (topR (inᴿ i l) i) ≡ true
      → (freeʳ k' P ≡ true) × (inᴿ k' l ≡ false)
    r {i} {k'} fi q with inᴿ i l in ei
    ... | true  with q
    ...   | ()
    r {i} {k'} fi q | false with occ-var {k = k'} {i} q
    ...   | refl = fi , ei

------------------------------------------------------------------------
-- An unknown a deferred entry moves under an assignment is free in `P`

private
  moved-e : ∀ {Ψ} (σ : Subst Ψ Ψ) → (x : EExp Ψ) → ¬ (x [ σ ]ᵉ ≡ x)
          → Σ[ i ∈ EVar Ψ ] ((occᵉ-e i x ≡ true) × ¬ (sE σ i ≡ evar i))
  moved-e σ (evar i)   n = i , ≟-self i , n
  moved-e σ (econst c) n = ⊥-elim (n refl)
  moved-e σ (a ·̂ₑ b)   n with a [ σ ]ᵉ ≟ᵉ a | b [ σ ]ᵉ ≟ᵉ b
  ... | yes p | yes q = ⊥-elim (n (cong₂ _·̂ₑ_ p q))
  ... | no p  | _     with moved-e σ a p
  ...   | i , o , m = i , ∨-left (occᵉ-e i a) (occᵉ-e i b) o , m
  moved-e σ (a ·̂ₑ b)   n | yes _ | no q with moved-e σ b q
  ...   | i , o , m = i , ∨-right (occᵉ-e i a) (occᵉ-e i b) o , m
  moved-e σ (a ⊔̂ₑ b)   n with a [ σ ]ᵉ ≟ᵉ a | b [ σ ]ᵉ ≟ᵉ b
  ... | yes p | yes q = ⊥-elim (n (cong₂ _⊔̂ₑ_ p q))
  ... | no p  | _     with moved-e σ a p
  ...   | i , o , m = i , ∨-left (occᵉ-e i a) (occᵉ-e i b) o , m
  moved-e σ (a ⊔̂ₑ b)   n | yes _ | no q with moved-e σ b q
  ...   | i , o , m = i , ∨-right (occᵉ-e i a) (occᵉ-e i b) o , m

  Movedʳ : ∀ {Ψ} → Subst Ψ Ψ → RExp Ψ → Set
  Movedʳ {Ψ} σ x = (Σ[ i ∈ EVar Ψ ] ((occᵉ-r i x ≡ true) × ¬ (sE σ i ≡ evar i)))
             ⊎ (Σ[ i ∈ RVar Ψ ] ((occʳ-r i x ≡ true) × ¬ (sR σ i ≡ rvar i)))

  moved-r : ∀ {Ψ} (σ : Subst Ψ Ψ) → (x : RExp Ψ) → ¬ (x [ σ ]ʳ ≡ x) → Movedʳ σ x
  moved-r σ (rvar i)   n = inj₂ (i , ≟-self i , n)
  moved-r σ (rconst c) n = ⊥-elim (n refl)
  moved-r σ (a ·̂ᵣ b)   n with a [ σ ]ʳ ≟ʳ a | b [ σ ]ʳ ≟ʳ b
  ... | yes p | yes q = ⊥-elim (n (cong₂ _·̂ᵣ_ p q))
  ... | no p  | _     = lft (moved-r σ a p)
    where
      lft : Movedʳ σ a → Movedʳ σ (a ·̂ᵣ b)
      lft (inj₁ (i , o , m)) = inj₁ (i , ∨-left (occᵉ-r i a) (occᵉ-r i b) o , m)
      lft (inj₂ (i , o , m)) = inj₂ (i , ∨-left (occʳ-r i a) (occʳ-r i b) o , m)
  ... | yes _ | no q  = rgt (moved-r σ b q)
    where
      rgt : Movedʳ σ b → Movedʳ σ (a ·̂ᵣ b)
      rgt (inj₁ (i , o , m)) = inj₁ (i , ∨-right (occᵉ-r i a) (occᵉ-r i b) o , m)
      rgt (inj₂ (i , o , m)) = inj₂ (i , ∨-right (occʳ-r i a) (occʳ-r i b) o , m)
  moved-r σ (a ⊔̂ᵣ b)   n with a [ σ ]ʳ ≟ʳ a | b [ σ ]ʳ ≟ʳ b
  ... | yes p | yes q = ⊥-elim (n (cong₂ _⊔̂ᵣ_ p q))
  ... | no p  | _     = lft (moved-r σ a p)
    where
      lft : Movedʳ σ a → Movedʳ σ (a ⊔̂ᵣ b)
      lft (inj₁ (i , o , m)) = inj₁ (i , ∨-left (occᵉ-r i a) (occᵉ-r i b) o , m)
      lft (inj₂ (i , o , m)) = inj₂ (i , ∨-left (occʳ-r i a) (occʳ-r i b) o , m)
  ... | yes _ | no q  = rgt (moved-r σ b q)
    where
      rgt : Movedʳ σ b → Movedʳ σ (a ⊔̂ᵣ b)
      rgt (inj₁ (i , o , m)) = inj₁ (i , ∨-right (occᵉ-r i a) (occᵉ-r i b) o , m)
      rgt (inj₂ (i , o , m)) = inj₂ (i , ∨-right (occʳ-r i a) (occʳ-r i b) o , m)
  moved-r σ ∣ ε ∣̂ᵉ     n with ε [ σ ]ᵉ ≟ᵉ ε
  ... | yes p = ⊥-elim (n (cong ∣_∣̂ᵉ p))
  ... | no p with moved-e σ ε p
  ...   | i , o , m = inj₁ (i , o , m)

-- under the rigid, the unknown moved is the same one, shifted

free-↑ᵉ : ∀ {Θ Ψ} (P : Subst Θ Ψ) → ∀ {k} → freeᵉ (suc k) (P ↑ᵉ) ≡ true → freeᵉ k P ≡ true
free-↑ᵉ {Ψ = Ψ} P {k} q with freeᵉ-,ᵉ⁻ (P ⨟ˢ wkˢᵉ) (evar (newᵉ {Ψ})) (trans (sym (freeᵉ-≐ (↑ᵉ-≐ P) (suc k))) q)
... | inj₁ ()
... | inj₂ q' with freeᵉ-⨟⁻ P wkˢᵉ q'
...   | inj₁ (α , ())
...   | inj₂ (inj₁ (i , p , ()))
...   | inj₂ (inj₂ (i , p , s')) with occ-var {k = suc k} {suc i} s'
...     | refl = p

freeʳ-↑ᵉ : ∀ {Θ Ψ} (P : Subst Θ Ψ) → ∀ {k} → freeʳ k (P ↑ᵉ) ≡ true → freeʳ k P ≡ true
freeʳ-↑ᵉ {Ψ = Ψ} P {k} q with freeʳ-⨟⁻ P wkˢᵉ (trans (sym (freeʳ-≐ (↑ᵉ-≐ P) k)) q)
... | inj₁ (α , ())
... | inj₂ (i , p , s') with occ-var {k = k} {i} s'
...   | refl = p

-- An effect-grade assignment moves only its own unknown, lifted over
-- the entry's rigids

MovesOnlyᵉ : ∀ {Ψ} → Subst Ψ Ψ → EVar Ψ → Set
MovesOnlyᵉ σ k = (∀ i → ¬ (sE σ i ≡ evar i) → i ≡ k) × (∀ i → sR σ i ≡ rvar i)

MovesOnlyʳ : ∀ {Ψ} → Subst Ψ Ψ → RVar Ψ → Set
MovesOnlyʳ σ k = (∀ i → sE σ i ≡ evar i) × (∀ i → ¬ (sR σ i ≡ rvar i) → i ≡ k)

private
  wk-var : ∀ {Ψ} {x : EExp Ψ} {i : EVar Ψ} → wkᵉ-e x ≡ evar (suc i) → x ≡ evar i
  wk-var {x = evar j} refl = refl
  wk-var {x = econst _} ()
  wk-var {x = _ ·̂ₑ _} ()
  wk-var {x = _ ⊔̂ₑ _} ()

  wk-rvar : ∀ {Ψ} {x : RExp Ψ} {i : RVar Ψ} → wkᵉ-r x ≡ rvar i → x ≡ rvar i
  wk-rvar {x = rvar j} refl = refl
  wk-rvar {x = rconst _} ()
  wk-rvar {x = _ ·̂ᵣ _} ()
  wk-rvar {x = _ ⊔̂ᵣ _} ()
  wk-rvar {x = ∣ _ ∣̂ᵉ} ()

movesᵉ-↑ : ∀ {Ψ} {σ : Subst Ψ Ψ} {k : EVar Ψ} → MovesOnlyᵉ σ k → MovesOnlyᵉ (σ ↑ᵉ) (suc k)
movesᵉ-↑ {σ = σ} {k} (me , mr) = e , r
  where
    e : ∀ i → ¬ (sE (σ ↑ᵉ) i ≡ evar i) → i ≡ suc k
    e zero    n = ⊥-elim (n refl)
    e (suc i) n = cong suc (me i (λ q → n (cong wkᵉ-e q)))
    r : ∀ i → sR (σ ↑ᵉ) i ≡ rvar i
    r i rewrite mr i = refl

movesʳ-↑ : ∀ {Ψ} {σ : Subst Ψ Ψ} {k : RVar Ψ} → MovesOnlyʳ σ k → MovesOnlyʳ (σ ↑ᵉ) k
movesʳ-↑ {σ = σ} {k} (me , mr) = e , r
  where
    e : ∀ i → sE (σ ↑ᵉ) i ≡ evar i
    e zero    = refl
    e (suc i) rewrite me i = refl
    r : ∀ i → ¬ (sR (σ ↑ᵉ) i ≡ rvar i) → i ≡ k
    r i n = mr i (λ q → n (cong wkᵉ-r q))

movedᵉ-e : ∀ n {Θ Ψ} (P : Subst Θ Ψ) (σ : Subst Ψ Ψ) (k : EVar Ψ) → MovesOnlyᵉ σ k
         → (x : EExp (Ψ +eⁿ n)) → Outerₑ (P ↑ᵉⁿ n) x → ¬ (x [ σ ↑ᵉⁿ n ]ᵉ ≡ x) → freeᵉ k P ≡ true
movedᵉ-e nzero    P σ k mo x o n with moved-e σ x n
... | i , oc , m with proj₁ mo i m
...   | refl = o oc
movedᵉ-e (nsuc n) P σ k mo x o nx = free-↑ᵉ P (movedᵉ-e n (P ↑ᵉ) (σ ↑ᵉ) (suc k) (movesᵉ-↑ mo) x o nx)

movedᵉ-r : ∀ n {Θ Ψ} (P : Subst Θ Ψ) (σ : Subst Ψ Ψ) (k : EVar Ψ) → MovesOnlyᵉ σ k
         → (x : RExp (Ψ +eⁿ n)) → Outerᵣ (P ↑ᵉⁿ n) x → ¬ (x [ σ ↑ᵉⁿ n ]ʳ ≡ x) → freeᵉ k P ≡ true
movedᵉ-r nzero    P σ k mo x o n with moved-r σ x n
... | inj₁ (i , oc , m) with proj₁ mo i m
...   | refl = proj₁ o oc
movedᵉ-r nzero    P σ k mo x o n | inj₂ (i , oc , m) = ⊥-elim (m (proj₂ mo i))
movedᵉ-r (nsuc n) P σ k mo x o nx = free-↑ᵉ P (movedᵉ-r n (P ↑ᵉ) (σ ↑ᵉ) (suc k) (movesᵉ-↑ mo) x o nx)

movedʳ-e : ∀ n {Θ Ψ} (P : Subst Θ Ψ) (σ : Subst Ψ Ψ) (k : RVar Ψ) → MovesOnlyʳ σ k
         → (x : EExp (Ψ +eⁿ n)) → ¬ (x [ σ ↑ᵉⁿ n ]ᵉ ≡ x) → ⊥
movedʳ-e nzero    P σ k mo x n with moved-e σ x n
... | i , oc , m = m (proj₁ mo i)
movedʳ-e (nsuc n) P σ k mo x nx = movedʳ-e n (P ↑ᵉ) (σ ↑ᵉ) k (movesʳ-↑ mo) x nx

movedʳ-r : ∀ n {Θ Ψ} (P : Subst Θ Ψ) (σ : Subst Ψ Ψ) (k : RVar Ψ) → MovesOnlyʳ σ k
         → (x : RExp (Ψ +eⁿ n)) → Outerᵣ (P ↑ᵉⁿ n) x → ¬ (x [ σ ↑ᵉⁿ n ]ʳ ≡ x) → freeʳ k P ≡ true
movedʳ-r nzero    P σ k mo x o n with moved-r σ x n
... | inj₁ (i , oc , m) = ⊥-elim (m (proj₁ mo i))
... | inj₂ (i , oc , m) with proj₂ mo i m
...   | refl = proj₂ o oc
movedʳ-r (nsuc n) P σ k mo x o nx = freeʳ-↑ᵉ P (movedʳ-r n (P ↑ᵉ) (σ ↑ᵉ) k (movesʳ-↑ mo) x o nx)

Side : ∀ {X : Set} → Dir → X → X → X
Side dir↓ x y = y
Side dir↑ x y = x

private
  allOf-nothing : ∀ {X : Set} {P : X → Set} → (f : (a : X) → Maybe (P a)) → (l : List X)
                → allOf f l ≡ nothing → Σ[ a ∈ X ] ((a ∈ l) × (f a ≡ nothing))
  allOf-nothing f (a ∷ l) q with f a in e | allOf f l in e'
  ... | nothing | _       = a , here refl , e
  ... | just _  | nothing with allOf-nothing f l e'
  ...   | b , m , e'' = b , there m , e''
  allOf-nothing f (a ∷ l) () | just _ | just _
  allOf-nothing f []      ()

  still?-nothing : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (E : Dfr Ψ) → still? d σ E ≡ nothing
                 → (Σ[ a ∈ RExp (Ψ +eⁿ nb E) × RExp (Ψ +eⁿ nb E) ] ((a ∈ ors (body E)) × (fixedʳ? d (σ ↑ᵉⁿ nb E) a ≡ nothing)))
                 ⊎ (Σ[ a ∈ EExp (Ψ +eⁿ nb E) × EExp (Ψ +eⁿ nb E) ] ((a ∈ oes (body E)) × (fixedᵉ? d (σ ↑ᵉⁿ nb E) a ≡ nothing)))
  still?-nothing d σ E q
    with allOf (fixedʳ? d (σ ↑ᵉⁿ nb E)) (ors (body E)) in er
       | allOf (fixedᵉ? d (σ ↑ᵉⁿ nb E)) (oes (body E)) in ee
  ... | nothing | _       = inj₁ (allOf-nothing _ (ors (body E)) er)
  ... | just _  | nothing = inj₂ (allOf-nothing _ (oes (body E)) ee)
  still?-nothing d σ E () | just _ | just _

  fixedʳ?-nothing : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (x y : RExp Ψ)
                  → fixedʳ? d σ (x , y) ≡ nothing → ¬ (Side d x y [ σ ]ʳ ≡ Side d x y)
  fixedʳ?-nothing dir↓ σ x y q with y [ σ ]ʳ ≟ʳ y
  ... | no n  = n
  fixedʳ?-nothing dir↓ σ x y () | yes _
  fixedʳ?-nothing dir↑ σ x y q with x [ σ ]ʳ ≟ʳ x
  ... | no n  = n
  fixedʳ?-nothing dir↑ σ x y () | yes _

  fixedᵉ?-nothing : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (x y : EExp Ψ)
                  → fixedᵉ? d σ (x , y) ≡ nothing → ¬ (Side d x y [ σ ]ᵉ ≡ Side d x y)
  fixedᵉ?-nothing dir↓ σ x y q with y [ σ ]ᵉ ≟ᵉ y
  ... | no n  = n
  fixedᵉ?-nothing dir↓ σ x y () | yes _
  fixedᵉ?-nothing dir↑ σ x y q with x [ σ ]ᵉ ≟ᵉ x
  ... | no n  = n
  fixedᵉ?-nothing dir↑ σ x y () | yes _

  side-outer : ∀ {X : Set} (O : X → Set) (d : Dir) {x y : X} → O x × O y → O (Side d x y)
  side-outer O dir↓ (_ , oy) = oy
  side-outer O dir↑ (ox , _) = ox

-- An unknown some deferred entry does not keep still under its
-- assignment is free in `P`

stills-freeᵉ : ∀ {Θ Ψ} {P : Subst Θ Ψ} {R : Resid Ψ} → AllIn P R → (d : Dir) → (σ : Subst Ψ Ψ) → (k : EVar Ψ)
             → MovesOnlyᵉ σ k → stills? d σ (dfs R) ≡ nothing → freeᵉ k P ≡ true
stills-freeᵉ {P = P} {R} ai d σ k mo q with allOf-nothing (still? d σ) (dfs R) q
... | E , mE , qE with still?-nothing d σ E qE
...   | inj₁ ((x , y) , m , qf) =
        movedᵉ-r (nb E) P σ k mo (Side d x y)
                 (side-outer (Outerᵣ (P ↑ᵉⁿ nb E)) d {x} {y} (oo-rs (ai-dfs ai mE) m))
                 (fixedʳ?-nothing d (σ ↑ᵉⁿ nb E) x y qf)
...   | inj₂ ((x , y) , m , qf) =
        movedᵉ-e (nb E) P σ k mo (Side d x y)
                 (side-outer (Outerₑ (P ↑ᵉⁿ nb E)) d {x} {y} (oo-es (ai-dfs ai mE) m))
                 (fixedᵉ?-nothing d (σ ↑ᵉⁿ nb E) x y qf)

stills-freeʳ : ∀ {Θ Ψ} {P : Subst Θ Ψ} {R : Resid Ψ} → AllIn P R → (d : Dir) → (σ : Subst Ψ Ψ) → (k : RVar Ψ)
             → MovesOnlyʳ σ k → stills? d σ (dfs R) ≡ nothing → freeʳ k P ≡ true
stills-freeʳ {P = P} {R} ai d σ k mo q with allOf-nothing (still? d σ) (dfs R) q
... | E , mE , qE with still?-nothing d σ E qE
...   | inj₁ ((x , y) , m , qf) =
        movedʳ-r (nb E) P σ k mo (Side d x y)
                 (side-outer (Outerᵣ (P ↑ᵉⁿ nb E)) d {x} {y} (oo-rs (ai-dfs ai mE) m))
                 (fixedʳ?-nothing d (σ ↑ᵉⁿ nb E) x y qf)
...   | inj₂ ((x , y) , m , qf) =
        ⊥-elim (movedʳ-e (nb E) P σ k mo (Side d x y) (fixedᵉ?-nothing d (σ ↑ᵉⁿ nb E) x y qf))

movesᵉ-upd : ∀ {Ψ} (k : EVar Ψ) (b : EExp Ψ) → MovesOnlyᵉ (updᵉ k b) k
movesᵉ-upd k b = e , (λ i → refl)
  where
    e : ∀ i → ¬ (sE (updᵉ k b) i ≡ evar i) → i ≡ k
    e i n with i ≟ᶠ k
    ... | yes q = q
    ... | no _  = ⊥-elim (n refl)

movesʳ-upd : ∀ {Ψ} (k : RVar Ψ) (b : RExp Ψ) → MovesOnlyʳ (updʳ k b) k
movesʳ-upd k b = (λ i → refl) , r
  where
    r : ∀ i → ¬ (sR (updʳ k b) i ≡ rvar i) → i ≡ k
    r i n with i ≟ᶠ k
    ... | yes q = q
    ... | no _  = ⊥-elim (n refl)

------------------------------------------------------------------------
-- A step sends an unknown that occurs to a value over the others

private
  anyL-true : ∀ {X : Set} (f : X → 𝔹) (l : List X) → anyL f l ≡ true → Σ[ a ∈ X ] ((a ∈ l) × (f a ≡ true))
  anyL-true f (a ∷ l) q with f a in e
  ... | true  = a , here refl , e
  ... | false with anyL-true f l q
  ...   | b , m , e' = b , there m , e'

  first-just : ∀ {X : Set} (x y : Maybe X) {z : X} → first x y ≡ just z
             → (x ≡ just z) ⊎ ((x ≡ nothing) × (y ≡ just z))
  first-just (just x) y q = inj₁ q
  first-just nothing  y q = inj₂ (refl , q)

  nj : ∀ {A : Set} {a : A} → nothing ≡ just a → ⊥
  nj ()

  just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  failed-nothing : ∀ {X : Set} {m : Maybe X} → failed m ≡ true → m ≡ nothing
  failed-nothing {m = nothing} _ = refl

  joinₑ-occ : ∀ {Ψ} (x : EExp Ψ) (xs : List (EExp Ψ)) {i}
            → occᵉ-e i (joinₑ x xs) ≡ true → Σ[ x' ∈ EExp Ψ ] ((x' ∈ x ∷ xs) × (occᵉ-e i x' ≡ true))
  joinₑ-occ x []        q = x , here refl , q
  joinₑ-occ x (y ∷ xs) {i} q with joinₑ-occ (x ⊔̂ₑ y) xs q
  ... | x' , here refl , q' with ∨-true (occᵉ-e i x) (occᵉ-e i y) q'
  ...   | inj₁ r = x , here refl , r
  ...   | inj₂ r = y , there (here refl) , r
  joinₑ-occ x (y ∷ xs) q | x' , there m , q' = x' , there (there m) , q'

  joinᵣ-occ : ∀ {Ψ} (x : RExp Ψ) (xs : List (RExp Ψ))
            → (∀ {i} → occᵉ-r i (joinᵣ x xs) ≡ true → Σ[ x' ∈ RExp Ψ ] ((x' ∈ x ∷ xs) × (occᵉ-r i x' ≡ true)))
            × (∀ {i} → occʳ-r i (joinᵣ x xs) ≡ true → Σ[ x' ∈ RExp Ψ ] ((x' ∈ x ∷ xs) × (occʳ-r i x' ≡ true)))
  joinᵣ-occ x []       = (λ q → x , here refl , q) , (λ q → x , here refl , q)
  joinᵣ-occ x (y ∷ xs) = e , r
    where
      e : ∀ {i} → occᵉ-r i (joinᵣ (x ⊔̂ᵣ y) xs) ≡ true → _
      e {i} q with proj₁ (joinᵣ-occ (x ⊔̂ᵣ y) xs) q
      ... | x' , here refl , q' with ∨-true (occᵉ-r i x) (occᵉ-r i y) q'
      ...   | inj₁ s = x , here refl , s
      ...   | inj₂ s = y , there (here refl) , s
      e q | x' , there m , q' = x' , there (there m) , q'
      r : ∀ {i} → occʳ-r i (joinᵣ (x ⊔̂ᵣ y) xs) ≡ true → _
      r {i} q with proj₂ (joinᵣ-occ (x ⊔̂ᵣ y) xs) q
      ... | x' , here refl , q' with ∨-true (occʳ-r i x) (occʳ-r i y) q'
      ...   | inj₁ s = x , here refl , s
      ...   | inj₂ s = y , there (here refl) , s
      r q | x' , there m , q' = x' , there (there m) , q'

record Sound {Θ Ψ} (P : Subst Θ Ψ) (k : EVar Ψ) (b : EExp Ψ) : Set where
  constructor sound
  field
    s-free : freeᵉ k P ≡ true
    s-out  : Outerₑ P b
    s-fr   : occᵉ-e k b ≡ false

record Soundʳ {Θ Ψ} (P : Subst Θ Ψ) (k : RVar Ψ) (b : RExp Ψ) : Set where
  constructor soundʳ
  field
    s-free : freeʳ k P ≡ true
    s-out  : Outerᵣ P b
    s-fr   : occʳ-r k b ≡ false

module _ {Θ Ψ} {P : Subst Θ Ψ} {R : Resid Ψ} (ai : AllIn P R) where

  private
    k-in : ∀ {k : EVar Ψ} {x} → (x , evar k) ∈ es R → freeᵉ k P ≡ true
    k-in {k} m = proj₂ (ai-es ai m) (≟-self k)

    k-inˡ : ∀ {k : EVar Ψ} {x} → (evar k , x) ∈ es R → freeᵉ k P ≡ true
    k-inˡ {k} m = proj₁ (ai-es ai m) (≟-self k)

  occursᵉ-free : ∀ k → occursᵉ k R ≡ true → freeᵉ k P ≡ true
  occursᵉ-free k q with ∨-true (anyL _ (es R)) _ q
  ... | inj₁ r with anyL-true _ (es R) r
  ...   | (x , y) , m , o = proj₁ (ai-es ai m) o
  occursᵉ-free k q | inj₂ q₁ with ∨-true (anyL _ (rs R)) _ q₁
  ... | inj₁ r with anyL-true _ (rs R) r
  ...   | (x , y) , m , o = proj₁ (proj₁ (ai-rs ai m)) o
  occursᵉ-free k q | inj₂ q₁ | inj₂ q₂ with ∨-true (anyL _ (ds R)) _ q₂
  ... | inj₁ r with anyL-true _ (ds R) r
  ...   | (A , ρ) , m , o = proj₁ (ai-ds ai m) o
  occursᵉ-free k q | inj₂ q₁ | inj₂ q₂ | inj₂ q₃ with ∨-true (inDfsᵉ dir↑ k R) _ q₃
  ... | inj₁ r = stills-freeᵉ ai dir↑ _ k (movesᵉ-upd k (econst ⊤ₑ)) (failed-nothing r)
  ... | inj₂ r = stills-freeᵉ ai dir↓ _ k (movesᵉ-upd k (econst ⊤ₑ)) (failed-nothing r)

  occursᵉ⁺-free : ∀ k → occursᵉ⁺ k R ≡ true → freeᵉ k P ≡ true
  occursᵉ⁺-free k q with ∨-true (anyL _ (es R)) _ q
  ... | inj₁ r with anyL-true _ (es R) r
  ...   | (x , y) , m , o = proj₂ (ai-es ai m) o
  occursᵉ⁺-free k q | inj₂ q₁ with ∨-true (anyL _ (rs R)) _ q₁
  ... | inj₁ r with anyL-true _ (rs R) r
  ...   | (x , y) , m , o = proj₁ (proj₂ (ai-rs ai m)) o
  occursᵉ⁺-free k q | inj₂ q₁ | inj₂ r =
    stills-freeᵉ ai dir↓ _ k (movesᵉ-upd k (econst ⊤ₑ)) (failed-nothing r)

  occursʳ-free : ∀ k → occursʳ k R ≡ true → freeʳ k P ≡ true
  occursʳ-free k q with ∨-true (anyL _ (rs R)) _ q
  ... | inj₁ r with anyL-true _ (rs R) r
  ...   | (x , y) , m , o = proj₂ (proj₁ (ai-rs ai m)) o
  occursʳ-free k q | inj₂ q₁ with ∨-true (anyL _ (ds R)) _ q₁
  ... | inj₁ r with anyL-true _ (ds R) r
  ...   | (A , ρ) , m , o = proj₂ (ai-ds ai m) o
  occursʳ-free k q | inj₂ q₁ | inj₂ q₂ with ∨-true (inDfsʳ dir↑ k R) _ q₂
  ... | inj₁ r = stills-freeʳ ai dir↑ _ k (movesʳ-upd k (rconst ⊤ᵣ)) (failed-nothing r)
  ... | inj₂ r = stills-freeʳ ai dir↓ _ k (movesʳ-upd k (rconst ⊤ᵣ)) (failed-nothing r)

  occursʳ⁺-free : ∀ k → occursʳ⁺ k R ≡ true → freeʳ k P ≡ true
  occursʳ⁺-free k q with ∨-true (anyL _ (rs R)) _ q
  ... | inj₁ r with anyL-true _ (rs R) r
  ...   | (x , y) , m , o = proj₂ (proj₂ (ai-rs ai m)) o
  occursʳ⁺-free k q | inj₂ r = stills-freeʳ ai dir↓ _ k (movesʳ-upd k (rconst ⊤ᵣ)) (failed-nothing r)

  -- each rule

  stepᵉ-sound : ∀ k {r} → stepᵉ k R ≡ just r → Sound P k (proj₁ r)
  stepᵉ-sound k {r} eq with cleanᵉ? k R
  ... | nothing = ⊥-elim (nj eq)
  ... | just cl = go (first-just Lo _ eq)
    where
      Lo = lowerᵉ? k R cl (Bᵉ.lowsOf {Ψ} k (es R)) (Bᵉʳ.freeRs {Ψ} k (rs R))
      Ra = raiseᵉ? k R cl (Bᵉ.upsOf {Ψ} k (es R)) (Bᵉʳ.freeLs {Ψ} k (rs R)) (dfreeᵉ? k R)
      Un = unitᵉ? k R cl (Is-just? uₑ-least?) (Bᵉ.lowsOf {Ψ} k (es R)) (Bᵉʳ.freeRs {Ψ} k (rs R))
                  (occursᵉ k R)
      To = topᵉ? k R cl (Bᵉ.freeLs {Ψ} k (es R)) (Bᵉʳ.freeLs {Ψ} k (rs R)) (dfreeᵉ? k R) (occursᵉ⁺ k R)

      lower : ∀ L F → lowerᵉ? k R cl L F ≡ just r → Sound P k (proj₁ r)
      lower (just (Bᵉ.lows (x ∷ xs) c s f)) (just fr) q
        with stills? dir↓ (updᵉ k (joinₑ x xs)) (dfs R)
      ... | just sd rewrite sym (cong proj₁ (just-inj q)) =
            sound (k-in (s (here refl))) (λ o → case (joinₑ-occ x xs o)) (fr' (occᵉ-e k (joinₑ x xs)) refl)
        where
          case : ∀ {i} → Σ[ x' ∈ EExp Ψ ] ((x' ∈ x ∷ xs) × (occᵉ-e i x' ≡ true)) → freeᵉ i P ≡ true
          case (x' , m , o) = proj₁ (ai-es ai (s m)) o
          fr' : (w : 𝔹) → occᵉ-e k (joinₑ x xs) ≡ w → w ≡ false
          fr' false _ = refl
          fr' true  e with joinₑ-occ x xs e
          ... | x' , m , o with trans (sym o) (f m)
          ...   | ()
      ... | nothing = ⊥-elim (nj q)
      lower (just (Bᵉ.lows [] c s f)) (just fr) ()
      lower (just (Bᵉ.lows (x ∷ xs) c s f)) nothing ()
      lower (just (Bᵉ.lows [] c s f)) nothing ()
      lower nothing F ()

      raise : ∀ U F D → raiseᵉ? k R cl U F D ≡ just r → Sound P k (proj₁ r)
      raise (just up) (just fl) (just df) q with stills? dir↑ (updᵉ k (Bᵉ.cap up)) (dfs R)
      ... | just sd rewrite sym (cong proj₁ (just-inj q)) =
            sound (k-inˡ (Bᵉ.srcᵘ up)) (proj₂ (ai-es ai (Bᵉ.srcᵘ up))) (Bᵉ.cfree up)
      raise (just up) (just fl) (just df) q | nothing = ⊥-elim (nj q)
      raise (just up) (just fl) nothing ()
      raise (just up) nothing D ()
      raise nothing F D ()

      unit : ∀ I L F o → unitᵉ? k R cl I L F o ≡ just r → o ≡ occursᵉ k R → Sound P k (proj₁ r)
      unit (just ij) (just (Bᵉ.lows [] c s f)) (just fr) true q e
        with stills? dir↓ (updᵉ k ûₑ) (dfs R)
      ... | just sd rewrite sym (cong proj₁ (just-inj q)) = sound (occursᵉ-free k (sym e)) (λ ()) refl
      unit (just ij) (just (Bᵉ.lows [] c s f)) (just fr) true q e | nothing = ⊥-elim (nj q)
      unit (just ij) (just (Bᵉ.lows [] c s f)) (just fr) false () e
      unit (just ij) (just (Bᵉ.lows [] c s f)) nothing o () e
      unit (just ij) (just (Bᵉ.lows (_ ∷ _) c s f)) F o () e
      unit (just ij) nothing F o () e
      unit nothing L F o () e

      top : ∀ E F D o → topᵉ? k R cl E F D o ≡ just r → o ≡ occursᵉ⁺ k R → Sound P k (proj₁ r)
      top (just fe) (just fl) (just df) true q e with stills? dir↑ (updᵉ k (econst ⊤ₑ)) (dfs R)
      ... | just sd rewrite sym (cong proj₁ (just-inj q)) = sound (occursᵉ⁺-free k (sym e)) (λ ()) refl
      top (just fe) (just fl) (just df) true q e | nothing = ⊥-elim (nj q)
      top (just fe) (just fl) (just df) false () e
      top (just fe) (just fl) nothing o () e
      top (just fe) nothing D o () e
      top nothing F D o () e

      go : (Lo ≡ just r) ⊎ ((Lo ≡ nothing) × (first Ra (first Un To) ≡ just r)) → Sound P k (proj₁ r)
      go (inj₁ q) = lower (Bᵉ.lowsOf {Ψ} k (es R)) (Bᵉʳ.freeRs {Ψ} k (rs R)) q
      go (inj₂ (_ , q)) with first-just Ra _ q
      ... | inj₁ q' = raise (Bᵉ.upsOf {Ψ} k (es R)) (Bᵉʳ.freeLs {Ψ} k (rs R)) (dfreeᵉ? k R) q'
      ... | inj₂ (_ , q') with first-just Un To q'
      ...   | inj₁ q'' = unit (Is-just? uₑ-least?) (Bᵉ.lowsOf {Ψ} k (es R)) (Bᵉʳ.freeRs {Ψ} k (rs R))
                              (occursᵉ k R) q'' refl
      ...   | inj₂ (_ , q'') = top (Bᵉ.freeLs {Ψ} k (es R)) (Bᵉʳ.freeLs {Ψ} k (rs R)) (dfreeᵉ? k R)
                                   (occursᵉ⁺ k R) q'' refl

  stepʳ-sound : ∀ k {r} → stepʳ k R ≡ just r → Soundʳ P k (proj₁ r)
  stepʳ-sound k {r} eq with cleanʳ? k R
  ... | nothing = ⊥-elim (nj eq)
  ... | just cl = go (first-just Lo _ eq)
    where
      Lo = lowerʳ? k R cl (Bʳ.lowsOf {Ψ} k (rs R))
      Ra = raiseʳ? k R cl (Bʳ.upsOf {Ψ} k (rs R)) (dfreeʳ? k R)
      Un = unitʳ? k R cl (Is-just? uᵣ-least?) (Bʳ.lowsOf {Ψ} k (rs R)) (occursʳ k R)
      To = topʳ? k R cl (Bʳ.freeLs {Ψ} k (rs R)) (dfreeʳ? k R) (occursʳ⁺ k R)

      kr-in : ∀ {x} → (x , rvar k) ∈ rs R → freeʳ k P ≡ true
      kr-in m = proj₂ (proj₂ (ai-rs ai m)) (≟-self k)

      kr-inˡ : ∀ {x} → (rvar k , x) ∈ rs R → freeʳ k P ≡ true
      kr-inˡ m = proj₂ (proj₁ (ai-rs ai m)) (≟-self k)

      lower : ∀ L → lowerʳ? k R cl L ≡ just r → Soundʳ P k (proj₁ r)
      lower (just (Bʳ.lows (x ∷ xs) c s f)) q with stills? dir↓ (updʳ k (joinᵣ x xs)) (dfs R)
      ... | just sd rewrite sym (cong proj₁ (just-inj q)) =
            soundʳ (kr-in (s (here refl)))
                   ((λ o → caseᵉ (proj₁ (joinᵣ-occ x xs) o)) , (λ o → caseʳ (proj₂ (joinᵣ-occ x xs) o)))
                   (fr' (occʳ-r k (joinᵣ x xs)) refl)
        where
          caseᵉ : ∀ {i} → Σ[ x' ∈ RExp Ψ ] ((x' ∈ x ∷ xs) × (occᵉ-r i x' ≡ true)) → freeᵉ i P ≡ true
          caseᵉ (x' , m , o) = proj₁ (proj₁ (ai-rs ai (s m))) o
          caseʳ : ∀ {i} → Σ[ x' ∈ RExp Ψ ] ((x' ∈ x ∷ xs) × (occʳ-r i x' ≡ true)) → freeʳ i P ≡ true
          caseʳ (x' , m , o) = proj₂ (proj₁ (ai-rs ai (s m))) o
          fr' : (w : 𝔹) → occʳ-r k (joinᵣ x xs) ≡ w → w ≡ false
          fr' false _ = refl
          fr' true  e with proj₂ (joinᵣ-occ x xs) e
          ... | x' , m , o with trans (sym o) (f m)
          ...   | ()
      ... | nothing = ⊥-elim (nj q)
      lower (just (Bʳ.lows [] c s f)) ()
      lower nothing ()

      raise : ∀ U D → raiseʳ? k R cl U D ≡ just r → Soundʳ P k (proj₁ r)
      raise (just up) (just df) q with stills? dir↑ (updʳ k (Bʳ.cap up)) (dfs R)
      ... | just sd rewrite sym (cong proj₁ (just-inj q)) =
            soundʳ (kr-inˡ (Bʳ.srcᵘ up)) (proj₂ (ai-rs ai (Bʳ.srcᵘ up))) (Bʳ.cfree up)
      ... | nothing = ⊥-elim (nj q)
      raise (just up) nothing ()
      raise nothing D ()

      unit : ∀ I L o → unitʳ? k R cl I L o ≡ just r → o ≡ occursʳ k R → Soundʳ P k (proj₁ r)
      unit (just ij) (just (Bʳ.lows [] c s f)) true q e with stills? dir↓ (updʳ k ûᵣ) (dfs R)
      ... | just sd rewrite sym (cong proj₁ (just-inj q)) =
            soundʳ (occursʳ-free k (sym e)) ((λ ()) , (λ ())) refl
      ... | nothing = ⊥-elim (nj q)
      unit (just ij) (just (Bʳ.lows [] c s f)) false () e
      unit (just ij) (just (Bʳ.lows (_ ∷ _) c s f)) o () e
      unit (just ij) nothing o () e
      unit nothing L o () e

      top : ∀ F D o → topʳ? k R cl F D o ≡ just r → o ≡ occursʳ⁺ k R → Soundʳ P k (proj₁ r)
      top (just fl) (just df) true q e with stills? dir↑ (updʳ k (rconst ⊤ᵣ)) (dfs R)
      ... | just sd rewrite sym (cong proj₁ (just-inj q)) =
            soundʳ (occursʳ⁺-free k (sym e)) ((λ ()) , (λ ())) refl
      ... | nothing = ⊥-elim (nj q)
      top (just fl) (just df) false () e
      top (just fl) nothing o () e
      top nothing D o () e

      go : (Lo ≡ just r) ⊎ ((Lo ≡ nothing) × (first Ra (first Un To) ≡ just r)) → Soundʳ P k (proj₁ r)
      go (inj₁ q) = lower (Bʳ.lowsOf {Ψ} k (rs R)) q
      go (inj₂ (_ , q)) with first-just Ra _ q
      ... | inj₁ q' = raise (Bʳ.upsOf {Ψ} k (rs R)) (dfreeʳ? k R) q'
      ... | inj₂ (_ , q') with first-just Un To q'
      ...   | inj₁ q'' = unit (Is-just? uᵣ-least?) (Bʳ.lowsOf {Ψ} k (rs R)) (occursʳ k R) q'' refl
      ...   | inj₂ (_ , q'') = top (Bʳ.freeLs {Ψ} k (rs R)) (dfreeʳ? k R) (occursʳ⁺ k R) q'' refl

------------------------------------------------------------------------
-- The members of a raised set are local

module _ {Ψ} (l : List (Mem Ψ)) where

  open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-v; occᵉ-c; occʳ-v; occʳ-c)

  hit-e : ∀ {k} → inᴱ k l ≡ true → (ε : EExp Ψ) → occᵉ-e k ε ≡ true → hitₑ l ε ≡ true
  hit-e {k} h (evar i)   q with occ-var {k = k} {i} q
  ... | refl = h
  hit-e h (econst c) ()
  hit-e {k} h (a ·̂ₑ b) q with ∨-true (occᵉ-e k a) _ q
  ... | inj₁ r = ∨-left (hitₑ l a) _ (hit-e h a r)
  ... | inj₂ r = ∨-right (hitₑ l a) _ (hit-e h b r)
  hit-e {k} h (a ⊔̂ₑ b) q with ∨-true (occᵉ-e k a) _ q
  ... | inj₁ r = ∨-left (hitₑ l a) _ (hit-e h a r)
  ... | inj₂ r = ∨-right (hitₑ l a) _ (hit-e h b r)

  hit-re : ∀ {k} → inᴱ k l ≡ true → (ρ : RExp Ψ) → occᵉ-r k ρ ≡ true → hitᵣ l ρ ≡ true
  hit-re h (rvar i) ()
  hit-re h (rconst c) ()
  hit-re {k} h (a ·̂ᵣ b) q with ∨-true (occᵉ-r k a) _ q
  ... | inj₁ r = ∨-left (hitᵣ l a) _ (hit-re h a r)
  ... | inj₂ r = ∨-right (hitᵣ l a) _ (hit-re h b r)
  hit-re {k} h (a ⊔̂ᵣ b) q with ∨-true (occᵉ-r k a) _ q
  ... | inj₁ r = ∨-left (hitᵣ l a) _ (hit-re h a r)
  ... | inj₂ r = ∨-right (hitᵣ l a) _ (hit-re h b r)
  hit-re h ∣ ε ∣̂ᵉ q = hit-e h ε q

  hit-r : ∀ {k} → inᴿ k l ≡ true → (ρ : RExp Ψ) → occʳ-r k ρ ≡ true → hitᵣ l ρ ≡ true
  hit-r {k} h (rvar i) q with occ-var {k = k} {i} q
  ... | refl = h
  hit-r h (rconst c) ()
  hit-r {k} h (a ·̂ᵣ b) q with ∨-true (occʳ-r k a) _ q
  ... | inj₁ r = ∨-left (hitᵣ l a) _ (hit-r h a r)
  ... | inj₂ r = ∨-right (hitᵣ l a) _ (hit-r h b r)
  hit-r {k} h (a ⊔̂ᵣ b) q with ∨-true (occʳ-r k a) _ q
  ... | inj₁ r = ∨-left (hitᵣ l a) _ (hit-r h a r)
  ... | inj₂ r = ∨-right (hitᵣ l a) _ (hit-r h b r)
  hit-r h ∣ ε ∣̂ᵉ ()

  mutual
    hit-ve : ∀ {k} → inᴱ k l ≡ true → (A : OVType Ψ) → occᵉ-v k A ≡ true → hitᵥ l A ≡ true
    hit-ve h (tvar α) ()
    hit-ve h (Base b) ()
    hit-ve h Unit ()
    hit-ve h Bool ()
    hit-ve h Empty ()
    hit-ve {k} h (A |×| B) q with ∨-true (occᵉ-v k A) _ q
    ... | inj₁ r = ∨-left (hitᵥ l A) _ (hit-ve h A r)
    ... | inj₂ r = ∨-right (hitᵥ l A) _ (hit-ve h B r)
    hit-ve {k} h (A ⇒ C) q with ∨-true (occᵉ-v k A) _ q
    ... | inj₁ r = ∨-left (hitᵥ l A) _ (hit-ve h A r)
    ... | inj₂ r = ∨-right (hitᵥ l A) _ (hit-ce h C r)
    hit-ve {k} h ([ ρ ] A) q with ∨-true (occᵉ-r k ρ) _ q
    ... | inj₁ r = ∨-left (hitᵣ l ρ) _ (hit-re h ρ r)
    ... | inj₂ r = ∨-right (hitᵣ l ρ) _ (hit-ve h A r)

    hit-ce : ∀ {k} → inᴱ k l ≡ true → (C : OCType Ψ) → occᵉ-c k C ≡ true → hitᶜ l C ≡ true
    hit-ce {k} h (A ‼ ε) q with ∨-true (occᵉ-v k A) _ q
    ... | inj₁ r = ∨-left (hitᵥ l A) _ (hit-ve h A r)
    ... | inj₂ r = ∨-right (hitᵥ l A) _ (hit-e h ε r)

  mutual
    hit-vr : ∀ {k} → inᴿ k l ≡ true → (A : OVType Ψ) → occʳ-v k A ≡ true → hitᵥ l A ≡ true
    hit-vr h (tvar α) ()
    hit-vr h (Base b) ()
    hit-vr h Unit ()
    hit-vr h Bool ()
    hit-vr h Empty ()
    hit-vr {k} h (A |×| B) q with ∨-true (occʳ-v k A) _ q
    ... | inj₁ r = ∨-left (hitᵥ l A) _ (hit-vr h A r)
    ... | inj₂ r = ∨-right (hitᵥ l A) _ (hit-vr h B r)
    hit-vr {k} h (A ⇒ C) q with ∨-true (occʳ-v k A) _ q
    ... | inj₁ r = ∨-left (hitᵥ l A) _ (hit-vr h A r)
    ... | inj₂ r = ∨-right (hitᵥ l A) _ (hit-cr h C r)
    hit-vr {k} h ([ ρ ] A) q with ∨-true (occʳ-r k ρ) _ q
    ... | inj₁ r = ∨-left (hitᵣ l ρ) _ (hit-r h ρ r)
    ... | inj₂ r = ∨-right (hitᵣ l ρ) _ (hit-vr h A r)

    hit-cr : ∀ {k} → inᴿ k l ≡ true → (C : OCType Ψ) → occʳ-c k C ≡ true → hitᶜ l C ≡ true
    hit-cr {k} h (A ‼ ε) q = ∨-left (hitᵥ l A) _ (hit-vr h A q)

  memLocalᵉ : ∀ {Θ} (O : Subst Θ Ψ) → freeᴹ l O ≡ false → ∀ {k} → inᴱ k l ≡ true → freeᵉ k O ≡ false
  memLocalᵉ O fx {k} h with freeᵉ k O in e
  ... | false = refl
  ... | true with ∨-true (anyᶠ (λ α → occᵉ-v k (sTy O α))) _ e
  ...   | inj₁ r with anyᶠ-true _ r
  ...     | α , o = ⊥-elim (tf (trans (sym (∨-left (anyᶠ (λ α → hitᵥ l (sTy O α))) _
                                         (anyᶠ-intro (λ α → hitᵥ l (sTy O α)) α (hit-ve h (sTy O α) o)))) fx))
  memLocalᵉ O fx {k} h | true | inj₂ r with ∨-true (anyᶠ (λ i → occᵉ-r k (sR O i))) _ r
  ...     | inj₁ r' with anyᶠ-true _ r'
  ...       | i , o = ⊥-elim (tf (trans (sym (∨-right (anyᶠ (λ α → hitᵥ l (sTy O α))) _
                                           (∨-left (anyᶠ (λ i → hitᵣ l (sR O i))) _
                                             (anyᶠ-intro (λ i → hitᵣ l (sR O i)) i (hit-re h (sR O i) o))))) fx))
  memLocalᵉ O fx {k} h | true | inj₂ r | inj₂ r' with anyᶠ-true _ r'
  ...       | i , o = ⊥-elim (tf (trans (sym (∨-right (anyᶠ (λ α → hitᵥ l (sTy O α))) _
                                           (∨-right (anyᶠ (λ i → hitᵣ l (sR O i))) _
                                             (anyᶠ-intro (λ i → hitₑ l (sE O i)) i (hit-e h (sE O i) o))))) fx))

  memLocalʳ : ∀ {Θ} (O : Subst Θ Ψ) → freeᴹ l O ≡ false → ∀ {k} → inᴿ k l ≡ true → freeʳ k O ≡ false
  memLocalʳ O fx {k} h with freeʳ k O in e
  ... | false = refl
  ... | true with ∨-true (anyᶠ (λ α → occʳ-v k (sTy O α))) _ e
  ...   | inj₁ r with anyᶠ-true _ r
  ...     | α , o = ⊥-elim (tf (trans (sym (∨-left (anyᶠ (λ α → hitᵥ l (sTy O α))) _
                                         (anyᶠ-intro (λ α → hitᵥ l (sTy O α)) α (hit-vr h (sTy O α) o)))) fx))
  memLocalʳ O fx {k} h | true | inj₂ r with anyᶠ-true _ r
  ...     | i , o = ⊥-elim (tf (trans (sym (∨-right (anyᶠ (λ α → hitᵥ l (sTy O α))) _
                                         (∨-left (anyᶠ (λ i → hitᵣ l (sR O i))) _
                                           (anyᶠ-intro (λ i → hitᵣ l (sR O i)) i (hit-r h (sR O i) o))))) fx))

------------------------------------------------------------------------
-- Normal forms and settling keep the unknowns among those free in `P`

private
  splits-∈ : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set}
           → (f : (a : X) → Pieces P a) → (l : List X) → ∀ {b} → b ∈ Split.out (splits f l)
           → Σ[ a ∈ X ] ((a ∈ l) × (b ∈ Pieces.parts (f a)))
  splits-∈ f (a ∷ l) m with ∈-++⁻ (Pieces.parts (f a)) m
  ... | inj₁ m' = a , here refl , m'
  ... | inj₂ m' with splits-∈ f l m'
  ...   | a' , ma , mb = a' , there ma , mb

  partsₑ-∈ : ∀ {Ψ} (s : Alts (List (EAtom Ψ))) (y : EExp Ψ) → ∀ {x' y'} → (x' , y') ∈ partsₑ s y
           → (∀ {i} → occᵉ-e i x' ≡ true → occᵉ-e i ⟦ s ⟧ᵉᵖ⁺ ≡ true) × (y' ≡ y)
  partsₑ-∈ (alt p)  y (here refl) = (λ q → q) , refl
  partsₑ-∈ (p ∷⁺ s) y (here refl) = (λ {i} q → ∨-left (occᵉ-e i ⟦ p ⟧ᵉᵖ) _ q) , refl
  partsₑ-∈ (p ∷⁺ s) y (there m) with partsₑ-∈ s y m
  ... | o , e = (λ {i} q → ∨-right (occᵉ-e i ⟦ p ⟧ᵉᵖ) _ (o q)) , e

  partsʳ-∈ : ∀ {Ψ} (s : Alts (List (RAtom Ψ))) (y : RExp Ψ) → ∀ {x' y'} → (x' , y') ∈ partsʳ s y
           → ((∀ {i} → occᵉ-r i x' ≡ true → occᵉ-r i ⟦ s ⟧ʳᵖ⁺ ≡ true)
             × (∀ {i} → occʳ-r i x' ≡ true → occʳ-r i ⟦ s ⟧ʳᵖ⁺ ≡ true)) × (y' ≡ y)
  partsʳ-∈ (alt p)  y (here refl) = ((λ q → q) , (λ q → q)) , refl
  partsʳ-∈ (p ∷⁺ s) y (here refl) =
    ((λ {i} q → ∨-left (occᵉ-r i ⟦ p ⟧ʳᵖ) _ q) , (λ {i} q → ∨-left (occʳ-r i ⟦ p ⟧ʳᵖ) _ q)) , refl
  partsʳ-∈ (p ∷⁺ s) y (there m) with partsʳ-∈ s y m
  ... | (oe , or) , e =
    ((λ {i} q → ∨-right (occᵉ-r i ⟦ p ⟧ʳᵖ) _ (oe q)) , (λ {i} q → ∨-right (occʳ-r i ⟦ p ⟧ʳᵖ) _ (or q))) , e

  canon-outₑ : ∀ {Θ Ψ} {P : Subst Θ Ψ} (x : EExp Ψ) → Outerₑ P x → Outerₑ P (canonₑ x)
  canon-outₑ x o q = o (canonₑ-occ x q)

  canon-outᵣ : ∀ {Θ Ψ} {P : Subst Θ Ψ} (x : RExp Ψ) → Outerᵣ P x → Outerᵣ P (canonᵣ x)
  canon-outᵣ x (oe , or) = (λ q → oe (canonᵣ-occᵉ x q)) , (λ q → or (canonᵣ-occʳ x q))


-- The residual `loc-normal` and `loc-settle` leave

module _ {Θ Θ' Φ} {O : Subst (Θ +e) Φ} {R : Resid Φ} {P : Subst Θ' Φ} where

  allIn-normal : (L : Localised O R) → AllIn P (lR L) → AllIn P (lR (loc-normal L))
  allIn-normal (loc σ R₀ fx sn cp la) ai = allIn r e d (ai-dfs ai)
    where
      r : ∀ {x y} → (x , y) ∈ Split.out (splits piecesʳ (rs R₀)) → Outerᵣ P x × Outerᵣ P y
      r m with splits-∈ piecesʳ (rs R₀) m
      ... | (x₀ , y₀) , m₀ , mp with partsʳ-∈ (canonSumᵣ (nrmᵣ x₀)) (canonᵣ y₀) mp
      ...   | (oe , or) , refl =
              ((λ q → proj₁ (proj₁ (ai-rs ai m₀)) (canonᵣ-occᵉ x₀ (oe q))) ,
               (λ q → proj₂ (proj₁ (ai-rs ai m₀)) (canonᵣ-occʳ x₀ (or q)))) ,
              canon-outᵣ {P = P} y₀ (proj₂ (ai-rs ai m₀))

      e : ∀ {x y} → (x , y) ∈ Split.out (splits piecesᵉ (es R₀)) → Outerₑ P x × Outerₑ P y
      e m with splits-∈ piecesᵉ (es R₀) m
      ... | (x₀ , y₀) , m₀ , mp with partsₑ-∈ (canonSumₑ (nrmₑ x₀)) (canonₑ y₀) mp
      ...   | o , refl = (λ q → proj₁ (ai-es ai m₀) (canonₑ-occ x₀ (o q))) , canon-outₑ {P = P} y₀ (proj₂ (ai-es ai m₀))

      d : ∀ {A ρ} → (A , ρ) ∈ Split.out (splits piecesᵈ (ds R₀)) → Outerᵣ P ρ
      d m with splits-∈ piecesᵈ (ds R₀) m
      ... | (A₀ , ρ₀) , m₀ , here refl = canon-outᵣ {P = P} ρ₀ (ai-ds ai m₀)

  allIn-settle : (L : Localised O R) → AllIn P (lR L) → AllIn P (lR (loc-settle L))
  allIn-settle (loc σ R₀ fx sn cp la) ai = allIn r e d (ai-dfs ai)
    where
      Uʳ = unsettled settledʳ (rs R₀)
      Uᵉ = unsettled settledᵉ (es R₀)
      Uᵈ = unsettled settledᵈ (ds R₀)
      F  = refine (Unsettled.kept Uᵈ)

      r : ∀ {x y} → (x , y) ∈ Unsettled.kept Uʳ ++ Refined.ords F → Outerᵣ P x × Outerᵣ P y
      r m with ∈-++⁻ (Unsettled.kept Uʳ) m
      ... | inj₁ m' = ai-rs ai (Unsettled.kept⊆ Uʳ m')
      ... | inj₂ m' with Refined.ordsˢ F m' | Refined.ordsᵘ F m'
      ...   | A , mA | refl = ai-ds ai (Unsettled.kept⊆ Uᵈ mA) , ((λ ()) , (λ ()))

      e : ∀ {x y} → (x , y) ∈ Unsettled.kept Uᵉ → Outerₑ P x × Outerₑ P y
      e m = ai-es ai (Unsettled.kept⊆ Uᵉ m)

      d : ∀ {A ρ} → (A , ρ) ∈ Refined.rest F → Outerᵣ P ρ
      d m = ai-ds ai (Unsettled.kept⊆ Uᵈ (Refined.rest⊆ F m))

------------------------------------------------------------------------
-- Every local unknown is visited by a pass

misses-∈ : ∀ {n} → (f : Fin n → 𝔹) → ∀ {k} → f k ≡ false → Σ[ q ∈ f k ≡ false ] ((k , q) ∈ misses f)
misses-∈ {nsuc n} f {zero} q with isFalse (f zero) in e
... | just q' = q' , here refl
... | nothing = ⊥-elim (isFalse-nothing q e)
  where
    isFalse-nothing : ∀ {b} → b ≡ false → isFalse b ≡ nothing → ⊥
    isFalse-nothing refl ()
misses-∈ {nsuc n} f {suc k} q with misses-∈ (λ i → f (suc i)) q
... | q' , m = q' , head-∈ (isFalse (f zero)) (shift-∈ (misses (λ i → f (suc i))) m)
  where
    shift-∈ : ∀ l → (k , q') ∈ l → (suc k , q') ∈ missShift f l
    shift-∈ (_ ∷ l) (here refl) = here refl
    shift-∈ (_ ∷ l) (there m')  = there (shift-∈ l m')

    head-∈ : ∀ x {l} → (suc k , q') ∈ l → (suc k , q') ∈ missHead f x l
    head-∈ (just _) m' = there m'
    head-∈ nothing  m' = m'

------------------------------------------------------------------------
-- The rounds, for a predicate on the residual that every stage keeps
-- and that, at a fixed point, leaves no local unknown

module _ {Θ Φ} (O : Subst (Θ +e) Φ) (R : Resid Φ) (Pu : Resid Φ → Set) where

  record Keeps? : Set where
    field
      pu-normal : ∀ L → Pu (lR L) → Pu (lR (loc-normal {O = O} {R = R} L))
      pu-settle : ∀ L → Pu (lR L) → Pu (lR (loc-settle {O = O} {R = R} L))
      pu-stepᵉ  : ∀ R₀ k {r} → freeᵉ k O ≡ false → stepᵉ k R₀ ≡ just r → Pu R₀
                → Pu (R₀ [ updᵉ k (proj₁ r) ]ᴿ)
      pu-stepʳ  : ∀ R₀ k {r} → freeʳ k O ≡ false → stepʳ k R₀ ≡ just r → Pu R₀
                → Pu (R₀ [ updʳ k (proj₁ r) ]ᴿ)
      pu-collᵉ  : ∀ R₀ {c} → collapseᵉ? O R₀ ≡ just c → Pu R₀
                → Pu (R₀ [ updᵉ (proj₁ c) (evar (proj₁ (proj₂ c))) ]ᴿ)
      pu-collʳ  : ∀ R₀ {c} → collapseʳ? O R₀ ≡ just c → Pu R₀
                → Pu (R₀ [ updʳ (proj₁ c) (rvar (proj₁ (proj₂ c))) ]ᴿ)
      pu-raise  : ∀ R₀ j {rd} → Find.raise? O R₀ j ≡ just rd → Pu R₀
                → Pu (R₀ [ tops (Raised.mems rd) ]ᴿ)
      pu-fixed  : ∀ R₀ → Pu R₀
                → (∀ k → freeᵉ k O ≡ false → stepᵉ k R₀ ≡ nothing)
                → (∀ k → freeʳ k O ≡ false → stepʳ k R₀ ≡ nothing)
                → AllIn O R₀

  -- What a stage leaves: a `P'` over the residual, no more local
  -- unknowns than before, fewer when it changed something

  record Left (P : Subst Φ Φ) (L' : Localised O R) (ch : 𝔹) : Set where
    constructor left
    field
      P'  : Subst Φ Φ
      ai' : AllIn P' (lR L')
      pu' : Pu (lR L')
      le  : cnt O P' ≤ cnt O P
      lt  : ch ≡ true → cnt O P' < cnt O P

  open Left

  private
    <→≤ : ∀ {m n} → m < n → m ≤ n
    <→≤ (s≤s p) = ≤-trans p (n≤1+n _)

    ≤-<-trans : ∀ {a b c} → a ≤ b → b < c → a < c
    ≤-<-trans p (s≤s q) = s≤s (≤-trans p q)

  module Run (K : Keeps?) where

    open Keeps? K

    -- a step on a local unknown

    stepᵉ-left : ∀ (L : Localised O R) P k (q : freeᵉ k O ≡ false) {r} → stepᵉ k (lR L) ≡ just r
               → AllIn P (lR L) → Pu (lR L)
               → Σ[ P₁ ∈ Subst Φ Φ ] (AllIn P₁ (lR L [ updᵉ k (proj₁ r) ]ᴿ) × Pu (lR L [ updᵉ k (proj₁ r) ]ᴿ)
                                       × (cnt O P₁ < cnt O P))
    stepᵉ-left L P k q e ai pu =
      P ⨟ˢ updᵉ k _ , allIn-⨟ P _ ai , pu-stepᵉ (lR L) k q e pu ,
      drops-<ᵉ (drops-updᵉ {P = P} k _ (Sound.s-out sd) (Sound.s-fr sd)) O k q (Sound.s-free sd) (≟-self k)
      where sd = stepᵉ-sound ai k e

    stepʳ-left : ∀ (L : Localised O R) P k (q : freeʳ k O ≡ false) {r} → stepʳ k (lR L) ≡ just r
               → AllIn P (lR L) → Pu (lR L)
               → Σ[ P₁ ∈ Subst Φ Φ ] (AllIn P₁ (lR L [ updʳ k (proj₁ r) ]ᴿ) × Pu (lR L [ updʳ k (proj₁ r) ]ᴿ)
                                       × (cnt O P₁ < cnt O P))
    stepʳ-left L P k q e ai pu =
      P ⨟ˢ updʳ k _ , allIn-⨟ P _ ai , pu-stepʳ (lR L) k q e pu ,
      drops-<ʳ (drops-updʳ {P = P} k _ (Soundʳ.s-out sd) (Soundʳ.s-fr sd)) O k q (Soundʳ.s-free sd) (≟-self k)
      where sd = stepʳ-sound ai k e

    -- a pass

    passᵉ-left : ∀ ks (L : Localised O R) P → AllIn P (lR L) → Pu (lR L)
               → Left P (proj₁ (passᵉ O R ks L)) (proj₂ (passᵉ O R ks L))
                 × (proj₂ (passᵉ O R ks L) ≡ false
                    → (proj₁ (passᵉ O R ks L) ≡ L) × (∀ {k q} → (k , q) ∈ ks → stepᵉ k (lR L) ≡ nothing))
    passᵉ-left []             L P ai pu = left P ai pu ≤-refl (λ ()) , (λ _ → refl , λ ())
    passᵉ-left ((k , q) ∷ ks) L P ai pu with stepᵉ k (lR L) in e
    ... | nothing with passᵉ-left ks L P ai pu
    ...   | lf , fx = lf , (λ f → proj₁ (fx f) , λ { (here refl) → e ; (there m) → proj₂ (fx f) m })
    passᵉ-left ((k , q) ∷ ks) L P ai pu | just (b , st) with stepᵉ-left L P k q e ai pu
    ... | P₁ , ai₁ , pu₁ , lt₁
      with passᵉ-left ks (loc-ext L (updᵉ k b) (freeᵉ-fix k O q b) (λ τ en → st τ ∅ᴴ) (λ α → refl)) P₁ ai₁ pu₁
    ...   | left P' ai' pu' le' _ , _ = left P' ai' pu' (≤-trans le' (<→≤ lt₁)) (λ _ → ≤-<-trans le' lt₁) , λ ()

    passʳ-left : ∀ ks (L : Localised O R) P → AllIn P (lR L) → Pu (lR L)
               → Left P (proj₁ (passʳ O R ks L)) (proj₂ (passʳ O R ks L))
                 × (proj₂ (passʳ O R ks L) ≡ false
                    → (proj₁ (passʳ O R ks L) ≡ L) × (∀ {k q} → (k , q) ∈ ks → stepʳ k (lR L) ≡ nothing))
    passʳ-left []             L P ai pu = left P ai pu ≤-refl (λ ()) , (λ _ → refl , λ ())
    passʳ-left ((k , q) ∷ ks) L P ai pu with stepʳ k (lR L) in e
    ... | nothing with passʳ-left ks L P ai pu
    ...   | lf , fx = lf , (λ f → proj₁ (fx f) , λ { (here refl) → e ; (there m) → proj₂ (fx f) m })
    passʳ-left ((k , q) ∷ ks) L P ai pu | just (b , st) with stepʳ-left L P k q e ai pu
    ... | P₁ , ai₁ , pu₁ , lt₁
      with passʳ-left ks (loc-ext L (updʳ k b) (freeʳ-fix k O q b) (λ τ en → st τ ∅ᴴ) (λ α → refl)) P₁ ai₁ pu₁
    ...   | left P' ai' pu' le' _ , _ = left P' ai' pu' (≤-trans le' (<→≤ lt₁)) (λ _ → ≤-<-trans le' lt₁) , λ ()

    -- the identifications of a round

    collapseᵉL-left : ∀ n (L : Localised O R) P → AllIn P (lR L) → Pu (lR L)
                    → Left P (proj₁ (collapseᵉL O R n L)) (proj₂ (collapseᵉL O R n L))
                      × (proj₂ (collapseᵉL O R n L) ≡ false → proj₁ (collapseᵉL O R n L) ≡ L)
    collapseᵉL-left nzero    L P ai pu = left P ai pu ≤-refl (λ ()) , (λ _ → refl)
    collapseᵉL-left (nsuc n) L P ai pu with collapseᵉ? O (lR L) in e
    ... | nothing = left P ai pu ≤-refl (λ ()) , (λ _ → refl)
    ... | just (k , r , q , st , (w₁ , m₁) , (w₂ , m₂) , ne)
      with collapseᵉL-left n (loc-ext L (updᵉ k (evar r)) (freeᵉ-fix k O q (evar r)) (λ τ en → st τ ∅ᴴ) (λ α → refl))
             (P ⨟ˢ updᵉ k (evar r)) (allIn-⨟ P _ ai) (pu-collᵉ (lR L) e pu)
    ...   | left P' ai' pu' le' _ , _ =
            left P' ai' pu' (≤-trans le' (<→≤ lt₁)) (λ _ → ≤-<-trans le' lt₁) , λ ()
      where
        lt₁ : cnt O (P ⨟ˢ updᵉ k (evar r)) < cnt O P
        lt₁ = drops-<ᵉ (drops-updᵉ {P = P} k (evar r) (proj₂ (ai-es ai m₂)) ne) O k q
                       (proj₁ (ai-es ai m₁) (≟-self k)) (≟-self k)

    collapseʳL-left : ∀ n (L : Localised O R) P → AllIn P (lR L) → Pu (lR L)
                    → Left P (proj₁ (collapseʳL O R n L)) (proj₂ (collapseʳL O R n L))
                      × (proj₂ (collapseʳL O R n L) ≡ false → proj₁ (collapseʳL O R n L) ≡ L)
    collapseʳL-left nzero    L P ai pu = left P ai pu ≤-refl (λ ()) , (λ _ → refl)
    collapseʳL-left (nsuc n) L P ai pu with collapseʳ? O (lR L) in e
    ... | nothing = left P ai pu ≤-refl (λ ()) , (λ _ → refl)
    ... | just (k , r , q , st , (w₁ , m₁) , (w₂ , m₂) , ne)
      with collapseʳL-left n (loc-ext L (updʳ k (rvar r)) (freeʳ-fix k O q (rvar r)) (λ τ en → st τ ∅ᴴ) (λ α → refl))
             (P ⨟ˢ updʳ k (rvar r)) (allIn-⨟ P _ ai) (pu-collʳ (lR L) e pu)
    ...   | left P' ai' pu' le' _ , _ =
            left P' ai' pu' (≤-trans le' (<→≤ lt₁)) (λ _ → ≤-<-trans le' lt₁) , λ ()
      where
        lt₁ : cnt O (P ⨟ˢ updʳ k (rvar r)) < cnt O P
        lt₁ = drops-<ʳ (drops-updʳ {P = P} k (rvar r) (proj₂ (ai-rs ai m₂)) ne) O k q
                       (proj₂ (proj₁ (ai-rs ai m₁)) (≟-self k)) (≟-self k)
