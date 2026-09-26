------------------------------------------------------------------
-- The invariants of a residual and of a solver state             --
--                                                                --
-- Read against `P`, whose images mention the protected unknowns: --
--   I1′  the greater side of each ordering is a whole unknown or --
--        mentions protected unknowns only (`Goodᵣ`, `Goodₑ`);    --
--   I5   the greater side of each ordering of a deferred entry   --
--        mentions protected unknowns and the entry's own rigids  --
--        only (`Great`);                                         --
-- and the types of the subtyping demands have good grades. A     --
-- state is read against `π ⨟ˢ θ s` (`Inv`), `π` embedding the    --
-- program's variables and the enclosing rigids.                  --
------------------------------------------------------------------

open import Data.List.Base using (List; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using ([_,_]′)

open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Invariants.Residual (S : LanguageSpec) where

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S using (mapᵖ)
open import TypeInference.OpenSyntax.Instances S using (_↑ᵉⁿ_)

open import TypeInference.SolverImpl.Deferred S
open import TypeInference.SolverImpl.Resid    S
open import TypeInference.SolverImpl.State    S
open import TypeInference.SolverImpl.Localise S using (Outerₑ; Outerᵣ)
open import TypeInference.SolverImpl.Invariants.Outer S

------------------------------------------------------------------------
-- The invariants

-- The greater sides of an entry's orderings, over the unknowns free in
-- `P` and the entry's rigids

record Great {Θ Ψ} (P : Subst Θ Ψ) (E : Dfr Ψ) : Set where
  constructor mkGreat
  field
    greatʳ : ∀ {x y} → (x , y) ∈ ors (body E) → Outerᵣ (P ↑ᵉⁿ nb E) y
    greatᵉ : ∀ {x y} → (x , y) ∈ oes (body E) → Outerₑ (P ↑ᵉⁿ nb E) y

open Great public

record ResInv {Θ Ψ} (P : Subst Θ Ψ) (R : Resid Ψ) : Set where
  constructor mkResInv
  field
    inv-ss : ∀ {A B} → (A , B) ∈ ss R → TyGoodᵛ P A × TyGoodᵛ P B
    I1′ʳ   : ∀ {x y} → (x , y) ∈ rs R → Goodᵣ P y
    I1′ᵉ   : ∀ {x y} → (x , y) ∈ es R → Goodₑ P y
    I5     : ∀ {E} → E ∈ dfs R → Great P E

open ResInv public

-- A state: the images of `θ s` good, and its residual

record Inv {Θ₀ Θ} (π : Subst Θ₀ Θ) (s : St Θ) : Set where
  constructor mkInv
  field
    inv-θ : GV (π ⨟ˢ θ s) (θ s)
    inv-R : ResInv (π ⨟ˢ θ s) (res s)

open Inv public

-- A move by a good substitution

GoodMove : ∀ {Θ₀ Θ} → (π : Subst Θ₀ Θ) → {s s' : St Θ} → s ⟶ s' → Set
GoodMove π {s' = s'} m = GV (π ⨟ˢ θ s') (mδ m)

------------------------------------------------------------------------
-- Entries

great-⊆ : ∀ {Θ Θ' Ψ} {P : Subst Θ Ψ} {P' : Subst Θ' Ψ} → P ⊆ᶠ P' → (E : Dfr Ψ)
        → Great P E → Great P' E
great-⊆ i E g =
  mkGreat (λ {x} {y} m → outerᵣ-⊆ {ρ = y} (⊆ᶠ-↑ᵉⁿ (nb E) i) (greatʳ g m))
          (λ {x} {y} m → outerₑ-⊆ {ε = y} (⊆ᶠ-↑ᵉⁿ (nb E) i) (greatᵉ g m))

great-⨟ : ∀ {Θ Ψ Ψ'} (P : Subst Θ Ψ) (σ : Subst Ψ Ψ') → (E : Dfr Ψ)
        → Great P E → Great (P ⨟ˢ σ) (E [ σ ]ᵈ)
great-⨟ P σ (dfr l k o) g = mkGreat r e
  where
    eq : ((P ↑ᵉⁿ k) ⨟ˢ (σ ↑ᵉⁿ k)) ⊆ᶠ ((P ⨟ˢ σ) ↑ᵉⁿ k)
    eq = ≐→⊆ᶠ (⨟-↑ᵉⁿ P σ k)

    r : ∀ {x y} → (x , y) ∈ ors (o [ σ ↑ᵉⁿ k ]ᴼ) → Outerᵣ ((P ⨟ˢ σ) ↑ᵉⁿ k) y
    r m with ∈-map⁻ (mapᵖ (_[ σ ↑ᵉⁿ k ]ʳ)) m
    ... | (x₀ , y₀) , m₀ , refl =
          outerᵣ-⊆ {ρ = y₀ [ σ ↑ᵉⁿ k ]ʳ} eq
                   (outerᵣ-⨟ (P ↑ᵉⁿ k) (σ ↑ᵉⁿ k) {y₀} (greatʳ g m₀))

    e : ∀ {x y} → (x , y) ∈ oes (o [ σ ↑ᵉⁿ k ]ᴼ) → Outerₑ ((P ⨟ˢ σ) ↑ᵉⁿ k) y
    e m with ∈-map⁻ (mapᵖ (_[ σ ↑ᵉⁿ k ]ᵉ)) m
    ... | (x₀ , y₀) , m₀ , refl =
          outerₑ-⊆ {ε = y₀ [ σ ↑ᵉⁿ k ]ᵉ} eq
                   (outerₑ-⨟ (P ↑ᵉⁿ k) (σ ↑ᵉⁿ k) {y₀} (greatᵉ g m₀))

------------------------------------------------------------------------
-- Residuals

resinv-⊆ : ∀ {Θ Θ' Ψ} {P : Subst Θ Ψ} {P' : Subst Θ' Ψ} {R : Resid Ψ}
         → P ⊆ᶠ P' → ResInv P R → ResInv P' R
resinv-⊆ i r =
  mkResInv (λ {A} {B} m → tygoodᵛ-⊆ i A (proj₁ (inv-ss r m)) , tygoodᵛ-⊆ i B (proj₂ (inv-ss r m)))
           (λ m → goodᵣ-⊆ i (I1′ʳ r m)) (λ m → goodₑ-⊆ i (I1′ᵉ r m))
           (λ {E} m → great-⊆ i E (I5 r m))

resinv-≐ : ∀ {Θ Ψ} {P P' : Subst Θ Ψ} {R : Resid Ψ} → P ≐ˢ P' → ResInv P R → ResInv P' R
resinv-≐ p = resinv-⊆ (≐→⊆ᶠ p)

-- Under a good substitution

resinv-subst : ∀ {Θ Ψ Ψ'} {P : Subst Θ Ψ} {σ : Subst Ψ Ψ'} {R : Resid Ψ}
             → GV (P ⨟ˢ σ) σ → ResInv P R → ResInv (P ⨟ˢ σ) (R [ σ ]ᴿ)
resinv-subst {P = P} {σ} {R} g r = mkResInv sᵢ rᵢ eᵢ dᵢ
  where
    sᵢ : ∀ {A B} → (A , B) ∈ ss (R [ σ ]ᴿ) → TyGoodᵛ (P ⨟ˢ σ) A × TyGoodᵛ (P ⨟ˢ σ) B
    sᵢ m with ∈-map⁻ (mapᵖ (_[ σ ]ᵛ)) m
    ... | (A₀ , B₀) , m₀ , refl =
          tygoodᵛ-⨟ {P = P} g A₀ (proj₁ (inv-ss r m₀)) , tygoodᵛ-⨟ {P = P} g B₀ (proj₂ (inv-ss r m₀))

    rᵢ : ∀ {x y} → (x , y) ∈ rs (R [ σ ]ᴿ) → Goodᵣ (P ⨟ˢ σ) y
    rᵢ m with ∈-map⁻ (mapᵖ (_[ σ ]ʳ)) m
    ... | (x₀ , y₀) , m₀ , refl = goodᵣ-⨟ {P = P} g (I1′ʳ r m₀)

    eᵢ : ∀ {x y} → (x , y) ∈ es (R [ σ ]ᴿ) → Goodₑ (P ⨟ˢ σ) y
    eᵢ m with ∈-map⁻ (mapᵖ (_[ σ ]ᵉ)) m
    ... | (x₀ , y₀) , m₀ , refl = goodₑ-⨟ {P = P} g (I1′ᵉ r m₀)

    dᵢ : ∀ {E} → E ∈ dfs (R [ σ ]ᴿ) → Great (P ⨟ˢ σ) E
    dᵢ m with ∈-map⁻ (_[ σ ]ᵈ) m
    ... | E₀ , m₀ , refl = great-⨟ P σ E₀ (I5 r m₀)

-- The empty residual, unions, and pushing an atom

resinv-empty : ∀ {Θ Ψ} {P : Subst Θ Ψ} → ResInv P emptyᴿ
resinv-empty = mkResInv (λ ()) (λ ()) (λ ()) (λ ())

resinv-∪ : ∀ {Θ Ψ} {P : Subst Θ Ψ} {R R' : Resid Ψ}
         → ResInv P R → ResInv P R' → ResInv P (R ∪ᴿ R')
resinv-∪ {R = R} a b =
  mkResInv (λ m → [ inv-ss a , inv-ss b ]′ (∈-++⁻ (ss R) m))
           (λ m → [ I1′ʳ a , I1′ʳ b ]′ (∈-++⁻ (rs R) m))
           (λ m → [ I1′ᵉ a , I1′ᵉ b ]′ (∈-++⁻ (es R) m))
           (λ m → [ I5 a , I5 b ]′ (∈-++⁻ (dfs R) m))

resinv-pushʳ : ∀ {Θ Ψ} {P : Subst Θ Ψ} {R : Resid Ψ} {x y : RExp Ψ}
             → Goodᵣ P y → ResInv P R → ResInv P (pushʳ x y R)
resinv-pushʳ g r =
  mkResInv (inv-ss r) (λ { (here refl) → g ; (there m) → I1′ʳ r m }) (I1′ᵉ r) (I5 r)

resinv-pushᵉ : ∀ {Θ Ψ} {P : Subst Θ Ψ} {R : Resid Ψ} {x y : EExp Ψ}
             → Goodₑ P y → ResInv P R → ResInv P (pushᵉ x y R)
resinv-pushᵉ g r =
  mkResInv (inv-ss r) (I1′ʳ r) (λ { (here refl) → g ; (there m) → I1′ᵉ r m }) (I5 r)

resinv-pushᵗ : ∀ {Θ Ψ} {P : Subst Θ Ψ} {R : Resid Ψ} {αs : List (TyVar Ψ)}
             → ResInv P R → ResInv P (pushᵗ αs R)
resinv-pushᵗ r = mkResInv (inv-ss r) (I1′ʳ r) (I1′ᵉ r) (I5 r)

resinv-pushᵈ : ∀ {Θ Ψ} {P : Subst Θ Ψ} {R : Resid Ψ} {A : OVType Ψ} {ρ : RExp Ψ}
             → ResInv P R → ResInv P (pushᵈ A ρ R)
resinv-pushᵈ r = mkResInv (inv-ss r) (I1′ʳ r) (I1′ᵉ r) (I5 r)

------------------------------------------------------------------------
-- The initial state, read against the identity

inv-init : ∀ {Θ} → Inv (idˢ {Θ}) init
inv-init = mkInv GV-id resinv-empty
