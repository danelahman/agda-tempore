------------------------------------------------------------------
-- Invariants of the solver state                                 --
--                                                                --
-- A state is read against `π : Subst Θ₀ Θ`, which embeds the     --
-- program's own variables and the rigids of the enclosing clause --
-- scopes into the constraint's scope. An unknown is *protected*  --
-- when it is free in an image of `π ⨟ˢ θ s`: of a program        --
-- variable or of such a rigid.                                   --
--                                                                --
--   I1′  every greater side of an ordering of the residual is a  --
--        whole unknown, or mentions protected unknowns only;     --
--   I5   every greater side of an ordering of a deferred entry   --
--        mentions protected unknowns and the entry's own rigids  --
--        only.                                                   --
--                                                                --
-- They are kept together with two auxiliary facts: the images    --
-- of `θ s`, and the types of the subtyping demands, have good    --
-- grades throughout, for a subtyping demand decomposes into      --
-- orderings between them. A step of the driver is also asked to  --
-- move the unknowns by a good substitution, which is what        --
-- carries the outer residual across a clause's scope.            --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe using (Is-just)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.Outcome

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Invariants
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types S using (_≡ᵇ?_)

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S using (Hyps; mapᵖ; Is-just?; ∅ᴴ)
open import TypeInference.OpenSyntax.Instances S using (_+eⁿ_; _↑ᵉⁿ_; ≐ˢ-↑ᵉⁿ)

open import TypeInference.Constraints.Syntax S

open import TypeInference.SolverImpl.Core.Thick using (thickᵉ)
open import TypeInference.SolverImpl.Core.Unify S using (Rig; unify)
open import TypeInference.SolverImpl.Core.AList S using (AList; ⟦_⟧ᴬ)
open import TypeInference.SolverImpl.Core.Eqn   S using (eqᵛ)
open import TypeInference.SolverImpl.Core.Decorate S using (expandSub)
open import TypeInference.SolverImpl.Enum S using (AllOp)

open OpEnum opEnum
open import TypeInference.SolverImpl.Core.Occurs S
  using (occᵉ-e; occᵉ-r; occᵉ-v; occʳ-r; occʳ-v)
open import TypeInference.SolverImpl.Core.Rigid S
  using (zip₂; zip₂-just; popˢ; strSub; strᵉ; strʳ; strᵉ⁺; strʳ⁺; strᵛ⁺; str-occᵉ; str-occʳ; strᵉ⁺-just; strʳ⁺-just;
         strᵉ-upd; strʳ-upd; notNothing; ∨-true; ∨-left; ∨-right; dec-true; true-dec)
open import TypeInference.SolverImpl.Deferred S
open import TypeInference.SolverImpl.Resid    S
open import TypeInference.SolverImpl.State    S
open import TypeInference.SolverImpl.Normal   S using (decide≾ᵣ; decide≾ₑ)
open import TypeInference.SolverImpl.Solve    S opEnum
open import TypeInference.SolverImpl.Localise S
  using (Localised; localise; lσ; lR; lfix; Outerₑ; Outerᵣ; freeᵉ; freeʳ; outerₑ?; outerᵣ?; outerVarₑ; outerVarᵣ; anyᶠ; evar?)
open import TypeInference.SolverImpl.Invariants.Outer S
open import TypeInference.SolverImpl.Invariants.Expand S using (expandSub-good)
open import TypeInference.SolverImpl.Invariants.Unify  S using (unify-good)

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

resinv-pushᵗ : ∀ {Θ Ψ} {P : Subst Θ Ψ} {R : Resid Ψ} {A : OVType Ψ}
             → ResInv P R → ResInv P (pushᵗ A R)
resinv-pushᵗ r = mkResInv (inv-ss r) (I1′ʳ r) (I1′ᵉ r) (I5 r)

resinv-pushᵈ : ∀ {Θ Ψ} {P : Subst Θ Ψ} {R : Resid Ψ} {A : OVType Ψ} {ρ : RExp Ψ}
             → ResInv P R → ResInv P (pushᵈ A ρ R)
resinv-pushᵈ r = mkResInv (inv-ss r) (I1′ʳ r) (I1′ᵉ r) (I5 r)

------------------------------------------------------------------------
-- The initial state, read against the identity: the protected unknowns
-- are the program's variables

inv-init : ∀ {Θ} → Inv (idˢ {Θ}) init
inv-init = mkInv GV-id resinv-empty

------------------------------------------------------------------------
-- Closing a clause's scope

⊥just : ∀ {X Y : Set} {x : X} → nothing ≡ just x → Y
⊥just ()

⊥nothing : ∀ {X Y : Set} {x : X} → just x ≡ nothing → Y
⊥nothing ()

-- Moving the rigid, and sending it to a constant, are good

GV-pop : ∀ {Θ Ψ} {P : Subst Θ (Ψ +e)} → (j : EVar (Ψ +e)) → GV P (popˢ j)
GV-pop {Ψ = Ψ} j = GV-ren (λ α → α , refl) (λ i → i , refl) e
  where
    e : ∀ k → Σ[ k' ∈ EVar (Ψ +e) ] (sE (popˢ j) k ≡ evar k')
    e k with thickᵉ {Ψ} j k
    ... | just k₀ = _ , refl
    ... | nothing = _ , refl

GV-upd : ∀ {Θ Ψ} {P : Subst Θ Ψ} → (j : EVar Ψ) → (c : E) → GV P (updᵉ j (econst c))
GV-upd {P = P} j c = mkGV (λ α → tt) (λ i → whole i) e
  where
    e : ∀ k → Goodₑ P (sE (updᵉ j (econst c)) k)
    e k with k ≟ᶠ j
    ... | yes _ = outer (λ ())
    ... | no _  = whole k

upd-⊆ᶠ : ∀ {Θ Ψ} → (Y : Subst Θ Ψ) → (j : EVar Ψ) → (c : E) → (Y ⨟ˢ updᵉ j (econst c)) ⊆ᶠ Y
upd-⊆ᶠ Y j c = mk⊆ᶠ e r
  where
    e : ∀ {k} → freeᵉ k (Y ⨟ˢ updᵉ j (econst c)) ≡ true → freeᵉ k Y ≡ true
    e q with freeᵉ-⨟⁻ Y (updᵉ j (econst c)) q
    ... | inj₁ (α , ())
    ... | inj₂ (inj₁ (i , p , ()))
    ... | inj₂ (inj₂ (i , p , o)) with i ≟ᶠ j
    ...   | yes _ with o
    ...     | ()
    e {k} q | inj₂ (inj₂ (i , p , o)) | no _ =
      subst (λ x → freeᵉ x Y ≡ true) (sym (true-dec (k ≟ᶠ i) o)) p

    r : ∀ {k} → freeʳ k (Y ⨟ˢ updᵉ j (econst c)) ≡ true → freeʳ k Y ≡ true
    r {k} q with freeʳ-⨟⁻ Y (updᵉ j (econst c)) q
    ... | inj₁ (α , ())
    ... | inj₂ (i , p , o) = subst (λ x → freeʳ x Y ≡ true) (sym (true-dec (k ≟ᶠ i) o)) p

-- An entry closed over one more rigid, or with it sent to the unit

great-close : ∀ {Θ Ψ} → (X : Subst Θ Ψ) → (E : Dfr (Ψ +e))
            → Great (X ↑ᵉ) E → Great X (closeᵈ E)
great-close X (dfr l k o) g with o [ κ⟨ ûₑ ⟩ ↑ᵉⁿ k ]ᴼ [ wkˢᵉ ↑ᵉⁿ k ]ᴼ ≟ᴼ o
... | no _  = mkGreat (greatʳ g) (greatᵉ g)
... | yes _ = mkGreat r e
  where
    κk = κ⟨ ûₑ ⟩ ↑ᵉⁿ k

    inc : (((X ↑ᵉ) ↑ᵉⁿ k) ⨟ˢ κk) ⊆ᶠ (X ↑ᵉⁿ k)
    inc = ⊆ᶠ-trans (≐→⊆ᶠ (⨟-↑ᵉⁿ (X ↑ᵉ) κ⟨ ûₑ ⟩ k)) (⊆ᶠ-↑ᵉⁿ k (↑ᵉ-κ-⊆ᶠ X uₑ))

    r : ∀ {x y} → (x , y) ∈ ors (o [ κk ]ᴼ) → Outerᵣ (X ↑ᵉⁿ k) y
    r m with ∈-map⁻ (mapᵖ (_[ κk ]ʳ)) m
    ... | (x₀ , y₀) , m₀ , refl =
          outerᵣ-⊆ {ρ = y₀ [ κk ]ʳ} inc (outerᵣ-⨟ ((X ↑ᵉ) ↑ᵉⁿ k) κk {y₀} (greatʳ g m₀))

    e : ∀ {x y} → (x , y) ∈ oes (o [ κk ]ᴼ) → Outerₑ (X ↑ᵉⁿ k) y
    e m with ∈-map⁻ (mapᵖ (_[ κk ]ᵉ)) m
    ... | (x₀ , y₀) , m₀ , refl =
          outerₑ-⊆ {ε = y₀ [ κk ]ᵉ} inc (outerₑ-⨟ ((X ↑ᵉ) ↑ᵉⁿ k) κk {y₀} (greatᵉ g m₀))

great-lift : ∀ {Θ Θ' Ψ} → (P : Subst Θ (Ψ +e)) → (X : Subst Θ' Ψ) → (j : EVar (Ψ +e))
           → (P ⨟ˢ popˢ j) ⊆ᶠ (X ↑ᵉ) → (E : Dfr (Ψ +e))
           → Great P E → Great X (liftᵈ j E)
great-lift P X j inc E g =
  great-close X (E [ popˢ j ]ᵈ) (great-⊆ inc (E [ popˢ j ]ᵈ) (great-⨟ P (popˢ j) E g))

-- The test for an expression over the unknowns free in a substitution
-- succeeds on one

outerₑ?-ok : ∀ {Θ Φ} {O : Subst Θ Φ} → (ε : EExp Φ) → Outerₑ O ε → outerₑ? O ε ≡ nothing → ⊥
outerₑ?-ok {O = O} (evar i) o q = at (freeᵉ i O) refl (o (dec-true (i ≟ᶠ i) refl)) q
  where
    at : (b : 𝔹) → (r : freeᵉ i O ≡ b) → freeᵉ i O ≡ true → outerVarₑ O i b r ≡ nothing → ⊥
    at true  r t ()
    at false r t q' with trans (sym r) t
    ... | ()
outerₑ?-ok         (econst c) o ()
outerₑ?-ok {O = O} (a ·̂ₑ b)   o q with outerₑ? O a in qa | outerₑ? O b in qb
... | just _  | just _  = ⊥nothing q
... | nothing | _       = outerₑ?-ok a (λ {k} r → o (∨-left (occᵉ-e k a) _ r)) qa
... | just _  | nothing = outerₑ?-ok b (λ {k} r → o (∨-right (occᵉ-e k a) _ r)) qb
outerₑ?-ok {O = O} (a ⊔̂ₑ b)   o q with outerₑ? O a in qa | outerₑ? O b in qb
... | just _  | just _  = ⊥nothing q
... | nothing | _       = outerₑ?-ok a (λ {k} r → o (∨-left (occᵉ-e k a) _ r)) qa
... | just _  | nothing = outerₑ?-ok b (λ {k} r → o (∨-right (occᵉ-e k a) _ r)) qb

outerᵣ?-ok : ∀ {Θ Φ} {O : Subst Θ Φ} → (ρ : RExp Φ) → Outerᵣ O ρ → outerᵣ? O ρ ≡ nothing → ⊥
outerᵣ?-ok {O = O} (rvar i) (oe , or) q = at (freeʳ i O) refl (or (dec-true (i ≟ᶠ i) refl)) q
  where
    at : (b : 𝔹) → (r : freeʳ i O ≡ b) → freeʳ i O ≡ true → outerVarᵣ O i b r ≡ nothing → ⊥
    at true  r t ()
    at false r t q' with trans (sym r) t
    ... | ()
outerᵣ?-ok         (rconst c) o ()
outerᵣ?-ok {O = O} (a ·̂ᵣ b)   (oe , or) q with outerᵣ? O a in qa | outerᵣ? O b in qb
... | just _  | just _  = ⊥nothing q
... | nothing | _       = outerᵣ?-ok a ((λ {k} r → oe (∨-left (occᵉ-r k a) _ r)) ,
                                        (λ {k} r → or (∨-left (occʳ-r k a) _ r))) qa
... | just _  | nothing = outerᵣ?-ok b ((λ {k} r → oe (∨-right (occᵉ-r k a) _ r)) ,
                                        (λ {k} r → or (∨-right (occʳ-r k a) _ r))) qb
outerᵣ?-ok {O = O} (a ⊔̂ᵣ b)   (oe , or) q with outerᵣ? O a in qa | outerᵣ? O b in qb
... | just _  | just _  = ⊥nothing q
... | nothing | _       = outerᵣ?-ok a ((λ {k} r → oe (∨-left (occᵉ-r k a) _ r)) ,
                                        (λ {k} r → or (∨-left (occʳ-r k a) _ r))) qa
... | just _  | nothing = outerᵣ?-ok b ((λ {k} r → oe (∨-right (occᵉ-r k a) _ r)) ,
                                        (λ {k} r → or (∨-right (occʳ-r k a) _ r))) qb
outerᵣ?-ok {O = O} ∣ ε ∣̂ᵉ     (oe , or) q with outerₑ? O ε in qe
... | just _  = ⊥nothing q
... | nothing = outerₑ?-ok ε oe qe

-- A strengthening that fails finds the rigid

nothing-of : ∀ {A : Set} → (m : Maybe A) → (∀ {x} → m ≡ just x → ⊥) → m ≡ nothing
nothing-of (just x) f = ⊥-elim (f refl)
nothing-of nothing  f = refl

module _ {Φ} (j : EVar (Φ +e)) where

  strᵉ⁺-occ : ∀ (ε : EExp (Φ +e)) → strᵉ⁺ {Φ} j ε ≡ nothing → occᵉ-e j ε ≡ true
  strᵉ⁺-occ ε q =
    str-occᵉ j ε (nothing-of (strᵉ j ε) (λ r → ⊥just (trans (sym q) (proj₂ (strᵉ⁺-just j ε r)))))

  strʳ⁺-occ : ∀ (ρ : RExp (Φ +e)) → strʳ⁺ {Φ} j ρ ≡ nothing → occᵉ-r j ρ ≡ true
  strʳ⁺-occ ρ q =
    str-occʳ j ρ (nothing-of (strʳ j ρ) (λ r → ⊥just (trans (sym q) (proj₂ (strʳ⁺-just j ρ r)))))

  strᵉ⁺-upd : ∀ (ε : EExp (Φ +e)) c → strᵉ⁺ {Φ} j (ε [ updᵉ j (econst c) ]ᵉ) ≡ nothing → ⊥
  strᵉ⁺-upd ε c q with strᵉ-upd j c ε
  ... | _ , r = ⊥just (trans (sym q) (proj₂ (strᵉ⁺-just j (ε [ updᵉ j (econst c) ]ᵉ) r)))

  strʳ⁺-upd : ∀ (ρ : RExp (Φ +e)) c → strʳ⁺ {Φ} j (ρ [ updᵉ j (econst c) ]ʳ) ≡ nothing → ⊥
  strʳ⁺-upd ρ c q with strʳ-upd j c ρ
  ... | _ , r = ⊥just (trans (sym q) (proj₂ (strʳ⁺-just j (ρ [ updᵉ j (econst c) ]ʳ) r)))

-- At the close of a scope: `P` reads the inner state, `X` the outer one,
-- and `P` followed by moving the rigid is free in no more unknowns than
-- `X` lifted over the rigid. `O` and `O⁺` are the outer unknowns' images
-- without and with the rigid.

module Close {Θ₀ Θ₁ Θ Φ} (P : Subst Θ₀ (Φ +e)) (X : Subst Θ₁ Φ)
             (O : Subst Θ (Φ +e)) (O⁺ : Subst (Θ +e) (Φ +e)) (j : EVar (Φ +e))
             (inc : (P ⨟ˢ popˢ j) ⊆ᶠ (X ↑ᵉ))
             (jP : freeᵉ j P ≡ true)
             (dropₑ : ∀ {ε} → Outerₑ O⁺ ε → occᵉ-e j ε ≡ false → Outerₑ O ε)
             (dropᵣ : ∀ {ρ} → Outerᵣ O⁺ ρ → occᵉ-r j ρ ≡ false → Outerᵣ O ρ) where

  -- a kept side, moved and strengthened, is good for the outer state

  popₑ : ∀ {ε ε₀} → Goodₑ P ε → ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀ → Goodₑ X ε₀
  popₑ g e = unwkₑ X (goodₑ-⊆ inc (subst (Goodₑ (P ⨟ˢ popˢ j)) e (goodₑ-⨟ {P = P} (GV-pop j) g)))

  popᵣ : ∀ {ρ ρ₀} → Goodᵣ P ρ → ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀ → Goodᵣ X ρ₀
  popᵣ g e = unwkᵣ X (goodᵣ-⊆ inc (subst (Goodᵣ (P ⨟ˢ popˢ j)) e (goodᵣ-⨟ {P = P} (GV-pop j) g)))

  popᵛ : ∀ {A A₀} → TyGoodᵛ P A → A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀ → TyGoodᵛ X A₀
  popᵛ {A} {A₀} g e =
    unwkᵛ X A₀ (tygoodᵛ-⊆ inc (wkᵉ-v A₀)
                  (subst (TyGoodᵛ (P ⨟ˢ popˢ j)) e (tygoodᵛ-⨟ {P = P} (GV-pop j) A g)))

  private
    incᵘ : ((P ⨟ˢ updᵉ j ûₑ) ⨟ˢ popˢ j) ⊆ᶠ (X ↑ᵉ)
    incᵘ = ⊆ᶠ-trans (⊆ᶠ-⨟ (upd-⊆ᶠ P j uₑ) (popˢ j) (λ α → α , refl)) inc

  popₑᵘ : ∀ {ε ε₀} → Goodₑ P ε → ε [ updᵉ j ûₑ ]ᵉ [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀ → Goodₑ X ε₀
  popₑᵘ g e =
    unwkₑ X (goodₑ-⊆ incᵘ (subst (Goodₑ ((P ⨟ˢ updᵉ j ûₑ) ⨟ˢ popˢ j)) e
                             (goodₑ-⨟ {P = P ⨟ˢ updᵉ j ûₑ} (GV-pop j)
                                      (goodₑ-⨟ {P = P} (GV-upd j uₑ) g))))

  popᵣᵘ : ∀ {ρ ρ₀} → Goodᵣ P ρ → ρ [ updᵉ j ûₑ ]ʳ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀ → Goodᵣ X ρ₀
  popᵣᵘ g e =
    unwkᵣ X (goodᵣ-⊆ incᵘ (subst (Goodᵣ ((P ⨟ˢ updᵉ j ûₑ) ⨟ˢ popˢ j)) e
                             (goodᵣ-⨟ {P = P ⨟ˢ updᵉ j ûₑ} (GV-pop j)
                                      (goodᵣ-⨟ {P = P} (GV-upd j uₑ) g))))

  -- the orderings one atom step keeps

  stripᵉ-unit-good : (ij? : Maybe (Is-just uₑ-least?)) → ∀ ε ε' ε₀ e₁ → Goodₑ P ε'
                   → ∀ {a} → stripᵉ-unit ij? j ε ε' ε₀ e₁ ≡ just a
                   → ∀ {x y} → (x , y) ∈ proj₁ a → Goodₑ X y
  stripᵉ-unit-good nothing   ε ε' ε₀ e₁ g ()
  stripᵉ-unit-good (just ij) ε ε' ε₀ e₁ g eq with strᵉ⁺ j (ε' [ updᵉ j ûₑ ]ᵉ)
  ... | nothing = ⊥just eq
  ... | just (ε₀' , e₂) with eq
  ...   | refl = λ { (here refl) → popₑᵘ g e₂ }

  stripʳ-unit-good : (ij? : Maybe (Is-just uₑ-least?)) → ∀ ρ ρ' ρ₀ e₁ → Goodᵣ P ρ'
                   → ∀ {a} → stripʳ-unit ij? j ρ ρ' ρ₀ e₁ ≡ just a
                   → ∀ {x y} → (x , y) ∈ proj₁ a → Goodᵣ X y
  stripʳ-unit-good nothing   ρ ρ' ρ₀ e₁ g ()
  stripʳ-unit-good (just ij) ρ ρ' ρ₀ e₁ g eq with strʳ⁺ j (ρ' [ updᵉ j ûₑ ]ʳ)
  ... | nothing = ⊥just eq
  ... | just (ρ₀' , e₂) with eq
  ...   | refl = λ { (here refl) → popᵣᵘ g e₂ }

  stripᵉ-top-good : ∀ ε ε' ε₀' e₁ → Goodₑ P ε'
                  → ∀ {a} → stripᵉ-top O j ε ε' ε₀' e₁ ≡ just a
                  → ∀ {x y} → (x , y) ∈ proj₁ a → Goodₑ X y
  stripᵉ-top-good ε ε' ε₀' e₁ g eq with outerₑ? O ε' | strᵉ⁺ j (ε [ updᵉ j (econst ⊤ₑ) ]ᵉ)
  ... | just _ | just (ε₀ , e₂) with eq
  ...   | refl = λ { (here refl) → popₑ g e₁ }
  stripᵉ-top-good ε ε' ε₀' e₁ g eq | just _  | nothing = ⊥just eq
  stripᵉ-top-good ε ε' ε₀' e₁ g eq | nothing | _       = ⊥just eq

  stripʳ-top-good : ∀ ρ ρ' ρ₀' e₁ → Goodᵣ P ρ'
                  → ∀ {a} → stripʳ-top O j ρ ρ' ρ₀' e₁ ≡ just a
                  → ∀ {x y} → (x , y) ∈ proj₁ a → Goodᵣ X y
  stripʳ-top-good ρ ρ' ρ₀' e₁ g eq with outerᵣ? O ρ' | strʳ⁺ j (ρ [ updᵉ j (econst ⊤ₑ) ]ʳ)
  ... | just _ | just (ρ₀ , e₂) with eq
  ...   | refl = λ { (here refl) → popᵣ g e₁ }
  stripʳ-top-good ρ ρ' ρ₀' e₁ g eq | just _  | nothing = ⊥just eq
  stripʳ-top-good ρ ρ' ρ₀' e₁ g eq | nothing | _       = ⊥just eq

  atomᵉ-good : ∀ ε ε' → Goodₑ P ε' → ∀ {a} → atomᵉ O j ε ε' ≡ just a
             → ∀ {x y} → (x , y) ∈ proj₁ a → Goodₑ X y
  atomᵉ-good ε ε' g eq with strᵉ⁺ j ε | strᵉ⁺ j ε'
  ... | just (ε₀ , e₁) | just (ε₀' , e₂) with eq
  ...   | refl = λ { (here refl) → popₑ g e₂ }
  atomᵉ-good ε ε' g eq | just (ε₀ , e₁) | nothing with decide≾ₑ {Q = ∅ᴴ} ε ε'
  ... | just _  with eq
  ...   | refl = λ ()
  atomᵉ-good ε ε' g eq | just (ε₀ , e₁) | nothing | nothing =
    stripᵉ-unit-good (Is-just? uₑ-least?) ε ε' ε₀ e₁ g eq
  atomᵉ-good ε ε' g eq | nothing | just (ε₀' , e₂) with decide≾ₑ {Q = ∅ᴴ} ε ε'
  ... | just _  with eq
  ...   | refl = λ ()
  atomᵉ-good ε ε' g eq | nothing | just (ε₀' , e₂) | nothing =
    stripᵉ-top-good ε ε' ε₀' e₂ g eq
  atomᵉ-good ε ε' g eq | nothing | nothing with decide≾ₑ {Q = ∅ᴴ} ε ε'
  ... | just _  with eq
  ...   | refl = λ ()
  atomᵉ-good ε ε' g eq | nothing | nothing | nothing = ⊥just eq

  atomʳ-good : ∀ ρ ρ' → Goodᵣ P ρ' → ∀ {a} → atomʳ O j ρ ρ' ≡ just a
             → ∀ {x y} → (x , y) ∈ proj₁ a → Goodᵣ X y
  atomʳ-good ρ ρ' g eq with strʳ⁺ j ρ | strʳ⁺ j ρ'
  ... | just (ρ₀ , e₁) | just (ρ₀' , e₂) with eq
  ...   | refl = λ { (here refl) → popᵣ g e₂ }
  atomʳ-good ρ ρ' g eq | just (ρ₀ , e₁) | nothing with decide≾ᵣ {Q = ∅ᴴ} ρ ρ'
  ... | just _  with eq
  ...   | refl = λ ()
  atomʳ-good ρ ρ' g eq | just (ρ₀ , e₁) | nothing | nothing =
    stripʳ-unit-good (Is-just? uₑ-least?) ρ ρ' ρ₀ e₁ g eq
  atomʳ-good ρ ρ' g eq | nothing | just (ρ₀' , e₂) with decide≾ᵣ {Q = ∅ᴴ} ρ ρ'
  ... | just _  with eq
  ...   | refl = λ ()
  atomʳ-good ρ ρ' g eq | nothing | just (ρ₀' , e₂) | nothing =
    stripʳ-top-good ρ ρ' ρ₀' e₂ g eq
  atomʳ-good ρ ρ' g eq | nothing | nothing with decide≾ᵣ {Q = ∅ᴴ} ρ ρ'
  ... | just _  with eq
  ...   | refl = λ ()
  atomʳ-good ρ ρ' g eq | nothing | nothing | nothing = ⊥just eq

  -- An ordering no atom step keeps, whose greater side is over the
  -- outer unknowns and the rigid, mentions the rigid there: otherwise
  -- it is kept at the top rigid

  top-falseₑ : ∀ ε ε' ε₀' e₂ → stripᵉ-top O j ε ε' ε₀' e₂ ≡ nothing
             → Outerₑ O⁺ ε' → occᵉ-e j ε' ≡ false → ⊥
  top-falseₑ ε ε' ε₀' e₂ eq o q
    with outerₑ? O ε' in oq | strᵉ⁺ j (ε [ updᵉ j (econst ⊤ₑ) ]ᵉ) in sq
  ... | just _  | just _  = ⊥nothing eq
  ... | nothing | _       = outerₑ?-ok ε' (dropₑ {ε'} o q) oq
  ... | just _  | nothing = strᵉ⁺-upd j ε ⊤ₑ sq

  top-falseᵣ : ∀ ρ ρ' ρ₀' e₂ → stripʳ-top O j ρ ρ' ρ₀' e₂ ≡ nothing
             → Outerᵣ O⁺ ρ' → occᵉ-r j ρ' ≡ false → ⊥
  top-falseᵣ ρ ρ' ρ₀' e₂ eq o q
    with outerᵣ? O ρ' in oq | strʳ⁺ j (ρ [ updᵉ j (econst ⊤ₑ) ]ʳ) in sq
  ... | just _  | just _  = ⊥nothing eq
  ... | nothing | _       = outerᵣ?-ok ρ' (dropᵣ {ρ'} o q) oq
  ... | just _  | nothing = strʳ⁺-upd j ρ ⊤ₑ sq

  atomᵉ-false : ∀ ε ε' → atomᵉ O j ε ε' ≡ nothing → Outerₑ O⁺ ε' → occᵉ-e j ε' ≡ false → ⊥
  atomᵉ-false ε ε' eq o q with strᵉ⁺ j ε | strᵉ⁺ j ε' in e'
  ... | just _  | just _ = ⊥nothing eq
  ... | _       | nothing with trans (sym (strᵉ⁺-occ j ε' e')) q
  ...   | ()
  atomᵉ-false ε ε' eq o q | nothing | just (ε₀' , e₂) with decide≾ₑ {Q = ∅ᴴ} ε ε'
  ... | just _  = ⊥nothing eq
  ... | nothing = top-falseₑ ε ε' ε₀' e₂ eq o q

  atomʳ-false : ∀ ρ ρ' → atomʳ O j ρ ρ' ≡ nothing → Outerᵣ O⁺ ρ' → occᵉ-r j ρ' ≡ false → ⊥
  atomʳ-false ρ ρ' eq o q with strʳ⁺ j ρ | strʳ⁺ j ρ' in e'
  ... | just _  | just _ = ⊥nothing eq
  ... | _       | nothing with trans (sym (strʳ⁺-occ j ρ' e')) q
  ...   | ()
  atomʳ-false ρ ρ' eq o q | nothing | just (ρ₀' , e₂) with decide≾ᵣ {Q = ∅ᴴ} ρ ρ'
  ... | just _  = ⊥nothing eq
  ... | nothing = top-falseᵣ ρ ρ' ρ₀' e₂ eq o q

  -- so, by I1′, it mentions protected unknowns only

  deferredₑ : ∀ ε ε' → Goodₑ P ε' → atomᵉ O j ε ε' ≡ nothing → Outerₑ O⁺ ε'
            → Outerₑ (X ↑ᵉ) (ε' [ popˢ j ]ᵉ)
  deferredₑ ε ε' g eq o = outerₑ-⊆ {ε = ε' [ popˢ j ]ᵉ} inc (outerₑ-⨟ P (popˢ j) {ε'} (prot g))
    where
      prot : Goodₑ P ε' → Outerₑ P ε'
      prot (outer o') = o'
      prot (whole k) with occᵉ-e {Φ +e} j (evar k) in q
      ... | false = ⊥-elim (atomᵉ-false ε ε' eq o q)
      ... | true  = out
        where
          out : Outerₑ P (evar k)
          out {k'} r = subst (λ x → freeᵉ x P ≡ true)
                             (trans (true-dec (j ≟ᶠ k) q) (sym (true-dec (k' ≟ᶠ k) r))) jP

  deferredᵣ : ∀ ρ ρ' → Goodᵣ P ρ' → atomʳ O j ρ ρ' ≡ nothing → Outerᵣ O⁺ ρ'
            → Outerᵣ (X ↑ᵉ) (ρ' [ popˢ j ]ʳ)
  deferredᵣ ρ ρ' g eq o = outerᵣ-⊆ {ρ = ρ' [ popˢ j ]ʳ} inc (outerᵣ-⨟ P (popˢ j) {ρ'} (prot g))
    where
      prot : Goodᵣ P ρ' → Outerᵣ P ρ'
      prot (outer o') = o'
      prot (whole k)  = ⊥-elim (atomʳ-false ρ ρ' eq o refl)

  -- the lists

  listᵉ-good : ∀ l → (∀ {x y} → (x , y) ∈ l → Goodₑ P y)
             → ∀ {a} → listᵉ O O⁺ j l ≡ just a
             → (∀ {x y} → (x , y) ∈ proj₁ a → Goodₑ X y)
             × (∀ {x y} → (x , y) ∈ proj₁ (proj₂ a) → Outerₑ (X ↑ᵉ) y)
  listᵉ-good []              g refl = (λ ()) , (λ ())
  listᵉ-good ((ε , ε') ∷ l) g eq with listᵉ O O⁺ j l in e₂
  ... | nothing = ⊥just eq
  ... | just (l₀ , d₀ , f) with atomᵉ O j ε ε' in e₁
  ...   | just (a , fa) with eq
  ...     | refl = (λ m → [ atomᵉ-good ε ε' (g (here refl)) e₁ , proj₁ ih ]′ (∈-++⁻ a m))
                 , proj₂ ih
    where
      ih = listᵉ-good l (λ m → g (there m)) e₂
  listᵉ-good ((ε , ε') ∷ l) g eq | just (l₀ , d₀ , f) | nothing
    with outerₑ? O⁺ ε | outerₑ? O⁺ ε'
  ... | just o | just o' with eq
  ...   | refl = proj₁ ih
               , (λ { (here refl) → deferredₑ ε ε' (g (here refl)) e₁ o'
                    ; (there m)   → proj₂ ih m })
    where
      ih = listᵉ-good l (λ m → g (there m)) e₂
  listᵉ-good ((ε , ε') ∷ l) g eq | just _ | nothing | just _  | nothing = ⊥just eq
  listᵉ-good ((ε , ε') ∷ l) g eq | just _ | nothing | nothing | _       = ⊥just eq

  listʳ-good : ∀ l → (∀ {x y} → (x , y) ∈ l → Goodᵣ P y)
             → ∀ {a} → listʳ O O⁺ j l ≡ just a
             → (∀ {x y} → (x , y) ∈ proj₁ a → Goodᵣ X y)
             × (∀ {x y} → (x , y) ∈ proj₁ (proj₂ a) → Outerᵣ (X ↑ᵉ) y)
  listʳ-good []              g refl = (λ ()) , (λ ())
  listʳ-good ((ρ , ρ') ∷ l) g eq with listʳ O O⁺ j l in e₂
  ... | nothing = ⊥just eq
  ... | just (l₀ , d₀ , f) with atomʳ O j ρ ρ' in e₁
  ...   | just (a , fa) with eq
  ...     | refl = (λ m → [ atomʳ-good ρ ρ' (g (here refl)) e₁ , proj₁ ih ]′ (∈-++⁻ a m))
                 , proj₂ ih
    where
      ih = listʳ-good l (λ m → g (there m)) e₂
  listʳ-good ((ρ , ρ') ∷ l) g eq | just (l₀ , d₀ , f) | nothing
    with outerᵣ? O⁺ ρ | outerᵣ? O⁺ ρ'
  ... | just o | just o' with eq
  ...   | refl = proj₁ ih
               , (λ { (here refl) → deferredᵣ ρ ρ' (g (here refl)) e₁ o'
                    ; (there m)   → proj₂ ih m })
    where
      ih = listʳ-good l (λ m → g (there m)) e₂
  listʳ-good ((ρ , ρ') ∷ l) g eq | just _ | nothing | just _  | nothing = ⊥just eq
  listʳ-good ((ρ , ρ') ∷ l) g eq | just _ | nothing | nothing | _       = ⊥just eq

  atomˢ-good : ∀ A B → TyGoodᵛ P A → TyGoodᵛ P B → ∀ {a} → atomˢ j A B ≡ just a
             → ∀ {A₀ B₀} → (A₀ , B₀) ∈ proj₁ a → TyGoodᵛ X A₀ × TyGoodᵛ X B₀
  atomˢ-good A B gA gB eq with strᵛ⁺ j A | strᵛ⁺ j B
  ... | just (A₀ , e₁) | just (B₀ , e₂) with eq
  ...   | refl = λ { (here refl) → popᵛ gA e₁ , popᵛ gB e₂ }
  atomˢ-good A B gA gB eq | just _  | nothing = ⊥just eq
  atomˢ-good A B gA gB eq | nothing | _       = ⊥just eq

  listˢ-good : ∀ l → (∀ {A B} → (A , B) ∈ l → TyGoodᵛ P A × TyGoodᵛ P B)
             → ∀ {a} → listˢ j l ≡ just a
             → ∀ {A₀ B₀} → (A₀ , B₀) ∈ proj₁ a → TyGoodᵛ X A₀ × TyGoodᵛ X B₀
  listˢ-good []             g refl = λ ()
  listˢ-good ((A , B) ∷ l) g eq with atomˢ j A B in e₁ | listˢ j l in e₂
  ... | just (a , fa) | just (l₁ , f) with eq
  ...   | refl = λ m → [ atomˢ-good A B (proj₁ (g (here refl))) (proj₂ (g (here refl))) e₁
                       , listˢ-good l (λ m' → g (there m')) e₂ ]′ (∈-++⁻ a m)
  listˢ-good ((A , B) ∷ l) g eq | just _  | nothing = ⊥just eq
  listˢ-good ((A , B) ∷ l) g eq | nothing | _       = ⊥just eq

  -- The split of the inner residual: I1′ and I5 for the outer state

  splitᴿ-good : ∀ R → ResInv P R → ∀ {a} → splitᴿ O O⁺ j R ≡ solved a → ResInv X (proj₁ a)
  splitᴿ-good R r eq
    with listᵗ j (ts R) | listˢ j (ss R) in e₄ | listᵈ j (ds R)
       | listʳ O O⁺ j (rs R) in e₁ | listᵉ O O⁺ j (es R) in e₂ | outerD? O⁺ (dfs R)
  ... | just (lt , ft) | just (ls , fs) | just (ld , fd)
      | just (lr , dr , fr) | just (le , de , fe) | just od with eq
  ...   | refl = mkResInv (listˢ-good (ss R) (inv-ss r) e₄) (proj₁ pr) (proj₁ pe) dfs'
    where
      pr = listʳ-good (rs R) (I1′ʳ r) e₁
      pe = listᵉ-good (es R) (I1′ᵉ r) e₂

      dfs' : ∀ {E} → E ∈ (closeᵈ (dfr nothing 0 (ords dr de)) ∷ map (liftᵈ j) (dfs R))
           → Great X E
      dfs' (here refl) = great-close X (dfr nothing 0 (ords dr de)) (mkGreat (proj₂ pr) (proj₂ pe))
      dfs' (there m) with ∈-map⁻ (liftᵈ j) m
      ... | E₀ , m₀ , refl = great-lift P X j inc E₀ (I5 r m₀)
  splitᴿ-good R r eq | nothing | _       | _       | _      | _      | _       = ⊥refuted eq
  splitᴿ-good R r eq | just _  | nothing | _       | _      | _      | _       = ⊥refuted eq
  splitᴿ-good R r eq | just _  | just _  | nothing | _      | _      | _       = ⊥refuted eq
  splitᴿ-good R r eq | just _  | just _  | just _  | nothing | _     | _       = ⊥stuck eq
  splitᴿ-good R r eq | just _  | just _  | just _  | just _ | nothing | _      = ⊥stuck eq
  splitᴿ-good R r eq | just _  | just _  | just _  | just _ | just _ | nothing = ⊥stuck eq

------------------------------------------------------------------------
-- The close of a clause's scope keeps the invariants: the kept atoms
-- and the new entry by `Close`, the outer residual by the outer
-- unknowns' good move

popᵉ-inv : ∀ {Θ₀ Θ} → (π : Subst Θ₀ Θ) → (s : St Θ) → (C : Constraint (Θ +e))
         → (Φ : Scope) → (θ'' : Subst (Θ +e) Φ) → (R'' : Resid Φ) → (rg'' : Rig Φ)
         → (m'' : ⇑ᵉˢ s ⟶ st Φ θ'' R'' rg'') → (w'' : Wit (st Φ θ'' R'' rg'') C)
         → Inv π s → ResInv ((π ↑ᵉ) ⨟ˢ θ'') R''
         → GV ((π ↑ᵉ) ⨟ˢ θ'') (wkˢᵉ {Ψ s} ⨟ˢ mδ m'')
         → ∀ {s' : St Θ} {m : s ⟶ s'} {w : Wit s' (∀ᵉ C)}
         → popᵉ s C Φ θ'' R'' rg'' m'' w'' ≡ solved (s' , m , w)
         → Inv π s' × GoodMove π m
popᵉ-inv π s C (scope nt nr nzero) θ'' R'' rg'' m'' w'' iv ri gm ()
popᵉ-inv π s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' iv ri gm eq
  with evar? (sE (mδ m'') (newᵉ {Ψ s}))
... | nothing = ⊥refuted eq
... | just (j , eqj) with strSub j (wkˢᵉ {Ψ s} ⨟ˢ mδ m'')
                        | splitᴿ (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') (mδ m'') j R'' in eqsp
...   | just (δ₀ , pδ) | solved (R₀ , tr) with eq
...     | refl = mkInv invθ (resinv-∪ (resinv-⊆ toX (resinv-subst gδ₀' (inv-R iv))) R₀-inv) , gδ₀
  where
    γ  = mδ m''
    P'' = (π ↑ᵉ) ⨟ˢ θ''
    X  = π ⨟ˢ (θ s ⨟ˢ δ₀)

    key : (θ'' ⨟ˢ popˢ j) ≐ˢ ((θ s ⨟ˢ δ₀) ↑ᵉ)
    key = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m'')) (popˢ j))
          (≐ˢ-trans (⨟-assoc (θ s ↑ᵉ) γ (popˢ j))
          (≐ˢ-trans (⨟-congʳ (θ s ↑ᵉ) (pop-key γ eqj pδ)) (⨟-↑ᵉ (θ s) δ₀)))

    incl : (P'' ⨟ˢ popˢ j) ⊆ᶠ (X ↑ᵉ)
    incl = ≐→⊆ᶠ (≐ˢ-trans (⨟-assoc (π ↑ᵉ) θ'' (popˢ j))
                (≐ˢ-trans (⨟-congʳ (π ↑ᵉ) key) (⨟-↑ᵉ π (θ s ⨟ˢ δ₀))))

    -- the rigid is the image of the scope's own variable
    jP : freeᵉ j P'' ≡ true
    jP = ∨-right (anyᶠ (λ α → occᵉ-v j (sTy P'' α))) _
           (∨-right (anyᶠ (λ i → occᵉ-r j (sR P'' i))) _
             (anyᶠ-intro (λ i → occᵉ-e j (sE P'' i)) zero
               (subst (λ x → occᵉ-e j x ≡ true)
                      (sym (trans (sym (≐ᵉ (mtri m'') zero)) eqj))
                      (dec-true (j ≟ᶠ j) refl))))

    -- the images of the outer unknowns, and the rigid
    split≐ : γ ≐ˢ ((wkˢᵉ {Ψ s} ⨟ˢ γ) ,ᵉ evar j)
    split≐ = mk≐ˢ (λ α → refl) (λ i → refl) (λ { zero → eqj ; (suc i) → refl })

    dropᶠ : ∀ {k} → freeᵉ k γ ≡ true → (k ≡ j → ⊥) → freeᵉ k (wkˢᵉ {Ψ s} ⨟ˢ γ) ≡ true
    dropᶠ {k} q ne with freeᵉ-,ᵉ⁻ (wkˢᵉ {Ψ s} ⨟ˢ γ) (evar j) (trans (sym (freeᵉ-≐ split≐ k)) q)
    ... | inj₁ r = ⊥-elim (ne (true-dec (k ≟ᶠ j) r))
    ... | inj₂ r = r

    dropₑ : ∀ {ε} → Outerₑ γ ε → occᵉ-e j ε ≡ false → Outerₑ (wkˢᵉ {Ψ s} ⨟ˢ γ) ε
    dropₑ {ε} o q {k} r = dropᶠ (o r) (λ { refl → case (trans (sym q) r) })
      where
        case : false ≡ true → ⊥
        case ()

    dropᵣ : ∀ {ρ} → Outerᵣ γ ρ → occᵉ-r j ρ ≡ false → Outerᵣ (wkˢᵉ {Ψ s} ⨟ˢ γ) ρ
    dropᵣ {ρ} (oe , or) q =
      (λ {k} r → dropᶠ (oe r) (λ { refl → case (trans (sym q) r) })) ,
      (λ {k} r → trans (sym (freeʳ-≐ split≐ k)) (or r))
      where
        case : false ≡ true → ⊥
        case ()

    open Close P'' X (wkˢᵉ {Ψ s} ⨟ˢ γ) γ j incl jP (λ {ε} → dropₑ {ε}) (λ {ρ} → dropᵣ {ρ})

    -- the outer unknowns move well
    gδ₀ : GV X δ₀
    gδ₀ = mkGV (λ α → popᵛ {sTy γ α} (gvᵗ gm α) (trans (≐ᵗ pδ α) (wkˢᵉ-v (sTy δ₀ α))))
               (λ i → popᵣ {sR γ i} (gvʳ gm i) (trans (≐ʳ pδ i) (wkˢᵉ-r (sR δ₀ i))))
               (λ i → popₑ {sE γ (suc i)} (gvᵉ gm i) (trans (≐ᵉ pδ i) (wkˢᵉ-e (sE δ₀ i))))

    toX : ((π ⨟ˢ θ s) ⨟ˢ δ₀) ⊆ᶠ X
    toX = ≐→⊆ᶠ (⨟-assoc π (θ s) δ₀)

    gδ₀' : GV ((π ⨟ˢ θ s) ⨟ˢ δ₀) δ₀
    gδ₀' = GV-⊆ (≐→⊆ᶠ (≐ˢ-sym (⨟-assoc π (θ s) δ₀))) gδ₀

    invθ : GV X (θ s ⨟ˢ δ₀)
    invθ = GV-⊆ toX (GV-⨟ {P = π ⨟ˢ θ s} (inv-θ iv) gδ₀')

    R₀-inv : ResInv X R₀
    R₀-inv = splitᴿ-good R'' ri eqsp
popᵉ-inv π s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' iv ri gm eq
  | just (j , eqj) | just _ | refuted = ⊥refuted eq
popᵉ-inv π s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' iv ri gm eq
  | just (j , eqj) | just _ | stuck = ⊥stuck eq
popᵉ-inv π s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' iv ri gm eq
  | just (j , eqj) | nothing | _ = ⊥refuted eq

------------------------------------------------------------------------
-- Decomposing subtyping demands: the orderings produced are between
-- grades of the two types, so good ones

record AtomsGood {Θ Ψ} (P : Subst Θ Ψ) (a : SubAtoms Ψ) : Set where
  constructor mkAG
  field
    agʳ : ∀ {x y} → (x , y) ∈ aordᵣ a → Goodᵣ P y
    agᵉ : ∀ {x y} → (x , y) ∈ aordₑ a → Goodₑ P y

open AtomsGood public

ag-none : ∀ {Θ Ψ} {P : Subst Θ Ψ} → AtomsGood P (noAtoms {Ψ})
ag-none = mkAG (λ ()) (λ ())

ag-∪ : ∀ {Θ Ψ} {P : Subst Θ Ψ} {a b : SubAtoms Ψ}
     → AtomsGood P a → AtomsGood P b → AtomsGood P (a ∪ᴬ b)
ag-∪ {a = a} g h = mkAG (λ m → [ agʳ g , agʳ h ]′ (∈-++⁻ (aordᵣ a) m))
                        (λ m → [ agᵉ g , agᵉ h ]′ (∈-++⁻ (aordₑ a) m))

module _ {Θ Ψ} (P : Subst Θ Ψ) where

  mutual

    subDec-good : ∀ (A B : OVType Ψ) → TyGoodᵛ P A → TyGoodᵛ P B
                → ∀ {d} → subDec A B ≡ just d → AtomsGood P (atomsOf d)
    subDec-good (tvar α) (tvar β) gA gB refl = mkAG (λ ()) (λ ())
    subDec-good (Base b) (Base b') gA gB eq with b ≡ᵇ? b'
    ... | yes refl with eq
    ...   | refl = ag-none
    subDec-good (Base b) (Base b') gA gB () | no _
    subDec-good Unit  Unit  gA gB refl = ag-none
    subDec-good Bool  Bool  gA gB refl = ag-none
    subDec-good Empty Empty gA gB refl = ag-none
    subDec-good (A |×| B) (A' |×| B') (gA , gB) (gA' , gB') eq
      with zip₂-just pairᴰ (subDec A A') (subDec B B') eq
    ... | d₁ , d₂ , e₁ , e₂ , refl = ag-∪ (subDec-good A A' gA gA' e₁) (subDec-good B B' gB gB' e₂)
    subDec-good (A ⇒ C) (A' ⇒ C') (gA , gC) (gA' , gC') eq
      with zip₂-just arrᴰ (subDec A' A) (subDecᶜ C C') eq
    ... | d₁ , d₂ , e₁ , e₂ , refl = ag-∪ (subDec-good A' A gA' gA e₁) (subDecᶜ-good C C' gC gC' e₂)
    subDec-good ([ ρ ] A) ([ ρ' ] A') (gρ , gA) (gρ' , gA') eq
      with subDec A A' in e
    ... | just d with eq
    ...   | refl = ag-∪ (mkAG (λ { (here refl) → gρ }) (λ ())) (subDec-good A A' gA gA' e)
    subDec-good ([ ρ ] A) ([ ρ' ] A') (gρ , gA) (gρ' , gA') () | nothing
    subDec-good (tvar α) (Base b') gA gB ()
    subDec-good (tvar α) (Unit) gA gB ()
    subDec-good (tvar α) (Bool) gA gB ()
    subDec-good (tvar α) (A' |×| B') gA gB ()
    subDec-good (tvar α) (Empty) gA gB ()
    subDec-good (tvar α) (A' ⇒ C') gA gB ()
    subDec-good (tvar α) ([ ρ' ] A') gA gB ()
    subDec-good (Base b) (tvar β) gA gB ()
    subDec-good (Base b) (Unit) gA gB ()
    subDec-good (Base b) (Bool) gA gB ()
    subDec-good (Base b) (A' |×| B') gA gB ()
    subDec-good (Base b) (Empty) gA gB ()
    subDec-good (Base b) (A' ⇒ C') gA gB ()
    subDec-good (Base b) ([ ρ' ] A') gA gB ()
    subDec-good (Unit) (tvar β) gA gB ()
    subDec-good (Unit) (Base b') gA gB ()
    subDec-good (Unit) (Bool) gA gB ()
    subDec-good (Unit) (A' |×| B') gA gB ()
    subDec-good (Unit) (Empty) gA gB ()
    subDec-good (Unit) (A' ⇒ C') gA gB ()
    subDec-good (Unit) ([ ρ' ] A') gA gB ()
    subDec-good (Bool) (tvar β) gA gB ()
    subDec-good (Bool) (Base b') gA gB ()
    subDec-good (Bool) (Unit) gA gB ()
    subDec-good (Bool) (A' |×| B') gA gB ()
    subDec-good (Bool) (Empty) gA gB ()
    subDec-good (Bool) (A' ⇒ C') gA gB ()
    subDec-good (Bool) ([ ρ' ] A') gA gB ()
    subDec-good (A |×| B) (tvar β) gA gB ()
    subDec-good (A |×| B) (Base b') gA gB ()
    subDec-good (A |×| B) (Unit) gA gB ()
    subDec-good (A |×| B) (Bool) gA gB ()
    subDec-good (A |×| B) (Empty) gA gB ()
    subDec-good (A |×| B) (A' ⇒ C') gA gB ()
    subDec-good (A |×| B) ([ ρ' ] A') gA gB ()
    subDec-good (Empty) (tvar β) gA gB ()
    subDec-good (Empty) (Base b') gA gB ()
    subDec-good (Empty) (Unit) gA gB ()
    subDec-good (Empty) (Bool) gA gB ()
    subDec-good (Empty) (A' |×| B') gA gB ()
    subDec-good (Empty) (A' ⇒ C') gA gB ()
    subDec-good (Empty) ([ ρ' ] A') gA gB ()
    subDec-good (A ⇒ C) (tvar β) gA gB ()
    subDec-good (A ⇒ C) (Base b') gA gB ()
    subDec-good (A ⇒ C) (Unit) gA gB ()
    subDec-good (A ⇒ C) (Bool) gA gB ()
    subDec-good (A ⇒ C) (A' |×| B') gA gB ()
    subDec-good (A ⇒ C) (Empty) gA gB ()
    subDec-good (A ⇒ C) ([ ρ' ] A') gA gB ()
    subDec-good ([ ρ ] A) (tvar β) gA gB ()
    subDec-good ([ ρ ] A) (Base b') gA gB ()
    subDec-good ([ ρ ] A) (Unit) gA gB ()
    subDec-good ([ ρ ] A) (Bool) gA gB ()
    subDec-good ([ ρ ] A) (A' |×| B') gA gB ()
    subDec-good ([ ρ ] A) (Empty) gA gB ()
    subDec-good ([ ρ ] A) (A' ⇒ C') gA gB ()

    subDecᶜ-good : ∀ (C D : OCType Ψ) → TyGoodᶜ P C → TyGoodᶜ P D
                 → ∀ {d} → subDecᶜ C D ≡ just d → AtomsGood P (atomsOfᶜ d)
    subDecᶜ-good (A ‼ ε) (A' ‼ ε') (gA , gε) (gA' , gε') eq with subDec A A' in e
    ... | just d with eq
    ...   | refl = ag-∪ (subDec-good A A' gA gA' e) (mkAG (λ ()) (λ { (here refl) → gε' }))
    subDecᶜ-good (A ‼ ε) (A' ‼ ε') (gA , gε) (gA' , gε') () | nothing

  subsList-good : ∀ (l : List (OVType Ψ × OVType Ψ))
                → (∀ {A B} → (A , B) ∈ l → TyGoodᵛ P A × TyGoodᵛ P B)
                → ∀ {d} → subsList l ≡ just d → AtomsGood P (atomsOfˢ d)
  subsList-good []             g refl = ag-none
  subsList-good ((A , B) ∷ l) g eq with subDec A B in e₁ | subsList l in e₂
  ... | just d | just ds with eq
  ...   | refl = ag-∪ (subDec-good A B (proj₁ (g (here refl))) (proj₂ (g (here refl))) e₁)
                      (subsList-good l (λ m → g (there m)) e₂)
  subsList-good ((A , B) ∷ l) g () | just _  | nothing
  subsList-good ((A , B) ∷ l) g () | nothing | _

-- A residual with its subtyping demands decomposed

resinv-atomise : ∀ {Θ Ψ} {P : Subst Θ Ψ} → (R : Resid Ψ) → (d : SubsDec (ss R))
               → AtomsGood P (atomsOfˢ d) → ResInv P R → ResInv P (atomiseᴿ R d)
resinv-atomise R d ag r =
  mkResInv sᵢ (λ m → [ I1′ʳ r , agʳ ag ]′ (∈-++⁻ (rs R) m))
              (λ m → [ I1′ᵉ r , agᵉ ag ]′ (∈-++⁻ (es R) m)) (I5 r)
  where
    sᵢ : ∀ {A B} → (A , B) ∈ map (mapᵖ tvar) (asubᵥ (atomsOfˢ d)) → _ × _
    sᵢ m with ∈-map⁻ (mapᵖ tvar) m
    ... | (α , β) , m₀ , refl = tt , tt

resinv-atoms : ∀ {Θ Ψ} {P : Subst Θ Ψ} → (a : SubAtoms Ψ) → AtomsGood P a → ResInv P (atomsᴿ a)
resinv-atoms a ag = mkResInv sᵢ (agʳ ag) (agᵉ ag) (λ ())
  where
    sᵢ : ∀ {A B} → (A , B) ∈ map (mapᵖ tvar) (asubᵥ a) → _ × _
    sᵢ m with ∈-map⁻ (mapᵖ tvar) m
    ... | (α , β) , m₀ , refl = tt , tt

------------------------------------------------------------------------
-- Moves

-- The substitution a state is read with, after a move

at-move : ∀ {Θ₀ Θ} → (π : Subst Θ₀ Θ) → {s s' : St Θ} → (m : s ⟶ s')
        → ((π ⨟ˢ θ s) ⨟ˢ mδ m) ≐ˢ (π ⨟ˢ θ s')
at-move π {s} m = ≐ˢ-trans (⨟-assoc π (θ s) (mδ m)) (⨟-congʳ π (mtri m))

goodMove-⨟ : ∀ {Θ₀ Θ} → (π : Subst Θ₀ Θ) → {s s₁ s₂ : St Θ} → (m₁ : s ⟶ s₁) → (m₂ : s₁ ⟶ s₂)
           → GoodMove π m₁ → GoodMove π m₂ → GoodMove π (⟶-⨟ m₁ m₂)
goodMove-⨟ π {s₁ = s₁} m₁ m₂ g₁ g₂ =
  GV-⊆ (≐→⊆ᶠ (at-move π m₂))
       (GV-⨟ {P = π ⨟ˢ θ s₁} g₁ (GV-⊆ (≐→⊆ᶠ (≐ˢ-sym (at-move π m₂))) g₂))

-- A good move carries the images of the program's variables

inv-θ-move : ∀ {Θ₀ Θ} → (π : Subst Θ₀ Θ) → {s s' : St Θ} → (m : s ⟶ s')
           → GV (π ⨟ˢ θ s) (θ s) → GoodMove π m → GV (π ⨟ˢ θ s') (θ s')
inv-θ-move π {s} m g gm =
  GV-≐ (mtri m) (GV-⊆ (≐→⊆ᶠ (at-move π m))
                      (GV-⨟ {P = π ⨟ˢ θ s} g (GV-⊆ (≐→⊆ᶠ (≐ˢ-sym (at-move π m))) gm)))

------------------------------------------------------------------------
-- The constraints generation gives: every greater side, and every
-- grade of a type, whole or over the program's variables and the
-- enclosing rigids

Shape : ∀ {Θ₀ Θ} → Subst Θ₀ Θ → Constraint Θ → Set
Shape π ⊤̂           = ⊤
Shape π ⊥̂           = ⊤
Shape π (C ∧̂ D)     = Shape π C × Shape π D
Shape π (A ≐ᵥ B)    = TyGoodᵛ π A × TyGoodᵛ π B
Shape π (A ≾̂ᵥᶜ B)   = TyGoodᵛ π A × TyGoodᵛ π B
Shape π (ρ ≾̂ᵣᶜ ρ')  = Goodᵣ π ρ'
Shape π (ε ≾̂ₑᶜ ε')  = Goodₑ π ε'
Shape π (Etᶜ A)     = ⊤
Shape π (Et∨≾ᵘ A ρ) = ⊤
Shape π (∃ᵗ C)      = Shape (π ⨟ˢ wkˢᵗ) C
Shape π (∃ʳ C)      = Shape (π ⨟ˢ wkˢʳ) C
Shape π (∃ᵉ C)      = Shape (π ⨟ˢ wkˢᵉ) C
Shape π (∀ᵉ C)      = Shape (π ↑ᵉ) C
Shape π (⋀ᵒᵖ f)     = ∀ op → Shape π (f op)

------------------------------------------------------------------------
-- The step whose preservation is not proved here, stated about the
-- existing function: `localise` keeps I1′ and I5 for the unknowns the
-- scope was entered with.

record Pending : Set where
  field
    localise-good : ∀ {Θ₀ Θ Φ} → (O : Subst (Θ +e) Φ) → (P : Subst Θ₀ Φ) → (R : Resid Φ)
                  → P ⊆ᶠ O → ResInv P R → ResInv P (lR (localise O R))

------------------------------------------------------------------------
-- Entering a binder, and leaving it

inv-↑ᵗ : ∀ {Θ₀ Θ} {π : Subst Θ₀ Θ} {s : St Θ} → Inv π s → Inv (π ⨟ˢ wkˢᵗ) (s ↑ᵗˢ)
inv-↑ᵗ {π = π} {s} iv =
  mkInv (GV-⊆ inc (GV-↑ᵗ (inv-θ iv))) (resinv-⊆ inc (resinv-subst GV-wkᵗ (inv-R iv)))
  where
    inc = ≐→⊆ᶠ (≐ˢ-trans (⨟-assoc π (θ s) wkˢᵗ)
               (≐ˢ-trans (⨟-congʳ π (≐ˢ-sym (wkˢᵗ-↑ᵗ (θ s)))) (≐ˢ-sym (⨟-assoc π wkˢᵗ (θ s ↑ᵗ)))))

inv-↑ʳ : ∀ {Θ₀ Θ} {π : Subst Θ₀ Θ} {s : St Θ} → Inv π s → Inv (π ⨟ˢ wkˢʳ) (s ↑ʳˢ)
inv-↑ʳ {π = π} {s} iv =
  mkInv (GV-⊆ inc (GV-↑ʳ (inv-θ iv))) (resinv-⊆ inc (resinv-subst GV-wkʳ (inv-R iv)))
  where
    inc = ≐→⊆ᶠ (≐ˢ-trans (⨟-assoc π (θ s) wkˢʳ)
               (≐ˢ-trans (⨟-congʳ π (≐ˢ-sym (wkˢʳ-↑ʳ (θ s)))) (≐ˢ-sym (⨟-assoc π wkˢʳ (θ s ↑ʳ)))))

inv-↑ᵉ : ∀ {Θ₀ Θ} {π : Subst Θ₀ Θ} {s : St Θ} → Inv π s → Inv (π ⨟ˢ wkˢᵉ) (s ↑ᵉˢ)
inv-↑ᵉ {π = π} {s} iv =
  mkInv (GV-⊆ inc (GV-↑ᵉ (inv-θ iv))) (resinv-⊆ inc (resinv-subst GV-wkᵉ (inv-R iv)))
  where
    inc = ≐→⊆ᶠ (≐ˢ-trans (⨟-assoc π (θ s) wkˢᵉ)
               (≐ˢ-trans (⨟-congʳ π (≐ˢ-sym (wkˢᵉ-↑ᵉ (θ s)))) (≐ˢ-sym (⨟-assoc π wkˢᵉ (θ s ↑ᵉ)))))

-- A rigid binder: the rigid is the image of the binder's own variable

inv-⇑ : ∀ {Θ₀ Θ} {π : Subst Θ₀ Θ} {s : St Θ} → Inv π s → Inv (π ↑ᵉ) (⇑ᵉˢ s)
inv-⇑ {π = π} {s} iv =
  mkInv (GV-⊆ (⊆ᶠ-trans (wk-⊆ᶠ-↑ᵉ (π ⨟ˢ θ s)) (≐→⊆ᶠ (≐ˢ-sym (⨟-↑ᵉ π (θ s)))))
              (GV-↑ᵉ (inv-θ iv)))
        resinv-empty

------------------------------------------------------------------------
-- Retrying the deferred conditions drops orderings and entries

keptOf : ∀ {Ψ} {H : Hyps Ψ} {E : Dfr Ψ} → Retried H E → List (Dfr Ψ)
keptOf (refutedᵈ _)   = []
keptOf (keptᵈ D _ _)  = D

great-retryᵈ : ∀ {Θ Ψ} {X : Subst Θ Ψ} → (H : Hyps Ψ) → (E : Dfr Ψ) → Great X E
             → ∀ {E'} → E' ∈ keptOf (retryᵈ H E) → Great X E'
great-retryᵈ {X = X} H (dfr l k o) g
  with sift (verdictʳ H k) (ors o) | sift (verdictᵉ H k) (oes o)
... | inj₁ _                 | _                      = λ ()
... | inj₂ _                 | inj₁ _                 = λ ()
... | inj₂ (sifted lr sr br) | inj₂ (sifted le se be) = kept lr le sr se
  where
    kept : ∀ lr le → (∀ {a} → a ∈ lr → a ∈ ors o) → (∀ {a} → a ∈ le → a ∈ oes o)
         → ∀ {E'} → E' ∈ unlessEmpty l k (ords lr le) → Great X E'
    kept []      []      sr' se' ()
    kept (a ∷ r) le      sr' se' (here refl) =
      mkGreat (λ m → greatʳ g (sr' m)) (λ m → greatᵉ g (se' m))
    kept []      (a ∷ e) sr' se' (here refl) =
      mkGreat (λ m → greatʳ g (sr' m)) (λ m → greatᵉ g (se' m))

keptᴰ : ∀ {Ψ} {H : Hyps Ψ} {D : List (Dfr Ψ)} → RefutedL D ⊎ RetriedL H D → List (Dfr Ψ)
keptᴰ (inj₁ _) = []
keptᴰ (inj₂ r) = RetriedL.D' r

great-retryᴰ : ∀ {Θ Ψ} {X : Subst Θ Ψ} → (H : Hyps Ψ) → (D : List (Dfr Ψ))
             → (∀ {E} → E ∈ D → Great X E)
             → ∀ {E'} → E' ∈ keptᴰ (retryᴰ H D) → Great X E'
great-retryᴰ H []      g = λ ()
great-retryᴰ H (E ∷ D) g
  with retryᵈ H E | great-retryᵈ H E (g (here refl))
     | retryᴰ H D | great-retryᴰ H D (λ m' → g (there m'))
... | refutedᵈ _     | _  | _                       | _  = λ ()
... | keptᵈ _ _ _    | _  | inj₁ _                  | _  = λ ()
... | keptᵈ Dₑ bₑ fₑ | gₑ | inj₂ (retriedL D'' b f) | gs = λ m → [ gₑ , gs ]′ (∈-++⁻ Dₑ m)

retry-inv : ∀ {Θ₀ Θ} → (π : Subst Θ₀ Θ) → (s : St Θ) → Inv π s
          → ∀ {s' : St Θ} {m : s ⟶ s'} → retry s ≡ just (s' , m) → Inv π s' × GoodMove π m
retry-inv π s iv eq
  with retryᴰ (ordsOf (res s)) (dfs (res s)) | great-retryᴰ (ordsOf (res s)) (dfs (res s)) (I5 (inv-R iv))
... | inj₁ _                 | _  = ⊥just eq
... | inj₂ (retriedL D' b f) | gr with eq
...   | refl = mkInv (inv-θ iv) (mkResInv (inv-ss r) (I1′ʳ r) (I1′ᵉ r) gr) , GV-id
  where
    r = inv-R iv

thenRetry-inv : ∀ {Θ₀ Θ} → (π : Subst Θ₀ Θ) → {s : St Θ} {C : Constraint Θ}
              → (x : Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C)))
              → (∀ {s₁ : St Θ} {m₁ : s ⟶ s₁} {w₁ : Wit s₁ C}
                   → x ≡ solved (s₁ , m₁ , w₁) → Inv π s₁ × GoodMove π m₁)
              → ∀ {s' : St Θ} {m : s ⟶ s'} {w : Wit s' C}
              → thenRetry {C = C} x ≡ solved (s' , m , w) → Inv π s' × GoodMove π m
thenRetry-inv π refuted p ()
thenRetry-inv π stuck   p ()
thenRetry-inv π {C = C} (solved (s₁ , m₁ , w₁)) p eq with retry s₁ in e
... | nothing = ⊥refuted eq
... | just (s₂ , m₂) with eq
...   | refl = proj₁ r₂ , goodMove-⨟ π m₁ m₂ (proj₂ (p refl)) (proj₂ r₂)
  where
    r₂ = retry-inv π s₁ (proj₁ (p refl)) e

-- Labelling an entry keeps its orderings

great-relabel : ∀ {Θ Ψ} {X : Subst Θ Ψ} → (op : Op) → (E : Dfr Ψ) → Great X E
              → Great X (relabel op E)
great-relabel op (dfr nothing  k o) g = mkGreat (greatʳ g) (greatᵉ g)
great-relabel op (dfr (just l) k o) g = mkGreat (greatʳ g) (greatᵉ g)

labelled-inv : ∀ {Θ₀ Θ} → (π : Subst Θ₀ Θ) → {s : St Θ} {C : Constraint Θ} → (op : Op)
             → (x : Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C)))
             → (∀ {s₁ : St Θ} {m₁ : s ⟶ s₁} {w₁ : Wit s₁ C}
                  → x ≡ solved (s₁ , m₁ , w₁) → Inv π s₁ × GoodMove π m₁)
             → ∀ {s' : St Θ} {m : s ⟶ s'} {w : Wit s' C}
             → labelled {C = C} op x ≡ solved (s' , m , w) → Inv π s' × GoodMove π m
labelled-inv π op refuted p ()
labelled-inv π op stuck   p ()
labelled-inv π op (solved (s₁ , m₁ , w₁)) p refl =
  mkInv (inv-θ i₁) (mkResInv (inv-ss r) (I1′ʳ r) (I1′ᵉ r) dfs') ,
  GV-≐ (≐ˢ-sym (⨟-idʳ (mδ m₁))) (proj₂ (p refl))
  where
    i₁ = proj₁ (p refl)
    r  = inv-R i₁

    dfs' : ∀ {E} → E ∈ map (relabel op) (dfs (res s₁)) → Great (π ⨟ˢ θ s₁) E
    dfs' m with ∈-map⁻ (relabel op) m
    ... | E₀ , m₀ , refl = great-relabel op E₀ (I5 r m₀)

threadOps-inv : ∀ {Θ₀ Θ} → (π : Subst Θ₀ Θ) → {f : Op → Constraint Θ}
   → (g : (s : St Θ) → (op : Op)
            → Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' (f op))))
   → ((s : St Θ) → (op : Op) → Inv π s → {s' : St Θ} {m : s ⟶ s'} {w : Wit s' (f op)}
        → g s op ≡ solved (s' , m , w) → Inv π s' × GoodMove π m)
   → (l : List Op) → (s : St Θ) → Inv π s
   → {s' : St Θ} {m : s ⟶ s'} {ws : AllOp (λ op → Wit s' (f op)) l}
   → threadOps {f = f} g l s ≡ solved (s' , m , ws)
   → Inv π s' × GoodMove π m
threadOps-inv π g gp []       s iv refl = iv , GV-id
threadOps-inv π {f = f} g gp (op ∷ l) s iv eq with g s op in e₁
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (s₁ , m₁ , w₁) with threadOps {f = f} g l s₁ in e₂
...   | refuted = ⊥refuted eq
...   | stuck   = ⊥stuck eq
...   | solved (s₂ , m₂ , ws) with eq
...     | refl = proj₁ ih₂ , goodMove-⨟ π m₁ m₂ (proj₂ ih₁) (proj₂ ih₂)
  where
    ih₁ = gp s op iv e₁
    ih₂ = threadOps-inv π g gp l s₁ (proj₁ ih₁) e₂

------------------------------------------------------------------------
-- The driver keeps the invariants, given the pending steps

module Driver (pend : Pending) where

  open Pending pend

  reexpand-inv : ∀ {Θ₀ Θ} → (π : Subst Θ₀ Θ) → (s : St Θ) → Inv π s
               → ∀ {s' : St Θ} {m : s ⟶ s'} → reexpand s ≡ just (s' , m)
               → Inv π s' × GoodMove π m
  reexpand-inv π s iv eq with expandSub (ss (res s)) in eqx
  ... | nothing = ⊥just eq
  ... | just (Ψ' , δ) with subsList (ss (res s [ δ ]ᴿ)) in eqs
  ...   | nothing = ⊥just eq
  ...   | just e with eq
  ...     | refl = mkInv (GV-⊆ inc (GV-⨟ {P = P₀} (inv-θ iv) g))
                         (resinv-⊆ inc (resinv-atomise (res s [ δ ]ᴿ) e
                                         (subsList-good (P₀ ⨟ˢ δ) (ss (res s [ δ ]ᴿ)) (inv-ss r₁) eqs) r₁)) ,
                   GV-⊆ inc g
    where
      P₀ = π ⨟ˢ θ s
      g : GV (P₀ ⨟ˢ δ) δ
      g = expandSub-good (ss (res s)) eqx
      r₁ = resinv-subst {P = P₀} g (inv-R iv)
      inc = ≐→⊆ᶠ (⨟-assoc π (θ s) δ)

  solve-inv : ∀ {Θ₀ Θ} → (π : Subst Θ₀ Θ) → (s : St Θ) → (C : Constraint Θ)
            → Inv π s → Shape π C
            → ∀ {s' : St Θ} {m : s ⟶ s'} {w : Wit s' C}
            → solve s C ≡ solved (s' , m , w) → Inv π s' × GoodMove π m

  solve-inv π s ⊤̂ iv sh refl = iv , GV-id

  solve-inv π s ⊥̂ iv sh ()

  solve-inv π s (C ∧̂ D) iv (sc , sd) eq with solve s C in e₁
  ... | refuted = ⊥refuted eq
  ... | stuck   = ⊥stuck eq
  ... | solved (s₁ , m₁ , w₁) with solve s₁ D in e₂
  ...   | refuted = ⊥refuted eq
  ...   | stuck   = ⊥stuck eq
  ...   | solved (s₂ , m₂ , w₂) with eq
  ...     | refl = proj₁ ih₂ , goodMove-⨟ π m₁ m₂ (proj₂ ih₁) (proj₂ ih₂)
    where
      ih₁ = solve-inv π s C iv sc e₁
      ih₂ = solve-inv π s₁ D (proj₁ ih₁) sd e₂

  solve-inv π s (A ≐ᵥ B) iv (gA , gB) eq
    with unify* (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ [])
  ... | nothing = ⊥refuted eq
  ... | just (Ψ⁺ , ρ , equ) with expandSub (ss (res s [ ⟦ ρ ⟧ᴬ ]ᴿ)) in eqx
  ...   | nothing = ⊥refuted eq
  ...   | just (Ψ' , δ) with subsList (ss (res s [ ⟦ ρ ⟧ᴬ ]ᴿ [ δ ]ᴿ)) in eqs
  ...     | nothing = ⊥refuted eq
  ...     | just e with eq
  ...       | refl = mkInv (GV-⊆ inc (GV-⨟ {P = P₀ ⨟ˢ ⟦ ρ ⟧ᴬ} (GV-⨟ {P = P₀} (inv-θ iv) g₁) g₂))
                           (resinv-⊆ inc r₃) ,
                     GV-⊆ inc (GV-⨟ {P = P₀ ⨟ˢ ⟦ ρ ⟧ᴬ} g₁ g₂)
    where
      P₀ = π ⨟ˢ θ s
      g₁ : GV (P₀ ⨟ˢ ⟦ ρ ⟧ᴬ) ⟦ ρ ⟧ᴬ
      g₁ = unify-good (rig s) (A [ θ s ]ᵛ) (B [ θ s ]ᵛ)
                      (tygoodᵛ-⨟ {P = π} (inv-θ iv) A gA) (tygoodᵛ-⨟ {P = π} (inv-θ iv) B gB) equ
      g₂ : GV ((P₀ ⨟ˢ ⟦ ρ ⟧ᴬ) ⨟ˢ δ) δ
      g₂ = expandSub-good (ss (res s [ ⟦ ρ ⟧ᴬ ]ᴿ)) eqx
      r₂ = resinv-subst {P = P₀ ⨟ˢ ⟦ ρ ⟧ᴬ} g₂ (resinv-subst {P = P₀} g₁ (inv-R iv))
      r₃ = resinv-atomise (res s [ ⟦ ρ ⟧ᴬ ]ᴿ [ δ ]ᴿ) e
             (subsList-good ((P₀ ⨟ˢ ⟦ ρ ⟧ᴬ) ⨟ˢ δ) (ss (res s [ ⟦ ρ ⟧ᴬ ]ᴿ [ δ ]ᴿ)) (inv-ss r₂) eqs) r₂
      inc = ≐→⊆ᶠ (≐ˢ-trans (⨟-congˡ (⨟-assoc π (θ s) ⟦ ρ ⟧ᴬ) δ)
                           (⨟-assoc π (θ s ⨟ˢ ⟦ ρ ⟧ᴬ) δ))

  solve-inv π s (A ≾̂ᵥᶜ B) iv (gA , gB) eq
    with expandSub ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) in eqx
  ... | nothing = ⊥refuted eq
  ... | just (Ψ' , δ) with subDec (A [ θ s ]ᵛ [ δ ]ᵛ) (B [ θ s ]ᵛ [ δ ]ᵛ) in eqd
  ...   | nothing = ⊥refuted eq
  ...   | just d  with subsList (ss (res s [ δ ]ᴿ)) in eqs
  ...     | nothing = ⊥refuted eq
  ...     | just e  with eq
  ...       | refl = mkInv (GV-⊆ inc (GV-⨟ {P = P₀} (inv-θ iv) g))
                           (resinv-⊆ inc (resinv-∪ r₂ (resinv-atoms (atomsOf d) ad))) ,
                     GV-⊆ inc g
    where
      P₀ = π ⨟ˢ θ s
      g : GV (P₀ ⨟ˢ δ) δ
      g = expandSub-good ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) eqx
      r₁ = resinv-subst {P = P₀} g (inv-R iv)
      r₂ = resinv-atomise (res s [ δ ]ᴿ) e (subsList-good (P₀ ⨟ˢ δ) (ss (res s [ δ ]ᴿ)) (inv-ss r₁) eqs) r₁
      tA = tygoodᵛ-⨟ {P = P₀} g (A [ θ s ]ᵛ) (tygoodᵛ-⨟ {P = π} (inv-θ iv) A gA)
      tB = tygoodᵛ-⨟ {P = P₀} g (B [ θ s ]ᵛ) (tygoodᵛ-⨟ {P = π} (inv-θ iv) B gB)
      ad = subDec-good (P₀ ⨟ˢ δ) (A [ θ s ]ᵛ [ δ ]ᵛ) (B [ θ s ]ᵛ [ δ ]ᵛ) tA tB eqd
      inc = ≐→⊆ᶠ (⨟-assoc π (θ s) δ)

  solve-inv π s (ρ ≾̂ᵣᶜ ρ') iv sh refl =
    mkInv (inv-θ iv) (resinv-pushʳ (goodᵣ-⨟ {P = π} (inv-θ iv) sh) (inv-R iv)) , GV-id

  solve-inv π s (ε ≾̂ₑᶜ ε') iv sh refl =
    mkInv (inv-θ iv) (resinv-pushᵉ (goodₑ-⨟ {P = π} (inv-θ iv) sh) (inv-R iv)) , GV-id

  solve-inv π s (Etᶜ A) iv sh refl = mkInv (inv-θ iv) (resinv-pushᵗ (inv-R iv)) , GV-id

  solve-inv π s (Et∨≾ᵘ A ρ) iv sh eq with decide≾ᵣ {Q = ∅ᴴ} (ρ [ θ s ]ʳ) ûᵣ
  ... | just p with eq
  ...   | refl = iv , GV-id
  solve-inv π s (Et∨≾ᵘ A ρ) iv sh eq | nothing with eq
  ... | refl = mkInv (inv-θ iv) (resinv-pushᵈ (inv-R iv)) , GV-id

  solve-inv {Θ = Θ} π s (∃ᵗ C) iv sh eq with solve (s ↑ᵗˢ) C in e
  ... | refuted = ⊥refuted eq
  ... | stuck   = ⊥stuck eq
  ... | solved (s'' , m'' , w'') with eq
  ...   | refl = mkInv (GV-⊆ inc (GV-wkᵗ⨟ (inv-θ i''))) (resinv-⊆ inc (inv-R i'')) ,
                 GV-⊆ inc (GV-wkᵗ⨟ (proj₂ ih))
    where
      ih  = solve-inv (π ⨟ˢ wkˢᵗ) (s ↑ᵗˢ) C (inv-↑ᵗ iv) sh e
      i'' = proj₁ ih
      inc = ≐→⊆ᶠ (⨟-assoc π (wkˢᵗ {Θ}) (θ s''))

  solve-inv {Θ = Θ} π s (∃ʳ C) iv sh eq with solve (s ↑ʳˢ) C in e
  ... | refuted = ⊥refuted eq
  ... | stuck   = ⊥stuck eq
  ... | solved (s'' , m'' , w'') with eq
  ...   | refl = mkInv (GV-⊆ inc (GV-wkʳ⨟ (inv-θ i''))) (resinv-⊆ inc (inv-R i'')) ,
                 GV-⊆ inc (GV-wkʳ⨟ (proj₂ ih))
    where
      ih  = solve-inv (π ⨟ˢ wkˢʳ) (s ↑ʳˢ) C (inv-↑ʳ iv) sh e
      i'' = proj₁ ih
      inc = ≐→⊆ᶠ (⨟-assoc π (wkˢʳ {Θ}) (θ s''))

  solve-inv {Θ = Θ} π s (∃ᵉ C) iv sh eq with solve (s ↑ᵉˢ) C in e
  ... | refuted = ⊥refuted eq
  ... | stuck   = ⊥stuck eq
  ... | solved (s'' , m'' , w'') with eq
  ...   | refl = mkInv (GV-⊆ inc (GV-wkᵉ⨟ (inv-θ i''))) (resinv-⊆ inc (inv-R i'')) ,
                 GV-⊆ inc (GV-wkᵉ⨟ (proj₂ ih))
    where
      ih  = solve-inv (π ⨟ˢ wkˢᵉ) (s ↑ᵉˢ) C (inv-↑ᵉ iv) sh e
      i'' = proj₁ ih
      inc = ≐→⊆ᶠ (⨟-assoc π (wkˢᵉ {Θ}) (θ s''))

  solve-inv π s (∀ᵉ C) iv sh eq with solve (⇑ᵉˢ s) C in e
  ... | refuted = ⊥refuted eq
  ... | stuck   = ⊥stuck eq
  ... | solved (s'' , m'' , w'') with reexpand s'' in e₃
  ...   | nothing = ⊥refuted eq
  ...   | just (s₃ , m₃) =
        thenRetry-inv π {C = ∀ᵉ C}
          (popᵉ s C (Ψ s₄) (θ s₄) (res s₄) (rig s₄) (⟶-⨟ m₃' mₗ)
                (wit-mono mₗ C (wit-mono m₃ C w'')))
          (popᵉ-inv π s C (Ψ s₄) (θ s₄) (res s₄) (rig s₄) (⟶-⨟ m₃' mₗ)
                    (wit-mono mₗ C (wit-mono m₃ C w'')) iv R₄ gm)
          eq
    where
      π⁺  = π ↑ᵉ
      ih  = solve-inv π⁺ (⇑ᵉˢ s) C (inv-⇑ iv) sh e
      ih₃ = reexpand-inv π⁺ s'' (proj₁ ih) e₃
      m₃' = ⟶-⨟ m'' m₃
      O   = mδ m₃'
      L   = localise O (res s₃)
      s₄  = proj₁ (localiseˢ s m₃')
      mₗ  = proj₂ (localiseˢ s m₃')

      -- the outer unknowns and the rigid move well up to the close
      g₃ : GV (π⁺ ⨟ˢ θ s₃) O
      g₃ = goodMove-⨟ π⁺ m'' m₃ (proj₂ ih) (proj₂ ih₃)

      -- localising leaves the images of those unknowns alone
      θ₄≐ : (θ s₃ ⨟ˢ lσ L) ≐ˢ θ s₃
      θ₄≐ = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₃')) (lσ L))
            (≐ˢ-trans (⨟-assoc (θ s ↑ᵉ) O (lσ L))
            (≐ˢ-trans (⨟-congʳ (θ s ↑ᵉ) (lfix L)) (mtri m₃')))

      P₄≐ : (π⁺ ⨟ˢ θ s₃) ≐ˢ (π⁺ ⨟ˢ θ s₄)
      P₄≐ = ⨟-congʳ π⁺ (≐ˢ-sym θ₄≐)

      -- the protected unknowns are among those the scope was entered with
      inO : (π⁺ ⨟ˢ θ s₃) ⊆ᶠ O
      inO = ⊆ᶠ-trans (≐→⊆ᶠ (⨟-congʳ π⁺ (≐ˢ-sym (mtri m₃'))))
            (⊆ᶠ-trans (≐→⊆ᶠ (≐ˢ-sym (⨟-assoc π⁺ (θ s ↑ᵉ) O)))
                      (⨟-⊆ᶠ (π⁺ ⨟ˢ (θ s ↑ᵉ)) O))

      R₄ : ResInv (π⁺ ⨟ˢ θ s₄) (res s₄)
      R₄ = resinv-⊆ (≐→⊆ᶠ P₄≐) (localise-good O (π⁺ ⨟ˢ θ s₃) (res s₃) inO (inv-R (proj₁ ih₃)))

      gm : GV (π⁺ ⨟ˢ θ s₄) (wkˢᵉ ⨟ˢ mδ (⟶-⨟ m₃' mₗ))
      gm = GV-⊆ (≐→⊆ᶠ P₄≐)
                (GV-≐ (⨟-congʳ wkˢᵉ (≐ˢ-sym (lfix L))) (GV-wkᵉ⨟ g₃))

  solve-inv π s (⋀ᵒᵖ f) iv sh eq
    with threadOps {f = f} (λ s' op → labelled {C = f op} op (solve s' (f op))) ops s in e
  ... | refuted = ⊥refuted eq
  ... | stuck   = ⊥stuck eq
  ... | solved (s₁ , m₁ , ws) with eq
  ...   | refl =
          threadOps-inv π (λ s' op → labelled {C = f op} op (solve s' (f op)))
            (λ s' op iv' e' → labelled-inv π op (solve s' (f op))
                                (λ e'' → solve-inv π s' (f op) iv' (sh op) e'') e')
            ops s iv e
