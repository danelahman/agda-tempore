------------------------------------------------------------------
-- The closure of the one-step localisation relation            --
--                                                              --
-- A declarative specification of localisation. A state of a    --
-- scope is its open unknowns, the local ones without a value   --
-- (`Open`), and its residual, kept in canonical form           --
-- (`canonᴿ`). A step (`Steps._⟶ˡ_`) is the collapse of the     --
-- cycles (`collapseˡ`), a value rule at one open unknown       --
-- (`valueᵉ`, `valueʳ`), the settling of the disjunctions       --
-- (`settleˡ`), or, where no other step applies (`Stuck`), the  --
-- raising of a set (`raiseˡ`), each followed by the canonical  --
-- form of the whole residual; every step keeps the contract    --
-- `Localised` (`Steps.step-loc`, `Steps.along`).               --
--                                                              --
-- A fixed selection (`Steps.select`: the collapse; the value   --
-- rules at the open effect unknowns, then the resource ones,   --
-- each sort least index first; the settling; the raising) with --
-- well-founded recursion on the number of open unknowns, then  --
-- of disjunctions (`Steps.decreases`), reaches an irreducible  --
-- state along a path of steps (`Steps.Closure`, `localiseᶜ`,   --
-- `localise`, `localise-ds`).                                  --
--                                                              --
-- The solver localises by the rounds of `SolverImpl.Localise`, --
-- not by this module.                                          --
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
open import Data.Maybe using (Is-just; is-just)
open import Data.Nat.Base using (ℕ; _+_; _≤_; _<_; z≤n; s≤s; s≤s⁻¹) renaming (zero to nzero; suc to nsuc)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; <-irrefl; m≤n⇒m≤1+n; ≮⇒≥; +-mono-≤; +-mono-<-≤; +-mono-≤-<; _<?_)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Induction.WellFounded using (Acc; acc)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (length)
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; fold; _◅_) renaming (ε to ε⋆)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Inference.SolverImpl.Localise.Closure
  (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S))
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import OpenCalculus.Syntax.Grades            S
open import OpenCalculus.Syntax.Types             S
open import OpenCalculus.Syntax.GradeSubstitution S
open import OpenCalculus.Hypotheses               S

open import OpenCalculus.Inference.SolverImpl.Core.Occurs S
  using (occᵉ-e; occᵉ-r; occᵉ-v; occᵉ-c; occʳ-r; occʳ-v; occʳ-c)
open import OpenCalculus.Inference.SolverImpl.Core.Rigid S
  using (∨-true; ∨-left; ∨-right; dec-true; true-dec)

open import OpenCalculus.Inference.SolverImpl.Deferred  S hints
  using (≾ˢ-↑ᵉⁿ; Dir; dir↓; dir↑; Still; stills?; keepᵈ; allOf; κ⟨_⟩; wk-κ; κ-wkᵛ; κ-wkʳ; κ-wkᵉ; ⊩ᴴ-κ)
open import OpenCalculus.Inference.SolverImpl.Resid  S
open import OpenCalculus.Inference.SolverImpl.Values S hints
  using (module Vᵉ; module Vʳ; module Vⁱ; isFalse; equal-keeps; updᵉ-e; updᵉ-r; updʳ-r;
         joinₑ; joinᵣ; joinₑ-ub⊩; joinₑ-lub⊩; joinᵣ-ub⊩; joinᵣ-lub⊩)
open import OpenCalculus.Inference.SolverImpl.Vars      S
  using (Vars; vᵉ; vʳ; Fixes; mkFixes; fvᵛ; fvʳ; fvᵉ; ⊆-refl; fix-v; fix-r; fix-e; ∨-inʳ)
import OpenCalculus.Inference.SolverImpl.Reach as Reachability
open import OpenCalculus.Inference.SolverImpl.Entail S hints using (decideᵣ; decideₑ; full)
open import OpenCalculus.Inference.SolverImpl.Canon  S hints
  using (canonᵣ; canonᵣ-≡; Ordʳ; Ordᵉ; Pieces; pieces; Split; splits; piecesʳ; piecesᵉ)
open import OpenCalculus.Inference.SolverImpl.Localise S hints
  hiding (Raised; raised; module Find; Collapse; collapsed; collapse; Mvᵉ; Mvʳ;
          module Cᵉ; module Cʳ; loc-normal; loc-settle; localise; localise-ds)

------------------------------------------------------------------------
-- Booleans and finite enumerations

isTrue : (b : 𝔹) → Maybe (b ≡ true)
isTrue true  = just refl
isTrue false = nothing

------------------------------------------------------------------------
-- A set of unknowns sent to the top at once

-- A member among those open (`oe`, `or`)

openᴹ : ∀ {Φ} → (EVar Φ → 𝔹) → (RVar Φ → 𝔹) → Mem Φ → 𝔹
openᴹ oe or (eᵐ k) = oe k
openᴹ oe or (rᵐ k) = or k

record Raised {Θ Φ} (O : Subst (Θ +e) Φ) (R : Resid Φ) (j : EVar Φ)
              (oe : EVar Φ → 𝔹) (or : RVar Φ → 𝔹) : Set where
  constructor raised
  field
    mems : List (Mem Φ)
    mrch : Reach R j mems
    mupe : ∀ {a} → a ∈ es R → UpAtₑ (wkˢᵉ {Θ} ⨟ˢ O) mems a
    mupr : ∀ {a} → a ∈ rs R → UpAtᵣ (wkˢᵉ {Θ} ⨟ˢ O) mems a
    mcln : CleanM mems R
    msti : ∀ {E} → E ∈ dfs R → Still dir↑ (tops mems) E
    mfix : freeᴹ mems O ≡ false
    mone : Σ[ m ∈ Mem Φ ] ((m ∈ mems) × (openᴹ oe or m ≡ true))

-- The candidates are the open unknowns (`oe₀`, `or₀`)

module Find {Θ Φ} (O : Subst (Θ +e) Φ) (R : Resid Φ) (j : EVar Φ)
            (oe₀ : EVar Φ → 𝔹) (or₀ : RVar Φ → 𝔹) where

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

  check : (l : List (Mem Φ)) → Reach R j l → Maybe (Raised O R j oe₀ or₀)
  check []      rc = nothing
  check (m ∷ l) rc with allOf (upAtₑ? O' (m ∷ l)) (es R) | allOf (upAtᵣ? O' (m ∷ l)) (rs R)
                      | cleanM? (m ∷ l) R | stills? dir↑ (tops (m ∷ l)) (dfs R)
                      | isFalse (freeᴹ (m ∷ l) O) | isTrue (openᴹ oe₀ or₀ m)
  ... | just ue | just ur | just cl | just sd | just fx | just op =
        just (raised (m ∷ l) rc ue ur cl sd fx (m , here refl , op))
  ... | _       | _       | _       | _       | _       | _       = nothing

  select : ℕ → (EVar Φ → 𝔹) → (RVar Φ → 𝔹) → Maybe (Raised O R j oe₀ or₀)
  select nzero    oe or = nothing
  select (nsuc n) oe or with grow oe or (nE Φ + nR Φ) [] reach[]
  ... | l , rc with check l rc
  ...   | just r  = just r
  ...   | nothing with anyᶠ (badᵉ l) ∨ anyᶠ (badʳ l)
  ...     | false = nothing
  ...     | true  = select n (λ k → oe k ∧ not (badᵉ l k)) (λ k → or k ∧ not (badʳ l k))

  raise? : Maybe (Raised O R j oe₀ or₀)
  raise? = select (nsuc (nE Φ + nR Φ)) oe₀ or₀

------------------------------------------------------------------------
-- The local unknowns without a value (open): each step gives a value
-- to at least one, and to none twice

-- The number of indices a test accepts

bit : 𝔹 → ℕ
bit true  = 1
bit false = 0

countᶠ : ∀ {n} → (Fin n → 𝔹) → ℕ
countᶠ {nzero}  f = 0
countᶠ {nsuc n} f = bit (f zero) + countᶠ (λ i → f (suc i))

bit-≤ : ∀ {a b} → (a ≡ true → b ≡ true) → bit a ≤ bit b
bit-≤ {false}         _ = z≤n
bit-≤ {true}  {true}  _ = ≤-refl
bit-≤ {true}  {false} h with h refl
... | ()

count-≤ : ∀ {n} → (f g : Fin n → 𝔹) → (∀ i → g i ≡ true → f i ≡ true) → countᶠ g ≤ countᶠ f
count-≤ {nzero}  f g h = z≤n
count-≤ {nsuc n} f g h =
  +-mono-≤ (bit-≤ (h zero)) (count-≤ (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))

count-< : ∀ {n} → (f g : Fin n → 𝔹) → (∀ i → g i ≡ true → f i ≡ true)
        → (k : Fin n) → f k ≡ true → g k ≡ false → countᶠ g < countᶠ f
count-< {nsuc n} f g h zero fk gk with f zero | g zero
count-< {nsuc n} f g h zero refl refl | true | false =
  +-mono-<-≤ ≤-refl (count-≤ (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)))
count-< {nsuc n} f g h (suc k) fk gk =
  +-mono-≤-< (bit-≤ (h zero)) (count-< (λ i → f (suc i)) (λ i → g (suc i)) (λ i → h (suc i)) k fk gk)

≟-refl : ∀ {n} → (k : Fin n) → ⌊ k ≟ᶠ k ⌋ ≡ true
≟-refl k with k ≟ᶠ k
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

∧-trueˡ : ∀ {a b} → a ∧ b ≡ true → a ≡ true
∧-trueˡ {true} _ = refl

∧-not : ∀ {a b} → a ≡ true → b ≡ true → a ∧ not b ≡ false
∧-not refl refl = refl

not-true : ∀ {b} → not b ≡ true → b ≡ false
not-true {false} _ = refl

record Open {Θ Φ} (O : Subst (Θ +e) Φ) : Set where
  constructor opened
  field
    oᵉ    : EVar Φ → 𝔹
    oʳ    : RVar Φ → 𝔹
    oᵉ-lc : ∀ k → oᵉ k ≡ true → freeᵉ k O ≡ false
    oʳ-lc : ∀ k → oʳ k ≡ true → freeʳ k O ≡ false

open Open public

module _ {Θ Φ} {O : Subst (Θ +e) Φ} where

  -- The number of open unknowns

  μᴼ : Open O → ℕ
  μᴼ P = countᶠ (oᵉ P) + countᶠ (oʳ P)

  -- The open unknowns less those two tests accept

  shut : Open O → (EVar Φ → 𝔹) → (RVar Φ → 𝔹) → Open O
  shut P ge gr = opened (λ k → oᵉ P k ∧ not (ge k)) (λ k → oʳ P k ∧ not (gr k))
                        (λ k q → oᵉ-lc P k (∧-trueˡ q)) (λ k q → oʳ-lc P k (∧-trueˡ q))

  shut-<ᵉ : (P : Open O) → (ge : EVar Φ → 𝔹) → (gr : RVar Φ → 𝔹) → (k : EVar Φ)
          → oᵉ P k ≡ true → ge k ≡ true → μᴼ (shut P ge gr) < μᴼ P
  shut-<ᵉ P ge gr k o g =
    +-mono-<-≤ (count-< (oᵉ P) _ (λ i → ∧-trueˡ) k o (∧-not o g))
               (count-≤ (oʳ P) _ (λ i → ∧-trueˡ))

  shut-<ʳ : (P : Open O) → (ge : EVar Φ → 𝔹) → (gr : RVar Φ → 𝔹) → (k : RVar Φ)
          → oʳ P k ≡ true → gr k ≡ true → μᴼ (shut P ge gr) < μᴼ P
  shut-<ʳ P ge gr k o g =
    +-mono-≤-< (count-≤ (oᵉ P) _ (λ i → ∧-trueˡ))
               (count-< (oʳ P) _ (λ i → ∧-trueˡ) k o (∧-not o g))

-- Every local unknown

allOpen : ∀ {Θ Φ} → (O : Subst (Θ +e) Φ) → Open O
allOpen O = opened (λ k → not (freeᵉ k O)) (λ k → not (freeʳ k O))
                   (λ k → not-true) (λ k → not-true)

------------------------------------------------------------------------
-- The local unknowns identified, of both sorts at once: `cσ` sends each
-- that may move, being open and absent from every type, to its
-- representative, and keeps every instance; the members moved are shut
-- (`cP`), and there is one where `cmove` holds

record Collapse {Θ Φ} (O : Subst (Θ +e) Φ) (P : Open O) (R : Resid Φ) : Set where
  constructor collapsed
  field
    cσ    : Subst Φ Φ
    cmove : 𝔹
    cP    : Open O
    cdec  : cmove ≡ true → μᴼ cP < μᴼ P
    cty   : ∀ α → sTy cσ α ≡ tvar α
    cfix  : (O ⨟ˢ cσ) ≐ˢ O
    ckeep : Keeps cσ R

open Collapse public

module _ {Θ Φ} (O : Subst (Θ +e) Φ) (P : Open O) (R : Resid Φ) where

  Mvᵉ : EVar Φ → Set
  Mvᵉ k = (oᵉ P k ≡ true) × Cleanᵉ k R

  Mvʳ : RVar Φ → Set
  Mvʳ k = (oʳ P k ≡ true) × Cleanʳ k R

  -- Each sort's components (`Reach`): outer unknowns preferred as
  -- representatives, the open ones absent from every type movable

  module Cᵉ = Reachability.Collapse (λ a b → (evar a , evar b) ∈ es R) sameᶠ? (edgesᵉ (es R))
                (bothEnds (edgesᵉ (es R))) _≟ᶠ_ (λ k → freeᵉ k O) Mvᵉ
                (λ k → both (isTrue (oᵉ P k)) (cleanᵉ? k R))
  module Cʳ = Reachability.Collapse (λ a b → (rvar a , rvar b) ∈ rs R) sameᶠ? (edgesʳ (rs R))
                (bothEnds (edgesʳ (rs R))) _≟ᶠ_ (λ k → freeʳ k O) Mvʳ
                (λ k → both (isTrue (oʳ P k)) (cleanʳ? k R))

  movedᵉ : Cᵉ.Moves → EVar Φ → 𝔹
  movedᵉ me k = is-just (Cᵉ.identOf me k)

  movedʳ : Cʳ.Moves → RVar Φ → 𝔹
  movedʳ mr k = is-just (Cʳ.identOf mr k)

  movedᵉ-hd : ∀ {k} (i : Cᵉ.Ident k) (me : Cᵉ.Moves) → movedᵉ ((k , i) ∷ me) k ≡ true
  movedᵉ-hd {k} i me with k ≟ᶠ k
  ... | yes refl = refl
  ... | no ne    = ⊥-elim (ne refl)

  movedʳ-hd : ∀ {k} (i : Cʳ.Ident k) (mr : Cʳ.Moves) → movedʳ ((k , i) ∷ mr) k ≡ true
  movedʳ-hd {k} i mr with k ≟ᶠ k
  ... | yes refl = refl
  ... | no ne    = ⊥-elim (ne refl)

  collapse : Collapse O P R
  collapse = from Cᵉ.moves Cʳ.moves
    where
      dec : (me : Cᵉ.Moves) → (mr : Cʳ.Moves) → nonempty me ∨ nonempty mr ≡ true
          → μᴼ (shut P (movedᵉ me) (movedʳ mr)) < μᴼ P
      dec ((k , i) ∷ me) mr _ =
        shut-<ᵉ P (movedᵉ ((k , i) ∷ me)) (movedʳ mr) k (proj₁ (Cᵉ.Ident.mv i)) (movedᵉ-hd i me)
      dec [] ((k , i) ∷ mr) _ =
        shut-<ʳ P (movedᵉ []) (movedʳ ((k , i) ∷ mr)) k (proj₁ (Cʳ.Ident.mv i)) (movedʳ-hd i mr)

      from : Cᵉ.Moves → Cʳ.Moves → Collapse O P R
      from me mr = collapsed σ (nonempty me ∨ nonempty mr) (shut P (movedᵉ me) (movedʳ mr))
                             (dec me mr) (λ α → refl) fixO keeps
        where
          σ : Subst Φ Φ
          σ = sub tvar (λ k → rvar (Cʳ.target mr k)) (λ k → evar (Cᵉ.target me k))

          -- a set of unknowns none that may move is in
          fixes : ∀ {W : Vars Φ} → (∀ k → Mvᵉ k → vᵉ W k ≡ false) → (∀ k → Mvʳ k → vʳ W k ≡ false)
                → Fixes W σ
          fixes fe fr =
            mkFixes (λ _ _ → refl)
                    (λ i o → [ cong rvar , (λ q → ⊥-elim (clash o (fr i q))) ]′ (Cʳ.stays mr i))
                    (λ i o → [ cong evar , (λ q → ⊥-elim (clash o (fe i q))) ]′ (Cᵉ.stays me i))

          lcᵉ : ∀ {k} → Mvᵉ k → freeᵉ k O ≡ false
          lcᵉ {k} q = oᵉ-lc P k (proj₁ q)

          lcʳ : ∀ {k} → Mvʳ k → freeʳ k O ≡ false
          lcʳ {k} q = oʳ-lc P k (proj₁ q)

          fixO : (O ⨟ˢ σ) ≐ˢ O
          fixO =
            mk≐ˢ (λ α → fix-v (fixes {fvᵛ (sTy O α)} (λ k q → proj₁ (localᵉ O (lcᵉ q)) α)
                                                     (λ k q → proj₁ (localʳ O (lcʳ q)) α))
                              (sTy O α) ⊆-refl)
                 (λ i → fix-r (fixes {fvʳ (sR O i)} (λ k q → proj₁ (proj₂ (localᵉ O (lcᵉ q))) i)
                                                    (λ k q → proj₂ (localʳ O (lcʳ q)) i))
                              (sR O i) ⊆-refl)
                 (λ i → fix-e (fixes {fvᵉ (sE O i)} (λ k q → proj₂ (proj₂ (localᵉ O (lcᵉ q))) i)
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
-- Canonical form: each atom written in normal form, an ordering with a
-- join of alternatives on its left made one ordering per alternative
-- (`normalᴿ`), then the orderings decided true from no hypotheses
-- dropped (`dropᴿ`). The instances are unchanged.

normalᴿ : ∀ {Ψ} → Resid Ψ → Resid Ψ
normalᴿ R = resid (Split.out (splits piecesʳ (rs R))) (Split.out (splits piecesᵉ (es R)))
                  (ts R) (ss R) (Split.out (splits piecesᵈ (ds R))) (dfs R)

dropᴿ : ∀ {Ψ} → Resid Ψ → Resid Ψ
dropᴿ R = record R { rs = Unsettled.kept (unsettled settledʳ (rs R))
                   ; es = Unsettled.kept (unsettled settledᵉ (es R)) }

canonᴿ : ∀ {Ψ} → Resid Ψ → Resid Ψ
canonᴿ R = dropᴿ (normalᴿ R)

loc-normal : ∀ {Θ Φ} {O : Subst (Θ +e) Φ} {R : Resid Φ} → Localised O R → Localised O R
loc-normal (loc σ R₀ fx sn cp la) =
  loc σ (normalᴿ R₀) fx
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

loc-drop : ∀ {Θ Φ} {O : Subst (Θ +e) Φ} {R : Resid Φ} → Localised O R → Localised O R
loc-drop (loc σ R₀ fx sn cp la) =
  loc σ (dropᴿ R₀) fx
      (λ δ Q h → sn δ Q (mk⊩ᴿ (Unsettled.back Uʳ δ (⊩rs h)) (Unsettled.back Uᵉ δ (⊩es h))
                              (⊩ts h) (⊩ss h) (⊩ds h) (⊩dfs h)))
      (λ τ en h → let h' = cp τ en h in
                 mk⊩ᴿ (λ m → ⊩rs h' (Unsettled.kept⊆ Uʳ m)) (λ m → ⊩es h' (Unsettled.kept⊆ Uᵉ m))
                      (⊩ts h') (⊩ss h') (⊩ds h') (⊩dfs h'))
      la
  where
    Uʳ = unsettled settledʳ (rs R₀)
    Uᵉ = unsettled settledᵉ (es R₀)

loc-canon : ∀ {Θ Φ} {O : Subst (Θ +e) Φ} {R : Resid Φ} → Localised O R → Localised O R
loc-canon L = loc-drop (loc-normal L)

-- Normal forms keep the number of disjunctions

normal-ds : ∀ {Ψ} → (l : List (OVType Ψ × RExp Ψ)) → length (Split.out (splits piecesᵈ l)) ≡ length l
normal-ds []      = refl
normal-ds (a ∷ l) = cong nsuc (normal-ds l)

------------------------------------------------------------------------
-- Settling the disjunctions: each whose grade is below the unit at the
-- strength `full` from the orderings, or whose type is eternal at every
-- instance, is dropped; each whose type is eternal at no instance
-- becomes its grade side, which is what it means at every instance
-- solving the scope from no hypotheses, the rigid a parameter

ordsᴴ : ∀ {Ψ} → Resid Ψ → Hyps Ψ
ordsᴴ R = hyps [] [] (rs R) (es R) [] []

settledOf : ∀ {Ψ} → (R : Resid Ψ) → Unsettled (Under (ordsᴴ R) Disj) (ds R)
settledOf R = unsettled (settledᵈ (ordsᴴ R)) (ds R)

refinedOf : ∀ {Ψ} → (R : Resid Ψ) → Refined (Unsettled.kept (settledOf R))
refinedOf R = refine (Unsettled.kept (settledOf R))

settleᴿ : ∀ {Ψ} → Resid Ψ → Resid Ψ
settleᴿ R = record R { rs = rs R ++ Refined.orders (refinedOf R) ; ds = Refined.rest (refinedOf R) }

-- Some disjunction is settled

Settles : ∀ {Ψ} → Resid Ψ → Set
Settles R = length (ds (settleᴿ R)) < length (ds R)

loc-settle : ∀ {Θ Φ} {O : Subst (Θ +e) Φ} {R : Resid Φ} → Localised O R → Localised O R
loc-settle (loc σ R₀ fx sn cp la) =
  loc σ (settleᴿ R₀) fx
      (λ δ Q h → sn δ Q (mk⊩ᴿ (λ m → ⊩rs h (∈-++⁺ˡ m)) (⊩es h) (⊩ts h) (⊩ss h)
                              (λ m → Unsettled.back Uᵈ δ
                                       (λ m' _ → Refined.back F δ (⊩ds h)
                                                   (λ m'' → ⊩rs h (∈-++⁺ʳ (rs R₀) m''))
                                                   m')
                                       m
                                       (mk⊩ᴴ (λ ()) (λ ()) (λ m' → ⊩rs h (∈-++⁺ˡ m')) (⊩es h) (λ ()) (λ ())))
                              (⊩dfs h)))
      (λ τ en h → let h' = cp τ en h in
                 mk⊩ᴿ (λ m → [ ⊩rs h' , Refined.fwd F τ (λ m' → ⊩ds h' (Unsettled.kept⊆ Uᵈ m')) ]′
                               (∈-++⁻ (rs R₀) m))
                      (⊩es h') (⊩ts h') (⊩ss h')
                      (λ m → ⊩ds h' (Unsettled.kept⊆ Uᵈ (Refined.rest⊆ F m)))
                      (⊩dfs h'))
      la
  where
    Uᵈ = settledOf R₀
    F  = refinedOf R₀

-- With no disjunction settled, the type of each is eternal at some
-- instance

unsettled-≤ : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set}
            → (set : (a : X) → Maybe (Every P a)) → (l : List X)
            → length (Unsettled.kept (unsettled set l)) ≤ length l
unsettled-≤ set []      = z≤n
unsettled-≤ set (a ∷ l) with set a
... | just _  = m≤n⇒m≤1+n (unsettled-≤ set l)
... | nothing = s≤s (unsettled-≤ set l)

unsettled-all : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set}
              → (set : (a : X) → Maybe (Every P a)) → (l : List X)
              → length l ≤ length (Unsettled.kept (unsettled set l))
              → ∀ {a} → a ∈ l → a ∈ Unsettled.kept (unsettled set l)
unsettled-all set (a ∷ l) h m with set a
... | just _  = ⊥-elim (<-irrefl refl (≤-trans h (unsettled-≤ set l)))
unsettled-all set (a ∷ l) h (here refl) | nothing = here refl
unsettled-all set (a ∷ l) h (there m)   | nothing = there (unsettled-all set l (s≤s⁻¹ h) m)

refine-≤ : ∀ {Ψ} → (l : List (OVType Ψ × RExp Ψ)) → length (Refined.rest (refine l)) ≤ length l
refine-≤ []            = z≤n
refine-≤ {Ψ} ((A , ρ) ∷ l) = go (etDec A) refl (refine l) (refine-≤ l)
  where
    go : (x : Maybe (List (TyVar Ψ))) → (e : etDec A ≡ x) → (F : Refined l)
       → length (Refined.rest F) ≤ length l → length (Refined.rest (consᴿ A ρ x e F)) ≤ nsuc (length l)
    go nothing   e (refined r _ _ _ _ _) le = m≤n⇒m≤1+n le
    go (just αs) e (refined r _ _ _ _ _) le = s≤s le

refine-all : ∀ {Ψ} → (l : List (OVType Ψ × RExp Ψ)) → length l ≤ length (Refined.rest (refine l))
           → ∀ {A ρ} → (A , ρ) ∈ l → Σ[ αs ∈ List (TyVar Ψ) ] (etDec A ≡ just αs)
refine-all {Ψ} ((A , ρ) ∷ l) = go (etDec A) refl (refine l) (refine-≤ l) (refine-all l)
  where
    go : (x : Maybe (List (TyVar Ψ))) → (e : etDec A ≡ x) → (F : Refined l)
       → length (Refined.rest F) ≤ length l
       → (length l ≤ length (Refined.rest F) → ∀ {A' ρ'} → (A' , ρ') ∈ l
          → Σ[ αs ∈ List (TyVar Ψ) ] (etDec A' ≡ just αs))
       → nsuc (length l) ≤ length (Refined.rest (consᴿ A ρ x e F))
       → ∀ {A' ρ'} → (A' , ρ') ∈ (A , ρ) ∷ l → Σ[ αs ∈ List (TyVar Ψ) ] (etDec A' ≡ just αs)
    go nothing   e (refined r _ _ _ _ _) le rec h m = ⊥-elim (<-irrefl refl (≤-trans h le))
    go (just αs) e (refined r _ _ _ _ _) le rec h (here refl) = αs , e
    go (just αs) e (refined r _ _ _ _ _) le rec h (there m)   = rec (s≤s⁻¹ h) m

settled-none : ∀ {Ψ} → (R : Resid Ψ) → ¬ Settles R
             → ∀ {A ρ} → (A , ρ) ∈ ds R → Σ[ αs ∈ List (TyVar Ψ) ] (etDec A ≡ just αs)
settled-none R ns m =
  refine-all K (≤-trans dk ds≤) (unsettled-all (settledᵈ (ordsᴴ R)) (ds R) (≤-trans ds≤ (refine-≤ K)) m)
  where
    K   = Unsettled.kept (settledOf R)
    dk  = unsettled-≤ (settledᵈ (ordsᴴ R)) (ds R)
    ds≤ = ≮⇒≥ ns

------------------------------------------------------------------------
-- The one-step relation on the states of a scope: the open unknowns
-- and the residual. A step is a value rule at one open unknown
-- (`valueᵉ`, `valueʳ`), the collapse of the cycles (`collapseˡ`), the
-- settling of the disjunctions (`settleˡ`), or, where no other step
-- applies, the raising of a set (`raiseˡ`); each is followed by the
-- canonical form of the whole residual.

-- The first index at which a partial function is defined, or none

searchᶠ : ∀ {n} {X : Fin n → Set} → (f : (i : Fin n) → Maybe (X i))
        → (Σ[ i ∈ Fin n ] Σ[ x ∈ X i ] (f i ≡ just x)) ⊎ (∀ i → f i ≡ nothing)
searchᶠ {nzero}  f = inj₂ (λ ())
searchᶠ {nsuc n} f with f zero in e
... | just x  = inj₁ (zero , x , e)
... | nothing with searchᶠ (λ i → f (suc i))
...   | inj₁ (i , x , e') = inj₁ (suc i , x , e')
...   | inj₂ g            = inj₂ (λ { zero → e ; (suc i) → g i })

gate : ∀ {X : Set} → 𝔹 → Maybe X → Maybe X
gate true  m = m
gate false _ = nothing

gate-just : ∀ {X : Set} {b} {m : Maybe X} {x} → gate b m ≡ just x → (b ≡ true) × (m ≡ just x)
gate-just {b = true} e = refl , e

gate-nothing : ∀ {X : Set} {b} {m : Maybe X} → gate b m ≡ nothing → b ≡ true → m ≡ nothing
gate-nothing e refl = e

just≢nothing : ∀ {X : Set} {x : X} {m : Maybe X} → m ≡ just x → m ≡ nothing → ⊥
just≢nothing refl ()

inᴱ-here : ∀ {Φ} {k : EVar Φ} (l : List (Mem Φ)) → eᵐ k ∈ l → inᴱ k l ≡ true
inᴱ-here {k = k} (eᵐ k' ∷ l) (here refl) rewrite ≟-refl k = refl
inᴱ-here {k = k} (eᵐ k' ∷ l) (there m) = ∨-inʳ ⌊ k ≟ᶠ k' ⌋ (inᴱ-here l m)
inᴱ-here (rᵐ _ ∷ l) (there m) = inᴱ-here l m

inᴿ-here : ∀ {Φ} {k : RVar Φ} (l : List (Mem Φ)) → rᵐ k ∈ l → inᴿ k l ≡ true
inᴿ-here {k = k} (rᵐ k' ∷ l) (here refl) rewrite ≟-refl k = refl
inᴿ-here {k = k} (rᵐ k' ∷ l) (there m) = ∨-inʳ ⌊ k ≟ᶠ k' ⌋ (inᴿ-here l m)
inᴿ-here (eᵐ _ ∷ l) (there m) = inᴿ-here l m

module Steps {Θ Φ} (O : Subst (Θ +e) Φ) where

  Cfg : Set
  Cfg = Open O × Resid Φ

  shutᵉ : Open O → EVar Φ → Open O
  shutᵉ P k = shut P (λ i → ⌊ i ≟ᶠ k ⌋) (λ _ → false)

  shutʳ : Open O → RVar Φ → Open O
  shutʳ P k = shut P (λ _ → false) (λ i → ⌊ i ≟ᶠ k ⌋)

  shutᴹ : Open O → List (Mem Φ) → Open O
  shutᴹ P l = shut P (λ k → inᴱ k l) (λ k → inᴿ k l)

  -- No value rule applies at an open unknown, no cycle collapses and no
  -- disjunction is settled

  record Stuck (P : Open O) (R : Resid Φ) : Set where
    constructor stuck
    field
      noᵉ : ∀ k → oᵉ P k ≡ true → stepᵉ k R ≡ nothing
      noʳ : ∀ k → oʳ P k ≡ true → stepʳ k R ≡ nothing
      noc : cmove (collapse O P R) ≡ false
      nod : ¬ Settles R

  infix 4 _⟶ˡ_

  data _⟶ˡ_ : Cfg → Cfg → Set where
    collapseˡ : ∀ {P R} → cmove (collapse O P R) ≡ true
              → (P , R) ⟶ˡ (cP (collapse O P R) , canonᴿ (R [ cσ (collapse O P R) ]ᴿ))
    valueᵉ    : ∀ {P R k b} {st : Keeps (updᵉ k b) R} {dr : Drops (updᵉ k b) R} → oᵉ P k ≡ true → stepᵉ k R ≡ just (b , st , dr)
              → (P , R) ⟶ˡ (shutᵉ P k , canonᴿ (left dr [ updᵉ k b ]ᴿ))
    valueʳ    : ∀ {P R k b} {st : Keeps (updʳ k b) R} {dr : Drops (updʳ k b) R} → oʳ P k ≡ true → stepʳ k R ≡ just (b , st , dr)
              → (P , R) ⟶ˡ (shutʳ P k , canonᴿ (left dr [ updʳ k b ]ᴿ))
    settleˡ   : ∀ {P R} → Settles R → (P , R) ⟶ˡ (P , canonᴿ (settleᴿ R))
    raiseˡ    : ∀ {P R j eqj r} → Stuck P R → evar? (sE O (newᵉ {Θ})) ≡ just (j , eqj)
              → Find.raise? O R j (oᵉ P) (oʳ P) ≡ just r
              → (P , R) ⟶ˡ (shutᴹ P (Raised.mems r) , canonᴿ (R [ tops (Raised.mems r) ]ᴿ))

  Irreducible : Cfg → Set
  Irreducible c = ∀ {c'} → ¬ (c ⟶ˡ c')

  -- The measure, ordered lexicographically: the open unknowns, then the
  -- disjunctions. Every step but the settling shuts an open unknown;
  -- the settling keeps them and drops or refines a disjunction.

  μ : Cfg → ℕ
  μ (P , _) = μᴼ P

  ν : Cfg → ℕ
  ν (_ , R) = length (ds R)

  settle-ν : (R : Resid Φ) → Settles R → length (ds (canonᴿ (settleᴿ R))) < length (ds R)
  settle-ν R s = subst (_< length (ds R)) (sym (normal-ds (ds (settleᴿ R)))) s

  Shuts : ∀ {c c'} → c ⟶ˡ c' → Set
  Shuts (settleˡ _) = ⊥
  Shuts _           = ⊤

  shut-μ : ∀ {c c'} → (s : c ⟶ˡ c') → Shuts s → μ c' < μ c
  shut-μ {P , R} (collapseˡ e)        _ = cdec (collapse O P R) e
  shut-μ {P , R} (valueᵉ {k = k} o _) _ = shut-<ᵉ P _ _ k o (≟-refl k)
  shut-μ {P , R} (valueʳ {k = k} o _) _ = shut-<ʳ P _ _ k o (≟-refl k)
  shut-μ {P , R} (raiseˡ {r = r} _ _ _) _ with Raised.mone r
  ... | eᵐ k , m , op = shut-<ᵉ P _ _ k op (inᴱ-here (Raised.mems r) m)
  ... | rᵐ k , m , op = shut-<ʳ P _ _ k op (inᴿ-here (Raised.mems r) m)

  decreases : ∀ {c c'} → c ⟶ˡ c' → (μ c' < μ c) ⊎ ((μ c' ≡ μ c) × (ν c' < ν c))
  decreases (settleˡ {R = R} s) = inj₂ (refl , settle-ν R s)
  decreases s@(collapseˡ _)    = inj₁ (shut-μ s tt)
  decreases s@(valueᵉ _ _)     = inj₁ (shut-μ s tt)
  decreases s@(valueʳ _ _)     = inj₁ (shut-μ s tt)
  decreases s@(raiseˡ _ _ _)   = inj₁ (shut-μ s tt)

  -- Each step preserves the contract

  LocAt : Resid Φ → Resid Φ → Set
  LocAt R₀ R = Σ[ L ∈ Localised O R₀ ] (lR L ≡ R)

  step-loc : ∀ {R₀ c c'} → LocAt R₀ (proj₂ c) → c ⟶ˡ c' → LocAt R₀ (proj₂ c')
  step-loc {c = P , _} (L , refl) (collapseˡ _) =
    loc-canon (loc-ext L (cσ C) (cfix C) (λ τ en → ckeep C τ ∅ᴴ) keepAll (cty C)) , refl
    where C = collapse O P (lR L)
  step-loc {c = P , _} (L , refl) (valueᵉ {k = k} {b} {st} {dr} o _) =
    loc-canon (loc-ext L (updᵉ k b) (freeᵉ-fix k O (oᵉ-lc P k o) b) (λ τ en → st τ ∅ᴴ) dr (λ α → refl)) ,
    refl
  step-loc {c = P , _} (L , refl) (valueʳ {k = k} {b} {st} {dr} o _) =
    loc-canon (loc-ext L (updʳ k b) (freeʳ-fix k O (oʳ-lc P k o) b) (λ τ en → st τ ∅ᴴ) dr (λ α → refl)) ,
    refl
  step-loc (L , refl) (settleˡ _) = loc-canon (loc-settle L) , refl
  step-loc (L , refl) (raiseˡ {eqj = eqj} {r = raised l rc ue ur cl sd fx _} _ _ _) =
    loc-canon (loc-ext L (tops l) (freeᴹ-fix l O fx)
                       (λ τ en h → raise-⊩ {Q₀ = ∅ᴴ} O eqj l rc ue ur cl sd τ en h)
                       keepAll (λ α → refl)) ,
    refl

  along : ∀ {R₀ c c'} → LocAt R₀ (proj₂ c) → Star _⟶ˡ_ c c' → LocAt R₀ (proj₂ c')
  along L ε⋆       = L
  along L (s ◅ ss) = along (step-loc L s) ss

  -- The fixed selection: the collapse; the value rules at the open
  -- effect unknowns, then the resource ones, each sort latest created
  -- (least index) first; the settling; the raising

  select : (c : Cfg) → (Σ[ c' ∈ Cfg ] (c ⟶ˡ c')) ⊎ Irreducible c
  select (P , R) with cmove (collapse O P R) in ec
  ... | true  = inj₁ (_ , collapseˡ ec)
  ... | false with searchᶠ (λ k → gate (oᵉ P k) (stepᵉ k R))
  ...   | inj₁ (k , _ , e) = inj₁ (_ , valueᵉ (proj₁ (gate-just e)) (proj₂ (gate-just e)))
  ...   | inj₂ nᵉ with searchᶠ (λ k → gate (oʳ P k) (stepʳ k R))
  ...     | inj₁ (k , _ , e) = inj₁ (_ , valueʳ (proj₁ (gate-just e)) (proj₂ (gate-just e)))
  ...     | inj₂ nʳ with length (ds (settleᴿ R)) <? length (ds R)
  ...       | yes s = inj₁ (_ , settleˡ s)
  ...       | no ns with evar? (sE O (newᵉ {Θ})) in ej
  ...         | nothing = inj₂ irr
    where
      irr : ∀ {c'} → ¬ ((P , R) ⟶ˡ c')
      irr (collapseˡ e)  = clash e ec
      irr (valueᵉ o e)   = just≢nothing e (gate-nothing (nᵉ _) o)
      irr (valueʳ o e)   = just≢nothing e (gate-nothing (nʳ _) o)
      irr (settleˡ s)    = ns s
      irr (raiseˡ _ e _) = just≢nothing e ej
  ...         | just (j , eqj) with Find.raise? O R j (oᵉ P) (oʳ P) in er
  ...           | just r  = inj₁ (_ , raiseˡ st ej er)
    where
      st : Stuck P R
      st = stuck (λ k o → gate-nothing (nᵉ k) o) (λ k o → gate-nothing (nʳ k) o) ec ns
  ...           | nothing = inj₂ irr
    where
      irr : ∀ {c'} → ¬ ((P , R) ⟶ˡ c')
      irr (collapseˡ e)   = clash e ec
      irr (valueᵉ o e)    = just≢nothing e (gate-nothing (nᵉ _) o)
      irr (valueʳ o e)    = just≢nothing e (gate-nothing (nʳ _) o)
      irr (settleˡ s)     = ns s
      irr (raiseˡ _ e e') with trans (sym ej) e
      ... | refl = just≢nothing e' er

  -- Localisation by well-founded recursion on the measure

  record Closure (c₀ : Cfg) : Set where
    constructor closure
    field
      final : Cfg
      path  : Star _⟶ˡ_ c₀ final
      irred : Irreducible final

  _◅ᶜ_ : ∀ {c c'} → c ⟶ˡ c' → Closure c' → Closure c
  s ◅ᶜ closure f p i = closure f (s ◅ p) i

  run : (c : Cfg) → Acc _<_ (μ c) → Acc _<_ (ν c) → Closure c
  run c aμ aν with select c
  run c aμ aν | inj₂ irr = closure c ε⋆ irr
  run (P , R) aμ (acc rν) | inj₁ (_ , s@(settleˡ x)) = s ◅ᶜ run _ aμ (rν (settle-ν R x))
  run c (acc rμ) aν | inj₁ (c' , s@(collapseˡ _))  = s ◅ᶜ run c' (rμ (shut-μ s tt)) (<-wellFounded-fast _)
  run c (acc rμ) aν | inj₁ (c' , s@(valueᵉ _ _))   = s ◅ᶜ run c' (rμ (shut-μ s tt)) (<-wellFounded-fast _)
  run c (acc rμ) aν | inj₁ (c' , s@(valueʳ _ _))   = s ◅ᶜ run c' (rμ (shut-μ s tt)) (<-wellFounded-fast _)
  run c (acc rμ) aν | inj₁ (c' , s@(raiseˡ _ _ _)) = s ◅ᶜ run c' (rμ (shut-μ s tt)) (<-wellFounded-fast _)

  -- The initial state: every local unknown open, the residual in
  -- canonical form

  initial : Resid Φ → Cfg
  initial R = allOpen O , canonᴿ R

  closureOf : (R : Resid Φ) → Closure (initial R)
  closureOf R = from (μ (initial R)) refl
    where
      -- by cases on the measure first: at a scope of unknown size the
      -- closure does not unfold
      from : (n : ℕ) → μ (initial R) ≡ n → Closure (initial R)
      from nzero    _ = run (initial R) (<-wellFounded-fast _) (<-wellFounded-fast _)
      from (nsuc _) _ = run (initial R) (<-wellFounded-fast _) (<-wellFounded-fast _)

-- Localisation: the irreducible state the fixed selection reaches, the
-- images of `O` read from `memo O`

localiseᶜ : ∀ {Θ Φ} → (O : Subst (Θ +e) Φ) → (R : Resid Φ) → Steps.Closure (memo O) (Steps.initial (memo O) R)
localiseᶜ O R = Steps.closureOf (memo O) R

localiseᴸ : ∀ {Θ Φ} → (O : Subst (Θ +e) Φ) → (R : Resid Φ)
          → Steps.LocAt (memo O) R (proj₂ (Steps.Closure.final (localiseᶜ O R)))
localiseᴸ O R = Steps.along (memo O) (loc-canon loc-id , refl) (Steps.Closure.path (localiseᶜ O R))

localise : ∀ {Θ Φ} → (O : Subst (Θ +e) Φ) → (R : Resid Φ) → Localised O R
localise O R = loc-≐ (memo-≐ O) (proj₁ (localiseᴸ O R))

-- After localisation, the type of each disjunction left is eternal at
-- some instance: the state is irreducible, so no disjunction settles

localise-ds : ∀ {Θ Φ} → (O : Subst (Θ +e) Φ) → (R : Resid Φ)
            → ∀ {A ρ} → (A , ρ) ∈ ds (lR (localise O R))
            → Σ[ αs ∈ List (TyVar Φ) ] (etDec A ≡ just αs)
localise-ds O R m with localiseᶜ O R | localiseᴸ O R
... | Steps.closure (P , R') p irr | L , e =
      settled-none R' (λ s → irr (Steps.settleˡ s)) (subst (λ X → _ ∈ ds X) e m)

