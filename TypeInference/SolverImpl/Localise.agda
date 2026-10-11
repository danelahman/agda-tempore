------------------------------------------------------------------
-- Values for the unknowns local to a rigid scope               --
--                                                              --
-- An unknown is local to a scope when it is free in the image  --
-- of none of the unknowns the scope was entered with; the      --
-- rigid is one of those, so it is never local and never        --
-- assigned.                                                    --
--                                                              --
-- Localisation is a closure under a one-step relation          --
-- (`Steps._⟶ˡ_`) on states: the open unknowns, the local ones  --
-- without a value (`Open`), and the residual. The residual is  --
-- kept in canonical form (`canonᴿ`): each side of an ordering  --
-- and each disjunction's grade written canonically, so no unit --
-- factor or bracketing hides a whole side, an ordering whose   --
-- left side has two or more alternatives made one ordering per --
-- alternative, the join being the least upper bound, a right   --
-- side never split (`normalᴿ`); the orderings decided true     --
-- against no hypotheses dropped (`dropᴿ`). A step is one of    --
-- the following, followed by the canonical form of the whole   --
-- residual:                                                    --
--   * collapse (`collapseˡ`): each strongly connected          --
--     component of the orderings whose sides are whole         --
--     unknowns is one unknown (`Reach`'s `Collapse`): each     --
--     open member absent from every type is sent to the        --
--     representative, an outer member where there is one, else --
--     one that may not move, else the least, each by index,    --
--     all at once (`collapse`). The members are equal at every --
--     instance (`equal`), so the instance is kept (`equal-⊩`); --
--     a member sent occurs in no type.                         --
--   * a value (`valueᵉ`, `valueʳ`): an open unknown is sent to --
--     the value of the first of four rules of `Values` that    --
--     applies, under an oracle (`oracleᵉ`, `oracleʳ`) that     --
--     keeps the orderings of the other sort and the deferred   --
--     conditions:                                              --
--       - the join of its lower bounds, where it occurs on a   --
--         right side only as the whole side (Pottier's         --
--         condition); each ordering with it on the greater     --
--         side is dropped, being a bound, below the join, or   --
--         valid (`lower-drops`);                               --
--       - dually, the first upper bound decided (from no       --
--         hypotheses) below each of its others, where it       --
--         occurs on a left side only as the whole side;        --
--       - the unit, where it has no bound below and the unit   --
--         is least, the unit being then the join of no bounds; --
--       - the top, where it occurs on no left side.            --
--     An ordering valid at every instance bounds it on neither --
--     side. In every case it occurs in no type of the          --
--     residual. The grade of a disjunction is the left side of --
--     an ordering below the unit: the first and third rules    --
--     keep it, the others ask it to be free of the unknown. A  --
--     value may mention the rigid, so the value over the rigid --
--     is one expression, uniform in it.                        --
--   * settling (`settleˡ`): a var-rule disjunction whose grade --
--     is below the unit at the strength `full` from the        --
--     orderings, or whose type is eternal at every instance,   --
--     is dropped; one whose type is eternal at no instance     --
--     becomes its grade side, which is what it means at every  --
--     instance solving the scope from no hypotheses, the rigid --
--     a parameter (`settleᴿ`). At least one disjunction is     --
--     settled (`Settles`).                                     --
--   * raising (`raiseˡ`), where no other step applies          --
--     (`Stuck`): a set of open unknowns is sent to the top at  --
--     once. Each member is reached from the rigid: it is       --
--     bounded below by an expression decided to be the top     --
--     once the rigid and the members reached before it are.    --
--     Each ordering with a member on its left has on its right --
--     an expression decided to be the top once the members     --
--     are, or one that mentions only outer unknowns other than --
--     the rigid. No member occurs in a type or in a            --
--     disjunction's grade.                                     --
-- An unknown given a value is shut.                            --
--                                                              --
-- In the deferred conditions of inner scopes, an unknown may   --
-- be lowered where it is on no greater side, and raised where  --
-- it is on no smaller side: a lower smaller side or a higher   --
-- greater side keeps a condition. It occurs where it is in     --
-- one.                                                         --
--                                                              --
-- Selection (`Steps.select`) is fixed: the collapse; the value --
-- rules at the open effect unknowns, then at the resource      --
-- ones, each sort latest created (least index) first; the      --
-- settling; the raising. `localise` starts from every local    --
-- unknown open and the residual in canonical form              --
-- (`Steps.initial`) and recurses well-foundedly on the number  --
-- of open unknowns, then the number of disjunctions,           --
-- lexicographically (`Steps.decreases`): every step but the    --
-- settling shuts an open unknown, and the settling keeps them  --
-- and removes a disjunction. It reaches an irreducible state   --
-- along a path of steps (`Steps.Closure`, `localiseᶜ`).        --
--                                                              --
-- Contract (`Localised`), kept by every step (`Steps.step-loc`,--
-- `Steps.along`). `lσ` fixes the images of the outer unknowns  --
-- (`lfix`); a discharge of the new residual along `δ` is one   --
-- of the old along `lσ ⨟ δ` (`lsnd`); an instance entering the --
-- scope that discharges the old residual from no hypotheses    --
-- discharges the new one (`lcpl`); each step assigns grade     --
-- unknowns only, so subtyping demands between type variables   --
-- stay so (`latom`); the type of each disjunction left is      --
-- eternal at some instance, no disjunction settling at an      --
-- irreducible state (`localise-ds`). A step leaves the         --
-- residual moved by its assignment, less the orderings the     --
-- assignment settles: they hold at every instance once it is   --
-- made (`Drops`, `loc-ext`).                                   --
--                                                              --
-- Every grade former is monotone, so each value keeps every    --
-- instance that satisfied the residual (`lowerᵉ-⊩` and its     --
-- five siblings), and so does identifying the components       --
-- (`equal-⊩`); the orderings of the sorts assigned are kept by --
-- the rules of `Values` (`lower-keeps`, `raise-keeps`,         --
-- `raise-free`, `equal-keeps`), which also classify them       --
-- (`lowsOf`, `upsOf`). Raising a set keeps every               --
-- instance entering the scope, one that takes the rigid to a   --
-- fresh eigenvariable (`raise-⊩`): with the eigenvariable at   --
-- the top as well, the instance stays one and every member is  --
-- at the top, and the raised instance lies between the two.    --
--                                                              --
-- The lowering and unit values are principal: at every         --
-- instance of the residual they lie below the unknown          --
-- (`lowerᵉ-least`, `lowerʳ-least`, `minₑ`, `minᵣ`). The raise  --
-- and top values, and a raised set, only keep every instance;  --
-- that they are least is not claimed.                          --
--                                                              --
-- A local unknown no step gives a value leaves the scope       --
-- stuck. Known cases: a cycle through a compound side that     --
-- mentions the rigid `j` and an outer unknown `c`, such as     --
-- `j · a ≾ a ≾ c · j` (right-sided time) or `j ≾ a ≾ c · a`    --
-- (left-sided time), where with `c` local, or with no rigid,   --
-- the steps resolve it, and a cycle whose sides are whole      --
-- unknowns is collapsed (`Cycle` in `Examples/Stages`); an     --
-- outer scope's local unknown on both sides of an inner        --
-- scope's deferred condition; a local unknown with no lower    --
-- bound under several upper bounds, none decided below the     --
-- others, which in a program comes only from `absurd`.         --
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
open import TypeInference.SolverImpl.Values    S
  using (module Vᵉ; module Vʳ; module Vⁱ; isFalse; equal-keeps; updᵉ-e; updᵉ-r; updʳ-r;
         joinₑ; joinᵣ; joinₑ-ub⊩; joinₑ-lub⊩; joinᵣ-ub⊩; joinᵣ-lub⊩)
open import TypeInference.SolverImpl.Vars      S
  using (Vars; vᵉ; vʳ; Fixes; mkFixes; fvᵛ; fvʳ; fvᵉ; ⊆-refl; fix-v; fix-r; fix-e; ∨-inʳ)
import TypeInference.SolverImpl.Reach as Reachability
open import TypeInference.SolverImpl.Entail    S using (decideᵣ; decideₑ; full)
open import TypeInference.SolverImpl.Canon     S
  using (canonᵣ; canonᵣ-≡; Ordʳ; Ordᵉ; Pieces; pieces; Split; splits; piecesʳ; piecesᵉ)

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

isTrue : (b : 𝔹) → Maybe (b ≡ true)
isTrue true  = just refl
isTrue false = nothing

------------------------------------------------------------------------
-- An assignment leaves alone what the assigned unknown does not occur in

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

-- A variable, with the equation that names it

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

allFalse : ∀ {Y : Set} → (f : Y → 𝔹) → (l : List Y) → Maybe (∀ {y} → y ∈ l → f y ≡ false)
allFalse f []      = just (λ ())
allFalse f (y ∷ l) with isFalse (f y) | allFalse f l
... | just q  | just g  = just (λ { (here refl) → q ; (there m) → g m })
... | just _  | nothing = nothing
... | nothing | _       = nothing

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

-- A resource assignment leaves every effect ordering as it was

effects-fixed : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} → (k : RVar Ψ) → (b : RExp Ψ)
              → (τ : Subst Ψ Ψ') → Q ⊩ᴿ R [ τ ]
              → ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ updʳ k b ⨟ˢ τ ]ᵉ ≾̂ₑ ε' [ updʳ k b ⨟ˢ τ ]ᵉ
effects-fixed {Q = Q} k b τ h {ε} {ε'} m =
  subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym (updʳ-⨟e k b τ ε)) (sym (updʳ-⨟e k b τ ε')) (⊩es h m)

-- The orderings of either sort read at an instance, before and after an
-- assignment (`Values`)

module Atᵉ {Ψ Ψ'} (Q : Hyps Ψ') (k : EVar Ψ) (b : EExp Ψ) (τ : Subst Ψ Ψ') where
  open Vᵉ.Keep {Ψ} k (Q ⊩_≾̂ₑ_) ⊩≾̂ₑ-refl transₑ (_[ τ ]ᵉ) (_[ updᵉ k b ⨟ˢ τ ]ᵉ)
               (λ {x} → updᵉ-⨟e k b τ x) (λ p → ⊩-substₑ ∅ᴴ-⊩ᴴ p) public
  module R = Vⁱ.Keep {Ψ} k (Q ⊩_≾̂ᵣ_) ⊩≾̂ᵣ-refl transᵣ (_[ τ ]ʳ) (_[ updᵉ k b ⨟ˢ τ ]ʳ)
                      (λ {x} → updᵉ-⨟r k b τ x) (λ p → ⊩-substᵣ ∅ᴴ-⊩ᴴ p)

module Atʳ {Ψ Ψ'} (Q : Hyps Ψ') (k : RVar Ψ) (b : RExp Ψ) (τ : Subst Ψ Ψ') where
  open Vʳ.Keep {Ψ} k (Q ⊩_≾̂ᵣ_) ⊩≾̂ᵣ-refl transᵣ (_[ τ ]ʳ) (_[ updʳ k b ⨟ˢ τ ]ʳ)
               (λ {x} → updʳ-⨟r k b τ x) (λ p → ⊩-substᵣ ∅ᴴ-⊩ᴴ p) public

-- Lowering an effect unknown below its value, to a bound above each of
-- its lower bounds

lowerᵉ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : EVar Ψ} {R : Resid Ψ}
         → (lw : Vᵉ.Lows {Ψ} k (es R))
         → (∀ {a} → a ∈ rs R → Vⁱ.FreeR {Ψ} k a)
         → Cleanᵉ k R
         → (b : EExp Ψ) → (∀ {E} → E ∈ dfs R → Still dir↓ (updᵉ k b) E)
         → (τ : Subst Ψ Ψ')
         → Q ⊩ b [ τ ]ᵉ ≾̂ₑ sE τ k
         → (∀ {x} → x ∈ Vᵉ.bnds lw → Q ⊩ x [ τ ]ᵉ ≾̂ₑ b [ τ ]ᵉ)
         → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updᵉ k b ⨟ˢ τ ]
lowerᵉ-⊩ {Q = Q} {k} {R} lw fr cl b sd τ below ub h =
  mk⊩ᴿ (Atᵉ.R.lower-free Q k b τ fr (mono-substᵣ le) (⊩rs h))
       (Atᵉ.lower-keeps Q k b τ lw (mono-substₑ le)
          (λ {x} mx → subst (λ z → Q ⊩ x [ τ ]ᵉ ≾̂ₑ z [ τ ]ᵉ) (sym (updᵉ-hit k b)) (ub mx))
          (⊩es h))
       (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↓ E (sd m) le (⊩dfs h m))
  where
    le : Q ⊩ (updᵉ k b ⨟ˢ τ) ≾ˢ τ
    le = updᵉ-below k b τ below

    c = cleanᵉ-⊩ cl b τ h (λ {A} {ρ} m → mono-substᵣ le ρ)

-- Raising an effect unknown to its upper bound below the others

raiseᵉ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : EVar Ψ} {R : Resid Ψ}
         → (up : Vᵉ.Ups {Ψ} k (es R))
         → (∀ {a} → a ∈ rs R → Vⁱ.FreeL {Ψ} k a)
         → Cleanᵉ k R → DFreeᵉ k R
         → (∀ {E} → E ∈ dfs R → Still dir↑ (updᵉ k (Vᵉ.cap up)) E)
         → (τ : Subst Ψ Ψ')
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

lowerʳ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : RVar Ψ} {R : Resid Ψ}
         → (lw : Vʳ.Lows {Ψ} k (rs R))
         → Cleanʳ k R
         → (b : RExp Ψ) → (∀ {E} → E ∈ dfs R → Still dir↓ (updʳ k b) E)
         → (τ : Subst Ψ Ψ')
         → Q ⊩ b [ τ ]ʳ ≾̂ᵣ sR τ k
         → (∀ {x} → x ∈ Vʳ.bnds lw → Q ⊩ x [ τ ]ʳ ≾̂ᵣ b [ τ ]ʳ)
         → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updʳ k b ⨟ˢ τ ]
lowerʳ-⊩ {Q = Q} {k} {R} lw cl b sd τ below ub h =
  mk⊩ᴿ (Atʳ.lower-keeps Q k b τ lw (mono-substᵣ le)
          (λ {x} mx → subst (λ z → Q ⊩ x [ τ ]ʳ ≾̂ᵣ z [ τ ]ʳ) (sym (updʳ-hit k b)) (ub mx))
          (⊩rs h))
       (effects-fixed k b τ h)
       (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↓ E (sd m) le (⊩dfs h m))
  where
    le : Q ⊩ (updʳ k b ⨟ˢ τ) ≾ˢ τ
    le = updʳ-below k b τ below

    c = cleanʳ-⊩ cl b τ h (λ {A} {ρ} m → mono-substᵣ le ρ)

raiseʳ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : RVar Ψ} {R : Resid Ψ}
         → (up : Vʳ.Ups {Ψ} k (rs R))
         → Cleanʳ k R → DFreeʳ k R
         → (∀ {E} → E ∈ dfs R → Still dir↑ (updʳ k (Vʳ.cap up)) E)
         → (τ : Subst Ψ Ψ')
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

topᵉ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : EVar Ψ} {R : Resid Ψ}
       → (∀ {a} → a ∈ es R → Vᵉ.FreeL {Ψ} k a)
       → (∀ {a} → a ∈ rs R → Vⁱ.FreeL {Ψ} k a)
       → Cleanᵉ k R → DFreeᵉ k R
       → (∀ {E} → E ∈ dfs R → Still dir↑ (updᵉ k (econst ⊤ₑ)) E)
       → (τ : Subst Ψ Ψ')
       → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updᵉ k (econst ⊤ₑ) ⨟ˢ τ ]
topᵉ-⊩ {Q = Q} {k} {R} fe fl cl df sd τ h =
  mk⊩ᴿ (Atᵉ.R.raise-free Q k (econst ⊤ₑ) τ fl (mono-substᵣ ge) (⊩rs h))
       (Atᵉ.raise-free Q k (econst ⊤ₑ) τ fe (mono-substₑ ge) (⊩es h))
       (proj₁ c) (proj₁ (proj₂ c)) (proj₂ (proj₂ c))
       (λ {E} m → keepᵈ dir↑ E (sd m) ge (⊩dfs h m))
  where
    ge : Q ⊩ τ ≾ˢ (updᵉ k (econst ⊤ₑ) ⨟ˢ τ)
    ge = updᵉ-above k (econst ⊤ₑ) τ topₑ

    c = cleanᵉ-⊩ cl (econst ⊤ₑ) τ h
          (λ {A} {ρ} m → subst (λ x → Q ⊩ x ≾̂ᵣ ρ [ τ ]ʳ)
                               (sym (updᵉ-⨟r k (econst ⊤ₑ) τ ρ (df m))) ⊩≾̂ᵣ-refl)

topʳ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : RVar Ψ} {R : Resid Ψ}
       → (∀ {a} → a ∈ rs R → Vʳ.FreeL {Ψ} k a)
       → Cleanʳ k R → DFreeʳ k R
       → (∀ {E} → E ∈ dfs R → Still dir↑ (updʳ k (rconst ⊤ᵣ)) E)
       → (τ : Subst Ψ Ψ')
       → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ updʳ k (rconst ⊤ᵣ) ⨟ˢ τ ]
topʳ-⊩ {Q = Q} {k} {R} fl cl df sd τ h =
  mk⊩ᴿ (Atʳ.raise-free Q k (rconst ⊤ᵣ) τ fl (mono-substᵣ ge) (⊩rs h))
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
-- Settled atoms: an ordering decided true against no hypotheses holds
-- at every instance and bounds nothing; so does a disjunction whose
-- type is eternal at every instance, and one whose grade is below the
-- unit from the orderings left holds wherever they do

Every : ∀ {Ψ} {X : Set} → (∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set) → X → Set
Every P a = ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst _ Ψ') → P Q δ a

Disj : ∀ {Ψ Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → OVType Ψ × RExp Ψ → Set
Disj Q δ (A , ρ) = VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ)

settledʳ : ∀ {Ψ} → (a : RExp Ψ × RExp Ψ) → Maybe (Every Ordʳ a)
settledʳ (ρ , ρ') with decideᵣ full ∅ᴴ ρ ρ'
... | just p  = just (λ δ → ⊩-substᵣ ∅ᴴ-⊩ᴴ p)
... | nothing = nothing

settledᵉ : ∀ {Ψ} → (a : EExp Ψ × EExp Ψ) → Maybe (Every Ordᵉ a)
settledᵉ (ε , ε') with decideₑ full ∅ᴴ ε ε'
... | just p  = just (λ δ → ⊩-substₑ ∅ᴴ-⊩ᴴ p)
... | nothing = nothing

-- A disjunction settled from hypotheses `H`: its grade below the unit
-- at the strength `full`, or its type eternal at every instance

Under : ∀ {Ψ} {X : Set} → Hyps Ψ → (∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set)
      → ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set
Under H P Q δ a = Q ⊩ᴴ H [ δ ] → P Q δ a

settledᵈ : ∀ {Ψ} → (H : Hyps Ψ) → (a : OVType Ψ × RExp Ψ) → Maybe (Every (Under H Disj) a)
settledᵈ H (A , ρ) with decideᵣ full H ρ ûᵣ
... | just p  = just (λ δ h → ≾ᵘ-ok (⊩-substᵣ h p))
... | nothing with etDec A in e
...   | just [] = just (λ δ _ → et-ok (⊩ᴱ-subst ∅ᴴ-⊩ᴴ (etDec-sound {Q = ∅ᴴ} A e (λ ()))))
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

-- An entry settled, or kept

consᵘ : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set} {a : X} {l : List X}
      → Maybe (Every P a) → Unsettled P l → Unsettled P (a ∷ l)
consᵘ (just p) (unset l' sb bk) =
  unset l' (λ m → there (sb m))
        (λ δ k → λ { (here refl) → p δ ; (there m) → bk δ k m })
consᵘ {a = a} nothing (unset l' sb bk) =
  unset (a ∷ l')
        (λ { (here refl) → here refl ; (there m) → there (sb m) })
        (λ δ k → λ { (here refl) → k (here refl)
                   ; (there m)   → bk δ (λ m' → k (there m')) m })

unsettled : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set}
          → ((a : X) → Maybe (Every P a)) → (l : List X) → Unsettled P l
unsettled set []      = unset [] (λ ()) (λ δ k → λ ())
unsettled set (a ∷ l) = consᵘ (set a) (unsettled set l)

-- The entries a test marks, each settled, the others kept

when : ∀ {Y : Set} → (b : 𝔹) → (b ≡ true → Y) → Maybe Y
when true  f = just (f refl)
when false f = nothing

dropping : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set}
         → (d : X → 𝔹) → (l : List X) → (∀ {a} → a ∈ l → d a ≡ true → Every P a)
         → Unsettled P l
dropping d []      h = unset [] (λ ()) (λ δ k → λ ())
dropping d (a ∷ l) h = consᵘ (when (d a) (h (here refl))) (dropping d l (λ m → h (there m)))

allKept : ∀ {Ψ} {X : Set} {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set} {l : List X}
        → Unsettled P l
allKept {l = l} = unset l (λ m → m) (λ δ k → k)

------------------------------------------------------------------------
-- One step: the value an unknown is sent to, with the proof that every
-- instance survives it, and the orderings it settles

Keeps : ∀ {Ψ} → Subst Ψ Ψ → Resid Ψ → Set
Keeps {Ψ} σ R = ∀ {Ψ'} → (τ : Subst Ψ Ψ') → (Q : Hyps Ψ') → Q ⊩ᴿ R [ τ ] → Q ⊩ᴿ R [ σ ⨟ˢ τ ]

-- The orderings an assignment `σ` leaves open; each other one holds at
-- every instance once `σ` is made

record Drops {Ψ} (σ : Subst Ψ Ψ) (R : Resid Ψ) : Set where
  constructor drops
  field
    dropsʳ : Unsettled (λ Q δ → Ordʳ Q (σ ⨟ˢ δ)) (rs R)
    dropsᵉ : Unsettled (λ Q δ → Ordᵉ Q (σ ⨟ˢ δ)) (es R)

keepAll : ∀ {Ψ} {σ : Subst Ψ Ψ} {R : Resid Ψ} → Drops σ R
keepAll = drops allKept allKept

-- The residual the open orderings leave

left : ∀ {Ψ} {σ : Subst Ψ Ψ} {R : Resid Ψ} → Drops σ R → Resid Ψ
left {R = R} (drops Dʳ Dᵉ) = record R { rs = Unsettled.kept Dʳ ; es = Unsettled.kept Dᵉ }

-- Lowering settles the orderings of its sort with the unknown on the
-- greater side (`lower-drops`)

loweredᵉ : ∀ {Ψ} {k : EVar Ψ} {R : Resid Ψ} → (lw : Vᵉ.Lows {Ψ} k (es R)) → (b : EExp Ψ)
         → (∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → ∀ {x} → x ∈ Vᵉ.bnds lw
            → Q ⊩ x [ δ ]ᵉ ≾̂ₑ b [ δ ]ᵉ)
         → Drops (updᵉ k b) R
loweredᵉ {k = k} {R} lw b ub =
  drops allKept
        (dropping (λ a → occᵉ-e k (proj₂ a)) (es R)
                  (λ m q {Ψ'} {Q} δ → Atᵉ.lower-drops Q k b δ lw (hit δ) m q))
  where
    hit : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst _ Ψ') → ∀ {x} → x ∈ Vᵉ.bnds lw
        → Q ⊩ x [ δ ]ᵉ ≾̂ₑ evar k [ updᵉ k b ⨟ˢ δ ]ᵉ
    hit {Q = Q} δ {x} mx = subst (λ z → Q ⊩ x [ δ ]ᵉ ≾̂ₑ z [ δ ]ᵉ) (sym (updᵉ-hit k b)) (ub δ mx)

loweredʳ : ∀ {Ψ} {k : RVar Ψ} {R : Resid Ψ} → (lw : Vʳ.Lows {Ψ} k (rs R)) → (b : RExp Ψ)
         → (∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → ∀ {x} → x ∈ Vʳ.bnds lw
            → Q ⊩ x [ δ ]ʳ ≾̂ᵣ b [ δ ]ʳ)
         → Drops (updʳ k b) R
loweredʳ {k = k} {R} lw b ub =
  drops (dropping (λ a → occʳ-r k (proj₂ a)) (rs R)
                  (λ m q {Ψ'} {Q} δ → Atʳ.lower-drops Q k b δ lw (hit δ) m q))
        allKept
  where
    hit : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst _ Ψ') → ∀ {x} → x ∈ Vʳ.bnds lw
        → Q ⊩ x [ δ ]ʳ ≾̂ᵣ rvar k [ updʳ k b ⨟ˢ δ ]ʳ
    hit {Q = Q} δ {x} mx = subst (λ z → Q ⊩ x [ δ ]ʳ ≾̂ᵣ z [ δ ]ʳ) (sym (updʳ-hit k b)) (ub δ mx)

-- The lowering value is principal: at every instance of the residual
-- it lies below the unknown

lowerᵉ-least : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : EVar Ψ} {R : Resid Ψ} {x : EExp Ψ} {xs : List (EExp Ψ)}
             → (∀ {y} → y ∈ x ∷ xs → (y , evar k) ∈ es R)
             → (τ : Subst Ψ Ψ') → Q ⊩ᴿ R [ τ ] → Q ⊩ joinₑ x xs [ τ ]ᵉ ≾̂ₑ sE τ k
lowerᵉ-least {x = x} {xs} s τ h = joinₑ-lub⊩ τ x xs (λ m → ⊩es h (s m))

lowerʳ-least : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {k : RVar Ψ} {R : Resid Ψ} {x : RExp Ψ} {xs : List (RExp Ψ)}
             → (∀ {y} → y ∈ x ∷ xs → (y , rvar k) ∈ rs R)
             → (τ : Subst Ψ Ψ') → Q ⊩ᴿ R [ τ ] → Q ⊩ joinᵣ x xs [ τ ]ʳ ≾̂ᵣ sR τ k
lowerʳ-least {x = x} {xs} s τ h = joinᵣ-lub⊩ τ x xs (λ m → ⊩rs h (s m))

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

-- A value: every instance survives it, and it names the orderings it
-- settles

Step : ∀ {Ψ} → Subst Ψ Ψ → Resid Ψ → Set
Step σ R = Keeps σ R × Drops σ R

-- The oracle of an effect unknown: the orderings of resources and the
-- deferred conditions are kept, and, for raising, the grades of the
-- disjunctions are free of it

oracleᵉ : ∀ {Ψ} → (k : EVar Ψ) → (R : Resid Ψ) → Vᵉ.Oracle {Ψ} k
oracleᵉ {Ψ} k R = record
  { Lower  = λ b → (∀ {a} → a ∈ rs R → Vⁱ.FreeR {Ψ} k a)
                 × (∀ {E} → E ∈ dfs R → Still dir↓ (updᵉ k b) E)
  ; lower? = λ b → both (Vⁱ.freeRs {Ψ} k (rs R)) (stills? dir↓ (updᵉ k b) (dfs R))
  ; Raise  = λ b → (∀ {a} → a ∈ rs R → Vⁱ.FreeL {Ψ} k a) × DFreeᵉ k R
                 × (∀ {E} → E ∈ dfs R → Still dir↑ (updᵉ k b) E)
  ; raise? = λ b → both (Vⁱ.freeLs {Ψ} k (rs R))
                        (both (dfreeᵉ? k R) (stills? dir↑ (updᵉ k b) (dfs R)))
  }

oracleʳ : ∀ {Ψ} → (k : RVar Ψ) → (R : Resid Ψ) → Vʳ.Oracle {Ψ} k
oracleʳ {Ψ} k R = record
  { Lower  = λ b → ∀ {E} → E ∈ dfs R → Still dir↓ (updʳ k b) E
  ; lower? = λ b → stills? dir↓ (updʳ k b) (dfs R)
  ; Raise  = λ b → DFreeʳ k R × (∀ {E} → E ∈ dfs R → Still dir↑ (updʳ k b) E)
  ; raise? = λ b → both (dfreeʳ? k R) (stills? dir↑ (updʳ k b) (dfs R))
  }

-- The rules of `Values` in order: lowering, raising, the least
-- element for an unknown that occurs, the top for one that occurs on a
-- greater side

stepᵉ : ∀ {Ψ} → (k : EVar Ψ) → (R : Resid Ψ) → Maybe (Σ[ b ∈ EExp Ψ ] Step (updᵉ k b) R)
stepᵉ {Ψ} k R with cleanᵉ? k R
... | nothing = nothing
... | just cl =
      first (Maybe.map lower (Vᵉ.lower {Ψ} k o (es R)))
      (first (Maybe.map raise (Vᵉ.raise {Ψ} k o (es R)))
      (first (if occursᵉ k R then Maybe.map least (Vᵉ.least {Ψ} k o (es R)) else nothing)
             (if occursᵉ⁺ k R then Maybe.map top (Vᵉ.topOf {Ψ} k o (es R)) else nothing)))
  where
    o = oracleᵉ k R

    lower : Vᵉ.ByLower {Ψ} k o (es R) → Σ[ b ∈ EExp Ψ ] Step (updᵉ k b) R
    lower (Vᵉ.byLower lw x xs e (fr , sd)) =
      joinₑ x xs ,
      (λ τ Q h → lowerᵉ-⊩ lw fr cl (joinₑ x xs) sd τ
                   (lowerᵉ-least {x = x} {xs} (λ m → Vᵉ.src lw (subst (_ ∈_) (sym e) m)) τ h)
                   (λ m → joinₑ-ub⊩ τ x xs (subst (_ ∈_) e m)) h) ,
      loweredᵉ lw (joinₑ x xs) (λ δ m → joinₑ-ub⊩ δ x xs (subst (_ ∈_) e m))

    raise : Vᵉ.ByRaise {Ψ} k o (es R) → Σ[ b ∈ EExp Ψ ] Step (updᵉ k b) R
    raise (Vᵉ.byRaise up (fl , df , sd)) =
      Vᵉ.cap up , (λ τ Q h → raiseᵉ-⊩ up fl cl df sd τ h) , keepAll

    least : Vᵉ.ByLeast {Ψ} k o (es R) → Σ[ b ∈ EExp Ψ ] Step (updᵉ k b) R
    least (Vᵉ.byLeast lw nob ij (fr , sd)) =
      ûₑ , (λ τ Q h → lowerᵉ-⊩ lw fr cl ûₑ sd τ (minₑ ij) (λ m → ⊥-elim (∉[] (subst (_ ∈_) nob m))) h) ,
      loweredᵉ lw ûₑ (λ δ m → ⊥-elim (∉[] (subst (_ ∈_) nob m)))

    top : Vᵉ.ByTop {Ψ} k o (es R) → Σ[ b ∈ EExp Ψ ] Step (updᵉ k b) R
    top (Vᵉ.byTop fe (fl , df , sd)) =
      econst ⊤ₑ , (λ τ Q h → topᵉ-⊩ fe fl cl df sd τ h) , keepAll

stepʳ : ∀ {Ψ} → (k : RVar Ψ) → (R : Resid Ψ) → Maybe (Σ[ b ∈ RExp Ψ ] Step (updʳ k b) R)
stepʳ {Ψ} k R with cleanʳ? k R
... | nothing = nothing
... | just cl =
      first (Maybe.map lower (Vʳ.lower {Ψ} k o (rs R)))
      (first (Maybe.map raise (Vʳ.raise {Ψ} k o (rs R)))
      (first (if occursʳ k R then Maybe.map least (Vʳ.least {Ψ} k o (rs R)) else nothing)
             (if occursʳ⁺ k R then Maybe.map top (Vʳ.topOf {Ψ} k o (rs R)) else nothing)))
  where
    o = oracleʳ k R

    lower : Vʳ.ByLower {Ψ} k o (rs R) → Σ[ b ∈ RExp Ψ ] Step (updʳ k b) R
    lower (Vʳ.byLower lw x xs e sd) =
      joinᵣ x xs ,
      (λ τ Q h → lowerʳ-⊩ lw cl (joinᵣ x xs) sd τ
                   (lowerʳ-least {x = x} {xs} (λ m → Vʳ.src lw (subst (_ ∈_) (sym e) m)) τ h)
                   (λ m → joinᵣ-ub⊩ τ x xs (subst (_ ∈_) e m)) h) ,
      loweredʳ lw (joinᵣ x xs) (λ δ m → joinᵣ-ub⊩ δ x xs (subst (_ ∈_) e m))

    raise : Vʳ.ByRaise {Ψ} k o (rs R) → Σ[ b ∈ RExp Ψ ] Step (updʳ k b) R
    raise (Vʳ.byRaise up (df , sd)) =
      Vʳ.cap up , (λ τ Q h → raiseʳ-⊩ up cl df sd τ h) , keepAll

    least : Vʳ.ByLeast {Ψ} k o (rs R) → Σ[ b ∈ RExp Ψ ] Step (updʳ k b) R
    least (Vʳ.byLeast lw nob ij sd) =
      ûᵣ , (λ τ Q h → lowerʳ-⊩ lw cl ûᵣ sd τ (minᵣ ij) (λ m → ⊥-elim (∉[] (subst (_ ∈_) nob m))) h) ,
      loweredʳ lw ûᵣ (λ δ m → ⊥-elim (∉[] (subst (_ ∈_) nob m)))

    top : Vʳ.ByTop {Ψ} k o (rs R) → Σ[ b ∈ RExp Ψ ] Step (updʳ k b) R
    top (Vʳ.byTop fl (df , sd)) =
      rconst ⊤ᵣ , (λ τ Q h → topʳ-⊩ fl cl df sd τ h) , keepAll

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

-- One disjunction, by the verdict of `etDec` on its type

consᴿ : ∀ {Ψ} {l : List (OVType Ψ × RExp Ψ)} → (A : OVType Ψ) → (ρ : RExp Ψ)
      → (x : Maybe (List (TyVar Ψ))) → etDec A ≡ x → Refined l → Refined ((A , ρ) ∷ l)
consᴿ A ρ nothing e (refined r os sb bk fw re) =
  refined r ((ρ , ûᵣ) ∷ os) (λ m → there (sb m))
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

refine : ∀ {Ψ} → (l : List (OVType Ψ × RExp Ψ)) → Refined l
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
-- Normal forms: each ordering split into its pieces (`piecesʳ`,
-- `piecesᵉ` of `Canon`), both sides canonical and one ordering per
-- alternative of the left side, the join being the least upper bound;
-- each disjunction's grade written canonically. A right side is never
-- split.

-- A disjunction: its grade in canonical form

piecesᵈ : ∀ {Ψ} → (a : OVType Ψ × RExp Ψ) → Pieces Disj a
piecesᵈ (A , ρ) =
  pieces ((A , canonᵣ ρ) ∷ [])
         (λ δ k → VarOK-≡̂ (≡̂ᵛ-refl _) (eqᵣ (≡̂ᵣ-subst δ (canonᵣ-≡ ρ))) (k (here refl)))
         (λ δ ok → λ { (here refl) →
            VarOK-≡̂ (≡̂ᵛ-refl _) (eqᵣ (≡̂ᵣ-sym (≡̂ᵣ-subst δ (canonᵣ-≡ ρ)))) ok })

------------------------------------------------------------------------
-- Unknowns that bound each other: each strongly connected component of
-- the orderings between whole unknowns is one unknown, its members
-- being equal at every instance satisfying them

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


-- A deferred condition survives a substitution equivalent to the one
-- it moves

keep⇕ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {σ : Subst Ψ Ψ} {τ : Subst Ψ Ψ'} → (E : Dfr Ψ)
      → Q ⊩ (σ ⨟ˢ τ) ≾ˢ τ → Q ⊩ τ ≾ˢ (σ ⨟ˢ τ) → Q ⊩ᵈ E [ τ ] → Q ⊩ᵈ E [ σ ⨟ˢ τ ]
keep⇕ (dfr l k o) le ge h =
  mk⊩ᵒ (λ {x} {y} m → transᵣ (mono-substᵣ (≾ˢ-↑ᵉⁿ k le) x)
                             (transᵣ (⊩ors h m) (mono-substᵣ (≾ˢ-↑ᵉⁿ k ge) y)))
       (λ {x} {y} m → transₑ (mono-substₑ (≾ˢ-↑ᵉⁿ k le) x)
                             (transₑ (⊩oes h m) (mono-substₑ (≾ˢ-↑ᵉⁿ k ge) y)))


-- Sending each unknown to one equal to it at an instance keeps the
-- instance where the types are fixed: every grade former is monotone,
-- so each side moves by as little in either direction

record TypesFixed {Ψ} (σ : Subst Ψ Ψ) (R : Resid Ψ) : Set where
  constructor typesFixed
  field
    fts : ∀ {A}   → A ∈ ts R       → A [ σ ]ᵛ ≡ A
    fss : ∀ {A B} → (A , B) ∈ ss R → (A [ σ ]ᵛ ≡ A) × (B [ σ ]ᵛ ≡ B)
    fds : ∀ {A ρ} → (A , ρ) ∈ ds R → A [ σ ]ᵛ ≡ A

equal-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {σ : Subst Ψ Ψ} {R : Resid Ψ}
        → TypesFixed σ R → (τ : Subst Ψ Ψ') → Q ⊩ᴿ R [ τ ]
        → Q ⊩ (σ ⨟ˢ τ) ≾ˢ τ → Q ⊩ τ ≾ˢ (σ ⨟ˢ τ) → Q ⊩ᴿ R [ σ ⨟ˢ τ ]
equal-⊩ {Q = Q} {σ} (typesFixed ft fs fd) τ h le ge =
  mk⊩ᴿ (equal-keeps {_⊑_ = Q ⊩_≾̂ᵣ_} transᵣ (mono-substᵣ le) (mono-substᵣ ge) (⊩rs h))
       (equal-keeps {_⊑_ = Q ⊩_≾̂ₑ_} transₑ (mono-substₑ le) (mono-substₑ ge) (⊩es h))
       (λ {A} m → subst (Q ⊩ᴱ_) (ty A (ft m)) (⊩ts h m))
       (λ {A} {B} m → subst₂ (Q ∣_<:̂ᵛ_) (ty A (proj₁ (fs m))) (ty B (proj₂ (fs m))) (⊩ss h m))
       (λ {A} {ρ} m → subst (λ X → VarOK Q X (ρ [ σ ⨟ˢ τ ]ʳ)) (ty A (fd m))
                            (VarOK-≡̂ (≡̂ᵛ-refl (A [ τ ]ᵛ)) (mono-substᵣ le ρ) (⊩ds h m)))
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

  module Cᵉ = Reachability.Collapse _≟ᶠ_ (λ a b → (evar a , evar b) ∈ es R) (edgesᵉ (es R))
                (bothEnds (edgesᵉ (es R))) (λ k → freeᵉ k O) Mvᵉ
                (λ k → both (isTrue (oᵉ P k)) (cleanᵉ? k R))
  module Cʳ = Reachability.Collapse _≟ᶠ_ (λ a b → (rvar a , rvar b) ∈ rs R) (edgesʳ (rs R))
                (bothEnds (edgesʳ (rs R))) (λ k → freeʳ k O) Mvʳ
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
-- Localisation: the residual's states, the contract a state keeps, and
-- the one-step relation whose irreducible states localisation reaches

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

-- A localisation for one outer substitution is one for any pointwise equal

loc-≐ : ∀ {Θ Φ} {O O' : Subst (Θ +e) Φ} {R : Resid Φ} → O ≐ˢ O' → Localised O R → Localised O' R
loc-≐ p (loc σ R' fx sn cp la) =
  loc σ R' (≐ˢ-trans (⨟-congˡ (≐ˢ-sym p) σ) (≐ˢ-trans fx p)) sn
      (λ τ en h → cp τ (proj₁ en , ≐ˢ-trans (⨟-congˡ p τ) (proj₂ en)) h) la

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
ordsᴴ R = hyps [] [] (rs R) (es R) []

settledOf : ∀ {Ψ} → (R : Resid Ψ) → Unsettled (Under (ordsᴴ R) Disj) (ds R)
settledOf R = unsettled (settledᵈ (ordsᴴ R)) (ds R)

refinedOf : ∀ {Ψ} → (R : Resid Ψ) → Refined (Unsettled.kept (settledOf R))
refinedOf R = refine (Unsettled.kept (settledOf R))

settleᴿ : ∀ {Ψ} → Resid Ψ → Resid Ψ
settleᴿ R = record R { rs = rs R ++ Refined.ords (refinedOf R) ; ds = Refined.rest (refinedOf R) }

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
                                       (mk⊩ᴴ (λ ()) (λ ()) (λ m' → ⊩rs h (∈-++⁺ˡ m')) (⊩es h) (λ ())))
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


-- An assignment the later substitution already agrees with is absorbed

updᵉ-absorb : ∀ {Ψ Ψ'} → (k : EVar Ψ) → (b : EExp Ψ) → (Y : Subst Ψ Ψ')
            → sE Y k ≡ b [ Y ]ᵉ → (updᵉ k b ⨟ˢ Y) ≐ˢ Y
updᵉ-absorb {Ψ} k b Y q = mk≐ˢ (λ α → refl) (λ i → refl) e
  where
    e : (i : EVar Ψ) → sE (updᵉ k b) i [ Y ]ᵉ ≡ sE Y i
    e i with i ≟ᶠ k
    ... | yes refl = sym q
    ... | no _     = refl
