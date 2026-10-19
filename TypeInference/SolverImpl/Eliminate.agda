------------------------------------------------------------------
-- Eliminating an unknown from a report                         --
--                                                              --
-- The steps, in the order they are tried, each at the first    --
-- unknown outside a given set where it applies:                --
--   * merging (`mergeᵉ?`, `mergeʳ?`): a lowering, as below,    --
--     whose value is a single unknown;                         --
--   * equating (`equateᵉ`, `equateʳ`): a grade unknown that    --
--     the hypotheses equate with an expression an ordering     --
--     sets against it, both orderings decided at the strength  --
--     `atomic` (`Entail`), is replaced by it everywhere, and   --
--     the orderings made reflexive are removed (`Values`'      --
--     `equate`: of two equal unknowns, the one of smaller      --
--     index remains);                                          --
--   * lowering (`stepᵉ`, `stepʳ`): a grade unknown is sent to  --
--     the value `B* · L · C*` from the join `L` of its lower   --
--     bounds, or its closure where it has the cycle            --
--     `v · v ≾ v`; the bounds are removed with it, and its     --
--     cycles, which close at the value (`Values`' `lower`);    --
--   * raising (`upᵉ-step`, `upʳ-step`): a grade unknown is     --
--     sent to the first upper bound that caps the others, the  --
--     orderings it caps removed (`Values`' `raise`);           --
--   * the forced unit (`unitᵉ`, `unitʳ`): a grade unknown      --
--     bounded above by an expression decided below the unit,   --
--     the unit being least, is sent to the unit, whatever its  --
--     occurrences; for an effect unknown also through its      --
--     image, where the grade system reflects the order at the  --
--     unit (`reflects-u?`). The bounding orderings are         --
--     removed, the atoms the unknown occurs in are written     --
--     canonically, each ordering split into one per            --
--     alternative of its left side, and the orderings made     --
--     reflexive are removed;                                   --
--   * cycle elimination (`collapseᵗ`): the type variables of   --
--     each strongly connected component of the subtyping atoms --
--     are sent to its representative (`Reach`'s `Collapse`),  --
--     a member that is never eliminated where there is one,    --
--     else the least by index, and the atoms made reflexive    --
--     are removed;                                             --
--   * lowering a type variable (`stepᵗ`) to a single bound     --
--     below, open types having no join.                        --
-- An oracle (`oracleᵉ`, `oracleʳ`) licenses lowering and       --
-- raising: the polarity (`Polarity`) of the unknown in the     --
-- reported type and in the atoms of the other sorts and the    --
-- disjunctions; atoms valid at every instance bound nothing.   --
--                                                              --
-- Contract (`Elim`). Every step is a substitution `η`: the new --
-- type is the old one along `η`, up to convertibility          --
-- (`conv`), and the new hypotheses entail the old ones along   --
-- `η` (`inst`). Every closed instance of the old hypotheses is --
-- one of the new (`keep`), at which the new type is a subtype  --
-- of the old (`princ`). Steps compose (`_⨾ᴱ_`). The unknowns   --
-- of a given set are never eliminated, and `η` fixes them      --
-- (`Elimᶠ`). Which unknowns remain is not claimed: a step is   --
-- taken where its test succeeds. For a step against a bound,   --
-- the hypotheses it keeps on the unknown's sort are entailed   --
-- by `Values` (`lowerR`, `raiseL`); the type, the other sort   --
-- and the disjunctions are kept by polarity (`Monoᵉ`, `Raiseᵉ` --
-- and their counterparts, each an instance of `Lift`, which    --
-- relates the parts of a former at their variance). For a step --
-- by equality, the hypotheses bound `η` by the identity in     --
-- both directions, and it moves no type (`Equal`). A forced    --
-- unit is such a step under the hypotheses with the unknown    --
-- below the unit added, which every closed instance meets      --
-- (`unit-forcedᵣ`, `unit-forcedₑ`; through the image, by       --
-- reflection at the instance).                                 --
--                                                              --
-- The polarity-based elimination follows Pottier's             --
-- simplification of subtyping constraints (ICFP 1996); cycle   --
-- elimination follows Fähndrich, Foster, Su and Aiken (PLDI    --
-- 1998).                                                       --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false; not; _∨_; _∧_) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_; map; filter; filterᵇ)
open import Data.Bool.ListAction using (any)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-map⁺; ∈-map⁻; ∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; lookup; tabulate)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as Maybe
open import Data.Maybe using (Is-just)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)

open import Induction.WellFounded using (Acc; acc; WfRec)

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; ¬?)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; fold) renaming (ε to ε⋆)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Eliminate (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S
  using (_⊨ᴴ_; ⊨ᴴ-refl; ⊨ᴴ-trans; ⊩ᴴ-⊨ᴴ; mk⊨ᴴ; VarOK-∅-mono; val-≾ᵣ; val-≾ₑ⁻)

open import TypeInference.SolverImpl.Former   S
open import TypeInference.SolverImpl.Polarity S
open import TypeInference.SolverImpl.Vars     S
  using (Vars; vᵗ; vʳ; vᵉ; Fixes; mkFixes; fixes-id; fixes-⨟; fixes-updᵉ; fixes-updʳ; outside)
open import TypeInference.SolverImpl.Core.Occurs S
  using (occᵉ-e; occᵉ-r; occᵉ-v; occʳ-r; occʳ-v)
open import TypeInference.SolverImpl.Resid       S using (∅ᴴ-⊩ᴴ)
open import TypeInference.SolverImpl.Entail      S using (decideᵣ; decideₑ; atomic)
import TypeInference.SolverImpl.Reach as Reachability
open import TypeInference.SolverImpl.Values      S
  using (module Vᵉ; module Vʳ; module Vⁱ; isFalse; Parts; partition; kept; kept⊆; which;
         updᵉ-e; updᵉ-r; updʳ-r;
         joinₑ; joinᵣ; joinₑ-ub⊩; joinₑ-lub⊩; joinᵣ-ub⊩; joinᵣ-lub⊩; module LowToₑ; module LowToᵣ)
open import TypeInference.SolverImpl.Canon       S
  using (canonₑ; canonᵣ; canonₑ-≡; canonᵣ-≡; canonᵛ; canonᵛ-≡̂; canonᶜ; canonᶜ-≡̂;
         canonᴴ; canonᴴ-⊩; canonᴴ-⊩⁻; Ordʳ; Ordᵉ; Pieces; whole; Split; splitsBy;
         piecesʳ; piecesᵉ)

-- Updating one slot of a finitely indexed family, by structural
-- recursion on the index, without a decision of equality.

upd : ∀ {n} {A : Set} → Fin n → A → (Fin n → A) → Fin n → A
upd zero    a f zero    = a
upd zero    a f (suc j) = f (suc j)
upd (suc i) a f zero    = f zero
upd (suc i) a f (suc j) = upd i a (λ k → f (suc k)) j

upd-≡ : ∀ {n} {A : Set} → (i : Fin n) → (a : A) → (f : Fin n → A) → upd i a f i ≡ a
upd-≡ zero    a f = refl
upd-≡ (suc i) a f = upd-≡ i a (λ k → f (suc k))

upd-≢ : ∀ {n} {A : Set} → (i j : Fin n) → (a : A) → (f : Fin n → A) → ¬ (i ≡ j)
      → upd i a f j ≡ f j
upd-≢ zero    zero    a f ¬p = ⊥-elim (¬p refl)
upd-≢ zero    (suc j) a f ¬p = refl
upd-≢ (suc i) zero    a f ¬p = refl
upd-≢ (suc i) (suc j) a f ¬p = upd-≢ i j a (λ k → f (suc k)) (λ q → ¬p (cong suc q))

-- Reading the polarity analysis back

⌊⌋-false : ∀ {n} {i j : Fin n} → ⌊ i ≟ᶠ j ⌋ ≡ false → ¬ (i ≡ j)
⌊⌋-false {i = i} {j = j} q with i ≟ᶠ j
... | yes _  = λ _ → ⊥-elim (tf q)
  where tf : (𝔹.true) ≡ false → _
        tf ()
... | no  ¬p = ¬p

∨-false : (a b : 𝔹) → a ∨ b ≡ false → (a ≡ false) × (b ≡ false)
∨-false false b e = refl , e

below-∪ : (p q : Pol) → below (p ∪ᴾ q) ≡ false
        → (below p ≡ false) × (below q ≡ false)
below-∪ p q e = ∨-false (below p) (below q) e

-- The pairs whose two sides are not the same

apart : ∀ {X : Set} {_≅_ : X → X → Set} → Decidable _≅_ → List (X × X) → List (X × X)
apart _≟_ = filter (λ p → ¬? (proj₁ p ≟ proj₂ p))

apart-⊆ : ∀ {X : Set} {_≅_ : X → X → Set} → (_≟_ : Decidable _≅_) → ∀ {p l}
        → p ∈ apart _≟_ l → p ∈ l
apart-⊆ _≟_ m = proj₁ (∈-filter⁻ (λ p → ¬? (proj₁ p ≟ proj₂ p)) m)

apart-∈ : ∀ {X : Set} {_≅_ : X → X → Set} → (_≟_ : Decidable _≅_) → ∀ {a b l}
        → (a , b) ∈ l → (a ≅ b) ⊎ ((a , b) ∈ apart _≟_ l)
apart-∈ _≟_ {a} {b} m with a ≟ b
... | yes e  = inj₁ e
... | no  ¬e = inj₂ (∈-filter⁺ (λ p → ¬? (proj₁ p ≟ proj₂ p)) m ¬e)

-- Along a split, the pieces apart from those with the same two sides

apart-back : ∀ {Ψ} {X : Set} {_≅_ : X → X → Set} → (_≟_ : Decidable _≅_)
           → {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X × X → Set}
           → (∀ {Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} {x x'} → x ≅ x' → P Q δ (x , x'))
           → ∀ {l} → (S : Split P l) → ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
           → (∀ {b} → b ∈ apart _≟_ (Split.out S) → P Q δ b) → ∀ {a} → a ∈ l → P Q δ a
apart-back _≟_ {P} prefl S {Q = Q} δ k = Split.back S δ pick
  where
    pick : ∀ {b} → b ∈ Split.out S → P Q δ b
    pick {x , x'} mb with apart-∈ _≟_ mb
    ... | inj₁ e = prefl e
    ... | inj₂ m    = k m

apart-fwd : ∀ {Ψ} {X : Set} {_≅_ : X → X → Set} → (_≟_ : Decidable _≅_)
          → {P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X × X → Set}
          → ∀ {l} → (S : Split P l) → ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
          → (∀ {a} → a ∈ l → P Q δ a) → ∀ {b} → b ∈ apart _≟_ (Split.out S) → P Q δ b
apart-fwd _≟_ S δ k mb = Split.fwd S δ k (apart-⊆ _≟_ mb)

------------------------------------------------------------------------
-- One step: the reported type, the hypothesis set, the substitution,
-- and the facts relating them

record Elim {Θ : Scope} (C : OCType Θ) (Q : Hyps Θ) : Set where
  constructor mkElim
  field
    Ĉ     : OCType Θ
    Q̂     : Hyps Θ
    η     : Subst Θ Θ
    conv  : Ĉ ≡̂ᶜ C [ η ]ᶜ
    inst  : Q̂ ⊩ᴴ Q [ η ]
    keep  : Q ⊨ᴴ Q̂
    princ : (δ : Subst Θ ∅ˢ) → ∅ᴴ ⊩ᴴ Q [ δ ] → ∅ᴴ ∣ Ĉ [ δ ]ᶜ <:̂ᶜ C [ δ ]ᶜ

open Elim public

idElim : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → Elim C Q
idElim C Q =
  mkElim C Q idˢ (subst (C ≡̂ᶜ_) (sym ([id]ᶜ C)) (≡̂ᶜ-refl C)) ⊩ᴴ-refl ⊨ᴴ-refl
         (λ δ h → <:̂ᶜ-refl (C [ δ ]ᶜ))

infixl 5 _⨾ᴱ_

_⨾ᴱ_ : ∀ {Θ} {C : OCType Θ} {Q : Hyps Θ} → (r : Elim C Q)
     → Elim (Ĉ r) (Q̂ r) → Elim C Q
_⨾ᴱ_ {C = C} r s =
  mkElim (Ĉ s) (Q̂ s) (η r ⨟ˢ η s)
         (≡̂ᶜ-trans (conv s)
           (subst (Ĉ r [ η s ]ᶜ ≡̂ᶜ_) ([⨟]ᶜ C (η r) (η s)) (≡̂ᶜ-subst (η s) (conv r))))
         (⊩ᴴ-⨟ (inst s) (inst r))
         (⊨ᴴ-trans (keep r) (keep s))
         (λ δ h → <:̂ᶜ-trans (princ s δ (keep r δ h)) (princ r δ h))

-- An elimination fixing a set of unknowns

Elimᶠ : ∀ {Θ} → Vars Θ → OCType Θ → Hyps Θ → Set
Elimᶠ F C Q = Σ[ r ∈ Elim C Q ] Fixes F (η r)

infixl 5 _⨾ᶠ_

_⨾ᶠ_ : ∀ {Θ} {F : Vars Θ} {C : OCType Θ} {Q : Hyps Θ} → (r : Elimᶠ F C Q)
     → Elimᶠ F (Ĉ (proj₁ r)) (Q̂ (proj₁ r)) → Elimᶠ F C Q
(r , f) ⨾ᶠ (s , g) = r ⨾ᴱ s , fixes-⨟ f g

-- Normalising a whole report, as an elimination step that instantiates
-- no unknown

canonElim : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → Elim C Q
canonElim C Q =
  mkElim (canonᶜ C) (canonᴴ Q) idˢ
         (subst (canonᶜ C ≡̂ᶜ_) (sym ([id]ᶜ C)) (≡̂ᶜ-sym (canonᶜ-≡̂ C)))
         (canonᴴ-⊩ Q) (⊩ᴴ-⊨ᴴ (canonᴴ-⊩⁻ Q))
         (λ δ h → <:̂ᶜ-subst h (≡̂ᶜ-<:̂ (≡̂ᶜ-sym (canonᶜ-≡̂ C))))

------------------------------------------------------------------------
-- The two conclusions of a monotonicity argument, by the side of the
-- ordering the traversed position sits on

module _ {Θ : Scope} (Q : Hyps Θ) where

  atᵉ : Sign → EExp Θ → EExp Θ → Set
  atᵉ ⁺ x y = Q ⊩ x ≾̂ₑ y
  atᵉ ⁻ x y = Q ⊩ y ≾̂ₑ x

  atʳ : Sign → RExp Θ → RExp Θ → Set
  atʳ ⁺ x y = Q ⊩ x ≾̂ᵣ y
  atʳ ⁻ x y = Q ⊩ y ≾̂ᵣ x

  atᵛ : Sign → OVType Θ → OVType Θ → Set
  atᵛ ⁺ A B = Q ∣ A <:̂ᵛ B
  atᵛ ⁻ A B = Q ∣ B <:̂ᵛ A

  atᶜ : Sign → OCType Θ → OCType Θ → Set
  atᶜ ⁺ C D = Q ∣ C <:̂ᶜ D
  atᶜ ⁻ C D = Q ∣ D <:̂ᶜ C

module _ {Θ : Scope} {Q : Hyps Θ} where

  atᵉ-≡ : (s : Sign) → {x y : EExp Θ} → x ≡ y → atᵉ Q s x y
  atᵉ-≡ ⁺ refl = ⊩≾̂ₑ-refl
  atᵉ-≡ ⁻ refl = ⊩≾̂ₑ-refl

  atʳ-≡ : (s : Sign) → {x y : RExp Θ} → x ≡ y → atʳ Q s x y
  atʳ-≡ ⁺ refl = ⊩≾̂ᵣ-refl
  atʳ-≡ ⁻ refl = ⊩≾̂ᵣ-refl

  atᵛ-≡ : (s : Sign) → {A B : OVType Θ} → A ≡ B → atᵛ Q s A B
  atᵛ-≡ ⁺ {A} refl = <:̂ᵛ-refl A
  atᵛ-≡ ⁻ {A} refl = <:̂ᵛ-refl A

  atᶜ-‼ : (s : Sign) → {A A' : OVType Θ} {ε ε' : EExp Θ}
        → atᵛ Q s A A' → atᵉ Q s ε ε' → atᶜ Q s (A ‼ ε) (A' ‼ ε')
  atᶜ-‼ ⁺ p q = p ‼ₛ q
  atᶜ-‼ ⁻ p q = p ‼ₛ q

------------------------------------------------------------------------
-- A substitution related to the identity at every leaf of a type, at
-- the sign of the leaf's position, is related to it at the type: the
-- parts of a former are related at their variance (`Former`). A leaf
-- is admitted by a predicate on its polarity, closed under the parts
-- of a union.

module Lift {Θ : Scope} {Q : Hyps Θ} (η : Subst Θ Θ)
            (G : Pol → Set) (G-∪ : ∀ p q → G (p ∪ᴾ q) → G p × G q)
            (lt : Sign → TyVar Θ → Pol) (lr : Sign → RExp Θ → Pol) (le : Sign → EExp Θ → Pol)
            (ft : ∀ s α → G (lt s α) → atᵛ Q s (sTy η α) (tvar α))
            (fr : ∀ s ρ → G (lr s ρ) → atʳ Q s (ρ [ η ]ʳ) ρ)
            (fe : ∀ s ε → G (le s ε) → atᵉ Q s (ε [ η ]ᵉ) ε) where

  G-∈ : ∀ {X : Set} → (xs : List X) → {f : ∀ {x} → x ∈ xs → Pol} → G (unionᴾ xs f)
      → ∀ {x} → (m : x ∈ xs) → G (f m)
  G-∈ (x ∷ xs) g (here refl) = proj₁ (G-∪ _ _ g)
  G-∈ (x ∷ xs) {f} g (there m) = G-∈ xs {λ m' → f (there m')} (proj₂ (G-∪ _ _ g)) m

  -- A position of a variance read at a sign, from the facts at either sign

  byVar : (T : Sign → Set) → (v : Variance) → (s : Sign) → {f : Sign → Pol}
        → G (atVar v s f) → (∀ s' → G (f s') → T s') → Var v (T s) (T (flipˢ s))
  byVar T co     s g k = k s g
  byVar T contra s g k = k (flipˢ s) g
  byVar T inv    s g k = k s (proj₁ (G-∪ _ _ g)) , k (flipˢ s) (proj₂ (G-∪ _ _ g))

  frᵢ : ∀ s ρ → G (lr s ρ) → atʳ Q s (ρ [ η ]ʳ) (ρ [ idˢ ]ʳ)
  frᵢ s ρ g = subst (atʳ Q s (ρ [ η ]ʳ)) (sym ([id]ʳ ρ)) (fr s ρ g)

  feᵢ : ∀ s ε → G (le s ε) → atᵉ Q s (ε [ η ]ᵉ) (ε [ idˢ ]ᵉ)
  feᵢ s ε g = subst (atᵉ Q s (ε [ η ]ᵉ)) (sym ([id]ᵉ ε)) (fe s ε g)

  -- The two instances compared at a sign

  ends : Sign → Subst Θ Θ × Subst Θ Θ
  ends ⁺ = η , idˢ
  ends ⁻ = idˢ , η

  liftᵃ : (s : Sign) → (A : OVType Θ) → (a : Acc _≺_ A) → G (polᵛᵃ lt lr le s A a)
        → atᵛ Q s (A [ η ]ᵛ) (A [ idˢ ]ᵛ)
  partˡ : (s : Sign) → {A : OVType Θ} {ps : List (Part Θ)} → (g : Decomp A A ps)
        → All Diag ps → (r : WfRec _≺_ (Acc _≺_) A) → ∀ {p} → (m : p ∈ ps)
        → G (polᴾ lt lr le s g r m) → Holdsᴾ Q (p [ proj₁ (ends s) ∣ proj₂ (ends s) ]ᴾ)

  liftᵃ s A (acc r) h with self A
  ... | var α       = ft s α h
  ... | form ps g d = intro s (tabulate (λ m → partˡ s g d r m (G-∈ ps h m)))
    where
      intro : (s : Sign) → All (λ p → Holdsᴾ Q (p [ proj₁ (ends s) ∣ proj₂ (ends s) ]ᴾ)) ps
            → atᵛ Q s (A [ η ]ᵛ) (A [ idˢ ]ᵛ)
      intro ⁺ a = <:-intro g η idˢ a
      intro ⁻ a = <:-intro g idˢ η a

  partˡ ⁺ g d r {ty v X _} m h with lookup d m
  ... | refl = byVar (λ s' → atᵛ Q s' (X [ η ]ᵛ) (X [ idˢ ]ᵛ)) v ⁺ h
                     (λ s' → liftᵃ s' X (r (left g m)))
  partˡ ⁻ g d r {ty v X _} m h with lookup d m
  ... | refl = byVar (λ s' → atᵛ Q s' (X [ η ]ᵛ) (X [ idˢ ]ᵛ)) v ⁻ h
                     (λ s' → liftᵃ s' X (r (left g m)))
  partˡ ⁺ g d r {rg v ρ _} m h with lookup d m
  ... | refl = byVar (λ s' → atʳ Q s' (ρ [ η ]ʳ) (ρ [ idˢ ]ʳ)) v ⁺ h (λ s' → frᵢ s' ρ)
  partˡ ⁻ g d r {rg v ρ _} m h with lookup d m
  ... | refl = byVar (λ s' → atʳ Q s' (ρ [ η ]ʳ) (ρ [ idˢ ]ʳ)) v ⁻ h (λ s' → frᵢ s' ρ)
  partˡ ⁺ g d r {eg v ε _} m h with lookup d m
  ... | refl = byVar (λ s' → atᵉ Q s' (ε [ η ]ᵉ) (ε [ idˢ ]ᵉ)) v ⁺ h (λ s' → feᵢ s' ε)
  partˡ ⁻ g d r {eg v ε _} m h with lookup d m
  ... | refl = byVar (λ s' → atᵉ Q s' (ε [ η ]ᵉ) (ε [ idˢ ]ᵉ)) v ⁻ h (λ s' → feᵢ s' ε)

  lift : (s : Sign) → (A : OVType Θ) → G (polᵛ lt lr le s A) → atᵛ Q s (A [ η ]ᵛ) A
  lift s A h = subst (atᵛ Q s (A [ η ]ᵛ)) ([id]ᵛ A) (liftᵃ s A (≺-wf A) h)

------------------------------------------------------------------------
-- A substitution lowering every unknown lowers every grade expression
-- and keeps every ordering whose right side it does not lower. At each
-- instance it keeps every var-rule disjunction, eternality reading only
-- the skeleton.

module Lowering {Θ : Scope} {Q : Hyps Θ} (η₀ : Subst Θ Θ)
                (lowg : Q ⊩ η₀ ≾ˢ idˢ) (lowt : ∀ β → Q ∣ sTy η₀ β <:̂ᵛ tvar β) where

  lowʳ : (ρ : RExp Θ) → Q ⊩ ρ [ η₀ ]ʳ ≾̂ᵣ ρ
  lowʳ ρ = subst (Q ⊩ ρ [ η₀ ]ʳ ≾̂ᵣ_) ([id]ʳ ρ) (mono-substᵣ lowg ρ)

  lowᵉ : (ε : EExp Θ) → Q ⊩ ε [ η₀ ]ᵉ ≾̂ₑ ε
  lowᵉ ε = subst (Q ⊩ ε [ η₀ ]ᵉ ≾̂ₑ_) ([id]ᵉ ε) (mono-substₑ lowg ε)

  fixedʳ : ∀ {ρ} → ρ [ η₀ ]ʳ ≡ ρ → Q ⊩ ρ ≾̂ᵣ ρ [ η₀ ]ʳ
  fixedʳ e = atʳ-≡ ⁻ e

  fixedᵉ : ∀ {ε} → ε [ η₀ ]ᵉ ≡ ε → Q ⊩ ε ≾̂ₑ ε [ η₀ ]ᵉ
  fixedᵉ e = atᵉ-≡ ⁻ e

  keep-ordʳ : (l : List (RExp Θ × RExp Θ)) → (∀ {p} → p ∈ l → p ∈ ordᵣ Q)
            → (∀ {ρ ρ'} → (ρ , ρ') ∈ l → Q ⊩ ρ' ≾̂ᵣ ρ' [ η₀ ]ʳ)
            → ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ (_[ η₀ ]ʳ)) l → Q ⊩ ρ ≾̂ᵣ ρ'
  keep-ordʳ l k r m with ∈-map⁻ (mapᵖ (_[ η₀ ]ʳ)) m
  ... | (ρ₀ , ρ₀') , m₀ , refl = transᵣ (lowʳ ρ₀) (transᵣ (hypᵣ (k m₀)) (r m₀))

  keep-ordᵉ : (l : List (EExp Θ × EExp Θ)) → (∀ {p} → p ∈ l → p ∈ ordₑ Q)
            → (∀ {ε ε'} → (ε , ε') ∈ l → Q ⊩ ε' ≾̂ₑ ε' [ η₀ ]ᵉ)
            → ∀ {ε ε'} → (ε , ε') ∈ map (mapᵖ (_[ η₀ ]ᵉ)) l → Q ⊩ ε ≾̂ₑ ε'
  keep-ordᵉ l k r m with ∈-map⁻ (mapᵖ (_[ η₀ ]ᵉ)) m
  ... | (ε₀ , ε₀') , m₀ , refl = transₑ (lowᵉ ε₀) (transₑ (hypₑ (k m₀)) (r m₀))

  keep-disj : (δ : Subst Θ ∅ˢ) → ∅ᴴ ⊩ᴴ Q [ δ ]
            → ∀ {A ρ} → (A , ρ) ∈ map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q)
            → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ)
  keep-disj δ h m with ∈-map⁻ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m
  ... | (A₀ , ρ₀) , m₀ , refl =
        VarOK-∅-mono et (⊩-substᵣ h (lowʳ ρ₀)) (⊩disj h m₀)
    where
      et : ∅ᴴ ⊩ᴱ A₀ [ δ ]ᵛ → ∅ᴴ ⊩ᴱ A₀ [ η₀ ]ᵛ [ δ ]ᵛ
      et e = subst (∅ᴴ ⊩ᴱ_) (sym ([⨟]ᵛ A₀ η₀ δ))
                   (⊩ᴱ-<:ˢ {σ = η₀ ⨟ˢ δ} {τ = δ} (λ β → <:̂ᵛ-subst h (lowt β)) A₀ e)

-- A substitution that, under the hypotheses, is both below and above
-- the identity moves no type

module Equal {Θ : Scope} {Q : Hyps Θ} (η₀ : Subst Θ Θ)
             (lowg : Q ⊩ η₀ ≾ˢ idˢ) (hig : Q ⊩ idˢ ≾ˢ η₀)
             (lowt : ∀ β → Q ∣ sTy η₀ β <:̂ᵛ tvar β) (hit : ∀ β → Q ∣ tvar β <:̂ᵛ sTy η₀ β) where

  open Lowering {Q = Q} η₀ lowg lowt public

  raiseʳ : (ρ : RExp Θ) → Q ⊩ ρ ≾̂ᵣ ρ [ η₀ ]ʳ
  raiseʳ ρ = subst (λ x → Q ⊩ x ≾̂ᵣ ρ [ η₀ ]ʳ) ([id]ʳ ρ) (mono-substᵣ hig ρ)

  raiseᵉ : (ε : EExp Θ) → Q ⊩ ε ≾̂ₑ ε [ η₀ ]ᵉ
  raiseᵉ ε = subst (λ x → Q ⊩ x ≾̂ₑ ε [ η₀ ]ᵉ) ([id]ᵉ ε) (mono-substₑ hig ε)

  sameʳ : (s : Sign) → (ρ : RExp Θ) → atʳ Q s (ρ [ η₀ ]ʳ) ρ
  sameʳ ⁺ ρ = lowʳ ρ
  sameʳ ⁻ ρ = raiseʳ ρ

  sameᵉ : (s : Sign) → (ε : EExp Θ) → atᵉ Q s (ε [ η₀ ]ᵉ) ε
  sameᵉ ⁺ ε = lowᵉ ε
  sameᵉ ⁻ ε = raiseᵉ ε

  sameᵗ : (s : Sign) → (β : TyVar Θ) → atᵛ Q s (sTy η₀ β) (tvar β)
  sameᵗ ⁺ β = lowt β
  sameᵗ ⁻ β = hit β

  sameᵛ : (s : Sign) → (A : OVType Θ) → atᵛ Q s (A [ η₀ ]ᵛ) A
  sameᵛ s A = Lift.lift η₀ (λ _ → ⊤) (λ _ _ _ → tt , tt)
                (λ _ _ → noᴾ) (λ _ _ → noᴾ) (λ _ _ → noᴾ)
                (λ s β _ → sameᵗ s β) (λ s ρ _ → sameʳ s ρ) (λ s ε _ → sameᵉ s ε) s A tt

  sameᶜ : (s : Sign) → (C : OCType Θ) → atᶜ Q s (C [ η₀ ]ᶜ) C
  sameᶜ s (A ‼ ε) = atᶜ-‼ s (sameᵛ s A) (sameᵉ s ε)

------------------------------------------------------------------------
-- An unknown absent from an expression is fixed by updating it

absᵉ-e : ∀ {Θ} → (i : EVar Θ) → (b : EExp Θ) → (ε : EExp Θ)
       → below (polₑ-e i ⁻ ε) ≡ false → ε [ updᵉ i b ]ᵉ ≡ ε
absᵉ-e i b (evar j)   q = updᵉ-miss i b j q
absᵉ-e i b (econst c) q = refl
absᵉ-e i b (ε ·̂ₑ ε')  q = cong₂ _·̂ₑ_ (absᵉ-e i b ε (proj₁ d)) (absᵉ-e i b ε' (proj₂ d))
  where d = below-∪ (polₑ-e i ⁻ ε) (polₑ-e i ⁻ ε') q
absᵉ-e i b (ε ⊔̂ₑ ε')  q = cong₂ _⊔̂ₑ_ (absᵉ-e i b ε (proj₁ d)) (absᵉ-e i b ε' (proj₂ d))
  where d = below-∪ (polₑ-e i ⁻ ε) (polₑ-e i ⁻ ε') q

absᵉ-r : ∀ {Θ} → (i : EVar Θ) → (b : EExp Θ) → (ρ : RExp Θ)
       → below (polₑ-r i ⁻ ρ) ≡ false → ρ [ updᵉ i b ]ʳ ≡ ρ
absᵉ-r i b (rvar j)   q = refl
absᵉ-r i b (rconst c) q = refl
absᵉ-r i b (ρ ·̂ᵣ ρ')  q = cong₂ _·̂ᵣ_ (absᵉ-r i b ρ (proj₁ d)) (absᵉ-r i b ρ' (proj₂ d))
  where d = below-∪ (polₑ-r i ⁻ ρ) (polₑ-r i ⁻ ρ') q
absᵉ-r i b (ρ ⊔̂ᵣ ρ')  q = cong₂ _⊔̂ᵣ_ (absᵉ-r i b ρ (proj₁ d)) (absᵉ-r i b ρ' (proj₂ d))
  where d = below-∪ (polₑ-r i ⁻ ρ) (polₑ-r i ⁻ ρ') q
absᵉ-r i b ∣ ε ∣̂ᵉ     q = cong ∣_∣̂ᵉ (absᵉ-e i b ε q)

-- Lowering an effect unknown lowers whatever has no occurrence of it
-- below

module Monoᵉ {Θ : Scope} {Q : Hyps Θ} (i : EVar Θ) (b : EExp Θ)
             (lowg : Q ⊩ updᵉ i b ≾ˢ idˢ) where

  open Lowering {Q = Q} (updᵉ i b) lowg (λ β → tvarₛ reflᵗᵛ)

  monoᵉ-e : (s : Sign) → (ε : EExp Θ) → below (polₑ-e i s ε) ≡ false
          → atᵉ Q s (ε [ updᵉ i b ]ᵉ) ε
  monoᵉ-e ⁺ ε q = lowᵉ ε
  monoᵉ-e ⁻ ε q = atᵉ-≡ ⁻ (absᵉ-e i b ε q)

  monoᵉ-r : (s : Sign) → (ρ : RExp Θ) → below (polₑ-r i s ρ) ≡ false
          → atʳ Q s (ρ [ updᵉ i b ]ʳ) ρ
  monoᵉ-r ⁺ ρ q = lowʳ ρ
  monoᵉ-r ⁻ ρ q = atʳ-≡ ⁻ (absᵉ-r i b ρ q)

  monoᵉ-v : (s : Sign) → (A : OVType Θ) → below (polₑ-v i s A) ≡ false
          → atᵛ Q s (A [ updᵉ i b ]ᵛ) A
  monoᵉ-v = Lift.lift (updᵉ i b) (λ p → below p ≡ false) below-∪
              (λ _ _ → noᴾ) (polₑ-r i) (polₑ-e i) (λ s α _ → atᵛ-≡ s refl) monoᵉ-r monoᵉ-e

  monoᵉ-c : (s : Sign) → (C : OCType Θ) → below (polₑ-c i s C) ≡ false
          → atᶜ Q s (C [ updᵉ i b ]ᶜ) C
  monoᵉ-c s (A ‼ ε) q =
    atᶜ-‼ s (monoᵉ-v s A (proj₁ d)) (monoᵉ-e s ε (proj₂ d))
    where d = below-∪ (polₑ-v i s A) (polₑ-e i s ε) q

-- Reading the folded analysis at one entry of a component

polsₑ-ordᵣ-∈ : ∀ {Θ} → (i : EVar Θ) → (l : List (RExp Θ × RExp Θ))
             → below (polsₑ-ordᵣ i l) ≡ false
             → ∀ {ρ ρ'} → (ρ , ρ') ∈ l
             → (below (polₑ-r i ⁺ ρ) ≡ false) × (below (polₑ-r i ⁻ ρ') ≡ false)
polsₑ-ordᵣ-∈ i ((ρ₀ , ρ₀') ∷ l) q (here refl) = proj₁ d₁ , proj₁ d₂
  where d₁ = below-∪ (polₑ-r i ⁺ ρ₀) (polₑ-r i ⁻ ρ₀' ∪ᴾ polsₑ-ordᵣ i l) q
        d₂ = below-∪ (polₑ-r i ⁻ ρ₀') (polsₑ-ordᵣ i l) (proj₂ d₁)
polsₑ-ordᵣ-∈ i ((ρ₀ , ρ₀') ∷ l) q (there m) = polsₑ-ordᵣ-∈ i l (proj₂ d₂) m
  where d₁ = below-∪ (polₑ-r i ⁺ ρ₀) (polₑ-r i ⁻ ρ₀' ∪ᴾ polsₑ-ordᵣ i l) q
        d₂ = below-∪ (polₑ-r i ⁻ ρ₀') (polsₑ-ordᵣ i l) (proj₂ d₁)

polsₑ-disj-∈ : ∀ {Θ} → (i : EVar Θ) → (l : List (OVType Θ × RExp Θ))
             → below (polsₑ-disj i l) ≡ false
             → ∀ {A ρ} → (A , ρ) ∈ l → below (polₑ-r i ⁺ ρ) ≡ false
polsₑ-disj-∈ i ((A₀ , ρ₀) ∷ l) q (here refl) =
  proj₁ (below-∪ (polₑ-r i ⁺ ρ₀) (polsₑ-disj i l) q)
polsₑ-disj-∈ i ((A₀ , ρ₀) ∷ l) q (there m)   =
  polsₑ-disj-∈ i l (proj₂ (below-∪ (polₑ-r i ⁺ ρ₀) (polsₑ-disj i l) q)) m

-- Booleans, each decided false

falses₂ : ∀ {a b : 𝔹} → Maybe ((a ≡ false) × (b ≡ false))
falses₂ {a} {b} with isFalse a | isFalse b
... | just p | just q = just (p , q)
... | _      | _      = nothing

falses : ∀ {a b c : 𝔹} → Maybe ((a ≡ false) × (b ≡ false) × (c ≡ false))
falses {a} with isFalse a | falses₂
... | just p | just qr = just (p , qr)
... | _      | _       = nothing

-- The orderings of resources that are not valid, through which an
-- effect unknown bounds nothing else

liveᵉ : ∀ {Θ} → EVar Θ → Hyps Θ → List (RExp Θ × RExp Θ)
liveᵉ {Θ} i Q = kept (Vⁱ.lives {Θ} i (ordᵣ Q))

-- The oracle of an effect unknown: it may decrease where it occurs on
-- no greater side of an ordering of resources that is not valid and
-- nowhere covariantly in the type, the value being free of it; and
-- increase where it occurs on no smaller side of such an ordering, in
-- no grade of a disjunction and nowhere contravariantly in the type

oracleᵉ : ∀ {Θ} → OCType Θ → Hyps Θ → (i : EVar Θ) → Vᵉ.Oracle {Θ} i
oracleᵉ C Q i = record
  { Lower  = λ b → (below (polₑ-e i ⁻ b) ≡ false) × (below (polsₑ-ordᵣ i (liveᵉ i Q)) ≡ false)
                 × (below (polₑ-c i ⁺ C) ≡ false)
  ; lower? = λ b → falses
  ; Raise  = λ b → (above (polsₑ-ordᵣ i (liveᵉ i Q)) ≡ false) × (above (polsₑ-disj i (disj Q)) ≡ false)
                 × (above (polₑ-c i ⁺ C) ≡ false)
  ; raise? = λ b → falses
  }

-- Lowering an effect unknown to the join of its bounds below
-- (`Values.lower`); the orderings bounding it are dropped, the rest
-- kept along `η`

stepᵉ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ)
      → Vᵉ.ByLower {Θ} i (oracleᵉ C Q i) (ordₑ Q) → Elim C Q
stepᵉ {Θ} C Q i (Vᵉ.byLower lw x xs e b to (cb , cR , cc)) =
  mkElim (C [ η₀ ]ᶜ) Q₀ η₀ (≡̂ᶜ-refl _) inst₀ keep₀
         (λ δ h → <:̂ᶜ-subst h (Monoᵉ.monoᵉ-c i b lowg ⁺ C cc))
  where
    η₀ : Subst Θ Θ
    η₀ = updᵉ i b

    Q₀ : Hyps Θ
    Q₀ = hyps (ets Q) (subᵥ Q)
              (map (mapᵖ (_[ η₀ ]ʳ)) (ordᵣ Q))
              (map (mapᵖ (_[ η₀ ]ᵉ)) (Vᵉ.rest lw))
              (map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q))

    lowg : Q ⊩ η₀ ≾ˢ idˢ
    lowg = ≾ˢ-idˡ (updᵉ-below i b idˢ
             (LowToₑ.Join.below i lw e to idˢ
               (λ {y} {y'} m → subst₂ (Q ⊩_≾̂ₑ_) (sym ([id]ᵉ y)) (sym ([id]ᵉ y')) (hypₑ m))))

    open Lowering {Q = Q} η₀ lowg (λ β → tvarₛ reflᵗᵛ)
    module K = Vᵉ.Keep {Θ} i (Q ⊩_≾̂ₑ_) ⊩≾̂ₑ-refl transₑ (λ ε → ε) (_[ η₀ ]ᵉ)
                       (λ {ε} → updᵉ-e i b ε) (λ p → ⊩-substₑ ∅ᴴ-⊩ᴴ p)
    module Kⁱ = Vⁱ.Keep {Θ} i (Q ⊩_≾̂ᵣ_) ⊩≾̂ᵣ-refl transᵣ (λ ρ → ρ) (_[ η₀ ]ʳ)
                        (λ {ρ} → updᵉ-r i b ρ) (λ p → ⊩-substᵣ ∅ᴴ-⊩ᴴ p)

    inst₀ : Q₀ ⊩ᴴ Q [ η₀ ]
    inst₀ = mk⊩ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m))
                 (λ m → hypᵣ (∈-map⁺ (mapᵖ (_[ η₀ ]ʳ)) m)) ordE
                 (λ m → hyp-ok₀ (∈-map⁺ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m))
      where
        ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q₀ ⊩ ε [ η₀ ]ᵉ ≾̂ₑ ε' [ η₀ ]ᵉ
        ordE {ε} m with Vᵉ.cls lw m
        ... | inj₁ (refl , mb) =
              subst (Q₀ ⊩ ε [ η₀ ]ᵉ ≾̂ₑ_) (trans (absᵉ-e i b b cb) (sym (updᵉ-hit i b)))
                    (LowToₑ.Join.above i lw e to η₀ mb)
        ... | inj₂ (inj₁ (refl , mc)) =
              subst₂ (λ y z → Q₀ ⊩ y ≾̂ₑ z) ([id]ᵉ (ε [ η₀ ]ᵉ)) (trans ([id]ᵉ b) (sym (updᵉ-hit i b)))
                     (⊩-substₑ {σ = idˢ} ∅ᴴ-⊩ᴴ (Vᵉ.lowTo-closes {Θ} i to mc))
        ... | inj₂ (inj₂ m') = hypₑ (∈-map⁺ (mapᵖ (_[ η₀ ]ᵉ)) m')

    keepR : ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ (_[ η₀ ]ʳ)) (ordᵣ Q) → Q ⊩ ρ ≾̂ᵣ ρ'
    keepR m with ∈-map⁻ (mapᵖ (_[ η₀ ]ʳ)) m
    ... | (ρ₀ , ρ₀') , m₀ , refl with which (Vⁱ.lives {Θ} i (ordᵣ Q)) m₀
    ...   | inj₁ v  = Kⁱ.valid-holds v
    ...   | inj₂ mk =
            transᵣ (lowʳ ρ₀)
                   (transᵣ (hypᵣ m₀)
                           (fixedʳ (absᵉ-r i b ρ₀' (proj₂ (polsₑ-ordᵣ-∈ i (liveᵉ i Q) cR mk)))))

    keepE : ∀ {ε ε'} → (ε , ε') ∈ map (mapᵖ (_[ η₀ ]ᵉ)) (Vᵉ.rest lw) → Q ⊩ ε ≾̂ₑ ε'
    keepE m with ∈-map⁻ (mapᵖ (_[ η₀ ]ᵉ)) m
    ... | (ε₀ , ε₀') , m₀ , refl =
          K.lowerR (Vᵉ.restR lw m₀) lowᵉ (hypₑ (Vᵉ.rest⊆ lw m₀))

    keep₀ : Q ⊨ᴴ Q₀
    keep₀ = mk⊨ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) keepR keepE keep-disj

stepᵉ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ)
       → vᵉ F i ≡ false → Maybe (Elimᶠ F C Q)
stepᵉ? {Θ} F C Q i o = Maybe.map at (Vᵉ.lower {Θ} i (oracleᵉ C Q i) (ordₑ Q))
  where
    at : Vᵉ.ByLower {Θ} i (oracleᵉ C Q i) (ordₑ Q) → Elimᶠ F C Q
    at bl@(Vᵉ.byLower _ _ _ _ b _ _) = stepᵉ C Q i bl , fixes-updᵉ i b o

fins : (n : ℕ) → List (Fin n)
fins zero    = []
fins (suc n) = zero ∷ map suc (fins n)

-- The first unknown of a list outside a set at which a step applies

first : ∀ {n} {X : Set} → (p : Fin n → 𝔹) → ((i : Fin n) → p i ≡ false → Maybe X)
      → List (Fin n) → Maybe X
first p f []       = nothing
first p f (i ∷ is) with p i in o
... | true  = first p f is
... | false with f i o
...   | just r  = just r
...   | nothing = first p f is

-- Effect expressions carry no resource unknown, so only the resource
-- expressions and the box grades of a type move.

absʳ-r : ∀ {Θ} → (i : RVar Θ) → (b : RExp Θ) → (ρ : RExp Θ)
       → below (polᵣ-r i ⁻ ρ) ≡ false → ρ [ updʳ i b ]ʳ ≡ ρ
absʳ-r i b (rvar j)   q = updʳ-miss i b j q
absʳ-r i b (rconst c) q = refl
absʳ-r i b (ρ ·̂ᵣ ρ')  q = cong₂ _·̂ᵣ_ (absʳ-r i b ρ (proj₁ d)) (absʳ-r i b ρ' (proj₂ d))
  where d = below-∪ (polᵣ-r i ⁻ ρ) (polᵣ-r i ⁻ ρ') q
absʳ-r i b (ρ ⊔̂ᵣ ρ')  q = cong₂ _⊔̂ᵣ_ (absʳ-r i b ρ (proj₁ d)) (absʳ-r i b ρ' (proj₂ d))
  where d = below-∪ (polᵣ-r i ⁻ ρ) (polᵣ-r i ⁻ ρ') q
absʳ-r i b ∣ ε ∣̂ᵉ     q = cong ∣_∣̂ᵉ (updʳ-e i b ε)

-- Lowering a resource unknown lowers whatever has no occurrence of it
-- below

module Monoʳ {Θ : Scope} {Q : Hyps Θ} (i : RVar Θ) (b : RExp Θ)
             (lowg : Q ⊩ updʳ i b ≾ˢ idˢ) where

  open Lowering {Q = Q} (updʳ i b) lowg (λ β → tvarₛ reflᵗᵛ)

  monoʳ-r : (s : Sign) → (ρ : RExp Θ) → below (polᵣ-r i s ρ) ≡ false
          → atʳ Q s (ρ [ updʳ i b ]ʳ) ρ
  monoʳ-r ⁺ ρ q = lowʳ ρ
  monoʳ-r ⁻ ρ q = atʳ-≡ ⁻ (absʳ-r i b ρ q)

  monoʳ-v : (s : Sign) → (A : OVType Θ) → below (polᵣ-v i s A) ≡ false
          → atᵛ Q s (A [ updʳ i b ]ᵛ) A
  monoʳ-v = Lift.lift (updʳ i b) (λ p → below p ≡ false) below-∪
              (λ _ _ → noᴾ) (polᵣ-r i) (λ _ _ → noᴾ) (λ s α _ → atᵛ-≡ s refl) monoʳ-r
              (λ s ε _ → atᵉ-≡ s (updʳ-e i b ε))

  monoʳ-c : (s : Sign) → (C : OCType Θ) → below (polᵣ-c i s C) ≡ false
          → atᶜ Q s (C [ updʳ i b ]ᶜ) C
  monoʳ-c s (A ‼ ε) q = atᶜ-‼ s (monoʳ-v s A q) (atᵉ-≡ s (updʳ-e i b ε))

polsᵣ-disj-∈ : ∀ {Θ} → (i : RVar Θ) → (l : List (OVType Θ × RExp Θ))
             → below (polsᵣ-disj i l) ≡ false
             → ∀ {A ρ} → (A , ρ) ∈ l → below (polᵣ-r i ⁺ ρ) ≡ false
polsᵣ-disj-∈ i ((A₀ , ρ₀) ∷ l) q (here refl) =
  proj₁ (below-∪ (polᵣ-r i ⁺ ρ₀) (polsᵣ-disj i l) q)
polsᵣ-disj-∈ i ((A₀ , ρ₀) ∷ l) q (there m)   =
  polsᵣ-disj-∈ i l (proj₂ (below-∪ (polᵣ-r i ⁺ ρ₀) (polsᵣ-disj i l) q)) m

-- The oracle of a resource unknown: it may decrease where it occurs
-- nowhere covariantly in the type, the value being free of it, and
-- increase where it occurs in no grade of a disjunction and nowhere
-- contravariantly in the type

oracleʳ : ∀ {Θ} → OCType Θ → Hyps Θ → (i : RVar Θ) → Vʳ.Oracle {Θ} i
oracleʳ C Q i = record
  { Lower  = λ b → (below (polᵣ-r i ⁻ b) ≡ false) × (below (polᵣ-c i ⁺ C) ≡ false)
  ; lower? = λ b → falses₂
  ; Raise  = λ b → (above (polsᵣ-disj i (disj Q)) ≡ false) × (above (polᵣ-c i ⁺ C) ≡ false)
  ; raise? = λ b → falses₂
  }

stepʳ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ)
      → Vʳ.ByLower {Θ} i (oracleʳ C Q i) (ordᵣ Q) → Elim C Q
stepʳ {Θ} C Q i (Vʳ.byLower lw x xs e b to (cb , cc)) =
  mkElim (C [ η₀ ]ᶜ) Q₀ η₀ (≡̂ᶜ-refl _) inst₀ keep₀
         (λ δ h → <:̂ᶜ-subst h (Monoʳ.monoʳ-c i b lowg ⁺ C cc))
  where
    η₀ : Subst Θ Θ
    η₀ = updʳ i b

    Q₀ : Hyps Θ
    Q₀ = hyps (ets Q) (subᵥ Q)
              (map (mapᵖ (_[ η₀ ]ʳ)) (Vʳ.rest lw))
              (map (mapᵖ (_[ η₀ ]ᵉ)) (ordₑ Q))
              (map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q))

    lowg : Q ⊩ η₀ ≾ˢ idˢ
    lowg = ≾ˢ-idˡ (updʳ-below i b idˢ
             (LowToᵣ.Join.below i lw e to idˢ
               (λ {y} {y'} m → subst₂ (Q ⊩_≾̂ᵣ_) (sym ([id]ʳ y)) (sym ([id]ʳ y')) (hypᵣ m))))

    open Lowering {Q = Q} η₀ lowg (λ β → tvarₛ reflᵗᵛ)
    module K = Vʳ.Keep {Θ} i (Q ⊩_≾̂ᵣ_) ⊩≾̂ᵣ-refl transᵣ (λ ρ → ρ) (_[ η₀ ]ʳ)
                       (λ {ρ} → updʳ-r i b ρ) (λ p → ⊩-substᵣ ∅ᴴ-⊩ᴴ p)

    inst₀ : Q₀ ⊩ᴴ Q [ η₀ ]
    inst₀ = mk⊩ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) ordR
                 (λ m → hypₑ (∈-map⁺ (mapᵖ (_[ η₀ ]ᵉ)) m))
                 (λ m → hyp-ok₀ (∈-map⁺ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m))
      where
        ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q₀ ⊩ ρ [ η₀ ]ʳ ≾̂ᵣ ρ' [ η₀ ]ʳ
        ordR {ρ} m with Vʳ.cls lw m
        ... | inj₁ (refl , mb) =
              subst (Q₀ ⊩ ρ [ η₀ ]ʳ ≾̂ᵣ_) (trans (absʳ-r i b b cb) (sym (updʳ-hit i b)))
                    (LowToᵣ.Join.above i lw e to η₀ mb)
        ... | inj₂ (inj₁ (refl , mc)) =
              subst₂ (λ y z → Q₀ ⊩ y ≾̂ᵣ z) ([id]ʳ (ρ [ η₀ ]ʳ)) (trans ([id]ʳ b) (sym (updʳ-hit i b)))
                     (⊩-substᵣ {σ = idˢ} ∅ᴴ-⊩ᴴ (Vʳ.lowTo-closes {Θ} i to mc))
        ... | inj₂ (inj₂ m') = hypᵣ (∈-map⁺ (mapᵖ (_[ η₀ ]ʳ)) m')

    keepR : ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ (_[ η₀ ]ʳ)) (Vʳ.rest lw) → Q ⊩ ρ ≾̂ᵣ ρ'
    keepR m with ∈-map⁻ (mapᵖ (_[ η₀ ]ʳ)) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
          K.lowerR (Vʳ.restR lw m₀) lowʳ (hypᵣ (Vʳ.rest⊆ lw m₀))

    keep₀ : Q ⊨ᴴ Q₀
    keep₀ = mk⊨ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) keepR
                 (keep-ordᵉ (ordₑ Q) (λ m → m)
                            (λ {ε} {ε'} m → fixedᵉ (updʳ-e i b ε')))
                 keep-disj

stepʳ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ)
       → vʳ F i ≡ false → Maybe (Elimᶠ F C Q)
stepʳ? {Θ} F C Q i o = Maybe.map at (Vʳ.lower {Θ} i (oracleʳ C Q i) (ordᵣ Q))
  where
    at : Vʳ.ByLower {Θ} i (oracleʳ C Q i) (ordᵣ Q) → Elimᶠ F C Q
    at bl@(Vʳ.byLower _ _ _ _ b _ _) = stepʳ C Q i bl , fixes-updʳ i b o

-- Merging: a lowering whose value is a single unknown

mergeᵉ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ)
        → vᵉ F i ≡ false → Maybe (Elimᶠ F C Q)
mergeᵉ? {Θ} F C Q i o with Vᵉ.lower {Θ} i (oracleᵉ C Q i) (ordₑ Q)
... | just bl@(Vᵉ.byLower _ _ _ _ b@(evar _) _ _) = just (stepᵉ C Q i bl , fixes-updᵉ i b o)
... | _ = nothing

mergeʳ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ)
        → vʳ F i ≡ false → Maybe (Elimᶠ F C Q)
mergeʳ? {Θ} F C Q i o with Vʳ.lower {Θ} i (oracleʳ C Q i) (ordᵣ Q)
... | just bl@(Vʳ.byLower _ _ _ _ b@(rvar _) _ _) = just (stepʳ C Q i bl , fixes-updʳ i b o)
... | _ = nothing

------------------------------------------------------------------------
-- The dual steps: an unknown on no left side but against its bounds
-- above, and nowhere covariantly in the type, is raised to the bound
-- decided below the others. Raising it raises every right side and
-- every contravariant position.

above-∪ : (p q : Pol) → above (p ∪ᴾ q) ≡ false
        → (above p ≡ false) × (above q ≡ false)
above-∪ p q e = ∨-false (above p) (above q) e

-- An unknown on no left side of an expression is absent from it

absᵉ-e⁺ : ∀ {Θ} → (i : EVar Θ) → (b : EExp Θ) → (ε : EExp Θ)
        → above (polₑ-e i ⁺ ε) ≡ false → ε [ updᵉ i b ]ᵉ ≡ ε
absᵉ-e⁺ i b (evar j)   q = updᵉ-miss i b j q
absᵉ-e⁺ i b (econst c) q = refl
absᵉ-e⁺ i b (ε ·̂ₑ ε')  q = cong₂ _·̂ₑ_ (absᵉ-e⁺ i b ε (proj₁ d)) (absᵉ-e⁺ i b ε' (proj₂ d))
  where d = above-∪ (polₑ-e i ⁺ ε) (polₑ-e i ⁺ ε') q
absᵉ-e⁺ i b (ε ⊔̂ₑ ε')  q = cong₂ _⊔̂ₑ_ (absᵉ-e⁺ i b ε (proj₁ d)) (absᵉ-e⁺ i b ε' (proj₂ d))
  where d = above-∪ (polₑ-e i ⁺ ε) (polₑ-e i ⁺ ε') q

absᵉ-r⁺ : ∀ {Θ} → (i : EVar Θ) → (b : EExp Θ) → (ρ : RExp Θ)
        → above (polₑ-r i ⁺ ρ) ≡ false → ρ [ updᵉ i b ]ʳ ≡ ρ
absᵉ-r⁺ i b (rvar j)   q = refl
absᵉ-r⁺ i b (rconst c) q = refl
absᵉ-r⁺ i b (ρ ·̂ᵣ ρ')  q = cong₂ _·̂ᵣ_ (absᵉ-r⁺ i b ρ (proj₁ d)) (absᵉ-r⁺ i b ρ' (proj₂ d))
  where d = above-∪ (polₑ-r i ⁺ ρ) (polₑ-r i ⁺ ρ') q
absᵉ-r⁺ i b (ρ ⊔̂ᵣ ρ')  q = cong₂ _⊔̂ᵣ_ (absᵉ-r⁺ i b ρ (proj₁ d)) (absᵉ-r⁺ i b ρ' (proj₂ d))
  where d = above-∪ (polₑ-r i ⁺ ρ) (polₑ-r i ⁺ ρ') q
absᵉ-r⁺ i b ∣ ε ∣̂ᵉ     q = cong ∣_∣̂ᵉ (absᵉ-e⁺ i b ε q)

absʳ-r⁺ : ∀ {Θ} → (i : RVar Θ) → (b : RExp Θ) → (ρ : RExp Θ)
        → above (polᵣ-r i ⁺ ρ) ≡ false → ρ [ updʳ i b ]ʳ ≡ ρ
absʳ-r⁺ i b (rvar j)   q = updʳ-miss i b j q
absʳ-r⁺ i b (rconst c) q = refl
absʳ-r⁺ i b (ρ ·̂ᵣ ρ')  q = cong₂ _·̂ᵣ_ (absʳ-r⁺ i b ρ (proj₁ d)) (absʳ-r⁺ i b ρ' (proj₂ d))
  where d = above-∪ (polᵣ-r i ⁺ ρ) (polᵣ-r i ⁺ ρ') q
absʳ-r⁺ i b (ρ ⊔̂ᵣ ρ')  q = cong₂ _⊔̂ᵣ_ (absʳ-r⁺ i b ρ (proj₁ d)) (absʳ-r⁺ i b ρ' (proj₂ d))
  where d = above-∪ (polᵣ-r i ⁺ ρ) (polᵣ-r i ⁺ ρ') q
absʳ-r⁺ i b ∣ ε ∣̂ᵉ     q = cong ∣_∣̂ᵉ (updʳ-e i b ε)

-- Raising an unknown raises whatever has no occurrence of it above

module Raise {Θ : Scope} {Q : Hyps Θ} (η₀ : Subst Θ Θ) (hig : Q ⊩ idˢ ≾ˢ η₀) where

  upʳ : (ρ : RExp Θ) → Q ⊩ ρ ≾̂ᵣ ρ [ η₀ ]ʳ
  upʳ ρ = subst (λ x → Q ⊩ x ≾̂ᵣ ρ [ η₀ ]ʳ) ([id]ʳ ρ) (mono-substᵣ hig ρ)

  upᵉ : (ε : EExp Θ) → Q ⊩ ε ≾̂ₑ ε [ η₀ ]ᵉ
  upᵉ ε = subst (λ x → Q ⊩ x ≾̂ₑ ε [ η₀ ]ᵉ) ([id]ᵉ ε) (mono-substₑ hig ε)

module Raiseᵉ {Θ : Scope} {Q : Hyps Θ} (i : EVar Θ) (b : EExp Θ)
              (hig : Q ⊩ idˢ ≾ˢ updᵉ i b) where

  open Raise {Q = Q} (updᵉ i b) hig

  raiseᵉ-e : (s : Sign) → (ε : EExp Θ) → above (polₑ-e i s ε) ≡ false
           → atᵉ Q s (ε [ updᵉ i b ]ᵉ) ε
  raiseᵉ-e ⁺ ε q = atᵉ-≡ ⁺ (absᵉ-e⁺ i b ε q)
  raiseᵉ-e ⁻ ε q = upᵉ ε

  raiseᵉ-r : (s : Sign) → (ρ : RExp Θ) → above (polₑ-r i s ρ) ≡ false
           → atʳ Q s (ρ [ updᵉ i b ]ʳ) ρ
  raiseᵉ-r ⁺ ρ q = atʳ-≡ ⁺ (absᵉ-r⁺ i b ρ q)
  raiseᵉ-r ⁻ ρ q = upʳ ρ

  raiseᵉ-v : (s : Sign) → (A : OVType Θ) → above (polₑ-v i s A) ≡ false
           → atᵛ Q s (A [ updᵉ i b ]ᵛ) A
  raiseᵉ-v = Lift.lift (updᵉ i b) (λ p → above p ≡ false) above-∪
               (λ _ _ → noᴾ) (polₑ-r i) (polₑ-e i) (λ s α _ → atᵛ-≡ s refl) raiseᵉ-r raiseᵉ-e

  raiseᵉ-c : (s : Sign) → (C : OCType Θ) → above (polₑ-c i s C) ≡ false
           → atᶜ Q s (C [ updᵉ i b ]ᶜ) C
  raiseᵉ-c s (A ‼ ε) q =
    atᶜ-‼ s (raiseᵉ-v s A (proj₁ d)) (raiseᵉ-e s ε (proj₂ d))
    where d = above-∪ (polₑ-v i s A) (polₑ-e i s ε) q

module Raiseʳ {Θ : Scope} {Q : Hyps Θ} (i : RVar Θ) (b : RExp Θ)
              (hig : Q ⊩ idˢ ≾ˢ updʳ i b) where

  open Raise {Q = Q} (updʳ i b) hig

  raiseʳ-r : (s : Sign) → (ρ : RExp Θ) → above (polᵣ-r i s ρ) ≡ false
           → atʳ Q s (ρ [ updʳ i b ]ʳ) ρ
  raiseʳ-r ⁺ ρ q = atʳ-≡ ⁺ (absʳ-r⁺ i b ρ q)
  raiseʳ-r ⁻ ρ q = upʳ ρ

  raiseʳ-v : (s : Sign) → (A : OVType Θ) → above (polᵣ-v i s A) ≡ false
           → atᵛ Q s (A [ updʳ i b ]ᵛ) A
  raiseʳ-v = Lift.lift (updʳ i b) (λ p → above p ≡ false) above-∪
               (λ _ _ → noᴾ) (polᵣ-r i) (λ _ _ → noᴾ) (λ s α _ → atᵛ-≡ s refl) raiseʳ-r
               (λ s ε _ → atᵉ-≡ s (updʳ-e i b ε))

  raiseʳ-c : (s : Sign) → (C : OCType Θ) → above (polᵣ-c i s C) ≡ false
           → atᶜ Q s (C [ updʳ i b ]ᶜ) C
  raiseʳ-c s (A ‼ ε) q = atᶜ-‼ s (raiseʳ-v s A q) (atᵉ-≡ s (updʳ-e i b ε))

-- Reading the folded analysis at the left side of an entry

polsₑ-ordᵣ-∈⁺ : ∀ {Θ} → (i : EVar Θ) → (l : List (RExp Θ × RExp Θ))
              → above (polsₑ-ordᵣ i l) ≡ false
              → ∀ {ρ ρ'} → (ρ , ρ') ∈ l → above (polₑ-r i ⁺ ρ) ≡ false
polsₑ-ordᵣ-∈⁺ i ((ρ₀ , ρ₀') ∷ l) q (here refl) = proj₁ d₁
  where d₁ = above-∪ (polₑ-r i ⁺ ρ₀) (polₑ-r i ⁻ ρ₀' ∪ᴾ polsₑ-ordᵣ i l) q
polsₑ-ordᵣ-∈⁺ i ((ρ₀ , ρ₀') ∷ l) q (there m) = polsₑ-ordᵣ-∈⁺ i l (proj₂ d₂) m
  where d₁ = above-∪ (polₑ-r i ⁺ ρ₀) (polₑ-r i ⁻ ρ₀' ∪ᴾ polsₑ-ordᵣ i l) q
        d₂ = above-∪ (polₑ-r i ⁻ ρ₀') (polsₑ-ordᵣ i l) (proj₂ d₁)

polsₑ-disj-∈⁺ : ∀ {Θ} → (i : EVar Θ) → (l : List (OVType Θ × RExp Θ))
              → above (polsₑ-disj i l) ≡ false
              → ∀ {A ρ} → (A , ρ) ∈ l → above (polₑ-r i ⁺ ρ) ≡ false
polsₑ-disj-∈⁺ i ((A₀ , ρ₀) ∷ l) q (here refl) =
  proj₁ (above-∪ (polₑ-r i ⁺ ρ₀) (polsₑ-disj i l) q)
polsₑ-disj-∈⁺ i ((A₀ , ρ₀) ∷ l) q (there m)   =
  polsₑ-disj-∈⁺ i l (proj₂ (above-∪ (polₑ-r i ⁺ ρ₀) (polsₑ-disj i l) q)) m

polsᵣ-disj-∈⁺ : ∀ {Θ} → (i : RVar Θ) → (l : List (OVType Θ × RExp Θ))
              → above (polsᵣ-disj i l) ≡ false
              → ∀ {A ρ} → (A , ρ) ∈ l → above (polᵣ-r i ⁺ ρ) ≡ false
polsᵣ-disj-∈⁺ i ((A₀ , ρ₀) ∷ l) q (here refl) =
  proj₁ (above-∪ (polᵣ-r i ⁺ ρ₀) (polsᵣ-disj i l) q)
polsᵣ-disj-∈⁺ i ((A₀ , ρ₀) ∷ l) q (there m)   =
  polsᵣ-disj-∈⁺ i l (proj₂ (above-∪ (polᵣ-r i ⁺ ρ₀) (polsᵣ-disj i l) q)) m

-- The disjunctions kept at each instance: the grade does not move, and
-- eternality reads only the skeleton

keep-disj⁺ : ∀ {Θ} {Q : Hyps Θ} → (η₀ : Subst Θ Θ) → (∀ β → sTy η₀ β ≡ tvar β)
           → (∀ {A ρ} → (A , ρ) ∈ disj Q → ρ [ η₀ ]ʳ ≡ ρ)
           → (δ : Subst Θ ∅ˢ) → ∅ᴴ ⊩ᴴ Q [ δ ]
           → ∀ {A ρ} → (A , ρ) ∈ map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q)
           → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ)
keep-disj⁺ {Q = Q} η₀ tv fr δ h m with ∈-map⁻ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m
... | (A₀ , ρ₀) , m₀ , refl =
      VarOK-∅-mono et (⊩-substᵣ h (atʳ-≡ ⁺ (fr m₀))) (⊩disj h m₀)
  where
    lowt : ∀ β → Q ∣ sTy η₀ β <:̂ᵛ tvar β
    lowt β = subst (λ x → Q ∣ x <:̂ᵛ tvar β) (sym (tv β)) (tvarₛ reflᵗᵛ)

    et : ∅ᴴ ⊩ᴱ A₀ [ δ ]ᵛ → ∅ᴴ ⊩ᴱ A₀ [ η₀ ]ᵛ [ δ ]ᵛ
    et e = subst (∅ᴴ ⊩ᴱ_) (sym ([⨟]ᵛ A₀ η₀ δ))
                 (⊩ᴱ-<:ˢ {σ = η₀ ⨟ˢ δ} {τ = δ} (λ β → <:̂ᵛ-subst h (lowt β)) A₀ e)

-- Raising an effect unknown to its bound above (`Values.raise`): the
-- orderings with it on the left are dropped, each then decided from no
-- hypotheses; the rest are kept along `η`

upᵉ-step : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ)
         → Vᵉ.ByRaise {Θ} i (oracleᵉ C Q i) (ordₑ Q) → Elim C Q
upᵉ-step {Θ} C Q i (Vᵉ.byRaise up (cR , cD , cc)) =
  mkElim (C [ η₀ ]ᶜ) Q₀ η₀ (≡̂ᶜ-refl _) inst₀ keep₀
         (λ δ h → <:̂ᶜ-subst h (Raiseᵉ.raiseᵉ-c i b hig ⁺ C cc))
  where
    b : EExp Θ
    b = Vᵉ.cap up

    η₀ : Subst Θ Θ
    η₀ = updᵉ i b

    rest = Vᵉ.restᵘ (Vᵉ.capd up)

    Q₀ : Hyps Θ
    Q₀ = hyps (ets Q) (subᵥ Q)
              (map (mapᵖ (_[ η₀ ]ʳ)) (ordᵣ Q))
              (map (mapᵖ (_[ η₀ ]ᵉ)) rest)
              (map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q))

    hig : Q ⊩ idˢ ≾ˢ η₀
    hig = ≾ˢ-idʳ (updᵉ-above i b idˢ
            (subst (λ y → Q ⊩ evar i ≾̂ₑ y) (sym ([id]ᵉ b)) (hypₑ (Vᵉ.srcᵘ up))))

    open Raise {Q = Q} η₀ hig
    module K = Vᵉ.Keep {Θ} i (Q ⊩_≾̂ₑ_) ⊩≾̂ₑ-refl transₑ (λ ε → ε) (_[ η₀ ]ᵉ)
                       (λ {ε} → updᵉ-e i b ε) (λ p → ⊩-substₑ ∅ᴴ-⊩ᴴ p)
    module Kⁱ = Vⁱ.Keep {Θ} i (Q ⊩_≾̂ᵣ_) ⊩≾̂ᵣ-refl transᵣ (λ ρ → ρ) (_[ η₀ ]ʳ)
                        (λ {ρ} → updᵉ-r i b ρ) (λ p → ⊩-substᵣ ∅ᴴ-⊩ᴴ p)

    -- the value, where it stands for the unknown
    hit : sE η₀ i ≡ b [ η₀ ]ᵉ
    hit = trans (updᵉ-hit i b) (sym (updᵉ-e i b b (Vᵉ.capF up)))

    inst₀ : Q₀ ⊩ᴴ Q [ η₀ ]
    inst₀ = mk⊩ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m))
                 (λ m → hypᵣ (∈-map⁺ (mapᵖ (_[ η₀ ]ʳ)) m)) ordE
                 (λ m → hyp-ok₀ (∈-map⁺ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m))
      where
        ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q₀ ⊩ ε [ η₀ ]ᵉ ≾̂ₑ ε' [ η₀ ]ᵉ
        ordE {ε' = ε'} m with Vᵉ.clsᵘ (Vᵉ.capd up) m
        ... | inj₁ (refl , inj₁ refl) = subst (λ z → Q₀ ⊩ z ≾̂ₑ b [ η₀ ]ᵉ) (sym hit) ⊩≾̂ₑ-refl
        ... | inj₁ (refl , inj₂ p)    =
              subst (λ z → Q₀ ⊩ z ≾̂ₑ ε' [ η₀ ]ᵉ) (sym hit) (⊩-substₑ ∅ᴴ-⊩ᴴ p)
        ... | inj₂ m'                 = hypₑ (∈-map⁺ (mapᵖ (_[ η₀ ]ᵉ)) m')

    keepR : ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ (_[ η₀ ]ʳ)) (ordᵣ Q) → Q ⊩ ρ ≾̂ᵣ ρ'
    keepR m with ∈-map⁻ (mapᵖ (_[ η₀ ]ʳ)) m
    ... | (ρ₀ , ρ₀') , m₀ , refl with which (Vⁱ.lives {Θ} i (ordᵣ Q)) m₀
    ...   | inj₁ v  = Kⁱ.valid-holds v
    ...   | inj₂ mk =
            transᵣ (atʳ-≡ ⁺ (absᵉ-r⁺ i b ρ₀ (polsₑ-ordᵣ-∈⁺ i (liveᵉ i Q) cR mk)))
                   (transᵣ (hypᵣ m₀) (upʳ ρ₀'))

    keepE : ∀ {ε ε'} → (ε , ε') ∈ map (mapᵖ (_[ η₀ ]ᵉ)) rest → Q ⊩ ε ≾̂ₑ ε'
    keepE m with ∈-map⁻ (mapᵖ (_[ η₀ ]ᵉ)) m
    ... | (ε₀ , ε₀') , m₀ , refl =
          K.raiseL (Vᵉ.restL (Vᵉ.capd up) m₀) upᵉ (hypₑ (Vᵉ.rest⊆ᵘ (Vᵉ.capd up) m₀))

    keep₀ : Q ⊨ᴴ Q₀
    keep₀ = mk⊨ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) keepR keepE
                 (keep-disj⁺ η₀ (λ β → refl)
                    (λ {A} {ρ} m → absᵉ-r⁺ i b ρ (polsₑ-disj-∈⁺ i (disj Q) cD m)))

upʳ-step : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ)
         → Vʳ.ByRaise {Θ} i (oracleʳ C Q i) (ordᵣ Q) → Elim C Q
upʳ-step {Θ} C Q i (Vʳ.byRaise up (cD , cc)) =
  mkElim (C [ η₀ ]ᶜ) Q₀ η₀ (≡̂ᶜ-refl _) inst₀ keep₀
         (λ δ h → <:̂ᶜ-subst h (Raiseʳ.raiseʳ-c i b hig ⁺ C cc))
  where
    b : RExp Θ
    b = Vʳ.cap up

    η₀ : Subst Θ Θ
    η₀ = updʳ i b

    rest = Vʳ.restᵘ (Vʳ.capd up)

    Q₀ : Hyps Θ
    Q₀ = hyps (ets Q) (subᵥ Q)
              (map (mapᵖ (_[ η₀ ]ʳ)) rest)
              (map (mapᵖ (_[ η₀ ]ᵉ)) (ordₑ Q))
              (map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q))

    hig : Q ⊩ idˢ ≾ˢ η₀
    hig = ≾ˢ-idʳ (updʳ-above i b idˢ
            (subst (λ y → Q ⊩ rvar i ≾̂ᵣ y) (sym ([id]ʳ b)) (hypᵣ (Vʳ.srcᵘ up))))

    open Raise {Q = Q} η₀ hig
    module K = Vʳ.Keep {Θ} i (Q ⊩_≾̂ᵣ_) ⊩≾̂ᵣ-refl transᵣ (λ ρ → ρ) (_[ η₀ ]ʳ)
                       (λ {ρ} → updʳ-r i b ρ) (λ p → ⊩-substᵣ ∅ᴴ-⊩ᴴ p)

    hit : sR η₀ i ≡ b [ η₀ ]ʳ
    hit = trans (updʳ-hit i b) (sym (updʳ-r i b b (Vʳ.capF up)))

    inst₀ : Q₀ ⊩ᴴ Q [ η₀ ]
    inst₀ = mk⊩ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) ordR
                 (λ m → hypₑ (∈-map⁺ (mapᵖ (_[ η₀ ]ᵉ)) m))
                 (λ m → hyp-ok₀ (∈-map⁺ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m))
      where
        ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q₀ ⊩ ρ [ η₀ ]ʳ ≾̂ᵣ ρ' [ η₀ ]ʳ
        ordR {ρ' = ρ'} m with Vʳ.clsᵘ (Vʳ.capd up) m
        ... | inj₁ (refl , inj₁ refl) = subst (λ z → Q₀ ⊩ z ≾̂ᵣ b [ η₀ ]ʳ) (sym hit) ⊩≾̂ᵣ-refl
        ... | inj₁ (refl , inj₂ p)    =
              subst (λ z → Q₀ ⊩ z ≾̂ᵣ ρ' [ η₀ ]ʳ) (sym hit) (⊩-substᵣ ∅ᴴ-⊩ᴴ p)
        ... | inj₂ m'                 = hypᵣ (∈-map⁺ (mapᵖ (_[ η₀ ]ʳ)) m')

    keepR : ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ (_[ η₀ ]ʳ)) rest → Q ⊩ ρ ≾̂ᵣ ρ'
    keepR m with ∈-map⁻ (mapᵖ (_[ η₀ ]ʳ)) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
          K.raiseL (Vʳ.restL (Vʳ.capd up) m₀) upʳ (hypᵣ (Vʳ.rest⊆ᵘ (Vʳ.capd up) m₀))

    keepE : ∀ {ε ε'} → (ε , ε') ∈ map (mapᵖ (_[ η₀ ]ᵉ)) (ordₑ Q) → Q ⊩ ε ≾̂ₑ ε'
    keepE m with ∈-map⁻ (mapᵖ (_[ η₀ ]ᵉ)) m
    ... | (ε₀ , ε₀') , m₀ , refl =
          subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym (updʳ-e i b ε₀)) (sym (updʳ-e i b ε₀')) (hypₑ m₀)

    keep₀ : Q ⊨ᴴ Q₀
    keep₀ = mk⊨ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) keepR keepE
                 (keep-disj⁺ η₀ (λ β → refl)
                    (λ {A} {ρ} m → absʳ-r⁺ i b ρ (polsᵣ-disj-∈⁺ i (disj Q) cD m)))

-- The searches

upᵉ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ)
     → vᵉ F i ≡ false → Maybe (Elimᶠ F C Q)
upᵉ? {Θ} F C Q i o = Maybe.map at (Vᵉ.raise {Θ} i (oracleᵉ C Q i) (ordₑ Q))
  where
    at : Vᵉ.ByRaise {Θ} i (oracleᵉ C Q i) (ordₑ Q) → Elimᶠ F C Q
    at br@(Vᵉ.byRaise up _) = upᵉ-step C Q i br , fixes-updᵉ i (Vᵉ.cap up) o

upʳ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ)
     → vʳ F i ≡ false → Maybe (Elimᶠ F C Q)
upʳ? {Θ} F C Q i o = Maybe.map at (Vʳ.raise {Θ} i (oracleʳ C Q i) (ordᵣ Q))
  where
    at : Vʳ.ByRaise {Θ} i (oracleʳ C Q i) (ordᵣ Q) → Elimᶠ F C Q
    at br@(Vʳ.byRaise up _) = upʳ-step C Q i br , fixes-updʳ i (Vʳ.cap up) o

-- The bound of a type variable is another type variable, so the
-- substitution acts on the eternality and subtyping atoms too: a
-- renaming of the type variables, fixing every grade unknown

idᶠ : ∀ {n} → Fin n → Fin n
idᶠ β = β

renᵗ : ∀ {Θ} → (TyVar Θ → TyVar Θ) → Subst Θ Θ
renᵗ f = sub (λ β → tvar (f β)) rvar evar

updᵗ : ∀ {Θ} → TyVar Θ → TyVar Θ → Subst Θ Θ
updᵗ α γ = renᵗ (upd α γ idᶠ)

fixes-updᵗ : ∀ {Θ} {F : Vars Θ} → (α γ : TyVar Θ) → vᵗ F α ≡ false → Fixes F (updᵗ α γ)
fixes-updᵗ {F = F} α γ o =
  mkFixes (λ β h → cong tvar (upd-≢ α β γ idᶠ (⌊⌋-false (outside (vᵗ F) o h))))
          (λ _ _ → refl) (λ _ _ → refl)

fixᵗ-e : ∀ {Θ} → (f : TyVar Θ → TyVar Θ) → (ε : EExp Θ) → ε [ renᵗ f ]ᵉ ≡ ε
fixᵗ-e f (evar j)   = refl
fixᵗ-e f (econst c) = refl
fixᵗ-e f (ε ·̂ₑ ε')  = cong₂ _·̂ₑ_ (fixᵗ-e f ε) (fixᵗ-e f ε')
fixᵗ-e f (ε ⊔̂ₑ ε')  = cong₂ _⊔̂ₑ_ (fixᵗ-e f ε) (fixᵗ-e f ε')

fixᵗ-r : ∀ {Θ} → (f : TyVar Θ → TyVar Θ) → (ρ : RExp Θ) → ρ [ renᵗ f ]ʳ ≡ ρ
fixᵗ-r f (rvar j)   = refl
fixᵗ-r f (rconst c) = refl
fixᵗ-r f (ρ ·̂ᵣ ρ')  = cong₂ _·̂ᵣ_ (fixᵗ-r f ρ) (fixᵗ-r f ρ')
fixᵗ-r f (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔̂ᵣ_ (fixᵗ-r f ρ) (fixᵗ-r f ρ')
fixᵗ-r f ∣ ε ∣̂ᵉ     = cong ∣_∣̂ᵉ (fixᵗ-e f ε)

-- Lowering a type variable to a variable below it lowers every type
-- with no occurrence of it below

module Monoᵗ {Θ : Scope} {Q : Hyps Θ} (α γ : TyVar Θ) (le : (γ , α) ∈ subᵥ Q) where

  lowt : ∀ β → Q ∣ sTy (updᵗ α γ) β <:̂ᵛ tvar β
  lowt β with α ≟ᶠ β
  ... | yes refl = subst (λ x → Q ∣ tvar x <:̂ᵛ tvar α) (sym (upd-≡ α γ idᶠ))
                         (tvarₛ (hypᵗᵛ le))
  ... | no  ¬p   = subst (λ x → Q ∣ tvar x <:̂ᵛ tvar β) (sym (upd-≢ α β γ idᶠ ¬p))
                         (tvarₛ reflᵗᵛ)

  lowg : Q ⊩ updᵗ α γ ≾ˢ idˢ
  lowg = mk≾ˢ (λ _ → ⊩≾̂ᵣ-refl) (λ _ → ⊩≾̂ₑ-refl)

  monoᵗ-v : (s : Sign) → (A : OVType Θ) → below (polₜ-v α s A) ≡ false
          → atᵛ Q s (A [ updᵗ α γ ]ᵛ) A
  monoᵗ-v = Lift.lift (updᵗ α γ) (λ p → below p ≡ false) below-∪
              (λ s β → atˢ s ⌊ α ≟ᶠ β ⌋) (λ _ _ → noᴾ) (λ _ _ → noᴾ) tv
              (λ s ρ _ → atʳ-≡ s (fixᵗ-r (upd α γ idᶠ) ρ)) (λ s ε _ → atᵉ-≡ s (fixᵗ-e (upd α γ idᶠ) ε))
    where
      tv : ∀ s β → below (atˢ s ⌊ α ≟ᶠ β ⌋) ≡ false → atᵛ Q s (sTy (updᵗ α γ) β) (tvar β)
      tv ⁺ β q = lowt β
      tv ⁻ β q = atᵛ-≡ ⁻ (cong tvar (upd-≢ α β γ idᶠ (⌊⌋-false q)))

  monoᵗ-c : (s : Sign) → (C : OCType Θ) → below (polₜ-c α s C) ≡ false
          → atᶜ Q s (C [ updᵗ α γ ]ᶜ) C
  monoᵗ-c s (A ‼ ε) q = atᶜ-‼ s (monoᵗ-v s A q) (atᵉ-≡ s (fixᵗ-e (upd α γ idᶠ) ε))

polsₜ-sub-∈ : ∀ {n} → (α : Fin n) → (l : List (Fin n × Fin n))
            → below (polsₜ-sub α l) ≡ false
            → ∀ {β γ} → (β , γ) ∈ l → ⌊ α ≟ᶠ γ ⌋ ≡ false
polsₜ-sub-∈ α ((β₀ , γ₀) ∷ l) q (here refl) = proj₁ d₂
  where d₁ = below-∪ (atˢ ⁺ ⌊ α ≟ᶠ β₀ ⌋) (atˢ ⁻ ⌊ α ≟ᶠ γ₀ ⌋ ∪ᴾ polsₜ-sub α l) q
        d₂ = below-∪ (atˢ ⁻ ⌊ α ≟ᶠ γ₀ ⌋) (polsₜ-sub α l) (proj₂ d₁)
polsₜ-sub-∈ α ((β₀ , γ₀) ∷ l) q (there m) = polsₜ-sub-∈ α l (proj₂ d₂) m
  where d₁ = below-∪ (atˢ ⁺ ⌊ α ≟ᶠ β₀ ⌋) (atˢ ⁻ ⌊ α ≟ᶠ γ₀ ⌋ ∪ᴾ polsₜ-sub α l) q
        d₂ = below-∪ (atˢ ⁻ ⌊ α ≟ᶠ γ₀ ⌋) (polsₜ-sub α l) (proj₂ d₁)

record Splitᵗ {n : ℕ} (α : Fin n) (l : List (Fin n × Fin n)) : Set where
  constructor splitt
  field
    bndᵗ   : Fin n
    restᵗ  : List (Fin n × Fin n)
    memᵗ   : (bndᵗ , α) ∈ l
    subᵗ   : ∀ {p} → p ∈ restᵗ → p ∈ l
    casesᵗ : ∀ {p} → p ∈ l → (p ≡ (bndᵗ , α)) ⊎ (p ∈ restᵗ)

open Splitᵗ

consᵗ : ∀ {n} {α : Fin n} {l : List (Fin n × Fin n)} {p} → Splitᵗ α l
      → Splitᵗ α (p ∷ l)
consᵗ {p = p} s =
  splitt (bndᵗ s) (p ∷ restᵗ s) (there (memᵗ s))
         (λ { (here refl) → here refl ; (there m) → there (subᵗ s m) })
         (λ { (here refl) → inj₂ (here refl)
            ; (there m)   → [ inj₁ , (λ r → inj₂ (there r)) ]′ (casesᵗ s m) })

splitᵗ : ∀ {n} → (α : Fin n) → (l : List (Fin n × Fin n)) → Maybe (Splitᵗ α l)
splitᵗ α [] = nothing
splitᵗ α ((β , γ) ∷ l) with α ≟ᶠ γ
... | yes refl = just (splitt β l (here refl) there
                              (λ { (here refl) → inj₁ refl ; (there m) → inj₂ m }))
... | no  _    with splitᵗ α l
...   | just s  = just (consᵗ s)
...   | nothing = nothing

stepᵗ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (α : TyVar Θ)
      → (s : Splitᵗ α (subᵥ Q))
      → below (polₜ-v {Θ} α ⁻ (tvar (bndᵗ s))) ≡ false
      → below (polsₜ-sub α (apart _≟ᶠ_ (restᵗ s))) ≡ false
      → below (polₜ-c α ⁺ C) ≡ false
      → Elim C Q
stepᵗ {Θ} C Q α s cb cq cc =
  mkElim (C [ η₀ ]ᶜ) Q₀ η₀ (≡̂ᶜ-refl _) inst₀ keep₀
         (λ δ h → <:̂ᶜ-subst h (M.monoᵗ-c ⁺ C cc))
  where
    γ₀ : TyVar Θ
    γ₀ = bndᵗ s

    η₀ : Subst Θ Θ
    η₀ = updᵗ α γ₀

    Q₀ : Hyps Θ
    Q₀ = hyps (map (upd α γ₀ idᶠ) (ets Q))
              (map (mapᵖ (upd α γ₀ idᶠ)) (restᵗ s))
              (map (mapᵖ (_[ η₀ ]ʳ)) (ordᵣ Q))
              (map (mapᵖ (_[ η₀ ]ᵉ)) (ordₑ Q))
              (map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q))

    α≢γ₀ : ¬ (α ≡ γ₀)
    α≢γ₀ = ⌊⌋-false cb

    cS : ∀ {β γ} → (β , γ) ∈ apart _≟ᶠ_ (restᵗ s) → ⌊ α ≟ᶠ γ ⌋ ≡ false
    cS = polsₜ-sub-∈ α (apart _≟ᶠ_ (restᵗ s)) cq

    module M = Monoᵗ {Q = Q} α γ₀ (memᵗ s)

    open Lowering {Q = Q} η₀ M.lowg M.lowt

    inst₀ : Q₀ ⊩ᴴ Q [ η₀ ]
    inst₀ = mk⊩ᴴ (λ m → et-hyp (∈-map⁺ (upd α γ₀ idᶠ) m)) sb
                 (λ m → hypᵣ (∈-map⁺ (mapᵖ (_[ η₀ ]ʳ)) m))
                 (λ m → hypₑ (∈-map⁺ (mapᵖ (_[ η₀ ]ᵉ)) m))
                 (λ m → hyp-ok₀ (∈-map⁺ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m))
      where
        sb : ∀ {β γ} → (β , γ) ∈ subᵥ Q → Q₀ ∣ sTy η₀ β <:̂ᵛ sTy η₀ γ
        sb m with casesᵗ s m
        ... | inj₁ refl =
              subst₂ (λ x y → Q₀ ∣ tvar x <:̂ᵛ tvar y)
                     (sym (upd-≢ α γ₀ γ₀ idᶠ α≢γ₀)) (sym (upd-≡ α γ₀ idᶠ))
                     (tvarₛ reflᵗᵛ)
        ... | inj₂ m' = tvarₛ (hypᵗᵛ (∈-map⁺ (mapᵖ (upd α γ₀ idᶠ)) m'))

    keep₀ : Q ⊨ᴴ Q₀
    keep₀ = mk⊨ᴴ et sb
                 (keep-ordʳ (ordᵣ Q) (λ m → m)
                            (λ {ρ} {ρ'} m → fixedʳ (fixᵗ-r (upd α γ₀ idᶠ) ρ')))
                 (keep-ordᵉ (ordₑ Q) (λ m → m)
                            (λ {ε} {ε'} m → fixedᵉ (fixᵗ-e (upd α γ₀ idᶠ) ε')))
                 keep-disj
      where
        et : ∀ {x} → x ∈ map (upd α γ₀ idᶠ) (ets Q) → Q ⊩ᴱ tvar x
        et m with ∈-map⁻ (upd α γ₀ idᶠ) m
        ... | β , m₀ , refl = <:̂ᵛ-eternalˡ (M.lowt β) (et-hyp m₀)

        sb : ∀ {x y} → (x , y) ∈ map (mapᵖ (upd α γ₀ idᶠ)) (restᵗ s)
           → Q ∣ tvar x <:̂ᵛ tvar y
        sb m with ∈-map⁻ (mapᵖ (upd α γ₀ idᶠ)) m
        ... | (β , γ) , m₀ , refl with apart-∈ _≟ᶠ_ m₀
        ...   | inj₁ refl = tvarₛ reflᵗᵛ
        ...   | inj₂ m₁   =
                <:̂ᵛ-trans (M.lowt β)
                  (subst (λ y → Q ∣ tvar β <:̂ᵛ tvar y)
                         (sym (upd-≢ α γ γ₀ idᶠ (⌊⌋-false (cS m₁))))
                         (tvarₛ (hypᵗᵛ (subᵗ s m₀))))

stepᵗ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (α : TyVar Θ)
       → vᵗ F α ≡ false → Maybe (Elimᶠ F C Q)
stepᵗ? {Θ} F C Q α o with splitᵗ α (subᵥ Q)
... | nothing = nothing
... | just s
    with below (polₜ-v {Θ} α ⁻ (tvar (bndᵗ s))) in c1
       | below (polsₜ-sub α (apart _≟ᶠ_ (restᵗ s))) in c2
       | below (polₜ-c α ⁺ C) in c3
...   | false | false | false = just (stepᵗ C Q α s c1 c2 c3 , fixes-updᵗ α (bndᵗ s) o)
...   | _     | _     | _     = nothing

------------------------------------------------------------------------
-- Elimination by equality: an unknown the hypotheses equate with an
-- expression is replaced by it everywhere, and the orderings the
-- replacement makes reflexive are dropped. Under the hypotheses the
-- replacement moves nothing.

-- One step at an effect unknown

equateᵉ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ) → (b : EExp Θ)
        → Q ⊩ evar i ≡̂ₑ b → Elim C Q
equateᵉ {Θ} C Q i b eq =
  mkElim (C [ η₀ ]ᶜ) Q₀ η₀ (≡̂ᶜ-refl _) inst₀ keep₀
         (λ δ h → <:̂ᶜ-subst h (sameᶜ ⁺ C))
  where
    η₀ : Subst Θ Θ
    η₀ = updᵉ i b

    Q₀ : Hyps Θ
    Q₀ = hyps (ets Q) (subᵥ Q)
              (apart _≟ʳ_ (map (mapᵖ (_[ η₀ ]ʳ)) (ordᵣ Q)))
              (apart _≟ᵉ_ (map (mapᵖ (_[ η₀ ]ᵉ)) (ordₑ Q)))
              (map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q))

    open Equal {Q = Q} η₀
      (≾ˢ-idˡ (updᵉ-below i b idˢ (subst (λ y → Q ⊩ y ≾̂ₑ evar i) (sym ([id]ᵉ b)) (proj₂ eq))))
      (≾ˢ-idʳ (updᵉ-above i b idˢ (subst (λ y → Q ⊩ evar i ≾̂ₑ y) (sym ([id]ᵉ b)) (proj₁ eq))))
      (λ β → tvarₛ reflᵗᵛ) (λ β → tvarₛ reflᵗᵛ)

    inst₀ : Q₀ ⊩ᴴ Q [ η₀ ]
    inst₀ = mk⊩ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) ordR ordE
                 (λ m → hyp-ok₀ (∈-map⁺ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m))
      where
        ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q₀ ⊩ ρ [ η₀ ]ʳ ≾̂ᵣ ρ' [ η₀ ]ʳ
        ordR {ρ} m with apart-∈ _≟ʳ_ (∈-map⁺ (mapᵖ (_[ η₀ ]ʳ)) m)
        ... | inj₁ e  = eqᵣ (≅ʳ⇒≡̂ e)
        ... | inj₂ m' = hypᵣ m'

        ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q₀ ⊩ ε [ η₀ ]ᵉ ≾̂ₑ ε' [ η₀ ]ᵉ
        ordE {ε} m with apart-∈ _≟ᵉ_ (∈-map⁺ (mapᵖ (_[ η₀ ]ᵉ)) m)
        ... | inj₁ e  = eqₑ (≅ᵉ⇒≡̂ e)
        ... | inj₂ m' = hypₑ m'

    keep₀ : Q ⊨ᴴ Q₀
    keep₀ = mk⊨ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m))
                 (λ m → keep-ordʳ (ordᵣ Q) (λ q → q) (λ {ρ} {ρ'} _ → raiseʳ ρ')
                                  (apart-⊆ _≟ʳ_ m))
                 (λ m → keep-ordᵉ (ordₑ Q) (λ q → q) (λ {ε} {ε'} _ → raiseᵉ ε')
                                  (apart-⊆ _≟ᵉ_ m))
                 keep-disj

-- One step at a resource unknown

equateʳ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ) → (b : RExp Θ)
        → Q ⊩ rvar i ≡̂ᵣ b → Elim C Q
equateʳ {Θ} C Q i b eq =
  mkElim (C [ η₀ ]ᶜ) Q₀ η₀ (≡̂ᶜ-refl _) inst₀ keep₀
         (λ δ h → <:̂ᶜ-subst h (sameᶜ ⁺ C))
  where
    η₀ : Subst Θ Θ
    η₀ = updʳ i b

    Q₀ : Hyps Θ
    Q₀ = hyps (ets Q) (subᵥ Q)
              (apart _≟ʳ_ (map (mapᵖ (_[ η₀ ]ʳ)) (ordᵣ Q)))
              (map (mapᵖ (_[ η₀ ]ᵉ)) (ordₑ Q))
              (map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q))

    open Equal {Q = Q} η₀
      (≾ˢ-idˡ (updʳ-below i b idˢ (subst (λ y → Q ⊩ y ≾̂ᵣ rvar i) (sym ([id]ʳ b)) (proj₂ eq))))
      (≾ˢ-idʳ (updʳ-above i b idˢ (subst (λ y → Q ⊩ rvar i ≾̂ᵣ y) (sym ([id]ʳ b)) (proj₁ eq))))
      (λ β → tvarₛ reflᵗᵛ) (λ β → tvarₛ reflᵗᵛ)

    inst₀ : Q₀ ⊩ᴴ Q [ η₀ ]
    inst₀ = mk⊩ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) ordR
                 (λ m → hypₑ (∈-map⁺ (mapᵖ (_[ η₀ ]ᵉ)) m))
                 (λ m → hyp-ok₀ (∈-map⁺ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m))
      where
        ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q₀ ⊩ ρ [ η₀ ]ʳ ≾̂ᵣ ρ' [ η₀ ]ʳ
        ordR {ρ} m with apart-∈ _≟ʳ_ (∈-map⁺ (mapᵖ (_[ η₀ ]ʳ)) m)
        ... | inj₁ e  = eqᵣ (≅ʳ⇒≡̂ e)
        ... | inj₂ m' = hypᵣ m'

    keep₀ : Q ⊨ᴴ Q₀
    keep₀ = mk⊨ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m))
                 (λ m → keep-ordʳ (ordᵣ Q) (λ q → q) (λ {ρ} {ρ'} _ → raiseʳ ρ')
                                  (apart-⊆ _≟ʳ_ m))
                 (keep-ordᵉ (ordₑ Q) (λ q → q) (λ {ε} {ε'} _ → raiseᵉ ε'))
                 keep-disj

------------------------------------------------------------------------
-- Cycle elimination: the type variables of each strongly connected
-- component of the subtyping atoms sent to its representative `f`, which
-- the hypotheses bound by each in both directions; the subtyping atoms
-- made reflexive are dropped

collapseᵗ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (f : TyVar Θ → TyVar Θ)
          → (∀ β → (Q ⊩ᵗᵛ f β ≾ β) × (Q ⊩ᵗᵛ β ≾ f β)) → Elim C Q
collapseᵗ {Θ} C Q f both =
  mkElim (C [ η₀ ]ᶜ) Q₀ η₀ (≡̂ᶜ-refl _) inst₀ keep₀
         (λ δ h → <:̂ᶜ-subst h (sameᶜ ⁺ C))
  where
    η₀ : Subst Θ Θ
    η₀ = renᵗ f

    Q₀ : Hyps Θ
    Q₀ = hyps (map f (ets Q))
              (apart _≟ᶠ_ (map (mapᵖ f) (subᵥ Q)))
              (map (mapᵖ (_[ η₀ ]ʳ)) (ordᵣ Q))
              (map (mapᵖ (_[ η₀ ]ᵉ)) (ordₑ Q))
              (map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q))

    lowt : ∀ β → Q ∣ sTy η₀ β <:̂ᵛ tvar β
    lowt β = tvarₛ (proj₁ (both β))

    hit : ∀ β → Q ∣ tvar β <:̂ᵛ sTy η₀ β
    hit β = tvarₛ (proj₂ (both β))

    open Equal {Q = Q} η₀ (mk≾ˢ (λ _ → ⊩≾̂ᵣ-refl) (λ _ → ⊩≾̂ₑ-refl))
                          (mk≾ˢ (λ _ → ⊩≾̂ᵣ-refl) (λ _ → ⊩≾̂ₑ-refl)) lowt hit

    inst₀ : Q₀ ⊩ᴴ Q [ η₀ ]
    inst₀ = mk⊩ᴴ (λ m → et-hyp (∈-map⁺ f m)) sb
                 (λ m → hypᵣ (∈-map⁺ (mapᵖ (_[ η₀ ]ʳ)) m))
                 (λ m → hypₑ (∈-map⁺ (mapᵖ (_[ η₀ ]ᵉ)) m))
                 (λ m → hyp-ok₀ (∈-map⁺ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m))
      where
        sb : ∀ {β β'} → (β , β') ∈ subᵥ Q → Q₀ ∣ sTy η₀ β <:̂ᵛ sTy η₀ β'
        sb {β} m with apart-∈ _≟ᶠ_ (∈-map⁺ (mapᵖ f) m)
        ... | inj₁ e  = subst (λ y → Q₀ ∣ tvar (f β) <:̂ᵛ tvar y) e (tvarₛ reflᵗᵛ)
        ... | inj₂ m' = tvarₛ (hypᵗᵛ m')

    keep₀ : Q ⊨ᴴ Q₀
    keep₀ = mk⊨ᴴ et sb
                 (keep-ordʳ (ordᵣ Q) (λ m → m) (λ {ρ} {ρ'} m → fixedʳ (fixᵗ-r f ρ')))
                 (keep-ordᵉ (ordₑ Q) (λ m → m) (λ {ε} {ε'} m → fixedᵉ (fixᵗ-e f ε')))
                 keep-disj
      where
        et : ∀ {x} → x ∈ map f (ets Q) → Q ⊩ᴱ tvar x
        et m with ∈-map⁻ f m
        ... | β , m₀ , refl = <:̂ᵛ-eternalˡ (lowt β) (et-hyp m₀)

        sb : ∀ {x y} → (x , y) ∈ apart _≟ᶠ_ (map (mapᵖ f) (subᵥ Q)) → Q ∣ tvar x <:̂ᵛ tvar y
        sb m with ∈-map⁻ (mapᵖ f) (apart-⊆ _≟ᶠ_ m)
        ... | (β , β') , m₀ , refl =
              <:̂ᵛ-trans (lowt β) (<:̂ᵛ-trans (tvarₛ (hypᵗᵛ m₀)) (hit β'))

withMem : ∀ {X : Set} → (l : List X) → List (Σ[ a ∈ X ] (a ∈ l))
withMem []      = []
withMem (a ∷ l) = (a , here refl) ∷ map (λ { (b , m) → b , there m }) (withMem l)

-- The search: the components over the type variables with an atom on
-- each side, only they lying on a cycle; the variables of `F` are
-- preferred as representatives and never move

collapseᵗ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → Maybe (Elimᶠ F C Q)
collapseᵗ? {Θ} F C Q = from moves
  where
    Edge : TyVar Θ → TyVar Θ → Set
    Edge a b = (a , b) ∈ subᵥ Q

    vs : List (TyVar Θ)
    vs = filterᵇ (λ β → any (λ p → ⌊ proj₁ p ≟ᶠ β ⌋) (subᵥ Q)
                      ∧ any (λ p → ⌊ proj₂ p ≟ᶠ β ⌋) (subᵥ Q))
                 (fins (nTy Θ))

    same? : (a b : TyVar Θ) → Maybe (Star Edge a b)
    same? a b with a ≟ᶠ b
    ... | yes refl = just ε⋆
    ... | no _     = nothing

    open Reachability Edge same? (map (λ { ((a , b) , m) → a , b , m }) (withMem (subᵥ Q))) vs
      using (module Collapse)
    open Collapse _≟ᶠ_ (vᵗ F) (λ k → vᵗ F k ≡ false) (λ k → isFalse (vᵗ F k))

    t≢f : ∀ {b : 𝔹} → b ≡ true → b ≡ false → ⊥
    t≢f refl ()

    from : Moves → Maybe (Elimᶠ F C Q)
    from []         = nothing
    from ms@(_ ∷ _) =
      just (collapseᵗ C Q (target ms)
                      (equal (Q ⊩ᵗᵛ_≾_) reflᵗᵛ (λ e p → transᵗᵛ (hypᵗᵛ e) p) ms) ,
            mkFixes (λ β h → [ cong tvar , (λ o → ⊥-elim (t≢f h o)) ]′ (stays ms β))
                    (λ _ _ → refl) (λ _ _ → refl))

-- The searches by equality: the first fit expression facing the
-- unknown that the test at the strength `atomic` equates with it
-- (`Values.equate`)

equateᵉ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ)
         → vᵉ F i ≡ false → Maybe (Elimᶠ F C Q)
equateᵉ? {Θ} F C Q i o =
  Maybe.map (λ { (b , p , q) → equateᵉ C Q i b (p , q) , fixes-updᵉ i b o })
            (Vᵉ.equate {Θ} i (decideₑ atomic Q) (ordₑ Q))

equateʳ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ)
         → vʳ F i ≡ false → Maybe (Elimᶠ F C Q)
equateʳ? {Θ} F C Q i o =
  Maybe.map (λ { (b , p , q) → equateʳ C Q i b (p , q) , fixes-updʳ i b o })
            (Vʳ.equate {Θ} i (decideᵣ atomic Q) (ordᵣ Q))

------------------------------------------------------------------------
-- The forced unit: an unknown bounded above by an expression decided
-- below the unit, the unit being least, is the unit at every closed
-- instance (`Values.Forces`)

-- Least, and below the unit: equal to it

unit-forcedᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ}
             → Is-just uᵣ-least? → Q ⊩ ρ ≾̂ᵣ ûᵣ → Q ⊩ ρ ≡̂ᵣ ûᵣ
unit-forcedᵣ l p = p , minᵣ l

unit-forcedₑ : ∀ {Θ} {Q : Hyps Θ} {ε : EExp Θ}
             → Is-just uₑ-least? → Q ⊩ ε ≾̂ₑ ûₑ → Q ⊩ ε ≡̂ₑ ûₑ
unit-forcedₑ l p = p , minₑ l

-- A step equal to the identity under hypotheses `Q⁺` that every closed
-- instance of `Q` meets: at those instances the type does not move

forced : ∀ {Θ} → (C : OCType Θ) → (Q Q⁺ : Hyps Θ) → (η₀ : Subst Θ Θ)
       → Q⁺ ⊩ η₀ ≾ˢ idˢ → Q⁺ ⊩ idˢ ≾ˢ η₀ → (∀ β → sTy η₀ β ≡ tvar β)
       → (Q̂ : Hyps Θ) → Q̂ ⊩ᴴ Q [ η₀ ] → Q⁺ ⊨ᴴ Q̂ → Q ⊨ᴴ Q⁺ → Elim C Q
forced C Q Q⁺ η₀ lowg hig tv Q̂ inst₀ keep⁺ keep₁ =
  mkElim (C [ η₀ ]ᶜ) Q̂ η₀ (≡̂ᶜ-refl _) inst₀ (⊨ᴴ-trans keep₁ keep⁺)
         (λ δ h → <:̂ᶜ-subst (keep₁ δ h) (E.sameᶜ ⁺ C))
  where
    module E = Equal {Q = Q⁺} η₀ lowg hig
                     (λ β → subst (λ x → Q⁺ ∣ x <:̂ᵛ tvar β) (sym (tv β)) (tvarₛ reflᵗᵛ))
                     (λ β → subst (λ x → Q⁺ ∣ tvar β <:̂ᵛ x) (sym (tv β)) (tvarₛ reflᵗᵛ))

-- The atoms an assignment `η₀` changes, written canonically: an
-- ordering marked by `tᵣ` or `tₑ` split into one per alternative of its
-- left side, a disjunction marked by `tᵈ` in canonical form; the
-- orderings made reflexive are dropped

private
  ordʳ-id : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Ordʳ Q idˢ (ρ , ρ') → Q ⊩ ρ ≾̂ᵣ ρ'
  ordʳ-id {Q = Q} {ρ} {ρ'} = subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([id]ʳ ρ) ([id]ʳ ρ')

  idʳ-ord : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Q ⊩ ρ ≾̂ᵣ ρ' → Ordʳ Q idˢ (ρ , ρ')
  idʳ-ord {Q = Q} {ρ} {ρ'} = subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym ([id]ʳ ρ)) (sym ([id]ʳ ρ'))

  ordᵉ-id : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Ordᵉ Q idˢ (ε , ε') → Q ⊩ ε ≾̂ₑ ε'
  ordᵉ-id {Q = Q} {ε} {ε'} = subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([id]ᵉ ε) ([id]ᵉ ε')

  idᵉ-ord : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Q ⊩ ε ≾̂ₑ ε' → Ordᵉ Q idˢ (ε , ε')
  idᵉ-ord {Q = Q} {ε} {ε'} = subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym ([id]ᵉ ε)) (sym ([id]ᵉ ε'))

module Retouch {Θ : Scope} (η₀ : Subst Θ Θ) (tᵣ : RExp Θ × RExp Θ → 𝔹)
               (tₑ : EExp Θ × EExp Θ → 𝔹) (tᵈ : OVType Θ × RExp Θ → 𝔹)
               (Q : Hyps Θ) (rs : List (RExp Θ × RExp Θ)) (es : List (EExp Θ × EExp Θ)) where

  touchʳ : (a : RExp Θ × RExp Θ) → Pieces Ordʳ (mapᵖ (_[ η₀ ]ʳ) a)
  touchʳ a with tᵣ a
  ... | true  = piecesʳ (mapᵖ (_[ η₀ ]ʳ) a)
  ... | false = whole (mapᵖ (_[ η₀ ]ʳ) a)

  touchᵉ : (a : EExp Θ × EExp Θ) → Pieces Ordᵉ (mapᵖ (_[ η₀ ]ᵉ) a)
  touchᵉ a with tₑ a
  ... | true  = piecesᵉ (mapᵖ (_[ η₀ ]ᵉ) a)
  ... | false = whole (mapᵖ (_[ η₀ ]ᵉ) a)

  touchᵈ : OVType Θ × RExp Θ → OVType Θ × RExp Θ
  touchᵈ a with tᵈ a
  ... | true  = mapᵈ canonᵛ canonᵣ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ) a)
  ... | false = mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ) a

  touchᵈ-≡̂ : (a : OVType Θ × RExp Θ)
           → (proj₁ a [ η₀ ]ᵛ ≡̂ᵛ proj₁ (touchᵈ a)) × (proj₂ a [ η₀ ]ʳ ≡̂ᵣ proj₂ (touchᵈ a))
  touchᵈ-≡̂ (A , ρ) with tᵈ (A , ρ)
  ... | true  = canonᵛ-≡̂ (A [ η₀ ]ᵛ) , canonᵣ-≡ (ρ [ η₀ ]ʳ)
  ... | false = ≡̂ᵛ-refl (A [ η₀ ]ᵛ) , ≡̂ᵣ-refl

  Sʳ : Split Ordʳ (map (mapᵖ (_[ η₀ ]ʳ)) rs)
  Sʳ = splitsBy (mapᵖ (_[ η₀ ]ʳ)) touchʳ rs

  Sᵉ : Split Ordᵉ (map (mapᵖ (_[ η₀ ]ᵉ)) es)
  Sᵉ = splitsBy (mapᵖ (_[ η₀ ]ᵉ)) touchᵉ es

  -- The orderings `rs` and `es` and the disjunctions of `Q`, moved

  retouched : Hyps Θ
  retouched = hyps (ets Q) (subᵥ Q) (apart _≟ʳ_ (Split.out Sʳ))
                   (apart _≟ᵉ_ (Split.out Sᵉ)) (map touchᵈ (disj Q))

  instʳ : ∀ {x x'} → (x , x') ∈ rs → retouched ⊩ x [ η₀ ]ʳ ≾̂ᵣ x' [ η₀ ]ʳ
  instʳ m =
    ordʳ-id (apart-back _≟ʳ_ (λ e → eqᵣ (≡̂ᵣ-subst _ (≅ʳ⇒≡̂ e))) Sʳ idˢ (λ mb → idʳ-ord (hypᵣ mb))
                        (∈-map⁺ (mapᵖ (_[ η₀ ]ʳ)) m))

  instᵉ : ∀ {x x'} → (x , x') ∈ es → retouched ⊩ x [ η₀ ]ᵉ ≾̂ₑ x' [ η₀ ]ᵉ
  instᵉ m =
    ordᵉ-id (apart-back _≟ᵉ_ (λ e → eqₑ (≡̂ₑ-subst _ (≅ᵉ⇒≡̂ e))) Sᵉ idˢ (λ mb → idᵉ-ord (hypₑ mb))
                        (∈-map⁺ (mapᵖ (_[ η₀ ]ᵉ)) m))

  instᵈ : ∀ {A ρ} → (A , ρ) ∈ disj Q → VarOK retouched (A [ η₀ ]ᵛ) (ρ [ η₀ ]ʳ)
  instᵈ {A} {ρ} m =
    hyp-ok (∈-map⁺ touchᵈ m) (proj₁ (touchᵈ-≡̂ (A , ρ))) (eqᵣ (proj₂ (touchᵈ-≡̂ (A , ρ))))

  keepʳ : ∀ {Q⁺} → (∀ {x x'} → (x , x') ∈ rs → Q⁺ ⊩ x [ η₀ ]ʳ ≾̂ᵣ x' [ η₀ ]ʳ)
        → ∀ {y y'} → (y , y') ∈ ordᵣ retouched → Q⁺ ⊩ y ≾̂ᵣ y'
  keepʳ {Q⁺} k mb = ordʳ-id (apart-fwd _≟ʳ_ Sʳ idˢ k' mb)
    where
      k' : ∀ {a} → a ∈ map (mapᵖ (_[ η₀ ]ʳ)) rs → Ordʳ Q⁺ idˢ a
      k' m with ∈-map⁻ (mapᵖ (_[ η₀ ]ʳ)) m
      ... | (x , x') , m₀ , refl = idʳ-ord (k m₀)

  keepᵉ : ∀ {Q⁺} → (∀ {x x'} → (x , x') ∈ es → Q⁺ ⊩ x [ η₀ ]ᵉ ≾̂ₑ x' [ η₀ ]ᵉ)
        → ∀ {y y'} → (y , y') ∈ ordₑ retouched → Q⁺ ⊩ y ≾̂ₑ y'
  keepᵉ {Q⁺} k mb = ordᵉ-id (apart-fwd _≟ᵉ_ Sᵉ idˢ k' mb)
    where
      k' : ∀ {a} → a ∈ map (mapᵖ (_[ η₀ ]ᵉ)) es → Ordᵉ Q⁺ idˢ a
      k' m with ∈-map⁻ (mapᵖ (_[ η₀ ]ᵉ)) m
      ... | (x , x') , m₀ , refl = idᵉ-ord (k m₀)

  keepᵈ : (δ : Subst Θ ∅ˢ)
        → (∀ {A ρ} → (A , ρ) ∈ map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q)
           → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ))
        → ∀ {A ρ} → (A , ρ) ∈ map touchᵈ (disj Q) → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ)
  keepᵈ δ k m with ∈-map⁻ touchᵈ m
  ... | (A₀ , ρ₀) , m₀ , refl =
        VarOK-≡̂ (≡̂ᵛ-subst δ (≡̂ᵛ-sym (proj₁ t))) (eqᵣ (≡̂ᵣ-subst δ (≡̂ᵣ-sym (proj₂ t))))
                (k (∈-map⁺ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m₀))
    where t = touchᵈ-≡̂ (A₀ , ρ₀)

-- The resource unit, forced by an ordering `x ≾ c` (`m₀`, `f₀`): every
-- forcing ordering is dropped

unitʳ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ)
      → ∀ {a₀} → a₀ ∈ ordᵣ Q → Vʳ.Forces {Θ} i a₀ → Elim C Q
unitʳ {Θ} C Q i {x₀ , c₀} m₀ f₀@(lst , _ , _) =
  forced C Q Q⁺ η₀ lowg hig (λ β → refl) Q₁ inst₀ keep⁺ (⊩ᴴ-⊨ᴴ keep₁)
  where
    η₀ : Subst Θ Θ
    η₀ = updʳ i ûᵣ

    P = partition (Vʳ.forces? {Θ} i) (ordᵣ Q)

    open Retouch η₀ (λ { (x , x') → occʳ-r i x ∨ occʳ-r i x' }) (λ _ → false)
                    (λ { (A , ρ) → occʳ-v i A ∨ occʳ-r i ρ }) Q (kept P) (ordₑ Q)

    Q₁ : Hyps Θ
    Q₁ = retouched

    Q⁺ : Hyps Θ
    Q⁺ = record Q { ordᵣ = (rvar i , ûᵣ) ∷ ordᵣ Q }

    eq⁺ : Q⁺ ⊩ rvar i ≡̂ᵣ ûᵣ
    eq⁺ = unit-forcedᵣ lst (hypᵣ (here refl))

    lowg : Q⁺ ⊩ η₀ ≾ˢ idˢ
    lowg = ≾ˢ-idˡ (updʳ-below i ûᵣ idˢ (proj₂ eq⁺))

    hig : Q⁺ ⊩ idˢ ≾ˢ η₀
    hig = ≾ˢ-idʳ (updʳ-above i ûᵣ idˢ (proj₁ eq⁺))

    open Equal {Q = Q⁺} η₀ lowg hig (λ β → tvarₛ reflᵗᵛ) (λ β → tvarₛ reflᵗᵛ)

    -- a forcing ordering: its left side is the unknown, its right side
    -- below the unit
    lhs : ∀ {x c} → Vʳ.Forces {Θ} i (x , c) → x ≡̂ᵣ rvar i
    lhs {x} (_ , e , _) = subst (x ≡̂ᵣ_) e (canonᵣ-≡ x)

    keep₁ : Q ⊩ᴴ Q⁺
    keep₁ = mk⊩ᴴ⁼ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) ordR hypₑ hyp-ok₀
      where
        ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q⁺ → Q ⊩ ρ ≾̂ᵣ ρ'
        ordR (here refl) =
          transᵣ (eqᵣ (≡̂ᵣ-sym (lhs {x₀} f₀))) (transᵣ (hypᵣ m₀) (⊩ᴴ-≾ᵣ ∅ᴴ-⊩ᴴ (proj₂ (proj₂ f₀))))
        ordR (there m)   = hypᵣ m

    inst₀ : Q₁ ⊩ᴴ Q [ η₀ ]
    inst₀ = mk⊩ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) ordR instᵉ instᵈ
      where
        ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q₁ ⊩ ρ [ η₀ ]ʳ ≾̂ᵣ ρ' [ η₀ ]ʳ
        ordR {ρ} m with which P m
        ... | inj₁ f  =
              transᵣ (eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-subst η₀ (lhs {ρ} f))
                                    (subst (_≡̂ᵣ ûᵣ) (sym (updʳ-hit i ûᵣ)) ≡̂ᵣ-refl)))
                     (minᵣ (proj₁ f))
        ... | inj₂ mk = instʳ mk

    keep⁺ : Q⁺ ⊨ᴴ Q₁
    keep⁺ = mk⊨ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m))
                 (keepʳ (λ {x} {x'} mk → transᵣ (lowʳ x)
                                           (transᵣ (hypᵣ (there (kept⊆ P mk))) (raiseʳ x'))))
                 (keepᵉ (λ {x} {x'} m → transₑ (lowᵉ x) (transₑ (hypₑ m) (raiseᵉ x'))))
                 (λ δ h → keepᵈ δ (keep-disj δ h))

-- An effect unknown forced by an ordering of effects, or by an ordering
-- of resources through its image

data Forcedᵉ {Θ} (Q : Hyps Θ) (i : EVar Θ) : Set where
  byEff : ∀ {a} → a ∈ ordₑ Q → Vᵉ.Forces {Θ} i a → Forcedᵉ Q i
  byImg : ∀ {a} → a ∈ ordᵣ Q → Vⁱ.Forces {Θ} i a → Forcedᵉ Q i

unitᵉ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ) → Forcedᵉ Q i → Elim C Q
unitᵉ {Θ} C Q i w = forced C Q Q⁺ η₀ lowg hig (λ β → refl) Q₁ inst₀ keep⁺ (keep₁ w)
  where
    η₀ : Subst Θ Θ
    η₀ = updᵉ i ûₑ

    Pₑ = partition (Vᵉ.forces? {Θ} i) (ordₑ Q)
    Pᵣ = partition (Vⁱ.forces? {Θ} i) (ordᵣ Q)

    open Retouch η₀ (λ { (x , x') → occᵉ-r i x ∨ occᵉ-r i x' })
                    (λ { (x , x') → occᵉ-e i x ∨ occᵉ-e i x' })
                    (λ { (A , ρ) → occᵉ-v i A ∨ occᵉ-r i ρ }) Q (kept Pᵣ) (kept Pₑ)

    Q₁ : Hyps Θ
    Q₁ = retouched

    Q⁺ : Hyps Θ
    Q⁺ = record Q { ordₑ = (evar i , ûₑ) ∷ ordₑ Q }

    least : Forcedᵉ Q i → Is-just uₑ-least?
    least (byEff _ (lst , _ , _))       = lst
    least (byImg _ ((lst , _ , _) , _)) = lst

    eq⁺ : Q⁺ ⊩ evar i ≡̂ₑ ûₑ
    eq⁺ = unit-forcedₑ (least w) (hypₑ (here refl))

    lowg : Q⁺ ⊩ η₀ ≾ˢ idˢ
    lowg = ≾ˢ-idˡ (updᵉ-below i ûₑ idˢ (proj₂ eq⁺))

    hig : Q⁺ ⊩ idˢ ≾ˢ η₀
    hig = ≾ˢ-idʳ (updᵉ-above i ûₑ idˢ (proj₁ eq⁺))

    open Equal {Q = Q⁺} η₀ lowg hig (λ β → tvarₛ reflᵗᵛ) (λ β → tvarₛ reflᵗᵛ)

    lhsₑ : ∀ {x c} → Vᵉ.Forces {Θ} i (x , c) → x ≡̂ₑ evar i
    lhsₑ {x} (_ , e , _) = subst (x ≡̂ₑ_) e (canonₑ-≡ x)

    lhsᵣ : ∀ {x c} → Vⁱ.Forces {Θ} i (x , c) → x ≡̂ᵣ ∣ evar i ∣̂ᵉ
    lhsᵣ {x} (_ , e , _) = subst (x ≡̂ᵣ_) e (canonᵣ-≡ x)

    -- every closed instance sends the unknown below the unit: by the
    -- ordering of effects, or by reflection at the instance
    keep₁ : Forcedᵉ Q i → Q ⊨ᴴ Q⁺
    keep₁ (byEff {x , c} m₀ f₀) =
      ⊩ᴴ-⊨ᴴ (mk⊩ᴴ⁼ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) hypᵣ ordE hyp-ok₀)
      where
        ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q⁺ → Q ⊩ ε ≾̂ₑ ε'
        ordE (here refl) =
          transₑ (eqₑ (≡̂ₑ-sym (lhsₑ {x} f₀))) (transₑ (hypₑ m₀) (⊩ᴴ-≾ₑ ∅ᴴ-⊩ᴴ (proj₂ (proj₂ f₀))))
        ordE (there m)   = hypₑ m
    keep₁ (byImg {x , c} m₀ f₀@((_ , refl-u , _) , _ , below-u)) δ h =
      mk⊩ᴴ (⊩ets h) (⊩subᵥ h) (⊩ordᵣ h) ordE (⊩disj h)
      where
        image : ∅ᴴ ⊩ ∣ sE δ i ∣̂ᵉ ≾̂ᵣ ûᵣ
        image = transᵣ (eqᵣ (≡̂ᵣ-subst δ (≡̂ᵣ-sym (lhsᵣ {x} f₀))))
                       (transᵣ (⊩ordᵣ h m₀) (⊩-substᵣ ∅ᴴ-⊩ᴴ below-u))

        ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q⁺ → ∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
        ordE (here refl) = val-≾ₑ⁻ (refl-u _ (val-≾ᵣ image))
        ordE (there m)   = ⊩ordₑ h m

    inst₀ : Q₁ ⊩ᴴ Q [ η₀ ]
    inst₀ = mk⊩ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) ordR ordE instᵈ
      where
        ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q₁ ⊩ ρ [ η₀ ]ʳ ≾̂ᵣ ρ' [ η₀ ]ʳ
        ordR {ρ} m with which Pᵣ m
        ... | inj₁ f@((_ , _ , lstᵣ) , _ , _) =
              transᵣ (eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-subst η₀ (lhsᵣ {ρ} f))
                                    (≡̂ᵣ-trans (subst (λ z → ∣ z ∣̂ᵉ ≡̂ᵣ ∣ ûₑ ∣̂ᵉ)
                                                     (sym (updᵉ-hit i ûₑ)) ≡̂ᵣ-refl)
                                              (≡̂ᵣ-trans ≡̂ᵣ-map-const (≡̂ᵣ-const map-uᵉ)))))
                     (minᵣ lstᵣ)
        ... | inj₂ mk = instʳ mk

        ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q₁ ⊩ ε [ η₀ ]ᵉ ≾̂ₑ ε' [ η₀ ]ᵉ
        ordE {ε} m with which Pₑ m
        ... | inj₁ f  =
              transₑ (eqₑ (≡̂ₑ-trans (≡̂ₑ-subst η₀ (lhsₑ {ε} f))
                                    (subst (_≡̂ₑ ûₑ) (sym (updᵉ-hit i ûₑ)) ≡̂ₑ-refl)))
                     (minₑ (proj₁ f))
        ... | inj₂ mk = instᵉ mk

    keep⁺ : Q⁺ ⊨ᴴ Q₁
    keep⁺ = mk⊨ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m))
                 (keepʳ (λ {x} {x'} mk → transᵣ (lowʳ x) (transᵣ (hypᵣ (kept⊆ Pᵣ mk)) (raiseʳ x'))))
                 (keepᵉ (λ {x} {x'} mk → transₑ (lowᵉ x)
                                           (transₑ (hypₑ (there (kept⊆ Pₑ mk))) (raiseᵉ x'))))
                 (λ δ h → keepᵈ δ (keep-disj δ h))

-- The searches: the first forcing ordering

firstHit : ∀ {X : Set} {P : X → Set} → ((a : X) → Maybe (P a)) → (l : List X)
         → Maybe (Σ[ a ∈ X ] ((a ∈ l) × P a))
firstHit p []      = nothing
firstHit p (a ∷ l) with p a
... | just q  = just (a , here refl , q)
... | nothing = Maybe.map (λ { (b , m , q) → b , there m , q }) (firstHit p l)

unitʳ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ)
       → vʳ F i ≡ false → Maybe (Elimᶠ F C Q)
unitʳ? {Θ} F C Q i o =
  Maybe.map (λ { (_ , m , f) → unitʳ C Q i m f , fixes-updʳ i ûᵣ o })
            (firstHit (Vʳ.forces? {Θ} i) (ordᵣ Q))

unitᵉ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ)
       → vᵉ F i ≡ false → Maybe (Elimᶠ F C Q)
unitᵉ? {Θ} F C Q i o with firstHit (Vᵉ.forces? {Θ} i) (ordₑ Q)
... | just (_ , m , f) = just (unitᵉ C Q i (byEff m f) , fixes-updᵉ i ûₑ o)
... | nothing =
      Maybe.map (λ { (_ , m , f) → unitᵉ C Q i (byImg m f) , fixes-updᵉ i ûₑ o })
                (firstHit (Vⁱ.forces? {Θ} i) (ordᵣ Q))

------------------------------------------------------------------------
-- The steps in order: merging, equating, lowering, raising and the
-- forced unit, each at an effect unknown before a resource one, then
-- cycle elimination and lowering a type variable

anyStep : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → Maybe (Elimᶠ F C Q)
anyStep {Θ} F C Q =
  orElse (first (vᵉ F) (mergeᵉ? F C Q) (fins (nE Θ)))
  (orElse (first (vʳ F) (mergeʳ? F C Q) (fins (nR Θ)))
  (orElse (first (vᵉ F) (equateᵉ? F C Q) (fins (nE Θ)))
  (orElse (first (vʳ F) (equateʳ? F C Q) (fins (nR Θ)))
  (orElse (first (vᵉ F) (stepᵉ? F C Q) (fins (nE Θ)))
  (orElse (first (vʳ F) (stepʳ? F C Q) (fins (nR Θ)))
  (orElse (first (vᵉ F) (upᵉ? F C Q) (fins (nE Θ)))
  (orElse (first (vʳ F) (upʳ? F C Q) (fins (nR Θ)))
  (orElse (first (vᵉ F) (unitᵉ? F C Q) (fins (nE Θ)))
  (orElse (first (vʳ F) (unitʳ? F C Q) (fins (nR Θ)))
  (orElse (collapseᵗ? F C Q)
          (first (vᵗ F) (stepᵗ? F C Q) (fins (nTy Θ)))))))))))))
  where
    orElse : ∀ {X : Set} → Maybe X → Maybe X → Maybe X
    orElse (just x) _ = just x
    orElse nothing  y = y

reduce : ∀ {Θ} → (F : Vars Θ) → ℕ → (C : OCType Θ) → (Q : Hyps Θ) → Elimᶠ F C Q
reduce F zero    C Q = idElim C Q , fixes-id
reduce F (suc n) C Q with anyStep F C Q
... | nothing = idElim C Q , fixes-id
... | just r  = r ⨾ᶠ reduce F n (Ĉ (proj₁ r)) (Q̂ (proj₁ r))

-- One round per unknown suffices: a step removes one

eliminate : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → Elimᶠ F C Q
eliminate {Θ} F C Q = reduce F (nE Θ + nR Θ + nTy Θ) C Q
