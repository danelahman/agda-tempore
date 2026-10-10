------------------------------------------------------------------
-- Eliminating an unknown from a report                         --
--                                                              --
-- An unknown that no demand bounds below, other than the       --
-- hypotheses bounding it below, is sent to the join of those   --
-- lower bounds, which are removed with it; an unknown absent   --
-- from the reported type is eliminated outright by the same    --
-- step. Dually, a grade unknown that no demand bounds above,   --
-- other than the hypotheses bounding it above, is sent to an   --
-- upper bound decided (from no hypotheses) below the others,   --
-- and those hypotheses are removed with it. The bounds are     --
-- read off by `Bounds` (`lowsOf`, `upsOf`); the demands are    --
-- those of `Polarity`. The two grade sorts are treated alike;  --
-- open types have no join, so a type variable is eliminated    --
-- against a single bound.                                      --
--                                                              --
-- A grade unknown that the hypotheses equate with an           --
-- expression free of it is replaced by that expression         --
-- everywhere, and the orderings made reflexive are removed; of --
-- two equal unknowns, the one of smaller index remains. This   --
-- step is tried before the steps against a bound, and the two  --
-- alternate.                                                   --
--                                                              --
-- Cycle elimination: a type variable on a cycle of subtyping   --
-- atoms is sent to the representative of its strongly          --
-- connected component (`Reach`), and the atoms made reflexive  --
-- are removed. The representative is a member that is never    --
-- eliminated, if there is one, and otherwise the least member, --
-- by index; two members that are never eliminated both remain. --
-- This step is tried before the type variables' step against a --
-- bound.                                                       --
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
-- by `Bounds` (`lowerR`, `raiseL`); the type, the other sort   --
-- and the disjunctions are kept by polarity (`Monoᵉ`, `Raiseᵉ` --
-- and their counterparts, each an instance of `Lift`, which    --
-- relates the parts of a former at their variance). For a step --
-- by equality (`equateᵉ`, `equateʳ`, `equateᵗ`), the           --
-- hypotheses bound `η` by the identity in both directions, and --
-- it moves no type (`Equal`).                                  --
--                                                              --
-- The polarity-based elimination follows Pottier's             --
-- simplification of subtyping constraints (ICFP 1996); cycle   --
-- elimination follows Fähndrich, Foster, Su and Aiken (PLDI    --
-- 1998).                                                       --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false; not; _∨_; _∧_) renaming (Bool to 𝔹)
open import Data.Empty using (⊥-elim)
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
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<ᵇ_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)

open import Induction.WellFounded using (Acc; acc; WfRec)

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; ¬?)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; fold)

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
  using (_⊨ᴴ_; ⊨ᴴ-refl; ⊨ᴴ-trans; mk⊨ᴴ; VarOK-∅-mono)

open import TypeInference.SolverImpl.Former   S
open import TypeInference.SolverImpl.Polarity S
open import TypeInference.SolverImpl.Vars     S
  using (Vars; vᵗ; vʳ; vᵉ; Fixes; mkFixes; fixes-id; fixes-⨟; fixes-updᵉ; fixes-updʳ; outside)
open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-e; occʳ-r)
open import TypeInference.SolverImpl.Resid       S using (∅ᴴ-⊩ᴴ)
import TypeInference.SolverImpl.Reach as Reachability
open import TypeInference.SolverImpl.Bounds      S
  using (module Bᵉ; module Bʳ; updᵉ-e; updʳ-r; joinₑ; joinᵣ; joinₑ-ub⊩; joinₑ-lub⊩;
         joinᵣ-ub⊩; joinᵣ-lub⊩)

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

-- Lowering an effect unknown to the join of its bounds below
-- (`Bounds.Lows`); the orderings bounding it are dropped, the rest kept
-- along `η`

stepᵉ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ)
      → (lw : Bᵉ.Lows i (ordₑ Q)) → (x : EExp Θ) → (xs : List (EExp Θ)) → Bᵉ.bnds lw ≡ x ∷ xs
      → below (polₑ-e i ⁻ (joinₑ x xs)) ≡ false
      → below (polₑᴴ (hyps (ets Q) (subᵥ Q) (ordᵣ Q) (Bᵉ.rest lw) (disj Q)) i) ≡ false
      → below (polₑ-c i ⁺ C) ≡ false
      → Elim C Q
stepᵉ {Θ} C Q i lw x xs e cb cq cc =
  mkElim (C [ η₀ ]ᶜ) Q₀ η₀ (≡̂ᶜ-refl _) inst₀ keep₀
         (λ δ h → <:̂ᶜ-subst h (Monoᵉ.monoᵉ-c i b lowg ⁺ C cc))
  where
    b : EExp Θ
    b = joinₑ x xs

    η₀ : Subst Θ Θ
    η₀ = updᵉ i b

    Q₀ : Hyps Θ
    Q₀ = hyps (ets Q) (subᵥ Q)
              (map (mapᵖ (_[ η₀ ]ʳ)) (ordᵣ Q))
              (map (mapᵖ (_[ η₀ ]ᵉ)) (Bᵉ.rest lw))
              (map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q))

    bnd : ∀ {ε} → ε ∈ x ∷ xs → (ε , evar i) ∈ ordₑ Q
    bnd m = Bᵉ.src lw (subst (_ ∈_) (sym e) m)

    d₁ = below-∪ (polsₑ-ordᵣ i (ordᵣ Q))
                 (polsₑ-ordₑ i (Bᵉ.rest lw) ∪ᴾ polsₑ-disj i (disj Q)) cq

    cR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → below (polₑ-r i ⁻ ρ') ≡ false
    cR m = proj₂ (polsₑ-ordᵣ-∈ i (ordᵣ Q) (proj₁ d₁) m)

    lowg : Q ⊩ η₀ ≾ˢ idˢ
    lowg = ≾ˢ-idˡ (updᵉ-below i b idˢ
             (joinₑ-lub⊩ idˢ x xs
               (λ {y} m → subst (λ z → Q ⊩ z ≾̂ₑ evar i) (sym ([id]ᵉ y)) (hypₑ (bnd m)))))

    open Lowering {Q = Q} η₀ lowg (λ β → tvarₛ reflᵗᵛ)
    module K = Bᵉ.Keep i (Q ⊩_≾̂ₑ_) ⊩≾̂ₑ-refl transₑ (λ ε → ε) (_[ η₀ ]ᵉ) (λ {ε} → updᵉ-e i b ε)

    inst₀ : Q₀ ⊩ᴴ Q [ η₀ ]
    inst₀ = mk⊩ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m))
                 (λ m → hypᵣ (∈-map⁺ (mapᵖ (_[ η₀ ]ʳ)) m)) ordE
                 (λ m → hyp-ok₀ (∈-map⁺ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m))
      where
        ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q₀ ⊩ ε [ η₀ ]ᵉ ≾̂ₑ ε' [ η₀ ]ᵉ
        ordE {ε} m with Bᵉ.cls lw m
        ... | inj₁ (refl , mb) =
              subst (Q₀ ⊩ ε [ η₀ ]ᵉ ≾̂ₑ_) (trans (absᵉ-e i b b cb) (sym (updᵉ-hit i b)))
                    (joinₑ-ub⊩ η₀ x xs (subst (_ ∈_) e mb))
        ... | inj₂ m' = hypₑ (∈-map⁺ (mapᵖ (_[ η₀ ]ᵉ)) m')

    keepE : ∀ {ε ε'} → (ε , ε') ∈ map (mapᵖ (_[ η₀ ]ᵉ)) (Bᵉ.rest lw) → Q ⊩ ε ≾̂ₑ ε'
    keepE m with ∈-map⁻ (mapᵖ (_[ η₀ ]ᵉ)) m
    ... | (ε₀ , ε₀') , m₀ , refl =
          K.lowerR (Bᵉ.restR lw m₀) lowᵉ (hypₑ (Bᵉ.rest⊆ lw m₀))

    keep₀ : Q ⊨ᴴ Q₀
    keep₀ = mk⊨ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m))
                 (keep-ordʳ (ordᵣ Q) (λ m → m)
                            (λ {ρ} {ρ'} m → fixedʳ (absᵉ-r i b ρ' (cR m))))
                 keepE keep-disj

-- The search: one unknown at a time, the first that qualifies

stepᵉ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ)
       → vᵉ F i ≡ false → Maybe (Elimᶠ F C Q)
stepᵉ? F C Q i o with Bᵉ.lowsOf i (ordₑ Q)
... | nothing                                = nothing
... | just (Bᵉ.lows [] _ _ _ _ _ _)          = nothing
... | just lw@(Bᵉ.lows (x ∷ xs) _ _ _ _ _ _)
    with below (polₑ-e i ⁻ (joinₑ x xs)) in c1
       | below (polₑᴴ (hyps (ets Q) (subᵥ Q) (ordᵣ Q) (Bᵉ.rest lw) (disj Q)) i) in c2
       | below (polₑ-c i ⁺ C) in c3
...   | false | false | false =
        just (stepᵉ C Q i lw x xs refl c1 c2 c3 , fixes-updᵉ i (joinₑ x xs) o)
...   | _     | _     | _     = nothing

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

stepʳ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ)
      → (lw : Bʳ.Lows i (ordᵣ Q)) → (x : RExp Θ) → (xs : List (RExp Θ)) → Bʳ.bnds lw ≡ x ∷ xs
      → below (polᵣ-r i ⁻ (joinᵣ x xs)) ≡ false
      → below (polᵣᴴ (hyps (ets Q) (subᵥ Q) (Bʳ.rest lw) (ordₑ Q) (disj Q)) i) ≡ false
      → below (polᵣ-c i ⁺ C) ≡ false
      → Elim C Q
stepʳ {Θ} C Q i lw x xs e cb cq cc =
  mkElim (C [ η₀ ]ᶜ) Q₀ η₀ (≡̂ᶜ-refl _) inst₀ keep₀
         (λ δ h → <:̂ᶜ-subst h (Monoʳ.monoʳ-c i b lowg ⁺ C cc))
  where
    b : RExp Θ
    b = joinᵣ x xs

    η₀ : Subst Θ Θ
    η₀ = updʳ i b

    Q₀ : Hyps Θ
    Q₀ = hyps (ets Q) (subᵥ Q)
              (map (mapᵖ (_[ η₀ ]ʳ)) (Bʳ.rest lw))
              (map (mapᵖ (_[ η₀ ]ᵉ)) (ordₑ Q))
              (map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q))

    bnd : ∀ {ρ} → ρ ∈ x ∷ xs → (ρ , rvar i) ∈ ordᵣ Q
    bnd m = Bʳ.src lw (subst (_ ∈_) (sym e) m)

    lowg : Q ⊩ η₀ ≾ˢ idˢ
    lowg = ≾ˢ-idˡ (updʳ-below i b idˢ
             (joinᵣ-lub⊩ idˢ x xs
               (λ {y} m → subst (λ z → Q ⊩ z ≾̂ᵣ rvar i) (sym ([id]ʳ y)) (hypᵣ (bnd m)))))

    open Lowering {Q = Q} η₀ lowg (λ β → tvarₛ reflᵗᵛ)
    module K = Bʳ.Keep i (Q ⊩_≾̂ᵣ_) ⊩≾̂ᵣ-refl transᵣ (λ ρ → ρ) (_[ η₀ ]ʳ) (λ {ρ} → updʳ-r i b ρ)

    inst₀ : Q₀ ⊩ᴴ Q [ η₀ ]
    inst₀ = mk⊩ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) ordR
                 (λ m → hypₑ (∈-map⁺ (mapᵖ (_[ η₀ ]ᵉ)) m))
                 (λ m → hyp-ok₀ (∈-map⁺ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m))
      where
        ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q₀ ⊩ ρ [ η₀ ]ʳ ≾̂ᵣ ρ' [ η₀ ]ʳ
        ordR {ρ} m with Bʳ.cls lw m
        ... | inj₁ (refl , mb) =
              subst (Q₀ ⊩ ρ [ η₀ ]ʳ ≾̂ᵣ_) (trans (absʳ-r i b b cb) (sym (updʳ-hit i b)))
                    (joinᵣ-ub⊩ η₀ x xs (subst (_ ∈_) e mb))
        ... | inj₂ m' = hypᵣ (∈-map⁺ (mapᵖ (_[ η₀ ]ʳ)) m')

    keepR : ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ (_[ η₀ ]ʳ)) (Bʳ.rest lw) → Q ⊩ ρ ≾̂ᵣ ρ'
    keepR m with ∈-map⁻ (mapᵖ (_[ η₀ ]ʳ)) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
          K.lowerR (Bʳ.restR lw m₀) lowʳ (hypᵣ (Bʳ.rest⊆ lw m₀))

    keep₀ : Q ⊨ᴴ Q₀
    keep₀ = mk⊨ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) keepR
                 (keep-ordᵉ (ordₑ Q) (λ m → m)
                            (λ {ε} {ε'} m → fixedᵉ (updʳ-e i b ε')))
                 keep-disj

stepʳ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ)
       → vʳ F i ≡ false → Maybe (Elimᶠ F C Q)
stepʳ? F C Q i o with Bʳ.lowsOf i (ordᵣ Q)
... | nothing                                = nothing
... | just (Bʳ.lows [] _ _ _ _ _ _)          = nothing
... | just lw@(Bʳ.lows (x ∷ xs) _ _ _ _ _ _)
    with below (polᵣ-r i ⁻ (joinᵣ x xs)) in c1
       | below (polᵣᴴ (hyps (ets Q) (subᵥ Q) (Bʳ.rest lw) (ordₑ Q) (disj Q)) i) in c2
       | below (polᵣ-c i ⁺ C) in c3
...   | false | false | false =
        just (stepʳ C Q i lw x xs refl c1 c2 c3 , fixes-updʳ i (joinᵣ x xs) o)
...   | _     | _     | _     = nothing

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

-- Raising an effect unknown to its bound above (`Bounds.Ups`): the
-- orderings with it on the left are dropped, each then decided from no
-- hypotheses; the rest are kept along `η`

upᵉ-step : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ)
         → (up : Bᵉ.Ups i (ordₑ Q))
         → above (polₑᴴ (hyps (ets Q) (subᵥ Q) (ordᵣ Q) (Bᵉ.restᵘ (Bᵉ.capd up)) (disj Q)) i)
           ≡ false
         → above (polₑ-c i ⁺ C) ≡ false
         → Elim C Q
upᵉ-step {Θ} C Q i up cq cc =
  mkElim (C [ η₀ ]ᶜ) Q₀ η₀ (≡̂ᶜ-refl _) inst₀ keep₀
         (λ δ h → <:̂ᶜ-subst h (Raiseᵉ.raiseᵉ-c i b hig ⁺ C cc))
  where
    b : EExp Θ
    b = Bᵉ.cap up

    η₀ : Subst Θ Θ
    η₀ = updᵉ i b

    rest = Bᵉ.restᵘ (Bᵉ.capd up)

    Q₀ : Hyps Θ
    Q₀ = hyps (ets Q) (subᵥ Q)
              (map (mapᵖ (_[ η₀ ]ʳ)) (ordᵣ Q))
              (map (mapᵖ (_[ η₀ ]ᵉ)) rest)
              (map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q))

    d₁ = above-∪ (polsₑ-ordᵣ i (ordᵣ Q)) (polsₑ-ordₑ i rest ∪ᴾ polsₑ-disj i (disj Q)) cq
    d₂ = above-∪ (polsₑ-ordₑ i rest) (polsₑ-disj i (disj Q)) (proj₂ d₁)

    hig : Q ⊩ idˢ ≾ˢ η₀
    hig = ≾ˢ-idʳ (updᵉ-above i b idˢ
            (subst (λ y → Q ⊩ evar i ≾̂ₑ y) (sym ([id]ᵉ b)) (hypₑ (Bᵉ.srcᵘ up))))

    open Raise {Q = Q} η₀ hig
    module K = Bᵉ.Keep i (Q ⊩_≾̂ₑ_) ⊩≾̂ₑ-refl transₑ (λ ε → ε) (_[ η₀ ]ᵉ) (λ {ε} → updᵉ-e i b ε)

    -- the value, where it stands for the unknown
    hit : sE η₀ i ≡ b [ η₀ ]ᵉ
    hit = trans (updᵉ-hit i b) (sym (updᵉ-e i b b (Bᵉ.capF up)))

    inst₀ : Q₀ ⊩ᴴ Q [ η₀ ]
    inst₀ = mk⊩ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m))
                 (λ m → hypᵣ (∈-map⁺ (mapᵖ (_[ η₀ ]ʳ)) m)) ordE
                 (λ m → hyp-ok₀ (∈-map⁺ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m))
      where
        ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q₀ ⊩ ε [ η₀ ]ᵉ ≾̂ₑ ε' [ η₀ ]ᵉ
        ordE {ε' = ε'} m with Bᵉ.clsᵘ (Bᵉ.capd up) m
        ... | inj₁ (refl , inj₁ refl) = subst (λ z → Q₀ ⊩ z ≾̂ₑ b [ η₀ ]ᵉ) (sym hit) ⊩≾̂ₑ-refl
        ... | inj₁ (refl , inj₂ p)    =
              subst (λ z → Q₀ ⊩ z ≾̂ₑ ε' [ η₀ ]ᵉ) (sym hit) (⊩-substₑ ∅ᴴ-⊩ᴴ p)
        ... | inj₂ m'                 = hypₑ (∈-map⁺ (mapᵖ (_[ η₀ ]ᵉ)) m')

    keepR : ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ (_[ η₀ ]ʳ)) (ordᵣ Q) → Q ⊩ ρ ≾̂ᵣ ρ'
    keepR m with ∈-map⁻ (mapᵖ (_[ η₀ ]ʳ)) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
          transᵣ (atʳ-≡ ⁺ (absᵉ-r⁺ i b ρ₀ (polsₑ-ordᵣ-∈⁺ i (ordᵣ Q) (proj₁ d₁) m₀)))
                 (transᵣ (hypᵣ m₀) (upʳ ρ₀'))

    keepE : ∀ {ε ε'} → (ε , ε') ∈ map (mapᵖ (_[ η₀ ]ᵉ)) rest → Q ⊩ ε ≾̂ₑ ε'
    keepE m with ∈-map⁻ (mapᵖ (_[ η₀ ]ᵉ)) m
    ... | (ε₀ , ε₀') , m₀ , refl =
          K.raiseL (Bᵉ.restL (Bᵉ.capd up) m₀) upᵉ (hypₑ (Bᵉ.rest⊆ᵘ (Bᵉ.capd up) m₀))

    keep₀ : Q ⊨ᴴ Q₀
    keep₀ = mk⊨ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) keepR keepE
                 (keep-disj⁺ η₀ (λ β → refl)
                    (λ {A} {ρ} m → absᵉ-r⁺ i b ρ (polsₑ-disj-∈⁺ i (disj Q) (proj₂ d₂) m)))

upʳ-step : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ)
         → (up : Bʳ.Ups i (ordᵣ Q))
         → above (polᵣᴴ (hyps (ets Q) (subᵥ Q) (Bʳ.restᵘ (Bʳ.capd up)) (ordₑ Q) (disj Q)) i)
           ≡ false
         → above (polᵣ-c i ⁺ C) ≡ false
         → Elim C Q
upʳ-step {Θ} C Q i up cq cc =
  mkElim (C [ η₀ ]ᶜ) Q₀ η₀ (≡̂ᶜ-refl _) inst₀ keep₀
         (λ δ h → <:̂ᶜ-subst h (Raiseʳ.raiseʳ-c i b hig ⁺ C cc))
  where
    b : RExp Θ
    b = Bʳ.cap up

    η₀ : Subst Θ Θ
    η₀ = updʳ i b

    rest = Bʳ.restᵘ (Bʳ.capd up)

    Q₀ : Hyps Θ
    Q₀ = hyps (ets Q) (subᵥ Q)
              (map (mapᵖ (_[ η₀ ]ʳ)) rest)
              (map (mapᵖ (_[ η₀ ]ᵉ)) (ordₑ Q))
              (map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q))

    d₁ = above-∪ (polsᵣ-ord i rest) (polsᵣ-disj i (disj Q)) cq

    hig : Q ⊩ idˢ ≾ˢ η₀
    hig = ≾ˢ-idʳ (updʳ-above i b idˢ
            (subst (λ y → Q ⊩ rvar i ≾̂ᵣ y) (sym ([id]ʳ b)) (hypᵣ (Bʳ.srcᵘ up))))

    open Raise {Q = Q} η₀ hig
    module K = Bʳ.Keep i (Q ⊩_≾̂ᵣ_) ⊩≾̂ᵣ-refl transᵣ (λ ρ → ρ) (_[ η₀ ]ʳ) (λ {ρ} → updʳ-r i b ρ)

    hit : sR η₀ i ≡ b [ η₀ ]ʳ
    hit = trans (updʳ-hit i b) (sym (updʳ-r i b b (Bʳ.capF up)))

    inst₀ : Q₀ ⊩ᴴ Q [ η₀ ]
    inst₀ = mk⊩ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) ordR
                 (λ m → hypₑ (∈-map⁺ (mapᵖ (_[ η₀ ]ᵉ)) m))
                 (λ m → hyp-ok₀ (∈-map⁺ (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) m))
      where
        ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Q₀ ⊩ ρ [ η₀ ]ʳ ≾̂ᵣ ρ' [ η₀ ]ʳ
        ordR {ρ' = ρ'} m with Bʳ.clsᵘ (Bʳ.capd up) m
        ... | inj₁ (refl , inj₁ refl) = subst (λ z → Q₀ ⊩ z ≾̂ᵣ b [ η₀ ]ʳ) (sym hit) ⊩≾̂ᵣ-refl
        ... | inj₁ (refl , inj₂ p)    =
              subst (λ z → Q₀ ⊩ z ≾̂ᵣ ρ' [ η₀ ]ʳ) (sym hit) (⊩-substᵣ ∅ᴴ-⊩ᴴ p)
        ... | inj₂ m'                 = hypᵣ (∈-map⁺ (mapᵖ (_[ η₀ ]ʳ)) m')

    keepR : ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ (_[ η₀ ]ʳ)) rest → Q ⊩ ρ ≾̂ᵣ ρ'
    keepR m with ∈-map⁻ (mapᵖ (_[ η₀ ]ʳ)) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
          K.raiseL (Bʳ.restL (Bʳ.capd up) m₀) upʳ (hypᵣ (Bʳ.rest⊆ᵘ (Bʳ.capd up) m₀))

    keepE : ∀ {ε ε'} → (ε , ε') ∈ map (mapᵖ (_[ η₀ ]ᵉ)) (ordₑ Q) → Q ⊩ ε ≾̂ₑ ε'
    keepE m with ∈-map⁻ (mapᵖ (_[ η₀ ]ᵉ)) m
    ... | (ε₀ , ε₀') , m₀ , refl =
          subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym (updʳ-e i b ε₀)) (sym (updʳ-e i b ε₀')) (hypₑ m₀)

    keep₀ : Q ⊨ᴴ Q₀
    keep₀ = mk⊨ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) keepR keepE
                 (keep-disj⁺ η₀ (λ β → refl)
                    (λ {A} {ρ} m → absʳ-r⁺ i b ρ (polsᵣ-disj-∈⁺ i (disj Q) (proj₂ d₁) m)))

-- The searches

upᵉ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ)
     → vᵉ F i ≡ false → Maybe (Elimᶠ F C Q)
upᵉ? F C Q i o with Bᵉ.upsOf i (ordₑ Q)
... | nothing = nothing
... | just up
    with above (polₑᴴ (hyps (ets Q) (subᵥ Q) (ordᵣ Q) (Bᵉ.restᵘ (Bᵉ.capd up)) (disj Q)) i) in c2
       | above (polₑ-c i ⁺ C) in c3
...   | false | false = just (upᵉ-step C Q i up c2 c3 , fixes-updᵉ i (Bᵉ.cap up) o)
...   | _     | _     = nothing

upʳ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ)
     → vʳ F i ≡ false → Maybe (Elimᶠ F C Q)
upʳ? F C Q i o with Bʳ.upsOf i (ordᵣ Q)
... | nothing = nothing
... | just up
    with above (polᵣᴴ (hyps (ets Q) (subᵥ Q) (Bʳ.restᵘ (Bʳ.capd up)) (ordₑ Q) (disj Q)) i) in c2
       | above (polᵣ-c i ⁺ C) in c3
...   | false | false = just (upʳ-step C Q i up c2 c3 , fixes-updʳ i (Bʳ.cap up) o)
...   | _     | _     = nothing

-- The bound of a type variable is another type variable, so the
-- substitution acts on the eternality and subtyping atoms too.

idᶠ : ∀ {n} → Fin n → Fin n
idᶠ β = β

updᵗ : ∀ {Θ} → TyVar Θ → TyVar Θ → Subst Θ Θ
updᵗ α γ = sub (λ β → tvar (upd α γ idᶠ β)) rvar evar

fixes-updᵗ : ∀ {Θ} {F : Vars Θ} → (α γ : TyVar Θ) → vᵗ F α ≡ false → Fixes F (updᵗ α γ)
fixes-updᵗ {F = F} α γ o =
  mkFixes (λ β h → cong tvar (upd-≢ α β γ idᶠ (⌊⌋-false (outside (vᵗ F) o h))))
          (λ _ _ → refl) (λ _ _ → refl)

fixᵗ-e : ∀ {Θ} → (α γ : TyVar Θ) → (ε : EExp Θ) → ε [ updᵗ α γ ]ᵉ ≡ ε
fixᵗ-e α γ (evar j)   = refl
fixᵗ-e α γ (econst c) = refl
fixᵗ-e α γ (ε ·̂ₑ ε')  = cong₂ _·̂ₑ_ (fixᵗ-e α γ ε) (fixᵗ-e α γ ε')
fixᵗ-e α γ (ε ⊔̂ₑ ε')  = cong₂ _⊔̂ₑ_ (fixᵗ-e α γ ε) (fixᵗ-e α γ ε')

fixᵗ-r : ∀ {Θ} → (α γ : TyVar Θ) → (ρ : RExp Θ) → ρ [ updᵗ α γ ]ʳ ≡ ρ
fixᵗ-r α γ (rvar j)   = refl
fixᵗ-r α γ (rconst c) = refl
fixᵗ-r α γ (ρ ·̂ᵣ ρ')  = cong₂ _·̂ᵣ_ (fixᵗ-r α γ ρ) (fixᵗ-r α γ ρ')
fixᵗ-r α γ (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔̂ᵣ_ (fixᵗ-r α γ ρ) (fixᵗ-r α γ ρ')
fixᵗ-r α γ ∣ ε ∣̂ᵉ     = cong ∣_∣̂ᵉ (fixᵗ-e α γ ε)

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
              (λ s ρ _ → atʳ-≡ s (fixᵗ-r α γ ρ)) (λ s ε _ → atᵉ-≡ s (fixᵗ-e α γ ε))
    where
      tv : ∀ s β → below (atˢ s ⌊ α ≟ᶠ β ⌋) ≡ false → atᵛ Q s (sTy (updᵗ α γ) β) (tvar β)
      tv ⁺ β q = lowt β
      tv ⁻ β q = atᵛ-≡ ⁻ (cong tvar (upd-≢ α β γ idᶠ (⌊⌋-false q)))

  monoᵗ-c : (s : Sign) → (C : OCType Θ) → below (polₜ-c α s C) ≡ false
          → atᶜ Q s (C [ updᵗ α γ ]ᶜ) C
  monoᵗ-c s (A ‼ ε) q = atᶜ-‼ s (monoᵗ-v s A q) (atᵉ-≡ s (fixᵗ-e α γ ε))

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
      → below (polₜᴴ (hyps (ets Q) (restᵗ s) (ordᵣ Q) (ordₑ Q) (disj Q)) α) ≡ false
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

    cS : ∀ {β γ} → (β , γ) ∈ restᵗ s → ⌊ α ≟ᶠ γ ⌋ ≡ false
    cS = polsₜ-sub-∈ α (restᵗ s) cq

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
                 (keep-ordʳ (ordᵣ Q) (λ m → m) (λ {ρ} {ρ'} m → fixedʳ (fixᵗ-r α γ₀ ρ')))
                 (keep-ordᵉ (ordₑ Q) (λ m → m) (λ {ε} {ε'} m → fixedᵉ (fixᵗ-e α γ₀ ε')))
                 keep-disj
      where
        et : ∀ {x} → x ∈ map (upd α γ₀ idᶠ) (ets Q) → Q ⊩ᴱ tvar x
        et m with ∈-map⁻ (upd α γ₀ idᶠ) m
        ... | β , m₀ , refl = <:̂ᵛ-eternalˡ (M.lowt β) (et-hyp m₀)

        sb : ∀ {x y} → (x , y) ∈ map (mapᵖ (upd α γ₀ idᶠ)) (restᵗ s)
           → Q ∣ tvar x <:̂ᵛ tvar y
        sb m with ∈-map⁻ (mapᵖ (upd α γ₀ idᶠ)) m
        ... | (β , γ) , m₀ , refl =
              <:̂ᵛ-trans (M.lowt β)
                (subst (λ y → Q ∣ tvar β <:̂ᵛ tvar y)
                       (sym (upd-≢ α γ γ₀ idᶠ (⌊⌋-false (cS m₀))))
                       (tvarₛ (hypᵗᵛ (subᵗ s m₀))))

stepᵗ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (α : TyVar Θ)
       → vᵗ F α ≡ false → Maybe (Elimᶠ F C Q)
stepᵗ? {Θ} F C Q α o with splitᵗ α (subᵥ Q)
... | nothing = nothing
... | just s
    with below (polₜ-v {Θ} α ⁻ (tvar (bndᵗ s))) in c1
       | below (polₜᴴ (hyps (ets Q) (restᵗ s) (ordᵣ Q) (ordₑ Q) (disj Q)) α) in c2
       | below (polₜ-c α ⁺ C) in c3
...   | false | false | false = just (stepᵗ C Q α s c1 c2 c3 , fixes-updᵗ α (bndᵗ s) o)
...   | _     | _     | _     = nothing

------------------------------------------------------------------------
-- Elimination by equality: an unknown the hypotheses equate with an
-- expression is replaced by it everywhere, and the orderings the
-- replacement makes reflexive are dropped. Under the hypotheses the
-- replacement moves nothing.

-- The pairs whose two sides differ

apart : ∀ {X : Set} → DecidableEquality X → List (X × X) → List (X × X)
apart _≟_ = filter (λ p → ¬? (proj₁ p ≟ proj₂ p))

apart-⊆ : ∀ {X : Set} → (_≟_ : DecidableEquality X) → ∀ {p l}
        → p ∈ apart _≟_ l → p ∈ l
apart-⊆ _≟_ m = proj₁ (∈-filter⁻ (λ p → ¬? (proj₁ p ≟ proj₂ p)) m)

apart-∈ : ∀ {X : Set} → (_≟_ : DecidableEquality X) → ∀ {a b l}
        → (a , b) ∈ l → (a ≡ b) ⊎ ((a , b) ∈ apart _≟_ l)
apart-∈ _≟_ {a} {b} m with a ≟ b
... | yes e  = inj₁ e
... | no  ¬e = inj₂ (∈-filter⁺ (λ p → ¬? (proj₁ p ≟ proj₂ p)) m ¬e)

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
        ... | inj₁ e  = subst (Q₀ ⊩ ρ [ η₀ ]ʳ ≾̂ᵣ_) e ⊩≾̂ᵣ-refl
        ... | inj₂ m' = hypᵣ m'

        ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Q₀ ⊩ ε [ η₀ ]ᵉ ≾̂ₑ ε' [ η₀ ]ᵉ
        ordE {ε} m with apart-∈ _≟ᵉ_ (∈-map⁺ (mapᵖ (_[ η₀ ]ᵉ)) m)
        ... | inj₁ e  = subst (Q₀ ⊩ ε [ η₀ ]ᵉ ≾̂ₑ_) e ⊩≾̂ₑ-refl
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
        ... | inj₁ e  = subst (Q₀ ⊩ ρ [ η₀ ]ʳ ≾̂ᵣ_) e ⊩≾̂ᵣ-refl
        ... | inj₂ m' = hypᵣ m'

    keep₀ : Q ⊨ᴴ Q₀
    keep₀ = mk⊨ᴴ et-hyp (λ m → tvarₛ (hypᵗᵛ m))
                 (λ m → keep-ordʳ (ordᵣ Q) (λ q → q) (λ {ρ} {ρ'} _ → raiseʳ ρ')
                                  (apart-⊆ _≟ʳ_ m))
                 (keep-ordᵉ (ordₑ Q) (λ q → q) (λ {ε} {ε'} _ → raiseᵉ ε'))
                 keep-disj

-- One step at a type variable: the hypotheses bound it and `γ` by each
-- other, and it is sent to `γ`; the subtyping atoms made reflexive are
-- dropped

equateᵗ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (α γ : TyVar Θ)
        → Q ⊩ᵗᵛ α ≾ γ → Q ⊩ᵗᵛ γ ≾ α → Elim C Q
equateᵗ {Θ} C Q α γ up down =
  mkElim (C [ η₀ ]ᶜ) Q₀ η₀ (≡̂ᶜ-refl _) inst₀ keep₀
         (λ δ h → <:̂ᶜ-subst h (sameᶜ ⁺ C))
  where
    f : TyVar Θ → TyVar Θ
    f = upd α γ idᶠ

    η₀ : Subst Θ Θ
    η₀ = updᵗ α γ

    Q₀ : Hyps Θ
    Q₀ = hyps (map f (ets Q))
              (apart _≟ᶠ_ (map (mapᵖ f) (subᵥ Q)))
              (map (mapᵖ (_[ η₀ ]ʳ)) (ordᵣ Q))
              (map (mapᵖ (_[ η₀ ]ᵉ)) (ordₑ Q))
              (map (mapᵈ (_[ η₀ ]ᵛ) (_[ η₀ ]ʳ)) (disj Q))

    both : ∀ β → (Q ⊩ᵗᵛ f β ≾ β) × (Q ⊩ᵗᵛ β ≾ f β)
    both β with α ≟ᶠ β
    ... | yes refl = subst (λ x → (Q ⊩ᵗᵛ x ≾ α) × (Q ⊩ᵗᵛ α ≾ x)) (sym (upd-≡ α γ idᶠ))
                           (down , up)
    ... | no  ¬p   = subst (λ x → (Q ⊩ᵗᵛ x ≾ β) × (Q ⊩ᵗᵛ β ≾ x)) (sym (upd-≢ α β γ idᶠ ¬p))
                           (reflᵗᵛ , reflᵗᵛ)

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
                 (keep-ordʳ (ordᵣ Q) (λ m → m) (λ {ρ} {ρ'} m → fixedʳ (fixᵗ-r α γ ρ')))
                 (keep-ordᵉ (ordₑ Q) (λ m → m) (λ {ε} {ε'} m → fixedᵉ (fixᵗ-e α γ ε')))
                 keep-disj
      where
        et : ∀ {x} → x ∈ map f (ets Q) → Q ⊩ᴱ tvar x
        et m with ∈-map⁻ f m
        ... | β , m₀ , refl = <:̂ᵛ-eternalˡ (lowt β) (et-hyp m₀)

        sb : ∀ {x y} → (x , y) ∈ apart _≟ᶠ_ (map (mapᵖ f) (subᵥ Q)) → Q ∣ tvar x <:̂ᵛ tvar y
        sb m with ∈-map⁻ (mapᵖ f) (apart-⊆ _≟ᶠ_ m)
        ... | (β , β') , m₀ , refl =
              <:̂ᵛ-trans (lowt β) (<:̂ᵛ-trans (tvarₛ (hypᵗᵛ m₀)) (hit β'))

-- The search at the type variables: each strongly connected component
-- of the subtyping atoms has a representative (`Reach`), the first
-- member in the order the variables of `F`, then the others, each by
-- index. The first member outside `F` that is not its representative
-- is sent to it; a component with two members in `F` keeps them both.

withMem : ∀ {X : Set} → (l : List X) → List (Σ[ a ∈ X ] (a ∈ l))
withMem []      = []
withMem (a ∷ l) = (a , here refl) ∷ map (λ { (b , m) → b , there m }) (withMem l)

equateᵗ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → Maybe (Elimᶠ F C Q)
equateᵗ? {Θ} F C Q = try closure (withMem vs)
  where
    Edge : TyVar Θ → TyVar Θ → Set
    Edge a b = (a , b) ∈ subᵥ Q

    -- the type variables with an atom on each side: only they lie on a
    -- cycle
    vs : List (TyVar Θ)
    vs = filterᵇ (λ β → any (λ p → ⌊ proj₁ p ≟ᶠ β ⌋) (subᵥ Q)
                      ∧ any (λ p → ⌊ proj₂ p ≟ᶠ β ⌋) (subᵥ Q))
                 (fins (nTy Θ))

    open Reachability _≟ᶠ_ Edge (map (λ { ((a , b) , m) → a , b , m }) (withMem (subᵥ Q))) vs
      using (Closure; closure; rep)

    ord : List (Σ[ v ∈ TyVar Θ ] v ∈ vs)
    ord = filterᵇ (λ p → vᵗ F (proj₁ p)) (withMem vs)
       ++ filterᵇ (λ p → not (vᵗ F (proj₁ p))) (withMem vs)

    chain : ∀ {a b} → Star Edge a b → Q ⊩ᵗᵛ a ≾ b
    chain = fold (Q ⊩ᵗᵛ_≾_) (λ e p → transᵗᵛ (hypᵗᵛ e) p) reflᵗᵛ

    at : (α : TyVar Θ) → vᵗ F α ≡ false → Maybe (Σ[ γ ∈ TyVar Θ ] Star Edge α γ × Star Edge γ α)
       → Maybe (Elimᶠ F C Q)
    at α o (just (γ , p , q)) with α ≟ᶠ γ
    ... | no  _ = just (equateᵗ C Q α γ (chain p) (chain q) , fixes-updᵗ α γ o)
    ... | yes _ = nothing
    at α o nothing = nothing

    try : Closure → List (Σ[ v ∈ TyVar Θ ] v ∈ vs) → Maybe (Elimᶠ F C Q)
    try K [] = nothing
    try K ((α , mα) ∷ l) with vᵗ F α in o
    ... | true  = try K l
    ... | false with at α o (rep K ord mα)
    ...   | just r  = just r
    ...   | nothing = try K l

-- The expressions an ordering sets against an unknown, and those fit to
-- replace it: free of it, and an unknown only if of smaller index

facingₑ : ∀ {Θ} → EVar Θ → List (EExp Θ × EExp Θ) → List (EExp Θ)
facingₑ i [] = []
facingₑ i ((ε , ε') ∷ l) with ε ≟ᵉ evar i | ε' ≟ᵉ evar i
... | yes _ | _     = ε' ∷ facingₑ i l
... | no  _ | yes _ = ε ∷ facingₑ i l
... | no  _ | no  _ = facingₑ i l

facingᵣ : ∀ {Θ} → RVar Θ → List (RExp Θ × RExp Θ) → List (RExp Θ)
facingᵣ i [] = []
facingᵣ i ((ρ , ρ') ∷ l) with ρ ≟ʳ rvar i | ρ' ≟ʳ rvar i
... | yes _ | _     = ρ' ∷ facingᵣ i l
... | no  _ | yes _ = ρ ∷ facingᵣ i l
... | no  _ | no  _ = facingᵣ i l

fitₑ : ∀ {Θ} → EVar Θ → EExp Θ → 𝔹
fitₑ i (evar j) = toℕ j <ᵇ toℕ i
fitₑ i ε        = not (occᵉ-e i ε)

fitᵣ : ∀ {Θ} → RVar Θ → RExp Θ → 𝔹
fitᵣ i (rvar j) = toℕ j <ᵇ toℕ i
fitᵣ i ρ        = not (occʳ-r i ρ)

-- A test of entailed ordering on each grade sort; a `nothing` decides
-- nothing

record Entails : Set where
  constructor entails
  field
    entᵣ? : ∀ {Θ} → (Q : Hyps Θ) → (ρ ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
    entₑ? : ∀ {Θ} → (Q : Hyps Θ) → (ε ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')

module _ (ent : Entails) where

  open Entails ent

  -- The search: the first fit expression facing the unknown that the
  -- test equates with it

  equateᵉ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ)
           → vᵉ F i ≡ false → Maybe (Elimᶠ F C Q)
  equateᵉ? {Θ} F C Q i o = try (facingₑ i (ordₑ Q))
    where
      try : List (EExp Θ) → Maybe (Elimᶠ F C Q)
      try [] = nothing
      try (b ∷ bs) with fitₑ i b | entₑ? Q (evar i) b | entₑ? Q b (evar i)
      ... | true | just p | just q = just (equateᵉ C Q i b (p , q) , fixes-updᵉ i b o)
      ... | _    | _      | _      = try bs

  equateʳ? : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ)
           → vʳ F i ≡ false → Maybe (Elimᶠ F C Q)
  equateʳ? {Θ} F C Q i o = try (facingᵣ i (ordᵣ Q))
    where
      try : List (RExp Θ) → Maybe (Elimᶠ F C Q)
      try [] = nothing
      try (b ∷ bs) with fitᵣ i b | entᵣ? Q (rvar i) b | entᵣ? Q b (rvar i)
      ... | true | just p | just q = just (equateʳ C Q i b (p , q) , fixes-updʳ i b o)
      ... | _    | _      | _      = try bs

  -- A step by equality first, then one against the bounds below, then
  -- one against a bound above, at an unknown outside `F`

  anyStep : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → Maybe (Elimᶠ F C Q)
  anyStep {Θ} F C Q with first (vᵉ F) (equateᵉ? F C Q) (fins (nE Θ))
  ... | just r  = just r
  ... | nothing with first (vʳ F) (equateʳ? F C Q) (fins (nR Θ))
  ...   | just r  = just r
  ...   | nothing with first (vᵉ F) (stepᵉ? F C Q) (fins (nE Θ))
  ...     | just r  = just r
  ...     | nothing with first (vʳ F) (stepʳ? F C Q) (fins (nR Θ))
  ...       | just r  = just r
  ...       | nothing with first (vᵉ F) (upᵉ? F C Q) (fins (nE Θ))
  ...         | just r  = just r
  ...         | nothing with first (vʳ F) (upʳ? F C Q) (fins (nR Θ))
  ...           | just r  = just r
  ...           | nothing with equateᵗ? F C Q
  ...             | just r  = just r
  ...             | nothing = first (vᵗ F) (stepᵗ? F C Q) (fins (nTy Θ))

  reduce : ∀ {Θ} → (F : Vars Θ) → ℕ → (C : OCType Θ) → (Q : Hyps Θ) → Elimᶠ F C Q
  reduce F zero    C Q = idElim C Q , fixes-id
  reduce F (suc n) C Q with anyStep F C Q
  ... | nothing = idElim C Q , fixes-id
  ... | just r  = r ⨾ᶠ reduce F n (Ĉ (proj₁ r)) (Q̂ (proj₁ r))

  -- One round per unknown suffices: a step removes one

  eliminate : ∀ {Θ} → (F : Vars Θ) → (C : OCType Θ) → (Q : Hyps Θ) → Elimᶠ F C Q
  eliminate {Θ} F C Q = reduce F (nE Θ + nR Θ + nTy Θ) C Q
