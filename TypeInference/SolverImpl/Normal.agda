------------------------------------------------------------------
-- Deciding an entailed ordering of open grade expressions        --
--                                                                --
-- Both sides are put in the sum-of-products normal form of       --
-- `SolverImpl.Product` and compared alternative by alternative,  --
-- the answer glued back with `eqᵣ`/`monoᵣ`/`transᵣ`. Two         --
-- alternatives are compared as sequences of atoms in which a     --
-- missing position is the unit: an atom may be matched against   --
-- nothing, on the right when the unit is below it and on the     --
-- left when it is below the unit, and the top on the right       --
-- stands for any run of atoms on the left.                       --
--                                                                --
-- Two atoms are compared by the grade's own order, by identity,  --
-- and along the atomic hypotheses: those assumed orderings whose --
-- two sides are single atoms, chained. An effect hypothesis      --
-- carries over to the images of its atoms. Hypotheses with a     --
-- product or a join on either side are not used.                 --
--                                                                --
-- The sums are met by the universal property of the join:        --
-- `⊔-lub` reduces the left side to each of its alternatives in   --
-- turn, and `⊔-ubˡ`/`⊔-ubʳ` pick out an alternative of the right --
-- side for each. So a bounded ∀/∃ over alternatives sits above a --
-- pointwise comparison of products. The right side is first      --
-- grouped by skeleton, and each group that varies in one slot    --
-- folded into one alternative, that slot holding the join of its --
-- constants (`foldSumₑ`/`foldSumᵣ`).                             --
--                                                                --
-- `⊩-reflectᵣ`/`⊩-reflectₑ` are the closed special case: a       --
-- variable-free expression is convertible to the constant it     --
-- evaluates to, in both directions.                              --
------------------------------------------------------------------

open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps as H

module TypeInference.SolverImpl.Normal
  (S : LanguageSpec)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))              -- optional unit-minimality of `_≾ᵣ_`
  (umin?ₑ : Maybe (H.UnitMinₑ S))              -- optional unit-minimality of `_≾ₑ_`
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.SolverImpl.Product S public

-- The unit is below anything as soon as the option is supplied

min≾ₑ : ∀ {Θ} {Q : Hyps Θ} {ε : EExp Θ} → Maybe UnitMinₑ → Maybe (Q ⊩ ûₑ ≾̂ₑ ε)
min≾ₑ (just p) = just (minₑ p)
min≾ₑ nothing  = nothing

min≾ᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → Maybe UnitMinᵣ → Maybe (Q ⊩ ûᵣ ≾̂ᵣ ρ)
min≾ᵣ (just p) = just (minᵣ p)
min≾ᵣ nothing  = nothing

------------------------------------------------------------------
-- Atomic hypotheses
--
-- Two atoms are linked when they are equal, or are constants ordered
-- by the grade's own order. `a` reaches `b` along a chain of edges
-- when `a` is linked to the first source, each target to the next
-- source, and the last target to `b`. The search saturates the atoms
-- reached from `a`, one round per edge.

module Chains {A : Set} (_⊑_ : A → A → Set)
              (refl⊑  : ∀ {a} → a ⊑ a)
              (trans⊑ : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c)
              (link?  : (a b : A) → Maybe (a ⊑ b))
              (edges  : List (Σ[ a ∈ A ] Σ[ b ∈ A ] a ⊑ b))
              where

  find : ∀ {a} → List (Σ[ c ∈ A ] a ⊑ c) → (b : A) → Maybe (a ⊑ b)
  find []            b = nothing
  find ((c , w) ∷ s) b with link? c b
  ... | just l  = just (trans⊑ w l)
  ... | nothing = find s b

  grow : ∀ {a} → List (Σ[ c ∈ A ] Σ[ d ∈ A ] c ⊑ d)
       → List (Σ[ c ∈ A ] a ⊑ c) → List (Σ[ c ∈ A ] a ⊑ c)
  grow []                 s = s
  grow ((c , d , p) ∷ es) s with grow es s
  ... | s' with find s' c | find s' d
  ...   | just w | nothing = (d , trans⊑ w p) ∷ s'
  ...   | _      | _       = s'

  sat : ∀ {a} → ℕ → List (Σ[ c ∈ A ] a ⊑ c) → List (Σ[ c ∈ A ] a ⊑ c)
  sat zero    s = s
  sat (suc n) s = sat n (grow edges s)

  reach? : (a b : A) → Maybe (a ⊑ b)
  reach? a = find (sat (length edges) ((a , refl⊑) ∷ []))

-- An atomic hypothesis, as an edge between its two atoms

EEdge : ∀ {Θ} → Hyps Θ → Set
EEdge {Θ} Q = Σ[ a ∈ EAtom Θ ] Σ[ b ∈ EAtom Θ ] (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)

REdge : ∀ {Θ} → Hyps Θ → Set
REdge {Θ} Q = Σ[ a ∈ RAtom Θ ] Σ[ b ∈ RAtom Θ ] (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)

-- A side that is a single atom

atomᵉ? : ∀ {Θ} → (ε : EExp Θ) → Maybe (Σ[ a ∈ EAtom Θ ] ⟦ a ⟧ᵉᵃ ≡ ε)
atomᵉ? (evar i)   = just (av i , refl)
atomᵉ? (econst c) = just (ac c , refl)
atomᵉ? _          = nothing

atomʳ? : ∀ {Θ} → (ρ : RExp Θ) → Maybe (Σ[ a ∈ RAtom Θ ] ⟦ a ⟧ʳᵃ ≡ ρ)
atomʳ? (rvar i)       = just (rv i , refl)
atomʳ? (rconst c)     = just (rc c , refl)
atomʳ? ∣ evar i ∣̂ᵉ    = just (rm i , refl)
atomʳ? _              = nothing

-- The atomic hypotheses among a list of assumed orderings

edgesₑ : ∀ {Θ} {Q : Hyps Θ} → (l : List (EExp Θ × EExp Θ))
       → (∀ {p} → p ∈ l → p ∈ ordₑ Q) → List (EEdge Q)
edgesₑ []             k = []
edgesₑ ((ε , ε') ∷ l) k with atomᵉ? ε | atomᵉ? ε'
... | just (a , refl) | just (b , refl) =
      (a , b , hypₑ (k (here refl))) ∷ edgesₑ l (λ m → k (there m))
... | _               | _               = edgesₑ l (λ m → k (there m))

edgesᵣ : ∀ {Θ} {Q : Hyps Θ} → (l : List (RExp Θ × RExp Θ))
       → (∀ {p} → p ∈ l → p ∈ ordᵣ Q) → List (REdge Q)
edgesᵣ []             k = []
edgesᵣ ((ρ , ρ') ∷ l) k with atomʳ? ρ | atomʳ? ρ'
... | just (a , refl) | just (b , refl) =
      (a , b , hypᵣ (k (here refl))) ∷ edgesᵣ l (λ m → k (there m))
... | _               | _               = edgesᵣ l (λ m → k (there m))

-- The image of an effect atom, and of an effect edge by `map-mono`

∣_∣ᵃ : ∀ {Θ} → EAtom Θ → RAtom Θ
∣ ac c ∣ᵃ = rc (mapᵉ c)
∣ av i ∣ᵃ = rm i

∣⟦_⟧∣ : ∀ {Θ} → (a : EAtom Θ) → ∣ ⟦ a ⟧ᵉᵃ ∣̂ᵉ ≡̂ᵣ ⟦ ∣ a ∣ᵃ ⟧ʳᵃ
∣⟦ ac c ⟧∣ = ≡̂ᵣ-map-const
∣⟦ av i ⟧∣ = ≡̂ᵣ-refl

mapEdge : ∀ {Θ} {Q : Hyps Θ} → EEdge Q → REdge Q
mapEdge (a , b , p) =
  ∣ a ∣ᵃ , ∣ b ∣ᵃ , transᵣ (eqᵣ (≡̂ᵣ-sym ∣⟦ a ⟧∣)) (transᵣ (map-mono p) (eqᵣ ∣⟦ b ⟧∣))

-- Linked atoms

linkₑ? : ∀ {Θ} {Q : Hyps Θ} → (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
linkₑ? (ac c) (ac d) with c ≾ₑ? d
... | yes p = just (atomₑ p)
... | no _  = nothing
linkₑ? (av i) (av j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ₑ-refl
... | no _     = nothing
linkₑ? _      _      = nothing

linkᵣ? : ∀ {Θ} {Q : Hyps Θ} → (a b : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
linkᵣ? (rc c) (rc d) with c ≾ᵣ? d
... | yes p = just (atomᵣ p)
... | no _  = nothing
linkᵣ? (rv i) (rv j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ᵣ-refl
... | no _     = nothing
linkᵣ? (rm i) (rm j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ᵣ-refl
... | no _     = nothing
linkᵣ? _      _      = nothing

-- Reachability along the atomic hypotheses; on the resource side
-- along the resource ones and the images of the effect ones

reachₑ? : ∀ {Θ} {Q : Hyps Θ} → (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
reachₑ? {Q = Q} =
  Chains.reach? (λ a b → Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ) ⊩≾̂ₑ-refl transₑ linkₑ?
                (edgesₑ (ordₑ Q) (λ m → m))

reachᵣ? : ∀ {Θ} {Q : Hyps Θ} → (a b : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
reachᵣ? {Q = Q} =
  Chains.reach? (λ a b → Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ) ⊩≾̂ᵣ-refl transᵣ linkᵣ?
                (edgesᵣ (ordᵣ Q) (λ m → m) ++ map mapEdge (edgesₑ (ordₑ Q) (λ m → m)))

-- Anything is below an atom that the top is linked to or reaches

ceilₑ : ∀ {Θ} {Q : Hyps Θ} {ε : EExp Θ} → (b : EAtom Θ) → Maybe (Q ⊩ ε ≾̂ₑ ⟦ b ⟧ᵉᵃ)
ceilₑ {Q = Q} b with linkₑ? {Q = Q} (ac ⊤ₑ) b <∣> reachₑ? (ac ⊤ₑ) b
... | just p  = just (transₑ topₑ p)
... | nothing = nothing

ceilᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → (b : RAtom Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
ceilᵣ {Q = Q} b with linkᵣ? {Q = Q} (rc ⊤ᵣ) b <∣> reachᵣ? (rc ⊤ᵣ) b
... | just p  = just (transᵣ topᵣ p)
... | nothing = nothing

------------------------------------------------------------------
-- Products
--
-- Two products are compared as sequences whose missing positions
-- are the unit. A step consumes an atom from at least one side:
--
--   * match the two heads, by monotonicity (`atom≾`);
--   * pass over the right head, the unit being below it (`unit≾`);
--   * pass over the left head, it being below the unit (`≾unit`);
--   * absorb the left head into a right head above the top, which
--     stays to absorb more, as `a · ⊤ ≾ ⊤`;
--   * pass over the atom after a constant head on the right, the
--     unit being below it, and merge that constant with what then
--     follows it, as `consₑ`/`consᵣ` do (`mergeʳ`);
--   * the same on the left, the atom being below the unit (`mergeˡ`).
--
-- The steps are tried in that order, and a failure falls through to
-- the next, so the search succeeds whenever the two products can be
-- aligned in order: each left atom matched, absorbed or below the
-- unit, each right atom matched, absorbing a run, or above the unit,
-- constants on either side of an atom passed over being multiplied.
-- The order decides only which derivation is found first. Each step
-- shortens the two sides together, and their total length is the
-- fuel.
--
-- What it does not find: anything that needs a hypothesis other than
-- an atomic one. A left alternative below the join of right
-- alternatives only jointly is found when those alternatives form a
-- group that the fold makes one; not when they have different
-- skeletons, or form a group that varies in more than one slot.
--
-- The products are read back with a trailing unit (`⟦_⟧ᵉˢ`), so that
-- each step is one use of `monoₑ`; `prod≾ₑ` converts at the ends.

-- An atom below an atom: linked, below an atom above the top, or
-- reached along the atomic hypotheses

atom≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
atom≾ₑ a b = linkₑ? a b <∣> ceilₑ b <∣> reachₑ? a b

-- The unit below an atom: as the constant atom `uₑ`, or by
-- unit-minimality

unit≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (b : EAtom Θ) → Maybe (Q ⊩ ûₑ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
unit≾ₑ b = atom≾ₑ (ac uₑ) b <∣> min≾ₑ umin?ₑ

-- An atom below the unit, as the constant atom `uₑ`

≾unitₑ : ∀ {Θ} {Q : Hyps Θ} → (a : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ûₑ)
≾unitₑ a = atom≾ₑ a (ac uₑ)

-- An atom absorbed into an atom above the top

absorbs≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (a b : EAtom Θ)
          → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ·̂ₑ ⟦ b ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
absorbs≾ₑ a b = ceilₑ b

-- The four steps, each given the comparison of what remains

matchₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → (a b : EAtom Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
       → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ·̂ₑ ε ≾̂ₑ ⟦ b ⟧ᵉᵃ ·̂ₑ ε')
matchₑ {Q = Q} a b r with atom≾ₑ {Q = Q} a b
... | nothing = nothing
... | just p with r
...   | just q  = just (monoₑ p q)
...   | nothing = nothing

skipʳₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → (b : EAtom Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
       → Maybe (Q ⊩ ε ≾̂ₑ ⟦ b ⟧ᵉᵃ ·̂ₑ ε')
skipʳₑ {Q = Q} b r with unit≾ₑ {Q = Q} b
... | nothing = nothing
... | just p with r
...   | just q  = just (transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-identityˡ)) (monoₑ p q))
...   | nothing = nothing

skipˡₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → (a : EAtom Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
       → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ·̂ₑ ε ≾̂ₑ ε')
skipˡₑ {Q = Q} a r with ≾unitₑ {Q = Q} a
... | nothing = nothing
... | just p with r
...   | just q  = just (transₑ (monoₑ p q) (eqₑ ≡̂ₑ-identityˡ))
...   | nothing = nothing

intoTopₑ : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → (a b : EAtom Θ)
         → Maybe (Q ⊩ ε ≾̂ₑ ⟦ b ⟧ᵉᵃ ·̂ₑ ε')
         → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ·̂ₑ ε ≾̂ₑ ⟦ b ⟧ᵉᵃ ·̂ₑ ε')
intoTopₑ {Q = Q} a b r with absorbs≾ₑ {Q = Q} a b
... | nothing = nothing
... | just p with r
...   | just q  = just (transₑ (monoₑ ⊩≾̂ₑ-refl q)
                               (transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-assoc)) (monoₑ p ⊩≾̂ₑ-refl)))
...   | nothing = nothing

-- An atom passed over between a constant and the rest, the constant
-- merged with what follows by `consₑ`

spliceʳₑ : ∀ {Θ} {Q : Hyps Θ} {ε} → (c : E) → (b : EAtom Θ) → (bs : List (EAtom Θ))
         → Maybe (Q ⊩ ε ≾̂ₑ ⟦ consₑ (ac c) bs ⟧ᵉˢ)
         → Maybe (Q ⊩ ε ≾̂ₑ econst c ·̂ₑ (⟦ b ⟧ᵉᵃ ·̂ₑ ⟦ bs ⟧ᵉˢ))
spliceʳₑ {Q = Q} c b bs r with unit≾ₑ {Q = Q} b
... | nothing = nothing
... | just p with r
...   | just q  = just (transₑ q (transₑ (eqₑ (≡̂ₑ-trans (consₑ-≡ (ac c) bs)
                                                      (≡̂ₑ-cong ≡̂ₑ-refl (≡̂ₑ-sym ≡̂ₑ-identityˡ))))
                                          (monoₑ ⊩≾̂ₑ-refl (monoₑ p ⊩≾̂ₑ-refl))))
...   | nothing = nothing

spliceˡₑ : ∀ {Θ} {Q : Hyps Θ} {ε'} → (c : E) → (a : EAtom Θ) → (as : List (EAtom Θ))
         → Maybe (Q ⊩ ⟦ consₑ (ac c) as ⟧ᵉˢ ≾̂ₑ ε')
         → Maybe (Q ⊩ econst c ·̂ₑ (⟦ a ⟧ᵉᵃ ·̂ₑ ⟦ as ⟧ᵉˢ) ≾̂ₑ ε')
spliceˡₑ {Q = Q} c a as r with ≾unitₑ {Q = Q} a
... | nothing = nothing
... | just p with r
...   | just q  = just (transₑ (monoₑ ⊩≾̂ₑ-refl (monoₑ p ⊩≾̂ₑ-refl))
                               (transₑ (eqₑ (≡̂ₑ-trans (≡̂ₑ-cong ≡̂ₑ-refl ≡̂ₑ-identityˡ)
                                                      (≡̂ₑ-sym (consₑ-≡ (ac c) as))))
                                       q))
...   | nothing = nothing

-- The same, at a side that starts with a constant and an atom, given
-- the comparison against any shorter side

mergeʳₑ : ∀ {Θ} {Q : Hyps Θ} {ε} → ((bs : List (EAtom Θ)) → Maybe (Q ⊩ ε ≾̂ₑ ⟦ bs ⟧ᵉˢ))
        → (bs : List (EAtom Θ)) → Maybe (Q ⊩ ε ≾̂ₑ ⟦ bs ⟧ᵉˢ)
mergeʳₑ r (ac c ∷ b ∷ bs) = spliceʳₑ c b bs (r (consₑ (ac c) bs))
mergeʳₑ r _               = nothing

mergeˡₑ : ∀ {Θ} {Q : Hyps Θ} {ε'} → ((as : List (EAtom Θ)) → Maybe (Q ⊩ ⟦ as ⟧ᵉˢ ≾̂ₑ ε'))
        → (as : List (EAtom Θ)) → Maybe (Q ⊩ ⟦ as ⟧ᵉˢ ≾̂ₑ ε')
mergeˡₑ r (ac c ∷ a ∷ as) = spliceˡₑ c a as (r (consₑ (ac c) as))
mergeˡₑ r _               = nothing

-- The steps, with fuel for as many as the two sides have atoms

prodˢ≾ₑ : ∀ {Θ} {Q : Hyps Θ} → ℕ → (as bs : List (EAtom Θ))
        → Maybe (Q ⊩ ⟦ as ⟧ᵉˢ ≾̂ₑ ⟦ bs ⟧ᵉˢ)
prodˢ≾ₑ n       []       []       = just ⊩≾̂ₑ-refl
prodˢ≾ₑ zero    _        _        = nothing
prodˢ≾ₑ (suc n) []       (b ∷ bs) =
  skipʳₑ b (prodˢ≾ₑ n [] bs)
  <∣> mergeʳₑ (prodˢ≾ₑ n []) (b ∷ bs)
prodˢ≾ₑ (suc n) (a ∷ as) []       =
  skipˡₑ a (prodˢ≾ₑ n as [])
  <∣> mergeˡₑ (λ as' → prodˢ≾ₑ n as' []) (a ∷ as)
prodˢ≾ₑ (suc n) (a ∷ as) (b ∷ bs) =
  matchₑ a b (prodˢ≾ₑ n as bs)
  <∣> skipʳₑ b (prodˢ≾ₑ n (a ∷ as) bs)
  <∣> skipˡₑ a (prodˢ≾ₑ n as (b ∷ bs))
  <∣> intoTopₑ a b (prodˢ≾ₑ n as (b ∷ bs))
  <∣> mergeʳₑ (prodˢ≾ₑ n (a ∷ as)) (b ∷ bs)
  <∣> mergeˡₑ (λ as' → prodˢ≾ₑ n as' (b ∷ bs)) (a ∷ as)

prod≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (as bs : List (EAtom Θ))
       → Maybe (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ ⟦ bs ⟧ᵉᵖ)
prod≾ₑ as bs with prodˢ≾ₑ (length as + length bs) as bs
... | just p  = just (transₑ (eqₑ (≡̂ₑ-sym (⟦⟧ᵉᵖ-≡ as)))
                             (transₑ p (eqₑ (⟦⟧ᵉᵖ-≡ bs))))
... | nothing = nothing

-- One alternative against a whole sum: some alternative of the sum
-- bounds it, and the join is above that one

altSum≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (as : List (EAtom Θ))
         → (t : Alts (List (EAtom Θ)))
         → Maybe (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ ⟦ t ⟧ᵉᵖ⁺)
altSum≾ₑ as (alt P) = prod≾ₑ as P
altSum≾ₑ as (P ∷⁺ t) with prod≾ₑ as P
... | just p  = just (transₑ p ⊔-ubˡₑ)
... | nothing with altSum≾ₑ as t
...   | just q  = just (transₑ q ⊔-ubʳₑ)
...   | nothing = nothing

-- The whole comparison: every alternative of the left side is below
-- the right side, and their join is then below it too

sum≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (s t : Alts (List (EAtom Θ)))
      → Maybe (Q ⊩ ⟦ s ⟧ᵉᵖ⁺ ≾̂ₑ ⟦ t ⟧ᵉᵖ⁺)
sum≾ₑ (alt P)  t = altSum≾ₑ P t
sum≾ₑ (P ∷⁺ s) t with altSum≾ₑ P t | sum≾ₑ s t
... | just p | just q = just (⊔-lubₑ p q)
... | _      | _      = nothing

-- The right side is compared folded: each of its groups that varies in
-- one slot is one alternative, above each of the group's members

foldₑ-≡ᵖ : ∀ {Θ} → (ε : EExp Θ) → ε ≡̂ₑ ⟦ foldSumₑ (nrmₑ ε) ⟧ᵉᵖ⁺
foldₑ-≡ᵖ ε =
  ≡̂ₑ-trans (nrmₑ-≡ ε)
  (≡̂ₑ-trans (≡̂ₑ-sym (foldSumₑ-≡ (nrmₑ ε))) (⟦⟧ᵉᵖ⁺-≡ (foldSumₑ (nrmₑ ε))))

decide≾ₑ : ∀ {Θ} {Q : Hyps Θ} → (ε ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
decide≾ₑ ε ε' with sum≾ₑ (nrmₑ ε) (foldSumₑ (nrmₑ ε'))
... | just p  = just (transₑ (eqₑ (nrmₑ-≡ᵖ ε)) (transₑ p (eqₑ (≡̂ₑ-sym (foldₑ-≡ᵖ ε')))))
... | nothing = nothing

------------------------------------------------------------------
-- Resource grades: the same, with a third kind of atom, the image
-- `∣ x ∣` of an effect variable, which is treated as a variable. The
-- unit is below it by unit-minimality of either sort, the latter
-- carried through the morphism by `map-mono`, as `∣ u ∣ = u`.

∣û∣ₑ : ∀ {Θ} → ûᵣ {Θ} ≡̂ᵣ ∣ ûₑ ∣̂ᵉ
∣û∣ₑ = ≡̂ᵣ-sym (≡̂ᵣ-trans ≡̂ᵣ-map-const
                        (subst (λ c → rconst (mapᵉ uₑ) ≡̂ᵣ rconst c) map-uᵉ ≡̂ᵣ-refl))

atom≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (a b : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
atom≾ᵣ a b = linkᵣ? a b <∣> ceilᵣ b <∣> reachᵣ? a b

minᵐ : ∀ {Θ} {Q : Hyps Θ} → (b : RAtom Θ) → Maybe (Q ⊩ ûᵣ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
minᵐ {Q = Q} (rm i) with min≾ₑ {Q = Q} {ε = evar i} umin?ₑ
... | just q  = just (transᵣ (eqᵣ ∣û∣ₑ) (map-mono q))
... | nothing = nothing
minᵐ _ = nothing

unit≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (b : RAtom Θ) → Maybe (Q ⊩ ûᵣ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
unit≾ᵣ b = atom≾ᵣ (rc uᵣ) b <∣> min≾ᵣ umin?ᵣ <∣> minᵐ b

≾unitᵣ : ∀ {Θ} {Q : Hyps Θ} → (a : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ûᵣ)
≾unitᵣ a = atom≾ᵣ a (rc uᵣ)

absorbs≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (a b : RAtom Θ)
          → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ·̂ᵣ ⟦ b ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
absorbs≾ᵣ a b = ceilᵣ b

matchᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → (a b : RAtom Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
       → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ·̂ᵣ ρ ≾̂ᵣ ⟦ b ⟧ʳᵃ ·̂ᵣ ρ')
matchᵣ {Q = Q} a b r with atom≾ᵣ {Q = Q} a b
... | nothing = nothing
... | just p with r
...   | just q  = just (monoᵣ p q)
...   | nothing = nothing

skipʳᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → (b : RAtom Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
       → Maybe (Q ⊩ ρ ≾̂ᵣ ⟦ b ⟧ʳᵃ ·̂ᵣ ρ')
skipʳᵣ {Q = Q} b r with unit≾ᵣ {Q = Q} b
... | nothing = nothing
... | just p with r
...   | just q  = just (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityˡ)) (monoᵣ p q))
...   | nothing = nothing

skipˡᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → (a : RAtom Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
       → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ·̂ᵣ ρ ≾̂ᵣ ρ')
skipˡᵣ {Q = Q} a r with ≾unitᵣ {Q = Q} a
... | nothing = nothing
... | just p with r
...   | just q  = just (transᵣ (monoᵣ p q) (eqᵣ ≡̂ᵣ-identityˡ))
...   | nothing = nothing

intoTopᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → (a b : RAtom Θ)
         → Maybe (Q ⊩ ρ ≾̂ᵣ ⟦ b ⟧ʳᵃ ·̂ᵣ ρ')
         → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ·̂ᵣ ρ ≾̂ᵣ ⟦ b ⟧ʳᵃ ·̂ᵣ ρ')
intoTopᵣ {Q = Q} a b r with absorbs≾ᵣ {Q = Q} a b
... | nothing = nothing
... | just p with r
...   | just q  = just (transᵣ (monoᵣ ⊩≾̂ᵣ-refl q)
                               (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-assoc)) (monoᵣ p ⊩≾̂ᵣ-refl)))
...   | nothing = nothing

spliceʳᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ} → (c : R) → (b : RAtom Θ) → (bs : List (RAtom Θ))
         → Maybe (Q ⊩ ρ ≾̂ᵣ ⟦ consᵣ (rc c) bs ⟧ʳˢ)
         → Maybe (Q ⊩ ρ ≾̂ᵣ rconst c ·̂ᵣ (⟦ b ⟧ʳᵃ ·̂ᵣ ⟦ bs ⟧ʳˢ))
spliceʳᵣ {Q = Q} c b bs r with unit≾ᵣ {Q = Q} b
... | nothing = nothing
... | just p with r
...   | just q  = just (transᵣ q (transᵣ (eqᵣ (≡̂ᵣ-trans (consᵣ-≡ (rc c) bs)
                                                      (≡̂ᵣ-cong ≡̂ᵣ-refl (≡̂ᵣ-sym ≡̂ᵣ-identityˡ))))
                                          (monoᵣ ⊩≾̂ᵣ-refl (monoᵣ p ⊩≾̂ᵣ-refl))))
...   | nothing = nothing

spliceˡᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ'} → (c : R) → (a : RAtom Θ) → (as : List (RAtom Θ))
         → Maybe (Q ⊩ ⟦ consᵣ (rc c) as ⟧ʳˢ ≾̂ᵣ ρ')
         → Maybe (Q ⊩ rconst c ·̂ᵣ (⟦ a ⟧ʳᵃ ·̂ᵣ ⟦ as ⟧ʳˢ) ≾̂ᵣ ρ')
spliceˡᵣ {Q = Q} c a as r with ≾unitᵣ {Q = Q} a
... | nothing = nothing
... | just p with r
...   | just q  = just (transᵣ (monoᵣ ⊩≾̂ᵣ-refl (monoᵣ p ⊩≾̂ᵣ-refl))
                               (transᵣ (eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl ≡̂ᵣ-identityˡ)
                                                      (≡̂ᵣ-sym (consᵣ-≡ (rc c) as))))
                                       q))
...   | nothing = nothing

mergeʳᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ} → ((bs : List (RAtom Θ)) → Maybe (Q ⊩ ρ ≾̂ᵣ ⟦ bs ⟧ʳˢ))
        → (bs : List (RAtom Θ)) → Maybe (Q ⊩ ρ ≾̂ᵣ ⟦ bs ⟧ʳˢ)
mergeʳᵣ r (rc c ∷ b ∷ bs) = spliceʳᵣ c b bs (r (consᵣ (rc c) bs))
mergeʳᵣ r _               = nothing

mergeˡᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ'} → ((as : List (RAtom Θ)) → Maybe (Q ⊩ ⟦ as ⟧ʳˢ ≾̂ᵣ ρ'))
        → (as : List (RAtom Θ)) → Maybe (Q ⊩ ⟦ as ⟧ʳˢ ≾̂ᵣ ρ')
mergeˡᵣ r (rc c ∷ a ∷ as) = spliceˡᵣ c a as (r (consᵣ (rc c) as))
mergeˡᵣ r _               = nothing

prodˢ≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → ℕ → (as bs : List (RAtom Θ))
        → Maybe (Q ⊩ ⟦ as ⟧ʳˢ ≾̂ᵣ ⟦ bs ⟧ʳˢ)
prodˢ≾ᵣ n       []       []       = just ⊩≾̂ᵣ-refl
prodˢ≾ᵣ zero    _        _        = nothing
prodˢ≾ᵣ (suc n) []       (b ∷ bs) =
  skipʳᵣ b (prodˢ≾ᵣ n [] bs)
  <∣> mergeʳᵣ (prodˢ≾ᵣ n []) (b ∷ bs)
prodˢ≾ᵣ (suc n) (a ∷ as) []       =
  skipˡᵣ a (prodˢ≾ᵣ n as [])
  <∣> mergeˡᵣ (λ as' → prodˢ≾ᵣ n as' []) (a ∷ as)
prodˢ≾ᵣ (suc n) (a ∷ as) (b ∷ bs) =
  matchᵣ a b (prodˢ≾ᵣ n as bs)
  <∣> skipʳᵣ b (prodˢ≾ᵣ n (a ∷ as) bs)
  <∣> skipˡᵣ a (prodˢ≾ᵣ n as (b ∷ bs))
  <∣> intoTopᵣ a b (prodˢ≾ᵣ n as (b ∷ bs))
  <∣> mergeʳᵣ (prodˢ≾ᵣ n (a ∷ as)) (b ∷ bs)
  <∣> mergeˡᵣ (λ as' → prodˢ≾ᵣ n as' (b ∷ bs)) (a ∷ as)

prod≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (as bs : List (RAtom Θ))
       → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ bs ⟧ʳᵖ)
prod≾ᵣ as bs with prodˢ≾ᵣ (length as + length bs) as bs
... | just p  = just (transᵣ (eqᵣ (≡̂ᵣ-sym (⟦⟧ʳᵖ-≡ as)))
                             (transᵣ p (eqᵣ (⟦⟧ʳᵖ-≡ bs))))
... | nothing = nothing

altSum≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (as : List (RAtom Θ))
         → (t : Alts (List (RAtom Θ)))
         → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ t ⟧ʳᵖ⁺)
altSum≾ᵣ as (alt P) = prod≾ᵣ as P
altSum≾ᵣ as (P ∷⁺ t) with prod≾ᵣ as P
... | just p  = just (transᵣ p ⊔-ubˡᵣ)
... | nothing with altSum≾ᵣ as t
...   | just q  = just (transᵣ q ⊔-ubʳᵣ)
...   | nothing = nothing

sum≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (s t : Alts (List (RAtom Θ)))
      → Maybe (Q ⊩ ⟦ s ⟧ʳᵖ⁺ ≾̂ᵣ ⟦ t ⟧ʳᵖ⁺)
sum≾ᵣ (alt P)  t = altSum≾ᵣ P t
sum≾ᵣ (P ∷⁺ s) t with altSum≾ᵣ P t | sum≾ᵣ s t
... | just p | just q = just (⊔-lubᵣ p q)
... | _      | _      = nothing

foldᵣ-≡ᵖ : ∀ {Θ} → (ρ : RExp Θ) → ρ ≡̂ᵣ ⟦ foldSumᵣ (nrmᵣ ρ) ⟧ʳᵖ⁺
foldᵣ-≡ᵖ ρ =
  ≡̂ᵣ-trans (nrmᵣ-≡ ρ)
  (≡̂ᵣ-trans (≡̂ᵣ-sym (foldSumᵣ-≡ (nrmᵣ ρ))) (⟦⟧ʳᵖ⁺-≡ (foldSumᵣ (nrmᵣ ρ))))

decide≾ᵣ : ∀ {Θ} {Q : Hyps Θ} → (ρ ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
decide≾ᵣ ρ ρ' with sum≾ᵣ (nrmᵣ ρ) (foldSumᵣ (nrmᵣ ρ'))
... | just p  = just (transᵣ (eqᵣ (nrmᵣ-≡ᵖ ρ)) (transᵣ p (eqᵣ (≡̂ᵣ-sym (foldᵣ-≡ᵖ ρ')))))
... | nothing = nothing

evalᵉ : EExp ∅ˢ → E
evalᵉ (evar ())
evalᵉ (econst c) = c
evalᵉ (ε ·̂ₑ ε')  = evalᵉ ε ·ₑ evalᵉ ε'
evalᵉ (ε ⊔̂ₑ ε')  = evalᵉ ε ⊔ₑ evalᵉ ε'

evalʳ : RExp ∅ˢ → R
evalʳ (rvar ())
evalʳ (rconst c) = c
evalʳ (ρ ·̂ᵣ ρ')  = evalʳ ρ ·ᵣ evalʳ ρ'
evalʳ (ρ ⊔̂ᵣ ρ')  = evalʳ ρ ⊔ᵣ evalʳ ρ'
evalʳ ∣ ε ∣̂ᵉ     = mapᵉ (evalᵉ ε)

evalᵉ-≡ : (ε : EExp ∅ˢ) → ε ≡̂ₑ econst (evalᵉ ε)
evalᵉ-≡ (evar ())
evalᵉ-≡ (econst c) = ≡̂ₑ-refl
evalᵉ-≡ (ε ·̂ₑ ε')  =
  ≡̂ₑ-trans (≡̂ₑ-cong (evalᵉ-≡ ε) (evalᵉ-≡ ε')) ≡̂ₑ-const-·
evalᵉ-≡ (ε ⊔̂ₑ ε')  =
  ≡̂ₑ-trans (≡̂ₑ-cong-⊔ (evalᵉ-≡ ε) (evalᵉ-≡ ε')) ≡̂ₑ-const-⊔

evalʳ-≡ : (ρ : RExp ∅ˢ) → ρ ≡̂ᵣ rconst (evalʳ ρ)
evalʳ-≡ (rvar ())
evalʳ-≡ (rconst c) = ≡̂ᵣ-refl
evalʳ-≡ (ρ ·̂ᵣ ρ')  =
  ≡̂ᵣ-trans (≡̂ᵣ-cong (evalʳ-≡ ρ) (evalʳ-≡ ρ')) ≡̂ᵣ-const-·
evalʳ-≡ (ρ ⊔̂ᵣ ρ')  =
  ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (evalʳ-≡ ρ) (evalʳ-≡ ρ')) ≡̂ᵣ-const-⊔
evalʳ-≡ ∣ ε ∣̂ᵉ     =
  ≡̂ᵣ-trans (≡̂ᵣ-map-cong (evalᵉ-≡ ε)) ≡̂ᵣ-map-const

-- A closed expression and its value entail one another

⊩-reflectᵣ : (ρ : RExp ∅ˢ)
           → (∅ᴴ ⊩ ρ ≾̂ᵣ rconst (evalʳ ρ)) × (∅ᴴ ⊩ rconst (evalʳ ρ) ≾̂ᵣ ρ)
⊩-reflectᵣ ρ = eqᵣ (evalʳ-≡ ρ) , eqᵣ (≡̂ᵣ-sym (evalʳ-≡ ρ))

⊩-reflectₑ : (ε : EExp ∅ˢ)
           → (∅ᴴ ⊩ ε ≾̂ₑ econst (evalᵉ ε)) × (∅ᴴ ⊩ econst (evalᵉ ε) ≾̂ₑ ε)
⊩-reflectₑ ε = eqₑ (evalᵉ-≡ ε) , eqₑ (≡̂ₑ-sym (evalᵉ-≡ ε))
