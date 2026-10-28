---------------------------------------------------------------------
-- Sum-of-products normal form of open grade expressions           --
--                                                                 --
-- A grade expression is flattened to a sum of alternatives, each  --
-- a product of atoms: constants, variables, and images of effect  --
-- variables under the morphism. Adjacent constants are            --
-- multiplied, units are dropped, a product is distributed over a  --
-- join, and repeated alternatives are merged. A sum with the top  --
-- among its alternatives is the top, `⊤` absorbing the join. A    --
-- sum is nonempty, the join having no unit; a product may be      --
-- empty, and is then the unit itself. Where the grade declares    --
-- `_·_` commutative, each product is then put in one order, its   --
-- constants multiplied into one in front of its variables, these  --
-- by index. The normal form is certified by `≡̂ᵣ`/`≡̂ₑ`, so one     --
-- may compare alternative by alternative and atom by atom, or     --
-- read the sum back as an expression.                             --
--                                                                 --
-- Two read-backs at each layer: `⟦_⟧ʳˢ`/`⟦_⟧ʳˢ⁺` end every        --
-- product in the unit, which makes the certificates structural;   --
-- `⟦_⟧ʳᵖ`/`⟦_⟧ʳᵖ⁺` drop that trailing unit and collapse a lone    --
-- alternative, and are what `canonᵣ`/`canonₑ` return.             --
--                                                                 --
-- `foldSumₑ`/`foldSumᵣ` group and fold a sum without pruning it;  --
-- `SolverImpl.Entail` compares against the folded right side.     --
--                                                                 --
-- `Grouping` groups the alternatives by skeleton, lists the       --
-- groups in skeleton order, folds a group that varies in one slot --
-- into one alternative whose slot is a join of constants, and,    --
-- given a decided order that the join absorbs, drops every        --
-- alternative below another. `SolverImpl.Canon` instantiates it   --
-- with the decider of `SolverImpl.Entail` to form `canonᵣ` and    --
-- `canonₑ`. Each step is certified by a single `≡̂ᵣ`/`≡̂ₑ`.         --
--                                                                 --
-- Contract. An expression is convertible to its normal form       --
-- (`nrmᵣ-≡`, `nrmₑ-≡`) and to its fold (`foldSumᵣ-≡`,             --
-- `foldSumₑ-≡`). That two convertible expressions get one normal  --
-- form is not claimed.                                            --
---------------------------------------------------------------------

open import Algebra.Definitions using (Commutative)
open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.Fin.Base using (toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Properties using () renaming (≡-dec to ≡-decᴸ)
open import Data.List.Relation.Unary.Any using (Any; here; there; _─_)
import Data.List.Relation.Unary.Any as Any
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Nat.Base using (ℕ; zero; suc; _<ᵇ_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Inference.SolverImpl.Product (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import OpenCalculus.Syntax.Grades S
open import OpenCalculus.Hypotheses    S

------------------------------------------------------------------
-- Alternatives
--
-- The alternatives of a sum, a nonempty list: the join is a least
-- upper bound of two, and has no unit to stand for none.

infixr 5 _∷⁺_

data Alts (X : Set) : Set where
  alt  : X → Alts X
  _∷⁺_ : X → Alts X → Alts X

infixr 5 _⧺_

_⧺_ : ∀ {X} → Alts X → Alts X → Alts X
alt x    ⧺ t = x ∷⁺ t
(x ∷⁺ s) ⧺ t = x ∷⁺ (s ⧺ t)

mapᴬ : ∀ {X Y} → (X → Y) → Alts X → Alts Y
mapᴬ f (alt x)  = alt (f x)
mapᴬ f (x ∷⁺ s) = f x ∷⁺ mapᴬ f s

-- The lexicographic order on lists, from an order on their elements

lex : ∀ {A : Set} → DecidableEquality A → (A → A → 𝔹) → List A → List A → 𝔹
lex _≟_ _<_ []       []       = false
lex _≟_ _<_ []       (_ ∷ _)  = true
lex _≟_ _<_ (_ ∷ _)  []       = false
lex _≟_ _<_ (a ∷ as) (b ∷ bs) with a ≟ b
... | yes _ = lex _≟_ _<_ as bs
... | no _  = a < b

-- Insertion sort, from a strict order on the elements

insertBy : ∀ {A : Set} → (A → A → 𝔹) → A → List A → List A
insertBy _<_ a []       = a ∷ []
insertBy _<_ a (b ∷ bs) with b < a
... | true  = b ∷ insertBy _<_ a bs
... | false = a ∷ b ∷ bs

sortBy : ∀ {A : Set} → (A → A → 𝔹) → List A → List A
sortBy _<_ []       = []
sortBy _<_ (a ∷ as) = insertBy _<_ a (sortBy _<_ as)

------------------------------------------------------------------
-- Canonical sums
--
-- A product in normal form is read as its skeleton, the sequence of
-- its variable atoms, with a constant slot before, between and after
-- them, an empty slot being the unit. The alternatives of a sum are
-- grouped by skeleton, and the groups ordered by it. A group whose
-- alternatives agree in every slot but one is folded into a single
-- alternative, that slot holding the join of their constants: the two
-- distributivity laws bring the join into the slot, and a join of
-- constants is a constant. A group that varies in more than one slot
-- is kept as it is, without repeats and in the order its alternatives
-- arrive.
--
-- The grouping never compares constants: two in the same slot are
-- joined. Skeletons are ordered syntactically, lexicographically from
-- an order on variable atoms. Comparing alternatives by the grade
-- order is left to `Pruning`, which is given the order.
--
-- Stated over any carrier with the laws it uses, and instantiated
-- below at both sorts.

module Grouping
  {X K V : Set} (_≈_ : X → X → Set)
  (≈-refl   : ∀ {a} → a ≈ a)
  (≈-sym    : ∀ {a b} → a ≈ b → b ≈ a)
  (≈-trans  : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c)
  (_∙_ _∨_  : X → X → X)
  (∙-cong   : ∀ {a a' b b'} → a ≈ a' → b ≈ b' → (a ∙ b) ≈ (a' ∙ b'))
  (∨-cong   : ∀ {a a' b b'} → a ≈ a' → b ≈ b' → (a ∨ b) ≈ (a' ∨ b'))
  (∨-idem   : ∀ {a} → (a ∨ a) ≈ a)
  (∨-comm   : ∀ {a b} → (a ∨ b) ≈ (b ∨ a))
  (∨-assoc  : ∀ {a b c} → ((a ∨ b) ∨ c) ≈ (a ∨ (b ∨ c)))
  (distribˡ : ∀ {a b c} → (a ∙ (b ∨ c)) ≈ ((a ∙ b) ∨ (a ∙ c)))
  (distribʳ : ∀ {a b c} → ((b ∨ c) ∙ a) ≈ ((b ∙ a) ∨ (c ∙ a)))
  (κ : K → X) (_⊔ᴷ_ : K → K → K)
  (κ-⊔      : ∀ {c d} → (κ c ∨ κ d) ≈ κ (c ⊔ᴷ d))
  (_≈ᴷ?_    : (c d : K) → Maybe (κ c ≈ κ d))
  (ν : V → X) (_≟ⱽ_ : DecidableEquality V) (_<ⱽ_ : V → V → 𝔹)
  where

  -- The slots of a product with a given skeleton, one more than its
  -- variables

  infixr 5 _▸_

  data Slots : List V → Set where
    ⌜_⌝ : K → Slots []
    _▸_ : ∀ {a vs} → K → Slots vs → Slots (a ∷ vs)

  ⟦_⟧ᵏ : ∀ {vs} → Slots vs → X
  ⟦ ⌜ c ⌝ ⟧ᵏ           = κ c
  ⟦ _▸_ {a} c s ⟧ᵏ     = κ c ∙ (ν a ∙ ⟦ s ⟧ᵏ)

  ⟦_⟧ᵏ⁺ : ∀ {vs} → Alts (Slots vs) → X
  ⟦ alt s ⟧ᵏ⁺  = ⟦ s ⟧ᵏ
  ⟦ s ∷⁺ g ⟧ᵏ⁺ = ⟦ s ⟧ᵏ ∨ ⟦ g ⟧ᵏ⁺

  _≈ᵏ?_ : ∀ {vs} → (s t : Slots vs) → Maybe (⟦ s ⟧ᵏ ≈ ⟦ t ⟧ᵏ)
  ⌜ c ⌝   ≈ᵏ? ⌜ d ⌝ = c ≈ᴷ? d
  (c ▸ s) ≈ᵏ? (d ▸ t) with c ≈ᴷ? d | s ≈ᵏ? t
  ... | just p | just q = just (∙-cong p (∙-cong ≈-refl q))
  ... | _      | _      = nothing

  -- A product, with its skeleton

  Prod : Set
  Prod = Σ[ vs ∈ List V ] Slots vs

  ⟦_⟧ᵖ : Prod → X
  ⟦ P ⟧ᵖ = ⟦ proj₂ P ⟧ᵏ

  ⟦_⟧ᵖ⁺ : Alts Prod → X
  ⟦ alt P ⟧ᵖ⁺  = ⟦ P ⟧ᵖ
  ⟦ P ∷⁺ s ⟧ᵖ⁺ = ⟦ P ⟧ᵖ ∨ ⟦ s ⟧ᵖ⁺

  ⧺-≈ : (s t : Alts Prod) → ⟦ s ⧺ t ⟧ᵖ⁺ ≈ (⟦ s ⟧ᵖ⁺ ∨ ⟦ t ⟧ᵖ⁺)
  ⧺-≈ (alt P)  t = ≈-refl
  ⧺-≈ (P ∷⁺ s) t = ≈-trans (∨-cong ≈-refl (⧺-≈ s t)) (≈-sym ∨-assoc)

  -- Folding a group. With an empty skeleton the group is a join of
  -- constants. Otherwise either every alternative has the same first
  -- slot, and the rest of the slots are folded, or they all have the
  -- same remaining slots, and the first slot is the join of theirs.

  joinᴷ : Alts (Slots []) → K
  joinᴷ (alt ⌜ c ⌝)  = c
  joinᴷ (⌜ c ⌝ ∷⁺ g) = c ⊔ᴷ joinᴷ g

  joinᴷ-≈ : (g : Alts (Slots [])) → ⟦ g ⟧ᵏ⁺ ≈ κ (joinᴷ g)
  joinᴷ-≈ (alt ⌜ c ⌝)  = ≈-refl
  joinᴷ-≈ (⌜ c ⌝ ∷⁺ g) = ≈-trans (∨-cong ≈-refl (joinᴷ-≈ g)) κ-⊔

  tails : ∀ {a vs} → Alts (Slots (a ∷ vs)) → Alts (Slots vs)
  tails (alt (_ ▸ s))  = alt s
  tails ((_ ▸ s) ∷⁺ g) = s ∷⁺ tails g

  sameHead? : ∀ {a vs} → (g : Alts (Slots (a ∷ vs)))
            → Maybe (Σ[ c ∈ K ] (⟦ g ⟧ᵏ⁺ ≈ (κ c ∙ (ν a ∙ ⟦ tails g ⟧ᵏ⁺))))
  sameHead? (alt (c ▸ s)) = just (c , ≈-refl)
  sameHead? ((c ▸ s) ∷⁺ g) with sameHead? g
  ... | nothing       = nothing
  ... | just (c' , p) with c ≈ᴷ? c'
  ...   | nothing = nothing
  ...   | just e  =
          just (c , ≈-trans (∨-cong ≈-refl (≈-trans p (∙-cong (≈-sym e) ≈-refl)))
                            (≈-sym (≈-trans (∙-cong ≈-refl distribˡ) distribˡ)))

  sameTail? : ∀ {a vs} → (g : Alts (Slots (a ∷ vs)))
            → Maybe (Σ[ s ∈ Slots (a ∷ vs) ] (⟦ g ⟧ᵏ⁺ ≈ ⟦ s ⟧ᵏ))
  sameTail? (alt (c ▸ s)) = just (c ▸ s , ≈-refl)
  sameTail? ((c ▸ s) ∷⁺ g) with sameTail? g
  ... | nothing = nothing
  ... | just (c' ▸ s' , p) with s ≈ᵏ? s'
  ...   | nothing = nothing
  ...   | just e  =
          just ((c ⊔ᴷ c') ▸ s , ≈-trans (∨-cong ≈-refl
                                        (≈-trans p (∙-cong ≈-refl (∙-cong ≈-refl (≈-sym e)))))
                                      (≈-trans (≈-sym distribʳ) (∙-cong κ-⊔ ≈-refl)))

  fold? : ∀ {vs} → (g : Alts (Slots vs)) → Maybe (Σ[ s ∈ Slots vs ] (⟦ g ⟧ᵏ⁺ ≈ ⟦ s ⟧ᵏ))
  fold? {[]}    g = just (⌜ joinᴷ g ⌝ , joinᴷ-≈ g)
  fold? {_ ∷ _} g with sameHead? g
  ... | nothing      = sameTail? g
  ... | just (c , p) with fold? (tails g)
  ...   | nothing      = sameTail? g
  ...   | just (s , q) = just (c ▸ s , ≈-trans p (∙-cong ≈-refl (∙-cong ≈-refl q)))

  -- Groups: the alternatives of one skeleton

  Group : Set
  Group = Σ[ vs ∈ List V ] Alts (Slots vs)

  ⟦_⟧ᵍ : Group → X
  ⟦ G ⟧ᵍ = ⟦ proj₂ G ⟧ᵏ⁺

  ⟦_⟧ᵍ⁺ : Alts Group → X
  ⟦ alt G ⟧ᵍ⁺   = ⟦ G ⟧ᵍ
  ⟦ G ∷⁺ Gs ⟧ᵍ⁺ = ⟦ G ⟧ᵍ ∨ ⟦ Gs ⟧ᵍ⁺

  -- An alternative already in the group is absorbed by it

  within? : ∀ {vs} → (s : Slots vs) → (g : Alts (Slots vs))
          → Maybe ((⟦ s ⟧ᵏ ∨ ⟦ g ⟧ᵏ⁺) ≈ ⟦ g ⟧ᵏ⁺)
  within? s (alt t) with s ≈ᵏ? t
  ... | just e  = just (≈-trans (∨-cong e ≈-refl) ∨-idem)
  ... | nothing = nothing
  within? s (t ∷⁺ g) with s ≈ᵏ? t
  ... | just e  =
        just (≈-trans (∨-cong e ≈-refl) (≈-trans (≈-sym ∨-assoc) (∨-cong ∨-idem ≈-refl)))
  ... | nothing with within? s g
  ...   | just p  =
          just (≈-trans (≈-sym ∨-assoc)
               (≈-trans (∨-cong ∨-comm ≈-refl) (≈-trans ∨-assoc (∨-cong ≈-refl p))))
  ...   | nothing = nothing

  add : ∀ {vs} → Slots vs → Alts (Slots vs) → Alts (Slots vs)
  add s g with within? s g
  ... | just _  = g
  ... | nothing = s ∷⁺ g

  add-≈ : ∀ {vs} → (s : Slots vs) → (g : Alts (Slots vs))
        → ⟦ add s g ⟧ᵏ⁺ ≈ (⟦ s ⟧ᵏ ∨ ⟦ g ⟧ᵏ⁺)
  add-≈ s g with within? s g
  ... | just p  = ≈-sym p
  ... | nothing = ≈-refl

  -- Skeletons: equality, and the order the groups are listed in

  _≟ˢ_ : DecidableEquality (List V)
  _≟ˢ_ = ≡-decᴸ _≟ⱽ_

  _<ˢ_ : List V → List V → 𝔹
  _<ˢ_ = lex _≟ⱽ_ _<ⱽ_

  -- Inserting an alternative into its group, or a new group into its
  -- place

  insert : Prod → Alts Group → Alts Group
  insert (vs , s) (alt (ws , g)) with vs ≟ˢ ws
  ... | yes refl = alt (vs , add s g)
  ... | no _ with vs <ˢ ws
  ...   | true  = (vs , alt s) ∷⁺ alt (ws , g)
  ...   | false = (ws , g) ∷⁺ alt (vs , alt s)
  insert (vs , s) ((ws , g) ∷⁺ Gs) with vs ≟ˢ ws
  ... | yes refl = (vs , add s g) ∷⁺ Gs
  ... | no _ with vs <ˢ ws
  ...   | true  = (vs , alt s) ∷⁺ (ws , g) ∷⁺ Gs
  ...   | false = (ws , g) ∷⁺ insert (vs , s) Gs

  insert-≈ : (P : Prod) → (Gs : Alts Group) → ⟦ insert P Gs ⟧ᵍ⁺ ≈ (⟦ P ⟧ᵖ ∨ ⟦ Gs ⟧ᵍ⁺)
  insert-≈ (vs , s) (alt (ws , g)) with vs ≟ˢ ws
  ... | yes refl = add-≈ s g
  ... | no _ with vs <ˢ ws
  ...   | true  = ≈-refl
  ...   | false = ∨-comm
  insert-≈ (vs , s) ((ws , g) ∷⁺ Gs) with vs ≟ˢ ws
  ... | yes refl = ≈-trans (∨-cong (add-≈ s g) ≈-refl) ∨-assoc
  ... | no _ with vs <ˢ ws
  ...   | true  = ≈-refl
  ...   | false =
          ≈-trans (∨-cong ≈-refl (insert-≈ (vs , s) Gs))
          (≈-trans (≈-sym ∨-assoc) (≈-trans (∨-cong ∨-comm ≈-refl) ∨-assoc))

  groups : Alts Prod → Alts Group
  groups (alt (vs , s)) = alt (vs , alt s)
  groups (P ∷⁺ ps)      = insert P (groups ps)

  groups-≈ : (ps : Alts Prod) → ⟦ groups ps ⟧ᵍ⁺ ≈ ⟦ ps ⟧ᵖ⁺
  groups-≈ (alt P)   = ≈-refl
  groups-≈ (P ∷⁺ ps) = ≈-trans (insert-≈ P (groups ps)) (∨-cong ≈-refl (groups-≈ ps))

  -- Each group folded where it can be, and the groups read back as one
  -- sum

  foldGroup : Group → Group
  foldGroup (vs , g) with fold? g
  ... | just (s , _) = vs , alt s
  ... | nothing      = vs , g

  foldGroup-≈ : (G : Group) → ⟦ foldGroup G ⟧ᵍ ≈ ⟦ G ⟧ᵍ
  foldGroup-≈ (vs , g) with fold? g
  ... | just (s , p) = ≈-sym p
  ... | nothing      = ≈-refl

  foldGroups-≈ : (Gs : Alts Group) → ⟦ mapᴬ foldGroup Gs ⟧ᵍ⁺ ≈ ⟦ Gs ⟧ᵍ⁺
  foldGroups-≈ (alt G)   = foldGroup-≈ G
  foldGroups-≈ (G ∷⁺ Gs) = ∨-cong (foldGroup-≈ G) (foldGroups-≈ Gs)

  members : Group → Alts Prod
  members (vs , g) = mapᴬ (vs ,_) g

  members-≈ : (G : Group) → ⟦ members G ⟧ᵖ⁺ ≈ ⟦ G ⟧ᵍ
  members-≈ (vs , alt s)  = ≈-refl
  members-≈ (vs , s ∷⁺ g) = ∨-cong ≈-refl (members-≈ (vs , g))

  flatten : Alts Group → Alts Prod
  flatten (alt G)   = members G
  flatten (G ∷⁺ Gs) = members G ⧺ flatten Gs

  flatten-≈ : (Gs : Alts Group) → ⟦ flatten Gs ⟧ᵖ⁺ ≈ ⟦ Gs ⟧ᵍ⁺
  flatten-≈ (alt G)   = members-≈ G
  flatten-≈ (G ∷⁺ Gs) =
    ≈-trans (⧺-≈ (members G) (flatten Gs)) (∨-cong (members-≈ G) (flatten-≈ Gs))

  canonical : Alts Prod → Alts Prod
  canonical ps = flatten (mapᴬ foldGroup (groups ps))

  canonical-≈ : (ps : Alts Prod) → ⟦ canonical ps ⟧ᵖ⁺ ≈ ⟦ ps ⟧ᵖ⁺
  canonical-≈ ps =
    ≈-trans (flatten-≈ (mapᴬ foldGroup (groups ps)))
    (≈-trans (foldGroups-≈ (groups ps)) (groups-≈ ps))

  ----------------------------------------------------------------
  -- Pruning
  --
  -- Given an order whose every instance a join absorbs, and a partial
  -- decision of it on products, an alternative below another is
  -- dropped. Two alternatives each below the other are equal as
  -- grades, and the one listed first is kept, so on a grouped sum the
  -- tie goes to the smaller skeleton, and within a group to the
  -- earlier arrival.
  --
  -- The sum is pruned from the right: an alternative strictly below
  -- one kept further on is dropped, and otherwise it is kept and every
  -- alternative kept further on that is below it, ties included, is
  -- dropped. Where the decided order is transitive, what remains is
  -- the set of alternatives not below any other, with ties broken as
  -- above, whatever order they are examined in. Canonicity is
  -- relative to the decision: an ordering it does not find prunes
  -- nothing.
  --
  -- Pruning keeps the skeleton order. It can make a group foldable, by
  -- removing the alternatives that made it vary in a second slot, and a
  -- fold can expose a new ordering. The fold and the pruning are
  -- repeated until the sum stops shrinking, in at most as many rounds
  -- as there are alternatives.

  module Pruning
    (_≲_    : X → X → Set)
    (absorb : ∀ {a b} → a ≲ b → (a ∨ b) ≈ b)
    (_≲?_   : (P P' : Prod) → Maybe (⟦ P ⟧ᵖ ≲ ⟦ P' ⟧ᵖ))
    where

    -- A sum with its first alternative set apart, the rest possibly
    -- gone

    _∷?_ : Prod → Maybe (Alts Prod) → Alts Prod
    P ∷? nothing = alt P
    P ∷? just s  = P ∷⁺ s

    _∨?_ : X → Maybe (Alts Prod) → X
    a ∨? nothing = a
    a ∨? just s  = a ∨ ⟦ s ⟧ᵖ⁺

    ∷?-≈ : (P : Prod) → (m : Maybe (Alts Prod)) → ⟦ P ∷? m ⟧ᵖ⁺ ≈ (⟦ P ⟧ᵖ ∨? m)
    ∷?-≈ P nothing  = ≈-refl
    ∷?-≈ P (just s) = ≈-refl

    ∨-swap : ∀ {a b c} → (a ∨ (b ∨ c)) ≈ (b ∨ (a ∨ c))
    ∨-swap = ≈-trans (≈-sym ∨-assoc) (≈-trans (∨-cong ∨-comm ≈-refl) ∨-assoc)

    ∨?-swap : ∀ {a b} → (m : Maybe (Alts Prod)) → (a ∨ (b ∨? m)) ≈ (b ∨ (a ∨? m))
    ∨?-swap nothing  = ∨-comm
    ∨?-swap (just s) = ∨-swap

    -- An alternative strictly below one of the sum is absorbed by it

    below? : (P : Prod) → (s : Alts Prod) → Maybe ((⟦ P ⟧ᵖ ∨ ⟦ s ⟧ᵖ⁺) ≈ ⟦ s ⟧ᵖ⁺)
    below? P (alt K) with P ≲? K | K ≲? P
    ... | just p | nothing = just (absorb p)
    ... | _      | _       = nothing
    below? P (K ∷⁺ s) with P ≲? K | K ≲? P
    ... | just p | nothing = just (≈-trans (≈-sym ∨-assoc) (∨-cong (absorb p) ≈-refl))
    ... | _      | _ with below? P s
    ...   | just q  = just (≈-trans ∨-swap (∨-cong ≈-refl q))
    ...   | nothing = nothing

    -- The alternatives of the sum below a given one, ties included,
    -- absorbed into it

    sweep : (P : Prod) → (s : Alts Prod)
          → Σ[ m ∈ Maybe (Alts Prod) ] ((⟦ P ⟧ᵖ ∨ ⟦ s ⟧ᵖ⁺) ≈ (⟦ P ⟧ᵖ ∨? m))
    sweep P (alt K) with K ≲? P
    ... | just q  = nothing , ≈-trans ∨-comm (absorb q)
    ... | nothing = just (alt K) , ≈-refl
    sweep P (K ∷⁺ s) with K ≲? P | sweep P s
    ... | just q  | m , p =
          m , ≈-trans (≈-sym ∨-assoc) (≈-trans (∨-cong (≈-trans ∨-comm (absorb q)) ≈-refl) p)
    ... | nothing | m , p =
          just (K ∷? m) ,
          ≈-trans ∨-swap (≈-trans (∨-cong ≈-refl p)
                         (≈-trans (∨?-swap m) (∨-cong ≈-refl (≈-sym (∷?-≈ K m)))))

    -- An alternative placed in a pruned sum: absorbed, or absorbing
    -- those below it

    place : Prod → Alts Prod → Alts Prod
    place P s with below? P s
    ... | just _  = s
    ... | nothing = P ∷? proj₁ (sweep P s)

    place-≈ : (P : Prod) → (s : Alts Prod) → ⟦ place P s ⟧ᵖ⁺ ≈ (⟦ P ⟧ᵖ ∨ ⟦ s ⟧ᵖ⁺)
    place-≈ P s with below? P s
    ... | just q  = ≈-sym q
    ... | nothing = ≈-trans (∷?-≈ P (proj₁ (sweep P s))) (≈-sym (proj₂ (sweep P s)))

    -- The sum with each alternative below another one dropped

    prune : Alts Prod → Alts Prod
    prune (alt P)  = alt P
    prune (P ∷⁺ s) = place P (prune s)

    prune-≈ : (ps : Alts Prod) → ⟦ prune ps ⟧ᵖ⁺ ≈ ⟦ ps ⟧ᵖ⁺
    prune-≈ (alt P)  = ≈-refl
    prune-≈ (P ∷⁺ s) = ≈-trans (place-≈ P (prune s)) (∨-cong ≈-refl (prune-≈ s))

    -- One round folds and orders, then prunes; rounds are repeated
    -- while the sum shrinks

    size : Alts Prod → ℕ
    size (alt _)  = 1
    size (_ ∷⁺ s) = suc (size s)

    round : Alts Prod → Alts Prod
    round ps = prune (canonical ps)

    round-≈ : (ps : Alts Prod) → ⟦ round ps ⟧ᵖ⁺ ≈ ⟦ ps ⟧ᵖ⁺
    round-≈ ps = ≈-trans (prune-≈ (canonical ps)) (canonical-≈ ps)

    rounds  : ℕ → Alts Prod → Alts Prod
    rounds′ : ℕ → Alts Prod → Alts Prod → Alts Prod

    rounds zero    ps = ps
    rounds (suc n) ps = rounds′ n ps (round ps)

    rounds′ n ps qs with size qs <ᵇ size ps
    ... | true  = rounds n qs
    ... | false = qs

    rounds-≈  : (n : ℕ) → (ps : Alts Prod) → ⟦ rounds n ps ⟧ᵖ⁺ ≈ ⟦ ps ⟧ᵖ⁺
    rounds′-≈ : (n : ℕ) → (ps qs : Alts Prod) → ⟦ qs ⟧ᵖ⁺ ≈ ⟦ ps ⟧ᵖ⁺
              → ⟦ rounds′ n ps qs ⟧ᵖ⁺ ≈ ⟦ ps ⟧ᵖ⁺

    rounds-≈ zero    ps = ≈-refl
    rounds-≈ (suc n) ps = rounds′-≈ n ps (round ps) (round-≈ ps)

    rounds′-≈ n ps qs p with size qs <ᵇ size ps
    ... | true  = ≈-trans (rounds-≈ n qs) p
    ... | false = p

    -- A round that shrinks the sum removes an alternative, so as many
    -- rounds as there are alternatives reach one that does not

    maximal : Alts Prod → Alts Prod
    maximal ps = rounds (size ps) ps

    maximal-≈ : (ps : Alts Prod) → ⟦ maximal ps ⟧ᵖ⁺ ≈ ⟦ ps ⟧ᵖ⁺
    maximal-≈ ps = rounds-≈ (size ps) ps

------------------------------------------------------------------
-- Effect grades

data EAtom (Θ : Scope) : Set where
  ac : E → EAtom Θ
  av : EVar Θ → EAtom Θ

⟦_⟧ᵉᵃ : ∀ {Θ} → EAtom Θ → EExp Θ
⟦ ac c ⟧ᵉᵃ = econst c
⟦ av i ⟧ᵉᵃ = evar i

⟦_⟧ᵉᵖ : ∀ {Θ} → List (EAtom Θ) → EExp Θ
⟦ [] ⟧ᵉᵖ         = ûₑ
⟦ a ∷ [] ⟧ᵉᵖ     = ⟦ a ⟧ᵉᵃ
⟦ a ∷ b ∷ as ⟧ᵉᵖ = ⟦ a ⟧ᵉᵃ ·̂ₑ ⟦ b ∷ as ⟧ᵉᵖ

⟦_⟧ᵉˢ : ∀ {Θ} → List (EAtom Θ) → EExp Θ
⟦ [] ⟧ᵉˢ     = ûₑ
⟦ a ∷ as ⟧ᵉˢ = ⟦ a ⟧ᵉᵃ ·̂ₑ ⟦ as ⟧ᵉˢ

⟦_⟧ᵉᵖ⁺ : ∀ {Θ} → Alts (List (EAtom Θ)) → EExp Θ
⟦ alt P ⟧ᵉᵖ⁺  = ⟦ P ⟧ᵉᵖ
⟦ P ∷⁺ s ⟧ᵉᵖ⁺ = ⟦ P ⟧ᵉᵖ ⊔̂ₑ ⟦ s ⟧ᵉᵖ⁺

⟦_⟧ᵉˢ⁺ : ∀ {Θ} → Alts (List (EAtom Θ)) → EExp Θ
⟦ alt P ⟧ᵉˢ⁺  = ⟦ P ⟧ᵉˢ
⟦ P ∷⁺ s ⟧ᵉˢ⁺ = ⟦ P ⟧ᵉˢ ⊔̂ₑ ⟦ s ⟧ᵉˢ⁺

⟦⟧ᵉᵖ-≡ : ∀ {Θ} → (as : List (EAtom Θ)) → ⟦ as ⟧ᵉˢ ≡̂ₑ ⟦ as ⟧ᵉᵖ
⟦⟧ᵉᵖ-≡ []           = ≡̂ₑ-refl
⟦⟧ᵉᵖ-≡ (a ∷ [])     = ≡̂ₑ-identityʳ
⟦⟧ᵉᵖ-≡ (a ∷ b ∷ as) = ≡̂ₑ-cong ≡̂ₑ-refl (⟦⟧ᵉᵖ-≡ (b ∷ as))

⟦⟧ᵉᵖ⁺-≡ : ∀ {Θ} → (s : Alts (List (EAtom Θ))) → ⟦ s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉᵖ⁺
⟦⟧ᵉᵖ⁺-≡ (alt P)  = ⟦⟧ᵉᵖ-≡ P
⟦⟧ᵉᵖ⁺-≡ (P ∷⁺ s) = ≡̂ₑ-cong-⊔ (⟦⟧ᵉᵖ-≡ P) (⟦⟧ᵉᵖ⁺-≡ s)

-- Consing an atom onto a product: constants are merged, units dropped

consₑ : ∀ {Θ} → EAtom Θ → List (EAtom Θ) → List (EAtom Θ)
consₑ (ac c) (ac d ∷ as) = consₑ (ac (c ·ₑ d)) as
consₑ (ac c) as with c ≃ₑ? uₑ
... | yes _ = as
... | no _  = ac c ∷ as
consₑ (av i) as = av i ∷ as

consₑ-≡ : ∀ {Θ} → (a : EAtom Θ) → (as : List (EAtom Θ))
        → ⟦ consₑ a as ⟧ᵉˢ ≡̂ₑ ⟦ a ⟧ᵉᵃ ·̂ₑ ⟦ as ⟧ᵉˢ
consₑ-≡ (ac c) (ac d ∷ as) =
  ≡̂ₑ-trans (consₑ-≡ (ac (c ·ₑ d)) as)
  (≡̂ₑ-trans (≡̂ₑ-cong (≡̂ₑ-sym ≡̂ₑ-const-·) ≡̂ₑ-refl) ≡̂ₑ-assoc)
consₑ-≡ (ac c) [] with c ≃ₑ? uₑ
... | yes e = ≡̂ₑ-trans (≡̂ₑ-sym ≡̂ₑ-identityˡ) (≡̂ₑ-cong (≡̂ₑ-const (≃ₑ-sym e)) ≡̂ₑ-refl)
... | no _     = ≡̂ₑ-refl
consₑ-≡ (ac c) (av i ∷ as) with c ≃ₑ? uₑ
... | yes e = ≡̂ₑ-trans (≡̂ₑ-sym ≡̂ₑ-identityˡ) (≡̂ₑ-cong (≡̂ₑ-const (≃ₑ-sym e)) ≡̂ₑ-refl)
... | no _     = ≡̂ₑ-refl
consₑ-≡ (av i) as = ≡̂ₑ-refl

appₑ : ∀ {Θ} → List (EAtom Θ) → List (EAtom Θ) → List (EAtom Θ)
appₑ []       ys = ys
appₑ (a ∷ as) ys = consₑ a (appₑ as ys)

appₑ-≡ : ∀ {Θ} → (as bs : List (EAtom Θ))
       → ⟦ appₑ as bs ⟧ᵉˢ ≡̂ₑ ⟦ as ⟧ᵉˢ ·̂ₑ ⟦ bs ⟧ᵉˢ
appₑ-≡ []       bs = ≡̂ₑ-sym ≡̂ₑ-identityˡ
appₑ-≡ (a ∷ as) bs =
  ≡̂ₑ-trans (consₑ-≡ a (appₑ as bs))
  (≡̂ₑ-trans (≡̂ₑ-cong ≡̂ₑ-refl (appₑ-≡ as bs)) (≡̂ₑ-sym ≡̂ₑ-assoc))

-- Appending the alternatives of two sums is their join

⧺ₑ-≡ : ∀ {Θ} → (s t : Alts (List (EAtom Θ)))
     → ⟦ s ⧺ t ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺ ⊔̂ₑ ⟦ t ⟧ᵉˢ⁺
⧺ₑ-≡ (alt P)  t = ≡̂ₑ-refl
⧺ₑ-≡ (P ∷⁺ s) t =
  ≡̂ₑ-trans (≡̂ₑ-cong-⊔ ≡̂ₑ-refl (⧺ₑ-≡ s t)) (≡̂ₑ-sym ≡̂ₑ-assoc-⊔)

-- Multiplying sums: every alternative of the one against every
-- alternative of the other, which is where distributivity is spent

mul1ₑ : ∀ {Θ} → List (EAtom Θ) → Alts (List (EAtom Θ)) → Alts (List (EAtom Θ))
mul1ₑ P (alt Q)  = alt (appₑ P Q)
mul1ₑ P (Q ∷⁺ t) = appₑ P Q ∷⁺ mul1ₑ P t

mulₑ : ∀ {Θ} → Alts (List (EAtom Θ)) → Alts (List (EAtom Θ))
     → Alts (List (EAtom Θ))
mulₑ (alt P)  t = mul1ₑ P t
mulₑ (P ∷⁺ s) t = mul1ₑ P t ⧺ mulₑ s t

mul1ₑ-≡ : ∀ {Θ} → (P : List (EAtom Θ)) → (t : Alts (List (EAtom Θ)))
        → ⟦ mul1ₑ P t ⟧ᵉˢ⁺ ≡̂ₑ ⟦ P ⟧ᵉˢ ·̂ₑ ⟦ t ⟧ᵉˢ⁺
mul1ₑ-≡ P (alt Q)  = appₑ-≡ P Q
mul1ₑ-≡ P (Q ∷⁺ t) =
  ≡̂ₑ-trans (≡̂ₑ-cong-⊔ (appₑ-≡ P Q) (mul1ₑ-≡ P t)) (≡̂ₑ-sym ≡̂ₑ-distribˡ-⊔)

mulₑ-≡ : ∀ {Θ} → (s t : Alts (List (EAtom Θ)))
       → ⟦ mulₑ s t ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺ ·̂ₑ ⟦ t ⟧ᵉˢ⁺
mulₑ-≡ (alt P)  t = mul1ₑ-≡ P t
mulₑ-≡ (P ∷⁺ s) t =
  ≡̂ₑ-trans (⧺ₑ-≡ (mul1ₑ P t) (mulₑ s t))
  (≡̂ₑ-trans (≡̂ₑ-cong-⊔ (mul1ₑ-≡ P t) (mulₑ-≡ s t)) (≡̂ₑ-sym ≡̂ₑ-distribʳ-⊔))

-- Merging repeated alternatives, which the join's idempotence,
-- commutativity and associativity licence; a repeat is absorbed by
-- its last occurrence

-- Atoms and products are compared by the sameness of their read-backs

_≟ᵃₑ_ : ∀ {Θ} → (a b : EAtom Θ) → Dec (⟦ a ⟧ᵉᵃ ≅ᵉ ⟦ b ⟧ᵉᵃ)
a ≟ᵃₑ b = ⟦ a ⟧ᵉᵃ ≟ᵉ ⟦ b ⟧ᵉᵃ

_≟ᵖₑ_ : ∀ {Θ} → (P Q : List (EAtom Θ)) → Dec (⟦ P ⟧ᵉˢ ≅ᵉ ⟦ Q ⟧ᵉˢ)
P ≟ᵖₑ Q = ⟦ P ⟧ᵉˢ ≟ᵉ ⟦ Q ⟧ᵉˢ

-- An alternative already in the sum is absorbed by it, which keeps
-- the order of the remaining alternatives

withinₑ? : ∀ {Θ} → (P : List (EAtom Θ)) → (s : Alts (List (EAtom Θ)))
         → Maybe (⟦ P ⟧ᵉˢ ⊔̂ₑ ⟦ s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺)
withinₑ? P (alt Q) with P ≟ᵖₑ Q
... | yes e = just (≡̂ₑ-trans (≡̂ₑ-cong-⊔ (≅ᵉ⇒≡̂ e) ≡̂ₑ-refl) ≡̂ₑ-idem-⊔)
... | no _     = nothing
withinₑ? P (Q ∷⁺ t) with P ≟ᵖₑ Q
... | yes e =
      just (≡̂ₑ-trans (≡̂ₑ-cong-⊔ (≅ᵉ⇒≡̂ e) ≡̂ₑ-refl)
           (≡̂ₑ-trans (≡̂ₑ-sym ≡̂ₑ-assoc-⊔) (≡̂ₑ-cong-⊔ ≡̂ₑ-idem-⊔ ≡̂ₑ-refl)))
... | no _ with withinₑ? P t
...   | just p  =
        just (≡̂ₑ-trans (≡̂ₑ-sym ≡̂ₑ-assoc-⊔)
             (≡̂ₑ-trans (≡̂ₑ-cong-⊔ ≡̂ₑ-comm-⊔ ≡̂ₑ-refl)
             (≡̂ₑ-trans ≡̂ₑ-assoc-⊔ (≡̂ₑ-cong-⊔ ≡̂ₑ-refl p))))
...   | nothing = nothing

nub1ₑ : ∀ {Θ} → List (EAtom Θ) → Alts (List (EAtom Θ)) → Alts (List (EAtom Θ))
nub1ₑ P s with withinₑ? P s
... | just _  = s
... | nothing = P ∷⁺ s

nubₑ : ∀ {Θ} → Alts (List (EAtom Θ)) → Alts (List (EAtom Θ))
nubₑ (alt P)  = alt P
nubₑ (P ∷⁺ s) = nub1ₑ P (nubₑ s)

nub1ₑ-≡ : ∀ {Θ} → (P : List (EAtom Θ)) → (s : Alts (List (EAtom Θ)))
        → ⟦ nub1ₑ P s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ P ⟧ᵉˢ ⊔̂ₑ ⟦ s ⟧ᵉˢ⁺
nub1ₑ-≡ P s with withinₑ? P s
... | just p  = ≡̂ₑ-sym p
... | nothing = ≡̂ₑ-refl

nubₑ-≡ : ∀ {Θ} → (s : Alts (List (EAtom Θ))) → ⟦ nubₑ s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺
nubₑ-≡ (alt P)  = ≡̂ₑ-refl
nubₑ-≡ (P ∷⁺ s) =
  ≡̂ₑ-trans (nub1ₑ-≡ P (nubₑ s)) (≡̂ₑ-cong-⊔ ≡̂ₑ-refl (nubₑ-≡ s))

-- An alternative that is the top: the constant `⊤`, or the empty
-- product when the unit is the top, `consₑ` dropping a constant that
-- is the unit

isTopₑ? : ∀ {Θ} → (P : List (EAtom Θ)) → Maybe (⟦ P ⟧ᵉᵖ ≡̂ₑ econst ⊤ₑ)
isTopₑ? [] with uₑ ≃ₑ? ⊤ₑ
... | yes p = just (≡̂ₑ-const p)
... | no _  = nothing
isTopₑ? (ac c ∷ []) with c ≃ₑ? ⊤ₑ
... | yes p = just (≡̂ₑ-const p)
... | no _  = nothing
isTopₑ? _ = nothing

isTopₑ-≡ : ∀ {Θ} → (P : List (EAtom Θ)) → ⟦ P ⟧ᵉᵖ ≡̂ₑ econst ⊤ₑ
         → ⟦ P ⟧ᵉˢ ≡̂ₑ econst ⊤ₑ
isTopₑ-≡ P eq = ≡̂ₑ-trans (⟦⟧ᵉᵖ-≡ P) eq

-- A sum with a top alternative is the top, which absorbs the join

topSumₑ? : ∀ {Θ} → (s : Alts (List (EAtom Θ))) → Maybe (⟦ s ⟧ᵉˢ⁺ ≡̂ₑ econst ⊤ₑ)
topSumₑ? (alt P) with isTopₑ? P
... | just eq = just (isTopₑ-≡ P eq)
... | nothing = nothing
topSumₑ? (P ∷⁺ s) with isTopₑ? P
... | just eq =
      just (≡̂ₑ-trans (≡̂ₑ-cong-⊔ (isTopₑ-≡ P eq) ≡̂ₑ-refl)
                     (≡̂ₑ-trans ≡̂ₑ-comm-⊔ ≡̂ₑ-⊤-⊔))
... | nothing with topSumₑ? s
...   | just q  = just (≡̂ₑ-trans (≡̂ₑ-cong-⊔ ≡̂ₑ-refl q) ≡̂ₑ-⊤-⊔)
...   | nothing = nothing

-- Such a sum is replaced by the normal form of the top itself

absorbₑ : ∀ {Θ} → Alts (List (EAtom Θ)) → Alts (List (EAtom Θ))
absorbₑ s with topSumₑ? s
... | just _  = alt (consₑ (ac ⊤ₑ) [])
... | nothing = s

absorbₑ-≡ : ∀ {Θ} → (s : Alts (List (EAtom Θ))) → ⟦ absorbₑ s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺
absorbₑ-≡ s with topSumₑ? s
... | just q  =
      ≡̂ₑ-trans (consₑ-≡ (ac ⊤ₑ) []) (≡̂ₑ-trans ≡̂ₑ-identityʳ (≡̂ₑ-sym q))
... | nothing = ≡̂ₑ-refl

flatₑ : ∀ {Θ} → EExp Θ → Alts (List (EAtom Θ))
flatₑ (evar i)   = alt (av i ∷ [])
flatₑ (econst c) = alt (consₑ (ac c) [])
flatₑ (ε ·̂ₑ ε')  = absorbₑ (nubₑ (mulₑ (flatₑ ε) (flatₑ ε')))
flatₑ (ε ⊔̂ₑ ε')  = absorbₑ (nubₑ (flatₑ ε ⧺ flatₑ ε'))

flatₑ-≡ : ∀ {Θ} → (ε : EExp Θ) → ε ≡̂ₑ ⟦ flatₑ ε ⟧ᵉˢ⁺
flatₑ-≡ (evar i)   = ≡̂ₑ-sym ≡̂ₑ-identityʳ
flatₑ-≡ (econst c) = ≡̂ₑ-sym (≡̂ₑ-trans (consₑ-≡ (ac c) []) ≡̂ₑ-identityʳ)
flatₑ-≡ (ε ·̂ₑ ε')  =
  ≡̂ₑ-trans (≡̂ₑ-cong (flatₑ-≡ ε) (flatₑ-≡ ε'))
           (≡̂ₑ-sym (≡̂ₑ-trans (absorbₑ-≡ (nubₑ (mulₑ (flatₑ ε) (flatₑ ε'))))
                    (≡̂ₑ-trans (nubₑ-≡ (mulₑ (flatₑ ε) (flatₑ ε')))
                              (mulₑ-≡ (flatₑ ε) (flatₑ ε')))))
flatₑ-≡ (ε ⊔̂ₑ ε')  =
  ≡̂ₑ-trans (≡̂ₑ-cong-⊔ (flatₑ-≡ ε) (flatₑ-≡ ε'))
           (≡̂ₑ-sym (≡̂ₑ-trans (absorbₑ-≡ (nubₑ (flatₑ ε ⧺ flatₑ ε')))
                    (≡̂ₑ-trans (nubₑ-≡ (flatₑ ε ⧺ flatₑ ε'))
                              (⧺ₑ-≡ (flatₑ ε) (flatₑ ε')))))

------------------------------------------------------------------
-- Resource grades

data RAtom (Θ : Scope) : Set where
  rc : R → RAtom Θ
  rv : RVar Θ → RAtom Θ
  rm : EVar Θ → RAtom Θ

⟦_⟧ʳᵃ : ∀ {Θ} → RAtom Θ → RExp Θ
⟦ rc c ⟧ʳᵃ = rconst c
⟦ rv i ⟧ʳᵃ = rvar i
⟦ rm i ⟧ʳᵃ = ∣ evar i ∣̂ᵉ

⟦_⟧ʳᵖ : ∀ {Θ} → List (RAtom Θ) → RExp Θ
⟦ [] ⟧ʳᵖ         = ûᵣ
⟦ a ∷ [] ⟧ʳᵖ     = ⟦ a ⟧ʳᵃ
⟦ a ∷ b ∷ as ⟧ʳᵖ = ⟦ a ⟧ʳᵃ ·̂ᵣ ⟦ b ∷ as ⟧ʳᵖ

⟦_⟧ʳˢ : ∀ {Θ} → List (RAtom Θ) → RExp Θ
⟦ [] ⟧ʳˢ     = ûᵣ
⟦ a ∷ as ⟧ʳˢ = ⟦ a ⟧ʳᵃ ·̂ᵣ ⟦ as ⟧ʳˢ

⟦_⟧ʳᵖ⁺ : ∀ {Θ} → Alts (List (RAtom Θ)) → RExp Θ
⟦ alt P ⟧ʳᵖ⁺  = ⟦ P ⟧ʳᵖ
⟦ P ∷⁺ s ⟧ʳᵖ⁺ = ⟦ P ⟧ʳᵖ ⊔̂ᵣ ⟦ s ⟧ʳᵖ⁺

⟦_⟧ʳˢ⁺ : ∀ {Θ} → Alts (List (RAtom Θ)) → RExp Θ
⟦ alt P ⟧ʳˢ⁺  = ⟦ P ⟧ʳˢ
⟦ P ∷⁺ s ⟧ʳˢ⁺ = ⟦ P ⟧ʳˢ ⊔̂ᵣ ⟦ s ⟧ʳˢ⁺

⟦⟧ʳᵖ-≡ : ∀ {Θ} → (as : List (RAtom Θ)) → ⟦ as ⟧ʳˢ ≡̂ᵣ ⟦ as ⟧ʳᵖ
⟦⟧ʳᵖ-≡ []           = ≡̂ᵣ-refl
⟦⟧ʳᵖ-≡ (a ∷ [])     = ≡̂ᵣ-identityʳ
⟦⟧ʳᵖ-≡ (a ∷ b ∷ as) = ≡̂ᵣ-cong ≡̂ᵣ-refl (⟦⟧ʳᵖ-≡ (b ∷ as))

⟦⟧ʳᵖ⁺-≡ : ∀ {Θ} → (s : Alts (List (RAtom Θ))) → ⟦ s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳᵖ⁺
⟦⟧ʳᵖ⁺-≡ (alt P)  = ⟦⟧ʳᵖ-≡ P
⟦⟧ʳᵖ⁺-≡ (P ∷⁺ s) = ≡̂ᵣ-cong-⊔ (⟦⟧ʳᵖ-≡ P) (⟦⟧ʳᵖ⁺-≡ s)

consᵣ : ∀ {Θ} → RAtom Θ → List (RAtom Θ) → List (RAtom Θ)
consᵣ (rc c) (rc d ∷ as) = consᵣ (rc (c ·ᵣ d)) as
consᵣ (rc c) as with c ≃ᵣ? uᵣ
... | yes _ = as
... | no _  = rc c ∷ as
consᵣ (rv i) as = rv i ∷ as
consᵣ (rm i) as = rm i ∷ as

consᵣ-≡ : ∀ {Θ} → (a : RAtom Θ) → (as : List (RAtom Θ))
        → ⟦ consᵣ a as ⟧ʳˢ ≡̂ᵣ ⟦ a ⟧ʳᵃ ·̂ᵣ ⟦ as ⟧ʳˢ
consᵣ-≡ (rc c) (rc d ∷ as) =
  ≡̂ᵣ-trans (consᵣ-≡ (rc (c ·ᵣ d)) as)
  (≡̂ᵣ-trans (≡̂ᵣ-cong (≡̂ᵣ-sym ≡̂ᵣ-const-·) ≡̂ᵣ-refl) ≡̂ᵣ-assoc)
consᵣ-≡ (rc c) [] with c ≃ᵣ? uᵣ
... | yes e = ≡̂ᵣ-trans (≡̂ᵣ-sym ≡̂ᵣ-identityˡ) (≡̂ᵣ-cong (≡̂ᵣ-const (≃ᵣ-sym e)) ≡̂ᵣ-refl)
... | no _     = ≡̂ᵣ-refl
consᵣ-≡ (rc c) (rv i ∷ as) with c ≃ᵣ? uᵣ
... | yes e = ≡̂ᵣ-trans (≡̂ᵣ-sym ≡̂ᵣ-identityˡ) (≡̂ᵣ-cong (≡̂ᵣ-const (≃ᵣ-sym e)) ≡̂ᵣ-refl)
... | no _     = ≡̂ᵣ-refl
consᵣ-≡ (rc c) (rm i ∷ as) with c ≃ᵣ? uᵣ
... | yes e = ≡̂ᵣ-trans (≡̂ᵣ-sym ≡̂ᵣ-identityˡ) (≡̂ᵣ-cong (≡̂ᵣ-const (≃ᵣ-sym e)) ≡̂ᵣ-refl)
... | no _     = ≡̂ᵣ-refl
consᵣ-≡ (rv i) as = ≡̂ᵣ-refl
consᵣ-≡ (rm i) as = ≡̂ᵣ-refl

appᵣ : ∀ {Θ} → List (RAtom Θ) → List (RAtom Θ) → List (RAtom Θ)
appᵣ []       ys = ys
appᵣ (a ∷ as) ys = consᵣ a (appᵣ as ys)

appᵣ-≡ : ∀ {Θ} → (as bs : List (RAtom Θ))
       → ⟦ appᵣ as bs ⟧ʳˢ ≡̂ᵣ ⟦ as ⟧ʳˢ ·̂ᵣ ⟦ bs ⟧ʳˢ
appᵣ-≡ []       bs = ≡̂ᵣ-sym ≡̂ᵣ-identityˡ
appᵣ-≡ (a ∷ as) bs =
  ≡̂ᵣ-trans (consᵣ-≡ a (appᵣ as bs))
  (≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl (appᵣ-≡ as bs)) (≡̂ᵣ-sym ≡̂ᵣ-assoc))

⧺ᵣ-≡ : ∀ {Θ} → (s t : Alts (List (RAtom Θ)))
     → ⟦ s ⧺ t ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺ ⊔̂ᵣ ⟦ t ⟧ʳˢ⁺
⧺ᵣ-≡ (alt P)  t = ≡̂ᵣ-refl
⧺ᵣ-≡ (P ∷⁺ s) t =
  ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ ≡̂ᵣ-refl (⧺ᵣ-≡ s t)) (≡̂ᵣ-sym ≡̂ᵣ-assoc-⊔)

mul1ᵣ : ∀ {Θ} → List (RAtom Θ) → Alts (List (RAtom Θ)) → Alts (List (RAtom Θ))
mul1ᵣ P (alt Q)  = alt (appᵣ P Q)
mul1ᵣ P (Q ∷⁺ t) = appᵣ P Q ∷⁺ mul1ᵣ P t

mulᵣ : ∀ {Θ} → Alts (List (RAtom Θ)) → Alts (List (RAtom Θ))
     → Alts (List (RAtom Θ))
mulᵣ (alt P)  t = mul1ᵣ P t
mulᵣ (P ∷⁺ s) t = mul1ᵣ P t ⧺ mulᵣ s t

mul1ᵣ-≡ : ∀ {Θ} → (P : List (RAtom Θ)) → (t : Alts (List (RAtom Θ)))
        → ⟦ mul1ᵣ P t ⟧ʳˢ⁺ ≡̂ᵣ ⟦ P ⟧ʳˢ ·̂ᵣ ⟦ t ⟧ʳˢ⁺
mul1ᵣ-≡ P (alt Q)  = appᵣ-≡ P Q
mul1ᵣ-≡ P (Q ∷⁺ t) =
  ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (appᵣ-≡ P Q) (mul1ᵣ-≡ P t)) (≡̂ᵣ-sym ≡̂ᵣ-distribˡ-⊔)

mulᵣ-≡ : ∀ {Θ} → (s t : Alts (List (RAtom Θ)))
       → ⟦ mulᵣ s t ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺ ·̂ᵣ ⟦ t ⟧ʳˢ⁺
mulᵣ-≡ (alt P)  t = mul1ᵣ-≡ P t
mulᵣ-≡ (P ∷⁺ s) t =
  ≡̂ᵣ-trans (⧺ᵣ-≡ (mul1ᵣ P t) (mulᵣ s t))
  (≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (mul1ᵣ-≡ P t) (mulᵣ-≡ s t)) (≡̂ᵣ-sym ≡̂ᵣ-distribʳ-⊔))

_≟ᵃᵣ_ : ∀ {Θ} → (a b : RAtom Θ) → Dec (⟦ a ⟧ʳᵃ ≅ʳ ⟦ b ⟧ʳᵃ)
a ≟ᵃᵣ b = ⟦ a ⟧ʳᵃ ≟ʳ ⟦ b ⟧ʳᵃ

_≟ᵖᵣ_ : ∀ {Θ} → (P Q : List (RAtom Θ)) → Dec (⟦ P ⟧ʳˢ ≅ʳ ⟦ Q ⟧ʳˢ)
P ≟ᵖᵣ Q = ⟦ P ⟧ʳˢ ≟ʳ ⟦ Q ⟧ʳˢ

-- An alternative already in the sum is absorbed by it, which keeps
-- the order of the remaining alternatives

withinᵣ? : ∀ {Θ} → (P : List (RAtom Θ)) → (s : Alts (List (RAtom Θ)))
         → Maybe (⟦ P ⟧ʳˢ ⊔̂ᵣ ⟦ s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺)
withinᵣ? P (alt Q) with P ≟ᵖᵣ Q
... | yes e = just (≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (≅ʳ⇒≡̂ e) ≡̂ᵣ-refl) ≡̂ᵣ-idem-⊔)
... | no _     = nothing
withinᵣ? P (Q ∷⁺ t) with P ≟ᵖᵣ Q
... | yes e =
      just (≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (≅ʳ⇒≡̂ e) ≡̂ᵣ-refl)
           (≡̂ᵣ-trans (≡̂ᵣ-sym ≡̂ᵣ-assoc-⊔) (≡̂ᵣ-cong-⊔ ≡̂ᵣ-idem-⊔ ≡̂ᵣ-refl)))
... | no _ with withinᵣ? P t
...   | just p  =
        just (≡̂ᵣ-trans (≡̂ᵣ-sym ≡̂ᵣ-assoc-⊔)
             (≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ ≡̂ᵣ-comm-⊔ ≡̂ᵣ-refl)
             (≡̂ᵣ-trans ≡̂ᵣ-assoc-⊔ (≡̂ᵣ-cong-⊔ ≡̂ᵣ-refl p))))
...   | nothing = nothing

nub1ᵣ : ∀ {Θ} → List (RAtom Θ) → Alts (List (RAtom Θ)) → Alts (List (RAtom Θ))
nub1ᵣ P s with withinᵣ? P s
... | just _  = s
... | nothing = P ∷⁺ s

nubᵣ : ∀ {Θ} → Alts (List (RAtom Θ)) → Alts (List (RAtom Θ))
nubᵣ (alt P)  = alt P
nubᵣ (P ∷⁺ s) = nub1ᵣ P (nubᵣ s)

nub1ᵣ-≡ : ∀ {Θ} → (P : List (RAtom Θ)) → (s : Alts (List (RAtom Θ)))
        → ⟦ nub1ᵣ P s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ P ⟧ʳˢ ⊔̂ᵣ ⟦ s ⟧ʳˢ⁺
nub1ᵣ-≡ P s with withinᵣ? P s
... | just p  = ≡̂ᵣ-sym p
... | nothing = ≡̂ᵣ-refl

nubᵣ-≡ : ∀ {Θ} → (s : Alts (List (RAtom Θ))) → ⟦ nubᵣ s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺
nubᵣ-≡ (alt P)  = ≡̂ᵣ-refl
nubᵣ-≡ (P ∷⁺ s) =
  ≡̂ᵣ-trans (nub1ᵣ-≡ P (nubᵣ s)) (≡̂ᵣ-cong-⊔ ≡̂ᵣ-refl (nubᵣ-≡ s))

isTopᵣ? : ∀ {Θ} → (P : List (RAtom Θ)) → Maybe (⟦ P ⟧ʳᵖ ≡̂ᵣ rconst ⊤ᵣ)
isTopᵣ? [] with uᵣ ≃ᵣ? ⊤ᵣ
... | yes p = just (≡̂ᵣ-const p)
... | no _  = nothing
isTopᵣ? (rc c ∷ []) with c ≃ᵣ? ⊤ᵣ
... | yes p = just (≡̂ᵣ-const p)
... | no _  = nothing
isTopᵣ? _ = nothing

isTopᵣ-≡ : ∀ {Θ} → (P : List (RAtom Θ)) → ⟦ P ⟧ʳᵖ ≡̂ᵣ rconst ⊤ᵣ
         → ⟦ P ⟧ʳˢ ≡̂ᵣ rconst ⊤ᵣ
isTopᵣ-≡ P eq = ≡̂ᵣ-trans (⟦⟧ʳᵖ-≡ P) eq

topSumᵣ? : ∀ {Θ} → (s : Alts (List (RAtom Θ))) → Maybe (⟦ s ⟧ʳˢ⁺ ≡̂ᵣ rconst ⊤ᵣ)
topSumᵣ? (alt P) with isTopᵣ? P
... | just eq = just (isTopᵣ-≡ P eq)
... | nothing = nothing
topSumᵣ? (P ∷⁺ s) with isTopᵣ? P
... | just eq =
      just (≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (isTopᵣ-≡ P eq) ≡̂ᵣ-refl)
                     (≡̂ᵣ-trans ≡̂ᵣ-comm-⊔ ≡̂ᵣ-⊤-⊔))
... | nothing with topSumᵣ? s
...   | just q  = just (≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ ≡̂ᵣ-refl q) ≡̂ᵣ-⊤-⊔)
...   | nothing = nothing

absorbᵣ : ∀ {Θ} → Alts (List (RAtom Θ)) → Alts (List (RAtom Θ))
absorbᵣ s with topSumᵣ? s
... | just _  = alt (consᵣ (rc ⊤ᵣ) [])
... | nothing = s

absorbᵣ-≡ : ∀ {Θ} → (s : Alts (List (RAtom Θ))) → ⟦ absorbᵣ s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺
absorbᵣ-≡ s with topSumᵣ? s
... | just q  =
      ≡̂ᵣ-trans (consᵣ-≡ (rc ⊤ᵣ) []) (≡̂ᵣ-trans ≡̂ᵣ-identityʳ (≡̂ᵣ-sym q))
... | nothing = ≡̂ᵣ-refl

-- The sum of `∣ ε ∣̂ᵉ`, read off `ε` directly: the morphism is a
-- monoid map, so it passes through a product and a join alike.

flatᵐ : ∀ {Θ} → EExp Θ → Alts (List (RAtom Θ))
flatᵐ (evar i)   = alt (rm i ∷ [])
flatᵐ (econst c) = alt (consᵣ (rc (mapᵉ c)) [])
flatᵐ (ε ·̂ₑ ε')  = absorbᵣ (nubᵣ (mulᵣ (flatᵐ ε) (flatᵐ ε')))
flatᵐ (ε ⊔̂ₑ ε')  = absorbᵣ (nubᵣ (flatᵐ ε ⧺ flatᵐ ε'))

flatᵐ-≡ : ∀ {Θ} → (ε : EExp Θ) → ∣ ε ∣̂ᵉ ≡̂ᵣ ⟦ flatᵐ ε ⟧ʳˢ⁺
flatᵐ-≡ (evar i)   = ≡̂ᵣ-sym ≡̂ᵣ-identityʳ
flatᵐ-≡ (econst c) =
  ≡̂ᵣ-trans ≡̂ᵣ-map-const
           (≡̂ᵣ-sym (≡̂ᵣ-trans (consᵣ-≡ (rc (mapᵉ c)) []) ≡̂ᵣ-identityʳ))
flatᵐ-≡ (ε ·̂ₑ ε')  =
  ≡̂ᵣ-trans ≡̂ᵣ-map-·
  (≡̂ᵣ-trans (≡̂ᵣ-cong (flatᵐ-≡ ε) (flatᵐ-≡ ε'))
            (≡̂ᵣ-sym (≡̂ᵣ-trans (absorbᵣ-≡ (nubᵣ (mulᵣ (flatᵐ ε) (flatᵐ ε'))))
                     (≡̂ᵣ-trans (nubᵣ-≡ (mulᵣ (flatᵐ ε) (flatᵐ ε')))
                               (mulᵣ-≡ (flatᵐ ε) (flatᵐ ε'))))))
flatᵐ-≡ (ε ⊔̂ₑ ε')  =
  ≡̂ᵣ-trans ≡̂ᵣ-map-⊔
  (≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (flatᵐ-≡ ε) (flatᵐ-≡ ε'))
            (≡̂ᵣ-sym (≡̂ᵣ-trans (absorbᵣ-≡ (nubᵣ (flatᵐ ε ⧺ flatᵐ ε')))
                     (≡̂ᵣ-trans (nubᵣ-≡ (flatᵐ ε ⧺ flatᵐ ε'))
                               (⧺ᵣ-≡ (flatᵐ ε) (flatᵐ ε'))))))

flatᵣ : ∀ {Θ} → RExp Θ → Alts (List (RAtom Θ))
flatᵣ (rvar i)   = alt (rv i ∷ [])
flatᵣ (rconst c) = alt (consᵣ (rc c) [])
flatᵣ (ρ ·̂ᵣ ρ')  = absorbᵣ (nubᵣ (mulᵣ (flatᵣ ρ) (flatᵣ ρ')))
flatᵣ (ρ ⊔̂ᵣ ρ')  = absorbᵣ (nubᵣ (flatᵣ ρ ⧺ flatᵣ ρ'))
flatᵣ ∣ ε ∣̂ᵉ     = flatᵐ ε

flatᵣ-≡ : ∀ {Θ} → (ρ : RExp Θ) → ρ ≡̂ᵣ ⟦ flatᵣ ρ ⟧ʳˢ⁺
flatᵣ-≡ (rvar i)   = ≡̂ᵣ-sym ≡̂ᵣ-identityʳ
flatᵣ-≡ (rconst c) = ≡̂ᵣ-sym (≡̂ᵣ-trans (consᵣ-≡ (rc c) []) ≡̂ᵣ-identityʳ)
flatᵣ-≡ (ρ ·̂ᵣ ρ')  =
  ≡̂ᵣ-trans (≡̂ᵣ-cong (flatᵣ-≡ ρ) (flatᵣ-≡ ρ'))
           (≡̂ᵣ-sym (≡̂ᵣ-trans (absorbᵣ-≡ (nubᵣ (mulᵣ (flatᵣ ρ) (flatᵣ ρ'))))
                    (≡̂ᵣ-trans (nubᵣ-≡ (mulᵣ (flatᵣ ρ) (flatᵣ ρ')))
                              (mulᵣ-≡ (flatᵣ ρ) (flatᵣ ρ')))))
flatᵣ-≡ (ρ ⊔̂ᵣ ρ')  =
  ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (flatᵣ-≡ ρ) (flatᵣ-≡ ρ'))
           (≡̂ᵣ-sym (≡̂ᵣ-trans (absorbᵣ-≡ (nubᵣ (flatᵣ ρ ⧺ flatᵣ ρ')))
                    (≡̂ᵣ-trans (nubᵣ-≡ (flatᵣ ρ ⧺ flatᵣ ρ'))
                              (⧺ᵣ-≡ (flatᵣ ρ) (flatᵣ ρ')))))
flatᵣ-≡ ∣ ε ∣̂ᵉ     = flatᵐ-≡ ε

------------------------------------------------------------------
-- Commuting products
--
-- Where the grade declares `_·_` commutative (`·ₑ-comm?`/`·ᵣ-comm?`),
-- each product of the flattening is put in one order: the product of
-- its constants, then its variables by index. Products that differ
-- only in the order of their factors then coincide, and repeats are
-- merged again. Elsewhere the flattening is the normal form.

-- The constant of an effect product, and its variables

constₑ : ∀ {Θ} → List (EAtom Θ) → E
constₑ []          = uₑ
constₑ (ac c ∷ as) = c ·ₑ constₑ as
constₑ (av _ ∷ as) = constₑ as

varsᵃₑ : ∀ {Θ} → List (EAtom Θ) → List (EAtom Θ)
varsᵃₑ []          = []
varsᵃₑ (ac _ ∷ as) = varsᵃₑ as
varsᵃₑ (av i ∷ as) = av i ∷ varsᵃₑ as

_<ᵉᵃ_ : ∀ {Θ} → EAtom Θ → EAtom Θ → 𝔹
av i <ᵉᵃ av j = toℕ i <ᵇ toℕ j
_    <ᵉᵃ _    = false

commuteₑ : ∀ {Θ} → List (EAtom Θ) → List (EAtom Θ)
commuteₑ as = consₑ (ac (constₑ as)) (sortBy _<ᵉᵃ_ (varsᵃₑ as))

module Commuteₑ (ij : Is-just ·ₑ-comm?) where

  swapₑ : ∀ {Θ} {a b x : EExp Θ} → a ·̂ₑ (b ·̂ₑ x) ≡̂ₑ b ·̂ₑ (a ·̂ₑ x)
  swapₑ = ≡̂ₑ-trans (≡̂ₑ-sym ≡̂ₑ-assoc)
                   (≡̂ₑ-trans (≡̂ₑ-cong (≡̂ₑ-comm ij) ≡̂ₑ-refl) ≡̂ₑ-assoc)

  insert-≡ : ∀ {Θ} → (a : EAtom Θ) → (bs : List (EAtom Θ))
           → ⟦ insertBy _<ᵉᵃ_ a bs ⟧ᵉˢ ≡̂ₑ ⟦ a ⟧ᵉᵃ ·̂ₑ ⟦ bs ⟧ᵉˢ
  insert-≡ a []       = ≡̂ₑ-refl
  insert-≡ a (b ∷ bs) with b <ᵉᵃ a
  ... | true  = ≡̂ₑ-trans (≡̂ₑ-cong ≡̂ₑ-refl (insert-≡ a bs)) swapₑ
  ... | false = ≡̂ₑ-refl

  sort-≡ : ∀ {Θ} → (as : List (EAtom Θ)) → ⟦ sortBy _<ᵉᵃ_ as ⟧ᵉˢ ≡̂ₑ ⟦ as ⟧ᵉˢ
  sort-≡ []       = ≡̂ₑ-refl
  sort-≡ (a ∷ as) =
    ≡̂ₑ-trans (insert-≡ a (sortBy _<ᵉᵃ_ as)) (≡̂ₑ-cong ≡̂ₑ-refl (sort-≡ as))

  split-≡ : ∀ {Θ} → (as : List (EAtom Θ))
          → ⟦ as ⟧ᵉˢ ≡̂ₑ econst (constₑ as) ·̂ₑ ⟦ varsᵃₑ as ⟧ᵉˢ
  split-≡ []          = ≡̂ₑ-sym ≡̂ₑ-identityʳ
  split-≡ (ac d ∷ as) =
    ≡̂ₑ-trans (≡̂ₑ-cong ≡̂ₑ-refl (split-≡ as))
    (≡̂ₑ-trans (≡̂ₑ-sym ≡̂ₑ-assoc) (≡̂ₑ-cong ≡̂ₑ-const-· ≡̂ₑ-refl))
  split-≡ (av i ∷ as) = ≡̂ₑ-trans (≡̂ₑ-cong ≡̂ₑ-refl (split-≡ as)) swapₑ

  -- A product is the atom at any of its positions times the rest

  remove-≡ : ∀ {Θ} {P : EAtom Θ → Set} {as : List (EAtom Θ)} → (p : Any P as)
           → ⟦ as ⟧ᵉˢ ≡̂ₑ ⟦ Any.lookup p ⟧ᵉᵃ ·̂ₑ ⟦ as ─ p ⟧ᵉˢ
  remove-≡ (here _)  = ≡̂ₑ-refl
  remove-≡ (there p) = ≡̂ₑ-trans (≡̂ₑ-cong ≡̂ₑ-refl (remove-≡ p)) swapₑ

  commute-≡ : ∀ {Θ} → (as : List (EAtom Θ)) → ⟦ commuteₑ as ⟧ᵉˢ ≡̂ₑ ⟦ as ⟧ᵉˢ
  commute-≡ as =
    ≡̂ₑ-trans (consₑ-≡ (ac (constₑ as)) (sortBy _<ᵉᵃ_ (varsᵃₑ as)))
    (≡̂ₑ-trans (≡̂ₑ-cong ≡̂ₑ-refl (sort-≡ (varsᵃₑ as))) (≡̂ₑ-sym (split-≡ as)))

  commutes-≡ : ∀ {Θ} → (s : Alts (List (EAtom Θ)))
             → ⟦ mapᴬ commuteₑ s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺
  commutes-≡ (alt P)  = commute-≡ P
  commutes-≡ (P ∷⁺ s) = ≡̂ₑ-cong-⊔ (commute-≡ P) (commutes-≡ s)

commSumₑ : ∀ {Θ} → Maybe (Commutative _≃ₑ_ _·ₑ_)
         → Alts (List (EAtom Θ)) → Alts (List (EAtom Θ))
commSumₑ (just _) s = nubₑ (mapᴬ commuteₑ s)
commSumₑ nothing  s = s

commSumₑ-≡ : ∀ {Θ} → (m : Maybe (Commutative _≃ₑ_ _·ₑ_)) → ·ₑ-comm? ≡ m
           → (s : Alts (List (EAtom Θ))) → ⟦ commSumₑ m s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺
commSumₑ-≡ (just c) eq s =
  ≡̂ₑ-trans (nubₑ-≡ (mapᴬ commuteₑ s)) (Commuteₑ.commutes-≡ (≡-Is-just eq) s)
commSumₑ-≡ nothing  _  s = ≡̂ₑ-refl

-- The constant of a resource product, and its variables: resource
-- variables, then images of effect variables, each by index

constᵣ : ∀ {Θ} → List (RAtom Θ) → R
constᵣ []          = uᵣ
constᵣ (rc c ∷ as) = c ·ᵣ constᵣ as
constᵣ (rv _ ∷ as) = constᵣ as
constᵣ (rm _ ∷ as) = constᵣ as

varsᵃᵣ : ∀ {Θ} → List (RAtom Θ) → List (RAtom Θ)
varsᵃᵣ []          = []
varsᵃᵣ (rc _ ∷ as) = varsᵃᵣ as
varsᵃᵣ (rv i ∷ as) = rv i ∷ varsᵃᵣ as
varsᵃᵣ (rm i ∷ as) = rm i ∷ varsᵃᵣ as

_<ʳᵃ_ : ∀ {Θ} → RAtom Θ → RAtom Θ → 𝔹
rv i <ʳᵃ rv j = toℕ i <ᵇ toℕ j
rv _ <ʳᵃ rm _ = true
rm i <ʳᵃ rm j = toℕ i <ᵇ toℕ j
_    <ʳᵃ _    = false

commuteᵣ : ∀ {Θ} → List (RAtom Θ) → List (RAtom Θ)
commuteᵣ as = consᵣ (rc (constᵣ as)) (sortBy _<ʳᵃ_ (varsᵃᵣ as))

module Commuteᵣ (ij : Is-just ·ᵣ-comm?) where

  swapᵣ : ∀ {Θ} {a b x : RExp Θ} → a ·̂ᵣ (b ·̂ᵣ x) ≡̂ᵣ b ·̂ᵣ (a ·̂ᵣ x)
  swapᵣ = ≡̂ᵣ-trans (≡̂ᵣ-sym ≡̂ᵣ-assoc)
                   (≡̂ᵣ-trans (≡̂ᵣ-cong (≡̂ᵣ-comm ij) ≡̂ᵣ-refl) ≡̂ᵣ-assoc)

  insert-≡ : ∀ {Θ} → (a : RAtom Θ) → (bs : List (RAtom Θ))
           → ⟦ insertBy _<ʳᵃ_ a bs ⟧ʳˢ ≡̂ᵣ ⟦ a ⟧ʳᵃ ·̂ᵣ ⟦ bs ⟧ʳˢ
  insert-≡ a []       = ≡̂ᵣ-refl
  insert-≡ a (b ∷ bs) with b <ʳᵃ a
  ... | true  = ≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl (insert-≡ a bs)) swapᵣ
  ... | false = ≡̂ᵣ-refl

  sort-≡ : ∀ {Θ} → (as : List (RAtom Θ)) → ⟦ sortBy _<ʳᵃ_ as ⟧ʳˢ ≡̂ᵣ ⟦ as ⟧ʳˢ
  sort-≡ []       = ≡̂ᵣ-refl
  sort-≡ (a ∷ as) =
    ≡̂ᵣ-trans (insert-≡ a (sortBy _<ʳᵃ_ as)) (≡̂ᵣ-cong ≡̂ᵣ-refl (sort-≡ as))

  split-≡ : ∀ {Θ} → (as : List (RAtom Θ))
          → ⟦ as ⟧ʳˢ ≡̂ᵣ rconst (constᵣ as) ·̂ᵣ ⟦ varsᵃᵣ as ⟧ʳˢ
  split-≡ []          = ≡̂ᵣ-sym ≡̂ᵣ-identityʳ
  split-≡ (rc d ∷ as) =
    ≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl (split-≡ as))
    (≡̂ᵣ-trans (≡̂ᵣ-sym ≡̂ᵣ-assoc) (≡̂ᵣ-cong ≡̂ᵣ-const-· ≡̂ᵣ-refl))
  split-≡ (rv i ∷ as) = ≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl (split-≡ as)) swapᵣ
  split-≡ (rm i ∷ as) = ≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl (split-≡ as)) swapᵣ

  remove-≡ : ∀ {Θ} {P : RAtom Θ → Set} {as : List (RAtom Θ)} → (p : Any P as)
           → ⟦ as ⟧ʳˢ ≡̂ᵣ ⟦ Any.lookup p ⟧ʳᵃ ·̂ᵣ ⟦ as ─ p ⟧ʳˢ
  remove-≡ (here _)  = ≡̂ᵣ-refl
  remove-≡ (there p) = ≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl (remove-≡ p)) swapᵣ

  commute-≡ : ∀ {Θ} → (as : List (RAtom Θ)) → ⟦ commuteᵣ as ⟧ʳˢ ≡̂ᵣ ⟦ as ⟧ʳˢ
  commute-≡ as =
    ≡̂ᵣ-trans (consᵣ-≡ (rc (constᵣ as)) (sortBy _<ʳᵃ_ (varsᵃᵣ as)))
    (≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl (sort-≡ (varsᵃᵣ as))) (≡̂ᵣ-sym (split-≡ as)))

  commutes-≡ : ∀ {Θ} → (s : Alts (List (RAtom Θ)))
             → ⟦ mapᴬ commuteᵣ s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺
  commutes-≡ (alt P)  = commute-≡ P
  commutes-≡ (P ∷⁺ s) = ≡̂ᵣ-cong-⊔ (commute-≡ P) (commutes-≡ s)

commSumᵣ : ∀ {Θ} → Maybe (Commutative _≃ᵣ_ _·ᵣ_)
         → Alts (List (RAtom Θ)) → Alts (List (RAtom Θ))
commSumᵣ (just _) s = nubᵣ (mapᴬ commuteᵣ s)
commSumᵣ nothing  s = s

commSumᵣ-≡ : ∀ {Θ} → (m : Maybe (Commutative _≃ᵣ_ _·ᵣ_)) → ·ᵣ-comm? ≡ m
           → (s : Alts (List (RAtom Θ))) → ⟦ commSumᵣ m s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺
commSumᵣ-≡ (just c) eq s =
  ≡̂ᵣ-trans (nubᵣ-≡ (mapᴬ commuteᵣ s)) (Commuteᵣ.commutes-≡ (≡-Is-just eq) s)
commSumᵣ-≡ nothing  _  s = ≡̂ᵣ-refl

-- The normal forms: the flattening, its products reordered where the
-- grade commutes

nrmₑ : ∀ {Θ} → EExp Θ → Alts (List (EAtom Θ))
nrmₑ ε = commSumₑ ·ₑ-comm? (flatₑ ε)

nrmₑ-≡ : ∀ {Θ} → (ε : EExp Θ) → ε ≡̂ₑ ⟦ nrmₑ ε ⟧ᵉˢ⁺
nrmₑ-≡ ε = ≡̂ₑ-trans (flatₑ-≡ ε) (≡̂ₑ-sym (commSumₑ-≡ ·ₑ-comm? refl (flatₑ ε)))

nrmᵣ : ∀ {Θ} → RExp Θ → Alts (List (RAtom Θ))
nrmᵣ ρ = commSumᵣ ·ᵣ-comm? (flatᵣ ρ)

nrmᵣ-≡ : ∀ {Θ} → (ρ : RExp Θ) → ρ ≡̂ᵣ ⟦ nrmᵣ ρ ⟧ʳˢ⁺
nrmᵣ-≡ ρ = ≡̂ᵣ-trans (flatᵣ-≡ ρ) (≡̂ᵣ-sym (commSumᵣ-≡ ·ᵣ-comm? refl (flatᵣ ρ)))

-- The normal form read back without trailing units, which is what
-- `deriveₑ`/`deriveᵣ` of `Entail` compare, alternative by alternative

nrmₑ-≡ᵖ : ∀ {Θ} → (ε : EExp Θ) → ε ≡̂ₑ ⟦ nrmₑ ε ⟧ᵉᵖ⁺
nrmₑ-≡ᵖ ε = ≡̂ₑ-trans (nrmₑ-≡ ε) (⟦⟧ᵉᵖ⁺-≡ (nrmₑ ε))

nrmᵣ-≡ᵖ : ∀ {Θ} → (ρ : RExp Θ) → ρ ≡̂ᵣ ⟦ nrmᵣ ρ ⟧ʳᵖ⁺
nrmᵣ-≡ᵖ ρ = ≡̂ᵣ-trans (nrmᵣ-≡ ρ) (⟦⟧ʳᵖ⁺-≡ (nrmᵣ ρ))

------------------------------------------------------------------
-- Canonical forms
--
-- `Grouping` at both sorts, and the passage to and from its products.
-- A product of `nrmₑ`/`nrmᵣ` is read into its skeleton and slots, the
-- constants of a run multiplied into one slot, and read back through
-- `consₑ`/`consᵣ`, which drops a slot holding the unit. The canonical
-- forms themselves need the decider, and are assembled in
-- `SolverImpl.Canon`.

-- Constants are compared by the grade's equivalence

sameConstₑ? : ∀ {Θ} → (c d : E) → Maybe (econst {Θ} c ≡̂ₑ econst d)
sameConstₑ? c d with c ≃ₑ? d
... | yes e = just (≡̂ₑ-const e)
... | no _  = nothing

sameConstᵣ? : ∀ {Θ} → (c d : R) → Maybe (rconst {Θ} c ≡̂ᵣ rconst d)
sameConstᵣ? c d with c ≃ᵣ? d
... | yes e = just (≡̂ᵣ-const e)
... | no _  = nothing

-- Effect variables are ordered by index

_<ᵉᵛ_ : ∀ {Θ} → EVar Θ → EVar Θ → 𝔹
i <ᵉᵛ j = toℕ i <ᵇ toℕ j

module Gₑ {Θ : Scope} =
  Grouping {EExp Θ} {E} {EVar Θ} _≡̂ₑ_ ≡̂ₑ-refl ≡̂ₑ-sym ≡̂ₑ-trans _·̂ₑ_ _⊔̂ₑ_
           ≡̂ₑ-cong ≡̂ₑ-cong-⊔ ≡̂ₑ-idem-⊔ ≡̂ₑ-comm-⊔ ≡̂ₑ-assoc-⊔
           ≡̂ₑ-distribˡ-⊔ ≡̂ₑ-distribʳ-⊔
           econst _⊔ₑ_ ≡̂ₑ-const-⊔ sameConstₑ? evar _≟ᶠ_ (_<ᵉᵛ_ {Θ})

-- The unit, where no constant has been met

⌊_⌋ₑ : Maybe E → E
⌊ nothing ⌋ₑ = uₑ
⌊ just c ⌋ₑ  = c

_·ᵐₑ_ : Maybe E → E → E
nothing ·ᵐₑ c = c
just b  ·ᵐₑ c = b ·ₑ c

slotsₑ : ∀ {Θ} → Maybe E → List (EAtom Θ) → Gₑ.Prod {Θ}
slotsₑ m        []           = [] , Gₑ.⌜ ⌊ m ⌋ₑ ⌝
slotsₑ m        (ac c ∷ as) = slotsₑ (just (m ·ᵐₑ c)) as
slotsₑ m        (av i ∷ as) = i ∷ proj₁ P , (⌊ m ⌋ₑ Gₑ.▸ proj₂ P)
  where P = slotsₑ nothing as

slotsₑ-≡ : ∀ {Θ} → (m : Maybe E) → (as : List (EAtom Θ))
         → Gₑ.⟦ slotsₑ m as ⟧ᵖ ≡̂ₑ econst ⌊ m ⌋ₑ ·̂ₑ ⟦ as ⟧ᵉˢ
slotsₑ-≡ m        []           = ≡̂ₑ-sym ≡̂ₑ-identityʳ
slotsₑ-≡ nothing  (ac c ∷ as) = ≡̂ₑ-trans (slotsₑ-≡ (just c) as) (≡̂ₑ-sym ≡̂ₑ-identityˡ)
slotsₑ-≡ (just b) (ac c ∷ as) =
  ≡̂ₑ-trans (slotsₑ-≡ (just (b ·ₑ c)) as)
  (≡̂ₑ-trans (≡̂ₑ-cong (≡̂ₑ-sym ≡̂ₑ-const-·) ≡̂ₑ-refl) ≡̂ₑ-assoc)
slotsₑ-≡ m        (av i ∷ as) =
  ≡̂ₑ-cong ≡̂ₑ-refl (≡̂ₑ-cong ≡̂ₑ-refl (≡̂ₑ-trans (slotsₑ-≡ nothing as) ≡̂ₑ-identityˡ))

atomsₑ : ∀ {Θ vs} → Gₑ.Slots {Θ} vs → List (EAtom Θ)
atomsₑ Gₑ.⌜ c ⌝            = consₑ (ac c) []
atomsₑ (Gₑ._▸_ {i} c s) = consₑ (ac c) (av i ∷ atomsₑ s)

atomsₑ-≡ : ∀ {Θ vs} → (s : Gₑ.Slots {Θ} vs) → ⟦ atomsₑ s ⟧ᵉˢ ≡̂ₑ Gₑ.⟦ s ⟧ᵏ
atomsₑ-≡ Gₑ.⌜ c ⌝            = ≡̂ₑ-trans (consₑ-≡ (ac c) []) ≡̂ₑ-identityʳ
atomsₑ-≡ (Gₑ._▸_ {i} c s) =
  ≡̂ₑ-trans (consₑ-≡ (ac c) (av i ∷ atomsₑ s))
           (≡̂ₑ-cong ≡̂ₑ-refl (≡̂ₑ-cong ≡̂ₑ-refl (atomsₑ-≡ s)))

toProdsₑ : ∀ {Θ} → Alts (List (EAtom Θ)) → Alts (Gₑ.Prod {Θ})
toProdsₑ = mapᴬ (slotsₑ nothing)

toProdsₑ-≡ : ∀ {Θ} → (s : Alts (List (EAtom Θ))) → Gₑ.⟦ toProdsₑ s ⟧ᵖ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺
toProdsₑ-≡ (alt P)  = ≡̂ₑ-trans (slotsₑ-≡ nothing P) ≡̂ₑ-identityˡ
toProdsₑ-≡ (P ∷⁺ s) =
  ≡̂ₑ-cong-⊔ (≡̂ₑ-trans (slotsₑ-≡ nothing P) ≡̂ₑ-identityˡ) (toProdsₑ-≡ s)

fromProdsₑ : ∀ {Θ} → Alts (Gₑ.Prod {Θ}) → Alts (List (EAtom Θ))
fromProdsₑ = mapᴬ (λ P → atomsₑ (proj₂ P))

fromProdsₑ-≡ : ∀ {Θ} → (ps : Alts (Gₑ.Prod {Θ})) → ⟦ fromProdsₑ ps ⟧ᵉˢ⁺ ≡̂ₑ Gₑ.⟦ ps ⟧ᵖ⁺
fromProdsₑ-≡ (alt P)   = atomsₑ-≡ (proj₂ P)
fromProdsₑ-≡ (P ∷⁺ ps) = ≡̂ₑ-cong-⊔ (atomsₑ-≡ (proj₂ P)) (fromProdsₑ-≡ ps)

-- The variable atoms of a resource product: resource variables, then
-- images of effect variables, each ordered by index

data RVAtom (Θ : Scope) : Set where
  vr : RVar Θ → RVAtom Θ
  vm : EVar Θ → RVAtom Θ

varAtomᵣ : ∀ {Θ} → RVAtom Θ → RAtom Θ
varAtomᵣ (vr i) = rv i
varAtomᵣ (vm i) = rm i

⟦_⟧ʳᵛ : ∀ {Θ} → RVAtom Θ → RExp Θ
⟦ a ⟧ʳᵛ = ⟦ varAtomᵣ a ⟧ʳᵃ

_≟ʳᵛ_ : ∀ {Θ} → DecidableEquality (RVAtom Θ)
vr i ≟ʳᵛ vr j with i ≟ᶠ j
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
vr i ≟ʳᵛ vm j = no λ ()
vm i ≟ʳᵛ vr j = no λ ()
vm i ≟ʳᵛ vm j with i ≟ᶠ j
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }

_<ʳᵛ_ : ∀ {Θ} → RVAtom Θ → RVAtom Θ → 𝔹
vr i <ʳᵛ vr j = toℕ i <ᵇ toℕ j
vr _ <ʳᵛ vm _ = true
vm _ <ʳᵛ vr _ = false
vm i <ʳᵛ vm j = toℕ i <ᵇ toℕ j

module Gᵣ {Θ : Scope} =
  Grouping {RExp Θ} {R} {RVAtom Θ} _≡̂ᵣ_ ≡̂ᵣ-refl ≡̂ᵣ-sym ≡̂ᵣ-trans _·̂ᵣ_ _⊔̂ᵣ_
           ≡̂ᵣ-cong ≡̂ᵣ-cong-⊔ ≡̂ᵣ-idem-⊔ ≡̂ᵣ-comm-⊔ ≡̂ᵣ-assoc-⊔
           ≡̂ᵣ-distribˡ-⊔ ≡̂ᵣ-distribʳ-⊔
           rconst _⊔ᵣ_ ≡̂ᵣ-const-⊔ sameConstᵣ? ⟦_⟧ʳᵛ _≟ʳᵛ_ _<ʳᵛ_

⌊_⌋ᵣ : Maybe R → R
⌊ nothing ⌋ᵣ = uᵣ
⌊ just c ⌋ᵣ  = c

_·ᵐᵣ_ : Maybe R → R → R
nothing ·ᵐᵣ c = c
just b  ·ᵐᵣ c = b ·ᵣ c

slotsᵣ : ∀ {Θ} → Maybe R → List (RAtom Θ) → Gᵣ.Prod {Θ}
slotsᵣ m        []           = [] , Gᵣ.⌜ ⌊ m ⌋ᵣ ⌝
slotsᵣ m        (rc c ∷ as) = slotsᵣ (just (m ·ᵐᵣ c)) as
slotsᵣ m        (rv i ∷ as) = vr i ∷ proj₁ P , (⌊ m ⌋ᵣ Gᵣ.▸ proj₂ P)
  where P = slotsᵣ nothing as
slotsᵣ m        (rm i ∷ as) = vm i ∷ proj₁ P , (⌊ m ⌋ᵣ Gᵣ.▸ proj₂ P)
  where P = slotsᵣ nothing as

slotsᵣ-≡ : ∀ {Θ} → (m : Maybe R) → (as : List (RAtom Θ))
         → Gᵣ.⟦ slotsᵣ m as ⟧ᵖ ≡̂ᵣ rconst ⌊ m ⌋ᵣ ·̂ᵣ ⟦ as ⟧ʳˢ
slotsᵣ-≡ m        []           = ≡̂ᵣ-sym ≡̂ᵣ-identityʳ
slotsᵣ-≡ nothing  (rc c ∷ as) = ≡̂ᵣ-trans (slotsᵣ-≡ (just c) as) (≡̂ᵣ-sym ≡̂ᵣ-identityˡ)
slotsᵣ-≡ (just b) (rc c ∷ as) =
  ≡̂ᵣ-trans (slotsᵣ-≡ (just (b ·ᵣ c)) as)
  (≡̂ᵣ-trans (≡̂ᵣ-cong (≡̂ᵣ-sym ≡̂ᵣ-const-·) ≡̂ᵣ-refl) ≡̂ᵣ-assoc)
slotsᵣ-≡ m        (rv i ∷ as) =
  ≡̂ᵣ-cong ≡̂ᵣ-refl (≡̂ᵣ-cong ≡̂ᵣ-refl (≡̂ᵣ-trans (slotsᵣ-≡ nothing as) ≡̂ᵣ-identityˡ))
slotsᵣ-≡ m        (rm i ∷ as) =
  ≡̂ᵣ-cong ≡̂ᵣ-refl (≡̂ᵣ-cong ≡̂ᵣ-refl (≡̂ᵣ-trans (slotsᵣ-≡ nothing as) ≡̂ᵣ-identityˡ))

atomsᵣ : ∀ {Θ vs} → Gᵣ.Slots {Θ} vs → List (RAtom Θ)
atomsᵣ Gᵣ.⌜ c ⌝            = consᵣ (rc c) []
atomsᵣ (Gᵣ._▸_ {a} c s) = consᵣ (rc c) (varAtomᵣ a ∷ atomsᵣ s)

atomsᵣ-≡ : ∀ {Θ vs} → (s : Gᵣ.Slots {Θ} vs) → ⟦ atomsᵣ s ⟧ʳˢ ≡̂ᵣ Gᵣ.⟦ s ⟧ᵏ
atomsᵣ-≡ Gᵣ.⌜ c ⌝            = ≡̂ᵣ-trans (consᵣ-≡ (rc c) []) ≡̂ᵣ-identityʳ
atomsᵣ-≡ (Gᵣ._▸_ {a} c s) =
  ≡̂ᵣ-trans (consᵣ-≡ (rc c) (varAtomᵣ a ∷ atomsᵣ s))
           (≡̂ᵣ-cong ≡̂ᵣ-refl (≡̂ᵣ-cong ≡̂ᵣ-refl (atomsᵣ-≡ s)))

toProdsᵣ : ∀ {Θ} → Alts (List (RAtom Θ)) → Alts (Gᵣ.Prod {Θ})
toProdsᵣ = mapᴬ (slotsᵣ nothing)

toProdsᵣ-≡ : ∀ {Θ} → (s : Alts (List (RAtom Θ))) → Gᵣ.⟦ toProdsᵣ s ⟧ᵖ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺
toProdsᵣ-≡ (alt P)  = ≡̂ᵣ-trans (slotsᵣ-≡ nothing P) ≡̂ᵣ-identityˡ
toProdsᵣ-≡ (P ∷⁺ s) =
  ≡̂ᵣ-cong-⊔ (≡̂ᵣ-trans (slotsᵣ-≡ nothing P) ≡̂ᵣ-identityˡ) (toProdsᵣ-≡ s)

fromProdsᵣ : ∀ {Θ} → Alts (Gᵣ.Prod {Θ}) → Alts (List (RAtom Θ))
fromProdsᵣ = mapᴬ (λ P → atomsᵣ (proj₂ P))

fromProdsᵣ-≡ : ∀ {Θ} → (ps : Alts (Gᵣ.Prod {Θ})) → ⟦ fromProdsᵣ ps ⟧ʳˢ⁺ ≡̂ᵣ Gᵣ.⟦ ps ⟧ᵖ⁺
fromProdsᵣ-≡ (alt P)   = atomsᵣ-≡ (proj₂ P)
fromProdsᵣ-≡ (P ∷⁺ ps) = ≡̂ᵣ-cong-⊔ (atomsᵣ-≡ (proj₂ P)) (fromProdsᵣ-≡ ps)

-- A sum grouped by skeleton, each group that varies in one slot folded
-- into one alternative; no alternative is dropped

foldSumₑ : ∀ {Θ} → Alts (List (EAtom Θ)) → Alts (List (EAtom Θ))
foldSumₑ s = fromProdsₑ (Gₑ.canonical (toProdsₑ s))

foldSumₑ-≡ : ∀ {Θ} → (s : Alts (List (EAtom Θ))) → ⟦ foldSumₑ s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺
foldSumₑ-≡ s =
  ≡̂ₑ-trans (fromProdsₑ-≡ (Gₑ.canonical (toProdsₑ s)))
  (≡̂ₑ-trans (Gₑ.canonical-≈ (toProdsₑ s)) (toProdsₑ-≡ s))

foldSumᵣ : ∀ {Θ} → Alts (List (RAtom Θ)) → Alts (List (RAtom Θ))
foldSumᵣ s = fromProdsᵣ (Gᵣ.canonical (toProdsᵣ s))

foldSumᵣ-≡ : ∀ {Θ} → (s : Alts (List (RAtom Θ))) → ⟦ foldSumᵣ s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺
foldSumᵣ-≡ s =
  ≡̂ᵣ-trans (fromProdsᵣ-≡ (Gᵣ.canonical (toProdsᵣ s)))
  (≡̂ᵣ-trans (Gᵣ.canonical-≈ (toProdsᵣ s)) (toProdsᵣ-≡ s))

------------------------------------------------------------------
-- The skeletons of an expression's alternatives, read off its
-- syntax, and the order of grade orderings by the skeletons of their
-- two sides. On a canonical expression they are the skeletons of its
-- groups, in order.

varsₑ : ∀ {Θ} → EExp Θ → List (EVar Θ)
varsₑ (evar i)   = i ∷ []
varsₑ (econst _) = []
varsₑ (ε ·̂ₑ ε')  = varsₑ ε ++ varsₑ ε'
varsₑ (ε ⊔̂ₑ ε')  = varsₑ ε ++ varsₑ ε'

skeletonsₑ : ∀ {Θ} → EExp Θ → List (List (EVar Θ))
skeletonsₑ (ε ⊔̂ₑ ε') = skeletonsₑ ε ++ skeletonsₑ ε'
skeletonsₑ (evar i)   = (i ∷ []) ∷ []
skeletonsₑ (econst c) = [] ∷ []
skeletonsₑ (ε ·̂ₑ ε')  = varsₑ (ε ·̂ₑ ε') ∷ []

varsᵣ : ∀ {Θ} → RExp Θ → List (RVAtom Θ)
varsᵣ (rvar i)   = vr i ∷ []
varsᵣ (rconst _) = []
varsᵣ (ρ ·̂ᵣ ρ')  = varsᵣ ρ ++ varsᵣ ρ'
varsᵣ (ρ ⊔̂ᵣ ρ')  = varsᵣ ρ ++ varsᵣ ρ'
varsᵣ ∣ ε ∣̂ᵉ     = map vm (varsₑ ε)

skeletonsᵣ : ∀ {Θ} → RExp Θ → List (List (RVAtom Θ))
skeletonsᵣ (ρ ⊔̂ᵣ ρ') = skeletonsᵣ ρ ++ skeletonsᵣ ρ'
skeletonsᵣ (rvar i)   = (vr i ∷ []) ∷ []
skeletonsᵣ (rconst c) = [] ∷ []
skeletonsᵣ (ρ ·̂ᵣ ρ')  = varsᵣ (ρ ·̂ᵣ ρ') ∷ []
skeletonsᵣ ∣ ε ∣̂ᵉ     = varsᵣ ∣ ε ∣̂ᵉ ∷ []

infix 4 _≺ₑ_ _≺ᵣ_

_≺ₑ_ : ∀ {Θ} → EExp Θ × EExp Θ → EExp Θ × EExp Θ → 𝔹
_≺ₑ_ {Θ} (ε₁ , ε₁') (ε₂ , ε₂') =
  lex (≡-decᴸ (≡-decᴸ _≟ᶠ_)) (lex (≡-decᴸ _≟ᶠ_) (Gₑ._<ˢ_ {Θ}))
      (skeletonsₑ ε₁ ∷ skeletonsₑ ε₁' ∷ []) (skeletonsₑ ε₂ ∷ skeletonsₑ ε₂' ∷ [])

_≺ᵣ_ : ∀ {Θ} → RExp Θ × RExp Θ → RExp Θ × RExp Θ → 𝔹
(ρ₁ , ρ₁') ≺ᵣ (ρ₂ , ρ₂') =
  lex (≡-decᴸ (≡-decᴸ _≟ʳᵛ_)) (lex (≡-decᴸ _≟ʳᵛ_) Gᵣ._<ˢ_)
      (skeletonsᵣ ρ₁ ∷ skeletonsᵣ ρ₁' ∷ []) (skeletonsᵣ ρ₂ ∷ skeletonsᵣ ρ₂' ∷ [])
