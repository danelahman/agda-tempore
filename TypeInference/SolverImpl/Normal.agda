------------------------------------------------------------------
-- Deciding an entailed ordering of open grade expressions        --
--                                                                --
-- Both sides are put in the sum-of-products normal form of       --
-- `SolverImpl.Product` and compared alternative by alternative,  --
-- the answer glued back with `eqᵣ`/`monoᵣ`/`transᵣ`. Two         --
-- alternatives are compared by `_⊑ᵖ_`: the left embeds into the  --
-- right in order, a missing position being the unit, an atom     --
-- matched against nothing on the right when the unit is below it --
-- and on the left when it is below the unit, and an atom above   --
-- the top on the right standing for any run of atoms on the      --
-- left. Where the grade declares `_·_` commutative, the normal   --
-- form has put the factors of every product in one order.        --
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
--                                                                --
-- Contract. `decide≾ᵣ ρ ρ'` and `decide≾ₑ` are sound by their    --
-- types: a `just` is a derivation of `Q ⊩ ρ ≾̂ᵣ ρ'`, built from   --
-- the laws. Products: `_⊑ᵖ?_` decides `_⊑ᵖ_` (`steps-complete`,  --
-- `step-shrinks`), `prodˢ≾` returns a proof exactly when `_⊑ᵖ_`  --
-- holds (`prodˢ≾-complete`, `prodˢ≾-exact`), and `_⊑ᵖ_` is sound --
-- for entailment (`⊑ᵖ-sound`, at `stepₑ`/`stepᵣ`). A `nothing`   --
-- claims nothing about entailment: no completeness is proved,    --
-- for any fragment, and the atom comparisons are sound only.     --
-- What the search does not find is listed under Products below.  --
------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant using () renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_; Is-just; to-witness)
open import Data.Maybe.Properties using (just-injective)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to Any-just)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≡ᵇ_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-pred; n≤1+n; m≤n⇒m≤1+n; n<1+n; +-mono-<; +-monoˡ-<; +-monoʳ-<)
open import Data.Bool.Base using (true; false)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (tt)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Normal
  (S : LanguageSpec)
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.SolverImpl.Product S public

-- The unit is below anything when the grade decides it least

min≾ₑ : ∀ {Θ} {Q : Hyps Θ} {ε : EExp Θ} → Maybe (Is-just uₑ-least?) → Maybe (Q ⊩ ûₑ ≾̂ₑ ε)
min≾ₑ (just ij) = just (minₑ ij)
min≾ₑ nothing   = nothing

min≾ᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → Maybe (Is-just uᵣ-least?) → Maybe (Q ⊩ ûᵣ ≾̂ᵣ ρ)
min≾ᵣ (just ij) = just (minᵣ ij)
min≾ᵣ nothing   = nothing

------------------------------------------------------------------
-- Atomic hypotheses
--
-- Two atoms are linked when they are equal, or are constants ordered
-- by the grade's own order. `a` reaches `b` along a chain of edges
-- when `a` is linked to the first source, each target to the next
-- source, and the last target to `b`. What the source of each edge
-- reaches is saturated at every call of `decide≾`, at most one round
-- per edge, stopping at the first round that reaches nothing new; `a`
-- reaches `b` when they are linked, or `a` is linked to a source that
-- reaches `b`.

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
  sat (suc n) s with grow edges s
  ... | s' with length s' ≡ᵇ length s
  ...   | true  = s'
  ...   | false = sat n s'

  -- each source with what it reaches

  Table : Set
  Table = List (Σ[ c ∈ A ] List (Σ[ d ∈ A ] c ⊑ d))

  table : Table
  table = map (λ { (c , _ , _) → c , sat (length edges) ((c , refl⊑) ∷ []) }) edges

  reach? : Table → (a b : A) → Maybe (a ⊑ b)
  reach? t a b = link? a b <∣> go t
    where
      go : Table → Maybe (a ⊑ b)
      go []             = nothing
      go ((c , s) ∷ t') with link? a c
      ... | nothing = go t'
      ... | just l with find s b
      ...   | just w  = just (trans⊑ l w)
      ...   | nothing = go t'

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

-- What the sources of the atomic hypotheses reach; on the resource
-- side along the resource ones and the images of the effect ones

tableₑ : ∀ {Θ} → (Q : Hyps Θ) → Chains.Table (λ a b → Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
                                              ⊩≾̂ₑ-refl transₑ linkₑ? (edgesₑ (ordₑ Q) (λ m → m))
tableₑ Q = Chains.table _ ⊩≾̂ₑ-refl transₑ linkₑ? (edgesₑ (ordₑ Q) (λ m → m))

redgesᵣ : ∀ {Θ} → (Q : Hyps Θ) → List (REdge Q)
redgesᵣ Q = edgesᵣ (ordᵣ Q) (λ m → m) ++ map mapEdge (edgesₑ (ordₑ Q) (λ m → m))

tableᵣ : ∀ {Θ} → (Q : Hyps Θ) → Chains.Table (λ a b → Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
                                              ⊩≾̂ᵣ-refl transᵣ linkᵣ? (redgesᵣ Q)
tableᵣ Q = Chains.table _ ⊩≾̂ᵣ-refl transᵣ linkᵣ? (redgesᵣ Q)

------------------------------------------------------------------
-- Consing a constant adds at most one atom

consₑ-length : ∀ {Θ} → (c : E) → (as : List (EAtom Θ))
             → length (consₑ (ac c) as) ≤ suc (length as)
consₑ-length c (ac d ∷ as) = m≤n⇒m≤1+n (consₑ-length (c ·ₑ d) as)
consₑ-length c [] with c ≡ₑ? uₑ
... | yes _ = z≤n
... | no _  = ≤-refl
consₑ-length c (av i ∷ as) with c ≡ₑ? uₑ
... | yes _ = n≤1+n _
... | no _  = ≤-refl

consᵣ-length : ∀ {Θ} → (c : R) → (as : List (RAtom Θ))
             → length (consᵣ (rc c) as) ≤ suc (length as)
consᵣ-length c (rc d ∷ as) = m≤n⇒m≤1+n (consᵣ-length (c ·ᵣ d) as)
consᵣ-length c [] with c ≡ᵣ? uᵣ
... | yes _ = z≤n
... | no _  = ≤-refl
consᵣ-length c (rv i ∷ as) with c ≡ᵣ? uᵣ
... | yes _ = n≤1+n _
... | no _  = ≤-refl
consᵣ-length c (rm i ∷ as) with c ≡ᵣ? uᵣ
... | yes _ = n≤1+n _
... | no _  = ≤-refl

is-just? : ∀ {X : Set} → (m : Maybe X) → Dec (Is-just m)
is-just? (just _) = yes (Any-just tt)
is-just? nothing  = no λ ()

------------------------------------------------------------------
-- Products
--
-- Two products are compared as sequences whose missing positions
-- are the unit, by `_⊑ᵖ_`: `as ⊑ᵖ bs` when steps lead from the pair
-- `(as , bs)` to `([] , [])`. A step consumes an atom from at least
-- one side:
--
--   * `match`: the two heads, the left below the right;
--   * `skipʳ`: the right head, the unit being below it;
--   * `skipˡ`: the left head, it being below the unit;
--   * `absorb`: the left head, into a right head that the top is
--     below, which stays to absorb more, as `a · ⊤ ≾ ⊤`;
--   * `mergeʳ`: the atom after a constant head on the right, the unit
--     being below it, the constant then consed onto what follows it
--     (`consₑ`/`consᵣ`, which multiply adjacent constants);
--   * `mergeˡ`: the same on the left, the atom being below the unit.
--
-- So the left side embeds into the right in order: each left atom
-- matched, absorbed or below the unit, each right atom matched,
-- absorbing a run, or above the unit, constants on either side of an
-- atom passed over multiplied. The atom comparisons (`_≤ᵃ_`, `u≤_`,
-- `_≤u`, `⊤≤_`) are parameters, decided.
--
-- `_⊑ᵖ?_` decides `_⊑ᵖ_` by depth-first search over the steps out of
-- a pair (`steps`, listing every step, `steps-complete`), on the
-- total length, which each step shortens (`step-shrinks`). Within
-- `Sound`, `⊑ᵖ-sound` reads a derivation into any relation closed
-- under the steps, and `prodˢ≾` returns such a reading exactly when
-- `_⊑ᵖ_` holds (`prodˢ≾-complete`, `prodˢ≾-exact`).
--
-- Where `_·_` commutes, the products of the normal form are sorted,
-- and embedding in order is embedding as multisets when atoms are
-- matched by identity. Atoms matched along a hypothesis across the
-- sort order are not found: with the variables in the order `a, b,
-- x, y`, `x ≾ b, y ≾ a ⊩ x · y ≾ a · b` is missed.
--
-- Nor is anything that needs a hypothesis other than an atomic one.
-- A left alternative below the join of right alternatives only
-- jointly is found when those alternatives form a group that the
-- fold makes one; not when they have different skeletons, or form a
-- group that varies in more than one slot.

module Embedding
  {A K : Set}
  (const? : A → Maybe K)
  (cons   : K → List A → List A)
  (cons-length : ∀ c as → length (cons c as) ≤ suc (length as))
  (_≤ᵃ_ : A → A → Set) (_≤ᵃ?_ : ∀ a b → Dec (a ≤ᵃ b))
  (u≤_  : A → Set)     (u≤?   : ∀ b → Dec (u≤ b))
  (_≤u  : A → Set)     (≤u?   : ∀ a → Dec (a ≤u))
  (⊤≤_  : A → Set)     (⊤≤?   : ∀ b → Dec (⊤≤ b))
  where

  data Step : List A → List A → List A → List A → Set where
    match  : ∀ {a as b bs} → a ≤ᵃ b → Step (a ∷ as) (b ∷ bs) as bs
    skipʳ  : ∀ {as b bs} → u≤ b → Step as (b ∷ bs) as bs
    skipˡ  : ∀ {a as bs} → a ≤u → Step (a ∷ as) bs as bs
    absorb : ∀ {a as b bs} → ⊤≤ b → Step (a ∷ as) (b ∷ bs) as (b ∷ bs)
    mergeʳ : ∀ {as a b bs c} → const? a ≡ just c → u≤ b
           → Step as (a ∷ b ∷ bs) as (cons c bs)
    mergeˡ : ∀ {a b as bs c} → const? a ≡ just c → b ≤u
           → Step (a ∷ b ∷ as) bs (cons c as) bs

  infix 4 _⊑ᵖ_ _⊑ᵖ?_

  data _⊑ᵖ_ : List A → List A → Set where
    done : [] ⊑ᵖ []
    step : ∀ {as bs as' bs'} → Step as bs as' bs' → as' ⊑ᵖ bs' → as ⊑ᵖ bs

  -- The steps out of a pair

  Next : List A → List A → Set
  Next as bs = Σ[ as' ∈ List A ] Σ[ bs' ∈ List A ] Step as bs as' bs'

  Reaches : ∀ {as bs} → List A → List A → Next as bs → Set
  Reaches as' bs' (cs , ds , _) = (cs , ds) ≡ (as' , bs')

  opt : ∀ {P : Set} {X : Set} → Dec P → (P → X) → List X
  opt (yes p) f = f p ∷ []
  opt (no _)  f = []

  opt-complete : ∀ {P X : Set} {R : X → Set} → (d : Dec P) → (f : P → X)
               → P → (∀ p → R (f p)) → Any R (opt d f)
  opt-complete (yes p) f _ r = here (r p)
  opt-complete (no ¬p) f p r = ⊥-elim (¬p p)

  matches skipsʳ skipsˡ absorbs mergesʳ mergesˡ : ∀ as bs → List (Next as bs)

  matches (a ∷ as) (b ∷ bs) = opt (a ≤ᵃ? b) λ p → as , bs , match p
  matches _        _        = []

  skipsʳ as (b ∷ bs) = opt (u≤? b) λ p → as , bs , skipʳ p
  skipsʳ as []       = []

  skipsˡ (a ∷ as) bs = opt (≤u? a) λ p → as , bs , skipˡ p
  skipsˡ []       bs = []

  absorbs (a ∷ as) (b ∷ bs) = opt (⊤≤? b) λ p → as , b ∷ bs , absorb p
  absorbs _        _        = []

  mergeʳ-at : ∀ as a b bs → (m : Maybe K) → const? a ≡ m → List (Next as (a ∷ b ∷ bs))
  mergeʳ-at as a b bs (just c) e = opt (u≤? b) λ p → as , cons c bs , mergeʳ e p
  mergeʳ-at as a b bs nothing  e = []

  mergesʳ as (a ∷ b ∷ bs) = mergeʳ-at as a b bs (const? a) refl
  mergesʳ as _            = []

  mergeˡ-at : ∀ a b as bs → (m : Maybe K) → const? a ≡ m → List (Next (a ∷ b ∷ as) bs)
  mergeˡ-at a b as bs (just c) e = opt (≤u? b) λ p → cons c as , bs , mergeˡ e p
  mergeˡ-at a b as bs nothing  e = []

  mergesˡ (a ∷ b ∷ as) bs = mergeˡ-at a b as bs (const? a) refl
  mergesˡ _            bs = []

  -- In the order the search tries them

  steps : ∀ as bs → List (Next as bs)
  steps as bs = matches as bs ++ skipsʳ as bs ++ skipsˡ as bs
             ++ absorbs as bs ++ mergesʳ as bs ++ mergesˡ as bs

  mergeʳ-at-complete : ∀ {as a b bs c} → (m : Maybe K) → (e : const? a ≡ m)
                     → const? a ≡ just c → u≤ b
                     → Any (Reaches as (cons c bs)) (mergeʳ-at as a b bs m e)
  mergeʳ-at-complete {as} {b = b} {bs} (just c') e e' p =
    opt-complete (u≤? b) (λ p → as , cons c' bs , mergeʳ e p) p
                 λ _ → cong (λ k → as , cons k bs) (just-injective (trans (sym e) e'))
  mergeʳ-at-complete nothing e e' p with trans (sym e) e'
  ... | ()

  mergeˡ-at-complete : ∀ {a b as bs c} → (m : Maybe K) → (e : const? a ≡ m)
                     → const? a ≡ just c → b ≤u
                     → Any (Reaches (cons c as) bs) (mergeˡ-at a b as bs m e)
  mergeˡ-at-complete {b = b} {as} {bs} (just c') e e' p =
    opt-complete (≤u? b) (λ p → cons c' as , bs , mergeˡ e p) p
                 λ _ → cong (λ k → cons k as , bs) (just-injective (trans (sym e) e'))
  mergeˡ-at-complete nothing e e' p with trans (sym e) e'
  ... | ()

  steps-complete : ∀ {as bs as' bs'} → Step as bs as' bs' → Any (Reaches as' bs') (steps as bs)
  steps-complete {a ∷ as} {b ∷ bs} (match p) =
    ++⁺ˡ (opt-complete (a ≤ᵃ? b) (λ p → as , bs , match p) p λ _ → refl)
  steps-complete {as} {b ∷ bs} (skipʳ p) =
    ++⁺ʳ (matches as (b ∷ bs))
      (++⁺ˡ (opt-complete (u≤? b) (λ p → as , bs , skipʳ p) p λ _ → refl))
  steps-complete {a ∷ as} {bs} (skipˡ p) =
    ++⁺ʳ (matches (a ∷ as) bs) (++⁺ʳ (skipsʳ (a ∷ as) bs)
      (++⁺ˡ (opt-complete (≤u? a) (λ p → as , bs , skipˡ p) p λ _ → refl)))
  steps-complete {a ∷ as} {b ∷ bs} (absorb p) =
    ++⁺ʳ (matches (a ∷ as) (b ∷ bs)) (++⁺ʳ (skipsʳ (a ∷ as) (b ∷ bs))
      (++⁺ʳ (skipsˡ (a ∷ as) (b ∷ bs))
        (++⁺ˡ (opt-complete (⊤≤? b) (λ p → as , b ∷ bs , absorb p) p λ _ → refl))))
  steps-complete {as} {a ∷ b ∷ bs} (mergeʳ e p) =
    ++⁺ʳ (matches as (a ∷ b ∷ bs)) (++⁺ʳ (skipsʳ as (a ∷ b ∷ bs))
      (++⁺ʳ (skipsˡ as (a ∷ b ∷ bs)) (++⁺ʳ (absorbs as (a ∷ b ∷ bs))
        (++⁺ˡ (mergeʳ-at-complete (const? a) refl e p)))))
  steps-complete {a ∷ b ∷ as} {bs} (mergeˡ e p) =
    ++⁺ʳ (matches (a ∷ b ∷ as) bs) (++⁺ʳ (skipsʳ (a ∷ b ∷ as) bs)
      (++⁺ʳ (skipsˡ (a ∷ b ∷ as) bs) (++⁺ʳ (absorbs (a ∷ b ∷ as) bs)
        (++⁺ʳ (mergesʳ (a ∷ b ∷ as) bs) (mergeˡ-at-complete (const? a) refl e p)))))

  -- Every step shortens the pair

  size : List A → List A → ℕ
  size as bs = length as + length bs

  step-shrinks : ∀ {as bs as' bs'} → Step as bs as' bs' → size as' bs' < size as bs
  step-shrinks {a ∷ as} {b ∷ bs} (match _) = +-mono-< (n<1+n (length as)) (n<1+n (length bs))
  step-shrinks {as} {b ∷ bs} (skipʳ _)     = +-monoʳ-< (length as) (n<1+n (length bs))
  step-shrinks {a ∷ as} {bs} (skipˡ _)     = +-monoˡ-< (length bs) (n<1+n (length as))
  step-shrinks {a ∷ as} {bs} (absorb _)    = +-monoˡ-< (length bs) (n<1+n (length as))
  step-shrinks {as} {_ ∷ _ ∷ bs} (mergeʳ {c = c} _ _) =
    +-monoʳ-< (length as) (s≤s (cons-length c bs))
  step-shrinks {_ ∷ _ ∷ as} {bs} (mergeˡ {c = c} _ _) =
    +-monoˡ-< (length bs) (s≤s (cons-length c as))

  -- The search, on fuel bounding the total length

  Onward : ∀ {as bs} → Next as bs → Set
  Onward (as' , bs' , _) = as' ⊑ᵖ bs'

  onward : ∀ {as bs} {ts : List (Next as bs)} → Any Onward ts → as ⊑ᵖ bs
  onward (here {x = _ , _ , s} d) = step s d
  onward (there a)                = onward a

  reached : ∀ {as bs as' bs'} → (t : Next as bs) → Reaches as' bs' t → as' ⊑ᵖ bs' → Onward t
  reached (_ , _ , _) refl d = d

  backward : ∀ {as bs as' bs'} → Step as bs as' bs' → as' ⊑ᵖ bs'
           → Any Onward (steps as bs)
  backward s d = Any.map (λ {t} r → reached t r d) (steps-complete s)

  suc≰0 : ∀ {n} → suc n ≤ 0 → ⊥
  suc≰0 ()

  search : (n : ℕ) → ∀ as bs → .(size as bs ≤ n) → Dec (as ⊑ᵖ bs)
  search-steps : (n : ℕ) → ∀ as bs → .(size as bs ≤ suc n)
               → Dec (Any Onward (steps as bs))

  search n       []       []       _ = yes done
  search zero    (_ ∷ _)  _        h = ⊥-elim-irr (suc≰0 h)
  search zero    []       (_ ∷ _)  h = ⊥-elim-irr (suc≰0 h)
  search (suc n) (a ∷ as) bs       h =
    map′ onward (λ { (step s d) → backward s d }) (search-steps n (a ∷ as) bs h)
  search (suc n) []       (b ∷ bs) h =
    map′ onward (λ { (step s d) → backward s d }) (search-steps n [] (b ∷ bs) h)

  search-steps n as bs h =
    any? (λ { (as' , bs' , s) → search n as' bs' (≤-pred (≤-trans (step-shrinks s) h)) })
         (steps as bs)

  _⊑ᵖ?_ : ∀ as bs → Dec (as ⊑ᵖ bs)
  as ⊑ᵖ? bs = search (size as bs) as bs ≤-refl

  -- Reading a derivation into a relation closed under the steps

  module Sound (_≼_ : List A → List A → Set) (done≼ : [] ≼ [])
               (step≼ : ∀ {as bs as' bs'} → Step as bs as' bs' → as' ≼ bs' → as ≼ bs)
               where

    ⊑ᵖ-sound : ∀ {as bs} → as ⊑ᵖ bs → as ≼ bs
    ⊑ᵖ-sound done       = done≼
    ⊑ᵖ-sound (step s d) = step≼ s (⊑ᵖ-sound d)

    prodˢ≾ : ∀ as bs → Maybe (as ≼ bs)
    prodˢ≾ as bs with as ⊑ᵖ? bs
    ... | yes d = just (⊑ᵖ-sound d)
    ... | no _  = nothing

    prodˢ≾-complete : ∀ {as bs} → as ⊑ᵖ bs → Is-just (prodˢ≾ as bs)
    prodˢ≾-complete {as} {bs} d with as ⊑ᵖ? bs
    ... | yes _ = Any-just tt
    ... | no ¬d = ⊥-elim (¬d d)

    prodˢ≾-exact : ∀ {as bs} → Is-just (prodˢ≾ as bs) → as ⊑ᵖ bs
    prodˢ≾-exact {as} {bs} j with as ⊑ᵖ? bs | j
    ... | yes d | _ = d
    ... | no _  | ()

module Searchₑ {Θ} {Q : Hyps Θ}
               (t : Chains.Table (λ a b → Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
                                 ⊩≾̂ₑ-refl transₑ linkₑ? (edgesₑ (ordₑ Q) (λ m → m))) where

  reachₑ? : (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
  reachₑ? = Chains.reach? _ ⊩≾̂ₑ-refl transₑ linkₑ? (edgesₑ (ordₑ Q) (λ m → m)) t

  -- Anything is below an atom that the top reaches

  ceilₑ : ∀ {ε : EExp Θ} → (b : EAtom Θ) → Maybe (Q ⊩ ε ≾̂ₑ ⟦ b ⟧ᵉᵃ)
  ceilₑ b with reachₑ? (ac ⊤ₑ) b
  ... | just p  = just (transₑ topₑ p)
  ... | nothing = nothing

  -- An atom below an atom: linked, below an atom above the top, or
  -- reached along the atomic hypotheses

  atom≾ₑ : (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
  atom≾ₑ a b = linkₑ? a b <∣> ceilₑ b <∣> reachₑ? a b

  -- The unit below an atom: when the grade's unit is least, or as the
  -- constant atom `uₑ`

  unit≾ₑ : (b : EAtom Θ) → Maybe (Q ⊩ ûₑ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
  unit≾ₑ b = min≾ₑ (Is-just? uₑ-least?) <∣> atom≾ₑ (ac uₑ) b

  -- An atom below the unit, as the constant atom `uₑ`

  ≾unitₑ : (a : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ûₑ)
  ≾unitₑ a = atom≾ₑ a (ac uₑ)

  -- The product comparison, its atom comparisons being these

  constᵉ? : EAtom Θ → Maybe E
  constᵉ? (ac c) = just c
  constᵉ? (av _) = nothing

  module Pₑ = Embedding constᵉ? (λ c → consₑ (ac c)) consₑ-length
                (λ a b → Is-just (atom≾ₑ a b)) (λ a b → is-just? (atom≾ₑ a b))
                (λ b → Is-just (unit≾ₑ b))     (λ b → is-just? (unit≾ₑ b))
                (λ a → Is-just (≾unitₑ a))     (λ a → is-just? (≾unitₑ a))
                (λ b → Is-just (reachₑ? (ac ⊤ₑ) b)) (λ b → is-just? (reachₑ? (ac ⊤ₑ) b))
  open Pₑ using (Step; match; skipʳ; skipˡ; absorb; mergeʳ; mergeˡ)

  -- Each step is an entailment; products are read back with a trailing
  -- unit (`⟦_⟧ᵉˢ`), so that each step is one use of `monoₑ`

  stepₑ : ∀ {as bs as' bs'} → Step as bs as' bs'
        → Q ⊩ ⟦ as' ⟧ᵉˢ ≾̂ₑ ⟦ bs' ⟧ᵉˢ → Q ⊩ ⟦ as ⟧ᵉˢ ≾̂ₑ ⟦ bs ⟧ᵉˢ
  stepₑ (match p)  q = monoₑ (to-witness p) q
  stepₑ (skipʳ p)  q = transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-identityˡ)) (monoₑ (to-witness p) q)
  stepₑ (skipˡ p)  q = transₑ (monoₑ (to-witness p) q) (eqₑ ≡̂ₑ-identityˡ)
  stepₑ (absorb p) q =
    transₑ (monoₑ ⊩≾̂ₑ-refl q)
           (transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-assoc)) (monoₑ (transₑ topₑ (to-witness p)) ⊩≾̂ₑ-refl))
  stepₑ (mergeʳ {a = ac c} {bs = bs} refl p) q =
    transₑ q (transₑ (eqₑ (≡̂ₑ-trans (consₑ-≡ (ac c) bs)
                                    (≡̂ₑ-cong ≡̂ₑ-refl (≡̂ₑ-sym ≡̂ₑ-identityˡ))))
                     (monoₑ ⊩≾̂ₑ-refl (monoₑ (to-witness p) ⊩≾̂ₑ-refl)))
  stepₑ (mergeˡ {a = ac c} {as = as} refl p) q =
    transₑ (monoₑ ⊩≾̂ₑ-refl (monoₑ (to-witness p) ⊩≾̂ₑ-refl))
           (transₑ (eqₑ (≡̂ₑ-trans (≡̂ₑ-cong ≡̂ₑ-refl ≡̂ₑ-identityˡ)
                                  (≡̂ₑ-sym (consₑ-≡ (ac c) as))))
                   q)
  stepₑ (mergeʳ {a = av _} () _) _
  stepₑ (mergeˡ {a = av _} () _) _

  open Pₑ.Sound (λ as bs → Q ⊩ ⟦ as ⟧ᵉˢ ≾̂ₑ ⟦ bs ⟧ᵉˢ) ⊩≾̂ₑ-refl stepₑ using (prodˢ≾)

  prod≾ₑ : (as bs : List (EAtom Θ))
         → Maybe (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ ⟦ bs ⟧ᵉᵖ)
  prod≾ₑ as bs with prodˢ≾ as bs
  ... | just p  = just (transₑ (eqₑ (≡̂ₑ-sym (⟦⟧ᵉᵖ-≡ as)))
                               (transₑ p (eqₑ (⟦⟧ᵉᵖ-≡ bs))))
  ... | nothing = nothing

  -- One alternative against a whole sum: some alternative of the sum
  -- bounds it, and the join is above that one

  altSum≾ₑ : (as : List (EAtom Θ))
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

  sum≾ₑ : (s t : Alts (List (EAtom Θ)))
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
decide≾ₑ {Q = Q} ε ε' with Searchₑ.sum≾ₑ (tableₑ Q) (nrmₑ ε) (foldSumₑ (nrmₑ ε'))
... | just p  = just (transₑ (eqₑ (nrmₑ-≡ᵖ ε)) (transₑ p (eqₑ (≡̂ₑ-sym (foldₑ-≡ᵖ ε')))))
... | nothing = nothing

------------------------------------------------------------------
-- Resource grades: the same, with a third kind of atom, the image
-- `∣ x ∣` of an effect variable, which is treated as a variable. The
-- unit is below it when either sort's unit is least, the latter
-- carried through the morphism by `map-mono`, as `∣ u ∣ = u`.

∣û∣ₑ : ∀ {Θ} → ûᵣ {Θ} ≡̂ᵣ ∣ ûₑ ∣̂ᵉ
∣û∣ₑ = ≡̂ᵣ-sym (≡̂ᵣ-trans ≡̂ᵣ-map-const
                        (subst (λ c → rconst (mapᵉ uₑ) ≡̂ᵣ rconst c) map-uᵉ ≡̂ᵣ-refl))

module Searchᵣ {Θ} {Q : Hyps Θ}
               (t : Chains.Table (λ a b → Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
                                 ⊩≾̂ᵣ-refl transᵣ linkᵣ? (redgesᵣ Q)) where

  reachᵣ? : (a b : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  reachᵣ? = Chains.reach? _ ⊩≾̂ᵣ-refl transᵣ linkᵣ? (redgesᵣ Q) t

  ceilᵣ : ∀ {ρ : RExp Θ} → (b : RAtom Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  ceilᵣ b with reachᵣ? (rc ⊤ᵣ) b
  ... | just p  = just (transᵣ topᵣ p)
  ... | nothing = nothing

  atom≾ᵣ : (a b : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  atom≾ᵣ a b = linkᵣ? a b <∣> ceilᵣ b <∣> reachᵣ? a b

  minᵐ : (b : RAtom Θ) → Maybe (Q ⊩ ûᵣ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  minᵐ (rm i) with min≾ₑ {ε = evar i} (Is-just? uₑ-least?)
  ... | just q  = just (transᵣ (eqᵣ ∣û∣ₑ) (map-mono q))
  ... | nothing = nothing
  minᵐ _ = nothing

  unit≾ᵣ : (b : RAtom Θ) → Maybe (Q ⊩ ûᵣ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  unit≾ᵣ b = min≾ᵣ (Is-just? uᵣ-least?) <∣> minᵐ b <∣> atom≾ᵣ (rc uᵣ) b

  ≾unitᵣ : (a : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ûᵣ)
  ≾unitᵣ a = atom≾ᵣ a (rc uᵣ)

  -- The product comparison, its atom comparisons being these

  constʳ? : RAtom Θ → Maybe R
  constʳ? (rc c) = just c
  constʳ? (rv _) = nothing
  constʳ? (rm _) = nothing

  module Pᵣ = Embedding constʳ? (λ c → consᵣ (rc c)) consᵣ-length
                (λ a b → Is-just (atom≾ᵣ a b)) (λ a b → is-just? (atom≾ᵣ a b))
                (λ b → Is-just (unit≾ᵣ b))     (λ b → is-just? (unit≾ᵣ b))
                (λ a → Is-just (≾unitᵣ a))     (λ a → is-just? (≾unitᵣ a))
                (λ b → Is-just (reachᵣ? (rc ⊤ᵣ) b)) (λ b → is-just? (reachᵣ? (rc ⊤ᵣ) b))
  open Pᵣ using (Step; match; skipʳ; skipˡ; absorb; mergeʳ; mergeˡ)

  -- Each step is an entailment; products are read back with a trailing
  -- unit (`⟦_⟧ʳˢ`), so that each step is one use of `monoᵣ`

  stepᵣ : ∀ {as bs as' bs'} → Step as bs as' bs'
        → Q ⊩ ⟦ as' ⟧ʳˢ ≾̂ᵣ ⟦ bs' ⟧ʳˢ → Q ⊩ ⟦ as ⟧ʳˢ ≾̂ᵣ ⟦ bs ⟧ʳˢ
  stepᵣ (match p)  q = monoᵣ (to-witness p) q
  stepᵣ (skipʳ p)  q = transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityˡ)) (monoᵣ (to-witness p) q)
  stepᵣ (skipˡ p)  q = transᵣ (monoᵣ (to-witness p) q) (eqᵣ ≡̂ᵣ-identityˡ)
  stepᵣ (absorb p) q =
    transᵣ (monoᵣ ⊩≾̂ᵣ-refl q)
           (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-assoc)) (monoᵣ (transᵣ topᵣ (to-witness p)) ⊩≾̂ᵣ-refl))
  stepᵣ (mergeʳ {a = rc c} {bs = bs} refl p) q =
    transᵣ q (transᵣ (eqᵣ (≡̂ᵣ-trans (consᵣ-≡ (rc c) bs)
                                    (≡̂ᵣ-cong ≡̂ᵣ-refl (≡̂ᵣ-sym ≡̂ᵣ-identityˡ))))
                     (monoᵣ ⊩≾̂ᵣ-refl (monoᵣ (to-witness p) ⊩≾̂ᵣ-refl)))
  stepᵣ (mergeˡ {a = rc c} {as = as} refl p) q =
    transᵣ (monoᵣ ⊩≾̂ᵣ-refl (monoᵣ (to-witness p) ⊩≾̂ᵣ-refl))
           (transᵣ (eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl ≡̂ᵣ-identityˡ)
                                  (≡̂ᵣ-sym (consᵣ-≡ (rc c) as))))
                   q)
  stepᵣ (mergeʳ {a = rv _} () _) _
  stepᵣ (mergeʳ {a = rm _} () _) _
  stepᵣ (mergeˡ {a = rv _} () _) _
  stepᵣ (mergeˡ {a = rm _} () _) _

  open Pᵣ.Sound (λ as bs → Q ⊩ ⟦ as ⟧ʳˢ ≾̂ᵣ ⟦ bs ⟧ʳˢ) ⊩≾̂ᵣ-refl stepᵣ using (prodˢ≾)

  prod≾ᵣ : (as bs : List (RAtom Θ))
         → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ bs ⟧ʳᵖ)
  prod≾ᵣ as bs with prodˢ≾ as bs
  ... | just p  = just (transᵣ (eqᵣ (≡̂ᵣ-sym (⟦⟧ʳᵖ-≡ as)))
                               (transᵣ p (eqᵣ (⟦⟧ʳᵖ-≡ bs))))
  ... | nothing = nothing

  altSum≾ᵣ : (as : List (RAtom Θ))
           → (t : Alts (List (RAtom Θ)))
           → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ t ⟧ʳᵖ⁺)
  altSum≾ᵣ as (alt P) = prod≾ᵣ as P
  altSum≾ᵣ as (P ∷⁺ t) with prod≾ᵣ as P
  ... | just p  = just (transᵣ p ⊔-ubˡᵣ)
  ... | nothing with altSum≾ᵣ as t
  ...   | just q  = just (transᵣ q ⊔-ubʳᵣ)
  ...   | nothing = nothing

  sum≾ᵣ : (s t : Alts (List (RAtom Θ)))
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
decide≾ᵣ {Q = Q} ρ ρ' with Searchᵣ.sum≾ᵣ (tableᵣ Q) (nrmᵣ ρ) (foldSumᵣ (nrmᵣ ρ'))
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
