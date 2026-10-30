--------------------------------------------------------------------
-- The engine of entailment: normal forms, chains, embedding      --
--                                                                --
-- Both sides of an ordering are put in the sum-of-products       --
-- normal form of `SolverImpl.Product`. Two products are compared --
-- by `_⊑ᵖ_`: the left embeds into the right in order, a missing  --
-- position being the unit, an atom matched against nothing on    --
-- the right when the unit is below it and on the left when it is --
-- below the unit, and an atom above the top on the right         --
-- standing for any run of atoms on the left. Where the hints     --
-- declare `_·_` commutative, products compare as multisets:      --
-- some permutation of the left embeds in order into the right.   --
--                                                                --
-- `Chains` is the reachability table along a list of edges       --
-- between atoms, and `Embedding` the comparison of products with --
-- its atom comparisons as parameters. `SolverImpl.Entail`        --
-- instantiates both at the edges of a hypothesis graph.          --
--                                                                --
-- Contract. `_⊑ᵖ?_` decides `_⊑ᵖ_` (`steps-complete`,            --
-- `step-shrinks`), `prodˢ≾` returns a reading exactly when       --
-- `_⊑ᵖ_` holds (`prodˢ≾-complete`, `prodˢ≾-exact`), and          --
-- `⊑ᵖ-sound` reads a derivation into any relation closed under   --
-- the steps. A table entry is a composite of the edges' proofs   --
-- (`reach?`). What the search does not find is listed under      --
-- Products below.                                                --
--------------------------------------------------------------------


open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant using () renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_; length; map; deduplicate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using (length-removeAt′)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?; index; _─_)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; map⁺)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_; Is-just)
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
open import Relation.Binary.Definitions using (Decidable)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.SolverImpl.Normal
  (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S))
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import PolymorphicCalculus.Syntax.Grades S
open import PolymorphicCalculus.Hypotheses    S

open import PolymorphicCalculus.Inference.SolverImpl.Product S hints public

------------------------------------------------------------------
-- Chains between atoms
--
-- Two atoms are linked by `link?`. `a` reaches `b` along a chain of
-- edges when `a` is linked to the first source, each target to the
-- next source, and the last target to `b`; `a` reaches `b` when they
-- are linked, or `a` is linked to a source that reaches `b`.
--
-- The table holds one entry per source `c`, sources the same by `_≟_`
-- counted once, in order of first occurrence among the edges: the
-- atoms `d` that `c` reaches, each with the derivation of `c ⊑ d`
-- composed along its chain. An entry is saturated by at most one
-- round per edge, stopping at the first round that reaches nothing
-- new. An entry depends on its source alone, and `reach?` answers
-- with the first entry that answers, so a repeated entry could not
-- change an answer.

module Chains {A : Set} (_⊑_ : A → A → Set)
              (refl⊑  : ∀ {a} → a ⊑ a)
              (trans⊑ : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c)
              (link?  : (a b : A) → Maybe (a ⊑ b))
              {_≅_    : A → A → Set} (_≟_ : Decidable _≅_)
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

  -- each distinct source with what it reaches

  Table : Set
  Table = List (Σ[ c ∈ A ] List (Σ[ d ∈ A ] c ⊑ d))

  sources : List A
  sources = deduplicate _≟_ (map (λ { (c , _ , _) → c }) edges)

  table : Table
  table = map (λ c → c , sat (length edges) ((c , refl⊑) ∷ [])) sources

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

-- The image of an effect atom

∣_∣ᵃ : ∀ {Θ} → EAtom Θ → RAtom Θ
∣ ac c ∣ᵃ = rc (mapᵉ c)
∣ av i ∣ᵃ = rm i

∣⟦_⟧∣ : ∀ {Θ} → (a : EAtom Θ) → ∣ ⟦ a ⟧ᵉᵃ ∣̂ᵉ ≡̂ᵣ ⟦ ∣ a ∣ᵃ ⟧ʳᵃ
∣⟦ ac c ⟧∣ = ≡̂ᵣ-map-const
∣⟦ av i ⟧∣ = ≡̂ᵣ-refl


------------------------------------------------------------------
-- Consing a constant adds at most one atom

consₑ-length : ∀ {Θ} → (c : E) → (as : List (EAtom Θ))
             → length (consₑ (ac c) as) ≤ suc (length as)
consₑ-length c (ac d ∷ as) = m≤n⇒m≤1+n (consₑ-length (c ·ₑ d) as)
consₑ-length c [] with c ≃ₑ? uₑ
... | yes _ = z≤n
... | no _  = ≤-refl
consₑ-length c (av i ∷ as) with c ≃ₑ? uₑ
... | yes _ = n≤1+n _
... | no _  = ≤-refl

consᵣ-length : ∀ {Θ} → (c : R) → (as : List (RAtom Θ))
             → length (consᵣ (rc c) as) ≤ suc (length as)
consᵣ-length c (rc d ∷ as) = m≤n⇒m≤1+n (consᵣ-length (c ·ᵣ d) as)
consᵣ-length c [] with c ≃ᵣ? uᵣ
... | yes _ = z≤n
... | no _  = ≤-refl
consᵣ-length c (rv i ∷ as) with c ≃ᵣ? uᵣ
... | yes _ = n≤1+n _
... | no _  = ≤-refl
consᵣ-length c (rm i ∷ as) with c ≃ᵣ? uᵣ
... | yes _ = n≤1+n _
... | no _  = ≤-refl

is-just? : ∀ {X : Set} → (m : Maybe X) → Dec (Is-just m)
is-just? (just _) = yes (Any-just tt)
is-just? nothing  = no λ ()

-- Every position at which a decided predicate holds; each position
-- is listed up to what removing its element leaves

anys : ∀ {A : Set} {P : A → Set} → (∀ x → Dec (P x)) → (xs : List A) → List (Any P xs)
anys P? []       = []
anys P? (x ∷ xs) with P? x
... | yes px = here px ∷ map there (anys P? xs)
... | no _   = map there (anys P? xs)

anys-complete : ∀ {A : Set} {P : A → Set} (P? : ∀ x → Dec (P x)) {xs : List A}
              → (p : Any P xs) → Any (λ p' → (xs ─ p') ≡ (xs ─ p)) (anys P? xs)
anys-complete P? {x ∷ xs} (here px) with P? x
... | yes _  = here refl
... | no ¬px = ⊥-elim (¬px px)
anys-complete P? {x ∷ xs} (there p) with P? x
... | yes _ = there (map⁺ (Any.map (cong (x ∷_)) (anys-complete P? p)))
... | no _  = map⁺ (Any.map (cong (x ∷_)) (anys-complete P? p))

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
--   * `mergeˡ`: the same on the left, the atom being below the unit;
--
-- and, where `_·_` commutes (`Comm`, decided):
--
--   * `pick`: the left head and a right atom at any position, the
--     left below the right;
--   * `absorbAt`: the left head, into a right atom at any position
--     that the top is below, which stays.
--
-- So the left side embeds into the right in order: each left atom
-- matched, absorbed or below the unit, each right atom matched,
-- absorbing a run, or above the unit, constants on either side of an
-- atom passed over multiplied. Where `_·_` commutes, products compare
-- as multisets: some permutation of the left embeds in order into the
-- right. The atom comparisons (`_≤ᵃ_`, `u≤_`, `_≤u`, `⊤≤_`) are
-- parameters, decided.
--
-- `_⊑ᵖ?_` decides `_⊑ᵖ_` by depth-first search over the steps out of
-- a pair (`steps`, listing every step, `steps-complete`), on the
-- total length, which each step shortens (`step-shrinks`). Within
-- `Sound`, `⊑ᵖ-sound` reads a derivation into any relation closed
-- under the steps, and `prodˢ≾` returns such a reading exactly when
-- `_⊑ᵖ_` holds (`prodˢ≾-complete`, `prodˢ≾-exact`). `steps` lists
-- `pick` and `absorbAt` past the right head only, at the positions
-- `anys` finds; at the head they reach what `match` and `absorb` do.
-- The search is backtracking bipartite matching, exponential in the
-- length of a product.
--
-- Not found: a left alternative below the join of right alternatives only
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
  (Comm : Set)         (comm? : Dec Comm)
  where

  data Step : List A → List A → List A → List A → Set where
    match    : ∀ {a as b bs} → a ≤ᵃ b → Step (a ∷ as) (b ∷ bs) as bs
    skipʳ    : ∀ {as b bs} → u≤ b → Step as (b ∷ bs) as bs
    skipˡ    : ∀ {a as bs} → a ≤u → Step (a ∷ as) bs as bs
    absorb   : ∀ {a as b bs} → ⊤≤ b → Step (a ∷ as) (b ∷ bs) as (b ∷ bs)
    mergeʳ   : ∀ {as a b bs c} → const? a ≡ just c → u≤ b
             → Step as (a ∷ b ∷ bs) as (cons c bs)
    mergeˡ   : ∀ {a b as bs c} → const? a ≡ just c → b ≤u
             → Step (a ∷ b ∷ as) bs (cons c as) bs
    pick     : ∀ {a as bs} → Comm → (p : Any (a ≤ᵃ_) bs) → Step (a ∷ as) bs as (bs ─ p)
    absorbAt : ∀ {a as bs} → Comm → Any ⊤≤_ bs → Step (a ∷ as) bs as bs

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

  opts : ∀ {P : Set} {X : Set} → Dec P → (P → List X) → List X
  opts (yes p) f = f p
  opts (no _)  f = []

  opts-complete : ∀ {P X : Set} {R : X → Set} → (d : Dec P) → (f : P → List X)
                → P → (∀ p → Any R (f p)) → Any R (opts d f)
  opts-complete (yes p) f _ r = r p
  opts-complete (no ¬p) f p r = ⊥-elim (¬p p)

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

  -- `pick` and `absorbAt` past the right head, which `match` and
  -- `absorb` cover

  picks absorbsAt : ∀ as bs → List (Next as bs)

  picks (a ∷ as) (b ∷ bs) =
    opts comm? λ c → map (λ p → as , b ∷ (bs ─ p) , pick c (there p)) (anys (a ≤ᵃ?_) bs)
  picks _        _        = []

  absorbsAt (a ∷ as) (b ∷ bs) =
    opts comm? λ c → map (λ p → as , b ∷ bs , absorbAt c (there p)) (anys ⊤≤? bs)
  absorbsAt _        _        = []

  -- In the order the search tries them

  steps : ∀ as bs → List (Next as bs)
  steps as bs = matches as bs ++ skipsʳ as bs ++ skipsˡ as bs
             ++ absorbs as bs ++ mergesʳ as bs ++ mergesˡ as bs
             ++ picks as bs ++ absorbsAt as bs

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

  match-complete : ∀ {a as b bs} → a ≤ᵃ b → Any (Reaches as bs) (steps (a ∷ as) (b ∷ bs))
  match-complete {a} {as} {b} {bs} p =
    ++⁺ˡ (opt-complete (a ≤ᵃ? b) (λ p → as , bs , match p) p λ _ → refl)

  absorb-complete : ∀ {a as b bs} → ⊤≤ b → Any (Reaches as (b ∷ bs)) (steps (a ∷ as) (b ∷ bs))
  absorb-complete {a} {as} {b} {bs} p =
    ++⁺ʳ (matches (a ∷ as) (b ∷ bs)) (++⁺ʳ (skipsʳ (a ∷ as) (b ∷ bs))
      (++⁺ʳ (skipsˡ (a ∷ as) (b ∷ bs))
        (++⁺ˡ (opt-complete (⊤≤? b) (λ p → as , b ∷ bs , absorb p) p λ _ → refl))))

  -- The last two entries of `steps`
  tail⁺ : ∀ {as bs} {R : Next as bs → Set} → Any R (picks as bs ++ absorbsAt as bs)
        → Any R (steps as bs)
  tail⁺ {as} {bs} r =
    ++⁺ʳ (matches as bs) (++⁺ʳ (skipsʳ as bs) (++⁺ʳ (skipsˡ as bs)
      (++⁺ʳ (absorbs as bs) (++⁺ʳ (mergesʳ as bs) (++⁺ʳ (mergesˡ as bs) r)))))

  steps-complete : ∀ {as bs as' bs'} → Step as bs as' bs' → Any (Reaches as' bs') (steps as bs)
  steps-complete (match p) = match-complete p
  steps-complete {as} {b ∷ bs} (skipʳ p) =
    ++⁺ʳ (matches as (b ∷ bs))
      (++⁺ˡ (opt-complete (u≤? b) (λ p → as , bs , skipʳ p) p λ _ → refl))
  steps-complete {a ∷ as} {bs} (skipˡ p) =
    ++⁺ʳ (matches (a ∷ as) bs) (++⁺ʳ (skipsʳ (a ∷ as) bs)
      (++⁺ˡ (opt-complete (≤u? a) (λ p → as , bs , skipˡ p) p λ _ → refl)))
  steps-complete (absorb p) = absorb-complete p
  steps-complete {as} {a ∷ b ∷ bs} (mergeʳ e p) =
    ++⁺ʳ (matches as (a ∷ b ∷ bs)) (++⁺ʳ (skipsʳ as (a ∷ b ∷ bs))
      (++⁺ʳ (skipsˡ as (a ∷ b ∷ bs)) (++⁺ʳ (absorbs as (a ∷ b ∷ bs))
        (++⁺ˡ (mergeʳ-at-complete (const? a) refl e p)))))
  steps-complete {a ∷ b ∷ as} {bs} (mergeˡ e p) =
    ++⁺ʳ (matches (a ∷ b ∷ as) bs) (++⁺ʳ (skipsʳ (a ∷ b ∷ as) bs)
      (++⁺ʳ (skipsˡ (a ∷ b ∷ as) bs) (++⁺ʳ (absorbs (a ∷ b ∷ as) bs)
        (++⁺ʳ (mergesʳ (a ∷ b ∷ as) bs)
          (++⁺ˡ (mergeˡ-at-complete (const? a) refl e p))))))
  steps-complete (pick _ (here p)) = match-complete p
  steps-complete {a ∷ as} {b ∷ bs} (pick c (there p)) =
    tail⁺ (++⁺ˡ (opts-complete comm? _ c λ _ →
      map⁺ (Any.map (cong (λ l → as , b ∷ l)) (anys-complete (a ≤ᵃ?_) p))))
  steps-complete (absorbAt _ (here p)) = absorb-complete p
  steps-complete {a ∷ as} {b ∷ bs} (absorbAt c (there p)) =
    tail⁺ {R = Reaches as (b ∷ bs)} (++⁺ʳ (picks (a ∷ as) (b ∷ bs))
      (opts-complete comm? _ c λ _ → map⁺ (Any.map (λ _ → refl) (anys-complete ⊤≤? p))))

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
  step-shrinks {a ∷ as} {bs} (pick _ p) =
    subst (λ n → length as + length (bs ─ p) < suc (length as) + n)
          (sym (length-removeAt′ bs (index p)))
          (+-mono-< (n<1+n (length as)) (n<1+n (length (bs ─ p))))
  step-shrinks {a ∷ as} {bs} (absorbAt _ _) = +-monoˡ-< (length bs) (n<1+n (length as))

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
