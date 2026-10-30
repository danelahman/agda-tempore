--------------------------------------------------------------------
-- Reachability in a finite graph                                 --
--                                                                --
-- Over a list of vertices `vs` and a list of edges, the          --
-- reflexive-transitive closure by Warshall's algorithm. It holds --
-- an entry for each pair of vertices, starting from the edges    --
-- and the chains `same?` gives between vertices it identifies    --
-- (the diagonal); for each vertex `k` in turn, a pair joined     --
-- through `k`, the first to `k` and `k` to the second, gains an  --
-- entry. An entry is a chain of edges (`Star`). The              --
-- representative of a vertex in a given order is the first       --
-- vertex joined to it in both directions (`rep`).                --
--                                                                --
-- Cycle elimination (`Collapse`; Fähndrich, Foster, Su and       --
-- Aiken, PLDI 1998) pairs each vertex that may move with the     --
-- representative of its strongly connected component where that  --
-- is another vertex, the order being the preferred vertices,     --
-- then those neither preferred nor movable, then the movable     --
-- ones, each in the order of `vs`.                               --
--                                                                --
-- Contract. Sound by type: an entry for `a`, `b` is a chain of   --
-- edges from `a` to `b` (`reach`), a representative comes with a --
-- chain each way (`rep`), and so does each pair of a collapse    --
-- (`Ident`); along any relation each edge implies, a vertex and  --
-- its target are related both ways (`equal`). Completeness is    --
-- not proved.                                                    --
--------------------------------------------------------------------

open import Data.Bool.Base using (Bool; not; _∨_)
open import Data.List.Base using (List; []; _∷_; _++_; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing; _<∣>_; is-just)
import Data.Maybe.Base as Maybe
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_; fold)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no)

open import Util.Equality

module PolymorphicCalculus.Inference.SolverImpl.Reach
  {V : Set} (Edge : V → V → Set) (same? : (a b : V) → Maybe (Star Edge a b))
  (edges : List (Σ[ a ∈ V ] Σ[ b ∈ V ] Edge a b)) (vs : List V)
  where

Chain : V → V → Set
Chain = Star Edge

-- For each vertex, perhaps a chain to it

Row : V → Set
Row a = All (λ b → Maybe (Chain a b)) vs

Closure : Set
Closure = All Row vs

-- The chain `same?` gives on the diagonal, else an edge between
-- vertices it joins to the ends

start : (a b : V) → Maybe (Chain a b)
start a b with same? a b
... | just p  = just p
... | nothing = find edges
  where
    find : List (Σ[ c ∈ V ] Σ[ d ∈ V ] Edge c d) → Maybe (Chain a b)
    find []                = nothing
    find ((c , d , e) ∷ l) with same? a c | same? d b
    ... | just p | just q = just (p ◅◅ (e ◅ q))
    ... | _      | _      = find l

-- The pairs joined through `k` gain an entry

through : ∀ {k} → k ∈ vs → Closure → Closure
through {k} m C = via (All.lookup C m) C
  where
    via : Row k → Closure → Closure
    via rk = All.map (λ r → join (All.lookup r m) r)
      where
        join : ∀ {a} → Maybe (Chain a k) → Row a → Row a
        join nothing  r = r
        join (just p) r = All.zipWith (λ { (x , y) → x <∣> Maybe.map (p ◅◅_) y }) (r , rk)

closure : Closure
closure = pivots vs (λ m → m) (All.tabulate (λ {a} _ → All.tabulate (λ {b} _ → start a b)))
  where
    pivots : (l : List V) → (∀ {x} → x ∈ l → x ∈ vs) → Closure → Closure
    pivots []      f C = C
    pivots (k ∷ l) f C = pivots l (λ m → f (there m)) (through (f (here refl)) C)

reach : Closure → ∀ {a b} → a ∈ vs → b ∈ vs → Maybe (Chain a b)
reach C ma mb = All.lookup (All.lookup C ma) mb

-- The first vertex of `ord` joined to `a` in both directions

rep : Closure → List (Σ[ v ∈ V ] v ∈ vs) → ∀ {a} → a ∈ vs
    → Maybe (Σ[ r ∈ V ] Chain a r × Chain r a)
rep C []               ma = nothing
rep C ((v , mv) ∷ ord) ma with reach C ma mv | reach C mv ma
... | just p | just q = just (v , p , q)
... | _      | _      = rep C ord ma

------------------------------------------------------------------------
-- Cycle elimination over a policy: the preferred vertices, and those
-- that may move (`Mv`)

module Collapse (_≟_ : DecidableEquality V) (preferred : V → Bool) (Mv : V → Set) (mv? : (v : V) → Maybe (Mv v)) where

  -- A vertex that moves: its target, a chain each way, and its licence

  record Ident (k : V) : Set where
    constructor ident
    field
      to   : V
      up   : Chain k to
      down : Chain to k
      mv   : Mv k

  Moves : Set
  Moves = List (Σ[ k ∈ V ] Ident k)

  private
    members : List (Σ[ v ∈ V ] v ∈ vs)
    members = go vs (λ m → m)
      where
        go : (l : List V) → (∀ {x} → x ∈ l → x ∈ vs) → List (Σ[ v ∈ V ] v ∈ vs)
        go []      f = []
        go (v ∷ l) f = (v , f (here refl)) ∷ go l (λ m → f (there m))

    may : V → Bool
    may v = is-just (mv? v)

    order : List (Σ[ v ∈ V ] v ∈ vs)
    order = filterᵇ (λ p → preferred (proj₁ p)) members
         ++ filterᵇ (λ p → not (preferred (proj₁ p) ∨ may (proj₁ p))) members
         ++ filterᵇ (λ p → may (proj₁ p)) members

    add : ∀ {k} → Maybe (Mv k) → Maybe (Σ[ r ∈ V ] Chain k r × Chain r k) → Moves → Moves
    add {k} (just q) (just (r , p , p')) ms with k ≟ r
    ... | no _  = (k , ident r p p' q) ∷ ms
    ... | yes _ = ms
    add _ _ ms = ms

    over : Closure → List (Σ[ v ∈ V ] v ∈ vs) → Moves
    over C []             = []
    over C ((k , mk) ∷ l) = add (mv? k) (rep C order mk) (over C l)

  moves : Moves
  moves = over closure members

  identOf : Moves → (k : V) → Maybe (Ident k)
  identOf []              k = nothing
  identOf ((k' , i) ∷ ms) k with k ≟ k'
  ... | yes refl = just i
  ... | no _     = identOf ms k

  toOf : ∀ {k} → Maybe (Ident k) → V
  toOf {k} nothing  = k
  toOf     (just i) = Ident.to i

  target : Moves → V → V
  target ms k = toOf (identOf ms k)

  -- Each vertex stays, or may move

  stays : (ms : Moves) → (k : V) → (target ms k ≡ k) ⊎ Mv k
  stays ms k = go (identOf ms k)
    where
      go : (x : Maybe (Ident k)) → (toOf x ≡ k) ⊎ Mv k
      go nothing  = inj₁ refl
      go (just i) = inj₂ (Ident.mv i)

  -- The members of a component are equal: along any relation each edge
  -- implies, a vertex and its target are related both ways (for
  -- orderings, equal at every instance by antisymmetry)

  equal : (P : V → V → Set) → (∀ {a} → P a a) → (∀ {a b c} → Edge a b → P b c → P a c)
        → (ms : Moves) → (k : V) → P (target ms k) k × P k (target ms k)
  equal P r t ms k = go (identOf ms k)
    where
      go : (x : Maybe (Ident k)) → P (toOf x) k × P k (toOf x)
      go nothing  = r , r
      go (just i) = fold P t r (Ident.down i) , fold P t r (Ident.up i)
