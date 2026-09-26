--------------------------------------------------------------------
-- Reachability in a finite graph                                 --
--                                                                --
-- Over a list of vertices `vs` and a list of edges, the          --
-- reflexive-transitive closure by Warshall's algorithm. It holds --
-- an entry for each pair of vertices, starting from the edges    --
-- and the diagonal; for each vertex `k` in turn, a pair joined   --
-- through `k`, the first to `k` and `k` to the second, gains an  --
-- entry. An entry is a chain of edges (`Star`).                  --
--                                                                --
-- A vertex lies on a cycle when the closure joins another vertex --
-- to it in both directions (`onCycle`); its representative is    --
-- the first vertex of a given order so joined to it (`rep`).     --
--                                                                --
-- Contract. Sound by type: an entry for `a`, `b` is a chain of   --
-- edges from `a` to `b` (`reach`), and a representative comes    --
-- with a chain each way (`rep`). Completeness is not proved.     --
--------------------------------------------------------------------

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing; _<∣>_)
import Data.Maybe.Base as Maybe
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no)

open import Util.Equality

module TypeInference.SolverImpl.Reach
  {V : Set} (_≟_ : DecidableEquality V) (Edge : V → V → Set)
  (edges : List (Σ[ a ∈ V ] Σ[ b ∈ V ] Edge a b)) (vs : List V)
  where

Chain : V → V → Set
Chain = Star Edge

-- For each vertex, perhaps a chain to it

Row : V → Set
Row a = All (λ b → Maybe (Chain a b)) vs

Closure : Set
Closure = All Row vs

-- The empty chain on the diagonal, else an edge

start : (a b : V) → Maybe (Chain a b)
start a b with a ≟ b
... | yes refl = just ε
... | no _     = find edges
  where
    find : List (Σ[ c ∈ V ] Σ[ d ∈ V ] Edge c d) → Maybe (Chain a b)
    find []                = nothing
    find ((c , d , e) ∷ l) with c ≟ a | d ≟ b
    ... | yes refl | yes refl = just (e ◅ ε)
    ... | _        | _        = find l

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

-- Whether `a` lies on a cycle: another vertex is joined to it in both
-- directions

onCycle : Closure → ∀ {a} → a ∈ vs → Bool
onCycle C {a} ma = go vs (λ m → m)
  where
    go : (l : List V) → (∀ {x} → x ∈ l → x ∈ vs) → Bool
    go []      f = false
    go (v ∷ l) f with v ≟ a | reach C ma (f (here refl)) | reach C (f (here refl)) ma
    ... | no _ | just _ | just _ = true
    ... | _    | _      | _      = go l (λ m → f (there m))

-- The first vertex of `ord` joined to `a` in both directions

rep : Closure → List (Σ[ v ∈ V ] v ∈ vs) → ∀ {a} → a ∈ vs
    → Maybe (Σ[ r ∈ V ] Chain a r × Chain r a)
rep C []               ma = nothing
rep C ((v , mv) ∷ ord) ma with reach C ma mv | reach C mv ma
... | just p | just q = just (v , p , q)
... | _      | _      = rep C ord ma
