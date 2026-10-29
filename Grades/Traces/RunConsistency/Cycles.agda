------------------------------------------------------------------------
-- Run consistency over graphs: a cycle of the guarantee never helps. --
--                                                                    --
-- The joint walk of `Traces.RunConsistency`, lifted to a graph of    --
-- guarantees `L` and a graph of allowances `U`: a state is a node of --
-- each, with the slack `k` and the budget `b`. The allowance moves   --
-- alone (`bank`, `skip`, `fill`); the guarantee moves alone          --
-- (`spend`, `pay`) or with the allowance (`match`). Every delay is   --
-- one exact value, read off an edge.                                 --
--                                                                    --
-- A pair is at least as good as another, `(k , b) ≤ᵖ (k′ , b′)`,     --
-- when `b ≤ b′` and `k + b ≤ k′ + b′`. Every move is monotone in it  --
-- (`monoᵁ`, `monoᴸ`), and the moves of the guarantee only lower it   --
-- or reset it to `(0 , 0)`. So the moves of a walk past a node of    --
-- `L` back to the same node can be replaced by the allowance's moves --
-- alone, a match becoming a skip, at a pair at least as good         --
-- (`dropᴸ`); and every walk is dominated, at the same pair of nodes, --
-- by one whose path through `L` repeats no node (`shorten`). A walk  --
-- with smaller delays of the guarantee and larger delays of the      --
-- allowance does no worse (`Extremal.dominated`).                    --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.RunConsistency.Cycles
  {D : Duration} (T : TimeDomain D) (Op : Set)
  (costˡᵒ costʰⁱ : Op → Duration.Carrier D) where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Monus T as M using (Carrier; 0ᴰ; compare; tri<; tri≈; tri>; <⇒≤)
open M.Notation

------------------------------------------------------------------------
-- Graphs

record Graph : Set₁ where
  field
    Node   : Set
    _≟_    : DecidableEquality Node
    start  : Node
    _─d[_]→_ : Node → Carrier → Node → Set   -- a delay
    _─o[_]→_ : Node → Op → Node → Set        -- an operation

------------------------------------------------------------------------
-- Arithmetic

private
  ≰⇒≥ : {d k : Carrier} → ¬ (d ≤ k) → k ≤ d
  ≰⇒≥ {d} {k} ¬le with compare k d
  ... | tri< lt = <⇒≤ lt
  ... | tri≈ eq = ≤-reflexive eq
  ... | tri> gt = ⊥-elim (¬le (<⇒≤ gt))
    where open import Data.Empty using (⊥-elim)

  top-up : (k b d : Carrier) → k ≤ d → b ∸ (d ∸ k) ≡ (k + b) ∸ d
  top-up k b d le =
    sym (trans (cong ((k + b) ∸_) (sym (m+[n∸m]≡n le)))
               (trans (sym (M.∸-+-assoc (k + b) k (d ∸ k)))
                      (cong (_∸ (d ∸ k)) (M.m+n∸m k b))))

  no-top-up : (b d k : Carrier) → d ≤ k → b ∸ (d ∸ k) ≡ b
  no-top-up b d k le = trans (cong (b ∸_) (M.∸-≤ le)) (M.∸-0 b)

  left-≤ : (k b d : Carrier) → b ∸ (d ∸ k) ≤ (k + b) ∸ d
  left-≤ k b d = case (d ≤? k)
    where
      case : Dec (d ≤ k) → b ∸ (d ∸ k) ≤ (k + b) ∸ d
      case (no ¬le) = ≤-reflexive (top-up k b d (≰⇒≥ ¬le))
      case (yes le) =
        subst (_≤ (k + b) ∸ d) (sym (no-top-up b d k le))
              (M.+-≤-∸ (≤-trans le (m≤m+n k b)) (+-monoˡ-≤ b le))

  left-sum : (k b d : Carrier) → (k ∸ d) + (b ∸ (d ∸ k)) ≡ (k + b) ∸ d
  left-sum k b d = case (d ≤? k)
    where
      case : Dec (d ≤ k) → (k ∸ d) + (b ∸ (d ∸ k)) ≡ (k + b) ∸ d
      case (yes le) = trans (cong ((k ∸ d) +_) (no-top-up b d k le)) (sym (M.+-∸-comm b le))
      case (no ¬le) =
        trans (cong₂ _+_ (M.∸-≤ (≰⇒≥ ¬le)) (top-up k b d (≰⇒≥ ¬le))) (+-identityˡ _)

  sum-+ : {k₁ b₁ k₂ b₂ : Carrier} (e : Carrier)
        → k₁ + b₁ ≤ k₂ + b₂ → k₁ + (b₁ + e) ≤ k₂ + (b₂ + e)
  sum-+ {k₁} {b₁} {k₂} {b₂} e le =
    subst₂ _≤_ (+-assoc k₁ b₁ e) (+-assoc k₂ b₂ e) (+-monoˡ-≤ e le)

  -- a move of the guarantee spending `d` is monotone in the pair

  spend-mono : ∀ {k₁ b₁ k₂ b₂} d → b₁ ≤ b₂ → k₁ + b₁ ≤ k₂ + b₂
             → b₁ ∸ (d ∸ k₁) ≤ b₂ ∸ (d ∸ k₂)
             × (k₁ ∸ d) + (b₁ ∸ (d ∸ k₁)) ≤ (k₂ ∸ d) + (b₂ ∸ (d ∸ k₂))
  spend-mono {k₁} {b₁} {k₂} {b₂} d hb hs = hb′ (d ≤? k₂) , hs′
    where
      all≤ : (k₁ + b₁) ∸ d ≤ (k₂ + b₂) ∸ d
      all≤ = M.∸-monoˡ-≤ d hs

      hs′ : (k₁ ∸ d) + (b₁ ∸ (d ∸ k₁)) ≤ (k₂ ∸ d) + (b₂ ∸ (d ∸ k₂))
      hs′ = subst₂ _≤_ (sym (left-sum k₁ b₁ d)) (sym (left-sum k₂ b₂ d)) all≤

      hb′ : Dec (d ≤ k₂) → b₁ ∸ (d ∸ k₁) ≤ b₂ ∸ (d ∸ k₂)
      hb′ (yes le′) = subst (b₁ ∸ (d ∸ k₁) ≤_) (sym (no-top-up b₂ d k₂ le′))
                            (≤-trans (M.∸-≤-self b₁ (d ∸ k₁)) hb)
      hb′ (no ¬le′) = subst (b₁ ∸ (d ∸ k₁) ≤_) (sym (top-up k₂ b₂ d (≰⇒≥ ¬le′)))
                            (≤-trans (left-≤ k₁ b₁ d) all≤)

  -- and antitone in what it spends

  spend-anti : ∀ k b {d d′} → d′ ≤ d
             → b ∸ (d ∸ k) ≤ b ∸ (d′ ∸ k)
             × (k ∸ d) + (b ∸ (d ∸ k)) ≤ (k ∸ d′) + (b ∸ (d′ ∸ k))
  spend-anti k b {d} {d′} le =
    M.∸-monoʳ-≤ b (M.∸-monoˡ-≤ k le) ,
    subst₂ _≤_ (sym (left-sum k b d)) (sym (left-sum k b d′)) (M.∸-monoʳ-≤ (k + b) le)

module _ (L U : Graph) where

  private
    module L = Graph L
    module U = Graph U
  open import Data.List.Membership.DecPropositional L._≟_ using (_∈?_)

  ----------------------------------------------------------------------
  -- States and moves

  record State : Set where
    constructor ⟨_,_,_,_⟩
    field
      nL : L.Node
      nU : U.Node
      k  : Carrier
      b  : Carrier

  open State public

  data Uᵐ : State → State → Set where
    bank : ∀ {n m m′ k b e} → m U.─d[ e ]→ m′
         → Uᵐ ⟨ n , m , k , b ⟩ ⟨ n , m′ , k , b + e ⟩
    skip : ∀ {n m m′ k b o} → m U.─o[ o ]→ m′
         → Uᵐ ⟨ n , m , k , b ⟩ ⟨ n , m′ , k , b ⟩
    fill : ∀ {n m m′ k b o} → m U.─o[ o ]→ m′
         → Uᵐ ⟨ n , m , k , b ⟩ ⟨ n , m′ , (k + b) + costˡᵒ o , 0ᴰ ⟩

  data Lᵐ : State → State → Set where
    spend : ∀ {n n′ m k b d} → n L.─d[ d ]→ n′ → d ≤ k + b
          → Lᵐ ⟨ n , m , k , b ⟩ ⟨ n′ , m , k ∸ d , b ∸ (d ∸ k) ⟩
    pay   : ∀ {n n′ m k b o} → n L.─o[ o ]→ n′ → costʰⁱ o ≤ b
          → Lᵐ ⟨ n , m , k , b ⟩ ⟨ n′ , m , 0ᴰ , b ∸ costʰⁱ o ⟩
    match : ∀ {n n′ m m′ k b o} → n L.─o[ o ]→ n′ → m U.─o[ o ]→ m′
          → Lᵐ ⟨ n , m , k , b ⟩ ⟨ n′ , m′ , 0ᴰ , 0ᴰ ⟩

  data Move (s t : State) : Set where
    uᵐ : Uᵐ s t → Move s t
    lᵐ : Lᵐ s t → Move s t

  -- walks, built at their ends

  infixl 5 _▸_ _++ʷ_

  data Walk (s : State) : State → Set where
    []  : Walk s s
    _▸_ : ∀ {t r} → Walk s t → Move t r → Walk s r

  _++ʷ_ : ∀ {s t r} → Walk s t → Walk t r → Walk s r
  w ++ʷ []      = w
  w ++ʷ (v ▸ μ) = (w ++ʷ v) ▸ μ

  -- the nodes of `L` a walk visits, the latest first

  path : ∀ {s t} → Walk s t → List L.Node
  path {s} []        = nL s ∷ []
  path (w ▸ uᵐ _)    = path w
  path (_▸_ {r = r} w (lᵐ _)) = nL r ∷ path w

  -- walks of the allowance alone

  data Walkᵁ (s : State) : State → Set where
    []  : Walkᵁ s s
    _▸_ : ∀ {t r} → Walkᵁ s t → Uᵐ t r → Walkᵁ s r

  embed : ∀ {s t} → Walkᵁ s t → Walk s t
  embed []      = []
  embed (w ▸ μ) = embed w ▸ uᵐ μ

  path-++ᵁ : ∀ {s t r} (w : Walk s t) (v : Walkᵁ t r) → path (w ++ʷ embed v) ≡ path w
  path-++ᵁ w []      = refl
  path-++ᵁ w (v ▸ μ) = path-++ᵁ w v

  ----------------------------------------------------------------------
  -- Pairs at least as good

  infix 4 _≤ᵖ_

  record _≤ᵖ_ (s t : State) : Set where
    constructor _,_
    field
      ≤-budget : b s ≤ b t
      ≤-total  : k s + b s ≤ k t + b t

  ≤ᵖ-trans : ∀ {s t r} → s ≤ᵖ t → t ≤ᵖ r → s ≤ᵖ r
  ≤ᵖ-trans (p , q) (p′ , q′) = ≤-trans p p′ , ≤-trans q q′

  private
    -- the pair left by a move of the guarantee is no better

    spend-≤ : ∀ {n m n′ m′} (k b d : Carrier) → ⟨ n , m , k ∸ d , b ∸ (d ∸ k) ⟩ ≤ᵖ ⟨ n′ , m′ , k , b ⟩
    spend-≤ k b d =
      M.∸-≤-self b (d ∸ k) ,
      ≤-trans (≤-reflexive (left-sum k b d)) (M.∸-≤-self (k + b) d)

    pay-≤ : ∀ {n m n′ m′} (k b c : Carrier) → ⟨ n , m , 0ᴰ , b ∸ c ⟩ ≤ᵖ ⟨ n′ , m′ , k , b ⟩
    pay-≤ k b c =
      M.∸-≤-self b c ,
      ≤-trans (≤-reflexive (+-identityˡ _)) (≤-trans (M.∸-≤-self b c) (m≤n+m b k))

    zero-≤ : ∀ {n m n′ m′} (k b : Carrier) → ⟨ n , m , 0ᴰ , 0ᴰ ⟩ ≤ᵖ ⟨ n′ , m′ , k , b ⟩
    zero-≤ k b = z≤n , subst (_≤ k + b) (sym (+-identityˡ 0ᴰ)) z≤n

  ----------------------------------------------------------------------
  -- Every move is monotone in the pair

  -- the allowance moves alike whatever the node of `L`

  monoᵁ : ∀ {s r} → Uᵐ s r → ∀ n′ {k′ b′} → s ≤ᵖ ⟨ n′ , nU s , k′ , b′ ⟩
        → Σ[ k₂ ∈ Carrier ] Σ[ b₂ ∈ Carrier ]
            Uᵐ ⟨ n′ , nU s , k′ , b′ ⟩ ⟨ n′ , nU r , k₂ , b₂ ⟩ × r ≤ᵖ ⟨ n′ , nU r , k₂ , b₂ ⟩
  monoᵁ (bank {e = e} x) n′ {k′} {b′} (hb , hs) =
    k′ , b′ + e , bank x , +-monoˡ-≤ e hb , sum-+ e hs
  monoᵁ (skip x) n′ {k′} {b′} (hb , hs) = k′ , b′ , skip x , (hb , hs)
  monoᵁ (fill {o = o} x) n′ {k′} {b′} (hb , hs) =
    (k′ + b′) + costˡᵒ o , 0ᴰ , fill x , ≤-refl , +-monoˡ-≤ 0ᴰ (+-monoˡ-≤ (costˡᵒ o) hs)

  monoᴸ : ∀ {s r} → Lᵐ s r → ∀ {k′ b′} → s ≤ᵖ ⟨ nL s , nU s , k′ , b′ ⟩
        → Σ[ k₂ ∈ Carrier ] Σ[ b₂ ∈ Carrier ]
            Lᵐ ⟨ nL s , nU s , k′ , b′ ⟩ ⟨ nL r , nU r , k₂ , b₂ ⟩ × r ≤ᵖ ⟨ nL r , nU r , k₂ , b₂ ⟩
  monoᴸ (spend {k = k₁} {b₁} {d} x le) {k₂} {b₂} (hb , hs) =
    k₂ ∸ d , b₂ ∸ (d ∸ k₂) , spend x (≤-trans le hs) ,
    (proj₁ (spend-mono d hb hs) , proj₂ (spend-mono d hb hs))
  monoᴸ (pay {o = o} x le) {k′} {b′} (hb , hs) =
    0ᴰ , b′ ∸ costʰⁱ o , pay x (≤-trans le hb) ,
    M.∸-monoˡ-≤ (costʰⁱ o) hb , +-monoʳ-≤ 0ᴰ (M.∸-monoˡ-≤ (costʰⁱ o) hb)
  monoᴸ (match x y) h = 0ᴰ , 0ᴰ , match x y , ≤-refl , ≤-refl

  ----------------------------------------------------------------------
  -- The guarantee's moves dropped

  -- a walk from a node `n` of `L`, replayed by the allowance alone from
  -- a pair at least as good, the guarantee staying at `n`, a match
  -- becoming a skip

  dropᴸ : ∀ {s t} → Walk s t
        → ∀ {k′ b′} → s ≤ᵖ ⟨ nL s , nU s , k′ , b′ ⟩
        → Σ[ k₂ ∈ Carrier ] Σ[ b₂ ∈ Carrier ]
            Walkᵁ ⟨ nL s , nU s , k′ , b′ ⟩ ⟨ nL s , nU t , k₂ , b₂ ⟩ × t ≤ᵖ ⟨ nL s , nU t , k₂ , b₂ ⟩
  dropᴸ []         {k′} {b′} h = k′ , b′ , [] , h
  dropᴸ {s} (w ▸ uᵐ μ) h with dropᴸ w h
  ... | k₂ , b₂ , v , h′ with monoᵁ μ (nL s) h′
  ...   | k₃ , b₃ , μ′ , h″ = k₃ , b₃ , v ▸ μ′ , h″
  dropᴸ (w ▸ lᵐ (spend {k = k} {b} {d} _ _)) h with dropᴸ w h
  ... | k₂ , b₂ , v , h′ = k₂ , b₂ , v , ≤ᵖ-trans (spend-≤ k b d) h′
  dropᴸ (w ▸ lᵐ (pay {k = k} {b} {o} _ _)) h with dropᴸ w h
  ... | k₂ , b₂ , v , h′ = k₂ , b₂ , v , ≤ᵖ-trans (pay-≤ k b (costʰⁱ o)) h′
  dropᴸ (w ▸ lᵐ (match _ y)) h with dropᴸ w h
  ... | k₂ , b₂ , v , h′ = k₂ , b₂ , v ▸ skip y , zero-≤ k₂ b₂

  ----------------------------------------------------------------------
  -- A walk cut at a visit of a node of `L`

  split : ∀ {s t} (w : Walk s t) {n} → n ∈ path w
        → Σ[ m ∈ U.Node ] Σ[ k′ ∈ Carrier ] Σ[ b′ ∈ Carrier ]
          Σ[ u ∈ Walk s ⟨ n , m , k′ , b′ ⟩ ]
            Walk ⟨ n , m , k′ , b′ ⟩ t × (Unique (path w) → Unique (path u))
  split []          (here refl) = _ , _ , _ , [] , [] , λ q → q
  split (w ▸ uᵐ μ)  p with split w p
  ... | m , k′ , b′ , u , v , q = m , k′ , b′ , u , v ▸ uᵐ μ , q
  split (w ▸ lᵐ μ)  (here refl) = _ , _ , _ , w ▸ lᵐ μ , [] , λ q → q
  split (w ▸ lᵐ μ)  (there p) with split w p
  ... | m , k′ , b′ , u , v , q = m , k′ , b′ , u , v ▸ lᵐ μ , λ { (_ ∷ q′) → q q′ }

  ----------------------------------------------------------------------
  -- Every walk is dominated by one that repeats no node of `L`

  Shorter : State → State → Set
  Shorter s t = Σ[ k′ ∈ Carrier ] Σ[ b′ ∈ Carrier ]
                Σ[ w ∈ Walk s ⟨ nL t , nU t , k′ , b′ ⟩ ]
                  Unique (path w) × t ≤ᵖ ⟨ nL t , nU t , k′ , b′ ⟩

  private
    stepᵁ : ∀ {s n m m′ k b k₁ b₁} → Shorter s ⟨ n , m , k , b ⟩
          → Uᵐ ⟨ n , m , k , b ⟩ ⟨ n , m′ , k₁ , b₁ ⟩ → Shorter s ⟨ n , m′ , k₁ , b₁ ⟩
    stepᵁ {n = n} (k₂ , b₂ , w , q , h) μ with monoᵁ μ n h
    ... | k₃ , b₃ , μ′ , h′ = k₃ , b₃ , w ▸ uᵐ μ′ , q , h′

  shorten : ∀ {s t} → Walk s t → Shorter s t
  shorten {s} [] = k s , b s , [] , All.[] ∷ [] , ≤-refl , ≤-refl
  shorten (w ▸ uᵐ μ@(bank _)) = stepᵁ (shorten w) μ
  shorten (w ▸ uᵐ μ@(skip _)) = stepᵁ (shorten w) μ
  shorten (w ▸ uᵐ μ@(fill _)) = stepᵁ (shorten w) μ
  shorten (_▸_ {r = r} w (lᵐ μ)) with shorten w
  ... | k₂ , b₂ , w′ , q , h with monoᴸ μ h
  ...   | k₃ , b₃ , μ′ , h′ with nL r ∈? path w′
  ...     | no  ∉ = k₃ , b₃ , w′ ▸ lᵐ μ′ , ¬Any⇒All¬ _ ∉ ∷ q , h′
  ...     | yes p with split w′ p
  ...       | m₁ , k₄ , b₄ , u , v , qu with dropᴸ (v ▸ lᵐ μ′) (≤-refl , ≤-refl)
  ...         | k₅ , b₅ , uw , h″ =
    k₅ , b₅ , u ++ʷ embed uw , subst Unique (sym (path-++ᵁ u uw)) (qu q) , ≤ᵖ-trans h′ h″

  ----------------------------------------------------------------------
  -- Consistency needs no cycle of the guarantee

  -- with `L` accepting at `final` and `U` able to finish at `live`,
  -- some walk from the starts reaches an accepting node of `L` and a
  -- live node of `U`; if one does, one does whose path through `L`
  -- repeats no node

  Consistentᴳ : (L.Node → Set) → (U.Node → Set) → Set
  Consistentᴳ final live =
    Σ[ t ∈ State ] Walk ⟨ L.start , U.start , 0ᴰ , 0ᴰ ⟩ t × final (nL t) × live (nU t)

  acyclic : ∀ {final live} → Consistentᴳ final live
          → Σ[ t ∈ State ] Σ[ w ∈ Walk ⟨ L.start , U.start , 0ᴰ , 0ᴰ ⟩ t ]
              Unique (path w) × final (nL t) × live (nU t)
  acyclic (t , w , f , l) with shorten w
  ... | k′ , b′ , w′ , q , _ = _ , w′ , q , f , l

------------------------------------------------------------------------
-- Smaller demands and larger resources are no worse
--
-- Two pairs of graphs on the same nodes, with the same operations: in
-- the second, every delay of the guarantee is matched by one no larger
-- and every delay of the allowance by one no smaller. Every walk of
-- the first is dominated, at the same nodes, by a walk of the second.
-- So reading the guarantee's delays at their least values and the
-- allowance's at their greatest loses no walk.

graph : (N : Set) → DecidableEquality N → N
      → (N → Carrier → N → Set) → (N → Op → N → Set) → Graph
graph N eq s dl ol = record { Node = N ; _≟_ = eq ; start = s ; _─d[_]→_ = dl ; _─o[_]→_ = ol }

module Extremal
  (NL NU : Set) (_≟ᴸ_ : DecidableEquality NL) (_≟ᵁ_ : DecidableEquality NU)
  (sL : NL) (sU : NU)
  (OL : NL → Op → NL → Set) (OU : NU → Op → NU → Set)
  (DL DL′ : NL → Carrier → NL → Set) (DU DU′ : NU → Carrier → NU → Set)
  (demand   : ∀ {n d n′} → DL n d n′ → Σ[ d′ ∈ Carrier ] DL′ n d′ n′ × d′ ≤ d)
  (resource : ∀ {m e m′} → DU m e m′ → Σ[ e′ ∈ Carrier ] DU′ m e′ m′ × e ≤ e′) where

  private
    L  = graph NL _≟ᴸ_ sL DL  OL
    L′ = graph NL _≟ᴸ_ sL DL′ OL
    U  = graph NU _≟ᵁ_ sU DU  OU
    U′ = graph NU _≟ᵁ_ sU DU′ OU

    W  = Walk L U
    W′ = Walk L′ U′

  -- one move, replayed from a pair at least as good

  step : ∀ {s t r k₂ b₂} → W′ s ⟨ nL t , nU t , k₂ , b₂ ⟩
       → Move L U t r → b t ≤ b₂ → k t + b t ≤ k₂ + b₂
       → Σ[ k₃ ∈ Carrier ] Σ[ b₃ ∈ Carrier ]
           W′ s ⟨ nL r , nU r , k₃ , b₃ ⟩
         × b r ≤ b₃ × k r + b r ≤ k₃ + b₃
  step {k₂ = k₂} {b₂} w′ (uᵐ (bank {k = k₁} {b₁} {e} x)) hb hs with resource x
  ... | e′ , x′ , le =
    k₂ , b₂ + e′ , w′ ▸ uᵐ (bank x′) ,
    ≤-trans (+-monoˡ-≤ e hb) (+-monoʳ-≤ b₂ le) ,
    ≤-trans (subst₂ _≤_ (+-assoc k₁ b₁ e) (+-assoc k₂ b₂ e) (+-monoˡ-≤ e hs))
            (+-monoʳ-≤ k₂ (+-monoʳ-≤ b₂ le))
  step {k₂ = k₂} {b₂} w′ (uᵐ (skip x)) hb hs = k₂ , b₂ , w′ ▸ uᵐ (skip x) , hb , hs
  step {k₂ = k₂} {b₂} w′ (uᵐ (fill {o = o} x)) hb hs =
    (k₂ + b₂) + costˡᵒ o , 0ᴰ , w′ ▸ uᵐ (fill x) ,
    ≤-refl , +-monoˡ-≤ 0ᴰ (+-monoˡ-≤ (costˡᵒ o) hs)
  step {k₂ = k₂} {b₂} w′ (lᵐ (spend {k = k₁} {b₁} {d} x le)) hb hs with demand x
  ... | d′ , x′ , le′ =
    k₂ ∸ d′ , b₂ ∸ (d′ ∸ k₂) , w′ ▸ lᵐ (spend x′ (≤-trans le′ (≤-trans le hs))) ,
    ≤-trans (proj₁ (spend-mono d hb hs)) (proj₁ (spend-anti k₂ b₂ le′)) ,
    ≤-trans (proj₂ (spend-mono d hb hs)) (proj₂ (spend-anti k₂ b₂ le′))
  step {k₂ = k₂} {b₂} w′ (lᵐ (pay {o = o} x le)) hb hs =
    0ᴰ , b₂ ∸ costʰⁱ o , w′ ▸ lᵐ (pay x (≤-trans le hb)) ,
    M.∸-monoˡ-≤ (costʰⁱ o) hb , +-monoʳ-≤ 0ᴰ (M.∸-monoˡ-≤ (costʰⁱ o) hb)
  step {k₂ = k₂} {b₂} w′ (lᵐ (match x y)) hb hs = 0ᴰ , 0ᴰ , w′ ▸ lᵐ (match x y) , ≤-refl , ≤-refl

  dominated : ∀ {n m k₀ b₀ t} → W ⟨ n , m , k₀ , b₀ ⟩ t
            → ∀ {k′ b′} → b₀ ≤ b′ → k₀ + b₀ ≤ k′ + b′
            → Σ[ k₂ ∈ Carrier ] Σ[ b₂ ∈ Carrier ]
                W′ ⟨ n , m , k′ , b′ ⟩ ⟨ nL t , nU t , k₂ , b₂ ⟩
              × b t ≤ b₂ × k t + b t ≤ k₂ + b₂
  dominated [] {k′} {b′} hb hs = k′ , b′ , [] , hb , hs
  dominated (w ▸ μ) hb hs with dominated w hb hs
  ... | k₂ , b₂ , w′ , hb′ , hs′ = step w′ μ hb′ hs′
