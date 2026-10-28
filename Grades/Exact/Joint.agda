------------------------------------------------------------------------
-- A lower and an upper word of letters with a common run, walked     --
-- together.                                                          --
--                                                                    --
-- Some exact word fits an instance of a lower word `v` and one of an --
-- upper word `w` exactly when the two words can be walked together   --
-- in time, each letter a piece of a length it admits. The walk stops --
-- where a piece of either word ends; there the other word is at a    --
-- boundary as well (`sync`), or inside a piece, known by its letter  --
-- and the time it has run (`inL`, `inU`). A piece starts at a        --
-- boundary of its own word. Two pieces running at once must meet:    --
-- an operation lies inside a stretch admitting it, and two           --
-- operations run together only from a common start, as one. So the   --
-- walk is the run of a timed automaton with two clocks, the time     --
-- each word's current piece has run, one of them reset at every      --
-- stop. A stretch letter admitting no time may be passed at a        --
-- boundary.                                                          --
--                                                                    --
--   sound:    a walk builds the three words, and the two pourings    --
--             (`Exact.Pour`) of the common one into the others;      --
--   complete: a common word gives, at each instant, labels of the    --
--             two instances with a common lower bound, and the walk  --
--             follows their pieces in time.                          --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Joint
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Subset using (_∈_; _⊆_)
open import Data.Fin.Subset.Properties using (⊥⊆)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T using (Cut; Hi)
open import Grades.Durations.Intervals.Dense T using (_∈ⁱ_)

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Order T Op n code code-injective
open import Grades.Exact.Pour T Op n code code-injective
  using (Pour; done; match; nextx; nexty; pour; pour-⊑) renaming (Adm to Admᵢ)
open import Grades.Exact.Expression T Op n code code-injective running
  using (Instance; upper; lower; End; _∈ᵉ_)
open import Grades.Exact.Letters T Op n code code-injective running
  using (Letter; op; st; Word′; Shape; WordOf; Inst; opk; stk)

open RunningTimes.RunningTimes running using (rt; rt-pos)

------------------------------------------------------------------------
-- Letters, the lengths they admit, and which may run together

Adm : ∀ {s} → Letter (End s) → Carrier → Set
Adm (op o)   τ = τ ∈ⁱ rt o
Adm (st S e) τ = τ ∈ᵉ e

Meets : ∀ {A B : Set} → Letter A → Letter B → Set
Meets (op o)   (op o′)  = ⊥
Meets (op o)   (st S _) = code o ∈ S
Meets (st S _) (op o)   = code o ∈ S
Meets (st _ _) (st _ _) = ⊤

------------------------------------------------------------------------
-- The walk

data Phase : Set where
  sync : Phase
  inL  : Letter Cut → Carrier → Phase
  inU  : Letter Hi → Carrier → Phase

-- the lower and the upper word at a boundary

data AtL : Phase → Set where
  sync : AtL sync
  inU  : ∀ {m e} → AtL (inU m e)

data AtU : Phase → Set where
  sync : AtU sync
  inL  : ∀ {ℓ e} → AtU (inL ℓ e)

data Walk : Word′ lower → Word′ upper → Phase → Set where
  done  : Walk [] [] sync
  -- a stretch admitting no time, passed
  skipL : ∀ {S c v w φ} → AtL φ → 0ᴰ ∈ᵉ c → Walk v w φ → Walk (st S c ∷ v) w φ
  skipU : ∀ {S h v w φ} → AtU φ → 0ᴰ ∈ᵉ h → Walk v w φ → Walk v (st S h ∷ w) φ
  -- both start; an operation of both, as one
  opop  : ∀ {o t v w} → Adm (op {Cut} o) t → Walk v w sync
        → Walk (op o ∷ v) (op o ∷ w) sync
  -- both start; the lower ends first, the upper, or both
  syncL : ∀ {ℓ m t v w} → Meets ℓ m → 0ᴰ <ᴰ t → Adm ℓ t
        → Walk v w (inU m t) → Walk (ℓ ∷ v) (m ∷ w) sync
  syncU : ∀ {ℓ m t v w} → Meets ℓ m → 0ᴰ <ᴰ t → Adm m t
        → Walk v w (inL ℓ t) → Walk (ℓ ∷ v) (m ∷ w) sync
  syncB : ∀ {ℓ m t v w} → Meets ℓ m → 0ᴰ <ᴰ t → Adm ℓ t → Adm m t
        → Walk v w sync → Walk (ℓ ∷ v) (m ∷ w) sync
  -- the lower starts inside an upper piece
  firstL : ∀ {ℓ m e t v w} → Meets ℓ m → 0ᴰ <ᴰ t → Adm ℓ t
         → Walk v w (inU m (e +ᴰ t)) → Walk (ℓ ∷ v) w (inU m e)
  lateU  : ∀ {ℓ m e t v w} → Meets ℓ m → 0ᴰ <ᴰ t → Adm m (e +ᴰ t)
         → Walk v w (inL ℓ t) → Walk (ℓ ∷ v) w (inU m e)
  bothU  : ∀ {ℓ m e t v w} → Meets ℓ m → 0ᴰ <ᴰ t → Adm ℓ t → Adm m (e +ᴰ t)
         → Walk v w sync → Walk (ℓ ∷ v) w (inU m e)
  -- the upper starts inside a lower piece
  firstU : ∀ {ℓ m e t v w} → Meets ℓ m → 0ᴰ <ᴰ t → Adm m t
         → Walk v w (inL ℓ (e +ᴰ t)) → Walk v (m ∷ w) (inL ℓ e)
  lateL  : ∀ {ℓ m e t v w} → Meets ℓ m → 0ᴰ <ᴰ t → Adm ℓ (e +ᴰ t)
         → Walk v w (inU m t) → Walk v (m ∷ w) (inL ℓ e)
  bothL  : ∀ {ℓ m e t v w} → Meets ℓ m → 0ᴰ <ᴰ t → Adm ℓ (e +ᴰ t) → Adm m t
         → Walk v w sync → Walk v (m ∷ w) (inL ℓ e)

------------------------------------------------------------------------
-- Pourings

private
  pour-≤ˣ : ∀ {i x a y b} → Pour (i ∷ x) a y b → a ≤ᴰ len i
  pour-≤ˣ (match _)            = 0ᴰ-least _
  pour-≤ˣ (nextx _)            = ≤ᴰ-refl
  pour-≤ˣ (nexty w)            = pour-≤ˣ w
  pour-≤ˣ (pour q _ r _ _)     = ≤ᴰ-trans (≤ᴰ-+ _ q) r

  pour-≤ʸ : ∀ {x a j y b} → Pour x a (j ∷ y) b → b ≤ᴰ len j
  pour-≤ʸ (match _)            = 0ᴰ-least _
  pour-≤ʸ (nextx w)            = pour-≤ʸ w
  pour-≤ʸ (nexty _)            = ≤ᴰ-refl
  pour-≤ʸ (pour q _ _ r _)     = ≤ᴰ-trans (≤ᴰ-+ _ q) r

  -- an item poured, from its start, into a stretch

  pour₀ : ∀ {i x d S y b} t → Admᵢ i S → t ≤ᴰ len i → b +ᴰ t ≤ᴰ ∣ d ∣⁺
        → Pour (i ∷ x) t (st d S ∷ y) (b +ᴰ t) → Pour (i ∷ x) 0ᴰ (st d S ∷ y) b
  pour₀ {i} {x} {d} {S} {y} {b} t a r₁ r₂ w =
    pour t a (subst (_≤ᴰ len i) (sym (+ᴰ-identityˡ t)) r₁) r₂
      (subst (λ z → Pour (i ∷ x) z (st d S ∷ y) (b +ᴰ t)) (sym (+ᴰ-identityˡ t)) w)

  -- a whole item poured into a stretch
  fill : ∀ {i x d S y b} → Admᵢ i S → b +ᴰ len i ≤ᴰ ∣ d ∣⁺
       → Pour x 0ᴰ (st d S ∷ y) (b +ᴰ len i) → Pour (i ∷ x) 0ᴰ (st d S ∷ y) b
  fill {i} a r w = pour₀ (len i) a ≤ᴰ-refl r (nextx w)

  -- a whole stretch filled from a word's start
  fill₀ : ∀ {i x d S y} → Admᵢ i S → len i ≡ ∣ d ∣⁺
        → Pour x 0ᴰ y 0ᴰ → Pour (i ∷ x) 0ᴰ (st d S ∷ y) 0ᴰ
  fill₀ {i} {x} {d} {S} {y} a e w =
    fill a (≤ᴰ-reflexive (trans (+ᴰ-identityˡ (len i)) e))
      (subst (λ z → Pour x 0ᴰ (st d S ∷ y) z) (sym (trans (+ᴰ-identityˡ (len i)) e)) (nexty w))

  -- a strict wait admits nothing, so fits any stretch
  wait : (t : Carrier) → 0ᴰ <ᴰ t → Item
  wait t p = st (pos⁺ t p) Data.Fin.Subset.⊥

  -- the stretch of a positive length
  stretch⁺ : ∀ S (d : D⁺) → stretch S ∣ d ∣⁺ ≡ st d S ∷ []
  stretch⁺ S d = trans (stretch-pos S ∣ d ∣⁺ (∣∣⁺-pos d)) (cong (λ z → st z S ∷ []) (∣∣⁺-inj refl))

  -- instances, letter by letter

  inst-op : ∀ {s o y v} (d : D⁺) → ∣ d ∣⁺ ∈ⁱ rt o → Inst {s} y v → Inst (op o d ∷ y) (op o ∷ v)
  inst-op d r (ps , sh , wo) = _ , Shape.op sh , WordOf.op r wo

  inst-st : ∀ {s S} {e : End s} {y v} (d : D⁺) → ∣ d ∣⁺ ∈ᵉ e → Inst {s} y v
          → Inst (st d S ∷ y) (st S e ∷ v)
  inst-st {S = S} {y = y} d a (ps , sh , wo) =
    _ , Shape.st a sh , subst (λ z → WordOf ((stk S , ∣ d ∣⁺) ∷ ps) (z ++ y)) (stretch⁺ S d) (WordOf.st wo)

  inst-skip : ∀ {s S} {e : End s} {y v} → 0ᴰ ∈ᵉ e → Inst {s} y v → Inst y (st S e ∷ v)
  inst-skip {S = S} {y = y} a (ps , sh , wo) =
    _ , Shape.st a sh ,
    subst (λ z → WordOf ((stk S , 0ᴰ) ∷ ps) (z ++ y)) (stretch-zero S 0ᴰ (<-irrefl)) (WordOf.st wo)

  inst-[] : ∀ {s} → Inst {s} [] []
  inst-[] = [] , Shape.[] , WordOf.[]

------------------------------------------------------------------------
-- Soundness

-- what a walk from a phase builds: an instance of what remains of each
-- word, with the piece in progress, and a common word poured into both

Sem : Word′ lower → Word′ upper → Phase → Set
Sem v w sync =
  Σ[ x ∈ Word ] Σ[ y ∈ Word ] Σ[ z ∈ Word ]
    Inst y v × Inst z w × Pour x 0ᴰ y 0ᴰ × Pour x 0ᴰ z 0ᴰ
Sem v w (inU (st S h) e) =
  Σ[ d ∈ D⁺ ] Σ[ x ∈ Word ] Σ[ y ∈ Word ] Σ[ z ∈ Word ]
    Adm (st {Hi} S h) ∣ d ∣⁺ × Inst y v × Inst z w × Pour x 0ᴰ y 0ᴰ × Pour x 0ᴰ (st d S ∷ z) e
Sem v w (inU (op o) e) =
  Σ[ d ∈ D⁺ ] Σ[ x ∈ Word ] Σ[ y ∈ Word ] Σ[ z ∈ Word ]
    ∣ d ∣⁺ ∈ⁱ rt o × Inst y v × Inst z w × Pour (op o d ∷ x) e y 0ᴰ × Pour x 0ᴰ z 0ᴰ
Sem v w (inL (st S c) e) =
  Σ[ d ∈ D⁺ ] Σ[ x ∈ Word ] Σ[ y ∈ Word ] Σ[ z ∈ Word ]
    Adm (st {Cut} S c) ∣ d ∣⁺ × Inst y v × Inst z w × Pour x 0ᴰ (st d S ∷ y) e × Pour x 0ᴰ z 0ᴰ
Sem v w (inL (op o) e) =
  Σ[ d ∈ D⁺ ] Σ[ x ∈ Word ] Σ[ y ∈ Word ] Σ[ z ∈ Word ]
    ∣ d ∣⁺ ∈ⁱ rt o × Inst y v × Inst z w × Pour x 0ᴰ y 0ᴰ × Pour (op o d ∷ x) e z 0ᴰ

private
  -- an item of length `t` running inside a stretch, and a whole one
  -- both start: the item of the common word, poured into either
  item : ∀ {A} (ℓ : Letter A) (t : Carrier) → 0ᴰ <ᴰ t → Item
  item (op o)   t p = op o (pos⁺ t p)
  item (st S _) t p = wait t p

  pieceˡ : ∀ (ℓ : Letter Cut) (t : Carrier) → 0ᴰ <ᴰ t → Item
  pieceˡ (op o)   t p = op o (pos⁺ t p)
  pieceˡ (st S _) t p = st (pos⁺ t p) S

  pieceᵘ : ∀ (m : Letter Hi) (t : Carrier) → 0ᴰ <ᴰ t → Item
  pieceᵘ (op o)   t p = op o (pos⁺ t p)
  pieceᵘ (st S _) t p = st (pos⁺ t p) S

  inst-pieceˡ : ∀ ℓ {t} (p : 0ᴰ <ᴰ t) → Adm ℓ t → ∀ {y v} → Inst y v → Inst (pieceˡ ℓ t p ∷ y) (ℓ ∷ v)
  inst-pieceˡ (op o)   p a i = inst-op (pos⁺ _ p) a i
  inst-pieceˡ (st S c) p a i = inst-st (pos⁺ _ p) a i

  inst-pieceᵘ : ∀ m {t} (p : 0ᴰ <ᴰ t) → Adm m t → ∀ {z w} → Inst z w → Inst (pieceᵘ m t p ∷ z) (m ∷ w)
  inst-pieceᵘ (op o)   p a i = inst-op (pos⁺ _ p) a i
  inst-pieceᵘ (st S h) p a i = inst-st (pos⁺ _ p) a i

  -- offsets written as sums from zero

  0+ʸ : ∀ {x a y t} → Pour x a y t → Pour x a y (0ᴰ +ᴰ t)
  0+ʸ {x} {a} {y} {t} = subst (Pour x a y) (sym (+ᴰ-identityˡ t))

  0+ˣ : ∀ {x y b t} → Pour x t y b → Pour x (0ᴰ +ᴰ t) y b
  0+ˣ {x} {y} {b} {t} = subst (λ z → Pour x z y b) (sym (+ᴰ-identityˡ t))

  0+≤ : ∀ {t u} → t ≤ᴰ u → 0ᴰ +ᴰ t ≤ᴰ u
  0+≤ {t} r = ≤ᴰ-trans (≤ᴰ-reflexive (+ᴰ-identityˡ t)) r

  +pos : ∀ {e t} → 0ᴰ <ᴰ t → 0ᴰ <ᴰ e +ᴰ t
  +pos {e} {t} p = <-≤-trans p (≤ᴰ-+ˡ t e)

sound : ∀ {v w φ} → Walk v w φ → Sem v w φ
sound done = [] , [] , [] , inst-[] , inst-[] , done , done
sound (skipL sync a w) with sound w
... | x , y , z , iy , iz , p , q = x , y , z , inst-skip a iy , iz , p , q
sound (skipL (inU {m = st S h}) a w) with sound w
... | d , x , y , z , ad , iy , iz , p , q = d , x , y , z , ad , inst-skip a iy , iz , p , q
sound (skipL (inU {m = op o}) a w) with sound w
... | d , x , y , z , ad , iy , iz , p , q = d , x , y , z , ad , inst-skip a iy , iz , p , q
sound (skipU sync a w) with sound w
... | x , y , z , iy , iz , p , q = x , y , z , iy , inst-skip a iz , p , q
sound (skipU (inL {ℓ = st S c}) a w) with sound w
... | d , x , y , z , ad , iy , iz , p , q = d , x , y , z , ad , iy , inst-skip a iz , p , q
sound (skipU (inL {ℓ = op o}) a w) with sound w
... | d , x , y , z , ad , iy , iz , p , q = d , x , y , z , ad , iy , inst-skip a iz , p , q
sound (opop {o} {t} a w) with sound w
... | x , y , z , iy , iz , p , q =
  let d = pos⁺ t (rt-pos o a) in
  op o d ∷ x , op o d ∷ y , op o d ∷ z , inst-op d a iy , inst-op d a iz , match p , match q

-- both start

sound (syncL {op o} {st S h} {t} m pt a w) with sound w
... | d , x , y , z , ad , iy , iz , p , q =
  op o (pos⁺ t pt) ∷ x , op o (pos⁺ t pt) ∷ y , st d S ∷ z ,
  inst-op (pos⁺ t pt) a iy , inst-st d ad iz , match p , fill m (0+≤ (pour-≤ʸ q)) (0+ʸ q)
sound (syncL {st S′ c} {st S h} {t} m pt a w) with sound w
... | d , x , y , z , ad , iy , iz , p , q =
  wait t pt ∷ x , st (pos⁺ t pt) S′ ∷ y , st d S ∷ z ,
  inst-st (pos⁺ t pt) a iy , inst-st d ad iz , fill₀ ⊥⊆ refl p , fill ⊥⊆ (0+≤ (pour-≤ʸ q)) (0+ʸ q)
sound (syncL {st S′ c} {op o} {t} m pt a w) with sound w
... | d , x , y , z , r , iy , iz , p , q =
  op o d ∷ x , st (pos⁺ t pt) S′ ∷ y , op o d ∷ z ,
  inst-st (pos⁺ t pt) a iy , inst-op d r iz ,
  pour₀ t m (pour-≤ˣ p) (0+≤ ≤ᴰ-refl) (0+ʸ (nexty p)) , match q
sound (syncL {op o} {op o′} () pt a w)

sound (syncU {st S′ c} {op o} {t} m pt a w) with sound w
... | d , x , y , z , ad , iy , iz , p , q =
  op o (pos⁺ t pt) ∷ x , st d S′ ∷ y , op o (pos⁺ t pt) ∷ z ,
  inst-st d ad iy , inst-op (pos⁺ t pt) a iz , fill m (0+≤ (pour-≤ʸ p)) (0+ʸ p) , match q
sound (syncU {st S′ c} {st S h} {t} m pt a w) with sound w
... | d , x , y , z , ad , iy , iz , p , q =
  wait t pt ∷ x , st d S′ ∷ y , st (pos⁺ t pt) S ∷ z ,
  inst-st d ad iy , inst-st (pos⁺ t pt) a iz , fill ⊥⊆ (0+≤ (pour-≤ʸ p)) (0+ʸ p) , fill₀ ⊥⊆ refl q
sound (syncU {op o} {st S h} {t} m pt a w) with sound w
... | d , x , y , z , r , iy , iz , p , q =
  op o d ∷ x , op o d ∷ y , st (pos⁺ t pt) S ∷ z ,
  inst-op d r iy , inst-st (pos⁺ t pt) a iz ,
  match p , pour₀ t m (pour-≤ˣ q) (0+≤ ≤ᴰ-refl) (0+ʸ (nexty q))
sound (syncU {op o} {op o′} () pt a w)

sound (syncB {op o} {st S h} {t} m pt a b w) with sound w
... | x , y , z , iy , iz , p , q =
  op o (pos⁺ t pt) ∷ x , op o (pos⁺ t pt) ∷ y , st (pos⁺ t pt) S ∷ z ,
  inst-op (pos⁺ t pt) a iy , inst-st (pos⁺ t pt) b iz , match p , fill₀ m refl q
sound (syncB {st S′ c} {op o} {t} m pt a b w) with sound w
... | x , y , z , iy , iz , p , q =
  op o (pos⁺ t pt) ∷ x , st (pos⁺ t pt) S′ ∷ y , op o (pos⁺ t pt) ∷ z ,
  inst-st (pos⁺ t pt) a iy , inst-op (pos⁺ t pt) b iz , fill₀ m refl p , match q
sound (syncB {st S′ c} {st S h} {t} m pt a b w) with sound w
... | x , y , z , iy , iz , p , q =
  wait t pt ∷ x , st (pos⁺ t pt) S′ ∷ y , st (pos⁺ t pt) S ∷ z ,
  inst-st (pos⁺ t pt) a iy , inst-st (pos⁺ t pt) b iz , fill₀ ⊥⊆ refl p , fill₀ ⊥⊆ refl q
sound (syncB {op o} {op o′} () pt a b w)

-- the lower starts inside an upper piece

sound (firstL {op o} {st S h} {e} {t} m pt a w) with sound w
... | d , x , y , z , ad , iy , iz , p , q =
  d , op o (pos⁺ t pt) ∷ x , op o (pos⁺ t pt) ∷ y , z ,
  ad , inst-op (pos⁺ t pt) a iy , iz , match p , fill m (pour-≤ʸ q) q
sound (firstL {st S′ c} {st S h} {e} {t} m pt a w) with sound w
... | d , x , y , z , ad , iy , iz , p , q =
  d , wait t pt ∷ x , st (pos⁺ t pt) S′ ∷ y , z ,
  ad , inst-st (pos⁺ t pt) a iy , iz , fill₀ ⊥⊆ refl p , fill ⊥⊆ (pour-≤ʸ q) q
sound (firstL {st S′ c} {op o} {e} {t} m pt a w) with sound w
... | d , x , y , z , r , iy , iz , p , q =
  d , x , st (pos⁺ t pt) S′ ∷ y , z ,
  r , inst-st (pos⁺ t pt) a iy , iz , pour t m (pour-≤ˣ p) (0+≤ ≤ᴰ-refl) (0+ʸ (nexty p)) , q
sound (firstL {op o} {op o′} () pt a w)

sound (lateU {st S′ c} {st S h} {e} {t} m pt a w) with sound w
... | d′ , x , y , z , ad , iy , iz , p , q =
  pos⁺ (e +ᴰ t) (+pos pt) , wait t pt ∷ x , st d′ S′ ∷ y , z ,
  a , inst-st d′ ad iy , iz , fill ⊥⊆ (0+≤ (pour-≤ʸ p)) (0+ʸ p) , fill ⊥⊆ ≤ᴰ-refl (nexty q)
sound (lateU {op o} {st S h} {e} {t} m pt a w) with sound w
... | d′ , x , y , z , r , iy , iz , p , q =
  pos⁺ (e +ᴰ t) (+pos pt) , op o d′ ∷ x , op o d′ ∷ y , z ,
  a , inst-op d′ r iy , iz , match p , pour₀ t m (pour-≤ˣ q) ≤ᴰ-refl (nexty q)
sound (lateU {st S′ c} {op o} {e} {t} m pt a w) with sound w
... | d′ , x , y , z , ad , iy , iz , p , q =
  pos⁺ (e +ᴰ t) (+pos pt) , x , st d′ S′ ∷ y , z ,
  a , inst-st d′ ad iy , iz , pour t m ≤ᴰ-refl (0+≤ (pour-≤ʸ p)) (nextx (0+ʸ p)) , q
sound (lateU {op o} {op o′} () pt a w)

sound (bothU {op o} {st S h} {e} {t} m pt a b w) with sound w
... | x , y , z , iy , iz , p , q =
  pos⁺ (e +ᴰ t) (+pos pt) , op o (pos⁺ t pt) ∷ x , op o (pos⁺ t pt) ∷ y , z ,
  b , inst-op (pos⁺ t pt) a iy , iz , match p , fill m ≤ᴰ-refl (nexty q)
sound (bothU {st S′ c} {st S h} {e} {t} m pt a b w) with sound w
... | x , y , z , iy , iz , p , q =
  pos⁺ (e +ᴰ t) (+pos pt) , wait t pt ∷ x , st (pos⁺ t pt) S′ ∷ y , z ,
  b , inst-st (pos⁺ t pt) a iy , iz , fill₀ ⊥⊆ refl p , fill ⊥⊆ ≤ᴰ-refl (nexty q)
sound (bothU {st S′ c} {op o} {e} {t} m pt a b w) with sound w
... | x , y , z , iy , iz , p , q =
  pos⁺ (e +ᴰ t) (+pos pt) , x , st (pos⁺ t pt) S′ ∷ y , z ,
  b , inst-st (pos⁺ t pt) a iy , iz , pour t m ≤ᴰ-refl (0+≤ ≤ᴰ-refl) (nextx (0+ʸ (nexty p))) , q
sound (bothU {op o} {op o′} () pt a b w)

-- the upper starts inside a lower piece

sound (firstU {st S′ c} {op o} {e} {t} m pt a w) with sound w
... | d , x , y , z , ad , iy , iz , p , q =
  d , op o (pos⁺ t pt) ∷ x , y , op o (pos⁺ t pt) ∷ z ,
  ad , iy , inst-op (pos⁺ t pt) a iz , fill m (pour-≤ʸ p) p , match q
sound (firstU {st S′ c} {st S h} {e} {t} m pt a w) with sound w
... | d , x , y , z , ad , iy , iz , p , q =
  d , wait t pt ∷ x , y , st (pos⁺ t pt) S ∷ z ,
  ad , iy , inst-st (pos⁺ t pt) a iz , fill ⊥⊆ (pour-≤ʸ p) p , fill₀ ⊥⊆ refl q
sound (firstU {op o} {st S h} {e} {t} m pt a w) with sound w
... | d , x , y , z , r , iy , iz , p , q =
  d , x , y , st (pos⁺ t pt) S ∷ z ,
  r , iy , inst-st (pos⁺ t pt) a iz , p , pour t m (pour-≤ˣ q) (0+≤ ≤ᴰ-refl) (0+ʸ (nexty q))
sound (firstU {op o} {op o′} () pt a w)

sound (lateL {st S′ c} {st S h} {e} {t} m pt a w) with sound w
... | d , x , y , z , ad , iy , iz , p , q =
  pos⁺ (e +ᴰ t) (+pos pt) , wait t pt ∷ x , y , st d S ∷ z ,
  a , iy , inst-st d ad iz , fill ⊥⊆ ≤ᴰ-refl (nexty p) , fill ⊥⊆ (0+≤ (pour-≤ʸ q)) (0+ʸ q)
sound (lateL {st S′ c} {op o} {e} {t} m pt a w) with sound w
... | d , x , y , z , r , iy , iz , p , q =
  pos⁺ (e +ᴰ t) (+pos pt) , op o d ∷ x , y , op o d ∷ z ,
  a , iy , inst-op d r iz , pour₀ t m (pour-≤ˣ p) ≤ᴰ-refl (nexty p) , match q
sound (lateL {op o} {st S h} {e} {t} m pt a w) with sound w
... | d , x , y , z , ad , iy , iz , p , q =
  pos⁺ (e +ᴰ t) (+pos pt) , x , y , st d S ∷ z ,
  a , iy , inst-st d ad iz , p , pour t m ≤ᴰ-refl (0+≤ (pour-≤ʸ q)) (nextx (0+ʸ q))
sound (lateL {op o} {op o′} () pt a w)

sound (bothL {st S′ c} {op o} {e} {t} m pt a b w) with sound w
... | x , y , z , iy , iz , p , q =
  pos⁺ (e +ᴰ t) (+pos pt) , op o (pos⁺ t pt) ∷ x , y , op o (pos⁺ t pt) ∷ z ,
  a , iy , inst-op (pos⁺ t pt) b iz , fill m ≤ᴰ-refl (nexty p) , match q
sound (bothL {st S′ c} {st S h} {e} {t} m pt a b w) with sound w
... | x , y , z , iy , iz , p , q =
  pos⁺ (e +ᴰ t) (+pos pt) , wait t pt ∷ x , y , st (pos⁺ t pt) S ∷ z ,
  a , iy , inst-st (pos⁺ t pt) b iz , fill ⊥⊆ ≤ᴰ-refl (nexty p) , fill₀ ⊥⊆ refl q
sound (bothL {op o} {st S h} {e} {t} m pt a b w) with sound w
... | x , y , z , iy , iz , p , q =
  pos⁺ (e +ᴰ t) (+pos pt) , x , y , st (pos⁺ t pt) S ∷ z ,
  a , iy , inst-st (pos⁺ t pt) b iz , p , pour t m ≤ᴰ-refl (0+≤ ≤ᴰ-refl) (nextx (0+ʸ (nexty q)))
sound (bothL {op o} {op o′} () pt a b w)
