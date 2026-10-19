------------------------------------------------------------------------
-- Exact timed words and their monoid structure.                      --
--                                                                    --
-- An exact word is one run, described to the precision a timed       --
-- grade can see: a sequence of operations, each with the exact time  --
-- it ran for, and of stretches, each with an exact length and the    --
-- set of operations that may happen inside it. A stretch with the    --
-- empty set is a strict wait, `![ t ]`: pure waiting. Lengths and    --
-- running times are positive durations of a time domain.             --
--                                                                    --
-- Sequencing merges adjacent stretches with the same set, adding     --
-- their lengths, so a word in normal form has no two adjacent        --
-- stretches with one set; the normal words form a monoid, and the    --
-- strict waits a monoid morphism from the durations.                 --
--                                                                    --
-- Operations are coded injectively into `Fin n`, and the sets of a   --
-- stretch are subsets of the codes.                                  --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)

module Syntax.Grades.Exact.Base
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′) where

open import Data.Bool.Base using (Bool)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Subset using (Subset) public
import Data.Fin.Properties as Fin
open import Data.List.Base using (List; []; _∷_; _++_; foldr)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
import Data.Vec.Properties as Vec
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Monus T
  using (Carrier; 0ᴰ; _+ᴰ_; _<ᴰ_; _<ᴰ?_; +ᴰ-identityˡ; +ᴰ-identityʳ;
         +ᴰ-assoc; <⇒≢; <-≤-trans; ≤ᴰ-+; ≤ᴰ-+ˡ; ≮0⇒≡0)

open import Syntax.Grades.Traces.Positive T public

------------------------------------------------------------------------
-- Sets of operations

OpSet : Set
OpSet = Subset n

infix 4 _≟ˢ_ _≟ₒ_

_≟ˢ_ : DecidableEquality OpSet
_≟ˢ_ = Vec.≡-dec Bool._≟_

_≟ₒ_ : DecidableEquality Op
o ≟ₒ o′ with code o Fin.≟ code o′
... | yes e = yes (code-injective e)
... | no ¬e = no λ { refl → ¬e refl }

------------------------------------------------------------------------
-- Items and words

data Item : Set where
  op : Op → D⁺ → Item          -- an operation, with its running time
  st : D⁺ → OpSet → Item       -- a stretch, with the operations it admits

Word : Set
Word = List Item

-- the length of an item, and the duration of a word

len : Item → Carrier
len (op _ d) = ∣ d ∣⁺
len (st d _) = ∣ d ∣⁺

len-pos : (i : Item) → 0ᴰ <ᴰ len i
len-pos (op _ d) = ∣∣⁺-pos d
len-pos (st d _) = ∣∣⁺-pos d

dur : Word → Carrier
dur []      = 0ᴰ
dur (i ∷ w) = len i +ᴰ dur w

-- a nonempty word takes time

dur-pos : (i : Item) (w : Word) → 0ᴰ <ᴰ dur (i ∷ w)
dur-pos i w = <-≤-trans (len-pos i) (≤ᴰ-+ (len i) (dur w))

dur-++ : (x y : Word) → dur (x ++ y) ≡ dur x +ᴰ dur y
dur-++ []      y = sym (+ᴰ-identityˡ (dur y))
dur-++ (i ∷ x) y =
  trans (cong (len i +ᴰ_) (dur-++ x y)) (sym (+ᴰ-assoc (len i) (dur x) (dur y)))

------------------------------------------------------------------------
-- Normal form: no two adjacent stretches with the same set

Apart : Item → Word → Set
Apart (st _ S) (st _ S′ ∷ _) = ¬ (S ≡ S′)
Apart _        _             = ⊤

Normal : Word → Set
Normal []      = ⊤
Normal (i ∷ w) = Apart i w × Normal w

------------------------------------------------------------------------
-- Prepending an item, merging it into a leading stretch with its set

merge : (d : D⁺) (S : OpSet) (e : D⁺) (S′ : OpSet) → Word → Dec (S ≡ S′) → Word
merge d S e S′ w (yes _) = st (d +⁺ e) S ∷ w
merge d S e S′ w (no _)  = st d S ∷ st e S′ ∷ w

infixr 5 _◂_

_◂_ : Item → Word → Word
op o d ◂ w            = op o d ∷ w
st d S ◂ []           = st d S ∷ []
st d S ◂ (op o e ∷ w) = st d S ∷ op o e ∷ w
st d S ◂ (st e S′ ∷ w) = merge d S e S′ w (S ≟ˢ S′)

-- sequencing

infixl 7 _∙_

_∙_ : Word → Word → Word
x ∙ y = foldr _◂_ y x

------------------------------------------------------------------------
-- Prepending keeps the normal form, and the duration

merge-normal : ∀ d S e S′ w (c : Dec (S ≡ S′))
             → Apart (st e S′) w → Normal w → Normal (merge d S e S′ w c)
merge-normal d S e S′ (st _ S″ ∷ w) (yes refl) a nw = a , nw
merge-normal d S e S′ (op _ _ ∷ w)  (yes refl) a nw = tt , nw
merge-normal d S e S′ []            (yes refl) a nw = tt , nw
merge-normal d S e S′ w             (no ¬e)    a nw = ¬e , a , nw

◂-normal : (i : Item) {w : Word} → Normal w → Normal (i ◂ w)
◂-normal (op o d) nw = tt , nw
◂-normal (st d S) {[]} nw = tt , tt
◂-normal (st d S) {op o e ∷ w} nw = tt , nw
◂-normal (st d S) {st e S′ ∷ w} (a , nw) = merge-normal d S e S′ w (S ≟ˢ S′) a nw

∙-normal : (x : Word) {y : Word} → Normal y → Normal (x ∙ y)
∙-normal []      ny = ny
∙-normal (i ∷ x) ny = ◂-normal i (∙-normal x ny)

merge-dur : ∀ d S e S′ w (c : Dec (S ≡ S′))
          → dur (merge d S e S′ w c) ≡ dur (st d S ∷ st e S′ ∷ w)
merge-dur d S e S′ w (yes _) = +ᴰ-assoc ∣ d ∣⁺ ∣ e ∣⁺ (dur w)
merge-dur d S e S′ w (no _)  = refl

dur-◂ : (i : Item) (w : Word) → dur (i ◂ w) ≡ len i +ᴰ dur w
dur-◂ (op o d) w             = refl
dur-◂ (st d S) []            = refl
dur-◂ (st d S) (op o e ∷ w)  = refl
dur-◂ (st d S) (st e S′ ∷ w) = merge-dur d S e S′ w (S ≟ˢ S′)

dur-∙ : (x y : Word) → dur (x ∙ y) ≡ dur x +ᴰ dur y
dur-∙ []      y = sym (+ᴰ-identityˡ (dur y))
dur-∙ (i ∷ x) y =
  trans (dur-◂ i (x ∙ y))
        (trans (cong (len i +ᴰ_) (dur-∙ x y)) (sym (+ᴰ-assoc (len i) (dur x) (dur y))))

------------------------------------------------------------------------
-- The monoid laws

-- prepending to a normal word whose head it is apart from is consing

◂-apart : (i : Item) (w : Word) → Apart i w → i ◂ w ≡ i ∷ w
◂-apart (op o d) w             _ = refl
◂-apart (st d S) []            _ = refl
◂-apart (st d S) (op o e ∷ w)  _ = refl
◂-apart (st d S) (st e S′ ∷ w) a with S ≟ˢ S′
... | yes e′ = ⊥-elim (a e′)
... | no _   = refl

∙-identityˡ : (y : Word) → [] ∙ y ≡ y
∙-identityˡ y = refl

∙-identityʳ : (x : Word) → Normal x → x ∙ [] ≡ x
∙-identityʳ []      _        = refl
∙-identityʳ (i ∷ x) (a , nx) =
  trans (cong (i ◂_) (∙-identityʳ x nx)) (◂-apart i x a)

-- two stretches with one set, prepended in turn, are their sum

◂-◂ : (d e : D⁺) (S : OpSet) (w : Word) → st d S ◂ st e S ◂ w ≡ st (d +⁺ e) S ◂ w
◂-◂ d e S [] with S ≟ˢ S
... | yes _ = refl
... | no ¬e = ⊥-elim (¬e refl)
◂-◂ d e S (op o f ∷ w) with S ≟ˢ S
... | yes _ = refl
... | no ¬e = ⊥-elim (¬e refl)
◂-◂ d e S (st f S′ ∷ w) with S ≟ˢ S′
... | no ¬e = case (S ≟ˢ S)
  where
    case : (c : Dec (S ≡ S)) → merge d S e S (st f S′ ∷ w) c ≡ merge (d +⁺ e) S f S′ w (no ¬e)
    case (yes _) = refl
    case (no ¬r) = ⊥-elim (¬r refl)
... | yes refl = case (S ≟ˢ S)
  where
    case : (c : Dec (S ≡ S))
         → merge d S (e +⁺ f) S w c ≡ st ((d +⁺ e) +⁺ f) S ∷ w
    case (yes _) = cong (λ z → st z S ∷ w) (sym (+⁺-assoc d e f))
    case (no ¬r) = ⊥-elim (¬r refl)

-- prepending commutes with sequencing on the right

◂-∙ : (i : Item) (w z : Word) → (i ◂ w) ∙ z ≡ i ◂ (w ∙ z)
◂-∙ (op o d) w             z = refl
◂-∙ (st d S) []            z = refl
◂-∙ (st d S) (op o e ∷ w)  z = refl
◂-∙ (st d S) (st e S′ ∷ w) z with S ≟ˢ S′
... | yes refl = sym (◂-◂ d e S (w ∙ z))
... | no _     = refl

∙-assoc : (x y z : Word) → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
∙-assoc []      y z = refl
∙-assoc (i ∷ x) y z = trans (◂-∙ i (x ∙ y) z) (cong (i ◂_) (∙-assoc x y z))

-- the product is conical

◂-nonempty : (i : Item) (w : Word) → ¬ (i ◂ w ≡ [])
◂-nonempty (op o d) w ()
◂-nonempty (st d S) [] ()
◂-nonempty (st d S) (op o e ∷ w) ()
◂-nonempty (st d S) (st e S′ ∷ w) eq with S ≟ˢ S′
◂-nonempty (st d S) (st e S′ ∷ w) () | yes _
◂-nonempty (st d S) (st e S′ ∷ w) () | no _

∙-conicalˡ : (x : Word) {y : Word} → x ∙ y ≡ [] → x ≡ []
∙-conicalˡ []      _  = refl
∙-conicalˡ (i ∷ x) eq = ⊥-elim (◂-nonempty i _ eq)

∙-conicalʳ : (x : Word) {y : Word} → x ∙ y ≡ [] → y ≡ []
∙-conicalʳ []      eq = eq
∙-conicalʳ (i ∷ x) eq = ⊥-elim (◂-nonempty i _ eq)

------------------------------------------------------------------------
-- Strict waits

-- the strict wait of a positive length, and of no length

wait-of : (τ : Carrier) → Dec (0ᴰ <ᴰ τ) → Word
wait-of τ (yes p) = st (pos⁺ τ p) Data.Fin.Subset.⊥ ∷ []
wait-of τ (no _)  = []

![_] : Carrier → Word
![ τ ] = wait-of τ (0ᴰ <ᴰ? τ)

![]-normal : (τ : Carrier) → Normal ![ τ ]
![]-normal τ = case (0ᴰ <ᴰ? τ)
  where
    case : (c : Dec (0ᴰ <ᴰ τ)) → Normal (wait-of τ c)
    case (yes _) = tt , tt
    case (no _)  = tt

![]-zero : ![ 0ᴰ ] ≡ []
![]-zero = case (0ᴰ <ᴰ? 0ᴰ)
  where
    case : (c : Dec (0ᴰ <ᴰ 0ᴰ)) → wait-of 0ᴰ c ≡ []
    case (yes p) = ⊥-elim (<⇒≢ p refl)
    case (no _)  = refl

![]-hom : (m n : Carrier) → ![ m +ᴰ n ] ≡ ![ m ] ∙ ![ n ]
![]-hom m n = hom (0ᴰ <ᴰ? m) (0ᴰ <ᴰ? n) (0ᴰ <ᴰ? (m +ᴰ n))
  where
    ∅ = Data.Fin.Subset.⊥
    hom : (a : Dec (0ᴰ <ᴰ m)) (b : Dec (0ᴰ <ᴰ n)) (c : Dec (0ᴰ <ᴰ (m +ᴰ n)))
        → wait-of (m +ᴰ n) c ≡ wait-of m a ∙ wait-of n b
    hom (yes p) (yes q) (yes r) with ∅ ≟ˢ ∅
    ... | yes _ = cong (λ d → st d ∅ ∷ []) (∣∣⁺-inj refl)
    ... | no ¬e = ⊥-elim (¬e refl)
    hom (yes p) (no ¬q) (yes r) =
      cong (λ d → st d ∅ ∷ [])
           (∣∣⁺-inj (trans (cong (m +ᴰ_) (≮0⇒≡0 ¬q)) (+ᴰ-identityʳ m)))
    hom (no ¬p) (yes q) (yes r) =
      cong (λ d → st d ∅ ∷ [])
           (∣∣⁺-inj (trans (cong (_+ᴰ n) (≮0⇒≡0 ¬p)) (+ᴰ-identityˡ n)))
    hom (no ¬p) (no ¬q) (yes r) =
      ⊥-elim (<⇒≢ r (sym (trans (cong₂ _+ᴰ_ (≮0⇒≡0 ¬p) (≮0⇒≡0 ¬q)) (+ᴰ-identityˡ 0ᴰ))))
    hom (yes p) _ (no ¬r) = ⊥-elim (¬r (<-≤-trans p (≤ᴰ-+ m n)))
    hom (no _) (yes q) (no ¬r) = ⊥-elim (¬r (<-≤-trans q (≤ᴰ-+ˡ n m)))
    hom (no _) (no _) (no _) = refl
