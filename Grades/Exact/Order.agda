------------------------------------------------------------------------
-- The order on exact timed words.                                    --
--                                                                    --
-- A word is read as a labelling of the time it spans: at each instant --
-- below its duration it is inside a stretch admitting a set `S` of   --
-- operations (`bud S`), or inside an operation `o` of running time   --
-- `d`, at an offset `δ` from its start (`opl o δ d`). Labels are     --
-- ordered pointwise by                                               --
--                                                                    --
--   bud S ≤ˡ bud S′       when  S ⊆ S′                               --
--   opl o δ d ≤ˡ opl o δ d                                           --
--   opl o δ d ≤ˡ bud S    when  o ∈ S                                --
--                                                                    --
-- and `x ⊑ y`, `x` fits `y`, says the two words take the same time   --
-- and `x`'s label lies below `y`'s at every instant. So an operation  --
-- of `y` is matched by the same operation of `x` over the same span, --
-- since equal offsets at an instant mean equal starts; a strict wait --
-- of `y` is waited out by `x`; inside a stretch of `y` admitting `S`,--
-- `x` waits, or runs stretches with smaller sets, or runs operations --
-- of `S` -- an operation of `x` that `y` does not match belongs to   --
-- the set of every stretch it overlaps (the window rule).            --
--                                                                    --
-- The labelling ignores how stretches are merged, so the order is a  --
-- preorder that sequencing preserves, and on normal words it is      --
-- antisymmetric: the labelling determines the normal form. A word    --
-- fits the empty word only if it is empty.                           --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Exact.Order
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Subset using (_∈_; _⊆_)
open import Data.Fin.Subset.Properties using (⊆-refl; ⊆-trans; ⊆-antisym; ⊥⊆)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Monus T

open import Grades.Exact.Base T Op n code code-injective

------------------------------------------------------------------------
-- Arithmetic

private
  variable
    p q d e : Carrier

  ≮⇒≥ : ¬ (p <ᴰ d) → d ≤ᴰ p
  ≮⇒≥ {p} {d} ¬p with d ≤ᴰ? p
  ... | yes r = r
  ... | no ¬r = ⊥-elim (¬p ¬r)

  -- below a sum, past its first summand: below the second, after it

  ∸-<-intro : d ≤ᴰ p → p <ᴰ d +ᴰ e → p ∸ᴰ d <ᴰ e
  ∸-<-intro {d} {p} r s t =
    s (≤ᴰ-trans (+ᴰ-monoʳ-≤ d t) (≤ᴰ-reflexive (+-∸ r)))

  ∸-<-elim : d ≤ᴰ p → p ∸ᴰ d <ᴰ e → p <ᴰ d +ᴰ e
  ∸-<-elim {d} {p} {e} r s t =
    s (+ᴰ-cancelˡ-≤ d (≤ᴰ-trans t (≤ᴰ-reflexive (sym (+-∸ r)))))

  -- the sum is not below its first summand

  ≮-+ : ¬ (d +ᴰ e <ᴰ d)
  ≮-+ {d} {e} r = r (≤ᴰ-+ d e)

------------------------------------------------------------------------
-- Labels

data Label : Set where
  bud : OpSet → Label
  opl : Op → Carrier → D⁺ → Label

infix 4 _≤ˡ_

data _≤ˡ_ : Label → Label → Set where
  bud≤bud : ∀ {S S′} → S ⊆ S′ → bud S ≤ˡ bud S′
  opl≤opl : ∀ {o δ d} → opl o δ d ≤ˡ opl o δ d
  opl≤bud : ∀ {o δ d S} → code o ∈ S → opl o δ d ≤ˡ bud S

≤ˡ-refl : ∀ {ℓ} → ℓ ≤ˡ ℓ
≤ˡ-refl {bud S}     = bud≤bud ⊆-refl
≤ˡ-refl {opl o δ d} = opl≤opl

≤ˡ-reflexive : ∀ {ℓ ℓ′} → ℓ ≡ ℓ′ → ℓ ≤ˡ ℓ′
≤ˡ-reflexive refl = ≤ˡ-refl

≤ˡ-trans : ∀ {ℓ ℓ′ ℓ″} → ℓ ≤ˡ ℓ′ → ℓ′ ≤ˡ ℓ″ → ℓ ≤ˡ ℓ″
≤ˡ-trans (bud≤bud a) (bud≤bud b) = bud≤bud (⊆-trans a b)
≤ˡ-trans opl≤opl     r           = r
≤ˡ-trans (opl≤bud a) (bud≤bud b) = opl≤bud (b a)

≤ˡ-antisym : ∀ {ℓ ℓ′} → ℓ ≤ˡ ℓ′ → ℓ′ ≤ˡ ℓ → ℓ ≡ ℓ′
≤ˡ-antisym (bud≤bud a) (bud≤bud b) = cong bud (⊆-antisym a b)
≤ˡ-antisym opl≤opl     _           = refl

-- the label of an item at an instant inside it

labᵢ : Item → Carrier → Label
labᵢ (op o d) p = opl o p d
labᵢ (st d S) p = bud S

------------------------------------------------------------------------
-- The labelling of a word

lab : Word → Carrier → Label
lab-at : (i : Item) → Word → (p : Carrier) → Dec (p <ᴰ len i) → Label

lab []      p = bud Data.Fin.Subset.⊥
lab (i ∷ w) p = lab-at i w p (p <ᴰ? len i)

lab-at i w p (yes _) = labᵢ i p
lab-at i w p (no _)  = lab w (p ∸ᴰ len i)

-- inside the first item, and past it

lab-here : ∀ {i w p} → p <ᴰ len i → lab (i ∷ w) p ≡ labᵢ i p
lab-here {i} {w} {p} r = case (p <ᴰ? len i)
  where
    case : (c : Dec (p <ᴰ len i)) → lab-at i w p c ≡ labᵢ i p
    case (yes _) = refl
    case (no ¬r) = ⊥-elim (¬r r)

lab-there : ∀ {i w p} → ¬ (p <ᴰ len i) → lab (i ∷ w) p ≡ lab w (p ∸ᴰ len i)
lab-there {i} {w} {p} ¬r = case (p <ᴰ? len i)
  where
    case : (c : Dec (p <ᴰ len i)) → lab-at i w p c ≡ lab w (p ∸ᴰ len i)
    case (yes r) = ⊥-elim (¬r r)
    case (no _)  = refl

lab-skip : ∀ i w q → lab (i ∷ w) (len i +ᴰ q) ≡ lab w q
lab-skip i w q = trans (lab-there (≮-+ {len i} {q})) (cong (lab w) (m+n∸m (len i) q))

-- the labelling sees the tail only through its labels

lab-cong : ∀ i {u v} → (∀ q → lab u q ≡ lab v q) → ∀ p → lab (i ∷ u) p ≡ lab (i ∷ v) p
lab-cong i {u} {v} h p = case (p <ᴰ? len i)
  where
    case : (c : Dec (p <ᴰ len i)) → lab-at i u p c ≡ lab-at i v p c
    case (yes _) = refl
    case (no _)  = h (p ∸ᴰ len i)

------------------------------------------------------------------------
-- Merging is invisible to the labelling

lab-merge : ∀ d e S w p → lab (st (d +⁺ e) S ∷ w) p ≡ lab (st d S ∷ st e S ∷ w) p
lab-merge d e S w p = case (p <ᴰ? ∣ d ∣⁺)
  where
    case : Dec (p <ᴰ ∣ d ∣⁺) → lab (st (d +⁺ e) S ∷ w) p ≡ lab (st d S ∷ st e S ∷ w) p
    case (yes r) =
      trans (lab-here {st (d +⁺ e) S} (<-≤-trans r (≤ᴰ-+ ∣ d ∣⁺ ∣ e ∣⁺)))
            (sym (lab-here {st d S} r))
    case (no ¬r) = case′ (p ∸ᴰ ∣ d ∣⁺ <ᴰ? ∣ e ∣⁺)
      where
        r = ≮⇒≥ ¬r
        case′ : Dec (p ∸ᴰ ∣ d ∣⁺ <ᴰ ∣ e ∣⁺)
              → lab (st (d +⁺ e) S ∷ w) p ≡ lab (st d S ∷ st e S ∷ w) p
        case′ (yes s) =
          trans (lab-here {st (d +⁺ e) S} (∸-<-elim r s))
                (sym (trans (lab-there {st d S} ¬r) (lab-here {st e S} s)))
        case′ (no ¬s) =
          trans (lab-there {st (d +⁺ e) S} (λ t → ¬s (∸-<-intro r t)))
                (sym (trans (lab-there {st d S} ¬r)
                     (trans (lab-there {st e S} ¬s)
                            (cong (lab w) (∸-+-assoc p ∣ d ∣⁺ ∣ e ∣⁺)))))

lab-◂ : ∀ i w p → lab (i ◂ w) p ≡ lab (i ∷ w) p
lab-◂ (op o d) w             p = refl
lab-◂ (st d S) []            p = refl
lab-◂ (st d S) (op o e ∷ w)  p = refl
lab-◂ (st d S) (st e S′ ∷ w) p with S ≟ˢ S′
... | yes refl = lab-merge d e S w p
... | no _     = refl

-- so sequencing is labelled as concatenation

lab-∙ : ∀ x y p → lab (x ∙ y) p ≡ lab (x ++ y) p
lab-∙ []      y p = refl
lab-∙ (i ∷ x) y p = trans (lab-◂ i (x ∙ y) p) (lab-cong i (lab-∙ x y) p)

lab-++ˡ : ∀ x y {p} → p <ᴰ dur x → lab (x ++ y) p ≡ lab x p
lab-++ˡ []      y r = ⊥-elim (r (0ᴰ-least _))
lab-++ˡ (i ∷ x) y {p} r = case (p <ᴰ? len i)
  where
    case : (c : Dec (p <ᴰ len i)) → lab-at i (x ++ y) p c ≡ lab-at i x p c
    case (yes _) = refl
    case (no ¬s) = lab-++ˡ x y (∸-<-intro (≮⇒≥ ¬s) r)

lab-++ʳ : ∀ x y {p} → ¬ (p <ᴰ dur x) → lab (x ++ y) p ≡ lab y (p ∸ᴰ dur x)
lab-++ʳ []      y {p} r = cong (lab y) (sym (∸-0 p))
lab-++ʳ (i ∷ x) y {p} r =
  trans (lab-there {i} ¬s)
        (trans (lab-++ʳ x y (λ t → r (∸-<-elim s′ t)))
               (cong (lab y) (∸-+-assoc p (len i) (dur x))))
  where
    s′ : len i ≤ᴰ p
    s′ = ≤ᴰ-trans (≤ᴰ-+ (len i) (dur x)) (≮⇒≥ r)
    ¬s : ¬ (p <ᴰ len i)
    ¬s t = t s′

------------------------------------------------------------------------
-- The order

infix 4 _⊑_

record _⊑_ (x y : Word) : Set where
  constructor fits
  field
    ⊑-dur : dur x ≡ dur y
    ⊑-lab : ∀ p → p <ᴰ dur y → lab x p ≤ˡ lab y p

open _⊑_ public

⊑-refl : ∀ {x} → x ⊑ x
⊑-refl = fits refl (λ _ _ → ≤ˡ-refl)

⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
⊑-trans (fits e h) (fits e′ h′) =
  fits (trans e e′)
       (λ p r → ≤ˡ-trans (h p (subst (p <ᴰ_) (sym e′) r)) (h′ p r))

-- sequencing is monotone

⊑-∙ : ∀ {x x′ y y′} → x ⊑ x′ → y ⊑ y′ → x ∙ y ⊑ x′ ∙ y′
⊑-∙ {x} {x′} {y} {y′} (fits e h) (fits e′ h′) =
  fits (trans (dur-∙ x y) (trans (cong₂ _+ᴰ_ e e′) (sym (dur-∙ x′ y′)))) at
  where
    at : ∀ p → p <ᴰ dur (x′ ∙ y′) → lab (x ∙ y) p ≤ˡ lab (x′ ∙ y′) p
    at p r = subst₂ _≤ˡ_ (sym (lab-∙ x y p)) (sym (lab-∙ x′ y′ p)) (case (p <ᴰ? dur x′))
      where
        r′ : p <ᴰ dur x′ +ᴰ dur y′
        r′ = subst (p <ᴰ_) (dur-∙ x′ y′) r
        case : Dec (p <ᴰ dur x′) → lab (x ++ y) p ≤ˡ lab (x′ ++ y′) p
        case (yes s) =
          subst₂ _≤ˡ_ (sym (lab-++ˡ x y (subst (p <ᴰ_) (sym e) s)))
                      (sym (lab-++ˡ x′ y′ s)) (h p s)
        case (no ¬s) =
          subst₂ _≤ˡ_ (sym (trans (lab-++ʳ x y (subst (λ z → ¬ (p <ᴰ z)) (sym e) ¬s))
                                  (cong (λ z → lab y (p ∸ᴰ z)) e)))
                      (sym (lab-++ʳ x′ y′ ¬s))
                      (h′ (p ∸ᴰ dur x′) (∸-<-intro (≮⇒≥ ¬s) r′))

-- a word fits the empty word only if it is empty

⊑-ε : ∀ {x} → x ⊑ [] → x ≡ []
⊑-ε {[]}    _          = refl
⊑-ε {i ∷ x} (fits e _) = ⊥-elim (dur-pos i x (≤ᴰ-reflexive e))

------------------------------------------------------------------------
-- The generating instances

-- an operation fits a stretch of its running time admitting it

op⊑st : ∀ {o d S} → code o ∈ S → op o d ∷ [] ⊑ st d S ∷ []
op⊑st {o} {d} {S} a = fits refl at
  where
    at : ∀ p → p <ᴰ dur (st d S ∷ []) → lab (op o d ∷ []) p ≤ˡ lab (st d S ∷ []) p
    at p r = subst₂ _≤ˡ_ (sym (lab-here {op o d} r′)) (sym (lab-here {st d S} r′)) (opl≤bud a)
      where r′ = subst (p <ᴰ_) (+ᴰ-identityʳ ∣ d ∣⁺) r

-- a stretch fits one admitting more

st⊑st : ∀ {d S S′} → S ⊆ S′ → st d S ∷ [] ⊑ st d S′ ∷ []
st⊑st {d} {S} {S′} a = fits refl at
  where
    at : ∀ p → p <ᴰ dur (st d S′ ∷ []) → lab (st d S ∷ []) p ≤ˡ lab (st d S′ ∷ []) p
    at p r = subst₂ _≤ˡ_ (sym (lab-here {st d S} r′)) (sym (lab-here {st d S′} r′)) (bud≤bud a)
      where r′ = subst (p <ᴰ_) (+ᴰ-identityʳ ∣ d ∣⁺) r

------------------------------------------------------------------------
-- The labelling determines the normal form

private
  -- a stretch strictly shorter than the leading stretch of a word with
  -- the same labels has a neighbour labelled differently

  shorter : ∀ {d e S w v} → Apart (st d S) w → ∣ d ∣⁺ <ᴰ ∣ e ∣⁺
          → dur (st d S ∷ w) ≡ dur (st e S ∷ v)
          → (∀ p → p <ᴰ dur (st d S ∷ w) → lab (st d S ∷ w) p ≡ lab (st e S ∷ v) p)
          → ⊥
  shorter {d} {e} {S} {[]} {v} a r de h =
    <⇒≢ (<-≤-trans r (≤ᴰ-+ ∣ e ∣⁺ (dur v))) (sym (trans (sym de) (+ᴰ-identityʳ ∣ d ∣⁺)))
  shorter {d} {e} {S} {i ∷ w} {v} a r de h =
    mismatch i a (trans (sym (lab-here {i} {w} (len-pos i)))
                 (trans (sym (lab-skip (st d S) (i ∷ w) 0ᴰ))
                 (trans (cong (lab (st d S ∷ i ∷ w)) (+ᴰ-identityʳ ∣ d ∣⁺))
                 (trans (h ∣ d ∣⁺ (<-+ (dur-pos i w)))
                        (lab-here {st e S} r)))))
    where
      mismatch : ∀ j → Apart (st d S) (j ∷ w) → labᵢ j 0ᴰ ≡ bud S → ⊥
      mismatch (op _ _)  _ ()
      mismatch (st _ S″) a refl = a refl

  head-label : ∀ {i j w v}
             → (∀ p → p <ᴰ dur (i ∷ w) → lab (i ∷ w) p ≡ lab (j ∷ v) p)
             → labᵢ i 0ᴰ ≡ labᵢ j 0ᴰ
  head-label {i} {j} {w} {v} h =
    trans (sym (lab-here {i} {w} (len-pos i)))
          (trans (h 0ᴰ (dur-pos i w)) (lab-here {j} {v} (len-pos j)))

lab-determines : ∀ x y → Normal x → Normal y → dur x ≡ dur y
               → (∀ p → p <ᴰ dur x → lab x p ≡ lab y p) → x ≡ y
lab-determines []      []      _ _ _  _ = refl
lab-determines []      (j ∷ v) _ _ de _ = ⊥-elim (dur-pos j v (≤ᴰ-reflexive (sym de)))
lab-determines (i ∷ w) []      _ _ de _ = ⊥-elim (dur-pos i w (≤ᴰ-reflexive de))
lab-determines (i ∷ w) (j ∷ v) (a , nw) (b , nv) de h
  with same-head i j a b de h
  where
    same-head : ∀ i j → Apart i w → Apart j v → dur (i ∷ w) ≡ dur (j ∷ v)
              → (∀ p → p <ᴰ dur (i ∷ w) → lab (i ∷ w) p ≡ lab (j ∷ v) p) → i ≡ j
    same-head (op o d) (op o′ d′) _ _ _ h with head-label {op o d} {op o′ d′} {w} {v} h
    ... | refl = refl
    same-head (op o d) (st e S) _ _ _ h with head-label {op o d} {st e S} {w} {v} h
    ... | ()
    same-head (st d S) (op o e) _ _ _ h with head-label {st d S} {op o e} {w} {v} h
    ... | ()
    same-head (st d S) (st e S′) a b de h with head-label {st d S} {st e S′} {w} {v} h
    ... | refl with compare ∣ d ∣⁺ ∣ e ∣⁺
    ...   | tri≈ r = cong (λ z → st z S) (∣∣⁺-inj r)
    ...   | tri< r = ⊥-elim (shorter a r de h)
    ...   | tri> r = ⊥-elim (shorter b r (sym de) h′)
      where
        h′ : ∀ p → p <ᴰ dur (st e S ∷ v) → lab (st e S ∷ v) p ≡ lab (st d S ∷ w) p
        h′ p t = sym (h p (subst (p <ᴰ_) (sym de) t))
... | refl =
  cong (i ∷_) (lab-determines w v nw nv
                 (+ᴰ-cancelˡ (len i) de)
                 (λ q t → trans (sym (lab-skip i w q))
                          (trans (h (len i +ᴰ q) (+ᴰ-monoʳ-< (len i) t))
                                 (lab-skip i v q))))

-- so the order is antisymmetric on normal words

⊑-antisym : ∀ {x y} → Normal x → Normal y → x ⊑ y → y ⊑ x → x ≡ y
⊑-antisym {x} {y} nx ny (fits e h) (fits e′ h′) =
  lab-determines x y nx ny e
    (λ p r → ≤ˡ-antisym (h p (subst (p <ᴰ_) e r)) (h′ p r))

------------------------------------------------------------------------
-- Consequences

-- a product fits the empty word only if both factors are empty

⊑-ε-∙ˡ : ∀ {x y} → x ∙ y ⊑ [] → x ≡ []
⊑-ε-∙ˡ {x} r = ∙-conicalˡ x (⊑-ε r)

⊑-ε-∙ʳ : ∀ {x y} → x ∙ y ⊑ [] → y ≡ []
⊑-ε-∙ʳ {x} r = ∙-conicalʳ x (⊑-ε r)

-- a word and its normal form fit each other

private
  lab-++-[] : ∀ x {p} → p <ᴰ dur x → lab (x ∙ []) p ≡ lab x p
  lab-++-[] x {p} r = trans (lab-∙ x [] p) (lab-++ˡ x [] r)

  dur-[] : ∀ x → dur (x ∙ []) ≡ dur x
  dur-[] x = trans (dur-∙ x []) (+ᴰ-identityʳ (dur x))

⊑-normalise : ∀ {x} → x ⊑ x ∙ []
⊑-normalise {x} =
  fits (sym (dur-[] x))
       (λ p r → ≤ˡ-reflexive (sym (lab-++-[] x (subst (p <ᴰ_) (dur-[] x) r))))

normalise-⊑ : ∀ {x} → x ∙ [] ⊑ x
normalise-⊑ {x} = fits (dur-[] x) (λ p r → ≤ˡ-reflexive (lab-++-[] x r))

-- a strict wait fits a stretch of its length

wait⊑st : ∀ {d S} → st d Data.Fin.Subset.⊥ ∷ [] ⊑ st d S ∷ []
wait⊑st = st⊑st ⊥⊆
