------------------------------------------------------------------------
-- Moving within an operation of a word.                              --
--                                                                    --
-- Where a word is inside an operation, at an offset into it, the     --
-- offset is at most the instant and below the running time, the      --
-- instant lies within the word, and moving back or forward by some   --
-- time while staying inside the operation moves the offset alike.    --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)

module Syntax.Grades.Exact.Offsets
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Monus T
open import Syntax.Durations.Solver T using (solve; _⊜_; _⊕_)

open import Syntax.Grades.Exact.Base T Op n code code-injective
open import Syntax.Grades.Exact.Order T Op n code code-injective

private
  variable
    p q : Carrier

  ≮⇒≥ : ¬ (p <ᴰ q) → q ≤ᴰ p
  ≮⇒≥ {p} {q} ¬p with q ≤ᴰ? p
  ... | yes s = s
  ... | no ¬s = ⊥-elim (¬p ¬s)

  split : q ≤ᴰ p → Σ[ r ∈ Carrier ] p ≡ q +ᴰ r
  split r with diff r
  ... | x , e = x , sym e

  opl-inj : ∀ {o o′ δ δ′ d d′} → opl o δ d ≡ opl o′ δ′ d′ → (o ≡ o′) × (δ ≡ δ′) × (d ≡ d′)
  opl-inj refl = refl , refl , refl

-- the facts, by induction on the word; each splits on whether the
-- instant lies inside the first item, which it can only do when that
-- item is the operation

offset-≤ : ∀ x {q o δ d} → lab x q ≡ opl o δ d → δ ≤ᴰ q
offset-≤ []      ()
offset-≤ (i ∷ w) {q} h = case i (q <ᴰ? len i) h
  where
    case : ∀ i (c : Dec (q <ᴰ len i)) → lab-at i w q c ≡ opl _ _ _ → _ ≤ᴰ q
    case (op o′ d′) (yes _) refl = ≤ᴰ-refl
    case (st _ _)   (yes _) ()
    case i          (no ¬r) h′ = ≤ᴰ-trans (offset-≤ w h′) (∸-≤-self q (len i))

offset-< : ∀ x {q o δ d} → lab x q ≡ opl o δ d → δ <ᴰ ∣ d ∣⁺
offset-< []      ()
offset-< (i ∷ w) {q} h = case i (q <ᴰ? len i) h
  where
    case : ∀ i (c : Dec (q <ᴰ len i)) → lab-at i w q c ≡ opl _ _ _ → _ <ᴰ _
    case (op o′ d′) (yes r) refl = r
    case (st _ _)   (yes _) ()
    case i          (no ¬r) h′ = offset-< w h′

inside : ∀ x {q o δ d} → lab x q ≡ opl o δ d → q <ᴰ dur x
inside []      ()
inside (i ∷ w) {q} h = case (q <ᴰ? len i) h
  where
    case : (c : Dec (q <ᴰ len i)) → lab-at i w q c ≡ opl _ _ _ → q <ᴰ len i +ᴰ dur w
    case (yes r) _  = <-≤-trans r (≤ᴰ-+ (len i) (dur w))
    case (no ¬r) h′ = case′ (split (≮⇒≥ ¬r))
      where
        case′ : Σ[ r ∈ Carrier ] q ≡ len i +ᴰ r → q <ᴰ len i +ᴰ dur w
        case′ (r , e) =
          subst (_<ᴰ len i +ᴰ dur w) (sym e)
            (+ᴰ-monoʳ-< (len i)
              (inside w (subst (λ z → lab w z ≡ _) (trans (cong (_∸ᴰ len i) e) (m+n∸m (len i) r)) h′)))

-- moving forward inside an operation

forward : ∀ x {q o δ d e} → lab x q ≡ opl o δ d → δ +ᴰ e <ᴰ ∣ d ∣⁺
        → lab x (q +ᴰ e) ≡ opl o (δ +ᴰ e) d
forward []      () _
forward (i ∷ w) {q} {e = e} h s = case i (q <ᴰ? len i) h
  where
    case : ∀ i (c : Dec (q <ᴰ len i)) → lab-at i w q c ≡ opl _ _ _
         → lab (i ∷ w) (q +ᴰ e) ≡ opl _ (_ +ᴰ e) _
    case (op o′ d′) (yes r) refl = lab-here {op o′ d′} {w} s
    case (st _ _)   (yes _) ()
    case i          (no ¬r) h′ = case′ (split (≮⇒≥ ¬r))
      where
        case′ : Σ[ r ∈ Carrier ] q ≡ len i +ᴰ r → lab (i ∷ w) (q +ᴰ e) ≡ opl _ (_ +ᴰ e) _
        case′ (r , eq) =
          trans (cong (lab (i ∷ w)) (trans (cong (_+ᴰ e) eq) (+ᴰ-assoc (len i) r e)))
            (trans (lab-skip i w (r +ᴰ e))
                   (forward w (subst (λ z → lab w z ≡ _)
                                     (trans (cong (_∸ᴰ len i) eq) (m+n∸m (len i) r)) h′) s))

-- moving back inside an operation

backward : ∀ x {e q o δ d} → lab x (e +ᴰ q) ≡ opl o (e +ᴰ δ) d → lab x q ≡ opl o δ d
backward []      ()
backward (i ∷ w) {e} {q} {o} {δ} {d} h = case i (e +ᴰ q <ᴰ? len i) h
  where
    case : ∀ i (c : Dec (e +ᴰ q <ᴰ len i)) → lab-at i w (e +ᴰ q) c ≡ opl o (e +ᴰ δ) d
         → lab (i ∷ w) q ≡ opl o δ d
    case (op o′ d′) (yes r) h″ with opl-inj h″
    ... | refl , eδ , refl =
      trans (lab-here {op o′ d′} {w} (≤-<-trans (≤ᴰ-+ˡ q e) r))
            (cong (λ z → opl o′ z d′) (+ᴰ-cancelˡ e eδ))
    case (st _ _) (yes _) ()
    case i (no ¬r) h′ = case′ (split (≮⇒≥ ¬r))
      where
        case′ : Σ[ r ∈ Carrier ] e +ᴰ q ≡ len i +ᴰ r → lab (i ∷ w) q ≡ opl o δ d
        case′ (r , eq) = case″ (split e≤r)
          where
            h‴ : lab w r ≡ opl o (e +ᴰ δ) d
            h‴ = subst (λ z → lab w z ≡ _) (trans (cong (_∸ᴰ len i) eq) (m+n∸m (len i) r)) h′
            -- the operation started after the first item
            e≤r : e ≤ᴰ r
            e≤r = ≤ᴰ-trans (≤ᴰ-+ e δ) (offset-≤ w h‴)
            case″ : Σ[ t ∈ Carrier ] r ≡ e +ᴰ t → lab (i ∷ w) q ≡ opl o δ d
            case″ (t , et) =
              trans (cong (lab (i ∷ w)) qt)
                (trans (lab-skip i w t) (backward w (subst (λ z → lab w z ≡ _) et h‴)))
              where
                qt : q ≡ len i +ᴰ t
                qt = +ᴰ-cancelˡ e (trans eq (trans (cong (len i +ᴰ_) et)
                       (solve 3 (λ l e t → l ⊕ (e ⊕ t) ⊜ e ⊕ (l ⊕ t)) refl (len i) e t)))
