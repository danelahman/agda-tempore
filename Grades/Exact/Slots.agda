------------------------------------------------------------------------
-- Exact words in whole steps, as words over a finite alphabet.       --
--                                                                    --
-- In whole steps a word is a sequence of unit slots, each labelled   --
-- by what happens in it: a stretch admitting a set `S` (`inˢ S`), or --
-- an operation, by its code and whether the slot is its first and    --
-- its last (`opˢ c first last`). Slots are ordered as labels are,    --
-- operation slots matching only themselves, and the encoding `enc`   --
-- turns the fit order into slot-by-slot comparison:                  --
--                                                                    --
--   x ⊑ y   iff   enc x lies slot by slot below enc y                --
--                                                                    --
-- An operation of the lesser word facing one of the greater has the  --
-- same first and last slots, so it is the same operation, starting   --
-- and ending together. Concatenation is encoded as concatenation.    --
--                                                                    --
-- The slots are coded bijectively as the letters `Fin k`, for        --
-- `k = 2 ^ n + n * 4`.                                               --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

module Grades.Exact.Slots
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′) where

open import Data.Bool.Base using (Bool; true; false; T; _∧_; if_then_else_)
open import Data.Bool.Properties using (T-∧) renaming (_≟_ to _≟ᵇ_)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin.Base as Fin
open import Data.Fin.Base using (zero; suc; combine; remQuot; splitAt; join; _↑ˡ_; _↑ʳ_)
import Data.Fin.Properties as Fin
open import Data.Fin.Subset using (Subset; _∈_; _⊆_)
open import Data.Fin.Subset.Properties using (_∈?_; _⊆?_)
open import Data.List.Base using (List; []; _∷_; _++_; map; applyUpTo; length)
open import Data.List.Properties using (length-applyUpTo)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
import Data.List.Relation.Binary.Pointwise as Pointwise
open import Data.Nat.Base using (zero; suc; _+_; _*_; _^_; _≤_; _<_; z≤n; s≤s; _≡ᵇ_)
import Data.Nat.Properties as ℕ
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no; does)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Grades.Durations.Nat using (ℕᴰ; ℕᵀ)

open import Grades.Exact.Base ℕᵀ Op n code code-injective
open import Grades.Exact.Order ℕᵀ Op n code code-injective
open import Grades.Exact.Offsets ℕᵀ Op n code code-injective
open import Grades.Durations.Monus ℕᵀ using (_<ᴰ_; _∸ᴰ_; m+n∸m)

------------------------------------------------------------------------
-- Slots and their order

data Slot : Set where
  inˢ : OpSet → Slot
  opˢ : Fin n → Bool → Bool → Slot

infix 4 _≤ˢ_

_≤ˢ_ : Slot → Slot → Bool
inˢ S     ≤ˢ inˢ S′      = does (S ⊆? S′)
opˢ c f l ≤ˢ opˢ c′ f′ l′ = does (c Fin.≟ c′) ∧ does (f ≟ᵇ f′) ∧ does (l ≟ᵇ l′)
opˢ c _ _ ≤ˢ inˢ S       = does (c ∈? S)
inˢ _     ≤ˢ opˢ _ _ _   = false

private
  T-does : ∀ {P : Set} (d : Dec P) → T (does d) → P
  T-does (yes p) _ = p

  does-T : ∀ {P : Set} (d : Dec P) → P → T (does d)
  does-T (yes _) _ = _
  does-T (no ¬p) p = ¬p p

≤ˢ-refl : ∀ s → T (s ≤ˢ s)
≤ˢ-refl (inˢ S)     = does-T (S ⊆? S) (λ x → x)
≤ˢ-refl (opˢ c f l) =
  Equivalence.from T-∧ (does-T (c Fin.≟ c) refl ,
    Equivalence.from T-∧ (does-T (f ≟ᵇ f) refl , does-T (l ≟ᵇ l) refl))

private
  opˢ-≤ : ∀ {c f l c′ f′ l′} → T (opˢ c f l ≤ˢ opˢ c′ f′ l′) → c ≡ c′ × f ≡ f′ × l ≡ l′
  opˢ-≤ {c} {f} {l} {c′} {f′} {l′} t with Equivalence.to T-∧ t
  ... | t₁ , t₂ with Equivalence.to T-∧ t₂
  ...   | t₃ , t₄ = T-does (c Fin.≟ c′) t₁ , T-does (f ≟ᵇ f′) t₃ , T-does (l ≟ᵇ l′) t₄

≤ˢ-trans : ∀ s s′ s″ → T (s ≤ˢ s′) → T (s′ ≤ˢ s″) → T (s ≤ˢ s″)
≤ˢ-trans (inˢ S)     (inˢ S′)       (inˢ S″)        a b =
  does-T (S ⊆? S″) (λ x → T-does (S′ ⊆? S″) b (T-does (S ⊆? S′) a x))
≤ˢ-trans (opˢ c f l) (opˢ c′ f′ l′) s″ a b with opˢ-≤ {c} {f} {l} {c′} {f′} {l′} a
... | refl , refl , refl = b
≤ˢ-trans (opˢ c f l) (inˢ S′)       (inˢ S″)        a b =
  does-T (c ∈? S″) (T-does (S′ ⊆? S″) b (T-does (c ∈? S′) a))
≤ˢ-trans (inˢ _)     (opˢ _ _ _)    _               () _
≤ˢ-trans (inˢ _)     (inˢ _)        (opˢ _ _ _)     _ ()
≤ˢ-trans (opˢ _ _ _) (inˢ _)        (opˢ _ _ _)     _ ()

------------------------------------------------------------------------
-- The slots of a word

slotOf : Label → Slot
slotOf (bud S)     = inˢ S
slotOf (opl o δ d) = opˢ (code o) (δ ≡ᵇ 0) (suc δ ≡ᵇ ∣ d ∣⁺)

enc : Word → List Slot
enc x = applyUpTo (λ p → slotOf (lab x p)) (dur x)

-- labels in order give slots in order

≤ˡ⇒≤ˢ : ∀ {ℓ ℓ′} → ℓ ≤ˡ ℓ′ → T (slotOf ℓ ≤ˢ slotOf ℓ′)
≤ˡ⇒≤ˢ (bud≤bud {S} {S′} a)   = does-T (S ⊆? S′) a
≤ˡ⇒≤ˢ (opl≤opl {o} {δ} {d})  = ≤ˢ-refl (opˢ (code o) (δ ≡ᵇ 0) (suc δ ≡ᵇ ∣ d ∣⁺))
≤ˡ⇒≤ˢ (opl≤bud {o} {S = S} a) = does-T (code o ∈? S) a

------------------------------------------------------------------------
-- Lists of slots indexed by the instants

private
  <⇒<ᴰ : ∀ {p q} → p < q → p <ᴰ q
  <⇒<ᴰ = ℕ.<⇒≱

  <ᴰ⇒< : ∀ {p q} → p <ᴰ q → p < q
  <ᴰ⇒< = ℕ.≰⇒>

  pointwise⁺ : ∀ {A B : Set} {R : A → B → Set} (f : ℕ → A) (g : ℕ → B) m
             → (∀ p → p < m → R (f p) (g p)) → Pointwise R (applyUpTo f m) (applyUpTo g m)
  pointwise⁺ f g zero    h = []
  pointwise⁺ f g (suc m) h = h 0 (s≤s z≤n) ∷ pointwise⁺ (λ p → f (suc p)) (λ p → g (suc p)) m
                                               (λ p r → h (suc p) (s≤s r))

  pointwise⁻ : ∀ {A B : Set} {R : A → B → Set} (f : ℕ → A) (g : ℕ → B) m
             → Pointwise R (applyUpTo f m) (applyUpTo g m) → ∀ p → p < m → R (f p) (g p)
  pointwise⁻ f g (suc m) (r ∷ rs) zero    _        = r
  pointwise⁻ f g (suc m) (r ∷ rs) (suc p) (s≤s lt) =
    pointwise⁻ (λ p → f (suc p)) (λ p → g (suc p)) m rs p lt

  applyUpTo-cong : ∀ {A : Set} (f g : ℕ → A) m → (∀ p → p < m → f p ≡ g p)
                 → applyUpTo f m ≡ applyUpTo g m
  applyUpTo-cong f g zero    h = refl
  applyUpTo-cong f g (suc m) h =
    cong₂ _∷_ (h 0 (s≤s z≤n))
              (applyUpTo-cong (λ p → f (suc p)) (λ p → g (suc p)) m (λ p r → h (suc p) (s≤s r)))

  applyUpTo-+ : ∀ {A : Set} (f : ℕ → A) a b
              → applyUpTo f (a + b) ≡ applyUpTo f a ++ applyUpTo (λ q → f (a + q)) b
  applyUpTo-+ f zero    b = refl
  applyUpTo-+ f (suc a) b = cong (f 0 ∷_) (applyUpTo-+ (λ p → f (suc p)) a b)

-- concatenation is encoded as concatenation

lab-++ʳ″ : ∀ x y q → lab (x ++ y) (dur x + q) ≡ lab y q
lab-++ʳ″ x y q = trans (lab-++ʳ x y (λ r → r (ℕ.m≤m+n (dur x) q))) (cong (lab y) (m+n∸m (dur x) q))

enc-++ : ∀ x y → enc (x ++ y) ≡ enc x ++ enc y
enc-++ x y =
  trans (cong (applyUpTo (λ p → slotOf (lab (x ++ y) p))) (dur-++ x y))
  (trans (applyUpTo-+ (λ p → slotOf (lab (x ++ y) p)) (dur x) (dur y))
         (cong₂ _++_
           (applyUpTo-cong _ _ (dur x) (λ p r → cong slotOf (lab-++ˡ x y (<⇒<ᴰ r))))
           (applyUpTo-cong _ _ (dur y) (λ q r → cong slotOf (lab-++ʳ″ x y q)))))

------------------------------------------------------------------------
-- Fit is slot-by-slot comparison

Below : List Slot → List Slot → Set
Below = Pointwise (λ s s′ → T (s ≤ˢ s′))

private
  opl-inj : ∀ {o o′ δ δ′ d d′} → opl o δ d ≡ opl o′ δ′ d′ → (o ≡ o′) × (δ ≡ δ′) × (d ≡ d′)
  opl-inj refl = refl , refl , refl

  -- facing operations have the same slots

  OpAgree : Word → Word → Set
  OpAgree x y = ∀ p {o δ d o′ δ′ d′} → lab x p ≡ opl o δ d → lab y p ≡ opl o′ δ′ d′
              → slotOf (opl o δ d) ≡ slotOf (opl o′ δ′ d′)

  agree-sym : ∀ {x y} → OpAgree x y → OpAgree y x
  agree-sym a p hy hx = sym (a p hx hy)

  true≢false : true ≡ false → ⊥
  true≢false ()

  opˢ-inj : ∀ {c f l c′ f′ l′} → opˢ c f l ≡ opˢ c′ f′ l′ → c ≡ c′ × f ≡ f′ × l ≡ l′
  opˢ-inj refl = refl , refl , refl

  ≡ᵇ-refl : ∀ k → (k ≡ᵇ k) ≡ true
  ≡ᵇ-refl zero    = refl
  ≡ᵇ-refl (suc k) = ≡ᵇ-refl k

  -- two operations facing each other share their offset ...

  same-offset : ∀ x y {p o δ δ′ d d′} → OpAgree x y
              → lab x p ≡ opl o δ d → lab y p ≡ opl o δ′ d′ → δ ≤ δ′ → δ ≡ δ′
  same-offset x y {p} {o} {δ} {δ′} {d} {d′} ag hx hy le with ℕ.m≤n⇒∃[o]m+o≡n le
  ... | b , refl with ℕ.m≤n⇒∃[o]m+o≡n (offset-≤ x hx)
  ...   | q , refl = case b refl
    where
      hx′ : lab x q ≡ opl o 0 d
      hx′ = backward x (trans hx (cong (λ z → opl o z d) (sym (ℕ.+-identityʳ δ))))
      hy′ : lab y q ≡ opl o b d′
      hy′ = backward y hy
      case : ∀ b′ → b′ ≡ b → δ ≡ δ + b
      case zero    e = sym (trans (cong (δ +_) (sym e)) (ℕ.+-identityʳ δ))
      case (suc c) e with opˢ-inj (ag q hx′ hy′)
      ... | _ , f , _ = ⊥-elim (true≢false (trans f (cong (_≡ᵇ 0) (sym e))))

  -- ... and their running time

  same-length : ∀ x y {p o δ d d′} → OpAgree x y
              → lab x p ≡ opl o δ d → lab y p ≡ opl o δ d′ → ∣ d ∣⁺ ≤ ∣ d′ ∣⁺ → d ≡ d′
  same-length x y {p} {o} {δ} {d} {d′} ag hx hy le
    with ℕ.m≤n⇒∃[o]m+o≡n (<ᴰ⇒< (offset-< x hx))
  ... | m , dm = ∣∣⁺-inj (sym last-y)
    where
      -- the last slot of the operation of `x`
      δm<d : δ + m <ᴰ ∣ d ∣⁺
      δm<d = <⇒<ᴰ (subst (δ + m <_) dm (subst (_≤ suc δ + m) refl ℕ.≤-refl))
      δm<d′ : δ + m <ᴰ ∣ d′ ∣⁺
      δm<d′ = <⇒<ᴰ (ℕ.<-≤-trans (<ᴰ⇒< δm<d) le)
      hx′ : lab x (p + m) ≡ opl o (δ + m) d
      hx′ = forward x hx δm<d
      hy′ : lab y (p + m) ≡ opl o (δ + m) d′
      hy′ = forward y hy δm<d′
      last-x : (suc (δ + m) ≡ᵇ ∣ d ∣⁺) ≡ true
      last-x = subst (λ z → (suc (δ + m) ≡ᵇ z) ≡ true) dm (≡ᵇ-refl (suc (δ + m)))
      last-y : ∣ d′ ∣⁺ ≡ ∣ d ∣⁺
      last-y with opˢ-inj (ag (p + m) hx′ hy′)
      ... | _ , _ , l =
        trans (sym (ℕ.≡ᵇ⇒≡ (suc (δ + m)) ∣ d′ ∣⁺ (subst T (sym (trans (sym l) last-x)) _))) dm

  -- so slots in order everywhere give labels in order

  label-≤ : ∀ x y {p} → OpAgree x y
          → ∀ ℓ ℓ′ → lab x p ≡ ℓ → lab y p ≡ ℓ′ → T (slotOf ℓ ≤ˢ slotOf ℓ′) → ℓ ≤ˡ ℓ′
  label-≤ x y ag (bud S)     (bud S′)      _  _  t = bud≤bud (T-does (S ⊆? S′) t)
  label-≤ x y ag (opl o δ d) (bud S)       _  _  t = opl≤bud (T-does (code o ∈? S) t)
  label-≤ x y ag (bud S)     (opl _ _ _)   _  _  ()
  label-≤ x y ag (opl o δ d) (opl o′ δ′ d′) hx hy t with opˢ-≤ {code o} {δ ≡ᵇ 0} {suc δ ≡ᵇ ∣ d ∣⁺} {code o′} {δ′ ≡ᵇ 0} {suc δ′ ≡ᵇ ∣ d′ ∣⁺} t
  ... | c , _ , _ with code-injective c
  ... | refl with offsets (ℕ.≤-total δ δ′)
    where
      offsets : δ ≤ δ′ ⊎ δ′ ≤ δ → δ ≡ δ′
      offsets (inj₁ le) = same-offset x y ag hx hy le
      offsets (inj₂ le) = sym (same-offset y x (agree-sym {x} {y} ag) hy hx le)
  ...   | refl with lengths (ℕ.≤-total ∣ d ∣⁺ ∣ d′ ∣⁺)
    where
      lengths : ∣ d ∣⁺ ≤ ∣ d′ ∣⁺ ⊎ ∣ d′ ∣⁺ ≤ ∣ d ∣⁺ → d ≡ d′
      lengths (inj₁ le) = same-length x y ag hx hy le
      lengths (inj₂ le) = sym (same-length y x (agree-sym {x} {y} ag) hy hx le)
  ...     | refl = opl≤opl

-- the encoding of the order

enc-⊑ : ∀ {x y} → x ⊑ y → Below (enc x) (enc y)
enc-⊑ {x} {y} (fits e h) =
  subst (λ m → Below (enc x) (applyUpTo (λ p → slotOf (lab y p)) m)) e
    (pointwise⁺ _ _ (dur x)
      (λ p r → ≤ˡ⇒≤ˢ (h p (<⇒<ᴰ (subst (p <_) e r)))))

⊑-enc : ∀ {x y} → Below (enc x) (enc y) → x ⊑ y
⊑-enc {x} {y} b = fits e at
  where
    e : dur x ≡ dur y
    e = trans (sym (length-applyUpTo _ (dur x)))
              (trans (Pointwise.Pointwise-length b) (length-applyUpTo _ (dur y)))
    sw : ∀ p → p < dur x → T (slotOf (lab x p) ≤ˢ slotOf (lab y p))
    sw = pointwise⁻ _ _ (dur x)
           (subst (λ m → Below (enc x) (applyUpTo (λ p → slotOf (lab y p)) m)) (sym e) b)
    ag : OpAgree x y
    ag p {o} {δ} {d} {o′} {δ′} {d′} hx hy with opˢ-≤ (subst₂ (λ ℓ ℓ′ → T (slotOf ℓ ≤ˢ slotOf ℓ′)) hx hy
                                                      (sw p (<ᴰ⇒< (inside x hx))))
    ... | c , f , l = cong₃ opˢ c f l
    at : ∀ p → p <ᴰ dur y → lab x p ≤ˡ lab y p
    at p r = label-≤ x y ag (lab x p) (lab y p) refl refl
               (sw p (<ᴰ⇒< (subst (p <ᴰ_) (sym e) r)))

-- fit is slot-by-slot comparison

⊑⇔enc : ∀ {x y} → x ⊑ y ⇔ Below (enc x) (enc y)
⊑⇔enc = mk⇔ enc-⊑ ⊑-enc

------------------------------------------------------------------------
-- Slots as letters

private
  bit : Bool → Fin 2
  bit false = zero
  bit true  = suc zero

  unbit : Fin 2 → Bool
  unbit zero       = false
  unbit (suc zero) = true

  unbit-bit : ∀ b → unbit (bit b) ≡ b
  unbit-bit false = refl
  unbit-bit true  = refl

  bit-unbit : ∀ i → bit (unbit i) ≡ i
  bit-unbit zero       = refl
  bit-unbit (suc zero) = refl

  toF : ∀ {m} → Vec Bool m → Fin (2 ^ m)
  toF []      = zero
  toF (b ∷ v) = combine (bit b) (toF v)

  fromF : ∀ m → Fin (2 ^ m) → Vec Bool m
  fromF zero    _ = []
  fromF (suc m) i = unbit (proj₁ (remQuot {2} (2 ^ m) i)) ∷ fromF m (proj₂ (remQuot {2} (2 ^ m) i))

  fromF-toF : ∀ {m} (v : Vec Bool m) → fromF m (toF v) ≡ v
  fromF-toF []      = refl
  fromF-toF {suc m} (b ∷ v) =
    trans (cong (λ p → unbit (proj₁ p) ∷ fromF m (proj₂ p)) (Fin.remQuot-combine {2} {2 ^ m} (bit b) (toF v)))
          (cong₂ _∷_ (unbit-bit b) (fromF-toF v))

  toF-fromF : ∀ m (i : Fin (2 ^ m)) → toF {m} (fromF m i) ≡ i
  toF-fromF zero    zero = refl
  toF-fromF (suc m) i =
    trans (cong₂ combine (bit-unbit (proj₁ (remQuot {2} (2 ^ m) i))) (toF-fromF m (proj₂ (remQuot {2} (2 ^ m) i))))
          (Fin.combine-remQuot {2} (2 ^ m) i)

  flags : Bool → Bool → Fin 4
  flags f l = combine (bit f) (bit l)

  unflags : Fin 4 → Bool × Bool
  unflags i = unbit (proj₁ (remQuot {2} 2 i)) , unbit (proj₂ (remQuot {2} 2 i))

  unflags-flags : ∀ f l → unflags (flags f l) ≡ (f , l)
  unflags-flags f l =
    trans (cong (λ p → unbit (proj₁ p) , unbit (proj₂ p)) (Fin.remQuot-combine {2} {2} (bit f) (bit l)))
          (cong₂ _,_ (unbit-bit f) (unbit-bit l))

  flags-unflags : ∀ i → uncurry flags (unflags i) ≡ i
  flags-unflags i =
    trans (cong₂ combine (bit-unbit (proj₁ (remQuot {2} 2 i))) (bit-unbit (proj₂ (remQuot {2} 2 i))))
          (Fin.combine-remQuot {2} 2 i)

  decode-op : Fin (n * 4) → Slot
  decode-op j = opˢ (proj₁ (remQuot {n} 4 j)) (proj₁ (unflags (proj₂ (remQuot {n} 4 j))))
                    (proj₂ (unflags (proj₂ (remQuot {n} 4 j))))

  decode-sum : Fin (2 ^ n) ⊎ Fin (n * 4) → Slot
  decode-sum (inj₁ j) = inˢ (fromF n j)
  decode-sum (inj₂ j) = decode-op j

-- the number of letters

k : ℕ
k = 2 ^ n + n * 4

encode : Slot → Fin k
encode (inˢ S)     = toF S ↑ˡ (n * 4)
encode (opˢ c f l) = (2 ^ n) ↑ʳ combine c (flags f l)

decode : Fin k → Slot
decode i = decode-sum (splitAt (2 ^ n) i)

decode-encode : ∀ s → decode (encode s) ≡ s
decode-encode (inˢ S) =
  trans (cong decode-sum (Fin.splitAt-↑ˡ (2 ^ n) (toF S) (n * 4))) (cong inˢ (fromF-toF S))
decode-encode (opˢ c f l) =
  trans (cong decode-sum (Fin.splitAt-↑ʳ (2 ^ n) (n * 4) (combine c (flags f l))))
    (trans (cong (λ p → opˢ (proj₁ p) (proj₁ (unflags (proj₂ p))) (proj₂ (unflags (proj₂ p))))
                 (Fin.remQuot-combine {n} {4} c (flags f l)))
           (cong (λ p → opˢ c (proj₁ p) (proj₂ p)) (unflags-flags f l)))

private
  encode-sum : Fin (2 ^ n) ⊎ Fin (n * 4) → Fin k
  encode-sum = join (2 ^ n) (n * 4)

  encode-decode-sum : ∀ x → encode (decode-sum x) ≡ encode-sum x
  encode-decode-sum (inj₁ j) = cong (_↑ˡ (n * 4)) (toF-fromF n j)
  encode-decode-sum (inj₂ j) =
    cong (λ z → (2 ^ n) ↑ʳ z)
      (trans (cong (combine (proj₁ (remQuot {n} 4 j))) (flags-unflags (proj₂ (remQuot {n} 4 j))))
             (Fin.combine-remQuot {n} 4 j))

encode-decode : ∀ i → encode (decode i) ≡ i
encode-decode i = trans (encode-decode-sum (splitAt (2 ^ n) i)) (Fin.join-splitAt (2 ^ n) (n * 4) i)

-- the order on letters

_≤ᶠ_ : Fin k → Fin k → Bool
a ≤ᶠ b = decode a ≤ˢ decode b

≤ᶠ-refl : ∀ a → T (a ≤ᶠ a)
≤ᶠ-refl a = ≤ˢ-refl (decode a)

≤ᶠ-trans : ∀ a b c → T (a ≤ᶠ b) → T (b ≤ᶠ c) → T (a ≤ᶠ c)
≤ᶠ-trans a b c = ≤ˢ-trans (decode a) (decode b) (decode c)

-- the strict wait, as a letter

tick : Fin k
tick = encode (inˢ Data.Fin.Subset.⊥)

-- words as words of letters

encᶠ : Word → List (Fin k)
encᶠ x = map encode (enc x)
