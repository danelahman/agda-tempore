------------------------------------------------------------------------
-- The joint walk is complete: a common word gives a walk.            --
--                                                                    --
-- Let `x` fit an instance `y` of a lower word and an instance `z` of --
-- an upper word. At every instant the labels of `y` and `z` lie      --
-- above that of `x`, so they meet: an operation of one lies inside a --
-- stretch of the other admitting it, and two operations at one       --
-- instant are the same, at the same offset, so they start and end    --
-- together. The walk follows the pieces of `y` and `z` in time,      --
-- stopping where either ends, comparing where the two current pieces --
-- end, and reading the labels at the instant the later of them       --
-- started.                                                           --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Joint.Complete
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Subset using (_∈_)
open import Data.Unit using (tt)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function.Bundles using (_⇔_; mk⇔)

open import Grades.Durations.Monus T
open import Grades.Durations.Solver T using (solve; _⊜_; _⊕_)
open import Grades.Durations.Intervals.Dense T using (_∈ⁱ_)

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Order T Op n code code-injective
open import Grades.Exact.Pour T Op n code code-injective using (pour-⊑)
open import Grades.Exact.Expression T Op n code code-injective running
  using (Instance; upper; lower; End; _∈ᵉ_)
open import Grades.Exact.Letters T Op n code code-injective running
open import Grades.Exact.Positions T Op n code code-injective running
  using (At; at-st; at-op; at; dur-wordOf; sumᴰ-++; amts-++)
open import Grades.Exact.Joint T Op n code code-injective running

open RunningTimes.RunningTimes running using (rt; rt-pos)

------------------------------------------------------------------------
-- A common word

Common : Word′ lower → Word′ upper → Set
Common v w = Σ[ x ∈ Word ] (Σ[ y ∈ Word ] ⟦ v ⟧ʷ y × x ⊑ y) × (Σ[ z ∈ Word ] ⟦ w ⟧ʷ z × x ⊑ z)

-- a walk gives one

sound-common : ∀ {v w} → Walk v w sync → Common v w
sound-common {v} {w} j with sound j
... | x , y , z , iy , iz , p , q = x , (y , inst-⟦⟧ v iy , pour-⊑ p) , (z , inst-⟦⟧ w iz , pour-⊑ q)

------------------------------------------------------------------------
-- Arithmetic of the pieces

private
  σ : List (Piece Carrier) → Carrier
  σ ps = sumᴰ (amts ps)

  σ-snoc : ∀ ps p → σ (ps ++ p ∷ []) ≡ σ ps +ᴰ proj₂ p
  σ-snoc ps p =
    trans (cong sumᴰ (amts-++ ps (p ∷ [])))
          (trans (sumᴰ-++ (amts ps) (proj₂ p ∷ [])) (cong (σ ps +ᴰ_) (+ᴰ-identityʳ (proj₂ p))))

  σ-cons : ∀ ps p qs → σ (ps ++ p ∷ qs) ≡ σ ps +ᴰ (proj₂ p +ᴰ σ qs)
  σ-cons ps p qs = trans (cong sumᴰ (amts-++ ps (p ∷ qs))) (sumᴰ-++ (amts ps) (proj₂ p ∷ amts qs))

  snoc : ∀ {A : Set} (xs : List A) p ys → xs ++ p ∷ ys ≡ (xs ++ p ∷ []) ++ ys
  snoc xs p ys = sym (++-assoc xs (p ∷ []) ys)

  shift : ∀ {psd p psr y} → WordOf (psd ++ p ∷ psr) y → WordOf ((psd ++ p ∷ []) ++ psr) y
  shift {psd} {p} {psr} {y} = subst (λ l → WordOf l y) (snoc psd p psr)

  suffix : ∀ psd {psr y} → WordOf (psd ++ psr) y → Σ Word (WordOf psr)
  suffix []        w                = _ , w
  suffix (_ ∷ psd) (WordOf.op _ w)  = suffix psd w
  suffix (_ ∷ psd) (WordOf.st w)    = suffix psd w

  head-rt : ∀ {o τ ps y} → WordOf ((opk o , τ) ∷ ps) y → τ ∈ⁱ rt o
  head-rt (WordOf.op r _) = r

  ≮⇒≥ : ∀ {p d} → ¬ (p <ᴰ d) → d ≤ᴰ p
  ≮⇒≥ {p} {d} ¬p with d ≤ᴰ? p
  ... | yes r = r
  ... | no ¬r = ⊥-elim (¬p ¬r)

  ≮0 : ∀ {τ} → ¬ (0ᴰ <ᴰ τ) → τ ≡ 0ᴰ
  ≮0 = ≮0⇒≡0

  -- a piece of no length

  zero-adm : ∀ {s} {e : End s} {τ} → _∈ᵉ_ τ {s} e → ¬ (0ᴰ <ᴰ τ) → _∈ᵉ_ 0ᴰ {s} e
  zero-adm {s} {e} a ¬p = subst (λ t → _∈ᵉ_ t {s} e) (≮0⇒≡0 ¬p) a

  zero-step : ∀ psd p {c} → ¬ (0ᴰ <ᴰ proj₂ p) → σ psd ≡ c → σ (psd ++ p ∷ []) ≡ c
  zero-step psd p ¬p e =
    trans (σ-snoc psd p) (trans (cong (σ psd +ᴰ_) (≮0⇒≡0 ¬p)) (trans (+ᴰ-identityʳ _) e))

  -- the head letter admits the head piece

  adm-head : ∀ {s} {ℓ : Letter (End s)} {v p ps y} → Shape (ℓ ∷ v) (p ∷ ps) → WordOf (p ∷ ps) y
           → Adm ℓ (proj₂ p)
  adm-head (Shape.op _)   w = head-rt w
  adm-head (Shape.st a _) _ = a

  shape-tail : ∀ {s} {ℓ : Letter (End s)} {v p ps} → Shape (ℓ ∷ v) (p ∷ ps) → Shape v ps
  shape-tail (Shape.op sh)   = sh
  shape-tail (Shape.st _ sh) = sh

  -- instants and sums

  mid : ∀ {a b e} → a +ᴰ e ≡ b → b +ᴰ 0ᴰ ≡ a +ᴰ e
  mid ee = trans (+ᴰ-identityʳ _) (sym ee)

  mid′ : ∀ {a b e} → a +ᴰ e ≡ b → a +ᴰ e ≡ b +ᴰ 0ᴰ
  mid′ ee = trans ee (sym (+ᴰ-identityʳ _))

  +pos′ : ∀ {e τ} → 0ᴰ <ᴰ τ → 0ᴰ <ᴰ e +ᴰ τ
  +pos′ {e} {τ} p = <-≤-trans p (≤ᴰ-+ˡ τ e)

  step-on : ∀ A B b e → σ A +ᴰ e ≡ σ B → σ A +ᴰ (e +ᴰ proj₂ b) ≡ σ (B ++ b ∷ [])
  step-on A B b e ee =
    trans (sym (+ᴰ-assoc (σ A) e (proj₂ b))) (trans (cong (_+ᴰ proj₂ b) ee) (sym (σ-snoc B b)))

  meet-up : ∀ A a B b e → σ B +ᴰ e ≡ σ A → e +ᴰ proj₂ a ≡ proj₂ b → σ (A ++ a ∷ []) ≡ σ (B ++ b ∷ [])
  meet-up A a B b e ee eq =
    trans (σ-snoc A a)
      (trans (cong (_+ᴰ proj₂ a) (sym ee))
        (trans (+ᴰ-assoc (σ B) e (proj₂ a)) (trans (cong (σ B +ᴰ_) eq) (sym (σ-snoc B b)))))

  over : ∀ A B b e → σ B +ᴰ e ≡ σ A → e <ᴰ proj₂ b → σ A +ᴰ (proj₂ b ∸ᴰ e) ≡ σ (B ++ b ∷ [])
  over A B b e ee lt =
    trans (cong (_+ᴰ (proj₂ b ∸ᴰ e)) (sym ee))
      (trans (+ᴰ-assoc (σ B) e _) (trans (cong (σ B +ᴰ_) (+-∸ (<⇒≤ lt))) (sym (σ-snoc B b))))

  ∸-pos : ∀ {e τ} → e <ᴰ τ → 0ᴰ <ᴰ τ ∸ᴰ e
  ∸-pos {e} {τ} lt r = <⇒≢ lt (sym (trans (sym (+-∸ (<⇒≤ lt))) (trans (cong (e +ᴰ_) (≤0⇒≡0 r)) (+ᴰ-identityʳ e))))

  ∸-< : ∀ {e τ τ′} → e <ᴰ τ → τ <ᴰ e +ᴰ τ′ → τ ∸ᴰ e <ᴰ τ′
  ∸-< {e} {τ} {τ′} lt gt r = gt (≤ᴰ-trans (+ᴰ-monoʳ-≤ e r) (≤ᴰ-reflexive (+-∸ (<⇒≤ lt))))

  -- labels below a label of an operation are that label

  ≤opl : ∀ {ℓ o a d} → ℓ ≤ˡ opl o a d → ℓ ≡ opl o a d
  ≤opl opl≤opl = refl

  in-bud : ∀ {ℓ o a d S} → ℓ ≤ˡ opl o a d → ℓ ≤ˡ bud S → code o ∈ S
  in-bud opl≤opl (opl≤bud m) = m

  same-op : ∀ {ℓ o a d o′ a′ d′} → ℓ ≤ˡ opl o a d → ℓ ≤ˡ opl o′ a′ d′
          → o ≡ o′ × a ≡ a′ × d ≡ d′
  same-op opl≤opl opl≤opl = refl , refl , refl

------------------------------------------------------------------------
-- The walk, following a common word

module Follow {x y z : Word} (fy : x ⊑ y) (fz : x ⊑ z) where

  private
    dur-yz : dur y ≡ dur z
    dur-yz = trans (sym (⊑-dur fy)) (⊑-dur fz)

    -- at an instant inside both, the labels have a common lower bound
    below : ∀ t → t <ᴰ dur y → lab x t ≤ˡ lab y t × lab x t ≤ˡ lab z t
    below t r = ⊑-lab fy t r , ⊑-lab fz t (subst (t <ᴰ_) dur-yz r)

    -- an instant inside a piece of `y`
    inside : ∀ psd p psr {q} → WordOf (psd ++ p ∷ psr) y → q <ᴰ proj₂ p → σ psd +ᴰ q <ᴰ dur y
    inside psd p psr {q} w r =
      subst (σ psd +ᴰ q <ᴰ_) (sym (trans (dur-wordOf w) (σ-cons psd p psr)))
        (<-≤-trans (+ᴰ-monoʳ-< (σ psd) r) (+ᴰ-monoʳ-≤ (σ psd) (≤ᴰ-+ (proj₂ p) (σ psr))))

    -- the duration of an instance in pieces
    dur-y : ∀ {ps} → WordOf ps y → dur y ≡ σ ps
    dur-y = dur-wordOf

    dur-z : ∀ {qs} → WordOf qs z → dur z ≡ σ qs
    dur-z = dur-wordOf

    -- an exhausted side leaves no time on the other
    rest-zero : ∀ qsd q qsr {ps}
              → WordOf ps y → WordOf (qsd ++ q ∷ qsr) z → σ ps ≡ σ qsd → proj₂ q ≡ 0ᴰ
    rest-zero qsd q qsr wy wz e =
      zero-sumˡ (+ᴰ-absorbʳ (sym (trans (sym e) (trans (sym (dur-y wy))
        (trans dur-yz (trans (dur-z wz) (σ-cons qsd q qsr)))))))

    rest-zeroʸ : ∀ psd p psr {qs}
               → WordOf (psd ++ p ∷ psr) y → WordOf qs z → σ qs ≡ σ psd → proj₂ p ≡ 0ᴰ
    rest-zeroʸ psd p psr wy wz e =
      zero-sumˡ (+ᴰ-absorbʳ (sym (trans (sym e) (trans (sym (dur-z wz))
        (trans (sym dur-yz) (trans (dur-y wy) (σ-cons psd p psr)))))))

    -- one side ending inside a piece of the other is impossible

    past-endᵁ : ∀ psd qsd q qsr → WordOf (psd ++ []) y → WordOf (qsd ++ q ∷ qsr) z
              → ∀ e → σ qsd +ᴰ e ≡ σ psd → e <ᴰ proj₂ q → ⊥
    past-endᵁ psd qsd q qsr wy wz e ee lt =
      <-irrefl (<-≤-trans (subst (_<ᴰ σ qsd +ᴰ proj₂ q) ee (+ᴰ-monoʳ-< (σ qsd) lt))
                 (≤ᴰ-trans (+ᴰ-monoʳ-≤ (σ qsd) (≤ᴰ-+ (proj₂ q) (σ qsr)))
                   (≤ᴰ-reflexive (sym (trans (sym (trans (dur-y wy) (cong σ (++-identityʳ psd))))
                                     (trans dur-yz (trans (dur-z wz) (σ-cons qsd q qsr))))))))

    past-endᴸ : ∀ psd p psr qsd → WordOf (psd ++ p ∷ psr) y → WordOf (qsd ++ []) z
              → ∀ e → σ psd +ᴰ e ≡ σ qsd → e <ᴰ proj₂ p → ⊥
    past-endᴸ psd p psr qsd wy wz e ee lt =
      <-irrefl (<-≤-trans (subst (_<ᴰ σ psd +ᴰ proj₂ p) ee (+ᴰ-monoʳ-< (σ psd) lt))
                 (≤ᴰ-trans (+ᴰ-monoʳ-≤ (σ psd) (≤ᴰ-+ (proj₂ p) (σ psr)))
                   (≤ᴰ-reflexive (sym (trans (sym (trans (dur-z wz) (cong σ (++-identityʳ qsd))))
                                     (trans (sym dur-yz) (trans (dur-y wy) (σ-cons psd p psr))))))))

  mutual

    -- both at a boundary

    syncs : ∀ psd psr qsd qsr {v : Word′ lower} {w : Word′ upper}
          → WordOf (psd ++ psr) y → WordOf (qsd ++ qsr) z → Shape v psr → Shape w qsr
          → σ psd ≡ σ qsd → Walk v w sync
    syncs psd [] qsd [] wy wz Shape.[] Shape.[] e = done
    syncs psd [] qsd (q ∷ qsr) wy wz Shape.[] sh e =
      skipU₀ psd [] qsd q qsr wy wz Shape.[] sh e
        (λ r → <⇒≢ r (sym (rest-zero qsd q qsr wy wz (trans (cong σ (++-identityʳ psd)) e))))
    syncs psd (p ∷ psr) qsd [] wy wz sh Shape.[] e =
      skipL₀ psd p psr qsd [] wy wz sh Shape.[] e
        (λ r → <⇒≢ r (sym (rest-zeroʸ psd p psr wy wz (trans (cong σ (++-identityʳ qsd)) (sym e)))))
    syncs psd (p ∷ psr) qsd (q ∷ qsr) wy wz shL shU e with 0ᴰ <ᴰ? proj₂ p | 0ᴰ <ᴰ? proj₂ q
    ... | no ¬pp | _ = skipL₀ psd p psr qsd (q ∷ qsr) wy wz shL shU e ¬pp
    ... | yes pp | no ¬pq = skipU₀ psd (p ∷ psr) qsd q qsr wy wz shL shU e ¬pq
    ... | yes pp | yes pq = start psd p psr qsd q qsr wy wz shL shU e pp pq

    -- a piece of no length, passed

    skipL₀ : ∀ psd p psr qsd qsr {v : Word′ lower} {w : Word′ upper}
           → WordOf (psd ++ p ∷ psr) y → WordOf (qsd ++ qsr) z → Shape v (p ∷ psr) → Shape w qsr
           → σ psd ≡ σ qsd → ¬ (0ᴰ <ᴰ proj₂ p) → Walk v w sync
    skipL₀ psd p psr qsd qsr wy wz (Shape.op sh) shU e ¬pp =
      ⊥-elim (¬pp (rt-pos _ (head-rt (proj₂ (suffix psd wy)))))
    skipL₀ psd p psr qsd qsr wy wz (Shape.st a sh) shU e ¬pp =
      skipL sync (zero-adm {lower} a ¬pp)
        (syncs (psd ++ p ∷ []) psr qsd qsr (shift wy) wz sh shU (zero-step psd p ¬pp e))

    skipU₀ : ∀ psd psr qsd q qsr {v : Word′ lower} {w : Word′ upper}
           → WordOf (psd ++ psr) y → WordOf (qsd ++ q ∷ qsr) z → Shape v psr → Shape w (q ∷ qsr)
           → σ psd ≡ σ qsd → ¬ (0ᴰ <ᴰ proj₂ q) → Walk v w sync
    skipU₀ psd psr qsd q qsr wy wz shL (Shape.op sh) e ¬pq =
      ⊥-elim (¬pq (rt-pos _ (head-rt (proj₂ (suffix qsd wz)))))
    skipU₀ psd psr qsd q qsr wy wz shL (Shape.st a sh) e ¬pq =
      skipU sync (zero-adm {upper} a ¬pq)
        (syncs psd psr (qsd ++ q ∷ []) qsr wy (shift wz) shL sh (sym (zero-step qsd q ¬pq (sym e))))

    -- both start

    start : ∀ psd p psr qsd q qsr {v : Word′ lower} {w : Word′ upper}
          → WordOf (psd ++ p ∷ psr) y → WordOf (qsd ++ q ∷ qsr) z → Shape v (p ∷ psr) → Shape w (q ∷ qsr)
          → σ psd ≡ σ qsd → 0ᴰ <ᴰ proj₂ p → 0ᴰ <ᴰ proj₂ q → Walk v w sync
    start psd p psr qsd q qsr wy wz shL shU e pp pq =
      startᵏ psd p psr qsd q qsr wy wz shL shU e pp pq (at psd wy) (at qsd wz)
        (below (σ psd +ᴰ 0ᴰ) (inside psd p psr wy pp))

    startᵏ : ∀ psd p psr qsd q qsr {v : Word′ lower} {w : Word′ upper}
           → WordOf (psd ++ p ∷ psr) y → WordOf (qsd ++ q ∷ qsr) z → Shape v (p ∷ psr) → Shape w (q ∷ qsr)
           → σ psd ≡ σ qsd → 0ᴰ <ᴰ proj₂ p → 0ᴰ <ᴰ proj₂ q
           → At y (σ psd) p → At z (σ qsd) q
           → lab x (σ psd +ᴰ 0ᴰ) ≤ˡ lab y (σ psd +ᴰ 0ᴰ) × lab x (σ psd +ᴰ 0ᴰ) ≤ˡ lab z (σ psd +ᴰ 0ᴰ)
           → Walk v w sync
    startᵏ psd _ psr qsd _ qsr wy wz (Shape.op shL) (Shape.op shU) e pp pq (at-op d hy) (at-op d′ hz) (by , bz)
      with same-op (subst (lab x (σ psd +ᴰ 0ᴰ) ≤ˡ_) (hy pp) by)
                   (subst (lab x (σ psd +ᴰ 0ᴰ) ≤ˡ_) (trans (cong (λ s → lab z (s +ᴰ 0ᴰ)) e) (hz pq)) bz)
    ... | refl , _ , refl =
      opop (head-rt (proj₂ (suffix psd wy)))
        (syncs (psd ++ _ ∷ []) psr (qsd ++ _ ∷ []) qsr (shift wy) (shift wz) shL shU
               (trans (σ-snoc psd _) (trans (cong (_+ᴰ ∣ d ∣⁺) e) (sym (σ-snoc qsd _)))))
    startᵏ psd _ psr qsd _ qsr wy wz (Shape.op shL) (Shape.st a shU) e pp pq (at-op d hy) (at-st hz) (by , bz) =
      startᵐ psd _ psr qsd _ qsr wy wz (Shape.op shL) (Shape.st a shU) e pp pq
        (in-bud (subst (lab x (σ psd +ᴰ 0ᴰ) ≤ˡ_) (hy pp) by)
                (subst (lab x (σ psd +ᴰ 0ᴰ) ≤ˡ_) (trans (cong (λ s → lab z (s +ᴰ 0ᴰ)) e) (hz pq)) bz))
    startᵏ psd _ psr qsd _ qsr wy wz (Shape.st a shL) (Shape.op shU) e pp pq (at-st hy) (at-op d hz) (by , bz) =
      startᵐ psd _ psr qsd _ qsr wy wz (Shape.st a shL) (Shape.op shU) e pp pq
        (in-bud (subst (lab x (σ psd +ᴰ 0ᴰ) ≤ˡ_) (trans (cong (λ s → lab z (s +ᴰ 0ᴰ)) e) (hz pq)) bz)
                (subst (lab x (σ psd +ᴰ 0ᴰ) ≤ˡ_) (hy pp) by))
    startᵏ psd _ psr qsd _ qsr wy wz (Shape.st a shL) (Shape.st b shU) e pp pq _ _ _ =
      startᵐ psd _ psr qsd _ qsr wy wz (Shape.st a shL) (Shape.st b shU) e pp pq tt

    startᵐ : ∀ psd p psr qsd q qsr {ℓ v m w}
           → WordOf (psd ++ p ∷ psr) y → WordOf (qsd ++ q ∷ qsr) z
           → Shape {lower} (ℓ ∷ v) (p ∷ psr) → Shape {upper} (m ∷ w) (q ∷ qsr)
           → σ psd ≡ σ qsd → 0ᴰ <ᴰ proj₂ p → 0ᴰ <ᴰ proj₂ q → Meets ℓ m
           → Walk (ℓ ∷ v) (m ∷ w) sync
    startᵐ psd p psr qsd q qsr {ℓ} {_} {m} wy wz shL shU e pp pq mt with compare (proj₂ p) (proj₂ q)
    ... | tri< lt =
      syncL mt pp (adm-head shL (proj₂ (suffix psd wy)))
        (inUs (psd ++ p ∷ []) psr qsd q qsr (shift wy) wz (shape-tail shL) shU (proj₂ p)
              (trans (cong (_+ᴰ proj₂ p) (sym e)) (sym (σ-snoc psd p))) pp lt)
    ... | tri≈ eq =
      syncB mt pp (adm-head shL (proj₂ (suffix psd wy)))
        (subst (Adm {upper} m) (sym eq) (adm-head shU (proj₂ (suffix qsd wz))))
        (syncs (psd ++ p ∷ []) psr (qsd ++ q ∷ []) qsr (shift wy) (shift wz) (shape-tail shL) (shape-tail shU)
               (trans (σ-snoc psd p) (trans (cong₂ _+ᴰ_ e eq) (sym (σ-snoc qsd q)))))
    ... | tri> gt =
      syncU mt pq (adm-head shU (proj₂ (suffix qsd wz)))
        (inLs psd p psr (qsd ++ q ∷ []) qsr wy (shift wz) shL (shape-tail shU) (proj₂ q)
              (trans (cong (_+ᴰ proj₂ q) e) (sym (σ-snoc qsd q))) pq gt)

    -- the upper word inside a piece

    inUs : ∀ psd psr qsd q qsr {v : Word′ lower} {m w}
         → WordOf (psd ++ psr) y → WordOf (qsd ++ q ∷ qsr) z → Shape v psr → Shape {upper} (m ∷ w) (q ∷ qsr)
         → ∀ e → σ qsd +ᴰ e ≡ σ psd → 0ᴰ <ᴰ e → e <ᴰ proj₂ q → Walk v w (inU m e)
    inUs psd [] qsd q qsr wy wz Shape.[] shU e ee pe lt =
      ⊥-elim (past-endᵁ psd qsd q qsr wy wz e ee lt)
    inUs psd (p ∷ psr) qsd q qsr wy wz shL shU e ee pe lt with 0ᴰ <ᴰ? proj₂ p
    ... | no ¬pp = inU-skip psd p psr qsd q qsr wy wz shL shU e ee pe lt ¬pp
    ... | yes pp =
      inUᵏ psd p psr qsd q qsr wy wz shL shU e ee pe lt pp (at psd wy) (at qsd wz)
        (below (σ psd +ᴰ 0ᴰ) (inside psd p psr wy pp))

    inU-skip : ∀ psd p psr qsd q qsr {v : Word′ lower} {m w}
             → WordOf (psd ++ p ∷ psr) y → WordOf (qsd ++ q ∷ qsr) z → Shape v (p ∷ psr) → Shape {upper} (m ∷ w) (q ∷ qsr)
             → ∀ e → σ qsd +ᴰ e ≡ σ psd → 0ᴰ <ᴰ e → e <ᴰ proj₂ q → ¬ (0ᴰ <ᴰ proj₂ p) → Walk v w (inU m e)
    inU-skip psd p psr qsd q qsr wy wz (Shape.op sh) shU e ee pe lt ¬pp =
      ⊥-elim (¬pp (rt-pos _ (head-rt (proj₂ (suffix psd wy)))))
    inU-skip psd p psr qsd q qsr wy wz (Shape.st a sh) shU e ee pe lt ¬pp =
      skipL inU (zero-adm {lower} a ¬pp)
        (inUs (psd ++ p ∷ []) psr qsd q qsr (shift wy) wz sh shU e (sym (zero-step psd p ¬pp (sym ee))) pe lt)

    inUᵏ : ∀ psd p psr qsd q qsr {v : Word′ lower} {m w}
         → WordOf (psd ++ p ∷ psr) y → WordOf (qsd ++ q ∷ qsr) z → Shape v (p ∷ psr) → Shape {upper} (m ∷ w) (q ∷ qsr)
         → ∀ e → σ qsd +ᴰ e ≡ σ psd → 0ᴰ <ᴰ e → e <ᴰ proj₂ q → 0ᴰ <ᴰ proj₂ p
         → At y (σ psd) p → At z (σ qsd) q
         → lab x (σ psd +ᴰ 0ᴰ) ≤ˡ lab y (σ psd +ᴰ 0ᴰ) × lab x (σ psd +ᴰ 0ᴰ) ≤ˡ lab z (σ psd +ᴰ 0ᴰ)
         → Walk v w (inU m e)
    inUᵏ psd _ psr qsd _ qsr wy wz (Shape.op shL) (Shape.op shU) e ee pe lt pp (at-op d hy) (at-op d′ hz) (by , bz)
      with same-op (subst (lab x (σ psd +ᴰ 0ᴰ) ≤ˡ_) (hy pp) by)
                   (subst (lab x (σ psd +ᴰ 0ᴰ) ≤ˡ_) (trans (cong (lab z) (mid ee)) (hz lt)) bz)
    ... | _ , e0 , _ = ⊥-elim (<⇒≢ pe e0)
    inUᵏ psd _ psr qsd _ qsr wy wz (Shape.op shL) (Shape.st a shU) e ee pe lt pp (at-op d hy) (at-st hz) (by , bz) =
      inUᵐ psd _ psr qsd _ qsr wy wz (Shape.op shL) (Shape.st a shU) e ee pe lt pp
        (in-bud (subst (lab x (σ psd +ᴰ 0ᴰ) ≤ˡ_) (hy pp) by)
                (subst (lab x (σ psd +ᴰ 0ᴰ) ≤ˡ_) (trans (cong (lab z) (mid ee)) (hz lt)) bz))
    inUᵏ psd _ psr qsd _ qsr wy wz (Shape.st a shL) (Shape.op shU) e ee pe lt pp (at-st hy) (at-op d hz) (by , bz) =
      inUᵐ psd _ psr qsd _ qsr wy wz (Shape.st a shL) (Shape.op shU) e ee pe lt pp
        (in-bud (subst (lab x (σ psd +ᴰ 0ᴰ) ≤ˡ_) (trans (cong (lab z) (mid ee)) (hz lt)) bz)
                (subst (lab x (σ psd +ᴰ 0ᴰ) ≤ˡ_) (hy pp) by))
    inUᵏ psd _ psr qsd _ qsr wy wz (Shape.st a shL) (Shape.st b shU) e ee pe lt pp _ _ _ =
      inUᵐ psd _ psr qsd _ qsr wy wz (Shape.st a shL) (Shape.st b shU) e ee pe lt pp tt

    inUᵐ : ∀ psd p psr qsd q qsr {ℓ v m w}
         → WordOf (psd ++ p ∷ psr) y → WordOf (qsd ++ q ∷ qsr) z
         → Shape {lower} (ℓ ∷ v) (p ∷ psr) → Shape {upper} (m ∷ w) (q ∷ qsr)
         → ∀ e → σ qsd +ᴰ e ≡ σ psd → 0ᴰ <ᴰ e → e <ᴰ proj₂ q → 0ᴰ <ᴰ proj₂ p → Meets ℓ m
         → Walk (ℓ ∷ v) w (inU m e)
    inUᵐ psd p psr qsd q qsr {ℓ} {_} {m} wy wz shL shU e ee pe lt pp mt with compare (e +ᴰ proj₂ p) (proj₂ q)
    ... | tri< lt′ =
      firstL mt pp (adm-head shL (proj₂ (suffix psd wy)))
        (inUs (psd ++ p ∷ []) psr qsd q qsr (shift wy) wz (shape-tail shL) shU (e +ᴰ proj₂ p)
              (step-on qsd psd p e ee) (+pos′ pp) lt′)
    ... | tri≈ eq =
      bothU mt pp (adm-head shL (proj₂ (suffix psd wy)))
        (subst (Adm {upper} m) (sym eq) (adm-head shU (proj₂ (suffix qsd wz))))
        (syncs (psd ++ p ∷ []) psr (qsd ++ q ∷ []) qsr (shift wy) (shift wz) (shape-tail shL) (shape-tail shU)
               (meet-up psd p qsd q e ee eq))
    ... | tri> gt =
      lateU mt (∸-pos lt) (subst (Adm {upper} m) (sym (+-∸ (<⇒≤ lt))) (adm-head shU (proj₂ (suffix qsd wz))))
        (inLs psd p psr (qsd ++ q ∷ []) qsr wy (shift wz) shL (shape-tail shU) (proj₂ q ∸ᴰ e)
              (over psd qsd q e ee lt) (∸-pos lt) (∸-< lt gt))

    -- the lower word inside a piece

    inLs : ∀ psd p psr qsd qsr {ℓ v} {w : Word′ upper}
         → WordOf (psd ++ p ∷ psr) y → WordOf (qsd ++ qsr) z → Shape {lower} (ℓ ∷ v) (p ∷ psr) → Shape w qsr
         → ∀ e → σ psd +ᴰ e ≡ σ qsd → 0ᴰ <ᴰ e → e <ᴰ proj₂ p → Walk v w (inL ℓ e)
    inLs psd p psr qsd [] wy wz shL Shape.[] e ee pe lt =
      ⊥-elim (past-endᴸ psd p psr qsd wy wz e ee lt)
    inLs psd p psr qsd (q ∷ qsr) wy wz shL shU e ee pe lt with 0ᴰ <ᴰ? proj₂ q
    ... | no ¬pq = inL-skip psd p psr qsd q qsr wy wz shL shU e ee pe lt ¬pq
    ... | yes pq =
      inLᵏ psd p psr qsd q qsr wy wz shL shU e ee pe lt pq (at psd wy) (at qsd wz)
        (below (σ qsd +ᴰ 0ᴰ) (subst (_<ᴰ dur y) (mid′ ee) (inside psd p psr wy lt)))

    inL-skip : ∀ psd p psr qsd q qsr {ℓ v} {w : Word′ upper}
             → WordOf (psd ++ p ∷ psr) y → WordOf (qsd ++ q ∷ qsr) z → Shape {lower} (ℓ ∷ v) (p ∷ psr) → Shape w (q ∷ qsr)
             → ∀ e → σ psd +ᴰ e ≡ σ qsd → 0ᴰ <ᴰ e → e <ᴰ proj₂ p → ¬ (0ᴰ <ᴰ proj₂ q) → Walk v w (inL ℓ e)
    inL-skip psd p psr qsd q qsr wy wz shL (Shape.op sh) e ee pe lt ¬pq =
      ⊥-elim (¬pq (rt-pos _ (head-rt (proj₂ (suffix qsd wz)))))
    inL-skip psd p psr qsd q qsr wy wz shL (Shape.st a sh) e ee pe lt ¬pq =
      skipU inL (zero-adm {upper} a ¬pq)
        (inLs psd p psr (qsd ++ q ∷ []) qsr wy (shift wz) shL sh e (sym (zero-step qsd q ¬pq (sym ee))) pe lt)

    inLᵏ : ∀ psd p psr qsd q qsr {ℓ v} {w : Word′ upper}
         → WordOf (psd ++ p ∷ psr) y → WordOf (qsd ++ q ∷ qsr) z → Shape {lower} (ℓ ∷ v) (p ∷ psr) → Shape w (q ∷ qsr)
         → ∀ e → σ psd +ᴰ e ≡ σ qsd → 0ᴰ <ᴰ e → e <ᴰ proj₂ p → 0ᴰ <ᴰ proj₂ q
         → At y (σ psd) p → At z (σ qsd) q
         → lab x (σ qsd +ᴰ 0ᴰ) ≤ˡ lab y (σ qsd +ᴰ 0ᴰ) × lab x (σ qsd +ᴰ 0ᴰ) ≤ˡ lab z (σ qsd +ᴰ 0ᴰ)
         → Walk v w (inL ℓ e)
    inLᵏ psd _ psr qsd _ qsr wy wz (Shape.op shL) (Shape.op shU) e ee pe lt pq (at-op d hy) (at-op d′ hz) (by , bz)
      with same-op (subst (lab x (σ qsd +ᴰ 0ᴰ) ≤ˡ_) (trans (cong (lab y) (mid ee)) (hy lt)) by)
                   (subst (lab x (σ qsd +ᴰ 0ᴰ) ≤ˡ_) (hz pq) bz)
    ... | _ , e0 , _ = ⊥-elim (<⇒≢ pe (sym e0))
    inLᵏ psd _ psr qsd _ qsr wy wz (Shape.op shL) (Shape.st a shU) e ee pe lt pq (at-op d hy) (at-st hz) (by , bz) =
      inLᵐ psd _ psr qsd _ qsr wy wz (Shape.op shL) (Shape.st a shU) e ee pe lt pq
        (in-bud (subst (lab x (σ qsd +ᴰ 0ᴰ) ≤ˡ_) (trans (cong (lab y) (mid ee)) (hy lt)) by)
                (subst (lab x (σ qsd +ᴰ 0ᴰ) ≤ˡ_) (hz pq) bz))
    inLᵏ psd _ psr qsd _ qsr wy wz (Shape.st a shL) (Shape.op shU) e ee pe lt pq (at-st hy) (at-op d hz) (by , bz) =
      inLᵐ psd _ psr qsd _ qsr wy wz (Shape.st a shL) (Shape.op shU) e ee pe lt pq
        (in-bud (subst (lab x (σ qsd +ᴰ 0ᴰ) ≤ˡ_) (hz pq) bz)
                (subst (lab x (σ qsd +ᴰ 0ᴰ) ≤ˡ_) (trans (cong (lab y) (mid ee)) (hy lt)) by))
    inLᵏ psd _ psr qsd _ qsr wy wz (Shape.st a shL) (Shape.st b shU) e ee pe lt pq _ _ _ =
      inLᵐ psd _ psr qsd _ qsr wy wz (Shape.st a shL) (Shape.st b shU) e ee pe lt pq tt

    inLᵐ : ∀ psd p psr qsd q qsr {ℓ v m w}
         → WordOf (psd ++ p ∷ psr) y → WordOf (qsd ++ q ∷ qsr) z
         → Shape {lower} (ℓ ∷ v) (p ∷ psr) → Shape {upper} (m ∷ w) (q ∷ qsr)
         → ∀ e → σ psd +ᴰ e ≡ σ qsd → 0ᴰ <ᴰ e → e <ᴰ proj₂ p → 0ᴰ <ᴰ proj₂ q → Meets ℓ m
         → Walk v (m ∷ w) (inL ℓ e)
    inLᵐ psd p psr qsd q qsr {ℓ} {_} {m} wy wz shL shU e ee pe lt pq mt with compare (e +ᴰ proj₂ q) (proj₂ p)
    ... | tri< lt′ =
      firstU mt pq (adm-head shU (proj₂ (suffix qsd wz)))
        (inLs psd p psr (qsd ++ q ∷ []) qsr wy (shift wz) shL (shape-tail shU) (e +ᴰ proj₂ q)
              (step-on psd qsd q e ee) (+pos′ pq) lt′)
    ... | tri≈ eq =
      bothL mt pq (subst (Adm {lower} ℓ) (sym eq) (adm-head shL (proj₂ (suffix psd wy))))
        (adm-head shU (proj₂ (suffix qsd wz)))
        (syncs (psd ++ p ∷ []) psr (qsd ++ q ∷ []) qsr (shift wy) (shift wz) (shape-tail shL) (shape-tail shU)
               (sym (meet-up qsd q psd p e ee eq)))
    ... | tri> gt =
      lateL mt (∸-pos lt) (subst (Adm {lower} ℓ) (sym (+-∸ (<⇒≤ lt))) (adm-head shL (proj₂ (suffix psd wy))))
        (inUs (psd ++ p ∷ []) psr qsd q qsr (shift wy) wz (shape-tail shL) shU (proj₂ p ∸ᴰ e)
              (over qsd psd p e ee lt) (∸-pos lt) (∸-< lt gt))


------------------------------------------------------------------------
-- A common word gives a walk, and a walk one

complete-common : ∀ {v w} → Common v w → Walk v w sync
complete-common {v} {w} (x , (y , y∈ , fy) , (z , z∈ , fz)) with ⟦⟧-inst v y∈ | ⟦⟧-inst w z∈
... | ps , shy , wy | qs , shz , wz = Follow.syncs fy fz [] ps [] qs wy wz shy shz refl

walk⇔common : ∀ {v w} → Walk v w sync ⇔ Common v w
walk⇔common = mk⇔ sound-common complete-common
