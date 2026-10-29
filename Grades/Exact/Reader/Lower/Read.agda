------------------------------------------------------------------------
-- A fit of an exact run into a word of a lower bound is read by the  --
-- lower reader.                                                      --
--                                                                    --
-- The reader keeps to the stretches of the fit, one by one. An item  --
-- the fit matches with an operation of the bound is matched. An item --
-- lying within the current stretch of the fit is poured whole. An    --
-- item the current stretch of the fit ends inside closes the chain   --
-- before it when the chain's bounds are already met, and otherwise   --
-- overflows into the next stretch. The reader ends its stretches no  --
-- later than the fit: every stretch of the fit ends past where the   --
-- reader's chain, at its bounds, would.                              --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Reader.Lower.Read
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_; map; [_])
open import Data.List.Properties using (++-assoc; map-++)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T
  using (Cut; ⁺; ⁻; 0⁺; 0⁻; _+ˡ_; ⊑⇒≤; ≤⇒⁻⊑⁻; by-pt; by-side;
         +ˡ-monoˡ; +ˡ-monoʳ; +ˡ-assoc; +ˡ-identityˡ; +ˡ-identityʳ; +ˡ-inflate)
  renaming (_∣_ to _∣ᶜ_; _⊑_ to _⊑ᶜ_; ⊑-refl to ⊑ᶜ-refl; ⊑-trans to ⊑ᶜ-trans)
open import Grades.Durations.Intervals.Dense T using (⊑⁻⇒<)

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Order T Op n code code-injective
open import Grades.Exact.Letters T Op n code code-injective running
open import Grades.Exact.Positions T Op n code code-injective running
open import Grades.Exact.Expression T Op n code code-injective running using (lower)
open import Grades.Exact.Reader.Lower T Op n code code-injective running
open import Grades.Exact.Reader.Upper.Read T Op n code code-injective running
  using (OpPos; wordOf-pos; opPos-++ʳ; module Fit)

private
  variable
    a b c : Carrier

  ≮⇒≥ : ¬ (a <ᴰ b) → b ≤ᴰ a
  ≮⇒≥ {a} {b} ¬p with b ≤ᴰ? a
  ... | yes r = r
  ... | no ¬r = ⊥-elim (¬p ¬r)

------------------------------------------------------------------------
-- The pieces of an exact run, read as lower weights

pcsᴸ : Word → List Pl
pcsᴸ x = map toLo (pieces x)

pcsᴸ-∷ʳ : ∀ x i → pcsᴸ (x ∷ʳ i) ≡ pcsᴸ x ∷ʳ toLo (kind i , len i)
pcsᴸ-∷ʳ x i = trans (cong (map toLo) (map-++ _ x [ i ])) (map-++ toLo (pieces x) _)

sum-pcsᴸ : ∀ x → sumˡ (map proj₂ (pcsᴸ x)) ≡ cl⁻ (dur x)
sum-pcsᴸ []      = refl
sum-pcsᴸ (i ∷ x) rewrite sum-pcsᴸ x = refl

-- every bound asks for a positive length

ValidL : Word′ lower → Set
ValidL []           = ⊤
ValidL (op _ ∷ v)   = ValidL v
ValidL (st _ c ∷ v) = 0⁺ ⊑ᶜ c × ValidL v

------------------------------------------------------------------------
-- Arithmetic of lower ends against closed ones

cancel-cl⁻ : ∀ a {c c′} → cl⁻ a +ˡ c ⊑ᶜ cl⁻ a +ˡ c′ → c ⊑ᶜ c′
cancel-cl⁻ a {p ∣ᶜ s} {q ∣ᶜ t} (by-pt r)      = by-pt (λ z → r (+ᴰ-monoʳ-≤ a z))
cancel-cl⁻ a {p ∣ᶜ s} {q ∣ᶜ t} (by-side e r)  = by-side (+ᴰ-cancelˡ a e) r

sumˡ-∷ʳ : ∀ cs c → sumˡ (cs ∷ʳ c) ≡ sumˡ cs +ˡ c
sumˡ-∷ʳ []       c = trans (+ˡ-identityʳ c) (sym (+ˡ-identityˡ c))
sumˡ-∷ʳ (c′ ∷ cs) c = trans (cong (c′ +ˡ_) (sumˡ-∷ʳ cs c)) (sym (+ˡ-assoc c′ (sumˡ cs) c))

------------------------------------------------------------------------
-- Whether a chain may still close before an item

data Choice (pre : List Pl) (cs : List Cut) : Bool → Set where
  free  : Dec (Fitsᴸ pre cs) → Choice pre cs false
  short : ¬ Fitsᴸ pre cs → Choice pre cs true

------------------------------------------------------------------------
-- The reading of one fit

module FitL (x y : Word) (ps : List (Piece Carrier)) (wy : WordOf ps y) (fit : x ⊑ y) where

  open Fit x y ps wy fit public using (σof; cst; cop)

  private
    ++-∷ʳ : ∀ {A : Set} (a : List A) p r → a ++ p ∷ r ≡ (a ∷ʳ p) ++ r
    ++-∷ʳ a p r = sym (++-assoc a [ p ] r)

    σ-∷ʳ : ∀ pfx p → σof (pfx ∷ʳ p) ≡ σof pfx +ᴰ proj₂ p
    σ-∷ʳ pfx p = trans (cong sumᴰ (amts-++ pfx [ p ]))
                       (trans (sumᴰ-++ (amts pfx) _) (cong (σof pfx +ᴰ_) (+ᴰ-identityʳ _)))

    dur-∷ʳ : ∀ xd i → dur (xd ∷ʳ i) ≡ dur xd +ᴰ len i
    dur-∷ʳ xd i = trans (dur-++ xd [ i ]) (cong (dur xd +ᴰ_) (+ᴰ-identityʳ _))

    dur-x : dur x ≡ dur y
    dur-x = ⊑-dur fit

    dur-x′ : ∀ xd xr → x ≡ xd ++ xr → dur x ≡ dur xd +ᴰ dur xr
    dur-x′ xd xr ex = trans (cong dur ex) (dur-++ xd xr)

    rest-end : ∀ pfx rest → ps ≡ pfx ++ rest → σof pfx +ᴰ sumᴰ (amts rest) ≡ dur y
    rest-end pfx rest e =
      trans (sym (sumᴰ-++ (amts pfx) (amts rest)))
            (trans (cong sumᴰ (sym (amts-++ pfx rest)))
                   (trans (cong (λ z → sumᴰ (amts z)) (sym e)) (sym (dur-wordOf wy))))

    opPos : ∀ pfx rest → ps ≡ pfx ++ rest → OpPos rest
    opPos pfx rest e = opPos-++ʳ pfx (subst OpPos e (wordOf-pos wy))

    x-∷ʳ : ∀ {xd i xr} → x ≡ xd ++ i ∷ xr → x ≡ (xd ∷ʳ i) ++ xr
    x-∷ʳ {xd} {i} {xr} ex = trans ex (++-∷ʳ xd i xr)

    ps-∷ʳ : ∀ {pfx p rest} → ps ≡ pfx ++ p ∷ rest → ps ≡ (pfx ∷ʳ p) ++ rest
    ps-∷ʳ {pfx} {p} {rest} e = trans e (++-∷ʳ pfx p rest)

    fitsP : ∀ pre cs → sumˡ cs ⊑ᶜ cl⁻ (dur pre) → Fitsᴸ (pcsᴸ pre) cs
    fitsP pre cs f = subst (sumˡ cs ⊑ᶜ_) (sym (sum-pcsᴸ pre)) f

    Pfits : ∀ pre cs → Fitsᴸ (pcsᴸ pre) cs → sumˡ cs ⊑ᶜ cl⁻ (dur pre)
    Pfits pre cs f = subst (sumˡ cs ⊑ᶜ_) (sum-pcsᴸ pre) f

    -- the pieces after a prefix: nonempty while the word lasts
    some-rest : ∀ pfx rest → ps ≡ pfx ++ rest → σof pfx <ᴰ dur y → rest ≡ [] → ⊥
    some-rest pfx [] e s refl = s (≤ᴰ-reflexive (trans (sym (rest-end pfx [] e)) (+ᴰ-identityʳ _)))

    -- the pieces after the prefix are positive
    first-pos : ∀ pfx p rest {vr} → ps ≡ pfx ++ p ∷ rest → Shape vr (p ∷ rest) → ValidL vr → 0ᴰ <ᴰ proj₂ p
    first-pos pfx (opk o , τ) rest e (op _) _ = proj₁ (opPos pfx _ e)
    first-pos pfx (stk S , ℓ) rest e (st a _) (z , _) = ⊑⁻⇒< (⊑ᶜ-trans z a) refl

    -- no operation of the bound starts strictly inside an item
    not-inside : ∀ {xd i xr pfx o τ rest} → x ≡ xd ++ i ∷ xr → ps ≡ pfx ++ (opk o , τ) ∷ rest
               → dur xd <ᴰ σof pfx → σof pfx <ᴰ dur xd +ᴰ len i → ⊥
    not-inside {xd} {pfx = pfx} {τ = τ} {rest} ex e r s with
      cop ex e (σof pfx) (<⇒≤ r) s ≤ᴰ-refl
          (subst (_<ᴰ σof pfx +ᴰ τ) (+ᴰ-identityʳ _) (+ᴰ-monoʳ-< (σof pfx) (proj₁ (opPos pfx _ e))))
    ... | _ , _ , _ , eb = <⇒≢ r eb

    -- the chain met at a boundary of the fit
    met : ∀ {B0 pre cs t} → cl⁻ B0 +ˡ sumˡ cs ⊑ᶜ cl⁻ t → t ≤ᴰ B0 +ᴰ dur pre → Fitsᴸ (pcsᴸ pre) cs
    met {B0} {pre} {cs} {t} I r =
      fitsP pre cs (cancel-cl⁻ B0 (⊑ᶜ-trans I (≤⇒⁻⊑⁻ r)))

    -- the chain met once an item is added
    met-with : ∀ {B0 pre cs t i} → cl⁻ B0 +ˡ sumˡ cs ⊑ᶜ cl⁻ t → t ≤ᴰ (B0 +ᴰ dur pre) +ᴰ len i
             → Fitsᴸ (pcsᴸ pre ∷ʳ toLo (kind i , len i)) cs
    met-with {B0} {pre} {cs} {t} {i} I r =
      subst (λ P → Fitsᴸ P cs) (pcsᴸ-∷ʳ pre i)
        (fitsP (pre ∷ʳ i) cs
          (subst (sumˡ cs ⊑ᶜ_) (cong cl⁻ (sym (dur-∷ʳ pre i)))
            (cancel-cl⁻ B0 (⊑ᶜ-trans I (≤⇒⁻⊑⁻ (≤ᴰ-trans r (≤ᴰ-reflexive (+ᴰ-assoc B0 _ _))))))))

  Front : Word → Carrier → Carrier → Set
  Front []      _ _ = ⊤
  Front (i ∷ _) σ b = σ <ᴰ b +ᴰ len i

  private
    end-≤ : ∀ pfx p rest → ps ≡ pfx ++ p ∷ rest → σof pfx +ᴰ proj₂ p ≤ᴰ dur y
    end-≤ pfx p rest e =
      subst (σof pfx +ᴰ proj₂ p ≤ᴰ_)
            (trans (+ᴰ-assoc (σof pfx) (proj₂ p) _) (rest-end pfx (p ∷ rest) e))
            (≤ᴰ-+ (σof pfx +ᴰ proj₂ p) _)

    -- an instant shared by an item and a stretch reaching past its start
    share : ∀ {σ b σ′ e} → σ <ᴰ σ′ → b <ᴰ σ′ → σ <ᴰ e → b <ᴰ e
          → Σ[ t ∈ Carrier ] σ ≤ᴰ t × t <ᴰ σ′ × b ≤ᴰ t × t <ᴰ e
    share {σ} {b} r₁ r₂ r₃ r₄ with σ ≤ᴰ? b
    ... | yes σ≤b = b , σ≤b , r₂ , ≤ᴰ-refl , r₄
    ... | no ¬σ≤b = σ , ≤ᴰ-refl , r₁ , <⇒≤ ¬σ≤b , r₃

    one-capˡ : ∀ c → sumˡ (c ∷ []) ≡ c
    one-capˡ c = +ˡ-identityʳ c

    -- the bound of a stretch below what its length admits, past a start
    start-I1 : ∀ {b σ′ c ℓ′} → b ≤ᴰ σ′ → c ⊑ᶜ cl⁻ ℓ′ → cl⁻ b +ˡ sumˡ (c ∷ []) ⊑ᶜ cl⁻ (σ′ +ᴰ ℓ′)
    start-I1 {b} {σ′} {c} {ℓ′} r a =
      subst (λ z → cl⁻ b +ˡ z ⊑ᶜ cl⁻ (σ′ +ᴰ ℓ′)) (sym (one-capˡ c))
        (⊑ᶜ-trans (+ˡ-monoˡ c (≤⇒⁻⊑⁻ r)) (+ˡ-monoʳ (cl⁻ σ′) a))

    more-I1 : ∀ {B0 cs σ′ c ℓ′} → cl⁻ B0 +ˡ sumˡ cs ⊑ᶜ cl⁻ σ′ → c ⊑ᶜ cl⁻ ℓ′
            → cl⁻ B0 +ˡ sumˡ (cs ∷ʳ c) ⊑ᶜ cl⁻ (σ′ +ᴰ ℓ′)
    more-I1 {B0} {cs} {σ′} {c} {ℓ′} I a =
      subst (λ z → cl⁻ B0 +ˡ z ⊑ᶜ cl⁻ (σ′ +ᴰ ℓ′)) (sym (sumˡ-∷ʳ cs c))
        (subst (_⊑ᶜ cl⁻ (σ′ +ᴰ ℓ′)) (+ˡ-assoc (cl⁻ B0) (sumˡ cs) c)
          (⊑ᶜ-trans (+ˡ-monoˡ c I) (+ˡ-monoʳ (cl⁻ σ′) a)))

    still-short : ∀ {pre cs c} → ¬ Fitsᴸ pre cs → ¬ Fitsᴸ pre (cs ∷ʳ c)
    still-short {pre} {cs} {c} ¬f f =
      ¬f (⊑ᶜ-trans (+ˡ-inflate (sumˡ cs) c) (subst (_⊑ᶜ _) (sumˡ-∷ʳ cs c) f))

  mutual

    runR : ∀ xd xr pfx rest vr → x ≡ xd ++ xr → ps ≡ pfx ++ rest → Shape vr rest → ValidL vr
         → dur xd ≡ σof pfx → RunL (pcsᴸ xr) vr
    runR xd [] pfx [] [] ex e [] _ eb = done
    runR xd (i ∷ xr) pfx [] [] ex e [] _ eb =
      ⊥-elim (<-irrefl (subst (dur xd <ᴰ_) bad (<-≤-trans (<-+ (len-pos i)) (≤ᴰ-+ (dur xd +ᴰ len i) (dur xr)))))
      where
        bad : (dur xd +ᴰ len i) +ᴰ dur xr ≡ dur xd
        bad = trans (+ᴰ-assoc (dur xd) _ _)
                (trans (sym (dur-x′ xd (i ∷ xr) ex))
                  (trans dur-x (trans (sym (rest-end pfx [] e)) (trans (+ᴰ-identityʳ _) (sym eb)))))
    runR xd [] pfx (p ∷ rest) (ℓ ∷ vr) ex e sh vl eb =
      ⊥-elim (<-irrefl (<-≤-trans (subst (_<ᴰ σof pfx +ᴰ proj₂ p) (+ᴰ-identityʳ _)
                                     (+ᴰ-monoʳ-< (σof pfx) (first-pos pfx p rest e sh vl)))
                                  (subst (σof pfx +ᴰ proj₂ p ≤ᴰ_) bad (end-≤ pfx p rest e))))
      where
        bad : dur y ≡ σof pfx
        bad = trans (sym dur-x) (trans (dur-x′ xd [] ex) (trans (+ᴰ-identityʳ _) eb))
    runR xd (i ∷ xr) pfx ((opk o , τ) ∷ rest) (op o ∷ vr) ex e (op sh) vl eb
      with cop ex e (dur xd) ≤ᴰ-refl (<-+ (len-pos i)) (≤ᴰ-reflexive (sym eb))
             (subst (_<ᴰ σof pfx +ᴰ τ) (trans (+ᴰ-identityʳ _) (sym eb))
               (+ᴰ-monoʳ-< (σof pfx) (proj₁ (opPos pfx _ e))))
    ... | d , refl , refl , _ =
      match refl (runR (xd ∷ʳ i) xr (pfx ∷ʳ _) rest vr (x-∷ʳ ex) (ps-∷ʳ e) sh vl
                   (trans (dur-∷ʳ xd i) (trans (cong (_+ᴰ ∣ d ∣⁺) eb) (sym (σ-∷ʳ pfx _)))))
    runR xd xr pfx ((stk S , ℓ) ∷ rest) (st S c ∷ vr) ex e (st a sh) (z , vl) eb =
      start (chF xd xr pfx S ℓ rest vr (dur xd) [] (c ∷ []) ex e sh vl
               (sym (+ᴰ-identityʳ _)) (start-I1 (≤ᴰ-reflexive eb) a)
               (≤ᴰ-trans (≤ᴰ-reflexive eb) (≤ᴰ-+ (σof pfx) ℓ))
               (front xr) (⊑⁻⇒< (⊑ᶜ-trans z a) refl))
      where
        front : ∀ xr → Front xr (σof pfx) (dur xd)
        front []      = tt
        front (i ∷ _) = subst (_<ᴰ dur xd +ᴰ len i) eb (<-+ (len-pos i))

    chF : ∀ xd xr pfx S ℓ rest vr B0 pre cs
        → x ≡ xd ++ xr → ps ≡ pfx ++ (stk S , ℓ) ∷ rest → Shape vr rest → ValidL vr
        → dur xd ≡ B0 +ᴰ dur pre
        → cl⁻ B0 +ˡ sumˡ cs ⊑ᶜ cl⁻ (σof pfx +ᴰ ℓ)
        → dur xd ≤ᴰ σof pfx +ᴰ ℓ
        → Front xr (σof pfx) (dur xd)
        → 0ᴰ <ᴰ ℓ
        → ChL S (pcsᴸ pre) cs false (pcsᴸ xr) vr
    chF xd [] pfx S ℓ rest vr B0 pre cs ex e sh vl eb I1 F1 F2 ℓp =
      close (met {B0} {pre} {cs} I1 (≤ᴰ-trans σ′≤ (≤ᴰ-reflexive eb))) (endL (pfx ∷ʳ _) rest vr (ps-∷ʳ e) sh vl (σ-end))
      where
        b≡y : dur xd ≡ dur y
        b≡y = trans (sym (+ᴰ-identityʳ _)) (trans (sym (dur-x′ xd [] ex)) dur-x)
        σ′≤ : σof pfx +ᴰ ℓ ≤ᴰ dur xd
        σ′≤ = subst (σof pfx +ᴰ ℓ ≤ᴰ_) (sym b≡y) (end-≤ pfx _ rest e)
        σ-end : σof (pfx ∷ʳ (stk S , ℓ)) ≡ dur y
        σ-end = trans (σ-∷ʳ pfx _) (trans (≤ᴰ-antisym σ′≤ F1) b≡y)
    chF xd (i ∷ xr) pfx S ℓ rest vr B0 pre cs ex e sh vl eb I1 F1 F2 ℓp
      with (σof pfx +ᴰ ℓ) ≤ᴰ? dur xd
    ... | yes σ′≤b =
      close (met {B0} {pre} {cs} I1 (≤ᴰ-trans σ′≤b (≤ᴰ-reflexive eb)))
            (runR xd (i ∷ xr) (pfx ∷ʳ _) rest vr ex (ps-∷ʳ e) sh vl
               (trans (≤ᴰ-antisym F1 σ′≤b) (sym (σ-∷ʳ pfx _))))
    ... | no ¬σ′≤b with share {σof pfx} {dur xd} {σof pfx +ᴰ ℓ} {dur xd +ᴰ len i}
                           (subst (_<ᴰ σof pfx +ᴰ ℓ) (+ᴰ-identityʳ _) (+ᴰ-monoʳ-< (σof pfx) ℓp))
                           ¬σ′≤b F2 (<-+ (len-pos i))
    ...   | t , r₁ , s₁ , r₂ , s₂ with cst ex e t r₂ s₂ r₁ s₁ | (dur xd +ᴰ len i) ≤ᴰ? (σof pfx +ᴰ ℓ)
    ...     | ad | yes inside =
      pour ad
        (subst (λ P → ChL S P cs false (pcsᴸ xr) vr) (pcsᴸ-∷ʳ pre i)
          (chF (xd ∷ʳ i) xr pfx S ℓ rest vr B0 (pre ∷ʳ i) cs (x-∷ʳ ex) e sh vl
            (trans (dur-∷ʳ xd i) (trans (cong (_+ᴰ len i) eb)
                     (trans (+ᴰ-assoc B0 _ _) (cong (B0 +ᴰ_) (sym (dur-∷ʳ pre i))))))
            I1 (subst (_≤ᴰ σof pfx +ᴰ ℓ) (sym (dur-∷ʳ xd i)) inside)
            (front xr) ℓp))
      where
        front : ∀ xr → Front xr (σof pfx) (dur (xd ∷ʳ i))
        front []       = tt
        front (i′ ∷ _) = subst (λ z → σof pfx <ᴰ z +ᴰ len i′) (sym (dur-∷ʳ xd i))
                           (<-≤-trans F2 (≤ᴰ-+ (dur xd +ᴰ len i) (len i′)))
    ...     | ad | no ¬inside =
      beyond xd i xr pfx S ℓ rest vr B0 pre cs ex e sh vl eb I1 ad ¬σ′≤b ¬inside
             (free (Fitsᴸ? (pcsᴸ pre) cs))

    -- the current stretch of the fit ends inside the item: close before
    -- it when the bounds are met, overflow otherwise
    beyond : ∀ xd i xr pfx S ℓ rest vr B0 pre cs {m}
           → x ≡ xd ++ i ∷ xr → ps ≡ pfx ++ (stk S , ℓ) ∷ rest → Shape vr rest → ValidL vr
           → dur xd ≡ B0 +ᴰ dur pre
           → cl⁻ B0 +ˡ sumˡ cs ⊑ᶜ cl⁻ (σof pfx +ᴰ ℓ)
           → AdmK (kind i) S → dur xd <ᴰ σof pfx +ᴰ ℓ → σof pfx +ᴰ ℓ <ᴰ dur xd +ᴰ len i
           → Choice (pcsᴸ pre) cs m
           → ChL S (pcsᴸ pre) cs m (pcsᴸ (i ∷ xr)) vr
    beyond xd i xr pfx S ℓ [] [] B0 pre cs ex e [] _ eb I1 ad r s ch =
      ⊥-elim (s (≤ᴰ-trans (≤ᴰ-trans (≤ᴰ-+ (dur xd +ᴰ len i) (dur xr))
                    (≤ᴰ-reflexive (trans (+ᴰ-assoc (dur xd) _ _) (sym (dur-x′ xd (i ∷ xr) ex)))))
                    (≤ᴰ-reflexive (trans dur-x (sym (trans (sym (+ᴰ-identityʳ _)) (rest-end′))))))) 
      where
        rest-end′ : (σof pfx +ᴰ ℓ) +ᴰ 0ᴰ ≡ dur y
        rest-end′ = trans (cong (_+ᴰ 0ᴰ) (sym (σ-∷ʳ pfx _))) (rest-end (pfx ∷ʳ _) [] (ps-∷ʳ e))
    beyond xd i xr pfx S ℓ ((opk o , τ) ∷ rest) (op o ∷ vr) B0 pre cs ex e (op sh) vl eb I1 ad r s ch =
      ⊥-elim (not-inside ex (ps-∷ʳ e) (subst (dur xd <ᴰ_) (sym (σ-∷ʳ pfx _)) r)
                                      (subst (_<ᴰ dur xd +ᴰ len i) (sym (σ-∷ʳ pfx _)) s))
    beyond xd i xr pfx S ℓ ((stk S′ , ℓ′) ∷ rest) (st S′ c′ ∷ vr) B0 pre cs ex e (st a sh) (z , vl)
           eb I1 ad r s ch = go ch
      where
        σ′ = σof pfx +ᴰ ℓ
        e′ : ps ≡ (pfx ∷ʳ (stk S , ℓ)) ++ (stk S′ , ℓ′) ∷ rest
        e′ = ps-∷ʳ e
        σ≡ : σof (pfx ∷ʳ (stk S , ℓ)) ≡ σ′
        σ≡ = σ-∷ʳ pfx _
        ℓ′p : 0ᴰ <ᴰ ℓ′
        ℓ′p = ⊑⁻⇒< (⊑ᶜ-trans z a) refl
        g : Fitsᴸ (pcsᴸ pre ∷ʳ toLo (kind i , len i)) cs
        g = met-with {B0} {pre} {cs} {i = i} I1 (≤ᴰ-trans (<⇒≤ s) (≤ᴰ-reflexive (cong (_+ᴰ len i) eb)))
        overflow : ¬ Fitsᴸ (pcsᴸ pre) cs → ∀ {m} → ChL S (pcsᴸ pre) cs m (pcsᴸ (i ∷ xr)) (st S′ c′ ∷ vr)
        overflow ¬f =
          over ad ¬f g
            (chM xd i xr (pfx ∷ʳ _) S′ ℓ′ rest vr B0 pre (cs ∷ʳ c′) ex e′ sh vl eb
               (subst (λ u → cl⁻ B0 +ˡ sumˡ (cs ∷ʳ c′) ⊑ᶜ cl⁻ (u +ᴰ ℓ′)) (sym σ≡) (more-I1 {B0} {cs} I1 a))
               (subst (dur xd <ᴰ_) (sym σ≡) r) (subst (_<ᴰ dur xd +ᴰ len i) (sym σ≡) s)
               (still-short {pcsᴸ pre} {cs} {c′} ¬f) ℓ′p)
        go : ∀ {m} → Choice (pcsᴸ pre) cs m → ChL S (pcsᴸ pre) cs m (pcsᴸ (i ∷ xr)) (st S′ c′ ∷ vr)
        go (free (yes f)) =
          close f (start (chF xd (i ∷ xr) (pfx ∷ʳ _) S′ ℓ′ rest vr (dur xd) [] (c′ ∷ []) ex e′ sh vl
                            (sym (+ᴰ-identityʳ _))
                            (subst (λ u → cl⁻ (dur xd) +ˡ sumˡ (c′ ∷ []) ⊑ᶜ cl⁻ (u +ᴰ ℓ′)) (sym σ≡)
                               (start-I1 (<⇒≤ r) a))
                            (subst (λ u → dur xd ≤ᴰ u +ᴰ ℓ′) (sym σ≡) (≤ᴰ-trans (<⇒≤ r) (≤ᴰ-+ σ′ ℓ′)))
                            (subst (_<ᴰ dur xd +ᴰ len i) (sym σ≡) s) ℓ′p))
        go (free (no ¬f)) = overflow ¬f
        go (short ¬f)     = overflow ¬f

    chM : ∀ xd i xr pfx S ℓ rest vr B0 pre cs
        → x ≡ xd ++ i ∷ xr → ps ≡ pfx ++ (stk S , ℓ) ∷ rest → Shape vr rest → ValidL vr
        → dur xd ≡ B0 +ᴰ dur pre
        → cl⁻ B0 +ˡ sumˡ cs ⊑ᶜ cl⁻ (σof pfx +ᴰ ℓ)
        → dur xd <ᴰ σof pfx → σof pfx <ᴰ dur xd +ᴰ len i
        → ¬ Fitsᴸ (pcsᴸ pre) cs
        → 0ᴰ <ᴰ ℓ
        → ChL S (pcsᴸ pre) cs true (pcsᴸ (i ∷ xr)) vr
    chM xd i xr pfx S ℓ rest vr B0 pre cs ex e sh vl eb I1 r s ¬f ℓp
      with cst ex e (σof pfx) (<⇒≤ r) s ≤ᴰ-refl
             (subst (_<ᴰ σof pfx +ᴰ ℓ) (+ᴰ-identityʳ _) (+ᴰ-monoʳ-< (σof pfx) ℓp))
         | (dur xd +ᴰ len i) ≤ᴰ? (σof pfx +ᴰ ℓ)
    ... | ad | yes inside =
      pour ad
        (subst (λ P → ChL S P cs false (pcsᴸ xr) vr) (pcsᴸ-∷ʳ pre i)
          (chF (xd ∷ʳ i) xr pfx S ℓ rest vr B0 (pre ∷ʳ i) cs (x-∷ʳ ex) e sh vl
            (trans (dur-∷ʳ xd i) (trans (cong (_+ᴰ len i) eb)
                     (trans (+ᴰ-assoc B0 _ _) (cong (B0 +ᴰ_) (sym (dur-∷ʳ pre i))))))
            I1 (subst (_≤ᴰ σof pfx +ᴰ ℓ) (sym (dur-∷ʳ xd i)) inside)
            (front xr) ℓp))
      where
        front : ∀ xr → Front xr (σof pfx) (dur (xd ∷ʳ i))
        front []       = tt
        front (i′ ∷ _) = subst (λ z → σof pfx <ᴰ z +ᴰ len i′) (sym (dur-∷ʳ xd i))
                           (<-≤-trans s (≤ᴰ-+ (dur xd +ᴰ len i) (len i′)))
    ... | ad | no ¬inside =
      beyond xd i xr pfx S ℓ rest vr B0 pre cs ex e sh vl eb I1 ad
             (<-trans r (subst (_<ᴰ σof pfx +ᴰ ℓ) (+ᴰ-identityʳ _) (+ᴰ-monoʳ-< (σof pfx) ℓp)))
             ¬inside (short ¬f)

    endL : ∀ pfx rest vr → ps ≡ pfx ++ rest → Shape vr rest → ValidL vr → σof pfx ≡ dur y → RunL [] vr
    endL pfx [] [] e [] _ _ = done
    endL pfx (p ∷ rest) (ℓ ∷ vr) e sh vl eσ =
      ⊥-elim (<-irrefl (<-≤-trans (subst (_<ᴰ σof pfx +ᴰ proj₂ p) (+ᴰ-identityʳ _)
                                     (+ᴰ-monoʳ-< (σof pfx) (first-pos pfx p rest e sh vl)))
                                  (subst (σof pfx +ᴰ proj₂ p ≤ᴰ_) (sym eσ) (end-≤ pfx p rest e))))

------------------------------------------------------------------------
-- Every fit into a word with positive bounds is read

readᴸ : ∀ {x y v} → Inst y v → ValidL v → x ⊑ y → RunL (pcsᴸ x) v
readᴸ {x} {y} {v} (ps , sh , wy) vl fit = FitL.runR x y ps wy fit [] x [] ps v refl refl sh vl refl
