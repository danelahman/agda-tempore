------------------------------------------------------------------------
-- A fit of an exact run into a word of an upper bound is read by the --
-- upper reader.                                                      --
--                                                                    --
-- The reader is steered by the fit. An item that the fit matches     --
-- with an operation of the bound is matched; any other item is       --
-- poured whole into the current stretch when the chain still fits,   --
-- and otherwise overflows into the stretch of the fit that holds the --
-- instant where the current stretch, full, would end, or where the   --
-- item starts if that is later; when the current stretch does not    --
-- admit the item, the chain is closed and a new one opened at the    --
-- stretch of the fit holding the item's start. The reader runs ahead --
-- of the fit: every stretch of the fit ends no later than the        --
-- reader's chain, full, would.                                       --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Reader.Upper.Read
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_; map; foldr; [_])
open import Data.List.Properties using (++-assoc; map-++)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T
  using (Cut; Hi; fin; ∞; _⊑ʰ_; _⊑ʰ?_; ⁺; ⁻; 0⁺; _+ʰ_; ⊑⇒≤; ≤⇒⁺⊑⁺;
         by-pt; by-side; ⊑ʰ-trans; ⊑ʰ-∞; +ʰ-identityˡ; +ʰ-identityʳ; +ʰ-mono; +ʰ-monoʳ; +ʰ-assoc; ⊑ʰ-refl; ⊑ʰ-reflexive)
  renaming (_∣_ to _∣ᶜ_)

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Order T Op n code code-injective
open import Grades.Exact.Letters T Op n code code-injective running
open import Grades.Exact.Positions T Op n code code-injective running
open import Grades.Exact.Expression T Op n code code-injective running
  using (upper)
open import Grades.Exact.Reader.Upper T Op n code code-injective running

private
  variable
    a b c p q : Carrier

  ≮⇒≥ : ¬ (p <ᴰ a) → a ≤ᴰ p
  ≮⇒≥ {p} {a} ¬p with a ≤ᴰ? p
  ... | yes r = r
  ... | no ¬r = ⊥-elim (¬p ¬r)

------------------------------------------------------------------------
-- The pieces of an exact run, read as weights

pcs : Word → List Ph
pcs x = map toHi (pieces x)

pcs-∷ʳ : ∀ x i → pcs (x ∷ʳ i) ≡ pcs x ∷ʳ toHi (kind i , len i)
pcs-∷ʳ x i = trans (cong (map toHi) (map-++ _ x [ i ])) (map-++ toHi (pieces x) _)

sum-pcs : ∀ x → sumʰ (map proj₂ (pcs x)) ≡ cl (dur x)
sum-pcs []      = refl
sum-pcs (i ∷ x) rewrite sum-pcs x = refl

------------------------------------------------------------------------
-- Arithmetic of upper ends against closed ones

cl-+ : ∀ a b → cl a +ʰ cl b ≡ cl (a +ᴰ b)
cl-+ a b = refl

cancel-cl : ∀ a {h h′} → cl a +ʰ h ⊑ʰ cl a +ʰ h′ → h ⊑ʰ h′
cancel-cl a {h} {∞} _ = ⊑ʰ-∞ h
cancel-cl a {∞} {fin _} ()
cancel-cl a {fin (p ∣ᶜ s)} {fin (q ∣ᶜ t)} (by-pt r) = by-pt (λ z → r (+ᴰ-monoʳ-≤ a z))
cancel-cl a {fin (p ∣ᶜ s)} {fin (q ∣ᶜ t)} (by-side e r) = by-side (+ᴰ-cancelˡ a e) r

sumʰ-∷ʳ : ∀ cs h → sumʰ (cs ∷ʳ h) ≡ sumʰ cs +ʰ h
sumʰ-∷ʳ []       h = trans (+ʰ-identityʳ h) (sym (+ʰ-identityˡ h))
sumʰ-∷ʳ (c ∷ cs) h = trans (cong (c +ʰ_) (sumʰ-∷ʳ cs h)) (sym (+ʰ-assoc c (sumʰ cs) h))

-- an item overflowing a chain ends past where the chain, full, ends

past-chain : ∀ {σ′ B0 X τ C} → ¬ (cl (X +ᴰ τ) ⊑ʰ C) → cl σ′ ⊑ʰ cl B0 +ʰ C
           → σ′ <ᴰ B0 +ᴰ (X +ᴰ τ)
past-chain {σ′} {B0} {X} {τ} {C} ¬f I r =
  ¬f (cancel-cl B0 (⊑ʰ-trans (≤⇒⁺⊑⁺ r) I))

-- a stretch starting no later than the chain's end, full, ends no later
-- than the chain with it, full

extend : ∀ {σ ℓ B0 C h} → cl σ ⊑ʰ cl B0 +ʰ C → cl ℓ ⊑ʰ h → cl (σ +ᴰ ℓ) ⊑ʰ cl B0 +ʰ (C +ʰ h)
extend {σ} {ℓ} {B0} {C} {h} r s =
  subst (cl (σ +ᴰ ℓ) ⊑ʰ_) (+ʰ-assoc (cl B0) C h) (+ʰ-mono {cl σ} r s)

------------------------------------------------------------------------
-- Lists of pieces in time

-- operation pieces take time

OpPos : List Pc → Set
OpPos []                 = ⊤
OpPos ((opk _ , τ) ∷ ps) = 0ᴰ <ᴰ τ × OpPos ps
OpPos ((stk _ , τ) ∷ ps) = OpPos ps

wordOf-pos : ∀ {ps y} → WordOf ps y → OpPos ps
wordOf-pos []         = tt
wordOf-pos (op {d = d} _ w) = ∣∣⁺-pos d , wordOf-pos w
wordOf-pos (st w)     = wordOf-pos w

opPos-++ʳ : ∀ pfx {ps} → OpPos (pfx ++ ps) → OpPos ps
opPos-++ʳ []                  o       = o
opPos-++ʳ ((opk _ , _) ∷ pfx) (_ , o) = opPos-++ʳ pfx o
opPos-++ʳ ((stk _ , _) ∷ pfx) o       = opPos-++ʳ pfx o

-- the operation pieces start no earlier than `b`, the first at `σ`

OpsFrom : Carrier → Carrier → List Pc → Set
OpsFrom b σ []                 = ⊤
OpsFrom b σ ((opk _ , τ) ∷ ps) = b ≤ᴰ σ × OpsFrom b (σ +ᴰ τ) ps
OpsFrom b σ ((stk _ , τ) ∷ ps) = OpsFrom b (σ +ᴰ τ) ps

ops-from-≤ : ∀ {b b′} σ ps → b′ ≤ᴰ b → OpsFrom b σ ps → OpsFrom b′ σ ps
ops-from-≤ σ []                 r _       = tt
ops-from-≤ σ ((opk _ , τ) ∷ ps) r (s , o) = ≤ᴰ-trans r s , ops-from-≤ (σ +ᴰ τ) ps r o
ops-from-≤ σ ((stk _ , τ) ∷ ps) r o       = ops-from-≤ (σ +ᴰ τ) ps r o

-- every piece starts at or after the first
ops-from-start : ∀ {b} σ ps → b ≤ᴰ σ → OpsFrom b σ ps
ops-from-start σ []                 r = tt
ops-from-start σ ((opk _ , τ) ∷ ps) r = r , ops-from-start (σ +ᴰ τ) ps (≤ᴰ-trans r (≤ᴰ-+ σ τ))
ops-from-start σ ((stk _ , τ) ∷ ps) r = ops-from-start (σ +ᴰ τ) ps (≤ᴰ-trans r (≤ᴰ-+ σ τ))

ops-from-drop : ∀ {b} σ psm p ps → OpsFrom b σ (psm ++ p ∷ ps)
              → OpsFrom b ((σ +ᴰ sumᴰ (amts psm)) +ᴰ proj₂ p) ps
ops-from-drop σ [] (opk _ , τ) ps (_ , o) =
  subst (λ z → OpsFrom _ (z +ᴰ τ) ps) (sym (+ᴰ-identityʳ σ)) o
ops-from-drop σ [] (stk _ , τ) ps o =
  subst (λ z → OpsFrom _ (z +ᴰ τ) ps) (sym (+ᴰ-identityʳ σ)) o
ops-from-drop σ ((opk _ , τ) ∷ psm) p ps (_ , o) =
  subst (λ z → OpsFrom _ (z +ᴰ proj₂ p) ps) (+ᴰ-assoc σ τ _) (ops-from-drop (σ +ᴰ τ) psm p ps o)
ops-from-drop σ ((stk _ , τ) ∷ psm) p ps o =
  subst (λ z → OpsFrom _ (z +ᴰ proj₂ p) ps) (+ᴰ-assoc σ τ _) (ops-from-drop (σ +ᴰ τ) psm p ps o)

-- the pieces lying before `b` are stretches

data AllSt : Word′ upper → Set where
  []  : AllSt []
  _∷_ : ∀ {S c v} → ⊤ → AllSt v → AllSt (st S c ∷ v)

before-all-st : ∀ {b} σ psm {vm} → Shape vm psm → OpsFrom b σ psm → OpPos psm
              → σ +ᴰ sumᴰ (amts psm) ≤ᴰ b → AllSt vm
before-all-st σ [] [] _ _ _ = []
before-all-st {b} σ ((opk _ , τ) ∷ psm) (op sh) (r , _) (ps₀ , _) s =
  ⊥-elim (ps₀ (+ᴰ-cancelˡ-≤ σ
    (≤ᴰ-trans (≤ᴰ-trans (≤ᴰ-+ (σ +ᴰ τ) (sumᴰ (amts psm)))
                         (≤ᴰ-reflexive (+ᴰ-assoc σ τ _)))
              (≤ᴰ-trans s (≤ᴰ-trans r (≤ᴰ-reflexive (sym (+ᴰ-identityʳ σ))))))))
before-all-st σ ((stk _ , τ) ∷ psm) (st _ sh) o p s =
  tt ∷ before-all-st (σ +ᴰ τ) psm sh o p (≤ᴰ-trans (≤ᴰ-reflexive (+ᴰ-assoc σ τ _)) s)

-- splitting a shape along its pieces

shape-split : ∀ psm {p ps v} → Shape v (psm ++ p ∷ ps)
            → Σ[ vm ∈ Word′ upper ] Σ[ ℓ ∈ _ ] Σ[ v′ ∈ Word′ upper ]
                v ≡ vm ++ ℓ ∷ v′ × Shape vm psm × Shape (ℓ ∷ v′) (p ∷ ps)
shape-split [] {v = ℓ ∷ v} sh@(op _) = [] , ℓ , v , refl , [] , sh
shape-split [] {v = ℓ ∷ v} sh@(st _ _) = [] , ℓ , v , refl , [] , sh
shape-split (_ ∷ psm) (op sh) with shape-split psm sh
... | vm , ℓ , v′ , refl , s₁ , s₂ = _ ∷ vm , ℓ , v′ , refl , op s₁ , s₂
shape-split (_ ∷ psm) (st a sh) with shape-split psm sh
... | vm , ℓ , v′ , refl , s₁ , s₂ = _ ∷ vm , ℓ , v′ , refl , st a s₁ , s₂

-- the piece holding an instant

locate : ∀ σ ps q → σ ≤ᴰ q → q <ᴰ σ +ᴰ sumᴰ (amts ps)
       → Σ[ psm ∈ List Pc ] Σ[ p ∈ Pc ] Σ[ ps′ ∈ List Pc ]
           ps ≡ psm ++ p ∷ ps′ × σ +ᴰ sumᴰ (amts psm) ≤ᴰ q
           × q <ᴰ (σ +ᴰ sumᴰ (amts psm)) +ᴰ proj₂ p
locate σ []      q r s = ⊥-elim (s (≤ᴰ-trans (≤ᴰ-reflexive (+ᴰ-identityʳ σ)) r))
locate σ (p ∷ ps) q r s with q <ᴰ? σ +ᴰ proj₂ p
... | yes t = [] , p , ps , refl , ≤ᴰ-trans (≤ᴰ-reflexive (+ᴰ-identityʳ σ)) r ,
              subst (λ z → q <ᴰ z +ᴰ proj₂ p) (sym (+ᴰ-identityʳ σ)) t
... | no ¬t with locate (σ +ᴰ proj₂ p) ps q (≮⇒≥ ¬t) (subst (q <ᴰ_) (sym (+ᴰ-assoc σ _ _)) s)
...   | psm , p′ , ps′ , refl , u , w =
  p ∷ psm , p′ , ps′ , refl , subst (_≤ᴰ q) (+ᴰ-assoc σ _ _) u ,
  subst (λ z → q <ᴰ z +ᴰ proj₂ p′) (+ᴰ-assoc σ _ _) w

-- passing stretches at length zero

skip-run : ∀ {qs vm rest} → AllSt vm → RunU qs rest → RunU qs (vm ++ rest)
skip-run []       r = r
skip-run (_ ∷ as) r = start (close (skip-run as r))

pass-over : ∀ {pre cs p ps vm rest} → AllSt vm → OverU pre cs p ps rest → OverU pre cs p ps (vm ++ rest)
pass-over []       o = o
pass-over (_ ∷ as) o = pass (pass-over as o)

------------------------------------------------------------------------
-- The reading of one fit

module Fit (x y : Word) (ps : List Pc) (wy : WordOf ps y) (fit : x ⊑ y) where

  σof : List Pc → Carrier
  σof pfx = sumᴰ (amts pfx)

  private
    ++-∷ʳ : ∀ {A : Set} (a : List A) p r → a ++ p ∷ r ≡ (a ∷ʳ p) ++ r
    ++-∷ʳ a p r = sym (++-assoc a [ p ] r)

    σ-∷ʳ : ∀ pfx p → σof (pfx ∷ʳ p) ≡ σof pfx +ᴰ proj₂ p
    σ-∷ʳ pfx p = trans (cong sumᴰ (amts-++ pfx [ p ]))
                       (trans (sumᴰ-++ (amts pfx) _) (cong (σof pfx +ᴰ_) (+ᴰ-identityʳ _)))

    dur-∷ʳ : ∀ xd i → dur (xd ∷ʳ i) ≡ dur xd +ᴰ len i
    dur-∷ʳ xd i = trans (dur-++ xd [ i ]) (cong (dur xd +ᴰ_) (+ᴰ-identityʳ _))

    dur-y : dur y ≡ sumᴰ (amts ps)
    dur-y = dur-wordOf wy

    dur-x : dur x ≡ dur y
    dur-x = ⊑-dur fit

    wy′ : ∀ {pfx rest} → ps ≡ pfx ++ rest → WordOf (pfx ++ rest) y
    wy′ e = subst (λ z → WordOf z y) e wy

    atP : ∀ pfx {p rest} → ps ≡ pfx ++ p ∷ rest → At y (σof pfx) p
    atP pfx {p} {rest} e = at pfx (wy′ {pfx} {p ∷ rest} e)

    -- the pieces after a prefix end within the word
    rest-end : ∀ pfx rest → ps ≡ pfx ++ rest → σof pfx +ᴰ sumᴰ (amts rest) ≡ dur y
    rest-end pfx rest e =
      trans (sym (sumᴰ-++ (amts pfx) (amts rest)))
            (trans (cong sumᴰ (sym (amts-++ pfx rest))) (trans (cong (λ z → sumᴰ (amts z)) (sym e)) (sym dur-y)))

    end-≤ : ∀ pfx p rest → ps ≡ pfx ++ p ∷ rest → σof pfx +ᴰ proj₂ p ≤ᴰ dur y
    end-≤ pfx p rest e =
      subst (σof pfx +ᴰ proj₂ p ≤ᴰ_)
            (trans (+ᴰ-assoc (σof pfx) (proj₂ p) _) (rest-end pfx (p ∷ rest) e))
            (≤ᴰ-+ (σof pfx +ᴰ proj₂ p) _)

    opPos : ∀ pfx rest → ps ≡ pfx ++ rest → OpPos rest
    opPos pfx rest e = opPos-++ʳ pfx (subst OpPos e (wordOf-pos wy))

    -- an instant inside an item, and its offset
    offset : ∀ {a p} → a ≤ᴰ p → Σ[ q ∈ Carrier ] a +ᴰ q ≡ p
    offset = diff

    off-< : ∀ {a q c} → a +ᴰ q <ᴰ a +ᴰ c → q <ᴰ c
    off-< {a} s t = s (+ᴰ-monoʳ-≤ a t)

  -- an item and a stretch piece sharing the instant `t`
  cst : ∀ {xd i xr pfx S ℓ rest} → x ≡ xd ++ i ∷ xr → ps ≡ pfx ++ (stk S , ℓ) ∷ rest
      → ∀ t → dur xd ≤ᴰ t → t <ᴰ dur xd +ᴰ len i → σof pfx ≤ᴰ t → t <ᴰ σof pfx +ᴰ ℓ
      → AdmK (kind i) S
  cst {xd} {i} {xr} {pfx} {S} {ℓ} {rest} ex e t r₁ s₁ r₂ s₂ with offset r₁ | offset r₂
  ... | q₁ , e₁ | q₂ , e₂ =
    compat-st fit xd i xr ex (atP pfx e) q₁ q₂ (trans e₁ (sym e₂))
      (off-< (subst (_<ᴰ dur xd +ᴰ len i) (sym e₁) s₁))
      (off-< (subst (_<ᴰ σof pfx +ᴰ ℓ) (sym e₂) s₂))
      (<-≤-trans (subst (_<ᴰ σof pfx +ᴰ ℓ) (sym e₂) s₂) (end-≤ pfx _ rest e))

  -- an item and an operation piece sharing the instant `t`
  cop : ∀ {xd i xr pfx o τ rest} → x ≡ xd ++ i ∷ xr → ps ≡ pfx ++ (opk o , τ) ∷ rest
      → ∀ t → dur xd ≤ᴰ t → t <ᴰ dur xd +ᴰ len i → σof pfx ≤ᴰ t → t <ᴰ σof pfx +ᴰ τ
      → Σ[ d ∈ D⁺ ] i ≡ op o d × ∣ d ∣⁺ ≡ τ × dur xd ≡ σof pfx
  cop {xd} {i} {xr} {pfx} {o} {τ} {rest} ex e t r₁ s₁ r₂ s₂ with offset r₁ | offset r₂
  ... | q₁ , e₁ | q₂ , e₂ =
    compat-op fit xd i xr ex (atP pfx e) q₁ q₂ (trans e₁ (sym e₂))
      (off-< (subst (_<ᴰ dur xd +ᴰ len i) (sym e₁) s₁))
      (off-< (subst (_<ᴰ σof pfx +ᴰ τ) (sym e₂) s₂))
      (<-≤-trans (subst (_<ᴰ σof pfx +ᴰ τ) (sym e₂) s₂) (end-≤ pfx _ rest e))

  -- an operation of the bound starts at the instant `t`

  Matched : Carrier → Set
  Matched t = Σ[ o ∈ Op ] Σ[ d ∈ D⁺ ] lab y t ≡ opl o 0ᴰ d

  matched? : ∀ t → Dec (Matched t)
  matched? t = go (lab y t) refl
    where
      go : (ℓ : Label) → lab y t ≡ ℓ → Dec (Matched t)
      go (bud S) e = no λ { (o , d , e′) → bud≢ (trans (sym e) e′) }
        where
          bud≢ : ∀ {S o d} → bud S ≡ opl o 0ᴰ d → ⊥
          bud≢ ()
      go (opl o δ d) e with δ ≟ᴰ 0ᴰ
      ... | yes refl = yes (o , d , e)
      ... | no ne    = no λ { (o′ , d′ , e′) → ne (off (trans (sym e) e′)) }
        where
          off : ∀ {o δ d o′ d′} → opl o δ d ≡ opl o′ 0ᴰ d′ → δ ≡ 0ᴰ
          off refl = refl

  -- an unmatched item has no operation of the bound starting inside it

  lift : ∀ xd i xr pfx rest → x ≡ xd ++ i ∷ xr → ps ≡ pfx ++ rest
       → OpsFrom (dur xd) (σof pfx) rest → ¬ Matched (dur xd)
       → OpsFrom (dur xd +ᴰ len i) (σof pfx) rest
  lift xd i xr pfx [] ex e _ _ = tt
  lift xd i xr pfx ((opk o , τ) ∷ rest) ex e (r , os) ¬m with σof pfx <ᴰ? dur xd +ᴰ len i
  ... | no ¬s = ≮⇒≥ ¬s ,
        subst (λ z → OpsFrom _ z rest) (σ-∷ʳ pfx _)
          (lift xd i xr (pfx ∷ʳ _) rest ex (trans e (++-∷ʳ pfx _ rest))
                (subst (λ z → OpsFrom _ z rest) (sym (σ-∷ʳ pfx _)) os) ¬m)
  ... | yes s with cop ex e (σof pfx) r s ≤ᴰ-refl
                       (subst (_<ᴰ σof pfx +ᴰ τ) (+ᴰ-identityʳ _)
                         (+ᴰ-monoʳ-< (σof pfx) (proj₁ (opPos pfx _ e))))
  ...   | d , refl , refl , eb with atP pfx e
  ...     | at-op d′ h = ⊥-elim (¬m (o , d′ ,
                trans (cong (lab y) (trans eb (sym (+ᴰ-identityʳ _)))) (h (∣∣⁺-pos d′))))
  lift xd i xr pfx ((stk S , τ) ∷ rest) ex e os ¬m =
    subst (λ z → OpsFrom _ z rest) (σ-∷ʳ pfx _)
      (lift xd i xr (pfx ∷ʳ _) rest ex (trans e (++-∷ʳ pfx _ rest))
            (subst (λ z → OpsFrom _ z rest) (sym (σ-∷ʳ pfx _)) os) ¬m)

  ----------------------------------------------------------------------
  -- The reading

  private
    x-∷ʳ : ∀ {xd i xr} → x ≡ xd ++ i ∷ xr → x ≡ (xd ∷ʳ i) ++ xr
    x-∷ʳ {xd} {i} {xr} ex = trans ex (++-∷ʳ xd i xr)

    ps-∷ʳ : ∀ {pfx p rest} → ps ≡ pfx ++ p ∷ rest → ps ≡ (pfx ∷ʳ p) ++ rest
    ps-∷ʳ {pfx} {p} {rest} e = trans e (++-∷ʳ pfx p rest)

    dur-x′ : ∀ xd xr → x ≡ xd ++ xr → dur x ≡ dur xd +ᴰ dur xr
    dur-x′ xd xr ex = trans (cong dur ex) (dur-++ xd xr)

    cl-≤ : ∀ {a b} → a ≤ᴰ b → cl a ⊑ʰ cl b
    cl-≤ = ≤⇒⁺⊑⁺

    fitsP : ∀ pre cs → cl (dur pre) ⊑ʰ sumʰ cs → Fitsᵁ (pcs pre) cs
    fitsP pre cs f = subst (_⊑ʰ sumʰ cs) (sym (sum-pcs pre)) f

    Pfits : ∀ pre cs → Fitsᵁ (pcs pre) cs → cl (dur pre) ⊑ʰ sumʰ cs
    Pfits pre cs f = subst (_⊑ʰ sumʰ cs) (sum-pcs pre) f

    fits-∷ʳ : ∀ pre i cs → Fitsᵁ (pcs pre ∷ʳ toHi (kind i , len i)) cs → cl (dur pre +ᴰ len i) ⊑ʰ sumʰ cs
    fits-∷ʳ pre i cs f =
      subst (_⊑ʰ sumʰ cs) (cong cl (dur-∷ʳ pre i)) (Pfits (pre ∷ʳ i) cs (subst (λ P → Fitsᵁ P cs) (sym (pcs-∷ʳ pre i)) f))

    -- a cap admitting a length admits zero
    cap-0 : ∀ {ℓ h} → cl ℓ ⊑ʰ h → cl 0ᴰ ⊑ʰ h
    cap-0 {ℓ} a = ⊑ʰ-trans (cl-≤ (0ᴰ-least ℓ)) a

    one-cap : ∀ h → sumʰ (h ∷ []) ≡ h
    one-cap h = +ʰ-identityʳ h

    -- the chain's end, full, is at least where its items end
    item-end : ∀ {b B0 X C} → b ≡ B0 +ᴰ X → cl X ⊑ʰ C → cl b ⊑ʰ cl B0 +ʰ C
    item-end {b} {B0} {X} {C} eb f = subst (_⊑ʰ cl B0 +ʰ C) (cong cl (sym eb)) (+ʰ-monoʳ (cl B0) f)

    -- adding a stretch to a chain keeps what it fits
    fits-more : ∀ {X cs h ℓ} → cl X ⊑ʰ sumʰ cs → cl ℓ ⊑ʰ h → cl X ⊑ʰ sumʰ (cs ∷ʳ h)
    fits-more {X} {cs} {h} {ℓ} f a =
      subst (cl X ⊑ʰ_) (sym (sumʰ-∷ʳ cs h))
        (⊑ʰ-trans f (subst (_⊑ʰ sumʰ cs +ʰ h) (+ʰ-identityʳ (sumʰ cs)) (+ʰ-monoʳ (sumʰ cs) (cap-0 a))))

    pos-len : ∀ i → 0ᴰ <ᴰ len i
    pos-len = len-pos

  mutual

    runR : ∀ xd xr pfx rest vr → x ≡ xd ++ xr → ps ≡ pfx ++ rest → Shape vr rest
         → dur xd ≡ σof pfx → RunU (pcs xr) vr
    runR xd [] pfx [] [] ex e [] eb = done
    runR xd (i ∷ xr) pfx [] [] ex e [] eb =
      ⊥-elim (<-irrefl (subst (dur xd <ᴰ_) bad (<-≤-trans (<-+ (pos-len i)) (≤ᴰ-+ (dur xd +ᴰ len i) (dur xr)))))
      where
        bad : (dur xd +ᴰ len i) +ᴰ dur xr ≡ dur xd
        bad = trans (+ᴰ-assoc (dur xd) _ _)
                (trans (sym (dur-x′ xd (i ∷ xr) ex))
                  (trans dur-x (trans (sym (rest-end pfx [] e)) (trans (+ᴰ-identityʳ _) (sym eb)))))
    runR xd [] pfx ((opk o , τ) ∷ rest) (op o ∷ vr) ex e (op sh) eb =
      ⊥-elim (<-irrefl (<-≤-trans (subst (_<ᴰ σof pfx +ᴰ τ) (+ᴰ-identityʳ _)
                         (+ᴰ-monoʳ-< (σof pfx) (proj₁ (opPos pfx _ e))))
                  (subst (σof pfx +ᴰ τ ≤ᴰ_) bad (end-≤ pfx _ rest e))))
      where
        bad : dur y ≡ σof pfx
        bad = trans (sym dur-x) (trans (dur-x′ xd [] ex) (trans (+ᴰ-identityʳ _) eb))
    runR xd (i ∷ xr) pfx ((opk o , τ) ∷ rest) (op o ∷ vr) ex e (op sh) eb
      with cop ex e (dur xd) ≤ᴰ-refl (<-+ (pos-len i)) (≤ᴰ-reflexive (sym eb))
             (subst (_<ᴰ σof pfx +ᴰ τ) (trans (+ᴰ-identityʳ _) (sym eb))
               (+ᴰ-monoʳ-< (σof pfx) (proj₁ (opPos pfx _ e))))
    ... | d , refl , refl , _ =
      match refl (runR (xd ∷ʳ i) xr (pfx ∷ʳ _) rest vr (x-∷ʳ ex) (ps-∷ʳ e) sh
                   (trans (dur-∷ʳ xd i) (trans (cong (_+ᴰ ∣ d ∣⁺) eb) (sym (σ-∷ʳ pfx _)))))
    runR xd xr pfx ((stk S , ℓ) ∷ rest) (st S h ∷ vr) ex e (st a sh) eb =
      start (chF xd xr pfx S ℓ rest vr (dur xd) [] (h ∷ []) ex e sh (sym (+ᴰ-identityʳ _))
               (subst (cl 0ᴰ ⊑ʰ_) (sym (one-cap h)) (cap-0 a))
               (subst (cl (σof pfx +ᴰ ℓ) ⊑ʰ_) (cong (cl (dur xd) +ʰ_) (sym (one-cap h)))
                  (+ʰ-mono {cl (σof pfx)} (cl-≤ (≤ᴰ-reflexive (sym eb))) a))
               (≤ᴰ-reflexive (sym eb))
               (ops-from-start (σof pfx +ᴰ ℓ) rest (≤ᴰ-trans (≤ᴰ-reflexive eb) (≤ᴰ-+ (σof pfx) ℓ))))

    chF : ∀ xd xr pfx S ℓ rest vr B0 pre cs
        → x ≡ xd ++ xr → ps ≡ pfx ++ (stk S , ℓ) ∷ rest → Shape vr rest
        → dur xd ≡ B0 +ᴰ dur pre
        → cl (dur pre) ⊑ʰ sumʰ cs
        → cl (σof pfx +ᴰ ℓ) ⊑ʰ cl B0 +ʰ sumʰ cs
        → σof pfx ≤ᴰ dur xd
        → OpsFrom (dur xd) (σof pfx +ᴰ ℓ) rest
        → ChU S (pcs pre) cs false (pcs xr) vr
    chF xd [] pfx S ℓ rest vr B0 pre cs ex e sh eb fi i1 i2 i3 =
      close (endW (pfx ∷ʳ _) rest vr (ps-∷ʳ e) sh
               (subst₂ (λ u v → OpsFrom u v rest) bx (sym (σ-∷ʳ pfx _)) i3))
      where
        bx : dur xd ≡ dur y
        bx = trans (sym (+ᴰ-identityʳ _)) (trans (sym (dur-x′ xd [] ex)) dur-x)
    chF xd (i ∷ xr) pfx S ℓ rest vr B0 pre cs ex e sh eb fi i1 i2 i3 with matched? (dur xd)
    ... | yes m with (σof pfx +ᴰ ℓ) ≤ᴰ? dur xd
    ...   | yes s = close (clW xd i xr (pfx ∷ʳ _) rest vr ex (ps-∷ʳ e) sh
                             (subst (_≤ᴰ dur xd) (sym (σ-∷ʳ pfx _)) s)
                             (subst (λ v → OpsFrom (dur xd) v rest) (sym (σ-∷ʳ pfx _)) i3))
    ...   | no ¬s with atP pfx e | offset i2
    ...     | at-st h | q , eq with m
    ...       | o , d , em = ⊥-elim (bud≢ (trans (sym (h (off-< (subst (_<ᴰ σof pfx +ᴰ ℓ) (sym eq) ¬s))))
                                         (trans (cong (lab y) eq) em)))
      where
        bud≢ : ∀ {S o d} → bud S ≡ opl o 0ᴰ d → ⊥
        bud≢ ()
    chF xd (i ∷ xr) pfx S ℓ rest vr B0 pre cs ex e sh eb fi i1 i2 i3 | no ¬m with AdmK? (kind i) S
    ... | yes ad with Fitsᵁ? (pcs pre ∷ʳ toHi (kind i , len i)) cs
    ...   | yes f =
      pour ad f
        (subst (λ P → ChU S P cs false (pcs xr) vr) (pcs-∷ʳ pre i)
          (chF (xd ∷ʳ i) xr pfx S ℓ rest vr B0 (pre ∷ʳ i) cs (x-∷ʳ ex) e sh
            (trans (dur-∷ʳ xd i) (trans (cong (_+ᴰ len i) eb)
                     (trans (+ᴰ-assoc B0 _ _) (cong (B0 +ᴰ_) (sym (dur-∷ʳ pre i))))))
            (subst (_⊑ʰ sumʰ cs) (cong cl (sym (dur-∷ʳ pre i))) (fits-∷ʳ pre i cs f))
            i1
            (≤ᴰ-trans i2 (subst (dur xd ≤ᴰ_) (sym (dur-∷ʳ xd i)) (≤ᴰ-+ (dur xd) (len i))))
            (subst (λ u → OpsFrom u (σof pfx +ᴰ ℓ) rest) (sym (dur-∷ʳ xd i))
              (subst (λ v → OpsFrom (dur xd +ᴰ len i) v rest) (σ-∷ʳ pfx _)
                (lift xd i xr (pfx ∷ʳ _) rest ex (ps-∷ʳ e)
                  (subst (λ v → OpsFrom (dur xd) v rest) (sym (σ-∷ʳ pfx _)) i3) ¬m)))))
    ...   | no ¬f =
      over ad ¬f (overing ((σof pfx +ᴰ ℓ) ≤ᴰ? dur xd))
      where
        σ′ = σof pfx +ᴰ ℓ
        e′ = ps-∷ʳ e
        σ≡ : σof (pfx ∷ʳ (stk S , ℓ)) ≡ σ′
        σ≡ = σ-∷ʳ pfx _
        ¬f′ : ¬ (cl (dur pre +ᴰ len i) ⊑ʰ sumʰ cs)
        ¬f′ g = ¬f (subst (λ P → Fitsᵁ P cs) (pcs-∷ʳ pre i)
                      (fitsP (pre ∷ʳ i) cs (subst (_⊑ʰ sumʰ cs) (cong cl (sym (dur-∷ʳ pre i))) g)))
        σ′< : σ′ <ᴰ dur xd +ᴰ len i
        σ′< = subst (σ′ <ᴰ_) (trans (sym (+ᴰ-assoc B0 _ _)) (cong (_+ᴰ len i) (sym eb)))
                (past-chain ¬f′ i1)
        os : OpsFrom (dur xd +ᴰ len i) (σof (pfx ∷ʳ (stk S , ℓ))) rest
        os = lift xd i xr (pfx ∷ʳ _) rest ex e′ (subst (λ v → OpsFrom (dur xd) v rest) (sym σ≡) i3) ¬m
        overing : Dec (σ′ ≤ᴰ dur xd)
                → OverU (pcs pre) cs (toHi (kind i , len i)) (pcs xr) vr
        overing (yes s) =
          ovW xd i xr (pfx ∷ʳ _) rest vr B0 pre cs (dur xd) ex e′ sh eb fi
              (subst (_≤ᴰ dur xd) (sym σ≡) s) (item-end eb fi) ≤ᴰ-refl (<-+ (pos-len i)) os
        overing (no ¬s) =
          ovW xd i xr (pfx ∷ʳ _) rest vr B0 pre cs σ′ ex e′ sh eb fi
              (≤ᴰ-reflexive σ≡) i1 (<⇒≤ ¬s) σ′< os
    chF xd (i ∷ xr) pfx S ℓ rest vr B0 pre cs ex e sh eb fi i1 i2 i3 | no ¬m | no ¬ad with σof pfx +ᴰ ℓ ≤ᴰ? dur xd
    ... | yes s = close (clW xd i xr (pfx ∷ʳ _) rest vr ex (ps-∷ʳ e) sh
                          (subst (_≤ᴰ dur xd) (sym (σ-∷ʳ pfx _)) s)
                          (subst (λ v → OpsFrom (dur xd) v rest) (sym (σ-∷ʳ pfx _)) i3))
    ... | no ¬s = ⊥-elim (¬ad (cst ex e (dur xd) ≤ᴰ-refl (<-+ (pos-len i)) i2 ¬s))

    chM : ∀ xd i xr pfx S ℓ rest vr B0 pre cs t
        → x ≡ xd ++ i ∷ xr → ps ≡ pfx ++ (stk S , ℓ) ∷ rest → Shape vr rest
        → dur xd ≡ B0 +ᴰ dur pre
        → cl (dur pre) ⊑ʰ sumʰ cs
        → cl (σof pfx +ᴰ ℓ) ⊑ʰ cl B0 +ʰ sumʰ cs
        → σof pfx ≤ᴰ t → t <ᴰ σof pfx +ᴰ ℓ → dur xd ≤ᴰ t → t <ᴰ dur xd +ᴰ len i
        → OpsFrom (dur xd +ᴰ len i) (σof pfx +ᴰ ℓ) rest
        → ChU S (pcs pre) cs true (pcs (i ∷ xr)) vr
    chM xd i xr pfx S ℓ rest vr B0 pre cs t ex e sh eb fi i1 r₁ s₁ r₂ s₂ os
      with cst ex e t r₂ s₂ r₁ s₁ | Fitsᵁ? (pcs pre ∷ʳ toHi (kind i , len i)) cs
    ... | ad | yes f =
      pour ad f
        (subst (λ P → ChU S P cs false (pcs xr) vr) (pcs-∷ʳ pre i)
          (chF (xd ∷ʳ i) xr pfx S ℓ rest vr B0 (pre ∷ʳ i) cs (x-∷ʳ ex) e sh
            (trans (dur-∷ʳ xd i) (trans (cong (_+ᴰ len i) eb)
                     (trans (+ᴰ-assoc B0 _ _) (cong (B0 +ᴰ_) (sym (dur-∷ʳ pre i))))))
            (subst (_⊑ʰ sumʰ cs) (cong cl (sym (dur-∷ʳ pre i))) (fits-∷ʳ pre i cs f))
            i1
            (subst (σof pfx ≤ᴰ_) (sym (dur-∷ʳ xd i)) (≤ᴰ-trans r₁ (<⇒≤ s₂)))
            (subst (λ u → OpsFrom u (σof pfx +ᴰ ℓ) rest) (sym (dur-∷ʳ xd i)) os)))
    ... | ad | no ¬f =
      over ad ¬f
        (ovW xd i xr (pfx ∷ʳ _) rest vr B0 pre cs σ′ ex (ps-∷ʳ e) sh eb fi
             (≤ᴰ-reflexive (σ-∷ʳ pfx _)) i1 (≤ᴰ-trans r₂ (<⇒≤ s₁)) σ′<
             (subst (λ v → OpsFrom _ v rest) (sym (σ-∷ʳ pfx _)) os))
      where
        σ′ = σof pfx +ᴰ ℓ
        ¬f′ : ¬ (cl (dur pre +ᴰ len i) ⊑ʰ sumʰ cs)
        ¬f′ g = ¬f (subst (λ P → Fitsᵁ P cs) (pcs-∷ʳ pre i)
                      (fitsP (pre ∷ʳ i) cs (subst (_⊑ʰ sumʰ cs) (cong cl (sym (dur-∷ʳ pre i))) g)))
        σ′< : σ′ <ᴰ dur xd +ᴰ len i
        σ′< = subst (σ′ <ᴰ_) (trans (sym (+ᴰ-assoc B0 _ _)) (cong (_+ᴰ len i) (sym eb)))
                (past-chain ¬f′ i1)

    ovW : ∀ xd i xr pfx rest vr B0 pre cs t
        → x ≡ xd ++ i ∷ xr → ps ≡ pfx ++ rest → Shape vr rest
        → dur xd ≡ B0 +ᴰ dur pre
        → cl (dur pre) ⊑ʰ sumʰ cs
        → σof pfx ≤ᴰ t → cl t ⊑ʰ cl B0 +ʰ sumʰ cs → dur xd ≤ᴰ t → t <ᴰ dur xd +ᴰ len i
        → OpsFrom (dur xd +ᴰ len i) (σof pfx) rest
        → OverU (pcs pre) cs (toHi (kind i , len i)) (pcs xr) vr
    ovW xd i xr pfx [] [] B0 pre cs t ex e [] eb fi r₁ c₁ r₂ s₂ os =
      ⊥-elim (s₂ (≤ᴰ-trans end r₁))
      where
        end : dur xd +ᴰ len i ≤ᴰ σof pfx
        end = subst (dur xd +ᴰ len i ≤ᴰ_)
               (trans (sym (dur-x′ xd (i ∷ xr) ex)) (trans dur-x (trans (sym (rest-end pfx [] e)) (+ᴰ-identityʳ _))))
               (+ᴰ-monoʳ-≤ (dur xd) (≤ᴰ-+ (len i) (dur xr)))
    ovW xd i xr pfx ((opk o , τ) ∷ rest) (op o ∷ vr) B0 pre cs t ex e (op sh) eb fi r₁ c₁ r₂ s₂ (r , _) =
      ⊥-elim (s₂ (≤ᴰ-trans r r₁))
    ovW xd i xr pfx ((stk S , ℓ) ∷ rest) (st S h ∷ vr) B0 pre cs t ex e (st a sh) eb fi r₁ c₁ r₂ s₂ os
      with t <ᴰ? σof pfx +ᴰ ℓ
    ... | yes s =
      enter (chM xd i xr pfx S ℓ rest vr B0 pre (cs ∷ʳ h) t ex e sh eb (fits-more {cs = cs} fi a)
               (subst (cl (σof pfx +ᴰ ℓ) ⊑ʰ_) (cong (cl B0 +ʰ_) (sym (sumʰ-∷ʳ cs h)))
                  (extend (⊑ʰ-trans (cl-≤ r₁) c₁) a))
               r₁ s r₂ s₂ os)
    ... | no ¬s =
      pass (ovW xd i xr (pfx ∷ʳ _) rest vr B0 pre cs t ex (ps-∷ʳ e) sh eb fi
              (subst (_≤ᴰ t) (sym (σ-∷ʳ pfx _)) (≮⇒≥ ¬s)) c₁ r₂ s₂
              (subst (λ v → OpsFrom _ v rest) (sym (σ-∷ʳ pfx _)) os))

    clW : ∀ xd i xr pfx rest vr
        → x ≡ xd ++ i ∷ xr → ps ≡ pfx ++ rest → Shape vr rest
        → σof pfx ≤ᴰ dur xd → OpsFrom (dur xd) (σof pfx) rest
        → RunU (pcs (i ∷ xr)) vr
    clW xd i xr pfx [] [] ex e [] r os =
      ⊥-elim (<-irrefl (<-≤-trans (<-+ (pos-len i)) (≤ᴰ-trans le r)))
      where
        le : dur xd +ᴰ len i ≤ᴰ σof pfx
        le = subst (dur xd +ᴰ len i ≤ᴰ_)
               (trans (sym (dur-x′ xd (i ∷ xr) ex)) (trans dur-x (trans (sym (rest-end pfx [] e)) (+ᴰ-identityʳ _))))
               (+ᴰ-monoʳ-≤ (dur xd) (≤ᴰ-+ (len i) (dur xr)))
    clW xd i xr pfx ((opk o , τ) ∷ rest) (op o ∷ vr) ex e (op sh) r (r′ , os)
      with cop ex e (dur xd) ≤ᴰ-refl (<-+ (pos-len i)) r
             (subst (_<ᴰ σof pfx +ᴰ τ) (sym (≤ᴰ-antisym r′ r))
               (subst (_<ᴰ σof pfx +ᴰ τ) (+ᴰ-identityʳ _)
                 (+ᴰ-monoʳ-< (σof pfx) (proj₁ (opPos pfx _ e)))))
    ... | d , refl , refl , eb =
      match refl (runR (xd ∷ʳ i) xr (pfx ∷ʳ _) rest vr (x-∷ʳ ex) (ps-∷ʳ e) sh
                   (trans (dur-∷ʳ xd i) (trans (cong (_+ᴰ ∣ d ∣⁺) eb) (sym (σ-∷ʳ pfx _)))))
    clW xd i xr pfx ((stk S , ℓ) ∷ rest) (st S h ∷ vr) ex e (st a sh) r os with dur xd <ᴰ? σof pfx +ᴰ ℓ
    ... | yes s =
      start (chF xd (i ∷ xr) pfx S ℓ rest vr (dur xd) [] (h ∷ []) ex e sh (sym (+ᴰ-identityʳ _))
               (subst (cl 0ᴰ ⊑ʰ_) (sym (one-cap h)) (cap-0 a))
               (subst (cl (σof pfx +ᴰ ℓ) ⊑ʰ_) (cong (cl (dur xd) +ʰ_) (sym (one-cap h)))
                  (+ʰ-mono {cl (σof pfx)} (cl-≤ r) a))
               r (ops-from-start (σof pfx +ᴰ ℓ) rest (<⇒≤ s)))
    ... | no ¬s =
      start (close (clW xd i xr (pfx ∷ʳ _) rest vr ex (ps-∷ʳ e) sh
                      (subst (_≤ᴰ dur xd) (sym (σ-∷ʳ pfx _)) (≮⇒≥ ¬s))
                      (subst (λ v → OpsFrom _ v rest) (sym (σ-∷ʳ pfx _)) os)))

    endW : ∀ pfx rest vr → ps ≡ pfx ++ rest → Shape vr rest
         → OpsFrom (dur y) (σof pfx) rest → RunU [] vr
    endW pfx [] [] e [] _ = done
    endW pfx ((opk o , τ) ∷ rest) (op o ∷ vr) e (op sh) (r , _) =
      ⊥-elim (<-irrefl (<-≤-trans (subst (_<ᴰ σof pfx +ᴰ τ) (+ᴰ-identityʳ _)
                         (+ᴰ-monoʳ-< (σof pfx) (proj₁ (opPos pfx _ e))))
                  (≤ᴰ-trans (end-≤ pfx _ rest e) r)))
    endW pfx ((stk S , ℓ) ∷ rest) (st S h ∷ vr) e (st a sh) os =
      start (close (endW (pfx ∷ʳ _) rest vr (ps-∷ʳ e) sh
                      (subst (λ v → OpsFrom _ v rest) (sym (σ-∷ʳ pfx _)) os)))

------------------------------------------------------------------------
-- Every fit is read

read : ∀ {x y v} → Inst y v → x ⊑ y → RunU (pcs x) v
read {x} {y} {v} (ps , sh , wy) fit = Fit.runR x y ps wy fit [] x [] ps v refl refl sh refl
