------------------------------------------------------------------------
-- An accepting upper run on an exact run against closed bounds       --
-- builds a word of the bound that the run fits.                      --
--                                                                    --
-- Along a chain, each stretch the run overflows is filled to its     --
-- bound, and the stretch the chain is closed in takes what remains;  --
-- a stretch passed on the way has length zero. The walk of `Pour`    --
-- follows the run piece by piece.                                    --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Reader.Upper.Build
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_; map; [_])
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Monus T
open import Grades.Durations.Solver T using (solve; _⊜_; _⊕_)
open import Grades.Durations.Intervals T using (≤⇒⁺⊑⁺)

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Pour T Op n code code-injective
open import Grades.Exact.Letters T Op n code code-injective running
open import Grades.Exact.Reader.Upper T Op n code code-injective running

------------------------------------------------------------------------
-- The first item of an exact run, read from its first piece

data Head : Pc → Word → Word → Set where
  none : ∀ {S τ x} → τ ≡ 0ᴰ → Head (stk S , τ) x x
  one  : ∀ {k τ x} (i : Item) → kind i ≡ k → len i ≡ τ → Head (k , τ) (i ∷ x) x

head-of : ∀ {p cps x} → WordOf (p ∷ cps) x → Σ[ x′ ∈ Word ] Head p x x′ × WordOf cps x′
head-of (op {o} {d} r wo) = _ , one (op o d) refl refl , wo
head-of (st {S} {τ} {ps} {x} wo) = go (sview S τ)
  where
    go : ∀ {z} → SView S τ z → Σ[ x′ ∈ Word ] Head (stk S , τ) (z ++ x) x′ × WordOf ps x′
    go (vzero e)   = x , none e , wo
    go (vpos e e′) = x , one (st e S) refl e′ , wo

------------------------------------------------------------------------
-- Where the walk stands in a chain

-- `X` is poured into the chain, `Cp` fills its earlier stretches; a
-- fresh piece starts with `oy` already in the current stretch, an
-- overflowing one has `ox` of itself in the earlier stretches

data Mode (X Cp ox oy : Carrier) : Bool → Set where
  fresh : ox ≡ 0ᴰ → Cp +ᴰ oy ≡ X → Mode X Cp ox oy false
  mid   : oy ≡ 0ᴰ → X +ᴰ ox ≡ Cp → Mode X Cp ox oy true

MidOK : Bool → Carrier → List Pc → Set
MidOK false _  _            = ⊤
MidOK true  _  []           = ⊥
MidOK true  ox ((_ , τ) ∷ _) = ox <ᴰ τ

private
  variable
    a b c q : Carrier

  split : a ≤ᴰ b → Σ[ q ∈ Carrier ] a +ᴰ q ≡ b
  split = diff

  inst-st : ∀ {S s c y vc} → s ≤ᴰ c → Inst y (map clo vc) → Inst (stretch S s ++ y) (map clo (st S c ∷ vc))
  inst-st {S} {s} r (ps , sh , wo) = (stk S , s) ∷ ps , st (≤⇒⁺⊑⁺ r) sh , st wo

  stretch-0 : ∀ S → stretch S 0ᴰ ≡ []
  stretch-0 S = stretch-zero S 0ᴰ (λ p → <⇒≢ p refl)

  amts-∷ʳ : ∀ pre p → sumᴰ (amts (pre ∷ʳ p)) ≡ sumᴰ (amts pre) +ᴰ proj₂ p
  amts-∷ʳ pre p = trans (cong sumᴰ (map-∷ʳ proj₂ pre p)) (sumᴰ-∷ʳ (amts pre) (proj₂ p))

------------------------------------------------------------------------
-- Arithmetic of the two modes

module _ {X Cp ox oy : Carrier} where

  mode-ox≤ : ∀ {m k τ cps} → Mode X Cp ox oy m → MidOK m ox ((k , τ) ∷ cps) → ox ≤ᴰ τ
  mode-ox≤ {τ = τ} (fresh refl _) _  = 0ᴰ-least τ
  mode-ox≤         (mid _ _)      mo = <⇒≤ mo

  mode-zero : ∀ {m k τ cps} → Mode X Cp ox oy m → MidOK m ox ((k , τ) ∷ cps) → τ ≡ 0ᴰ → ox ≡ 0ᴰ
  mode-zero (fresh e _) _  _ = e
  mode-zero (mid _ _)   mo e = ⊥-elim (mo (subst (_≤ᴰ ox) (sym e) (0ᴰ-least ox)))

  mode-pour : ∀ {m q τ} → Mode X Cp ox oy m → ox +ᴰ q ≡ τ → Cp +ᴰ (oy +ᴰ q) ≡ X +ᴰ τ
  mode-pour {q = q} (fresh refl eX) eq =
    trans (sym (+ᴰ-assoc Cp oy q)) (cong₂ _+ᴰ_ eX (trans (sym (+ᴰ-identityˡ q)) eq))
  mode-pour {q = q} (mid refl eX) eq =
    trans (cong (Cp +ᴰ_) (+ᴰ-identityˡ q))
          (trans (cong (_+ᴰ q) (sym eX)) (trans (+ᴰ-assoc X ox q) (cong (X +ᴰ_) eq)))

  mode-oy≤ : ∀ {m c Ctot} → Mode X Cp ox oy m → Cp +ᴰ c ≡ Ctot → X ≤ᴰ Ctot → oy ≤ᴰ c
  mode-oy≤ (fresh _ eX) eC fX = +ᴰ-cancelˡ-≤ Cp (subst₂ _≤ᴰ_ (sym eX) (sym eC) fX)
  mode-oy≤ {c = c} (mid refl _) _ _ = 0ᴰ-least c

  mode-full : ∀ {m q c Ctot} → Mode X Cp ox oy m → oy +ᴰ q ≡ c → Cp +ᴰ c ≡ Ctot
            → X +ᴰ (ox +ᴰ q) ≡ Ctot
  mode-full {q = q} (fresh refl eX) eq eC =
    trans (cong (X +ᴰ_) (+ᴰ-identityˡ q))
          (trans (cong (_+ᴰ q) (sym eX)) (trans (+ᴰ-assoc Cp oy q) (trans (cong (Cp +ᴰ_) eq) eC)))
  mode-full {q = q} (mid refl eX) eq eC =
    trans (sym (+ᴰ-assoc X ox q))
          (trans (cong (_+ᴰ q) eX) (trans (cong (Cp +ᴰ_) (trans (sym (+ᴰ-identityˡ q)) eq)) eC))

------------------------------------------------------------------------
-- The construction

mutual

  build-run : ∀ {cps vc x} → WordOf cps x → RunU (map toHi cps) (map clo vc)
            → Σ[ y ∈ Word ] Inst y (map clo vc) × Pour x 0ᴰ y 0ᴰ
  build-run {[]} {[]} [] done = [] , ([] , [] , []) , done
  build-run {_ ∷ cps} {op o ∷ vc} (op {d = d} r wo) (match refl h) with build-run wo h
  ... | y , (ps , sh , wy) , w = op o d ∷ y , ((opk o , ∣ d ∣⁺) ∷ ps , op sh , op r wy) , match w
  build-run {_ ∷ cps} {op o ∷ vc} (st wo) (match () h)
  build-run {cps} {st S c ∷ vc} wo (start h)
    with build-ch {S} {[]} {c ∷ []} {false} {cps} {vc} 0ᴰ c 0ᴰ 0ᴰ
           (trans (+ᴰ-identityˡ c) (sym (+ᴰ-identityʳ c)))
           (fresh refl (+ᴰ-identityˡ 0ᴰ)) tt (0ᴰ-least _) wo h
  ... | s , s≤c , _ , y , iy , w = stretch S s ++ y , inst-st s≤c iy , w

  build-ch : ∀ {S preC csC m cps vc x} Cp c ox oy
           → Cp +ᴰ c ≡ sumᴰ csC
           → Mode (sumᴰ (amts preC)) Cp ox oy m
           → MidOK m ox cps
           → sumᴰ (amts preC) ≤ᴰ sumᴰ csC
           → WordOf cps x
           → ChU S (map toHi preC) (map cl csC) m (map toHi cps) (map clo vc)
           → Σ[ s ∈ Carrier ] s ≤ᴰ c × oy ≤ᴰ s
             × Σ[ y ∈ Word ] Inst y (map clo vc) × Pour x ox (stretch S s ++ y) oy
  build-ch {S} {preC} {csC} {m} {p@(k , τ) ∷ cps} {vc} {x} Cp c ox oy eC md mo fX wo (pour ad f h)
    with head-of wo | split (mode-ox≤ md mo)
  ... | x′ , hd , wo′ | q , eq
    with build-ch {S} {preC ∷ʳ p} {csC} {false} {cps} {vc} Cp c 0ᴰ (oy +ᴰ q) eC
           (fresh refl (trans (mode-pour md eq) (sym (amts-∷ʳ preC p)))) tt
           (fits⇒ (preC ∷ʳ p) csC
              (subst (λ P → Fitsᵁ P (map cl csC)) (sym (map-∷ʳ toHi preC p)) f))
           wo′
           (subst (λ P → ChU S P (map cl csC) false (map toHi cps) (map clo vc))
                  (sym (map-∷ʳ toHi preC p)) h)
  ... | s , s≤c , oy′≤s , y , iy , w =
    s , s≤c , ≤ᴰ-trans (≤ᴰ-+ oy q) oy′≤s , y , iy , walk hd w
    where
      walk : ∀ {x} → Head p x x′ → Pour x′ 0ᴰ (stretch S s ++ y) (oy +ᴰ q)
           → Pour x ox (stretch S s ++ y) oy
      walk (none e) w′ =
        subst (λ u → Pour x′ u (stretch S s ++ y) oy) (sym ox0)
          (subst (Pour x′ 0ᴰ (stretch S s ++ y)) (trans (cong (oy +ᴰ_) q0) (+ᴰ-identityʳ oy)) w′)
        where
          ox0 = mode-zero md mo e
          q0 : q ≡ 0ᴰ
          q0 = trans (sym (+ᴰ-identityˡ q)) (trans (cong (_+ᴰ q) (sym ox0)) (trans eq e))
      walk (one i ek el) w′ =
        walk-pour s q (adm-kind i (subst (λ k′ → AdmK k′ S) (sym ek) ad)) (trans eq (sym el))
                  oy′≤s w′
  build-ch {S} {preC} {csC} {m} {p@(k , τ) ∷ cps} {vc} {x} Cp c ox oy eC md mo fX wo (over ad ¬f o)
    with split (mode-oy≤ md eC fX)
  ... | q , eq = c , ≤ᴰ-refl , subst (oy ≤ᴰ_) eq (≤ᴰ-+ oy q) , go wo (head-of wo)
    where
      X = sumᴰ (amts preC)
      Ctot = sumᴰ csC
      full : X +ᴰ (ox +ᴰ q) ≡ Ctot
      full = mode-full md eq eC
      over-τ : Ctot <ᴰ X +ᴰ τ
      over-τ r = ¬f (subst (λ P → Fitsᵁ P (map cl csC)) (map-∷ʳ toHi preC p)
                      (⇒fits (preC ∷ʳ p) csC (subst (_≤ᴰ Ctot) (sym (amts-∷ʳ preC p)) r)))
      ox′<τ : ox +ᴰ q <ᴰ τ
      ox′<τ r = over-τ (subst (λ u → X +ᴰ τ ≤ᴰ u) full (+ᴰ-monoʳ-≤ X r))
      go : ∀ {x} → WordOf (p ∷ cps) x → Σ[ x′ ∈ Word ] Head p x x′ × WordOf cps x′
         → Σ[ y ∈ Word ] Inst y (map clo vc) × Pour x ox (stretch S c ++ y) oy
      go _ (_ , none e , _) = ⊥-elim (ox′<τ (subst (_≤ᴰ ox +ᴰ q) (sym e) (0ᴰ-least _)))
      go wo′ (x′ , one i ek el , _) with build-over {preC} {csC} {p} {cps} {vc} (ox +ᴰ q) full ox′<τ fX wo′ o
      ... | y , iy , w =
        y , iy , walk-fill c q (adm-kind i (subst (λ k′ → AdmK k′ S) (sym ek) ad)) eq
                   (subst (ox +ᴰ q ≤ᴰ_) (sym el) (<⇒≤ ox′<τ)) w

  build-ch {S} {preC} {csC} {false} {cps} {vc} {x} Cp c ox oy eC (fresh ox0 eX) _ fX wo (close r)
    with build-run wo r
  ... | y , iy , w =
    oy , oy≤c , ≤ᴰ-refl , y , iy ,
    subst (λ u → Pour x u (stretch S oy ++ y) oy) (sym ox0) (walk-past oy w)
    where
      oy≤c : oy ≤ᴰ c
      oy≤c = +ᴰ-cancelˡ-≤ Cp (subst₂ _≤ᴰ_ (sym eX) (sym eC) fX)
  build-over : ∀ {preC csC p cps vc x} ox
             → sumᴰ (amts preC) +ᴰ ox ≡ sumᴰ csC
             → ox <ᴰ proj₂ p
             → sumᴰ (amts preC) ≤ᴰ sumᴰ csC
             → WordOf (p ∷ cps) x
             → OverU (map toHi preC) (map cl csC) (toHi p) (map toHi cps) (map clo vc)
             → Σ[ y ∈ Word ] Inst y (map clo vc) × Pour x ox y 0ᴰ
  build-over {preC} {csC} {p} {cps} {st S c ∷ vc} {x} ox e lt fX wo (enter h)
    with build-ch {S} {preC} {csC ∷ʳ c} {true} {p ∷ cps} {vc} (sumᴰ csC) c ox 0ᴰ
           (sym (sumᴰ-∷ʳ csC c)) (mid refl e) lt
           (≤ᴰ-trans fX (subst (sumᴰ csC ≤ᴰ_) (sym (sumᴰ-∷ʳ csC c)) (≤ᴰ-+ (sumᴰ csC) c)))
           wo
           (subst (λ C → ChU S (map toHi preC) C true (map toHi (p ∷ cps)) (map clo vc))
                  (sym (map-∷ʳ cl csC c)) h)
  ... | s , s≤c , _ , y , iy , w = stretch S s ++ y , inst-st s≤c iy , w
  build-over {preC} {csC} {p} {cps} {st S c ∷ vc} {x} ox e lt fX wo (pass o)
    with build-over {preC} {csC} {p} {cps} {vc} ox e lt fX wo o
  ... | y , iy , w =
    stretch S 0ᴰ ++ y , inst-st (0ᴰ-least c) iy ,
    subst (λ z → Pour x ox (z ++ y) 0ᴰ) (sym (stretch-0 S)) w
