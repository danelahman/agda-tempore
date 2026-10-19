------------------------------------------------------------------------
-- An accepting lower run on an exact run against closed bounds       --
-- builds a word of the bound that the run fits.                      --
--                                                                    --
-- Along a chain, each stretch the run overflows out of takes exactly --
-- its bound, and the stretch the chain is closed in takes what       --
-- remains.                                                           --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module Syntax.Grades.Exact.Reader.Lower.Build
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

open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T using (≤⇒⁻⊑⁻)

open import Syntax.Grades.Exact.Base T Op n code code-injective
open import Syntax.Grades.Exact.Pour T Op n code code-injective
open import Syntax.Grades.Exact.Letters T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Lower T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Upper T Op n code code-injective running
  using (walk-past; walk-pour; walk-fill; sumᴰ-∷ʳ; map-∷ʳ)
open import Syntax.Grades.Exact.Reader.Upper.Build T Op n code code-injective running
  using (Head; none; one; head-of; Mode; fresh; mid; mode-pour; mode-full)

MidOKᴸ : Bool → Carrier → List (Piece Carrier) → Set
MidOKᴸ false _  _             = ⊤
MidOKᴸ true  _  []            = ⊥
MidOKᴸ true  ox ((_ , τ) ∷ _) = ox ≤ᴰ τ

private
  variable
    a b c q : Carrier

  inst-st : ∀ {S s c y vc} → c ≤ᴰ s → Inst y (map clo⁻ vc) → Inst (stretch S s ++ y) (map clo⁻ (st S c ∷ vc))
  inst-st {S} {s} r (ps , sh , wo) = (stk S , s) ∷ ps , st (≤⇒⁻⊑⁻ r) sh , st wo

  amts-∷ʳ : ∀ pre p → sumᴰ (amts (pre ∷ʳ p)) ≡ sumᴰ (amts pre) +ᴰ proj₂ p
  amts-∷ʳ pre p = trans (cong sumᴰ (map-∷ʳ proj₂ pre p)) (sumᴰ-∷ʳ (amts pre) (proj₂ p))

  modeᴸ-ox≤ : ∀ {X Cp ox oy m k τ cps} → Mode X Cp ox oy m → MidOKᴸ m ox ((k , τ) ∷ cps) → ox ≤ᴰ τ
  modeᴸ-ox≤ {τ = τ} (fresh refl _) _  = 0ᴰ-least τ
  modeᴸ-ox≤         (mid _ _)      mo = mo

  -- the bounds of a closed chain met: the current stretch reaches its bound
  modeᴸ-close : ∀ {X Cp ox oy c Ctot} → Mode X Cp ox oy false → Cp +ᴰ c ≡ Ctot → Ctot ≤ᴰ X → c ≤ᴰ oy
  modeᴸ-close {Cp = Cp} (fresh _ eX) eC f = +ᴰ-cancelˡ-≤ Cp (subst₂ _≤ᴰ_ (sym eC) (sym eX) f)

  -- the bounds not yet met: the current stretch is short of its bound
  modeᴸ-oy< : ∀ {X Cp ox oy m c Ctot} → Mode X Cp ox oy m → Cp +ᴰ c ≡ Ctot → X <ᴰ Ctot → oy ≤ᴰ c
  modeᴸ-oy< {Cp = Cp} {c = c} (fresh _ eX) eC f =
    +ᴰ-cancelˡ-≤ Cp (<⇒≤ (subst₂ _<ᴰ_ (sym eX) (sym eC) f))
  modeᴸ-oy< {c = c} (mid refl _) _ _ = 0ᴰ-least c

mutual

  build-runᴸ : ∀ {cps vc x} → WordOf cps x → RunL (map toLo cps) (map clo⁻ vc)
             → Σ[ y ∈ Word ] Inst y (map clo⁻ vc) × Pour x 0ᴰ y 0ᴰ
  build-runᴸ {[]} {[]} [] done = [] , ([] , [] , []) , done
  build-runᴸ {_ ∷ cps} {op o ∷ vc} (op {d = d} r wo) (match refl h) with build-runᴸ wo h
  ... | y , (ps , sh , wy) , w = op o d ∷ y , ((opk o , ∣ d ∣⁺) ∷ ps , op sh , op r wy) , match w
  build-runᴸ {_ ∷ cps} {op o ∷ vc} (st wo) (match () h)
  build-runᴸ {cps} {st S c ∷ vc} wo (start h)
    with build-chᴸ {S} {[]} {c ∷ []} {false} {cps} {vc} 0ᴰ c 0ᴰ 0ᴰ
           (trans (+ᴰ-identityˡ c) (sym (+ᴰ-identityʳ c)))
           (fresh refl (+ᴰ-identityˡ 0ᴰ)) tt wo h
  ... | s , c≤s , _ , y , iy , w = stretch S s ++ y , inst-st c≤s iy , w

  build-chᴸ : ∀ {S preC csC m cps vc x} Cp c ox oy
            → Cp +ᴰ c ≡ sumᴰ csC
            → Mode (sumᴰ (amts preC)) Cp ox oy m
            → MidOKᴸ m ox cps
            → WordOf cps x
            → ChL S (map toLo preC) (map cl⁻ csC) m (map toLo cps) (map clo⁻ vc)
            → Σ[ s ∈ Carrier ] c ≤ᴰ s × oy ≤ᴰ s
              × Σ[ y ∈ Word ] Inst y (map clo⁻ vc) × Pour x ox (stretch S s ++ y) oy
  build-chᴸ {S} {preC} {csC} {m} {p@(k , τ) ∷ cps} {st S′ c′ ∷ vc} {x} Cp c ox oy eC md mo wo
            (over ad ¬f g h)
    with diff (modeᴸ-oy< md eC X<C)
    where
      X<C : sumᴰ (amts preC) <ᴰ sumᴰ csC
      X<C r = ¬f (⇒fitsᴸ preC csC r)
  ... | q , eq = c , ≤ᴰ-refl , subst (oy ≤ᴰ_) eq (≤ᴰ-+ oy q) , go wo (head-of wo)
    where
      X = sumᴰ (amts preC)
      Ctot = sumᴰ csC
      full : X +ᴰ (ox +ᴰ q) ≡ Ctot
      full = mode-full md eq eC
      within : Ctot ≤ᴰ X +ᴰ τ
      within = subst (Ctot ≤ᴰ_) (amts-∷ʳ preC p)
                 (fitsᴸ⇒ (preC ∷ʳ p) csC (subst (λ P → Fitsᴸ P (map cl⁻ csC)) (sym (map-∷ʳ toLo preC p)) g))
      ox′≤τ : ox +ᴰ q ≤ᴰ τ
      ox′≤τ = +ᴰ-cancelˡ-≤ X (subst (_≤ᴰ X +ᴰ τ) (sym full) within)
      X<C : X <ᴰ Ctot
      X<C r = ¬f (⇒fitsᴸ preC csC r)
      go : ∀ {x} → WordOf (p ∷ cps) x → Σ[ x′ ∈ Word ] Head p x x′ × WordOf cps x′
         → Σ[ y ∈ Word ] Inst y (map clo⁻ (st S′ c′ ∷ vc)) × Pour x ox (stretch S c ++ y) oy
      go _ (_ , none e , _) =
        ⊥-elim (X<C (subst (Ctot ≤ᴰ_) (trans (cong (X +ᴰ_) e) (+ᴰ-identityʳ X)) within))
      go wo′ (x′ , one i ek el , _)
        with build-chᴸ {S′} {preC} {csC ∷ʳ c′} {true} {p ∷ cps} {vc} Ctot c′ (ox +ᴰ q) 0ᴰ
               (sym (sumᴰ-∷ʳ csC c′)) (mid refl full) ox′≤τ wo′
               (subst (λ C → ChL S′ (map toLo preC) C true (map toLo (p ∷ cps)) (map clo⁻ vc))
                      (sym (map-∷ʳ cl⁻ csC c′)) h)
      ... | s , c≤s , _ , y , iy , w =
        stretch S′ s ++ y , inst-st c≤s iy ,
        walk-fill c q (adm-kind i (subst (λ k′ → AdmK k′ S) (sym ek) ad)) eq
                  (subst (ox +ᴰ q ≤ᴰ_) (sym el) ox′≤τ) w
  build-chᴸ {S} {preC} {csC} {m} {p@(k , τ) ∷ cps} {vc} {x} Cp c ox oy eC md mo wo (pour ad h)
    with head-of wo | diff (modeᴸ-ox≤ md mo)
  ... | x′ , hd , wo′ | q , eq
    with build-chᴸ {S} {preC ∷ʳ p} {csC} {false} {cps} {vc} Cp c 0ᴰ (oy +ᴰ q) eC
           (fresh refl (trans (mode-pour md eq) (sym (amts-∷ʳ preC p)))) tt wo′
           (subst (λ P → ChL S P (map cl⁻ csC) false (map toLo cps) (map clo⁻ vc))
                  (sym (map-∷ʳ toLo preC p)) h)
  ... | s , c≤s , oy′≤s , y , iy , w =
    s , c≤s , ≤ᴰ-trans (≤ᴰ-+ oy q) oy′≤s , y , iy , walk hd w
    where
      walk : ∀ {x} → Head p x x′ → Pour x′ 0ᴰ (stretch S s ++ y) (oy +ᴰ q)
           → Pour x ox (stretch S s ++ y) oy
      walk (none e) w′ =
        subst (λ u → Pour x′ u (stretch S s ++ y) oy) (sym ox0)
          (subst (Pour x′ 0ᴰ (stretch S s ++ y)) (trans (cong (oy +ᴰ_) q0) (+ᴰ-identityʳ oy)) w′)
        where
          ox0 : ox ≡ 0ᴰ
          ox0 = ≤0⇒≡0 (subst (ox ≤ᴰ_) e (modeᴸ-ox≤ md mo))
          q0 : q ≡ 0ᴰ
          q0 = trans (sym (+ᴰ-identityˡ q)) (trans (cong (_+ᴰ q) (sym ox0)) (trans eq e))
      walk (one i ek el) w′ =
        walk-pour s q (adm-kind i (subst (λ k′ → AdmK k′ S) (sym ek) ad)) (trans eq (sym el))
                  oy′≤s w′
  build-chᴸ {S} {preC} {csC} {false} {cps} {vc} {x} Cp c ox oy eC (fresh ox0 eX) _ wo (close f r)
    with build-runᴸ wo r
  ... | y , iy , w =
    oy , modeᴸ-close (fresh ox0 eX) eC (fitsᴸ⇒ preC csC f) , ≤ᴰ-refl , y , iy ,
    subst (λ u → Pour x u (stretch S oy ++ y) oy) (sym ox0) (walk-past oy w)
