------------------------------------------------------------------------
-- The pouring reader.                                                --
--                                                                    --
-- The reader walks a lesser word, given as pieces (a kind and a      --
-- weight), against a greater word of letters. An operation letter    --
-- of the greater word is met by the same operation. Its stretch      --
-- letters are read in chains: the pieces poured into a chain are     --
-- collected in `pre`, the bounds of its stretches in `cs`, and       --
-- `Fits pre cs` compares the two. A piece is poured into the current --
-- stretch when that stretch admits its kind; a piece that overflows  --
-- the stretch continues into a later one, which joins the chain; a   --
-- chain is closed between two pieces.                                --
--                                                                    --
--   upper: a piece is poured whole when the chain still fits with    --
--          it, and overflows otherwise, passing stretches at length  --
--          zero on its way; a chain is closed freely, so a stretch   --
--          may be passed at length zero;                             --
--   lower: a piece is poured whole freely, and overflows into the    --
--          next stretch when the chain's bounds are met inside it    --
--          and not before; a chain is closed once its bounds are     --
--          met.                                                      --
--                                                                    --
-- `mid` records that the first piece has already overflowed, so the  --
-- chain cannot be closed before it. Weights and bounds are abstract  --
-- here: the extremal reading of a word and the exact reading of a    --
-- run are two instances of one reader.                               --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Reader
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _∷ʳ_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Exact.Base T Op n code code-injective using (OpSet; _≟ˢ_; _≟ₒ_)
open import Grades.Exact.Letters T Op n code code-injective running

------------------------------------------------------------------------
-- Kinds compare

_≟ᴷ_ : DecidableEquality Kind
opk o ≟ᴷ opk o′ with o ≟ₒ o′
... | yes refl = yes refl
... | no ¬e    = no λ { refl → ¬e refl }
stk S ≟ᴷ stk S′ with S ≟ˢ S′
... | yes refl = yes refl
... | no ¬e    = no λ { refl → ¬e refl }
opk _ ≟ᴷ stk _ = no λ ()
stk _ ≟ᴷ opk _ = no λ ()

------------------------------------------------------------------------
-- The upper reader

module Upper {P L : Set} (κ : P → Kind) (Fits : List P → List L → Set) where

  mutual

    data RunU : List P → List (Letter L) → Set where
      done  : RunU [] []
      match : ∀ {p ps o v} → κ p ≡ opk o → RunU ps v → RunU (p ∷ ps) (op o ∷ v)
      start : ∀ {S c ps v} → ChU S [] (c ∷ []) false ps v → RunU ps (st S c ∷ v)

    data ChU (S : OpSet) (pre : List P) (cs : List L)
           : Bool → List P → List (Letter L) → Set where
      pour  : ∀ {m p ps v} → AdmK (κ p) S → Fits (pre ∷ʳ p) cs
            → ChU S (pre ∷ʳ p) cs false ps v → ChU S pre cs m (p ∷ ps) v
      over  : ∀ {m p ps v} → AdmK (κ p) S → ¬ Fits (pre ∷ʳ p) cs
            → OverU pre cs p ps v → ChU S pre cs m (p ∷ ps) v
      close : ∀ {ps v} → RunU ps v → ChU S pre cs false ps v

    data OverU (pre : List P) (cs : List L) (p : P) (ps : List P)
           : List (Letter L) → Set where
      enter : ∀ {S c v} → ChU S pre (cs ∷ʳ c) true (p ∷ ps) v
            → OverU pre cs p ps (st S c ∷ v)
      pass  : ∀ {S c v} → OverU pre cs p ps v → OverU pre cs p ps (st S c ∷ v)

  module Decide (Fits? : ∀ pre cs → Dec (Fits pre cs)) where

    private
      _∨ᵈ_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
      yes a ∨ᵈ _     = yes (inj₁ a)
      no _  ∨ᵈ yes b = yes (inj₂ b)
      no ¬a ∨ᵈ no ¬b = no λ { (inj₁ a) → ¬a a ; (inj₂ b) → ¬b b }

    mutual

      runU? : ∀ ps v → Dec (RunU ps v)
      runU? []       []           = yes done
      runU? (p ∷ ps) []           = no λ ()
      runU? []       (op o ∷ v)   = no λ ()
      runU? (p ∷ ps) (op o ∷ v) with κ p ≟ᴷ opk o | runU? ps v
      ... | yes e | yes r = yes (match e r)
      ... | no ¬e | _     = no λ { (match e _) → ¬e e }
      ... | yes _ | no ¬r = no λ { (match _ r) → ¬r r }
      runU? ps       (st S c ∷ v) with chU? S [] (c ∷ []) false ps v
      ... | yes h = yes (start h)
      ... | no ¬h = no λ { (start h) → ¬h h }

      chU? : ∀ S pre cs m ps v → Dec (ChU S pre cs m ps v)
      chU? S pre cs true  []       v = no λ ()
      chU? S pre cs false []       v with runU? [] v
      ... | yes r = yes (close r)
      ... | no ¬r = no λ { (close r) → ¬r r }
      chU? S pre cs m     (p ∷ ps) v with AdmK? (κ p) S
      ... | no ¬a = closing m ¬a
        where
          closing : ∀ m → ¬ AdmK (κ p) S → Dec (ChU S pre cs m (p ∷ ps) v)
          closing true  ¬a = no λ { (pour a _ _) → ¬a a ; (over a _ _) → ¬a a }
          closing false ¬a with runU? (p ∷ ps) v
          ... | yes r = yes (close r)
          ... | no ¬r = no λ { (pour a _ _) → ¬a a ; (over a _ _) → ¬a a ; (close r) → ¬r r }
      ... | yes a with Fits? (pre ∷ʳ p) cs
      ...   | yes f = pouring m (chU? S (pre ∷ʳ p) cs false ps v)
        where
          pouring : ∀ m → Dec (ChU S (pre ∷ʳ p) cs false ps v) → Dec (ChU S pre cs m (p ∷ ps) v)
          pouring m     (yes h) = yes (pour a f h)
          pouring true  (no ¬h) = no λ { (pour _ _ h) → ¬h h ; (over _ ¬f _) → ¬f f }
          pouring false (no ¬h) with runU? (p ∷ ps) v
          ... | yes r = yes (close r)
          ... | no ¬r = no λ { (pour _ _ h) → ¬h h ; (over _ ¬f _) → ¬f f ; (close r) → ¬r r }
      ...   | no ¬f = overing m (overU? pre cs p ps v)
        where
          overing : ∀ m → Dec (OverU pre cs p ps v) → Dec (ChU S pre cs m (p ∷ ps) v)
          overing m     (yes o) = yes (over a ¬f o)
          overing true  (no ¬o) = no λ { (pour _ f _) → ¬f f ; (over _ _ o) → ¬o o }
          overing false (no ¬o) with runU? (p ∷ ps) v
          ... | yes r = yes (close r)
          ... | no ¬r = no λ { (pour _ f _) → ¬f f ; (over _ _ o) → ¬o o ; (close r) → ¬r r }

      overU? : ∀ pre cs p ps v → Dec (OverU pre cs p ps v)
      overU? pre cs p ps []           = no λ ()
      overU? pre cs p ps (op o ∷ v)   = no λ ()
      overU? pre cs p ps (st S c ∷ v) with chU? S pre (cs ∷ʳ c) true (p ∷ ps) v
      ... | yes h = yes (enter h)
      ... | no ¬h with overU? pre cs p ps v
      ...   | yes o = yes (pass o)
      ...   | no ¬o = no λ { (enter h) → ¬h h ; (pass o) → ¬o o }

------------------------------------------------------------------------
-- The lower reader

module Lower {P L : Set} (κ : P → Kind) (Fits : List P → List L → Set) where

  mutual

    data RunL : List P → List (Letter L) → Set where
      done  : RunL [] []
      match : ∀ {p ps o v} → κ p ≡ opk o → RunL ps v → RunL (p ∷ ps) (op o ∷ v)
      start : ∀ {S c ps v} → ChL S [] (c ∷ []) false ps v → RunL ps (st S c ∷ v)

    data ChL (S : OpSet) (pre : List P) (cs : List L)
           : Bool → List P → List (Letter L) → Set where
      pour  : ∀ {m p ps v} → AdmK (κ p) S
            → ChL S (pre ∷ʳ p) cs false ps v → ChL S pre cs m (p ∷ ps) v
      over  : ∀ {m p ps S′ c v} → AdmK (κ p) S → ¬ Fits pre cs → Fits (pre ∷ʳ p) cs
            → ChL S′ pre (cs ∷ʳ c) true (p ∷ ps) v → ChL S pre cs m (p ∷ ps) (st S′ c ∷ v)
      close : ∀ {ps v} → Fits pre cs → RunL ps v → ChL S pre cs false ps v

  -- the three moves on a first piece, apart

  PourL : OpSet → List P → List L → Bool → List P → List (Letter L) → Set
  PourL S pre cs m []       v = ⊥
  PourL S pre cs m (p ∷ ps) v = AdmK (κ p) S × ChL S (pre ∷ʳ p) cs false ps v

  OverL : OpSet → List P → List L → Bool → List P → List (Letter L) → Set
  OverL S pre cs m []       v              = ⊥
  OverL S pre cs m (p ∷ ps) []             = ⊥
  OverL S pre cs m (p ∷ ps) (op _ ∷ v)     = ⊥
  OverL S pre cs m (p ∷ ps) (st S′ c ∷ v)  =
    AdmK (κ p) S × ¬ Fits pre cs × Fits (pre ∷ʳ p) cs × ChL S′ pre (cs ∷ʳ c) true (p ∷ ps) v

  CloseL : OpSet → List P → List L → Bool → List P → List (Letter L) → Set
  CloseL S pre cs true  ps v = ⊥
  CloseL S pre cs false ps v = Fits pre cs × RunL ps v

  fromPour : ∀ {S pre cs m ps v} → PourL S pre cs m ps v → ChL S pre cs m ps v
  fromPour {ps = p ∷ ps} (a , h) = pour a h

  fromOver : ∀ {S pre cs m ps v} → OverL S pre cs m ps v → ChL S pre cs m ps v
  fromOver {ps = p ∷ ps} {st S′ c ∷ v} (a , ¬f , g , h) = over a ¬f g h

  fromClose : ∀ {S pre cs m ps v} → CloseL S pre cs m ps v → ChL S pre cs m ps v
  fromClose {m = false} (f , r) = close f r

  split : ∀ {S pre cs m ps v} → ChL S pre cs m ps v
        → ¬ PourL S pre cs m ps v → ¬ OverL S pre cs m ps v → ¬ CloseL S pre cs m ps v → ⊥
  split (pour a h)       ¬a _  _  = ¬a (a , h)
  split (over a ¬f g h)  _  ¬b _  = ¬b (a , ¬f , g , h)
  split (close f r)      _  _  ¬c = ¬c (f , r)

  module Decide (Fits? : ∀ pre cs → Dec (Fits pre cs)) where

    mutual

      runL? : ∀ ps v → Dec (RunL ps v)
      runL? []       []           = yes done
      runL? (p ∷ ps) []           = no λ ()
      runL? []       (op o ∷ v)   = no λ ()
      runL? (p ∷ ps) (op o ∷ v) with κ p ≟ᴷ opk o | runL? ps v
      ... | yes e | yes r = yes (match e r)
      ... | no ¬e | _     = no λ { (match e _) → ¬e e }
      ... | yes _ | no ¬r = no λ { (match _ r) → ¬r r }
      runL? ps       (st S c ∷ v) with chL? S [] (c ∷ []) false ps v
      ... | yes h = yes (start h)
      ... | no ¬h = no λ { (start h) → ¬h h }

      -- the three moves on a first piece, each decided

      chL? : ∀ S pre cs m ps v → Dec (ChL S pre cs m ps v)
      chL? S pre cs m ps v = combine (pourL? S pre cs m ps v) (overL? S pre cs m ps v) (closeL? S pre cs m ps v)
        where
          combine : Dec (PourL S pre cs m ps v) → Dec (OverL S pre cs m ps v) → Dec (CloseL S pre cs m ps v)
                  → Dec (ChL S pre cs m ps v)
          combine (yes h) _ _ = yes (fromPour h)
          combine (no _) (yes h) _ = yes (fromOver h)
          combine (no _) (no _) (yes h) = yes (fromClose h)
          combine (no ¬a) (no ¬b) (no ¬c) = no λ h → split h ¬a ¬b ¬c

      pourL? : ∀ S pre cs m ps v → Dec (PourL S pre cs m ps v)
      pourL? S pre cs m []       v = no λ ()
      pourL? S pre cs m (p ∷ ps) v with AdmK? (κ p) S | chL? S (pre ∷ʳ p) cs false ps v
      ... | yes a | yes h = yes (a , h)
      ... | no ¬a | _     = no λ { (a , _) → ¬a a }
      ... | yes _ | no ¬h = no λ { (_ , h) → ¬h h }

      overL? : ∀ S pre cs m ps v → Dec (OverL S pre cs m ps v)
      overL? S pre cs m []       v              = no λ ()
      overL? S pre cs m (p ∷ ps) []             = no λ ()
      overL? S pre cs m (p ∷ ps) (op o ∷ v)     = no λ ()
      overL? S pre cs m (p ∷ ps) (st S′ c ∷ v)
        with AdmK? (κ p) S | Fits? pre cs | Fits? (pre ∷ʳ p) cs | chL? S′ pre (cs ∷ʳ c) true (p ∷ ps) v
      ... | yes a | no ¬f | yes g | yes h = yes (a , ¬f , g , h)
      ... | no ¬a | _     | _     | _     = no λ { (a , _) → ¬a a }
      ... | yes _ | yes f | _     | _     = no λ { (_ , ¬f , _) → ¬f f }
      ... | yes _ | no _  | no ¬g | _     = no λ { (_ , _ , g , _) → ¬g g }
      ... | yes _ | no _  | yes _ | no ¬h = no λ { (_ , _ , _ , h) → ¬h h }

      closeL? : ∀ S pre cs m ps v → Dec (CloseL S pre cs m ps v)
      closeL? S pre cs true  ps v = no λ ()
      closeL? S pre cs false ps v with Fits? pre cs | runL? ps v
      ... | yes f | yes r = yes (f , r)
      ... | no ¬f | _     = no λ { (f , _) → ¬f f }
      ... | yes _ | no ¬r = no λ { (_ , r) → ¬r r }
