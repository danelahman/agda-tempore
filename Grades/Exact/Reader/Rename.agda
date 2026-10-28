------------------------------------------------------------------------
-- Moving runs of the reader along maps of pieces and bounds.         --
--                                                                    --
-- Pieces and bounds of one reading are mapped to those of another,   --
-- keeping kinds. When the comparisons of the two readings agree on   --
-- mapped lists, a run on lists is a run on their images, and         --
-- conversely: the reader sees the images exactly as the originals.   --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Reader.Rename
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; _∷ʳ_; map; [_])
open import Data.List.Properties using (map-++)
open import Data.Product using (_×_; _,_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_)

open import Grades.Exact.Letters T Op n code code-injective running
open import Grades.Exact.Reader T Op n code code-injective running
open import Grades.Exact.Reader.Transfer T Op n code code-injective running using (mapˡ)

open Equivalence using (to; from)

private
  map-∷ʳ : ∀ {A B : Set} (f : A → B) xs x → map f (xs ∷ʳ x) ≡ map f xs ∷ʳ f x
  map-∷ʳ f xs x = map-++ f xs [ x ]

module Rename {P P′ L L′ : Set} (κ : P → Kind) (κ′ : P′ → Kind)
  (Fits : List P → List L → Set) (Fits′ : List P′ → List L′ → Set)
  (f : P → P′) (g : L → L′)
  (kind : ∀ p → κ′ (f p) ≡ κ p)
  (fits : ∀ pre cs → Fits′ (map f pre) (map g cs) ⇔ Fits pre cs) where

  private
    fits∷ʳ : ∀ pre p cs → Fits′ (map f pre ∷ʳ f p) (map g cs) ⇔ Fits (pre ∷ʳ p) cs
    fits∷ʳ pre p cs =
      mk⇔ (λ h → to (fits (pre ∷ʳ p) cs) (subst (λ X → Fits′ X (map g cs)) (sym (map-∷ʳ f pre p)) h))
          (λ h → subst (λ X → Fits′ X (map g cs)) (map-∷ʳ f pre p) (from (fits (pre ∷ʳ p) cs) h))

  ----------------------------------------------------------------------
  -- The upper reader

  module U where
    open Upper κ Fits
    module U′ = Upper κ′ Fits′

    mutual

      runF : ∀ {ps v} → RunU ps v → U′.RunU (map f ps) (map (mapˡ g) v)
      runF done        = U′.done
      runF (match k r) = U′.match (trans (kind _) k) (runF r)
      runF (start h)   = U′.start (chF h)

      chF : ∀ {S pre cs m ps v} → ChU S pre cs m ps v
          → U′.ChU S (map f pre) (map g cs) m (map f ps) (map (mapˡ g) v)
      chF {S} {pre} {cs} (pour {p = p} {ps} {v} a h k) =
        U′.pour (subst (λ x → AdmK x S) (sym (kind p)) a) (from (fits∷ʳ pre p cs) h)
          (subst (λ X → U′.ChU S X (map g cs) false (map f ps) (map (mapˡ g) v)) (map-∷ʳ f pre p) (chF k))
      chF {S} {pre} {cs} (over {p = p} a ¬h o) =
        U′.over (subst (λ x → AdmK x S) (sym (kind p)) a) (λ h → ¬h (to (fits∷ʳ pre p cs) h)) (ovF o)
      chF (close r) = U′.close (runF r)

      ovF : ∀ {pre cs p ps v} → OverU pre cs p ps v
          → U′.OverU (map f pre) (map g cs) (f p) (map f ps) (map (mapˡ g) v)
      ovF {pre} {cs} {p} {ps} (enter {S} {c} {v} h) =
        U′.enter (subst (λ X → U′.ChU S (map f pre) X true (f p ∷ map f ps) (map (mapˡ g) v))
                        (map-∷ʳ g cs c) (chF h))
      ovF (pass o) = U′.pass (ovF o)

    mutual

      runB : ∀ ps v → U′.RunU (map f ps) (map (mapˡ g) v) → RunU ps v
      runB []       []           U′.done        = done
      runB (p ∷ ps) (op o ∷ v)   (U′.match k r) = match (trans (sym (kind p)) k) (runB ps v r)
      runB ps       (st S c ∷ v) (U′.start h)   = start (chB S [] (c ∷ []) false ps v h)

      chB : ∀ S pre cs m ps v → U′.ChU S (map f pre) (map g cs) m (map f ps) (map (mapˡ g) v)
          → ChU S pre cs m ps v
      chB S pre cs m (p ∷ ps) v (U′.pour a h k) =
        pour (subst (λ x → AdmK x S) (kind p) a) (to (fits∷ʳ pre p cs) h)
          (chB S (pre ∷ʳ p) cs false ps v
            (subst (λ X → U′.ChU S X (map g cs) false (map f ps) (map (mapˡ g) v)) (sym (map-∷ʳ f pre p)) k))
      chB S pre cs m (p ∷ ps) v (U′.over a ¬h o) =
        over (subst (λ x → AdmK x S) (kind p) a) (λ h → ¬h (from (fits∷ʳ pre p cs) h)) (ovB pre cs p ps v o)
      chB S pre cs false ps v (U′.close r) = close (runB ps v r)

      ovB : ∀ pre cs p ps v → U′.OverU (map f pre) (map g cs) (f p) (map f ps) (map (mapˡ g) v)
          → OverU pre cs p ps v
      ovB pre cs p ps (st S c ∷ v) (U′.enter h) =
        enter (chB S pre (cs ∷ʳ c) true (p ∷ ps) v
                 (subst (λ X → U′.ChU S (map f pre) X true (f p ∷ map f ps) (map (mapˡ g) v))
                        (sym (map-∷ʳ g cs c)) h))
      ovB pre cs p ps (st S c ∷ v) (U′.pass o) = pass (ovB pre cs p ps v o)

    rename : ∀ ps v → RunU ps v ⇔ U′.RunU (map f ps) (map (mapˡ g) v)
    rename ps v = mk⇔ runF (runB ps v)

  ----------------------------------------------------------------------
  -- The lower reader

  module L where
    open Lower κ Fits
    module L′ = Lower κ′ Fits′

    mutual

      runF : ∀ {ps v} → RunL ps v → L′.RunL (map f ps) (map (mapˡ g) v)
      runF done        = L′.done
      runF (match k r) = L′.match (trans (kind _) k) (runF r)
      runF (start h)   = L′.start (chF h)

      chF : ∀ {S pre cs m ps v} → ChL S pre cs m ps v
          → L′.ChL S (map f pre) (map g cs) m (map f ps) (map (mapˡ g) v)
      chF {S} {pre} {cs} (pour {p = p} {ps} {v} a k) =
        L′.pour (subst (λ x → AdmK x S) (sym (kind p)) a)
          (subst (λ X → L′.ChL S X (map g cs) false (map f ps) (map (mapˡ g) v)) (map-∷ʳ f pre p) (chF k))
      chF {S} {pre} {cs} (over {p = p} {ps} {S′} {c} {v} a ¬h h k) =
        L′.over (subst (λ x → AdmK x S) (sym (kind p)) a)
          (λ h′ → ¬h (to (fits pre cs) h′)) (from (fits∷ʳ pre p cs) h)
          (subst (λ X → L′.ChL S′ (map f pre) X true (f p ∷ map f ps) (map (mapˡ g) v))
                 (map-∷ʳ g cs c) (chF k))
      chF {pre = pre} {cs} (close h r) = L′.close (from (fits pre cs) h) (runF r)

    mutual

      runB : ∀ ps v → L′.RunL (map f ps) (map (mapˡ g) v) → RunL ps v
      runB []       []           L′.done        = done
      runB (p ∷ ps) (op o ∷ v)   (L′.match k r) = match (trans (sym (kind p)) k) (runB ps v r)
      runB ps       (st S c ∷ v) (L′.start h)   = start (chB S [] (c ∷ []) false ps v h)

      chB : ∀ S pre cs m ps v → L′.ChL S (map f pre) (map g cs) m (map f ps) (map (mapˡ g) v)
          → ChL S pre cs m ps v
      chB S pre cs m (p ∷ ps) (st S′ c ∷ v) (L′.over a ¬h h k) =
        over (subst (λ x → AdmK x S) (kind p) a) (λ h′ → ¬h (from (fits pre cs) h′))
          (to (fits∷ʳ pre p cs) h)
          (chB S′ pre (cs ∷ʳ c) true (p ∷ ps) v
            (subst (λ X → L′.ChL S′ (map f pre) X true (f p ∷ map f ps) (map (mapˡ g) v))
                   (sym (map-∷ʳ g cs c)) k))
      chB S pre cs m (p ∷ ps) v (L′.pour a k) =
        pour (subst (λ x → AdmK x S) (kind p) a)
          (chB S (pre ∷ʳ p) cs false ps v
            (subst (λ X → L′.ChL S X (map g cs) false (map f ps) (map (mapˡ g) v)) (sym (map-∷ʳ f pre p)) k))
      chB S pre cs false ps v (L′.close h r) = close (to (fits pre cs) h) (runB ps v r)

    rename : ∀ ps v → RunL ps v ⇔ L′.RunL (map f ps) (map (mapˡ g) v)
    rename ps v = mk⇔ runF (runB ps v)
