------------------------------------------------------------------------
-- Moving a run of the reader between two readings of the same words. --
--                                                                    --
-- Two lists of pieces with the same kinds are given zipped, and two  --
-- greater words with the same letters likewise. When the reader's    --
-- comparison agrees on the two readings at every chain it could      --
-- compare -- an infix of the pieces against a subsequence of the     --
-- bounds -- a run on one reading is a run on the other.              --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module Syntax.Grades.Exact.Reader.Transfer
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_; map; [_])
open import Data.List.Properties using (++-assoc; map-++)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_)

open import Syntax.Grades.Exact.Letters T Op n code code-injective running
open import Syntax.Grades.Exact.Reader T Op n code code-injective running

------------------------------------------------------------------------
-- Subsequences

data Sub {A : Set} : List A → List A → Set where
  []   : Sub [] []
  keep : ∀ {x xs ys} → Sub xs ys → Sub (x ∷ xs) (x ∷ ys)
  drop : ∀ {x xs ys} → Sub xs ys → Sub xs (x ∷ ys)

module _ {A : Set} where

  sub-refl : ∀ (xs : List A) → Sub xs xs
  sub-refl []       = []
  sub-refl (x ∷ xs) = keep (sub-refl xs)

  sub-[] : ∀ (xs : List A) → Sub [] xs
  sub-[] []       = []
  sub-[] (x ∷ xs) = drop (sub-[] xs)

  sub-trans : ∀ {xs ys zs : List A} → Sub xs ys → Sub ys zs → Sub xs zs
  sub-trans s        (drop t) = drop (sub-trans s t)
  sub-trans []       []       = []
  sub-trans (keep s) (keep t) = keep (sub-trans s t)
  sub-trans (drop s) (keep t) = drop (sub-trans s t)

  sub-++ˡ : ∀ (xs ys : List A) → Sub xs (xs ++ ys)
  sub-++ˡ []       ys = sub-[] ys
  sub-++ˡ (x ∷ xs) ys = keep (sub-++ˡ xs ys)

  sub-++ʳ : ∀ (xs ys : List A) → Sub ys (xs ++ ys)
  sub-++ʳ []       ys = sub-refl ys
  sub-++ʳ (x ∷ xs) ys = drop (sub-++ʳ xs ys)

  sub-skip : ∀ (xs : List A) {y ys} → Sub (xs ++ ys) (xs ++ y ∷ ys)
  sub-skip []       {_} {ys} = drop (sub-refl ys)
  sub-skip (x ∷ xs)          = keep (sub-skip xs)

------------------------------------------------------------------------
-- The bounds of a word, and letters read two ways

capsOf : ∀ {L} → List (Letter L) → List L
capsOf []           = []
capsOf (op _ ∷ v)   = capsOf v
capsOf (st _ c ∷ v) = c ∷ capsOf v

mapˡ : ∀ {L L′} → (L → L′) → Letter L → Letter L′
mapˡ f (op o)   = op o
mapˡ f (st S c) = st S (f c)

private
  π₁ = proj₁
  π₂ = proj₂

  ++-∷ʳ : ∀ {A : Set} (a pre : List A) (x : A) ps → a ++ pre ++ x ∷ ps ≡ a ++ (pre ∷ʳ x) ++ ps
  ++-∷ʳ a pre x ps = cong (a ++_) (sym (++-assoc pre [ x ] ps))

  map-∷ʳ : ∀ {A B : Set} (f : A → B) xs x → map f (xs ∷ʳ x) ≡ map f xs ∷ʳ f x
  map-∷ʳ f xs x = map-++ f xs [ x ]

------------------------------------------------------------------------
-- Agreement

module Agree {P L : Set} (κ : P → Kind) (Fits : List P → List L → Set)
  (zs₀ : List (P × P)) (vz₀ : List (Letter (L × L)))
  (kinds : ∀ a z b → a ++ z ∷ b ≡ zs₀ → κ (π₁ z) ≡ κ (π₂ z))
  (agree : ∀ a pre b cs → a ++ pre ++ b ≡ zs₀ → Sub cs (capsOf vz₀)
         → Fits (map π₁ pre) (map π₁ cs) ⇔ Fits (map π₂ pre) (map π₂ cs))
  where

  -- one direction at a time: from the reading `ρ` to the reading `σ`

  module Dir (ρ σ : ∀ {A : Set} → A × A → A)
    (ag : ∀ a pre b cs → a ++ pre ++ b ≡ zs₀ → Sub cs (capsOf vz₀)
        → Fits (map ρ pre) (map ρ cs) → Fits (map σ pre) (map σ cs))
    (ga : ∀ a pre b cs → a ++ pre ++ b ≡ zs₀ → Sub cs (capsOf vz₀)
        → Fits (map σ pre) (map σ cs) → Fits (map ρ pre) (map ρ cs))
    (kd : ∀ a z b → a ++ z ∷ b ≡ zs₀ → κ (ρ z) ≡ κ (σ z)) where

    capsˡ : ∀ (f : L × L → L) v → capsOf (map (mapˡ f) v) ≡ map f (capsOf v)
    capsˡ f []           = refl
    capsˡ f (op _ ∷ v)   = capsˡ f v
    capsˡ f (st _ c ∷ v) = cong (f c ∷_) (capsˡ f v)

    module U where
      open Upper κ Fits

      mutual

        runA : ∀ a psZ vZ → a ++ psZ ≡ zs₀ → Sub (capsOf vZ) (capsOf vz₀)
             → RunU (map ρ psZ) (map (mapˡ ρ) vZ) → RunU (map σ psZ) (map (mapˡ σ) vZ)
        runA a [] [] e s done = done
        runA a (z ∷ psZ) (op o ∷ vZ) e s (match k r) =
          match (trans (sym (kd a z psZ e)) k)
                (runA (a ++ [ z ]) psZ vZ (trans (++-assoc a [ z ] psZ) e) s r)
        runA a psZ (st S c ∷ vZ) e s (start h) =
          start (chA a [] [ c ] false psZ vZ S e s h)

        chA : ∀ a preZ csZ m psZ vZ S → a ++ preZ ++ psZ ≡ zs₀
            → Sub (csZ ++ capsOf vZ) (capsOf vz₀)
            → ChU S (map ρ preZ) (map ρ csZ) m (map ρ psZ) (map (mapˡ ρ) vZ)
            → ChU S (map σ preZ) (map σ csZ) m (map σ psZ) (map (mapˡ σ) vZ)
        chA a preZ csZ m (z ∷ psZ) vZ S e s (pour ad f h) =
          pour (subst (λ k → AdmK k S) (kd (a ++ preZ) z psZ (trans (++-assoc a preZ (z ∷ psZ)) e)) ad)
               (subst (λ X → Fits X (map σ csZ)) (map-∷ʳ σ preZ z)
                  (ag a (preZ ∷ʳ z) psZ csZ (trans (sym (++-∷ʳ a preZ z psZ)) e)
                      (sub-trans (sub-++ˡ csZ (capsOf vZ)) s)
                      (subst (λ X → Fits X (map ρ csZ)) (sym (map-∷ʳ ρ preZ z)) f)))
               (subst (λ X → ChU S X (map σ csZ) false (map σ psZ) (map (mapˡ σ) vZ))
                  (map-∷ʳ σ preZ z)
                  (chA a (preZ ∷ʳ z) csZ false psZ vZ S (trans (sym (++-∷ʳ a preZ z psZ)) e) s
                     (subst (λ X → ChU S X (map ρ csZ) false (map ρ psZ) (map (mapˡ ρ) vZ))
                        (sym (map-∷ʳ ρ preZ z)) h)))
        chA a preZ csZ m (z ∷ psZ) vZ S e s (over ad ¬f o) =
          over (subst (λ k → AdmK k S) (kd (a ++ preZ) z psZ (trans (++-assoc a preZ (z ∷ psZ)) e)) ad)
               (λ f → ¬f (subst (λ X → Fits X (map ρ csZ)) (map-∷ʳ ρ preZ z)
                  (ga a (preZ ∷ʳ z) psZ csZ (trans (sym (++-∷ʳ a preZ z psZ)) e)
                      (sub-trans (sub-++ˡ csZ (capsOf vZ)) s)
                      (subst (λ X → Fits X (map σ csZ)) (sym (map-∷ʳ σ preZ z)) f))))
               (ovA a preZ csZ z psZ vZ e s o)
        chA a preZ csZ false psZ vZ S e s (close r) =
          close (runA (a ++ preZ) psZ vZ (trans (++-assoc a preZ psZ) e)
                  (sub-trans (sub-++ʳ csZ (capsOf vZ)) s) r)

        ovA : ∀ a preZ csZ z psZ vZ → a ++ preZ ++ z ∷ psZ ≡ zs₀
            → Sub (csZ ++ capsOf vZ) (capsOf vz₀)
            → OverU (map ρ preZ) (map ρ csZ) (ρ z) (map ρ psZ) (map (mapˡ ρ) vZ)
            → OverU (map σ preZ) (map σ csZ) (σ z) (map σ psZ) (map (mapˡ σ) vZ)
        ovA a preZ csZ z psZ (st S c ∷ vZ) e s (enter h) =
          enter (subst (λ X → ChU S (map σ preZ) X true (σ z ∷ map σ psZ) (map (mapˡ σ) vZ))
                   (map-∷ʳ σ csZ c)
                   (chA a preZ (csZ ∷ʳ c) true (z ∷ psZ) vZ S e
                      (subst (λ X → Sub X (capsOf vz₀)) (sym (++-assoc csZ [ c ] (capsOf vZ))) s)
                      (subst (λ X → ChU S (map ρ preZ) X true (ρ z ∷ map ρ psZ) (map (mapˡ ρ) vZ))
                         (sym (map-∷ʳ ρ csZ c)) h)))
        ovA a preZ csZ z psZ (st S c ∷ vZ) e s (pass o) =
          pass (ovA a preZ csZ z psZ vZ e (sub-trans (sub-skip csZ) s) o)

    module Lo where
      open Lower κ Fits

      mutual

        runA : ∀ a psZ vZ → a ++ psZ ≡ zs₀ → Sub (capsOf vZ) (capsOf vz₀)
             → RunL (map ρ psZ) (map (mapˡ ρ) vZ) → RunL (map σ psZ) (map (mapˡ σ) vZ)
        runA a [] [] e s done = done
        runA a (z ∷ psZ) (op o ∷ vZ) e s (match k r) =
          match (trans (sym (kd a z psZ e)) k)
                (runA (a ++ [ z ]) psZ vZ (trans (++-assoc a [ z ] psZ) e) s r)
        runA a psZ (st S c ∷ vZ) e s (start h) =
          start (chA a [] [ c ] false psZ vZ S e s h)

        chA : ∀ a preZ csZ m psZ vZ S → a ++ preZ ++ psZ ≡ zs₀
            → Sub (csZ ++ capsOf vZ) (capsOf vz₀)
            → ChL S (map ρ preZ) (map ρ csZ) m (map ρ psZ) (map (mapˡ ρ) vZ)
            → ChL S (map σ preZ) (map σ csZ) m (map σ psZ) (map (mapˡ σ) vZ)
        chA a preZ csZ m (z ∷ psZ) (st S′ c ∷ vZ) S e s (over ad ¬f g h) =
          over (subst (λ k → AdmK k S) (kd (a ++ preZ) z psZ (trans (++-assoc a preZ (z ∷ psZ)) e)) ad)
               (λ f → ¬f (back a preZ (z ∷ psZ) e f))
               (subst (λ X → Fits X (map σ csZ)) (map-∷ʳ σ preZ z)
                  (ag a (preZ ∷ʳ z) psZ csZ (trans (sym (++-∷ʳ a preZ z psZ)) e) sc
                      (subst (λ X → Fits X (map ρ csZ)) (sym (map-∷ʳ ρ preZ z)) g)))
               (subst (λ X → ChL S′ (map σ preZ) X true (σ z ∷ map σ psZ) (map (mapˡ σ) vZ))
                   (map-∷ʳ σ csZ c)
                   (chA a preZ (csZ ∷ʳ c) true (z ∷ psZ) vZ S′ e
                      (subst (λ X → Sub X (capsOf vz₀)) (sym (++-assoc csZ [ c ] (capsOf vZ))) s)
                      (subst (λ X → ChL S′ (map ρ preZ) X true (ρ z ∷ map ρ psZ) (map (mapˡ ρ) vZ))
                         (sym (map-∷ʳ ρ csZ c)) h)))
          where
            sc : Sub csZ (capsOf vz₀)
            sc = sub-trans (sub-++ˡ csZ (capsOf (st S′ c ∷ vZ))) s
            back : ∀ a preZ rest → a ++ preZ ++ rest ≡ zs₀
                 → Fits (map σ preZ) (map σ csZ) → Fits (map ρ preZ) (map ρ csZ)
            back a preZ rest e′ = ga a preZ rest csZ e′ sc
        chA a preZ csZ m (z ∷ psZ) vZ S e s (pour ad h) =
          pour (subst (λ k → AdmK k S) (kd (a ++ preZ) z psZ (trans (++-assoc a preZ (z ∷ psZ)) e)) ad)
               (subst (λ X → ChL S X (map σ csZ) false (map σ psZ) (map (mapˡ σ) vZ))
                  (map-∷ʳ σ preZ z)
                  (chA a (preZ ∷ʳ z) csZ false psZ vZ S (trans (sym (++-∷ʳ a preZ z psZ)) e) s
                     (subst (λ X → ChL S X (map ρ csZ) false (map ρ psZ) (map (mapˡ ρ) vZ))
                        (sym (map-∷ʳ ρ preZ z)) h)))
        chA a preZ csZ false psZ vZ S e s (close f r) =
          close (ag a preZ psZ csZ e (sub-trans (sub-++ˡ csZ (capsOf vZ)) s) f)
                (runA (a ++ preZ) psZ vZ (trans (++-assoc a preZ psZ) e)
                  (sub-trans (sub-++ʳ csZ (capsOf vZ)) s) r)

  -- both directions

  private
    to : ∀ a pre b cs → a ++ pre ++ b ≡ zs₀ → Sub cs (capsOf vz₀)
       → Fits (map π₁ pre) (map π₁ cs) → Fits (map π₂ pre) (map π₂ cs)
    to a pre b cs e s = Equivalence.to (agree a pre b cs e s)
    from : ∀ a pre b cs → a ++ pre ++ b ≡ zs₀ → Sub cs (capsOf vz₀)
         → Fits (map π₂ pre) (map π₂ cs) → Fits (map π₁ pre) (map π₁ cs)
    from a pre b cs e s = Equivalence.from (agree a pre b cs e s)

  module Forward  = Dir π₁ π₂ to from kinds
  module Backward = Dir π₂ π₁ from to (λ a z b e → sym (kinds a z b e))

  agreeᵁ : Upper.RunU κ Fits (map π₁ zs₀) (map (mapˡ π₁) vz₀)
         ⇔ Upper.RunU κ Fits (map π₂ zs₀) (map (mapˡ π₂) vz₀)
  agreeᵁ = mk⇔ (Forward.U.runA [] zs₀ vz₀ refl (sub-refl _))
               (Backward.U.runA [] zs₀ vz₀ refl (sub-refl _))

  agreeᴸ : Lower.RunL κ Fits (map π₁ zs₀) (map (mapˡ π₁) vz₀)
         ⇔ Lower.RunL κ Fits (map π₂ zs₀) (map (mapˡ π₂) vz₀)
  agreeᴸ = mk⇔ (Forward.Lo.runA [] zs₀ vz₀ refl (sub-refl _))
               (Backward.Lo.runA [] zs₀ vz₀ refl (sub-refl _))
