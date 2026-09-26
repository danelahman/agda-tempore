------------------------------------------------------------------
-- The outcome of solving                                         --
--                                                                --
-- A solution, a refutation, or stuck: a rigid scope closes with  --
-- an unknown local to it for which `Localise` finds no value.    --
-- Nothing is claimed of a stuck constraint.                      --
------------------------------------------------------------------

module TypeInference.Outcome where

open import Data.Product using (Σ-syntax; _×_; _,_)

open import Util.Equality

data Outcome (A : Set) : Set where
  solved  : A → Outcome A
  refuted : Outcome A
  stuck   : Outcome A

-- A solution is carried along

mapᴼ : ∀ {A B : Set} → (A → B) → Outcome A → Outcome B
mapᴼ f (solved a) = solved (f a)
mapᴼ f refuted    = refuted
mapᴼ f stuck      = stuck

-- The three outcomes are distinct

⊥refuted : ∀ {A Y : Set} {a : A} → refuted ≡ solved a → Y
⊥refuted ()

⊥stuck : ∀ {A Y : Set} {a : A} → stuck ≡ solved a → Y
⊥stuck ()

⊥solved : ∀ {A Y : Set} {a : A} → solved a ≡ refuted → Y
⊥solved ()

⊥stuck-refuted : ∀ {A Y : Set} → stuck {A} ≡ refuted → Y
⊥stuck-refuted ()

mapᴼ-solved : ∀ {A B : Set} {f : A → B} → (x : Outcome A) → {b : B}
            → mapᴼ f x ≡ solved b → Σ[ a ∈ A ] ((x ≡ solved a) × (f a ≡ b))
mapᴼ-solved (solved a) refl = a , refl , refl

mapᴼ-refuted : ∀ {A B : Set} {f : A → B} → (x : Outcome A) → mapᴼ f x ≡ refuted → x ≡ refuted
mapᴼ-refuted refuted refl = refl

mapᴼ-stuck : ∀ {A B : Set} {f : A → B} → (x : Outcome A) → mapᴼ f x ≡ stuck → x ≡ stuck
mapᴼ-stuck stuck refl = refl
