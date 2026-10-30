------------------------------------------------------------------
-- The outcome of solving                                       --
--                                                              --
-- A solution, a refutation, or `stuck`, of which nothing is    --
-- claimed. The solver is stuck only at the close of a rigid    --
-- scope, on a local unknown `Localise` assigns no value.       --
------------------------------------------------------------------

module PolymorphicCalculus.Inference.Outcome where

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
