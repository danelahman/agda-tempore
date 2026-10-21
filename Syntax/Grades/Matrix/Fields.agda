------------------------------------------------------------------------
-- Matrices given by the entries between named modes, from a named    --
-- mode to one not named and back, from a mode not named to itself    --
-- and to another, and into `stuck`: the representation of matrices   --
-- whose entries name no modes. Their entries are invariant under     --
-- exchanging two modes not named (`entry-swap`), and so they are     --
-- matrices over the dioid with the trivial action (`fromFields`).    --
------------------------------------------------------------------------

open import Syntax.Grades.Indexed using (Names)
open import Syntax.Grades.Matrix.Dioid using (Dioid)

module Syntax.Grades.Matrix.Fields (𝒩 : Names) (S : Dioid) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Util.Equality

open Dioid S
open import Syntax.Grades.Matrix.Modes 𝒩
open import Syntax.Grades.Matrix.Nominal 𝒩 using (trivial)
open import Syntax.Grades.Matrix.Matrices 𝒩 S (trivial S) using (Matrix; module Matrix)

------------------------------------------------------------------------
-- Matrices given by their fields

record Fields : Set where
  constructor fields
  field
    modes        : List Name
    within       : Name → Name → Carrier   -- between named modes
    leaving      : Name → Carrier          -- from a named mode to one not named
    entering     : Name → Carrier          -- from a mode not named to a named one
    toStuck      : Name → Carrier          -- from a named mode into `stuck`
    staying      : Carrier                 -- from a mode not named to itself
    moving       : Carrier                 -- from a mode not named to another
    otherToStuck : Carrier                 -- from a mode not named into `stuck`

open Fields public

entryᶠ : Fields → Mode → Mode → Carrier
entryᶠ M stuck   stuck   = 𝟙
entryᶠ M stuck   ⌜ _ ⌝ = 𝟘
entryᶠ M ⌜ p ⌝ stuck with p ∈? modes M
... | yes _ = toStuck M p
... | no _  = otherToStuck M
entryᶠ M ⌜ p ⌝ ⌜ q ⌝ with p ∈? modes M | q ∈? modes M
... | yes _ | yes _ = within M p q
... | yes _ | no _  = leaving M p
... | no _  | yes _ = entering M q
... | no _  | no _ with p ≟ᴺ q
...   | yes _ = staying M
...   | no _  = moving M

-- the entries by the kind of the modes

module _ (M : Fields) where

  private F = modes M

  entry-yy : ∀ {p q} → p ∈ F → q ∈ F → entryᶠ M ⌜ p ⌝ ⌜ q ⌝ ≡ within M p q
  entry-yy {p} {q} p∈ q∈ with p ∈? F | q ∈? F
  ... | yes _ | yes _ = refl
  ... | no p∉ | _     = ⊥-elim (p∉ p∈)
  ... | yes _ | no q∉ = ⊥-elim (q∉ q∈)

  entry-yn : ∀ {p q} → p ∈ F → q ∉ F → entryᶠ M ⌜ p ⌝ ⌜ q ⌝ ≡ leaving M p
  entry-yn {p} {q} p∈ q∉ with p ∈? F | q ∈? F
  ... | yes _ | no _  = refl
  ... | no p∉ | _     = ⊥-elim (p∉ p∈)
  ... | yes _ | yes q∈ = ⊥-elim (q∉ q∈)

  entry-ny : ∀ {p q} → p ∉ F → q ∈ F → entryᶠ M ⌜ p ⌝ ⌜ q ⌝ ≡ entering M q
  entry-ny {p} {q} p∉ q∈ with p ∈? F | q ∈? F
  ... | no _   | yes _ = refl
  ... | yes p∈ | _     = ⊥-elim (p∉ p∈)
  ... | no _   | no q∉ = ⊥-elim (q∉ q∈)

  entry-nn-≡ : ∀ {p} → p ∉ F → entryᶠ M ⌜ p ⌝ ⌜ p ⌝ ≡ staying M
  entry-nn-≡ {p} p∉ with p ∈? F
  ... | yes p∈ = ⊥-elim (p∉ p∈)
  ... | no _ with p ≟ᴺ p
  ...   | yes _ = refl
  ...   | no ¬e = ⊥-elim (¬e refl)

  entry-nn-≢ : ∀ {p q} → p ∉ F → q ∉ F → ¬ p ≡ q → entryᶠ M ⌜ p ⌝ ⌜ q ⌝ ≡ moving M
  entry-nn-≢ {p} {q} p∉ q∉ p≢q with p ∈? F | q ∈? F
  ... | yes p∈ | _      = ⊥-elim (p∉ p∈)
  ... | no _   | yes q∈ = ⊥-elim (q∉ q∈)
  ... | no _   | no _ with p ≟ᴺ q
  ...   | yes e = ⊥-elim (p≢q e)
  ...   | no _  = refl

  entry-ys : ∀ {p} → p ∈ F → entryᶠ M ⌜ p ⌝ stuck ≡ toStuck M p
  entry-ys {p} p∈ with p ∈? F
  ... | yes _  = refl
  ... | no p∉  = ⊥-elim (p∉ p∈)

  entry-ns : ∀ {p} → p ∉ F → entryᶠ M ⌜ p ⌝ stuck ≡ otherToStuck M
  entry-ns {p} p∉ with p ∈? F
  ... | yes p∈ = ⊥-elim (p∉ p∈)
  ... | no _   = refl

  -- exchanging two modes not named keeps the entries

  entry-swap : ∀ {a b} → a ∉ F → b ∉ F → ∀ x y
             → entryᶠ M (swapᴹ a b x) (swapᴹ a b y) ≡ entryᶠ M x y
  entry-swap a∉ b∉ stuck stuck   = refl
  entry-swap a∉ b∉ stuck ⌜ q ⌝ = refl
  entry-swap {a} {b} a∉ b∉ ⌜ p ⌝ stuck = ps (p ∈? F)
    where
      ps : Dec (p ∈ F) → entryᶠ M ⌜ swap a b p ⌝ stuck ≡ entryᶠ M ⌜ p ⌝ stuck
      ps (yes p∈) = trans (entry-ys (subst (_∈ F) (sym (swap-∈ a∉ b∉ p∈)) p∈))
                          (trans (cong (toStuck M) (swap-∈ a∉ b∉ p∈)) (sym (entry-ys p∈)))
      ps (no p∉)  = trans (entry-ns (swap-∉ a∉ b∉ p∉)) (sym (entry-ns p∉))
  entry-swap {a} {b} a∉ b∉ ⌜ p ⌝ ⌜ q ⌝ = pq (p ∈? F) (q ∈? F) (p ≟ᴺ q)
    where
      pq : Dec (p ∈ F) → Dec (q ∈ F) → Dec (p ≡ q)
         → entryᶠ M ⌜ swap a b p ⌝ ⌜ swap a b q ⌝ ≡ entryᶠ M ⌜ p ⌝ ⌜ q ⌝
      pq (yes p∈) (yes q∈) _ =
        trans (cong₂ (λ m n → entryᶠ M ⌜ m ⌝ ⌜ n ⌝) (swap-∈ a∉ b∉ p∈) (swap-∈ a∉ b∉ q∈)) refl
      pq (yes p∈) (no q∉) _ =
        trans (cong (λ m → entryᶠ M ⌜ m ⌝ ⌜ swap a b q ⌝) (swap-∈ a∉ b∉ p∈))
              (trans (entry-yn p∈ (swap-∉ a∉ b∉ q∉)) (sym (entry-yn p∈ q∉)))
      pq (no p∉) (yes q∈) _ =
        trans (cong (λ n → entryᶠ M ⌜ swap a b p ⌝ ⌜ n ⌝) (swap-∈ a∉ b∉ q∈))
              (trans (entry-ny (swap-∉ a∉ b∉ p∉) q∈) (sym (entry-ny p∉ q∈)))
      pq (no p∉) (no q∉) (yes refl) =
        trans (entry-nn-≡ (swap-∉ a∉ b∉ p∉)) (sym (entry-nn-≡ p∉))
      pq (no p∉) (no q∉) (no p≢q) =
        trans (entry-nn-≢ (swap-∉ a∉ b∉ p∉) (swap-∉ a∉ b∉ q∉) (λ e → p≢q (swap-injective e)))
              (sym (entry-nn-≢ p∉ q∉ p≢q))


------------------------------------------------------------------------
-- As matrices over the trivial action

fromFields : Fields → Matrix
Matrix.modes (fromFields M) = modes M
Matrix.row (fromFields M) p y = entryᶠ M ⌜ p ⌝ y
Matrix.equivariant (fromFields M) a∉ b∉ p y = ≈-reflexive (entry-swap M a∉ b∉ ⌜ p ⌝ y)
