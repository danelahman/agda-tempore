------------------------------------------------------------------------
-- Restricting timed traces along a predicate on operation names.     --
--                                                                    --
-- The sub-alphabet `Op'` is the operations the predicate admits, and --
-- restriction drops every event outside it while keeping the delays, --
-- merging the delays that surrounded a dropped operation. Sequencing --
-- and the language product are preserved, so restriction is a monoid --
-- map -- which is what makes it a grade morphism.                    --
--                                                                    --
-- Both alphabets are in play at once, so this module opens the trace --
-- toolkit *unapplied* and names the alphabet at each use.            --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous; tri<; tri≈; tri>)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Data.Bool
open import Data.Bool.Properties using (T?)
open import Data.List
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.List.Properties using (map-++)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product
open import Data.Unit using (tt)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.Restriction
  {D : Duration} (TD : TimeDomain D) (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (OpPred : Op → Bool) where

-- the traces themselves do not depend on the order, so the trace
-- toolkit is opened at the time domain alone and the alphabet named at
-- each use; the sets of traces do, so each alphabet gets its own
-- instance below

open import Grades.Traces.Base TD

import Grades.Traces.Sets as Sets

open import Grades.Durations.Monus TD using (Carrier; 0ᴰ; _<ᴰ_; _<ᴰ?_)

module S = Sets TD Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans

Op' : Set
Op' = Σ[ op ∈ Op ] T (OpPred op)

T-irrelevant : {b : Bool} → (p q : T b) → p ≡ q
T-irrelevant {false} = λ ()
T-irrelevant {true} = λ p q → refl

_≟ₒ'_ : DecidableEquality Op'
(op , p) ≟ₒ' (op' , p') with op ≟ₒ op'
(op , p) ≟ₒ' (.op , p') | yes refl with T-irrelevant p p'
(op , p) ≟ₒ' (.op , p') | yes refl | refl = yes refl
(op , p) ≟ₒ' (op' , p') | no ¬q = no (λ { refl → ¬q refl })

-- the sub-alphabet is ordered by the ambient order on the symbol it
-- carries; the admission proof is unique, so this stays trichotomous

_<ᵒ'_ : Rel Op' lzero
x <ᵒ' y = proj₁ x <ᵒ proj₁ y

<ᵒ'-trans : Transitive _<ᵒ'_
<ᵒ'-trans = <ᵒ-trans

<ᵒ'-cmp : Trichotomous _≡_ _<ᵒ'_
<ᵒ'-cmp (op , p) (op' , p') with <ᵒ-cmp op op'
... | tri< lt ¬eq ¬gt   = tri< lt (λ { refl → ¬eq refl }) ¬gt
... | tri> ¬lt ¬eq gt   = tri> ¬lt (λ { refl → ¬eq refl }) gt
... | tri≈ ¬lt refl ¬gt with T-irrelevant p p'
...   | refl = tri≈ ¬lt refl ¬gt

-- the transitivity proof is instantiated at the sub-alphabet's own
-- triple, which a bare name would leave for unification to guess

module S' = Sets TD Op' _<ᵒ'_ <ᵒ'-cmp (λ {x} {y} {z} → <ᵒ'-trans {x} {y} {z})

operation' : (op : Op) → T (OpPred op) → Op'
operation' op p = op , p

-- Restricting a trace keeps the operations the predicate admits, drops
-- the rest, and leaves the delays alone -- a delay's duration is a
-- positive duration of the time domain, shared by both alphabets.

mutual
  restrict-trace : Trace Op → Trace Op'
  restrict-trace ε = ε
  restrict-trace (operation op t) with T? (OpPred op)
  ... | yes p = operation (operation' op p) (restrict-trace t)
  ... | no  _ = restrict-trace t
  restrict-trace (delay τ t) = prepend _ τ (restrict-trace⁻ t)

  restrict-trace⁻ : Trace⁻ Op → Trace Op'
  restrict-trace⁻ ε⁻ = ε
  restrict-trace⁻ (operation⁻ op t) with T? (OpPred op)
  ... | yes p = operation (operation' op p) (restrict-trace t)
  ... | no  _ = restrict-trace t

restrict-traces : List (Trace Op) → List (Trace Op')
restrict-traces traces = Data.List.map restrict-trace traces

restrict-nonempty : {traces : List (Trace Op)}
                  → S.NonEmpty traces → S'.NonEmpty (restrict-traces traces)
restrict-nonempty {[]}    ()
restrict-nonempty {_ ∷ _} ne = ne

open S.WithDecEq  _≟ₒ_  using () renaming (_⊑_ to _⊑ₒ_)
open S'.WithDecEq _≟ₒ'_ using () renaming (_⊑_ to _⊑ₒ'_)

restrict-⊑ : {xs ys : List (Trace Op)}
           → xs ⊑ₒ ys → restrict-traces xs ⊑ₒ' restrict-traces ys
restrict-⊑ {xs} {ys} hyp s mem with ∈-map⁻ restrict-trace (toWitness mem)
... | a , a∈xs , refl =
      fromWitness (∈-map⁺ restrict-trace (toWitness (hyp a (fromWitness a∈xs))))

restrict-op⁻ : (op : Op) (t : Trace Op)
             → restrict-trace⁻ (operation⁻ op t) ≡ restrict-trace (operation op t)
restrict-op⁻ op t with T? (OpPred op)
... | yes _ = refl
... | no  _ = refl

restrict-prepend : (d : D⁺ Op) (t : Trace Op)
                 → restrict-trace (prepend Op d t)
                 ≡ prepend Op' d (restrict-trace t)
restrict-prepend d ε                = refl
restrict-prepend d (operation op t) =
  cong (prepend Op' d) (restrict-op⁻ op t)
restrict-prepend d (delay e t)      =
  prepend-+⁺ Op' d e (restrict-trace⁻ t)

restrict-∙ : (s t : Trace Op)
           → restrict-trace (_∙_ Op s t)
           ≡ _∙_ Op' (restrict-trace s) (restrict-trace t)
restrict-∙ ε               t = refl
restrict-∙ (operation o s) t with T? (OpPred o)
... | yes p = cong (operation (operation' o p)) (restrict-∙ s t)
... | no  _ = restrict-∙ s t
restrict-∙ (delay d ε⁻)    t = restrict-prepend d t
restrict-∙ (delay d (operation⁻ o s)) t with T? (OpPred o)
... | yes p = cong (λ z → delay d (operation⁻ (operation' o p) z))
                   (restrict-∙ s t)
... | no  _ =
      trans
        (cong (prepend Op' d) (restrict-∙ s t))
        (sym (prepend-∙ Op' d (restrict-trace s) (restrict-trace t)))

restrict-map-∙ : (x : Trace Op) (ys : List (Trace Op))
               → restrict-traces (Data.List.map (_∙_ Op x) ys)
               ≡ Data.List.map (_∙_ Op' (restrict-trace x)) (restrict-traces ys)
restrict-map-∙ x []       = refl
restrict-map-∙ x (y ∷ ys) = cong₂ _∷_ (restrict-∙ x y) (restrict-map-∙ x ys)

restrict-·ˢ : (xs ys : List (Trace Op))
            → restrict-traces (S._·ˢ_ xs ys)
            ≡ S'._·ˢ_ (restrict-traces xs) (restrict-traces ys)
restrict-·ˢ []       ys = refl
restrict-·ˢ (x ∷ xs) ys =
  trans
    (map-++ restrict-trace (Data.List.map (_∙_ Op x) ys) (S._·ˢ_ xs ys))
    (cong₂ _++_ (restrict-map-∙ x ys) (restrict-·ˢ xs ys))

restrict-⟨⟩ : (τ : Carrier) → restrict-trace (⟨_⟩ Op τ) ≡ ⟨_⟩ Op' τ
restrict-⟨⟩ τ = case (0ᴰ <ᴰ? τ)
  where
    case : (p : Dec (0ᴰ <ᴰ τ)) → restrict-trace (delay-of Op τ p) ≡ delay-of Op' τ p
    case (yes _) = refl
    case (no _)  = refl