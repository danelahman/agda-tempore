-------------------------------------------------------------------
-- Restricting timed traces along a predicate on operation names --
-------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no)
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

module Syntax.Grades.Traces.Restriction
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (OpPred : Op → Bool) where

open import Syntax.Grades.Traces.Base

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

operation' : (op : Op) → T (OpPred op) → Op'
operation' op p = op , p

restrict-delay : ℕ⁺ Op → ℕ⁺ Op'
restrict-delay 𝟏        = 𝟏
restrict-delay (suc⁺ n) = suc⁺ (restrict-delay n)

mutual
  restrict-trace : Trace Op → Trace Op'
  restrict-trace ε = ε
  restrict-trace (operation op t) with T? (OpPred op)
  ... | yes p = operation (operation' op p) (restrict-trace t)
  ... | no  _ = restrict-trace t
  restrict-trace (delay τ t) = prepend _ (restrict-delay τ) (restrict-trace⁻ t)

  restrict-trace⁻ : Trace⁻ Op → Trace Op'
  restrict-trace⁻ ε⁻ = ε
  restrict-trace⁻ (operation⁻ op t) with T? (OpPred op)
  ... | yes p = operation (operation' op p) (restrict-trace t)
  ... | no  _ = restrict-trace t

restrict-traces : List (Trace Op) → List (Trace Op')
restrict-traces traces = Data.List.map restrict-trace traces

restrict-nonempty : {traces : List (Trace Op)} → NonEmpty Op traces → NonEmpty Op' (restrict-traces traces)
restrict-nonempty {[]}    ()
restrict-nonempty {_ ∷ _} ne = ne

open WithDecEq Op _≟ₒ_ using () renaming (_⊑_ to _⊑ₒ_)
open WithDecEq Op' _≟ₒ'_ using () renaming (_⊑_ to _⊑ₒ'_)

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

restrict-+⁺ : (d e : ℕ⁺ Op)
            → restrict-delay (_+⁺_ Op d e) ≡ _+⁺_ Op' (restrict-delay d) (restrict-delay e)
restrict-+⁺ 𝟏        e = refl
restrict-+⁺ (suc⁺ d) e = cong suc⁺ (restrict-+⁺ d e)

restrict-prepend : (d : ℕ⁺ Op) (t : Trace Op)
                 → restrict-trace (prepend Op d t)
                 ≡ prepend Op' (restrict-delay d) (restrict-trace t)
restrict-prepend d ε                = refl
restrict-prepend d (operation op t) =
  cong (prepend Op' (restrict-delay d)) (restrict-op⁻ op t)
restrict-prepend d (delay e t)      =
  trans
    (cong (λ z → prepend Op' z (restrict-trace⁻ t)) (restrict-+⁺ d e))
    (prepend-+⁺ Op' (restrict-delay d) (restrict-delay e) (restrict-trace⁻ t))

restrict-∙ : (s t : Trace Op)
           → restrict-trace (_∙_ Op s t)
           ≡ _∙_ Op' (restrict-trace s) (restrict-trace t)
restrict-∙ ε               t = refl
restrict-∙ (operation o s) t with T? (OpPred o)
... | yes p = cong (operation (operation' o p)) (restrict-∙ s t)
... | no  _ = restrict-∙ s t
restrict-∙ (delay d ε⁻)    t = restrict-prepend d t
restrict-∙ (delay d (operation⁻ o s)) t with T? (OpPred o)
... | yes p = cong (λ z → delay (restrict-delay d) (operation⁻ (operation' o p) z))
                   (restrict-∙ s t)
... | no  _ =
      trans
        (cong (prepend Op' (restrict-delay d)) (restrict-∙ s t))
        (sym (prepend-∙ Op' (restrict-delay d) (restrict-trace s) (restrict-trace t)))

restrict-map-∙ : (x : Trace Op) (ys : List (Trace Op))
               → restrict-traces (Data.List.map (_∙_ Op x) ys)
               ≡ Data.List.map (_∙_ Op' (restrict-trace x)) (restrict-traces ys)
restrict-map-∙ x []       = refl
restrict-map-∙ x (y ∷ ys) = cong₂ _∷_ (restrict-∙ x y) (restrict-map-∙ x ys)

restrict-·ˢ : (xs ys : List (Trace Op))
            → restrict-traces (_·ˢ_ Op xs ys)
            ≡ _·ˢ_ Op' (restrict-traces xs) (restrict-traces ys)
restrict-·ˢ []       ys = refl
restrict-·ˢ (x ∷ xs) ys =
  trans
    (map-++ restrict-trace (Data.List.map (_∙_ Op x) ys) (_·ˢ_ Op xs ys))
    (cong₂ _++_ (restrict-map-∙ x ys) (restrict-·ˢ xs ys))

restrict-1+ : (n : ℕ) → restrict-delay (1+_ Op n) ≡ 1+_ Op' n
restrict-1+ zero    = refl
restrict-1+ (suc n) = cong suc⁺ (restrict-1+ n)

restrict-⟨⟩ : (n : ℕ) → restrict-trace (⟨_⟩ Op n) ≡ ⟨_⟩ Op' n
restrict-⟨⟩ zero    = refl
restrict-⟨⟩ (suc n) = cong (λ d → delay d ε⁻) (restrict-1+ n)