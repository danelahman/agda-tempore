-------------------------------------------------------------------------------
-- Example grade system of two-sided trace intervals as effect grades and    --
-- one-sided trace intervals as resource grades (for a subset of operations) --
-------------------------------------------------------------------------------

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

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Grades.GradeSystem.TwoSidedToLeftSidedTraceIntervals (S : LanguageSpec) where

open Grade
open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

module _ (ResOp : Op → Bool) where

  ROp : Set
  ROp = Σ[ op ∈ Op ] T (ResOp op)

  T-irrelevant : {b : Bool} → (p q : T b) → p ≡ q
  T-irrelevant {false} = λ ()
  T-irrelevant {true} = λ p q → refl

  _≟ᵣₒ_ : DecidableEquality ROp
  (op , p) ≟ᵣₒ (op' , p') with op ≟ₒ op'
  (op , p) ≟ᵣₒ (.op , p') | yes refl with T-irrelevant p p'
  (op , p) ≟ᵣₒ (.op , p') | yes refl | refl = yes refl
  (op , p) ≟ᵣₒ (op' , p') | no ¬q = no (λ { refl → ¬q refl })

  open import Syntax.Grades.Traces.TwoSidedTraces Op _≟ₒ_
  open import Syntax.Grades.Traces.LeftSidedTraces ROp _≟ᵣₒ_

  open import Syntax.Grades.Traces.Base

  -- a resource operation packaged with its membership proof

  roperation : (op : Op) → T (ResOp op) → ROp
  roperation op p = op , p

  -- the duration type `ℕ⁺` is shared between the two trace instances, but
  -- the generic `Base` interface tags it with the operation set, so we
  -- transport a duration from the `Op`-side to the `ROp`-side

  restrict-dur : ℕ⁺ Op → ℕ⁺ ROp
  restrict-dur 𝟏        = 𝟏
  restrict-dur (suc⁺ n) = suc⁺ (restrict-dur n)

  -- restricting a (two-sided) trace to the resource operations: the
  -- resource operations are kept, the non-resource operations are dropped,
  -- and the surrounding delays are merged (via `prepend`) so that no two
  -- delays end up adjacent

  mutual
    restrict-trace : Trace Op → Trace ROp
    restrict-trace ε = ε
    restrict-trace (operation op t) with T? (ResOp op)
    ... | yes p = operation (roperation op p) (restrict-trace t)
    ... | no  _ = restrict-trace t
    restrict-trace (delay τ t) = prepend _ (restrict-dur τ) (restrict-trace⁻ t)

    -- a delay-free-headed trace may, after dropping a leading non-resource
    -- operation, expose a delay; the result is therefore a full trace and
    -- the exposed leading delay is re-merged by the `prepend` in the
    -- `delay` case above

    restrict-trace⁻ : Trace⁻ Op → Trace ROp
    restrict-trace⁻ ε⁻ = ε
    restrict-trace⁻ (operation⁻ op t) with T? (ResOp op)
    ... | yes p = operation (roperation op p) (restrict-trace t)
    ... | no  _ = restrict-trace t

  restrict-traces : List (Trace Op) → List (Trace ROp)
  restrict-traces traces = Data.List.map restrict-trace traces

  -- `restrict-traces` is a `map`, so it preserves the cons/nil shape of
  -- the underlying list and hence non-emptiness

  restrict-nonempty : {traces : List (Trace Op)} → NonEmpty Op traces → NonEmpty ROp (restrict-traces traces)
  restrict-nonempty {[]}    ()
  restrict-nonempty {_ ∷ _} ne = ne

  -- the subset orders on the `Op`- and `ROp`-sides

  open WithDecEq Op _≟ₒ_ using () renaming (_⊑_ to _⊑ₒ_)
  open WithDecEq ROp _≟ᵣₒ_ using () renaming (_⊑_ to _⊑ᵣ_)

  -- restriction preserves the subset order on sets of traces

  restrict-⊑ : {xs ys : List (Trace Op)}
             → xs ⊑ₒ ys → restrict-traces xs ⊑ᵣ restrict-traces ys
  restrict-⊑ {xs} {ys} hyp s mem with ∈-map⁻ restrict-trace (toWitness mem)
  ... | a , a∈xs , refl =
        fromWitness (∈-map⁺ restrict-trace (toWitness (hyp a (fromWitness a∈xs))))

  -- restricting an operation-headed trace is unaffected by which of the
  -- two trace forms it is presented in

  restrict-op⁻ : (op : Op) (t : Trace Op)
               → restrict-trace⁻ (operation⁻ op t) ≡ restrict-trace (operation op t)
  restrict-op⁻ op t with T? (ResOp op)
  ... | yes _ = refl
  ... | no  _ = refl

  -- restriction of durations commutes with their addition

  restrict-+⁺ : (d e : ℕ⁺ Op)
              → restrict-dur (_+⁺_ Op d e) ≡ _+⁺_ ROp (restrict-dur d) (restrict-dur e)
  restrict-+⁺ 𝟏        e = refl
  restrict-+⁺ (suc⁺ d) e = cong suc⁺ (restrict-+⁺ d e)

  -- restriction commutes with prepending a delay

  restrict-prepend : (d : ℕ⁺ Op) (t : Trace Op)
                   → restrict-trace (prepend Op d t)
                   ≡ prepend ROp (restrict-dur d) (restrict-trace t)
  restrict-prepend d ε                = refl
  restrict-prepend d (operation op t) =
    cong (prepend ROp (restrict-dur d)) (restrict-op⁻ op t)
  restrict-prepend d (delay e t)      =
    trans
      (cong (λ z → prepend ROp z (restrict-trace⁻ t)) (restrict-+⁺ d e))
      (prepend-+⁺ ROp (restrict-dur d) (restrict-dur e) (restrict-trace⁻ t))

  -- restriction is a monoid homomorphism for sequencing of traces

  restrict-∙ : (s t : Trace Op)
             → restrict-trace (_∙_ Op s t)
             ≡ _∙_ ROp (restrict-trace s) (restrict-trace t)
  restrict-∙ ε               t = refl
  restrict-∙ (operation o s) t with T? (ResOp o)
  ... | yes p = cong (operation (roperation o p)) (restrict-∙ s t)
  ... | no  _ = restrict-∙ s t
  restrict-∙ (delay d ε⁻)    t = restrict-prepend d t
  restrict-∙ (delay d (operation⁻ o s)) t with T? (ResOp o)
  ... | yes p = cong (λ z → delay (restrict-dur d) (operation⁻ (roperation o p) z))
                     (restrict-∙ s t)
  ... | no  _ =
        trans
          (cong (prepend ROp (restrict-dur d)) (restrict-∙ s t))
          (sym (prepend-∙ ROp (restrict-dur d) (restrict-trace s) (restrict-trace t)))

  -- ... and hence also for the elementwise sequencing of sets of traces

  restrict-map-∙ : (x : Trace Op) (ys : List (Trace Op))
                 → restrict-traces (Data.List.map (_∙_ Op x) ys)
                 ≡ Data.List.map (_∙_ ROp (restrict-trace x)) (restrict-traces ys)
  restrict-map-∙ x []       = refl
  restrict-map-∙ x (y ∷ ys) = cong₂ _∷_ (restrict-∙ x y) (restrict-map-∙ x ys)

  restrict-·ˢ : (xs ys : List (Trace Op))
              → restrict-traces (_·ˢ_ Op xs ys)
              ≡ _·ˢ_ ROp (restrict-traces xs) (restrict-traces ys)
  restrict-·ˢ []       ys = refl
  restrict-·ˢ (x ∷ xs) ys =
    trans
      (map-++ restrict-trace (Data.List.map (_∙_ Op x) ys) (_·ˢ_ Op xs ys))
      (cong₂ _++_ (restrict-map-∙ x ys) (restrict-·ˢ xs ys))

  -- restriction maps pure delays to pure delays

  restrict-1+ : (n : ℕ) → restrict-dur (1+_ Op n) ≡ 1+_ ROp n
  restrict-1+ zero    = refl
  restrict-1+ (suc n) = cong suc⁺ (restrict-1+ n)

  restrict-⟨⟩ : (n : ℕ) → restrict-trace (⟨_⟩ Op n) ≡ ⟨_⟩ ROp n
  restrict-⟨⟩ zero    = refl
  restrict-⟨⟩ (suc n) = cong (λ d → delay d ε⁻) (restrict-1+ n)

  tst→lst : two-sided-traces →ᵍ left-sided-traces
  tst→lst = record
    { map = λ { [ neTraces lower nonempty , upper , lo⊑up ] →
        [ neTraces (restrict-traces lower) (restrict-nonempty nonempty) ,⊤⟩ }
    ; map-monotone = λ I≾J → restrict-⊑ (proj₁ I≾J)
    ; map-u = refl
    ; map-· = λ {I} {J} →
        cong [_,⊤⟩ (eqNe ROp
          (restrict-·ˢ (traces (TraceInterval.lower I))
                       (traces (TraceInterval.lower J))))
    ; map-of-nat = λ {n} → cong (λ z → [ neTraces (z ∷ []) tt ,⊤⟩) (restrict-⟨⟩ n)
    }

