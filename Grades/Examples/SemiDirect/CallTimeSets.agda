------------------------------------------------------------------------
-- Call-time sets: the durations of a computation and the times       --
-- at which each operation happens.                                   --
--                                                                    --
-- A grade `(T , E)` is "takes a number of time steps in `T`, and     --
-- performs each operation `s` only at times in `E s`", all sets of   --
-- natural numbers counted from the start. Sequencing adds the        --
-- durations and shifts the later times by the earlier durations:     --
--                                                                    --
--   (T , E) · (T' , E')  =  (T + T' , E ∪ (T + E'))                  --
--                                                                    --
-- with `+` adding sets elementwise and `∪`, `T + _` taken name by    --
-- name. The sets are the regular languages over one letter, a number --
-- `n` being the word of `n` ticks, so that `+` is concatenation.     --
--                                                                    --
-- The durations are the non-empty such sets, the regular grade over  --
-- one letter; the times are all such sets, the empty one included,   --
-- ordered by inclusion with union the join. The call-time sets       --
-- are the semidirect product of the durations with the times by      --
-- name under the shift. A shift by a non-empty set of durations is   --
-- empty only on the empty set, which is (A6). The order is           --
-- componentwise inclusion, the unit `({0} , ∅)` is not least, and    --
-- `ι n` is `({n} , ∅)`. A set of times that the shift by `T` keeps   --
-- within itself the shift by `T⁺`, Kleene's plus of the durations,   --
-- keeps within it too, and its hints declare the closure             --
--                                                                    --
--   (T , E)⁺  =  (T⁺ , E ∪ (T⁺ + E)) .                               --
--                                                                    --
-- Operations are named by natural numbers.                           --
------------------------------------------------------------------------

module Grades.Examples.SemiDirect.CallTimeSets where

open import Data.Bool.Base using (T)
open import Data.Bool.Properties using (T-∨; T-irrelevant)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero)
open import Data.Maybe.Base using (just)
open import Data.List.Base using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Bundles using (Equivalence)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (T?; recompute)

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade; Plus)
open import Grades.Hints using (GradeHints)
open import Grades.Indexed using (ℕ-names; module Maps)
open import Grades.SemiDirect using (Semilattice; Action; semidirect; semidirect⁺ʰ)

open import Grades.Regular.Automaton 1
open import Grades.Regular.Operations 1 using (_∪_; _·_; Σ*; ⟦_⟧)
open import Grades.Regular.Properties 1
  using (∪-wf; ∪-accepts; ·-wf; ∈-·; Σ*-wf; ∈-Σ*; ⟦⟧-wf)
open import Grades.Regular.Inclusion 1 using (_⊆ᵇ_)
open import Grades.Regular.Decide 1
  using (⊆ᵇ-sound; ⊆ᵇ-complete; ∅ᴰ; ∅ᴰ-wf; ∉∅ᴰ; wellFormed?)
import Grades.Regular.Grade 1 zero as Dur
import Grades.Regular.Plus as K

open Maps ℕ-names using (indexedˢ; indexedᵃ; indexed⁺; Map)
open Equivalence using (to; from)

open import Util.Equality

------------------------------------------------------------------------
-- The durations: non-empty regular sets of natural numbers

durations : Grade ℕᴰ
durations = Dur.regular-grade

Durations : Set
Durations = Dur.Regular

------------------------------------------------------------------------
-- The times: regular sets of natural numbers

record Times : Set where
  constructor times
  field
    table : DFA
    .wf   : WellFormed table

open Times public using (table)

wf′ : (E : Times) → WellFormed (table E)
wf′ (times t w) = recompute (wellFormed? t) w

infix  4 _⊑_
infixl 6 _∪ₜ_

_⊑_ : Times → Times → Set
E ⊑ E' = T (table E ⊆ᵇ table E')

⊑⇒⊆ : ∀ E E' → E ⊑ E' → table E ⊆ table E'
⊑⇒⊆ E E' = ⊆ᵇ-sound {table E} {table E'} (wf′ E) (wf′ E')

⊆⇒⊑ : ∀ E E' → table E ⊆ table E' → E ⊑ E'
⊆⇒⊑ E E' = ⊆ᵇ-complete {table E} {table E'} (wf′ E) (wf′ E')

∅ₜ : Times
∅ₜ = times ∅ᴰ ∅ᴰ-wf

ℕₜ : Times
ℕₜ = times Σ* Σ*-wf

_∪ₜ_ : Times → Times → Times
E ∪ₜ E' = times (table E ∪ table E') (∪-wf {table E} {table E'} (wf′ E) (wf′ E'))

-- a single time

⟪_⟫ₜ : ℕ → Times
⟪ n ⟫ₜ = times ⟦ replicate n zero ⟧ (⟦⟧-wf (replicate n zero))

private
  ∈∪⁺ˡ : ∀ E E' w → w ∈ table E → w ∈ table (E ∪ₜ E')
  ∈∪⁺ˡ E E' w w∈ =
    subst T (sym (∪-accepts {table E} {table E'} (wf′ E) (wf′ E') w)) (from T-∨ (inj₁ w∈))

  ∈∪⁺ʳ : ∀ E E' w → w ∈ table E' → w ∈ table (E ∪ₜ E')
  ∈∪⁺ʳ E E' w w∈ =
    subst T (sym (∪-accepts {table E} {table E'} (wf′ E) (wf′ E') w)) (from T-∨ (inj₂ w∈))

  ∈∪⁻ : ∀ E E' w → w ∈ table (E ∪ₜ E') → w ∈ table E ⊎ w ∈ table E'
  ∈∪⁻ E E' w w∈ = to T-∨ (subst T (∪-accepts {table E} {table E'} (wf′ E) (wf′ E') w) w∈)

⊑ₜ-refl : ∀ {E} → E ⊑ E
⊑ₜ-refl {E} = ⊆⇒⊑ E E λ _ w∈ → w∈

⊑ₜ-trans : ∀ {E E' E''} → E ⊑ E' → E' ⊑ E'' → E ⊑ E''
⊑ₜ-trans {E} {E'} {E''} p q = ⊆⇒⊑ E E'' λ w w∈ → ⊑⇒⊆ E' E'' q w (⊑⇒⊆ E E' p w w∈)

⊑ₜ-irrelevant : ∀ {E E'} (p q : E ⊑ E') → p ≡ q
⊑ₜ-irrelevant = T-irrelevant

∅ₜ-⊑ : ∀ E → ∅ₜ ⊑ E
∅ₜ-⊑ E = ⊆⇒⊑ ∅ₜ E λ w w∈ → ⊥-elim (∉∅ᴰ w w∈)

⊑-ℕₜ : ∀ E → E ⊑ ℕₜ
⊑-ℕₜ E = ⊆⇒⊑ E ℕₜ λ w _ → ∈-Σ* w

∪ₜ-ubˡ : ∀ E E' → E ⊑ E ∪ₜ E'
∪ₜ-ubˡ E E' = ⊆⇒⊑ E (E ∪ₜ E') (∈∪⁺ˡ E E')

∪ₜ-ubʳ : ∀ E E' → E' ⊑ E ∪ₜ E'
∪ₜ-ubʳ E E' = ⊆⇒⊑ E' (E ∪ₜ E') (∈∪⁺ʳ E E')

∪ₜ-lub : ∀ {E E' E''} → E ⊑ E'' → E' ⊑ E'' → E ∪ₜ E' ⊑ E''
∪ₜ-lub {E} {E'} {E''} p q = ⊆⇒⊑ (E ∪ₜ E') E'' λ w w∈ →
  [ ⊑⇒⊆ E E'' p w , ⊑⇒⊆ E' E'' q w ]′ (∈∪⁻ E E' w w∈)

_⊑ₜ?_ : ∀ E E' → Dec (E ⊑ E')
E ⊑ₜ? E' = T? (table E ⊆ᵇ table E')

times-semilattice : Semilattice
times-semilattice = record
  { Carrier      = Times
  ; _⊑_          = _⊑_
  ; bot          = ∅ₜ
  ; top          = ℕₜ
  ; _∨_          = _∪ₜ_
  ; ⊑-refl       = λ {E} → ⊑ₜ-refl {E}
  ; ⊑-trans      = λ {E} {E'} {E''} → ⊑ₜ-trans {E} {E'} {E''}
  ; ⊑-irrelevant = λ {E} {E'} → ⊑ₜ-irrelevant {E} {E'}
  ; _⊑?_         = _⊑ₜ?_
  ; bot-⊑        = ∅ₜ-⊑
  ; ⊑-top        = ⊑-ℕₜ
  ; ∨-ubˡ        = ∪ₜ-ubˡ
  ; ∨-ubʳ        = ∪ₜ-ubʳ
  ; ∨-lub        = λ {E} {E'} {E''} → ∪ₜ-lub {E} {E'} {E''}
  }

------------------------------------------------------------------------
-- The shift of times by durations

shift : Durations → Times → Times
shift c E = times (Dur.table c · table E) (·-wf {Dur.table c} {table E} (Dur.wf′ c) (wf′ E))

private
  ∈shift⁺ : ∀ c E x y → x ∈ Dur.table c → y ∈ table E → (x ++ y) ∈ table (shift c E)
  ∈shift⁺ c E x y x∈ y∈ =
    from (∈-· {Dur.table c} {table E} (Dur.wf′ c) (wf′ E) (x ++ y)) (x , y , refl , x∈ , y∈)

  -- a word of a shift is a word of the durations followed by a time
  ∈shift-elim : ∀ c E (P : Word → Set) w → w ∈ table (shift c E)
              → (∀ x y → x ∈ Dur.table c → y ∈ table E → P (x ++ y)) → P w
  ∈shift-elim c E P w w∈ f = go (to (∈-· {Dur.table c} {table E} (Dur.wf′ c) (wf′ E) w) w∈)
    where
      go : (∃₂ λ x y → w ≡ x ++ y × x ∈ Dur.table c × y ∈ table E) → P w
      go (x , y , eq , x∈ , y∈) = subst P (sym eq) (f x y x∈ y∈)

-- the laws of the action, (A1) to (A6)

shift-identity : ∀ E → shift Dur.𝟏 E ⊑ E × E ⊑ shift Dur.𝟏 E
shift-identity E =
    ⊆⇒⊑ (shift Dur.𝟏 E) E (λ w w∈ → ∈shift-elim Dur.𝟏 E (λ w → w ∈ table E) w w∈
      λ x y x∈ y∈ → subst (λ x → (x ++ y) ∈ table E) (sym (Dur.∈𝟏⁻ x x∈)) y∈)
  , ⊆⇒⊑ E (shift Dur.𝟏 E) (λ w w∈ → ∈shift⁺ Dur.𝟏 E [] w Dur.∈𝟏⁺ w∈)

shift-comp : ∀ c c' E → shift (c Dur.·ᴿ c') E ⊑ shift c (shift c' E)
                      × shift c (shift c' E) ⊑ shift (c Dur.·ᴿ c') E
shift-comp c c' E =
    ⊆⇒⊑ (shift (c Dur.·ᴿ c') E) (shift c (shift c' E)) (λ w w∈ →
      ∈shift-elim (c Dur.·ᴿ c') E (_∈ table (shift c (shift c' E))) w w∈
        λ xy z xy∈ z∈ → Dur.∈·-elim c c' (λ xy → (xy ++ z) ∈ table (shift c (shift c' E))) xy xy∈
          λ x y x∈ y∈ → subst (_∈ table (shift c (shift c' E))) (sym (++-assoc x y z))
                          (∈shift⁺ c (shift c' E) x (y ++ z) x∈ (∈shift⁺ c' E y z y∈ z∈)))
  , ⊆⇒⊑ (shift c (shift c' E)) (shift (c Dur.·ᴿ c') E) (λ w w∈ →
      ∈shift-elim c (shift c' E) (_∈ table (shift (c Dur.·ᴿ c') E)) w w∈
        λ x yz x∈ yz∈ → ∈shift-elim c' E (λ yz → (x ++ yz) ∈ table (shift (c Dur.·ᴿ c') E)) yz yz∈
          λ y z y∈ z∈ → subst (_∈ table (shift (c Dur.·ᴿ c') E)) (++-assoc x y z)
                          (∈shift⁺ (c Dur.·ᴿ c') E (x ++ y) z (Dur.∈·⁺ c c' x y x∈ y∈) z∈))

shift-∅ : ∀ c → shift c ∅ₜ ⊑ ∅ₜ
shift-∅ c = ⊆⇒⊑ (shift c ∅ₜ) ∅ₜ λ w w∈ →
  ∈shift-elim c ∅ₜ (_∈ table ∅ₜ) w w∈ λ x y _ y∈ → ⊥-elim (∉∅ᴰ y y∈)

shift-∪ : ∀ c E E' → shift c (E ∪ₜ E') ⊑ shift c E ∪ₜ shift c E'
shift-∪ c E E' = ⊆⇒⊑ (shift c (E ∪ₜ E')) (shift c E ∪ₜ shift c E') λ w w∈ →
  ∈shift-elim c (E ∪ₜ E') (_∈ table (shift c E ∪ₜ shift c E')) w w∈ λ x y x∈ y∈ →
    [ (λ y∈ → ∈∪⁺ˡ (shift c E) (shift c E') (x ++ y) (∈shift⁺ c E x y x∈ y∈))
    , (λ y∈ → ∈∪⁺ʳ (shift c E) (shift c E') (x ++ y) (∈shift⁺ c E' x y x∈ y∈)) ]′
    (∈∪⁻ E E' y y∈)

shift-⊔ : ∀ c c' E → shift (c Dur.⊔ᴿ c') E ⊑ shift c E ∪ₜ shift c' E
shift-⊔ c c' E = ⊆⇒⊑ (shift (c Dur.⊔ᴿ c') E) (shift c E ∪ₜ shift c' E) λ w w∈ →
  ∈shift-elim (c Dur.⊔ᴿ c') E (_∈ table (shift c E ∪ₜ shift c' E)) w w∈ λ x y x∈ y∈ →
    Dur.∈⊔-elim c c' _ x x∈
      (λ x∈ → ∈∪⁺ˡ (shift c E) (shift c' E) (x ++ y) (∈shift⁺ c E x y x∈ y∈))
      (λ x∈ → ∈∪⁺ʳ (shift c E) (shift c' E) (x ++ y) (∈shift⁺ c' E x y x∈ y∈))

shift-monoˡ : ∀ {c c' E} → c Dur.≾ c' → shift c E ⊑ shift c' E
shift-monoˡ {c} {c'} {E} p = ⊆⇒⊑ (shift c E) (shift c' E) λ w w∈ →
  ∈shift-elim c E (_∈ table (shift c' E)) w w∈ λ x y x∈ y∈ →
    ∈shift⁺ c' E x y (Dur.≾⇒⊆ c c' p x x∈) y∈

shift-monoʳ : ∀ {c E E'} → E ⊑ E' → shift c E ⊑ shift c E'
shift-monoʳ {c} {E} {E'} q = ⊆⇒⊑ (shift c E) (shift c E') λ w w∈ →
  ∈shift-elim c E (_∈ table (shift c E')) w w∈ λ x y x∈ y∈ →
    ∈shift⁺ c E' x y x∈ (⊑⇒⊆ E E' q y y∈)

-- a shift by a non-empty set is empty only on the empty set

shift-reflects-∅ : ∀ {c E} → shift c E ⊑ ∅ₜ → E ⊑ ∅ₜ
shift-reflects-∅ {c} {E} q = ⊆⇒⊑ E ∅ₜ λ y y∈ →
  ⊥-elim (∉∅ᴰ (x ++ y) (⊑⇒⊆ (shift c E) ∅ₜ q (x ++ y)
                         (∈shift⁺ c E x y (proj₂ (Dur.inhabited′ c)) y∈)))
  where x = proj₁ (Dur.inhabited′ c)

-- what a shift by `c` does not raise, a shift by its closure `c⁺`
-- does not raise either: from `c + E ⊆ E`, `c⁺ + E ⊆ E` (Kleene's
-- induction)

shift-⁺ : ∀ c {E} → shift c E ⊑ E → shift (Plus.c⁺ (Dur.plusᴿ c)) E ⊑ E
shift-⁺ c {E} q = ⊆⇒⊑ (shift c⁺ E) E λ w w∈ →
  ∈shift-elim c⁺ E (_∈ table E) w w∈ λ x y x∈ y∈ →
    K.⁺-indˡ {X = λ v → v ∈ Dur.table c} {D = λ v → v ∈ table E}
      (λ u (a , b , e , a∈ , b∈) →
         subst (_∈ table E) (sym e) (⊑⇒⊆ (shift c E) E q (a ++ b) (∈shift⁺ c E a b a∈ b∈)))
      (x ++ y) (x , y , refl , Dur.∈⁺⁻ c x x∈ , y∈)
  where
    c⁺ = Plus.c⁺ (Dur.plusᴿ c)

shift-action : Action durations times-semilattice
shift-action = record
  { act              = shift
  ; act-identity     = shift-identity
  ; act-comp         = shift-comp
  ; act-bot          = shift-∅
  ; act-∨            = shift-∪
  ; act-monoˡ        = λ {c} {c'} {E} → shift-monoˡ {c} {c'} {E}
  ; act-monoʳ        = λ {c} {E} {E'} → shift-monoʳ {c} {E} {E'}
  ; act-⊔            = shift-⊔
  ; act-reflects-bot = λ {c} {E} _ → shift-reflects-∅ {c} {E}
  }

------------------------------------------------------------------------
-- The grade

times-by-name : Semilattice
times-by-name = indexedˢ times-semilattice

call-time-sets : Grade ℕᴰ
call-time-sets =
  semidirect durations times-by-name (indexedᵃ {M = durations} {N = times-semilattice} shift-action)

-- its hints: the closure of `(T , E)` is `(T⁺ , E ∪ (T⁺ + E))`, name
-- by name; by copatterns, so that `call-time-sets` is not compared as
-- a record value

private
  module H = GradeHints
    (semidirect⁺ʰ Dur.regular-gradeʰ times-by-name
       (indexedᵃ {M = durations} {N = times-semilattice} shift-action)
       (λ c → just (indexed⁺ {M = durations} {N = times-semilattice} shift-action
                      record { closure = Dur.plusᴿ c ; act-⁺ = λ {E} → shift-⁺ c {E} })))

call-time-setsʰ : GradeHints call-time-sets
GradeHints.𝟏-least? call-time-setsʰ = H.𝟏-least?
GradeHints.·-comm?  call-time-setsʰ = H.·-comm?
GradeHints.plus?    call-time-setsʰ = H.plus?
