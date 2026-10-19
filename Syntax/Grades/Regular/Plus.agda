------------------------------------------------------------------------
-- Kleene's plus of a regular grade.                                  --
--                                                                    --
-- `c⁺ = c · c*` is the least language above `c` closed under         --
-- concatenation, and it satisfies the induction laws of a Kleene     --
-- algebra: what `c` does not move on one side, `c⁺` does not move    --
-- either. The proofs are about words, by induction on iteration.     --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)

module Syntax.Grades.Regular.Plus (k : ℕ) (tick : Fin k) where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product.Base using (_×_; _,_; ∃; ∃₂)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality

open import Syntax.Grades using (Plus; plus)
open import Syntax.Grades.Regular.Automaton k
open import Syntax.Grades.Regular.Operations k using (_*)
open import Syntax.Grades.Regular.Properties k using (*-wf; *-canonical; ∈-*)
open import Syntax.Grades.Regular.Constructions k using (_∈*_; none; more)
open import Syntax.Grades.Regular.Grade k tick

open Equivalence using (to; from)

------------------------------------------------------------------------
-- Iteration

starᴿ : Regular → Regular
starᴿ c = regular (table c *) (*-wf (wf′ c)) (*-canonical (wf′ c))
                  ([] , from (∈-* (wf′ c) []) (none refl))

∈*⁻ : ∀ c w → w ∈ table (starᴿ c) → w ∈* table c
∈*⁻ c w = to (∈-* (wf′ c) w)

∈*⁺ : ∀ c w → w ∈* table c → w ∈ table (starᴿ c)
∈*⁺ c w = from (∈-* (wf′ c) w)

-- iterated words concatenate

*-++ : ∀ {L : DFA} {x y} → x ∈* L → y ∈* L → (x ++ y) ∈* L
*-++ {L} {y = y} (none refl)          ys = ys
*-++ {L} {y = y} (more u v refl u∈ vs) ys =
  more u (v ++ y) (++-assoc u v y) u∈ (*-++ {L} vs ys)

-- a language absorbing `L` on the left absorbs its iteration

*-absorbˡ : ∀ {L : DFA} {D : DFA} → (∀ u z → u ∈ L → z ∈ D → (u ++ z) ∈ D)
          → ∀ {y} z → y ∈* L → z ∈ D → (y ++ z) ∈ D
*-absorbˡ             f z (none refl)            z∈ = z∈
*-absorbˡ {L} {D} f z (more u v refl u∈ vs)  z∈ =
  subst (λ w → w ∈ D) (sym (++-assoc u v z)) (f u (v ++ z) u∈ (*-absorbˡ {L} {D} f z vs z∈))

-- ... and on the right

*-absorbʳ : ∀ {L : DFA} {D : DFA} → (∀ z u → z ∈ D → u ∈ L → (z ++ u) ∈ D)
          → ∀ {y} z → y ∈* L → z ∈ D → (z ++ y) ∈ D
*-absorbʳ {L} {D} f z (none refl)           z∈ = subst (λ w → w ∈ D) (sym (++-identityʳ z)) z∈
*-absorbʳ {L} {D} f z (more u v refl u∈ vs) z∈ =
  subst (λ w → w ∈ D) (++-assoc z u v) (*-absorbʳ {L} {D} f (z ++ u) vs (f z u z∈ u∈))

------------------------------------------------------------------------
-- The plus

plusᴿ : (c : Regular) → Plus _·ᴿ_ _≾_ c
plusᴿ c = plus c⁺ ≾-c⁺ c⁺-iter (λ {v} → least {v}) (λ {d} → indˡ {d}) (λ {d} → indʳ {d})
  where
    c⁺ = c ·ᴿ starᴿ c

    ≾-c⁺ : c ≾ c⁺
    ≾-c⁺ = ⊆⇒≾ c c⁺ λ w w∈ →
      subst (λ w → w ∈ table c⁺) (++-identityʳ w) (∈·⁺ c (starᴿ c) w [] w∈ (∈*⁺ c [] (none refl)))

    c⁺-iter : c⁺ ·ᴿ c⁺ ≾ c⁺
    c⁺-iter = ⊆⇒≾ (c⁺ ·ᴿ c⁺) c⁺ λ w w∈ →
      ∈·-elim c⁺ c⁺ (_∈ table c⁺) w w∈ λ a b a∈ b∈ →
        ∈·-elim c (starᴿ c) (λ v → (v ++ b) ∈ table c⁺) a a∈ λ x y x∈ y∈ →
          ∈·-elim c (starᴿ c) (λ v → ((x ++ y) ++ v) ∈ table c⁺) b b∈ λ z t z∈ t∈ →
            subst (λ w → w ∈ table c⁺) (sym (++-assoc x y (z ++ t)))
              (∈·⁺ c (starᴿ c) x (y ++ (z ++ t)) x∈
                (∈*⁺ c _ (*-++ (∈*⁻ c y y∈) (more z t refl z∈ (∈*⁻ c t t∈)))))

    least : ∀ {v} → c ≾ v → (v ·ᴿ v) ≾ v → c⁺ ≾ v
    least {v} cv vv = ⊆⇒≾ c⁺ v λ w w∈ →
      ∈·-elim c (starᴿ c) (_∈ table v) w w∈ λ x y x∈ y∈ →
        *-absorbʳ {L = table c} {D = table v}
          (λ z u z∈ u∈ → ≾⇒⊆ (v ·ᴿ v) v vv (z ++ u) (∈·⁺ v v z u z∈ (≾⇒⊆ c v cv u u∈)))
          x (∈*⁻ c y y∈) (≾⇒⊆ c v cv x x∈)

    indˡ : ∀ {d} → (c ·ᴿ d) ≾ d → (c⁺ ·ᴿ d) ≾ d
    indˡ {d} cd = ⊆⇒≾ (c⁺ ·ᴿ d) d λ w w∈ →
      ∈·-elim c⁺ d (_∈ table d) w w∈ λ a z a∈ z∈ →
        ∈·-elim c (starᴿ c) (λ v → (v ++ z) ∈ table d) a a∈ λ x y x∈ y∈ →
          subst (λ w → w ∈ table d) (sym (++-assoc x y z))
            (≾⇒⊆ (c ·ᴿ d) d cd (x ++ (y ++ z))
              (∈·⁺ c d x (y ++ z) x∈
                (*-absorbˡ {L = table c} {D = table d}
                  (λ u t u∈ t∈ → ≾⇒⊆ (c ·ᴿ d) d cd (u ++ t) (∈·⁺ c d u t u∈ t∈))
                  z (∈*⁻ c y y∈) z∈)))

    indʳ : ∀ {d} → (d ·ᴿ c) ≾ d → (d ·ᴿ c⁺) ≾ d
    indʳ {d} dc = ⊆⇒≾ (d ·ᴿ c⁺) d λ w w∈ →
      ∈·-elim d c⁺ (_∈ table d) w w∈ λ z a z∈ a∈ →
        ∈·-elim c (starᴿ c) (λ v → (z ++ v) ∈ table d) a a∈ λ x y x∈ y∈ →
          subst (λ w → w ∈ table d) (++-assoc z x y)
            (*-absorbʳ {L = table c} {D = table d}
              (λ t u t∈ u∈ → ≾⇒⊆ (d ·ᴿ c) d dc (t ++ u) (∈·⁺ d c t u t∈ u∈))
              (z ++ x) (∈*⁻ c y y∈)
              (≾⇒⊆ (d ·ᴿ c) d dc (z ++ x) (∈·⁺ d c z x z∈ x∈)))

-- the closure is the product with the iteration

c⁺-def : ∀ c → Plus.c⁺ (plusᴿ c) ≡ c ·ᴿ starᴿ c
c⁺-def c = refl
