------------------------------------------------------------------
-- Normalising the grade expressions of a report                  --
--                                                                --
-- Every grade expression of a reported type and of a reported    --
-- hypothesis set is replaced by its canonical form: the          --
-- sum-of-products normal form, grouped, folded and ordered by    --
-- skeleton, with every alternative that the decider places below --
-- another dropped, so the monoid and lattice laws leave no trace --
-- in what a caller is shown. The canonical form is relative to   --
-- what the decider proves, and so to the unit-minimality         --
-- witnesses it is given.                                         --
--                                                                --
-- A hypothesis set and its normal form entail each other, so the --
-- normal form is stored, not merely printed. A type is           --
-- convertible to its normal form, and `canonElim` is that fact   --
-- as an elimination step.                                        --
------------------------------------------------------------------

open import Data.List.Base using (List; map)
open import Data.Maybe using (Maybe)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Product using (_×_; _,_)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps as H

module TypeInference.SolverImpl.Canon
  (S : LanguageSpec)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))              -- optional unit-minimality of `_≾ᵣ_`
  (umin?ₑ : Maybe (H.UnitMinₑ S))              -- optional unit-minimality of `_≾ₑ_`
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S using (⊩ᴴ-⊨ᴴ)

open import TypeInference.SolverImpl.Normal    S umin?ᵣ umin?ₑ
open import TypeInference.SolverImpl.Eliminate S using (Elim; mkElim)

-- Grouping with pruning, two alternatives being compared by the
-- decider at the empty hypothesis set, whose verdict convertibility
-- turns into absorption.
--
-- Pruning subsumes the top's absorption of the join: a top
-- alternative is a constant, so it heads the skeleton order and wins
-- every tie, and the decider places every product below it.

module Mₑ {Θ : Scope} =
  Gₑ.Pruning {Θ} (∅ᴴ ⊩_≾̂ₑ_) ≡̂ₑ-absorb
             (λ P P' → decide≾ₑ {Q = ∅ᴴ} Gₑ.⟦ P ⟧ᵖ Gₑ.⟦ P' ⟧ᵖ)

module Mᵣ {Θ : Scope} =
  Gᵣ.Pruning {Θ} (∅ᴴ ⊩_≾̂ᵣ_) ≡̂ᵣ-absorb
             (λ P P' → decide≾ᵣ {Q = ∅ᴴ} Gᵣ.⟦ P ⟧ᵖ Gᵣ.⟦ P' ⟧ᵖ)

canonSumₑ : ∀ {Θ} → Alts (List (EAtom Θ)) → Alts (List (EAtom Θ))
canonSumₑ s = fromProdsₑ (Mₑ.maximal (toProdsₑ s))

canonSumₑ-≡ : ∀ {Θ} → (s : Alts (List (EAtom Θ))) → ⟦ canonSumₑ s ⟧ᵉˢ⁺ ≡̂ₑ ⟦ s ⟧ᵉˢ⁺
canonSumₑ-≡ s =
  ≡̂ₑ-trans (fromProdsₑ-≡ (Mₑ.maximal (toProdsₑ s)))
  (≡̂ₑ-trans (Mₑ.maximal-≈ (toProdsₑ s)) (toProdsₑ-≡ s))

canonSumᵣ : ∀ {Θ} → Alts (List (RAtom Θ)) → Alts (List (RAtom Θ))
canonSumᵣ s = fromProdsᵣ (Mᵣ.maximal (toProdsᵣ s))

canonSumᵣ-≡ : ∀ {Θ} → (s : Alts (List (RAtom Θ))) → ⟦ canonSumᵣ s ⟧ʳˢ⁺ ≡̂ᵣ ⟦ s ⟧ʳˢ⁺
canonSumᵣ-≡ s =
  ≡̂ᵣ-trans (fromProdsᵣ-≡ (Mᵣ.maximal (toProdsᵣ s)))
  (≡̂ᵣ-trans (Mᵣ.maximal-≈ (toProdsᵣ s)) (toProdsᵣ-≡ s))

-- The canonical form of an expression: a join of right-nested
-- products of atoms, a lone alternative standing for itself and the
-- empty product for the unit.

canonₑ : ∀ {Θ} → EExp Θ → EExp Θ
canonₑ ε = ⟦ canonSumₑ (nrmₑ ε) ⟧ᵉᵖ⁺

canonᵣ : ∀ {Θ} → RExp Θ → RExp Θ
canonᵣ ρ = ⟦ canonSumᵣ (nrmᵣ ρ) ⟧ʳᵖ⁺

canonₑ-≡ : ∀ {Θ} → (ε : EExp Θ) → ε ≡̂ₑ canonₑ ε
canonₑ-≡ ε =
  ≡̂ₑ-trans (nrmₑ-≡ ε)
  (≡̂ₑ-trans (≡̂ₑ-sym (canonSumₑ-≡ (nrmₑ ε))) (⟦⟧ᵉᵖ⁺-≡ (canonSumₑ (nrmₑ ε))))

canonᵣ-≡ : ∀ {Θ} → (ρ : RExp Θ) → ρ ≡̂ᵣ canonᵣ ρ
canonᵣ-≡ ρ =
  ≡̂ᵣ-trans (nrmᵣ-≡ ρ)
  (≡̂ᵣ-trans (≡̂ᵣ-sym (canonSumᵣ-≡ (nrmᵣ ρ))) (⟦⟧ʳᵖ⁺-≡ (canonSumᵣ (nrmᵣ ρ))))

-- Types: the grade slots are the box grades and the effect grades

canonᵛ : ∀ {Θ} → OVType Θ → OVType Θ
canonᶜ : ∀ {Θ} → OCType Θ → OCType Θ

canonᵛ (tvar α)  = tvar α
canonᵛ (Base b)  = Base b
canonᵛ Unit      = Unit
canonᵛ Bool      = Bool
canonᵛ (A |×| B) = canonᵛ A |×| canonᵛ B
canonᵛ Empty     = Empty
canonᵛ (A ⇒ C)   = canonᵛ A ⇒ canonᶜ C
canonᵛ ([ ρ ] A) = [ canonᵣ ρ ] canonᵛ A

canonᶜ (A ‼ ε) = canonᵛ A ‼ canonₑ ε

canonᵛ-≡̂ : ∀ {Θ} → (A : OVType Θ) → A ≡̂ᵛ canonᵛ A
canonᶜ-≡̂ : ∀ {Θ} → (C : OCType Θ) → C ≡̂ᶜ canonᶜ C

canonᵛ-≡̂ (tvar α)  = tvar≡̂
canonᵛ-≡̂ (Base b)  = Base≡̂
canonᵛ-≡̂ Unit      = Unit≡̂
canonᵛ-≡̂ Bool      = Bool≡̂
canonᵛ-≡̂ (A |×| B) = canonᵛ-≡̂ A |×|≡̂ canonᵛ-≡̂ B
canonᵛ-≡̂ Empty     = Empty≡̂
canonᵛ-≡̂ (A ⇒ C)   = canonᵛ-≡̂ A ⇒≡̂ canonᶜ-≡̂ C
canonᵛ-≡̂ ([ ρ ] A) = [ canonᵣ-≡ ρ ]≡̂ canonᵛ-≡̂ A

canonᶜ-≡̂ (A ‼ ε) = canonᵛ-≡̂ A ‼≡̂ canonₑ-≡ ε

-- Hypothesis sets: the orderings and the var-rule disjunctions

canonᴴ : ∀ {Θ} → Hyps Θ → Hyps Θ
canonᴴ Q = hyps (ets Q) (subᵥ Q)
                (map (mapᵖ canonᵣ) (ordᵣ Q))
                (map (mapᵖ canonₑ) (ordₑ Q))
                (map (mapᵈ canonᵛ canonᵣ) (disj Q))

-- A set and its normal form entail each other

canonᴴ-⊩ : ∀ {Θ} → (Q : Hyps Θ) → canonᴴ Q ⊩ᴴ Q
canonᴴ-⊩ Q = mk⊩ᴴ⁼ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) ordR ordE dsj
  where
    ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → canonᴴ Q ⊩ ρ ≾̂ᵣ ρ'
    ordR {ρ} {ρ'} m =
      transᵣ (eqᵣ (canonᵣ-≡ ρ))
        (transᵣ (hypᵣ (∈-map⁺ (mapᵖ canonᵣ) m)) (eqᵣ (≡̂ᵣ-sym (canonᵣ-≡ ρ'))))

    ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → canonᴴ Q ⊩ ε ≾̂ₑ ε'
    ordE {ε} {ε'} m =
      transₑ (eqₑ (canonₑ-≡ ε))
        (transₑ (hypₑ (∈-map⁺ (mapᵖ canonₑ) m)) (eqₑ (≡̂ₑ-sym (canonₑ-≡ ε'))))

    dsj : ∀ {A ρ} → (A , ρ) ∈ disj Q → VarOK (canonᴴ Q) A ρ
    dsj {A} {ρ} m =
      hyp-ok (∈-map⁺ (mapᵈ canonᵛ canonᵣ) m) (canonᵛ-≡̂ A) (eqᵣ (canonᵣ-≡ ρ))

canonᴴ-⊩⁻ : ∀ {Θ} → (Q : Hyps Θ) → Q ⊩ᴴ canonᴴ Q
canonᴴ-⊩⁻ Q = mk⊩ᴴ⁼ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) ordR ordE dsj
  where
    ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ canonᵣ) (ordᵣ Q) → Q ⊩ ρ ≾̂ᵣ ρ'
    ordR m with ∈-map⁻ (mapᵖ canonᵣ) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
          transᵣ (eqᵣ (≡̂ᵣ-sym (canonᵣ-≡ ρ₀))) (transᵣ (hypᵣ m₀) (eqᵣ (canonᵣ-≡ ρ₀')))

    ordE : ∀ {ε ε'} → (ε , ε') ∈ map (mapᵖ canonₑ) (ordₑ Q) → Q ⊩ ε ≾̂ₑ ε'
    ordE m with ∈-map⁻ (mapᵖ canonₑ) m
    ... | (ε₀ , ε₀') , m₀ , refl =
          transₑ (eqₑ (≡̂ₑ-sym (canonₑ-≡ ε₀))) (transₑ (hypₑ m₀) (eqₑ (canonₑ-≡ ε₀')))

    dsj : ∀ {A ρ} → (A , ρ) ∈ map (mapᵈ canonᵛ canonᵣ) (disj Q) → VarOK Q A ρ
    dsj m with ∈-map⁻ (mapᵈ canonᵛ canonᵣ) m
    ... | (A₀ , ρ₀) , m₀ , refl =
          hyp-ok m₀ (≡̂ᵛ-sym (canonᵛ-≡̂ A₀)) (eqᵣ (≡̂ᵣ-sym (canonᵣ-≡ ρ₀)))

-- Normalising a whole report, as an elimination step that instantiates
-- no unknown

canonElim : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → Elim C Q
canonElim C Q =
  mkElim (canonᶜ C) (canonᴴ Q) idˢ
         (subst (canonᶜ C ≡̂ᶜ_) (sym ([id]ᶜ C)) (≡̂ᶜ-sym (canonᶜ-≡̂ C)))
         (canonᴴ-⊩ Q) (⊩ᴴ-⊨ᴴ (canonᴴ-⊩⁻ Q))
         (λ δ h → <:̂ᶜ-subst h (≡̂ᶜ-<:̂ (≡̂ᶜ-sym (canonᶜ-≡̂ C))))
