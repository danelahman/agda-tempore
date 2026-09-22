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
-- A hypothesis set and its normal form are satisfied by exactly  --
-- the same groundings, so the normal form is stored, not merely  --
-- printed. A type and its normal form have the same denotation   --
-- at every grounding, and `canonElim` is that fact as an         --
-- elimination step.                                              --
------------------------------------------------------------------

open import Data.List.Base using (List; map)
open import Data.Maybe using (Maybe)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

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

open import Syntax.Types     S using (Eternal)
open import Syntax.Subtyping S using (_<:ᶜ_; <:ᶜ-refl)

import Syntax.Types S as T

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Grounding S

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

-- A grade expression and its normal form have the same value

⟦canon⟧-e : ∀ {Θ} {θ : Grounding Θ} → (ε : EExp Θ) → ⟦ canonₑ ε ⟧ᵉ θ ≡ ⟦ ε ⟧ᵉ θ
⟦canon⟧-e ε = sym (ground-≡̂ₑ (canonₑ-≡ ε))

⟦canon⟧-r : ∀ {Θ} {θ : Grounding Θ} → (ρ : RExp Θ) → ⟦ canonᵣ ρ ⟧ʳ θ ≡ ⟦ ρ ⟧ʳ θ
⟦canon⟧-r ρ = sym (ground-≡̂ᵣ (canonᵣ-≡ ρ))

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

⟦canon⟧-v : ∀ {Θ} {θ : Grounding Θ} → (A : OVType Θ) → ⟦ canonᵛ A ⟧ᵛ θ ≡ ⟦ A ⟧ᵛ θ
⟦canon⟧-c : ∀ {Θ} {θ : Grounding Θ} → (C : OCType Θ) → ⟦ canonᶜ C ⟧ᶜ θ ≡ ⟦ C ⟧ᶜ θ

⟦canon⟧-v (tvar α)  = refl
⟦canon⟧-v (Base b)  = refl
⟦canon⟧-v Unit      = refl
⟦canon⟧-v Bool      = refl
⟦canon⟧-v (A |×| B) = cong₂ T._|×|_ (⟦canon⟧-v A) (⟦canon⟧-v B)
⟦canon⟧-v Empty     = refl
⟦canon⟧-v (A ⇒ C)   = cong₂ T._⇒_ (⟦canon⟧-v A) (⟦canon⟧-c C)
⟦canon⟧-v ([ ρ ] A) = cong₂ T.[_]_ (⟦canon⟧-r ρ) (⟦canon⟧-v A)

⟦canon⟧-c (A ‼ ε) = cong₂ T._‼_ (⟦canon⟧-v A) (⟦canon⟧-e ε)

-- Hypothesis sets: the orderings and the var-rule disjunctions

canonᴴ : ∀ {Θ} → Hyps Θ → Hyps Θ
canonᴴ Q = hyps (ets Q) (subᵥ Q)
                (map (mapᵖ canonᵣ) (ordᵣ Q))
                (map (mapᵖ canonₑ) (ordₑ Q))
                (map (mapᵈ canonᵛ canonᵣ) (disj Q))

canonᴴ-⊨ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ canonᴴ Q
canonᴴ-⊨ {θ = θ} Q h = mk⊨ᴴ (etOK h) (subOK h) ordR ordE dsj
  where
    ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ canonᵣ) (ordᵣ Q) → ⟦ ρ ⟧ʳ θ ≾ᵣ ⟦ ρ' ⟧ʳ θ
    ordR m with ∈-map⁻ (mapᵖ canonᵣ) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
          subst₂ _≾ᵣ_ (sym (⟦canon⟧-r ρ₀)) (sym (⟦canon⟧-r ρ₀')) (ordROK h m₀)

    ordE : ∀ {ε ε'} → (ε , ε') ∈ map (mapᵖ canonₑ) (ordₑ Q) → ⟦ ε ⟧ᵉ θ ≾ₑ ⟦ ε' ⟧ᵉ θ
    ordE m with ∈-map⁻ (mapᵖ canonₑ) m
    ... | (ε₀ , ε₀') , m₀ , refl =
          subst₂ _≾ₑ_ (sym (⟦canon⟧-e ε₀)) (sym (⟦canon⟧-e ε₀')) (ordEOK h m₀)

    dsj : ∀ {A ρ} → (A , ρ) ∈ map (mapᵈ canonᵛ canonᵣ) (disj Q)
        → Eternal (⟦ A ⟧ᵛ θ) ⊎ (⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)
    dsj m with ∈-map⁻ (mapᵈ canonᵛ canonᵣ) m
    ... | (A₀ , ρ₀) , m₀ , refl =
          [ (λ et → inj₁ (subst Eternal (sym (⟦canon⟧-v A₀)) et))
          , (λ lu → inj₂ (subst (_≾ᵣ uᵣ) (sym (⟦canon⟧-r ρ₀)) lu)) ]′ (disjOK h m₀)

canonᴴ-⊨⁻ : ∀ {Θ} {θ : Grounding Θ} → (Q : Hyps Θ) → θ ⊨ᴴ canonᴴ Q → θ ⊨ᴴ Q
canonᴴ-⊨⁻ {θ = θ} Q h = mk⊨ᴴ (etOK h) (subOK h) ordR ordE dsj
  where
    ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → ⟦ ρ ⟧ʳ θ ≾ᵣ ⟦ ρ' ⟧ʳ θ
    ordR {ρ} {ρ'} m =
      subst₂ _≾ᵣ_ (⟦canon⟧-r ρ) (⟦canon⟧-r ρ')
             (ordROK h (∈-map⁺ (mapᵖ canonᵣ) m))

    ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → ⟦ ε ⟧ᵉ θ ≾ₑ ⟦ ε' ⟧ᵉ θ
    ordE {ε} {ε'} m =
      subst₂ _≾ₑ_ (⟦canon⟧-e ε) (⟦canon⟧-e ε')
             (ordEOK h (∈-map⁺ (mapᵖ canonₑ) m))

    dsj : ∀ {A ρ} → (A , ρ) ∈ disj Q → Eternal (⟦ A ⟧ᵛ θ) ⊎ (⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)
    dsj {A} {ρ} m =
      [ (λ et → inj₁ (subst Eternal (⟦canon⟧-v A) et))
      , (λ lu → inj₂ (subst (_≾ᵣ uᵣ) (⟦canon⟧-r ρ) lu)) ]′
      (disjOK h (∈-map⁺ (mapᵈ canonᵛ canonᵣ) m))

canonᴴ-≃ : ∀ {Θ} → (Q : Hyps Θ) → (θ : Grounding Θ)
         → (θ ⊨ᴴ Q → θ ⊨ᴴ canonᴴ Q) × (θ ⊨ᴴ canonᴴ Q → θ ⊨ᴴ Q)
canonᴴ-≃ Q θ = canonᴴ-⊨ Q , canonᴴ-⊨⁻ Q

-- Normalising a whole report, as an elimination step: no unknown is
-- instantiated, so the realising grounding is the one it is given.

canonElim : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → Elim C Q
canonElim C Q =
  mkElim (canonᶜ C) (canonᴴ Q)
         (λ θ h → canonᴴ-⊨ Q h)
         (λ θ h → θ , canonᴴ-⊨⁻ Q h , sym (⟦canon⟧-c C))
         (λ θ h → subst (_<:ᶜ ⟦ C ⟧ᶜ θ) (sym (⟦canon⟧-c C)) (<:ᶜ-refl (⟦ C ⟧ᶜ θ)))
