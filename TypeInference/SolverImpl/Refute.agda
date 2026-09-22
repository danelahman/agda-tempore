------------------------------------------------------------------
-- Semantic refutation of a grade ordering against the unit       --
--                                                                --
-- `Refutedᵤ ρ` says that no grounding brings `ρ` below the unit. --
-- A constant atom of `ρ`'s normal form that is not itself below  --
-- the unit establishes it, using only the zero-product laws of   --
-- `_≾ᵣ_`; every alternative of the sum is below the sum, so one  --
-- refuted alternative refutes the whole. `scanᵤ` looks for such  --
-- an atom with the instance's decider. Refutation is stable      --
-- under later instantiation, and rules out entailment from every --
-- ground-realisable hypothesis set.                              --
--                                                                --
-- Refutation cannot be quantified over all `Q`, as `hyp-derives` --
-- records.                                                       --
------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_,_)

open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps as H

module TypeInference.SolverImpl.Refute
  (S : LanguageSpec)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Grounding S

open import TypeInference.Constraints.Ground S using (_⨟ᵍ_; ⟦⟧-⨟ᵍ-r)

open import TypeInference.SolverImpl.Normal S umin?ᵣ umin?ₑ
  using (Alts; alt; _∷⁺_; RAtom; rc; rv; rm; ⟦_⟧ʳᵃ; ⟦_⟧ʳˢ; ⟦_⟧ʳˢ⁺;
         nrmᵣ; nrmᵣ-≡)

-- No grounding brings the expression below the unit

Refutedᵤ : ∀ {Ψ} → RExp Ψ → Set
Refutedᵤ {Ψ} ρ = (θ : Grounding Ψ) → ¬ (⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)

-- A product below the unit has both halves below the unit, so a
-- refutation of either half refutes the product

head-refutes : ∀ {Ψ} → (a : RAtom Ψ) → (as : List (RAtom Ψ))
             → Refutedᵤ ⟦ a ⟧ʳᵃ → Refutedᵤ ⟦ a ∷ as ⟧ʳˢ
head-refutes a as ref θ le = ref θ (≾ᵣ-zero-productˡ le)

tail-refutes : ∀ {Ψ} → (a : RAtom Ψ) → (as : List (RAtom Ψ))
             → Refutedᵤ ⟦ as ⟧ʳˢ → Refutedᵤ ⟦ a ∷ as ⟧ʳˢ
tail-refutes a as ref θ le = ref θ (≾ᵣ-zero-productʳ le)

-- A constant that is not below the unit, and a join one of whose
-- operands is refuted

const-refutes : ∀ {Ψ} {c : R} → ¬ (c ≾ᵣ uᵣ) → Refutedᵤ (rconst {Ψ} c)
const-refutes ¬p θ le = ¬p le

join-refutesˡ : ∀ {Ψ} {ρ ρ' : RExp Ψ} → Refutedᵤ ρ → Refutedᵤ (ρ ⊔̂ᵣ ρ')
join-refutesˡ {ρ = ρ} {ρ' = ρ'} ref θ le =
  ref θ (≾ᵣ-trans (⊔ᵣ-ubˡ (⟦ ρ ⟧ʳ θ) (⟦ ρ' ⟧ʳ θ)) le)

join-refutesʳ : ∀ {Ψ} {ρ ρ' : RExp Ψ} → Refutedᵤ ρ' → Refutedᵤ (ρ ⊔̂ᵣ ρ')
join-refutesʳ {ρ = ρ} {ρ' = ρ'} ref θ le =
  ref θ (≾ᵣ-trans (⊔ᵣ-ubʳ (⟦ ρ ⟧ʳ θ) (⟦ ρ' ⟧ʳ θ)) le)

-- Transported along a convertibility, and so along the certified
-- normalisation

refute-≡̂ᵣ : ∀ {Ψ} {ρ ρ' : RExp Ψ} → ρ ≡̂ᵣ ρ' → Refutedᵤ ρ' → Refutedᵤ ρ
refute-≡̂ᵣ eq ref θ le = ref θ (subst (_≾ᵣ uᵣ) (ground-≡̂ᵣ eq) le)

-- Refutation survives every later instantiation

refute-[]ʳ : ∀ {Ψ Ψ'} {ρ : RExp Ψ} → (δ : Subst Ψ Ψ')
           → Refutedᵤ ρ → Refutedᵤ (ρ [ δ ]ʳ)
refute-[]ʳ {ρ = ρ} δ ref θ le = ref (δ ⨟ᵍ θ) (subst (_≾ᵣ uᵣ) (⟦⟧-⨟ᵍ-r δ θ ρ) le)

-- A refuted expression is entailed by no ground-realisable hypothesis set

refute-⊩ : ∀ {Ψ} {ρ : RExp Ψ} {Q : Hyps Ψ} → (θ : Grounding Ψ) → θ ⊨ᴴ Q
         → Refutedᵤ ρ → ¬ (Q ⊩ ρ ≾̂ᵣ ûᵣ)
refute-⊩ θ h ref d = ref θ (ground-≾ᵣ h d)

-- Ground realisability is essential: a hypothesis names any ordering at all

hyp-derives : ∀ {Ψ} → (ρ : RExp Ψ) → hyps [] [] ((ρ , ûᵣ) ∷ []) [] [] ⊩ ρ ≾̂ᵣ ûᵣ
hyp-derives ρ = hypᵣ (here refl)

-- The scan is structural over the alternatives of the sum and over
-- the atoms of each.

scan-atom : ∀ {Ψ} → (a : RAtom Ψ) → Maybe (Refutedᵤ ⟦ a ⟧ʳᵃ)
scan-atom (rv i) = nothing
scan-atom (rm i) = nothing
scan-atom (rc c) with c ≾ᵣ? uᵣ
... | yes _ = nothing
... | no ¬p = just (const-refutes ¬p)

scan-atoms : ∀ {Ψ} → (as : List (RAtom Ψ)) → Maybe (Refutedᵤ ⟦ as ⟧ʳˢ)
scan-atoms []       = nothing
scan-atoms (a ∷ as) with scan-atom a | scan-atoms as
... | just r  | _      = just (head-refutes a as r)
... | nothing | just r = just (tail-refutes a as r)
... | nothing | nothing = nothing

scan-sum : ∀ {Ψ} → (s : Alts (List (RAtom Ψ))) → Maybe (Refutedᵤ ⟦ s ⟧ʳˢ⁺)
scan-sum (alt P)  = scan-atoms P
scan-sum (P ∷⁺ t) with scan-atoms P | scan-sum t
... | just r  | _      = just (join-refutesˡ {ρ = ⟦ P ⟧ʳˢ} {ρ' = ⟦ t ⟧ʳˢ⁺} r)
... | nothing | just r = just (join-refutesʳ {ρ = ⟦ P ⟧ʳˢ} {ρ' = ⟦ t ⟧ʳˢ⁺} r)
... | nothing | nothing = nothing

scanᵤ : ∀ {Ψ} → (ρ : RExp Ψ) → Maybe (Refutedᵤ ρ)
scanᵤ ρ with scan-sum (nrmᵣ ρ)
... | nothing = nothing
... | just r  = just (refute-≡̂ᵣ (nrmᵣ-≡ ρ) r)
