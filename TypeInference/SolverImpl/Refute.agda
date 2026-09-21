------------------------------------------------------------------
-- Semantic refutation of a grade ordering against the unit       --
--                                                                --
-- `Refutedᵤ ρ` says that no grounding brings `ρ` below the unit. --
-- A constant atom of `ρ`'s normal form that is not itself below  --
-- the unit establishes it, using only the zero-product laws of   --
-- `_≾ᵣ_`; `scanᵤ` looks for such an atom with the instance's     --
-- decider. Refutation is stable under later instantiation, and   --
-- rules out entailment from every ground-realisable hypothesis   --
-- set.                                                           --
--                                                                --
-- Refutation cannot be quantified over all `Q`, as `hyp-derives` --
-- records.                                                       --
------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.Open.Hyps as H

module TypeInference.SolverImpl.Refute
  (S : LanguageSpec)
  (_≾ᵣ?_ : Decidable (Grade._≾_ (GradeSystem.RGrade (LanguageSpec.Grades S))))
  (_≾ₑ?_ : Decidable (Grade._≾_ (GradeSystem.EGrade (LanguageSpec.Grades S))))
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.Open.Grades    S
open import TypeInference.Open.Hyps      S
open import TypeInference.Open.Subst     S
open import TypeInference.Open.Grounding S

open import TypeInference.Constraints.Ground S using (_⨟ᵍ_; ⟦⟧-⨟ᵍ-r)

open import TypeInference.SolverImpl.Normal S _≾ᵣ?_ _≾ₑ?_ umin?ᵣ umin?ₑ
  using (RAtom; rc; rv; rm; ⟦_⟧ʳᵃ; ⟦_⟧ʳˢ; nrmᵣ; nrmᵣ-≡)

-- No grounding brings the expression below the unit

Refutedᵤ : ∀ {Ψ} → RExp Ψ → Set
Refutedᵤ {Ψ} ρ = (θ : Grounding Ψ) → ¬ (⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)

-- Every atom of a product below the unit is itself below the unit

atoms-≾ᵤ : ∀ {Ψ} → (as : List (RAtom Ψ)) → (θ : Grounding Ψ)
         → ⟦ ⟦ as ⟧ʳˢ ⟧ʳ θ ≾ᵣ uᵣ
         → ∀ {a} → a ∈ as → ⟦ ⟦ a ⟧ʳᵃ ⟧ʳ θ ≾ᵣ uᵣ
atoms-≾ᵤ (a ∷ as) θ le (here refl) = ≾ᵣ-zero-productˡ le
atoms-≾ᵤ (a ∷ as) θ le (there m)   = atoms-≾ᵤ as θ (≾ᵣ-zero-productʳ le) m

const-refutes : ∀ {Ψ} {c : R} → (as : List (RAtom Ψ)) → rc {Ψ} c ∈ as
              → ¬ (c ≾ᵣ uᵣ) → Refutedᵤ ⟦ as ⟧ʳˢ
const-refutes as m ¬p θ le = ¬p (atoms-≾ᵤ as θ le m)

-- Transported back along the certified normalisation

nrm-refutes : ∀ {Ψ} {c : R} → (ρ : RExp Ψ) → rc {Ψ} c ∈ nrmᵣ ρ
            → ¬ (c ≾ᵣ uᵣ) → Refutedᵤ ρ
nrm-refutes ρ m ¬p θ le =
  const-refutes (nrmᵣ ρ) m ¬p θ (subst (_≾ᵣ uᵣ) (ground-≡̂ᵣ (nrmᵣ-≡ ρ)) le)

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

-- The scan is structural over the atom list: `consᵣ` merges adjacent
-- constants, so membership need not reduce to `here refl`.

scan-∷ : ∀ {Ψ} {a : RAtom Ψ} {as : List (RAtom Ψ)}
       → Maybe (Σ[ c ∈ R ] (rc {Ψ} c ∈ as) × ¬ (c ≾ᵣ uᵣ))
       → Maybe (Σ[ c ∈ R ] (rc {Ψ} c ∈ a ∷ as) × ¬ (c ≾ᵣ uᵣ))
scan-∷ nothing            = nothing
scan-∷ (just (c , m , p)) = just (c , there m , p)

scan-atoms : ∀ {Ψ} → (as : List (RAtom Ψ))
           → Maybe (Σ[ c ∈ R ] (rc {Ψ} c ∈ as) × ¬ (c ≾ᵣ uᵣ))
scan-atoms []             = nothing
scan-atoms (rv i ∷ as)    = scan-∷ (scan-atoms as)
scan-atoms (rm i ∷ as)    = scan-∷ (scan-atoms as)
scan-atoms (rc c ∷ as) with c ≾ᵣ? uᵣ
... | yes _ = scan-∷ (scan-atoms as)
... | no ¬p = just (c , here refl , ¬p)

scanᵤ : ∀ {Ψ} → (ρ : RExp Ψ) → Maybe (Refutedᵤ ρ)
scanᵤ ρ with scan-atoms (nrmᵣ ρ)
... | nothing          = nothing
... | just (c , m , p) = just (nrm-refutes ρ m p)
