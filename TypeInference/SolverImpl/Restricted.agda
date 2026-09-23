------------------------------------------------------------------
-- The driver as a solver interface instance                      --
--                                                                --
-- `TypeInference.Solver.Restricted.SolverOn` asks for a solver   --
-- returning a scope, a substitution and a hypothesis set; the    --
-- driver returns a state, and `toHyps` reads its residual back   --
-- as the hypothesis set. Principality is unguarded; refutation   --
-- is guarded by `NoRig`, since at a rigid binder a failure can   --
-- be a failure of `Normal`'s decision procedures.                --
--                                                                --
-- `reportOn` is the reporting boundary on top: the same residue  --
-- with its var-rule disjunctions settled, its repeated           --
-- hypotheses dropped, the unknowns its own hypotheses fix        --
-- eliminated from it and from the reported type, every grade     --
-- expression in product normal form, and last its disjunctions   --
-- settled again and every subtyping atom and grade ordering      --
-- entailed by the others kept dropped. It is applied here, on    --
-- top of the driver.                                             --
------------------------------------------------------------------

open import Data.List.Base using (List; [])
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps as H

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Restricted
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Subtyping S using (_<:ᶜ_)

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Grounding S

open import TypeInference.Raw.Syntax S using (RawC)

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S
open import TypeInference.Constraints.Properties   S using (⊨-resp-≐ˢ; ≐ˢ-sym)

open import TypeInference.Principality      S using (Principal)
open import TypeInference.Solver.Fragment   S
open import TypeInference.Solver.Restricted S

open import TypeInference.SolverImpl.Core.Unify    S using (Rig; _∈ᶠ_)
open import TypeInference.SolverImpl.Core.UnifyMGU S using (Fixing; fixing)

open import TypeInference.SolverImpl.Resid     S
open import TypeInference.SolverImpl.State     S
open import TypeInference.SolverImpl.Solve     S opEnum umin?ᵣ umin?ₑ
open import TypeInference.SolverImpl.Principal S opEnum umin?ᵣ umin?ₑ
open import TypeInference.SolverImpl.Simplify  S umin?ᵣ umin?ₑ
  using (simplify; simplify-⊨; simplify-⊨⁻; simplify-≃; trim; trim-≃; trimElim;
         memʳ?; memᵉ?)
open import TypeInference.SolverImpl.Normal    S umin?ᵣ umin?ₑ using (decide≾ᵣ; decide≾ₑ)
open import TypeInference.SolverImpl.Eliminate S using (Elim; Entails; entails; eliminate; _⨾ᴱ_)
open import TypeInference.SolverImpl.Canon     S umin?ᵣ umin?ₑ using (canonElim)

Fixing-[] : ∀ {Θ Ψ} → (σ : Subst Θ Ψ) → Fixing [] σ
Fixing-[] σ = fixing (λ i ()) (λ i i' ())

solveOn : ∀ {Θ} → Constraint Θ
        → Maybe (Σ[ Θ' ∈ Scope ] (Subst Θ Θ' × Hyps Θ'))
solveOn C with solve init C
... | nothing = nothing
... | just (s' , m , w) with reexpand s'
...   | nothing = nothing
...   | just (s₂ , m₂) with toHyps (res s₂)
...     | nothing       = nothing
...     | just (Q , hq) = just (Ψ s₂ , θ s₂ , Q)

solveOn-sound : ∀ {Θ} → (C : Constraint Θ)
              → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
              → solveOn C ≡ just (Θ' , σ , Q)
              → σ ⊨[ Q ] C
solveOn-sound C eq with solve init C in e
... | nothing = ⊥just eq
... | just (s' , m , w) with reexpand s' in e₂
...   | nothing = ⊥just eq
...   | just (s₂ , m₂) with toHyps (res s₂) in e'
...     | nothing = ⊥just eq
...     | just (Q₀ , hq) with eq
...       | refl = ⊨-resp-≐ˢ (⨟-idʳ (θ s₂)) C (wit-mono m₂ C w idˢ Q₀ hq)

solveOn-complete : ∀ {Θ} → (C : Constraint Θ) → NoRig C
                 → solveOn C ≡ nothing
                 → ∀ {Θ'} → (σ : Subst Θ Θ') → (Q : Hyps Θ')
                 → ¬ (σ ⊨[ Q ] C)
solveOn-complete C nr eq σ Q sat with solve init C in e
... | nothing = solve-fail init C nr e σ Q (Fixing-[] σ) ⊩ᴿ-empty sat
... | just (s' , m , w) with reexpand s' in e₂
...   | nothing =
        reexpand-fail s' e₂ (proj₁ fac) Q (proj₁ (proj₂ (proj₂ fac)))
  where
    fac = solve-principal init C e σ Q sat ⊩ᴿ-empty
...   | just (s₂ , m₂) with toHyps (res s₂) in e'
...     | just _  = ⊥nothing eq
...     | nothing with toHyps-nothing (res s₂) e'
...       | inj₁ (A , mem , q) =
            etDec-refute A q (proj₁ fac₂) (⊩ts (proj₂ (proj₂ fac₂)) mem)
  where
    fac  = solve-principal init C e σ Q sat ⊩ᴿ-empty
    fac₂ = reexpand-princ s' e₂ (proj₁ fac) Q (proj₁ (proj₂ (proj₂ fac)))
...       | inj₂ (A , B , mem , q) =
            ⊥nothing (trans (sym (proj₂ (reexpand-dec s' e₂ mem))) q)

solveOn-principal : ∀ {Θ} → (C : Constraint Θ)
                  → {Θ⁺ : Scope} {σ⁺ : Subst Θ Θ⁺} {Q⁺ : Hyps Θ⁺}
                  → solveOn C ≡ just (Θ⁺ , σ⁺ , Q⁺)
                  → ∀ {Θ''} → (σ : Subst Θ Θ'') → (Q : Hyps Θ'')
                  → σ ⊨[ Q ] C
                  → Σ[ δ ∈ Subst Θ⁺ Θ'' ]
                      (((σ⁺ ⨟ˢ δ) ≐ˢ σ) × (Q ⊩ᴴ Q⁺ [ δ ]))
solveOn-principal C eq σ Q sat with solve init C in e
... | nothing = ⊥just eq
... | just (s' , m , w) with reexpand s' in e₂
...   | nothing = ⊥just eq
...   | just (s₂ , m₂) with toHyps (res s₂) in e'
...     | nothing = ⊥just eq
...     | just (Q₀ , hq) with eq
...       | refl = δ₂ , tri , toHyps-compl (res s₂) e' δ₂ h₂
  where
    fac  = solve-principal init C e σ Q sat ⊩ᴿ-empty
    δ    = proj₁ fac
    tri₁ = proj₁ (proj₂ fac)
    hres = proj₁ (proj₂ (proj₂ fac))

    fac₂ = reexpand-princ s' e₂ δ Q hres
    δ₂   = proj₁ fac₂
    tri₂ = proj₁ (proj₂ fac₂)
    h₂   = proj₂ (proj₂ fac₂)

    tri = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₂)) δ₂)
          (≐ˢ-trans (⨟-assoc (θ s') (mδ m₂) δ₂)
          (≐ˢ-trans (⨟-congʳ (θ s') tri₂)
          (≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m)) δ) tri₁)))

solverImplOn : SolverOn NoRig (λ _ → ⊤)
solverImplOn = record
  { solve           = solveOn
  ; solve-sound     = solveOn-sound
  ; solve-complete  = solveOn-complete
  ; solve-principal = λ C _ → solveOn-principal C
  }

-- The entailment test of elimination by equality: an ordering among
-- the hypotheses, or one `decide≾` proves from them

entailsᴴ : Entails
entailsᴴ = entails entᵣ? entₑ?
  where
    entᵣ? : ∀ {Θ} → (Q : Hyps Θ) → (ρ ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
    entᵣ? Q ρ ρ' with memʳ? (ρ , ρ') (ordᵣ Q)
    ... | just m  = just (hypᵣ m)
    ... | nothing = decide≾ᵣ ρ ρ'

    entₑ? : ∀ {Θ} → (Q : Hyps Θ) → (ε ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
    entₑ? Q ε ε' with memᵉ? (ε , ε') (ordₑ Q)
    ... | just m  = just (hypₑ m)
    ... | nothing = decide≾ₑ ε ε'

-- A solution, its residue as the solver returns it, the residue
-- simplified, and the simplified residue with the unknowns it fixes
-- eliminated from it and from the reported type `X`. Simplification is
-- satisfied by exactly the same groundings; elimination keeps every
-- grounding, is realised by the grounding reading each eliminated
-- unknown off its bound or the expression it equals, and reports the
-- subtype. Normalisation of the grade expressions and `trim` run as the
-- last two elimination steps.

record Reported {Θ : Scope} (X : OCType Θ) (C : Constraint Θ) : Set where
  constructor report
  field
    Θ'     : Scope
    σ      : Subst Θ Θ'
    Q      : Hyps Θ'
    Q̂      : Hyps Θ'
    X̃      : OCType Θ'
    Q̃      : Hyps Θ'
    sat    : σ ⊨[ Q ] C
    to-Q̂   : (θ : Grounding Θ') → θ ⊨ᴴ Q  → θ ⊨ᴴ Q̂
    to-Q   : (θ : Grounding Θ') → θ ⊨ᴴ Q̂ → θ ⊨ᴴ Q
    to-Q̃   : (θ : Grounding Θ') → θ ⊨ᴴ Q̂ → θ ⊨ᴴ Q̃
    realₑ  : (θ : Grounding Θ') → θ ⊨ᴴ Q̃
           → Σ[ θ' ∈ Grounding Θ' ] ((θ' ⊨ᴴ Q̂) × (⟦ X [ σ ]ᶜ ⟧ᶜ θ' ≡ ⟦ X̃ ⟧ᶜ θ))
    princₑ : (θ : Grounding Θ') → θ ⊨ᴴ Q̂ → ⟦ X̃ ⟧ᶜ θ <:ᶜ ⟦ X [ σ ]ᶜ ⟧ᶜ θ

reportOn : ∀ {Θ} → (X : OCType Θ) → (C : Constraint Θ) → Maybe (Reported X C)
reportOn X C with solveOn C in e
... | nothing           = nothing
... | just (Θ' , σ , Q) =
      just (report Θ' σ Q (simplify Q) (Elim.Ĉ el) (Elim.Q̂ el) (solveOn-sound C e)
                   (simplify-⊨ Q) (simplify-⊨⁻ Q)
                   (Elim.keep el) (Elim.real el) (Elim.princ el))
  where
    el : Elim (X [ σ ]ᶜ) (simplify Q)
    el = eliminate entailsᴴ (X [ σ ]ᶜ) (simplify Q) ⨾ᴱ canonElim _ _ ⨾ᴱ trimElim _ _

-- The same simplification and trimming where a principal type hands
-- out its residue

reportedQ : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC n} → (p : Principal Γ M)
          → Hyps (Principal.Θ⁺ p)
reportedQ p = trim (simplify (Principal.Q⁺ p))

reportedQ-≃ : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC n} → (p : Principal Γ M)
            → (θ : Grounding (Principal.Θ⁺ p))
            → (θ ⊨ᴴ Principal.Q⁺ p → θ ⊨ᴴ reportedQ p)
              × (θ ⊨ᴴ reportedQ p → θ ⊨ᴴ Principal.Q⁺ p)
reportedQ-≃ p θ =
  (λ h → proj₁ (trim-≃ _ θ) (proj₁ (simplify-≃ (Principal.Q⁺ p) θ) h)) ,
  (λ h → proj₂ (simplify-≃ (Principal.Q⁺ p) θ) (proj₂ (trim-≃ _ θ) h))
