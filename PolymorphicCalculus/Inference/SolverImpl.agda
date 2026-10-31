------------------------------------------------------------------
-- The solver: solving, then reporting                          --
--                                                              --
-- The stages, each with its contract:                          --
--   * generation (`Generate`): the solutions of `C[ Γ , M ]`   --
--     are the derivations erasing to `M` (`charC`);            --
--   * the driver (`Solve`): subtyping demands expanded and     --
--     decomposed along the variance table (`Former`),          --
--     eternality decided along its eternality column           --
--     (`etDec`), other atoms residualised; a solution is       --
--     principal (`solve-principal`), a refutation sound        --
--     (`solve-fail`);                                          --
--   * the close of a rigid scope: `reexpand`, `localise`,      --
--     `splitᴿ`, `popᵉ`, then the deferred conditions retried   --
--     (`Deferred`);                                            --
--   * read-back: `toHyps`, then `checkClosed`;                 --
--   * the report (`reportSolved`): `simplify`, elimination of  --
--     unknowns (`Eliminate`), normal forms, `trim`,            --
--     strengthening, keeping the caller's unknowns and those   --
--     of the deferred conditions;                              --
--   * the report's closed check (`closedReport`).              --
-- Entailment is decided by `Entail` at explicit strengths.     --
--                                                              --
-- `runSolver` instantiates the `Solver` interface and is not   --
-- stuck without rigid binders (`runSolver-rigidFree`). `infer` --
-- is the reference entry point: a scheme is principal and its  --
-- hypotheses are satisfiable exactly when the term is typable  --
-- (`infer-typed`); a refutation means the term is untypable    --
-- (`infer-untypable`); a handler-free term is never stuck      --
-- (`infer-handlerFree`). `check` also searches for a closed    --
-- instance (`check-established`).                              --
--                                                              --
-- The hints for the grade system (`Grades.Hints`) let the      --
-- solver decide more; no declarative judgement depends on      --
-- them.                                                        --
------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.All using ([]; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)

open import Relation.Nullary using (¬_)
open import Function.Bundles using (_⇔_; Equivalence)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.Outcome

open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Inference.SolverImpl
  (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S))
  (opEnum : OpEnum S)
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import PolymorphicCalculus.Syntax.Grades    S
open import PolymorphicCalculus.Syntax.Types     S
open import PolymorphicCalculus.Syntax.Contexts  S hiding (_∷_)
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses      S
open import PolymorphicCalculus.Hypotheses.Instances S
  using (Satisfiable; Satisfiable-∅; _⊨ᴴ_; _⊩ᴼˢ_[_]; ⊩ᴼˢ-≐; _⊩_∣_[_]; _⊨_∣_; _⊨_; ⊨⇒⊩ᴴ; ⊩ᴴ⇒⊨;
         ++ᵠ⇒; ++ᵠ⇐; ⊨++ᵠ⇒; ⊨++ᵠ⇐)
open import PolymorphicCalculus.Typing  S

open import PolymorphicCalculus.Syntax.Raw S using (RawC; HandlerFreeᶜ)
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution S using (_[_]ᴿᶜ; [≐]ᴿᶜ)
open import PolymorphicCalculus.Typing.Erasure      S using (⌊_⌋ᶜ)
open import PolymorphicCalculus.Inference.Soundness  S using (ctx-substᶜ; ⌊ctxᶜ⌋; ⌊c⌋)

open import PolymorphicCalculus.Inference.Constraints.Syntax       S
open import PolymorphicCalculus.Inference.Constraints.Satisfaction S
open import PolymorphicCalculus.Inference.Constraints.Properties   S using (⊨-resp-≐ˢ; ⊨-mono)

open import PolymorphicCalculus.Inference.Generate S using (NoRigidᶜ; handlerFree-noRigidᶜ)
open import PolymorphicCalculus.Inference.Principality      S
open import PolymorphicCalculus.Inference.Solver            S

open import PolymorphicCalculus.Inference.SolverImpl.Deferred  S hints
  using (⊩ᴰ→⊩ᴼˢ; ⊩ᴼˢ→⊩ᴰ)
open import PolymorphicCalculus.Inference.SolverImpl.Resid     S
open import PolymorphicCalculus.Inference.SolverImpl.Entail    S hints
  using (checkClosed; checkClosed-⊩; checkClosed-⊆; checkClosed-fail; checkClosed-unq)
open import PolymorphicCalculus.Inference.SolverImpl.State     S
open import PolymorphicCalculus.Inference.SolverImpl.Solve     S hints opEnum
open import PolymorphicCalculus.Inference.SolverImpl.Principal S hints opEnum
open import PolymorphicCalculus.Inference.SolverImpl.RigidFree S hints opEnum using (solve-rigidFree)
open import PolymorphicCalculus.Inference.SolverImpl.Search    S hints opEnum
  using (Search; refutedˢ; openˢ; search; Establish; refutedᵉ; foundᵉ; undecidedᵉ; exhaustedᵉ;
         establish)
open import PolymorphicCalculus.Inference.SolverImpl.Simplify  S hints
  using (simplify; simplify-⊩; simplify-⊨; simplify-unq; trimElim)
open import PolymorphicCalculus.Inference.SolverImpl.Eliminate S hints
  using (Elim; Elimᶠ; eliminate; _⨾ᴱ_; canonElim)
open import PolymorphicCalculus.Inference.SolverImpl.Canon     S hints
  using (canonₑ; canonᵣ; canonₑ-≡; canonᵣ-≡)
open import PolymorphicCalculus.Inference.SolverImpl.Vars       S
  using (Vars; _∪ᵛ_; ⊆-refl; ⊆-∪ˡ; ⊆-∪ʳ; fvˢ; Fixes; fixes-id; fixes-⨟)
open import PolymorphicCalculus.Inference.SolverImpl.Strengthen S hints
  using (Ren; Strengthened; strengthen; ⌜_⌝ʳ; _[_]ᴴ; ⊩ᴴ-ren⁺; fixes-≐; fixes-⊆; fvᴰ;
         fix-⊩ᴼ; fix-⊩ᴼ⁻; conv⁻; inst⁻; keep⁻; princ⁻)

Fixing-[] : ∀ {Θ Ω} → (σ : Subst Θ Ω) → Fixing [] σ
Fixing-[] σ = fixing (λ i ()) (λ i i' ())

-- The driver's answer: a scope, a substitution, the residual read back
-- as hypotheses, and the deferred conditions, retried once more

Answer : Scope → Scope → Set
Answer Θ Θ' = Subst Θ Θ' × Hyps Θ' × QOrds Θ'

runSolverᴰ : ∀ {Θ} → Constraint Θ → Outcome (Σ[ Θ' ∈ Scope ] Answer Θ Θ')
runSolverᴰ C with solve init C
... | refuted = refuted
... | stuck   = stuck
... | solved (s' , m , w) with retry s'
...   | nothing = refuted
...   | just (s₁ , m₁) with reexpand s₁
...     | nothing = refuted
...     | just (s₂ , m₂) with toHyps (res s₂)
...       | nothing        = refuted
...       | just (Q₀ , hq) with checkClosed Q₀
...         | nothing = refuted
...         | just Q  = solved (Ω s₂ , θ s₂ , Q , dfs (res s₂))

-- The answer's hypotheses: the residual and the deferred conditions,
-- as quantified hypotheses

runSolver : ∀ {Θ} → Constraint Θ → Outcome (Σ[ Θ' ∈ Scope ] (Subst Θ Θ' × Hyps Θ'))
runSolver C with runSolverᴰ C
... | refuted                  = refuted
... | stuck                    = stuck
... | solved (Θ' , σ , Q , D) = solved (Θ' , σ , Q ++ᵠ D)

runSolver-++ᵠ : ∀ {Θ} → (C : Constraint Θ)
            → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {D : List (QOrd Θ')}
            → runSolverᴰ C ≡ solved (Θ' , σ , Q , D) → runSolver C ≡ solved (Θ' , σ , Q ++ᵠ D)
runSolver-++ᵠ C eq with runSolverᴰ C
... | solved _ with eq
...   | refl = refl

-- The residual read back has no quantified hypotheses

runSolverᴰ-unq : ∀ {Θ} → (C : Constraint Θ)
               → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {D : List (QOrd Θ')}
               → runSolverᴰ C ≡ solved (Θ' , σ , Q , D) → Unq Q
runSolverᴰ-unq C eq with solve init C
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (s' , m , w) with retry s'
...   | nothing = ⊥refuted eq
...   | just (s₁ , m₁) with reexpand s₁
...     | nothing = ⊥refuted eq
...     | just (s₂ , m₂) with toHyps (res s₂) in e'
...       | nothing = ⊥refuted eq
...       | just (Q₀ , hq) with checkClosed Q₀ in e''
...         | nothing = ⊥refuted eq
...         | just Q₁ with eq
...           | refl = checkClosed-unq Q₀ e'' (toHyps-unq (res s₂) e')

runSolverᴰ-sound : ∀ {Θ} → (C : Constraint Θ)
                 → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {D : List (QOrd Θ')}
                 → runSolverᴰ C ≡ solved (Θ' , σ , Q , D)
                 → σ ⊨[ Q ∣ D ] C
runSolverᴰ-sound C eq with solve init C
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (s' , m , w) with retry s'
...   | nothing = ⊥refuted eq
...   | just (s₁ , m₁) with reexpand s₁
...     | nothing = ⊥refuted eq
...     | just (s₂ , m₂) with toHyps (res s₂)
...       | nothing = ⊥refuted eq
...       | just (Q₀ , hq) with checkClosed Q₀ in e''
...         | nothing = ⊥refuted eq
...         | just Q₁ with eq
...           | refl = λ δ Q' → λ { (hQ , hR) →
                wit-mono m₂ C (wit-mono m₁ C w) δ Q'
                  (⊩ᴿ-bare (⊩ᴿ-resp-≐ˢ (⨟-idˡ δ) (⊩ᴿ-⨟ (⊩ᴴ-⨟ hQ (checkClosed-⊩ Q₀ e'')) hq))
                           (⊩ᴼˢ→⊩ᴰ (dfs (res s₂)) hR)) }

runSolver-sound : ∀ {Θ} → (C : Constraint Θ)
                → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
                → runSolver C ≡ solved (Θ' , σ , Q)
                → σ ⊨[ Q ] C
runSolver-sound C eq with runSolverᴰ C in e
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (Θ' , σ , Q , D) with eq
...   | refl = ⊨-resp-≐ˢ (⨟-idʳ σ) C (runSolverᴰ-sound C e idˢ (Q ++ᵠ D) (++ᵠ⇒ ⊩ᴴ-refl))

-- A refutation refutes every closed instance

runSolverᴰ-refutes : ∀ {Θ} → (C : Constraint Θ)
                   → runSolverᴰ C ≡ refuted
                   → (τ : Subst Θ ∅ˢ) → ¬ (τ ⊨[ ∅ᴴ ] C)
runSolverᴰ-refutes C eq τ sat with solve init C in e
... | refuted = solve-fail init C e τ (Fixing-[] τ) ⊩ᴿ-empty sat
... | stuck   = ⊥stuck-refuted eq
... | solved (s' , m , w) with retry s' in e₁
...   | nothing = retry-fail s' e₁ (proj₁ fac) (proj₁ (proj₂ (proj₂ fac)))
  where
    fac = solve-principal init C e τ sat ⊩ᴿ-empty
...   | just (s₁ , m₁) with reexpand s₁ in e₂
...     | nothing =
          reexpand-fail s₁ e₂ (proj₁ fac₁) ∅ᴴ (proj₁ (proj₂ (proj₂ fac₁)))
  where
    fac  = solve-principal init C e τ sat ⊩ᴿ-empty
    fac₁ = retry-princ s' e₁ (proj₁ fac) (proj₁ (proj₂ (proj₂ fac)))
...     | just (s₂ , m₂) with toHyps (res s₂) in e'
...       | just (Q₀ , hq) with checkClosed Q₀ in e''
...         | just _  = ⊥solved eq
...         | nothing =
              checkClosed-fail Q₀ e''
                (proj₁ fac₂ , ⊩ᴴ⇒⊨ (toHyps-compl (res s₂) e' (proj₁ fac₂) (proj₂ (proj₂ fac₂))))
  where
    fac  = solve-principal init C e τ sat ⊩ᴿ-empty
    fac₁ = retry-princ s' e₁ (proj₁ fac) (proj₁ (proj₂ (proj₂ fac)))
    fac₂ = reexpand-princ s₁ e₂ (proj₁ fac₁) ∅ᴴ (proj₁ (proj₂ (proj₂ fac₁)))
runSolverᴰ-refutes C eq τ sat | solved (s' , m , w) | just (s₁ , m₁) | just (s₂ , m₂) | nothing
  with toHyps-nothing (res s₂) e'
...         | inj₁ (A , mem , q) =
              etDec-refute A q (proj₁ fac₂) (⊩ts (proj₂ (proj₂ fac₂)) mem)
  where
    fac  = solve-principal init C e τ sat ⊩ᴿ-empty
    fac₁ = retry-princ s' e₁ (proj₁ fac) (proj₁ (proj₂ (proj₂ fac)))
    fac₂ = reexpand-princ s₁ e₂ (proj₁ fac₁) ∅ᴴ (proj₁ (proj₂ (proj₂ fac₁)))
...         | inj₂ (A , B , mem , q) =
              ⊥nothing (trans (sym (proj₂ (reexpand-dec s₁ e₂ mem))) q)

runSolver-refutes : ∀ {Θ} → (C : Constraint Θ)
                  → runSolver C ≡ refuted
                  → (τ : Subst Θ ∅ˢ) → ¬ (τ ⊨[ ∅ᴴ ] C)
runSolver-refutes C eq with runSolverᴰ C in e
... | refuted        = runSolverᴰ-refutes C e
... | stuck          = ⊥stuck-refuted eq
... | solved _       = ⊥solved eq

runSolver-complete : ∀ {Θ} → (C : Constraint Θ)
                   → runSolver C ≡ refuted
                   → ∀ {Θ'} → (σ : Subst Θ Θ') → (Q : Hyps Θ')
                   → Satisfiable Q
                   → ¬ (σ ⊨[ Q ] C)
runSolver-complete C eq σ Q (δ₀ , h₀) sat =
  runSolver-refutes C eq (σ ⨟ˢ δ₀) (⊨-mono (⊨⇒⊩ᴴ h₀) C sat)

-- A constraint with no rigid binder is never stuck

runSolverᴰ-rigidFree : ∀ {Θ} → (C : Constraint Θ) → RigidFree C → runSolverᴰ C ≢ stuck
runSolverᴰ-rigidFree C p with solve init C in e
... | refuted = λ ()
... | stuck   = ⊥-elim (solve-rigidFree init C p e)
... | solved (s' , m , w) with retry s'
...   | nothing = λ ()
...   | just (s₁ , m₁) with reexpand s₁
...     | nothing = λ ()
...     | just (s₂ , m₂) with toHyps (res s₂)
...       | nothing = λ ()
...       | just (Q₀ , hq) with checkClosed Q₀
...         | nothing = λ ()
...         | just _  = λ ()

runSolver-rigidFree : ∀ {Θ} → (C : Constraint Θ) → RigidFree C → runSolver C ≢ stuck
runSolver-rigidFree C p with runSolverᴰ C in e
... | refuted  = λ ()
... | stuck    = ⊥-elim (runSolverᴰ-rigidFree C p e)
... | solved _ = λ ()

runSolverᴰ-principal : ∀ {Θ} → (C : Constraint Θ)
                     → {Θ⁺ : Scope} {σ⁺ : Subst Θ Θ⁺} {Q⁺ : Hyps Θ⁺} {D⁺ : List (QOrd Θ⁺)}
                     → runSolverᴰ C ≡ solved (Θ⁺ , σ⁺ , Q⁺ , D⁺)
                     → ∀ {Θ''} → (σ : Subst Θ Θ'') → (Q : Hyps Θ'')
                     → σ ⊨[ Q ] C
                     → (δ₀ : Subst Θ'' ∅ˢ) → δ₀ ⊨ Q
                     → Σ[ δ ∈ Subst Θ⁺ ∅ˢ ]
                       (((σ⁺ ⨟ˢ δ) ≐ˢ (σ ⨟ˢ δ₀)) × (δ ⊨ Q⁺ ∣ D⁺))
runSolverᴰ-principal C eq σ Q sat δ₀ h₀ with solve init C in e
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (s' , m , w) with retry s' in e₁
...   | nothing = ⊥refuted eq
...   | just (s₁ , m₁) with reexpand s₁ in e₂
...     | nothing = ⊥refuted eq
...     | just (s₂ , m₂) with toHyps (res s₂) in e'
...       | nothing = ⊥refuted eq
...       | just (Q₀ , hq) with checkClosed Q₀ in e''
...         | nothing = ⊥refuted eq
...         | just Q₁ with eq
...           | refl = δ₂ , tri ,
                       checkClosed-⊆ Q₀ e'' (toHyps-compl (res s₂) e' δ₂ h₂)
                       , ⊩ᴰ→⊩ᴼˢ (dfs (res s₂)) (⊩dfs h₂)
  where
    fac  = solve-principal init C e (σ ⨟ˢ δ₀) (⊨-mono (⊨⇒⊩ᴴ h₀) C sat) ⊩ᴿ-empty
    δ    = proj₁ fac
    tri₀ = proj₁ (proj₂ fac)
    hres = proj₁ (proj₂ (proj₂ fac))

    fac₁ = retry-princ s' e₁ δ hres
    δ₁   = proj₁ fac₁
    tri₁ = proj₁ (proj₂ fac₁)
    h₁   = proj₁ (proj₂ (proj₂ fac₁))

    fac₂ = reexpand-princ s₁ e₂ δ₁ ∅ᴴ h₁
    δ₂   = proj₁ fac₂
    tri₂ = proj₁ (proj₂ fac₂)
    h₂   = proj₂ (proj₂ fac₂)

    tri = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₂)) δ₂)
          (≐ˢ-trans (⨟-assoc (θ s₁) (mδ m₂) δ₂)
          (≐ˢ-trans (⨟-congʳ (θ s₁) tri₂)
          (≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₁)) δ₁)
          (≐ˢ-trans (⨟-assoc (θ s') (mδ m₁) δ₁)
          (≐ˢ-trans (⨟-congʳ (θ s') tri₁)
          (≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m)) δ) tri₀))))))

runSolver-principal : ∀ {Θ} → (C : Constraint Θ)
                    → {Θ⁺ : Scope} {σ⁺ : Subst Θ Θ⁺} {Q⁺ : Hyps Θ⁺}
                    → runSolver C ≡ solved (Θ⁺ , σ⁺ , Q⁺)
                    → ∀ {Θ''} → (σ : Subst Θ Θ'') → (Q : Hyps Θ'')
                    → σ ⊨[ Q ] C
                    → (δ₀ : Subst Θ'' ∅ˢ) → δ₀ ⊨ Q
                    → Σ[ δ ∈ Subst Θ⁺ ∅ˢ ]
                      (((σ⁺ ⨟ˢ δ) ≐ˢ (σ ⨟ˢ δ₀)) × (δ ⊨ Q⁺))
runSolver-principal C eq σ Q sat δ₀ h₀ with runSolverᴰ C in e
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (Θ' , σ' , Q' , D) with eq
...   | refl with runSolverᴰ-principal C e σ Q sat δ₀ h₀
...     | δ , tri , h = δ , tri , ⊨++ᵠ⇐ h

solver : Solver
solver = record
  { solve           = runSolver
  ; solve-sound     = runSolver-sound
  ; solve-refutes   = runSolver-complete
  ; solve-principal = runSolver-principal
  }

-- A solution, its residue, and the residue simplified. Elimination by `η`
-- fixing the caller's unknowns (`w`): the reported type is `X` along `η`, the
-- reported hypotheses entail the simplified residue along `η` and keep its
-- closed instances, where the reported type is a subtype of `X`. The report
-- lives over the scope `Θ̃` of its variables, embedded by `ι`; the deferred
-- conditions `R` become `R̃`, the scheme's quantified hypotheses.

record Reported {Θ₀ Θ : Scope} (w : Subst Θ₀ Θ) (X : OCType Θ) (C : Constraint Θ) : Set where
  constructor reported
  field
    Θ'     : Scope
    σ      : Subst Θ Θ'
    Q      : Hyps Θ'
    R      : QOrds Θ'
    Q̂      : Hyps Θ'
    Θ̃      : Scope
    ι      : Ren Θ̃ Θ'
    σ̃      : Subst Θ₀ Θ̃
    X̃      : OCType Θ̃
    Q̃      : Hyps Θ̃
    R̃      : QOrds Θ̃
    η      : Subst Θ' Θ'
    sol    : runSolverᴰ C ≡ solved (Θ' , σ , Q , R)
    to-Q̂   : Q ⊨ᴴ Q̂
    to-Q   : Q̂ ⊩ᴴ Q
    fix    : w ⨟ˢ σ ⨟ˢ η ≐ˢ w ⨟ˢ σ
    σ̃-ι    : σ̃ ⨟ˢ ⌜ ι ⌝ʳ ≐ˢ w ⨟ˢ σ
    conv   : X̃ [ ⌜ ι ⌝ʳ ]ᶜ ≡̂ᶜ X [ σ ]ᶜ [ η ]ᶜ
    inst   : Q̃ [ ι ]ᴴ ⊩ᴴ Q̂ [ η ]
    instᴿ  : ∀ {Ξ} → (δ : Subst Θ' Ξ) → (Q' : Hyps Ξ)
           → Q' ⊩ᴼˢ R̃ [ ⌜ ι ⌝ʳ ⨟ˢ δ ] → Q' ⊩ᴼˢ R [ η ⨟ˢ δ ]
    to-Q̃   : (δ : Subst Θ' ∅ˢ) → ∅ᴴ ⊩ᴴ Q̂ [ δ ] → ∅ᴴ ⊩ᴴ Q̃ [ ⌜ ι ⌝ʳ ⨟ˢ δ ]
    to-R̃   : (δ : Subst Θ' ∅ˢ) → δ ⊨ Q̂ ∣ R → ∅ᴴ ⊩ᴼˢ R̃ [ ⌜ ι ⌝ʳ ⨟ˢ δ ]
    princ  : (δ : Subst Θ' ∅ˢ) → ∅ᴴ ⊩ᴴ Q̂ [ δ ]
           → ∅ᴴ ∣ X̃ [ ⌜ ι ⌝ʳ ⨟ˢ δ ]ᶜ <:̂ᶜ X [ σ ]ᶜ [ δ ]ᶜ
    ext-ι  : ∀ {Ω} → (δ : Subst Θ̃ Ω) → Σ[ δ' ∈ Subst Θ' Ω ] (⌜ ι ⌝ʳ ⨟ˢ δ' ≐ˢ δ)

-- An entry with its grade expressions in canonical form means the same

canonᵈ : ∀ {Θ} → QOrd Θ → QOrd Θ
canonᵈ (qord l k o) = qord l k (ords (map (mapᵖ canonᵣ) (ors o)) (map (mapᵖ canonₑ) (oes o)))

canonᵈ-⊩ : ∀ {Θ Ξ} {Q : Hyps Ξ} {δ : Subst Θ Ξ} → (E : QOrd Θ)
         → Q ⊩ᴼ E [ δ ] → Q ⊩ᴼ canonᵈ E [ δ ]
canonᵈ-⊩ {δ = δ} (qord l k o) h = mk⊩ᵒ r e
  where
    r : ∀ {x y} → (x , y) ∈ map (mapᵖ canonᵣ) (ors o)
      → wkᵉⁿ-H k _ ⊩ x [ δ ↑ᵉⁿ k ]ʳ ≾̂ᵣ y [ δ ↑ᵉⁿ k ]ʳ
    r m with ∈-map⁻ (mapᵖ canonᵣ) m
    ... | (x , y) , m₀ , refl =
      transᵣ (eqᵣ (≡̂ᵣ-sym (≡̂ᵣ-subst (δ ↑ᵉⁿ k) (canonᵣ-≡ x))))
             (transᵣ (⊩ors h m₀) (eqᵣ (≡̂ᵣ-subst (δ ↑ᵉⁿ k) (canonᵣ-≡ y))))

    e : ∀ {x y} → (x , y) ∈ map (mapᵖ canonₑ) (oes o)
      → wkᵉⁿ-H k _ ⊩ x [ δ ↑ᵉⁿ k ]ᵉ ≾̂ₑ y [ δ ↑ᵉⁿ k ]ᵉ
    e m with ∈-map⁻ (mapᵖ canonₑ) m
    ... | (x , y) , m₀ , refl =
      transₑ (eqₑ (≡̂ₑ-sym (≡̂ₑ-subst (δ ↑ᵉⁿ k) (canonₑ-≡ x))))
             (transₑ (⊩oes h m₀) (eqₑ (≡̂ₑ-subst (δ ↑ᵉⁿ k) (canonₑ-≡ y))))

canonᵈ-⊩⁻ : ∀ {Θ Ξ} {Q : Hyps Ξ} {δ : Subst Θ Ξ} → (E : QOrd Θ)
          → Q ⊩ᴼ canonᵈ E [ δ ] → Q ⊩ᴼ E [ δ ]
canonᵈ-⊩⁻ {δ = δ} (qord l k o) h =
  mk⊩ᵒ (λ {x} {y} m → transᵣ (eqᵣ (≡̂ᵣ-subst (δ ↑ᵉⁿ k) (canonᵣ-≡ x)))
                        (transᵣ (⊩ors h (∈-map⁺ (mapᵖ canonᵣ) m))
                                (eqᵣ (≡̂ᵣ-sym (≡̂ᵣ-subst (δ ↑ᵉⁿ k) (canonᵣ-≡ y))))))
       (λ {x} {y} m → transₑ (eqₑ (≡̂ₑ-subst (δ ↑ᵉⁿ k) (canonₑ-≡ x)))
                        (transₑ (⊩oes h (∈-map⁺ (mapᵖ canonₑ) m))
                                (eqₑ (≡̂ₑ-sym (≡̂ₑ-subst (δ ↑ᵉⁿ k) (canonₑ-≡ y))))))

∈-map-elim : ∀ {A B : Set} → (f : A → B) → {P : B → Set} → {l : List A}
           → (∀ {a} → a ∈ l → P (f a)) → ∀ {b} → b ∈ map f l → P b
∈-map-elim f {P} p m with ∈-map⁻ f m
... | a , m₀ , refl = p m₀

-- The report of what `runSolverᴰ` returns; the unknowns of the deferred
-- conditions are frozen for elimination and kept by the strengthening

reportSolved : ∀ {Θ₀ Θ} → (w : Subst Θ₀ Θ) → (X : OCType Θ) → (C : Constraint Θ)
             → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {D : List (QOrd Θ')}
             → runSolverᴰ C ≡ solved (Θ' , σ , Q , D) → Reported w X C
reportSolved w X C {Θ'} {σ} {Q} {D} e =
  reportElim (eliminate F (X [ σ ]ᶜ) (simplify Q))
  where
    open Strengthened

    F : Vars Θ'
    F = fvˢ (w ⨟ˢ σ) ∪ᵛ fvᴰ D

    u₀ : Unq (simplify Q)
    u₀ = simplify-unq (runSolverᴰ-unq C e)

    -- The report from an elimination and the strengthening of its result

    reportWith : (el : Elim (X [ σ ]ᶜ) (simplify Q)) → Fixes F (Elim.η el)
               → Strengthened (w ⨟ˢ σ) (Elim.Ĉ el) (Elim.Q̂ el) (fvᴰ D) → Reported w X C
    reportWith el fx sr =
      reported Θ' σ Q (D) (simplify Q) (Θ⁻ sr) (ι sr) (τ⁻ sr) (X⁻ sr) (Q⁻ sr)
             (D̃) (Elim.η el)
             e (simplify-⊨ Q) (simplify-⊩ Q)
             (fixes-≐ fx (w ⨟ˢ σ) (⊆-∪ˡ (fvˢ (w ⨟ˢ σ)) (fvᴰ D) ⊆-refl)) (τ-ι sr)
             (conv⁻ el sr) (inst⁻ el sr u₀) instᴿ' (keep⁻ el sr) to-R̃'
             (princ⁻ el sr) (ext-ι sr)
      where
        fxᴰ : Fixes (fvᴰ D) (Elim.η el)
        fxᴰ = fixes-⊆ (⊆-∪ʳ (fvˢ (w ⨟ˢ σ)) (fvᴰ D) ⊆-refl) fx

        read : QOrd Θ' → QOrd (Θ⁻ sr)
        read E = canonᵈ (E [ π sr ]ᵠ)

        D̃ : List (QOrd (Θ⁻ sr))
        D̃ = map read D

        -- read back along `ι`, an entry is itself
        back : ∀ {Ξ} {Q' : Hyps Ξ} {δ : Subst Θ' Ξ}
             → ∀ {E} → E ∈ D → Q' ⊩ᴼ read E [ ⌜ ι sr ⌝ʳ ⨟ˢ δ ] → Q' ⊩ᴼ E [ δ ]
        back {δ = δ} {E} m h =
          fix-⊩ᴼ⁻ (π-fix sr) ⊆-refl m
            (⊩ᴼ-resp-≐ˢ E (≐ˢ-sym (⨟-assoc (π sr) ⌜ ι sr ⌝ʳ δ))
              (⊩ᴼ-subst E (canonᵈ-⊩⁻ (E [ π sr ]ᵠ) h)))

        fwd : ∀ {Ξ} {Q' : Hyps Ξ} {δ : Subst Θ' Ξ}
            → ∀ {E} → E ∈ D → Q' ⊩ᴼ E [ δ ] → Q' ⊩ᴼ read E [ ⌜ ι sr ⌝ʳ ⨟ˢ δ ]
        fwd {δ = δ} {E} m h =
          canonᵈ-⊩ (E [ π sr ]ᵠ)
            (⊩ᴼ-subst⁻ E (⊩ᴼ-resp-≐ˢ E (⨟-assoc (π sr) ⌜ ι sr ⌝ʳ δ) (fix-⊩ᴼ (π-fix sr) ⊆-refl m h)))

        instᴿ' : ∀ {Ξ} → (δ : Subst Θ' Ξ) → (Q' : Hyps Ξ)
               → Q' ⊩ᴼˢ D̃ [ ⌜ ι sr ⌝ʳ ⨟ˢ δ ] → Q' ⊩ᴼˢ D [ Elim.η el ⨟ˢ δ ]
        instᴿ' δ Q' h =
          ⊩ᴰ→⊩ᴼˢ {Q = Q'} {δ = Elim.η el ⨟ˢ δ} D
            (λ {E} m → fix-⊩ᴼ {Q = Q'} {ρ = Elim.η el} {δ = δ} fxᴰ {D = D} ⊆-refl m
                         (back {Q' = Q'} {δ = δ} m
                           (⊩ᴼˢ→⊩ᴰ {Q = Q'} {δ = ⌜ ι sr ⌝ʳ ⨟ˢ δ} D̃ h (∈-map⁺ read m))))

        to-R̃' : (δ : Subst Θ' ∅ˢ) → δ ⊨ simplify Q ∣ D
              → ∅ᴴ ⊩ᴼˢ D̃ [ ⌜ ι sr ⌝ʳ ⨟ˢ δ ]
        to-R̃' δ h =
          ⊩ᴰ→⊩ᴼˢ {Q = ∅ᴴ} {δ = ⌜ ι sr ⌝ʳ ⨟ˢ δ} D̃
            (∈-map-elim read {P = λ E → ∅ᴴ ⊩ᴼ E [ ⌜ ι sr ⌝ʳ ⨟ˢ δ ]}
              (λ m₀ → fwd {Q' = ∅ᴴ} {δ = δ} m₀
                        (⊩ᴼˢ→⊩ᴰ {Q = ∅ᴴ} {δ = δ} D (proj₂ h) m₀)))

    -- The report from an elimination fixing `F`, and its strengthening

    reportStr : (el : Elim (X [ σ ]ᶜ) (simplify Q)) → Fixes F (Elim.η el) → Reported w X C
    reportStr el fx =
      reportWith el fx (strengthen (w ⨟ˢ σ) (Elim.Ĉ el) (Elim.Q̂ el) (fvᴰ D) (Elim.unqᴱ el u₀))

    -- The report from the elimination, followed by normal forms and `trim`

    reportElim : Elimᶠ F (X [ σ ]ᶜ) (simplify Q) → Reported w X C
    reportElim el₀ =
      reportStr (proj₁ el₀ ⨾ᴱ canonElim _ _ ⨾ᴱ trimElim _ _)
                (fixes-⨟ (fixes-⨟ (proj₂ el₀) fixes-id) fixes-id)

------------------------------------------------------------------------
-- The reference entry point
--
-- A report is a principal type scheme of `M` in `Γ`: every typing factors
-- through the principal derivation and then the report, at each closed instance.

scheme : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
       → Reported wk₊ (X̂ Θ ‼ t̂ Θ) C[ Γ , M ] → PrincipalScheme Γ M
scheme {Θ} Γ M r = mkPrincipalScheme Θ̃ σ̃ (Q̃ ++ᵠ R̃) X̃ inst' fac
  where
    open Reported r

    X : OCType (Θ +ty +e)
    X = X̂ Θ ‼ t̂ Θ

    p : PrincipalSolution Γ M
    p = principalSolution solver Γ M (runSolver-++ᵠ C[ Γ , M ] sol)

    -- a retraction of `ι`

    π : Subst Θ' Θ̃
    π = proj₁ (ext-ι idˢ)

    πι : ⌜ ι ⌝ʳ ⨟ˢ π ≐ˢ idˢ
    πι = proj₂ (ext-ι idˢ)

    -- the reported hypotheses entail the residue along `η` and `π`

    hQ : Q̃ ⊩ᴴ Q [ η ⨟ˢ π ]
    hQ = ⊩ᴴ-⨟ (⊩ᴴ-ren⁺ ι (⊩ᴴ-≐ (≐ˢ-sym πι) ⊩ᴴ-refl)) (⊩ᴴ-⨟ inst to-Q)

    -- and the reported deferred conditions the solver's, at each
    -- instance

    hR : ∀ {Θ''} → (δ : Subst Θ̃ Θ'') → (Q' : Hyps Θ'')
       → Q' ⊩ᴼˢ R̃ [ δ ] → Q' ⊩ᴼˢ Reported.R r [ η ⨟ˢ π ⨟ˢ δ ]
    hR δ Q' h =
      ⊩ᴼˢ-≐ (≐ˢ-sym (⨟-assoc η π δ))
        (instᴿ (π ⨟ˢ δ) Q'
          (⊩ᴼˢ-≐ (≐ˢ-sym (≐ˢ-trans (≐ˢ-sym (⨟-assoc ⌜ ι ⌝ʳ π δ))
                                  (≐ˢ-trans (⨟-congˡ πι δ) (⨟-idˡ δ)))) h))

    -- the program's variables follow

    ctx : ∀ {Θ''} → (δ : Subst Θ̃ Θ'') → wk₊ ⨟ˢ (σ ⨟ˢ (η ⨟ˢ π ⨟ˢ δ)) ≐ˢ σ̃ ⨟ˢ δ
    ctx δ =
      ≐ˢ-trans (≐ˢ-sym (⨟-assoc wk₊ σ (η ⨟ˢ π ⨟ˢ δ)))
      (≐ˢ-trans (≐ˢ-sym (⨟-assoc (wk₊ ⨟ˢ σ) (η ⨟ˢ π) δ))
      (⨟-congˡ
        (≐ˢ-trans (≐ˢ-sym (⨟-assoc (wk₊ ⨟ˢ σ) η π))
        (≐ˢ-trans (⨟-congˡ fix π)
        (≐ˢ-trans (⨟-congˡ (≐ˢ-sym σ̃-ι) π)
        (≐ˢ-trans (⨟-assoc σ̃ ⌜ ι ⌝ʳ π)
        (≐ˢ-trans (⨟-congʳ σ̃ πι) (⨟-idʳ σ̃))))))
        δ))

    -- and so does the type, up to convertibility

    ty : ∀ {Θ''} → (δ : Subst Θ̃ Θ'') → X [ σ ⨟ˢ (η ⨟ˢ π ⨟ˢ δ) ]ᶜ ≡̂ᶜ X̃ [ δ ]ᶜ
    ty δ =
      subst₂ _≡̂ᶜ_ eqL eqR (≡̂ᶜ-subst δ (≡̂ᶜ-subst π (≡̂ᶜ-sym conv)))
      where
        eqL : X [ σ ]ᶜ [ η ]ᶜ [ π ]ᶜ [ δ ]ᶜ ≡ X [ σ ⨟ˢ (η ⨟ˢ π ⨟ˢ δ) ]ᶜ
        eqL = trans (cong (_[ δ ]ᶜ) ([⨟]ᶜ (X [ σ ]ᶜ) η π))
              (trans ([⨟]ᶜ (X [ σ ]ᶜ) (η ⨟ˢ π) δ) ([⨟]ᶜ X σ (η ⨟ˢ π ⨟ˢ δ)))

        eqR : X̃ [ ⌜ ι ⌝ʳ ]ᶜ [ π ]ᶜ [ δ ]ᶜ ≡ X̃ [ δ ]ᶜ
        eqR = cong (_[ δ ]ᶜ) (trans ([⨟]ᶜ X̃ ⌜ ι ⌝ʳ π) (trans ([≐]ᶜ πι X̃) ([id]ᶜ X̃)))

    inst' : ∀ {Θ''} → (δ : Subst Θ̃ Θ'') → (Q' : Hyps Θ'') → Q' ⊩ᴴ Q̃ ++ᵠ R̃ [ δ ]
          → Σ[ D ∈ (Q' ∣ Γ [ σ̃ ⨟ˢ δ ]ᶜᵗˣ ⊢C⦂ X̃ [ δ ]ᶜ) ] (⌊ D ⌋ᶜ ≡ M [ σ̃ ⨟ˢ δ ]ᴿᶜ)
    inst' δ Q' hh =
      subC (ctx-substᶜ ceq D) (≡̂ᶜ-<:̂ (ty δ)) , trans (⌊ctxᶜ⌋ ceq D) (trans e meq)
      where
        τ = η ⨟ˢ π ⨟ˢ δ
        h  = proj₁ (++ᵠ⇒ hh)
        hs = proj₂ (++ᵠ⇒ hh)
        i = PrincipalSolution.instantiate p τ Q' (++ᵠ⇐ (⊩ᴴ-⨟ h hQ , hR δ Q' hs))
        D = proj₁ i
        e = proj₂ i

        ceq : Γ₊ Γ [ σ ⨟ˢ τ ]ᶜᵗˣ ≡ Γ [ σ̃ ⨟ˢ δ ]ᶜᵗˣ
        ceq = trans (Γ₊-[] Γ (σ ⨟ˢ τ)) ([≐]ᶜᵗˣ (ctx δ) Γ)

        meq : M₊ M [ σ ⨟ˢ τ ]ᴿᶜ ≡ M [ σ̃ ⨟ˢ δ ]ᴿᶜ
        meq = trans (M₊-[] M (σ ⨟ˢ τ)) ([≐]ᴿᶜ (ctx δ) M)

    fac : ∀ {Θ''} → (σ₀ : Subst Θ Θ'') → (Q₀ : Hyps Θ'') → {C₀ : OCType Θ''}
        → (D₀ : Q₀ ∣ Γ [ σ₀ ]ᶜᵗˣ ⊢C⦂ C₀) → ⌊ D₀ ⌋ᶜ ≡ M [ σ₀ ]ᴿᶜ
        → (δ₀ : Subst Θ'' ∅ˢ) → δ₀ ⊨ Q₀
        → Σ[ δ ∈ Subst Θ̃ ∅ˢ ]
            ((σ̃ ⨟ˢ δ ≐ˢ σ₀ ⨟ˢ δ₀) × (δ ⊨ Q̃ ++ᵠ R̃) × (∅ᴴ ∣ X̃ [ δ ]ᶜ <:̂ᶜ C₀ [ δ₀ ]ᶜ))
    fac σ₀ Q₀ {A₀ ‼ ε₀} D₀ e₀ δ₀ h₀ =
      ⌜ ι ⌝ʳ ⨟ˢ δ' , agree , ⊨++ᵠ⇐ (to-Q̃ δ' hQ̂ , to-R̃ δ' (hQ̂ , proj₂ hq)) ,
      <:̂ᶜ-trans (princ δ' hQ̂) below
      where
        pi   = principal-inst p σ₀ Q₀ D₀ e₀ δ₀ h₀
        δ'   = proj₁ pi
        ceq₁ = proj₁ (proj₂ pi)
        aeq  = proj₁ (proj₂ (proj₂ pi))
        le   = proj₁ (proj₂ (proj₂ (proj₂ pi)))
        hq   = ⊨++ᵠ⇒ (proj₂ (proj₂ (proj₂ (proj₂ pi))))

        hQ̂ : ∅ᴴ ⊩ᴴ Q̂ [ δ' ]
        hQ̂ = to-Q̂ δ' (proj₁ hq)

        agree : σ̃ ⨟ˢ (⌜ ι ⌝ʳ ⨟ˢ δ') ≐ˢ σ₀ ⨟ˢ δ₀
        agree =
          ≐ˢ-trans (≐ˢ-sym (⨟-assoc σ̃ ⌜ ι ⌝ʳ δ'))
          (≐ˢ-trans (⨟-congˡ σ̃-ι δ') ceq₁)

        below : ∅ᴴ ∣ X [ σ ]ᶜ [ δ' ]ᶜ <:̂ᶜ (A₀ ‼ ε₀) [ δ₀ ]ᶜ
        below =
          subst (λ A → ∅ᴴ ∣ A ‼ t̂ Θ [ σ ]ᵉ [ δ' ]ᵉ <:̂ᶜ A₀ [ δ₀ ]ᵛ ‼ ε₀ [ δ₀ ]ᵉ)
                (sym aeq) (<:̂ᵛ-refl (A₀ [ δ₀ ]ᵛ) ‼ₛ le)

-- The solver's answer, closed: an instance types `M`, and a typing
-- gives an instance

answer-typable : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
               → {Θ' : Scope} {σ : Subst (Θ +ty +e) Θ'} {Q : Hyps Θ'} {D : List (QOrd Θ')}
               → runSolverᴰ C[ Γ , M ] ≡ solved (Θ' , σ , Q , D)
               → Satisfiable (Q ++ᵠ D) → Typable Γ M
answer-typable Γ M {σ = σ} e (δ , h) =
  typable ∅ˢ (wk₊ ⨟ˢ (σ ⨟ˢ δ)) ∅ᴴ _ (ctx-substᶜ ceq D₀)
          (trans (⌊ctxᶜ⌋ ceq D₀) (trans (proj₂ i) meq)) (idˢ , ⊩ᴵ-∅)
  where
    i  = PrincipalSolution.instantiate
           (principalSolution solver Γ M (runSolver-++ᵠ C[ Γ , M ] e)) δ ∅ᴴ (⊨⇒⊩ᴴ h)
    D₀ = proj₁ i

    ceq : Γ₊ Γ [ σ ⨟ˢ δ ]ᶜᵗˣ ≡ Γ [ wk₊ ⨟ˢ (σ ⨟ˢ δ) ]ᶜᵗˣ
    ceq = Γ₊-[] Γ (σ ⨟ˢ δ)

    meq : M₊ M [ σ ⨟ˢ δ ]ᴿᶜ ≡ M [ wk₊ ⨟ˢ (σ ⨟ˢ δ) ]ᴿᶜ
    meq = M₊-[] M (σ ⨟ˢ δ)

answer-untypable : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                 → {Θ' : Scope} {σ : Subst (Θ +ty +e) Θ'} {Q : Hyps Θ'} {D : List (QOrd Θ')}
                 → runSolverᴰ C[ Γ , M ] ≡ solved (Θ' , σ , Q , D)
                 → ¬ Satisfiable (Q ++ᵠ D) → ¬ Typable Γ M
answer-untypable Γ M e n (typable Θ₀ σ₀ Q₀ (A₀ ‼ ε₀) D₀ e₀ (δ₀ , h₀)) =
  n (proj₁ f , ⊨++ᵠ⇐ (proj₂ (proj₂ f)))
  where
    f = runSolverᴰ-principal C[ Γ , M ] e (σ₀ ,ᵗ A₀ ,ᵉ ε₀) Q₀
          (typing-sat σ₀ D₀ e₀) δ₀ h₀

-- A refutation of the solver itself refutes every typing

refuted-untypable : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                  → runSolverᴰ C[ Γ , M ] ≡ refuted → ¬ Typable Γ M
refuted-untypable Γ M e (typable Θ₀ σ₀ Q₀ (A₀ ‼ ε₀) D₀ e₀ (δ₀ , h₀)) =
  runSolverᴰ-refutes C[ Γ , M ] e ((σ₀ ,ᵗ A₀ ,ᵉ ε₀) ⨟ˢ δ₀)
    (⊨-mono (⊨⇒⊩ᴴ h₀) C[ Γ , M ] (typing-sat σ₀ D₀ e₀))

-- The scheme reported from the solver's answer

answerScheme : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
             → {Θ' : Scope} {σ : Subst (Θ +ty +e) Θ'} {Q : Hyps Θ'} {D : List (QOrd Θ')}
             → runSolverᴰ C[ Γ , M ] ≡ solved (Θ' , σ , Q , D) → PrincipalScheme Γ M
answerScheme {Θ} Γ M e = scheme Γ M (reportSolved wk₊ (X̂ Θ ‼ t̂ Θ) C[ Γ , M ] e)

-- The closed check of a reported scheme: `checkClosed` on its hypotheses, which
-- elimination can make closed; a failure makes them unsatisfiable

data ClosedReport {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} (p : PrincipalScheme Γ M) : Set where
  refutedᶜ : ¬ Satisfiable (PrincipalScheme.Q̃ p) → ClosedReport p
  passedᶜ  : ClosedReport p

closedReport : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} → (p : PrincipalScheme Γ M) → ClosedReport p
closedReport p with checkClosed (PrincipalScheme.Q̃ p) in e
... | nothing = refutedᶜ (checkClosed-fail (PrincipalScheme.Q̃ p) e)
... | just _  = passedᶜ

closed-untypable : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} → (p : PrincipalScheme Γ M)
                 → ¬ Satisfiable (PrincipalScheme.Q̃ p) → ¬ Typable Γ M
closed-untypable p n t = n (Equivalence.to (typable-⇔ p) t)

------------------------------------------------------------------------
-- Inference: a principal type scheme, a refutation, or `stuck`, only where a
-- handler clause's scope closes with a local unknown `Localise` assigns no
-- value

inferReported : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n}
              → (p : PrincipalScheme Γ M) → ClosedReport p → Inference Γ M
inferReported p (refutedᶜ _) = untypable
inferReported p passedᶜ      = typed p

inferSearched : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
              → {Θ' : Scope} {σ : Subst (Θ +ty +e) Θ'} {Q : Hyps Θ'} {D : List (QOrd Θ')}
              → runSolverᴰ C[ Γ , M ] ≡ solved (Θ' , σ , Q , D) → Search Q D → Inference Γ M
inferSearched Γ M e (refutedˢ _) = untypable
inferSearched Γ M e (openˢ _ _)  = inferReported (answerScheme Γ M e) (closedReport _)

inferFrom : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
          → (s : Outcome (Σ[ Θ' ∈ Scope ] Answer (Θ +ty +e) Θ')) → runSolverᴰ C[ Γ , M ] ≡ s
          → Inference Γ M
inferFrom Γ M refuted                    e = untypable
inferFrom Γ M stuck                      e = stuck
inferFrom Γ M (solved (Θ' , σ , Q , D)) e = inferSearched Γ M e (search Q D)

infer : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n) → Inference Γ M
infer Γ M = inferFrom Γ M (runSolverᴰ C[ Γ , M ]) refl

-- An untypable verdict refutes every typing under satisfiable
-- hypotheses

inferFrom-untypable : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                    → (s : Outcome (Σ[ Θ' ∈ Scope ] Answer (Θ +ty +e) Θ'))
                    → (e : runSolverᴰ C[ Γ , M ] ≡ s)
                    → inferFrom Γ M s e ≡ untypable → ¬ Typable Γ M
inferFrom-untypable Γ M refuted                    e eq = refuted-untypable Γ M e
inferFrom-untypable Γ M stuck                      e ()
inferFrom-untypable Γ M (solved (Θ' , σ , Q , D)) e eq = searched (search Q D) eq
  where
    closed : (c : ClosedReport (answerScheme Γ M e))
             → inferReported (answerScheme Γ M e) c ≡ untypable → ¬ Typable Γ M
    closed (refutedᶜ n) eq = closed-untypable (answerScheme Γ M e) n
    closed passedᶜ      ()

    searched : (x : Search Q D) → inferSearched Γ M e x ≡ untypable → ¬ Typable Γ M
    searched (refutedˢ n) eq = answer-untypable Γ M e n
    searched (openˢ _ _)  eq = closed (closedReport _) eq

infer-untypable : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                → infer Γ M ≡ untypable → ¬ Typable Γ M
infer-untypable Γ M = inferFrom-untypable Γ M (runSolverᴰ C[ Γ , M ]) refl

-- Inference is stuck only where the solver is

inferFrom-stuck : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                → (s : Outcome (Σ[ Θ' ∈ Scope ] Answer (Θ +ty +e) Θ'))
                → (e : runSolverᴰ C[ Γ , M ] ≡ s)
                → inferFrom Γ M s e ≡ stuck → s ≡ stuck
inferFrom-stuck Γ M refuted                    e ()
inferFrom-stuck Γ M stuck                      e eq = refl
inferFrom-stuck Γ M (solved (Θ' , σ , Q , D)) e eq = ⊥-elim (searched (search Q D) eq)
  where
    closed : (c : ClosedReport (answerScheme Γ M e)) → inferReported (answerScheme Γ M e) c ≢ stuck
    closed (refutedᶜ _) ()
    closed passedᶜ      ()

    searched : (x : Search Q D) → inferSearched Γ M e x ≢ stuck
    searched (refutedˢ _) ()
    searched (openˢ _ _)  = closed (closedReport _)

------------------------------------------------------------------------
-- The check of a closed program: inference, then `Search.establish`. A closed
-- instance found satisfies the scheme; a refutation makes `M` untypable.

checkReported : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n}
              → (p : PrincipalScheme Γ M) → ClosedReport p → Check Γ M
checkReported p (refutedᶜ _) = untypable
checkReported p passedᶜ      = unestablished p

checkEstablished : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                 → {Θ' : Scope} {σ : Subst (Θ +ty +e) Θ'} {Q : Hyps Θ'} {D : List (QOrd Θ')}
                 → runSolverᴰ C[ Γ , M ] ≡ solved (Θ' , σ , Q , D) → Establish Q D → Check Γ M
checkEstablished Γ M e (refutedᵉ _) = untypable
checkEstablished Γ M e (foundᵉ s)   =
  established (answerScheme Γ M e) (Equivalence.to (typable-⇔ (answerScheme Γ M e)) (answer-typable Γ M e s))
checkEstablished Γ M e undecidedᵉ   = checkReported (answerScheme Γ M e) (closedReport _)
checkEstablished Γ M e exhaustedᵉ   = checkReported (answerScheme Γ M e) (closedReport _)

checkFrom : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
          → (s : Outcome (Σ[ Θ' ∈ Scope ] Answer (Θ +ty +e) Θ')) → runSolverᴰ C[ Γ , M ] ≡ s
          → Check Γ M
checkFrom Γ M refuted                    e = untypable
checkFrom Γ M stuck                      e = stuck
checkFrom Γ M (solved (Θ' , σ , Q , D)) e = checkEstablished Γ M e (establish Q D)

check : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n) → Check Γ M
check Γ M = checkFrom Γ M (runSolverᴰ C[ Γ , M ]) refl

checkFrom-untypable : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                    → (s : Outcome (Σ[ Θ' ∈ Scope ] Answer (Θ +ty +e) Θ'))
                    → (e : runSolverᴰ C[ Γ , M ] ≡ s)
                    → checkFrom Γ M s e ≡ untypable → ¬ Typable Γ M
checkFrom-untypable Γ M refuted                    e eq = refuted-untypable Γ M e
checkFrom-untypable Γ M stuck                      e ()
checkFrom-untypable Γ M (solved (Θ' , σ , Q , D)) e eq = established' (establish Q D) eq
  where
    closed : (c : ClosedReport (answerScheme Γ M e))
             → checkReported (answerScheme Γ M e) c ≡ untypable → ¬ Typable Γ M
    closed (refutedᶜ n) eq = closed-untypable (answerScheme Γ M e) n
    closed passedᶜ      ()

    established' : (x : Establish Q D) → checkEstablished Γ M e x ≡ untypable → ¬ Typable Γ M
    established' (refutedᵉ n) eq = answer-untypable Γ M e n
    established' (foundᵉ _)   ()
    established' undecidedᵉ   eq = closed (closedReport _) eq
    established' exhaustedᵉ   eq = closed (closedReport _) eq

checkFrom-stuck : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                → (s : Outcome (Σ[ Θ' ∈ Scope ] Answer (Θ +ty +e) Θ'))
                → (e : runSolverᴰ C[ Γ , M ] ≡ s)
                → checkFrom Γ M s e ≡ stuck → s ≡ stuck
checkFrom-stuck Γ M refuted                    e ()
checkFrom-stuck Γ M stuck                      e eq = refl
checkFrom-stuck Γ M (solved (Θ' , σ , Q , D)) e eq = ⊥-elim (established' (establish Q D) eq)
  where
    closed : (c : ClosedReport (answerScheme Γ M e)) → checkReported (answerScheme Γ M e) c ≢ stuck
    closed (refutedᶜ _) ()
    closed passedᶜ      ()

    established' : (x : Establish Q D) → checkEstablished Γ M e x ≢ stuck
    established' (refutedᵉ _) ()
    established' (foundᵉ _)   ()
    established' undecidedᵉ   = closed (closedReport _)
    established' exhaustedᵉ   = closed (closedReport _)

------------------------------------------------------------------------
-- The end-to-end theorem
--
-- A typed verdict is a principal scheme, satisfiable exactly when `M` is
-- typable; an untypable verdict is sound, so inference is complete up to
-- `stuck`, and a handler-free `M` is never stuck. An established check is typable.

infer-typed : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n) → {p : PrincipalScheme Γ M}
            → infer Γ M ≡ typed p
            → Typable Γ M ⇔ Satisfiable (PrincipalScheme.Q̃ p)
infer-typed Γ M {p} _ = typable-⇔ p

infer-unconditional : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n) → {p : PrincipalScheme Γ M}
                     → infer Γ M ≡ typed p
                     → PrincipalScheme.Q̃ p ≡ ∅ᴴ → Typable Γ M
infer-unconditional Γ M {p} _ = typable-unconditional p

infer-complete : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
               → Typable Γ M → infer Γ M ≢ untypable
infer-complete Γ M t eq = infer-untypable Γ M eq t

infer-noRigid : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
              → NoRigidᶜ (defs Γ) M → infer Γ M ≢ stuck
infer-noRigid Γ M h eq =
  runSolverᴰ-rigidFree C[ Γ , M ] (C[]-rigidFree Γ M h)
    (inferFrom-stuck Γ M (runSolverᴰ C[ Γ , M ]) refl eq)

infer-handlerFree : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                  → Unquantified (defs Γ) → HandlerFreeᶜ M → infer Γ M ≢ stuck
infer-handlerFree Γ M u h = infer-noRigid Γ M (handlerFree-noRigidᶜ u M h)

check-established : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                  → {p : PrincipalScheme Γ M} {s : Satisfiable (PrincipalScheme.Q̃ p)}
                  → check Γ M ≡ established p s → Typable Γ M
check-established Γ M {p} {s} _ = Equivalence.from (typable-⇔ p) s

check-untypable : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                → check Γ M ≡ untypable → ¬ Typable Γ M
check-untypable Γ M = checkFrom-untypable Γ M (runSolverᴰ C[ Γ , M ]) refl

check-complete : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
               → Typable Γ M → check Γ M ≢ untypable
check-complete Γ M t eq = check-untypable Γ M eq t

check-noRigid : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
              → NoRigidᶜ (defs Γ) M → check Γ M ≢ stuck
check-noRigid Γ M h eq =
  runSolverᴰ-rigidFree C[ Γ , M ] (C[]-rigidFree Γ M h)
    (checkFrom-stuck Γ M (runSolverᴰ C[ Γ , M ]) refl eq)

check-handlerFree : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                  → Unquantified (defs Γ) → HandlerFreeᶜ M → check Γ M ≢ stuck
check-handlerFree Γ M u h = check-noRigid Γ M (handlerFree-noRigidᶜ u M h)
