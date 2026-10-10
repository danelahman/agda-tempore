------------------------------------------------------------------
-- The solver: solving, then reporting                          --
--                                                              --
-- The stages, each with the lemmas stating its contract:       --
--                                                              --
--   * Generation (`Generate`): the solutions of `C[ Γ , M ]`   --
--     are the derivations erasing to `M` (`charC`).            --
--   * The driver (`Solve`): subtyping demands, type equations  --
--     included, are expanded (`expandSub-dec`,                 --
--     `expandSub-max`) and decomposed exactly along the        --
--     variance table of the type formers (`Former`: `Decomp`,  --
--     `<:-intro`/`<:-elim`; `SubDec`'s `intro`/`elim`,         --
--     `atomiseᴿ-sound`/`atomiseᴿ-compl`); eternality demands   --
--     and the type side of var-rule disjunctions are decided   --
--     when pushed, along its eternality column                 --
--     (`etDec-intro`/`-compl`/`-refute`, `etDec-grade`); other --
--     atoms are residualised. A solution carries its witness   --
--     (`Wit`) and is principal (`solve-principal`); a          --
--     refutation is sound (`solve-fail`).                      --
--   * The close of a clause's rigid scope: `reexpand`          --
--     (`reexpand-princ`/`-fail`), `Localise.localise`          --
--     (`Localised`, `localise-princ`), `splitᴿ`                --
--     (`splitᴿ-princ`/`-fail`), `popᵉ`                         --
--     (`popᵉ-princ`/`-escape`/`-fail`).                        --
--   * Deferred conditions (`Deferred`), retried after each     --
--     close (`retry-princ`/`-fail`) and read back as           --
--     obligations (`toOblig`).                                 --
--   * Read-back: `toHyps` (`toHyps-compl`, `etDec-refute`),    --
--     then `closedᴴ`, which decides the closed atoms and the   --
--     closed orderings entailed by transitivity                --
--     (`closedᴴ-⊩`/`-⊆`/`-fail`).                              --
--   * The report (`report`, `Reported`): `simplify`            --
--     (`simplify-⊩`/`-⊨`), which normalises the set, splits    --
--     each join on a left side and drops each var-rule         --
--     disjunction entailed by another; polarity-based          --
--     elimination of unknowns (`Elim`), the polarities read    --
--     along the variance table (`polᵛ`, `Lift`), with cycle    --
--     elimination on the type variables of subtyping cycles    --
--     (`equateᵗ`); normal forms again (`canonElim`); `trim`    --
--     (`trimElim`); strengthening (`Strengthened`). The        --
--     unknowns of the image of the caller's variables and      --
--     those of the deferred conditions are neither eliminated  --
--     nor dropped (`fix`, `instᴿ`).                            --
--                                                              --
-- Entailed orderings are decided by `decide≾ᵣ`/`decide≾ₑ` on   --
-- normal forms (`nrmᵣ-≡`, `canonᵣ-≡`), sound by their types;   --
-- no completeness is claimed. Products are compared by         --
-- `prodˢ≾`, which decides the embedding `_⊑ᵖ_`                 --
-- (`prodˢ≾-complete`, `prodˢ≾-exact`), sound for entailment    --
-- (`⊑ᵖ-sound`).                                                --
--                                                              --
-- `runSolver` instantiates `TypeInference.Solver.Solver`       --
-- (`runSolver-sound`, `runSolver-principal`,                   --
-- `runSolver-complete`) and is not stuck on a constraint       --
-- without rigid binders (`runSolver-rigidFree`). `infer` is    --
-- the reference entry point: `scheme` is a principal type      --
-- scheme whose conditions are satisfiable exactly              --
-- when the term is typable (`infer-typed`); a refutation means --
-- that the term is untypable (`infer-untypable`,               --
-- `infer-complete`); a handler-free term is never stuck        --
-- (`infer-handlerFree`); `stuck` carries no claim.             --
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
open import Function.Bundles using (_⇔_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.Outcome

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S hiding (_∷_)
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S
  using (Obligs; Satisfiable; _⊨ᴴ_; _⊩ᴼˢ_[_]; ⊩ᴼˢ-≐; _⊩_∣_[_]; _⊨_∣_)
open import TypeInference.OpenSyntax.Language  S

open import TypeInference.Raw.Syntax S using (RawC; HandlerFreeᶜ)
open import TypeInference.Raw.Subst  S using (_[_]ᴿᶜ; [≐]ᴿᶜ)
open import TypeInference.Erase      S using (⌊_⌋ᶜ)
open import TypeInference.Soundness  S using (ctx-substᶜ; ⌊ctxᶜ⌋; ⌊c⌋)

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S
open import TypeInference.Constraints.Properties   S using (⊨-resp-≐ˢ; ⊨-mono; ⊨-∣)

open import TypeInference.Principality      S
open import TypeInference.Solver            S

open import TypeInference.SolverImpl.Deferred  S
  using (Ords; ords; ors; oes; Dfr; dfr; _[_]ᵈ; _⊩ᵈ_[_]; mk⊩ᵒ; ⊩ors; ⊩oes;
         ⊩ᵈ-resp-≐ˢ; ⊩ᵈ-subst; ⊩ᵈ-subst⁻; toOblig; ⊩ᴰ→⊩ᴼˢ; ⊩ᴼˢ→⊩ᴰ)
open import TypeInference.OpenSyntax.Instances S using (wkᵉⁿ-H; _↑ᵉⁿ_)
open import TypeInference.SolverImpl.Resid     S
open import TypeInference.SolverImpl.Closed    S using (closedᴴ; closedᴴ-⊩; closedᴴ-⊆; closedᴴ-fail)
open import TypeInference.SolverImpl.State     S
open import TypeInference.SolverImpl.Solve     S opEnum
open import TypeInference.SolverImpl.Principal S opEnum
open import TypeInference.SolverImpl.RigidFree S opEnum using (solve-rigidFree)
open import TypeInference.SolverImpl.Simplify  S
  using (simplify; simplify-⊩; simplify-⊨; trimElim; entᵣ?; entₑ?)
open import TypeInference.SolverImpl.Eliminate S
  using (Elim; Elimᶠ; Entails; entails; eliminate; _⨾ᴱ_)
open import TypeInference.SolverImpl.Canon     S
  using (canonElim; canonₑ; canonᵣ; canonₑ-≡; canonᵣ-≡)
open import TypeInference.SolverImpl.Vars       S
  using (Vars; _∪ᵛ_; ⊆-refl; ⊆-∪ˡ; ⊆-∪ʳ; fvˢ; Fixes; fixes-id; fixes-⨟)
open import TypeInference.SolverImpl.Strengthen S
  using (Ren; Strengthened; strengthen; ⌜_⌝ʳ; _[_]ᴴ; ⊩ᴴ-ren⁺; fixes-≐; fixes-⊆; fvᴰ;
         fix-⊩ᵈ; fix-⊩ᵈ⁻; conv⁻; inst⁻; keep⁻; princ⁻)

Fixing-[] : ∀ {Θ Ψ} → (σ : Subst Θ Ψ) → Fixing [] σ
Fixing-[] σ = fixing (λ i ()) (λ i i' ())

-- The driver's answer: a scope, a substitution, the residual read back
-- as hypotheses, and the deferred conditions, retried once more

Answer : Scope → Scope → Set
Answer Θ Θ' = Subst Θ Θ' × Hyps Θ' × List (Dfr Θ')

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
...       | just (Q₀ , hq) with closedᴴ Q₀
...         | nothing = refuted
...         | just Q  = solved (Ψ s₂ , θ s₂ , Q , dfs (res s₂))

-- An entry reads back as an obligation

readOut : ∀ {Θ} → Σ[ Θ' ∈ Scope ] Answer Θ Θ'
        → Σ[ Θ' ∈ Scope ] (Subst Θ Θ' × Hyps Θ' × Obligs Θ')
readOut (Θ' , σ , Q , D) = Θ' , σ , Q , map toOblig D

runSolver : ∀ {Θ} → Constraint Θ
          → Outcome (Σ[ Θ' ∈ Scope ] (Subst Θ Θ' × Hyps Θ' × Obligs Θ'))
runSolver C = mapᴼ readOut (runSolverᴰ C)

runSolverᴰ-sound : ∀ {Θ} → (C : Constraint Θ)
                 → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {D : List (Dfr Θ')}
                 → runSolverᴰ C ≡ solved (Θ' , σ , Q , D)
                 → σ ⊨[ Q ∣ map toOblig D ] C
runSolverᴰ-sound C eq with solve init C
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (s' , m , w) with retry s'
...   | nothing = ⊥refuted eq
...   | just (s₁ , m₁) with reexpand s₁
...     | nothing = ⊥refuted eq
...     | just (s₂ , m₂) with toHyps (res s₂)
...       | nothing = ⊥refuted eq
...       | just (Q₀ , hq) with closedᴴ Q₀ in e''
...         | nothing = ⊥refuted eq
...         | just Q₁ with eq
...           | refl = λ δ Q' → λ { (hQ ∷ hR) →
                wit-mono m₂ C (wit-mono m₁ C w) δ Q'
                  (⊩ᴿ-bare (⊩ᴿ-resp-≐ˢ (⨟-idˡ δ) (⊩ᴿ-⨟ (⊩ᴴ-⨟ hQ (closedᴴ-⊩ Q₀ e'')) hq))
                           (⊩ᴼˢ→⊩ᴰ (dfs (res s₂)) hR)) }

runSolver-sound : ∀ {Θ} → (C : Constraint Θ)
                → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {R : Obligs Θ'}
                → runSolver C ≡ solved (Θ' , σ , Q , R)
                → σ ⊨[ Q ∣ R ] C
runSolver-sound C eq with mapᴼ-solved (runSolverᴰ C) eq
... | (Θ' , σ , Q , D) , e , refl = runSolverᴰ-sound C e

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
...       | just (Q₀ , hq) with closedᴴ Q₀ in e''
...         | just _  = ⊥solved eq
...         | nothing =
              closedᴴ-fail Q₀ e''
                (proj₁ fac₂ , toHyps-compl (res s₂) e' (proj₁ fac₂) (proj₂ (proj₂ fac₂)) ∷ [])
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
runSolver-refutes C eq = runSolverᴰ-refutes C (mapᴼ-refuted (runSolverᴰ C) eq)

runSolver-complete : ∀ {Θ} → (C : Constraint Θ)
                   → runSolver C ≡ refuted
                   → ∀ {Θ'} → (σ : Subst Θ Θ') → (Q : Hyps Θ') → (R : Obligs Θ')
                   → Satisfiable Q R
                   → ¬ (σ ⊨[ Q ∣ R ] C)
runSolver-complete C eq σ Q R (δ₀ , h₀) sat =
  runSolver-refutes C eq (σ ⨟ˢ δ₀) (sat δ₀ ∅ᴴ h₀)

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
...       | just (Q₀ , hq) with closedᴴ Q₀
...         | nothing = λ ()
...         | just _  = λ ()

runSolver-rigidFree : ∀ {Θ} → (C : Constraint Θ) → RigidFree C → runSolver C ≢ stuck
runSolver-rigidFree C p eq = runSolverᴰ-rigidFree C p (mapᴼ-stuck (runSolverᴰ C) eq)

runSolverᴰ-principal : ∀ {Θ} → (C : Constraint Θ)
                     → {Θ⁺ : Scope} {σ⁺ : Subst Θ Θ⁺} {Q⁺ : Hyps Θ⁺} {D⁺ : List (Dfr Θ⁺)}
                     → runSolverᴰ C ≡ solved (Θ⁺ , σ⁺ , Q⁺ , D⁺)
                     → ∀ {Θ''} → (σ : Subst Θ Θ'') → (Q : Hyps Θ'') → (R : Obligs Θ'')
                     → σ ⊨[ Q ∣ R ] C
                     → (δ₀ : Subst Θ'' ∅ˢ) → δ₀ ⊨ Q ∣ R
                     → Σ[ δ ∈ Subst Θ⁺ ∅ˢ ]
                       (((σ⁺ ⨟ˢ δ) ≐ˢ (σ ⨟ˢ δ₀)) × (δ ⊨ Q⁺ ∣ map toOblig D⁺))
runSolverᴰ-principal C eq σ Q R sat δ₀ h₀ with solve init C in e
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (s' , m , w) with retry s' in e₁
...   | nothing = ⊥refuted eq
...   | just (s₁ , m₁) with reexpand s₁ in e₂
...     | nothing = ⊥refuted eq
...     | just (s₂ , m₂) with toHyps (res s₂) in e'
...       | nothing = ⊥refuted eq
...       | just (Q₀ , hq) with closedᴴ Q₀ in e''
...         | nothing = ⊥refuted eq
...         | just Q₁ with eq
...           | refl = δ₂ , tri ,
                       closedᴴ-⊆ Q₀ e'' (toHyps-compl (res s₂) e' δ₂ h₂)
                       ∷ ⊩ᴰ→⊩ᴼˢ (dfs (res s₂)) (⊩dfs h₂)
  where
    fac  = solve-principal init C e (σ ⨟ˢ δ₀) (sat δ₀ ∅ᴴ h₀) ⊩ᴿ-empty
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
                    → {Θ⁺ : Scope} {σ⁺ : Subst Θ Θ⁺} {Q⁺ : Hyps Θ⁺} {R⁺ : Obligs Θ⁺}
                    → runSolver C ≡ solved (Θ⁺ , σ⁺ , Q⁺ , R⁺)
                    → ∀ {Θ''} → (σ : Subst Θ Θ'') → (Q : Hyps Θ'') → (R : Obligs Θ'')
                    → σ ⊨[ Q ∣ R ] C
                    → (δ₀ : Subst Θ'' ∅ˢ) → δ₀ ⊨ Q ∣ R
                    → Σ[ δ ∈ Subst Θ⁺ ∅ˢ ]
                      (((σ⁺ ⨟ˢ δ) ≐ˢ (σ ⨟ˢ δ₀)) × (δ ⊨ Q⁺ ∣ R⁺))
runSolver-principal C eq with mapᴼ-solved (runSolverᴰ C) eq
... | (Θ' , σ , Q , D) , e , refl = runSolverᴰ-principal C e

solver : Solver
solver = record
  { solve           = runSolver
  ; solve-sound     = runSolver-sound
  ; solve-refutes   = runSolver-complete
  ; solve-principal = runSolver-principal
  }

-- The entailment test of elimination by equality: an ordering among
-- the hypotheses, or one `decide≾` proves from them

entailsᴴ : Entails
entailsᴴ = entails entᵣ? entₑ?

-- A solution, its residue as the solver returns it, and the residue
-- simplified, which entails the residue and holds at each of its
-- closed instances. The unknowns the simplified residue fixes are then
-- eliminated from it and from the reported type `X` by a substitution
-- `η`: the reported type is `X` along `η` up to convertibility, the
-- reported hypotheses entail the simplified residue along `η`, each
-- closed instance of the simplified residue is one of them, and there
-- the reported type is a subtype of `X`. Normalisation of the grade
-- expressions and `trim` run as the last two elimination steps.
--
-- The report is relative to the caller's variables `w`: `η` fixes the
-- unknowns of their image. It is stated over the scope `Θ̃` of the
-- variables occurring in it or in that image, embedded in the
-- solution's by the renaming `ι`, the caller's variables instantiated
-- by `σ̃`; an instance of `Θ̃` extends along `ι`. The obligations `R`
-- follow: `R̃` along `ι` entails them along `η`, and each closed
-- instance meeting the simplified residue and `R` meets `R̃`.

record Reported {Θ₀ Θ : Scope} (w : Subst Θ₀ Θ) (X : OCType Θ) (C : Constraint Θ) : Set where
  constructor reported
  field
    Θ'     : Scope
    σ      : Subst Θ Θ'
    Q      : Hyps Θ'
    R      : Obligs Θ'
    Q̂      : Hyps Θ'
    Θ̃      : Scope
    ι      : Ren Θ̃ Θ'
    σ̃      : Subst Θ₀ Θ̃
    X̃      : OCType Θ̃
    Q̃      : Hyps Θ̃
    R̃      : Obligs Θ̃
    η      : Subst Θ' Θ'
    sol    : runSolver C ≡ solved (Θ' , σ , Q , R)
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
    ext-ι  : ∀ {Ψ} → (δ : Subst Θ̃ Ψ) → Σ[ δ' ∈ Subst Θ' Ψ ] (⌜ ι ⌝ʳ ⨟ˢ δ' ≐ˢ δ)

-- An entry with its grade expressions in canonical form means the same

canonᵈ : ∀ {Θ} → Dfr Θ → Dfr Θ
canonᵈ (dfr l k o) = dfr l k (ords (map (mapᵖ canonᵣ) (ors o)) (map (mapᵖ canonₑ) (oes o)))

canonᵈ-⊩ : ∀ {Θ Ξ} {Q : Hyps Ξ} {δ : Subst Θ Ξ} → (E : Dfr Θ)
         → Q ⊩ᵈ E [ δ ] → Q ⊩ᵈ canonᵈ E [ δ ]
canonᵈ-⊩ {δ = δ} (dfr l k o) h = mk⊩ᵒ r e
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

canonᵈ-⊩⁻ : ∀ {Θ Ξ} {Q : Hyps Ξ} {δ : Subst Θ Ξ} → (E : Dfr Θ)
          → Q ⊩ᵈ canonᵈ E [ δ ] → Q ⊩ᵈ E [ δ ]
canonᵈ-⊩⁻ {δ = δ} (dfr l k o) h =
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

-- The report of what `runSolverᴰ` returns. The variables of the deferred
-- conditions are frozen for elimination and kept by the strengthening:
-- the conditions are read over the report's scope along the
-- strengthening's retraction, in canonical form.

reportOutcome : ∀ {Θ₀ Θ} → (w : Subst Θ₀ Θ) → (X : OCType Θ) → (C : Constraint Θ)
              → (s : Outcome (Σ[ Θ' ∈ Scope ] Answer Θ Θ')) → runSolverᴰ C ≡ s
              → Outcome (Reported w X C)
reportOutcome w X C refuted                    e = refuted
reportOutcome w X C stuck                      e = stuck
reportOutcome w X C (solved (Θ' , σ , Q , D)) e =
  solved (reportElim (eliminate entailsᴴ F (X [ σ ]ᶜ) (simplify Q)))
  where
    open Strengthened

    F : Vars Θ'
    F = fvˢ (w ⨟ˢ σ) ∪ᵛ fvᴰ D

    -- The report from an elimination and the strengthening of its result

    reportWith : (el : Elim (X [ σ ]ᶜ) (simplify Q)) → Fixes F (Elim.η el)
               → Strengthened (w ⨟ˢ σ) (Elim.Ĉ el) (Elim.Q̂ el) (fvᴰ D) → Reported w X C
    reportWith el fx sr =
      reported Θ' σ Q (map toOblig D) (simplify Q) (Θ⁻ sr) (ι sr) (τ⁻ sr) (X⁻ sr) (Q⁻ sr)
             (map toOblig D̃) (Elim.η el)
             (cong (mapᴼ readOut) e) (simplify-⊨ Q) (simplify-⊩ Q)
             (fixes-≐ fx (w ⨟ˢ σ) (⊆-∪ˡ (fvˢ (w ⨟ˢ σ)) (fvᴰ D) ⊆-refl)) (τ-ι sr)
             (conv⁻ el sr) (inst⁻ el sr) instᴿ' (keep⁻ el sr) to-R̃'
             (princ⁻ el sr) (ext-ι sr)
      where
        fxᴰ : Fixes (fvᴰ D) (Elim.η el)
        fxᴰ = fixes-⊆ (⊆-∪ʳ (fvˢ (w ⨟ˢ σ)) (fvᴰ D) ⊆-refl) fx

        read : Dfr Θ' → Dfr (Θ⁻ sr)
        read E = canonᵈ (E [ π sr ]ᵈ)

        D̃ : List (Dfr (Θ⁻ sr))
        D̃ = map read D

        -- read back along `ι`, an entry is itself
        back : ∀ {Ξ} {Q' : Hyps Ξ} {δ : Subst Θ' Ξ}
             → ∀ {E} → E ∈ D → Q' ⊩ᵈ read E [ ⌜ ι sr ⌝ʳ ⨟ˢ δ ] → Q' ⊩ᵈ E [ δ ]
        back {δ = δ} {E} m h =
          fix-⊩ᵈ⁻ (π-fix sr) ⊆-refl m
            (⊩ᵈ-resp-≐ˢ E (≐ˢ-sym (⨟-assoc (π sr) ⌜ ι sr ⌝ʳ δ))
              (⊩ᵈ-subst E (canonᵈ-⊩⁻ (E [ π sr ]ᵈ) h)))

        fwd : ∀ {Ξ} {Q' : Hyps Ξ} {δ : Subst Θ' Ξ}
            → ∀ {E} → E ∈ D → Q' ⊩ᵈ E [ δ ] → Q' ⊩ᵈ read E [ ⌜ ι sr ⌝ʳ ⨟ˢ δ ]
        fwd {δ = δ} {E} m h =
          canonᵈ-⊩ (E [ π sr ]ᵈ)
            (⊩ᵈ-subst⁻ E (⊩ᵈ-resp-≐ˢ E (⨟-assoc (π sr) ⌜ ι sr ⌝ʳ δ) (fix-⊩ᵈ (π-fix sr) ⊆-refl m h)))

        instᴿ' : ∀ {Ξ} → (δ : Subst Θ' Ξ) → (Q' : Hyps Ξ)
               → Q' ⊩ᴼˢ map toOblig D̃ [ ⌜ ι sr ⌝ʳ ⨟ˢ δ ] → Q' ⊩ᴼˢ map toOblig D [ Elim.η el ⨟ˢ δ ]
        instᴿ' δ Q' h =
          ⊩ᴰ→⊩ᴼˢ {Q = Q'} {δ = Elim.η el ⨟ˢ δ} D
            (λ {E} m → fix-⊩ᵈ {Q = Q'} {ρ = Elim.η el} {δ = δ} fxᴰ {D = D} ⊆-refl m
                         (back {Q' = Q'} {δ = δ} m
                           (⊩ᴼˢ→⊩ᴰ {Q = Q'} {δ = ⌜ ι sr ⌝ʳ ⨟ˢ δ} D̃ h (∈-map⁺ read m))))

        to-R̃' : (δ : Subst Θ' ∅ˢ) → δ ⊨ simplify Q ∣ map toOblig D
              → ∅ᴴ ⊩ᴼˢ map toOblig D̃ [ ⌜ ι sr ⌝ʳ ⨟ˢ δ ]
        to-R̃' δ h =
          ⊩ᴰ→⊩ᴼˢ {Q = ∅ᴴ} {δ = ⌜ ι sr ⌝ʳ ⨟ˢ δ} D̃
            (∈-map-elim read {P = λ E → ∅ᴴ ⊩ᵈ E [ ⌜ ι sr ⌝ʳ ⨟ˢ δ ]}
              (λ m₀ → fwd {Q' = ∅ᴴ} {δ = δ} m₀
                        (⊩ᴼˢ→⊩ᴰ {Q = ∅ᴴ} {δ = δ} D (All.tail h) m₀)))

    -- The report from an elimination fixing `F`, and its strengthening

    reportStr : (el : Elim (X [ σ ]ᶜ) (simplify Q)) → Fixes F (Elim.η el) → Reported w X C
    reportStr el fx = reportWith el fx (strengthen (w ⨟ˢ σ) (Elim.Ĉ el) (Elim.Q̂ el) (fvᴰ D))

    -- The report from the elimination, followed by normal forms and `trim`

    reportElim : Elimᶠ F (X [ σ ]ᶜ) (simplify Q) → Reported w X C
    reportElim el₀ =
      reportStr (proj₁ el₀ ⨾ᴱ canonElim _ _ ⨾ᴱ trimElim _ _)
                (fixes-⨟ (fixes-⨟ (proj₂ el₀) fixes-id) fixes-id)

report : ∀ {Θ₀ Θ} → (w : Subst Θ₀ Θ) → (X : OCType Θ) → (C : Constraint Θ)
       → Outcome (Reported w X C)
report w X C = reportOutcome w X C (runSolverᴰ C) refl

-- A report is refuted only where the solver is

reportOutcome-refuted : ∀ {Θ₀ Θ} {w : Subst Θ₀ Θ} {X : OCType Θ} {C : Constraint Θ}
                      → (s : Outcome (Σ[ Θ' ∈ Scope ] Answer Θ Θ'))
                      → (e : runSolverᴰ C ≡ s)
                      → reportOutcome w X C s e ≡ refuted → runSolver C ≡ refuted
reportOutcome-refuted refuted    e eq = cong (mapᴼ readOut) e
reportOutcome-refuted stuck      e ()
reportOutcome-refuted (solved _) e ()

reportOutcome-stuck : ∀ {Θ₀ Θ} {w : Subst Θ₀ Θ} {X : OCType Θ} {C : Constraint Θ}
                    → (s : Outcome (Σ[ Θ' ∈ Scope ] Answer Θ Θ'))
                    → (e : runSolverᴰ C ≡ s)
                    → reportOutcome w X C s e ≡ stuck → runSolver C ≡ stuck
reportOutcome-stuck refuted    e ()
reportOutcome-stuck stuck      e eq = cong (mapᴼ readOut) e
reportOutcome-stuck (solved _) e ()

------------------------------------------------------------------------
-- The reference entry point
--
-- A report on the constraint of `M` in `Γ`, relative to the program's
-- variables, is a principal type scheme of `M` in `Γ`: its derivation is the
-- principal one instantiated along `η` and retracted along `ι`, and a
-- typing factors through the principal one and then through the report
-- at each closed instance.

scheme : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
       → Reported wk₊ (X̂ Θ ‼ t̂ Θ) C[ Γ , M ] → PrincipalScheme Γ M
scheme {Θ} Γ M r = mkPrincipalScheme Θ̃ σ̃ Q̃ R̃ X̃ inst' fac
  where
    open Reported r

    X : OCType (Θ +ty +e)
    X = X̂ Θ ‼ t̂ Θ

    p : PrincipalSolution Γ M
    p = principalSolution solver Γ M sol

    -- a retraction of `ι`

    π : Subst Θ' Θ̃
    π = proj₁ (ext-ι idˢ)

    πι : ⌜ ι ⌝ʳ ⨟ˢ π ≐ˢ idˢ
    πι = proj₂ (ext-ι idˢ)

    -- the reported hypotheses entail the residue along `η` and `π`

    hQ : Q̃ ⊩ᴴ Q [ η ⨟ˢ π ]
    hQ = ⊩ᴴ-⨟ (⊩ᴴ-ren⁺ ι (⊩ᴴ-≐ (≐ˢ-sym πι) ⊩ᴴ-refl)) (⊩ᴴ-⨟ inst to-Q)

    -- and the reported obligations the solver's, at each instance

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

    inst' : ∀ {Θ''} → (δ : Subst Θ̃ Θ'') → (Q' : Hyps Θ'') → Q' ⊩ Q̃ ∣ R̃ [ δ ]
          → Σ[ D ∈ (Q' ∣ Γ [ σ̃ ⨟ˢ δ ]ᶜᵗˣ ⊢C⦂ X̃ [ δ ]ᶜ) ] (⌊ D ⌋ᶜ ≡ M [ σ̃ ⨟ˢ δ ]ᴿᶜ)
    inst' δ Q' (h ∷ hs) =
      subC (ctx-substᶜ ceq D) (≡̂ᶜ-<:̂ (ty δ)) , trans (⌊ctxᶜ⌋ ceq D) (trans e meq)
      where
        τ = η ⨟ˢ π ⨟ˢ δ
        i = PrincipalSolution.instantiate p τ Q' (⊩ᴴ-⨟ h hQ ∷ hR δ Q' hs)
        D = proj₁ i
        e = proj₂ i

        ceq : Γ₊ Γ [ σ ⨟ˢ τ ]ᶜᵗˣ ≡ Γ [ σ̃ ⨟ˢ δ ]ᶜᵗˣ
        ceq = trans (Γ₊-[] Γ (σ ⨟ˢ τ)) ([≐]ᶜᵗˣ (ctx δ) Γ)

        meq : M₊ M [ σ ⨟ˢ τ ]ᴿᶜ ≡ M [ σ̃ ⨟ˢ δ ]ᴿᶜ
        meq = trans (M₊-[] M (σ ⨟ˢ τ)) ([≐]ᴿᶜ (ctx δ) M)

    fac : ∀ {Θ''} → (σ₀ : Subst Θ Θ'') → (Q₀ : Hyps Θ'') → {C₀ : OCType Θ''}
        → (D₀ : Q₀ ∣ Γ [ σ₀ ]ᶜᵗˣ ⊢C⦂ C₀) → ⌊ D₀ ⌋ᶜ ≡ M [ σ₀ ]ᴿᶜ
        → (δ₀ : Subst Θ'' ∅ˢ) → δ₀ ⊨ Q₀ ∣ []
        → Σ[ δ ∈ Subst Θ̃ ∅ˢ ]
            ((σ̃ ⨟ˢ δ ≐ˢ σ₀ ⨟ˢ δ₀) × (δ ⊨ Q̃ ∣ R̃) × (∅ᴴ ∣ X̃ [ δ ]ᶜ <:̂ᶜ C₀ [ δ₀ ]ᶜ))
    fac σ₀ Q₀ {A₀ ‼ ε₀} D₀ e₀ δ₀ h₀ =
      ⌜ ι ⌝ʳ ⨟ˢ δ' , agree , to-Q̃ δ' hQ̂ ∷ to-R̃ δ' (hQ̂ ∷ All.tail hq) ,
      <:̂ᶜ-trans (princ δ' hQ̂) below
      where
        pi   = principal-inst p σ₀ Q₀ D₀ e₀ δ₀ h₀
        δ'   = proj₁ pi
        ceq₁ = proj₁ (proj₂ pi)
        aeq  = proj₁ (proj₂ (proj₂ pi))
        le   = proj₁ (proj₂ (proj₂ (proj₂ pi)))
        hq   = proj₂ (proj₂ (proj₂ (proj₂ pi)))

        hQ̂ : ∅ᴴ ⊩ᴴ Q̂ [ δ' ]
        hQ̂ = to-Q̂ δ' (All.head hq)

        agree : σ̃ ⨟ˢ (⌜ ι ⌝ʳ ⨟ˢ δ') ≐ˢ σ₀ ⨟ˢ δ₀
        agree =
          ≐ˢ-trans (≐ˢ-sym (⨟-assoc σ̃ ⌜ ι ⌝ʳ δ'))
          (≐ˢ-trans (⨟-congˡ σ̃-ι δ') ceq₁)

        below : ∅ᴴ ∣ X [ σ ]ᶜ [ δ' ]ᶜ <:̂ᶜ (A₀ ‼ ε₀) [ δ₀ ]ᶜ
        below =
          subst (λ A → ∅ᴴ ∣ A ‼ t̂ Θ [ σ ]ᵉ [ δ' ]ᵉ <:̂ᶜ A₀ [ δ₀ ]ᵛ ‼ ε₀ [ δ₀ ]ᵉ)
                (sym aeq) (<:̂ᵛ-refl (A₀ [ δ₀ ]ᵛ) ‼ₛ le)

-- Inference: a principal type scheme, a refutation, or `stuck`. It is
-- stuck only where a handler clause's scope closes with a local unknown
-- to which `Localise` assigns no value; `SolverImpl.Localise` lists the
-- known cases.

inferred : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
         → Outcome (Reported wk₊ (X̂ Θ ‼ t̂ Θ) C[ Γ , M ]) → Inference Γ M
inferred Γ M (solved r) = typed (scheme Γ M r)
inferred Γ M refuted    = untypable
inferred Γ M stuck      = stuck

infer : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n) → Inference Γ M
infer {Θ} Γ M = inferred Γ M (report wk₊ (X̂ Θ ‼ t̂ Θ) C[ Γ , M ])

-- An untypable verdict refutes every typing under satisfiable
-- hypotheses

infer-untypable : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                → infer Γ M ≡ untypable → ¬ Typable Γ M
infer-untypable {Θ} Γ M eq (typable Θ₀ σ₀ Q₀ (A₀ ‼ ε₀) D₀ e₀ sQ) =
  runSolver-complete C[ Γ , M ]
    (reportOutcome-refuted (runSolverᴰ C[ Γ , M ]) refl (untyped (report wk₊ (X̂ Θ ‼ t̂ Θ) C[ Γ , M ]) eq))
    (σ₀ ,ᵗ A₀ ,ᵉ ε₀) Q₀ [] sQ (⊨-∣ C[ Γ , M ] (typing-sat σ₀ D₀ e₀))
  where
    untyped : (x : Outcome (Reported wk₊ (X̂ Θ ‼ t̂ Θ) C[ Γ , M ]))
            → inferred Γ M x ≡ untypable → x ≡ refuted
    untyped refuted    eq = refl
    untyped stuck      ()
    untyped (solved _) ()

------------------------------------------------------------------------
-- The end-to-end theorem
--
-- A typed verdict is a principal type scheme, and `M` is typable exactly
-- when its conditions are satisfiable; an untypable verdict means `M`
-- is not typable. Inference is therefore complete up to `stuck`: a
-- typable `M` is never declared untypable. A handler-free `M` is never
-- stuck. A typed verdict with no hypotheses and no obligations is
-- typable outright.

infer-typed : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n) → {p : PrincipalScheme Γ M}
            → infer Γ M ≡ typed p
            → Typable Γ M ⇔ Satisfiable (PrincipalScheme.Q̃ p) (PrincipalScheme.R̃ p)
infer-typed Γ M {p} _ = typable-⇔ p

infer-unconditional : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n) → {p : PrincipalScheme Γ M}
                     → infer Γ M ≡ typed p
                     → PrincipalScheme.Q̃ p ≡ ∅ᴴ → PrincipalScheme.R̃ p ≡ [] → Typable Γ M
infer-unconditional Γ M {p} _ = typable-unconditional p

infer-complete : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
               → Typable Γ M → infer Γ M ≢ untypable
infer-complete Γ M t eq = infer-untypable Γ M eq t

infer-handlerFree : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                  → HandlerFreeᶜ M → infer Γ M ≢ stuck
infer-handlerFree {Θ} Γ M h eq =
  runSolver-rigidFree C[ Γ , M ] (C[]-rigidFree Γ M h)
    (reportOutcome-stuck (runSolverᴰ C[ Γ , M ]) refl (unstuck (report wk₊ (X̂ Θ ‼ t̂ Θ) C[ Γ , M ]) eq))
  where
    unstuck : (x : Outcome (Reported wk₊ (X̂ Θ ‼ t̂ Θ) C[ Γ , M ]))
            → inferred Γ M x ≡ stuck → x ≡ stuck
    unstuck refuted    ()
    unstuck stuck      eq = refl
    unstuck (solved _) ()
