------------------------------------------------------------------
-- Parametricity certificates for grounded derivations            --
--                                                                --
-- The interpretation `⟦_⟧ᵛᵗ`/`⟦_⟧ᶜᵗ` of                          --
-- `DenotationalSemantics.Interpretation.Terms` is defined only on --
-- *parametric* terms. `Inference.Infer` produces its derivation   --
-- through `groundC`, so the missing link between inference and    --
-- the denotational semantics is                                   --
--                                                                --
--     Paramᵛ (groundV θ h D)   and   Paramᶜ (groundC θ h D).      --
--                                                                --
-- Every case but `handle` is inert: `Paramᵛ`/`Paramᶜ` is `⊤` or a --
-- product, so the certificate is assembled from the sub-          --
-- derivations', modulo the transports `groundV`/`groundC` insert  --
-- (`perform`'s ground-type round-trips, `ground-clause`'s         --
-- `subst₂`), each of which is stripped by `J`.                    --
--                                                                --
-- `handle` carries `EffUniformʰ`: the clause denotations have to  --
-- be natural in the residual effect grade. A grounded handler's   --
-- clause family is one mirrored derivation `Ĥ op` at scope        --
-- `Θ +e`, read at the groundings `θ ,ᵍᵉ ε''`, so its uniformity   --
-- is a *grade-naturality* statement about `groundC`. That         --
-- statement is `GroundUniform.ground-uniform`, an explicit        --
-- hypothesis of this module (not a postulate); see the module     --
-- note below it for what proving it would take.                   --
------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import Inference.Scopes

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module Inference.ParamGround
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types    S
open import Syntax.Contexts S
open import Syntax.Language S

open import Inference.Open.Grades           S
open import Inference.Open.Types            S
open import Inference.Open.Contexts         S
open import Inference.Open.Hyps             S
open import Inference.Open.Language         S
open import Inference.Open.GroundingTheorem S

-- The grounding interpretations would shadow the denotational ones; only the
-- latter are needed unqualified inside `EffUniformʰ`, so the former are renamed.

open import Inference.Open.Grounding S
  renaming (⟦_⟧ᵛ to ⟦_⟧ᵒᵛ; ⟦_⟧ᶜ to ⟦_⟧ᵒᶜ; ⟦_⟧ᶜᵗˣ to ⟦_⟧ᵒᶜᵗˣ)

open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE

--------------------------------------------------------------
-- Transport lemmas                                          --
--                                                           --
-- `Paramᵛ`/`Paramᶜ` is invariant under the type- and         --
-- context-equality transports `groundV`/`groundC` insert.    --
--------------------------------------------------------------

-- `perform`'s parameter: the value's type is retyped

ty-Paramᵛ : ∀ {Γ A A'} → (e : A ≡ A') → (V : Γ ⊢V⦂ A) → Paramᵛ V
          → Paramᵛ (subst (λ A₀ → Γ ⊢V⦂ A₀) e V)
ty-Paramᵛ refl V p = p

-- `perform`'s continuation: the last context entry is retyped

∷-Paramᶜ : ∀ {Γ A A' C} → (e : A ≡ A') → (M : Γ ∷ A ⊢C⦂ C) → Paramᶜ M
         → Paramᶜ (subst (λ A₀ → Γ ∷ A₀ ⊢C⦂ C) e M)
∷-Paramᶜ refl M p = p

-- `ground-clause`: the whole judgement is retyped

subst₂-Paramᶜ : ∀ {Γ Γ' C C'} → (e₁ : Γ ≡ Γ') → (e₂ : C ≡ C')
              → (M : Γ ⊢C⦂ C) → Paramᶜ M → Paramᶜ (subst₂ _⊢C⦂_ e₁ e₂ M)
subst₂-Paramᶜ refl refl M p = p

--------------------------------------------------------------
-- Monotonicity of grounding in the residual grade           --
--                                                           --
-- The first building block of a proof of `ground-uniform`:  --
-- every grade expression of the extended scope is monotone  --
-- in the grade the rigid variable is sent to.               --
--------------------------------------------------------------

ground-mono-e : ∀ {Θ} {θ : Grounding Θ} {ε₁ ε₂ : E} → ε₁ ≾ₑ ε₂
              → (ε : EExp (Θ +e))
              → ⟦ ε ⟧ᵉ (θ ,ᵍᵉ ε₁) ≾ₑ ⟦ ε ⟧ᵉ (θ ,ᵍᵉ ε₂)
ground-mono-e q (evar zero)    = q
ground-mono-e q (evar (suc i)) = ≾ₑ-refl
ground-mono-e q (econst ε)     = ≾ₑ-refl
ground-mono-e q (ε ·̂ₑ ε')      =
  ≾ₑ-trans (·ₑ-monoˡ-≾ₑ (ground-mono-e q ε)) (·ₑ-monoʳ-≾ₑ (ground-mono-e q ε'))

ground-mono-r : ∀ {Θ} {θ : Grounding Θ} {ε₁ ε₂ : E} → ε₁ ≾ₑ ε₂
              → (ρ : RExp (Θ +e))
              → ⟦ ρ ⟧ʳ (θ ,ᵍᵉ ε₁) ≾ᵣ ⟦ ρ ⟧ʳ (θ ,ᵍᵉ ε₂)
ground-mono-r q (rvar i)   = ≾ᵣ-refl
ground-mono-r q (rconst ρ) = ≾ᵣ-refl
ground-mono-r q (ρ ·̂ᵣ ρ')  =
  ≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (ground-mono-r q ρ)) (·ᵣ-monoʳ-≾ᵣ (ground-mono-r q ρ'))
ground-mono-r q ∣ ε ∣̂ᵉ     = map-monotoneᵉ (ground-mono-e q ε)

-- At the grade a mirrored clause is typed at, monotonicity *is* the coercion
-- `EffUniformʰ` names on its right-hand side.

ground-mono-clause : ∀ {Θ} {θ : Grounding Θ} {ε₁ ε₂ : E} → (q : ε₁ ≾ₑ ε₂)
                   → (op : Op)
                   → ground-mono-e {θ = θ} q (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ}))
                   ≡ ·ₑ-monoʳ-≾ₑ q
ground-mono-clause q op = ≾ₑ-irrelevant _ _

--------------------------------------------------------------
-- The grade-naturality hypothesis                           --
--------------------------------------------------------------

-- A grounded handler's clause at residual grade `ε''` is `ground-clause θ h op
-- ε'' (Ĥ op)`: one and the same mirrored derivation `Ĥ op`, typed at scope
-- `Θ +e` against the rigid grade `evar newᵉ`, read at the grounding `θ ,ᵍᵉ ε''`.
-- `ground-uniform` says that this syntactically uniform family is semantically
-- uniform, i.e. that it satisfies `EffUniformʰ`.
--
-- The certificate family `pH` is an argument rather than the one this module
-- builds, exactly as in `EffUniformʰ` itself; that also keeps the hypothesis
-- independent of the mutual block below.

record GroundUniform : Set where
  field
    ground-uniform :
      ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {B : OVType Θ}
      → (θ : Grounding Θ) → (h : θ ⊨ᴴ Q)
      → (Ĥ : (op : Op)
           → wkᵉ-H Q ∣ wkᵉ-ctx Γ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                         ∷ [ rconst (mapᵉ (op-grade op)) ]
                             (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ}))
             ⊢C⦂ wkᵉ-v B ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ})))
      → (pH : ∀ op ε'' → Paramᶜ (ground-clause θ h op ε'' (Ĥ op)))
      → EffUniformʰ {⟦ Γ ⟧ᵒᶜᵗˣ θ} {⟦ B ⟧ᵒᵛ θ}
                    (λ op ε'' → ground-clause θ h op ε'' (Ĥ op)) pH

open GroundUniform public

-- What proving `ground-uniform` takes. The strengthened induction hypothesis is
-- a naturality statement for `groundC` itself: a family of morphisms
-- `⟦ ⟦ A ⟧ᵒᵛ (θ ,ᵍᵉ ε₁) ⟧ᵛ →ᵐ ⟦ ⟦ A ⟧ᵒᵛ (θ ,ᵍᵉ ε₂) ⟧ᵛ` (and likewise on
-- contexts), along which the two grounded denotations commute. `ground-mono-e`/
-- `ground-mono-r` supply the coercion grades; the variance discipline such a
-- family needs is
--
--   covariant:      `A |×| B`, `A ‼ ε` (via `T-≤`), `Γ ∷ A`, `Γ ⟨ ρ ⟩`
--                   (`⟨⟩-≤` is covariant in the grade)
--   contravariant:  the domain of `A ⇒ C`, the grade of `[ ρ ] A`
--                   (`[]-≤` is contravariant in the grade)
--
-- so the family exists only for types in which `evar newᵉ` occurs covariantly.
-- The clause's own context and result type qualify, but `lam` (a newᵉ-mentioning
-- domain) and `box` (a newᵉ-mentioning grade) can put it negatively, where no
-- such morphism exists and a relational argument is required — structure the
-- abstract model interface does not provide.

--------------------------------------------------------------
-- The theorem                                               --
--------------------------------------------------------------

module _ (GU : GroundUniform) where

  mutual

    Param-groundV : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
                  → (θ : Grounding Θ) → (h : θ ⊨ᴴ Q) → (D : Q ∣ Γ ⊢V⦂ A)
                  → Paramᵛ (groundV θ h D)

    -- the `with` mirrors `groundV`'s, so that the grounded variable's
    -- membership witness is exposed and `Paramᵛ` reduces to `⊤`

    Param-groundV θ h (var x ok) with ground-var θ h x ok
    ... | f , y = tt
    Param-groundV θ h (const B c) = tt
    Param-groundV θ h ⋆           = tt
    Param-groundV θ h true        = tt
    Param-groundV θ h false       = tt
    Param-groundV θ h ⦉ V , W ⦊    = Param-groundV θ h V , Param-groundV θ h W
    Param-groundV θ h (lam M)     = Param-groundC θ h M

    Param-groundC : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
                  → (θ : Grounding Θ) → (h : θ ⊨ᴴ Q) → (D : Q ∣ Γ ⊢C⦂ C)
                  → Paramᶜ (groundC θ h D)

    Param-groundC θ h (return V) = Param-groundV θ h V
    Param-groundC θ h (M ⨟ N)    = Param-groundC θ h M , Param-groundC θ h N
    Param-groundC θ h (V · W)    = Param-groundV θ h V , Param-groundV θ h W
    Param-groundC θ h (match V `in M) =
      Param-groundV θ h V , Param-groundC θ h M
    Param-groundC θ h (absurd V) = Param-groundV θ h V
    Param-groundC θ h (if V `then M `else N) =
      Param-groundV θ h V , Param-groundC θ h M , Param-groundC θ h N

    -- the two ground-type round-trips are stripped by the transport lemmas

    Param-groundC θ h (perform op V M) =
        ty-Paramᵛ (⌜⌝ᵍ-ground (param op)) (groundV θ h V) (Param-groundV θ h V)
      , ∷-Paramᶜ (⌜⌝ᵍ-ground (arity op)) (groundC θ h M) (Param-groundC θ h M)

    Param-groundC θ h (delay τ M) = Param-groundC θ h M

    -- the only case with content: the clause family's uniformity is the
    -- grade-naturality hypothesis, at this handler's mirrored clauses

    Param-groundC θ h (handle M `with Ĥ `in N) =
        Param-groundC θ h M
      , Param-groundC θ h N
      , (λ op ε'' → Param-ground-clause θ h op ε'' (Ĥ op))
      , ground-uniform GU θ h Ĥ (λ op ε'' → Param-ground-clause θ h op ε'' (Ĥ op))

    Param-groundC θ h (unbox x ok N) with ground-unbox θ h x ok
    ... | le , y = Param-groundC θ h N
    Param-groundC θ h (box ρ V N) = Param-groundV θ h V , Param-groundC θ h N
    Param-groundC θ h (coerce le M) = Param-groundC θ h M

    -- one clause at one residual grade: the certificate of the clause read at
    -- `θ ,ᵍᵉ ε''`, transported along `ground-clause`'s `subst₂`

    Param-ground-clause :
      ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {B : OVType Θ}
      → (θ : Grounding Θ) → (h : θ ⊨ᴴ Q)
      → (op : Op) → (ε'' : E)
      → (X : wkᵉ-H Q ∣ wkᵉ-ctx Γ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                         ∷ [ rconst (mapᵉ (op-grade op)) ]
                             (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ}))
             ⊢C⦂ wkᵉ-v B ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ})))
      → Paramᶜ (ground-clause θ h op ε'' X)

    Param-ground-clause {Γ = Γ} {B} θ h op ε'' X =
      subst₂-Paramᶜ
        (cong₂ _∷_
               (cong₂ _∷_ (cong (_⟨ ⊤ᵣ ⟩) (ground-wkᵉ-ctx Γ)) (⌜⌝ᵍ-ground (param op)))
               (cong₂ (λ A₀ B₀ → [ mapᵉ (op-grade op) ] (A₀ ⇒ B₀ ‼ ε''))
                      (⌜⌝ᵍ-ground (arity op))
                      (ground-wkᵉ-v B)))
        (cong (_‼ (op-grade op ·ₑ ε'')) (ground-wkᵉ-v B))
        (groundC (θ ,ᵍᵉ ε'') (⊨ᴴ-wkᵉ-ground h) X)
        (Param-groundC (θ ,ᵍᵉ ε'') (⊨ᴴ-wkᵉ-ground h) X)
