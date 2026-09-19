------------------------------------------------------------------
-- Principal types                                              --
--                                                              --
-- Generation is run at `Θ` extended by a fresh type variable   --
-- and a fresh effect variable, standing for the result type    --
-- and the result effect; solving the resulting constraint      --
-- yields a principal solution together with its residual       --
-- constraint.                                                  --
--                                                              --
-- `Principal Γ M` packages the two halves:                     --
--                                                              --
-- `instantiate` — every instance of the residual hypotheses    --
-- gives a typing of `M`, by `solve-sound`, `⊨-mono` and        --
-- `soundC`; `mgu` — every typing of `M` factors through the    --
-- principal substitution and residue, by `completeC` and       --
-- `solve-principal`.                                           --
--                                                              --
-- `mgu` takes the derivation's erasure equation as a           --
-- hypothesis: the constraint that was solved is `genC _ M _`,  --
-- while completeness produces a solution of `genC _ ⌊ D ⌋ᶜ _`. --
--                                                              --
-- Principal types carrying a constraint set, after Pretnar     --
-- (LMCS 2014); "residual constraint" is OutsideIn(X)'s term    --
-- (Vytiniotis, Peyton Jones, Schrijvers, Sulzmann, JFP 2011).  --
-- The context is fixed, so what is principal is the type —     --
-- Damas and Milner's principal type scheme (1982) — not a      --
-- principal typing in Wells's sense (2002).                    --
------------------------------------------------------------------

open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Principality (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.Open.Grades   S
open import TypeInference.Open.Types    S
open import TypeInference.Open.Contexts S
open import TypeInference.Open.Subst    S
open import TypeInference.Open.Hyps     S
open import TypeInference.Open.Language S

open import TypeInference.Raw.Syntax S
open import TypeInference.Erase      S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S
open import TypeInference.Constraints.Properties   S

open import TypeInference.Generate     S
open import TypeInference.Soundness    S
open import TypeInference.Completeness S
open import TypeInference.Solver       S

-- `Θ +ty +e` binds the unknown result type and effect; the context is
-- weakened into that scope.

X̂ : (Θ : Scope) → OVType (Θ +ty +e)
X̂ Θ = tvar (newᵗ {Θ})

t̂ : (Θ : Scope) → EExp (Θ +ty +e)
t̂ Θ = evar (newᵉ {Θ +ty})

Γ₊ : ∀ {Θ n} → OCtx Θ n → OCtx (Θ +ty +e) n
Γ₊ Γ = wkᵉ-ctx (wkᵗ-ctx Γ)

C[_,_] : ∀ {Θ n} → OCtx Θ n → RawC n → Constraint (Θ +ty +e)
C[_,_] {Θ} Γ M = genC (Γ₊ Γ) M (X̂ Θ ‼ t̂ Θ)

record Principal {Θ : Scope} {n : ℕ} (Γ : OCtx Θ n) (M : RawC n) : Set where
  constructor mkPrincipal
  field

    -- the principal solution-with-residue

    Θ⁺ : Scope
    σ⁺ : Subst (Θ +ty +e) Θ⁺
    Q⁺ : Hyps Θ⁺

    -- the principal derivation itself (its type is `X̂ Θ [ σ⁺ ]ᵛ`, its
    -- effect `t̂ Θ [ σ⁺ ]ᵉ`)

    D⁺   : Q⁺ ∣ Γ₊ Γ [ σ⁺ ]ᶜᵗˣ ⊢C⦂ (X̂ Θ [ σ⁺ ]ᵛ) ‼ (t̂ Θ [ σ⁺ ]ᵉ)
    ⌊D⁺⌋ : ⌊ D⁺ ⌋ᶜ ≡ M

    -- every instance of the residue types `M`

    instantiate : ∀ {Θ''} → (δ : Subst Θ⁺ Θ'') → (Q : Hyps Θ'')
                → Q ⊩ᴴ Q⁺ [ δ ]
                -------------------------------------------------------
                → Σ[ D ∈ (Q ∣ Γ₊ Γ [ σ⁺ ⨟ˢ δ ]ᶜᵗˣ
                            ⊢C⦂ (X̂ Θ [ σ⁺ ⨟ˢ δ ]ᵛ) ‼ (t̂ Θ [ σ⁺ ⨟ˢ δ ]ᵉ)) ]
                    (⌊ D ⌋ᶜ ≡ M)

    -- every typing of `M` factors through the principal one

    mgu : ∀ {Θ''} → (σ : Subst (Θ +ty +e) Θ'') → (Q : Hyps Θ'')
        → {A₀ : OVType Θ''} → {ε₀ : EExp Θ''}
        → (D : Q ∣ Γ₊ Γ [ σ ]ᶜᵗˣ ⊢C⦂ A₀ ‼ ε₀)
        → ⌊ D ⌋ᶜ ≡ M
        → A₀ ≡ X̂ Θ [ σ ]ᵛ
        → Q ⊩ ε₀ ≾̂ₑ t̂ Θ [ σ ]ᵉ
        ----------------------------------------------------
        → Σ[ δ ∈ Subst Θ⁺ Θ'' ]
            (((σ⁺ ⨟ˢ δ) ≐ˢ σ) × (Q ⊩ᴴ Q⁺ [ δ ]))

-- Not re-exported: the field names (`mgu`, `instantiate`, …) are generic

open Principal

principal : (sv : Solver) → ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC n)
          → {Θ' : Scope} {σ : Subst (Θ +ty +e) Θ'} {Q : Hyps Θ'}
          → Solver.solve sv C[ Γ , M ] ≡ just (Θ' , σ , Q)
          ------------------------------------------------
          → Principal Γ M

principal sv {Θ} Γ M {Θ'} {σ} {Q} eq = mkPrincipal
  Θ' σ Q
  (proj₁ elab) (proj₂ elab)
  (λ δ Q' h → soundC (Γ₊ Γ) M (X̂ Θ) (t̂ Θ) (⊨-mono h C[ Γ , M ] sat))
  (λ σ' Q' D e aeq le →
     Solver.solve-principal sv C[ Γ , M ] eq σ' Q'
       (subst (λ N → σ' ⊨[ Q' ] genC (Γ₊ Γ) N (X̂ Θ ‼ t̂ Θ)) e
              (completeC (Γ₊ Γ) (X̂ Θ) (t̂ Θ) D refl aeq le)))
  where
    sat  = Solver.solve-sound sv C[ Γ , M ] eq
    elab = soundC (Γ₊ Γ) M (X̂ Θ) (t̂ Θ) sat

-- A typing of `M` at an arbitrary type and effect is an instance of the
-- principal one: the principal type instantiates to it exactly, the
-- principal effect up to the residual entailment.

principal-inst : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC n} → (p : Principal Γ M)
               → ∀ {Θ''} → (σ₀ : Subst Θ Θ'') → (Q : Hyps Θ'')
               → {A₀ : OVType Θ''} → {ε₀ : EExp Θ''}
               → (D : Q ∣ Γ [ σ₀ ]ᶜᵗˣ ⊢C⦂ A₀ ‼ ε₀)
               → ⌊ D ⌋ᶜ ≡ M
               ----------------------------------------------------------
               → Σ[ δ ∈ Subst (Θ⁺ p) Θ'' ]
                   ((X̂ _ [ σ⁺ p ]ᵛ [ δ ]ᵛ ≡ A₀)
                     × (Q ⊩ (t̂ _ [ σ⁺ p ]ᵉ [ δ ]ᵉ) ≾̂ₑ ε₀)
                     × (Q ⊩ᴴ Q⁺ p [ δ ]))

principal-inst {Θ} {Γ = Γ} {M = M} p {Θ''} σ₀ Q {A₀} {ε₀} D e =
  δ , aeq , subst (λ x → Q ⊩ x ≾̂ₑ ε₀) (sym teq) ⊩≾̂ₑ-refl , h
  where
    σ : Subst (Θ +ty +e) Θ''
    σ = σ₀ ,ᵗ A₀ ,ᵉ ε₀

    -- the extension undoes the two weakenings of the context

    ctxeq : Γ₊ Γ [ σ ]ᶜᵗˣ ≡ Γ [ σ₀ ]ᶜᵗˣ
    ctxeq = trans (wk-,ᵉ-ctx (σ₀ ,ᵗ A₀) ε₀ (wkᵗ-ctx Γ)) (wk-,ᵗ-ctx σ₀ A₀ Γ)

    D' : Q ∣ Γ₊ Γ [ σ ]ᶜᵗˣ ⊢C⦂ A₀ ‼ ε₀
    D' = ctx-substᶜ (sym ctxeq) D

    fac = mgu p σ Q D' (trans (⌊ctxᶜ⌋ (sym ctxeq) D) e) refl ⊩≾̂ₑ-refl

    δ = proj₁ fac
    h = proj₂ (proj₂ fac)

    -- the principal type and effect follow the factorisation

    aeq : X̂ Θ [ σ⁺ p ]ᵛ [ δ ]ᵛ ≡ A₀
    aeq = trans ([⨟]ᵛ (X̂ Θ) (σ⁺ p) δ) ([≐]ᵛ (proj₁ (proj₂ fac)) (X̂ Θ))

    teq : t̂ Θ [ σ⁺ p ]ᵉ [ δ ]ᵉ ≡ ε₀
    teq = trans ([⨟]ᵉ (t̂ Θ) (σ⁺ p) δ) ([≐]ᵉ (proj₁ (proj₂ fac)) (t̂ Θ))
