------------------------------------------------------------------
-- Principal types                                              --
--                                                              --
-- Generation is run at `Θ` extended by a fresh type variable   --
-- and a fresh effect variable, standing for the result type    --
-- and the result effect, the term weakened into that scope;    --
-- solving the resulting constraint yields a principal solution --
-- together with its residual constraint.                       --
--                                                              --
-- `Principal Γ M` packages `instantiate` — every instance of   --
-- the residual hypotheses gives a typing of `M` — and `mgu` —  --
-- every typing of `M` factors through the principal            --
-- substitution and residue, its type and effect bounded by the --
-- principal ones. A typing of `M` is a derivation that erases  --
-- to an instance of `M`, its annotations instantiated too.     --
--                                                              --
-- `PrincipalTyping Γ M` is the answer over a scope of its own: --
-- a typing of `M` that every instance of its hypotheses        --
-- instantiates, and through which every typing of `M` factors  --
-- at each closed instance.                                     --
--                                                              --
-- Principal types carrying a constraint set, after Pretnar     --
-- (LMCS 2014); "residual constraint" is OutsideIn(X)'s term    --
-- (Vytiniotis et al., JFP 2011). The context is fixed up to    --
-- its variables, so what is principal is the type — Damas and  --
-- Milner's principal type scheme (1982) — not a principal      --
-- typing in Wells's sense (2002).                              --
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

open import TypeInference.OpenSyntax.Grades   S
open import TypeInference.OpenSyntax.Types    S
open import TypeInference.OpenSyntax.Contexts S
open import TypeInference.OpenSyntax.Subst    S
open import TypeInference.OpenSyntax.Hyps     S
open import TypeInference.OpenSyntax.Language S

open import TypeInference.Raw.Syntax S
open import TypeInference.Raw.Subst  S
open import TypeInference.Erase      S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S
open import TypeInference.Constraints.Properties   S

open import TypeInference.Generate     S
open import TypeInference.Soundness    S
open import TypeInference.Completeness S
open import TypeInference.Solver       S

-- `Θ +ty +e` binds the unknown result type and effect; the context and
-- the term are weakened into that scope.

X̂ : (Θ : Scope) → OVType (Θ +ty +e)
X̂ Θ = tvar (newᵗ {Θ})

t̂ : (Θ : Scope) → EExp (Θ +ty +e)
t̂ Θ = evar (newᵉ {Θ +ty})

wk₊ : ∀ {Θ} → Subst Θ (Θ +ty +e)
wk₊ = wkˢᵗ ⨟ˢ wkˢᵉ

Γ₊ : ∀ {Θ n} → OCtx Θ n → OCtx (Θ +ty +e) n
Γ₊ Γ = wkᵉ-ctx (wkᵗ-ctx Γ)

M₊ : ∀ {Θ n} → RawC Θ n → RawC (Θ +ty +e) n
M₊ M = M [ wk₊ ]ᴿᶜ

Γ₊-[] : ∀ {Θ Θ' n} → (Γ : OCtx Θ n) → (σ : Subst (Θ +ty +e) Θ')
      → Γ₊ Γ [ σ ]ᶜᵗˣ ≡ Γ [ wk₊ ⨟ˢ σ ]ᶜᵗˣ
Γ₊-[] Γ σ =
  trans (cong (_[ σ ]ᶜᵗˣ)
          (sym (trans (sym ([⨟]ᶜᵗˣ Γ wkˢᵗ wkˢᵉ))
                 (trans (cong (_[ wkˢᵉ ]ᶜᵗˣ) (wkˢᵗ-ctx Γ)) (wkˢᵉ-ctx (wkᵗ-ctx Γ))))))
        ([⨟]ᶜᵗˣ Γ wk₊ σ)

M₊-[] : ∀ {Θ Θ' n} → (M : RawC Θ n) → (σ : Subst (Θ +ty +e) Θ')
      → M₊ M [ σ ]ᴿᶜ ≡ M [ wk₊ ⨟ˢ σ ]ᴿᶜ
M₊-[] M σ = [⨟]ᴿᶜ M wk₊ σ

C[_,_] : ∀ {Θ n} → OCtx Θ n → RawC Θ n → Constraint (Θ +ty +e)
C[_,_] {Θ} Γ M = genC (Γ₊ Γ) (M₊ M) (X̂ Θ ‼ t̂ Θ)

record Principal {Θ : Scope} {n : ℕ} (Γ : OCtx Θ n) (M : RawC Θ n) : Set where
  constructor mkPrincipal
  field

    -- the principal solution-with-residue

    Θ⁺ : Scope
    σ⁺ : Subst (Θ +ty +e) Θ⁺
    Q⁺ : Hyps Θ⁺

    -- the principal derivation itself (its type is `X̂ Θ [ σ⁺ ]ᵛ`, its
    -- effect `t̂ Θ [ σ⁺ ]ᵉ`)

    D⁺   : Q⁺ ∣ Γ₊ Γ [ σ⁺ ]ᶜᵗˣ ⊢C⦂ (X̂ Θ [ σ⁺ ]ᵛ) ‼ (t̂ Θ [ σ⁺ ]ᵉ)
    ⌊D⁺⌋ : ⌊ D⁺ ⌋ᶜ ≡ M₊ M [ σ⁺ ]ᴿᶜ

    -- every instance of the residue types `M`

    instantiate : ∀ {Θ''} → (δ : Subst Θ⁺ Θ'') → (Q : Hyps Θ'')
                → Q ⊩ᴴ Q⁺ [ δ ]
                -------------------------------------------------------
                → Σ[ D ∈ (Q ∣ Γ₊ Γ [ σ⁺ ⨟ˢ δ ]ᶜᵗˣ
                            ⊢C⦂ (X̂ Θ [ σ⁺ ⨟ˢ δ ]ᵛ) ‼ (t̂ Θ [ σ⁺ ⨟ˢ δ ]ᵉ)) ]
                    (⌊ D ⌋ᶜ ≡ M₊ M [ σ⁺ ⨟ˢ δ ]ᴿᶜ)

    -- every typing of `M` factors through the principal one

    mgu : ∀ {Θ''} → (σ : Subst (Θ +ty +e) Θ'') → (Q : Hyps Θ'')
        → {A₀ : OVType Θ''} → {ε₀ : EExp Θ''}
        → (D : Q ∣ Γ₊ Γ [ σ ]ᶜᵗˣ ⊢C⦂ A₀ ‼ ε₀)
        → ⌊ D ⌋ᶜ ≡ M₊ M [ σ ]ᴿᶜ
        → Q ∣ A₀ <:̂ᵛ X̂ Θ [ σ ]ᵛ
        → Q ⊩ ε₀ ≾̂ₑ t̂ Θ [ σ ]ᵉ
        ----------------------------------------------------
        → Σ[ δ ∈ Subst Θ⁺ Θ'' ]
            (((σ⁺ ⨟ˢ δ) ≐ˢ σ) × (Q ⊩ᴴ Q⁺ [ δ ]))

open Principal

principal : ∀ {Pᶜ Pᵖ : ∀ {Θ} → Constraint Θ → Set} → (sv : Solver Pᶜ Pᵖ)
          → ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
          → Pᵖ C[ Γ , M ]
          → {Θ' : Scope} {σ : Subst (Θ +ty +e) Θ'} {Q : Hyps Θ'}
          → Solver.solve sv C[ Γ , M ] ≡ just (Θ' , σ , Q)
          ------------------------------------------------
          → Principal Γ M

principal sv {Θ} Γ M p {Θ'} {σ} {Q} eq = mkPrincipal
  Θ' σ Q
  (proj₁ elab) (proj₂ elab)
  (λ δ Q' h → soundC (Γ₊ Γ) (M₊ M) (X̂ Θ) (t̂ Θ) (⊨-mono h C[ Γ , M ] sat))
  (λ σ' Q' D e st le →
     Solver.solve-principal sv C[ Γ , M ] p eq σ' Q'
       (completeC (Γ₊ Γ) (X̂ Θ) (t̂ Θ) (M₊ M) D e refl st le))
  where
    sat  = Solver.solve-sound sv C[ Γ , M ] eq
    elab = soundC (Γ₊ Γ) (M₊ M) (X̂ Θ) (t̂ Θ) sat

-- A typing of `M` in `Γ` at a type and effect is one of `M₊ M` in
-- `Γ₊ Γ`, the result unknowns sent to them, and so satisfies the
-- constraint of `M`

typing₊ : ∀ {Θ n Θ''} {Γ : OCtx Θ n} {M : RawC Θ n} → (σ₀ : Subst Θ Θ'') → {Q : Hyps Θ''}
        → {A₀ : OVType Θ''} → {ε₀ : EExp Θ''}
        → (D : Q ∣ Γ [ σ₀ ]ᶜᵗˣ ⊢C⦂ A₀ ‼ ε₀)
        → ⌊ D ⌋ᶜ ≡ M [ σ₀ ]ᴿᶜ
        -----------------------------------------------------------
        → Σ[ D' ∈ (Q ∣ Γ₊ Γ [ σ₀ ,ᵗ A₀ ,ᵉ ε₀ ]ᶜᵗˣ ⊢C⦂ A₀ ‼ ε₀) ]
            (⌊ D' ⌋ᶜ ≡ M₊ M [ σ₀ ,ᵗ A₀ ,ᵉ ε₀ ]ᴿᶜ)
typing₊ {Γ = Γ} {M} σ₀ {A₀ = A₀} {ε₀} D e =
  ctx-substᶜ (sym ctxeq) D , trans (⌊ctxᶜ⌋ (sym ctxeq) D) (trans e (sym (M₊-[] M σ)))
  where
    σ : Subst _ _
    σ = σ₀ ,ᵗ A₀ ,ᵉ ε₀

    ctxeq : Γ₊ Γ [ σ ]ᶜᵗˣ ≡ Γ [ σ₀ ]ᶜᵗˣ
    ctxeq = Γ₊-[] Γ σ

typing-sat : ∀ {Θ n Θ''} {Γ : OCtx Θ n} {M : RawC Θ n} → (σ₀ : Subst Θ Θ'') → {Q : Hyps Θ''}
           → {A₀ : OVType Θ''} → {ε₀ : EExp Θ''}
           → (D : Q ∣ Γ [ σ₀ ]ᶜᵗˣ ⊢C⦂ A₀ ‼ ε₀)
           → ⌊ D ⌋ᶜ ≡ M [ σ₀ ]ᴿᶜ
           ------------------------------------
           → (σ₀ ,ᵗ A₀ ,ᵉ ε₀) ⊨[ Q ] C[ Γ , M ]
typing-sat {Θ} {Γ = Γ} {M} σ₀ {A₀ = A₀} D e =
  completeC (Γ₊ Γ) (X̂ Θ) (t̂ Θ) (M₊ M) (proj₁ D') (proj₂ D') refl (<:̂ᵛ-refl A₀) ⊩≾̂ₑ-refl
  where
    D' = typing₊ σ₀ D e

-- A typing of `M` at an arbitrary type and effect is an instance of the
-- principal one: the principal solution instantiates to it on the
-- program's variables, the principal type exactly, the principal
-- effect up to the residual entailment.

principal-inst : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} → (p : Principal Γ M)
               → ∀ {Θ''} → (σ₀ : Subst Θ Θ'') → (Q : Hyps Θ'')
               → {A₀ : OVType Θ''} → {ε₀ : EExp Θ''}
               → (D : Q ∣ Γ [ σ₀ ]ᶜᵗˣ ⊢C⦂ A₀ ‼ ε₀)
               → ⌊ D ⌋ᶜ ≡ M [ σ₀ ]ᴿᶜ
               ----------------------------------------------------------
               → Σ[ δ ∈ Subst (Θ⁺ p) Θ'' ]
                   ((wk₊ ⨟ˢ σ⁺ p ⨟ˢ δ ≐ˢ σ₀)
                     × (X̂ _ [ σ⁺ p ]ᵛ [ δ ]ᵛ ≡ A₀)
                     × (Q ⊩ (t̂ _ [ σ⁺ p ]ᵉ [ δ ]ᵉ) ≾̂ₑ ε₀)
                     × (Q ⊩ᴴ Q⁺ p [ δ ]))

principal-inst {Θ} {Γ = Γ} {M = M} p {Θ''} σ₀ Q {A₀} {ε₀} D e =
  δ , ceq , aeq , subst (λ x → Q ⊩ x ≾̂ₑ ε₀) (sym teq) ⊩≾̂ₑ-refl , h
  where
    σ : Subst (Θ +ty +e) Θ''
    σ = σ₀ ,ᵗ A₀ ,ᵉ ε₀

    D' = typing₊ σ₀ D e

    fac = mgu p σ Q (proj₁ D') (proj₂ D') (<:̂ᵛ-refl A₀) ⊩≾̂ₑ-refl

    δ = proj₁ fac
    h = proj₂ (proj₂ fac)

    -- the principal solution, type and effect follow the factorisation

    ceq : wk₊ ⨟ˢ σ⁺ p ⨟ˢ δ ≐ˢ σ₀
    ceq = ≐ˢ-trans (⨟-assoc wk₊ (σ⁺ p) δ) (⨟-congʳ wk₊ (proj₁ (proj₂ fac)))

    aeq : X̂ Θ [ σ⁺ p ]ᵛ [ δ ]ᵛ ≡ A₀
    aeq = trans ([⨟]ᵛ (X̂ Θ) (σ⁺ p) δ) ([≐]ᵛ (proj₁ (proj₂ fac)) (X̂ Θ))

    teq : t̂ Θ [ σ⁺ p ]ᵉ [ δ ]ᵉ ≡ ε₀
    teq = trans ([⨟]ᵉ (t̂ Θ) (σ⁺ p) δ) ([≐]ᵉ (proj₁ (proj₂ fac)) (t̂ Θ))

-- A principal typing of `M` in `Γ`: an instantiation `σ̃` of the
-- program's variables, hypotheses `Q̃` and a type `X̃` over a scope `Θ̃`,
-- with a derivation. Every instance of `Q̃` types `M` (`instantiate`),
-- and every typing of `M` factors through it at each closed instance
-- satisfying its hypotheses (`factor`): the instantiations agree, the
-- factoring instance satisfies `Q̃`, and there `X̃` is a subtype of the
-- typing's type. Entailment is by closed instances, as in HM(X)
-- (Odersky, Sulzmann and Wehr, TAPOS 1999).

record PrincipalTyping {Θ : Scope} {n : ℕ} (Γ : OCtx Θ n) (M : RawC Θ n) : Set where
  constructor mkPrincipalTyping
  field
    Θ̃ : Scope
    σ̃ : Subst Θ Θ̃
    Q̃ : Hyps Θ̃
    X̃ : OCType Θ̃

    D̃   : Q̃ ∣ Γ [ σ̃ ]ᶜᵗˣ ⊢C⦂ X̃
    ⌊D̃⌋ : ⌊ D̃ ⌋ᶜ ≡ M [ σ̃ ]ᴿᶜ

    instantiate : ∀ {Θ''} → (δ : Subst Θ̃ Θ'') → (Q : Hyps Θ'')
                → Q ⊩ᴴ Q̃ [ δ ]
                --------------------------------------------------
                → Σ[ D ∈ (Q ∣ Γ [ σ̃ ⨟ˢ δ ]ᶜᵗˣ ⊢C⦂ X̃ [ δ ]ᶜ) ]
                    (⌊ D ⌋ᶜ ≡ M [ σ̃ ⨟ˢ δ ]ᴿᶜ)

    factor : ∀ {Θ''} → (σ₀ : Subst Θ Θ'') → (Q₀ : Hyps Θ'') → {C₀ : OCType Θ''}
           → (D₀ : Q₀ ∣ Γ [ σ₀ ]ᶜᵗˣ ⊢C⦂ C₀)
           → ⌊ D₀ ⌋ᶜ ≡ M [ σ₀ ]ᴿᶜ
           → (δ₀ : Subst Θ'' ∅ˢ) → ∅ᴴ ⊩ᴴ Q₀ [ δ₀ ]
           ---------------------------------------------------
           → Σ[ δ ∈ Subst Θ̃ ∅ˢ ]
               ((σ̃ ⨟ˢ δ ≐ˢ σ₀ ⨟ˢ δ₀)
                 × (∅ᴴ ⊩ᴴ Q̃ [ δ ])
                 × (∅ᴴ ∣ X̃ [ δ ]ᶜ <:̂ᶜ C₀ [ δ₀ ]ᶜ))
