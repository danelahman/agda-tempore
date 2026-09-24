------------------------------------------------------------------
-- Principal types                                              --
--                                                              --
-- Generation is run at `Θ` extended by a fresh type variable   --
-- and a fresh effect variable, standing for the result type    --
-- and the result effect, the term weakened into that scope;    --
-- solving the resulting constraint yields a principal solution --
-- together with its residual hypotheses and obligations.       --
--                                                              --
-- `Principal Γ M` packages `instantiate` — every instance      --
-- meeting the residue gives a typing of `M` — and `mgu` —      --
-- every typing of `M` factors through the principal            --
-- substitution and residue at each closed instance, its type   --
-- and effect bounded by the principal ones. A typing of `M` is --
-- a derivation that erases to an instance of `M`, its          --
-- annotations instantiated too.                                --
--                                                              --
-- `PrincipalTyping Γ M` is the answer over a scope of its own: --
-- a scheme whose every instance types `M`, and through which   --
-- every typing of `M` factors at each closed instance. `M` is  --
-- then typable (`Typable`) exactly when the scheme's           --
-- conditions are satisfiable (`typable-⇔`). `Inference Γ M` is --
-- the outcome of inference.                                    --
--                                                              --
-- Principal types carrying a constraint set, after Pretnar     --
-- (LMCS 2014); "residual constraint" is OutsideIn(X)'s term    --
-- (Vytiniotis et al., JFP 2011). The context is fixed up to    --
-- its variables, so what is principal is the type — Damas and  --
-- Milner's principal type scheme (1982) — not a principal      --
-- typing in Wells's sense (2002).                              --
------------------------------------------------------------------

open import Data.List.Base using ([])
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Nullary using (¬_)

open import TypeInference.Scopes
open import TypeInference.Outcome

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
open import TypeInference.OpenSyntax.Instances S using (Obligs; _⊩_∣_[_]; _⊨_∣_; Satisfiable)

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

    -- the principal solution, with its residue and obligations

    Θ⁺ : Scope
    σ⁺ : Subst (Θ +ty +e) Θ⁺
    Q⁺ : Hyps Θ⁺
    R⁺ : Obligs Θ⁺

    -- every instance meeting them types `M`, at the principal type
    -- `X̂ Θ [ σ⁺ ]ᵛ` and effect `t̂ Θ [ σ⁺ ]ᵉ`

    instantiate : ∀ {Θ''} → (δ : Subst Θ⁺ Θ'') → (Q : Hyps Θ'')
                → Q ⊩ Q⁺ ∣ R⁺ [ δ ]
                -------------------------------------------------------
                → Σ[ D ∈ (Q ∣ Γ₊ Γ [ σ⁺ ⨟ˢ δ ]ᶜᵗˣ
                            ⊢C⦂ (X̂ Θ [ σ⁺ ⨟ˢ δ ]ᵛ) ‼ (t̂ Θ [ σ⁺ ⨟ˢ δ ]ᵉ)) ]
                    (⌊ D ⌋ᶜ ≡ M₊ M [ σ⁺ ⨟ˢ δ ]ᴿᶜ)

    -- every typing of `M` factors through the principal one at each
    -- closed instance satisfying its hypotheses

    mgu : ∀ {Θ''} → (σ : Subst (Θ +ty +e) Θ'') → (Q : Hyps Θ'')
        → {A₀ : OVType Θ''} → {ε₀ : EExp Θ''}
        → (D : Q ∣ Γ₊ Γ [ σ ]ᶜᵗˣ ⊢C⦂ A₀ ‼ ε₀)
        → ⌊ D ⌋ᶜ ≡ M₊ M [ σ ]ᴿᶜ
        → Q ∣ A₀ <:̂ᵛ X̂ Θ [ σ ]ᵛ
        → Q ⊩ ε₀ ≾̂ₑ t̂ Θ [ σ ]ᵉ
        → (δ₀ : Subst Θ'' ∅ˢ) → δ₀ ⊨ Q ∣ []
        ----------------------------------------------------
        → Σ[ δ ∈ Subst Θ⁺ ∅ˢ ]
            (((σ⁺ ⨟ˢ δ) ≐ˢ (σ ⨟ˢ δ₀)) × (δ ⊨ Q⁺ ∣ R⁺))

open Principal

principal : (sv : Solver)
          → ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
          → {Θ' : Scope} {σ : Subst (Θ +ty +e) Θ'} {Q : Hyps Θ'} {R : Obligs Θ'}
          → Solver.solve sv C[ Γ , M ] ≡ solved (Θ' , σ , Q , R)
          ------------------------------------------------
          → Principal Γ M

principal sv {Θ} Γ M {Θ'} {σ} {Q} {R} eq = mkPrincipal
  Θ' σ Q R
  (λ δ Q' h → soundC (Γ₊ Γ) (M₊ M) (X̂ Θ) (t̂ Θ) (sat δ Q' h))
  (λ σ' Q' D e st le δ₀ h →
     Solver.solve-principal sv C[ Γ , M ] eq σ' Q' []
       (⊨-∣ C[ Γ , M ] (completeC (Γ₊ Γ) (X̂ Θ) (t̂ Θ) (M₊ M) D e refl st le)) δ₀ h)
  where
    sat = Solver.solve-sound sv C[ Γ , M ] eq

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

-- A typing of `M` at an arbitrary type and effect is, at each closed
-- instance satisfying its hypotheses, an instance of the principal
-- one: the principal solution instantiates to it on the program's
-- variables, the principal type exactly, the principal effect up to
-- entailment.

principal-inst : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} → (p : Principal Γ M)
               → ∀ {Θ''} → (σ₀ : Subst Θ Θ'') → (Q : Hyps Θ'')
               → {A₀ : OVType Θ''} → {ε₀ : EExp Θ''}
               → (D : Q ∣ Γ [ σ₀ ]ᶜᵗˣ ⊢C⦂ A₀ ‼ ε₀)
               → ⌊ D ⌋ᶜ ≡ M [ σ₀ ]ᴿᶜ
               → (δ₀ : Subst Θ'' ∅ˢ) → δ₀ ⊨ Q ∣ []
               ----------------------------------------------------------
               → Σ[ δ ∈ Subst (Θ⁺ p) ∅ˢ ]
                   ((wk₊ ⨟ˢ σ⁺ p ⨟ˢ δ ≐ˢ σ₀ ⨟ˢ δ₀)
                     × (X̂ _ [ σ⁺ p ]ᵛ [ δ ]ᵛ ≡ A₀ [ δ₀ ]ᵛ)
                     × (∅ᴴ ⊩ (t̂ _ [ σ⁺ p ]ᵉ [ δ ]ᵉ) ≾̂ₑ ε₀ [ δ₀ ]ᵉ)
                     × (δ ⊨ Q⁺ p ∣ R⁺ p))

principal-inst {Θ} {Γ = Γ} {M = M} p {Θ''} σ₀ Q {A₀} {ε₀} D e δ₀ h₀ =
  δ , ceq , aeq , subst (λ x → ∅ᴴ ⊩ x ≾̂ₑ ε₀ [ δ₀ ]ᵉ) (sym teq) ⊩≾̂ₑ-refl , h
  where
    σ : Subst (Θ +ty +e) Θ''
    σ = σ₀ ,ᵗ A₀ ,ᵉ ε₀

    D' = typing₊ σ₀ D e

    fac = mgu p σ Q (proj₁ D') (proj₂ D') (<:̂ᵛ-refl A₀) ⊩≾̂ₑ-refl δ₀ h₀

    δ   = proj₁ fac
    tri = proj₁ (proj₂ fac)
    h   = proj₂ (proj₂ fac)

    -- the principal solution, type and effect follow the factorisation

    ceq : wk₊ ⨟ˢ σ⁺ p ⨟ˢ δ ≐ˢ σ₀ ⨟ˢ δ₀
    ceq = ≐ˢ-trans (⨟-assoc wk₊ (σ⁺ p) δ)
          (≐ˢ-trans (⨟-congʳ wk₊ tri) (≐ˢ-sym (⨟-assoc wk₊ σ δ₀)))

    aeq : X̂ Θ [ σ⁺ p ]ᵛ [ δ ]ᵛ ≡ A₀ [ δ₀ ]ᵛ
    aeq = trans ([⨟]ᵛ (X̂ Θ) (σ⁺ p) δ) ([≐]ᵛ tri (X̂ Θ))

    teq : t̂ Θ [ σ⁺ p ]ᵉ [ δ ]ᵉ ≡ ε₀ [ δ₀ ]ᵉ
    teq = trans ([⨟]ᵉ (t̂ Θ) (σ⁺ p) δ) ([≐]ᵉ tri (t̂ Θ))

-- A principal typing of `M` in `Γ`: an instantiation `σ̃` of the
-- program's variables, hypotheses `Q̃`, obligations `R̃` and a type
-- `X̃` over a scope `Θ̃`, the scheme `∀ Θ̃. Q̃ ∧ R̃ ⇒ X̃`. Every instance
-- meeting `Q̃` and `R̃` types `M` (`instantiate`), and every typing of
-- `M` factors through it at each closed instance satisfying its
-- hypotheses (`factor`): the instantiations agree, the factoring
-- instance satisfies `Q̃` and `R̃`, and there `X̃` is a subtype of the
-- typing's type. Entailment is by closed instances, as in HM(X)
-- (Odersky, Sulzmann and Wehr, TAPOS 1999).

record PrincipalTyping {Θ : Scope} {n : ℕ} (Γ : OCtx Θ n) (M : RawC Θ n) : Set where
  constructor mkPrincipalTyping
  field
    Θ̃ : Scope
    σ̃ : Subst Θ Θ̃
    Q̃ : Hyps Θ̃
    R̃ : Obligs Θ̃
    X̃ : OCType Θ̃

    instantiate : ∀ {Θ''} → (δ : Subst Θ̃ Θ'') → (Q : Hyps Θ'')
                → Q ⊩ Q̃ ∣ R̃ [ δ ]
                --------------------------------------------------
                → Σ[ D ∈ (Q ∣ Γ [ σ̃ ⨟ˢ δ ]ᶜᵗˣ ⊢C⦂ X̃ [ δ ]ᶜ) ]
                    (⌊ D ⌋ᶜ ≡ M [ σ̃ ⨟ˢ δ ]ᴿᶜ)

    factor : ∀ {Θ''} → (σ₀ : Subst Θ Θ'') → (Q₀ : Hyps Θ'') → {C₀ : OCType Θ''}
           → (D₀ : Q₀ ∣ Γ [ σ₀ ]ᶜᵗˣ ⊢C⦂ C₀)
           → ⌊ D₀ ⌋ᶜ ≡ M [ σ₀ ]ᴿᶜ
           → (δ₀ : Subst Θ'' ∅ˢ) → δ₀ ⊨ Q₀ ∣ []
           ---------------------------------------------------
           → Σ[ δ ∈ Subst Θ̃ ∅ˢ ]
               ((σ̃ ⨟ˢ δ ≐ˢ σ₀ ⨟ˢ δ₀)
                 × (δ ⊨ Q̃ ∣ R̃)
                 × (∅ᴴ ∣ X̃ [ δ ]ᶜ <:̂ᶜ C₀ [ δ₀ ]ᶜ))

open PrincipalTyping

-- A typing of `M` in `Γ`: a derivation over some scope, erasing to an
-- instance of `M`, under hypotheses some closed instance satisfies

record Typable {Θ : Scope} {n : ℕ} (Γ : OCtx Θ n) (M : RawC Θ n) : Set where
  constructor typable
  field
    Θ₀     : Scope
    σ₀     : Subst Θ Θ₀
    Q₀     : Hyps Θ₀
    C₀     : OCType Θ₀
    D₀     : Q₀ ∣ Γ [ σ₀ ]ᶜᵗˣ ⊢C⦂ C₀
    erases : ⌊ D₀ ⌋ᶜ ≡ M [ σ₀ ]ᴿᶜ
    sat    : Satisfiable Q₀ []

-- A principal typing decides typability up to its conditions: `M` is
-- typable exactly when they are satisfiable. A satisfying instance
-- instantiates the scheme; a typing factors through it.

typable-⇔ : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} → (p : PrincipalTyping Γ M)
          → Typable Γ M ⇔ Satisfiable (Q̃ p) (R̃ p)
typable-⇔ {Γ = Γ} {M} p = mk⇔ to from
  where
    to : Typable Γ M → Satisfiable (Q̃ p) (R̃ p)
    to (typable Θ₀ σ₀ Q₀ C₀ D₀ e (δ₀ , h₀)) with factor p σ₀ Q₀ D₀ e δ₀ h₀
    ... | δ , _ , h , _ = δ , h

    from : Satisfiable (Q̃ p) (R̃ p) → Typable Γ M
    from (δ , h) with instantiate p δ ∅ᴴ h
    ... | D , e = typable ∅ˢ (σ̃ p ⨟ˢ δ) ∅ᴴ (X̃ p [ δ ]ᶜ) D e (idˢ , All._∷_ ⊩ᴴ-∅ All.[])

-- The outcome of inference: a principal typing, a refutation, or stuck

data Inference {Θ : Scope} {n : ℕ} (Γ : OCtx Θ n) (M : RawC Θ n) : Set where
  typed     : PrincipalTyping Γ M → Inference Γ M
  untypable : Inference Γ M
  stuck     : Inference Γ M
