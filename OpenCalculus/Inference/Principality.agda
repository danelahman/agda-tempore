------------------------------------------------------------------
-- Principal types                                              --
--                                                              --
-- Generation runs at `Θ` extended by a type variable and an    --
-- effect variable for the result type and effect, with the     --
-- context and the term weakened into that scope (`C[_,_]`). A  --
-- solution of that constraint, with its residual hypotheses    --
-- and obligations, is principal (`PrincipalSolution Γ M`) when --
-- every instance meeting the residue types `M` (`instantiate`) --
-- and every typing of `M` factors through it at each closed    --
-- instance, with type and effect bounded by the principal ones --
-- (`factor`). A typing of `M` is a derivation erasing to an    --
-- instance of `M`, annotations included.                       --
--                                                              --
-- `PrincipalScheme Γ M` is a principal type scheme over a      --
-- scope of its own: every instance types `M` (`instantiate`),  --
-- and every typing of `M` factors through it at each closed    --
-- instance (`factor`). `M` is typable (`Typable`) exactly when --
-- the scheme's conditions are satisfiable (`typable-⇔`).       --
-- `Inference Γ M` is the outcome of inference, `Check Γ M`     --
-- that of a check that exhibits a closed instance.             --
--                                                              --
-- Principal types with constraint sets follow Pretnar (LMCS    --
-- 2014); "residual constraint" is the term of OutsideIn(X)     --
-- (Vytiniotis et al., JFP 2011). The context is fixed up to    --
-- the instantiation of its variables, so the principal object  --
-- is a type scheme in the sense of Damas and Milner (1982),    --
-- not a principal typing in the sense of Wells (2002).         --
------------------------------------------------------------------

open import Data.List.Base using ([])
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_)

open import OpenCalculus.Syntax.Scopes
open import OpenCalculus.Inference.Outcome

module OpenCalculus.Inference.Principality (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OpenCalculus.Syntax.Grades   S
open import OpenCalculus.Syntax.Types    S
open import OpenCalculus.Syntax.Contexts S
open import OpenCalculus.Syntax.Subst    S
open import OpenCalculus.Hypotheses     S
open import OpenCalculus.Typing S
open import OpenCalculus.Hypotheses.Instances S
  using (_⊩_∣_[_]; _⊨_∣_; Satisfiable; Satisfiable-∅)

open import OpenCalculus.Syntax.Raw       S
open import OpenCalculus.Syntax.Raw.Subst S
open import OpenCalculus.Typing.Erasure   S

open import OpenCalculus.Inference.Constraints.Syntax       S
open import OpenCalculus.Inference.Constraints.Satisfaction S
open import OpenCalculus.Inference.Constraints.Properties   S

open import OpenCalculus.Inference.Generate     S
open import OpenCalculus.Inference.Soundness    S
open import OpenCalculus.Inference.Completeness S
open import OpenCalculus.Inference.Solver       S

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

-- A handler-free term's constraint has no rigid binder

C[]-rigidFree : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
              → HandlerFreeᶜ M → RigidFree C[ Γ , M ]
C[]-rigidFree Γ M h = genCˢ-rigidFree (M₊ M) (handlerFree-[]ᴿᶜ M h)

record PrincipalSolution {Θ : Scope} {n : ℕ} (Γ : OCtx Θ n) (M : RawC Θ n) : Set where
  constructor mkPrincipalSolution
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

    factor : ∀ {Θ''} → (σ : Subst (Θ +ty +e) Θ'') → (Q : Hyps Θ'')
        → {A₀ : OVType Θ''} → {ε₀ : EExp Θ''}
        → (D : Q ∣ Γ₊ Γ [ σ ]ᶜᵗˣ ⊢C⦂ A₀ ‼ ε₀)
        → ⌊ D ⌋ᶜ ≡ M₊ M [ σ ]ᴿᶜ
        → Q ∣ A₀ <:̂ᵛ X̂ Θ [ σ ]ᵛ
        → Q ⊩ ε₀ ≾̂ₑ t̂ Θ [ σ ]ᵉ
        → (δ₀ : Subst Θ'' ∅ˢ) → δ₀ ⊨ Q ∣ []
        ----------------------------------------------------
        → Σ[ δ ∈ Subst Θ⁺ ∅ˢ ]
            (((σ⁺ ⨟ˢ δ) ≐ˢ (σ ⨟ˢ δ₀)) × (δ ⊨ Q⁺ ∣ R⁺))

open PrincipalSolution

principalSolution : (sv : Solver)
          → ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
          → {Θ' : Scope} {σ : Subst (Θ +ty +e) Θ'} {Q : Hyps Θ'} {R : Obligs Θ'}
          → Solver.solve sv C[ Γ , M ] ≡ solved (Θ' , σ , Q , R)
          ------------------------------------------------
          → PrincipalSolution Γ M

principalSolution sv {Θ} Γ M {Θ'} {σ} {Q} {R} eq = mkPrincipalSolution
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

principal-inst : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} → (p : PrincipalSolution Γ M)
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

    fac = factor p σ Q (proj₁ D') (proj₂ D') (<:̂ᵛ-refl A₀) ⊩≾̂ₑ-refl δ₀ h₀

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

-- A principal type scheme of `M` in `Γ`: an instantiation `σ̃` of the
-- program's variables, hypotheses `Q̃`, obligations `R̃` and a type
-- `X̃` over a scope `Θ̃`, the scheme `∀ Θ̃. Q̃ ∧ R̃ ⇒ X̃`. Every instance
-- meeting `Q̃` and `R̃` types `M` (`instantiate`), and every typing of
-- `M` factors through it at each closed instance satisfying its
-- hypotheses (`factor`): the instantiations agree, the factoring
-- instance satisfies `Q̃` and `R̃`, and there `X̃` is a subtype of the
-- typing's type. Entailment is by closed instances, as in HM(X)
-- (Odersky, Sulzmann and Wehr, TAPOS 1999).

record PrincipalScheme {Θ : Scope} {n : ℕ} (Γ : OCtx Θ n) (M : RawC Θ n) : Set where
  constructor mkPrincipalScheme
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

open PrincipalScheme

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

-- `M` is typable exactly when the conditions of its principal type
-- scheme are satisfiable: a satisfying instance instantiates the scheme,
-- and a typing factors through it.

typable-⇔ : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} → (p : PrincipalScheme Γ M)
          → Typable Γ M ⇔ Satisfiable (Q̃ p) (R̃ p)
typable-⇔ {Γ = Γ} {M} p = mk⇔ to from
  where
    to : Typable Γ M → Satisfiable (Q̃ p) (R̃ p)
    to (typable Θ₀ σ₀ Q₀ C₀ D₀ e (δ₀ , h₀)) with factor p σ₀ Q₀ D₀ e δ₀ h₀
    ... | δ , _ , h , _ = δ , h

    from : Satisfiable (Q̃ p) (R̃ p) → Typable Γ M
    from (δ , h) with instantiate p δ ∅ᴴ h
    ... | D , e = typable ∅ˢ (σ̃ p ⨟ˢ δ) ∅ᴴ (X̃ p [ δ ]ᶜ) D e (idˢ , ⊩ᴴ-∅ , All.[])

-- A term whose principal type scheme has no hypotheses and no
-- obligations is typable

typable-unconditional : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} → (p : PrincipalScheme Γ M)
                       → Q̃ p ≡ ∅ᴴ → R̃ p ≡ [] → Typable Γ M
typable-unconditional p eq-Q eq-R =
  Equivalence.from (typable-⇔ p) (subst₂ Satisfiable (sym eq-Q) (sym eq-R) Satisfiable-∅)

-- The outcome of inference: a principal type scheme, a refutation, or stuck

data Inference {Θ : Scope} {n : ℕ} (Γ : OCtx Θ n) (M : RawC Θ n) : Set where
  typed     : PrincipalScheme Γ M → Inference Γ M
  untypable : Inference Γ M
  stuck     : Inference Γ M

-- The outcome of a check of a closed program: a principal type scheme
-- with a closed instance of its conditions, a refutation, a principal
-- type scheme for which no instance was found, or stuck

data Check {Θ : Scope} {n : ℕ} (Γ : OCtx Θ n) (M : RawC Θ n) : Set where
  established   : (p : PrincipalScheme Γ M) → Satisfiable (Q̃ p) (R̃ p) → Check Γ M
  untypable     : Check Γ M
  unestablished : PrincipalScheme Γ M → Check Γ M
  stuck         : Check Γ M
