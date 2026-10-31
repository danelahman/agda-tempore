------------------------------------------------------------------
-- Substitution of types and grades in open derivations         --
--                                                              --
-- Along `σ : Subst Θ Θ'` with `Q'` entailing `Q`, a derivation --
-- under `Q` becomes one under `Q'` (`substᵛ`, `substᶜ`),       --
-- erasing to the substituted raw term. At `idˢ ,ᵉ ε` it        --
-- instantiates the variable of a handler clause                --
-- (`instantiate-clause`).                                      --
------------------------------------------------------------------

open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Typing.GradeSubstitution (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import PolymorphicCalculus.Syntax.Grades                S
open import PolymorphicCalculus.Syntax.Types                 S
open import PolymorphicCalculus.Syntax.Contexts              S
open import PolymorphicCalculus.Syntax.Contexts.Properties   S
open import PolymorphicCalculus.Syntax.GradeSubstitution     S
open import PolymorphicCalculus.Hypotheses                   S
open import PolymorphicCalculus.Typing                       S
open import PolymorphicCalculus.Typing.Erasure               S
open import PolymorphicCalculus.Typing.Transport             S
open import PolymorphicCalculus.Syntax.Raw                   S
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution S

------------------------------------------------------------------------
-- The context and type of the clause of `op`, as in the rule `handler`

clause-ctx : ∀ {Θ n} → OCtx Θ n → OVType Θ → Op → OCtx (Θ +e) (suc (suc n))
clause-ctx {Θ} Γ B op =
  wkᵉ-ctx Γ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
    ∷ [ rconst ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ! evar (newᵉ {Θ}))

clause-ty : ∀ {Θ} → OVType Θ → Op → OCType (Θ +e)
clause-ty {Θ} B op = wkᵉ-v B ! (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ}))

clause-ctx-↑ : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (Γ : OCtx Θ n) → (B : OVType Θ) → (op : Op)
             → clause-ctx Γ B op [ σ ↑ᵉ ]ᶜᵗˣ ≡ clause-ctx (Γ [ σ ]ᶜᵗˣ) (B [ σ ]ᵛ) op
clause-ctx-↑ σ Γ B op =
  cong₂ _∷_
        (cong₂ _∷_ (cong (_⟨ rconst ⊤ᵣ ⟩) (wk-↑ᵉ-ctx σ Γ)) (⌜⌝ᵍ-subst (σ ↑ᵉ) (param op)))
        (cong₂ (λ A₀ B₀ → [ rconst ∣ op-grade op ∣ᵉ ] (A₀ ⇒ B₀ ! _))
               (⌜⌝ᵍ-subst (σ ↑ᵉ) (arity op)) (wk-↑ᵉ-v σ B))

clause-ty-↑ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B : OVType Θ) → (op : Op)
            → clause-ty B op [ σ ↑ᵉ ]ᶜ ≡ clause-ty (B [ σ ]ᵛ) op
clause-ty-↑ σ B op = cong (_! _) (wk-↑ᵉ-v σ B)

------------------------------------------------------------------------
-- The substitution lemma

substʳ : ∀ {Θ Θ' n} {Q : Hyps Θ} {Q' : Hyps Θ'} {Γ : OCtx Θ n}
           {ρ' ρ₀ ρ : RExp Θ} {X₀ X : OVType Θ} {z : [ ρ₀ ] X₀ ∈̂[ ρ' ] Γ}
       → (σ : Subst Θ Θ') → Q' ⊩ᴴ Q [ σ ]
       → Q ∣ Γ ⊢↪[ ρ' ] z ⦂[ ρ ] X
       → Q' ∣ Γ [ σ ]ᶜᵗˣ ⊢↪[ ρ' [ σ ]ʳ ] ∈̂-subst σ z ⦂[ ρ [ σ ]ʳ ] X [ σ ]ᵛ
substʳ σ h res-var               = res-var
substʳ σ h (res-ann ρₐ Xₐ R p q) =
  res-ann (ρₐ [ σ ]ʳ) (Xₐ [ σ ]ᵛ) (substʳ σ h R) (⊩-substᵣ h p) (<:̂ᵛ-subst h q)

⌊substʳ⌋ : ∀ {Θ Θ' n} {Q : Hyps Θ} {Q' : Hyps Θ'} {Γ : OCtx Θ n}
             {ρ' ρ₀ ρ : RExp Θ} {X₀ X : OVType Θ} {z : [ ρ₀ ] X₀ ∈̂[ ρ' ] Γ}
         → (σ : Subst Θ Θ') → (h : Q' ⊩ᴴ Q [ σ ])
         → (R : Q ∣ Γ ⊢↪[ ρ' ] z ⦂[ ρ ] X)
         → ⌊ substʳ σ h R ⌋ʳ ≡ ⌊ R ⌋ʳ [ σ ]ᴿᵛ
⌊substʳ⌋ {z = z} σ h res-var = cong var (var-pos-∈̂-subst σ z)
⌊substʳ⌋ σ h (res-ann ρₐ Xₐ R p q) =
  cong (_⦂ᵛ [ ρₐ [ σ ]ʳ ] (Xₐ [ σ ]ᵛ)) (⌊substʳ⌋ σ h R)

mutual

  substᵛ : ∀ {Θ Θ' n} {Q : Hyps Θ} {Q' : Hyps Θ'} {Γ : OCtx Θ n} {A : OVType Θ}
         → (σ : Subst Θ Θ') → Q' ⊩ᴴ Q [ σ ]
         → Q ∣ Γ ⊢V⦂ A
         ---------------------------------
         → Q' ∣ Γ [ σ ]ᶜᵗˣ ⊢V⦂ A [ σ ]ᵛ

  substᵛ σ h (var x p)       = var (∈̂-subst σ x) (VarOK-subst h p)
  substᵛ {Γ = Γ} σ h (usedef {s = s} f δ h' e) =
    usedef (subst (_ ∈ᵖ[ _ ]_) (sym (defs-subst Γ σ)) f) (δ ⨟ˢ σ) (⊩ᴴ-⨟ h h')
        (trans (cong (_[ σ ]ᵛ) e) ([⨟]ᵛ (Xˢ s) δ σ))
  substᵛ σ h (const B c)     = const B c
  substᵛ σ h ⋆               = ⋆
  substᵛ σ h true            = true
  substᵛ σ h false           = false
  substᵛ σ h zero            = zero
  substᵛ σ h (succ V)        = succ (substᵛ σ h V)
  substᵛ σ h ⦉ V , W ⦊        = ⦉ substᵛ σ h V , substᵛ σ h W ⦊
  substᵛ σ h (inl V)         = inl (substᵛ σ h V)
  substᵛ σ h (inr V)         = inr (substᵛ σ h V)
  substᵛ σ h nil             = nil
  substᵛ σ h (cons V W)      = cons (substᵛ σ h V) (substᵛ σ h W)
  substᵛ σ h (cmp ⋈ V W et)  = cmp ⋈ (substᵛ σ h V) (substᵛ σ h W) (⊩Et-subst h et)
  substᵛ σ h (lam M)         = lam (substᶜ σ h M)
  substᵛ {Γ = Γ} σ h (handler {B = B} N H) =
    handler (substᶜ σ h N) (λ op → substˡ σ h Γ B op (H op))
  substᵛ σ h (annᵛ A V)      = annᵛ (A [ σ ]ᵛ) (substᵛ σ h V)
  substᵛ σ h (subV V p)      = subV (substᵛ σ h V) (<:̂ᵛ-subst h p)

  substˡ : ∀ {Θ Θ' n} {Q : Hyps Θ} {Q' : Hyps Θ'}
         → (σ : Subst Θ Θ') → Q' ⊩ᴴ Q [ σ ]
         → (Γ : OCtx Θ n) → (B : OVType Θ) → (op : Op)
         → wkᵉ-H Q ∣ clause-ctx Γ B op ⊢C⦂ clause-ty B op
         ------------------------------------------------------------------
         → wkᵉ-H Q' ∣ clause-ctx (Γ [ σ ]ᶜᵗˣ) (B [ σ ]ᵛ) op ⊢C⦂ clause-ty (B [ σ ]ᵛ) op

  substˡ σ h Γ B op M =
    c-subst (clause-ty-↑ σ B op)
            (ctx-castᶜ (clause-ctx-↑ σ Γ B op) (substᶜ (σ ↑ᵉ) (⊩ᴴ-↑ᵉ h) M))

  substᶜ : ∀ {Θ Θ' n} {Q : Hyps Θ} {Q' : Hyps Θ'} {Γ : OCtx Θ n} {C : OCType Θ}
         → (σ : Subst Θ Θ') → Q' ⊩ᴴ Q [ σ ]
         → Q ∣ Γ ⊢C⦂ C
         ---------------------------------
         → Q' ∣ Γ [ σ ]ᶜᵗˣ ⊢C⦂ C [ σ ]ᶜ

  substᶜ σ h (return V)                = return (substᵛ σ h V)
  substᶜ σ h (M ⨟ N)                   = substᶜ σ h M ⨟ substᶜ σ h N
  substᶜ σ h (V · W)                   = substᵛ σ h V · substᵛ σ h W
  substᶜ σ h (match V `in M)           = match substᵛ σ h V `in substᶜ σ h M
  substᶜ σ h (absurd V)                = absurd (substᵛ σ h V)
  substᶜ σ h (if V `then M `else N)    =
    if substᵛ σ h V `then substᶜ σ h M `else substᶜ σ h N
  substᶜ σ h (caseℕ V `zero M `succ N) =
    caseℕ substᵛ σ h V `zero substᶜ σ h M `succ substᶜ σ h N
  substᶜ σ h (case+ V `inl M `inr N)   =
    case+ substᵛ σ h V `inl substᶜ σ h M `inr substᶜ σ h N
  substᶜ σ h (caseL V `nil M `cons N)  =
    caseL substᵛ σ h V `nil substᶜ σ h M `cons substᶜ σ h N
  substᶜ σ h (recℕ V M N p)            =
    recℕ (substᵛ σ h V) (substᶜ σ h M) (substᶜ σ h N) (⊩-substₑ h p)
  substᶜ σ h (recL V M N p)            =
    recL (substᵛ σ h V) (substᶜ σ h M) (substᶜ σ h N) (⊩-substₑ h p)
  substᶜ {Γ = Γ} σ h (perform op V M)  =
    perform op (ty-subst (⌜⌝ᵍ-subst σ (param op)) (substᵛ σ h V))
               (ctx-castᶜ (cong (Γ [ σ ]ᶜᵗˣ ⟨ rconst ∣ op-grade op ∣ᵉ ⟩ ∷_)
                                (⌜⌝ᵍ-subst σ (arity op)))
                          (substᶜ σ h M))
  substᶜ σ h (delay τ M)               = delay τ (substᶜ σ h M)
  substᶜ σ h (handle M `with V)        = handle substᶜ σ h M `with substᵛ σ h V
  substᶜ σ h (unbox R p N)             =
    unbox (substʳ σ h R) (⊩-substᵣ h p) (substᶜ σ h N)
  substᶜ σ h (box ρ V N)               = box (ρ [ σ ]ʳ) (substᵛ σ h V) (substᶜ σ h N)
  substᶜ σ h (annᶜ C M)                = annᶜ (C [ σ ]ᶜ) (substᶜ σ h M)
  substᶜ σ h (subC M p)                = subC (substᶜ σ h M) (<:̂ᶜ-subst h p)

------------------------------------------------------------------------
-- The substituted derivation erases to the substituted raw term

mutual

  ⌊substᵛ⌋ : ∀ {Θ Θ' n} {Q : Hyps Θ} {Q' : Hyps Θ'} {Γ : OCtx Θ n} {A : OVType Θ}
           → (σ : Subst Θ Θ') → (h : Q' ⊩ᴴ Q [ σ ]) → (V : Q ∣ Γ ⊢V⦂ A)
           → ⌊ substᵛ σ h V ⌋ᵛ ≡ ⌊ V ⌋ᵛ [ σ ]ᴿᵛ

  ⌊substᵛ⌋ σ h (var x p)      = cong var (var-pos-∈̂-subst σ x)
  ⌊substᵛ⌋ σ h (usedef f δ h' e) = refl
  ⌊substᵛ⌋ σ h (const B c)    = refl
  ⌊substᵛ⌋ σ h ⋆              = refl
  ⌊substᵛ⌋ σ h true           = refl
  ⌊substᵛ⌋ σ h false          = refl
  ⌊substᵛ⌋ σ h zero           = refl
  ⌊substᵛ⌋ σ h (succ V)       = cong succ (⌊substᵛ⌋ σ h V)
  ⌊substᵛ⌋ σ h ⦉ V , W ⦊       = cong₂ ⦉_,_⦊ (⌊substᵛ⌋ σ h V) (⌊substᵛ⌋ σ h W)
  ⌊substᵛ⌋ σ h (inl V)        = cong inl (⌊substᵛ⌋ σ h V)
  ⌊substᵛ⌋ σ h (inr V)        = cong inr (⌊substᵛ⌋ σ h V)
  ⌊substᵛ⌋ σ h nil            = refl
  ⌊substᵛ⌋ σ h (cons V W)     = cong₂ cons (⌊substᵛ⌋ σ h V) (⌊substᵛ⌋ σ h W)
  ⌊substᵛ⌋ σ h (cmp ⋈ V W et) = cong₂ (cmp ⋈) (⌊substᵛ⌋ σ h V) (⌊substᵛ⌋ σ h W)
  ⌊substᵛ⌋ σ h (lam M)        = cong lam (⌊substᶜ⌋ σ h M)
  ⌊substᵛ⌋ {Γ = Γ} σ h (handler {B = B} N H) =
    cong₂ handler (⌊substᶜ⌋ σ h N) (fun-ext (λ op → ⌊substˡ⌋ σ h Γ B op (H op)))
  ⌊substᵛ⌋ σ h (annᵛ A V)     = cong (_⦂ᵛ A [ σ ]ᵛ) (⌊substᵛ⌋ σ h V)
  ⌊substᵛ⌋ σ h (subV V p)     = ⌊substᵛ⌋ σ h V

  ⌊substˡ⌋ : ∀ {Θ Θ' n} {Q : Hyps Θ} {Q' : Hyps Θ'}
           → (σ : Subst Θ Θ') → (h : Q' ⊩ᴴ Q [ σ ])
           → (Γ : OCtx Θ n) → (B : OVType Θ) → (op : Op)
           → (M : wkᵉ-H Q ∣ clause-ctx Γ B op ⊢C⦂ clause-ty B op)
           → ⌊ substˡ σ h Γ B op M ⌋ᶜ ≡ ⌊ M ⌋ᶜ [ σ ↑ᵉ ]ᴿᶜ
  ⌊substˡ⌋ σ h Γ B op M =
    trans (⌊c-subst⌋ (clause-ty-↑ σ B op) _)
          (trans (⌊ctx-castᶜ⌋ (clause-ctx-↑ σ Γ B op) _)
                 (⌊substᶜ⌋ (σ ↑ᵉ) (⊩ᴴ-↑ᵉ h) M))

  ⌊substᶜ⌋ : ∀ {Θ Θ' n} {Q : Hyps Θ} {Q' : Hyps Θ'} {Γ : OCtx Θ n} {C : OCType Θ}
           → (σ : Subst Θ Θ') → (h : Q' ⊩ᴴ Q [ σ ]) → (M : Q ∣ Γ ⊢C⦂ C)
           → ⌊ substᶜ σ h M ⌋ᶜ ≡ ⌊ M ⌋ᶜ [ σ ]ᴿᶜ

  ⌊substᶜ⌋ σ h (return V)                = cong return (⌊substᵛ⌋ σ h V)
  ⌊substᶜ⌋ σ h (M ⨟ N)                   = cong₂ _⨟_ (⌊substᶜ⌋ σ h M) (⌊substᶜ⌋ σ h N)
  ⌊substᶜ⌋ σ h (V · W)                   = cong₂ _·_ (⌊substᵛ⌋ σ h V) (⌊substᵛ⌋ σ h W)
  ⌊substᶜ⌋ σ h (match V `in M)           =
    cong₂ match_`in_ (⌊substᵛ⌋ σ h V) (⌊substᶜ⌋ σ h M)
  ⌊substᶜ⌋ σ h (absurd V)                = cong absurd (⌊substᵛ⌋ σ h V)
  ⌊substᶜ⌋ σ h (if V `then M `else N)    =
    cong₃ if_`then_`else_ (⌊substᵛ⌋ σ h V) (⌊substᶜ⌋ σ h M) (⌊substᶜ⌋ σ h N)
  ⌊substᶜ⌋ σ h (caseℕ V `zero M `succ N) =
    cong₃ caseℕ_`zero_`succ_ (⌊substᵛ⌋ σ h V) (⌊substᶜ⌋ σ h M) (⌊substᶜ⌋ σ h N)
  ⌊substᶜ⌋ σ h (case+ V `inl M `inr N)   =
    cong₃ case+_`inl_`inr_ (⌊substᵛ⌋ σ h V) (⌊substᶜ⌋ σ h M) (⌊substᶜ⌋ σ h N)
  ⌊substᶜ⌋ σ h (caseL V `nil M `cons N)  =
    cong₃ caseL_`nil_`cons_ (⌊substᵛ⌋ σ h V) (⌊substᶜ⌋ σ h M) (⌊substᶜ⌋ σ h N)
  ⌊substᶜ⌋ σ h (recℕ V M N p)            =
    cong₃ recℕ (⌊substᵛ⌋ σ h V) (⌊substᶜ⌋ σ h M) (⌊substᶜ⌋ σ h N)
  ⌊substᶜ⌋ σ h (recL V M N p)            =
    cong₃ recL (⌊substᵛ⌋ σ h V) (⌊substᶜ⌋ σ h M) (⌊substᶜ⌋ σ h N)
  ⌊substᶜ⌋ {Γ = Γ} σ h (perform op V M)  =
    cong₂ (perform op)
          (trans (⌊ty-subst⌋ (⌜⌝ᵍ-subst σ (param op)) _) (⌊substᵛ⌋ σ h V))
          (trans (⌊ctx-castᶜ⌋ (cong (Γ [ σ ]ᶜᵗˣ ⟨ rconst ∣ op-grade op ∣ᵉ ⟩ ∷_)
                                    (⌜⌝ᵍ-subst σ (arity op))) _)
                 (⌊substᶜ⌋ σ h M))
  ⌊substᶜ⌋ σ h (delay τ M)               = cong (delay τ) (⌊substᶜ⌋ σ h M)
  ⌊substᶜ⌋ σ h (handle M `with V)        =
    cong₂ handle_`with_ (⌊substᶜ⌋ σ h M) (⌊substᵛ⌋ σ h V)
  ⌊substᶜ⌋ σ h (unbox R p N)             =
    cong₂ unbox (⌊substʳ⌋ σ h R) (⌊substᶜ⌋ σ h N)
  ⌊substᶜ⌋ σ h (box ρ V N)               =
    cong₂ (box (ρ [ σ ]ʳ)) (⌊substᵛ⌋ σ h V) (⌊substᶜ⌋ σ h N)
  ⌊substᶜ⌋ σ h (annᶜ C M)                = cong (_⦂ᶜ C [ σ ]ᶜ) (⌊substᶜ⌋ σ h M)
  ⌊substᶜ⌋ σ h (subC M p)                = ⌊substᶜ⌋ σ h M

------------------------------------------------------------------------
-- Instantiating the variable of a handler clause

-- The clause context of `op` with its variable read as `ε`

clause-ctx-at : ∀ {Θ n} → OCtx Θ n → OVType Θ → Op → EExp Θ → OCtx Θ (suc (suc n))
clause-ctx-at Γ B op ε =
  Γ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
    ∷ [ rconst ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε)

clause-ctx-,ᵉ : ∀ {Θ n} → (Γ : OCtx Θ n) → (B : OVType Θ) → (op : Op) → (ε : EExp Θ)
              → clause-ctx Γ B op [ idˢ ,ᵉ ε ]ᶜᵗˣ ≡ clause-ctx-at Γ B op ε
clause-ctx-,ᵉ Γ B op ε =
  cong₂ _∷_
        (cong₂ _∷_ (cong (_⟨ rconst ⊤ᵣ ⟩) (trans (wk-,ᵉ-ctx idˢ ε Γ) ([id]ᶜᵗˣ Γ)))
                   (⌜⌝ᵍ-subst (idˢ ,ᵉ ε) (param op)))
        (cong₂ (λ A₀ B₀ → [ rconst ∣ op-grade op ∣ᵉ ] (A₀ ⇒ B₀ ! ε))
               (⌜⌝ᵍ-subst (idˢ ,ᵉ ε) (arity op))
               (trans (wk-,ᵉ-v idˢ ε B) ([id]ᵛ B)))

clause-ty-,ᵉ : ∀ {Θ} → (B : OVType Θ) → (op : Op) → (ε : EExp Θ)
             → clause-ty B op [ idˢ ,ᵉ ε ]ᶜ ≡ B ! (econst (op-grade op) ·̂ₑ ε)
clause-ty-,ᵉ B op ε = cong (_! _) (trans (wk-,ᵉ-v idˢ ε B) ([id]ᵛ B))

instantiate-clause : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {B : OVType Θ} {op : Op}
                   → (ε : EExp Θ)
                   → wkᵉ-H Q ∣ clause-ctx Γ B op ⊢C⦂ clause-ty B op
                   ------------------------------------------------------------------
                   → Q ∣ clause-ctx-at Γ B op ε ⊢C⦂ B ! (econst (op-grade op) ·̂ₑ ε)

instantiate-clause {Γ = Γ} {B} {op} ε M =
  c-subst (clause-ty-,ᵉ B op ε)
          (ctx-castᶜ (clause-ctx-,ᵉ Γ B op ε) (substᶜ (idˢ ,ᵉ ε) (⊩ᴴ-wkᵉ-,ᵉ ε) M))

⌊instantiate-clause⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {B : OVType Θ} {op : Op}
                     → (ε : EExp Θ)
                     → (M : wkᵉ-H Q ∣ clause-ctx Γ B op ⊢C⦂ clause-ty B op)
                     → ⌊ instantiate-clause ε M ⌋ᶜ ≡ ⌊ M ⌋ᶜ [ idˢ ,ᵉ ε ]ᴿᶜ
⌊instantiate-clause⌋ {Γ = Γ} {B} {op} ε M =
  trans (⌊c-subst⌋ (clause-ty-,ᵉ B op ε) _)
        (trans (⌊ctx-castᶜ⌋ (clause-ctx-,ᵉ Γ B op ε) _)
               (⌊substᶜ⌋ (idˢ ,ᵉ ε) (⊩ᴴ-wkᵉ-,ᵉ ε) M))
