------------------------------------------------------------------
-- Inversion of open derivations at a run-time term             --
--                                                              --
-- A derivation of a value or computation is the rule of its    --
-- term's former under subsumptions and annotations: `invV` and --
-- `invC` give the premises of that rule, at a type below the   --
-- derivation's (`HeadV`, `HeadC`), the premises' erasures      --
-- being the term's parts.                                      --
--                                                              --
-- In a context of box-typed variables, a value of a data,      --
-- function or handler type is an introduction form (`canon-*`).--
------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Typing.Inversion (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OpenCalculus.Syntax.Grades         S
open import OpenCalculus.Syntax.Types          S
open import OpenCalculus.Syntax.Contexts       S
open import OpenCalculus.Hypotheses            S
open import OpenCalculus.Typing                S
open import OpenCalculus.Typing.Erasure        S
open import OpenCalculus.Typing.GradeSubstitution S using (clause-ctx; clause-ty)
open import OpenCalculus.Typing.Renaming       S using (∥_∥ᵛ; ∥_∥ᶜ)
open import OpenCalculus.Syntax.Run            S

module _ {Θ : Scope} (Q : Hyps Θ) where

  -- The premises of the rule of a value's former, at a type

  HeadV : ∀ {n} → OCtx Θ n → RunV n → OVType Θ → Set
  HeadV Γ (var i)       T = Σ[ ρ ∈ RExp Θ ] Σ[ x ∈ T ∈̂[ ρ ] Γ ] (var-pos x ≡ i) × VarOK Q T ρ
  HeadV Γ (const B c)   T = T ≡ Base B
  HeadV Γ ⋆             T = T ≡ Unit
  HeadV Γ true          T = T ≡ Bool
  HeadV Γ false         T = T ≡ Bool
  HeadV Γ zero          T = T ≡ Nat
  HeadV Γ (succ V)      T = (T ≡ Nat) × Σ[ D ∈ Q ∣ Γ ⊢V⦂ Nat ] ∥ D ∥ᵛ ≡ V
  HeadV Γ ⦉ V , W ⦊      T =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ] (T ≡ A |×| B)
      × (Σ[ D ∈ Q ∣ Γ ⊢V⦂ A ] ∥ D ∥ᵛ ≡ V) × (Σ[ E ∈ Q ∣ Γ ⊢V⦂ B ] ∥ E ∥ᵛ ≡ W)
  HeadV Γ (inl V)       T =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ] (T ≡ A |+| B) × (Σ[ D ∈ Q ∣ Γ ⊢V⦂ A ] ∥ D ∥ᵛ ≡ V)
  HeadV Γ (inr V)       T =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ] (T ≡ A |+| B) × (Σ[ D ∈ Q ∣ Γ ⊢V⦂ B ] ∥ D ∥ᵛ ≡ V)
  HeadV Γ nil           T = Σ[ A ∈ OVType Θ ] T ≡ |List| A
  HeadV Γ (cons V W)    T =
    Σ[ A ∈ OVType Θ ] (T ≡ |List| A)
      × (Σ[ D ∈ Q ∣ Γ ⊢V⦂ A ] ∥ D ∥ᵛ ≡ V) × (Σ[ E ∈ Q ∣ Γ ⊢V⦂ |List| A ] ∥ E ∥ᵛ ≡ W)
  HeadV Γ (cmp ⋈ V W)   T =
    (T ≡ Bool) × Σ[ A ∈ OVType Θ ] (Q ⊩ᴱ A)
      × (Σ[ D ∈ Q ∣ Γ ⊢V⦂ A ] ∥ D ∥ᵛ ≡ V) × (Σ[ E ∈ Q ∣ Γ ⊢V⦂ A ] ∥ E ∥ᵛ ≡ W)
  HeadV Γ (lam M)       T =
    Σ[ A ∈ OVType Θ ] Σ[ C ∈ OCType Θ ] (T ≡ A ⇒ C) × (Σ[ D ∈ Q ∣ Γ ∷ A ⊢C⦂ C ] ∥ D ∥ᶜ ≡ M)
  HeadV Γ (handler N H) T =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ] Σ[ ε ∈ EExp Θ ] Σ[ ε' ∈ EExp Θ ]
      (T ≡ (A ‼ ε) ⇛ (B ‼ ε'))
      × (Σ[ D ∈ Q ∣ Γ ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ A ⊢C⦂ B ‼ ε' ] ∥ D ∥ᶜ ≡ N)
      × (Σ[ E ∈ ((op : Op) → wkᵉ-H Q ∣ clause-ctx Γ B op ⊢C⦂ clause-ty B op) ]
           ((op : Op) → ∥ E op ∥ᶜ ≡ H op))

  InvV : ∀ {n} → OCtx Θ n → RunV n → OVType Θ → Set
  InvV Γ V T = Σ[ T₀ ∈ OVType Θ ] HeadV Γ V T₀ × Q ∣ T₀ <:̂ᵛ T

  -- The premises of the rule of a computation's former, at a type

  HeadC : ∀ {n} → OCtx Θ n → RunC n → OCType Θ → Set
  HeadC Γ (return V)                C =
    Σ[ A ∈ OVType Θ ] (C ≡ A ‼ ûₑ) × (Σ[ D ∈ Q ∣ Γ ⊢V⦂ A ] ∥ D ∥ᵛ ≡ V)
  HeadC Γ (M ⨟ N)                   C =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ] Σ[ ε ∈ EExp Θ ] Σ[ ε' ∈ EExp Θ ]
      (C ≡ B ‼ (ε ·̂ₑ ε'))
      × (Σ[ D ∈ Q ∣ Γ ⊢C⦂ A ‼ ε ] ∥ D ∥ᶜ ≡ M)
      × (Σ[ E ∈ Q ∣ Γ ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ A ⊢C⦂ B ‼ ε' ] ∥ E ∥ᶜ ≡ N)
  HeadC Γ (V · W)                   C =
    Σ[ A ∈ OVType Θ ] (Σ[ D ∈ Q ∣ Γ ⊢V⦂ A ⇒ C ] ∥ D ∥ᵛ ≡ V) × (Σ[ E ∈ Q ∣ Γ ⊢V⦂ A ] ∥ E ∥ᵛ ≡ W)
  HeadC Γ (match V `in M)           C =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ]
      (Σ[ D ∈ Q ∣ Γ ⊢V⦂ A |×| B ] ∥ D ∥ᵛ ≡ V) × (Σ[ E ∈ Q ∣ Γ ∷ A ∷ B ⊢C⦂ C ] ∥ E ∥ᶜ ≡ M)
  HeadC Γ (absurd V)                C = Σ[ D ∈ Q ∣ Γ ⊢V⦂ Empty ] ∥ D ∥ᵛ ≡ V
  HeadC Γ (if V `then M `else N)    C =
    (Σ[ D ∈ Q ∣ Γ ⊢V⦂ Bool ] ∥ D ∥ᵛ ≡ V)
      × (Σ[ E ∈ Q ∣ Γ ⊢C⦂ C ] ∥ E ∥ᶜ ≡ M) × (Σ[ F ∈ Q ∣ Γ ⊢C⦂ C ] ∥ F ∥ᶜ ≡ N)
  HeadC Γ (caseℕ V `zero M `succ N) C =
    (Σ[ D ∈ Q ∣ Γ ⊢V⦂ Nat ] ∥ D ∥ᵛ ≡ V)
      × (Σ[ E ∈ Q ∣ Γ ⊢C⦂ C ] ∥ E ∥ᶜ ≡ M) × (Σ[ F ∈ Q ∣ Γ ∷ Nat ⊢C⦂ C ] ∥ F ∥ᶜ ≡ N)
  HeadC Γ (case+ V `inl M `inr N)   C =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ]
      (Σ[ D ∈ Q ∣ Γ ⊢V⦂ A |+| B ] ∥ D ∥ᵛ ≡ V)
      × (Σ[ E ∈ Q ∣ Γ ∷ A ⊢C⦂ C ] ∥ E ∥ᶜ ≡ M) × (Σ[ F ∈ Q ∣ Γ ∷ B ⊢C⦂ C ] ∥ F ∥ᶜ ≡ N)
  HeadC Γ (caseL V `nil M `cons N)  C =
    Σ[ A ∈ OVType Θ ]
      (Σ[ D ∈ Q ∣ Γ ⊢V⦂ |List| A ] ∥ D ∥ᵛ ≡ V)
      × (Σ[ E ∈ Q ∣ Γ ⊢C⦂ C ] ∥ E ∥ᶜ ≡ M)
      × (Σ[ F ∈ Q ∣ Γ ∷ A ∷ |List| A ⊢C⦂ C ] ∥ F ∥ᶜ ≡ N)
  HeadC Γ (recℕ V M N)              C =
    Σ[ B ∈ OVType Θ ] Σ[ ε ∈ EExp Θ ] (C ≡ B ‼ ε)
      × (Σ[ D ∈ Q ∣ Γ ⊢V⦂ Nat ] ∥ D ∥ᵛ ≡ V)
      × (Σ[ E ∈ Q ∣ Γ ⊢C⦂ B ‼ ε ] ∥ E ∥ᶜ ≡ M)
      × (Σ[ F ∈ Q ∣ (Γ ⟨ rconst ⊤ᵣ ⟩ ∷ Nat) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B ⊢C⦂ B ‼ ε ] ∥ F ∥ᶜ ≡ N)
      × (Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε)
  HeadC Γ (recL V M N)              C =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ] Σ[ ε ∈ EExp Θ ] (C ≡ B ‼ ε)
      × (Σ[ D ∈ Q ∣ Γ ⊢V⦂ |List| A ] ∥ D ∥ᵛ ≡ V)
      × (Σ[ E ∈ Q ∣ Γ ⊢C⦂ B ‼ ε ] ∥ E ∥ᶜ ≡ M)
      × (Σ[ F ∈ Q ∣ (Γ ⟨ rconst ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B ⊢C⦂ B ‼ ε ]
           ∥ F ∥ᶜ ≡ N)
      × (Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε)
  HeadC Γ (perform op V M)          C =
    Σ[ A ∈ OVType Θ ] Σ[ ε ∈ EExp Θ ] (C ≡ A ‼ (econst (op-grade op) ·̂ₑ ε))
      × (Σ[ D ∈ Q ∣ Γ ⊢V⦂ ⌜ param op ⌝ᵍ ] ∥ D ∥ᵛ ≡ V)
      × (Σ[ E ∈ Q ∣ Γ ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ A ‼ ε ]
           ∥ E ∥ᶜ ≡ M)
  HeadC Γ (delay τ M)               C =
    Σ[ A ∈ OVType Θ ] Σ[ ε ∈ EExp Θ ] (C ≡ A ‼ (econst (of-durᵉ τ) ·̂ₑ ε))
      × (Σ[ D ∈ Q ∣ Γ ⟨ rconst (of-durʳ τ) ⟩ ⊢C⦂ A ‼ ε ] ∥ D ∥ᶜ ≡ M)
  HeadC Γ (handle M `with V)        C =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ] Σ[ ε ∈ EExp Θ ] Σ[ ε' ∈ EExp Θ ]
      (C ≡ B ‼ (ε ·̂ₑ ε'))
      × (Σ[ D ∈ Q ∣ Γ ⊢C⦂ A ‼ ε ] ∥ D ∥ᶜ ≡ M)
      × (Σ[ E ∈ Q ∣ Γ ⊢V⦂ (A ‼ ε) ⇛ (B ‼ ε') ] ∥ E ∥ᵛ ≡ V)
  HeadC Γ (unbox V N)               C =
    Σ[ ρ₀ ∈ RExp Θ ] Σ[ A₀ ∈ OVType Θ ] Σ[ ρ' ∈ RExp Θ ] Σ[ A ∈ OVType Θ ]
      Σ[ x ∈ [ ρ₀ ] A₀ ∈̂[ ρ' ] Γ ] (V ≡ var (var-pos x))
      × (Q ⊩ ρ' ≾̂ᵣ ρ₀) × (Q ∣ A₀ <:̂ᵛ A)
      × (Σ[ D ∈ Q ∣ Γ ∷ A ⊢C⦂ C ] ∥ D ∥ᶜ ≡ N)
  HeadC Γ (box V N)                 C =
    Σ[ ρ ∈ RExp Θ ] Σ[ A ∈ OVType Θ ]
      (Σ[ D ∈ Q ∣ Γ ⟨ ρ ⟩ ⊢V⦂ A ] ∥ D ∥ᵛ ≡ V) × (Σ[ E ∈ Q ∣ Γ ∷ [ ρ ] A ⊢C⦂ C ] ∥ E ∥ᶜ ≡ N)

  InvC : ∀ {n} → OCtx Θ n → RunC n → OCType Θ → Set
  InvC Γ M C = Σ[ C₀ ∈ OCType Θ ] HeadC Γ M C₀ × Q ∣ C₀ <:̂ᶜ C

module _ {Θ : Scope} {Q : Hyps Θ} where

  invV : ∀ {n} {Γ : OCtx Θ n} {T : OVType Θ} → (D : Q ∣ Γ ⊢V⦂ T) → InvV Q Γ ∥ D ∥ᵛ T
  invV {T = T} (var x p)        = T , (_ , x , refl , p) , <:̂ᵛ-refl T
  invV (const B c)              = _ , refl , <:̂ᵛ-refl _
  invV ⋆                        = _ , refl , <:̂ᵛ-refl _
  invV true                     = _ , refl , <:̂ᵛ-refl _
  invV false                    = _ , refl , <:̂ᵛ-refl _
  invV zero                     = _ , refl , <:̂ᵛ-refl _
  invV (succ V)                 = _ , (refl , V , refl) , <:̂ᵛ-refl _
  invV ⦉ V , W ⦊                 = _ , (_ , _ , refl , (V , refl) , (W , refl)) , <:̂ᵛ-refl _
  invV (inl V)                  = _ , (_ , _ , refl , (V , refl)) , <:̂ᵛ-refl _
  invV (inr V)                  = _ , (_ , _ , refl , (V , refl)) , <:̂ᵛ-refl _
  invV nil                      = _ , (_ , refl) , <:̂ᵛ-refl _
  invV (cons V W)               = _ , (_ , refl , (V , refl) , (W , refl)) , <:̂ᵛ-refl _
  invV (cmp ⋈ V W et)           = _ , (refl , _ , et , (V , refl) , (W , refl)) , <:̂ᵛ-refl _
  invV (lam M)                  = _ , (_ , _ , refl , (M , refl)) , <:̂ᵛ-refl _
  invV (handler N H)            =
    _ , (_ , _ , _ , _ , refl , (N , refl) , (H , λ op → refl)) , <:̂ᵛ-refl _
  invV (annᵛ A V)               = invV V
  invV (subV V p) with invV V
  ... | T₀ , h , q              = T₀ , h , <:̂ᵛ-trans q p

  invC : ∀ {n} {Γ : OCtx Θ n} {C : OCType Θ} → (D : Q ∣ Γ ⊢C⦂ C) → InvC Q Γ ∥ D ∥ᶜ C
  invC (return V)                = _ , (_ , refl , (V , refl)) , <:̂ᶜ-refl _
  invC (M ⨟ N)                   = _ , (_ , _ , _ , _ , refl , (M , refl) , (N , refl)) , <:̂ᶜ-refl _
  invC (V · W)                   = _ , (_ , (V , refl) , (W , refl)) , <:̂ᶜ-refl _
  invC (match V `in M)           = _ , (_ , _ , (V , refl) , (M , refl)) , <:̂ᶜ-refl _
  invC (absurd V)                = _ , (V , refl) , <:̂ᶜ-refl _
  invC (if V `then M `else N)    = _ , ((V , refl) , (M , refl) , (N , refl)) , <:̂ᶜ-refl _
  invC (caseℕ V `zero M `succ N) = _ , ((V , refl) , (M , refl) , (N , refl)) , <:̂ᶜ-refl _
  invC (case+ V `inl M `inr N)   = _ , (_ , _ , (V , refl) , (M , refl) , (N , refl)) , <:̂ᶜ-refl _
  invC (caseL V `nil M `cons N)  = _ , (_ , (V , refl) , (M , refl) , (N , refl)) , <:̂ᶜ-refl _
  invC (recℕ V M N p)            =
    _ , (_ , _ , refl , (V , refl) , (M , refl) , (N , refl) , p) , <:̂ᶜ-refl _
  invC (recL V M N p)            =
    _ , (_ , _ , _ , refl , (V , refl) , (M , refl) , (N , refl) , p) , <:̂ᶜ-refl _
  invC (perform op V M)          = _ , (_ , _ , refl , (V , refl) , (M , refl)) , <:̂ᶜ-refl _
  invC (delay τ M)               = _ , (_ , _ , refl , (M , refl)) , <:̂ᶜ-refl _
  invC (handle M `with V)        =
    _ , (_ , _ , _ , _ , refl , (M , refl) , (V , refl)) , <:̂ᶜ-refl _
  invC (unbox x p q N)           = _ , (_ , _ , _ , _ , x , refl , p , q , (N , refl)) , <:̂ᶜ-refl _
  invC (box ρ V N)               = _ , (_ , _ , (V , refl) , (N , refl)) , <:̂ᶜ-refl _
  invC (annᶜ C M)                = invC M
  invC (subC M p) with invC M
  ... | C₀ , h , q               = C₀ , h , <:̂ᶜ-trans q p

  -- inversion at a term the erasure is equal to

  invV≡ : ∀ {n} {Γ : OCtx Θ n} {T : OVType Θ} {V : RunV n}
        → (D : Q ∣ Γ ⊢V⦂ T) → ∥ D ∥ᵛ ≡ V → InvV Q Γ V T
  invV≡ D refl = invV D

  invC≡ : ∀ {n} {Γ : OCtx Θ n} {C : OCType Θ} {M : RunC n}
        → (D : Q ∣ Γ ⊢C⦂ C) → ∥ D ∥ᶜ ≡ M → InvC Q Γ M C
  invC≡ D refl = invC D

------------------------------------------------------------------------
-- Canonical forms in a context of box-typed variables

-- The forms of the values of each type

module _ {n : ℕ} where

  data LamView : RunV n → Set where
    is-lam : ∀ M → LamView (lam M)

  data HandlerView : RunV n → Set where
    is-handler : ∀ N H → HandlerView (handler N H)

  data PairView : RunV n → Set where
    is-pair : ∀ V W → PairView ⦉ V , W ⦊

  data SumView : RunV n → Set where
    is-inl : ∀ V → SumView (inl V)
    is-inr : ∀ V → SumView (inr V)

  data ListView : RunV n → Set where
    is-nil  : ListView nil
    is-cons : ∀ V W → ListView (cons V W)

  data NatView : RunV n → Set where
    is-zero : NatView zero
    is-succ : ∀ V → NatView (succ V)

  data BoolView : RunV n → Set where
    is-true  : BoolView true
    is-false : BoolView false
    is-cmp   : ∀ ⋈ V W → BoolView (cmp ⋈ V W)

  data VarView : RunV n → Set where
    is-var : ∀ i → VarView (var i)

  handler-form : ∀ {V} → HandlerView V
               → Σ[ N ∈ RunC (suc n) ] Σ[ H ∈ (Op → RunC (suc (suc n))) ] V ≡ handler N H
  handler-form (is-handler N H) = N , H , refl

BoxCtx : ∀ {Θ n} → OCtx Θ n → Set
BoxCtx {Θ} Γ = ∀ {A ρ} → A ∈̂[ ρ ] Γ → Σ[ ρ₀ ∈ RExp Θ ] Σ[ A₀ ∈ OVType Θ ] A ≡ [ ρ₀ ] A₀

module _ {Θ : Scope} {n : ℕ} {Q : Hyps Θ} {Γ : OCtx Θ n} (bx : BoxCtx Γ) where

  private
    no-var : ∀ {A ρ} {P : Set} → A ∈̂[ ρ ] Γ → (∀ {ρ₀ A₀} → A ≡ [ ρ₀ ] A₀ → ⊥) → P
    no-var x f with bx x
    ... | _ , _ , e = ⊥-elim (f e)

  canon-⇒ : ∀ {A C} → (D : Q ∣ Γ ⊢V⦂ A ⇒ C) → LamView ∥ D ∥ᵛ
  canon-⇒ (var x p)          = no-var x (λ ())
  canon-⇒ (lam M)            = is-lam _
  canon-⇒ (annᵛ _ D)         = canon-⇒ D
  canon-⇒ (subV D (p ⇒ₛ q))  = canon-⇒ D

  canon-⇛ : ∀ {C D'} → (D : Q ∣ Γ ⊢V⦂ C ⇛ D') → HandlerView ∥ D ∥ᵛ
  canon-⇛ (var x p)          = no-var x (λ ())
  canon-⇛ (handler N H)      = is-handler _ _
  canon-⇛ (annᵛ _ D)         = canon-⇛ D
  canon-⇛ (subV D (p ⇛ₛ q))  = canon-⇛ D

  canon-× : ∀ {A B} → (D : Q ∣ Γ ⊢V⦂ A |×| B) → PairView ∥ D ∥ᵛ
  canon-× (var x p)          = no-var x (λ ())
  canon-× ⦉ V , W ⦊           = is-pair _ _
  canon-× (annᵛ _ D)         = canon-× D
  canon-× (subV D (p |×|ₛ q)) = canon-× D

  canon-+ : ∀ {A B} → (D : Q ∣ Γ ⊢V⦂ A |+| B) → SumView ∥ D ∥ᵛ
  canon-+ (var x p)          = no-var x (λ ())
  canon-+ (inl V)            = is-inl _
  canon-+ (inr V)            = is-inr _
  canon-+ (annᵛ _ D)         = canon-+ D
  canon-+ (subV D (p |+|ₛ q)) = canon-+ D

  canon-List : ∀ {A} → (D : Q ∣ Γ ⊢V⦂ |List| A) → ListView ∥ D ∥ᵛ
  canon-List (var x p)          = no-var x (λ ())
  canon-List nil                = is-nil
  canon-List (cons V W)         = is-cons _ _
  canon-List (annᵛ _ D)         = canon-List D
  canon-List (subV D (|List|ₛ p)) = canon-List D

  canon-Nat : (D : Q ∣ Γ ⊢V⦂ Nat) → NatView ∥ D ∥ᵛ
  canon-Nat (var x p)        = no-var x (λ ())
  canon-Nat zero             = is-zero
  canon-Nat (succ V)         = is-succ _
  canon-Nat (annᵛ _ D)       = canon-Nat D
  canon-Nat (subV D Natₛ)    = canon-Nat D

  canon-Bool : (D : Q ∣ Γ ⊢V⦂ Bool) → BoolView ∥ D ∥ᵛ
  canon-Bool (var x p)        = no-var x (λ ())
  canon-Bool true             = is-true
  canon-Bool false            = is-false
  canon-Bool (cmp ⋈ V W et)   = is-cmp _ _ _
  canon-Bool (annᵛ _ D)       = canon-Bool D
  canon-Bool (subV D Boolₛ)   = canon-Bool D

  canon-Empty : (D : Q ∣ Γ ⊢V⦂ Empty) → ⊥
  canon-Empty (var x p)       = no-var x (λ ())
  canon-Empty (annᵛ _ D)      = canon-Empty D
  canon-Empty (subV D Emptyₛ) = canon-Empty D

canon-box : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ A}
          → (D : Q ∣ Γ ⊢V⦂ [ ρ ] A) → VarView ∥ D ∥ᵛ
canon-box (var x p)          = is-var _
canon-box (annᵛ _ D)         = canon-box D
canon-box (subV D ([ p ]ₛ q)) = canon-box D
