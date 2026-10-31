------------------------------------------------------------------
-- Inversion of open derivations at a run-time term             --
--                                                              --
-- `invV` and `invC` give the premises of the rule of a term's  --
-- former, at a type below the derivation's (`HeadV`, `HeadC`), --
-- with erasures the term's parts. In a context of box-typed    --
-- variables and no definitions, a value of a data, function or --
-- handler type is an introduction form (`canon-*`).            --
------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Typing.Inversion (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.Contexts          S
open import PolymorphicCalculus.Syntax.GradeSubstitution S using (Subst; _[_]ᵛ)
open import PolymorphicCalculus.Hypotheses               S
open import PolymorphicCalculus.Typing                   S
open import PolymorphicCalculus.Typing.Erasure           S
open import PolymorphicCalculus.Typing.GradeSubstitution S using (clause-ctx; clause-ty)
open import PolymorphicCalculus.Typing.Renaming          S using (∥_∥ᵛ; ∥_∥ᶜ)
open import PolymorphicCalculus.Syntax.Run               S

module _ {Θ : Scope} (Q : Hyps Θ) where

  -- The premises of the rule of a value's former, at a type

  HeadV : ∀ {n} → OCtx Θ n → RunV n → OVType Θ → Set
  HeadV Γ (var i)       T = Σ[ ρ ∈ RExp Θ ] Σ[ x ∈ T ∈̂[ ρ ] Γ ] (var-pos x ≡ i) × Q ⊩ T Et∨≾ᵘ ρ
  HeadV Γ (usedef k)    T =
    Σ[ s ∈ Scheme ] Σ[ f ∈ s ∈ᵖ[ k ] defs Γ ] Σ[ δ ∈ Subst (Θˢ s) Θ ]
      (Q ⊩ᴴ Qˢ s [ δ ]) × (T ≡ Xˢ s [ δ ]ᵛ)
  HeadV Γ (const B c)   T = T ≡ Base B
  HeadV Γ ⋆             T = T ≡ unit
  HeadV Γ true          T = T ≡ bool
  HeadV Γ false         T = T ≡ bool
  HeadV Γ zero          T = T ≡ nat
  HeadV Γ (succ V)      T = (T ≡ nat) × Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ nat ] ∥ D ∥ᵛ ≡ V
  HeadV Γ ⦉ V , W ⦊      T =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ] (T ≡ A |×| B)
      × (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ A ] ∥ D ∥ᵛ ≡ V) × (Σ[ E ∈ Q ∣ Γ ⊢ᵛ⦂ B ] ∥ E ∥ᵛ ≡ W)
  HeadV Γ (inl V)       T =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ] (T ≡ A |+| B) × (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ A ] ∥ D ∥ᵛ ≡ V)
  HeadV Γ (inr V)       T =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ] (T ≡ A |+| B) × (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ B ] ∥ D ∥ᵛ ≡ V)
  HeadV Γ nil           T = Σ[ A ∈ OVType Θ ] T ≡ list A
  HeadV Γ (cons V W)    T =
    Σ[ A ∈ OVType Θ ] (T ≡ list A)
      × (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ A ] ∥ D ∥ᵛ ≡ V) × (Σ[ E ∈ Q ∣ Γ ⊢ᵛ⦂ list A ] ∥ E ∥ᵛ ≡ W)
  HeadV Γ (cmp ⋈ V W)   T =
    (T ≡ bool) × Σ[ A ∈ OVType Θ ] (Q ⊩Et A)
      × (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ A ] ∥ D ∥ᵛ ≡ V) × (Σ[ E ∈ Q ∣ Γ ⊢ᵛ⦂ A ] ∥ E ∥ᵛ ≡ W)
  HeadV Γ (fun M)       T =
    Σ[ A ∈ OVType Θ ] Σ[ C ∈ OCType Θ ] (T ≡ A ⇒ C) × (Σ[ D ∈ Q ∣ Γ ∷ A ⊢ᶜ⦂ C ] ∥ D ∥ᶜ ≡ M)
  HeadV Γ (handler N H) T =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ] Σ[ ε ∈ EExp Θ ] Σ[ ε' ∈ EExp Θ ]
      (T ≡ (A ! ε) ⇛ (B ! ε'))
      × (Σ[ D ∈ Q ∣ Γ ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε' ] ∥ D ∥ᶜ ≡ N)
      × (Σ[ E ∈ ((op : Op) → wkᵉ-H Q ∣ clause-ctx Γ B op ⊢ᶜ⦂ clause-ty B op) ]
           ((op : Op) → ∥ E op ∥ᶜ ≡ H op))

  InvV : ∀ {n} → OCtx Θ n → RunV n → OVType Θ → Set
  InvV Γ V T = Σ[ T₀ ∈ OVType Θ ] HeadV Γ V T₀ × Q ⊩ T₀ <:̂ᵛ T

  -- The premises of the rule of a computation's former, at a type

  HeadC : ∀ {n} → OCtx Θ n → RunC n → OCType Θ → Set
  HeadC Γ (return V)                 C =
    Σ[ A ∈ OVType Θ ] (C ≡ A ! 𝟏̂ₑ) × (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ A ] ∥ D ∥ᵛ ≡ V)
  HeadC Γ (M ⨟ N)                    C =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ] Σ[ ε ∈ EExp Θ ] Σ[ ε' ∈ EExp Θ ]
      (C ≡ B ! (ε ·̂ₑ ε'))
      × (Σ[ D ∈ Q ∣ Γ ⊢ᶜ⦂ A ! ε ] ∥ D ∥ᶜ ≡ M)
      × (Σ[ E ∈ Q ∣ Γ ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε' ] ∥ E ∥ᶜ ≡ N)
  HeadC Γ (V · W)                    C =
    Σ[ A ∈ OVType Θ ] (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ A ⇒ C ] ∥ D ∥ᵛ ≡ V) × (Σ[ E ∈ Q ∣ Γ ⊢ᵛ⦂ A ] ∥ E ∥ᵛ ≡ W)
  HeadC Γ (match V `with M)          C =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ]
      (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ A |×| B ] ∥ D ∥ᵛ ≡ V) × (Σ[ E ∈ Q ∣ Γ ∷ A ∷ B ⊢ᶜ⦂ C ] ∥ E ∥ᶜ ≡ M)
  HeadC Γ (absurd V)                 C = Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ empty ] ∥ D ∥ᵛ ≡ V
  HeadC Γ (if V `then M `else N)     C =
    (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ bool ] ∥ D ∥ᵛ ≡ V)
      × (Σ[ E ∈ Q ∣ Γ ⊢ᶜ⦂ C ] ∥ E ∥ᶜ ≡ M) × (Σ[ F ∈ Q ∣ Γ ⊢ᶜ⦂ C ] ∥ F ∥ᶜ ≡ N)
  HeadC Γ (matchℕ V `zero M `succ N) C =
    (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ nat ] ∥ D ∥ᵛ ≡ V)
      × (Σ[ E ∈ Q ∣ Γ ⊢ᶜ⦂ C ] ∥ E ∥ᶜ ≡ M) × (Σ[ F ∈ Q ∣ Γ ∷ nat ⊢ᶜ⦂ C ] ∥ F ∥ᶜ ≡ N)
  HeadC Γ (match+ V `inl M `inr N)   C =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ]
      (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ A |+| B ] ∥ D ∥ᵛ ≡ V)
      × (Σ[ E ∈ Q ∣ Γ ∷ A ⊢ᶜ⦂ C ] ∥ E ∥ᶜ ≡ M) × (Σ[ F ∈ Q ∣ Γ ∷ B ⊢ᶜ⦂ C ] ∥ F ∥ᶜ ≡ N)
  HeadC Γ (matchL V `nil M `cons N)  C =
    Σ[ A ∈ OVType Θ ]
      (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ list A ] ∥ D ∥ᵛ ≡ V)
      × (Σ[ E ∈ Q ∣ Γ ⊢ᶜ⦂ C ] ∥ E ∥ᶜ ≡ M)
      × (Σ[ F ∈ Q ∣ Γ ∷ A ∷ list A ⊢ᶜ⦂ C ] ∥ F ∥ᶜ ≡ N)
  HeadC Γ (recℕ V M N)               C =
    Σ[ B ∈ OVType Θ ] Σ[ ε ∈ EExp Θ ] (C ≡ B ! ε)
      × (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ nat ] ∥ D ∥ᵛ ≡ V)
      × (Σ[ E ∈ Q ∣ Γ ⊢ᶜ⦂ B ! ε ] ∥ E ∥ᶜ ≡ M)
      × (Σ[ F ∈ Q ∣ (Γ ⟨ rconst ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε ] ∥ F ∥ᶜ ≡ N)
      × (Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε)
  HeadC Γ (recL V M N)               C =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ] Σ[ ε ∈ EExp Θ ] (C ≡ B ! ε)
      × (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ list A ] ∥ D ∥ᵛ ≡ V)
      × (Σ[ E ∈ Q ∣ Γ ⊢ᶜ⦂ B ! ε ] ∥ E ∥ᶜ ≡ M)
      × (Σ[ F ∈ Q ∣ (Γ ⟨ rconst ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε ]
           ∥ F ∥ᶜ ≡ N)
      × (Q ⊩ ε ·̂ₑ ε ≾̂ₑ ε)
  HeadC Γ (perform op V M)           C =
    Σ[ A ∈ OVType Θ ] Σ[ ε ∈ EExp Θ ] (C ≡ A ! (econst (op-grade op) ·̂ₑ ε))
      × (Σ[ D ∈ Q ∣ Γ ⊢ᵛ⦂ ⌜ param op ⌝ᵍ ] ∥ D ∥ᵛ ≡ V)
      × (Σ[ E ∈ Q ∣ Γ ⟨ rconst ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ A ! ε ]
           ∥ E ∥ᶜ ≡ M)
  HeadC Γ (delay τ M)                C =
    Σ[ A ∈ OVType Θ ] Σ[ ε ∈ EExp Θ ] (C ≡ A ! (econst (ιₑ τ) ·̂ₑ ε))
      × (Σ[ D ∈ Q ∣ Γ ⟨ rconst (ιᵣ τ) ⟩ ⊢ᶜ⦂ A ! ε ] ∥ D ∥ᶜ ≡ M)
  HeadC Γ (handle M `with V)         C =
    Σ[ A ∈ OVType Θ ] Σ[ B ∈ OVType Θ ] Σ[ ε ∈ EExp Θ ] Σ[ ε' ∈ EExp Θ ]
      (C ≡ B ! (ε ·̂ₑ ε'))
      × (Σ[ D ∈ Q ∣ Γ ⊢ᶜ⦂ A ! ε ] ∥ D ∥ᶜ ≡ M)
      × (Σ[ E ∈ Q ∣ Γ ⊢ᵛ⦂ (A ! ε) ⇛ (B ! ε') ] ∥ E ∥ᵛ ≡ V)
  HeadC Γ (unbox V N)                C =
    Σ[ ρ' ∈ RExp Θ ] Σ[ ρ ∈ RExp Θ ] Σ[ X ∈ OVType Θ ]
      (Σ[ R ∈ Q ⊢ [ ρ ] X ∈̂[ ρ' ] Γ ] eraseᵛ ⌊ R ⌋ʳ ≡ V)
      × (Q ⊩ ρ' ≾̂ᵣ ρ)
      × (Σ[ D ∈ Q ∣ Γ ∷ X ⊢ᶜ⦂ C ] ∥ D ∥ᶜ ≡ N)
  HeadC Γ (box V N)                  C =
    Σ[ ρ ∈ RExp Θ ] Σ[ A ∈ OVType Θ ]
      (Σ[ D ∈ Q ∣ Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A ] ∥ D ∥ᵛ ≡ V) × (Σ[ E ∈ Q ∣ Γ ∷ [ ρ ] A ⊢ᶜ⦂ C ] ∥ E ∥ᶜ ≡ N)

  InvC : ∀ {n} → OCtx Θ n → RunC n → OCType Θ → Set
  InvC Γ M C = Σ[ C₀ ∈ OCType Θ ] HeadC Γ M C₀ × Q ⊩ C₀ <:̂ᶜ C

module _ {Θ : Scope} {Q : Hyps Θ} where

  invV : ∀ {n} {Γ : OCtx Θ n} {T : OVType Θ} → (D : Q ∣ Γ ⊢ᵛ⦂ T) → InvV Q Γ ∥ D ∥ᵛ T
  invV {T = T} (var x p)        = T , (_ , x , refl , p) , <:̂ᵛ-refl T
  invV {T = T} (usedef f δ h e) = T , (_ , f , δ , h , e) , <:̂ᵛ-refl T
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
  invV (fun M)                  = _ , (_ , _ , refl , (M , refl)) , <:̂ᵛ-refl _
  invV (handler N H)            =
    _ , (_ , _ , _ , _ , refl , (N , refl) , (H , λ op → refl)) , <:̂ᵛ-refl _
  invV (annᵛ A V)               = invV V
  invV (subV V p) with invV V
  ... | T₀ , h , q              = T₀ , h , <:̂ᵛ-trans q p

  invC : ∀ {n} {Γ : OCtx Θ n} {C : OCType Θ} → (D : Q ∣ Γ ⊢ᶜ⦂ C) → InvC Q Γ ∥ D ∥ᶜ C
  invC (return V)                 = _ , (_ , refl , (V , refl)) , <:̂ᶜ-refl _
  invC (M ⨟ N)                    = _ , (_ , _ , _ , _ , refl , (M , refl) , (N , refl)) , <:̂ᶜ-refl _
  invC (V · W)                    = _ , (_ , (V , refl) , (W , refl)) , <:̂ᶜ-refl _
  invC (match V `with M)          = _ , (_ , _ , (V , refl) , (M , refl)) , <:̂ᶜ-refl _
  invC (absurd V)                 = _ , (V , refl) , <:̂ᶜ-refl _
  invC (if V `then M `else N)     = _ , ((V , refl) , (M , refl) , (N , refl)) , <:̂ᶜ-refl _
  invC (matchℕ V `zero M `succ N) = _ , ((V , refl) , (M , refl) , (N , refl)) , <:̂ᶜ-refl _
  invC (match+ V `inl M `inr N)   = _ , (_ , _ , (V , refl) , (M , refl) , (N , refl)) , <:̂ᶜ-refl _
  invC (matchL V `nil M `cons N)  = _ , (_ , (V , refl) , (M , refl) , (N , refl)) , <:̂ᶜ-refl _
  invC (recℕ V M N p)             =
    _ , (_ , _ , refl , (V , refl) , (M , refl) , (N , refl) , p) , <:̂ᶜ-refl _
  invC (recL V M N p)             =
    _ , (_ , _ , _ , refl , (V , refl) , (M , refl) , (N , refl) , p) , <:̂ᶜ-refl _
  invC (perform op V M)           = _ , (_ , _ , refl , (V , refl) , (M , refl)) , <:̂ᶜ-refl _
  invC (delay τ M)                = _ , (_ , _ , refl , (M , refl)) , <:̂ᶜ-refl _
  invC (handle M `with V)         =
    _ , (_ , _ , _ , _ , refl , (M , refl) , (V , refl)) , <:̂ᶜ-refl _
  invC (unbox R p N)              =
    _ , (_ , _ , _ , (R , refl) , p , (N , refl)) , <:̂ᶜ-refl _
  invC (box ρ V N)                = _ , (_ , _ , (V , refl) , (N , refl)) , <:̂ᶜ-refl _
  invC (annᶜ C M)                 = invC M
  invC (subC M p) with invC M
  ... | C₀ , h , q               = C₀ , h , <:̂ᶜ-trans q p

  -- inversion at a term the erasure is equal to

  invV≡ : ∀ {n} {Γ : OCtx Θ n} {T : OVType Θ} {V : RunV n}
        → (D : Q ∣ Γ ⊢ᵛ⦂ T) → ∥ D ∥ᵛ ≡ V → InvV Q Γ V T
  invV≡ D refl = invV D

  invC≡ : ∀ {n} {Γ : OCtx Θ n} {C : OCType Θ} {M : RunC n}
        → (D : Q ∣ Γ ⊢ᶜ⦂ C) → ∥ D ∥ᶜ ≡ M → InvC Q Γ M C
  invC≡ D refl = invC D

------------------------------------------------------------------------
-- Canonical forms in a context of box-typed variables

module _ {n : ℕ} where

  data FunView : RunV n → Set where
    is-fun : ∀ M → FunView (fun M)

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
BoxCtx {Θ} Γ =
  (∀ {A ρ} → A ∈̂[ ρ ] Γ → Σ[ ρ₀ ∈ RExp Θ ] Σ[ A₀ ∈ OVType Θ ] A ≡ [ ρ₀ ] A₀) × (defs Γ ≡ ∅ᵖ)

module _ {Θ : Scope} {n : ℕ} {Q : Hyps Θ} {Γ : OCtx Θ n} (bx : BoxCtx Γ) where

  private
    no-var : ∀ {A ρ} {P : Set} → A ∈̂[ ρ ] Γ → (∀ {ρ₀ A₀} → A ≡ [ ρ₀ ] A₀ → ⊥) → P
    no-var x f with proj₁ bx x
    ... | _ , _ , e = ⊥-elim (f e)

    no-usedef : ∀ {s k} {P : Set} → s ∈ᵖ[ k ] defs Γ → P
    no-usedef f = ⊥-elim (∅ᵖ-∌ (subst (_ ∈ᵖ[ _ ]_) (proj₂ bx) f))

  canon-⇒ : ∀ {A C} → (D : Q ∣ Γ ⊢ᵛ⦂ A ⇒ C) → FunView ∥ D ∥ᵛ
  canon-⇒ (var x p)          = no-var x (λ ())
  canon-⇒ (usedef f δ h e)   = no-usedef f
  canon-⇒ (fun M)            = is-fun _
  canon-⇒ (annᵛ _ D)         = canon-⇒ D
  canon-⇒ (subV D (p ⇒ₛ q))  = canon-⇒ D

  canon-⇛ : ∀ {C D'} → (D : Q ∣ Γ ⊢ᵛ⦂ C ⇛ D') → HandlerView ∥ D ∥ᵛ
  canon-⇛ (var x p)          = no-var x (λ ())
  canon-⇛ (usedef f δ h e)   = no-usedef f
  canon-⇛ (handler N H)      = is-handler _ _
  canon-⇛ (annᵛ _ D)         = canon-⇛ D
  canon-⇛ (subV D (p ⇛ₛ q))  = canon-⇛ D

  canon-× : ∀ {A B} → (D : Q ∣ Γ ⊢ᵛ⦂ A |×| B) → PairView ∥ D ∥ᵛ
  canon-× (var x p)          = no-var x (λ ())
  canon-× (usedef f δ h e)   = no-usedef f
  canon-× ⦉ V , W ⦊           = is-pair _ _
  canon-× (annᵛ _ D)         = canon-× D
  canon-× (subV D (p |×|ₛ q)) = canon-× D

  canon-+ : ∀ {A B} → (D : Q ∣ Γ ⊢ᵛ⦂ A |+| B) → SumView ∥ D ∥ᵛ
  canon-+ (var x p)          = no-var x (λ ())
  canon-+ (usedef f δ h e)   = no-usedef f
  canon-+ (inl V)            = is-inl _
  canon-+ (inr V)            = is-inr _
  canon-+ (annᵛ _ D)         = canon-+ D
  canon-+ (subV D (p |+|ₛ q)) = canon-+ D

  canon-list : ∀ {A} → (D : Q ∣ Γ ⊢ᵛ⦂ list A) → ListView ∥ D ∥ᵛ
  canon-list (var x p)          = no-var x (λ ())
  canon-list (usedef f δ h e)   = no-usedef f
  canon-list nil                = is-nil
  canon-list (cons V W)         = is-cons _ _
  canon-list (annᵛ _ D)         = canon-list D
  canon-list (subV D (listₛ p)) = canon-list D

  canon-nat : (D : Q ∣ Γ ⊢ᵛ⦂ nat) → NatView ∥ D ∥ᵛ
  canon-nat (var x p)        = no-var x (λ ())
  canon-nat (usedef f δ h e) = no-usedef f
  canon-nat zero             = is-zero
  canon-nat (succ V)         = is-succ _
  canon-nat (annᵛ _ D)       = canon-nat D
  canon-nat (subV D natₛ)    = canon-nat D

  canon-bool : (D : Q ∣ Γ ⊢ᵛ⦂ bool) → BoolView ∥ D ∥ᵛ
  canon-bool (var x p)        = no-var x (λ ())
  canon-bool (usedef f δ h e) = no-usedef f
  canon-bool true             = is-true
  canon-bool false            = is-false
  canon-bool (cmp ⋈ V W et)   = is-cmp _ _ _
  canon-bool (annᵛ _ D)       = canon-bool D
  canon-bool (subV D boolₛ)   = canon-bool D

  canon-empty : (D : Q ∣ Γ ⊢ᵛ⦂ empty) → ⊥
  canon-empty (var x p)       = no-var x (λ ())
  canon-empty (usedef f δ h e) = no-usedef f
  canon-empty (annᵛ _ D)      = canon-empty D
  canon-empty (subV D emptyₛ) = canon-empty D

canon-box : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ A}
          → defs Γ ≡ ∅ᵖ → (D : Q ∣ Γ ⊢ᵛ⦂ [ ρ ] A) → VarView ∥ D ∥ᵛ
canon-box nd (var x p)          = is-var _
canon-box nd (usedef f δ h e)   = ⊥-elim (∅ᵖ-∌ (subst (_ ∈ᵖ[ _ ]_) nd f))
canon-box nd (annᵛ _ D)         = canon-box nd D
canon-box nd (subV D ([ p ]ₛ q)) = canon-box nd D
