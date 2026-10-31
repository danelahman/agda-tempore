------------------------------------------------------------------
-- States and state typings                                     --
--                                                              --
-- A state `𝕊 ::= ∅ | 𝕊 ⟨ τ ⟩ₛ | 𝕊 ∷ₛ V` records the passages   --
-- of time and the resources of a run; `State n` has `n`        --
-- resources. A state typing `Ψ` types `𝕊` (`Types Ψ`) when     --
-- each resource has its type `[ ρ ] X` in the context before   --
-- it, behind `ρ`. `𝕊 ≤ₛ 𝕊'` extends a state; `δₛ` is the grade --
-- of the passages added.                                       --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _,_)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.OperationalSemantics.State (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import PolymorphicCalculus.Syntax.Grades         S
open import PolymorphicCalculus.Syntax.Types          S
open import PolymorphicCalculus.Syntax.Contexts       S
open import PolymorphicCalculus.Hypotheses            S
open import PolymorphicCalculus.Typing                S
open import PolymorphicCalculus.Typing.Renaming       S
open import PolymorphicCalculus.Typing.Inversion      S using (BoxCtx)
open import PolymorphicCalculus.Typing.ScopeClosed    S
open import PolymorphicCalculus.Syntax.Run            S

infixl 31 _∷ₛ_
infix  32 _⟨_⟩ₛ

------------------------------------------------------------------------
-- States

data State : ℕ → Set where
  ∅    : State 0
  _⟨_⟩ₛ : ∀ {n} → State n → 𝔻 → State n
  _∷ₛ_  : ∀ {n} → State n → RunV n → State (suc n)

-- The resource at a position, in the scope of the whole state

lookupₛ : ∀ {n} → State n → Fin n → RunV n
lookupₛ (𝕊 ⟨ τ ⟩ₛ) i       = lookupₛ 𝕊 i
lookupₛ (𝕊 ∷ₛ V)   zero    = wkᵛ V
lookupₛ (𝕊 ∷ₛ V)   (suc i) = wkᵛ (lookupₛ 𝕊 i)

-- Extension by passages and resources

infix 4 _≤ₛ_

data _≤ₛ_ {n} (𝕊 : State n) : ∀ {m} → State m → Set where
  ≤ₛ-refl : 𝕊 ≤ₛ 𝕊
  ≤ₛ-lock : ∀ {m} {𝕊' : State m} {τ} → 𝕊 ≤ₛ 𝕊' → 𝕊 ≤ₛ 𝕊' ⟨ τ ⟩ₛ
  ≤ₛ-res  : ∀ {m} {𝕊' : State m} {V} → 𝕊 ≤ₛ 𝕊' → 𝕊 ≤ₛ 𝕊' ∷ₛ V

wkₛ : ∀ {n m} {𝕊 : State n} {𝕊' : State m} → 𝕊 ≤ₛ 𝕊' → Fin n → Fin m
wkₛ ≤ₛ-refl     i = i
wkₛ (≤ₛ-lock e) i = wkₛ e i
wkₛ (≤ₛ-res e)  i = suc (wkₛ e i)

δₛ : ∀ {n m} {𝕊 : State n} {𝕊' : State m} → 𝕊 ≤ₛ 𝕊' → RExp ∅ˢ
δₛ ≤ₛ-refl             = ûᵣ
δₛ (≤ₛ-lock {τ = τ} e) = δₛ e ·̂ᵣ rconst (of-durʳ τ)
δₛ (≤ₛ-res e)          = δₛ e

infixl 25 _⨾ₛ_

_⨾ₛ_ : ∀ {n m k} {𝕊 : State n} {𝕊' : State m} {𝕊'' : State k}
     → 𝕊 ≤ₛ 𝕊' → 𝕊' ≤ₛ 𝕊'' → 𝕊 ≤ₛ 𝕊''
e ⨾ₛ ≤ₛ-refl     = e
e ⨾ₛ ≤ₛ-lock e'  = ≤ₛ-lock (e ⨾ₛ e')
e ⨾ₛ ≤ₛ-res e'   = ≤ₛ-res (e ⨾ₛ e')

wkₛ-⨾ : ∀ {n m k} {𝕊 : State n} {𝕊' : State m} {𝕊'' : State k}
      → (e : 𝕊 ≤ₛ 𝕊') → (e' : 𝕊' ≤ₛ 𝕊'') → ∀ i → wkₛ (e ⨾ₛ e') i ≡ wkₛ e' (wkₛ e i)
wkₛ-⨾ e ≤ₛ-refl      i = refl
wkₛ-⨾ e (≤ₛ-lock e') i = wkₛ-⨾ e e' i
wkₛ-⨾ e (≤ₛ-res e')  i = cong suc (wkₛ-⨾ e e' i)

lookupₛ-wk : ∀ {n m} {𝕊 : State n} {𝕊' : State m} → (e : 𝕊 ≤ₛ 𝕊')
           → ∀ i → lookupₛ 𝕊' (wkₛ e i) ≡ renᵛ (wkₛ e) (lookupₛ 𝕊 i)
lookupₛ-wk {𝕊 = 𝕊} ≤ₛ-refl i = sym (ren-idᵛ (λ j → refl) (lookupₛ 𝕊 i))
lookupₛ-wk (≤ₛ-lock e) i = lookupₛ-wk e i
lookupₛ-wk {𝕊 = 𝕊} (≤ₛ-res e) i =
  trans (cong wkᵛ (lookupₛ-wk e i)) (ren-fuseᵛ (λ j → refl) (lookupₛ 𝕊 i))

------------------------------------------------------------------------
-- State typings

infixl 31 _∷[_]_

data StateTyping : ∀ {n} → State n → Set where
  ∅      : StateTyping ∅
  _⟨⟩ˢ   : ∀ {n} {𝕊 : State n} {τ} → StateTyping 𝕊 → StateTyping (𝕊 ⟨ τ ⟩ₛ)
  _∷[_]_ : ∀ {n} {𝕊 : State n} {V} → StateTyping 𝕊 → RExp ∅ˢ → OVType ∅ˢ
         → StateTyping (𝕊 ∷ₛ V)

ctx : ∀ {n} {𝕊 : State n} → StateTyping 𝕊 → OCtx ∅ˢ n
ctx ∅                     = []
ctx (_⟨⟩ˢ {τ = τ} Ψ)      = ctx Ψ ⟨ rconst (of-durʳ τ) ⟩
ctx (Ψ ∷[ ρ ] X)          = ctx Ψ ∷ [ ρ ] X

ctx-defs : ∀ {n} {𝕊 : State n} → (Ψ : StateTyping 𝕊) → defs (ctx Ψ) ≡ ∅ᵖ
ctx-defs ∅            = refl
ctx-defs (Ψ ⟨⟩ˢ)      = ctx-defs Ψ
ctx-defs (Ψ ∷[ ρ ] X) = ctx-defs Ψ

data Types : ∀ {n} {𝕊 : State n} → StateTyping 𝕊 → Set where
  ∅    : Types ∅
  _⟨⟩ˢ : ∀ {n} {𝕊 : State n} {τ} {Ψ : StateTyping 𝕊}
       → Types Ψ → Types (_⟨⟩ˢ {τ = τ} Ψ)
  _∷ᵗ_ : ∀ {n} {𝕊 : State n} {Ψ : StateTyping 𝕊} {ρ X V}
       → Types Ψ → ctx Ψ ⟨ ρ ⟩ ⊢ᵛ V ⦂ X → Types (_∷[_]_ {V = V} Ψ ρ X)

types-defs : ∀ {n} {𝕊 : State n} {Ψ : StateTyping 𝕊} → Types Ψ → defs (ctx Ψ) ≡ ∅ᵖ
types-defs {Ψ = Ψ} _ = ctx-defs Ψ

-- Extension of a state typing along an extension of its state

infix 4 _⊆[_]_

data _⊆[_]_ {n} {𝕊 : State n} (Ψ : StateTyping 𝕊)
     : ∀ {m} {𝕊' : State m} → 𝕊 ≤ₛ 𝕊' → StateTyping 𝕊' → Set where
  ⊆-refl : Ψ ⊆[ ≤ₛ-refl ] Ψ
  ⊆-lock : ∀ {m} {𝕊' : State m} {e : 𝕊 ≤ₛ 𝕊'} {Ψ' : StateTyping 𝕊'} {τ}
         → Ψ ⊆[ e ] Ψ' → Ψ ⊆[ ≤ₛ-lock {τ = τ} e ] (Ψ' ⟨⟩ˢ)
  ⊆-res  : ∀ {m} {𝕊' : State m} {e : 𝕊 ≤ₛ 𝕊'} {Ψ' : StateTyping 𝕊'} {V ρ X}
         → Ψ ⊆[ e ] Ψ' → Ψ ⊆[ ≤ₛ-res {V = V} e ] (Ψ' ∷[ ρ ] X)

-- The extended context makes each variable older by the passages added

⊆-ext : ∀ {n m} {𝕊 : State n} {𝕊' : State m} {e : 𝕊 ≤ₛ 𝕊'}
          {Ψ : StateTyping 𝕊} {Ψ' : StateTyping 𝕊'}
      → Ψ ⊆[ e ] Ψ' → Ext ∅ᴴ (ctx Ψ) (ctx Ψ') (δₛ e)
epos (⊆-ext {e = e} p) = wkₛ e
ety  (⊆-ext ⊆-refl)     i = refl
ety  (⊆-ext (⊆-lock p)) i = ety (⊆-ext p) i
ety  (⊆-ext (⊆-res p))  i = ety (⊆-ext p) i
egr  (⊆-ext ⊆-refl)     i = eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityʳ)
egr  (⊆-ext (⊆-lock p)) i =
  transᵣ (monoᵣ (egr (⊆-ext p) i) ⊩≾̂ᵣ-refl) (eqᵣ ≡̂ᵣ-assoc)
egr  (⊆-ext (⊆-res p))  i = egr (⊆-ext p) i
edfs (⊆-ext ⊆-refl)       = refl
edfs (⊆-ext (⊆-lock p))   = edfs (⊆-ext p)
edfs (⊆-ext (⊆-res p))    = edfs (⊆-ext p)

ctx-box : ∀ {n} {𝕊 : State n} → (Ψ : StateTyping 𝕊) → BoxCtx (ctx Ψ)
ctx-box Ψ = boxed Ψ , ctx-defs Ψ
  where
    boxed : ∀ {n} {𝕊 : State n} → (Ψ : StateTyping 𝕊) → ∀ {A ρ} → A ∈̂[ ρ ] ctx Ψ
          → Σ[ ρ₀ ∈ RExp ∅ˢ ] Σ[ A₀ ∈ OVType ∅ˢ ] A ≡ [ ρ₀ ] A₀
    boxed (Ψ ⟨⟩ˢ)      (Tl-⟨⟩ x) = boxed Ψ x
    boxed (Ψ ∷[ ρ ] X) Hd        = ρ , X , refl
    boxed (Ψ ∷[ ρ ] X) (Tl-∷ x)  = boxed Ψ x

-- A resource used within its grade is typed in the whole state's context

private

  lookup-ext : ∀ {n m} {𝕊 : State n} {Ψ : StateTyping 𝕊} {Γ : OCtx ∅ˢ m} {δ ρ₀ ρ' A₀}
             → Types Ψ → (x : [ ρ₀ ] A₀ ∈̂[ ρ' ] ctx Ψ) → (e : Ext ∅ᴴ (ctx Ψ) Γ δ)
             → ∅ᴴ ⊩ ρ' ·̂ᵣ δ ≾̂ᵣ ρ₀
             → Γ ⊢ᵛ renᵛ (epos e) (lookupₛ 𝕊 (var-pos x)) ⦂ A₀
  lookup-ext (T ⟨⟩ˢ) (Tl-⟨⟩ x) e le =
    lookup-ext T x e' (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-assoc)) le)
    where
      e' : Ext ∅ᴴ _ _ _
      epos e' = epos e
      ety  e' = ety e
      egr  e' i = transᵣ (egr e i) (eqᵣ ≡̂ᵣ-assoc)
      edfs e'   = edfs e
  lookup-ext {𝕊 = 𝕊 ∷ₛ V} (T ∷ᵗ (D , refl)) Hd e le =
    rename-v r D , trans (∥rename-v∥ r D) (sym (ren-fuseᵛ (λ i → refl) ∥ D ∥ᵛ))
    where
      r = ext-unlock (ext-∘ʳ e wk-ren) (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityˡ)) le)
  lookup-ext {𝕊 = 𝕊 ∷ₛ V} (T ∷ᵗ _) (Tl-∷ x) e le with lookup-ext T x (ext-∘ʳ e wk-ren) le
  ... | D , p = D , trans p (sym (ren-fuseᵛ (λ i → refl) (lookupₛ 𝕊 (var-pos x))))

lookup-typed : ∀ {n} {𝕊 : State n} {Ψ : StateTyping 𝕊} {ρ₀ ρ' A₀}
             → Types Ψ → (x : [ ρ₀ ] A₀ ∈̂[ ρ' ] ctx Ψ) → ∅ᴴ ⊩ ρ' ≾̂ᵣ ρ₀
             → ctx Ψ ⊢ᵛ lookupₛ 𝕊 (var-pos x) ⦂ A₀
lookup-typed {𝕊 = 𝕊} T x le with lookup-ext T x id-ext (transᵣ (eqᵣ ≡̂ᵣ-identityʳ) le)
... | D , p = D , trans p (ren-idᵛ (λ i → refl) (lookupₛ 𝕊 (var-pos x)))
