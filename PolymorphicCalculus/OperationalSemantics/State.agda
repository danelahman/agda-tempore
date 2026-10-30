------------------------------------------------------------------
-- States and state typings                                     --
--                                                              --
-- A state `S ::= ∅ | S ⟨ τ ⟩ₛ | S ∷ₛ V` records the passages   --
-- of time and the resources of a run; `State n` has `n`        --
-- resources. A state typing `Σ` types `S` (`Types Σ`) when     --
-- each resource has its type `[ ρ ] X` in the context before   --
-- it, behind `ρ`. `S ≤ₛ S'` extends a state; `δₛ` is the grade --
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
lookupₛ (S ⟨ τ ⟩ₛ) i       = lookupₛ S i
lookupₛ (S ∷ₛ V)   zero    = wkᵛ V
lookupₛ (S ∷ₛ V)   (suc i) = wkᵛ (lookupₛ S i)

-- Extension by passages and resources

infix 4 _≤ₛ_

data _≤ₛ_ {n} (S : State n) : ∀ {m} → State m → Set where
  ≤ₛ-refl : S ≤ₛ S
  ≤ₛ-lock : ∀ {m} {S' : State m} {τ} → S ≤ₛ S' → S ≤ₛ S' ⟨ τ ⟩ₛ
  ≤ₛ-res  : ∀ {m} {S' : State m} {V} → S ≤ₛ S' → S ≤ₛ S' ∷ₛ V

wkₛ : ∀ {n m} {S : State n} {S' : State m} → S ≤ₛ S' → Fin n → Fin m
wkₛ ≤ₛ-refl     i = i
wkₛ (≤ₛ-lock e) i = wkₛ e i
wkₛ (≤ₛ-res e)  i = suc (wkₛ e i)

δₛ : ∀ {n m} {S : State n} {S' : State m} → S ≤ₛ S' → RExp ∅ˢ
δₛ ≤ₛ-refl             = ûᵣ
δₛ (≤ₛ-lock {τ = τ} e) = δₛ e ·̂ᵣ rconst (of-durʳ τ)
δₛ (≤ₛ-res e)          = δₛ e

infixl 25 _⨾ₛ_

_⨾ₛ_ : ∀ {n m k} {S : State n} {S' : State m} {S'' : State k}
     → S ≤ₛ S' → S' ≤ₛ S'' → S ≤ₛ S''
e ⨾ₛ ≤ₛ-refl     = e
e ⨾ₛ ≤ₛ-lock e'  = ≤ₛ-lock (e ⨾ₛ e')
e ⨾ₛ ≤ₛ-res e'   = ≤ₛ-res (e ⨾ₛ e')

wkₛ-⨾ : ∀ {n m k} {S : State n} {S' : State m} {S'' : State k}
      → (e : S ≤ₛ S') → (e' : S' ≤ₛ S'') → ∀ i → wkₛ (e ⨾ₛ e') i ≡ wkₛ e' (wkₛ e i)
wkₛ-⨾ e ≤ₛ-refl      i = refl
wkₛ-⨾ e (≤ₛ-lock e') i = wkₛ-⨾ e e' i
wkₛ-⨾ e (≤ₛ-res e')  i = cong suc (wkₛ-⨾ e e' i)

lookupₛ-wk : ∀ {n m} {S : State n} {S' : State m} → (e : S ≤ₛ S')
           → ∀ i → lookupₛ S' (wkₛ e i) ≡ renᵛ (wkₛ e) (lookupₛ S i)
lookupₛ-wk {S = S} ≤ₛ-refl i = sym (ren-idᵛ (λ j → refl) (lookupₛ S i))
lookupₛ-wk (≤ₛ-lock e) i = lookupₛ-wk e i
lookupₛ-wk {S = S} (≤ₛ-res e) i =
  trans (cong wkᵛ (lookupₛ-wk e i)) (ren-fuseᵛ (λ j → refl) (lookupₛ S i))

------------------------------------------------------------------------
-- State typings

infixl 31 _∷[_]_

data StateTyping : ∀ {n} → State n → Set where
  ∅      : StateTyping ∅
  _⟨⟩ˢ   : ∀ {n} {S : State n} {τ} → StateTyping S → StateTyping (S ⟨ τ ⟩ₛ)
  _∷[_]_ : ∀ {n} {S : State n} {V} → StateTyping S → RExp ∅ˢ → OVType ∅ˢ
         → StateTyping (S ∷ₛ V)

ctx : ∀ {n} {S : State n} → StateTyping S → OCtx ∅ˢ n
ctx ∅                     = []
ctx (_⟨⟩ˢ {τ = τ} Σ)      = ctx Σ ⟨ rconst (of-durʳ τ) ⟩
ctx (Σ ∷[ ρ ] X)          = ctx Σ ∷ [ ρ ] X

ctx-defs : ∀ {n} {S : State n} → (Σ : StateTyping S) → defs (ctx Σ) ≡ ∅ᵖ
ctx-defs ∅            = refl
ctx-defs (Σ ⟨⟩ˢ)      = ctx-defs Σ
ctx-defs (Σ ∷[ ρ ] X) = ctx-defs Σ

data Types : ∀ {n} {S : State n} → StateTyping S → Set where
  ∅    : Types ∅
  _⟨⟩ˢ : ∀ {n} {S : State n} {τ} {Σ : StateTyping S}
       → Types Σ → Types (_⟨⟩ˢ {τ = τ} Σ)
  _∷ᵗ_ : ∀ {n} {S : State n} {Σ : StateTyping S} {ρ X V}
       → Types Σ → ctx Σ ⟨ ρ ⟩ ⊢ᵛ V ⦂ X → Types (_∷[_]_ {V = V} Σ ρ X)

types-defs : ∀ {n} {S : State n} {Σ : StateTyping S} → Types Σ → defs (ctx Σ) ≡ ∅ᵖ
types-defs {Σ = Σ} _ = ctx-defs Σ

-- Extension of a state typing along an extension of its state

infix 4 _⊆[_]_

data _⊆[_]_ {n} {S : State n} (Σ : StateTyping S)
     : ∀ {m} {S' : State m} → S ≤ₛ S' → StateTyping S' → Set where
  ⊆-refl : Σ ⊆[ ≤ₛ-refl ] Σ
  ⊆-lock : ∀ {m} {S' : State m} {e : S ≤ₛ S'} {Σ' : StateTyping S'} {τ}
         → Σ ⊆[ e ] Σ' → Σ ⊆[ ≤ₛ-lock {τ = τ} e ] (Σ' ⟨⟩ˢ)
  ⊆-res  : ∀ {m} {S' : State m} {e : S ≤ₛ S'} {Σ' : StateTyping S'} {V ρ X}
         → Σ ⊆[ e ] Σ' → Σ ⊆[ ≤ₛ-res {V = V} e ] (Σ' ∷[ ρ ] X)

-- The extended context makes each variable older by the passages added

⊆-ext : ∀ {n m} {S : State n} {S' : State m} {e : S ≤ₛ S'}
          {Σ : StateTyping S} {Σ' : StateTyping S'}
      → Σ ⊆[ e ] Σ' → Ext ∅ᴴ (ctx Σ) (ctx Σ') (δₛ e)
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

ctx-box : ∀ {n} {S : State n} → (Σ : StateTyping S) → BoxCtx (ctx Σ)
ctx-box Σ = boxed Σ , ctx-defs Σ
  where
    boxed : ∀ {n} {S : State n} → (Σ : StateTyping S) → ∀ {A ρ} → A ∈̂[ ρ ] ctx Σ
          → Σ[ ρ₀ ∈ RExp ∅ˢ ] Σ[ A₀ ∈ OVType ∅ˢ ] A ≡ [ ρ₀ ] A₀
    boxed (Σ ⟨⟩ˢ)      (Tl-⟨⟩ x) = boxed Σ x
    boxed (Σ ∷[ ρ ] X) Hd        = ρ , X , refl
    boxed (Σ ∷[ ρ ] X) (Tl-∷ x)  = boxed Σ x

-- A resource used within its grade is typed in the whole state's context

private

  lookup-ext : ∀ {n m} {S : State n} {Σ : StateTyping S} {Γ : OCtx ∅ˢ m} {δ ρ₀ ρ' A₀}
             → Types Σ → (x : [ ρ₀ ] A₀ ∈̂[ ρ' ] ctx Σ) → (e : Ext ∅ᴴ (ctx Σ) Γ δ)
             → ∅ᴴ ⊩ ρ' ·̂ᵣ δ ≾̂ᵣ ρ₀
             → Γ ⊢ᵛ renᵛ (epos e) (lookupₛ S (var-pos x)) ⦂ A₀
  lookup-ext (T ⟨⟩ˢ) (Tl-⟨⟩ x) e le =
    lookup-ext T x e' (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-assoc)) le)
    where
      e' : Ext ∅ᴴ _ _ _
      epos e' = epos e
      ety  e' = ety e
      egr  e' i = transᵣ (egr e i) (eqᵣ ≡̂ᵣ-assoc)
      edfs e'   = edfs e
  lookup-ext {S = S ∷ₛ V} (T ∷ᵗ (D , refl)) Hd e le =
    rename-v r D , trans (∥rename-v∥ r D) (sym (ren-fuseᵛ (λ i → refl) ∥ D ∥ᵛ))
    where
      r = ext-unlock (ext-∘ʳ e wk-ren) (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityˡ)) le)
  lookup-ext {S = S ∷ₛ V} (T ∷ᵗ _) (Tl-∷ x) e le with lookup-ext T x (ext-∘ʳ e wk-ren) le
  ... | D , p = D , trans p (sym (ren-fuseᵛ (λ i → refl) (lookupₛ S (var-pos x))))

lookup-typed : ∀ {n} {S : State n} {Σ : StateTyping S} {ρ₀ ρ' A₀}
             → Types Σ → (x : [ ρ₀ ] A₀ ∈̂[ ρ' ] ctx Σ) → ∅ᴴ ⊩ ρ' ≾̂ᵣ ρ₀
             → ctx Σ ⊢ᵛ lookupₛ S (var-pos x) ⦂ A₀
lookup-typed {S = S} T x le with lookup-ext T x id-ext (transᵣ (eqᵣ ≡̂ᵣ-identityʳ) le)
... | D , p = D , trans p (ren-idᵛ (λ i → refl) (lookupₛ S (var-pos x)))
