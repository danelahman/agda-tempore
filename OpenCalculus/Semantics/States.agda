------------------------------------------------------------------
-- States and state typings                                     --
--                                                              --
-- A state `S ::= ∅ | S ⟨ τ ⟩ₛ | S ∷ₛ V` records the passages of --
-- time and the resources of a run, without grades; `State n`   --
-- has `n` resources, the variables of the run's term. A state  --
-- typing `Σ` of `S` gives each resource a type `[ ρ ] X`; the  --
-- context of the state is `ctx Σ`, and `Σ` types `S`           --
-- (`Types Σ`) when each resource `V` has `ctx Σ' ⟨ ρ ⟩ ⊢ V : X`  --
-- for the state typing `Σ'` before it.                         --
--                                                              --
-- `S ≤ₛ S'` when `S'` extends `S` by passages and resources;   --
-- `δₛ` is the grade of the passages added, and `Σ ⊆[ e ] Σ'`   --
-- extends a state typing along `e`.                            --
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Semantics.States (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import OpenCalculus.Syntax.Grades         S
open import OpenCalculus.Syntax.Types          S
open import OpenCalculus.Syntax.Contexts       S
open import OpenCalculus.Hypotheses            S
open import OpenCalculus.Typing                S
open import OpenCalculus.Typing.Renaming       S
open import OpenCalculus.Typing.Inversion      S using (BoxCtx)
open import OpenCalculus.Typing.ScopeClosed    S
open import OpenCalculus.Syntax.Run            S

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

-- the positions of the old resources in the extension

wkₛ : ∀ {n m} {S : State n} {S' : State m} → S ≤ₛ S' → Fin n → Fin m
wkₛ ≤ₛ-refl     i = i
wkₛ (≤ₛ-lock e) i = wkₛ e i
wkₛ (≤ₛ-res e)  i = suc (wkₛ e i)

-- the grade of the passages added

δₛ : ∀ {n m} {S : State n} {S' : State m} → S ≤ₛ S' → RExp ∅ˢ
δₛ ≤ₛ-refl             = ûᵣ
δₛ (≤ₛ-lock {τ = τ} e) = δₛ e ·̂ᵣ rconst (of-durʳ τ)
δₛ (≤ₛ-res e)          = δₛ e

------------------------------------------------------------------------
-- State typings

infixl 31 _∷[_]_

data StateTyping : ∀ {n} → State n → Set where
  ∅      : StateTyping ∅
  _⟨⟩ˢ   : ∀ {n} {S : State n} {τ} → StateTyping S → StateTyping (S ⟨ τ ⟩ₛ)
  _∷[_]_ : ∀ {n} {S : State n} {V} → StateTyping S → RExp ∅ˢ → OVType ∅ˢ
         → StateTyping (S ∷ₛ V)

-- The context of a state

ctx : ∀ {n} {S : State n} → StateTyping S → OCtx ∅ˢ n
ctx ∅                     = []
ctx (_⟨⟩ˢ {τ = τ} Σ)      = ctx Σ ⟨ rconst (of-durʳ τ) ⟩
ctx (Σ ∷[ ρ ] X)          = ctx Σ ∷ [ ρ ] X

-- A state typing types a state when each resource has its type, behind
-- a lock at its grade, in the context of the state before it

data Types : ∀ {n} {S : State n} → StateTyping S → Set where
  ∅    : Types ∅
  _⟨⟩ˢ : ∀ {n} {S : State n} {τ} {Σ : StateTyping S}
       → Types Σ → Types (_⟨⟩ˢ {τ = τ} Σ)
  _∷_  : ∀ {n} {S : State n} {Σ : StateTyping S} {ρ X V}
       → Types Σ → ctx Σ ⟨ ρ ⟩ ⊢ᵛ V ⦂ X → Types (_∷[_]_ {V = V} Σ ρ X)

-- Extension of a state typing along an extension of its state

infix 4 _⊆[_]_

data _⊆[_]_ {n} {S : State n} (Σ : StateTyping S)
     : ∀ {m} {S' : State m} → S ≤ₛ S' → StateTyping S' → Set where
  ⊆-refl : Σ ⊆[ ≤ₛ-refl ] Σ
  ⊆-lock : ∀ {m} {S' : State m} {e : S ≤ₛ S'} {Σ' : StateTyping S'} {τ}
         → Σ ⊆[ e ] Σ' → Σ ⊆[ ≤ₛ-lock {τ = τ} e ] (Σ' ⟨⟩ˢ)
  ⊆-res  : ∀ {m} {S' : State m} {e : S ≤ₛ S'} {Σ' : StateTyping S'} {V ρ X}
         → Σ ⊆[ e ] Σ' → Σ ⊆[ ≤ₛ-res {V = V} e ] (Σ' ∷[ ρ ] X)

-- The context of the extension extends the context by the grade of
-- the passages added

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

-- The variables of the context of a state are resources

ctx-box : ∀ {n} {S : State n} → (Σ : StateTyping S) → BoxCtx (ctx Σ)
ctx-box (Σ ⟨⟩ˢ)      (Tl-⟨⟩ x) = ctx-box Σ x
ctx-box (Σ ∷[ ρ ] X) Hd        = ρ , X , refl
ctx-box (Σ ∷[ ρ ] X) (Tl-∷ x)  = ctx-box Σ x

-- A resource used within its grade has its type in the context of the
-- whole state

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
  lookup-ext {S = S ∷ₛ V} (T ∷ (D , refl)) Hd e le =
    rename-v r D , trans (∥rename-v∥ r D) (sym (ren-fuseᵛ (λ i → refl) ∥ D ∥ᵛ))
    where
      r = ext-unlock (ext-∘ʳ e wk-ren) (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityˡ)) le)
  lookup-ext {S = S ∷ₛ V} (T ∷ _) (Tl-∷ x) e le with lookup-ext T x (ext-∘ʳ e wk-ren) le
  ... | D , p = D , trans p (sym (ren-fuseᵛ (λ i → refl) (lookupₛ S (var-pos x))))

lookup-typed : ∀ {n} {S : State n} {Σ : StateTyping S} {ρ₀ ρ' A₀}
             → Types Σ → (x : [ ρ₀ ] A₀ ∈̂[ ρ' ] ctx Σ) → ∅ᴴ ⊩ ρ' ≾̂ᵣ ρ₀
             → ctx Σ ⊢ᵛ lookupₛ S (var-pos x) ⦂ A₀
lookup-typed {S = S} T x le with lookup-ext T x id-ext (transᵣ (eqᵣ ≡̂ᵣ-identityʳ) le)
... | D , p = D , trans p (ren-idᵛ (λ i → refl) (lookupₛ S (var-pos x)))
