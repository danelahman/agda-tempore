------------------------------------------------------------------
-- Variables and contexts of the mirrored language                --
--                                                                --
-- Open contexts mirror `Syntax.Contexts`, but are indexed by the --
-- number of variables they bind, and their grades are open       --
-- expressions. There is no separate barrier former: a handler    --
-- clause is typed under an ordinary lock at the constant `⊤ᵣ`.   --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.OpenSyntax.Contexts (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types S

-- Structured open contexts, indexed by the number of variables bound

data OCtx (Θ : Scope) : ℕ → Set where
  []   : OCtx Θ 0                                     -- empty context
  _∷_  : ∀ {n} → OCtx Θ n → OVType Θ → OCtx Θ (suc n) -- context extension
  _⟨_⟩ : ∀ {n} → OCtx Θ n → RExp Θ → OCtx Θ n         -- using context after time-passage

infixl 31 _∷_
infix  32 _⟨_⟩

-- Variable in an open context (under ρ-amount of time-passage)

data _∈̂[_]_ {Θ : Scope} (A : OVType Θ) : RExp Θ → {n : ℕ} → OCtx Θ n → Set where
  Hd    : ∀ {n} {Γ : OCtx Θ n}          → A ∈̂[ ûᵣ ] Γ ∷ A
  Tl-∷  : ∀ {n} {Γ : OCtx Θ n} {B ρ}    → A ∈̂[ ρ ] Γ → A ∈̂[ ρ ] Γ ∷ B
  Tl-⟨⟩ : ∀ {n} {Γ : OCtx Θ n} {ρ ρ'}   → A ∈̂[ ρ' ] Γ → A ∈̂[ ρ' ·̂ᵣ ρ ] Γ ⟨ ρ ⟩

infix 27 _∈̂[_]_

-- Lookup by position: the type and the accumulated grade. Each recurses
-- exactly as the corresponding membership constructor acts.

lookup-ty : ∀ {Θ n} → OCtx Θ n → Fin n → OVType Θ
lookup-ty (Γ ∷ A)   zero    = A
lookup-ty (Γ ∷ A)   (suc i) = lookup-ty Γ i
lookup-ty (Γ ⟨ ρ ⟩) i       = lookup-ty Γ i

lookup-gr : ∀ {Θ n} → OCtx Θ n → Fin n → RExp Θ
lookup-gr (Γ ∷ A)   zero    = ûᵣ
lookup-gr (Γ ∷ A)   (suc i) = lookup-gr Γ i
lookup-gr (Γ ⟨ ρ ⟩) i       = lookup-gr Γ i ·̂ᵣ ρ

-- Lookup produces a membership witness

lookup-var : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n) → lookup-ty Γ i ∈̂[ lookup-gr Γ i ] Γ
lookup-var (Γ ∷ A)   zero    = Hd
lookup-var (Γ ∷ A)   (suc i) = Tl-∷ (lookup-var Γ i)
lookup-var (Γ ⟨ ρ ⟩) i       = Tl-⟨⟩ (lookup-var Γ i)

-- The position a membership witness points at

var-pos : ∀ {Θ n} {A : OVType Θ} {ρ} {Γ : OCtx Θ n} → A ∈̂[ ρ ] Γ → Fin n
var-pos Hd        = zero
var-pos (Tl-∷ x)  = suc (var-pos x)
var-pos (Tl-⟨⟩ x) = var-pos x

-- Lookup and `var-pos` are mutually inverse

var-pos-ty : ∀ {Θ n} {A : OVType Θ} {ρ} {Γ : OCtx Θ n}
           → (x : A ∈̂[ ρ ] Γ) → lookup-ty Γ (var-pos x) ≡ A
var-pos-ty Hd        = refl
var-pos-ty (Tl-∷ x)  = var-pos-ty x
var-pos-ty (Tl-⟨⟩ x) = var-pos-ty x

var-pos-gr : ∀ {Θ n} {A : OVType Θ} {ρ} {Γ : OCtx Θ n}
           → (x : A ∈̂[ ρ ] Γ) → lookup-gr Γ (var-pos x) ≡ ρ
var-pos-gr Hd                = refl
var-pos-gr (Tl-∷ x)          = var-pos-gr x
var-pos-gr (Tl-⟨⟩ {ρ = ρ} x) = cong (_·̂ᵣ ρ) (var-pos-gr x)

var-pos-lookup : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n) → var-pos (lookup-var Γ i) ≡ i
var-pos-lookup (Γ ∷ A)   zero    = refl
var-pos-lookup (Γ ∷ A)   (suc i) = cong suc (var-pos-lookup Γ i)
var-pos-lookup (Γ ⟨ ρ ⟩) i       = var-pos-lookup Γ i

-- Action of the scope extensions on contexts

wkᵗ-ctx : ∀ {Θ n} → OCtx Θ n → OCtx (Θ +ty) n
wkᵗ-ctx []        = []
wkᵗ-ctx (Γ ∷ A)   = wkᵗ-ctx Γ ∷ wkᵗ-v A
wkᵗ-ctx (Γ ⟨ ρ ⟩) = wkᵗ-ctx Γ ⟨ wkᵗ-r ρ ⟩

wkʳ-ctx : ∀ {Θ n} → OCtx Θ n → OCtx (Θ +r) n
wkʳ-ctx []        = []
wkʳ-ctx (Γ ∷ A)   = wkʳ-ctx Γ ∷ wkʳ-v A
wkʳ-ctx (Γ ⟨ ρ ⟩) = wkʳ-ctx Γ ⟨ wkʳ-r ρ ⟩

wkᵉ-ctx : ∀ {Θ n} → OCtx Θ n → OCtx (Θ +e) n
wkᵉ-ctx []        = []
wkᵉ-ctx (Γ ∷ A)   = wkᵉ-ctx Γ ∷ wkᵉ-v A
wkᵉ-ctx (Γ ⟨ ρ ⟩) = wkᵉ-ctx Γ ⟨ wkᵉ-r ρ ⟩
