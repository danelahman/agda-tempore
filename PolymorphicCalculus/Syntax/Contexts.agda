------------------------------------------------------------------
-- Program contexts, variables and contexts of the polymorphic  --
-- calculus                                                     --
--                                                              --
-- A program context binds the top-level definitions to closed  --
-- type schemes `∀ Θ. Q ⇒ X`, named by their position from the  --
-- first. A context starts with a program context and extends   --
-- it by variables and locks, indexed by the number of          --
-- variables it binds, with open grade expressions as grades.   --
-- A handler clause is typed under an ordinary lock at the      --
-- constant `⊤ᵣ`; there is no separate barrier former.          --
------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; [])
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; z<s; s<s)
open import Data.Nat.Properties using (_≟_; <-irrefl; n<1+n; <-trans)
open import Relation.Nullary using (¬_; yes; no)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Syntax.Contexts (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses               S using (Hyps; qhyps)

------------------------------------------------------------------------
-- Type schemes and program contexts

-- A closed type scheme `∀ Θ. Q ⇒ X`: a scope of its own, hypotheses
-- over it, and a value type over it.

record Scheme : Set where
  constructor ∀ˢ
  field
    Θˢ        : Scope
    Qˢ        : Hyps Θˢ
    Xˢ        : OVType Θˢ

open Scheme public

-- Program contexts, the first definition outermost

data PCtx : Set where
  ∅ᵖ   : PCtx
  _∷ᵖ_ : PCtx → Scheme → PCtx

infixl 31 _∷ᵖ_

-- The number of definitions

len : PCtx → ℕ
len ∅ᵖ       = 0
len (Δ ∷ᵖ s) = suc (len Δ)

-- `s ∈ᵖ[ k ] Δ`: the definition at position `k` of `Δ`, counted from
-- the first, has the scheme `s`

data _∈ᵖ[_]_ (s : Scheme) : ℕ → PCtx → Set where
  here  : ∀ {Δ}      → s ∈ᵖ[ len Δ ] Δ ∷ᵖ s
  there : ∀ {Δ s' k} → s ∈ᵖ[ k ] Δ → s ∈ᵖ[ k ] Δ ∷ᵖ s'

infix 27 _∈ᵖ[_]_

∅ᵖ-∌ : ∀ {s k} → ¬ s ∈ᵖ[ k ] ∅ᵖ
∅ᵖ-∌ ()

∈ᵖ-< : ∀ {s k Δ} → s ∈ᵖ[ k ] Δ → k < len Δ
∈ᵖ-< here      = n<1+n _
∈ᵖ-< (there m) = <-trans (∈ᵖ-< m) (n<1+n _)

-- Lookup by position

lookupᵖ : PCtx → ℕ → Maybe Scheme
lookupᵖ ∅ᵖ       k = nothing
lookupᵖ (Δ ∷ᵖ s) k with k ≟ len Δ
... | yes _ = just s
... | no  _ = lookupᵖ Δ k

lookupᵖ-∈ : ∀ {s k} → (Δ : PCtx) → lookupᵖ Δ k ≡ just s → s ∈ᵖ[ k ] Δ
lookupᵖ-∈ {k = k} (Δ ∷ᵖ s') e with k ≟ len Δ
lookupᵖ-∈ (Δ ∷ᵖ s') refl | yes refl = here
lookupᵖ-∈ (Δ ∷ᵖ s') e    | no _     = there (lookupᵖ-∈ Δ e)

∈-lookupᵖ : ∀ {s k Δ} → s ∈ᵖ[ k ] Δ → lookupᵖ Δ k ≡ just s
∈-lookupᵖ {Δ = Δ ∷ᵖ s} here with len Δ ≟ len Δ
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)
∈-lookupᵖ {k = k} {Δ = Δ ∷ᵖ s'} (there m) with k ≟ len Δ
... | yes refl = ⊥-elim (<-irrefl refl (∈ᵖ-< m))
... | no _     = ∈-lookupᵖ m

-- The schemes of a program context have no quantified hypotheses

Unquantified : PCtx → Set
Unquantified ∅ᵖ       = ⊤
Unquantified (Δ ∷ᵖ s) = Unquantified Δ × (qhyps (Qˢ s) ≡ [])

unquantified-∈ : ∀ {s k Δ} → Unquantified Δ → s ∈ᵖ[ k ] Δ → qhyps (Qˢ s) ≡ []
unquantified-∈ (_ , e) here      = e
unquantified-∈ (u , _) (there m) = unquantified-∈ u m

------------------------------------------------------------------------
-- Contexts

-- Structured open contexts, indexed by the number of variables bound;
-- `[]` is the empty program context, `Δ ▶ s` the program context
-- `Δ ∷ᵖ s`

data OCtx (Θ : Scope) : ℕ → Set where
  []   : OCtx Θ 0                                     -- empty context
  _▶_  : PCtx → Scheme → OCtx Θ 0                     -- nonempty program context
  _∷_  : ∀ {n} → OCtx Θ n → OVType Θ → OCtx Θ (suc n) -- context extension
  _⟨_⟩ : ∀ {n} → OCtx Θ n → RExp Θ → OCtx Θ n         -- using context after time-passage

infixl 31 _∷_
infix  32 _⟨_⟩
infix  30 _▶_

-- A program context as a context

⌜_⌝ᵖ : ∀ {Θ} → PCtx → OCtx Θ 0
⌜ ∅ᵖ ⌝ᵖ     = []
⌜ Δ ∷ᵖ s ⌝ᵖ = Δ ▶ s

-- The program context a context starts with

defs : ∀ {Θ n} → OCtx Θ n → PCtx
defs []        = ∅ᵖ
defs (Δ ▶ s)   = Δ ∷ᵖ s
defs (Γ ∷ A)   = defs Γ
defs (Γ ⟨ ρ ⟩) = defs Γ

defs-⌜⌝ : ∀ {Θ} → (Δ : PCtx) → defs (⌜_⌝ᵖ {Θ} Δ) ≡ Δ
defs-⌜⌝ ∅ᵖ       = refl
defs-⌜⌝ (Δ ∷ᵖ s) = refl

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
wkᵗ-ctx (Δ ▶ s)   = Δ ▶ s
wkᵗ-ctx (Γ ∷ A)   = wkᵗ-ctx Γ ∷ wkᵗ-v A
wkᵗ-ctx (Γ ⟨ ρ ⟩) = wkᵗ-ctx Γ ⟨ wkᵗ-r ρ ⟩

wkʳ-ctx : ∀ {Θ n} → OCtx Θ n → OCtx (Θ +r) n
wkʳ-ctx []        = []
wkʳ-ctx (Δ ▶ s)   = Δ ▶ s
wkʳ-ctx (Γ ∷ A)   = wkʳ-ctx Γ ∷ wkʳ-v A
wkʳ-ctx (Γ ⟨ ρ ⟩) = wkʳ-ctx Γ ⟨ wkʳ-r ρ ⟩

wkᵉ-ctx : ∀ {Θ n} → OCtx Θ n → OCtx (Θ +e) n
wkᵉ-ctx []        = []
wkᵉ-ctx (Δ ▶ s)   = Δ ▶ s
wkᵉ-ctx (Γ ∷ A)   = wkᵉ-ctx Γ ∷ wkᵉ-v A
wkᵉ-ctx (Γ ⟨ ρ ⟩) = wkᵉ-ctx Γ ⟨ wkᵉ-r ρ ⟩

-- Weakening keeps the program context

defs-wkᵗ : ∀ {Θ n} → (Γ : OCtx Θ n) → defs (wkᵗ-ctx Γ) ≡ defs Γ
defs-wkᵗ []        = refl
defs-wkᵗ (Δ ▶ s)   = refl
defs-wkᵗ (Γ ∷ A)   = defs-wkᵗ Γ
defs-wkᵗ (Γ ⟨ ρ ⟩) = defs-wkᵗ Γ

defs-wkʳ : ∀ {Θ n} → (Γ : OCtx Θ n) → defs (wkʳ-ctx Γ) ≡ defs Γ
defs-wkʳ []        = refl
defs-wkʳ (Δ ▶ s)   = refl
defs-wkʳ (Γ ∷ A)   = defs-wkʳ Γ
defs-wkʳ (Γ ⟨ ρ ⟩) = defs-wkʳ Γ

defs-wkᵉ : ∀ {Θ n} → (Γ : OCtx Θ n) → defs (wkᵉ-ctx Γ) ≡ defs Γ
defs-wkᵉ []        = refl
defs-wkᵉ (Δ ▶ s)   = refl
defs-wkᵉ (Γ ∷ A)   = defs-wkᵉ Γ
defs-wkᵉ (Γ ⟨ ρ ⟩) = defs-wkᵉ Γ

------------------------------------------------------------------------
-- Action of a substitution on contexts, which keeps the program
-- context and the number of bound variables

infixl 50 _[_]ᶜᵗˣ

_[_]ᶜᵗˣ : ∀ {Θ Θ' n} → OCtx Θ n → Subst Θ Θ' → OCtx Θ' n
[]        [ σ ]ᶜᵗˣ = []
(Δ ▶ s)   [ σ ]ᶜᵗˣ = Δ ▶ s
(Γ ∷ A)   [ σ ]ᶜᵗˣ = Γ [ σ ]ᶜᵗˣ ∷ A [ σ ]ᵛ
(Γ ⟨ ρ ⟩) [ σ ]ᶜᵗˣ = Γ [ σ ]ᶜᵗˣ ⟨ ρ [ σ ]ʳ ⟩

[id]ᶜᵗˣ : ∀ {Θ n} → (Γ : OCtx Θ n) → Γ [ idˢ ]ᶜᵗˣ ≡ Γ
[id]ᶜᵗˣ []        = refl
[id]ᶜᵗˣ (Δ ▶ s)  = refl
[id]ᶜᵗˣ (Γ ∷ A)   = cong₂ _∷_ ([id]ᶜᵗˣ Γ) ([id]ᵛ A)
[id]ᶜᵗˣ (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ ([id]ᶜᵗˣ Γ) ([id]ʳ ρ)

[⨟]ᶜᵗˣ : ∀ {Θ Θ' Θ'' n} → (Γ : OCtx Θ n) → (σ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
       → Γ [ σ ]ᶜᵗˣ [ δ ]ᶜᵗˣ ≡ Γ [ σ ⨟ˢ δ ]ᶜᵗˣ
[⨟]ᶜᵗˣ []        σ δ = refl
[⨟]ᶜᵗˣ (Δ ▶ s)  σ δ = refl
[⨟]ᶜᵗˣ (Γ ∷ A)   σ δ = cong₂ _∷_ ([⨟]ᶜᵗˣ Γ σ δ) ([⨟]ᵛ A σ δ)
[⨟]ᶜᵗˣ (Γ ⟨ ρ ⟩) σ δ = cong₂ _⟨_⟩ ([⨟]ᶜᵗˣ Γ σ δ) ([⨟]ʳ ρ σ δ)

[≐]ᶜᵗˣ : ∀ {Θ Θ' n} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ → (Γ : OCtx Θ n)
       → Γ [ σ ]ᶜᵗˣ ≡ Γ [ δ ]ᶜᵗˣ
[≐]ᶜᵗˣ p []        = refl
[≐]ᶜᵗˣ p (Δ ▶ s)  = refl
[≐]ᶜᵗˣ p (Γ ∷ A)   = cong₂ _∷_ ([≐]ᶜᵗˣ p Γ) ([≐]ᵛ p A)
[≐]ᶜᵗˣ p (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ ([≐]ᶜᵗˣ p Γ) ([≐]ʳ p ρ)

wkˢᵗ-ctx : ∀ {Θ n} → (Γ : OCtx Θ n) → Γ [ wkˢᵗ ]ᶜᵗˣ ≡ wkᵗ-ctx Γ
wkˢᵗ-ctx []        = refl
wkˢᵗ-ctx (Δ ▶ s)  = refl
wkˢᵗ-ctx (Γ ∷ A)   = cong₂ _∷_ (wkˢᵗ-ctx Γ) (wkˢᵗ-v A)
wkˢᵗ-ctx (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (wkˢᵗ-ctx Γ) (wkˢᵗ-r ρ)

wkˢʳ-ctx : ∀ {Θ n} → (Γ : OCtx Θ n) → Γ [ wkˢʳ ]ᶜᵗˣ ≡ wkʳ-ctx Γ
wkˢʳ-ctx []        = refl
wkˢʳ-ctx (Δ ▶ s)  = refl
wkˢʳ-ctx (Γ ∷ A)   = cong₂ _∷_ (wkˢʳ-ctx Γ) (wkˢʳ-v A)
wkˢʳ-ctx (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (wkˢʳ-ctx Γ) (wkˢʳ-r ρ)

wkˢᵉ-ctx : ∀ {Θ n} → (Γ : OCtx Θ n) → Γ [ wkˢᵉ ]ᶜᵗˣ ≡ wkᵉ-ctx Γ
wkˢᵉ-ctx []        = refl
wkˢᵉ-ctx (Δ ▶ s)  = refl
wkˢᵉ-ctx (Γ ∷ A)   = cong₂ _∷_ (wkˢᵉ-ctx Γ) (wkˢᵉ-v A)
wkˢᵉ-ctx (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (wkˢᵉ-ctx Γ) (wkˢᵉ-r ρ)

wk-,ᵗ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (B : OVType Θ') → (Γ : OCtx Θ n)
          → wkᵗ-ctx Γ [ σ ,ᵗ B ]ᶜᵗˣ ≡ Γ [ σ ]ᶜᵗˣ
wk-,ᵗ-ctx σ B Γ = trans (cong (_[ σ ,ᵗ B ]ᶜᵗˣ) (sym (wkˢᵗ-ctx Γ)))
                  (trans ([⨟]ᶜᵗˣ Γ wkˢᵗ (σ ,ᵗ B)) ([≐]ᶜᵗˣ (wkˢᵗ-,ᵗ σ B) Γ))

wk-,ʳ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (ρ' : RExp Θ') → (Γ : OCtx Θ n)
          → wkʳ-ctx Γ [ σ ,ʳ ρ' ]ᶜᵗˣ ≡ Γ [ σ ]ᶜᵗˣ
wk-,ʳ-ctx σ ρ' Γ = trans (cong (_[ σ ,ʳ ρ' ]ᶜᵗˣ) (sym (wkˢʳ-ctx Γ)))
                   (trans ([⨟]ᶜᵗˣ Γ wkˢʳ (σ ,ʳ ρ')) ([≐]ᶜᵗˣ (wkˢʳ-,ʳ σ ρ') Γ))

wk-,ᵉ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (ε' : EExp Θ') → (Γ : OCtx Θ n)
          → wkᵉ-ctx Γ [ σ ,ᵉ ε' ]ᶜᵗˣ ≡ Γ [ σ ]ᶜᵗˣ
wk-,ᵉ-ctx σ ε' Γ = trans (cong (_[ σ ,ᵉ ε' ]ᶜᵗˣ) (sym (wkˢᵉ-ctx Γ)))
                   (trans ([⨟]ᶜᵗˣ Γ wkˢᵉ (σ ,ᵉ ε')) ([≐]ᶜᵗˣ (wkˢᵉ-,ᵉ σ ε') Γ))

wk-↑ᵗ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (Γ : OCtx Θ n)
          → wkᵗ-ctx Γ [ σ ↑ᵗ ]ᶜᵗˣ ≡ wkᵗ-ctx (Γ [ σ ]ᶜᵗˣ)
wk-↑ᵗ-ctx σ Γ = trans (cong (_[ σ ↑ᵗ ]ᶜᵗˣ) (sym (wkˢᵗ-ctx Γ)))
                (trans ([⨟]ᶜᵗˣ Γ wkˢᵗ (σ ↑ᵗ))
                (trans ([≐]ᶜᵗˣ (wkˢᵗ-↑ᵗ σ) Γ)
                (trans (sym ([⨟]ᶜᵗˣ Γ σ wkˢᵗ)) (wkˢᵗ-ctx (Γ [ σ ]ᶜᵗˣ)))))

wk-↑ʳ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (Γ : OCtx Θ n)
          → wkʳ-ctx Γ [ σ ↑ʳ ]ᶜᵗˣ ≡ wkʳ-ctx (Γ [ σ ]ᶜᵗˣ)
wk-↑ʳ-ctx σ Γ = trans (cong (_[ σ ↑ʳ ]ᶜᵗˣ) (sym (wkˢʳ-ctx Γ)))
                (trans ([⨟]ᶜᵗˣ Γ wkˢʳ (σ ↑ʳ))
                (trans ([≐]ᶜᵗˣ (wkˢʳ-↑ʳ σ) Γ)
                (trans (sym ([⨟]ᶜᵗˣ Γ σ wkˢʳ)) (wkˢʳ-ctx (Γ [ σ ]ᶜᵗˣ)))))

wk-↑ᵉ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (Γ : OCtx Θ n)
          → wkᵉ-ctx Γ [ σ ↑ᵉ ]ᶜᵗˣ ≡ wkᵉ-ctx (Γ [ σ ]ᶜᵗˣ)
wk-↑ᵉ-ctx σ Γ = trans (cong (_[ σ ↑ᵉ ]ᶜᵗˣ) (sym (wkˢᵉ-ctx Γ)))
                (trans ([⨟]ᶜᵗˣ Γ wkˢᵉ (σ ↑ᵉ))
                (trans ([≐]ᶜᵗˣ (wkˢᵉ-↑ᵉ σ) Γ)
                (trans (sym ([⨟]ᶜᵗˣ Γ σ wkˢᵉ)) (wkˢᵉ-ctx (Γ [ σ ]ᶜᵗˣ)))))

lookup-ty-subst : ∀ {Θ Θ' n} → (Γ : OCtx Θ n) → (σ : Subst Θ Θ') → (i : Fin n)
                → lookup-ty (Γ [ σ ]ᶜᵗˣ) i ≡ lookup-ty Γ i [ σ ]ᵛ
lookup-ty-subst (Γ ∷ A)   σ zero    = refl
lookup-ty-subst (Γ ∷ A)   σ (suc i) = lookup-ty-subst Γ σ i
lookup-ty-subst (Γ ⟨ ρ ⟩) σ i       = lookup-ty-subst Γ σ i

lookup-gr-subst : ∀ {Θ Θ' n} → (Γ : OCtx Θ n) → (σ : Subst Θ Θ') → (i : Fin n)
                → lookup-gr (Γ [ σ ]ᶜᵗˣ) i ≡ lookup-gr Γ i [ σ ]ʳ
lookup-gr-subst (Γ ∷ A)   σ zero    = refl
lookup-gr-subst (Γ ∷ A)   σ (suc i) = lookup-gr-subst Γ σ i
lookup-gr-subst (Γ ⟨ ρ ⟩) σ i       = cong (_·̂ᵣ ρ [ σ ]ʳ) (lookup-gr-subst Γ σ i)

defs-subst : ∀ {Θ Θ' n} → (Γ : OCtx Θ n) → (σ : Subst Θ Θ') → defs (Γ [ σ ]ᶜᵗˣ) ≡ defs Γ
defs-subst []        σ = refl
defs-subst (Δ ▶ s)   σ = refl
defs-subst (Γ ∷ A)   σ = defs-subst Γ σ
defs-subst (Γ ⟨ ρ ⟩) σ = defs-subst Γ σ

