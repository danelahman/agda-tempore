------------------------------------------------------------------
-- Embedding uniform declarative typings in the open calculus   --
--                                                              --
-- A declarative typing `D : Δ ⊢C⦂ C` of a closed raw term `M`  --
-- is uniform in an open context `Γ'` (`Uᶜ Γ' M D`) when it     --
-- follows `M` former by former, each box at `M`'s grade, and   --
-- each handler's clause family is the instantiation of one     --
-- open clause typing at a rigid continuation grade. Annotations --
-- of `M` are passed over; `AnnFreeᶜ M` says there are none.    --
--                                                              --
-- A uniform typing in a context `Γ'` meaning `Δ` embeds as an  --
-- open typing `∅ᴴ ∣ Γ' ⊢C⦂ ⌜ C ⌝ᶜ` at the empty scope erasing  --
-- to `M` (`embedᶜ`, `embedᵛ`), and erases to `⌊ M ⌋ᴿᶜ`         --
-- (`uniform-⌊⌋ᶜ`). Grades of `Γ'` and `M` are expressions,     --
-- those of `D` their values; they meet through `⌞_⌟` and the   --
-- conversion of a closed expression to its value.              --
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations
open import Syntax.Comparisons using (Cmp)

open import Util.Equality

open import TypeInference.Scopes

module Instantiation.Embedding (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types     S
open import Syntax.Contexts  S
open import Syntax.Language  S hiding (coerce; numeralᵛ)
open import Syntax.Erasure   S hiding (⌊_⌋ᵛ; ⌊_⌋ᶜ; var-pos)
import Syntax.Erasure S as CE

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Language  S
open import TypeInference.OpenSyntax.Instances S using (valʳ; val-≾ᵣ⁻; val-≾ₑ⁻)
open import TypeInference.Raw.Syntax           S
open import TypeInference.Raw.Subst            S
import TypeInference.Erase S as OE

open import Instantiation.Types          S
open import Instantiation.Judgements     S
open import Instantiation.Correspondence S
open import Instantiation.Terms          S

------------------------------------------------------------------------
-- Raw terms without type annotations

mutual

  AnnFreeᵛ : ∀ {Θ n} → RawV Θ n → Set
  AnnFreeᵛ (succ V)   = AnnFreeᵛ V
  AnnFreeᵛ ⦉ V , W ⦊   = AnnFreeᵛ V × AnnFreeᵛ W
  AnnFreeᵛ (inl V)    = AnnFreeᵛ V
  AnnFreeᵛ (inr V)    = AnnFreeᵛ V
  AnnFreeᵛ (cons V W) = AnnFreeᵛ V × AnnFreeᵛ W
  AnnFreeᵛ (lam M)    = AnnFreeᶜ M
  AnnFreeᵛ (V ⦂ᵛ A)   = ⊥
  AnnFreeᵛ _          = ⊤

  AnnFreeᶜ : ∀ {Θ n} → RawC Θ n → Set
  AnnFreeᶜ (return V)                = AnnFreeᵛ V
  AnnFreeᶜ (M ⨟ N)                   = AnnFreeᶜ M × AnnFreeᶜ N
  AnnFreeᶜ (V · W)                   = AnnFreeᵛ V × AnnFreeᵛ W
  AnnFreeᶜ (match V `in M)           = AnnFreeᵛ V × AnnFreeᶜ M
  AnnFreeᶜ (absurd V)                = AnnFreeᵛ V
  AnnFreeᶜ (if V `then M `else N)    = AnnFreeᵛ V × AnnFreeᶜ M × AnnFreeᶜ N
  AnnFreeᶜ (cmp ⋈ V W)               = AnnFreeᵛ V × AnnFreeᵛ W
  AnnFreeᶜ (caseℕ V `zero M `succ N) = AnnFreeᵛ V × AnnFreeᶜ M × AnnFreeᶜ N
  AnnFreeᶜ (case+ V `inl M `inr N)   = AnnFreeᵛ V × AnnFreeᶜ M × AnnFreeᶜ N
  AnnFreeᶜ (recℕ V M N)              = AnnFreeᵛ V × AnnFreeᶜ M × AnnFreeᶜ N
  AnnFreeᶜ (caseL V `nil M `cons N)  = AnnFreeᵛ V × AnnFreeᶜ M × AnnFreeᶜ N
  AnnFreeᶜ (recL V M N)              = AnnFreeᵛ V × AnnFreeᶜ M × AnnFreeᶜ N
  AnnFreeᶜ (perform op V M)          = AnnFreeᵛ V × AnnFreeᶜ M
  AnnFreeᶜ (delay τ M)               = AnnFreeᶜ M
  AnnFreeᶜ (handle M `with H `in N)  = AnnFreeᶜ M × ((op : Op) → AnnFreeᶜ (H op)) × AnnFreeᶜ N
  AnnFreeᶜ (unbox i N)               = AnnFreeᶜ N
  AnnFreeᶜ (box ρ V N)               = AnnFreeᵛ V × AnnFreeᶜ N
  AnnFreeᶜ (M ⦂ᶜ C)                  = ⊥

-- Substitution keeps a term annotation-free

mutual

  annFree-[]ᵛ : ∀ {Θ Θ' n} → (V : RawV Θ n) → (σ : Subst Θ Θ')
              → AnnFreeᵛ V → AnnFreeᵛ (V [ σ ]ᴿᵛ)
  annFree-[]ᵛ (var i)     σ a       = tt
  annFree-[]ᵛ (const B c) σ a       = tt
  annFree-[]ᵛ ⋆           σ a       = tt
  annFree-[]ᵛ true        σ a       = tt
  annFree-[]ᵛ false       σ a       = tt
  annFree-[]ᵛ zero        σ a       = tt
  annFree-[]ᵛ (succ V)    σ a       = annFree-[]ᵛ V σ a
  annFree-[]ᵛ ⦉ V , W ⦊    σ (a , b) = annFree-[]ᵛ V σ a , annFree-[]ᵛ W σ b
  annFree-[]ᵛ (inl V)     σ a       = annFree-[]ᵛ V σ a
  annFree-[]ᵛ (inr V)     σ a       = annFree-[]ᵛ V σ a
  annFree-[]ᵛ nil         σ a       = tt
  annFree-[]ᵛ (cons V W)  σ (a , b) = annFree-[]ᵛ V σ a , annFree-[]ᵛ W σ b
  annFree-[]ᵛ (lam M)     σ a       = annFree-[]ᶜ M σ a

  annFree-[]ᶜ : ∀ {Θ Θ' n} → (M : RawC Θ n) → (σ : Subst Θ Θ')
              → AnnFreeᶜ M → AnnFreeᶜ (M [ σ ]ᴿᶜ)
  annFree-[]ᶜ (return V)                σ a = annFree-[]ᵛ V σ a
  annFree-[]ᶜ (M ⨟ N)                   σ (a , b) = annFree-[]ᶜ M σ a , annFree-[]ᶜ N σ b
  annFree-[]ᶜ (V · W)                   σ (a , b) = annFree-[]ᵛ V σ a , annFree-[]ᵛ W σ b
  annFree-[]ᶜ (match V `in M)           σ (a , b) = annFree-[]ᵛ V σ a , annFree-[]ᶜ M σ b
  annFree-[]ᶜ (absurd V)                σ a = annFree-[]ᵛ V σ a
  annFree-[]ᶜ (if V `then M `else N)    σ (a , b , c) =
    annFree-[]ᵛ V σ a , annFree-[]ᶜ M σ b , annFree-[]ᶜ N σ c
  annFree-[]ᶜ (cmp ⋈ V W)               σ (a , b) = annFree-[]ᵛ V σ a , annFree-[]ᵛ W σ b
  annFree-[]ᶜ (caseℕ V `zero M `succ N) σ (a , b , c) =
    annFree-[]ᵛ V σ a , annFree-[]ᶜ M σ b , annFree-[]ᶜ N σ c
  annFree-[]ᶜ (case+ V `inl M `inr N)   σ (a , b , c) =
    annFree-[]ᵛ V σ a , annFree-[]ᶜ M σ b , annFree-[]ᶜ N σ c
  annFree-[]ᶜ (recℕ V M N)              σ (a , b , c) =
    annFree-[]ᵛ V σ a , annFree-[]ᶜ M σ b , annFree-[]ᶜ N σ c
  annFree-[]ᶜ (caseL V `nil M `cons N)  σ (a , b , c) =
    annFree-[]ᵛ V σ a , annFree-[]ᶜ M σ b , annFree-[]ᶜ N σ c
  annFree-[]ᶜ (recL V M N)              σ (a , b , c) =
    annFree-[]ᵛ V σ a , annFree-[]ᶜ M σ b , annFree-[]ᶜ N σ c
  annFree-[]ᶜ (perform op V M)          σ (a , b) = annFree-[]ᵛ V σ a , annFree-[]ᶜ M σ b
  annFree-[]ᶜ (delay τ M)               σ a = annFree-[]ᶜ M σ a
  annFree-[]ᶜ (handle M `with H `in N)  σ (a , h , b) =
    annFree-[]ᶜ M σ a , (λ op → annFree-[]ᶜ (H op) (σ ↑ᵉ) (h op)) , annFree-[]ᶜ N σ b
  annFree-[]ᶜ (unbox i N)               σ a = annFree-[]ᶜ N σ a
  annFree-[]ᶜ (box ρ V N)               σ (a , b) = annFree-[]ᵛ V σ a , annFree-[]ᶜ N σ b

------------------------------------------------------------------------
-- Uniform typings

-- The open handler clause of operation `op` in `Γ'` with result type
-- `B`, at the rigid continuation grade `evar newᵉ`: the premise of the
-- open `handle` rule

Clause : ∀ {n} → OCtx ∅ˢ n → VType → Op → Set
Clause Γ' B op =
  wkᵉ-H ∅ᴴ ∣ wkᵉ-ctx Γ' ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
               ∷ [ rconst (mapᵉ (op-grade op)) ]
                   (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v ⌜ B ⌝ᵛ ‼ evar (newᵉ {∅ˢ}))
    ⊢C⦂ wkᵉ-v ⌜ B ⌝ᵛ ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {∅ˢ}))

-- `Uᶜ Γ' M D`: `D` is a uniform typing of `M` in `Γ'`. Binders extend
-- `Γ'` by the embedding of the bound type, locks by the grade as a
-- constant, so that `⌞ Γ' ⌟ᶜᵗˣ` stays the context of `D`.
--
-- A box grade is part of the program: the raw `box ρ V N` carries it,
-- and a typing of `M` uses it. Erasure drops it only because the closed
-- `box` rule leaves its grade implicit.
--
-- Uniform handlers are the paper rule: one derivation per operation
-- clause, parametric in the continuation grade. The closed rule's
-- clause family, a function of that grade, encodes the quantifier; a
-- uniform family is the instantiation, at each grade, of one open
-- clause typing at a rigid grade variable, up to erasure. A handler-free
-- typing is uniform when it follows its term.

mutual

  data Uᵛ : ∀ {n} → OCtx ∅ˢ n → RawV ∅ˢ n → ∀ {Δ A} → Δ ⊢V⦂ A → Set where

    u-var   : ∀ {n} {Γ' : OCtx ∅ˢ n} {i : Fin n} {Δ A ρ}
              {f : ¬ Eternal A → ρ ≾ᵣ uᵣ} {x : A ∈[ ρ ] Δ}
            → CE.var-pos x ≡ toℕ i
            → Uᵛ Γ' (var i) (var f x)

    u-const : ∀ {n} {Γ' : OCtx ∅ˢ n} {Δ B} {c : BaseConstants B}
            → Uᵛ Γ' (const B c) {Δ} (const c)

    u-⋆     : ∀ {n} {Γ' : OCtx ∅ˢ n} {Δ} → Uᵛ Γ' ⋆ {Δ} ⋆
    u-true  : ∀ {n} {Γ' : OCtx ∅ˢ n} {Δ} → Uᵛ Γ' true {Δ} true
    u-false : ∀ {n} {Γ' : OCtx ∅ˢ n} {Δ} → Uᵛ Γ' false {Δ} false
    u-zero  : ∀ {n} {Γ' : OCtx ∅ˢ n} {Δ} → Uᵛ Γ' zero {Δ} zero

    u-succ  : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Δ} {V : Δ ⊢V⦂ Nat}
            → Uᵛ Γ' Vᴿ V → Uᵛ Γ' (succ Vᴿ) (succ V)

    u-pair  : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Wᴿ Δ A B} {V : Δ ⊢V⦂ A} {W : Δ ⊢V⦂ B}
            → Uᵛ Γ' Vᴿ V → Uᵛ Γ' Wᴿ W → Uᵛ Γ' ⦉ Vᴿ , Wᴿ ⦊ ⦉ V , W ⦊

    u-inl   : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Δ A B} {V : Δ ⊢V⦂ A}
            → Uᵛ Γ' Vᴿ V → Uᵛ Γ' (inl Vᴿ) (inl {B = B} V)

    u-inr   : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Δ A B} {V : Δ ⊢V⦂ B}
            → Uᵛ Γ' Vᴿ V → Uᵛ Γ' (inr Vᴿ) (inr {A = A} V)

    u-nil   : ∀ {n} {Γ' : OCtx ∅ˢ n} {Δ A} → Uᵛ Γ' nil {Δ} (nil {A = A})

    u-cons  : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Wᴿ Δ A} {V : Δ ⊢V⦂ A} {W : Δ ⊢V⦂ |List| A}
            → Uᵛ Γ' Vᴿ V → Uᵛ Γ' Wᴿ W → Uᵛ Γ' (cons Vᴿ Wᴿ) (cons V W)

    u-lam   : ∀ {n} {Γ' : OCtx ∅ˢ n} {Mᴿ Δ A C} {M : Δ ∷ A ⊢C⦂ C}
            → Uᶜ (Γ' ∷ ⌜ A ⌝ᵛ) Mᴿ M → Uᵛ Γ' (lam Mᴿ) (lam M)

    u-subV  : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Δ A A'} {V : Δ ⊢V⦂ A} {p : A <:ᵛ A'}
            → Uᵛ Γ' Vᴿ V → Uᵛ Γ' Vᴿ (subV V p)

    u-annᵛ  : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ A' Δ A} {V : Δ ⊢V⦂ A}
            → Uᵛ Γ' Vᴿ V → Uᵛ Γ' (Vᴿ ⦂ᵛ A') V

  data Uᶜ : ∀ {n} → OCtx ∅ˢ n → RawC ∅ˢ n → ∀ {Δ C} → Δ ⊢C⦂ C → Set where

    u-return : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Δ A} {V : Δ ⊢V⦂ A}
             → Uᵛ Γ' Vᴿ V → Uᶜ Γ' (return Vᴿ) (return V)

    u-seq    : ∀ {n} {Γ' : OCtx ∅ˢ n} {Mᴿ Nᴿ Δ A B ε ε'}
               {M : Δ ⊢C⦂ A ‼ ε} {N : Δ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
             → Uᶜ Γ' Mᴿ M → Uᶜ (Γ' ⟨ ∣ econst ε ∣̂ᵉ ⟩ ∷ ⌜ A ⌝ᵛ) Nᴿ N
             → Uᶜ Γ' (Mᴿ ⨟ Nᴿ) (M ⨟ N)

    u-app    : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Wᴿ Δ A C} {V : Δ ⊢V⦂ A ⇒ C} {W : Δ ⊢V⦂ A}
             → Uᵛ Γ' Vᴿ V → Uᵛ Γ' Wᴿ W → Uᶜ Γ' (Vᴿ · Wᴿ) (V · W)

    u-match  : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Mᴿ Δ A B C}
               {V : Δ ⊢V⦂ A |×| B} {M : Δ ∷ A ∷ B ⊢C⦂ C}
             → Uᵛ Γ' Vᴿ V → Uᶜ (Γ' ∷ ⌜ A ⌝ᵛ ∷ ⌜ B ⌝ᵛ) Mᴿ M
             → Uᶜ Γ' (match Vᴿ `in Mᴿ) (match V `in M)

    u-absurd : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Δ C} {V : Δ ⊢V⦂ Empty}
             → Uᵛ Γ' Vᴿ V → Uᶜ Γ' (absurd Vᴿ) (absurd {C = C} V)

    u-if     : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Mᴿ Nᴿ Δ C}
               {V : Δ ⊢V⦂ Bool} {M N : Δ ⊢C⦂ C}
             → Uᵛ Γ' Vᴿ V → Uᶜ Γ' Mᴿ M → Uᶜ Γ' Nᴿ N
             → Uᶜ Γ' (if Vᴿ `then Mᴿ `else Nᴿ) (if V `then M `else N)

    u-cmp    : ∀ {n} {Γ' : OCtx ∅ˢ n} {⋈ : Cmp} {Vᴿ Wᴿ Δ A}
               {V W : Δ ⊢V⦂ A} {et : Eternal A}
             → Uᵛ Γ' Vᴿ V → Uᵛ Γ' Wᴿ W → Uᶜ Γ' (cmp ⋈ Vᴿ Wᴿ) (cmp ⋈ V W et)

    u-caseℕ  : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Mᴿ Nᴿ Δ C}
               {V : Δ ⊢V⦂ Nat} {M : Δ ⊢C⦂ C} {N : Δ ∷ Nat ⊢C⦂ C}
             → Uᵛ Γ' Vᴿ V → Uᶜ Γ' Mᴿ M → Uᶜ (Γ' ∷ Nat) Nᴿ N
             → Uᶜ Γ' (caseℕ Vᴿ `zero Mᴿ `succ Nᴿ) (caseℕ V `zero M `succ N)

    u-case+  : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Mᴿ Nᴿ Δ A B C}
               {V : Δ ⊢V⦂ A |+| B} {M : Δ ∷ A ⊢C⦂ C} {N : Δ ∷ B ⊢C⦂ C}
             → Uᵛ Γ' Vᴿ V → Uᶜ (Γ' ∷ ⌜ A ⌝ᵛ) Mᴿ M → Uᶜ (Γ' ∷ ⌜ B ⌝ᵛ) Nᴿ N
             → Uᶜ Γ' (case+ Vᴿ `inl Mᴿ `inr Nᴿ) (case+ V `inl M `inr N)

    u-caseL  : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Mᴿ Nᴿ Δ A C}
               {V : Δ ⊢V⦂ |List| A} {M : Δ ⊢C⦂ C} {N : Δ ∷ A ∷ |List| A ⊢C⦂ C}
             → Uᵛ Γ' Vᴿ V → Uᶜ Γ' Mᴿ M → Uᶜ (Γ' ∷ ⌜ A ⌝ᵛ ∷ |List| ⌜ A ⌝ᵛ) Nᴿ N
             → Uᶜ Γ' (caseL Vᴿ `nil Mᴿ `cons Nᴿ) (caseL V `nil M `cons N)

    u-recℕ   : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Mᴿ Nᴿ Δ B ε}
               {V : Δ ⊢V⦂ Nat} {M : Δ ⊢C⦂ B ‼ ε}
               {N : (Δ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε} {p : ε ·ₑ ε ≾ₑ ε}
             → Uᵛ Γ' Vᴿ V → Uᶜ Γ' Mᴿ M
             → Uᶜ ((Γ' ⟨ rconst ⊤ᵣ ⟩ ∷ Nat) ⟨ ∣ econst ε ∣̂ᵉ ⟩ ∷ ⌜ B ⌝ᵛ) Nᴿ N
             → Uᶜ Γ' (recℕ Vᴿ Mᴿ Nᴿ) (recℕ V M N p)

    u-recL   : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Mᴿ Nᴿ Δ A B ε}
               {V : Δ ⊢V⦂ |List| A} {M : Δ ⊢C⦂ B ‼ ε}
               {N : (Δ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε} {p : ε ·ₑ ε ≾ₑ ε}
             → Uᵛ Γ' Vᴿ V → Uᶜ Γ' Mᴿ M
             → Uᶜ ((Γ' ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ A ⌝ᵛ ∷ |List| ⌜ A ⌝ᵛ) ⟨ ∣ econst ε ∣̂ᵉ ⟩ ∷ ⌜ B ⌝ᵛ) Nᴿ N
             → Uᶜ Γ' (recL Vᴿ Mᴿ Nᴿ) (recL V M N p)

    u-perform : ∀ {n} {Γ' : OCtx ∅ˢ n} {op Vᴿ Mᴿ Δ A ε}
                {V : Δ ⊢V⦂ type-of-gtype (param op)}
                {M : Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
              → Uᵛ Γ' Vᴿ V
              → Uᶜ (Γ' ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ) Mᴿ M
              → Uᶜ Γ' (perform op Vᴿ Mᴿ) (perform op V M)

    u-delay  : ∀ {n} {Γ' : OCtx ∅ˢ n} {τ Mᴿ Δ A ε} {M : Δ ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε}
             → Uᶜ (Γ' ⟨ rconst (of-durʳ τ) ⟩) Mᴿ M → Uᶜ Γ' (delay τ Mᴿ) (delay τ M)

    -- one open clause per operation, typing the raw clause, of which
    -- each member of the family is the instantiation up to erasure

    u-handle : ∀ {n} {Γ' : OCtx ∅ˢ n} {Mᴿ Hᴿ Nᴿ Δ A B ε ε'}
               {M : Δ ⊢C⦂ A ‼ ε}
               {H : (op : Op) → (ε'' : E) →
                      Δ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                      ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
               {N : Δ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
             → Uᶜ Γ' Mᴿ M
             → (Hᵒ : (op : Op) → Clause Γ' B op)
             → ((op : Op) → OE.⌊ Hᵒ op ⌋ᶜ ≡ Hᴿ op)
             → ((op : Op) → (c : E)
                → CE.⌊ H op c ⌋ᶜ ≡ CE.⌊ proj₁ (instantiateᶜ (∅ᴰ ,ᵉᴰ c) (⊨ᴰ-,ᵉ c ⊨ᴰ-∅) (Hᵒ op)) ⌋ᶜ)
             → Uᶜ (Γ' ⟨ ∣ econst ε ∣̂ᵉ ⟩ ∷ ⌜ A ⌝ᵛ) Nᴿ N
             → Uᶜ Γ' (handle Mᴿ `with Hᴿ `in Nᴿ) (handle M `with H `in N)

    u-unbox  : ∀ {n} {Γ' : OCtx ∅ˢ n} {i : Fin n} {Nᴿ Δ A A₀ C ρ₀ ρ'}
               {x : [ ρ₀ ] A₀ ∈[ ρ' ] Δ} {p : ρ' ≾ᵣ ρ₀} {q : A₀ <:ᵛ A} {N : Δ ∷ A ⊢C⦂ C}
             → CE.var-pos x ≡ toℕ i
             → Uᶜ (Γ' ∷ ⌜ A ⌝ᵛ) Nᴿ N
             → Uᶜ Γ' (unbox i Nᴿ) (unbox x p q N)

    -- the box at the program's grade

    u-box    : ∀ {n} {Γ' : OCtx ∅ˢ n} {ρ : RExp ∅ˢ} {Vᴿ Nᴿ Δ A C ρᴰ}
               {V : Δ ⟨ ρᴰ ⟩ ⊢V⦂ A} {N : Δ ∷ [ ρᴰ ] A ⊢C⦂ C}
             → ⌞ ρ ⌟ʳ ≡ ρᴰ
             → Uᵛ (Γ' ⟨ ρ ⟩) Vᴿ V → Uᶜ (Γ' ∷ [ ρ ] ⌜ A ⌝ᵛ) Nᴿ N
             → Uᶜ Γ' (box ρ Vᴿ Nᴿ) (box V N)

    u-subC   : ∀ {n} {Γ' : OCtx ∅ˢ n} {Mᴿ Δ C C'} {M : Δ ⊢C⦂ C} {p : C <:ᶜ C'}
             → Uᶜ Γ' Mᴿ M → Uᶜ Γ' Mᴿ (subC M p)

    u-annᶜ   : ∀ {n} {Γ' : OCtx ∅ˢ n} {Mᴿ C' Δ C} {M : Δ ⊢C⦂ C}
             → Uᶜ Γ' Mᴿ M → Uᶜ Γ' (Mᴿ ⦂ᶜ C') M

------------------------------------------------------------------------
-- A uniform typing erases to its term. The handler case compares
-- clause families, functions, and so uses `fun-ext`.

mutual

  uniform-⌊⌋ᵛ : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Δ A} {V : Δ ⊢V⦂ A}
              → Uᵛ Γ' Vᴿ V → CE.⌊ V ⌋ᵛ ≡ ⌊ Vᴿ ⌋ᴿᵛ
  uniform-⌊⌋ᵛ (u-var p)    = cong var p
  uniform-⌊⌋ᵛ u-const      = refl
  uniform-⌊⌋ᵛ u-⋆          = refl
  uniform-⌊⌋ᵛ u-true       = refl
  uniform-⌊⌋ᵛ u-false      = refl
  uniform-⌊⌋ᵛ u-zero       = refl
  uniform-⌊⌋ᵛ (u-succ u)   = cong succ (uniform-⌊⌋ᵛ u)
  uniform-⌊⌋ᵛ (u-pair u v) = cong₂ ⦉_,_⦊ (uniform-⌊⌋ᵛ u) (uniform-⌊⌋ᵛ v)
  uniform-⌊⌋ᵛ (u-inl u)    = cong inl (uniform-⌊⌋ᵛ u)
  uniform-⌊⌋ᵛ (u-inr u)    = cong inr (uniform-⌊⌋ᵛ u)
  uniform-⌊⌋ᵛ u-nil        = refl
  uniform-⌊⌋ᵛ (u-cons u v) = cong₂ cons (uniform-⌊⌋ᵛ u) (uniform-⌊⌋ᵛ v)
  uniform-⌊⌋ᵛ (u-lam u)    = cong lam (uniform-⌊⌋ᶜ u)
  uniform-⌊⌋ᵛ (u-subV u)   = uniform-⌊⌋ᵛ u
  uniform-⌊⌋ᵛ (u-annᵛ u)   = uniform-⌊⌋ᵛ u

  uniform-⌊⌋ᶜ : ∀ {n} {Γ' : OCtx ∅ˢ n} {Mᴿ Δ C} {M : Δ ⊢C⦂ C}
              → Uᶜ Γ' Mᴿ M → CE.⌊ M ⌋ᶜ ≡ ⌊ Mᴿ ⌋ᴿᶜ
  uniform-⌊⌋ᶜ (u-return u)      = cong return (uniform-⌊⌋ᵛ u)
  uniform-⌊⌋ᶜ (u-seq u v)       = cong₂ _⨟_ (uniform-⌊⌋ᶜ u) (uniform-⌊⌋ᶜ v)
  uniform-⌊⌋ᶜ (u-app u v)       = cong₂ _·_ (uniform-⌊⌋ᵛ u) (uniform-⌊⌋ᵛ v)
  uniform-⌊⌋ᶜ (u-match u v)     = cong₂ match_`in_ (uniform-⌊⌋ᵛ u) (uniform-⌊⌋ᶜ v)
  uniform-⌊⌋ᶜ (u-absurd u)      = cong absurd (uniform-⌊⌋ᵛ u)
  uniform-⌊⌋ᶜ (u-if u v w)      =
    cong₃ if_`then_`else_ (uniform-⌊⌋ᵛ u) (uniform-⌊⌋ᶜ v) (uniform-⌊⌋ᶜ w)
  uniform-⌊⌋ᶜ (u-cmp {⋈ = ⋈} u v) = cong₂ (cmp ⋈) (uniform-⌊⌋ᵛ u) (uniform-⌊⌋ᵛ v)
  uniform-⌊⌋ᶜ (u-caseℕ u v w)   =
    cong₃ caseℕ_`zero_`succ_ (uniform-⌊⌋ᵛ u) (uniform-⌊⌋ᶜ v) (uniform-⌊⌋ᶜ w)
  uniform-⌊⌋ᶜ (u-case+ u v w)   =
    cong₃ case+_`inl_`inr_ (uniform-⌊⌋ᵛ u) (uniform-⌊⌋ᶜ v) (uniform-⌊⌋ᶜ w)
  uniform-⌊⌋ᶜ (u-caseL u v w)   =
    cong₃ caseL_`nil_`cons_ (uniform-⌊⌋ᵛ u) (uniform-⌊⌋ᶜ v) (uniform-⌊⌋ᶜ w)
  uniform-⌊⌋ᶜ (u-recℕ u v w)    = cong₃ recℕ (uniform-⌊⌋ᵛ u) (uniform-⌊⌋ᶜ v) (uniform-⌊⌋ᶜ w)
  uniform-⌊⌋ᶜ (u-recL u v w)    = cong₃ recL (uniform-⌊⌋ᵛ u) (uniform-⌊⌋ᶜ v) (uniform-⌊⌋ᶜ w)
  uniform-⌊⌋ᶜ (u-perform {op = op} u v) =
    cong₂ (perform op) (uniform-⌊⌋ᵛ u) (uniform-⌊⌋ᶜ v)
  uniform-⌊⌋ᶜ (u-delay {τ = τ} u) = cong (delay τ) (uniform-⌊⌋ᶜ u)
  uniform-⌊⌋ᶜ (u-handle {Hᴿ = Hᴿ} u Hᵒ e m v) =
    cong₃ (λ x y z → handle x `with y `in z)
          (uniform-⌊⌋ᶜ u)
          (fun-ext λ op → fun-ext λ c →
             trans (m op c)
                   (trans (instᶜ-⌊⌋ (∅ᴰ ,ᵉᴰ c) (⊨ᴰ-,ᵉ c ⊨ᴰ-∅) (Hᵒ op))
                          (cong ⌊_⌋ᴿᶜ (e op))))
          (uniform-⌊⌋ᶜ v)
  uniform-⌊⌋ᶜ (u-unbox p u)     = cong₂ unbox p (uniform-⌊⌋ᶜ u)
  uniform-⌊⌋ᶜ (u-box _ u v)     = cong₂ box (uniform-⌊⌋ᵛ u) (uniform-⌊⌋ᶜ v)
  uniform-⌊⌋ᶜ (u-subC u)        = uniform-⌊⌋ᶜ u
  uniform-⌊⌋ᶜ (u-annᶜ u)        = uniform-⌊⌋ᶜ u

------------------------------------------------------------------------
-- Lookup: a membership in the meaning of an open context is one in the
-- context, at the same position, of a type and grade meaning its own

private

  ∷-inj : ∀ {Γ Γ' : Ctx} {A B : VType} → Γ ∷ A ≡ Γ' ∷ B → (Γ ≡ Γ') × (A ≡ B)
  ∷-inj refl = refl , refl

  ⟨⟩-inj : ∀ {Γ Γ' : Ctx} {ρ ρ' : R} → Γ ⟨ ρ ⟩ ≡ Γ' ⟨ ρ' ⟩ → (Γ ≡ Γ') × (ρ ≡ ρ')
  ⟨⟩-inj refl = refl , refl

lookupˣ : ∀ {n Δ A ρ} → (Γ' : OCtx ∅ˢ n) → ⌞ Γ' ⌟ᶜᵗˣ ≡ Δ → (x : A ∈[ ρ ] Δ)
        → Σ[ A' ∈ OVType ∅ˢ ] Σ[ ρ' ∈ RExp ∅ˢ ] Σ[ x' ∈ A' ∈̂[ ρ' ] Γ' ]
            ((⌞ A' ⌟ᵛ ≡ A) × (⌞ ρ' ⌟ʳ ≡ ρ) × (toℕ (var-pos x') ≡ CE.var-pos x))
lookupˣ []          ()  Hd
lookupˣ (Γ' ⟨ _ ⟩)  ()  Hd
lookupˣ (Γ' ∷ A')   eq  Hd = A' , ûᵣ , Hd , proj₂ (∷-inj eq) , refl , refl
lookupˣ []          ()  (Tl-∷ x)
lookupˣ (Γ' ⟨ _ ⟩)  ()  (Tl-∷ x)
lookupˣ (Γ' ∷ B')   eq  (Tl-∷ x) with ∷-inj eq
... | e , _ with lookupˣ Γ' e x
... | A' , ρ' , x' , eA , eρ , ep = A' , ρ' , Tl-∷ x' , eA , eρ , cong suc ep
lookupˣ []          ()  (Tl-⟨⟩ x)
lookupˣ (Γ' ∷ _)    ()  (Tl-⟨⟩ x)
lookupˣ (Γ' ⟨ r ⟩)  eq  (Tl-⟨⟩ x) with ⟨⟩-inj eq
... | e , er with lookupˣ Γ' e x
... | A' , ρ' , x' , eA , eρ , ep = A' , ρ' ·̂ᵣ r , Tl-⟨⟩ x' , eA , cong₂ _·ᵣ_ eρ er , ep

-- a type meaning a box type is a box type

boxView : (B' : OVType ∅ˢ) → ∀ {ρ₀ A₀} → ⌞ B' ⌟ᵛ ≡ [ ρ₀ ] A₀
        → Σ[ r ∈ RExp ∅ˢ ] Σ[ A₀' ∈ OVType ∅ˢ ]
            ((B' ≡ [ r ] A₀') × (⌞ r ⌟ʳ ≡ ρ₀) × (⌞ A₀' ⌟ᵛ ≡ A₀))
boxView (tvar ())
boxView (Base b)   ()
boxView Unit       ()
boxView Bool       ()
boxView Nat        ()
boxView (A |×| B)  ()
boxView (A |+| B)  ()
boxView (|List| A) ()
boxView Empty      ()
boxView (A ⇒ C)    ()
boxView ([ r ] A)  refl = r , A , refl , refl , refl

------------------------------------------------------------------------
-- The embedding

private

  -- a closed type meaning `A` is a subtype of `⌜ A ⌝ᵛ`

  to-⌜⌝ : (A' : OVType ∅ˢ) → ∀ {A} → ⌞ A' ⌟ᵛ ≡ A → ∅ᴴ ∣ A' <:̂ᵛ ⌜ A ⌝ᵛ
  to-⌜⌝ A' refl = ≡̂ᵛ-<:̂ ⌜⌞ A' ⌟⌝ᵛ

  -- the value of a closed grade expression is its meaning

  valʳ-⌞⌟ : (r : RExp ∅ˢ) → ∀ {c} → ⌞ r ⌟ʳ ≡ c → valʳ r ≡ c
  valʳ-⌞⌟ r e = trans (sym (⌞⌟-valʳ r)) e

  -- ground types embed as their open images

  ⌜type-of-gtype⌝ : (g : GType) → ⌜ type-of-gtype g ⌝ᵛ ≡ ⌜ g ⌝ᵍ
  ⌜type-of-gtype⌝ (Base b)   = refl
  ⌜type-of-gtype⌝ Unit       = refl
  ⌜type-of-gtype⌝ Bool       = refl
  ⌜type-of-gtype⌝ Empty      = refl
  ⌜type-of-gtype⌝ (A |×|ᵍ B) = cong₂ _|×|_ (⌜type-of-gtype⌝ A) (⌜type-of-gtype⌝ B)
  ⌜type-of-gtype⌝ ([ ρ ]ᵍ A) = cong ([ rconst ρ ]_) (⌜type-of-gtype⌝ A)

  -- an embedded computation at a convertible effect

  Emb : ∀ {n} → OCtx ∅ˢ n → OCType ∅ˢ → RawC ∅ˢ n → Set
  Emb Γ' C Mᴿ = Σ[ M' ∈ ∅ᴴ ∣ Γ' ⊢C⦂ C ] (OE.⌊ M' ⌋ᶜ ≡ Mᴿ)

  const-· : ∀ {n} {Γ' : OCtx ∅ˢ n} {A' Mᴿ} {a b : E}
          → Emb Γ' (A' ‼ (econst a ·̂ₑ econst b)) Mᴿ → Emb Γ' (A' ‼ econst (a ·ₑ b)) Mᴿ
  const-· (M' , e) = coerce (eqₑ ≡̂ₑ-const-·) M' , e

  -- the bound type of a binder

  ext : ∀ {G Δ : Ctx} → G ≡ Δ → (A : VType) → G ∷ ⌞ ⌜ A ⌝ᵛ ⌟ᵛ ≡ Δ ∷ A
  ext eq A = cong₂ _∷_ eq ⌞⌜ A ⌝⌟ᵛ

  lock : ∀ {G Δ : Ctx} → G ≡ Δ → (ρ : R) → G ⟨ ρ ⟩ ≡ Δ ⟨ ρ ⟩
  lock eq ρ = cong (_⟨ ρ ⟩) eq

-- A uniform typing in a context meaning `Δ` is an open typing at the
-- empty scope, of the embedded type, erasing to the term

mutual

  embedᵛ : ∀ {n} {Γ' : OCtx ∅ˢ n} {Vᴿ Δ A} {V : Δ ⊢V⦂ A}
         → Uᵛ Γ' Vᴿ V → AnnFreeᵛ Vᴿ → ⌞ Γ' ⌟ᶜᵗˣ ≡ Δ
         → Σ[ V' ∈ ∅ᴴ ∣ Γ' ⊢V⦂ ⌜ A ⌝ᵛ ] (OE.⌊ V' ⌋ᵛ ≡ Vᴿ)
  embedᵛ {Γ' = Γ'} (u-var {A = A} {f = f} {x = x} p) _ eq with lookupˣ Γ' eq x
  ... | A' , ρ' , x' , eA , eρ , ep =
    subV (var x' ok) (to-⌜⌝ A' eA) , cong var (toℕ-injective (trans ep p))
    where
      ok : VarOK ∅ᴴ A' ρ'
      ok with eternal? A
      ... | yes et = et-ok (⌞⌟-⊩ᴱ A' (subst Eternal (sym eA) et))
      ... | no ¬et = ≾ᵘ-ok (val-≾ᵣ⁻ (subst (_≾ᵣ uᵣ) (sym (valʳ-⌞⌟ ρ' eρ)) (f ¬et)))
  embedᵛ u-const      _ eq = const _ _ , refl
  embedᵛ u-⋆          _ eq = ⋆ , refl
  embedᵛ u-true       _ eq = true , refl
  embedᵛ u-false      _ eq = false , refl
  embedᵛ u-zero       _ eq = zero , refl
  embedᵛ (u-succ u)   a eq with embedᵛ u a eq
  ... | V' , e = succ V' , cong succ e
  embedᵛ (u-pair u v) (a , b) eq with embedᵛ u a eq | embedᵛ v b eq
  ... | V' , e | W' , e' = ⦉ V' , W' ⦊ , cong₂ ⦉_,_⦊ e e'
  embedᵛ (u-inl u)    a eq with embedᵛ u a eq
  ... | V' , e = inl V' , cong inl e
  embedᵛ (u-inr u)    a eq with embedᵛ u a eq
  ... | V' , e = inr V' , cong inr e
  embedᵛ u-nil        _ eq = nil , refl
  embedᵛ (u-cons u v) (a , b) eq with embedᵛ u a eq | embedᵛ v b eq
  ... | V' , e | W' , e' = cons V' W' , cong₂ cons e e'
  embedᵛ (u-lam {A = A} u) a eq with embedᶜ u a (ext eq A)
  ... | M' , e = lam M' , cong lam e
  embedᵛ (u-subV {p = p} u) a eq with embedᵛ u a eq
  ... | V' , e = subV V' (⌜⌝-<:ᵛ p) , e
  embedᵛ (u-annᵛ u) () eq

  embedᶜ : ∀ {n} {Γ' : OCtx ∅ˢ n} {Mᴿ Δ C} {M : Δ ⊢C⦂ C}
         → Uᶜ Γ' Mᴿ M → AnnFreeᶜ Mᴿ → ⌞ Γ' ⌟ᶜᵗˣ ≡ Δ
         → Emb Γ' ⌜ C ⌝ᶜ Mᴿ
  embedᶜ (u-return u) a eq with embedᵛ u a eq
  ... | V' , e = return V' , cong return e
  embedᶜ (u-seq {A = A} {ε = ε} u v) (a , b) eq
    with embedᶜ u a eq | embedᶜ v b (ext (cong (_⟨ mapᵉ ε ⟩) eq) A)
  ... | M' , e | N' , e' = const-· (M' ⨟ N' , cong₂ _⨟_ e e')
  embedᶜ (u-app u v) (a , b) eq with embedᵛ u a eq | embedᵛ v b eq
  ... | V' , e | W' , e' = V' · W' , cong₂ _·_ e e'
  embedᶜ (u-match {A = A} {B = B} u v) (a , b) eq
    with embedᵛ u a eq | embedᶜ v b (ext (ext eq A) B)
  ... | V' , e | M' , e' = match V' `in M' , cong₂ match_`in_ e e'
  embedᶜ (u-absurd u) a eq with embedᵛ u a eq
  ... | V' , e = absurd V' , cong absurd e
  embedᶜ (u-if u v w) (a , b , c) eq with embedᵛ u a eq | embedᶜ v b eq | embedᶜ w c eq
  ... | V' , e | M' , e' | N' , e'' =
    if V' `then M' `else N' , cong₃ if_`then_`else_ e e' e''
  embedᶜ (u-cmp {⋈ = ⋈} {A = A} {et = et} u v) (a , b) eq
    with embedᵛ u a eq | embedᵛ v b eq
  ... | V' , e | W' , e' =
    cmp ⋈ V' W' (⌞⌟-⊩ᴱ ⌜ A ⌝ᵛ (subst Eternal (sym ⌞⌜ A ⌝⌟ᵛ) et)) , cong₂ (cmp ⋈) e e'
  embedᶜ (u-caseℕ u v w) (a , b , c) eq
    with embedᵛ u a eq | embedᶜ v b eq | embedᶜ w c (ext eq Nat)
  ... | V' , e | M' , e' | N' , e'' =
    caseℕ V' `zero M' `succ N' , cong₃ caseℕ_`zero_`succ_ e e' e''
  embedᶜ (u-case+ {A = A} {B = B} u v w) (a , b , c) eq
    with embedᵛ u a eq | embedᶜ v b (ext eq A) | embedᶜ w c (ext eq B)
  ... | V' , e | M' , e' | N' , e'' =
    case+ V' `inl M' `inr N' , cong₃ case+_`inl_`inr_ e e' e''
  embedᶜ (u-caseL {A = A} u v w) (a , b , c) eq
    with embedᵛ u a eq | embedᶜ v b eq | embedᶜ w c (ext (ext eq A) (|List| A))
  ... | V' , e | M' , e' | N' , e'' =
    caseL V' `nil M' `cons N' , cong₃ caseL_`nil_`cons_ e e' e''
  embedᶜ (u-recℕ {B = B} {ε = ε} {p = p} u v w) (a , b , c) eq
    with embedᵛ u a eq | embedᶜ v b eq
       | embedᶜ w c (ext (cong (_⟨ mapᵉ ε ⟩) (ext (lock eq ⊤ᵣ) Nat)) B)
  ... | V' , e | M' , e' | N' , e'' =
    recℕ V' M' N' (val-≾ₑ⁻ p) , cong₃ recℕ e e' e''
  embedᶜ (u-recL {A = A} {B = B} {ε = ε} {p = p} u v w) (a , b , c) eq
    with embedᵛ u a eq | embedᶜ v b eq
       | embedᶜ w c (ext (cong (_⟨ mapᵉ ε ⟩) (ext (ext (lock eq ⊤ᵣ) A) (|List| A))) B)
  ... | V' , e | M' , e' | N' , e'' =
    recL V' M' N' (val-≾ₑ⁻ p) , cong₃ recL e e' e''
  embedᶜ (u-perform {op = op} u v) (a , b) eq
    with embedᵛ u a eq
       | embedᶜ v b (cong₂ _∷_ (lock eq (mapᵉ (op-grade op))) (⟦⌜ arity op ⌝ᵍ⟧ ∅ᴰ))
  ... | V' , e | M' , e' =
    const-· (perform op (ty-subst (⌜type-of-gtype⌝ (param op)) V') M' ,
             cong₂ (perform op) (trans (⌊ty-subst⌋ (⌜type-of-gtype⌝ (param op)) V') e) e')
    where
      ⌊ty-subst⌋ : ∀ {n} {Γ' : OCtx ∅ˢ n} {A A'} → (q : A ≡ A') → (W : ∅ᴴ ∣ Γ' ⊢V⦂ A)
                 → OE.⌊ ty-subst q W ⌋ᵛ ≡ OE.⌊ W ⌋ᵛ
      ⌊ty-subst⌋ refl W = refl
  embedᶜ (u-delay {τ = τ} u) a eq with embedᶜ u a (lock eq (of-durʳ τ))
  ... | M' , e = const-· (delay τ M' , cong (delay τ) e)
  -- the raw clauses are a function of the operation, compared by `fun-ext`
  embedᶜ (u-handle {A = A} {ε = ε} u Hᵒ eH _ v) (a , _ , b) eq
    with embedᶜ u a eq | embedᶜ v b (ext (cong (_⟨ mapᵉ ε ⟩) eq) A)
  ... | M' , e | N' , e' =
    const-· (handle M' `with Hᵒ `in N' ,
             cong₃ (λ x y z → handle x `with y `in z) e (fun-ext eH) e')
  embedᶜ {Γ' = Γ'} (u-unbox {A = A} {x = x} {p = p} {q = q} ep u) a eq
    with lookupˣ Γ' eq x
  ... | B' , ρ' , x' , eB , eρ , epos with boxView B' eB
  ... | r , A₀' , refl , er , eA₀ with embedᶜ u a (ext eq A)
  ... | N' , e =
    unbox x' (val-≾ᵣ⁻ (subst₂ _≾ᵣ_ (sym (valʳ-⌞⌟ ρ' eρ)) (sym (valʳ-⌞⌟ r er)) p))
             (⌞⌟-<:ᵛ A₀' ⌜ A ⌝ᵛ (subst₂ _<:ᵛ_ (sym eA₀) (sym ⌞⌜ A ⌝⌟ᵛ) q)) N' ,
    cong₂ unbox (toℕ-injective (trans epos ep)) e
  embedᶜ (u-box {ρ = ρ} {A = A} er u v) (a , b) eq
    with embedᵛ u a (cong₂ _⟨_⟩ eq er)
       | embedᶜ v b (cong₂ _∷_ eq (cong₂ [_]_ er ⌞⌜ A ⌝⌟ᵛ))
  ... | V' , e | N' , e' = box ρ V' N' , cong₂ (box ρ) e e'
  embedᶜ (u-subC {p = p} u) a eq with embedᶜ u a eq
  ... | M' , e = subC M' (⌜⌝-<:ᶜ p) , e
  embedᶜ (u-annᶜ u) () eq
