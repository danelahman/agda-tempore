------------------------------------------------------------------
-- Embedding uniform declarative typings in the open calculus   --
--                                                              --
-- A declarative typing `D : Δ ⊢C⦂ C` of the elaboration of a   --
-- closed raw term `M` is uniform in an open context `Γ'`       --
-- (`Uᶜ Γ' r P M D`) when it follows `M` former by former, each --
-- box at `M`'s grade, each `handle` of `M` with a handler as   --
-- its handler, the clauses typed by one open clause typing at  --
-- a rigid continuation grade, and each                         --
-- comparison of `M`'s values read off the outcome of a         --
-- comparison run before it (`u-hoist`, `u-out`). The context   --
-- of `D` has the outcomes interleaved with the meaning of      --
-- `Γ'`: `r` gives the positions of `Γ'`'s variables, `P` the   --
-- outcomes pending for the values of the current computation.  --
-- Annotations of `M` are passed over; `AnnFreeᶜ M` says there  --
-- are none.                                                    --
--                                                              --
-- A uniform typing in a context `Γ'` meaning `Δ`, with no      --
-- handler type, embeds as an open typing                       --
-- `∅ᴴ ∣ Γ' ⊢C⦂ ⌜ C ⌝ᶜ` at the empty scope erasing to `M`       --
-- (`embedᶜ`, `embedᵛ`). Grades of `Γ'` and `M` are             --
-- expressions, those of `D` their values; they meet through    --
-- `⌞_⌟` and the conversion of a closed expression to its value.--
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.List.Base as List using (List; []; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; yes; no)

open import Grades.Base
open import Language.Spec
open import Language.Operations
open import Language.Comparisons using (Cmp)

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module Bridge.Instantiation.Embedding (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Language.Types                 S
open import ClosedCalculus.Syntax.Contexts S
open import ClosedCalculus.Syntax.Terms    S hiding (coerce; numeralᵛ)
open import ClosedCalculus.Syntax.Erasure  S hiding (⌊_⌋ᵛ; ⌊_⌋ᶜ; var-pos)
import ClosedCalculus.Syntax.Erasure S as CE

open import OpenCalculus.Syntax.Grades        S
open import OpenCalculus.Syntax.Types         S
open import OpenCalculus.Syntax.Contexts      S
open import OpenCalculus.Syntax.Subst         S
open import OpenCalculus.Hypotheses           S
open import OpenCalculus.Typing               S
open import OpenCalculus.Typing.Conversion    S using (narrowing; conv-last)
open import OpenCalculus.Hypotheses.Instances S using (val-≾ᵣ⁻; val-≾ₑ⁻)
open import OpenCalculus.Syntax.Raw           S
open import OpenCalculus.Syntax.Raw.Subst     S
import OpenCalculus.Typing.Erasure S as OE

open import Bridge.Instantiation.Types          S
open import Bridge.Instantiation.Judgements     S
open import Bridge.Instantiation.Correspondence S
open import Bridge.Instantiation.Hoisting       S

------------------------------------------------------------------------
-- Raw terms without type annotations

mutual

  AnnFreeᵛ : ∀ {Θ n} → RawV Θ n → Set
  AnnFreeᵛ (succ V)    = AnnFreeᵛ V
  AnnFreeᵛ ⦉ V , W ⦊    = AnnFreeᵛ V × AnnFreeᵛ W
  AnnFreeᵛ (inl V)     = AnnFreeᵛ V
  AnnFreeᵛ (inr V)     = AnnFreeᵛ V
  AnnFreeᵛ (cons V W)  = AnnFreeᵛ V × AnnFreeᵛ W
  AnnFreeᵛ (cmp ⋈ V W) = AnnFreeᵛ V × AnnFreeᵛ W
  AnnFreeᵛ (lam M)     = AnnFreeᶜ M
  AnnFreeᵛ (handler N H) = AnnFreeᶜ N × ((op : Op) → AnnFreeᶜ (H op))
  AnnFreeᵛ (V ⦂ᵛ A)    = ⊥
  AnnFreeᵛ _           = ⊤

  AnnFreeᶜ : ∀ {Θ n} → RawC Θ n → Set
  AnnFreeᶜ (return V)                = AnnFreeᵛ V
  AnnFreeᶜ (M ⨟ N)                   = AnnFreeᶜ M × AnnFreeᶜ N
  AnnFreeᶜ (V · W)                   = AnnFreeᵛ V × AnnFreeᵛ W
  AnnFreeᶜ (match V `in M)           = AnnFreeᵛ V × AnnFreeᶜ M
  AnnFreeᶜ (absurd V)                = AnnFreeᵛ V
  AnnFreeᶜ (if V `then M `else N)    = AnnFreeᵛ V × AnnFreeᶜ M × AnnFreeᶜ N
  AnnFreeᶜ (caseℕ V `zero M `succ N) = AnnFreeᵛ V × AnnFreeᶜ M × AnnFreeᶜ N
  AnnFreeᶜ (case+ V `inl M `inr N)   = AnnFreeᵛ V × AnnFreeᶜ M × AnnFreeᶜ N
  AnnFreeᶜ (recℕ V M N)              = AnnFreeᵛ V × AnnFreeᶜ M × AnnFreeᶜ N
  AnnFreeᶜ (caseL V `nil M `cons N)  = AnnFreeᵛ V × AnnFreeᶜ M × AnnFreeᶜ N
  AnnFreeᶜ (recL V M N)              = AnnFreeᵛ V × AnnFreeᶜ M × AnnFreeᶜ N
  AnnFreeᶜ (perform op V M)          = AnnFreeᵛ V × AnnFreeᶜ M
  AnnFreeᶜ (delay τ M)               = AnnFreeᶜ M
  AnnFreeᶜ (handle M `with V)       = AnnFreeᶜ M × AnnFreeᵛ V
  AnnFreeᶜ (unbox V N)               = AnnFreeᵛ V × AnnFreeᶜ N
  AnnFreeᶜ (box ρ V N)               = AnnFreeᵛ V × AnnFreeᶜ N
  AnnFreeᶜ (M ⦂ᶜ C)                  = ⊥

-- Substitution keeps a term annotation-free

mutual

  annFree-[]ᵛ : ∀ {Θ Θ' n} → (V : RawV Θ n) → (σ : Subst Θ Θ')
              → AnnFreeᵛ V → AnnFreeᵛ (V [ σ ]ᴿᵛ)
  annFree-[]ᵛ (var i)     σ a       = tt
  annFree-[]ᵛ (def k)     σ a       = tt
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
  annFree-[]ᵛ (cmp ⋈ V W) σ (a , b) = annFree-[]ᵛ V σ a , annFree-[]ᵛ W σ b
  annFree-[]ᵛ (lam M)     σ a       = annFree-[]ᶜ M σ a
  annFree-[]ᵛ (handler N H) σ (a , h) =
    annFree-[]ᶜ N σ a , (λ op → annFree-[]ᶜ (H op) (σ ↑ᵉ) (h op))

  annFree-[]ᶜ : ∀ {Θ Θ' n} → (M : RawC Θ n) → (σ : Subst Θ Θ')
              → AnnFreeᶜ M → AnnFreeᶜ (M [ σ ]ᴿᶜ)
  annFree-[]ᶜ (return V)                σ a = annFree-[]ᵛ V σ a
  annFree-[]ᶜ (M ⨟ N)                   σ (a , b) = annFree-[]ᶜ M σ a , annFree-[]ᶜ N σ b
  annFree-[]ᶜ (V · W)                   σ (a , b) = annFree-[]ᵛ V σ a , annFree-[]ᵛ W σ b
  annFree-[]ᶜ (match V `in M)           σ (a , b) = annFree-[]ᵛ V σ a , annFree-[]ᶜ M σ b
  annFree-[]ᶜ (absurd V)                σ a = annFree-[]ᵛ V σ a
  annFree-[]ᶜ (if V `then M `else N)    σ (a , b , c) =
    annFree-[]ᵛ V σ a , annFree-[]ᶜ M σ b , annFree-[]ᶜ N σ c
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
  annFree-[]ᶜ (handle M `with V)       σ (a , b) = annFree-[]ᶜ M σ a , annFree-[]ᵛ V σ b
  annFree-[]ᶜ (unbox V N)               σ (a , b) = annFree-[]ᵛ V σ a , annFree-[]ᶜ N σ b
  annFree-[]ᶜ (box ρ V N)               σ (a , b) = annFree-[]ᵛ V σ a , annFree-[]ᶜ N σ b

------------------------------------------------------------------------
-- Uniform typings

-- The open handler clause of operation `op` in `Γ'` with result type
-- `B`, at the rigid continuation grade `evar newᵉ`: the premise of the
-- open `handler` rule

Clause : ∀ {n} → OCtx ∅ˢ n → VType → Op → Set
Clause Γ' B op =
  wkᵉ-H ∅ᴴ ∣ wkᵉ-ctx Γ' ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
               ∷ [ rconst (mapᵉ (op-grade op)) ]
                   (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v ⌜ B ⌝ᵛ ‼ evar (newᵉ {∅ˢ}))
    ⊢C⦂ wkᵉ-v ⌜ B ⌝ᵛ ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {∅ˢ}))

-- A comparison of the raw term run before the current computation: its
-- operands and its outcome variable

record Pending (Δ : Ctx) (n : ℕ) : Set where
  constructor pending
  field
    rel   : Cmp
    left  : RawV ∅ˢ n
    right : RawV ∅ˢ n
    {gr}  : R
    out   : Bool ∈[ gr ] Δ

open Pending

-- under one more outcome, and under a lock

wkᴾ : ∀ {Δ n} → List (Pending Δ n) → List (Pending (Δ ▷ᵇ) n)
wkᴾ = map (λ p → pending (rel p) (left p) (right p) (Tl-∷ (Tl-⟨⟩ (out p))))

lockᴾ : ∀ {Δ n ρ} → List (Pending Δ n) → List (Pending (Δ ⟨ ρ ⟩) n)
lockᴾ = map (λ p → pending (rel p) (left p) (right p) (Tl-⟨⟩ (out p)))

-- `Uᶜ Γ' r P M D`: `D` is a uniform typing of `M` in `Γ'`, the
-- positions of `Γ'`'s variables given by `r` and the pending outcomes
-- by `P`. Binders extend `Γ'` by the embedding of the bound type, locks
-- by the grade as a constant, so that `⌞ Γ' ⌟ᶜᵗˣ` maps into the context
-- of `D`. Outcomes are pending only for the values of the computation
-- that hoists them.
--
-- A box grade is part of the program: the raw `box ρ V N` carries it,
-- and the declarative box of a uniform typing is at its value `⌞ ρ ⌟ʳ`.
--
-- Uniform handlers follow the rule of the open calculus: one derivation
-- per operation clause, parametric in the continuation grade, typing
-- the raw clause.

mutual

  data Uᵛ : ∀ {n} → OCtx ∅ˢ n → RMap → ∀ {Δ} → List (Pending Δ n)
          → RawV ∅ˢ n → ∀ {A} → Δ ⊢V⦂ A → Set where

    u-var   : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P} {i : Fin n} {A ρ}
              {f : ¬ Eternal A → ρ ≾ᵣ uᵣ} {x : A ∈[ ρ ] Δ}
            → CE.var-pos x ≡ posᴿ r (toℕ i)
            → Uᵛ Γ' r P (var i) (var f x)

    -- a comparison, read off its outcome

    u-out   : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ} {P : List (Pending Δ n)} {⋈ Vᴿ Wᴿ ρ}
              {f : ¬ Eternal Bool → ρ ≾ᵣ uᵣ} {x : Bool ∈[ ρ ] Δ}
            → pending ⋈ Vᴿ Wᴿ x ∈ P
            → Uᵛ Γ' r P (cmp ⋈ Vᴿ Wᴿ) (var f x)

    u-const : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ} {P : List (Pending Δ n)} {B} {c : BaseConstants B}
            → Uᵛ Γ' r P (const B c) (const c)

    u-⋆     : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ} {P : List (Pending Δ n)} → Uᵛ Γ' r P ⋆ ⋆
    u-true  : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ} {P : List (Pending Δ n)} → Uᵛ Γ' r P true true
    u-false : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ} {P : List (Pending Δ n)} → Uᵛ Γ' r P false false
    u-zero  : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ} {P : List (Pending Δ n)} → Uᵛ Γ' r P zero zero

    u-succ  : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ} {V : Δ ⊢V⦂ Nat}
            → Uᵛ Γ' r P Vᴿ V → Uᵛ Γ' r P (succ Vᴿ) (succ V)

    u-pair  : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ Wᴿ A B} {V : Δ ⊢V⦂ A} {W : Δ ⊢V⦂ B}
            → Uᵛ Γ' r P Vᴿ V → Uᵛ Γ' r P Wᴿ W → Uᵛ Γ' r P ⦉ Vᴿ , Wᴿ ⦊ ⦉ V , W ⦊

    u-inl   : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ A B} {V : Δ ⊢V⦂ A}
            → Uᵛ Γ' r P Vᴿ V → Uᵛ Γ' r P (inl Vᴿ) (inl {B = B} V)

    u-inr   : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ A B} {V : Δ ⊢V⦂ B}
            → Uᵛ Γ' r P Vᴿ V → Uᵛ Γ' r P (inr Vᴿ) (inr {A = A} V)

    u-nil   : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ} {P : List (Pending Δ n)} {A}
            → Uᵛ Γ' r P nil (nil {A = A})

    u-cons  : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ Wᴿ A} {V : Δ ⊢V⦂ A} {W : Δ ⊢V⦂ |List| A}
            → Uᵛ Γ' r P Vᴿ V → Uᵛ Γ' r P Wᴿ W → Uᵛ Γ' r P (cons Vᴿ Wᴿ) (cons V W)

    u-lam   : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ} {P : List (Pending Δ n)} {Mᴿ A C}
              {M : Δ ∷ A ⊢C⦂ C}
            → Uᶜ (Γ' ∷ ⌜ A ⌝ᵛ) (extᴿ r) [] Mᴿ M → Uᵛ Γ' r P (lam Mᴿ) (lam M)

    u-subV  : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ A A'} {V : Δ ⊢V⦂ A} {p : A <:ᵛ A'}
            → Uᵛ Γ' r P Vᴿ V → Uᵛ Γ' r P Vᴿ (subV V p)

    u-annᵛ  : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ A' A} {V : Δ ⊢V⦂ A}
            → Uᵛ Γ' r P Vᴿ V → Uᵛ Γ' r P (Vᴿ ⦂ᵛ A') V

  data Uᶜ : ∀ {n} → OCtx ∅ˢ n → RMap → ∀ {Δ} → List (Pending Δ n)
          → RawC ∅ˢ n → ∀ {C} → Δ ⊢C⦂ C → Set where

    -- a comparison of the term run before the current computation, its
    -- outcome pending for the computation's values

    u-hoist  : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Mᴿ ⋈ Vᴿ Wᴿ B B' ε'}
               {V W : Δ ⊢V⦂ B} {et : Eternal B} {N : Δ ⟨ mapᵉ uₑ ⟩ ∷ Bool ⊢C⦂ B' ‼ ε'}
             → AnnFreeᵛ Vᴿ → AnnFreeᵛ Wᴿ
             → Uᵛ Γ' r P Vᴿ V → Uᵛ Γ' r P Wᴿ W
             → Uᶜ Γ' (shᴿ r) (pending ⋈ Vᴿ Wᴿ Hd List.∷ wkᴾ P) Mᴿ N
             → Uᶜ Γ' r P Mᴿ (cmp ⋈ V W et ⨟ N)

    u-return : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ A} {V : Δ ⊢V⦂ A}
             → Uᵛ Γ' r P Vᴿ V → Uᶜ Γ' r P (return Vᴿ) (return V)

    u-seq    : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ} {P : List (Pending Δ n)} {Mᴿ Nᴿ A B ε ε'}
               {M : Δ ⊢C⦂ A ‼ ε} {N : Δ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
             → Uᶜ Γ' r [] Mᴿ M → Uᶜ (Γ' ⟨ ∣ econst ε ∣̂ᵉ ⟩ ∷ ⌜ A ⌝ᵛ) (extᴿ r) [] Nᴿ N
             → Uᶜ Γ' r P (Mᴿ ⨟ Nᴿ) (M ⨟ N)

    u-app    : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ Wᴿ A C} {V : Δ ⊢V⦂ A ⇒ C} {W : Δ ⊢V⦂ A}
             → Uᵛ Γ' r P Vᴿ V → Uᵛ Γ' r P Wᴿ W → Uᶜ Γ' r P (Vᴿ · Wᴿ) (V · W)

    u-match  : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ Mᴿ A B C}
               {V : Δ ⊢V⦂ A |×| B} {M : Δ ∷ A ∷ B ⊢C⦂ C}
             → Uᵛ Γ' r P Vᴿ V → Uᶜ (Γ' ∷ ⌜ A ⌝ᵛ ∷ ⌜ B ⌝ᵛ) (extᴿ (extᴿ r)) [] Mᴿ M
             → Uᶜ Γ' r P (match Vᴿ `in Mᴿ) (match V `in M)

    u-absurd : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ C} {V : Δ ⊢V⦂ Empty}
             → Uᵛ Γ' r P Vᴿ V → Uᶜ Γ' r P (absurd Vᴿ) (absurd {C = C} V)

    u-if     : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ Mᴿ Nᴿ C}
               {V : Δ ⊢V⦂ Bool} {M N : Δ ⊢C⦂ C}
             → Uᵛ Γ' r P Vᴿ V → Uᶜ Γ' r [] Mᴿ M → Uᶜ Γ' r [] Nᴿ N
             → Uᶜ Γ' r P (if Vᴿ `then Mᴿ `else Nᴿ) (if V `then M `else N)

    u-caseℕ  : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ Mᴿ Nᴿ C}
               {V : Δ ⊢V⦂ Nat} {M : Δ ⊢C⦂ C} {N : Δ ∷ Nat ⊢C⦂ C}
             → Uᵛ Γ' r P Vᴿ V → Uᶜ Γ' r [] Mᴿ M → Uᶜ (Γ' ∷ Nat) (extᴿ r) [] Nᴿ N
             → Uᶜ Γ' r P (caseℕ Vᴿ `zero Mᴿ `succ Nᴿ) (caseℕ V `zero M `succ N)

    u-case+  : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ Mᴿ Nᴿ A B C}
               {V : Δ ⊢V⦂ A |+| B} {M : Δ ∷ A ⊢C⦂ C} {N : Δ ∷ B ⊢C⦂ C}
             → Uᵛ Γ' r P Vᴿ V → Uᶜ (Γ' ∷ ⌜ A ⌝ᵛ) (extᴿ r) [] Mᴿ M
             → Uᶜ (Γ' ∷ ⌜ B ⌝ᵛ) (extᴿ r) [] Nᴿ N
             → Uᶜ Γ' r P (case+ Vᴿ `inl Mᴿ `inr Nᴿ) (case+ V `inl M `inr N)

    u-caseL  : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ Mᴿ Nᴿ A C}
               {V : Δ ⊢V⦂ |List| A} {M : Δ ⊢C⦂ C} {N : Δ ∷ A ∷ |List| A ⊢C⦂ C}
             → Uᵛ Γ' r P Vᴿ V → Uᶜ Γ' r [] Mᴿ M
             → Uᶜ (Γ' ∷ ⌜ A ⌝ᵛ ∷ |List| ⌜ A ⌝ᵛ) (extᴿ (extᴿ r)) [] Nᴿ N
             → Uᶜ Γ' r P (caseL Vᴿ `nil Mᴿ `cons Nᴿ) (caseL V `nil M `cons N)

    u-recℕ   : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ Mᴿ Nᴿ B ε}
               {V : Δ ⊢V⦂ Nat} {M : Δ ⊢C⦂ B ‼ ε}
               {N : (Δ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε} {p : ε ·ₑ ε ≾ₑ ε}
             → Uᵛ Γ' r P Vᴿ V → Uᶜ Γ' r [] Mᴿ M
             → Uᶜ ((Γ' ⟨ rconst ⊤ᵣ ⟩ ∷ Nat) ⟨ ∣ econst ε ∣̂ᵉ ⟩ ∷ ⌜ B ⌝ᵛ) (extᴿ (extᴿ r)) [] Nᴿ N
             → Uᶜ Γ' r P (recℕ Vᴿ Mᴿ Nᴿ) (recℕ V M N p)

    u-recL   : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ Mᴿ Nᴿ A B ε}
               {V : Δ ⊢V⦂ |List| A} {M : Δ ⊢C⦂ B ‼ ε}
               {N : (Δ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε} {p : ε ·ₑ ε ≾ₑ ε}
             → Uᵛ Γ' r P Vᴿ V → Uᶜ Γ' r [] Mᴿ M
             → Uᶜ ((Γ' ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ A ⌝ᵛ ∷ |List| ⌜ A ⌝ᵛ) ⟨ ∣ econst ε ∣̂ᵉ ⟩ ∷ ⌜ B ⌝ᵛ)
                  (extᴿ (extᴿ (extᴿ r))) [] Nᴿ N
             → Uᶜ Γ' r P (recL Vᴿ Mᴿ Nᴿ) (recL V M N p)

    u-perform : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P op Vᴿ Mᴿ A ε}
                {V : Δ ⊢V⦂ type-of-gtype (param op)}
                {M : Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
              → Uᵛ Γ' r P Vᴿ V
              → Uᶜ (Γ' ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ) (extᴿ r) [] Mᴿ M
              → Uᶜ Γ' r P (perform op Vᴿ Mᴿ) (perform op V M)

    u-delay  : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ} {P : List (Pending Δ n)} {τ Mᴿ A ε}
               {M : Δ ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε}
             → Uᶜ (Γ' ⟨ rconst (of-durʳ τ) ⟩) r [] Mᴿ M → Uᶜ Γ' r P (delay τ Mᴿ) (delay τ M)

    -- a `handle` whose handler is a handler, one open clause per
    -- operation, typing the raw clause

    u-handle : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ} {P : List (Pending Δ n)} {Mᴿ Hᴿ Nᴿ A B ε ε'}
               {M : Δ ⊢C⦂ A ‼ ε}
               {H : (op : Op) → (ε'' : E) →
                      Δ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                      ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
               {N : Δ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
             → Uᶜ Γ' r [] Mᴿ M
             → (Hᵒ : (op : Op) → Clause Γ' B op)
             → ((op : Op) → OE.⌊ Hᵒ op ⌋ᶜ ≡ Hᴿ op)
             → Uᶜ (Γ' ⟨ ∣ econst ε ∣̂ᵉ ⟩ ∷ ⌜ A ⌝ᵛ) (extᴿ r) [] Nᴿ N
             → Uᶜ Γ' r P (handle Mᴿ `with handler Nᴿ Hᴿ) (handle M `with H `in N)

    u-unbox  : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ} {P : List (Pending Δ n)} {i : Fin n}
               {Nᴿ A A₀ C ρ₀ ρ'}
               {x : [ ρ₀ ] A₀ ∈[ ρ' ] Δ} {p : ρ' ≾ᵣ ρ₀} {q : A₀ <:ᵛ A} {N : Δ ∷ A ⊢C⦂ C}
             → CE.var-pos x ≡ posᴿ r (toℕ i)
             → Uᶜ (Γ' ∷ ⌜ A ⌝ᵛ) (extᴿ r) [] Nᴿ N
             → Uᶜ Γ' r P (unbox (var i) Nᴿ) (unbox x p q N)

    -- the box at the program's grade; the boxed value reads the pending
    -- outcomes across the box's lock

    u-box    : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P} {ρ : RExp ∅ˢ} {Vᴿ Nᴿ A C}
               {V : Δ ⟨ ⌞ ρ ⌟ʳ ⟩ ⊢V⦂ A} {N : Δ ∷ [ ⌞ ρ ⌟ʳ ] A ⊢C⦂ C}
             → Uᵛ (Γ' ⟨ ρ ⟩) r (lockᴾ P) Vᴿ V → Uᶜ (Γ' ∷ [ ρ ] ⌜ A ⌝ᵛ) (extᴿ r) [] Nᴿ N
             → Uᶜ Γ' r P (box ρ Vᴿ Nᴿ) (box ⌞ ρ ⌟ʳ V N)

    u-subC   : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Mᴿ C C'} {M : Δ ⊢C⦂ C} {p : C <:ᶜ C'}
             → Uᶜ Γ' r P Mᴿ M → Uᶜ Γ' r P Mᴿ (subC M p)

    u-annᶜ   : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Mᴿ C' C} {M : Δ ⊢C⦂ C}
             → Uᶜ Γ' r P Mᴿ M → Uᶜ Γ' r P (Mᴿ ⦂ᶜ C') M

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
boxView (C ⇛ D)    ()
boxView ([ r ] A)  refl = r , A , refl , refl , refl

------------------------------------------------------------------------
-- A variable of the closed context, at a position the map gives to a
-- variable of its source, is that variable, at a grade above its own

unlook : ∀ {G Δ A ρ} → (ι : G ≼ Δ) → Exact ι → (x : A ∈[ ρ ] Δ) → (k : ℕ)
       → CE.var-pos x ≡ posᴿ ⌊ ι ⌋ᵐ k
       → Σ[ ρ₀ ∈ R ] Σ[ x₀ ∈ A ∈[ ρ₀ ] G ] ((ρ₀ ≾ᵣ ρ) × (CE.var-pos x₀ ≡ k))
unlook ≼-refl   f x         k       p = _ , x , ≾ᵣ-refl , p
unlook (≼-∷ ι)  f Hd        zero    p = _ , Hd , ≾ᵣ-refl , refl
unlook (≼-∷ ι)  f Hd        (suc k) ()
unlook (≼-∷ ι)  f (Tl-∷ x)  zero    ()
unlook (≼-∷ ι)  f (Tl-∷ x)  (suc k) p =
  proj₁ l , Tl-∷ (proj₁ (proj₂ l)) , proj₁ (proj₂ (proj₂ l)) ,
  cong suc (proj₂ (proj₂ (proj₂ l)))
  where l = unlook ι f x k (suc-injective p)
unlook (≼-⟨⟩ ι) f (Tl-⟨⟩ x) k       p =
  proj₁ l ·ᵣ _ , Tl-⟨⟩ (proj₁ (proj₂ l)) , ·ᵣ-monoˡ-≾ᵣ (proj₁ (proj₂ (proj₂ l))) ,
  proj₂ (proj₂ (proj₂ l))
  where l = unlook ι f x k p
unlook (≼-▷ ι)  f Hd        k       ()
unlook (≼-▷ ι)  f (Tl-∷ (Tl-⟨⟩ {ρ' = ρ'} x)) k p =
  proj₁ l , proj₁ (proj₂ l) ,
  ≾ᵣ-trans (proj₁ (proj₂ (proj₂ l)))
    (≾ᵣ-trans (≃ᵣ⇒≿ᵣ (·ᵣ-identityʳ ρ')) (·ᵣ-monoʳ-≾ᵣ (≃ᵣ⇒≿ᵣ map-uᵉ))) ,
  proj₂ (proj₂ (proj₂ l))
  where l = unlook ι f x k (suc-injective p)

------------------------------------------------------------------------
-- A value of eternal type is typed under any further lock, at the empty
-- scope

mutual

  lockᵛ : ∀ {n} {Γ' : OCtx ∅ˢ n} {A} {ρ : RExp ∅ˢ}
        → Eternal ⌞ A ⌟ᵛ → ∅ᴴ ∣ Γ' ⊢V⦂ A → ∅ᴴ ∣ Γ' ⟨ ρ ⟩ ⊢V⦂ A
  lockᵛ {A = A} et (var x ok)   = var (Tl-⟨⟩ x) (et-ok (⌞⌟-⊩ᴱ A et))
  lockᵛ et (def f δ h e)        = def f δ h e
  lockᵛ et (const B c)          = const B c
  lockᵛ et ⋆                    = ⋆
  lockᵛ et true                 = true
  lockᵛ et false                = false
  lockᵛ et zero                 = zero
  lockᵛ et (succ V)             = succ (lockᵛ et V)
  lockᵛ (e₁ |×|ₑ e₂) ⦉ V , W ⦊  = ⦉ lockᵛ e₁ V , lockᵛ e₂ W ⦊
  lockᵛ (e₁ |+|ₑ e₂) (inl V)    = inl (lockᵛ e₁ V)
  lockᵛ (e₁ |+|ₑ e₂) (inr V)    = inr (lockᵛ e₂ V)
  lockᵛ et nil                  = nil
  lockᵛ (|List|ₑ e) (cons V W)  = cons (lockᵛ e V) (lockᵛ (|List|ₑ e) W)
  lockᵛ et (cmp ⋈ V W e)        = cmp ⋈ (lockᵛ e' V) (lockᵛ e' W) e
    where e' = sound-⊩ᴱ (⊨ᴰ-∅ {σ = ∅ᴰ}) e
  lockᵛ () (lam M)
  lockᵛ () (handler N H)
  lockᵛ et (annᵛ A V)           = annᵛ A (lockᵛ et V)
  lockᵛ et (subV V p)           = subV (lockᵛ (<:ᵛ-eternalˡ (sound-<:ᵛ (⊨ᴰ-∅ {σ = ∅ᴰ}) p) et) V) p

  ⌊lockᵛ⌋ : ∀ {n} {Γ' : OCtx ∅ˢ n} {A} {ρ : RExp ∅ˢ}
          → (et : Eternal ⌞ A ⌟ᵛ) → (V : ∅ᴴ ∣ Γ' ⊢V⦂ A)
          → OE.⌊ lockᵛ {ρ = ρ} et V ⌋ᵛ ≡ OE.⌊ V ⌋ᵛ
  ⌊lockᵛ⌋ et (var x ok)          = refl
  ⌊lockᵛ⌋ et (def f δ h e)       = refl
  ⌊lockᵛ⌋ et (const B c)         = refl
  ⌊lockᵛ⌋ et ⋆                   = refl
  ⌊lockᵛ⌋ et true                = refl
  ⌊lockᵛ⌋ et false               = refl
  ⌊lockᵛ⌋ et zero                = refl
  ⌊lockᵛ⌋ et (succ V)            = cong succ (⌊lockᵛ⌋ et V)
  ⌊lockᵛ⌋ (e₁ |×|ₑ e₂) ⦉ V , W ⦊ = cong₂ ⦉_,_⦊ (⌊lockᵛ⌋ e₁ V) (⌊lockᵛ⌋ e₂ W)
  ⌊lockᵛ⌋ (e₁ |+|ₑ e₂) (inl V)   = cong inl (⌊lockᵛ⌋ e₁ V)
  ⌊lockᵛ⌋ (e₁ |+|ₑ e₂) (inr V)   = cong inr (⌊lockᵛ⌋ e₂ V)
  ⌊lockᵛ⌋ et nil                 = refl
  ⌊lockᵛ⌋ (|List|ₑ e) (cons V W) = cong₂ cons (⌊lockᵛ⌋ e V) (⌊lockᵛ⌋ (|List|ₑ e) W)
  ⌊lockᵛ⌋ et (cmp ⋈ V W e)       = cong₂ (cmp ⋈) (⌊lockᵛ⌋ e' V) (⌊lockᵛ⌋ e' W)
    where e' = sound-⊩ᴱ (⊨ᴰ-∅ {σ = ∅ᴰ}) e
  ⌊lockᵛ⌋ () (lam M)
  ⌊lockᵛ⌋ () (handler N H)
  ⌊lockᵛ⌋ et (annᵛ A V)          = cong (_⦂ᵛ A) (⌊lockᵛ⌋ et V)
  ⌊lockᵛ⌋ et (subV V p)          = ⌊lockᵛ⌋ (<:ᵛ-eternalˡ (sound-<:ᵛ (⊨ᴰ-∅ {σ = ∅ᴰ}) p) et) V

------------------------------------------------------------------------
-- The open typings of the pending comparisons

Entry : ∀ {n} → OCtx ∅ˢ n → ∀ {Δ} → Pending Δ n → Set
Entry Γ' p = Σ[ V' ∈ ∅ᴴ ∣ Γ' ⊢V⦂ Bool ] (OE.⌊ V' ⌋ᵛ ≡ cmp (rel p) (left p) (right p))

EEnv : ∀ {n} → OCtx ∅ˢ n → ∀ {Δ} → List (Pending Δ n) → Set
EEnv Γ' []      = ⊤
EEnv Γ' (p List.∷ P) = Entry Γ' p × EEnv Γ' P

entry : ∀ {n} {Γ' : OCtx ∅ˢ n} {Δ} {P : List (Pending Δ n)} {p}
      → EEnv Γ' P → p ∈ P → Entry Γ' p
entry (e , E) (here refl) = e
entry (e , E) (there m)   = entry E m

wk-env : ∀ {n} {Γ' : OCtx ∅ˢ n} {Δ} → (P : List (Pending Δ n)) → EEnv Γ' P → EEnv Γ' (wkᴾ P)
wk-env []      E       = tt
wk-env (p List.∷ P) (e , E) = e , wk-env P E

lock-env : ∀ {n} {Γ' : OCtx ∅ˢ n} {Δ} {ρ : RExp ∅ˢ} → (P : List (Pending Δ n))
         → EEnv Γ' P → EEnv (Γ' ⟨ ρ ⟩) (lockᴾ {ρ = ⌞ ρ ⌟ʳ} P)
lock-env []      E              = tt
lock-env (p List.∷ P) ((V' , e) , E) = (lockᵛ Boolₑ V' , trans (⌊lockᵛ⌋ Boolₑ V') e) , lock-env P E

------------------------------------------------------------------------
-- The embedding

private

  -- a closed type meaning `A` is a subtype of `⌜ A ⌝ᵛ`

  to-⌜⌝ : (A' : OVType ∅ˢ) → NoHandlerTypeᵛ A' → ∀ {A} → ⌞ A' ⌟ᵛ ≡ A
         → ∅ᴴ ∣ A' <:̂ᵛ ⌜ A ⌝ᵛ
  to-⌜⌝ A' h refl = ≡̂ᵛ-<:̂ (⌜⌞ A' ⌟⌝ᵛ h)

  -- the value of a closed grade expression is its meaning

  valʳ-⌞⌟ : (r : RExp ∅ˢ) → ∀ {c} → ⌞ r ⌟ʳ ≡ c → valʳ r ≡ c
  valʳ-⌞⌟ r e = trans (sym (⌞⌟-valʳ r)) e

  -- ground types embed as their open images

  ⌜type-of-gtype⌝ : (g : GType) → ⌜ type-of-gtype g ⌝ᵛ ≡ ⌜ g ⌝ᵍ
  ⌜type-of-gtype⌝ (Base b)   = refl
  ⌜type-of-gtype⌝ Unit       = refl
  ⌜type-of-gtype⌝ Bool       = refl
  ⌜type-of-gtype⌝ Nat        = refl
  ⌜type-of-gtype⌝ Empty      = refl
  ⌜type-of-gtype⌝ (A |×|ᵍ B) = cong₂ _|×|_ (⌜type-of-gtype⌝ A) (⌜type-of-gtype⌝ B)
  ⌜type-of-gtype⌝ (A |+|ᵍ B) = cong₂ _|+|_ (⌜type-of-gtype⌝ A) (⌜type-of-gtype⌝ B)
  ⌜type-of-gtype⌝ (|List|ᵍ A) = cong |List| (⌜type-of-gtype⌝ A)
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

-- A uniform typing in a context whose meaning maps into `Δ` is an open
-- typing at the empty scope, of the embedded type, erasing to the term

mutual

  embedᵛ : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Vᴿ A} {V : Δ ⊢V⦂ A}
         → Uᵛ Γ' r P Vᴿ V → AnnFreeᵛ Vᴿ → NoHandlerTypeᶜᵗˣ Γ'
         → ∀ {G} → ⌞ Γ' ⌟ᶜᵗˣ ≡ G → (ι : G ≼ Δ) → Exact ι → ⌊ ι ⌋ᵐ ≡ r → EEnv Γ' P
         → Σ[ V' ∈ ∅ᴴ ∣ Γ' ⊢V⦂ ⌜ A ⌝ᵛ ] (OE.⌊ V' ⌋ᵛ ≡ Vᴿ)
  embedᵛ {Γ' = Γ'} (u-var {i = i} {A = A} {f = f} {x = x} p) _ nh eq ι fι er E
    with unlook ι fι x (toℕ i) (trans p (cong (λ r → posᴿ r (toℕ i)) (sym er)))
  ... | ρ₀ , x₀ , le , q with lookupˣ Γ' eq x₀
  ... | A' , ρ' , x' , eA , eρ , ep =
    subV (var x' ok) (to-⌜⌝ A' (∈̂-noHandler nh x') eA) , cong var (toℕ-injective (trans ep q))
    where
      ok : VarOK ∅ᴴ A' ρ'
      ok with eternal? A
      ... | yes et = et-ok (⌞⌟-⊩ᴱ A' (subst Eternal (sym eA) et))
      ... | no ¬et =
        ≾ᵘ-ok (val-≾ᵣ⁻ (subst (_≾ᵣ uᵣ) (sym (valʳ-⌞⌟ ρ' eρ)) (≾ᵣ-trans le (f ¬et))))
  embedᵛ (u-out m)    _ nh eq ι fι er E = entry E m
  embedᵛ u-const      _ nh eq ι fι er E = const _ _ , refl
  embedᵛ u-⋆          _ nh eq ι fι er E = ⋆ , refl
  embedᵛ u-true       _ nh eq ι fι er E = true , refl
  embedᵛ u-false      _ nh eq ι fι er E = false , refl
  embedᵛ u-zero       _ nh eq ι fι er E = zero , refl
  embedᵛ (u-succ u)   a nh eq ι fι er E with embedᵛ u a nh eq ι fι er E
  ... | V' , e = succ V' , cong succ e
  embedᵛ (u-pair u v) (a , b) nh eq ι fι er E
    with embedᵛ u a nh eq ι fι er E | embedᵛ v b nh eq ι fι er E
  ... | V' , e | W' , e' = ⦉ V' , W' ⦊ , cong₂ ⦉_,_⦊ e e'
  embedᵛ (u-inl u)    a nh eq ι fι er E with embedᵛ u a nh eq ι fι er E
  ... | V' , e = inl V' , cong inl e
  embedᵛ (u-inr u)    a nh eq ι fι er E with embedᵛ u a nh eq ι fι er E
  ... | V' , e = inr V' , cong inr e
  embedᵛ u-nil        _ nh eq ι fι er E = nil , refl
  embedᵛ (u-cons u v) (a , b) nh eq ι fι er E
    with embedᵛ u a nh eq ι fι er E | embedᵛ v b nh eq ι fι er E
  ... | V' , e | W' , e' = cons V' W' , cong₂ cons e e'
  embedᵛ (u-lam {A = A} u) a nh eq ι fι er E
    with embedᶜ u a (nh , ⌜⌝-noHandlerᵛ A) (ext eq A) (≼-∷ ι) fι (cong extᴿ er) tt
  ... | M' , e = lam M' , cong lam e
  embedᵛ (u-subV {p = p} u) a nh eq ι fι er E with embedᵛ u a nh eq ι fι er E
  ... | V' , e = subV V' (⌜⌝-<:ᵛ p) , e
  embedᵛ (u-annᵛ u) () nh eq ι fι er E

  embedᶜ : ∀ {n} {Γ' : OCtx ∅ˢ n} {r Δ P Mᴿ C} {M : Δ ⊢C⦂ C}
         → Uᶜ Γ' r P Mᴿ M → AnnFreeᶜ Mᴿ → NoHandlerTypeᶜᵗˣ Γ'
         → ∀ {G} → ⌞ Γ' ⌟ᶜᵗˣ ≡ G → (ι : G ≼ Δ) → Exact ι → ⌊ ι ⌋ᵐ ≡ r → EEnv Γ' P
         → Emb Γ' ⌜ C ⌝ᶜ Mᴿ
  embedᶜ (u-hoist {P = P} {⋈ = ⋈} {B = B} {ε' = ε'} {et = et} aV aW u v w) a nh eq ι fι er E
    with embedᵛ u aV nh eq ι fι er E | embedᵛ v aW nh eq ι fι er E
  ... | V' , e | W' , e'
    with embedᶜ w a nh eq (≼-▷ ι) fι (cong shᴿ er)
                ((cmp ⋈ V' W' (⌞⌟-⊩ᴱ ⌜ B ⌝ᵛ (subst Eternal (sym ⌞⌜ B ⌝⌟ᵛ) et)) ,
                  cong₂ (cmp ⋈) e e') ,
                 wk-env P E)
  ... | N' , e'' = coerce (atomₑ (≃ₑ⇒≿ₑ (·ₑ-identityˡ ε'))) N' , e''
  embedᶜ (u-return u) a nh eq ι fι er E with embedᵛ u a nh eq ι fι er E
  ... | V' , e = return V' , cong return e
  embedᶜ (u-seq {A = A} {ε = ε} u v) (a , b) nh eq ι fι er E
    with embedᶜ u a nh eq ι fι er tt
       | embedᶜ v b (nh , ⌜⌝-noHandlerᵛ A) (ext (cong (_⟨ mapᵉ ε ⟩) eq) A) (≼-∷ (≼-⟨⟩ ι)) fι (cong extᴿ er) tt
  ... | M' , e | N' , e' = const-· (M' ⨟ N' , cong₂ _⨟_ e e')
  embedᶜ (u-app u v) (a , b) nh eq ι fι er E
    with embedᵛ u a nh eq ι fι er E | embedᵛ v b nh eq ι fι er E
  ... | V' , e | W' , e' = V' · W' , cong₂ _·_ e e'
  embedᶜ (u-match {A = A} {B = B} u v) (a , b) nh eq ι fι er E
    with embedᵛ u a nh eq ι fι er E
       | embedᶜ v b ((nh , ⌜⌝-noHandlerᵛ A) , ⌜⌝-noHandlerᵛ B) (ext (ext eq A) B) (≼-∷ (≼-∷ ι)) fι (cong (λ r → extᴿ (extᴿ r)) er) tt
  ... | V' , e | M' , e' = match V' `in M' , cong₂ match_`in_ e e'
  embedᶜ (u-absurd u) a nh eq ι fι er E with embedᵛ u a nh eq ι fι er E
  ... | V' , e = absurd V' , cong absurd e
  embedᶜ (u-if u v w) (a , b , c) nh eq ι fι er E
    with embedᵛ u a nh eq ι fι er E | embedᶜ v b nh eq ι fι er tt | embedᶜ w c nh eq ι fι er tt
  ... | V' , e | M' , e' | N' , e'' =
    if V' `then M' `else N' , cong₃ if_`then_`else_ e e' e''
  embedᶜ (u-caseℕ u v w) (a , b , c) nh eq ι fι er E
    with embedᵛ u a nh eq ι fι er E | embedᶜ v b nh eq ι fι er tt
       | embedᶜ w c (nh , tt) (ext eq Nat) (≼-∷ ι) fι (cong extᴿ er) tt
  ... | V' , e | M' , e' | N' , e'' =
    caseℕ V' `zero M' `succ N' , cong₃ caseℕ_`zero_`succ_ e e' e''
  embedᶜ (u-case+ {A = A} {B = B} u v w) (a , b , c) nh eq ι fι er E
    with embedᵛ u a nh eq ι fι er E
       | embedᶜ v b (nh , ⌜⌝-noHandlerᵛ A) (ext eq A) (≼-∷ ι) fι (cong extᴿ er) tt
       | embedᶜ w c (nh , ⌜⌝-noHandlerᵛ B) (ext eq B) (≼-∷ ι) fι (cong extᴿ er) tt
  ... | V' , e | M' , e' | N' , e'' =
    case+ V' `inl M' `inr N' , cong₃ case+_`inl_`inr_ e e' e''
  embedᶜ (u-caseL {A = A} u v w) (a , b , c) nh eq ι fι er E
    with embedᵛ u a nh eq ι fι er E | embedᶜ v b nh eq ι fι er tt
       | embedᶜ w c ((nh , ⌜⌝-noHandlerᵛ A) , ⌜⌝-noHandlerᵛ A) (ext (ext eq A) (|List| A)) (≼-∷ (≼-∷ ι)) fι
                (cong (λ r → extᴿ (extᴿ r)) er) tt
  ... | V' , e | M' , e' | N' , e'' =
    caseL V' `nil M' `cons N' , cong₃ caseL_`nil_`cons_ e e' e''
  embedᶜ (u-recℕ {B = B} {ε = ε} {p = p} u v w) (a , b , c) nh eq ι fι er E
    with embedᵛ u a nh eq ι fι er E | embedᶜ v b nh eq ι fι er tt
       | embedᶜ w c ((nh , tt) , ⌜⌝-noHandlerᵛ B) (ext (cong (_⟨ mapᵉ ε ⟩) (ext (lock eq ⊤ᵣ) Nat)) B)
                (≼-∷ (≼-⟨⟩ (≼-∷ (≼-⟨⟩ ι)))) fι (cong (λ r → extᴿ (extᴿ r)) er) tt
  ... | V' , e | M' , e' | N' , e'' =
    recℕ V' M' N' (val-≾ₑ⁻ p) , cong₃ recℕ e e' e''
  embedᶜ (u-recL {A = A} {B = B} {ε = ε} {p = p} u v w) (a , b , c) nh eq ι fι er E
    with embedᵛ u a nh eq ι fι er E | embedᶜ v b nh eq ι fι er tt
       | embedᶜ w c (((nh , ⌜⌝-noHandlerᵛ A) , ⌜⌝-noHandlerᵛ A) , ⌜⌝-noHandlerᵛ B)
                (ext (cong (_⟨ mapᵉ ε ⟩) (ext (ext (lock eq ⊤ᵣ) A) (|List| A))) B)
                (≼-∷ (≼-⟨⟩ (≼-∷ (≼-∷ (≼-⟨⟩ ι))))) fι
                (cong (λ r → extᴿ (extᴿ (extᴿ r))) er) tt
  ... | V' , e | M' , e' | N' , e'' =
    recL V' M' N' (val-≾ₑ⁻ p) , cong₃ recL e e' e''
  embedᶜ (u-perform {op = op} u v) (a , b) nh eq ι fι er E
    with embedᵛ u a nh eq ι fι er E
       | embedᶜ v b (nh , ⌜⌝ᵍ-noHandler (arity op))
                (cong₂ _∷_ (lock eq (mapᵉ (op-grade op))) (⟦⌜ arity op ⌝ᵍ⟧ ∅ᴰ))
                (≼-∷ (≼-⟨⟩ ι)) fι (cong extᴿ er) tt
  ... | V' , e | M' , e' =
    const-· (perform op (ty-subst (⌜type-of-gtype⌝ (param op)) V') M' ,
             cong₂ (perform op) (trans (⌊ty-subst⌋ (⌜type-of-gtype⌝ (param op)) V') e) e')
    where
      ⌊ty-subst⌋ : ∀ {n} {Γ' : OCtx ∅ˢ n} {A A'} → (q : A ≡ A') → (W : ∅ᴴ ∣ Γ' ⊢V⦂ A)
                 → OE.⌊ ty-subst q W ⌋ᵛ ≡ OE.⌊ W ⌋ᵛ
      ⌊ty-subst⌋ refl W = refl
  embedᶜ (u-delay {τ = τ} u) a nh eq ι fι er E
    with embedᶜ u a nh (lock eq (of-durʳ τ)) (≼-⟨⟩ ι) fι er tt
  ... | M' , e = const-· (delay τ M' , cong (delay τ) e)
  -- the raw clauses are a function of the operation, compared by `fun-ext`
  embedᶜ (u-handle {A = A} {ε = ε} u Hᵒ eH v) (a , b , _) nh eq ι fι er E
    with embedᶜ u a nh eq ι fι er tt
       | embedᶜ v b (nh , ⌜⌝-noHandlerᵛ A) (ext (cong (_⟨ mapᵉ ε ⟩) eq) A) (≼-∷ (≼-⟨⟩ ι)) fι
                (cong extᴿ er) tt
  ... | M' , e | N' , e' =
    const-· (handle M' `with handler N' Hᵒ ,
             cong₂ handle_`with_ e (cong₂ handler e' (fun-ext eH)))
  embedᶜ {Γ' = Γ'} (u-unbox {i = i} {A = A} {x = x} {p = p} {q = q} ep u) (_ , a) nh eq ι fι er E
    with unlook ι fι x (toℕ i) (trans ep (cong (λ r → posᴿ r (toℕ i)) (sym er)))
  ... | ρ₀ , x₀ , le , q₀ with lookupˣ Γ' eq x₀
  ... | B' , ρ' , x' , eB , eρ , epos with boxView B' eB
  ... | r' , A₀' , refl , er' , eA₀
    with embedᶜ u a (nh , ⌜⌝-noHandlerᵛ A) (ext eq A) (≼-∷ ι) fι (cong extᴿ er) tt
  ... | N' , e =
    unbox (res-var {z = x'}) (val-≾ᵣ⁻ (subst₂ _≾ᵣ_ (sym (valʳ-⌞⌟ ρ' eρ)) (sym (valʳ-⌞⌟ r' er'))
                               (≾ᵣ-trans le p)))
          (proj₁ N'') ,
    cong₂ unbox (cong var (toℕ-injective (trans epos q₀))) (trans (proj₂ N'') e)
    where
      -- the continuation, narrowed from the supertype to the payload

      N'' = conv-last narrowing refl
              (⌞⌟-<:ᵛ A₀' ⌜ A ⌝ᵛ (∈̂-noHandler nh x') (⌜⌝-noHandlerᵛ A)
                      (subst₂ _<:ᵛ_ (sym eA₀) (sym ⌞⌜ A ⌝⌟ᵛ) q)) N'
  embedᶜ (u-box {P = P} {ρ = ρ} {A = A} u v) (a , b) nh eq ι fι er E
    with embedᵛ u a nh (lock eq ⌞ ρ ⌟ʳ) (≼-⟨⟩ ι) fι er (lock-env P E)
       | embedᶜ v b (nh , ⌜⌝-noHandlerᵛ A) (cong₂ _∷_ eq (cong ([ ⌞ ρ ⌟ʳ ]_) ⌞⌜ A ⌝⌟ᵛ)) (≼-∷ ι) fι (cong extᴿ er) tt
  ... | V' , e | N' , e' = box ρ V' N' , cong₂ (box ρ) e e'
  embedᶜ (u-subC {p = p} u) a nh eq ι fι er E with embedᶜ u a nh eq ι fι er E
  ... | M' , e = subC M' (⌜⌝-<:ᶜ p) , e
  embedᶜ (u-annᶜ u) () nh eq ι fι er E
