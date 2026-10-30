------------------------------------------------------------------
-- The reduction of configurations                              --
--                                                              --
-- `⟨ S ∣ M ⟩ ↝[ e ] ⟨ S' ∣ M' ⟩`: small-step reduction of      --
-- run-time terms, `e : S ≤ₛ S'` extending the state. A delay   --
-- adds a passage, a `box` a resource, an `unbox` reads one. A  --
-- handled operation call runs the clause, its grade variable   --
-- uninstantiated, with the rest of the handled computation as  --
-- a resource at the operation's grade.                         --
------------------------------------------------------------------

open import Data.Bool.Base using () renaming (Bool to 𝔹; true to tt𝔹; false to ff𝔹)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _,_)

open import Relation.Nullary using (yes; no)

open import Grades.Base
open import Language.BaseTypes
open import Language.Comparisons
open import Language.Spec
open import Language.Operations

open import Util.Equality

module PolymorphicCalculus.OperationalSemantics.Reduction (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops
open BaseTypes BTs using (_≡ᵇ?_; eternalBaseType?; compareᵇ)

open BaseTypes BTs using (BaseType; BaseConstants)

open import PolymorphicCalculus.Syntax.Run                 S
open import PolymorphicCalculus.OperationalSemantics.State S

------------------------------------------------------------------------
-- Comparison of values, by the structural order of the data they denote

data Datum : Set where
  base       : (b : BaseType) → BaseConstants b → Datum
  unit       : Datum
  bit        : 𝔹 → Datum
  numᶻ       : Datum
  numˢ       : Datum → Datum
  pair       : Datum → Datum → Datum
  left right : Datum → Datum
  nilᵈ       : Datum
  consᵈ      : Datum → Datum → Datum
  other      : Datum

compareᴰ : Datum → Datum → Order
compareᴰ (base b c) (base b' c') with b ≡ᵇ? b'
... | no _    = equal
... | yes refl with eternalBaseType? b
...   | yes eb = compareᵇ eb c c'
...   | no _   = equal
compareᴰ unit           unit             = equal
compareᴰ (bit x)        (bit y)          = compareᴮ x y
compareᴰ numᶻ           numᶻ             = equal
compareᴰ numᶻ           (numˢ _)         = less
compareᴰ (numˢ _)       numᶻ             = greater
compareᴰ (numˢ x)       (numˢ y)         = compareᴰ x y
compareᴰ (pair x y)     (pair x' y')     = lexᵒ (compareᴰ x x') (compareᴰ y y')
compareᴰ (left x)       (left y)         = compareᴰ x y
compareᴰ (left _)       (right _)        = less
compareᴰ (right _)      (left _)         = greater
compareᴰ (right x)      (right y)        = compareᴰ x y
compareᴰ nilᵈ           nilᵈ             = equal
compareᴰ nilᵈ           (consᵈ _ _)      = less
compareᴰ (consᵈ _ _)    nilᵈ             = greater
compareᴰ (consᵈ x xs)   (consᵈ y ys)     = lexᵒ (compareᴰ x y) (compareᴰ xs ys)
compareᴰ _              _                = equal

datum : ∀ {n} → RunV n → Datum
datum (const b c)  = base b c
datum ⋆            = unit
datum true         = bit tt𝔹
datum false        = bit ff𝔹
datum (cmp ⋈ V W)  = bit (holds ⋈ (compareᴰ (datum V) (datum W)))
datum zero         = numᶻ
datum (succ V)     = numˢ (datum V)
datum ⦉ V , W ⦊     = pair (datum V) (datum W)
datum (inl V)      = left (datum V)
datum (inr V)      = right (datum V)
datum nil          = nilᵈ
datum (cons V W)   = consᵈ (datum V) (datum W)
datum _            = other

decide : ∀ {n} → Cmp → RunV n → RunV n → RunV n
decide ⋈ V W with holds ⋈ (compareᴰ (datum V) (datum W))
... | tt𝔹 = true
... | ff𝔹 = false

------------------------------------------------------------------------
-- Reduction

data Step {n} (S : State n) : RunC n → ∀ {m} (S' : State m) → S ≤ₛ S' → RunC m → Set

syntax Step S M S' e M' = ⟨ S ∣ M ⟩↝[ e ]⟨ S' ∣ M' ⟩

data Step {n} S where

  -- functions, data and recursion

  APP        : ∀ {M V}
             → ⟨ S ∣ lam M · V ⟩↝[ ≤ₛ-refl ]⟨ S ∣ M [ V ]₀ ⟩

  MATCH      : ∀ {V W M}
             → ⟨ S ∣ match ⦉ V , W ⦊ `in M ⟩↝[ ≤ₛ-refl ]⟨ S ∣ M [ V ]₁ [ W ]₀ ⟩

  CMP        : ∀ {⋈ V W M N}
             → ⟨ S ∣ if cmp ⋈ V W `then M `else N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ if decide ⋈ V W `then M `else N ⟩

  IF-TRUE    : ∀ {M N}
             → ⟨ S ∣ if true `then M `else N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ M ⟩

  IF-FALSE   : ∀ {M N}
             → ⟨ S ∣ if false `then M `else N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ N ⟩

  CASEℕ-ZERO : ∀ {M N}
             → ⟨ S ∣ caseℕ zero `zero M `succ N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ M ⟩

  CASEℕ-SUCC : ∀ {V M N}
             → ⟨ S ∣ caseℕ succ V `zero M `succ N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ N [ V ]₀ ⟩

  RECℕ-ZERO  : ∀ {M N}
             → ⟨ S ∣ recℕ zero M N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ M ⟩

  RECℕ-SUCC  : ∀ {V M N}
             → ⟨ S ∣ recℕ (succ V) M N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ recℕ V M N ⨟ N [ V ]₁ ⟩

  CASE-INL   : ∀ {V M N}
             → ⟨ S ∣ case+ inl V `inl M `inr N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ M [ V ]₀ ⟩

  CASE-INR   : ∀ {V M N}
             → ⟨ S ∣ case+ inr V `inl M `inr N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ N [ V ]₀ ⟩

  CASEL-NIL  : ∀ {M N}
             → ⟨ S ∣ caseL nil `nil M `cons N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ M ⟩

  CASEL-CONS : ∀ {V W M N}
             → ⟨ S ∣ caseL cons V W `nil M `cons N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ N [ V ]₁ [ W ]₀ ⟩

  RECL-NIL   : ∀ {M N}
             → ⟨ S ∣ recL nil M N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ M ⟩

  RECL-CONS  : ∀ {V W M N}
             → ⟨ S ∣ recL (cons V W) M N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ recL W M N ⨟ N [ V ]₂ [ W ]₁ ⟩

  -- sequencing

  SEQ-RET    : ∀ {V N}
             → ⟨ S ∣ return V ⨟ N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ N [ V ]₀ ⟩

  SEQ-OP     : ∀ {op V M N}
             → ⟨ S ∣ perform op V M ⨟ N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ perform op V (M ⨟ renᶜ (ext suc) N) ⟩

  SEQ-STEP   : ∀ {m} {S' : State m} {e : S ≤ₛ S'} {M M' N}
             → ⟨ S ∣ M ⟩↝[ e ]⟨ S' ∣ M' ⟩
             → ⟨ S ∣ M ⨟ N ⟩↝[ e ]⟨ S' ∣ M' ⨟ renᶜ (ext (wkₛ e)) N ⟩

  -- passage of time

  DELAY      : ∀ {τ M}
             → ⟨ S ∣ delay τ M ⟩↝[ ≤ₛ-lock ≤ₛ-refl ]⟨ S ⟨ τ ⟩ₛ ∣ M ⟩

  -- effect handling

  HANDLE-RET : ∀ {V N H}
             → ⟨ S ∣ handle return V `with handler N H ⟩↝[ ≤ₛ-refl ]⟨ S ∣ N [ V ]₀ ⟩

  HANDLE-OP  : ∀ {op V M N H}
             → ⟨ S ∣ handle perform op V M `with handler N H ⟩↝[ ≤ₛ-refl ]⟨ S ∣
                 box (lam (handle M `with wkᵛ (handler N H))) (H op [ V ]₁) ⟩

  HANDLE-STEP : ∀ {m} {S' : State m} {e : S ≤ₛ S'} {M M' V}
              → ⟨ S ∣ M ⟩↝[ e ]⟨ S' ∣ M' ⟩
              → ⟨ S ∣ handle M `with V ⟩↝[ e ]⟨ S' ∣ handle M' `with renᵛ (wkₛ e) V ⟩

  -- resources

  BOX        : ∀ {V N}
             → ⟨ S ∣ box V N ⟩↝[ ≤ₛ-res ≤ₛ-refl ]⟨ S ∷ₛ V ∣ N ⟩

  UNBOX      : ∀ {i N}
             → ⟨ S ∣ unbox (var i) N ⟩↝[ ≤ₛ-refl ]⟨ S ∣ N [ lookupₛ S i ]₀ ⟩

-- A finished computation: a returned value or an operation call

data Final {n} : RunC n → Set where
  is-return  : ∀ V → Final (return V)
  is-perform : ∀ op V M → Final (perform op V M)

-- A step, its extension of the state left implicit

infix 3 ⟨_∣_⟩↝⟨_∣_⟩

⟨_∣_⟩↝⟨_∣_⟩ : ∀ {n m} → State n → RunC n → State m → RunC m → Set
⟨ S ∣ M ⟩↝⟨ S' ∣ M' ⟩ = Σ[ e ∈ S ≤ₛ _ ] ⟨ S ∣ M ⟩↝[ e ]⟨ S' ∣ M' ⟩
