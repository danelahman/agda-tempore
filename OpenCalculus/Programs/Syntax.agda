------------------------------------------------------------------
-- Programs and their erasure                                   --
--                                                              --
-- A program is a sequence of top-level definitions `f = V`,    --
-- the first outermost, each a closed raw value naming the      --
-- definitions before it by their positions. Its definitions    --
-- have closed run-time values, the uses of earlier definitions --
-- substituted (`⟦_⟧ᴾ`). The erasure of a raw term in a program --
-- drops grades and annotations and substitutes the             --
-- definitions (`⌊_⌋ᴾᵛ`, `⌊_⌋ᴾᶜ`).                              --
------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)

open import Util.Equality

open import Language.Spec
open import Language.Operations

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Programs.Syntax (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops

open import OpenCalculus.Syntax.Raw S using (RawV; RawC)
open import OpenCalculus.Syntax.Run S

------------------------------------------------------------------------
-- Programs

data Program : Set where
  ∅ᴾ   : Program
  _∷ᴾ_ : Program → RawV ∅ˢ 0 → Program

infixl 31 _∷ᴾ_

-- The number of definitions

lenᴾ : Program → ℕ
lenᴾ ∅ᴾ       = 0
lenᴾ (P ∷ᴾ V) = suc (lenᴾ P)

------------------------------------------------------------------------
-- Substitution of closed run-time values for the definitions

-- Closed run-time values for some positions

Defs : Set
Defs = ℕ → Maybe (RunV 0)

-- A closed run-time term in any scope

from0 : ∀ {n} → Fin 0 → Fin n
from0 ()

wk₀ : ∀ {n} → RunV 0 → RunV n
wk₀ = renᵛ from0

mutual

  _[_]ᵈᵛ : ∀ {n} → RunV n → Defs → RunV n
  var i         [ ρ ]ᵈᵛ = var i
  usedef k      [ ρ ]ᵈᵛ = maybe′ wk₀ (usedef k) (ρ k)
  const B c     [ ρ ]ᵈᵛ = const B c
  ⋆             [ ρ ]ᵈᵛ = ⋆
  true          [ ρ ]ᵈᵛ = true
  false         [ ρ ]ᵈᵛ = false
  zero          [ ρ ]ᵈᵛ = zero
  succ V        [ ρ ]ᵈᵛ = succ (V [ ρ ]ᵈᵛ)
  ⦉ V , W ⦊      [ ρ ]ᵈᵛ = ⦉ V [ ρ ]ᵈᵛ , W [ ρ ]ᵈᵛ ⦊
  inl V         [ ρ ]ᵈᵛ = inl (V [ ρ ]ᵈᵛ)
  inr V         [ ρ ]ᵈᵛ = inr (V [ ρ ]ᵈᵛ)
  nil           [ ρ ]ᵈᵛ = nil
  cons V W      [ ρ ]ᵈᵛ = cons (V [ ρ ]ᵈᵛ) (W [ ρ ]ᵈᵛ)
  cmp ⋈ V W     [ ρ ]ᵈᵛ = cmp ⋈ (V [ ρ ]ᵈᵛ) (W [ ρ ]ᵈᵛ)
  lam M         [ ρ ]ᵈᵛ = lam (M [ ρ ]ᵈᶜ)
  handler N H   [ ρ ]ᵈᵛ = handler (N [ ρ ]ᵈᶜ) (λ op → H op [ ρ ]ᵈᶜ)

  _[_]ᵈᶜ : ∀ {n} → RunC n → Defs → RunC n
  return V                  [ ρ ]ᵈᶜ = return (V [ ρ ]ᵈᵛ)
  (M ⨟ N)                   [ ρ ]ᵈᶜ = M [ ρ ]ᵈᶜ ⨟ N [ ρ ]ᵈᶜ
  (V · W)                   [ ρ ]ᵈᶜ = V [ ρ ]ᵈᵛ · W [ ρ ]ᵈᵛ
  (match V `in M)           [ ρ ]ᵈᶜ = match V [ ρ ]ᵈᵛ `in M [ ρ ]ᵈᶜ
  absurd V                  [ ρ ]ᵈᶜ = absurd (V [ ρ ]ᵈᵛ)
  (if V `then M `else N)    [ ρ ]ᵈᶜ = if V [ ρ ]ᵈᵛ `then M [ ρ ]ᵈᶜ `else N [ ρ ]ᵈᶜ
  (caseℕ V `zero M `succ N) [ ρ ]ᵈᶜ = caseℕ V [ ρ ]ᵈᵛ `zero M [ ρ ]ᵈᶜ `succ N [ ρ ]ᵈᶜ
  (case+ V `inl M `inr N)   [ ρ ]ᵈᶜ = case+ V [ ρ ]ᵈᵛ `inl M [ ρ ]ᵈᶜ `inr N [ ρ ]ᵈᶜ
  (caseL V `nil M `cons N)  [ ρ ]ᵈᶜ = caseL V [ ρ ]ᵈᵛ `nil M [ ρ ]ᵈᶜ `cons N [ ρ ]ᵈᶜ
  recℕ V M N                [ ρ ]ᵈᶜ = recℕ (V [ ρ ]ᵈᵛ) (M [ ρ ]ᵈᶜ) (N [ ρ ]ᵈᶜ)
  recL V M N                [ ρ ]ᵈᶜ = recL (V [ ρ ]ᵈᵛ) (M [ ρ ]ᵈᶜ) (N [ ρ ]ᵈᶜ)
  perform op V M            [ ρ ]ᵈᶜ = perform op (V [ ρ ]ᵈᵛ) (M [ ρ ]ᵈᶜ)
  delay τ M                 [ ρ ]ᵈᶜ = delay τ (M [ ρ ]ᵈᶜ)
  (handle M `with V)        [ ρ ]ᵈᶜ = handle M [ ρ ]ᵈᶜ `with V [ ρ ]ᵈᵛ
  unbox V N                 [ ρ ]ᵈᶜ = unbox (V [ ρ ]ᵈᵛ) (N [ ρ ]ᵈᶜ)
  box V N                   [ ρ ]ᵈᶜ = box (V [ ρ ]ᵈᵛ) (N [ ρ ]ᵈᶜ)

infixl 50 _[_]ᵈᵛ _[_]ᵈᶜ

------------------------------------------------------------------------
-- The definitions of a program

⟦_⟧ᴾ : Program → Defs
⟦ ∅ᴾ ⟧ᴾ       k = nothing
⟦ P ∷ᴾ V ⟧ᴾ   k with k ≟ lenᴾ P
... | yes _ = just (eraseᵛ V [ ⟦ P ⟧ᴾ ]ᵈᵛ)
... | no  _ = ⟦ P ⟧ᴾ k

⟦∷⟧-here : ∀ P V {k} → k ≡ lenᴾ P → ⟦ P ∷ᴾ V ⟧ᴾ k ≡ just (eraseᵛ V [ ⟦ P ⟧ᴾ ]ᵈᵛ)
⟦∷⟧-here P V {k} e with k ≟ lenᴾ P
... | yes _ = refl
... | no ne = ⊥-elim (ne e)

⟦∷⟧-there : ∀ P V {k} → k ≢ lenᴾ P → ⟦ P ∷ᴾ V ⟧ᴾ k ≡ ⟦ P ⟧ᴾ k
⟦∷⟧-there P V {k} ne with k ≟ lenᴾ P
... | yes e = ⊥-elim (ne e)
... | no _  = refl

-- Erasure in a program

⌊_⌋ᴾᵛ : ∀ {Θ n} → RawV Θ n → Program → RunV n
⌊ V ⌋ᴾᵛ P = eraseᵛ V [ ⟦ P ⟧ᴾ ]ᵈᵛ

⌊_⌋ᴾᶜ : ∀ {Θ n} → RawC Θ n → Program → RunC n
⌊ M ⌋ᴾᶜ P = eraseᶜ M [ ⟦ P ⟧ᴾ ]ᵈᶜ
