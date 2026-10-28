------------------------------------------------------------------
-- Substitution on raw terms                                    --
--                                                              --
-- A substitution `σ : Subst Θ Θ'` acts on the grade and type   --
-- annotations of a raw term, lifted by `_↑ᵉ` into handler      --
-- clauses, and preserves the number of term variables.         --
-- Weakening is the action of `wkˢᵗ`, `wkˢʳ` and `wkˢᵉ`.        --
------------------------------------------------------------------

open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Syntax.Raw.Subst (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OpenCalculus.Syntax.Types S using (_‼_)
open import OpenCalculus.Syntax.Subst S

open import OpenCalculus.Syntax.Raw S

infixl 50 _[_]ᴿᵛ _[_]ᴿᶜ

mutual

  _[_]ᴿᵛ : ∀ {Θ Θ' n} → RawV Θ n → Subst Θ Θ' → RawV Θ' n
  var i        [ σ ]ᴿᵛ = var i
  const B c    [ σ ]ᴿᵛ = const B c
  ⋆            [ σ ]ᴿᵛ = ⋆
  true         [ σ ]ᴿᵛ = true
  false        [ σ ]ᴿᵛ = false
  zero         [ σ ]ᴿᵛ = zero
  succ V       [ σ ]ᴿᵛ = succ (V [ σ ]ᴿᵛ)
  inl V       [ σ ]ᴿᵛ = inl (V [ σ ]ᴿᵛ)
  inr V       [ σ ]ᴿᵛ = inr (V [ σ ]ᴿᵛ)
  nil          [ σ ]ᴿᵛ = nil
  cons V W     [ σ ]ᴿᵛ = cons (V [ σ ]ᴿᵛ) (W [ σ ]ᴿᵛ)
  ⦉ V , W ⦊     [ σ ]ᴿᵛ = ⦉ (V [ σ ]ᴿᵛ) , (W [ σ ]ᴿᵛ) ⦊
  lam M        [ σ ]ᴿᵛ = lam (M [ σ ]ᴿᶜ)
  (V ⦂ᵛ A)     [ σ ]ᴿᵛ = (V [ σ ]ᴿᵛ) ⦂ᵛ (A [ σ ]ᵛ)

  _[_]ᴿᶜ : ∀ {Θ Θ' n} → RawC Θ n → Subst Θ Θ' → RawC Θ' n
  return V                 [ σ ]ᴿᶜ = return (V [ σ ]ᴿᵛ)
  (M ⨟ N)                  [ σ ]ᴿᶜ = (M [ σ ]ᴿᶜ) ⨟ (N [ σ ]ᴿᶜ)
  (V · W)                  [ σ ]ᴿᶜ = (V [ σ ]ᴿᵛ) · (W [ σ ]ᴿᵛ)
  (match V `in M)          [ σ ]ᴿᶜ = match (V [ σ ]ᴿᵛ) `in (M [ σ ]ᴿᶜ)
  absurd V                 [ σ ]ᴿᶜ = absurd (V [ σ ]ᴿᵛ)
  (if V `then M `else N)   [ σ ]ᴿᶜ = if (V [ σ ]ᴿᵛ) `then (M [ σ ]ᴿᶜ) `else (N [ σ ]ᴿᶜ)
  cmp ⋈ V W                [ σ ]ᴿᶜ = cmp ⋈ (V [ σ ]ᴿᵛ) (W [ σ ]ᴿᵛ)
  (caseℕ V `zero M `succ N) [ σ ]ᴿᶜ = caseℕ (V [ σ ]ᴿᵛ) `zero (M [ σ ]ᴿᶜ) `succ (N [ σ ]ᴿᶜ)
  (case+ V `inl M `inr N) [ σ ]ᴿᶜ = case+ (V [ σ ]ᴿᵛ) `inl (M [ σ ]ᴿᶜ) `inr (N [ σ ]ᴿᶜ)
  recℕ V M N               [ σ ]ᴿᶜ = recℕ (V [ σ ]ᴿᵛ) (M [ σ ]ᴿᶜ) (N [ σ ]ᴿᶜ)
  (caseL V `nil M `cons N) [ σ ]ᴿᶜ = caseL (V [ σ ]ᴿᵛ) `nil (M [ σ ]ᴿᶜ) `cons (N [ σ ]ᴿᶜ)
  recL V M N               [ σ ]ᴿᶜ = recL (V [ σ ]ᴿᵛ) (M [ σ ]ᴿᶜ) (N [ σ ]ᴿᶜ)
  perform op V M           [ σ ]ᴿᶜ = perform op (V [ σ ]ᴿᵛ) (M [ σ ]ᴿᶜ)
  delay τ M                [ σ ]ᴿᶜ = delay τ (M [ σ ]ᴿᶜ)
  (handle M `with H `in N) [ σ ]ᴿᶜ =
    handle (M [ σ ]ᴿᶜ) `with (λ op → H op [ σ ↑ᵉ ]ᴿᶜ) `in (N [ σ ]ᴿᶜ)
  unbox i N                [ σ ]ᴿᶜ = unbox i (N [ σ ]ᴿᶜ)
  box ρ V N                [ σ ]ᴿᶜ = box (ρ [ σ ]ʳ) (V [ σ ]ᴿᵛ) (N [ σ ]ᴿᶜ)
  (M ⦂ᶜ C)                 [ σ ]ᴿᶜ = (M [ σ ]ᴿᶜ) ⦂ᶜ (C [ σ ]ᶜ)

-- The action looks at a substitution only pointwise

mutual

  [≐]ᴿᵛ : ∀ {Θ Θ' n} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ → (V : RawV Θ n)
        → V [ σ ]ᴿᵛ ≡ V [ δ ]ᴿᵛ
  [≐]ᴿᵛ p (var i)      = refl
  [≐]ᴿᵛ p (const B c)  = refl
  [≐]ᴿᵛ p ⋆            = refl
  [≐]ᴿᵛ p true         = refl
  [≐]ᴿᵛ p false        = refl
  [≐]ᴿᵛ p zero         = refl
  [≐]ᴿᵛ p (succ V)     = cong succ ([≐]ᴿᵛ p V)
  [≐]ᴿᵛ p (inl V)     = cong inl ([≐]ᴿᵛ p V)
  [≐]ᴿᵛ p (inr V)     = cong inr ([≐]ᴿᵛ p V)
  [≐]ᴿᵛ p nil          = refl
  [≐]ᴿᵛ p (cons V W)   = cong₂ cons ([≐]ᴿᵛ p V) ([≐]ᴿᵛ p W)
  [≐]ᴿᵛ p ⦉ V , W ⦊     = cong₂ ⦉_,_⦊ ([≐]ᴿᵛ p V) ([≐]ᴿᵛ p W)
  [≐]ᴿᵛ p (lam M)      = cong lam ([≐]ᴿᶜ p M)
  [≐]ᴿᵛ p (V ⦂ᵛ A)     = cong₂ _⦂ᵛ_ ([≐]ᴿᵛ p V) ([≐]ᵛ p A)

  [≐]ᴿᶜ : ∀ {Θ Θ' n} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ → (M : RawC Θ n)
        → M [ σ ]ᴿᶜ ≡ M [ δ ]ᴿᶜ
  [≐]ᴿᶜ p (return V)               = cong return ([≐]ᴿᵛ p V)
  [≐]ᴿᶜ p (M ⨟ N)                  = cong₂ _⨟_ ([≐]ᴿᶜ p M) ([≐]ᴿᶜ p N)
  [≐]ᴿᶜ p (V · W)                  = cong₂ _·_ ([≐]ᴿᵛ p V) ([≐]ᴿᵛ p W)
  [≐]ᴿᶜ p (match V `in M)          = cong₂ match_`in_ ([≐]ᴿᵛ p V) ([≐]ᴿᶜ p M)
  [≐]ᴿᶜ p (absurd V)               = cong absurd ([≐]ᴿᵛ p V)
  [≐]ᴿᶜ p (if V `then M `else N)   =
    cong₃ if_`then_`else_ ([≐]ᴿᵛ p V) ([≐]ᴿᶜ p M) ([≐]ᴿᶜ p N)
  [≐]ᴿᶜ p (cmp ⋈ V W)              = cong₂ (cmp ⋈) ([≐]ᴿᵛ p V) ([≐]ᴿᵛ p W)
  [≐]ᴿᶜ p (caseℕ V `zero M `succ N) =
    cong₃ caseℕ_`zero_`succ_ ([≐]ᴿᵛ p V) ([≐]ᴿᶜ p M) ([≐]ᴿᶜ p N)
  [≐]ᴿᶜ p (case+ V `inl M `inr N) =
    cong₃ case+_`inl_`inr_ ([≐]ᴿᵛ p V) ([≐]ᴿᶜ p M) ([≐]ᴿᶜ p N)
  [≐]ᴿᶜ p (recℕ V M N)             =
    cong₃ recℕ ([≐]ᴿᵛ p V) ([≐]ᴿᶜ p M) ([≐]ᴿᶜ p N)
  [≐]ᴿᶜ p (caseL V `nil M `cons N) =
    cong₃ caseL_`nil_`cons_ ([≐]ᴿᵛ p V) ([≐]ᴿᶜ p M) ([≐]ᴿᶜ p N)
  [≐]ᴿᶜ p (recL V M N)             =
    cong₃ recL ([≐]ᴿᵛ p V) ([≐]ᴿᶜ p M) ([≐]ᴿᶜ p N)
  [≐]ᴿᶜ p (perform op V M)         = cong₂ (perform op) ([≐]ᴿᵛ p V) ([≐]ᴿᶜ p M)
  [≐]ᴿᶜ p (delay τ M)              = cong (delay τ) ([≐]ᴿᶜ p M)
  [≐]ᴿᶜ p (handle M `with H `in N) =
    cong₃ (λ x y z → handle x `with y `in z)
          ([≐]ᴿᶜ p M)
          (fun-ext (λ op → [≐]ᴿᶜ (≐ˢ-↑ᵉ p) (H op)))
          ([≐]ᴿᶜ p N)
  [≐]ᴿᶜ p (unbox i N)              = cong (unbox i) ([≐]ᴿᶜ p N)
  [≐]ᴿᶜ p (box ρ V N)              = cong₃ box ([≐]ʳ p ρ) ([≐]ᴿᵛ p V) ([≐]ᴿᶜ p N)
  [≐]ᴿᶜ p (M ⦂ᶜ C)                 = cong₂ _⦂ᶜ_ ([≐]ᴿᶜ p M) ([≐]ᶜ p C)

-- Identity

mutual

  [id]ᴿᵛ : ∀ {Θ n} → (V : RawV Θ n) → V [ idˢ ]ᴿᵛ ≡ V
  [id]ᴿᵛ (var i)      = refl
  [id]ᴿᵛ (const B c)  = refl
  [id]ᴿᵛ ⋆            = refl
  [id]ᴿᵛ true         = refl
  [id]ᴿᵛ false        = refl
  [id]ᴿᵛ zero         = refl
  [id]ᴿᵛ (succ V)     = cong succ ([id]ᴿᵛ V)
  [id]ᴿᵛ (inl V)     = cong inl ([id]ᴿᵛ V)
  [id]ᴿᵛ (inr V)     = cong inr ([id]ᴿᵛ V)
  [id]ᴿᵛ nil          = refl
  [id]ᴿᵛ (cons V W)   = cong₂ cons ([id]ᴿᵛ V) ([id]ᴿᵛ W)
  [id]ᴿᵛ ⦉ V , W ⦊     = cong₂ ⦉_,_⦊ ([id]ᴿᵛ V) ([id]ᴿᵛ W)
  [id]ᴿᵛ (lam M)      = cong lam ([id]ᴿᶜ M)
  [id]ᴿᵛ (V ⦂ᵛ A)     = cong₂ _⦂ᵛ_ ([id]ᴿᵛ V) ([id]ᵛ A)

  [id]ᴿᶜ : ∀ {Θ n} → (M : RawC Θ n) → M [ idˢ ]ᴿᶜ ≡ M
  [id]ᴿᶜ (return V)               = cong return ([id]ᴿᵛ V)
  [id]ᴿᶜ (M ⨟ N)                  = cong₂ _⨟_ ([id]ᴿᶜ M) ([id]ᴿᶜ N)
  [id]ᴿᶜ (V · W)                  = cong₂ _·_ ([id]ᴿᵛ V) ([id]ᴿᵛ W)
  [id]ᴿᶜ (match V `in M)          = cong₂ match_`in_ ([id]ᴿᵛ V) ([id]ᴿᶜ M)
  [id]ᴿᶜ (absurd V)               = cong absurd ([id]ᴿᵛ V)
  [id]ᴿᶜ (if V `then M `else N)   =
    cong₃ if_`then_`else_ ([id]ᴿᵛ V) ([id]ᴿᶜ M) ([id]ᴿᶜ N)
  [id]ᴿᶜ (cmp ⋈ V W)              = cong₂ (cmp ⋈) ([id]ᴿᵛ V) ([id]ᴿᵛ W)
  [id]ᴿᶜ (caseℕ V `zero M `succ N) =
    cong₃ caseℕ_`zero_`succ_ ([id]ᴿᵛ V) ([id]ᴿᶜ M) ([id]ᴿᶜ N)
  [id]ᴿᶜ (case+ V `inl M `inr N) =
    cong₃ case+_`inl_`inr_ ([id]ᴿᵛ V) ([id]ᴿᶜ M) ([id]ᴿᶜ N)
  [id]ᴿᶜ (recℕ V M N)             =
    cong₃ recℕ ([id]ᴿᵛ V) ([id]ᴿᶜ M) ([id]ᴿᶜ N)
  [id]ᴿᶜ (caseL V `nil M `cons N) =
    cong₃ caseL_`nil_`cons_ ([id]ᴿᵛ V) ([id]ᴿᶜ M) ([id]ᴿᶜ N)
  [id]ᴿᶜ (recL V M N)             =
    cong₃ recL ([id]ᴿᵛ V) ([id]ᴿᶜ M) ([id]ᴿᶜ N)
  [id]ᴿᶜ (perform op V M)         = cong₂ (perform op) ([id]ᴿᵛ V) ([id]ᴿᶜ M)
  [id]ᴿᶜ (delay τ M)              = cong (delay τ) ([id]ᴿᶜ M)
  [id]ᴿᶜ (handle M `with H `in N) =
    cong₃ (λ x y z → handle x `with y `in z)
          ([id]ᴿᶜ M)
          (fun-ext (λ op → trans ([≐]ᴿᶜ ↑ᵉ-id (H op)) ([id]ᴿᶜ (H op))))
          ([id]ᴿᶜ N)
  [id]ᴿᶜ (unbox i N)              = cong (unbox i) ([id]ᴿᶜ N)
  [id]ᴿᶜ (box ρ V N)              = cong₃ box ([id]ʳ ρ) ([id]ᴿᵛ V) ([id]ᴿᶜ N)
  [id]ᴿᶜ (M ⦂ᶜ C)                 = cong₂ _⦂ᶜ_ ([id]ᴿᶜ M) ([id]ᶜ C)

-- Composition

mutual

  [⨟]ᴿᵛ : ∀ {Θ Θ' Θ'' n} → (V : RawV Θ n) → (σ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
        → V [ σ ]ᴿᵛ [ δ ]ᴿᵛ ≡ V [ σ ⨟ˢ δ ]ᴿᵛ
  [⨟]ᴿᵛ (var i)      σ δ = refl
  [⨟]ᴿᵛ (const B c)  σ δ = refl
  [⨟]ᴿᵛ ⋆            σ δ = refl
  [⨟]ᴿᵛ true         σ δ = refl
  [⨟]ᴿᵛ false        σ δ = refl
  [⨟]ᴿᵛ zero         σ δ = refl
  [⨟]ᴿᵛ (succ V)     σ δ = cong succ ([⨟]ᴿᵛ V σ δ)
  [⨟]ᴿᵛ (inl V)     σ δ = cong inl ([⨟]ᴿᵛ V σ δ)
  [⨟]ᴿᵛ (inr V)     σ δ = cong inr ([⨟]ᴿᵛ V σ δ)
  [⨟]ᴿᵛ nil          σ δ = refl
  [⨟]ᴿᵛ (cons V W)   σ δ = cong₂ cons ([⨟]ᴿᵛ V σ δ) ([⨟]ᴿᵛ W σ δ)
  [⨟]ᴿᵛ ⦉ V , W ⦊     σ δ = cong₂ ⦉_,_⦊ ([⨟]ᴿᵛ V σ δ) ([⨟]ᴿᵛ W σ δ)
  [⨟]ᴿᵛ (lam M)      σ δ = cong lam ([⨟]ᴿᶜ M σ δ)
  [⨟]ᴿᵛ (V ⦂ᵛ A)     σ δ = cong₂ _⦂ᵛ_ ([⨟]ᴿᵛ V σ δ) ([⨟]ᵛ A σ δ)

  [⨟]ᴿᶜ : ∀ {Θ Θ' Θ'' n} → (M : RawC Θ n) → (σ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
        → M [ σ ]ᴿᶜ [ δ ]ᴿᶜ ≡ M [ σ ⨟ˢ δ ]ᴿᶜ
  [⨟]ᴿᶜ (return V)               σ δ = cong return ([⨟]ᴿᵛ V σ δ)
  [⨟]ᴿᶜ (M ⨟ N)                  σ δ = cong₂ _⨟_ ([⨟]ᴿᶜ M σ δ) ([⨟]ᴿᶜ N σ δ)
  [⨟]ᴿᶜ (V · W)                  σ δ = cong₂ _·_ ([⨟]ᴿᵛ V σ δ) ([⨟]ᴿᵛ W σ δ)
  [⨟]ᴿᶜ (match V `in M)          σ δ = cong₂ match_`in_ ([⨟]ᴿᵛ V σ δ) ([⨟]ᴿᶜ M σ δ)
  [⨟]ᴿᶜ (absurd V)               σ δ = cong absurd ([⨟]ᴿᵛ V σ δ)
  [⨟]ᴿᶜ (if V `then M `else N)   σ δ =
    cong₃ if_`then_`else_ ([⨟]ᴿᵛ V σ δ) ([⨟]ᴿᶜ M σ δ) ([⨟]ᴿᶜ N σ δ)
  [⨟]ᴿᶜ (cmp ⋈ V W)              σ δ = cong₂ (cmp ⋈) ([⨟]ᴿᵛ V σ δ) ([⨟]ᴿᵛ W σ δ)
  [⨟]ᴿᶜ (caseℕ V `zero M `succ N) σ δ =
    cong₃ caseℕ_`zero_`succ_ ([⨟]ᴿᵛ V σ δ) ([⨟]ᴿᶜ M σ δ) ([⨟]ᴿᶜ N σ δ)
  [⨟]ᴿᶜ (case+ V `inl M `inr N) σ δ =
    cong₃ case+_`inl_`inr_ ([⨟]ᴿᵛ V σ δ) ([⨟]ᴿᶜ M σ δ) ([⨟]ᴿᶜ N σ δ)
  [⨟]ᴿᶜ (recℕ V M N)             σ δ =
    cong₃ recℕ ([⨟]ᴿᵛ V σ δ) ([⨟]ᴿᶜ M σ δ) ([⨟]ᴿᶜ N σ δ)
  [⨟]ᴿᶜ (caseL V `nil M `cons N) σ δ =
    cong₃ caseL_`nil_`cons_ ([⨟]ᴿᵛ V σ δ) ([⨟]ᴿᶜ M σ δ) ([⨟]ᴿᶜ N σ δ)
  [⨟]ᴿᶜ (recL V M N)             σ δ =
    cong₃ recL ([⨟]ᴿᵛ V σ δ) ([⨟]ᴿᶜ M σ δ) ([⨟]ᴿᶜ N σ δ)
  [⨟]ᴿᶜ (perform op V M)         σ δ = cong₂ (perform op) ([⨟]ᴿᵛ V σ δ) ([⨟]ᴿᶜ M σ δ)
  [⨟]ᴿᶜ (delay τ M)              σ δ = cong (delay τ) ([⨟]ᴿᶜ M σ δ)
  [⨟]ᴿᶜ (handle M `with H `in N) σ δ =
    cong₃ (λ x y z → handle x `with y `in z)
          ([⨟]ᴿᶜ M σ δ)
          (fun-ext (λ op → trans ([⨟]ᴿᶜ (H op) (σ ↑ᵉ) (δ ↑ᵉ))
                                 ([≐]ᴿᶜ (⨟-↑ᵉ σ δ) (H op))))
          ([⨟]ᴿᶜ N σ δ)
  [⨟]ᴿᶜ (unbox i N)              σ δ = cong (unbox i) ([⨟]ᴿᶜ N σ δ)
  [⨟]ᴿᶜ (box ρ V N)              σ δ = cong₃ box ([⨟]ʳ ρ σ δ) ([⨟]ᴿᵛ V σ δ) ([⨟]ᴿᶜ N σ δ)
  [⨟]ᴿᶜ (M ⦂ᶜ C)                 σ δ = cong₂ _⦂ᶜ_ ([⨟]ᴿᶜ M σ δ) ([⨟]ᶜ C σ δ)

-- A handler-free term stays handler-free

mutual

  handlerFree-[]ᴿᵛ : ∀ {Θ Θ' n} {σ : Subst Θ Θ'} → (V : RawV Θ n)
                   → HandlerFreeᵛ V → HandlerFreeᵛ (V [ σ ]ᴿᵛ)
  handlerFree-[]ᴿᵛ (var i)      h       = tt
  handlerFree-[]ᴿᵛ (const B c)  h       = tt
  handlerFree-[]ᴿᵛ ⋆            h       = tt
  handlerFree-[]ᴿᵛ true         h       = tt
  handlerFree-[]ᴿᵛ false        h       = tt
  handlerFree-[]ᴿᵛ zero         h       = tt
  handlerFree-[]ᴿᵛ (succ V)     h       = handlerFree-[]ᴿᵛ V h
  handlerFree-[]ᴿᵛ (inl V)     h       = handlerFree-[]ᴿᵛ V h
  handlerFree-[]ᴿᵛ (inr V)     h       = handlerFree-[]ᴿᵛ V h
  handlerFree-[]ᴿᵛ nil          h       = tt
  handlerFree-[]ᴿᵛ (cons V W)   (h , k) = handlerFree-[]ᴿᵛ V h , handlerFree-[]ᴿᵛ W k
  handlerFree-[]ᴿᵛ ⦉ V , W ⦊     (h , k) = handlerFree-[]ᴿᵛ V h , handlerFree-[]ᴿᵛ W k
  handlerFree-[]ᴿᵛ (lam M)      h       = handlerFree-[]ᴿᶜ M h
  handlerFree-[]ᴿᵛ (V ⦂ᵛ A)     h       = handlerFree-[]ᴿᵛ V h

  handlerFree-[]ᴿᶜ : ∀ {Θ Θ' n} {σ : Subst Θ Θ'} → (M : RawC Θ n)
                   → HandlerFreeᶜ M → HandlerFreeᶜ (M [ σ ]ᴿᶜ)
  handlerFree-[]ᴿᶜ (return V)               h           = handlerFree-[]ᴿᵛ V h
  handlerFree-[]ᴿᶜ (M ⨟ N)                  (h , k)     =
    handlerFree-[]ᴿᶜ M h , handlerFree-[]ᴿᶜ N k
  handlerFree-[]ᴿᶜ (V · W)                  (h , k)     =
    handlerFree-[]ᴿᵛ V h , handlerFree-[]ᴿᵛ W k
  handlerFree-[]ᴿᶜ (match V `in M)          (h , k)     =
    handlerFree-[]ᴿᵛ V h , handlerFree-[]ᴿᶜ M k
  handlerFree-[]ᴿᶜ (absurd V)               h           = handlerFree-[]ᴿᵛ V h
  handlerFree-[]ᴿᶜ (if V `then M `else N)   (h , k , l) =
    handlerFree-[]ᴿᵛ V h , handlerFree-[]ᴿᶜ M k , handlerFree-[]ᴿᶜ N l
  handlerFree-[]ᴿᶜ (cmp ⋈ V W)              (h , k)     =
    handlerFree-[]ᴿᵛ V h , handlerFree-[]ᴿᵛ W k
  handlerFree-[]ᴿᶜ (caseℕ V `zero M `succ N) (h , k , l) =
    handlerFree-[]ᴿᵛ V h , handlerFree-[]ᴿᶜ M k , handlerFree-[]ᴿᶜ N l
  handlerFree-[]ᴿᶜ (case+ V `inl M `inr N) (h , k , l) =
    handlerFree-[]ᴿᵛ V h , handlerFree-[]ᴿᶜ M k , handlerFree-[]ᴿᶜ N l
  handlerFree-[]ᴿᶜ (recℕ V M N)             (h , k , l) =
    handlerFree-[]ᴿᵛ V h , handlerFree-[]ᴿᶜ M k , handlerFree-[]ᴿᶜ N l
  handlerFree-[]ᴿᶜ (caseL V `nil M `cons N) (h , k , l) =
    handlerFree-[]ᴿᵛ V h , handlerFree-[]ᴿᶜ M k , handlerFree-[]ᴿᶜ N l
  handlerFree-[]ᴿᶜ (recL V M N)             (h , k , l) =
    handlerFree-[]ᴿᵛ V h , handlerFree-[]ᴿᶜ M k , handlerFree-[]ᴿᶜ N l
  handlerFree-[]ᴿᶜ (perform op V M)         (h , k)     =
    handlerFree-[]ᴿᵛ V h , handlerFree-[]ᴿᶜ M k
  handlerFree-[]ᴿᶜ (delay τ M)              h           = handlerFree-[]ᴿᶜ M h
  handlerFree-[]ᴿᶜ (handle M `with H `in N) ()
  handlerFree-[]ᴿᶜ (unbox i N)              h           = handlerFree-[]ᴿᶜ N h
  handlerFree-[]ᴿᶜ (box ρ V N)              (h , k)     =
    handlerFree-[]ᴿᵛ V h , handlerFree-[]ᴿᶜ N k
  handlerFree-[]ᴿᶜ (M ⦂ᶜ C)                 h           = handlerFree-[]ᴿᶜ M h

-- Inversion: a term whose instance has a given outermost former has that
-- former itself, with the immediate subterms instantiating to those of the
-- instance.

data InvV {Θ Θ' n} (σ : Subst Θ Θ') : RawV Θ n → RawV Θ' n → Set where
  var   : ∀ {i} → InvV σ (var i) (var i)
  const : ∀ {B c} → InvV σ (const B c) (const B c)
  ⋆     : InvV σ ⋆ ⋆
  true  : InvV σ true true
  false : InvV σ false false
  zero  : InvV σ zero zero
  succ  : ∀ {V V'} → V [ σ ]ᴿᵛ ≡ V' → InvV σ (succ V) (succ V')
  inl  : ∀ {V V'} → V [ σ ]ᴿᵛ ≡ V' → InvV σ (inl V) (inl V')
  inr  : ∀ {V V'} → V [ σ ]ᴿᵛ ≡ V' → InvV σ (inr V) (inr V')
  nil  : InvV σ nil nil
  cons : ∀ {V W V' W'} → V [ σ ]ᴿᵛ ≡ V' → W [ σ ]ᴿᵛ ≡ W'
       → InvV σ (cons V W) (cons V' W')
  ⦉_,_⦊  : ∀ {V W V' W'} → V [ σ ]ᴿᵛ ≡ V' → W [ σ ]ᴿᵛ ≡ W'
        → InvV σ ⦉ V , W ⦊ ⦉ V' , W' ⦊
  lam   : ∀ {M M'} → M [ σ ]ᴿᶜ ≡ M' → InvV σ (lam M) (lam M')
  annᵛ  : ∀ {V A V' A'} → V [ σ ]ᴿᵛ ≡ V' → A [ σ ]ᵛ ≡ A'
        → InvV σ (V ⦂ᵛ A) (V' ⦂ᵛ A')

data InvC {Θ Θ' n} (σ : Subst Θ Θ') : RawC Θ n → RawC Θ' n → Set where
  return  : ∀ {V V'} → V [ σ ]ᴿᵛ ≡ V' → InvC σ (return V) (return V')
  _⨟_     : ∀ {M N M' N'} → M [ σ ]ᴿᶜ ≡ M' → N [ σ ]ᴿᶜ ≡ N'
          → InvC σ (M ⨟ N) (M' ⨟ N')
  _·_     : ∀ {V W V' W'} → V [ σ ]ᴿᵛ ≡ V' → W [ σ ]ᴿᵛ ≡ W'
          → InvC σ (V · W) (V' · W')
  match   : ∀ {V M V' M'} → V [ σ ]ᴿᵛ ≡ V' → M [ σ ]ᴿᶜ ≡ M'
          → InvC σ (match V `in M) (match V' `in M')
  absurd  : ∀ {V V'} → V [ σ ]ᴿᵛ ≡ V' → InvC σ (absurd V) (absurd V')
  if      : ∀ {V M N V' M' N'} → V [ σ ]ᴿᵛ ≡ V' → M [ σ ]ᴿᶜ ≡ M' → N [ σ ]ᴿᶜ ≡ N'
          → InvC σ (if V `then M `else N) (if V' `then M' `else N')
  cmp     : ∀ {⋈ V W V' W'} → V [ σ ]ᴿᵛ ≡ V' → W [ σ ]ᴿᵛ ≡ W'
          → InvC σ (cmp ⋈ V W) (cmp ⋈ V' W')
  caseℕ   : ∀ {V M N V' M' N'} → V [ σ ]ᴿᵛ ≡ V' → M [ σ ]ᴿᶜ ≡ M' → N [ σ ]ᴿᶜ ≡ N'
          → InvC σ (caseℕ V `zero M `succ N) (caseℕ V' `zero M' `succ N')
  case+   : ∀ {V M N V' M' N'} → V [ σ ]ᴿᵛ ≡ V' → M [ σ ]ᴿᶜ ≡ M' → N [ σ ]ᴿᶜ ≡ N'
          → InvC σ (case+ V `inl M `inr N) (case+ V' `inl M' `inr N')
  recℕ    : ∀ {V M N V' M' N'} → V [ σ ]ᴿᵛ ≡ V' → M [ σ ]ᴿᶜ ≡ M' → N [ σ ]ᴿᶜ ≡ N'
          → InvC σ (recℕ V M N) (recℕ V' M' N')
  caseL   : ∀ {V M N V' M' N'} → V [ σ ]ᴿᵛ ≡ V' → M [ σ ]ᴿᶜ ≡ M' → N [ σ ]ᴿᶜ ≡ N'
          → InvC σ (caseL V `nil M `cons N) (caseL V' `nil M' `cons N')
  recL    : ∀ {V M N V' M' N'} → V [ σ ]ᴿᵛ ≡ V' → M [ σ ]ᴿᶜ ≡ M' → N [ σ ]ᴿᶜ ≡ N'
          → InvC σ (recL V M N) (recL V' M' N')
  perform : ∀ {op V M V' M'} → V [ σ ]ᴿᵛ ≡ V' → M [ σ ]ᴿᶜ ≡ M'
          → InvC σ (perform op V M) (perform op V' M')
  delay   : ∀ {τ M M'} → M [ σ ]ᴿᶜ ≡ M' → InvC σ (delay τ M) (delay τ M')
  handle  : ∀ {M H N M' H' N'} → M [ σ ]ᴿᶜ ≡ M'
          → ((op : Op) → H op [ σ ↑ᵉ ]ᴿᶜ ≡ H' op) → N [ σ ]ᴿᶜ ≡ N'
          → InvC σ (handle M `with H `in N) (handle M' `with H' `in N')
  unbox   : ∀ {i N N'} → N [ σ ]ᴿᶜ ≡ N' → InvC σ (unbox i N) (unbox i N')
  box     : ∀ {ρ V N ρ' V' N'} → ρ [ σ ]ʳ ≡ ρ' → V [ σ ]ᴿᵛ ≡ V' → N [ σ ]ᴿᶜ ≡ N'
          → InvC σ (box ρ V N) (box ρ' V' N')
  annᶜ    : ∀ {M A ε M' A' ε'} → M [ σ ]ᴿᶜ ≡ M' → A [ σ ]ᵛ ≡ A' → ε [ σ ]ᵉ ≡ ε'
          → InvC σ (M ⦂ᶜ (A ‼ ε)) (M' ⦂ᶜ (A' ‼ ε'))

invV : ∀ {Θ Θ' n} {σ : Subst Θ Θ'} → (V : RawV Θ n) → {V' : RawV Θ' n}
     → V [ σ ]ᴿᵛ ≡ V' → InvV σ V V'
invV (var i)      refl = var
invV (const B c)  refl = const
invV ⋆            refl = ⋆
invV true         refl = true
invV false        refl = false
invV zero         refl = zero
invV (succ V)     refl = succ refl
invV (inl V)     refl = inl refl
invV (inr V)     refl = inr refl
invV nil         refl = nil
invV (cons V W)  refl = cons refl refl
invV ⦉ V , W ⦊     refl = ⦉ refl , refl ⦊
invV (lam M)      refl = lam refl
invV (V ⦂ᵛ A)     refl = annᵛ refl refl

invC : ∀ {Θ Θ' n} {σ : Subst Θ Θ'} → (M : RawC Θ n) → {M' : RawC Θ' n}
     → M [ σ ]ᴿᶜ ≡ M' → InvC σ M M'
invC (return V)               refl = return refl
invC (M ⨟ N)                  refl = refl ⨟ refl
invC (V · W)                  refl = refl · refl
invC (match V `in M)          refl = match refl refl
invC (absurd V)               refl = absurd refl
invC (if V `then M `else N)   refl = if refl refl refl
invC (cmp ⋈ V W)              refl = cmp refl refl
invC (caseℕ V `zero M `succ N) refl = caseℕ refl refl refl
invC (case+ V `inl M `inr N) refl = case+ refl refl refl
invC (recℕ V M N)             refl = recℕ refl refl refl
invC (caseL V `nil M `cons N) refl = caseL refl refl refl
invC (recL V M N)             refl = recL refl refl refl
invC (perform op V M)         refl = perform refl refl
invC (delay τ M)              refl = delay refl
invC (handle M `with H `in N) refl = handle refl (λ op → refl) refl
invC (unbox i N)              refl = unbox refl
invC (box ρ V N)              refl = box refl refl refl
invC (M ⦂ᶜ (A ‼ ε))           refl = annᶜ refl refl refl
