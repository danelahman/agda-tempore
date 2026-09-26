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

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Raw.Subst (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Types S using (_‼_)
open import TypeInference.OpenSyntax.Subst S

open import TypeInference.Raw.Syntax S

infixl 50 _[_]ᴿᵛ _[_]ᴿᶜ

mutual

  _[_]ᴿᵛ : ∀ {Θ Θ' n} → RawV Θ n → Subst Θ Θ' → RawV Θ' n
  var i        [ σ ]ᴿᵛ = var i
  const B c    [ σ ]ᴿᵛ = const B c
  ⋆            [ σ ]ᴿᵛ = ⋆
  true         [ σ ]ᴿᵛ = true
  false        [ σ ]ᴿᵛ = false
  ⦉ V , W ⦊     [ σ ]ᴿᵛ = ⦉ (V [ σ ]ᴿᵛ) , (W [ σ ]ᴿᵛ) ⦊
  lam M        [ σ ]ᴿᵛ = lam (M [ σ ]ᴿᶜ)
  (lam[ A ] M) [ σ ]ᴿᵛ = lam[ A [ σ ]ᵛ ] (M [ σ ]ᴿᶜ)
  (V ⦂ᵛ A)     [ σ ]ᴿᵛ = (V [ σ ]ᴿᵛ) ⦂ᵛ (A [ σ ]ᵛ)

  _[_]ᴿᶜ : ∀ {Θ Θ' n} → RawC Θ n → Subst Θ Θ' → RawC Θ' n
  return V                 [ σ ]ᴿᶜ = return (V [ σ ]ᴿᵛ)
  (M ⨟ N)                  [ σ ]ᴿᶜ = (M [ σ ]ᴿᶜ) ⨟ (N [ σ ]ᴿᶜ)
  (V · W)                  [ σ ]ᴿᶜ = (V [ σ ]ᴿᵛ) · (W [ σ ]ᴿᵛ)
  (match V `in M)          [ σ ]ᴿᶜ = match (V [ σ ]ᴿᵛ) `in (M [ σ ]ᴿᶜ)
  absurd V                 [ σ ]ᴿᶜ = absurd (V [ σ ]ᴿᵛ)
  (if V `then M `else N)   [ σ ]ᴿᶜ = if (V [ σ ]ᴿᵛ) `then (M [ σ ]ᴿᶜ) `else (N [ σ ]ᴿᶜ)
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
  [≐]ᴿᵛ p ⦉ V , W ⦊     = cong₂ ⦉_,_⦊ ([≐]ᴿᵛ p V) ([≐]ᴿᵛ p W)
  [≐]ᴿᵛ p (lam M)      = cong lam ([≐]ᴿᶜ p M)
  [≐]ᴿᵛ p (lam[ A ] M) = cong₂ lam[_]_ ([≐]ᵛ p A) ([≐]ᴿᶜ p M)
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
  [id]ᴿᵛ ⦉ V , W ⦊     = cong₂ ⦉_,_⦊ ([id]ᴿᵛ V) ([id]ᴿᵛ W)
  [id]ᴿᵛ (lam M)      = cong lam ([id]ᴿᶜ M)
  [id]ᴿᵛ (lam[ A ] M) = cong₂ lam[_]_ ([id]ᵛ A) ([id]ᴿᶜ M)
  [id]ᴿᵛ (V ⦂ᵛ A)     = cong₂ _⦂ᵛ_ ([id]ᴿᵛ V) ([id]ᵛ A)

  [id]ᴿᶜ : ∀ {Θ n} → (M : RawC Θ n) → M [ idˢ ]ᴿᶜ ≡ M
  [id]ᴿᶜ (return V)               = cong return ([id]ᴿᵛ V)
  [id]ᴿᶜ (M ⨟ N)                  = cong₂ _⨟_ ([id]ᴿᶜ M) ([id]ᴿᶜ N)
  [id]ᴿᶜ (V · W)                  = cong₂ _·_ ([id]ᴿᵛ V) ([id]ᴿᵛ W)
  [id]ᴿᶜ (match V `in M)          = cong₂ match_`in_ ([id]ᴿᵛ V) ([id]ᴿᶜ M)
  [id]ᴿᶜ (absurd V)               = cong absurd ([id]ᴿᵛ V)
  [id]ᴿᶜ (if V `then M `else N)   =
    cong₃ if_`then_`else_ ([id]ᴿᵛ V) ([id]ᴿᶜ M) ([id]ᴿᶜ N)
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
  [⨟]ᴿᵛ ⦉ V , W ⦊     σ δ = cong₂ ⦉_,_⦊ ([⨟]ᴿᵛ V σ δ) ([⨟]ᴿᵛ W σ δ)
  [⨟]ᴿᵛ (lam M)      σ δ = cong lam ([⨟]ᴿᶜ M σ δ)
  [⨟]ᴿᵛ (lam[ A ] M) σ δ = cong₂ lam[_]_ ([⨟]ᵛ A σ δ) ([⨟]ᴿᶜ M σ δ)
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
  handlerFree-[]ᴿᵛ ⦉ V , W ⦊     (h , k) = handlerFree-[]ᴿᵛ V h , handlerFree-[]ᴿᵛ W k
  handlerFree-[]ᴿᵛ (lam M)      h       = handlerFree-[]ᴿᶜ M h
  handlerFree-[]ᴿᵛ (lam[ A ] M) h       = handlerFree-[]ᴿᶜ M h
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
  ⦉_,_⦊  : ∀ {V W V' W'} → V [ σ ]ᴿᵛ ≡ V' → W [ σ ]ᴿᵛ ≡ W'
        → InvV σ ⦉ V , W ⦊ ⦉ V' , W' ⦊
  lam   : ∀ {M M'} → M [ σ ]ᴿᶜ ≡ M' → InvV σ (lam M) (lam M')
  lamᵃ  : ∀ {A M A' M'} → A [ σ ]ᵛ ≡ A' → M [ σ ]ᴿᶜ ≡ M'
        → InvV σ (lam[ A ] M) (lam[ A' ] M')
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
invV ⦉ V , W ⦊     refl = ⦉ refl , refl ⦊
invV (lam M)      refl = lam refl
invV (lam[ A ] M) refl = lamᵃ refl refl
invV (V ⦂ᵛ A)     refl = annᵛ refl refl

invC : ∀ {Θ Θ' n} {σ : Subst Θ Θ'} → (M : RawC Θ n) → {M' : RawC Θ' n}
     → M [ σ ]ᴿᶜ ≡ M' → InvC σ M M'
invC (return V)               refl = return refl
invC (M ⨟ N)                  refl = refl ⨟ refl
invC (V · W)                  refl = refl · refl
invC (match V `in M)          refl = match refl refl
invC (absurd V)               refl = absurd refl
invC (if V `then M `else N)   refl = if refl refl refl
invC (perform op V M)         refl = perform refl refl
invC (delay τ M)              refl = delay refl
invC (handle M `with H `in N) refl = handle refl (λ op → refl) refl
invC (unbox i N)              refl = unbox refl
invC (box ρ V N)              refl = box refl refl refl
invC (M ⦂ᶜ (A ‼ ε))           refl = annᶜ refl refl refl
