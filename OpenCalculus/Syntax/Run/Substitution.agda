------------------------------------------------------------------
-- Parallel substitution of run-time terms                      --
--                                                              --
-- `psubᵛ σ`, `psubᶜ σ` replace every variable `i` by `σ i`.    --
-- They respect pointwise equality, compose with renaming and   --
-- with each other, and a substitution of variables is a        --
-- renaming; the substitution at depth `k` is the parallel one  --
-- at `subVar k U`.                                             --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)

open import Language.Spec
open import Language.Operations

open import Util.Equality

module OpenCalculus.Syntax.Run.Substitution (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops

open import OpenCalculus.Syntax.Run S

-- Lifting under a binder

exts : ∀ {n m} → (Fin n → RunV m) → Fin (suc n) → RunV (suc m)
exts σ zero    = var zero
exts σ (suc i) = wkᵛ (σ i)

mutual

  psubᵛ : ∀ {n m} → (Fin n → RunV m) → RunV n → RunV m
  psubᵛ σ (var i) = σ i
  psubᵛ σ (const B c) = const B c
  psubᵛ σ ⋆ = ⋆
  psubᵛ σ true = true
  psubᵛ σ false = false
  psubᵛ σ zero = zero
  psubᵛ σ nil = nil
  psubᵛ σ (succ V) = succ (psubᵛ σ V)
  psubᵛ σ (inl V) = inl (psubᵛ σ V)
  psubᵛ σ (inr V) = inr (psubᵛ σ V)
  psubᵛ σ ⦉ V , W ⦊ = ⦉ (psubᵛ σ V) , (psubᵛ σ W) ⦊
  psubᵛ σ (cons V W) = cons (psubᵛ σ V) (psubᵛ σ W)
  psubᵛ σ (cmp ⋈ V W) = cmp ⋈ (psubᵛ σ V) (psubᵛ σ W)
  psubᵛ σ (lam M) = lam (psubᶜ (exts σ) M)
  psubᵛ σ (handler N H) = handler (psubᶜ (exts σ) N) (λ op → psubᶜ (exts (exts σ)) (H op))

  psubᶜ : ∀ {n m} → (Fin n → RunV m) → RunC n → RunC m
  psubᶜ σ (return V) = return (psubᵛ σ V)
  psubᶜ σ (M ⨟ N) = (psubᶜ σ M) ⨟ (psubᶜ (exts σ) N)
  psubᶜ σ (V · W) = (psubᵛ σ V) · (psubᵛ σ W)
  psubᶜ σ (match V `in M) = match (psubᵛ σ V) `in (psubᶜ (exts (exts σ)) M)
  psubᶜ σ (absurd V) = absurd (psubᵛ σ V)
  psubᶜ σ (if V `then M `else N) = if (psubᵛ σ V) `then (psubᶜ σ M) `else (psubᶜ σ N)
  psubᶜ σ (caseℕ V `zero M `succ N) = caseℕ (psubᵛ σ V) `zero (psubᶜ σ M) `succ (psubᶜ (exts σ) N)
  psubᶜ σ (case+ V `inl M `inr N) = case+ (psubᵛ σ V) `inl (psubᶜ (exts σ) M) `inr (psubᶜ (exts σ) N)
  psubᶜ σ (caseL V `nil M `cons N) = caseL (psubᵛ σ V) `nil (psubᶜ σ M) `cons (psubᶜ (exts (exts σ)) N)
  psubᶜ σ (recℕ V M N) = recℕ (psubᵛ σ V) (psubᶜ σ M) (psubᶜ (exts (exts σ)) N)
  psubᶜ σ (recL V M N) = recL (psubᵛ σ V) (psubᶜ σ M) (psubᶜ (exts (exts (exts σ))) N)
  psubᶜ σ (perform op V M) = perform op (psubᵛ σ V) (psubᶜ (exts σ) M)
  psubᶜ σ (delay τ M) = delay τ (psubᶜ σ M)
  psubᶜ σ (handle M `with V) = handle (psubᶜ σ M) `with (psubᵛ σ V)
  psubᶜ σ (unbox V N) = unbox (psubᵛ σ V) (psubᶜ (exts σ) N)
  psubᶜ σ (box V N) = box (psubᵛ σ V) (psubᶜ (exts σ) N)

------------------------------------------------------------------------
-- Laws

exts-cong : ∀ {n m} {σ τ : Fin n → RunV m} → (∀ i → σ i ≡ τ i) → ∀ i → exts σ i ≡ exts τ i
exts-cong p zero    = refl
exts-cong p (suc i) = cong wkᵛ (p i)

mutual

  psub-congᵛ : ∀ {n m} {σ τ : Fin n → RunV m} → (∀ i → σ i ≡ τ i) → (V : RunV n) → psubᵛ σ V ≡ psubᵛ τ V
  psub-congᵛ p (var i) = p i
  psub-congᵛ p (const B c) = refl
  psub-congᵛ p ⋆ = refl
  psub-congᵛ p true = refl
  psub-congᵛ p false = refl
  psub-congᵛ p zero = refl
  psub-congᵛ p nil = refl
  psub-congᵛ p (succ V) = cong succ (psub-congᵛ p V)
  psub-congᵛ p (inl V) = cong inl (psub-congᵛ p V)
  psub-congᵛ p (inr V) = cong inr (psub-congᵛ p V)
  psub-congᵛ p ⦉ V , W ⦊ = cong₂ ⦉_,_⦊ (psub-congᵛ p V) (psub-congᵛ p W)
  psub-congᵛ p (cons V W) = cong₂ cons (psub-congᵛ p V) (psub-congᵛ p W)
  psub-congᵛ p (cmp ⋈ V W) = cong₂ (cmp ⋈) (psub-congᵛ p V) (psub-congᵛ p W)
  psub-congᵛ p (lam M) = cong lam (psub-congᶜ (exts-cong p) M)
  psub-congᵛ p (handler N H) = cong₂ handler (psub-congᶜ (exts-cong p) N) (fun-ext (λ op → psub-congᶜ (exts-cong (exts-cong p)) (H op)))

  psub-congᶜ : ∀ {n m} {σ τ : Fin n → RunV m} → (∀ i → σ i ≡ τ i) → (M : RunC n) → psubᶜ σ M ≡ psubᶜ τ M
  psub-congᶜ p (return V) = cong return (psub-congᵛ p V)
  psub-congᶜ p (M ⨟ N) = cong₂ _⨟_ (psub-congᶜ p M) (psub-congᶜ (exts-cong p) N)
  psub-congᶜ p (V · W) = cong₂ _·_ (psub-congᵛ p V) (psub-congᵛ p W)
  psub-congᶜ p (match V `in M) = cong₂ match_`in_ (psub-congᵛ p V) (psub-congᶜ (exts-cong (exts-cong p)) M)
  psub-congᶜ p (absurd V) = cong absurd (psub-congᵛ p V)
  psub-congᶜ p (if V `then M `else N) = cong₃ if_`then_`else_ (psub-congᵛ p V) (psub-congᶜ p M) (psub-congᶜ p N)
  psub-congᶜ p (caseℕ V `zero M `succ N) = cong₃ caseℕ_`zero_`succ_ (psub-congᵛ p V) (psub-congᶜ p M) (psub-congᶜ (exts-cong p) N)
  psub-congᶜ p (case+ V `inl M `inr N) = cong₃ case+_`inl_`inr_ (psub-congᵛ p V) (psub-congᶜ (exts-cong p) M) (psub-congᶜ (exts-cong p) N)
  psub-congᶜ p (caseL V `nil M `cons N) = cong₃ caseL_`nil_`cons_ (psub-congᵛ p V) (psub-congᶜ p M) (psub-congᶜ (exts-cong (exts-cong p)) N)
  psub-congᶜ p (recℕ V M N) = cong₃ recℕ (psub-congᵛ p V) (psub-congᶜ p M) (psub-congᶜ (exts-cong (exts-cong p)) N)
  psub-congᶜ p (recL V M N) = cong₃ recL (psub-congᵛ p V) (psub-congᶜ p M) (psub-congᶜ (exts-cong (exts-cong (exts-cong p))) N)
  psub-congᶜ p (perform op V M) = cong₂ (perform op) (psub-congᵛ p V) (psub-congᶜ (exts-cong p) M)
  psub-congᶜ p (delay τ M) = cong (delay τ) (psub-congᶜ p M)
  psub-congᶜ p (handle M `with V) = cong₂ handle_`with_ (psub-congᶜ p M) (psub-congᵛ p V)
  psub-congᶜ p (unbox V N) = cong₂ unbox (psub-congᵛ p V) (psub-congᶜ (exts-cong p) N)
  psub-congᶜ p (box V N) = cong₂ box (psub-congᵛ p V) (psub-congᶜ (exts-cong p) N)

ren-exts : ∀ {n m k} {f : Fin m → Fin k} {σ : Fin n → RunV m} {τ : Fin n → RunV k}
         → (∀ i → renᵛ f (σ i) ≡ τ i) → ∀ i → renᵛ (ext f) (exts σ i) ≡ exts τ i
ren-exts p zero    = refl
ren-exts {σ = σ} p (suc i) =
  trans (ren-fuseᵛ (λ j → refl) (σ i))
        (trans (sym (ren-fuseᵛ (λ j → refl) (σ i))) (cong wkᵛ (p i)))

mutual

  ren-psubᵛ : ∀ {n m k} {f : Fin m → Fin k} {σ : Fin n → RunV m} {τ : Fin n → RunV k} → (∀ i → renᵛ f (σ i) ≡ τ i) → (V : RunV n) → renᵛ f (psubᵛ σ V) ≡ psubᵛ τ V
  ren-psubᵛ p (var i) = p i
  ren-psubᵛ p (const B c) = refl
  ren-psubᵛ p ⋆ = refl
  ren-psubᵛ p true = refl
  ren-psubᵛ p false = refl
  ren-psubᵛ p zero = refl
  ren-psubᵛ p nil = refl
  ren-psubᵛ p (succ V) = cong succ (ren-psubᵛ p V)
  ren-psubᵛ p (inl V) = cong inl (ren-psubᵛ p V)
  ren-psubᵛ p (inr V) = cong inr (ren-psubᵛ p V)
  ren-psubᵛ p ⦉ V , W ⦊ = cong₂ ⦉_,_⦊ (ren-psubᵛ p V) (ren-psubᵛ p W)
  ren-psubᵛ p (cons V W) = cong₂ cons (ren-psubᵛ p V) (ren-psubᵛ p W)
  ren-psubᵛ p (cmp ⋈ V W) = cong₂ (cmp ⋈) (ren-psubᵛ p V) (ren-psubᵛ p W)
  ren-psubᵛ p (lam M) = cong lam (ren-psubᶜ (ren-exts p) M)
  ren-psubᵛ p (handler N H) = cong₂ handler (ren-psubᶜ (ren-exts p) N) (fun-ext (λ op → ren-psubᶜ (ren-exts (ren-exts p)) (H op)))

  ren-psubᶜ : ∀ {n m k} {f : Fin m → Fin k} {σ : Fin n → RunV m} {τ : Fin n → RunV k} → (∀ i → renᵛ f (σ i) ≡ τ i) → (M : RunC n) → renᶜ f (psubᶜ σ M) ≡ psubᶜ τ M
  ren-psubᶜ p (return V) = cong return (ren-psubᵛ p V)
  ren-psubᶜ p (M ⨟ N) = cong₂ _⨟_ (ren-psubᶜ p M) (ren-psubᶜ (ren-exts p) N)
  ren-psubᶜ p (V · W) = cong₂ _·_ (ren-psubᵛ p V) (ren-psubᵛ p W)
  ren-psubᶜ p (match V `in M) = cong₂ match_`in_ (ren-psubᵛ p V) (ren-psubᶜ (ren-exts (ren-exts p)) M)
  ren-psubᶜ p (absurd V) = cong absurd (ren-psubᵛ p V)
  ren-psubᶜ p (if V `then M `else N) = cong₃ if_`then_`else_ (ren-psubᵛ p V) (ren-psubᶜ p M) (ren-psubᶜ p N)
  ren-psubᶜ p (caseℕ V `zero M `succ N) = cong₃ caseℕ_`zero_`succ_ (ren-psubᵛ p V) (ren-psubᶜ p M) (ren-psubᶜ (ren-exts p) N)
  ren-psubᶜ p (case+ V `inl M `inr N) = cong₃ case+_`inl_`inr_ (ren-psubᵛ p V) (ren-psubᶜ (ren-exts p) M) (ren-psubᶜ (ren-exts p) N)
  ren-psubᶜ p (caseL V `nil M `cons N) = cong₃ caseL_`nil_`cons_ (ren-psubᵛ p V) (ren-psubᶜ p M) (ren-psubᶜ (ren-exts (ren-exts p)) N)
  ren-psubᶜ p (recℕ V M N) = cong₃ recℕ (ren-psubᵛ p V) (ren-psubᶜ p M) (ren-psubᶜ (ren-exts (ren-exts p)) N)
  ren-psubᶜ p (recL V M N) = cong₃ recL (ren-psubᵛ p V) (ren-psubᶜ p M) (ren-psubᶜ (ren-exts (ren-exts (ren-exts p))) N)
  ren-psubᶜ p (perform op V M) = cong₂ (perform op) (ren-psubᵛ p V) (ren-psubᶜ (ren-exts p) M)
  ren-psubᶜ p (delay τ M) = cong (delay τ) (ren-psubᶜ p M)
  ren-psubᶜ p (handle M `with V) = cong₂ handle_`with_ (ren-psubᶜ p M) (ren-psubᵛ p V)
  ren-psubᶜ p (unbox V N) = cong₂ unbox (ren-psubᵛ p V) (ren-psubᶜ (ren-exts p) N)
  ren-psubᶜ p (box V N) = cong₂ box (ren-psubᵛ p V) (ren-psubᶜ (ren-exts p) N)

exts-ren : ∀ {n m k} {f : Fin n → Fin m} {σ : Fin m → RunV k} {τ : Fin n → RunV k}
         → (∀ i → σ (f i) ≡ τ i) → ∀ i → exts σ (ext f i) ≡ exts τ i
exts-ren p zero    = refl
exts-ren p (suc i) = cong wkᵛ (p i)

mutual

  psub-renᵛ : ∀ {n m k} {f : Fin n → Fin m} {σ : Fin m → RunV k} {τ : Fin n → RunV k} → (∀ i → σ (f i) ≡ τ i) → (V : RunV n) → psubᵛ σ (renᵛ f V) ≡ psubᵛ τ V
  psub-renᵛ p (var i) = p i
  psub-renᵛ p (const B c) = refl
  psub-renᵛ p ⋆ = refl
  psub-renᵛ p true = refl
  psub-renᵛ p false = refl
  psub-renᵛ p zero = refl
  psub-renᵛ p nil = refl
  psub-renᵛ p (succ V) = cong succ (psub-renᵛ p V)
  psub-renᵛ p (inl V) = cong inl (psub-renᵛ p V)
  psub-renᵛ p (inr V) = cong inr (psub-renᵛ p V)
  psub-renᵛ p ⦉ V , W ⦊ = cong₂ ⦉_,_⦊ (psub-renᵛ p V) (psub-renᵛ p W)
  psub-renᵛ p (cons V W) = cong₂ cons (psub-renᵛ p V) (psub-renᵛ p W)
  psub-renᵛ p (cmp ⋈ V W) = cong₂ (cmp ⋈) (psub-renᵛ p V) (psub-renᵛ p W)
  psub-renᵛ p (lam M) = cong lam (psub-renᶜ (exts-ren p) M)
  psub-renᵛ p (handler N H) = cong₂ handler (psub-renᶜ (exts-ren p) N) (fun-ext (λ op → psub-renᶜ (exts-ren (exts-ren p)) (H op)))

  psub-renᶜ : ∀ {n m k} {f : Fin n → Fin m} {σ : Fin m → RunV k} {τ : Fin n → RunV k} → (∀ i → σ (f i) ≡ τ i) → (M : RunC n) → psubᶜ σ (renᶜ f M) ≡ psubᶜ τ M
  psub-renᶜ p (return V) = cong return (psub-renᵛ p V)
  psub-renᶜ p (M ⨟ N) = cong₂ _⨟_ (psub-renᶜ p M) (psub-renᶜ (exts-ren p) N)
  psub-renᶜ p (V · W) = cong₂ _·_ (psub-renᵛ p V) (psub-renᵛ p W)
  psub-renᶜ p (match V `in M) = cong₂ match_`in_ (psub-renᵛ p V) (psub-renᶜ (exts-ren (exts-ren p)) M)
  psub-renᶜ p (absurd V) = cong absurd (psub-renᵛ p V)
  psub-renᶜ p (if V `then M `else N) = cong₃ if_`then_`else_ (psub-renᵛ p V) (psub-renᶜ p M) (psub-renᶜ p N)
  psub-renᶜ p (caseℕ V `zero M `succ N) = cong₃ caseℕ_`zero_`succ_ (psub-renᵛ p V) (psub-renᶜ p M) (psub-renᶜ (exts-ren p) N)
  psub-renᶜ p (case+ V `inl M `inr N) = cong₃ case+_`inl_`inr_ (psub-renᵛ p V) (psub-renᶜ (exts-ren p) M) (psub-renᶜ (exts-ren p) N)
  psub-renᶜ p (caseL V `nil M `cons N) = cong₃ caseL_`nil_`cons_ (psub-renᵛ p V) (psub-renᶜ p M) (psub-renᶜ (exts-ren (exts-ren p)) N)
  psub-renᶜ p (recℕ V M N) = cong₃ recℕ (psub-renᵛ p V) (psub-renᶜ p M) (psub-renᶜ (exts-ren (exts-ren p)) N)
  psub-renᶜ p (recL V M N) = cong₃ recL (psub-renᵛ p V) (psub-renᶜ p M) (psub-renᶜ (exts-ren (exts-ren (exts-ren p))) N)
  psub-renᶜ p (perform op V M) = cong₂ (perform op) (psub-renᵛ p V) (psub-renᶜ (exts-ren p) M)
  psub-renᶜ p (delay τ M) = cong (delay τ) (psub-renᶜ p M)
  psub-renᶜ p (handle M `with V) = cong₂ handle_`with_ (psub-renᶜ p M) (psub-renᵛ p V)
  psub-renᶜ p (unbox V N) = cong₂ unbox (psub-renᵛ p V) (psub-renᶜ (exts-ren p) N)
  psub-renᶜ p (box V N) = cong₂ box (psub-renᵛ p V) (psub-renᶜ (exts-ren p) N)

exts-psub : ∀ {n m k} {σ : Fin m → RunV k} {τ : Fin n → RunV m} {υ : Fin n → RunV k}
          → (∀ i → psubᵛ σ (τ i) ≡ υ i) → ∀ i → psubᵛ (exts σ) (exts τ i) ≡ exts υ i
exts-psub p zero    = refl
exts-psub {τ = τ} p (suc i) =
  trans (psub-renᵛ (λ j → refl) (τ i))
        (trans (sym (ren-psubᵛ (λ j → refl) (τ i))) (cong wkᵛ (p i)))

mutual

  psub-psubᵛ : ∀ {n m k} {σ : Fin m → RunV k} {τ : Fin n → RunV m} {υ : Fin n → RunV k} → (∀ i → psubᵛ σ (τ i) ≡ υ i) → (V : RunV n) → psubᵛ σ (psubᵛ τ V) ≡ psubᵛ υ V
  psub-psubᵛ p (var i) = p i
  psub-psubᵛ p (const B c) = refl
  psub-psubᵛ p ⋆ = refl
  psub-psubᵛ p true = refl
  psub-psubᵛ p false = refl
  psub-psubᵛ p zero = refl
  psub-psubᵛ p nil = refl
  psub-psubᵛ p (succ V) = cong succ (psub-psubᵛ p V)
  psub-psubᵛ p (inl V) = cong inl (psub-psubᵛ p V)
  psub-psubᵛ p (inr V) = cong inr (psub-psubᵛ p V)
  psub-psubᵛ p ⦉ V , W ⦊ = cong₂ ⦉_,_⦊ (psub-psubᵛ p V) (psub-psubᵛ p W)
  psub-psubᵛ p (cons V W) = cong₂ cons (psub-psubᵛ p V) (psub-psubᵛ p W)
  psub-psubᵛ p (cmp ⋈ V W) = cong₂ (cmp ⋈) (psub-psubᵛ p V) (psub-psubᵛ p W)
  psub-psubᵛ p (lam M) = cong lam (psub-psubᶜ (exts-psub p) M)
  psub-psubᵛ p (handler N H) = cong₂ handler (psub-psubᶜ (exts-psub p) N) (fun-ext (λ op → psub-psubᶜ (exts-psub (exts-psub p)) (H op)))

  psub-psubᶜ : ∀ {n m k} {σ : Fin m → RunV k} {τ : Fin n → RunV m} {υ : Fin n → RunV k} → (∀ i → psubᵛ σ (τ i) ≡ υ i) → (M : RunC n) → psubᶜ σ (psubᶜ τ M) ≡ psubᶜ υ M
  psub-psubᶜ p (return V) = cong return (psub-psubᵛ p V)
  psub-psubᶜ p (M ⨟ N) = cong₂ _⨟_ (psub-psubᶜ p M) (psub-psubᶜ (exts-psub p) N)
  psub-psubᶜ p (V · W) = cong₂ _·_ (psub-psubᵛ p V) (psub-psubᵛ p W)
  psub-psubᶜ p (match V `in M) = cong₂ match_`in_ (psub-psubᵛ p V) (psub-psubᶜ (exts-psub (exts-psub p)) M)
  psub-psubᶜ p (absurd V) = cong absurd (psub-psubᵛ p V)
  psub-psubᶜ p (if V `then M `else N) = cong₃ if_`then_`else_ (psub-psubᵛ p V) (psub-psubᶜ p M) (psub-psubᶜ p N)
  psub-psubᶜ p (caseℕ V `zero M `succ N) = cong₃ caseℕ_`zero_`succ_ (psub-psubᵛ p V) (psub-psubᶜ p M) (psub-psubᶜ (exts-psub p) N)
  psub-psubᶜ p (case+ V `inl M `inr N) = cong₃ case+_`inl_`inr_ (psub-psubᵛ p V) (psub-psubᶜ (exts-psub p) M) (psub-psubᶜ (exts-psub p) N)
  psub-psubᶜ p (caseL V `nil M `cons N) = cong₃ caseL_`nil_`cons_ (psub-psubᵛ p V) (psub-psubᶜ p M) (psub-psubᶜ (exts-psub (exts-psub p)) N)
  psub-psubᶜ p (recℕ V M N) = cong₃ recℕ (psub-psubᵛ p V) (psub-psubᶜ p M) (psub-psubᶜ (exts-psub (exts-psub p)) N)
  psub-psubᶜ p (recL V M N) = cong₃ recL (psub-psubᵛ p V) (psub-psubᶜ p M) (psub-psubᶜ (exts-psub (exts-psub (exts-psub p))) N)
  psub-psubᶜ p (perform op V M) = cong₂ (perform op) (psub-psubᵛ p V) (psub-psubᶜ (exts-psub p) M)
  psub-psubᶜ p (delay τ M) = cong (delay τ) (psub-psubᶜ p M)
  psub-psubᶜ p (handle M `with V) = cong₂ handle_`with_ (psub-psubᶜ p M) (psub-psubᵛ p V)
  psub-psubᶜ p (unbox V N) = cong₂ unbox (psub-psubᵛ p V) (psub-psubᶜ (exts-psub p) N)
  psub-psubᶜ p (box V N) = cong₂ box (psub-psubᵛ p V) (psub-psubᶜ (exts-psub p) N)

exts-var : ∀ {n m} {σ : Fin n → RunV m} {f : Fin n → Fin m}
         → (∀ i → σ i ≡ var (f i)) → ∀ i → exts σ i ≡ var (ext f i)
exts-var p zero    = refl
exts-var p (suc i) = cong wkᵛ (p i)

mutual

  psub-varᵛ : ∀ {n m} {σ : Fin n → RunV m} {f : Fin n → Fin m} → (∀ i → σ i ≡ var (f i)) → (V : RunV n) → psubᵛ σ V ≡ renᵛ f V
  psub-varᵛ p (var i) = p i
  psub-varᵛ p (const B c) = refl
  psub-varᵛ p ⋆ = refl
  psub-varᵛ p true = refl
  psub-varᵛ p false = refl
  psub-varᵛ p zero = refl
  psub-varᵛ p nil = refl
  psub-varᵛ p (succ V) = cong succ (psub-varᵛ p V)
  psub-varᵛ p (inl V) = cong inl (psub-varᵛ p V)
  psub-varᵛ p (inr V) = cong inr (psub-varᵛ p V)
  psub-varᵛ p ⦉ V , W ⦊ = cong₂ ⦉_,_⦊ (psub-varᵛ p V) (psub-varᵛ p W)
  psub-varᵛ p (cons V W) = cong₂ cons (psub-varᵛ p V) (psub-varᵛ p W)
  psub-varᵛ p (cmp ⋈ V W) = cong₂ (cmp ⋈) (psub-varᵛ p V) (psub-varᵛ p W)
  psub-varᵛ p (lam M) = cong lam (psub-varᶜ (exts-var p) M)
  psub-varᵛ p (handler N H) = cong₂ handler (psub-varᶜ (exts-var p) N) (fun-ext (λ op → psub-varᶜ (exts-var (exts-var p)) (H op)))

  psub-varᶜ : ∀ {n m} {σ : Fin n → RunV m} {f : Fin n → Fin m} → (∀ i → σ i ≡ var (f i)) → (M : RunC n) → psubᶜ σ M ≡ renᶜ f M
  psub-varᶜ p (return V) = cong return (psub-varᵛ p V)
  psub-varᶜ p (M ⨟ N) = cong₂ _⨟_ (psub-varᶜ p M) (psub-varᶜ (exts-var p) N)
  psub-varᶜ p (V · W) = cong₂ _·_ (psub-varᵛ p V) (psub-varᵛ p W)
  psub-varᶜ p (match V `in M) = cong₂ match_`in_ (psub-varᵛ p V) (psub-varᶜ (exts-var (exts-var p)) M)
  psub-varᶜ p (absurd V) = cong absurd (psub-varᵛ p V)
  psub-varᶜ p (if V `then M `else N) = cong₃ if_`then_`else_ (psub-varᵛ p V) (psub-varᶜ p M) (psub-varᶜ p N)
  psub-varᶜ p (caseℕ V `zero M `succ N) = cong₃ caseℕ_`zero_`succ_ (psub-varᵛ p V) (psub-varᶜ p M) (psub-varᶜ (exts-var p) N)
  psub-varᶜ p (case+ V `inl M `inr N) = cong₃ case+_`inl_`inr_ (psub-varᵛ p V) (psub-varᶜ (exts-var p) M) (psub-varᶜ (exts-var p) N)
  psub-varᶜ p (caseL V `nil M `cons N) = cong₃ caseL_`nil_`cons_ (psub-varᵛ p V) (psub-varᶜ p M) (psub-varᶜ (exts-var (exts-var p)) N)
  psub-varᶜ p (recℕ V M N) = cong₃ recℕ (psub-varᵛ p V) (psub-varᶜ p M) (psub-varᶜ (exts-var (exts-var p)) N)
  psub-varᶜ p (recL V M N) = cong₃ recL (psub-varᵛ p V) (psub-varᶜ p M) (psub-varᶜ (exts-var (exts-var (exts-var p))) N)
  psub-varᶜ p (perform op V M) = cong₂ (perform op) (psub-varᵛ p V) (psub-varᶜ (exts-var p) M)
  psub-varᶜ p (delay τ M) = cong (delay τ) (psub-varᶜ p M)
  psub-varᶜ p (handle M `with V) = cong₂ handle_`with_ (psub-varᶜ p M) (psub-varᵛ p V)
  psub-varᶜ p (unbox V N) = cong₂ unbox (psub-varᵛ p V) (psub-varᶜ (exts-var p) N)
  psub-varᶜ p (box V N) = cong₂ box (psub-varᵛ p V) (psub-varᶜ (exts-var p) N)

-- The identity substitution

psub-idᶜ : ∀ {n} → (M : RunC n) → psubᶜ var M ≡ M
psub-idᶜ M = trans (psub-varᶜ {f = λ i → i} (λ i → refl) M) (ren-idᶜ (λ i → refl) M)

psub-idᵛ : ∀ {n} → (V : RunV n) → psubᵛ var V ≡ V
psub-idᵛ V = trans (psub-varᵛ {f = λ i → i} (λ i → refl) V) (ren-idᵛ (λ i → refl) V)

-- The substitution at depth `k`

subVar-exts₁ : ∀ {n} → (k : ℕ) → (U : RunV n) → ∀ i → subVar (suc k) U i ≡ exts (subVar k U) i
subVar-exts₁ k U zero    = refl
subVar-exts₁ k U (suc i) = refl

subVar-exts₂ : ∀ {n} → (k : ℕ) → (U : RunV n)
             → ∀ i → subVar (suc (suc k)) U i ≡ exts (exts (subVar k U)) i
subVar-exts₂ k U zero          = refl
subVar-exts₂ k U (suc zero)    = refl
subVar-exts₂ k U (suc (suc i)) = refl

subVar-exts₃ : ∀ {n} → (k : ℕ) → (U : RunV n)
             → ∀ i → subVar (suc (suc (suc k))) U i ≡ exts (exts (exts (subVar k U))) i
subVar-exts₃ k U zero                = refl
subVar-exts₃ k U (suc zero)          = refl
subVar-exts₃ k U (suc (suc zero))    = refl
subVar-exts₃ k U (suc (suc (suc i))) = refl

mutual

  sub-psubᵛ : ∀ {n} (k : ℕ) (U : RunV n) (V : RunV (k + suc n)) → subᵛ k U V ≡ psubᵛ (subVar k U) V
  sub-psubᵛ k U (var i) = refl
  sub-psubᵛ k U (const B c) = refl
  sub-psubᵛ k U ⋆ = refl
  sub-psubᵛ k U true = refl
  sub-psubᵛ k U false = refl
  sub-psubᵛ k U zero = refl
  sub-psubᵛ k U nil = refl
  sub-psubᵛ k U (succ V) = cong succ (sub-psubᵛ k U V)
  sub-psubᵛ k U (inl V) = cong inl (sub-psubᵛ k U V)
  sub-psubᵛ k U (inr V) = cong inr (sub-psubᵛ k U V)
  sub-psubᵛ k U ⦉ V , W ⦊ = cong₂ ⦉_,_⦊ (sub-psubᵛ k U V) (sub-psubᵛ k U W)
  sub-psubᵛ k U (cons V W) = cong₂ cons (sub-psubᵛ k U V) (sub-psubᵛ k U W)
  sub-psubᵛ k U (cmp ⋈ V W) = cong₂ (cmp ⋈) (sub-psubᵛ k U V) (sub-psubᵛ k U W)
  sub-psubᵛ k U (lam M) = cong lam (trans (sub-psubᶜ (suc k) U M) (psub-congᶜ (subVar-exts₁ k U) M))
  sub-psubᵛ k U (handler N H) = cong₂ handler (trans (sub-psubᶜ (suc k) U N) (psub-congᶜ (subVar-exts₁ k U) N)) (fun-ext (λ op → trans (sub-psubᶜ (suc (suc k)) U (H op)) (psub-congᶜ (subVar-exts₂ k U) (H op))))

  sub-psubᶜ : ∀ {n} (k : ℕ) (U : RunV n) (M : RunC (k + suc n)) → subᶜ k U M ≡ psubᶜ (subVar k U) M
  sub-psubᶜ k U (return V) = cong return (sub-psubᵛ k U V)
  sub-psubᶜ k U (M ⨟ N) = cong₂ _⨟_ (sub-psubᶜ k U M) (trans (sub-psubᶜ (suc k) U N) (psub-congᶜ (subVar-exts₁ k U) N))
  sub-psubᶜ k U (V · W) = cong₂ _·_ (sub-psubᵛ k U V) (sub-psubᵛ k U W)
  sub-psubᶜ k U (match V `in M) = cong₂ match_`in_ (sub-psubᵛ k U V) (trans (sub-psubᶜ (suc (suc k)) U M) (psub-congᶜ (subVar-exts₂ k U) M))
  sub-psubᶜ k U (absurd V) = cong absurd (sub-psubᵛ k U V)
  sub-psubᶜ k U (if V `then M `else N) = cong₃ if_`then_`else_ (sub-psubᵛ k U V) (sub-psubᶜ k U M) (sub-psubᶜ k U N)
  sub-psubᶜ k U (caseℕ V `zero M `succ N) = cong₃ caseℕ_`zero_`succ_ (sub-psubᵛ k U V) (sub-psubᶜ k U M) (trans (sub-psubᶜ (suc k) U N) (psub-congᶜ (subVar-exts₁ k U) N))
  sub-psubᶜ k U (case+ V `inl M `inr N) = cong₃ case+_`inl_`inr_ (sub-psubᵛ k U V) (trans (sub-psubᶜ (suc k) U M) (psub-congᶜ (subVar-exts₁ k U) M)) (trans (sub-psubᶜ (suc k) U N) (psub-congᶜ (subVar-exts₁ k U) N))
  sub-psubᶜ k U (caseL V `nil M `cons N) = cong₃ caseL_`nil_`cons_ (sub-psubᵛ k U V) (sub-psubᶜ k U M) (trans (sub-psubᶜ (suc (suc k)) U N) (psub-congᶜ (subVar-exts₂ k U) N))
  sub-psubᶜ k U (recℕ V M N) = cong₃ recℕ (sub-psubᵛ k U V) (sub-psubᶜ k U M) (trans (sub-psubᶜ (suc (suc k)) U N) (psub-congᶜ (subVar-exts₂ k U) N))
  sub-psubᶜ k U (recL V M N) = cong₃ recL (sub-psubᵛ k U V) (sub-psubᶜ k U M) (trans (sub-psubᶜ (suc (suc (suc k))) U N) (psub-congᶜ (subVar-exts₃ k U) N))
  sub-psubᶜ k U (perform op V M) = cong₂ (perform op) (sub-psubᵛ k U V) (trans (sub-psubᶜ (suc k) U M) (psub-congᶜ (subVar-exts₁ k U) M))
  sub-psubᶜ k U (delay τ M) = cong (delay τ) (sub-psubᶜ k U M)
  sub-psubᶜ k U (handle M `with V) = cong₂ handle_`with_ (sub-psubᶜ k U M) (sub-psubᵛ k U V)
  sub-psubᶜ k U (unbox V N) = cong₂ unbox (sub-psubᵛ k U V) (trans (sub-psubᶜ (suc k) U N) (psub-congᶜ (subVar-exts₁ k U) N))
  sub-psubᶜ k U (box V N) = cong₂ box (sub-psubᵛ k U V) (trans (sub-psubᶜ (suc k) U N) (psub-congᶜ (subVar-exts₁ k U) N))

