------------------------------------------
-- Renaming actions on well-typed terms --
------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum

open import Relation.Nullary

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.RenActions (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts  S
open import Syntax.Language  S
open import Syntax.Renamings S
open import Syntax.Types     S

-- Renaming of variables
--
-- Stated at the empty ambient, which is where all of the language's renamings
-- and every derived one live. Ambient-indexed renamings act through
-- `expose-ren-[]`.
--
-- `⟨⟩-ext-ctx` is the one rule whose variable is not analysed: it accepts any
-- variable of the context to its left, and pays for it by that variable being
-- eternal, which discharges the grade bound vacuously.

var-rename : ∀ {Δ Δ' A ρ}
           → Ren [] Δ Δ'
           → A ∈[ ρ ] Δ'
           → Σ[ ρ' ∈ R ] ((¬ Eternal A → ρ' ≾ᵣ ρ) × A ∈[ ρ' ] Δ)

var-rename id-ren x =
  _ , (λ _ → ≾ᵣ-refl) , x
var-rename (r₂ ∘ʳ r₁) x with var-rename r₂ x
... | ρ' , ρ'≾ρ , y with var-rename r₁ y
... | ρ'' , ρ''≾ρ' , z =
  ρ'' , (λ ¬et → ≾ᵣ-trans (ρ''≾ρ' ¬et) (ρ'≾ρ ¬et)) , z
var-rename wk-ren x =
  _ , (λ _ → ≾ᵣ-refl) , Tl-∷ x
var-rename (var-ren p y) Hd =
  _ , p , y
var-rename (var-ren p y) (Tl-∷ x) =
  _ , (λ _ → ≾ᵣ-refl) , x
var-rename ⟨⟩-η-ren (Tl-⟨⟩ x) =
  _ , (λ _ → ≾ᵣ-reflexive (sym (·ᵣ-identityʳ _))) , x
var-rename ⟨⟩-η⁻¹-ren x =
  _ , (λ _ → ≾ᵣ-reflexive (·ᵣ-identityʳ _)) , Tl-⟨⟩ x
var-rename ⟨⟩-μ-ren (Tl-⟨⟩ x) =
  _ , (λ _ → ≾ᵣ-reflexive (·ᵣ-assoc _ _ _)) , Tl-⟨⟩ (Tl-⟨⟩ x)
var-rename (⟨⟩-≤-ren {ρ = ρ₁} {ρ' = ρ₂} ρ₂≾ρ₁) (Tl-⟨⟩ x) =
  _ ·ᵣ ρ₂ , (λ _ → ·ᵣ-monoʳ-≾ᵣ ρ₂≾ρ₁) , Tl-⟨⟩ x
var-rename (cong-∷-ren r) Hd =
  uᵣ , (λ _ → ≾ᵣ-refl) , Hd
var-rename (cong-∷-ren r) (Tl-∷ x) with var-rename r x
... | ρ' , ρ'≾ρ , y = ρ' , ρ'≾ρ , Tl-∷ y
var-rename (cong-⟨⟩-ren r) (Tl-⟨⟩ x) with var-rename r x
... | ρ' , ρ'≾ρ , y = ρ' ·ᵣ _ , (λ ¬et → ·ᵣ-monoˡ-≾ᵣ (ρ'≾ρ ¬et)) , Tl-⟨⟩ y
var-rename (⟨⟩-ext-ctx _ ecΔ) x =
  _ , (λ ¬et → ⊥-elim (¬et (ec-eternal ecΔ x))) , Tl-⟨⟩ x

-- Renaming a *resource* variable, i.e. one of box type, which is what `unbox`
-- names. Box types are never eternal, so the grade bound is unconditional.
--
-- Stated with projections rather than a `with`, so that the `unbox` clause of
-- the action below reduces to an `unbox` node at an abstract renaming.

rvar-rename : ∀ {Γ Γ' A ρ ρ'}
            → Ren [] Γ Γ'
            → [ ρ ] A ∈[ ρ' ] Γ'
            -----------------------------------------------------------
            → Σ[ ρ'' ∈ R ] (([ ρ ] A ∈[ ρ'' ] Γ) × ρ'' ≾ᵣ ρ')

rvar-rename r x =
    proj₁ (var-rename r x)
  , proj₂ (proj₂ (var-rename r x))
  , proj₁ (proj₂ (var-rename r x)) (λ ())

-- The value-taking reading of `unbox`, as a derived rule.
--
-- The value is not taken in `Γ` but in a `Δ` that `Γ` reaches through one lock
-- of the box's own grade -- a Fitch-style witness. It has to be: `Eternal` has
-- no `[_]_` clause, so a box type is never eternal and `var`'s premise
-- `¬ Eternal A → ρ' ≾ᵣ uᵣ` always fires at box type. Any *value* of box type
-- therefore already carries `ρ' ≾ᵣ uᵣ`, i.e. that essentially no time has
-- passed, which is exactly what unboxing after a `delay` must not require. The
-- lookup-based rule bypasses that premise by reading the elapsed grade off the
-- context; a value-taking rule has to recover it, and the renaming is where
-- from.

unbox⇒var : ∀ {Γ Δ A ρ}
          → Ren [] Γ (Δ ⟨ ρ ⟩)
          → Δ ⊢V⦂ [ ρ ] A
          --------------------------------------------------------
          → Σ[ ρ₀ ∈ R ] Σ[ A₀ ∈ VType ] Σ[ ρ' ∈ R ]
              (([ ρ₀ ] A₀ ∈[ ρ' ] Γ) × (ρ' ≾ᵣ ρ₀) × (A₀ <:ᵛ A))

unbox⇒var {ρ = ρ} r V with grad-typ⇒var<: V
... | ρ₀ , A₀ , σ , y , (ρ≾ρ₀ , p) , σ≾u with var-rename r (Tl-⟨⟩ y)
... | ρ' , ρ'≾σ·ρ , z =
    ρ₀ , A₀ , ρ' , z
  , ≾ᵣ-trans (ρ'≾σ·ρ (λ ()))
      (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ σ≾u)
        (≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ ρ)) ρ≾ρ₀))
  , p

unbox-val : ∀ {Γ Δ A C ρ}
          → Ren [] Γ (Δ ⟨ ρ ⟩)
          → Δ ⊢V⦂ [ ρ ] A
          → Γ ∷ A ⊢C⦂ C
          ---------------
          → Γ ⊢C⦂ C

unbox-val r V M with unbox⇒var r V
... | _ , _ , _ , x , rel , p = unbox x rel p M

-- Action of renamings on well-typed values and computations
--
-- At the empty ambient throughout, and so transport-free: a handler clause's
-- context is the renamed one under one more lock and two more binders.

mutual

  V-rename : ∀ {Γ Γ' A}
           → Ren [] Γ Γ'
           → Γ' ⊢V⦂ A
           ------------
           → Γ ⊢V⦂ A

  V-rename r (var f x) with var-rename r x
  ... | _ , ρ'≾ρ , y = var (λ p → ≾ᵣ-trans (ρ'≾ρ p) (f p)) y
  V-rename r (const c)   = const c
  V-rename r ⋆           = ⋆
  V-rename r true        = true
  V-rename r false       = false
  V-rename r (⦉ V , W ⦊)  = ⦉ V-rename r V , V-rename r W ⦊
  V-rename r (lam M)     = lam (C-rename (cong-ren r) M)
  V-rename r (subV V p)  = subV (V-rename r V) p

  C-rename : ∀ {Γ Γ' C}
           → Ren [] Γ Γ'
           → Γ' ⊢C⦂ C
           ------------
           → Γ ⊢C⦂ C

  C-rename r (return V)       = return (V-rename r V)
  C-rename r (M ⨟ N)          = C-rename r M ⨟ C-rename (cong-ren r) N
  C-rename r (V · W)          = V-rename r V · V-rename r W
  C-rename r (match V `in M)  = match V-rename r V `in C-rename (cong-ren r) M
  C-rename r (absurd V)       = absurd (V-rename r V)
  C-rename r (if V `then M `else N) =
    if V-rename r V `then C-rename r M `else C-rename r N
  C-rename r (perform op V M) = perform op (V-rename r V) (C-rename (cong-ren r) M)
  C-rename r (delay τ M)      = delay τ (C-rename (cong-ren r) M)
  C-rename r (handle M `with H `in N) =
    handle C-rename r M
    `with (λ op ε'' →
             C-rename (cong-∷-ren (cong-∷-ren (cong-⟨⟩-ren r))) (H op ε''))
    `in (C-rename (cong-ren r) N)
  C-rename r (unbox x rel p M) =
    unbox (proj₁ (proj₂ (rvar-rename r x)))
          (≾ᵣ-trans (proj₂ (proj₂ (rvar-rename r x))) rel) p
          (C-rename (cong-ren r) M)
  C-rename r (box V M) = box (V-rename (cong-ren r) V) (C-rename (cong-ren r) M)
  C-rename r (subC M p) = subC (C-rename r M) p
