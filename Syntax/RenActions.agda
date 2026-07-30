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

-- Transporting a typing along an equality of contexts

∈-ctx-≡ : ∀ {Γ Γ' A ρ} → Γ ≡ Γ' → A ∈[ ρ ] Γ → A ∈[ ρ ] Γ'
∈-ctx-≡ refl x = x

V-ctx-≡ : ∀ {Γ Γ' A} → Γ ≡ Γ' → Γ ⊢V⦂ A → Γ' ⊢V⦂ A
V-ctx-≡ refl V = V

C-ctx-≡ : ∀ {Γ Γ' C} → Γ ≡ Γ' → Γ ⊢C⦂ C → Γ' ⊢C⦂ C
C-ctx-≡ refl M = M

-- Splitting the eternal restriction of an ambient-plus-local context, then
-- reassociating a suffix onto the local half. This is the shape an effect
-- handler clause's context takes once the ambient index is in play.

ᴱ-++ᶜ-assoc : (Ξ Δ Θ : Ctx) → ((Ξ ++ᶜ Δ) ᴱ) ++ᶜ Θ ≡ (Ξ ᴱ) ++ᶜ ((Δ ᴱ) ++ᶜ Θ)
ᴱ-++ᶜ-assoc Ξ Δ Θ =
  trans (cong (_++ᶜ Θ) (ᴱ-++ᶜ Ξ Δ)) (++ᶜ-assoc (Ξ ᴱ) (Δ ᴱ) Θ)

-- Renaming of variables
--
-- Stated at the empty ambient, which is where all of the language's renamings
-- and every derived one live: `[] ᴱ` is `[]`, and the congruences preserve it,
-- so nothing here is transported and every clause reduces. Ambient-indexed
-- renamings act through `expose-ren-[]` (see `V-renameᴬ` below).
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
var-rename (⟨⟩-ext-ren et) (Tl-⟨⟩ Hd) =
  uᵣ , (λ ¬et → ⊥-elim (¬et et)) , Hd
var-rename (⟨⟩-ext-ren et) (Tl-⟨⟩ (Tl-∷ x)) =
  _ , (λ _ → ≾ᵣ-refl) , Tl-∷ (Tl-⟨⟩ x)
var-rename (⟨⟩-ext-ctx _ ecΔ) x =
  _ , (λ ¬et → ⊥-elim (¬et (ec-eternal ecΔ x))) , Tl-⟨⟩ x

-- A FGCBV-specific variable-based variant of `unbox` based on every value of
-- box-type being forced to be a variable (as proved below in unbox⇒var).

unbox-var : ∀ {Γ A C ρ ρ'}
          → (x : [ ρ ] A ∈[ ρ' ] Γ)
          → ρ' ≾ᵣ ρ
          → Γ ∷ A ⊢C⦂ C
          → Γ ⊢C⦂ C
unbox-var x rel M =
  unbox
    ((⟨⟩-≤-ren rel
      ∘ʳ wk-ren-⟨ρ⟩-ctx (split-grade-≡ x))
     ∘ʳ eq-ren (split-≡ (split-pf x)))
    (var (λ _ → ≾ᵣ-refl) Hd)
    M

-- Extracting the underlying variable (and grade bound) from a box-typed value

unbox⇒var : ∀ {Γ A ρ Δ}
          → Ren [] Γ (Δ ⟨ ρ ⟩)
          → Δ ⊢V⦂ [ ρ ] A
          → Σ[ ρ' ∈ R ] (([ ρ ] A ∈[ ρ' ] Γ) × ρ' ≾ᵣ ρ)
unbox⇒var {ρ = ρ} w V with grad-typ⇒var V
... | _ , y , f , _ with var-rename w (Tl-⟨⟩ y)
... | ρ' , ρ'≾ρy·ρ , z =
  ρ' , z ,
  ≾ᵣ-trans (ρ'≾ρy·ρ (λ ()))
    (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (f (λ ()))) (≾ᵣ-reflexive (·ᵣ-identityˡ ρ)))

-- Action of renamings on well-typed values and computations
--
-- At the empty ambient throughout, and so transport-free: `unbox`'s stored
-- certificate lives there too and composes directly, and the handler clauses'
-- `restrict-ren r` stays there because `[] ᴱ` is `[]`.

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
  V-rename r (⦉ V , W ⦊)  = ⦉ V-rename r V , V-rename r W ⦊
  V-rename r (lam M)     = lam (C-rename (cong-ren r) M)

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
  C-rename r (perform op V M) = perform op (V-rename r V) (C-rename (cong-ren r) M)
  C-rename r (delay τ M)      = delay τ (C-rename (cong-ren r) M)
  C-rename r (handle M `with H `in N) =
    handle C-rename r M
    `with (λ op ε'' →
             C-rename (cong-∷-ren (cong-∷-ren (restrict-ren r))) (H op ε''))
    `in (C-rename (cong-ren r) N)
  C-rename r (unbox w V M) =
    unbox (w ∘ʳ r) V (C-rename (cong-ren r) M)
  C-rename r (box V M) = box (V-rename (cong-ren r) V) (C-rename (cong-ren r) M)
  C-rename r (coerce rel M) = coerce rel (C-rename r M)

-- ACTING BY AN AMBIENT-INDEXED RENAMING
--
-- A renaming that fixes an ambient acts by first forgetting what it fixes:
-- `expose-ren-[]` reassociates `Ren Ξ Δ Δ'` into a renaming of `Ξ ++ᶜ Δ` proper,
-- which is the context such a term has. This is the form the eternal weakening
-- takes, `wk-ren-ctx` being ambient-indexed.

V-renameᴬ : ∀ {Ξ Δ Δ' A} → Ren Ξ Δ Δ' → (Ξ ++ᶜ Δ') ⊢V⦂ A → (Ξ ++ᶜ Δ) ⊢V⦂ A
V-renameᴬ r V = V-rename (expose-ren-[] r) V

C-renameᴬ : ∀ {Ξ Δ Δ' C} → Ren Ξ Δ Δ' → (Ξ ++ᶜ Δ') ⊢C⦂ C → (Ξ ++ᶜ Δ) ⊢C⦂ C
C-renameᴬ r M = C-rename (expose-ren-[] r) M

-- THE ETERNAL WEAKENING
--
-- Inserting a context `Γ'` after an all-eternal prefix `Ξ`, under an arbitrary
-- suffix `Θ`. This is an ordinary renaming action: `wk-ren-ctx` introduces the
-- locks of `Γ'` by `⟨⟩-ext-ctx`, which is exactly what the eternal ambient
-- licenses. Its coherence is therefore `C-rename-nat`, and its preservation of
-- `Paramᶜ` is `renᶜ` — no separate recursion over terms.

wkᵛ : ∀ {Ξ A} → EternalCtx Ξ → (Γ' Θ : Ctx)
    → (Ξ ++ᶜ Θ) ⊢V⦂ A → (Ξ ++ᶜ (Γ' ++ᶜ Θ)) ⊢V⦂ A
wkᵛ ec Γ' Θ V = V-renameᴬ (wk-ren-ctx ec Γ' Θ) V

wkᶜ : ∀ {Ξ C} → EternalCtx Ξ → (Γ' Θ : Ctx)
    → (Ξ ++ᶜ Θ) ⊢C⦂ C → (Ξ ++ᶜ (Γ' ++ᶜ Θ)) ⊢C⦂ C
wkᶜ ec Γ' Θ M = C-renameᴬ (wk-ren-ctx ec Γ' Θ) M
