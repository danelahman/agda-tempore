-------------------------------------------------------------------------
-- Coherence of the renaming action.                                   --
--                                                                     --
-- The action is functorial and a congruence. The premises are stated  --
-- at `_≐ʳ_`, since `Ren` is freely generated and `cong-ren` commutes  --
-- with `_∘ʳ_` only up to it; the conclusions are equalities of terms. --
-------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.Syntax.Renaming.Coherence (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts   Spec
open import MonomorphicCalculus.Syntax.Terms   Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming   Spec
open import MonomorphicCalculus.Syntax.Types Spec
open import MonomorphicCalculus.Syntax.Renaming.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Terms.Equivalence     Spec


-- Renaming a variable is the variable the renaming sends it to: `var-img`
-- records the position, and the grade bound it recomputes is invisible to
-- `_≡_`. Stated at an arbitrary bound so that the caller may present the
-- result with whichever bound its own typing supplies.

var-ren-≡ : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ' Γ) → (x : A ∈[ ρ ] Γ)
          → (f  : ¬ Et A → ρ ≾ᵣ 𝟏ᵣ)
          → (f' : ¬ Et A → proj₁ (var-img r x) ≾ᵣ 𝟏ᵣ)
          → V-rename r (var f x) ≡ var f' (proj₂ (var-img r x))
var-ren-≡ r x f f' with var-rename r x
... | _ , _ , y = var-≡

-- The same with the target supplied, for callers that have computed it.

var-ren-img-≡ : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ' Γ) → (x : A ∈[ ρ ] Γ)
              → (f : ¬ Et A → ρ ≾ᵣ 𝟏ᵣ) → {t : Var Γ' A}
              → var-img r x ≡ t → (f' : ¬ Et A → proj₁ t ≾ᵣ 𝟏ᵣ)
              → V-rename r (var f x) ≡ var f' (proj₂ t)
var-ren-img-≡ r x f refl f' = var-ren-≡ r x f f'

-- The renaming action respects the `≐ʳ` equivalence on renamings.

mutual

  V-rename-≡ : ∀ {Γ Γ' A} {r r' : Ren [] Γ Γ'} → r ≐ʳ r'
             → (V : Γ' ⊢V⦂ A) → V-rename r V ≡ V-rename r' V

  V-rename-≡ {r = r} {r' = r'} h (var f x)
    with var-rename r x | var-rename r' x | at h x
  ... | _ | _ | refl = var-≡
  V-rename-≡ h (const B c) = refl
  V-rename-≡ h ⋆           = refl
  V-rename-≡ h true        = refl
  V-rename-≡ h false       = refl
  V-rename-≡ h zero        = refl
  V-rename-≡ h (succ V)    = cong succ (V-rename-≡ h V)
  V-rename-≡ h ⦉ V , W ⦊   = cong₂ ⦉_,_⦊ (V-rename-≡ h V) (V-rename-≡ h W)
  V-rename-≡ h (inl V)     = cong inl (V-rename-≡ h V)
  V-rename-≡ h (inr V)     = cong inr (V-rename-≡ h V)
  V-rename-≡ h nil         = refl
  V-rename-≡ h (cons V W)  = cong₂ cons (V-rename-≡ h V) (V-rename-≡ h W)
  V-rename-≡ h (fun M)     = cong fun (C-rename-≡ (cong-ren-≐ʳ ([] ∷ _) h) M)
  V-rename-≡ h (handler N H) =
    handler-≡ (C-rename-≡ (cong-ren-≐ʳ (_ ⟨ _ ⟩ ∷ _) h) N)
      (λ op ε'' →
         C-rename-≡ (cong-ren-≐ʳ (_ ⟨ _ ⟩ ∷ _ ∷ _) h) (H op ε''))
  V-rename-≡ h (subV V p) = subV-≡ (V-rename-≡ h V)

  C-rename-≡ : ∀ {Γ Γ' C} {r r' : Ren [] Γ Γ'} → r ≐ʳ r'
             → (M : Γ' ⊢C⦂ C) → C-rename r M ≡ C-rename r' M

  C-rename-≡ h (return V) = cong return (V-rename-≡ h V)
  C-rename-≡ h (M ⨟ N) =
    cong₂ _⨟_ (C-rename-≡ h M) (C-rename-≡ (cong-ren-≐ʳ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-≡ h (V · W) = cong₂ _·_ (V-rename-≡ h V) (V-rename-≡ h W)
  C-rename-≡ h (match V `with M) =
    cong₂ match_`with_ (V-rename-≡ h V) (C-rename-≡ (cong-ren-≐ʳ ([] ∷ _ ∷ _) h) M)
  C-rename-≡ h (absurd V) = cong absurd (V-rename-≡ h V)
  C-rename-≡ h (cmp ⋈ V W et) =
    cong₂ (λ a b → cmp ⋈ a b et) (V-rename-≡ h V) (V-rename-≡ h W)
  C-rename-≡ h (if V `then M `else N) =
    cong₃ if_`then_`else_
      (V-rename-≡ h V) (C-rename-≡ h M) (C-rename-≡ h N)
  C-rename-≡ h (matchℕ V `zero M `succ N) =
    cong₃ matchℕ_`zero_`succ_
      (V-rename-≡ h V) (C-rename-≡ h M)
      (C-rename-≡ (cong-ren-≐ʳ ([] ∷ _) h) N)
  C-rename-≡ h (recℕ V M N p) =
    cong₃ (λ a b c → recℕ a b c p)
      (V-rename-≡ h V) (C-rename-≡ h M)
      (C-rename-≡ (cong-ren-≐ʳ (([] ⟨ _ ⟩ ∷ nat) ⟨ _ ⟩ ∷ _) h) N)
  C-rename-≡ h (matchL V `nil M `cons N) =
    cong₃ matchL_`nil_`cons_
      (V-rename-≡ h V) (C-rename-≡ h M)
      (C-rename-≡ (cong-ren-≐ʳ ([] ∷ _ ∷ _) h) N)
  C-rename-≡ h (recL V M N p) =
    cong₃ (λ a b c → recL a b c p)
      (V-rename-≡ h V) (C-rename-≡ h M)
      (C-rename-≡ (cong-ren-≐ʳ (([] ⟨ _ ⟩ ∷ _ ∷ list _) ⟨ _ ⟩ ∷ _) h) N)
  C-rename-≡ h (match+ V `inl M `inr N) =
    cong₃ match+_`inl_`inr_
      (V-rename-≡ h V) (C-rename-≡ (cong-ren-≐ʳ ([] ∷ _) h) M)
      (C-rename-≡ (cong-ren-≐ʳ ([] ∷ _) h) N)
  C-rename-≡ h (perform op V M) =
    cong₂ (perform _) (V-rename-≡ h V) (C-rename-≡ (cong-ren-≐ʳ (_ ⟨ _ ⟩ ∷ _) h) M)
  C-rename-≡ h (delay τ M) =
    cong (delay _) (C-rename-≡ (cong-ren-≐ʳ ([] ⟨ _ ⟩) h) M)
  C-rename-≡ h (handle M `with V) =
    cong₂ handle_`with_ (C-rename-≡ h M) (V-rename-≡ h V)
  C-rename-≡ h (unbox x rel p M) =
    unbox-≡ (rvar-≡ (at h x)) (C-rename-≡ (cong-ren-≐ʳ ([] ∷ _) h) M)
  C-rename-≡ h (box _ V M) =
    cong₂ (box _) (V-rename-≡ (cong-ren-≐ʳ ([] ⟨ _ ⟩) h) V)
          (C-rename-≡ (cong-ren-≐ʳ ([] ∷ _) h) M)
  C-rename-≡ h (subC M p) = subC-≡ (C-rename-≡ h M)

-- `cong-∷-ren id-ren`, `⟨⟩-≤-ren` at equal grades, and `⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-η-ren`
-- all act as the identity without being it; the action is the identity only
-- up to the equivalence.

⟨⟩-≤-ren-id-≐ʳ : ∀ {Γ ρ} → (p : ρ ≾ᵣ ρ) → ⟨⟩-≤-ren {Δ = Γ} p ≐ʳ id-ren
⟨⟩-≤-ren-id-≐ʳ p = mk≐ʳ go
  where
    go : ∀ {A ρ₀} → (x : A ∈[ ρ₀ ] _) → _
    go (Tl-⟨⟩ x) = refl

cong-∷-ren-id-≐ʳ : ∀ {Γ A} {r : Ren [] Γ Γ}
                → r ≐ʳ id-ren → cong-∷-ren {A = A} r ≐ʳ id-ren
cong-∷-ren-id-≐ʳ h = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go Hd       = refl
    go (Tl-∷ x) = cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (at h x)

cong-⟨⟩-ren-id-≐ʳ : ∀ {Γ ρ} {r : Ren [] Γ Γ}
                 → r ≐ʳ id-ren → cong-⟨⟩-ren {ρ = ρ} r ≐ʳ id-ren
cong-⟨⟩-ren-id-≐ʳ {ρ = ρ} h = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go (Tl-⟨⟩ x) = cong (λ z → proj₁ z ·ᵣ ρ , Tl-⟨⟩ (proj₂ z)) (at h x)

cong-ren-id-≐ʳ : ∀ {Γ} {r : Ren [] Γ Γ} → (Γ₀ : Ctx)
              → r ≐ʳ id-ren → cong-ren {Γ'' = Γ₀} r ≐ʳ id-ren
cong-ren-id-≐ʳ []         h = h
cong-ren-id-≐ʳ (Γ₀ ∷ A)   h = cong-∷-ren-id-≐ʳ (cong-ren-id-≐ʳ Γ₀ h)
cong-ren-id-≐ʳ (Γ₀ ⟨ ρ ⟩) h = cong-⟨⟩-ren-id-≐ʳ (cong-ren-id-≐ʳ Γ₀ h)

∘ʳ-idˡ-≐ʳ : ∀ {Γ Γ'} {r : Ren [] Γ' Γ'} → (w : Ren [] Γ Γ')
        → r ≐ʳ id-ren → (r ∘ʳ w) ≐ʳ w
∘ʳ-idˡ-≐ʳ w h = mk≐ʳ (λ x → cong (var-img′ w) (at h x))

mutual

  V-rename-id-≡ : ∀ {Γ A} {r : Ren [] Γ Γ} → r ≐ʳ id-ren
                → (V : Γ ⊢V⦂ A) → V-rename r V ≡ V

  V-rename-id-≡ {r = r} h (var f x) with var-rename r x | at h x
  ... | _ | refl = var-≡
  V-rename-id-≡ h (const B c) = refl
  V-rename-id-≡ h ⋆         = refl
  V-rename-id-≡ h true      = refl
  V-rename-id-≡ h false     = refl
  V-rename-id-≡ h zero      = refl
  V-rename-id-≡ h (succ V)  = cong succ (V-rename-id-≡ h V)
  V-rename-id-≡ h ⦉ V , W ⦊  = cong₂ ⦉_,_⦊ (V-rename-id-≡ h V) (V-rename-id-≡ h W)
  V-rename-id-≡ h (inl V)   = cong inl (V-rename-id-≡ h V)
  V-rename-id-≡ h (inr V)   = cong inr (V-rename-id-≡ h V)
  V-rename-id-≡ h nil       = refl
  V-rename-id-≡ h (cons V W) = cong₂ cons (V-rename-id-≡ h V) (V-rename-id-≡ h W)
  V-rename-id-≡ h (fun M)   = cong fun (C-rename-id-≡ (cong-ren-id-≐ʳ ([] ∷ _) h) M)
  V-rename-id-≡ h (handler N H) =
    handler-≡ (C-rename-id-≡ (cong-ren-id-≐ʳ (_ ⟨ _ ⟩ ∷ _) h) N)
      (λ op ε'' →
         C-rename-id-≡ (cong-ren-id-≐ʳ (_ ⟨ _ ⟩ ∷ _ ∷ _) h) (H op ε''))
  V-rename-id-≡ h (subV V p) = subV-≡ (V-rename-id-≡ h V)

  C-rename-id-≡ : ∀ {Γ C} {r : Ren [] Γ Γ} → r ≐ʳ id-ren
                → (M : Γ ⊢C⦂ C) → C-rename r M ≡ M

  C-rename-id-≡ h (return V) = cong return (V-rename-id-≡ h V)
  C-rename-id-≡ h (M ⨟ N) =
    cong₂ _⨟_ (C-rename-id-≡ h M) (C-rename-id-≡ (cong-ren-id-≐ʳ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-id-≡ h (V · W) = cong₂ _·_ (V-rename-id-≡ h V) (V-rename-id-≡ h W)
  C-rename-id-≡ h (match V `with M) =
    cong₂ match_`with_ (V-rename-id-≡ h V) (C-rename-id-≡ (cong-ren-id-≐ʳ ([] ∷ _ ∷ _) h) M)
  C-rename-id-≡ h (absurd V) = cong absurd (V-rename-id-≡ h V)
  C-rename-id-≡ h (cmp ⋈ V W et) =
    cong₂ (λ a b → cmp ⋈ a b et) (V-rename-id-≡ h V) (V-rename-id-≡ h W)
  C-rename-id-≡ h (if V `then M `else N) =
    cong₃ if_`then_`else_
      (V-rename-id-≡ h V) (C-rename-id-≡ h M) (C-rename-id-≡ h N)
  C-rename-id-≡ h (matchℕ V `zero M `succ N) =
    cong₃ matchℕ_`zero_`succ_
      (V-rename-id-≡ h V) (C-rename-id-≡ h M)
      (C-rename-id-≡ (cong-ren-id-≐ʳ ([] ∷ _) h) N)
  C-rename-id-≡ h (recℕ V M N p) =
    cong₃ (λ a b c → recℕ a b c p)
      (V-rename-id-≡ h V) (C-rename-id-≡ h M)
      (C-rename-id-≡ (cong-ren-id-≐ʳ (([] ⟨ _ ⟩ ∷ nat) ⟨ _ ⟩ ∷ _) h) N)
  C-rename-id-≡ h (matchL V `nil M `cons N) =
    cong₃ matchL_`nil_`cons_
      (V-rename-id-≡ h V) (C-rename-id-≡ h M)
      (C-rename-id-≡ (cong-ren-id-≐ʳ ([] ∷ _ ∷ _) h) N)
  C-rename-id-≡ h (recL V M N p) =
    cong₃ (λ a b c → recL a b c p)
      (V-rename-id-≡ h V) (C-rename-id-≡ h M)
      (C-rename-id-≡ (cong-ren-id-≐ʳ (([] ⟨ _ ⟩ ∷ _ ∷ list _) ⟨ _ ⟩ ∷ _) h) N)
  C-rename-id-≡ h (match+ V `inl M `inr N) =
    cong₃ match+_`inl_`inr_
      (V-rename-id-≡ h V) (C-rename-id-≡ (cong-ren-id-≐ʳ ([] ∷ _) h) M)
      (C-rename-id-≡ (cong-ren-id-≐ʳ ([] ∷ _) h) N)
  C-rename-id-≡ h (perform op V M) =
    cong₂ (perform _) (V-rename-id-≡ h V)
              (C-rename-id-≡ (cong-ren-id-≐ʳ (_ ⟨ _ ⟩ ∷ _) h) M)
  C-rename-id-≡ h (delay τ M) =
    cong (delay _) (C-rename-id-≡ (cong-ren-id-≐ʳ ([] ⟨ _ ⟩) h) M)
  C-rename-id-≡ h (handle M `with V) =
    cong₂ handle_`with_ (C-rename-id-≡ h M) (V-rename-id-≡ h V)
  C-rename-id-≡ h (unbox x rel p M) =
    unbox-≡ (rvar-≡ (at h x)) (C-rename-id-≡ (cong-ren-id-≐ʳ ([] ∷ _) h) M)
  C-rename-id-≡ h (box _ V M) =
    cong₂ (box _) (V-rename-id-≡ (cong-ren-id-≐ʳ ([] ⟨ _ ⟩) h) V)
          (C-rename-id-≡ (cong-ren-id-≐ʳ ([] ∷ _) h) M)
  C-rename-id-≡ h (subC M p) = subC-≡ (C-rename-id-≡ h M)

eq-ren-≐ʳ : ∀ {Γ Γ'} → (e e' : Γ ≡ Γ') → eq-ren e ≐ʳ eq-ren e'
eq-ren-≐ʳ e e' rewrite uip {p = e} {q = e'} = ≐ʳ-refl

-- Renaming along an identity-like renaming between contexts that are only
-- propositionally equal: the action is the transport. `eq-ren refl` is
-- `id-ren`, so this is `C-rename-id-≡` once the equality is matched.

C-rename-eq-≡ : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → {r : Ren [] Γ' Γ}
              → r ≐ʳ eq-ren e → (M : Γ ⊢C⦂ C)
              → C-rename r M ≡ subst (_⊢C⦂ C) e M
C-rename-eq-≡ refl h M = C-rename-id-≡ h M

-- Extending such a renaming by a suffix stays identity-like.

cong-ren-eq-ren-≐ʳ : ∀ {Γ Γ'} → (Δ : Ctx) → (e : Γ ≡ Γ')
                  → cong-ren {Γ'' = Δ} (eq-ren e)
                  ≐ʳ eq-ren (cong (_++ᶜ Δ) e)
cong-ren-eq-ren-≐ʳ Δ refl = cong-ren-id-≐ʳ Δ ≐ʳ-refl

-- `eq-ren` commutes with the suffix formers. (`cong-ren` at nested suffixes is
-- not `cong-ren` at their concatenation: the contexts differ by `++ᶜ-assoc`,
-- so any such step has to be conjugated by `eq-ren`s.)

eq-ren-∷-≐ʳ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ')
           → eq-ren (cong (_∷ A) e) ≐ʳ cong-∷-ren {A = A} (eq-ren e)
eq-ren-∷-≐ʳ refl = ≐ʳ-sym (cong-∷-ren-id-≐ʳ ≐ʳ-refl)

eq-ren-⟨⟩-≐ʳ : ∀ {Γ Γ' ρ} → (e : Γ ≡ Γ')
            → eq-ren (cong (_⟨ ρ ⟩) e) ≐ʳ cong-⟨⟩-ren {ρ = ρ} (eq-ren e)
eq-ren-⟨⟩-≐ʳ refl = ≐ʳ-sym (cong-⟨⟩-ren-id-≐ʳ ≐ʳ-refl)

-- A context splitting is determined by its two halves, which identifies the
-- two ways `sub-wk`'s `handle` case reaches the substituted variable,
-- `split-++ʳ s D` and `split-≡-++ᶜ`, without computing either.

split-unique : ∀ {Γ Γ₁ Γ₂} → (s s' : Γ₁ , Γ₂ split Γ) → s ≡ s'
split-unique split-[]     split-[]      = refl
split-unique (split-∷ s)  (split-∷ s')  = cong split-∷ (split-unique s s')
split-unique (split-⟨⟩ s) (split-⟨⟩ s') = cong split-⟨⟩ (split-unique s s')

-- `cong-ren` at nested suffixes is `cong-ren` at their concatenation, but only
-- up to `++ᶜ-assoc`, so conjugated by `eq-ren`s.

cong-ren-assoc-≐ʳ : ∀ {Γ Γ'} → (Θ D : Ctx) → (r : Ren [] Γ' Γ)
                 → cong-ren {Γ'' = D} (cong-ren {Γ'' = Θ} r)
                 ≐ʳ (eq-ren (++ᶜ-assoc Γ Θ D)
                     ∘ʳ cong-ren {Γ'' = Θ ++ᶜ D} r
                     ∘ʳ eq-ren (sym (++ᶜ-assoc Γ' Θ D)))

cong-ren-assoc-≐ʳ Θ [] r =
  ≐ʳ-sym (≐ʳ-trans (∘ʳ-identityˡ-≐ʳ _) (∘ʳ-identityʳ-≐ʳ _))

cong-ren-assoc-≐ʳ {Γ} {Γ'} Θ (D ∷ A) r =
  ≐ʳ-trans (cong-∷-ren-≐ʳ (cong-ren-assoc-≐ʳ Θ D r))
    (≐ʳ-trans (cong-∷-ren-∘-≐ʳ _ _)
      (≐ʳ-trans (∘ʳ-≐ʳ (≐ʳ-trans (≐ʳ-sym (eq-ren-∷-≐ʳ (++ᶜ-assoc Γ Θ D)))
                                (eq-ren-≐ʳ _ _))
                      (cong-∷-ren-∘-≐ʳ _ _))
                (∘ʳ-≐ʳ ≐ʳ-refl
                      (∘ʳ-≐ʳ ≐ʳ-refl
                            (≐ʳ-trans (≐ʳ-sym (eq-ren-∷-≐ʳ (sym (++ᶜ-assoc Γ' Θ D))))
                                      (eq-ren-≐ʳ _ _))))))

cong-ren-assoc-≐ʳ {Γ} {Γ'} Θ (D ⟨ ρ ⟩) r =
  ≐ʳ-trans (cong-⟨⟩-ren-≐ʳ (cong-ren-assoc-≐ʳ Θ D r))
    (≐ʳ-trans (cong-⟨⟩-ren-∘-≐ʳ _ _)
      (≐ʳ-trans (∘ʳ-≐ʳ (≐ʳ-trans (≐ʳ-sym (eq-ren-⟨⟩-≐ʳ (++ᶜ-assoc Γ Θ D)))
                                (eq-ren-≐ʳ _ _))
                      (cong-⟨⟩-ren-∘-≐ʳ _ _))
                (∘ʳ-≐ʳ ≐ʳ-refl
                      (∘ʳ-≐ʳ ≐ʳ-refl
                            (≐ʳ-trans (≐ʳ-sym (eq-ren-⟨⟩-≐ʳ (sym (++ᶜ-assoc Γ' Θ D))))
                                      (eq-ren-≐ʳ _ _))))))

-- Composing two `eq-ren`s.

eq-ren-∘-≐ʳ : ∀ {Γ Γ' Γ''} → (e : Γ ≡ Γ') → (e' : Γ' ≡ Γ'')
           → (eq-ren e ∘ʳ eq-ren e') ≐ʳ eq-ren (trans e e')
eq-ren-∘-≐ʳ refl refl = ∘ʳ-identityˡ-≐ʳ _

-- The renaming action is functorial: renaming along a composite equals
-- renaming along each factor in turn.

mutual

  V-rename-∘ : ∀ {Γ Γ' Γ'' A} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
             → (V : Γ'' ⊢V⦂ A)
             → V-rename (r₂ ∘ʳ r₁) V ≡ V-rename r₁ (V-rename r₂ V)

  V-rename-∘ r₂ r₁ (var f x) with var-rename r₂ x
  ... | _ , _ , y with var-rename r₁ y
  ...   | _ , _ , z = var-≡
  V-rename-∘ r₂ r₁ (const B c) = refl
  V-rename-∘ r₂ r₁ ⋆         = refl
  V-rename-∘ r₂ r₁ true      = refl
  V-rename-∘ r₂ r₁ false     = refl
  V-rename-∘ r₂ r₁ zero      = refl
  V-rename-∘ r₂ r₁ (succ V)  = cong succ (V-rename-∘ r₂ r₁ V)
  V-rename-∘ r₂ r₁ ⦉ V , W ⦊  = cong₂ ⦉_,_⦊ (V-rename-∘ r₂ r₁ V) (V-rename-∘ r₂ r₁ W)
  V-rename-∘ r₂ r₁ (inl V)   = cong inl (V-rename-∘ r₂ r₁ V)
  V-rename-∘ r₂ r₁ (inr V)   = cong inr (V-rename-∘ r₂ r₁ V)
  V-rename-∘ r₂ r₁ nil       = refl
  V-rename-∘ r₂ r₁ (cons V W) = cong₂ cons (V-rename-∘ r₂ r₁ V) (V-rename-∘ r₂ r₁ W)
  V-rename-∘ r₂ r₁ (fun M)   =
    cong fun (trans (C-rename-≡ (cong-ren-∘-≐ʳ ([] ∷ _) r₂ r₁) M)
                    (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  V-rename-∘ r₂ r₁ (handler N H) =
    handler-≡ (trans (C-rename-≡ (cong-ren-∘-≐ʳ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) N)
                     (C-rename-∘ (cong-ren r₂) (cong-ren r₁) N))
      (λ op ε'' →
         trans
           (C-rename-≡ (cong-ren-∘-≐ʳ (_ ⟨ _ ⟩ ∷ _ ∷ _) r₂ r₁) (H op ε''))
           (C-rename-∘ (cong-∷-ren (cong-∷-ren (cong-⟨⟩-ren r₂)))
                       (cong-∷-ren (cong-∷-ren (cong-⟨⟩-ren r₁)))
                       (H op ε'')))
  V-rename-∘ r₂ r₁ (subV V p) = subV-≡ (V-rename-∘ r₂ r₁ V)

  C-rename-∘ : ∀ {Γ Γ' Γ'' C} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
             → (M : Γ'' ⊢C⦂ C)
             → C-rename (r₂ ∘ʳ r₁) M ≡ C-rename r₁ (C-rename r₂ M)

  C-rename-∘ r₂ r₁ (return V) = cong return (V-rename-∘ r₂ r₁ V)
  C-rename-∘ r₂ r₁ (M ⨟ N) =
    cong₂ _⨟_ (C-rename-∘ r₂ r₁ M)
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) N)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) N))
  C-rename-∘ r₂ r₁ (V · W) = cong₂ _·_ (V-rename-∘ r₂ r₁ V) (V-rename-∘ r₂ r₁ W)
  C-rename-∘ r₂ r₁ (match V `with M) =
    cong₂ match_`with_ (V-rename-∘ r₂ r₁ V)
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ ([] ∷ _ ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (absurd V) = cong absurd (V-rename-∘ r₂ r₁ V)
  C-rename-∘ r₂ r₁ (cmp ⋈ V W et) =
    cong₂ (λ a b → cmp ⋈ a b et) (V-rename-∘ r₂ r₁ V) (V-rename-∘ r₂ r₁ W)
  C-rename-∘ r₂ r₁ (if V `then M `else N) =
    cong₃ if_`then_`else_
      (V-rename-∘ r₂ r₁ V) (C-rename-∘ r₂ r₁ M) (C-rename-∘ r₂ r₁ N)
  C-rename-∘ r₂ r₁ (matchℕ V `zero M `succ N) =
    cong₃ matchℕ_`zero_`succ_ (V-rename-∘ r₂ r₁ V) (C-rename-∘ r₂ r₁ M)
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ ([] ∷ _) r₂ r₁) N)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) N))
  C-rename-∘ r₂ r₁ (recℕ V M N p) =
    cong₃ (λ a b c → recℕ a b c p) (V-rename-∘ r₂ r₁ V) (C-rename-∘ r₂ r₁ M)
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ (([] ⟨ _ ⟩ ∷ nat) ⟨ _ ⟩ ∷ _) r₂ r₁) N)
             (C-rename-∘ (cong-ren {Γ'' = (([] ⟨ _ ⟩ ∷ nat) ⟨ _ ⟩ ∷ _)} r₂) (cong-ren {Γ'' = (([] ⟨ _ ⟩ ∷ nat) ⟨ _ ⟩ ∷ _)} r₁) N))
  C-rename-∘ r₂ r₁ (matchL V `nil M `cons N) =
    cong₃ matchL_`nil_`cons_ (V-rename-∘ r₂ r₁ V) (C-rename-∘ r₂ r₁ M)
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ ([] ∷ _ ∷ _) r₂ r₁) N)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) N))
  C-rename-∘ r₂ r₁ (recL V M N p) =
    cong₃ (λ a b c → recL a b c p) (V-rename-∘ r₂ r₁ V) (C-rename-∘ r₂ r₁ M)
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ (([] ⟨ _ ⟩ ∷ _ ∷ list _) ⟨ _ ⟩ ∷ _) r₂ r₁) N)
             (C-rename-∘ (cong-ren {Γ'' = (([] ⟨ _ ⟩ ∷ _ ∷ list _) ⟨ _ ⟩ ∷ _)} r₂) (cong-ren {Γ'' = (([] ⟨ _ ⟩ ∷ _ ∷ list _) ⟨ _ ⟩ ∷ _)} r₁) N))
  C-rename-∘ r₂ r₁ (match+ V `inl M `inr N) =
    cong₃ match+_`inl_`inr_ (V-rename-∘ r₂ r₁ V)
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ ([] ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ ([] ∷ _) r₂ r₁) N)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) N))
  C-rename-∘ r₂ r₁ (perform op V M) =
    cong₂ (perform _) (V-rename-∘ r₂ r₁ V)
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (delay τ M) =
    cong (delay _) (trans (C-rename-≡ (cong-ren-∘-≐ʳ ([] ⟨ _ ⟩) r₂ r₁) M)
                      (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (handle M `with V) =
    cong₂ handle_`with_ (C-rename-∘ r₂ r₁ M) (V-rename-∘ r₂ r₁ V)
  C-rename-∘ r₂ r₁ (unbox x rel p M) with var-rename r₂ x
  ... | _ , _ , y with var-rename r₁ y
  ...   | _ , _ , z =
    unbox-≡ refl
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ ([] ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (box _ V M) =
    cong₂ (box _) (trans (V-rename-≡ (cong-ren-∘-≐ʳ ([] ⟨ _ ⟩) r₂ r₁) V)
                    (V-rename-∘ (cong-ren r₂) (cong-ren r₁) V))
          (trans (C-rename-≡ (cong-ren-∘-≐ʳ ([] ∷ _) r₂ r₁) M)
                    (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (subC M p) = subC-≡ (C-rename-∘ r₂ r₁ M)

-- Renaming related terms gives related terms.

V-rename-cong : ∀ {Γ Γ' A} → (r : Ren [] Γ Γ') → {V V' : Γ' ⊢V⦂ A}
              → V ≡ V' → V-rename r V ≡ V-rename r V'
V-rename-cong r = cong (V-rename r)

C-rename-cong : ∀ {Γ Γ' C} → (r : Ren [] Γ Γ') → {M M' : Γ' ⊢C⦂ C}
              → M ≡ M' → C-rename r M ≡ C-rename r M'
C-rename-cong r = cong (C-rename r)
