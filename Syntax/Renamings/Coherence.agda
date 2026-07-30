------------------------------------------------------------------------
-- Coherence of the renaming action.                                  --
--                                                                    --
-- The action is functorial and a congruence. The premises are stated  --
-- at `_≐ʳ_`, since `Ren` is freely generated and `cong-ren` commutes   --
-- with `_∘ʳ_` only up to it; the conclusions are equalities of terms.  --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Renamings.Coherence (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   Spec
open import Syntax.Language   Spec
open import Syntax.RenActions Spec
open import Syntax.Renamings  Spec
open import Syntax.Types      Spec
open import Syntax.Renamings.Equivalence Spec
open import Syntax.Terms.Equivalence     Spec


-- Renaming a variable is the variable the renaming sends it to: `var-img`
-- records the position, and the grade bound it recomputes is invisible to
-- `_≡_`. Stated at an arbitrary bound so that the caller may present the
-- result with whichever bound its own typing supplies.

var-ren-≡ : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ' Γ) → (x : A ∈[ ρ ] Γ)
          → (f  : ¬ Eternal A → ρ ≾ᵣ uᵣ)
          → (f' : ¬ Eternal A → proj₁ (var-img r x) ≾ᵣ uᵣ)
          → V-rename r (var f x) ≡ var f' (proj₂ (var-img r x))
var-ren-≡ r x f f' with var-rename r x
... | _ , _ , y = var-≡

-- The same with the target supplied, for callers that have computed it.

var-ren-img-≡ : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ' Γ) → (x : A ∈[ ρ ] Γ)
              → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → {t : Var Γ' A}
              → var-img r x ≡ t → (f' : ¬ Eternal A → proj₁ t ≾ᵣ uᵣ)
              → V-rename r (var f x) ≡ var f' (proj₂ t)
var-ren-img-≡ r x f refl f' = var-ren-≡ r x f f'

------------------------------------------------------------------------
-- THE ACTION RESPECTS ACTING ALIKE
--
-- Induction on the term. At `var` and `unbox` the whole content is the
-- hypothesis, the grade bounds being irrelevant; the binding formers use
-- `cong-ren-≐ʳ` and `handle` uses `restrict-ren-≐ʳ`.
------------------------------------------------------------------------

mutual

  V-rename-≡ : ∀ {Γ Γ' A} {r r' : Ren [] Γ Γ'} → r ≐ʳ r'
             → (V : Γ' ⊢V⦂ A) → V-rename r V ≡ V-rename r' V

  V-rename-≡ {r = r} {r' = r'} h (var f x)
    with var-rename r x | var-rename r' x | at h x
  ... | _ | _ | refl = var-≡
  V-rename-≡ h (const c)  = refl
  V-rename-≡ h ⋆          = refl
  V-rename-≡ h ⦉ V , W ⦊   = cong₂ ⦉_,_⦊ (V-rename-≡ h V) (V-rename-≡ h W)
  V-rename-≡ h (lam M)    = cong lam (C-rename-≡ (cong-ren-≐ʳ ([] ∷ _) h) M)

  C-rename-≡ : ∀ {Γ Γ' C} {r r' : Ren [] Γ Γ'} → r ≐ʳ r'
             → (M : Γ' ⊢C⦂ C) → C-rename r M ≡ C-rename r' M

  C-rename-≡ h (return V) = cong return (V-rename-≡ h V)
  C-rename-≡ h (M ⨟ N) =
    cong₂ _⨟_ (C-rename-≡ h M) (C-rename-≡ (cong-ren-≐ʳ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-≡ h (V · W) = cong₂ _·_ (V-rename-≡ h V) (V-rename-≡ h W)
  C-rename-≡ h (match V `in M) =
    cong₂ match_`in_ (V-rename-≡ h V) (C-rename-≡ (cong-ren-≐ʳ ([] ∷ _ ∷ _) h) M)
  C-rename-≡ h (absurd V) = cong absurd (V-rename-≡ h V)
  C-rename-≡ h (perform op V M) =
    cong₂ (perform _) (V-rename-≡ h V) (C-rename-≡ (cong-ren-≐ʳ (_ ⟨ _ ⟩ ∷ _) h) M)
  C-rename-≡ h (delay τ M) =
    cong (delay _) (C-rename-≡ (cong-ren-≐ʳ ([] ⟨ _ ⟩) h) M)
  C-rename-≡ h (handle M `with H `in N) =
    handle-≡ (C-rename-≡ h M)
      (λ op ε'' →
         C-rename-≡ (cong-∷-ren-≐ʳ (cong-∷-ren-≐ʳ (restrict-ren-≐ʳ h))) (H op ε''))
      (C-rename-≡ (cong-ren-≐ʳ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-≡ h (unbox x rel M) =
    unbox-≡ (at h x) (C-rename-≡ (cong-ren-≐ʳ ([] ∷ _) h) M)
  C-rename-≡ h (box V M) =
    cong₂ box (V-rename-≡ (cong-ren-≐ʳ ([] ⟨ _ ⟩) h) V)
          (C-rename-≡ (cong-ren-≐ʳ ([] ∷ _) h) M)
  C-rename-≡ h (coerce p M) = coerce-≡ (C-rename-≡ h M)

------------------------------------------------------------------------
-- RENAMING ALONG AN IDENTITY-LIKE RENAMING
--
-- `cong-∷-ren id-ren`, `⟨⟩-≤-ren` at equal grades and `⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-η-ren`
-- all act as the identity without being it, so the action is the identity only
-- up to the equivalence. Induction on the term, as for `C-rename-≡`.
------------------------------------------------------------------------

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

∘ʳ-idʳ-≐ʳ : ∀ {Γ Γ'} {r : Ren [] Γ Γ} → (w : Ren [] Γ Γ')
         → r ≐ʳ id-ren → (w ∘ʳ r) ≐ʳ w
∘ʳ-idʳ-≐ʳ w h = mk≐ʳ (λ x → at h (proj₂ (var-img w x)))

restrict-ren-id-≐ʳ : ∀ {Γ} {r : Ren [] Γ Γ} → r ≐ʳ id-ren → restrict-ren r ≐ʳ id-ren
restrict-ren-id-≐ʳ h = restrict-ren-≐ʳ h

mutual

  V-rename-id-≡ : ∀ {Γ A} {r : Ren [] Γ Γ} → r ≐ʳ id-ren
                → (V : Γ ⊢V⦂ A) → V-rename r V ≡ V

  V-rename-id-≡ {r = r} h (var f x) with var-rename r x | at h x
  ... | _ | refl = var-≡
  V-rename-id-≡ h (const c) = refl
  V-rename-id-≡ h ⋆         = refl
  V-rename-id-≡ h ⦉ V , W ⦊  = cong₂ ⦉_,_⦊ (V-rename-id-≡ h V) (V-rename-id-≡ h W)
  V-rename-id-≡ h (lam M)   = cong lam (C-rename-id-≡ (cong-ren-id-≐ʳ ([] ∷ _) h) M)

  C-rename-id-≡ : ∀ {Γ C} {r : Ren [] Γ Γ} → r ≐ʳ id-ren
                → (M : Γ ⊢C⦂ C) → C-rename r M ≡ M

  C-rename-id-≡ h (return V) = cong return (V-rename-id-≡ h V)
  C-rename-id-≡ h (M ⨟ N) =
    cong₂ _⨟_ (C-rename-id-≡ h M) (C-rename-id-≡ (cong-ren-id-≐ʳ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-id-≡ h (V · W) = cong₂ _·_ (V-rename-id-≡ h V) (V-rename-id-≡ h W)
  C-rename-id-≡ h (match V `in M) =
    cong₂ match_`in_ (V-rename-id-≡ h V) (C-rename-id-≡ (cong-ren-id-≐ʳ ([] ∷ _ ∷ _) h) M)
  C-rename-id-≡ h (absurd V) = cong absurd (V-rename-id-≡ h V)
  C-rename-id-≡ h (perform op V M) =
    cong₂ (perform _) (V-rename-id-≡ h V)
              (C-rename-id-≡ (cong-ren-id-≐ʳ (_ ⟨ _ ⟩ ∷ _) h) M)
  C-rename-id-≡ h (delay τ M) =
    cong (delay _) (C-rename-id-≡ (cong-ren-id-≐ʳ ([] ⟨ _ ⟩) h) M)
  C-rename-id-≡ h (handle M `with H `in N) =
    handle-≡ (C-rename-id-≡ h M)
      (λ op ε'' →
         C-rename-id-≡ (cong-∷-ren-id-≐ʳ (cong-∷-ren-id-≐ʳ (restrict-ren-id-≐ʳ h)))
                       (H op ε''))
      (C-rename-id-≡ (cong-ren-id-≐ʳ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-id-≡ h (unbox x rel M) =
    unbox-≡ (at h x) (C-rename-id-≡ (cong-ren-id-≐ʳ ([] ∷ _) h) M)
  C-rename-id-≡ h (box V M) =
    cong₂ box (V-rename-id-≡ (cong-ren-id-≐ʳ ([] ⟨ _ ⟩) h) V)
          (C-rename-id-≡ (cong-ren-id-≐ʳ ([] ∷ _) h) M)
  C-rename-id-≡ h (coerce p M) = coerce-≡ (C-rename-id-≡ h M)

eq-ren-≐ʳ : ∀ {Γ Γ'} → (e e' : Γ ≡ Γ') → eq-ren e ≐ʳ eq-ren e'
eq-ren-≐ʳ e e' rewrite uip {p = e} {q = e'} = ≐ʳ-refl

-- Renaming along an identity-*like* renaming between contexts that are only
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

-- `eq-ren` commutes with the suffix formers. (Note `cong-ren` at nested suffixes
-- is *not* `cong-ren` at their concatenation: the contexts differ by
-- `++ᶜ-assoc`, so any such step has to be conjugated by `eq-ren`s.)

eq-ren-∷-≐ʳ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ')
           → eq-ren (cong (_∷ A) e) ≐ʳ cong-∷-ren {A = A} (eq-ren e)
eq-ren-∷-≐ʳ refl = ≐ʳ-sym (cong-∷-ren-id-≐ʳ ≐ʳ-refl)

eq-ren-⟨⟩-≐ʳ : ∀ {Γ Γ' ρ} → (e : Γ ≡ Γ')
            → eq-ren (cong (_⟨ ρ ⟩) e) ≐ʳ cong-⟨⟩-ren {ρ = ρ} (eq-ren e)
eq-ren-⟨⟩-≐ʳ refl = ≐ʳ-sym (cong-⟨⟩-ren-id-≐ʳ ≐ʳ-refl)

-- A context splitting is determined by its two halves: `_,_split_` recurses on
-- the right half, so its constructor is forced at each step. This is what
-- identifies the two ways `sub-wk`'s `handle` case reaches the substituted
-- variable — `split-++ʳ (∈-ᴱ-split et z₀) D` and `split-≡-++ᶜ` — without
-- computing either. (Pure `Syntax.Contexts` material; see the cleanup list.)

split-unique : ∀ {Γ Γ₁ Γ₂} → (s s' : Γ₁ , Γ₂ split Γ) → s ≡ s'
split-unique split-[]     split-[]      = refl
split-unique (split-∷ s)  (split-∷ s')  = cong split-∷ (split-unique s s')
split-unique (split-⟨⟩ s) (split-⟨⟩ s') = cong split-⟨⟩ (split-unique s s')

-- Hence the variables they name agree, once the two contexts are identified.

split→∈-subst : ∀ {Γ Γ' Γ₁ Γ₂ A} → (e : Γ ≡ Γ')
              → (s : Γ₁ ∷ A , Γ₂ split Γ)
              → split→∈ (subst (λ Γ₀ → Γ₁ ∷ A , Γ₂ split Γ₀) e s)
              ≡ subst (λ Γ₀ → A ∈[ ctx-grade Γ₂ ] Γ₀) e (split→∈ s)
split→∈-subst refl s = refl

split→∈-unique : ∀ {Γ Γ' Γ₁ Γ₂ A} → (e : Γ ≡ Γ')
               → (s : Γ₁ ∷ A , Γ₂ split Γ) → (s' : Γ₁ ∷ A , Γ₂ split Γ')
               → subst (λ Γ₀ → A ∈[ ctx-grade Γ₂ ] Γ₀) e (split→∈ s)
               ≡ split→∈ s'
split→∈-unique e s s' =
  trans (sym (split→∈-subst e s))
        (cong split→∈ (split-unique (subst (λ Γ₀ → _ , _ split Γ₀) e s) s'))

-- `cong-ren` at nested suffixes is `cong-ren` at their concatenation — but only
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

-- THE ETERNAL RESTRICTION AGAINST A SUFFIX
--
-- `restrict-ren (cong-ren {Δ} r)` is `cong-ren {Δ ᴱ} (restrict-ren r)`,
-- conjugated by `eq-ren`s at `ᴱ`'s distribution over `_++ᶜ_`. This is the
-- functor `_ᴱ` commuting with the action of contexts on each fibre; the two
-- weakening cases below are its instances at `r := wk-ren`.

restrict-cong-≐ʳ : ∀ {Γ Γ'} → (r : Ren [] Γ' Γ) → (Δ : Ctx)
                → (e₁ : (Γ ++ᶜ Δ) ᴱ ≡ Γ ᴱ ++ᶜ Δ ᴱ)
                → (e₂ : (Γ' ++ᶜ Δ) ᴱ ≡ Γ' ᴱ ++ᶜ Δ ᴱ)
                → restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} r)
                ≐ʳ (eq-ren e₁
                    ∘ʳ cong-ren {Γ'' = Δ ᴱ} (restrict-ren r) ∘ʳ eq-ren (sym e₂))

restrict-cong-≐ʳ r [] e₁ e₂
  rewrite uip {p = e₁} {q = refl} | uip {p = e₂} {q = refl} =
  ≐ʳ-sym (≐ʳ-trans (∘ʳ-identityˡ-≐ʳ _) (∘ʳ-identityʳ-≐ʳ _))

restrict-cong-≐ʳ r (Δ ∷ C) e₁ e₂ with eternal? C

... | yes _ =
  ≐ʳ-trans (cong-∷-ren-≐ʳ (restrict-cong-≐ʳ r Δ (∷ᶜ-injective-ctx e₁)
                                              (∷ᶜ-injective-ctx e₂)))
    (≐ʳ-trans (cong-∷-ren-∘-≐ʳ _ _)
      (≐ʳ-trans (∘ʳ-≐ʳ (≐ʳ-sym (eq-ren-∷-≐ʳ (∷ᶜ-injective-ctx e₁)))
                      (cong-∷-ren-∘-≐ʳ _ _))
        (≐ʳ-trans (∘ʳ-≐ʳ (eq-ren-≐ʳ _ e₁)
                        (∘ʳ-≐ʳ ≐ʳ-refl
                              (≐ʳ-sym (eq-ren-∷-≐ʳ (sym (∷ᶜ-injective-ctx e₂))))))
                  (∘ʳ-≐ʳ ≐ʳ-refl (∘ʳ-≐ʳ ≐ʳ-refl (eq-ren-≐ʳ _ (sym e₂)))))))

... | no  _ = restrict-cong-≐ʳ r Δ e₁ e₂

restrict-cong-≐ʳ r (Δ ⟨ ρ ⟩) e₁ e₂ = restrict-cong-≐ʳ r Δ e₁ e₂

-- With an *eternal* `B`, weakening by `B` weakens the eternal restriction by it
-- too: `restrict-ren` walks down to `restrict-ren wk-ren`, which at an eternal
-- type is `wk-ren`. The two contexts differ by `ᴱ`'s distribution over `_++ᶜ_`,
-- so the statement is conjugated by `eq-ren`s at arbitrary proofs of that.
--
-- This and `restrict-wk-≐ʳ` below are `restrict-cong-≐ʳ` at `r := wk-ren`, and
-- their `∷`/`⟨⟩` cases repeat its proof. They are kept all the same: the
-- general law phrases the target as `(Γ ∷ B) ᴱ`, these as the already-reduced
-- `Γ ᴱ ∷ B`, and that reduction needs `eternal? B` decided. Absorbing it here,
-- once, is what lets the four call sites state their equalities in reduced
-- form; deriving them instead would leave each caller transporting a *renaming*
-- along `ᴱ-∷-keep`, which costs more than the repeated induction saves.

restrict-wk-et-≐ʳ : ∀ {Γ B} → (et : Eternal B) → (Δ : Ctx)
                 → (e₁ : (Γ ++ᶜ Δ) ᴱ ≡ Γ ᴱ ++ᶜ Δ ᴱ)
                 → (e₂ : ((Γ ∷ B) ++ᶜ Δ) ᴱ ≡ (Γ ᴱ ∷ B) ++ᶜ Δ ᴱ)
                 → restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (wk-ren {A = B}))
                 ≐ʳ (eq-ren e₁
                     ∘ʳ cong-ren {Γ'' = Δ ᴱ} (wk-ren {A = B}) ∘ʳ eq-ren (sym e₂))

restrict-wk-et-≐ʳ {Γ} {B} et [] e₁ e₂
  rewrite eternal?-yes et
        | uip {p = e₁} {q = refl} | uip {p = e₂} {q = refl} =
  ≐ʳ-sym (≐ʳ-trans (∘ʳ-identityˡ-≐ʳ _) (∘ʳ-identityʳ-≐ʳ _))

restrict-wk-et-≐ʳ {Γ} {B} et (Δ ∷ C) e₁ e₂ with eternal? C

... | yes _ =
  ≐ʳ-trans (cong-∷-ren-≐ʳ (restrict-wk-et-≐ʳ et Δ (∷ᶜ-injective-ctx e₁)
                                              (∷ᶜ-injective-ctx e₂)))
    (≐ʳ-trans (cong-∷-ren-∘-≐ʳ _ _)
      (≐ʳ-trans (∘ʳ-≐ʳ (≐ʳ-sym (eq-ren-∷-≐ʳ (∷ᶜ-injective-ctx e₁)))
                      (cong-∷-ren-∘-≐ʳ _ _))
        (≐ʳ-trans (∘ʳ-≐ʳ (eq-ren-≐ʳ _ e₁)
                        (∘ʳ-≐ʳ ≐ʳ-refl
                              (≐ʳ-sym (eq-ren-∷-≐ʳ (sym (∷ᶜ-injective-ctx e₂))))))
                  (∘ʳ-≐ʳ ≐ʳ-refl (∘ʳ-≐ʳ ≐ʳ-refl (eq-ren-≐ʳ _ (sym e₂)))))))

... | no  _ = restrict-wk-et-≐ʳ et Δ e₁ e₂

restrict-wk-et-≐ʳ {Γ} {B} et (Δ ⟨ ρ ⟩) e₁ e₂ = restrict-wk-et-≐ʳ et Δ e₁ e₂

-- The form `sub-wk`'s eternal `handle` clause needs: the clause's renaming
-- `cong-ren {D} (restrict-ren (cong-ren {Θ} wk-ren))` is `cong-ren` at the
-- concatenated suffix `Θ ᴱ ++ᶜ D`, conjugated by `eq-ren`s. Assembled from
-- `restrict-wk-et-≐ʳ`, `cong-ren-∘-≐ʳ`, `cong-ren-eq-ren-≐ʳ` and
-- `cong-ren-assoc-≐ʳ`, with the `eq-ren`s fused by `eq-ren-∘-≐ʳ` and any two
-- proofs identified by `eq-ren-≐ʳ`.

restrict-wk-clause-≐ʳ : ∀ {Γ B} → (et : Eternal B) → (Θ D : Ctx)
                     → (e₁ : (Γ ++ᶜ Θ) ᴱ ≡ Γ ᴱ ++ᶜ Θ ᴱ)
                     → (e₂ : ((Γ ∷ B) ++ᶜ Θ) ᴱ ≡ (Γ ᴱ ∷ B) ++ᶜ Θ ᴱ)
                     → cong-ren {Γ'' = D}
                         (restrict-ren {Ξ = []} (cong-ren {Γ'' = Θ} (wk-ren {A = B})))
                     ≐ʳ (eq-ren (cong (_++ᶜ D) e₁)
                         ∘ʳ (eq-ren (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) D)
                             ∘ʳ cong-ren {Γ'' = Θ ᴱ ++ᶜ D} (wk-ren {A = B})
                             ∘ʳ eq-ren (sym (++ᶜ-assoc (Γ ᴱ ∷ B) (Θ ᴱ) D)))
                         ∘ʳ eq-ren (cong (_++ᶜ D) (sym e₂)))

restrict-wk-clause-≐ʳ {Γ} {B} et Θ D e₁ e₂ =
  ≐ʳ-trans (cong-ren-≐ʳ D (restrict-wk-et-≐ʳ et Θ e₁ e₂))
    (≐ʳ-trans (cong-ren-∘-≐ʳ D _ _)
      (∘ʳ-≐ʳ (cong-ren-eq-ren-≐ʳ D e₁)
        (≐ʳ-trans (cong-ren-∘-≐ʳ D _ _)
                  (∘ʳ-≐ʳ (cong-ren-assoc-≐ʳ (Θ ᴱ) D (wk-ren {A = B}))
                        (cong-ren-eq-ren-≐ʳ D (sym e₂))))))

-- With a non-eternal `B`, weakening by `B` leaves the eternal restriction
-- alone: `restrict-ren` walks `cong-ren` down to `restrict-ren wk-ren`, which at
-- a non-eternal type is `id-ren`. The two contexts are then equal only
-- propositionally, so the statement is against an arbitrary proof of that
-- equality — any two agree by `uip`.

restrict-wk-≐ʳ : ∀ {Γ B} → (¬et : ¬ Eternal B) → (Δ : Ctx)
              → (e : (Γ ++ᶜ Δ) ᴱ ≡ ((Γ ∷ B) ++ᶜ Δ) ᴱ)
              → restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (wk-ren {A = B})) ≐ʳ eq-ren e

restrict-wk-≐ʳ {Γ} {B} ¬et [] e
  rewrite eternal?-no ¬et | uip {p = e} {q = refl} = ≐ʳ-refl

restrict-wk-≐ʳ {Γ} {B} ¬et (Δ ∷ C) e with eternal? C
... | yes _ =
  ≐ʳ-trans (cong-∷-ren-≐ʳ (restrict-wk-≐ʳ ¬et Δ (∷ᶜ-injective-ctx e)))
    (≐ʳ-trans (cong-ren-eq-ren-≐ʳ ([] ∷ C) (∷ᶜ-injective-ctx e))
              (eq-ren-≐ʳ _ e))
... | no  _ = restrict-wk-≐ʳ ¬et Δ e

restrict-wk-≐ʳ {Γ} {B} ¬et (Δ ⟨ ρ ⟩) e = restrict-wk-≐ʳ ¬et Δ e

------------------------------------------------------------------------
-- FUNCTORIALITY
--
-- At the binding formers the two sides rename along `cong-ren (r₂ ∘ʳ r₁)` and
-- `cong-ren r₂ ∘ʳ cong-ren r₁`: distinct renamings acting alike, so the proof
-- leans on the laws above. At `var` and `unbox` both sides locate the variable
-- with `r₂` and then with `r₁`, which is what `var-rename` of a composite does,
-- so abstracting the two lookups makes the clause `refl` up to irrelevance.
------------------------------------------------------------------------

mutual

  V-rename-∘ : ∀ {Γ Γ' Γ'' A} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
             → (V : Γ'' ⊢V⦂ A)
             → V-rename (r₂ ∘ʳ r₁) V ≡ V-rename r₁ (V-rename r₂ V)

  V-rename-∘ r₂ r₁ (var f x) with var-rename r₂ x
  ... | _ , _ , y with var-rename r₁ y
  ...   | _ , _ , z = var-≡
  V-rename-∘ r₂ r₁ (const c) = refl
  V-rename-∘ r₂ r₁ ⋆         = refl
  V-rename-∘ r₂ r₁ ⦉ V , W ⦊  = cong₂ ⦉_,_⦊ (V-rename-∘ r₂ r₁ V) (V-rename-∘ r₂ r₁ W)
  V-rename-∘ r₂ r₁ (lam M)   =
    cong lam (trans (C-rename-≡ (cong-ren-∘-≐ʳ ([] ∷ _) r₂ r₁) M)
                    (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))

  C-rename-∘ : ∀ {Γ Γ' Γ'' C} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
             → (M : Γ'' ⊢C⦂ C)
             → C-rename (r₂ ∘ʳ r₁) M ≡ C-rename r₁ (C-rename r₂ M)

  C-rename-∘ r₂ r₁ (return V) = cong return (V-rename-∘ r₂ r₁ V)
  C-rename-∘ r₂ r₁ (M ⨟ N) =
    cong₂ _⨟_ (C-rename-∘ r₂ r₁ M)
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) N)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) N))
  C-rename-∘ r₂ r₁ (V · W) = cong₂ _·_ (V-rename-∘ r₂ r₁ V) (V-rename-∘ r₂ r₁ W)
  C-rename-∘ r₂ r₁ (match V `in M) =
    cong₂ match_`in_ (V-rename-∘ r₂ r₁ V)
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ ([] ∷ _ ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (absurd V) = cong absurd (V-rename-∘ r₂ r₁ V)
  C-rename-∘ r₂ r₁ (perform op V M) =
    cong₂ (perform _) (V-rename-∘ r₂ r₁ V)
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (delay τ M) =
    cong (delay _) (trans (C-rename-≡ (cong-ren-∘-≐ʳ ([] ⟨ _ ⟩) r₂ r₁) M)
                      (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (handle M `with H `in N) =
    handle-≡ (C-rename-∘ r₂ r₁ M)
      (λ op ε'' →
         trans
           (C-rename-≡
             (≐ʳ-trans (cong-∷-ren-≐ʳ (cong-∷-ren-≐ʳ (restrict-ren-∘-≐ʳ r₂ r₁)))
                       (cong-ren-∘-≐ʳ ([] ∷ _ ∷ _)
                                     (restrict-ren r₂) (restrict-ren r₁)))
             (H op ε''))
           (C-rename-∘ (cong-∷-ren (cong-∷-ren (restrict-ren r₂)))
                       (cong-∷-ren (cong-∷-ren (restrict-ren r₁)))
                       (H op ε'')))
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) N)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) N))
  C-rename-∘ r₂ r₁ (unbox x rel M) with var-rename r₂ x
  ... | _ , _ , y with var-rename r₁ y
  ...   | _ , _ , z =
    unbox-≡ refl
      (trans (C-rename-≡ (cong-ren-∘-≐ʳ ([] ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (box V M) =
    cong₂ box (trans (V-rename-≡ (cong-ren-∘-≐ʳ ([] ⟨ _ ⟩) r₂ r₁) V)
                    (V-rename-∘ (cong-ren r₂) (cong-ren r₁) V))
          (trans (C-rename-≡ (cong-ren-∘-≐ʳ ([] ∷ _) r₂ r₁) M)
                    (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (coerce p M) = coerce-≡ (C-rename-∘ r₂ r₁ M)

------------------------------------------------------------------------
-- THE ACTION IS A CONGRUENCE
--
-- Renaming related terms gives related terms.
------------------------------------------------------------------------

V-rename-cong : ∀ {Γ Γ' A} → (r : Ren [] Γ Γ') → {V V' : Γ' ⊢V⦂ A}
              → V ≡ V' → V-rename r V ≡ V-rename r V'
V-rename-cong r = cong (V-rename r)

C-rename-cong : ∀ {Γ Γ' C} → (r : Ren [] Γ Γ') → {M M' : Γ' ⊢C⦂ C}
              → M ≡ M' → C-rename r M ≡ C-rename r M'
C-rename-cong r = cong (C-rename r)
