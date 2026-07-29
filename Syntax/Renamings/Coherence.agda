------------------------------------------------------------------------
-- Coherence of the renaming action.                                  --
--                                                                    --
-- The action is functorial and a congruence, both only up to          --
-- `_≐ᵛ_`/`_≐ᶜ_`: renaming along `r₂ ∘ʳ r₁` stores that composite in   --
-- every `unbox` node, where renaming twice stores `r₂ ∘ʳ (r₁ ∘ʳ w)`.  --
-- The two are `_≐ʳ_`-equal, never equal.                             --
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


-- Renaming a variable is the variable the renaming sends it to: `var-tgt`
-- records the position, and the grade bound it recomputes is invisible to
-- `_≐ᵛ_`. Stated at an arbitrary bound so that the caller may present the
-- result with whichever bound its own typing supplies.

var-ren-≐ : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → (x : A ∈[ ρ ] Γ)
          → (f  : ¬ Eternal A → ρ ≾ᵣ uᵣ)
          → (f' : ¬ Eternal A → proj₁ (var-tgt r x) ≾ᵣ uᵣ)
          → V-rename r (var f x) ≐ᵛ var f' (proj₂ (var-tgt r x))
var-ren-≐ r x f f' with var-rename r x
... | _ , _ , y = var-≐

-- The same with the target supplied, for callers that have computed it.

var-ren-tgt-≐ : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → (x : A ∈[ ρ ] Γ)
              → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → {t : Tgt Γ' A}
              → var-tgt r x ≡ t → (f' : ¬ Eternal A → proj₁ t ≾ᵣ uᵣ)
              → V-rename r (var f x) ≐ᵛ var f' (proj₂ t)
var-ren-tgt-≐ r x f refl f' = var-ren-≐ r x f f'

------------------------------------------------------------------------
-- THE ACTION RESPECTS ACTING ALIKE
--
-- Induction on the term. At `var` the whole content is the hypothesis, the
-- grade bounds being irrelevant; the binding formers use `cong-ren-≐`, `handle`
-- uses `restrict-ren-≐`, and `unbox` stores `r ∘ʳ w`, related by `∘ʳ-≐`.
------------------------------------------------------------------------

mutual

  V-rename-≐ : ∀ {Γ Γ' A} {r r' : Ren [] Γ Γ'} → r ≐ʳ r'
             → (V : Γ ⊢V⦂ A) → V-rename r V ≐ᵛ V-rename r' V

  V-rename-≐ {r = r} {r' = r'} h (var f x)
    with var-rename r x | var-rename r' x | at h x
  ... | _ | _ | refl = var-≐
  V-rename-≐ h (const c)  = const-≐
  V-rename-≐ h ⋆          = ⋆-≐
  V-rename-≐ h ⦉ V , W ⦊   = pair-≐ (V-rename-≐ h V) (V-rename-≐ h W)
  V-rename-≐ h (lam M)    = lam-≐ (C-rename-≐ (cong-ren-≐ ([] ∷ _) h) M)

  C-rename-≐ : ∀ {Γ Γ' C} {r r' : Ren [] Γ Γ'} → r ≐ʳ r'
             → (M : Γ ⊢C⦂ C) → C-rename r M ≐ᶜ C-rename r' M

  C-rename-≐ h (return V) = return-≐ (V-rename-≐ h V)
  C-rename-≐ h (M ⨟ N) =
    seq-≐ (C-rename-≐ h M) (C-rename-≐ (cong-ren-≐ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-≐ h (V · W) = app-≐ (V-rename-≐ h V) (V-rename-≐ h W)
  C-rename-≐ h (match V `in M) =
    match-≐ (V-rename-≐ h V) (C-rename-≐ (cong-ren-≐ ([] ∷ _ ∷ _) h) M)
  C-rename-≐ h (absurd V) = absurd-≐ (V-rename-≐ h V)
  C-rename-≐ h (perform op V M) =
    perform-≐ (V-rename-≐ h V) (C-rename-≐ (cong-ren-≐ (_ ⟨ _ ⟩ ∷ _) h) M)
  C-rename-≐ h (delay τ M) =
    delay-≐ (C-rename-≐ (cong-ren-≐ ([] ⟨ _ ⟩) h) M)
  C-rename-≐ h (handle M `with H `in N) =
    handle-≐ (C-rename-≐ h M)
      (λ op ε'' →
         C-rename-≐ (cong-∷-ren-≐ (cong-∷-ren-≐ (restrict-ren-≐ h))) (H op ε''))
      (C-rename-≐ (cong-ren-≐ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-≐ h (unbox w V M) =
    unbox-≐ (unbox-tgt-≐ (∘ʳ-≐ h (≐ʳ-refl {r = w})) V)
            (C-rename-≐ (cong-ren-≐ ([] ∷ _) h) M)
  C-rename-≐ h (box V M) =
    box-≐ (V-rename-≐ (cong-ren-≐ ([] ⟨ _ ⟩) h) V)
          (C-rename-≐ (cong-ren-≐ ([] ∷ _) h) M)
  C-rename-≐ h (coerce p M) = coerce-≐ (C-rename-≐ h M)

------------------------------------------------------------------------
-- RENAMING ALONG AN IDENTITY-LIKE RENAMING
--
-- `cong-∷-ren id-ren`, `⟨⟩-≤-ren` at equal grades and `⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-η-ren`
-- all act as the identity without being it, so the action is the identity only
-- up to the equivalence. Induction on the term, as for `C-rename-≐`.
------------------------------------------------------------------------

⟨⟩-≤-ren-id-≐ : ∀ {Γ ρ} → (p : ρ ≾ᵣ ρ) → ⟨⟩-≤-ren {Δ = Γ} p ≐ʳ id-ren
⟨⟩-≤-ren-id-≐ p = mk≐ʳ go
  where
    go : ∀ {A ρ₀} → (x : A ∈[ ρ₀ ] _) → _
    go (Tl-⟨⟩ x) = refl

cong-∷-ren-id-≐ : ∀ {Γ A} {r : Ren [] Γ Γ}
                → r ≐ʳ id-ren → cong-∷-ren {A = A} r ≐ʳ id-ren
cong-∷-ren-id-≐ h = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go Hd       = refl
    go (Tl-∷ x) = cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (at h x)

cong-⟨⟩-ren-id-≐ : ∀ {Γ ρ} {r : Ren [] Γ Γ}
                 → r ≐ʳ id-ren → cong-⟨⟩-ren {ρ = ρ} r ≐ʳ id-ren
cong-⟨⟩-ren-id-≐ {ρ = ρ} h = mk≐ʳ go
  where
    go : ∀ {A' ρ'} (x : A' ∈[ ρ' ] _) → _
    go (Tl-⟨⟩ x) = cong (λ z → proj₁ z ·ᵣ ρ , Tl-⟨⟩ (proj₂ z)) (at h x)

cong-ren-id-≐ : ∀ {Γ} {r : Ren [] Γ Γ} → (Γ₀ : Ctx)
              → r ≐ʳ id-ren → cong-ren {Γ'' = Γ₀} r ≐ʳ id-ren
cong-ren-id-≐ []         h = h
cong-ren-id-≐ (Γ₀ ∷ A)   h = cong-∷-ren-id-≐ (cong-ren-id-≐ Γ₀ h)
cong-ren-id-≐ (Γ₀ ⟨ ρ ⟩) h = cong-⟨⟩-ren-id-≐ (cong-ren-id-≐ Γ₀ h)

∘ʳ-id-≐ : ∀ {Γ Γ'} {r : Ren [] Γ' Γ'} → (w : Ren [] Γ Γ')
        → r ≐ʳ id-ren → (r ∘ʳ w) ≐ʳ w
∘ʳ-id-≐ w h = mk≐ʳ (λ x → at h (proj₂ (var-tgt w x)))

∘ʳ-id-≐ʳ : ∀ {Γ Γ'} {r : Ren [] Γ Γ} → (w : Ren [] Γ Γ')
         → r ≐ʳ id-ren → (w ∘ʳ r) ≐ʳ w
∘ʳ-id-≐ʳ w h = mk≐ʳ (λ x → cong (var-tgt′ w) (at h x))

restrict-ren-id-≐ : ∀ {Γ} {r : Ren [] Γ Γ} → r ≐ʳ id-ren → restrict-ren r ≐ʳ id-ren
restrict-ren-id-≐ h = restrict-ren-≐ h

mutual

  V-rename-id-≐ : ∀ {Γ A} {r : Ren [] Γ Γ} → r ≐ʳ id-ren
                → (V : Γ ⊢V⦂ A) → V-rename r V ≐ᵛ V

  V-rename-id-≐ {r = r} h (var f x) with var-rename r x | at h x
  ... | _ | refl = var-≐
  V-rename-id-≐ h (const c) = const-≐
  V-rename-id-≐ h ⋆         = ⋆-≐
  V-rename-id-≐ h ⦉ V , W ⦊  = pair-≐ (V-rename-id-≐ h V) (V-rename-id-≐ h W)
  V-rename-id-≐ h (lam M)   = lam-≐ (C-rename-id-≐ (cong-ren-id-≐ ([] ∷ _) h) M)

  C-rename-id-≐ : ∀ {Γ C} {r : Ren [] Γ Γ} → r ≐ʳ id-ren
                → (M : Γ ⊢C⦂ C) → C-rename r M ≐ᶜ M

  C-rename-id-≐ h (return V) = return-≐ (V-rename-id-≐ h V)
  C-rename-id-≐ h (M ⨟ N) =
    seq-≐ (C-rename-id-≐ h M) (C-rename-id-≐ (cong-ren-id-≐ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-id-≐ h (V · W) = app-≐ (V-rename-id-≐ h V) (V-rename-id-≐ h W)
  C-rename-id-≐ h (match V `in M) =
    match-≐ (V-rename-id-≐ h V) (C-rename-id-≐ (cong-ren-id-≐ ([] ∷ _ ∷ _) h) M)
  C-rename-id-≐ h (absurd V) = absurd-≐ (V-rename-id-≐ h V)
  C-rename-id-≐ h (perform op V M) =
    perform-≐ (V-rename-id-≐ h V)
              (C-rename-id-≐ (cong-ren-id-≐ (_ ⟨ _ ⟩ ∷ _) h) M)
  C-rename-id-≐ h (delay τ M) =
    delay-≐ (C-rename-id-≐ (cong-ren-id-≐ ([] ⟨ _ ⟩) h) M)
  C-rename-id-≐ h (handle M `with H `in N) =
    handle-≐ (C-rename-id-≐ h M)
      (λ op ε'' →
         C-rename-id-≐ (cong-∷-ren-id-≐ (cong-∷-ren-id-≐ (restrict-ren-id-≐ h)))
                       (H op ε''))
      (C-rename-id-≐ (cong-ren-id-≐ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-rename-id-≐ h (unbox w V M) =
    unbox-≐ (unbox-tgt-≐ (∘ʳ-id-≐ w h) V)
            (C-rename-id-≐ (cong-ren-id-≐ ([] ∷ _) h) M)
  C-rename-id-≐ h (box V M) =
    box-≐ (V-rename-id-≐ (cong-ren-id-≐ ([] ⟨ _ ⟩) h) V)
          (C-rename-id-≐ (cong-ren-id-≐ ([] ∷ _) h) M)
  C-rename-id-≐ h (coerce p M) = coerce-≐ (C-rename-id-≐ h M)

eq-ren-≐ : ∀ {Γ Γ'} → (e e' : Γ ≡ Γ') → eq-ren e ≐ʳ eq-ren e'
eq-ren-≐ e e' rewrite uip {p = e} {q = e'} = ≐ʳ-refl

-- Renaming along an identity-*like* renaming between contexts that are only
-- propositionally equal: the action is the transport. `eq-ren refl` is
-- `id-ren`, so this is `C-rename-id-≐` once the equality is matched.

C-rename-eq-≐ : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → {r : Ren [] Γ Γ'}
              → r ≐ʳ eq-ren e → (M : Γ ⊢C⦂ C)
              → C-rename r M ≐ᶜ subst (_⊢C⦂ C) e M
C-rename-eq-≐ refl h M = C-rename-id-≐ h M

-- Extending such a renaming by a suffix stays identity-like.

cong-ren-eq-ren-≐ : ∀ {Γ Γ'} → (Δ : Ctx) → (e : Γ ≡ Γ')
                  → cong-ren {Γ'' = Δ} (eq-ren e)
                  ≐ʳ eq-ren (cong (_++ᶜ Δ) e)
cong-ren-eq-ren-≐ Δ refl = cong-ren-id-≐ Δ ≐ʳ-refl

-- `eq-ren` commutes with the suffix formers. (Note `cong-ren` at nested suffixes
-- is *not* `cong-ren` at their concatenation: the contexts differ by
-- `++ᶜ-assoc`, so any such step has to be conjugated by `eq-ren`s.)

eq-ren-∷-≐ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ')
           → eq-ren (cong (_∷ A) e) ≐ʳ cong-∷-ren {A = A} (eq-ren e)
eq-ren-∷-≐ refl = ≐ʳ-sym (cong-∷-ren-id-≐ ≐ʳ-refl)

eq-ren-⟨⟩-≐ : ∀ {Γ Γ' ρ} → (e : Γ ≡ Γ')
            → eq-ren (cong (_⟨ ρ ⟩) e) ≐ʳ cong-⟨⟩-ren {ρ = ρ} (eq-ren e)
eq-ren-⟨⟩-≐ refl = ≐ʳ-sym (cong-⟨⟩-ren-id-≐ ≐ʳ-refl)

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

cong-ren-assoc-≐ : ∀ {Γ Γ'} → (Θ D : Ctx) → (r : Ren [] Γ Γ')
                 → cong-ren {Γ'' = D} (cong-ren {Γ'' = Θ} r)
                 ≐ʳ (eq-ren (sym (++ᶜ-assoc Γ' Θ D))
                     ∘ʳ cong-ren {Γ'' = Θ ++ᶜ D} r
                     ∘ʳ eq-ren (++ᶜ-assoc Γ Θ D))

cong-ren-assoc-≐ Θ [] r =
  ≐ʳ-sym (≐ʳ-trans (∘ʳ-identityˡ-≐ _) (∘ʳ-identityʳ-≐ _))

cong-ren-assoc-≐ {Γ} {Γ'} Θ (D ∷ A) r =
  ≐ʳ-trans (cong-∷-ren-≐ (cong-ren-assoc-≐ Θ D r))
    (≐ʳ-trans (cong-∷-ren-∘-≐ _ _)
      (≐ʳ-trans (∘ʳ-≐ (≐ʳ-trans (≐ʳ-sym (eq-ren-∷-≐ (sym (++ᶜ-assoc Γ' Θ D))))
                                (eq-ren-≐ _ _))
                      (cong-∷-ren-∘-≐ _ _))
                (∘ʳ-≐ ≐ʳ-refl
                      (∘ʳ-≐ ≐ʳ-refl
                            (≐ʳ-trans (≐ʳ-sym (eq-ren-∷-≐ (++ᶜ-assoc Γ Θ D)))
                                      (eq-ren-≐ _ _))))))

cong-ren-assoc-≐ {Γ} {Γ'} Θ (D ⟨ ρ ⟩) r =
  ≐ʳ-trans (cong-⟨⟩-ren-≐ (cong-ren-assoc-≐ Θ D r))
    (≐ʳ-trans (cong-⟨⟩-ren-∘-≐ _ _)
      (≐ʳ-trans (∘ʳ-≐ (≐ʳ-trans (≐ʳ-sym (eq-ren-⟨⟩-≐ (sym (++ᶜ-assoc Γ' Θ D))))
                                (eq-ren-≐ _ _))
                      (cong-⟨⟩-ren-∘-≐ _ _))
                (∘ʳ-≐ ≐ʳ-refl
                      (∘ʳ-≐ ≐ʳ-refl
                            (≐ʳ-trans (≐ʳ-sym (eq-ren-⟨⟩-≐ (++ᶜ-assoc Γ Θ D)))
                                      (eq-ren-≐ _ _))))))

-- Composing two `eq-ren`s.

eq-ren-∘-≐ : ∀ {Γ Γ' Γ''} → (e : Γ ≡ Γ') → (e' : Γ' ≡ Γ'')
           → (eq-ren e' ∘ʳ eq-ren e) ≐ʳ eq-ren (trans e e')
eq-ren-∘-≐ refl refl = ∘ʳ-identityˡ-≐ _

-- With an *eternal* `B`, weakening by `B` weakens the eternal restriction by it
-- too: `restrict-ren` walks down to `restrict-ren wk-ren`, which at an eternal
-- type is `wk-ren`. The two contexts differ by `ᴱ`'s distribution over `_++ᶜ_`,
-- so the statement is conjugated by `eq-ren`s at arbitrary proofs of that.

restrict-wk-et-≐ : ∀ {Γ B} → (et : Eternal B) → (Δ : Ctx)
                 → (e₁ : (Γ ++ᶜ Δ) ᴱ ≡ Γ ᴱ ++ᶜ Δ ᴱ)
                 → (e₂ : ((Γ ∷ B) ++ᶜ Δ) ᴱ ≡ (Γ ᴱ ∷ B) ++ᶜ Δ ᴱ)
                 → restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (wk-ren {A = B}))
                 ≐ʳ (eq-ren (sym e₂)
                     ∘ʳ cong-ren {Γ'' = Δ ᴱ} (wk-ren {A = B}) ∘ʳ eq-ren e₁)

restrict-wk-et-≐ {Γ} {B} et [] e₁ e₂
  rewrite eternal?-yes et
        | uip {p = e₁} {q = refl} | uip {p = e₂} {q = refl} =
  ≐ʳ-sym (≐ʳ-trans (∘ʳ-identityˡ-≐ _) (∘ʳ-identityʳ-≐ _))

restrict-wk-et-≐ {Γ} {B} et (Δ ∷ C) e₁ e₂ with eternal? C

... | yes _ =
  ≐ʳ-trans (cong-∷-ren-≐ (restrict-wk-et-≐ et Δ (∷ᶜ-injective-ctx e₁)
                                              (∷ᶜ-injective-ctx e₂)))
    (≐ʳ-trans (cong-∷-ren-∘-≐ _ _)
      (≐ʳ-trans (∘ʳ-≐ (≐ʳ-sym (eq-ren-∷-≐ (sym (∷ᶜ-injective-ctx e₂))))
                      (cong-∷-ren-∘-≐ _ _))
        (≐ʳ-trans (∘ʳ-≐ (eq-ren-≐ _ (sym e₂))
                        (∘ʳ-≐ ≐ʳ-refl
                              (≐ʳ-sym (eq-ren-∷-≐ (∷ᶜ-injective-ctx e₁)))))
                  (∘ʳ-≐ ≐ʳ-refl (∘ʳ-≐ ≐ʳ-refl (eq-ren-≐ _ e₁))))))

... | no  _ = restrict-wk-et-≐ et Δ e₁ e₂

restrict-wk-et-≐ {Γ} {B} et (Δ ⟨ ρ ⟩) e₁ e₂ = restrict-wk-et-≐ et Δ e₁ e₂

-- The form `sub-wk`'s eternal `handle` clause needs: the clause's renaming
-- `cong-ren {D} (restrict-ren (cong-ren {Θ} wk-ren))` is `cong-ren` at the
-- concatenated suffix `Θ ᴱ ++ᶜ D`, conjugated by `eq-ren`s. Assembled from
-- `restrict-wk-et-≐`, `cong-ren-∘-≐`, `cong-ren-eq-ren-≐` and
-- `cong-ren-assoc-≐`, with the `eq-ren`s fused by `eq-ren-∘-≐` and any two
-- proofs identified by `eq-ren-≐`.

restrict-wk-clause-≐ : ∀ {Γ B} → (et : Eternal B) → (Θ D : Ctx)
                     → (e₁ : (Γ ++ᶜ Θ) ᴱ ≡ Γ ᴱ ++ᶜ Θ ᴱ)
                     → (e₂ : ((Γ ∷ B) ++ᶜ Θ) ᴱ ≡ (Γ ᴱ ∷ B) ++ᶜ Θ ᴱ)
                     → cong-ren {Γ'' = D}
                         (restrict-ren {Ξ = []} (cong-ren {Γ'' = Θ} (wk-ren {A = B})))
                     ≐ʳ (eq-ren (cong (_++ᶜ D) (sym e₂))
                         ∘ʳ (eq-ren (sym (++ᶜ-assoc (Γ ᴱ ∷ B) (Θ ᴱ) D))
                             ∘ʳ cong-ren {Γ'' = Θ ᴱ ++ᶜ D} (wk-ren {A = B})
                             ∘ʳ eq-ren (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) D))
                         ∘ʳ eq-ren (cong (_++ᶜ D) e₁))

restrict-wk-clause-≐ {Γ} {B} et Θ D e₁ e₂ =
  ≐ʳ-trans (cong-ren-≐ D (restrict-wk-et-≐ et Θ e₁ e₂))
    (≐ʳ-trans (cong-ren-∘-≐ D _ _)
      (∘ʳ-≐ (cong-ren-eq-ren-≐ D (sym e₂))
        (≐ʳ-trans (cong-ren-∘-≐ D _ _)
                  (∘ʳ-≐ (cong-ren-assoc-≐ (Θ ᴱ) D (wk-ren {A = B}))
                        (cong-ren-eq-ren-≐ D e₁)))))

-- With a non-eternal `B`, weakening by `B` leaves the eternal restriction
-- alone: `restrict-ren` walks `cong-ren` down to `restrict-ren wk-ren`, which at
-- a non-eternal type is `id-ren`. The two contexts are then equal only
-- propositionally, so the statement is against an arbitrary proof of that
-- equality — any two agree by `uip`.

restrict-wk-≐ : ∀ {Γ B} → (¬et : ¬ Eternal B) → (Δ : Ctx)
              → (e : (Γ ++ᶜ Δ) ᴱ ≡ ((Γ ∷ B) ++ᶜ Δ) ᴱ)
              → restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (wk-ren {A = B})) ≐ʳ eq-ren e

restrict-wk-≐ {Γ} {B} ¬et [] e
  rewrite eternal?-no ¬et | uip {p = e} {q = refl} = ≐ʳ-refl

restrict-wk-≐ {Γ} {B} ¬et (Δ ∷ C) e with eternal? C
... | yes _ =
  ≐ʳ-trans (cong-∷-ren-≐ (restrict-wk-≐ ¬et Δ (∷ᶜ-injective-ctx e)))
    (≐ʳ-trans (cong-ren-eq-ren-≐ ([] ∷ C) (∷ᶜ-injective-ctx e))
              (eq-ren-≐ _ e))
... | no  _ = restrict-wk-≐ ¬et Δ e

restrict-wk-≐ {Γ} {B} ¬et (Δ ⟨ ρ ⟩) e = restrict-wk-≐ ¬et Δ e

------------------------------------------------------------------------
-- FUNCTORIALITY
--
-- At the binding formers the two sides rename along `cong-ren (r₂ ∘ʳ r₁)` and
-- `cong-ren r₂ ∘ʳ cong-ren r₁`, at `unbox` along `(r₂ ∘ʳ r₁) ∘ʳ w` and
-- `r₂ ∘ʳ (r₁ ∘ʳ w)`: distinct renamings acting alike, so the statement is at
-- `_≐ᵛ_`/`_≐ᶜ_` and the proof leans on the laws above.
------------------------------------------------------------------------

mutual

  V-rename-∘ : ∀ {Γ Γ' Γ'' A} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
             → (V : Γ ⊢V⦂ A)
             → V-rename (r₂ ∘ʳ r₁) V ≐ᵛ V-rename r₂ (V-rename r₁ V)

  V-rename-∘ r₂ r₁ (var f x) with var-rename r₁ x
  ... | _ , _ , y with var-rename r₂ y
  ...   | _ , _ , z = var-≐
  V-rename-∘ r₂ r₁ (const c) = const-≐
  V-rename-∘ r₂ r₁ ⋆         = ⋆-≐
  V-rename-∘ r₂ r₁ ⦉ V , W ⦊  = pair-≐ (V-rename-∘ r₂ r₁ V) (V-rename-∘ r₂ r₁ W)
  V-rename-∘ r₂ r₁ (lam M)   =
    lam-≐ (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ∷ _) r₂ r₁) M)
                    (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))

  C-rename-∘ : ∀ {Γ Γ' Γ'' C} → (r₂ : Ren [] Γ' Γ'') → (r₁ : Ren [] Γ Γ')
             → (M : Γ ⊢C⦂ C)
             → C-rename (r₂ ∘ʳ r₁) M ≐ᶜ C-rename r₂ (C-rename r₁ M)

  C-rename-∘ r₂ r₁ (return V) = return-≐ (V-rename-∘ r₂ r₁ V)
  C-rename-∘ r₂ r₁ (M ⨟ N) =
    seq-≐ (C-rename-∘ r₂ r₁ M)
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) N)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) N))
  C-rename-∘ r₂ r₁ (V · W) = app-≐ (V-rename-∘ r₂ r₁ V) (V-rename-∘ r₂ r₁ W)
  C-rename-∘ r₂ r₁ (match V `in M) =
    match-≐ (V-rename-∘ r₂ r₁ V)
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ∷ _ ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (absurd V) = absurd-≐ (V-rename-∘ r₂ r₁ V)
  C-rename-∘ r₂ r₁ (perform op V M) =
    perform-≐ (V-rename-∘ r₂ r₁ V)
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (delay τ M) =
    delay-≐ (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ⟨ _ ⟩) r₂ r₁) M)
                      (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (handle M `with H `in N) =
    handle-≐ (C-rename-∘ r₂ r₁ M)
      (λ op ε'' →
         ≐ᶜ-trans
           (C-rename-≐
             (≐ʳ-trans (cong-∷-ren-≐ (cong-∷-ren-≐ (restrict-ren-∘-≐ r₂ r₁)))
                       (cong-ren-∘-≐ ([] ∷ _ ∷ _)
                                     (restrict-ren r₂) (restrict-ren r₁)))
             (H op ε''))
           (C-rename-∘ (cong-∷-ren (cong-∷-ren (restrict-ren r₂)))
                       (cong-∷-ren (cong-∷-ren (restrict-ren r₁)))
                       (H op ε'')))
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ (_ ⟨ _ ⟩ ∷ _) r₂ r₁) N)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) N))
  C-rename-∘ r₂ r₁ (unbox w V M) =
    unbox-≐ (unbox-tgt-≐ (∘ʳ-assoc-≐ r₂ r₁ w) V)
      (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ∷ _) r₂ r₁) M)
                (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (box V M) =
    box-≐ (≐ᵛ-trans (V-rename-≐ (cong-ren-∘-≐ ([] ⟨ _ ⟩) r₂ r₁) V)
                    (V-rename-∘ (cong-ren r₂) (cong-ren r₁) V))
          (≐ᶜ-trans (C-rename-≐ (cong-ren-∘-≐ ([] ∷ _) r₂ r₁) M)
                    (C-rename-∘ (cong-ren r₂) (cong-ren r₁) M))
  C-rename-∘ r₂ r₁ (coerce p M) = coerce-≐ (C-rename-∘ r₂ r₁ M)

------------------------------------------------------------------------
-- THE ACTION IS A CONGRUENCE
--
-- Renaming related terms gives related terms. Induction on the relation, not on
-- the term; `unbox` needs `∘ʳ-≐` on the stored renamings.
------------------------------------------------------------------------

mutual

  V-rename-cong : ∀ {Γ Γ' A} → (r : Ren [] Γ Γ') → {V V' : Γ ⊢V⦂ A}
                → V ≐ᵛ V' → V-rename r V ≐ᵛ V-rename r V'

  V-rename-cong r var-≐            = var-≐
  V-rename-cong r const-≐          = const-≐
  V-rename-cong r ⋆-≐              = ⋆-≐
  V-rename-cong r (pair-≐ eV eW)   =
    pair-≐ (V-rename-cong r eV) (V-rename-cong r eW)
  V-rename-cong r (lam-≐ eM)       = lam-≐ (C-rename-cong (cong-ren r) eM)

  C-rename-cong : ∀ {Γ Γ' C} → (r : Ren [] Γ Γ') → {M M' : Γ ⊢C⦂ C}
                → M ≐ᶜ M' → C-rename r M ≐ᶜ C-rename r M'

  C-rename-cong r (return-≐ eV)     = return-≐ (V-rename-cong r eV)
  C-rename-cong r (seq-≐ eM eN)     =
    seq-≐ (C-rename-cong r eM) (C-rename-cong (cong-ren r) eN)
  C-rename-cong r (app-≐ eV eW)     =
    app-≐ (V-rename-cong r eV) (V-rename-cong r eW)
  C-rename-cong r (match-≐ eV eM)   =
    match-≐ (V-rename-cong r eV) (C-rename-cong (cong-ren r) eM)
  C-rename-cong r (absurd-≐ eV)     = absurd-≐ (V-rename-cong r eV)
  C-rename-cong r (perform-≐ eV eM) =
    perform-≐ (V-rename-cong r eV) (C-rename-cong (cong-ren r) eM)
  C-rename-cong r (delay-≐ eM)      = delay-≐ (C-rename-cong (cong-ren r) eM)
  C-rename-cong r (handle-≐ eM eH eN) =
    handle-≐ (C-rename-cong r eM)
             (λ op ε'' → C-rename-cong (cong-∷-ren (cong-∷-ren (restrict-ren r)))
                                       (eH op ε''))
             (C-rename-cong (cong-ren r) eN)
  C-rename-cong r (unbox-≐ {w = w} {w' = w'} {V = V} {V' = V'} hw eM) =
    unbox-≐ (trans (unbox-tgt-∘ r w V)
                   (trans (cong (var-tgt′ r) hw)
                          (sym (unbox-tgt-∘ r w' V'))))
            (C-rename-cong (cong-ren r) eM)
  C-rename-cong r (coerce-≐ eM)     = coerce-≐ (C-rename-cong r eM)
  C-rename-cong r (box-≐ eV eM)     =
    box-≐ (V-rename-cong (cong-ren r) eV) (C-rename-cong (cong-ren r) eM)
