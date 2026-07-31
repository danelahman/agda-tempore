------------------------------------------------------------------------
-- The eternal restriction of a single-variable substitution.          --
--                                                                     --
-- At a non-eternal type the substituted variable does not survive the  --
-- restriction, so the restricted substitution only retypes; at an      --
-- eternal one it replaces the variable `∈-ᴱ-split` names by the        --
-- restricted value. This is what a handler clause sees, and the only   --
-- fact about `_[_↦_]cl` that is not immediate from its definition.     --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions.Restrict (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.RenActions    S
open import Syntax.Renamings     S
open import Syntax.Substitutions S
open import Syntax.Types         S

open import Syntax.Renamings.Equivalence S
open import Syntax.Renamings.Coherence   S
open import Syntax.Terms.Equivalence     S

open import Syntax.Substitutions.Base             S
open import Syntax.Substitutions.Lookup           S
open import Syntax.Substitutions.Action           S
open import Syntax.Substitutions.Equivalence      S
open import Syntax.Substitutions.Interchange      S
open import Syntax.Substitutions.Chain            S
open import Syntax.Substitutions.ChainEquivalence S

------------------------------------------------------------------------
-- EMBEDDED RENAMINGS ACTING ALIKE
--
-- `⌜_⌝` is faithful for the two observations: a variable's image under an
-- embedded renaming is a `var` node at `var-img`, and a resource variable's
-- image *is* `var-img`.
------------------------------------------------------------------------

⌜⌝-≐ˢ₀ : ∀ {Γ Γ'} {r r' : Ren [] Γ Γ'} → r ≐ʳ r' → ⌜ r ⌝ ≐ˢ₀ ⌜ r' ⌝
⌜⌝-≐ˢ₀ h = mk≐ˢ₀ (λ x f → var-img-≡ (at h x) _ _) (λ y → at h y)

-- Replacing a chain's head by one acting alike.

◅-≐ˢ₀ : ∀ {Γ Δ Γ'} {s s' : Sub₀ [] Γ Δ} → s ≐ˢ₀ s' → (σ : Sub [] Δ Γ')
      → (s ◅ σ) ≐ˢ (s' ◅ σ)
◅-≐ˢ₀ h σ = mk≐ˢ (λ x f → V-sub₀-≐ˢ₀ h (sub-var σ x f)) (λ y → atᵗ h _)

-- and its tail: the head acts on the tail's image, so a `≐ˢ` there is a `cong`.

◅-tail-≐ˢ : ∀ {Γ Δ Γ'} → (s : Sub₀ [] Γ Δ) → {σ σ' : Sub [] Δ Γ'}
          → σ ≐ˢ σ' → (s ◅ σ) ≐ˢ (s ◅ σ')
◅-tail-≐ˢ s h =
  mk≐ˢ (λ x f → cong (V-sub₀ s) (atᵛ h x f))
       (λ y → cong (λ t → tgt-img₀ s (proj₂ t)) (atᵗ h y))

-- An identity-like head drops out.

id-◅-≐ˢ : ∀ {Γ Γ'} {r : Ren [] Γ Γ} → r ≐ʳ id-ren → (σ : Sub [] Γ Γ')
        → (⌜ r ⌝ ◅ σ) ≐ˢ σ
id-◅-≐ˢ {r = r} h σ =
  mk≐ˢ (λ x f → trans (V-sub₀-⌜⌝ r (sub-var σ x f))
                      (V-rename-id-≡ h (sub-var σ x f)))
       (λ y → at h (proj₂ (tgt-img σ y)))

------------------------------------------------------------------------
-- THE ETERNAL RESTRICTION OF A SINGLE SUBSTITUTION
--
-- At a non-eternal type the substituted variable does not survive the
-- restriction, so the restricted substitution only retypes: it acts as the
-- `eq-ren` of `ᴱ-drop-split`. As in `restrict-wk-≐ʳ`, the context equality is
-- an argument — any two agree by `uip` — and each type inspected is dispatched
-- through a helper taking the decision rather than a bare `with`.
------------------------------------------------------------------------

restrict-val-sub-ne : ∀ {Γ₀ A} → (dec : Dec (Eternal A)) → ¬ Eternal A
                    → (W : Γ₀ ⊢V⦂ A) → (e : ᴱ-∷ (Γ₀ ᴱ) A dec ≡ Γ₀ ᴱ)
                    → restrict-val-sub {[]} {Γ₀} {A} dec W ≐ˢ₀ ⌜ eq-ren e ⌝
restrict-val-sub-ne (yes et) ¬et W e = ⊥-elim (¬et et)
restrict-val-sub-ne (no  _)  ¬et W e rewrite uip {p = e} {q = refl} = ≐ˢ₀-refl

-- `Γ` and `Δ` are explicit: they occur only under `_ᴱ`, which is not injective,
-- so nothing at a call site determines them.

restrict-∷-sub-ne : ∀ {B} → (Γ Δ : Ctx) → (dec : Dec (Eternal B))
                  → {s : Sub₀ [] (Δ ᴱ) (Γ ᴱ)}
                  → (e₀ : Γ ᴱ ≡ Δ ᴱ) → s ≐ˢ₀ ⌜ eq-ren e₀ ⌝
                  → (e : ᴱ-∷ (Γ ᴱ) B dec ≡ ᴱ-∷ (Δ ᴱ) B dec)
                  → restrict-∷-sub {Ξ = []} {Δ = Δ} {Δ' = Γ} dec s ≐ˢ₀ ⌜ eq-ren e ⌝
restrict-∷-sub-ne Γ Δ (yes _) e₀ h e =
  ≐ˢ₀-trans (cong-∷-sub-⌜⌝ h)
            (⌜⌝-≐ˢ₀ (≐ʳ-trans (≐ʳ-sym (eq-ren-∷-≐ʳ e₀)) (eq-ren-≐ʳ _ e)))
restrict-∷-sub-ne Γ Δ (no  _) e₀ h e =
  ≐ˢ₀-trans h (⌜⌝-≐ˢ₀ (eq-ren-≐ʳ e₀ e))

restrict-sub-at-ne : ∀ {Γ A ρ} → (¬et : ¬ Eternal A) → (x : A ∈[ ρ ] Γ)
                   → (W : split-l x ⊢V⦂ A)
                   → (e : Γ ᴱ ≡ (split-l x ++ᶜ split-r x) ᴱ)
                   → restrict-sub₀ (sub-at₀ x W) ≐ˢ₀ ⌜ eq-ren e ⌝

restrict-sub-at-ne {A = A} ¬et Hd W e =
  restrict-val-sub-ne (eternal? A) ¬et W e
restrict-sub-at-ne {Γ₀ ∷ B} ¬et (Tl-∷ x) W e =
  restrict-∷-sub-ne Γ₀ (split-l x ++ᶜ split-r x) (eternal? B)
                    (ᴱ-drop-split ¬et x)
                    (restrict-sub-at-ne ¬et x W (ᴱ-drop-split ¬et x)) e
restrict-sub-at-ne ¬et (Tl-⟨⟩ x) W e =
  restrict-sub-at-ne ¬et x W e

------------------------------------------------------------------------
-- At an *eternal* type the substituted variable does survive, restricted:
-- the restricted substitution replaces the variable `∈-ᴱ-split` names by the
-- restricted value. The two contexts differ by `ᴱ`'s distribution over `_++ᶜ_`,
-- so the statement is conjugated by an `eq-ren`, hence lives at the chain
-- level; as for `restrict-wk-et-≐ʳ` the equality is an arbitrary argument.
------------------------------------------------------------------------

-- Re-heading a congruence chain: the retyping under one more binder is the
-- retyping under the binder.

-- A retyping under one more binder, resp. lock, is that binder's congruence
-- applied to the retyping.

eq-ren-∷-≐ˢ₀ : ∀ {Γ₁ Γ₂ B} → (e' : Γ₁ ≡ Γ₂) → (e : Γ₁ ∷ B ≡ Γ₂ ∷ B)
             → ⌜ eq-ren e ⌝ ≐ˢ₀ cong-∷-sub {A = B} ⌜ eq-ren e' ⌝
eq-ren-∷-≐ˢ₀ {B = B} e' e =
  ≐ˢ₀-trans
    (⌜⌝-≐ˢ₀ (≐ʳ-trans (eq-ren-≐ʳ e (cong (_∷ B) e')) (eq-ren-∷-≐ʳ e')))
    (≐ˢ₀-sym (cong-∷-sub-⌜⌝ ≐ˢ₀-refl))

eq-ren-⟨⟩-≐ˢ₀ : ∀ {Γ₁ Γ₂ ρ} → (e' : Γ₁ ≡ Γ₂) → (e : Γ₁ ⟨ ρ ⟩ ≡ Γ₂ ⟨ ρ ⟩)
              → ⌜ eq-ren e ⌝ ≐ˢ₀ cong-⟨⟩-sub {ρ = ρ} ⌜ eq-ren e' ⌝
eq-ren-⟨⟩-≐ˢ₀ {ρ = ρ} e' e =
  ≐ˢ₀-trans
    (⌜⌝-≐ˢ₀ (≐ʳ-trans (eq-ren-≐ʳ e (cong (_⟨ ρ ⟩) e')) (eq-ren-⟨⟩-≐ʳ e')))
    (≐ˢ₀-sym (cong-⟨⟩-sub-⌜⌝ ≐ˢ₀-refl))

head-∷-≐ˢ : ∀ {Γ₁ Γ₂ Γ' B} → (σ : Sub [] Γ₁ Γ')
          → (e' : Γ₁ ≡ Γ₂) → (e : Γ₁ ∷ B ≡ Γ₂ ∷ B)
          → (⌜ eq-ren e ⌝ ◅ cong-∷-subˢ {A = B} σ)
          ≐ˢ cong-∷-subˢ (⌜ eq-ren e' ⌝ ◅ σ)
head-∷-≐ˢ σ e' e = ◅-≐ˢ₀ (eq-ren-∷-≐ˢ₀ e' e) (cong-∷-subˢ σ)

head-⟨⟩-≐ˢ : ∀ {Γ₁ Γ₂ Γ' ρ} → (σ : Sub [] Γ₁ Γ')
           → (e' : Γ₁ ≡ Γ₂) → (e : Γ₁ ⟨ ρ ⟩ ≡ Γ₂ ⟨ ρ ⟩)
           → (⌜ eq-ren e ⌝ ◅ cong-⟨⟩-subˢ {ρ = ρ} σ)
           ≐ˢ cong-⟨⟩-subˢ (⌜ eq-ren e' ⌝ ◅ σ)
head-⟨⟩-≐ˢ σ e' e = ◅-≐ˢ₀ (eq-ren-⟨⟩-≐ˢ₀ e' e) (cong-⟨⟩-subˢ σ)

val-sub-≐ˢ : ∀ {Γ A} → {V V' : Γ ⊢V⦂ A}
           → V ≡ V' → [ val-sub {Ξ = []} {Δ = Γ} {A = A} V ]ˢ ≐ˢ [ val-sub V' ]ˢ
val-sub-≐ˢ refl = ≐ˢ-refl

-- The restricted value, at the position the clause substitution reaches it.

Wᴱ : ∀ {Γ A ρ} → (D : Ctx) → (et : Eternal A) → (x : A ∈[ ρ ] Γ)
   → (W : split-l x ⊢V⦂ A)
   → split-l (split→∈ (split-++ʳ (∈-ᴱ-split et x) D)) ⊢V⦂ A
Wᴱ {A = A} D et x W =
  subst (_⊢V⦂ A) (sym (split→∈-split-l (split-++ʳ (∈-ᴱ-split et x) D)))
        (eternal-val-restrict et W)

-- The suffix-free case. Each `eternal?` is decided *before* the equality
-- argument is taken, so the `with` abstracts it in the equality's type too.

restrict-sub-at-et₀ : ∀ {Γ A ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ)
                    → (W : split-l x ⊢V⦂ A)
                    → (e : split-l (split→∈ (∈-ᴱ-split et x))
                             ++ᶜ split-r (split→∈ (∈-ᴱ-split et x))
                         ≡ (split-l x ++ᶜ split-r x) ᴱ)
                    → (⌜ eq-ren e ⌝
                       ◅ [ sub-at₀ (split→∈ (∈-ᴱ-split et x)) (Wᴱ [] et x W) ]ˢ)
                    ≐ˢ [ restrict-sub₀ (sub-at₀ x W) ]ˢ

restrict-sub-at-et₀ {A = A} et Hd W with eternal? A
... | yes a  = λ e →
  ≐ˢ-trans (id-◅-≐ˢ (eq-ren-≐ʳ e refl) _)
           (val-sub-≐ˢ (cong (λ p → eternal-val-restrict p W)
                             (eternal-irrelevant et a)))
... | no ¬et = ⊥-elim (¬et et)

restrict-sub-at-et₀ et (Tl-∷ {B = B} x) W with eternal? B
... | yes _ = λ e →
  ≐ˢ-trans (head-∷-≐ˢ _ (∷ᶜ-injective-ctx e) e)
           (cong-∷-subˢ-≐ˢ (restrict-sub-at-et₀ et x W (∷ᶜ-injective-ctx e)))
... | no  _ = λ e → restrict-sub-at-et₀ et x W e

restrict-sub-at-et₀ et (Tl-⟨⟩ x) W e = restrict-sub-at-et₀ et x W e

-- and under a suffix, by induction on it: each step is the matching chain
-- congruence, the retyping moving through by `head-∷-≐ˢ`/`head-⟨⟩-≐ˢ`.

restrict-sub-at-et : ∀ {Γ A ρ} → (D : Ctx) → (et : Eternal A) → (x : A ∈[ ρ ] Γ)
                   → (W : split-l x ⊢V⦂ A)
                   → (e : split-l (split→∈ (split-++ʳ (∈-ᴱ-split et x) D))
                            ++ᶜ split-r (split→∈ (split-++ʳ (∈-ᴱ-split et x) D))
                        ≡ (split-l x ++ᶜ split-r x) ᴱ ++ᶜ D)
                   → (⌜ eq-ren e ⌝
                      ◅ [ sub-at₀ (split→∈ (split-++ʳ (∈-ᴱ-split et x) D))
                                  (Wᴱ D et x W) ]ˢ)
                   ≐ˢ [ cong-sub₀ {Γ'' = D} (restrict-sub₀ (sub-at₀ x W)) ]ˢ

restrict-sub-at-et []        et x W e = restrict-sub-at-et₀ et x W e
restrict-sub-at-et (D ∷ B)   et x W e =
  ≐ˢ-trans (head-∷-≐ˢ _ (∷ᶜ-injective-ctx e) e)
           (cong-∷-subˢ-≐ˢ (restrict-sub-at-et D et x W (∷ᶜ-injective-ctx e)))
restrict-sub-at-et (D ⟨ ρ ⟩) et x W e =
  ≐ˢ-trans (head-⟨⟩-≐ˢ _ (⟨⟩-injective-ctx e) e)
           (cong-⟨⟩-subˢ-≐ˢ (restrict-sub-at-et D et x W (⟨⟩-injective-ctx e)))

------------------------------------------------------------------------
-- WHAT THE CLAUSE SUBSTITUTION IS
--
-- The two facts above, read off at the clause's own suffix: at a non-eternal
-- type the clause is only retyped, and at an eternal one the restricted value
-- is substituted at the variable `∈-ᴱ-split` names.
------------------------------------------------------------------------

subst-ctx-cong : ∀ {C} → (F : Ctx → Ctx) → ∀ {Γ Γ'} → (e : Γ ≡ Γ')
               → (M : F Γ ⊢C⦂ C)
               → subst (λ Γ₀ → F Γ₀ ⊢C⦂ C) e M ≡ subst (_⊢C⦂ C) (cong F e) M
subst-ctx-cong F refl M = refl

cl-ne-≡ : ∀ {Γ A B ρ} → (¬et : ¬ Eternal A) → (x : A ∈[ ρ ] Γ)
        → (W : split-l x ⊢V⦂ A)
        → (H : (op : Op) → (ε'' : E)
             → Γ ᴱ ∷ type-of-gtype (param op)
                   ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
               ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
        → (op : Op) → (ε'' : E)
        → (H [ x ↦ W ]cl) op ε''
        ≡ subst (λ Γ₀ → Γ₀ ++ᶜ ([] ∷ type-of-gtype (param op)
                                   ∷ [ mapᵉ (op-grade op) ]
                                       (type-of-gtype (arity op) ⇒ B ‼ ε''))
                        ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                (ᴱ-drop-split ¬et x) (H op ε'')

cl-ne-≡ {B = B} ¬et x W H op ε'' =
  trans (C-sub₀-≐ˢ₀
          (≐ˢ₀-trans (cong-sub₀-≐ˢ₀ D (restrict-sub-at-ne ¬et x W eᴱ))
                     (cong-sub₀-⌜⌝ D (eq-ren eᴱ)))
          (H op ε''))
    (trans (C-sub₀-⌜⌝ (cong-ren {Γ'' = D} (eq-ren eᴱ)) (H op ε''))
      (trans (C-rename-eq-≡ (cong (_++ᶜ D) eᴱ) (cong-ren-eq-ren-≐ʳ D eᴱ) (H op ε''))
             (sym (subst-ctx-cong (_++ᶜ D) eᴱ (H op ε'')))))
  where
    D = [] ∷ type-of-gtype (param op)
           ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')

    eᴱ = ᴱ-drop-split ¬et x

cl-et-≡ : ∀ {Γ A B ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ)
        → (W : split-l x ⊢V⦂ A)
        → (H : (op : Op) → (ε'' : E)
             → Γ ᴱ ∷ type-of-gtype (param op)
                   ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
               ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
        → (op : Op) → (ε'' : E)
        → (e : split-l (split→∈ (split-++ʳ (∈-ᴱ-split et x)
                                  ([] ∷ type-of-gtype (param op)
                                      ∷ [ mapᵉ (op-grade op) ]
                                          (type-of-gtype (arity op) ⇒ B ‼ ε''))))
                 ++ᶜ split-r (split→∈ (split-++ʳ (∈-ᴱ-split et x)
                                        ([] ∷ type-of-gtype (param op)
                                            ∷ [ mapᵉ (op-grade op) ]
                                                (type-of-gtype (arity op) ⇒ B ‼ ε''))))
             ≡ (split-l x ++ᶜ split-r x) ᴱ
                 ++ᶜ ([] ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε'')))
        → (H [ x ↦ W ]cl) op ε''
        ≡ subst (_⊢C⦂ B ‼ (op-grade op ·ₑ ε'')) e
            ((H op ε'') [ split→∈ (split-++ʳ (∈-ᴱ-split et x)
                                    ([] ∷ type-of-gtype (param op)
                                        ∷ [ mapᵉ (op-grade op) ]
                                            (type-of-gtype (arity op) ⇒ B ‼ ε'')))
                          ↦ Wᴱ ([] ∷ type-of-gtype (param op)
                                   ∷ [ mapᵉ (op-grade op) ]
                                       (type-of-gtype (arity op) ⇒ B ‼ ε''))
                               et x W ]c)

cl-et-≡ {B = B} et x W H op ε'' e =
  trans (sym (C-sub-≐ˢ (restrict-sub-at-et D et x W e) (H op ε'')))
    (trans (C-sub₀-⌜⌝ (eq-ren e) X) (C-rename-eq-≡ e ≐ʳ-refl X))
  where
    D = [] ∷ type-of-gtype (param op)
           ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')

    X = (H op ε'') [ split→∈ (split-++ʳ (∈-ᴱ-split et x) D) ↦ Wᴱ D et x W ]c
