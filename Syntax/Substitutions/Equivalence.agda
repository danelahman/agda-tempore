------------------------------------------------------------------------
-- When two generating substitutions act alike.                       --
--                                                                    --
-- `Sub₀` is a free syntactic structure, so distinct generators can    --
-- put the same values in the same places. `_≐ˢ₀_` compares them by    --
-- what they do to a variable — as a value, and, at box type, as a     --
-- resource variable — and the action respects it.                     --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions.Equivalence (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.RenActions S
open import Syntax.Renamings  S
open import Syntax.Types      S

open import Syntax.Renamings.Equivalence S
open import Syntax.Renamings.Coherence   S
open import Syntax.Terms.Equivalence     S

open import Syntax.Substitutions   S

open import Syntax.Substitutions.Base   S
open import Syntax.Substitutions.Lookup S
open import Syntax.Substitutions.Action S

-- The grade bound a `var` carries is irrelevant, and so is the one handed to
-- the observation.

sub-var₀-irr : ∀ {Γ Γ' A ρ} → (s : Sub₀ [] Γ Γ') → (x : A ∈[ ρ ] Γ')
             → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
             → sub-var₀ s x f ≡ sub-var₀ s x f'
sub-var₀-irr s x f f' = cong (sub-var₀ s x) (bound-irr f f')

-- An eternal type discharges a grade bound whatever the grade.

et-bound : ∀ {A ρ} → Eternal A → ¬ Eternal A → ρ ≾ᵣ uᵣ
et-bound et ¬et = ⊥-elim (¬et et)

-- Two `var` nodes at the same image agree.

var-img-≡ : ∀ {Γ A} {t t' : Var Γ A} → t ≡ t'
          → (f  : ¬ Eternal A → proj₁ t  ≾ᵣ uᵣ)
          → (f' : ¬ Eternal A → proj₁ t' ≾ᵣ uᵣ)
          → var f (proj₂ t) ≡ var f' (proj₂ t')
var-img-≡ refl f f' = var-≡

-- Where a substitution sends a resource variable, forgetting the grade bound.
-- This is what an `unbox` node stores.

tgt-img₀ : ∀ {Γ Γ' A ρ ρ'} → Sub₀ [] Γ Γ' → [ ρ ] A ∈[ ρ' ] Γ' → RVar Γ
tgt-img₀ s y =
  tgt-grade₀ s y , tgt-type₀ s y , tgt-elapsed₀ s y , tgt-var₀ s y

infix 4 _≐ˢ₀_

-- A record, not a function type, for the same reason as `_≐ʳ_`: it is used at
-- substitutions Agda has to infer.
--
-- Two fields, because `atᵗ` is not derivable from `atᵛ`: a box-typed variable
-- has no `≾ᵣ uᵣ` bound, so it is never read as a value.

record _≐ˢ₀_ {Γ Γ'} (s s' : Sub₀ [] Γ Γ') : Set where
  constructor mk≐ˢ₀
  field
    atᵛ : ∀ {A ρ} → (x : A ∈[ ρ ] Γ') → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
        → sub-var₀ s x f ≡ sub-var₀ s' x f
    atᵗ : ∀ {A ρ ρ'} → (y : [ ρ ] A ∈[ ρ' ] Γ') → tgt-img₀ s y ≡ tgt-img₀ s' y

open _≐ˢ₀_ public

≐ˢ₀-refl : ∀ {Γ Γ'} {s : Sub₀ [] Γ Γ'} → s ≐ˢ₀ s
≐ˢ₀-refl = mk≐ˢ₀ (λ x f → refl) (λ y → refl)

≐ˢ₀-sym : ∀ {Γ Γ'} {s s' : Sub₀ [] Γ Γ'} → s ≐ˢ₀ s' → s' ≐ˢ₀ s
≐ˢ₀-sym h = mk≐ˢ₀ (λ x f → sym (atᵛ h x f)) (λ y → sym (atᵗ h y))

≐ˢ₀-trans : ∀ {Γ Γ'} {s s' s'' : Sub₀ [] Γ Γ'}
          → s ≐ˢ₀ s' → s' ≐ˢ₀ s'' → s ≐ˢ₀ s''
≐ˢ₀-trans h h' =
  mk≐ˢ₀ (λ x f → trans (atᵛ h x f) (atᵛ h' x f))
        (λ y → trans (atᵗ h y) (atᵗ h' y))

-- Unlike a renaming's, a substitution's image is a term: a congruence
-- weakens it (`∷`) or extends it past a lock (`⟨⟩`) rather than relocating
-- a variable, each a `cong` of the operation the clause applies.

cong-∷-sub-≐ˢ₀ : ∀ {Γ Γ' A} {s s' : Sub₀ [] Γ Γ'}
               → s ≐ˢ₀ s' → cong-∷-sub {A = A} s ≐ˢ₀ cong-∷-sub s'
cong-∷-sub-≐ˢ₀ h = mk≐ˢ₀ goᵛ goᵗ
  where
    goᵛ : ∀ {A' ρ'} → (x : A' ∈[ ρ' ] _) → (f : _) → _
    goᵛ Hd       f = refl
    goᵛ (Tl-∷ y) f = cong (V-rename wk-ren) (atᵛ h y f)

    goᵗ : ∀ {A' ρ ρ'} → (y : [ ρ ] A' ∈[ ρ' ] _) → _
    goᵗ Hd       = refl
    goᵗ (Tl-∷ y) = cong RVar-∷ (atᵗ h y)

-- Crossing a lock splits on the variable's eternality, but both sides split on
-- the same decision — the clause takes it as an argument.

cong-⟨⟩-sub-≐ˢ₀ : ∀ {Γ Γ' ρ} {s s' : Sub₀ [] Γ Γ'}
                → s ≐ˢ₀ s' → cong-⟨⟩-sub {ρ = ρ} s ≐ˢ₀ cong-⟨⟩-sub s'
cong-⟨⟩-sub-≐ˢ₀ {ρ = ρ} h = mk≐ˢ₀ goᵛ goᵗ
  where
    goᵛ : ∀ {A' ρ'} → (x : A' ∈[ ρ' ] _) → (f : _) → _
    goᵛ {A'} (Tl-⟨⟩ y) f with eternal? A'
    ... | yes et = cong (eternal-val-ext et) (atᵛ h y _)
    ... | no ¬et = cong (V-rename _) (atᵛ h y _)

    goᵗ : ∀ {A' ρ₀ ρ'} → (y : [ ρ₀ ] A' ∈[ ρ' ] _) → _
    goᵗ (Tl-⟨⟩ y) = cong (RVar-⟨⟩ ρ) (atᵗ h y)

cong-sub₀-≐ˢ₀ : ∀ {Γ Γ'} {s s' : Sub₀ [] Γ Γ'} → (Γ₀ : Ctx)
              → s ≐ˢ₀ s' → cong-sub₀ {Γ'' = Γ₀} s ≐ˢ₀ cong-sub₀ s'
cong-sub₀-≐ˢ₀ []         h = h
cong-sub₀-≐ˢ₀ (Γ₀ ∷ A)   h = cong-∷-sub-≐ˢ₀ (cong-sub₀-≐ˢ₀ Γ₀ h)
cong-sub₀-≐ˢ₀ (Γ₀ ⟨ ρ ⟩) h = cong-⟨⟩-sub-≐ˢ₀ (cong-sub₀-≐ˢ₀ Γ₀ h)

-- Renaming along an identity-like renaming is the transport.

V-rename-eq-≡ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {r : Ren [] Γ' Γ}
              → r ≐ʳ eq-ren e → (V : Γ ⊢V⦂ A)
              → V-rename r V ≡ subst (_⊢V⦂ A) e V
V-rename-eq-≡ refl h V = V-rename-id-≡ h V

-- Substitution respects the `≐ˢ₀` equivalence on substitutions.

mutual

  V-sub₀-≐ˢ₀ : ∀ {Γ Γ' A} {s s' : Sub₀ [] Γ Γ'} → s ≐ˢ₀ s'
             → (V : Γ' ⊢V⦂ A) → V-sub₀ s V ≡ V-sub₀ s' V

  V-sub₀-≐ˢ₀ h (var f x) = atᵛ h x f
  V-sub₀-≐ˢ₀ h (const c) = refl
  V-sub₀-≐ˢ₀ h ⋆         = refl
  V-sub₀-≐ˢ₀ h true      = refl
  V-sub₀-≐ˢ₀ h false     = refl
  V-sub₀-≐ˢ₀ h zero      = refl
  V-sub₀-≐ˢ₀ h (succ V)  = cong succ (V-sub₀-≐ˢ₀ h V)
  V-sub₀-≐ˢ₀ h ⦉ V , W ⦊  = cong₂ ⦉_,_⦊ (V-sub₀-≐ˢ₀ h V) (V-sub₀-≐ˢ₀ h W)
  V-sub₀-≐ˢ₀ h (inl V)   = cong inl (V-sub₀-≐ˢ₀ h V)
  V-sub₀-≐ˢ₀ h (inr V)   = cong inr (V-sub₀-≐ˢ₀ h V)
  V-sub₀-≐ˢ₀ h nil       = refl
  V-sub₀-≐ˢ₀ h (cons V W) = cong₂ cons (V-sub₀-≐ˢ₀ h V) (V-sub₀-≐ˢ₀ h W)
  V-sub₀-≐ˢ₀ h (lam M)   = cong lam (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ∷ _) h) M)
  V-sub₀-≐ˢ₀ h (subV V p) = subV-≡ (V-sub₀-≐ˢ₀ h V)

  C-sub₀-≐ˢ₀ : ∀ {Γ Γ' C} {s s' : Sub₀ [] Γ Γ'} → s ≐ˢ₀ s'
             → (M : Γ' ⊢C⦂ C) → C-sub₀ s M ≡ C-sub₀ s' M

  C-sub₀-≐ˢ₀ h (return V) = cong return (V-sub₀-≐ˢ₀ h V)
  C-sub₀-≐ˢ₀ h (M ⨟ N) =
    cong₂ _⨟_ (C-sub₀-≐ˢ₀ h M) (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-sub₀-≐ˢ₀ h (V · W) = cong₂ _·_ (V-sub₀-≐ˢ₀ h V) (V-sub₀-≐ˢ₀ h W)
  C-sub₀-≐ˢ₀ h (match V `in M) =
    cong₂ match_`in_ (V-sub₀-≐ˢ₀ h V) (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ∷ _ ∷ _) h) M)
  C-sub₀-≐ˢ₀ h (absurd V) = cong absurd (V-sub₀-≐ˢ₀ h V)
  C-sub₀-≐ˢ₀ h (cmp ⋈ V W et) =
    cong₂ (λ a b → cmp ⋈ a b et) (V-sub₀-≐ˢ₀ h V) (V-sub₀-≐ˢ₀ h W)
  C-sub₀-≐ˢ₀ h (if V `then M `else N) =
    cong₃ if_`then_`else_
      (V-sub₀-≐ˢ₀ h V) (C-sub₀-≐ˢ₀ h M) (C-sub₀-≐ˢ₀ h N)
  C-sub₀-≐ˢ₀ h (caseℕ V `zero M `succ N) =
    cong₃ caseℕ_`zero_`succ_ (V-sub₀-≐ˢ₀ h V) (C-sub₀-≐ˢ₀ h M)
      (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ∷ _) h) N)
  C-sub₀-≐ˢ₀ h (recℕ V M N p) =
    cong₃ (λ a b c → recℕ a b c p) (V-sub₀-≐ˢ₀ h V) (C-sub₀-≐ˢ₀ h M)
      (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ (([] ⟨ _ ⟩ ∷ Nat) ⟨ _ ⟩ ∷ _) h) N)
  C-sub₀-≐ˢ₀ h (caseL V `nil M `cons N) =
    cong₃ caseL_`nil_`cons_ (V-sub₀-≐ˢ₀ h V) (C-sub₀-≐ˢ₀ h M)
      (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ∷ _ ∷ _) h) N)
  C-sub₀-≐ˢ₀ h (recL V M N p) =
    cong₃ (λ a b c → recL a b c p) (V-sub₀-≐ˢ₀ h V) (C-sub₀-≐ˢ₀ h M)
      (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ (([] ⟨ _ ⟩ ∷ _ ∷ |List| _) ⟨ _ ⟩ ∷ _) h) N)
  C-sub₀-≐ˢ₀ h (case+ V `inl M `inr N) =
    cong₃ case+_`inl_`inr_ (V-sub₀-≐ˢ₀ h V)
      (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ∷ _) h) M)
      (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ∷ _) h) N)
  C-sub₀-≐ˢ₀ h (perform op V M) =
    cong₂ (perform _) (V-sub₀-≐ˢ₀ h V)
          (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ (_ ⟨ _ ⟩ ∷ _) h) M)
  C-sub₀-≐ˢ₀ h (delay τ M) =
    cong (delay _) (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ⟨ _ ⟩) h) M)
  C-sub₀-≐ˢ₀ h (handle M `with H `in N) =
    handle-≡ (C-sub₀-≐ˢ₀ h M)
      (λ op ε'' →
         C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ (_ ⟨ _ ⟩ ∷ _ ∷ _) h) (H op ε''))
      (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-sub₀-≐ˢ₀ h (unbox x rel p M) =
    unbox-≡ (atᵗ h x) (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ∷ _) h) M)
  C-sub₀-≐ˢ₀ h (box V M) =
    cong₂ box (V-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ⟨ _ ⟩) h) V)
              (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ∷ _) h) M)
  C-sub₀-≐ˢ₀ h (subC M p) = subC-≡ (C-sub₀-≐ˢ₀ h M)


eternal-val-ext-cong : ∀ {Γ A ρ} → (et : Eternal A) → {V V' : Γ ⊢V⦂ A}
                     → V ≡ V'
                     → eternal-val-ext {ρ = ρ} et V ≡ eternal-val-ext et V'
eternal-val-ext-cong et = cong (eternal-val-ext et)

substᶜ-≡ : ∀ {C Γ₁ Γ₂} → (e : Γ₁ ≡ Γ₂) → {M M' : Γ₁ ⊢C⦂ C}
         → M ≡ M' → subst (_⊢C⦂ C) e M ≡ subst (_⊢C⦂ C) e M'
substᶜ-≡ {C} e = cong (subst (_⊢C⦂ C) e)

substᶜ-≡′ : (f : Ctx → Ctx) → ∀ {C Γ₁ Γ₂} → (e : Γ₁ ≡ Γ₂) → {M M' : f Γ₁ ⊢C⦂ C}
          → M ≡ M'
          → subst (λ z → f z ⊢C⦂ C) e M ≡ subst (λ z → f z ⊢C⦂ C) e M'
substᶜ-≡′ f {C} e = cong (subst (λ z → f z ⊢C⦂ C) e)

sub-≡ᵛ : ∀ {Γ Γ₁ Γ₂ A B} → (s : Γ₁ ∷ A , Γ₂ split Γ) → {W W' : Γ₁ ⊢V⦂ A}
       → W ≡ W' → {V V' : Γ ⊢V⦂ B} → V ≡ V'
       → (V [ s ↦ W ]v) ≡ (V' [ s ↦ W' ]v)
sub-≡ᵛ s eW eV = cong₂ (λ U V₀ → V₀ [ s ↦ U ]v) eW eV

sub-≡ᶜ : ∀ {Γ Γ₁ Γ₂ A C} → (s : Γ₁ ∷ A , Γ₂ split Γ) → {W W' : Γ₁ ⊢V⦂ A}
       → W ≡ W' → {M M' : Γ ⊢C⦂ C} → M ≡ M'
       → (M [ s ↦ W ]c) ≡ (M' [ s ↦ W' ]c)
sub-≡ᶜ s eW eM = cong₂ (λ U M₀ → M₀ [ s ↦ U ]c) eW eM

