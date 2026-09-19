------------------------------------------------------------------------
-- Replacing one variable.                                             --
--                                                                     --
-- A notation, not a definition: replacing a single variable is the     --
-- generating substitution `val-sub` under the suffix that variable     --
-- stands over. That suffix is what a splitting names, so `sub-split₀`  --
-- takes the splitting and recurses on it, and every single-variable    --
-- operator below is the general action at it.                         --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.RenActions S
open import Syntax.Renamings  S
open import Syntax.Types      S

open import Syntax.Substitutions.Base      S
open import Syntax.Substitutions.Lookup    S
open import Syntax.Substitutions.Action    S

-- The substitution that replaces the entry a splitting names by `W`.
--
-- No transport appears: at the empty suffix `Γ₁ ++ᶜ []` is `Γ₁` and, at the
-- empty ambient, `[] ⋈ᶜ Γ₁` is `Γ₁`, so `val-sub` takes the value at the
-- splitting's left half as it stands. Each congruence extends both halves in
-- step, so the two ways of reading the result context agree throughout.

sub-split₀ : ∀ {Γ Γ₁ Γ₂ A} → Γ₁ ∷ A , Γ₂ split Γ → Γ₁ ⊢V⦂ A
           → Sub₀ [] (Γ₁ ++ᶜ Γ₂) Γ
sub-split₀ split-[]     W = val-sub W
sub-split₀ (split-∷ s)  W = cong-∷-sub (sub-split₀ s W)
sub-split₀ (split-⟨⟩ s) W = cong-⟨⟩-sub (sub-split₀ s W)

-- A variable names its own splitting, `split-pf`. `var-split` recurses on the
-- variable exactly as `sub-split₀` does on the splitting, so `split-l (Tl-∷ x)`
-- is `split-l x`, `split-pf (Tl-∷ x)` is `split-∷ (split-pf x)`, and hence
-- `sub-split₀ (split-pf (Tl-∷ x))` is `cong-∷-sub (sub-split₀ (split-pf x))` —
-- all definitionally (the `with` in `var-split` reduces by eta for `Σ`).

-- A prefix boundary names its own splitting too, `split-≡-++ᶜ`, whose halves
-- are the prefix and suffix as given. `≡-split` recurses on the suffix in step
-- with `sub-split₀`, so extending the suffix by a binder, resp. a lock, is
-- `cong-∷-sub`, resp. `cong-⟨⟩-sub` — again definitionally, which is what makes
-- the boundary substitution commute with the term formers on the nose.

sub-atˢ₀ : ∀ {Γ B} → (Θ : Ctx) → Γ ⊢V⦂ B
         → Sub₀ [] (Γ ++ᶜ Θ) ((Γ ∷ B) ++ᶜ Θ)
sub-atˢ₀ {Γ} {B} Θ W = sub-split₀ (split-≡-++ᶜ {Γ ∷ B} {Θ}) W

-- Substituting a value at a splitting in a variable, i.e. looking the variable
-- up. The grade bound is the `var` rule's own premise, which is what building a
-- *value* out of a variable needs.

⟨_,_⟩[_↦_]var : ∀ {Γ Γ₁ Γ₂ A B ρ'}
              → B ∈[ ρ' ] Γ
              → (¬ Eternal B → ρ' ≾ᵣ uᵣ)
              → (s : Γ₁ ∷ A , Γ₂ split Γ)
              → Γ₁ ⊢V⦂ A
              ---------------------------
              → Γ₁ ++ᶜ Γ₂ ⊢V⦂ B

⟨ y , f ⟩[ s ↦ W ]var = sub-var₀ (sub-split₀ s W) y f

-- Substituting in a *resource* variable, i.e. one of box type, which is what
-- an `unbox` names. Its grade is not bounded by the unit — that is exactly what
-- `unbox` is for — so it is not read as a value; it does not have to be, box
-- types having only variables as values.

⟨_⟩[_↦_]rvar : ∀ {Γ Γ₁ Γ₂ A B ρ σ}
             → ([ ρ ] B ∈[ σ ] Γ)
             → (s : Γ₁ ∷ A , Γ₂ split Γ)
             → Γ₁ ⊢V⦂ A
             ----------------------------------------------------------
             → Σ[ σ' ∈ R ] (([ ρ ] B ∈[ σ' ] (Γ₁ ++ᶜ Γ₂)) × (σ' ≾ᵣ σ))

⟨ y ⟩[ s ↦ W ]rvar = sub-tgt₀ (sub-split₀ s W) y

-- Substituting a value at a splitting in a well-typed term.

_[_↦_]v : ∀ {Γ Γ₁ Γ₂ A B}
        → Γ ⊢V⦂ B
        → (s : Γ₁ ∷ A , Γ₂ split Γ)
        → Γ₁ ⊢V⦂ A
        ---------------------------
        → Γ₁ ++ᶜ Γ₂ ⊢V⦂ B

V [ s ↦ W ]v = V-sub₀ (sub-split₀ s W) V

_[_↦_]c : ∀ {Γ Γ₁ Γ₂ A C}
        → Γ ⊢C⦂ C
        → (s : Γ₁ ∷ A , Γ₂ split Γ)
        → Γ₁ ⊢V⦂ A
        ---------------------------
        → Γ₁ ++ᶜ Γ₂ ⊢C⦂ C

M [ s ↦ W ]c = C-sub₀ (sub-split₀ s W) M

-- and in a handler's clause family, which sits under the barrier lock
-- `⟨ ⊤ᵣ ⟩` and two binders. That is an ordinary suffix, so the clause
-- substitution is the general one at it.

_[_↦_]cl : ∀ {Γ Γ₁ Γ₂ A B}
         → ((op : Op) → (ε'' : E)
              → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                    ∷ [ mapᵉ (op-grade op) ]
                        (type-of-gtype (arity op) ⇒ B ‼ ε'')
                ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
         → (s : Γ₁ ∷ A , Γ₂ split Γ)
         → Γ₁ ⊢V⦂ A
         → (op : Op) → (ε'' : E)
         → (Γ₁ ++ᶜ Γ₂) ⟨ ⊤ᵣ ⟩
               ∷ type-of-gtype (param op)
               ∷ [ mapᵉ (op-grade op) ]
                   (type-of-gtype (arity op) ⇒ B ‼ ε'')
           ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')

(H [ s ↦ W ]cl) op ε'' =
  C-sub₀ (cong-∷-sub (cong-∷-sub (cong-⟨⟩-sub (sub-split₀ s W))))
         (H op ε'')
