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

-- Substituting a value for a variable in a variable, i.e. looking the variable
-- up. The grade bound is the `var` rule's own premise, which is what building a
-- *value* out of a variable needs.

⟨_,_⟩[_↦_]var : ∀ {Γ A B ρ ρ'}
              → B ∈[ ρ' ] Γ
              → (¬ Eternal B → ρ' ≾ᵣ uᵣ)
              → (x : A ∈[ ρ ] Γ)
              → split-l x ⊢V⦂ A
              -------------------------------
              → split-l x ++ᶜ split-r x ⊢V⦂ B

⟨ y , f ⟩[ x ↦ W ]var = sub-var₀ (sub-split₀ (split-pf x) W) y f

-- Substituting in a *resource* variable, i.e. one of box type, which is what
-- an `unbox` names. Its grade is not bounded by the unit — that is exactly what
-- `unbox` is for — so it is not read as a value; it does not have to be, box
-- types having only variables as values.

⟨_⟩[_↦_]rvar : ∀ {Γ A B ρ σ τ}
             → ([ ρ ] B ∈[ σ ] Γ)
             → (x : A ∈[ τ ] Γ)
             → split-l x ⊢V⦂ A
             ----------------------------------------------------------------
             → Σ[ σ' ∈ R ]
                 (([ ρ ] B ∈[ σ' ] (split-l x ++ᶜ split-r x)) × (σ' ≾ᵣ σ))

⟨ y ⟩[ x ↦ W ]rvar = sub-tgt₀ (sub-split₀ (split-pf x) W) y

-- Substituting a value for a variable in a well-typed term.

_[_↦_]v : ∀ {Γ A B ρ}
        → Γ ⊢V⦂ B
        → (x : A ∈[ ρ ] Γ)
        → split-l x ⊢V⦂ A
        -------------------------------
        → split-l x ++ᶜ split-r x ⊢V⦂ B

V [ x ↦ W ]v = V-sub₀ (sub-split₀ (split-pf x) W) V

_[_↦_]c : ∀ {Γ A C ρ}
        → Γ ⊢C⦂ C
        → (x : A ∈[ ρ ] Γ)
        → split-l x ⊢V⦂ A
        -------------------------------
        → split-l x ++ᶜ split-r x ⊢C⦂ C

M [ x ↦ W ]c = C-sub₀ (sub-split₀ (split-pf x) W) M

-- and in a handler's clause family, which closes over the eternal part `Γ ᴱ`
-- of the context. The substitution restricts to it (`restrict-sub₀`), which is
-- what drops the substituted variable when its type is not eternal and keeps
-- its restricted value when it is.

_[_↦_]cl : ∀ {Γ A B ρ}
         → ((op : Op) → (ε'' : E)
              → Γ ᴱ ∷ type-of-gtype (param op)
                    ∷ [ mapᵉ (op-grade op) ]
                        (type-of-gtype (arity op) ⇒ B ‼ ε'')
                ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
         → (x : A ∈[ ρ ] Γ)
         → split-l x ⊢V⦂ A
         → (op : Op) → (ε'' : E)
         → (split-l x ++ᶜ split-r x) ᴱ
               ∷ type-of-gtype (param op)
               ∷ [ mapᵉ (op-grade op) ]
                   (type-of-gtype (arity op) ⇒ B ‼ ε'')
           ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')

(H [ x ↦ W ]cl) op ε'' =
  C-sub₀ (cong-∷-sub (cong-∷-sub (restrict-sub₀ (sub-split₀ (split-pf x) W))))
         (H op ε'')
