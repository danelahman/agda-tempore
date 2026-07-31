------------------------------------------------------------------------
-- Replacing one variable.                                             --
--                                                                     --
-- A notation, not a definition: replacing a single variable is the     --
-- generating substitution `val-sub` under the suffix that variable     --
-- stands over, and `var-split` builds exactly that suffix. So          --
-- `sub-at₀` recurses on the variable, mirroring the splitting, and     --
-- every single-variable operator below is the general action at it.    --
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

-- The substitution that replaces `x` by `W`.
--
-- No transport appears: `var-split` recurses on the variable exactly as this
-- does, so `split-l (Tl-∷ x)` is `split-l x` and `split-r (Tl-∷ x)` is
-- `split-r x ∷ B`, definitionally (the `with` in `var-split` reduces by eta
-- for `Σ`). At the empty ambient `[] ⋈ᶜ Γ` is `Γ`, so `val-sub` takes the
-- value at the splitting's left half as it stands.

sub-at₀ : ∀ {Γ A ρ} → (x : A ∈[ ρ ] Γ) → split-l x ⊢V⦂ A
        → Sub₀ [] (split-l x ++ᶜ split-r x) Γ
sub-at₀ Hd        W = val-sub W
sub-at₀ (Tl-∷ x)  W = cong-∷-sub (sub-at₀ x W)
sub-at₀ (Tl-⟨⟩ x) W = cong-⟨⟩-sub (sub-at₀ x W)

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

⟨ y , f ⟩[ x ↦ W ]var = sub-var₀ (sub-at₀ x W) y f

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

⟨ y ⟩[ x ↦ W ]rvar = sub-tgt₀ (sub-at₀ x W) y

-- Substituting a value for a variable in a well-typed term.

_[_↦_]v : ∀ {Γ A B ρ}
        → Γ ⊢V⦂ B
        → (x : A ∈[ ρ ] Γ)
        → split-l x ⊢V⦂ A
        -------------------------------
        → split-l x ++ᶜ split-r x ⊢V⦂ B

V [ x ↦ W ]v = V-sub₀ (sub-at₀ x W) V

_[_↦_]c : ∀ {Γ A C ρ}
        → Γ ⊢C⦂ C
        → (x : A ∈[ ρ ] Γ)
        → split-l x ⊢V⦂ A
        -------------------------------
        → split-l x ++ᶜ split-r x ⊢C⦂ C

M [ x ↦ W ]c = C-sub₀ (sub-at₀ x W) M

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
  C-sub₀ (cong-∷-sub (cong-∷-sub (restrict-sub₀ (sub-at₀ x W)))) (H op ε'')
