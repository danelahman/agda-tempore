-------------------------------------------------------------------------
-- Replacing one variable.                                             --
--                                                                     --
-- A notation, not a definition: replacing a single variable is the    --
-- generating substitution `val-sub` under the suffix that variable    --
-- stands over. That suffix is what a splitting names, so `sub-split₀` --
-- takes the splitting and recurses on it, and every single-variable   --
-- operator below is the general action at it.                         --
-------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.Syntax.Substitution (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming.Action S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Types           S

open import MonomorphicCalculus.Syntax.Substitution.Base    S
open import MonomorphicCalculus.Syntax.Substitution.Lookup  S
open import MonomorphicCalculus.Syntax.Substitution.Action  S

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
-- variable exactly as `sub-split₀` does on the splitting, so the two agree
-- definitionally (the `with` in `var-split` reduces by eta for `Σ`).

-- A prefix boundary names its own splitting too, `split-≡-++ᶜ`, whose halves
-- are the prefix and suffix as given. `≡-split` recurses on the suffix in step
-- with `sub-split₀`, so extending the suffix by a binder, resp. a lock, is
-- `cong-∷-sub`, resp. `cong-⟨⟩-sub`, again definitionally.

sub-atˢ₀ : ∀ {Γ B} → (Θ : Ctx) → Γ ⊢V⦂ B
         → Sub₀ [] (Γ ++ᶜ Θ) ((Γ ∷ B) ++ᶜ Θ)
sub-atˢ₀ {Γ} {B} Θ W = sub-split₀ (split-≡-++ᶜ {Γ ∷ B} {Θ}) W

-- Substituting a value at a splitting in a variable: looking the variable up.
-- The grade bound is the `var` rule's own premise, needed to build a
-- value out of a variable.

⟨_,_⟩[_↦_]var : ∀ {Γ Γ₁ Γ₂ A B ρ'}
              → B ∈[ ρ' ] Γ
              → (¬ Et B → ρ' ≾ᵣ 𝟏ᵣ)
              → (s : Γ₁ ∷ A , Γ₂ split Γ)
              → Γ₁ ⊢V⦂ A
              ---------------------------
              → Γ₁ ++ᶜ Γ₂ ⊢V⦂ B

⟨ y , f ⟩[ s ↦ W ]var = sub-var₀ (sub-split₀ s W) y f

-- Substituting in a resource variable, one of box type, as an `unbox` names. Its grade is not bounded by the unit, so it is not read
-- as a value; it does not have to be, a value of box type being a variable up
-- to subsumption.

⟨_⟩[_↦_]rvar : ∀ {Γ Γ₁ Γ₂ A B ρ σ}
             → ([ ρ ] B ∈[ σ ] Γ)
             → (s : Γ₁ ∷ A , Γ₂ split Γ)
             → Γ₁ ⊢V⦂ A
             ----------------------------------------------------------
             → Σ[ ρ₀ ∈ R ] Σ[ B₀ ∈ VType ] Σ[ σ' ∈ R ]
                 (([ ρ₀ ] B₀ ∈[ σ' ] (Γ₁ ++ᶜ Γ₂))
                   × (([ ρ₀ ] B₀) <:ᵛ ([ ρ ] B)) × (σ' ≾ᵣ σ))

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
              → Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                    ∷ [ ∣ op-grade op ∣ᵉ ]
                        (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                ⊢C⦂ B ! (op-grade op ·ₑ ε''))
         → (s : Γ₁ ∷ A , Γ₂ split Γ)
         → Γ₁ ⊢V⦂ A
         → (op : Op) → (ε'' : E)
         → (Γ₁ ++ᶜ Γ₂) ⟨ ⊤ᵣ ⟩
               ∷ ⌜ param op ⌝ᵍ
               ∷ [ ∣ op-grade op ∣ᵉ ]
                   (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
           ⊢C⦂ B ! (op-grade op ·ₑ ε'')

(H [ s ↦ W ]cl) op ε'' =
  C-sub₀ (cong-∷-sub (cong-∷-sub (cong-⟨⟩-sub (sub-split₀ s W))))
         (H op ε'')

-- One unfolding of a primitive recursion's step at a predecessor: the step's
-- view of the ambient context is included into the ambient itself (as a
-- handler clause's is when it fires), and the predecessor is substituted
-- across the lock binding the recursive call's result

recℕ-step : ∀ {Γ B ε}
          → Γ ⊢V⦂ nat
          → (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε
          ------------------------------------------
          → Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε
recℕ-step V N =
  C-rename (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren barrier-ren))) N
    [ split-∷ (split-⟨⟩ split-[]) ↦ V ]c

-- One unfolding of a list recursion's step at a head and a tail: as for
-- `recℕ-step`, the barred view is included into the ambient context, then the
-- head and the tail are substituted across the lock binding the recursive
-- call's result, the head first.

recL-step : ∀ {Γ A B ε}
          → Γ ⊢V⦂ A
          → Γ ⊢V⦂ list A
          → (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε
          ----------------------------------------------------
          → Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε
recL-step V W N =
  (C-rename (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren (cong-∷-ren barrier-ren)))) N
     [ split-∷ (split-⟨⟩ (split-∷ split-[])) ↦ V ]c)
     [ split-∷ (split-⟨⟩ split-[]) ↦ W ]c
