------------------------------------------------------
-- Parallel substitutions: the generating calculus   --
------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Grades.Base
open import Language.Spec

open import Util.Equality

module ClosedCalculus.Syntax.Substitutions.Base (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import ClosedCalculus.Syntax.Contexts  S
open import ClosedCalculus.Syntax.Terms     S
open import ClosedCalculus.Syntax.Renamings S
open import Language.Types                  S

-- A `Sub₀ Ξ Δ Δ'` is a morphism `Ξ ++ᶜ Δ → Ξ ++ᶜ Δ'`, so, as for `Ren`, the
-- indices run in the direction of the map and the action on terms is
-- contravariant: it takes a `Ξ ++ᶜ Δ'`-term to a `Ξ ++ᶜ Δ`-term.
--
-- The generators are `Ren`'s, with `var-ren` relaxed from a variable to a value
-- and the remaining eight reached through the embedding `⌜_⌝`. A renaming is
-- therefore a substitution that happens to put variables in for variables.
--
-- There is no composition generator: `sub-var₀` and the term action admit no
-- shared recursion order. Composition is instead taken freely one layer up
-- (`Substitutions.Chain`), where it is a list and neither recursion sees it.
--
-- The two congruences must be generators: `val-sub` only ever produces a target
-- of shape `Δ ∷ A` from source `Δ`, so neither can be defined by recursion.

data Sub₀ (Ξ : Ctx) : Ctx → Ctx → Set where
  -- a renaming, viewed as a substitution
  ⌜_⌝         : ∀ {Δ Δ'} → Ren Ξ Δ Δ' → Sub₀ Ξ Δ Δ'
  -- extension by a value. The value lives over the whole context, joined with
  -- `⋈ᶜ` so that the empty ambient reduces, exactly as in `var-ren`.
  val-sub     : ∀ {Δ A} → (Ξ ⋈ᶜ Δ) ⊢V⦂ A → Sub₀ Ξ Δ (Δ ∷ A)
  -- congruence substitutions
  cong-∷-sub  : ∀ {Δ Δ' A} → Sub₀ Ξ Δ Δ' → Sub₀ Ξ (Δ ∷ A) (Δ' ∷ A)
  cong-⟨⟩-sub : ∀ {Δ Δ' ρ} → Sub₀ Ξ Δ Δ' → Sub₀ Ξ (Δ ⟨ ρ ⟩) (Δ' ⟨ ρ ⟩)

-- The identity, and the equality substitution, inherited from the renamings.

id-sub₀ : ∀ {Ξ Δ} → Sub₀ Ξ Δ Δ
id-sub₀ = ⌜ id-ren ⌝

-- Congruence for a general context extension. Recursion on the suffix, so the
-- ambient is untouched.

cong-sub₀ : ∀ {Ξ Δ Δ' Γ''} → Sub₀ Ξ Δ Δ' → Sub₀ Ξ (Δ ++ᶜ Γ'') (Δ' ++ᶜ Γ'')
cong-sub₀ {Γ'' = []}        s = s
cong-sub₀ {Γ'' = Γ'' ∷ A}   s = cong-∷-sub (cong-sub₀ s)
cong-sub₀ {Γ'' = Γ'' ⟨ ρ ⟩} s = cong-⟨⟩-sub (cong-sub₀ s)

-- Moving a prefix of the ambient into the local part. As for renamings this is
-- a reassociation, and only the value-carrying rule does any work.

expose-sub₀ : ∀ {Ξ Δ₀ Δ₀'} → (Δ : Ctx) → Sub₀ (Ξ ⋈ᶜ Δ) Δ₀ Δ₀'
            → Sub₀ Ξ (Δ ++ᶜ Δ₀) (Δ ++ᶜ Δ₀')
expose-sub₀ Δ ⌜ r ⌝ =
  ⌜ expose-ren Δ r ⌝
expose-sub₀ {Ξ} Δ (val-sub {Δ₀} {A} V) =
  val-sub (subst (_⊢V⦂ A) (⋈ᶜ-assoc Ξ Δ Δ₀) V)
expose-sub₀ Δ (cong-∷-sub s) =
  cong-∷-sub (expose-sub₀ Δ s)
expose-sub₀ Δ (cong-⟨⟩-sub s) =
  cong-⟨⟩-sub (expose-sub₀ Δ s)

-- Viewing a substitution at the empty ambient, which is where the action lives.

expose-sub₀-[] : ∀ {Ξ Δ Δ'} → Sub₀ Ξ Δ Δ' → Sub₀ [] (Ξ ++ᶜ Δ) (Ξ ++ᶜ Δ')
expose-sub₀-[] {Ξ} s = expose-sub₀ Ξ s
