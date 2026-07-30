------------------------------------------------------------------------
-- The syntactic equivalence is contained in the equational theory.    --
--                                                                    --
-- `_≐ᵛ_`/`_≐ᶜ_` are propositional equality of terms, and `_==_` is    --
-- reflexive, so the inclusion is one line each way round the mutual   --
-- pair. The converse fails, and should: `_==_` has the βη axioms.     --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module EquationalTheory.Alignment (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.RenActions    S
open import Syntax.Renamings     S
open import Syntax.Substitutions S
open import Syntax.Types         S

open import Syntax.Terms.Equivalence S

open import EquationalTheory.EquationalTheory S

≐ᵛ→== : ∀ {Γ A} {V V' : Γ ⊢V⦂ A} → V ≐ᵛ V' → Γ ⊢V⦂ V == V'
≐ᵛ→== refl = V-refl

≐ᶜ→== : ∀ {Γ C} {M M' : Γ ⊢C⦂ C} → M ≐ᶜ M' → Γ ⊢C⦂ M == M'
≐ᶜ→== refl = C-refl
