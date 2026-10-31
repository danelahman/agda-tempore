------------------------------------------------------------------------
-- The categorical structure of renamings.                            --
--                                                                    --
-- `Ren` is freely generated — `id-ren` and `_∘ʳ_` are constructors — --
-- so it is a graph, and `_≐ʳ_` is the quotient that makes it a       --
-- category. This module names that structure and the two functors    --
-- acting on it, so that the laws elsewhere can be read as instances  --
-- rather than as separate facts.                                     --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.Syntax.Renaming.Category (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts        Spec
open import MonomorphicCalculus.Syntax.Terms           Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming        Spec
open import MonomorphicCalculus.Syntax.Types           Spec

open import MonomorphicCalculus.Syntax.Renaming.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Renaming.Coherence    Spec
open import MonomorphicCalculus.Syntax.Terms.Equivalence     Spec

-- Objects are contexts, morphisms are `Ren [] Γ Γ'` taken up to `_≐ʳ_`. The
-- three laws hold by computation at the level of `var-img`:
--
--   `∘ʳ-assoc-≐ʳ`, `∘ʳ-identityˡ-≐ʳ`, `∘ʳ-identityʳ-≐ʳ`   (Equivalence)
--
-- `∘ʳ-≐ʳ` is composition's congruence, i.e. `_≐ʳ_` is a congruence for the
-- category structure. `var-img` is the faithful functor into the presheaf
-- of variables that defines the quotient.

-- `Ren Ξ Δ Δ'` is a morphism `Ξ ++ᶜ Δ → Ξ ++ᶜ Δ'` fixing `Ξ`: the family
-- `Ξ ↦ Ren Ξ` is an indexed category, each `Ξ` giving a category with the
-- same objects, reindexed by the two functors below. `Ren []` is the fibre
-- over the empty ambient.
--
-- Only two constructors read `Ξ`: `var-ren`, whose variable ranges over
-- `Ξ ⋈ᶜ Δ` (the ambient may be read, never rewritten), and `⟨⟩-ext-ctx`,
-- which also demands `EternalCtx Ξ` — the lock-introducing map exists only
-- over an eternal ambient.

-- Forgetting what a renaming fixes is the projection to the fibre over the
-- empty ambient. It is a functor *on the nose*: `expose-ren` sends `id-ren`
-- to `id-ren` and `_∘ʳ_` to `_∘ʳ_` by definition, so no quotient is needed.

expose-ren-[]-id : ∀ {Ξ Δ} → expose-ren-[] {Ξ} {Δ} id-ren ≡ id-ren
expose-ren-[]-id = refl

expose-ren-[]-∘ : ∀ {Ξ Δ Δ' Δ''}
                → (r₂ : Ren Ξ Δ' Δ'') → (r₁ : Ren Ξ Δ Δ')
                → expose-ren-[] (r₂ ∘ʳ r₁)
                ≡ expose-ren-[] r₂ ∘ʳ expose-ren-[] r₁
expose-ren-[]-∘ r₂ r₁ = refl

-- Extending the ambient on the left is the reindexing functor of the
-- indexing, and likewise strictly functorial. Its `EternalCtx` premise is
-- the obligation `⟨⟩-ext-ctx` incurs: the prefix, now standing to the left
-- of the lock, must be eternal too.

cong-renˡ-id : ∀ {Ξ Δ} → (Γ'' : Ctx) → (ec : EternalCtx Γ'')
             → cong-renˡ {Ξ} {Δ} Γ'' ec id-ren ≡ id-ren
cong-renˡ-id Γ'' ec = refl

cong-renˡ-∘ : ∀ {Ξ Δ Δ' Δ''} → (Γ'' : Ctx) → (ec : EternalCtx Γ'')
            → (r₂ : Ren Ξ Δ' Δ'') → (r₁ : Ren Ξ Δ Δ')
            → cong-renˡ Γ'' ec (r₂ ∘ʳ r₁)
            ≡ cong-renˡ Γ'' ec r₂ ∘ʳ cong-renˡ Γ'' ec r₁
cong-renˡ-∘ Γ'' ec r₂ r₁ = refl

-- Extending the *local* part on the right is the action of contexts on each
-- fibre. Unlike the two above it is functorial only up to `_≐ʳ_`, since
-- `cong-ren` recurses on the suffix and so does not commute with `_∘ʳ_` on
-- the nose: that is `cong-ren-∘-≐ʳ` and `cong-ren-id-≐ʳ` (Coherence).

-- `Γ ⊢V⦂ A` and `Γ ⊢C⦂ C` are presheaves on the category above. The action is
-- `V-rename`/`C-rename`; the laws are `V-rename-∘`, `V-rename-id-≡` (the
-- action respects the quotient on renamings) and `V-rename-cong`, and likewise
-- for `C`. Everything a term stores is either shape or a proof-irrelevant
-- bound, so the laws hold at `_≡_`.
--
-- Transport along a context equality is this action restricted to the
-- subgroupoid of equalities: `castᵛ e V ≡ V-rename (eq-ren e) V`
-- (`V-rename-eq-≡`), with `eq-ren` the functor from that subgroupoid
-- (`eq-ren-∘-≐ʳ`, `eq-ren-≐ʳ`).
