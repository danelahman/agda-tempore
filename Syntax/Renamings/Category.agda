------------------------------------------------------------------------
-- The categorical structure of renamings.                            --
--                                                                    --
-- `Ren` is freely generated — `id-ren` and `_∘ʳ_` are constructors —  --
-- so it is a graph, and `_≐ʳ_` is the quotient that makes it a       --
-- category. This module names that structure and the two functors    --
-- acting on it, so that the laws elsewhere can be read as instances   --
-- rather than as separate facts.                                      --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Renamings.Category (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   Spec
open import Syntax.Language   Spec
open import Syntax.RenActions Spec
open import Syntax.Renamings  Spec
open import Syntax.Types      Spec

open import Syntax.Renamings.Equivalence Spec
open import Syntax.Renamings.Coherence   Spec
open import Syntax.Terms.Equivalence     Spec

------------------------------------------------------------------------
-- THE CATEGORY OF RENAMINGS
--
-- Objects are contexts, morphisms are `Ren [] Γ Γ'` taken up to `_≐ʳ_`.
-- The three laws hold by computation at the level of `var-img`, which is
-- what makes this quotient the right one:
--
--   `∘ʳ-assoc-≐ʳ`, `∘ʳ-identityˡ-≐ʳ`, `∘ʳ-identityʳ-≐ʳ`   (Equivalence)
--
-- and `∘ʳ-≐ʳ` is composition's congruence, i.e. `_≐ʳ_` is a congruence for
-- the category structure. `var-img` itself is the faithful functor into
-- the presheaf of variables that defines the quotient.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- THE AMBIENT INDEXING
--
-- `Ren Ξ Δ Δ'` is a morphism `Ξ ++ᶜ Δ → Ξ ++ᶜ Δ'` fixing `Ξ`, so the
-- family `Ξ ↦ Ren Ξ` is an indexed category: each `Ξ` gives a category
-- with the same objects, and the ambient is reindexed by the two functors
-- below. `Ren []` is the fibre over the empty ambient.
--
-- Only two constructors read `Ξ` at all: `var-ren`, whose variable ranges
-- over `Ξ ⋈ᶜ Δ` (the ambient may be *read*, never rewritten), and
-- `⟨⟩-ext-ctx`, which additionally demands `EternalCtx Ξ`. So the fibres
-- are all alike except that the lock-introducing map exists only over an
-- eternal ambient — semantically, only there is `⟦ Ξ ⟧ᶜᵗˣ` a `⟨_⟩`-algebra.

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
-- the obligation `⟨⟩-ext-ctx` incurs: the prefix now stands to the left of
-- the lock, so it must be eternal too.

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

------------------------------------------------------------------------
-- THE ETERNAL RESTRICTION IS AN IDEMPOTENT MONAD
--
-- Object map `_ᴱ` (Contexts), morphism map `restrict-ren` (Renamings), and
-- unit `ᴱ-ren : Ren [] Γ (Γ ᴱ)`. The functor laws are `restrict-ren-∘-≐ʳ`,
-- `restrict-ren-id-≐ʳ` and `restrict-ren-≐ʳ`. What is proved here is the unit's
-- naturality, the one law the development used only in special cases.
------------------------------------------------------------------------

-- The inclusion acts on a variable as the reflection `∈-ᴱ⁻` does: both
-- recurse on the context with the entry's decision as a parameter, so the
-- clauses line up. This is what ties the renaming `ᴱ-ren` to the
-- variable-level reflection the naturality square is stated over.

ᴱ-ren-img : (Γ : Ctx) → ∀ {A ρ} → (x : A ∈[ ρ ] Γ ᴱ)
          → var-img (ᴱ-ren Γ) x ≡ ∈-ᴱ⁻ Γ x

ᴱ-ren-img-∷ : (Γ : Ctx) → (B : VType) → (d : Dec (Eternal B)) → ∀ {A ρ}
            → (x : A ∈[ ρ ] ᴱ-∷ (Γ ᴱ) B d)
            → var-img (ᴱ-ren-∷ {Γ} B d (ᴱ-ren Γ)) x ≡ ∈-ᴱ⁻-∷ Γ B d x

ᴱ-ren-img-∷ Γ B (yes _) Hd       = refl
ᴱ-ren-img-∷ Γ B (yes _) (Tl-∷ y) = cong Var-∷ (ᴱ-ren-img Γ y)
ᴱ-ren-img-∷ Γ B (no  _) x        = cong Var-∷ (ᴱ-ren-img Γ x)

ᴱ-ren-img []        ()
ᴱ-ren-img (Γ ∷ B)   x = ᴱ-ren-img-∷ Γ B (eternal? B) x
ᴱ-ren-img (Γ ⟨ ρ ⟩) x = cong (Var-⟨⟩ ρ) (ᴱ-ren-img Γ x)

-- NATURALITY OF THE UNIT
--
-- Including and then restricting is renaming and then including.
-- The content is `restrict-img⁻`, which is this square stated over `∈-ᴱ⁻`;
-- `ᴱ-ren-img` transports it to the renamings themselves.

ᴱ-ren-nat : ∀ {Γ Γ'} → (r : Ren [] Γ Γ')
          → (restrict-ren r ∘ʳ ᴱ-ren Γ) ≐ʳ (ᴱ-ren Γ' ∘ʳ r)
ᴱ-ren-nat {Γ} {Γ'} r = mk≐ʳ go
  where
    go : ∀ {A ρ} → (x : A ∈[ ρ ] Γ' ᴱ)
       → var-img (restrict-ren r ∘ʳ ᴱ-ren Γ) x ≡ var-img (ᴱ-ren Γ' ∘ʳ r) x
    go x =
      trans (ᴱ-ren-img Γ (proj₂ (var-img (restrict-ren r) x)))
        (trans (restrict-img⁻ r x)
               (cong (var-img′ r) (sym (ᴱ-ren-img Γ' x))))

------------------------------------------------------------------------
-- TERMS ARE PRESHEAVES
--
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
------------------------------------------------------------------------
