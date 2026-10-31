------------------------------------------------
-- Context renamings: the generating calculus --
------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum

open import Relation.Nullary

open import Grades.Base
open import Language.Spec

open import Util.Equality

module MonomorphicCalculus.Syntax.Renaming.Base (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import MonomorphicCalculus.Syntax.Contexts S
open import MonomorphicCalculus.Syntax.Types S

-- All-eternal, and lock-free apart from locks at a grade ≾-equivalent to the
-- unit. Interprets to a graded `⟨_⟩`-algebra (`𝟙ᵐ` and `×ᵐ` are eternal
-- objects, and `⟨ ρ ⟩ᵒ` is the identity up to isomorphism at a unit-equivalent
-- `ρ`).
--
-- A unit-equivalent lock is admissible rather than new: `⟨⟩-η-ren`/`⟨⟩-η⁻¹-ren`
-- and `⟨⟩-≤-ren` already move a context across it in both directions. Both
-- bounds are needed.

data EternalCtx : Ctx → Set where
  ec-[] : EternalCtx []
  ec-∷  : ∀ {Δ A} → EternalCtx Δ → Eternal A → EternalCtx (Δ ∷ A)
  ec-⟨⟩ : ∀ {Δ ρ} → uᵣ ≾ᵣ ρ → ρ ≾ᵣ uᵣ → EternalCtx Δ → EternalCtx (Δ ⟨ ρ ⟩)

-- The 0-graded lock, the case the two bounds are `≾ᵣ-refl`, and the case of a
-- grade only propositionally equal to the unit, which is the form the grades
-- standing in a context take (`of-durʳ-zero`, `map-uᵉ`).

ec-⟨⟩ᵘ : ∀ {Δ} → EternalCtx Δ → EternalCtx (Δ ⟨ uᵣ ⟩)
ec-⟨⟩ᵘ = ec-⟨⟩ ≾ᵣ-refl ≾ᵣ-refl

ec-⟨⟩≡ : ∀ {Δ ρ} → ρ ≡ uᵣ → EternalCtx Δ → EternalCtx (Δ ⟨ ρ ⟩)
ec-⟨⟩≡ e = ec-⟨⟩ (≾ᵣ-reflexive (sym e)) (≾ᵣ-reflexive e)

ec-eternal : ∀ {Δ A ρ} → EternalCtx Δ → A ∈[ ρ ] Δ → Eternal A
ec-eternal (ec-∷ ec et)   Hd        = et
ec-eternal (ec-∷ ec et)   (Tl-∷ x)  = ec-eternal ec x
ec-eternal (ec-⟨⟩ q p ec) (Tl-⟨⟩ x) = ec-eternal ec x

ec-++ᶜ : ∀ {Δ Δ'} → EternalCtx Δ → EternalCtx Δ' → EternalCtx (Δ ++ᶜ Δ')
ec-++ᶜ ec ec-[]           = ec
ec-++ᶜ ec (ec-∷ ec' et)   = ec-∷ (ec-++ᶜ ec ec') et
ec-++ᶜ ec (ec-⟨⟩ q p ec') = ec-⟨⟩ q p (ec-++ᶜ ec ec')

ec-split : ∀ {Δ} → (Δ' : Ctx) → EternalCtx (Δ ++ᶜ Δ')
         → EternalCtx Δ × EternalCtx Δ'
ec-split []         ec             = ec , ec-[]
ec-split (Δ' ∷ A)   (ec-∷ ec et)   =
  proj₁ (ec-split Δ' ec) , ec-∷ (proj₂ (ec-split Δ' ec)) et
ec-split (Δ' ⟨ ρ ⟩) (ec-⟨⟩ q p ec) =
  proj₁ (ec-split Δ' ec) , ec-⟨⟩ q p (proj₂ (ec-split Δ' ec))

-- Variable renamings (as the smallest relation closed under
-- identities, composition, congruences, ordinary variable
-- renamings, and strong monoidal functor structure for ⟨_⟩)
--
-- A `Ren Ξ Δ Δ'` is a morphism `Ξ ++ᶜ Δ → Ξ ++ᶜ Δ'` of contexts. The action on
-- terms is contravariant: it takes a `Ξ ++ᶜ Δ'`-term to a `Ξ ++ᶜ Δ`-term
-- (`V-rename`, `C-rename`).
--
-- Indexed by an ambient context `Ξ`, which the renaming fixes. Every rule acts
-- only at the top of the local part `Δ`, leaving the ambient untouched;
-- semantically, each is natural in `Ξ` (`⟨⟩-η-nat`, `εᵘ-nat`, `⟨⟩-μ-nat`,
-- `⟨⟩-≤-nat` are laws of the model).
--
-- The exception is `⟨⟩-ext-ctx`: it introduces a lock, the counit of `⟨ ρ ⟩`
-- at an arbitrary grade, available only via the `Eternalᵒ` algebra `extᵉ` of
-- an eternal object. It is the one map of the model carrying no naturality
-- law.

data Ren (Ξ : Ctx) : Ctx → Ctx → Set where
  -- identity renaming
  id-ren      : ∀ {Δ} → Ren Ξ Δ Δ
  -- composition of renamings
  _∘ʳ_        : ∀ {Δ Δ' Δ''} → Ren Ξ Δ' Δ'' → Ren Ξ Δ Δ' → Ren Ξ Δ Δ''
  -- weakening renaming (the projection off the top variable)
  wk-ren      : ∀ {Δ A} → Ren Ξ (Δ ∷ A) Δ
  -- variable renaming (corresponds to contraction). As in the `var` typing
  -- rule, the grade bound is only required for non-eternal types: an eternal
  -- variable is available at any grade (in particular behind a lock).
  var-ren     : ∀ {Δ A ρ} → (¬ Eternal A → ρ ≾ᵣ uᵣ) → A ∈[ ρ ] (Ξ ⋈ᶜ Δ)
              → Ren Ξ Δ (Δ ∷ A)
  -- strong monoidal functor renamings for ⟨_⟩ modality
  ⟨⟩-η-ren    : ∀ {Δ} → Ren Ξ Δ (Δ ⟨ uᵣ ⟩)
  ⟨⟩-η⁻¹-ren  : ∀ {Δ} → Ren Ξ (Δ ⟨ uᵣ ⟩) Δ
  ⟨⟩-μ-ren    : ∀ {Δ ρ ρ'} → Ren Ξ (Δ ⟨ ρ ⟩ ⟨ ρ' ⟩) (Δ ⟨ ρ ·ᵣ ρ' ⟩)
  -- monotonicity renaming for ⟨_⟩ modality
  ⟨⟩-≤-ren    : ∀ {Δ ρ ρ'} → ρ' ≾ᵣ ρ → Ren Ξ (Δ ⟨ ρ' ⟩) (Δ ⟨ ρ ⟩)
  -- introducing a lock: available when the context to its left, `Ξ ++ᶜ Δ`,
  -- is eternal (`ec-++ᶜ` assembles the two halves). The only rule that reads
  -- the ambient.
  ⟨⟩-ext-ctx  : ∀ {Δ ρ} → EternalCtx Ξ → EternalCtx Δ → Ren Ξ (Δ ⟨ ρ ⟩) Δ
  -- congruence renamings
  cong-∷-ren  : ∀ {Δ Δ' A} → Ren Ξ Δ Δ' → Ren Ξ (Δ ∷ A) (Δ' ∷ A)
  cong-⟨⟩-ren : ∀ {Δ Δ' ρ} → Ren Ξ Δ Δ' → Ren Ξ (Δ ⟨ ρ ⟩) (Δ' ⟨ ρ ⟩)

infixr 20 _∘ʳ_

-- Extending a renaming with a variable

extend-ren : ∀ {Ξ Δ Δ' A ρ} → Ren Ξ Δ Δ' → (¬ Eternal A → ρ ≾ᵣ uᵣ)
           → A ∈[ ρ ] (Ξ ⋈ᶜ Δ) → Ren Ξ Δ (Δ' ∷ A)
extend-ren r p x = cong-∷-ren r ∘ʳ var-ren p x

-- Equality renaming. It runs from `Δ'` to `Δ`, since the action on terms is
-- contravariant and `castᵛ e` transports a term forwards along `e`
-- (`V-rename-eq-≡`).

eq-ren : ∀ {Ξ Δ Δ'} → Δ ≡ Δ' → Ren Ξ Δ' Δ
eq-ren refl = id-ren

-- Congruence renamings for general context extension. Recursion on the suffix,
-- so the ambient is untouched.

cong-ren : ∀ {Ξ Δ Δ' Γ''} → Ren Ξ Δ Δ' → Ren Ξ (Δ ++ᶜ Γ'') (Δ' ++ᶜ Γ'')
cong-ren {Γ'' = []} r        = r
cong-ren {Γ'' = Γ'' ∷ A} r   = cong-∷-ren (cong-ren r)
cong-ren {Γ'' = Γ'' ⟨ ρ' ⟩} r = cong-⟨⟩-ren (cong-ren r)

-- Extending the ambient on the left. Only `⟨⟩-ext-ctx` constrains it: the
-- prefix, now standing to the left of the lock, must be eternal too.

cong-renˡ : ∀ {Ξ Δ Δ'} → (Γ'' : Ctx) → EternalCtx Γ''
          → Ren Ξ Δ Δ' → Ren (Γ'' ++ᶜ Ξ) Δ Δ'
cong-renˡ Γ'' ec'' id-ren =
  id-ren
cong-renˡ Γ'' ec'' (r₂ ∘ʳ r₁) =
  cong-renˡ Γ'' ec'' r₂ ∘ʳ cong-renˡ Γ'' ec'' r₁
cong-renˡ Γ'' ec'' wk-ren =
  wk-ren
cong-renˡ {Ξ} {Δ} Γ'' ec'' (var-ren p x) =
  var-ren p (subst (λ Γ₀ → _ ∈[ _ ] Γ₀)
              (trans (sym (++ᶜ-assoc Γ'' Ξ Δ)) (sym (⋈ᶜ-++ᶜ (Γ'' ++ᶜ Ξ) Δ)))
              (∈-ctx-extensionˡ Γ'' (Ξ ++ᶜ Δ)
                (subst (λ Γ₀ → _ ∈[ _ ] Γ₀) (⋈ᶜ-++ᶜ Ξ Δ) x)))
cong-renˡ Γ'' ec'' ⟨⟩-η-ren =
  ⟨⟩-η-ren
cong-renˡ Γ'' ec'' ⟨⟩-η⁻¹-ren =
  ⟨⟩-η⁻¹-ren
cong-renˡ Γ'' ec'' ⟨⟩-μ-ren =
  ⟨⟩-μ-ren
cong-renˡ Γ'' ec'' (⟨⟩-≤-ren x) =
  ⟨⟩-≤-ren x
cong-renˡ Γ'' ec'' (⟨⟩-ext-ctx ecΞ ecΔ) =
  ⟨⟩-ext-ctx (ec-++ᶜ ec'' ecΞ) ecΔ
cong-renˡ Γ'' ec'' (cong-∷-ren r) =
  cong-∷-ren (cong-renˡ Γ'' ec'' r)
cong-renˡ Γ'' ec'' (cong-⟨⟩-ren r) =
  cong-⟨⟩-ren (cong-renˡ Γ'' ec'' r)

-- Moving a prefix of the ambient into the local part: a reassociation between
-- the same two contexts, one-directional since fixing more implies fixing
-- less.
--
-- Only `var-ren` (whose variable ranges over the whole context) and
-- `⟨⟩-ext-ctx` (whose eternality obligation is split by `ec-split` and
-- reassembled by `ec-++ᶜ`) do any work; the rest reassociates definitionally.

expose-ren : ∀ {Ξ Δ₀ Δ₀'} → (Δ : Ctx) → Ren (Ξ ⋈ᶜ Δ) Δ₀ Δ₀'
           → Ren Ξ (Δ ++ᶜ Δ₀) (Δ ++ᶜ Δ₀')
expose-ren Δ id-ren =
  id-ren
expose-ren Δ (r₂ ∘ʳ r₁) =
  expose-ren Δ r₂ ∘ʳ expose-ren Δ r₁
expose-ren Δ wk-ren =
  wk-ren
expose-ren {Ξ} Δ (var-ren {Δ = Δ₀} p x) =
  var-ren p (subst (λ Γ₀ → _ ∈[ _ ] Γ₀) (⋈ᶜ-assoc Ξ Δ Δ₀) x)
expose-ren Δ ⟨⟩-η-ren =
  ⟨⟩-η-ren
expose-ren Δ ⟨⟩-η⁻¹-ren =
  ⟨⟩-η⁻¹-ren
expose-ren Δ ⟨⟩-μ-ren =
  ⟨⟩-μ-ren
expose-ren Δ (⟨⟩-≤-ren rel) =
  ⟨⟩-≤-ren rel
expose-ren {Ξ} Δ (⟨⟩-ext-ctx ec ecΔ₀) =
  ⟨⟩-ext-ctx (proj₁ ec-Ξ-Δ) (ec-++ᶜ (proj₂ ec-Ξ-Δ) ecΔ₀)
  where
    ec-Ξ-Δ = ec-split Δ (subst EternalCtx (⋈ᶜ-++ᶜ Ξ Δ) ec)
expose-ren Δ (cong-∷-ren r) =
  cong-∷-ren (expose-ren Δ r)
expose-ren Δ (cong-⟨⟩-ren r) =
  cong-⟨⟩-ren (expose-ren Δ r)

-- Viewing a renaming at the empty ambient, i.e. forgetting what it fixes. This
-- is what lets a renaming meet `unbox`'s certificate, which is stored there.

expose-ren-[] : ∀ {Ξ Δ Δ'} → Ren Ξ Δ Δ' → Ren [] (Ξ ++ᶜ Δ) (Ξ ++ᶜ Δ')
expose-ren-[] {Ξ} r = expose-ren Ξ r

-- Weakening a grade to a context renaming

wk-ren-⟨ρ⟩-ctx : ∀ {Δ Δ' ρ Ξ} → ctx-grade Δ' ≡ ρ → Ren Ξ (Δ ++ᶜ Δ') (Δ ⟨ ρ ⟩)
wk-ren-⟨ρ⟩-ctx {Δ' = []} refl =
  ⟨⟩-η-ren
wk-ren-⟨ρ⟩-ctx {Δ' = Δ' ∷ _} refl =
  wk-ren-⟨ρ⟩-ctx refl ∘ʳ wk-ren
wk-ren-⟨ρ⟩-ctx {Δ} {Δ' ⟨ ρ' ⟩} {ρ} {Ξ} refl =
  ⟨⟩-μ-ren ∘ʳ cong-⟨⟩-ren (wk-ren-⟨ρ⟩-ctx refl)

-- Exchange renaming

exch-ren : ∀ {Δ A B Ξ} → Ren Ξ (Δ ∷ A ∷ B) (Δ ∷ B ∷ A)
exch-ren {Ξ = Ξ} =
  extend-ren (cong-∷-ren wk-ren) (λ _ → ≾ᵣ-refl) (∈-⋈ᶜ Ξ (Tl-∷ Hd))

-- The barrier `⟨ ⊤ᵣ ⟩` guarding a handler's clauses, as renamings.
--
-- `barrier-ren` includes a clause's view of the ambient context into the
-- ambient itself. `barrier-wk-ren` re-bars a context extended by a lock and a
-- binder: `⊤ᵣ` is greatest, so the two locks fold into it.

barrier-ren : ∀ {Δ} → Ren [] Δ (Δ ⟨ ⊤ᵣ ⟩)
barrier-ren = ⟨⟩-≤-ren (≾-⊤ᵣ uᵣ) ∘ʳ ⟨⟩-η-ren

barrier-wk-ren : ∀ {Δ} → (ρ : R) → (A : VType)
               → Ren [] ((Δ ⟨ ρ ⟩ ∷ A) ⟨ ⊤ᵣ ⟩) (Δ ⟨ ⊤ᵣ ⟩)
barrier-wk-ren ρ A = ⟨⟩-≤-ren (≾-⊤ᵣ _) ∘ʳ ⟨⟩-μ-ren ∘ʳ cong-⟨⟩-ren wk-ren

-- Inserting a context `Γ'` immediately after the ambient, under an arbitrary
-- suffix `Θ`. Recursion on `Θ`, bottoming out in an insertion at the top; the
-- lock case uses `⟨⟩-ext-ctx`, requiring the ambient to be eternal.

wk-ctx-ren : ∀ {Ξ} → EternalCtx Ξ → (Γ' : Ctx) → Ren Ξ Γ' []
wk-ctx-ren ec []         = id-ren
wk-ctx-ren ec (Γ' ∷ A)   = wk-ren ∘ʳ cong-∷-ren (wk-ctx-ren ec Γ')
wk-ctx-ren ec (Γ' ⟨ ρ ⟩) = ⟨⟩-ext-ctx ec ec-[] ∘ʳ cong-⟨⟩-ren (wk-ctx-ren ec Γ')
