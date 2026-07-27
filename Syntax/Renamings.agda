-----------------------
-- Context renamings --
-----------------------

open import Data.Empty
open import Data.Product
open import Data.Sum

open import Relation.Nullary

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

module Syntax.Renamings (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Contexts S
open import Syntax.Types     S

-- ETERNAL CONTEXTS
--
-- Lock-free and all-eternal. Interprets to a graded `⟨_⟩`-algebra (`𝟙ᵐ` and
-- `×ᵐ` are eternal objects), which is what a lock-introducing renaming needs of
-- the context standing to its left.

data EternalCtx : Ctx → Set where
  ec-[] : EternalCtx []
  ec-∷  : ∀ {Δ A} → EternalCtx Δ → Eternal A → EternalCtx (Δ ∷ A)

ec-eternal : ∀ {Δ A ρ} → EternalCtx Δ → A ∈[ ρ ] Δ → Eternal A
ec-eternal (ec-∷ ec et) Hd       = et
ec-eternal (ec-∷ ec et) (Tl-∷ x) = ec-eternal ec x

ec-++ᶜ : ∀ {Δ Δ'} → EternalCtx Δ → EternalCtx Δ' → EternalCtx (Δ ++ᶜ Δ')
ec-++ᶜ ec ec-[]         = ec
ec-++ᶜ ec (ec-∷ ec' et) = ec-∷ (ec-++ᶜ ec ec') et

ec-split : ∀ {Δ} → (Δ' : Ctx) → EternalCtx (Δ ++ᶜ Δ')
         → EternalCtx Δ × EternalCtx Δ'
ec-split []         ec           = ec , ec-[]
ec-split (Δ' ∷ A)   (ec-∷ ec et) =
  proj₁ (ec-split Δ' ec) , ec-∷ (proj₂ (ec-split Δ' ec)) et
ec-split (Δ' ⟨ ρ ⟩) ()

-- Variable renamings (as the smallest relation closed under
-- identities, composition, congruences, ordinary variable
-- renamings, and strong monoidal functor structure for ⟨_⟩)
--
-- Indexed by an AMBIENT context `Ξ`: `Ren Ξ Δ Δ'` renames `Ξ ++ᶜ Δ` into
-- `Ξ ++ᶜ Δ'`. Every rule acts only at the top of the local part `Δ`, carrying
-- the ambient untouched — semantically, each is natural in `Ξ` (`⟨⟩-η-nat`,
-- `εᵘ-nat`, `⟨⟩-μ-nat`, `⟨⟩-≤-nat` are laws of the model, and `strᵉ`'s
-- naturality is derivable there).
--
-- The exception, and the reason for the index, is `⟨⟩-ext-ctx`: it introduces a
-- lock, i.e. is the *counit* of `⟨ ρ ⟩` at an arbitrary grade. `⟨ ρ ⟩` has no
-- such counit in general — only the `Eternalᵒ` algebra `extᵉ` of an eternal
-- object does, which is why it alone constrains the ambient. Correspondingly it
-- is the one map of the model carrying no naturality law.

data Ren (Ξ : Ctx) : Ctx → Ctx → Set where
  -- identity renaming
  id-ren      : ∀ {Δ} → Ren Ξ Δ Δ
  -- composition of renamings
  _∘ʳ_        : ∀ {Δ Δ' Δ''} → Ren Ξ Δ' Δ'' → Ren Ξ Δ Δ' → Ren Ξ Δ Δ''
  -- weakening renaming
  wk-ren      : ∀ {Δ A} → Ren Ξ Δ (Δ ∷ A)
  -- variable renaming (corresponds to contraction). As in the `var` typing
  -- rule, the grade bound is only required for non-eternal types: an eternal
  -- variable is available at any grade (in particular behind a lock).
  var-ren     : ∀ {Δ A ρ} → (¬ Eternal A → ρ ≾ᵣ uᵣ) → A ∈[ ρ ] (Ξ ⋈ᶜ Δ)
              → Ren Ξ (Δ ∷ A) Δ
  -- strong monoidal functor renamings for ⟨_⟩ modality
  ⟨⟩-η-ren    : ∀ {Δ} → Ren Ξ (Δ ⟨ uᵣ ⟩) Δ
  ⟨⟩-η⁻¹-ren  : ∀ {Δ} → Ren Ξ Δ (Δ ⟨ uᵣ ⟩)
  ⟨⟩-μ-ren    : ∀ {Δ ρ ρ'} → Ren Ξ (Δ ⟨ ρ ·ᵣ ρ' ⟩) (Δ ⟨ ρ ⟩ ⟨ ρ' ⟩)
  -- monotonicity renaming for ⟨_⟩ modality
  ⟨⟩-≤-ren    : ∀ {Δ ρ ρ'} → ρ' ≾ᵣ ρ → Ren Ξ (Δ ⟨ ρ ⟩) (Δ ⟨ ρ' ⟩)
  -- moving an eternal variable out of a lock: an eternal value is available at
  -- the past world a `⟨ ρ ⟩` bundle already witnesses, so it can be extruded
  -- past the lock. Semantically the `⟨_⟩`-strength against an eternal object.
  ⟨⟩-ext-ren  : ∀ {Δ A ρ} → Eternal A
              → Ren Ξ ((Δ ∷ A) ⟨ ρ ⟩) ((Δ ⟨ ρ ⟩) ∷ A)
  -- introducing a lock: the counit of `⟨ ρ ⟩` at an arbitrary grade, available
  -- exactly when everything to the lock's left is eternal, since `⟦_⟧ᶜᵗˣ` of
  -- such a context is a `⟨_⟩`-algebra and `extᵉ` is that counit. The context to
  -- the left is `Ξ ++ᶜ Δ`, so both halves are asked for (`ec-++ᶜ` assembles
  -- them). The only rule that reads the ambient.
  ⟨⟩-ext-ctx  : ∀ {Δ ρ} → EternalCtx Ξ → EternalCtx Δ → Ren Ξ Δ (Δ ⟨ ρ ⟩)
  -- congruence renamings
  cong-∷-ren  : ∀ {Δ Δ' A} → Ren Ξ Δ Δ' → Ren Ξ (Δ ∷ A) (Δ' ∷ A)
  cong-⟨⟩-ren : ∀ {Δ Δ' ρ} → Ren Ξ Δ Δ' → Ren Ξ (Δ ⟨ ρ ⟩) (Δ' ⟨ ρ ⟩)

infixr 20 _∘ʳ_

-- Extending a renaming with a variable

extend-ren : ∀ {Ξ Δ Δ' A ρ} → Ren Ξ Δ Δ' → (¬ Eternal A → ρ ≾ᵣ uᵣ)
           → A ∈[ ρ ] (Ξ ⋈ᶜ Δ') → Ren Ξ (Δ ∷ A) Δ'
extend-ren ρ p x = var-ren p x ∘ʳ cong-∷-ren ρ

-- Equality renaming

eq-ren : ∀ {Ξ Δ Δ'} → Δ ≡ Δ' → Ren Ξ Δ Δ'
eq-ren refl = id-ren

-- Combination of congruence and monotonicity renamings

cong-⟨⟩-≤-ren : ∀ {Ξ Δ Δ' ρ ρ'} → Ren Ξ Δ Δ' → ρ' ≾ᵣ ρ
              → Ren Ξ (Δ ⟨ ρ ⟩) (Δ' ⟨ ρ' ⟩)
cong-⟨⟩-≤-ren id-ren ρ'≾ρ =
  ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren (r₂ ∘ʳ r₁) ρ'≾ρ =
  cong-⟨⟩-≤-ren r₂ ρ'≾ρ ∘ʳ cong-⟨⟩-ren r₁
cong-⟨⟩-≤-ren wk-ren ρ'≾ρ =
  cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren (var-ren p x) ρ'≾ρ =
  cong-⟨⟩-ren (var-ren p x) ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren ⟨⟩-η-ren ρ'≾ρ =
  cong-⟨⟩-ren ⟨⟩-η-ren ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren ⟨⟩-η⁻¹-ren ρ'≾ρ =
  cong-⟨⟩-ren ⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren ⟨⟩-μ-ren ρ'≾ρ =
  cong-⟨⟩-ren ⟨⟩-μ-ren ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren (⟨⟩-≤-ren rel) ρ'≾ρ =
  cong-⟨⟩-ren (⟨⟩-≤-ren rel) ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren (cong-∷-ren r) ρ'≾ρ =
  cong-⟨⟩-ren (cong-∷-ren r) ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren (cong-⟨⟩-ren r) ρ'≾ρ =
  cong-⟨⟩-ren (cong-⟨⟩-ren r) ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren (⟨⟩-ext-ren et) ρ'≾ρ =
  cong-⟨⟩-ren (⟨⟩-ext-ren et) ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren (⟨⟩-ext-ctx ecΞ ecΔ) ρ'≾ρ =
  cong-⟨⟩-ren (⟨⟩-ext-ctx ecΞ ecΔ) ∘ʳ ⟨⟩-≤-ren ρ'≾ρ

-- Congruence renamings for general context extension. Recursion on the suffix,
-- so the ambient is untouched.

cong-ren : ∀ {Ξ Δ Δ' Γ''} → Ren Ξ Δ Δ' → Ren Ξ (Δ ++ᶜ Γ'') (Δ' ++ᶜ Γ'')
cong-ren {Γ'' = []} r        = r
cong-ren {Γ'' = Γ'' ∷ A} r   = cong-∷-ren (cong-ren r)
cong-ren {Γ'' = Γ'' ⟨ ρ' ⟩} r = cong-⟨⟩-ren (cong-ren r)

-- Extending the *ambient* on the left. Only `⟨⟩-ext-ctx` constrains it, and
-- there the obligation is genuine: the prefix now stands to the left of the
-- lock, so it must be eternal too.

cong-renˡ : ∀ {Ξ Δ Δ'} → (Γ'' : Ctx) → EternalCtx Γ''
          → Ren Ξ Δ Δ' → Ren (Γ'' ++ᶜ Ξ) Δ Δ'
cong-renˡ Γ'' ec'' id-ren =
  id-ren
cong-renˡ Γ'' ec'' (r₂ ∘ʳ r₁) =
  cong-renˡ Γ'' ec'' r₂ ∘ʳ cong-renˡ Γ'' ec'' r₁
cong-renˡ Γ'' ec'' wk-ren =
  wk-ren
cong-renˡ {Ξ} {Δ' = Δ'} Γ'' ec'' (var-ren p x) =
  var-ren p (subst (λ Γ₀ → _ ∈[ _ ] Γ₀)
              (trans (sym (++ᶜ-assoc Γ'' Ξ Δ')) (sym (⋈ᶜ-++ᶜ (Γ'' ++ᶜ Ξ) Δ')))
              (∈-ctx-extensionˡ Γ'' (Ξ ++ᶜ Δ')
                (subst (λ Γ₀ → _ ∈[ _ ] Γ₀) (⋈ᶜ-++ᶜ Ξ Δ') x)))
cong-renˡ Γ'' ec'' ⟨⟩-η-ren =
  ⟨⟩-η-ren
cong-renˡ Γ'' ec'' ⟨⟩-η⁻¹-ren =
  ⟨⟩-η⁻¹-ren
cong-renˡ Γ'' ec'' ⟨⟩-μ-ren =
  ⟨⟩-μ-ren
cong-renˡ Γ'' ec'' (⟨⟩-≤-ren x) =
  ⟨⟩-≤-ren x
cong-renˡ Γ'' ec'' (⟨⟩-ext-ren et) =
  ⟨⟩-ext-ren et
cong-renˡ Γ'' ec'' (⟨⟩-ext-ctx ecΞ ecΔ) =
  ⟨⟩-ext-ctx (ec-++ᶜ ec'' ecΞ) ecΔ
cong-renˡ Γ'' ec'' (cong-∷-ren r) =
  cong-∷-ren (cong-renˡ Γ'' ec'' r)
cong-renˡ Γ'' ec'' (cong-⟨⟩-ren r) =
  cong-⟨⟩-ren (cong-renˡ Γ'' ec'' r)

-- Moving a prefix of the ambient into the local part. Both sides denote a map
-- between the same two contexts, so this is a reassociation; it goes only this
-- way, since the ambient means *fixed*, and fixing more implies fixing less.
--
-- Every case is the same constructor: no rule inspects where the ambient/local
-- boundary lies, and `++ᶜ` recurses on its right argument, so the local shapes
-- reassociate definitionally. Only `var-ren` (whose variable ranges over the
-- whole context) and `⟨⟩-ext-ctx` (whose eternality obligation is split by
-- `ec-split` and reassembled by `ec-++ᶜ`) do any work.

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
expose-ren Δ (⟨⟩-ext-ren et) =
  ⟨⟩-ext-ren et
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

-- Restriction of a renaming to the eternal parts of its contexts. Since the
-- eternal restriction is lock-free, every variable in it sits at grade `uᵣ`,
-- which is exactly what discharges the `≾ᵣ uᵣ` side-condition of `var-ren`.
-- Well-typed on the ambient too, `ᴱ-⋈ᶜ` distributing over the join (and being
-- `refl` at the empty ambient, so nothing is transported there).

restrict-ren : ∀ {Ξ Δ Δ'} → Ren Ξ Δ Δ' → Ren (Ξ ᴱ) (Δ ᴱ) (Δ' ᴱ)
restrict-ren id-ren =
  id-ren
restrict-ren (r₂ ∘ʳ r₁) =
  restrict-ren r₂ ∘ʳ restrict-ren r₁
restrict-ren (wk-ren {A = A}) with eternal? A
... | yes _ = wk-ren
... | no  _ = id-ren
restrict-ren {Ξ} {Δ' = Δ'} (var-ren {A = A} p x) with eternal? A
... | yes et = var-ren (λ _ → ≾ᵣ-refl)
                 (subst (λ Γ₀ → A ∈[ uᵣ ] Γ₀) (ᴱ-⋈ᶜ Ξ Δ') (∈-ᴱ et x))
... | no  _  = id-ren
restrict-ren ⟨⟩-η-ren =
  id-ren
restrict-ren ⟨⟩-η⁻¹-ren =
  id-ren
restrict-ren ⟨⟩-μ-ren =
  id-ren
restrict-ren (⟨⟩-≤-ren _) =
  id-ren
restrict-ren (cong-∷-ren {A = A} r) with eternal? A
... | yes _ = cong-∷-ren (restrict-ren r)
... | no  _ = restrict-ren r
restrict-ren (cong-⟨⟩-ren r) =
  restrict-ren r
restrict-ren (⟨⟩-ext-ren {A = A} et) with eternal? A
... | yes _  = id-ren
... | no ¬et = ⊥-elim (¬et et)
-- a lock is dropped by the restriction, so introducing one restricts to nothing
restrict-ren (⟨⟩-ext-ctx ecΞ ecΔ) =
  id-ren

-- Extending the eternal restriction by a variable. Unlike a general weakening
-- past the added structure, this always exists: a lock would be dropped by the
-- restriction, and a variable is either kept (weaken) or dropped (identity).

-- In the derived renamings the local parts are bound before the ambient, so
-- that positional instantiation still names them.

ren-ᴱ-∷ : ∀ {Δ Ξ} → (A : VType) → Ren Ξ (Δ ᴱ) ((Δ ∷ A) ᴱ)
ren-ᴱ-∷ A with eternal? A
... | yes _ = wk-ren
... | no  _ = id-ren

-- Weakening a grade to a context renaming

wk-ren-⟨ρ⟩-ctx : ∀ {Δ Δ' ρ Ξ} → ctx-grade Δ' ≡ ρ → Ren Ξ (Δ ⟨ ρ ⟩) (Δ ++ᶜ Δ')
wk-ren-⟨ρ⟩-ctx {Δ' = []} refl =
  ⟨⟩-η-ren
wk-ren-⟨ρ⟩-ctx {Δ' = Δ' ∷ _} refl =
  wk-ren ∘ʳ wk-ren-⟨ρ⟩-ctx refl
wk-ren-⟨ρ⟩-ctx {Δ} {Δ' ⟨ ρ' ⟩} {ρ} {Ξ} refl =
  cong-⟨⟩-ren (wk-ren-⟨ρ⟩-ctx refl) ∘ʳ ⟨⟩-μ-ren

-- Exchange renaming

exch-ren : ∀ {Δ A B Ξ} → Ren Ξ (Δ ∷ A ∷ B) (Δ ∷ B ∷ A)
exch-ren {Ξ = Ξ} =
  extend-ren (cong-∷-ren wk-ren) (λ _ → ≾ᵣ-refl) (∈-⋈ᶜ Ξ (Tl-∷ Hd))

-- Bringing a variable buried under a suffix context `Θ` up to the top. The
-- `∷`-case swaps it past the intervening variable (`exch-ren`), the `⟨⟩`-case
-- extrudes it out of the lock (`⟨⟩-ext-ren`), which requires it to be eternal.

bring-up : ∀ {Δ A Ξ} → Eternal A → (Θ : Ctx)
         → Ren Ξ ((Δ ∷ A) ++ᶜ Θ) ((Δ ++ᶜ Θ) ∷ A)
bring-up et []        = id-ren
bring-up et (Θ ∷ B)   = exch-ren ∘ʳ cong-∷-ren (bring-up et Θ)
bring-up et (Θ ⟨ ρ ⟩) = ⟨⟩-ext-ren et ∘ʳ cong-⟨⟩-ren (bring-up et Θ)

-- Contracting the eternal restriction prefix `Δ ᴱ` back into `Δ`'s own
-- variables. Each eternal variable duplicated by the prefix is brought up to
-- the top and contracted against its original occurrence in `Δ`.

contract : ∀ {Ξ} → (Δ : Ctx) → Ren Ξ (Δ ᴱ ++ᶜ Δ) Δ
contract []        = id-ren
contract {Ξ} (Δ ∷ A)   with eternal? A
... | yes eA = cong-∷-ren (contract Δ)
            ∘ʳ var-ren (λ _ → ≾ᵣ-refl) (∈-⋈ᶜ Ξ Hd)
            ∘ʳ cong-∷-ren (bring-up eA Δ)
... | no  _  = cong-∷-ren (contract Δ)
contract (Δ ⟨ ρ ⟩) = cong-⟨⟩-ren (contract Δ)

-- THE ETERNAL WEAKENING
--
-- Inserting a context `Γ'` immediately after the ambient, under an arbitrary
-- suffix `Θ`. Recursion on `Θ`, bottoming out in an insertion at the top; the
-- lock case is where `⟨⟩-ext-ctx` is used, which is why the ambient must be
-- eternal. This is what makes the weakening a renaming rather than a recursion
-- over terms.

wk-ctx-ren : ∀ {Ξ} → EternalCtx Ξ → (Γ' : Ctx) → Ren Ξ [] Γ'
wk-ctx-ren ec []         = id-ren
wk-ctx-ren ec (Γ' ∷ A)   = cong-∷-ren (wk-ctx-ren ec Γ') ∘ʳ wk-ren
wk-ctx-ren ec (Γ' ⟨ ρ ⟩) = cong-⟨⟩-ren (wk-ctx-ren ec Γ') ∘ʳ ⟨⟩-ext-ctx ec ec-[]

wk-ren-ctx : ∀ {Ξ} → EternalCtx Ξ → (Γ' Θ : Ctx) → Ren Ξ Θ (Γ' ++ᶜ Θ)
wk-ren-ctx ec Γ' []        = wk-ctx-ren ec Γ'
wk-ren-ctx ec Γ' (Θ ∷ A)   = cong-∷-ren (wk-ren-ctx ec Γ' Θ)
wk-ren-ctx ec Γ' (Θ ⟨ ρ ⟩) = cong-⟨⟩-ren (wk-ren-ctx ec Γ' Θ)
