-------------------------------------------------
-- The eternal restriction, acting on renamings --
-------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

module Syntax.Renamings.Eternal (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Contexts       S
open import Syntax.Types          S
open import Syntax.Renamings.Base S

-- Restriction of a renaming to the eternal parts of its contexts. Since the
-- eternal restriction is lock-free, every variable in it sits at grade `uᵣ`,
-- which is exactly what discharges the `≾ᵣ uᵣ` side-condition of `var-ren`.
-- Well-typed on the ambient too, `ᴱ-⋈ᶜ` distributing over the join (and being
-- `refl` at the empty ambient, so nothing is transported there).

-- Extending the eternal restriction by a variable. Unlike a general weakening
-- past the added structure, this always exists: a lock would be dropped by the
-- restriction, and a variable is either kept (weaken) or dropped (identity).
--
-- As `_ᴱ` itself, the decision is a parameter rather than a `with`, so that a
-- caller matching on it reduces this too.

ren-ᴱ-∷′ : ∀ {Δ Ξ} → (A : VType) → (dec : Dec (Eternal A))
         → Ren Ξ (ᴱ-∷ (Δ ᴱ) A dec) (Δ ᴱ)
ren-ᴱ-∷′ A (yes _) = wk-ren
ren-ᴱ-∷′ A (no  _) = id-ren

-- The two clauses of `restrict-ren` that inspect a variable's type, likewise
-- with the decision taken as a parameter.

restrict-var-ren : ∀ {Ξ Δ A ρ} → (dec : Dec (Eternal A))
                 → (¬ Eternal A → ρ ≾ᵣ uᵣ) → A ∈[ ρ ] (Ξ ⋈ᶜ Δ)
                 → Ren (Ξ ᴱ) (Δ ᴱ) (ᴱ-∷ (Δ ᴱ) A dec)
restrict-var-ren {Ξ} {Δ} {A} (yes et) p x =
  var-ren (λ _ → ≾ᵣ-refl)
    (subst (λ Γ₀ → A ∈[ uᵣ ] Γ₀) (ᴱ-⋈ᶜ Ξ Δ) (∈-ᴱ et x))
restrict-var-ren (no _) p x = id-ren

restrict-∷-ren : ∀ {Ξ Δ Δ' A} → (dec : Dec (Eternal A))
               → Ren (Ξ ᴱ) (Δ ᴱ) (Δ' ᴱ)
               → Ren (Ξ ᴱ) (ᴱ-∷ (Δ ᴱ) A dec) (ᴱ-∷ (Δ' ᴱ) A dec)
restrict-∷-ren (yes _) r = cong-∷-ren r
restrict-∷-ren (no  _) r = r

restrict-ren : ∀ {Ξ Δ Δ'} → Ren Ξ Δ Δ' → Ren (Ξ ᴱ) (Δ ᴱ) (Δ' ᴱ)
restrict-ren id-ren =
  id-ren
restrict-ren (r₂ ∘ʳ r₁) =
  restrict-ren r₂ ∘ʳ restrict-ren r₁
restrict-ren {Ξ} {Δ' = Δ} (wk-ren {A = A}) =
  ren-ᴱ-∷′ {Δ} {Ξ ᴱ} A (eternal? A)
restrict-ren {Ξ} {Δ} (var-ren {A = A} p x) =
  restrict-var-ren {Ξ} {Δ} {A} (eternal? A) p x
restrict-ren ⟨⟩-η-ren =
  id-ren
restrict-ren ⟨⟩-η⁻¹-ren =
  id-ren
restrict-ren ⟨⟩-μ-ren =
  id-ren
restrict-ren (⟨⟩-≤-ren _) =
  id-ren
restrict-ren {Ξ} (cong-∷-ren {Δ} {Δ'} {A} r) =
  restrict-∷-ren {Ξ} {Δ} {Δ'} {A} (eternal? A) (restrict-ren r)
restrict-ren (cong-⟨⟩-ren r) =
  restrict-ren r
-- both sides drop the lock, so this is the identity whatever `A`'s eternality
restrict-ren (⟨⟩-ext-ren {A = A} et) =
  id-ren
-- a lock is dropped by the restriction, so introducing one restricts to nothing
restrict-ren (⟨⟩-ext-ctx ecΞ ecΔ) =
  id-ren

-- In the derived renamings the local parts are bound before the ambient, so
-- that positional instantiation names them.

ren-ᴱ-∷ : ∀ {Δ Ξ} → (A : VType) → Ren Ξ ((Δ ∷ A) ᴱ) (Δ ᴱ)
ren-ᴱ-∷ {Δ} {Ξ} A = ren-ᴱ-∷′ {Δ} {Ξ} A (eternal? A)

-- Bringing a variable buried under a suffix context `Θ` up to the top. The
-- `∷`-case swaps it past the intervening variable (`exch-ren`), the `⟨⟩`-case
-- extrudes it out of the lock (`⟨⟩-ext-ren`), which requires it to be eternal.

bring-up : ∀ {Δ A Ξ} → Eternal A → (Θ : Ctx)
         → Ren Ξ ((Δ ++ᶜ Θ) ∷ A) ((Δ ∷ A) ++ᶜ Θ)
bring-up et []        = id-ren
bring-up et (Θ ∷ B)   = cong-∷-ren (bring-up et Θ) ∘ʳ exch-ren
bring-up et (Θ ⟨ ρ ⟩) = cong-⟨⟩-ren (bring-up et Θ) ∘ʳ ⟨⟩-ext-ren et

-- Contracting the eternal restriction prefix `Δ ᴱ` back into `Δ`'s own
-- variables. Each eternal variable duplicated by the prefix is brought up to
-- the top and contracted against its original occurrence in `Δ`.

contract : ∀ {Ξ} → (Δ : Ctx) → Ren Ξ Δ (Δ ᴱ ++ᶜ Δ)
contract []        = id-ren
contract {Ξ} (Δ ∷ A)   with eternal? A
... | yes eA = (cong-∷-ren (bring-up eA Δ)
            ∘ʳ var-ren (λ _ → ≾ᵣ-refl) (∈-⋈ᶜ Ξ Hd))
            ∘ʳ cong-∷-ren (contract Δ)
... | no  _  = cong-∷-ren (contract Δ)
contract (Δ ⟨ ρ ⟩) = cong-⟨⟩-ren (contract Δ)

-- THE ETERNAL INCLUSION
--
-- Weakening the eternal restriction `Δ ᴱ` back into `Δ`: non-eternal entries
-- are dropped by `wk-ren`, and a lock is introduced by `⟨⟩-ext-ctx`, which the
-- restriction's own eternality licenses. This is what a handler clause, which
-- closes over `Δ ᴱ`, is renamed along when the operation is handled; its
-- interpretation is exactly the eternal projection (`ᴱ-ren-mor`).

ᴱ-ren-∷ : ∀ {Δ} → (A : VType) → (dec : Dec (Eternal A))
        → Ren [] Δ (Δ ᴱ) → Ren [] (Δ ∷ A) (ᴱ-∷ (Δ ᴱ) A dec)
ᴱ-ren-∷ A (yes _) r = cong-∷-ren r
ᴱ-ren-∷ A (no  _) r = r ∘ʳ wk-ren

ᴱ-ren : (Δ : Ctx) → Ren [] Δ (Δ ᴱ)
ᴱ-ren []        = id-ren
ᴱ-ren (Δ ∷ A)   = ᴱ-ren-∷ {Δ} A (eternal? A) (ᴱ-ren Δ)
ᴱ-ren (Δ ⟨ ρ ⟩) = ⟨⟩-ext-ctx ec-[] (ᴱ-EternalCtx Δ) ∘ʳ cong-⟨⟩-ren (ᴱ-ren Δ)

-- THE ETERNAL WEAKENING
--
-- Inserting a context `Γ'` immediately after the ambient, under an arbitrary
-- suffix `Θ`. Recursion on `Θ`, bottoming out in an insertion at the top; the
-- lock case is where `⟨⟩-ext-ctx` is used, which is why the ambient must be
-- eternal. This is what makes the weakening a renaming rather than a recursion
-- over terms.

wk-ctx-ren : ∀ {Ξ} → EternalCtx Ξ → (Γ' : Ctx) → Ren Ξ Γ' []
wk-ctx-ren ec []         = id-ren
wk-ctx-ren ec (Γ' ∷ A)   = wk-ren ∘ʳ cong-∷-ren (wk-ctx-ren ec Γ')
wk-ctx-ren ec (Γ' ⟨ ρ ⟩) = ⟨⟩-ext-ctx ec ec-[] ∘ʳ cong-⟨⟩-ren (wk-ctx-ren ec Γ')

wk-ren-ctx : ∀ {Ξ} → EternalCtx Ξ → (Γ' Θ : Ctx) → Ren Ξ (Γ' ++ᶜ Θ) Θ
wk-ren-ctx ec Γ' []        = wk-ctx-ren ec Γ'
wk-ren-ctx ec Γ' (Θ ∷ A)   = cong-∷-ren (wk-ren-ctx ec Γ' Θ)
wk-ren-ctx ec Γ' (Θ ⟨ ρ ⟩) = cong-⟨⟩-ren (wk-ren-ctx ec Γ' Θ)
