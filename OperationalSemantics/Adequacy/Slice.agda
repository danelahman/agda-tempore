------------------------------------------------------------------------
-- The index of the logical relation: guarded state extensions.         --
--                                                                    --
-- Reindexing along `S ≤ₛ S'` is not free weakening — `suc-comp-ren`     --
-- takes a grade side-condition, and only eternal values move            --
-- unconditionally. So the relation is Kripke over the *slice* that       --
-- `suc-comp-ren` accepts: an extension together with the bound that      --
-- licenses crossing the lock it was guarded by.                          --
--                                                                    --
-- Only lock-guarded data has to be monotone (`⨟`/`perform` continuations, --
-- boxed resources); a plain value is used at the state it was built at,   --
-- which is exactly what the `var` rule's own grade premise says.          --
------------------------------------------------------------------------

open import Data.Product

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

module OperationalSemantics.Adequacy.Slice (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades

open import OperationalSemantics.PreservationTheorem Spec
open import OperationalSemantics.State               Spec

open import Syntax.Contexts   Spec
open import Syntax.Language   Spec
open import Syntax.RenActions Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

-- A `ρ`-guarded extension: `St'` extends `St`, and the grade it accumulated,
-- composed with the residual lock `ρ'`, stays below the guarding lock `ρ`.
-- This is precisely the data `suc-comp-ren` consumes.

record Slice (St : 𝕊 []) (ρ : R) (St' : 𝕊 []) (ρ' : R) : Set where
  constructor slice
  field
    ext   : St ≤ₛ St'
    bound : ≤ₛ-grade ext ·ᵣ ρ' ≾ᵣ ρ

open Slice public

-- The renaming a slice licenses.

slice-ren : ∀ {St ρ St' ρ'} → Slice St ρ St' ρ' → Ren (toCtx St ⟨ ρ ⟩) (toCtx St' ⟨ ρ' ⟩)
slice-ren (slice e b) = suc-comp-ren e b

-- Identity: no extension, nothing accumulated.

slice-id : ∀ {St ρ} → Slice St ρ St ρ
slice-id {ρ = ρ} = slice id-suc (≾ᵣ-reflexive (·ᵣ-identityˡ ρ))

-- Transporting a plain value: at the unit lock the slice is a renaming
-- `toCtx St → toCtx St'`.

slice-val : ∀ {St St' A} → Slice St uᵣ St' uᵣ → toCtx St ⊢V⦂ A → toCtx St' ⊢V⦂ A
slice-val q = V-rename (⟨⟩-η-ren ∘ʳ slice-ren q ∘ʳ ⟨⟩-η⁻¹-ren)

slice-comp : ∀ {St St' C} → Slice St uᵣ St' uᵣ → toCtx St ⊢C⦂ C → toCtx St' ⊢C⦂ C
slice-comp q = C-rename (⟨⟩-η-ren ∘ʳ slice-ren q ∘ʳ ⟨⟩-η⁻¹-ren)

-- The witness an `unbox` needs: enough time has passed for a `ρ`-boxed value
-- to be ready at `St'`. This is the shape of `UNBOX`'s premise, hence what
-- `unbox-lookup` consumes.

unbox-ren : ∀ {St ρ St'} → Slice St ρ St' uᵣ → Ren (toCtx St ⟨ ρ ⟩) (toCtx St')
unbox-ren q = ⟨⟩-η-ren ∘ʳ slice-ren q

-- Resuming a continuation guarded by `ρ` at a later state: transport it along
-- the slice, then feed it the arity value. The result lives over the *locked*
-- state `St' ⟨ ρ ⟩ₛ`, which is where `HANDLE-OP` resumes.

resume : ∀ {St St' ρ A ε B}
       → (q : Slice St ρ St' ρ)
       → toCtx St ⟨ ρ ⟩ ∷ B ⊢C⦂ A ‼ ε
       → toCtx (St' ⟨ ρ ⟩ₛ) ⊢V⦂ B
       → toCtx (St' ⟨ ρ ⟩ₛ) ⊢C⦂ A ‼ ε
resume q M W = (C-rename (cong-∷-ren (slice-ren q)) M) [ Hd ↦ W ]c

------------------------------------------------------------------------
-- LEMMAS TO PROVE
------------------------------------------------------------------------

postulate

  -- The slice is a category: composition and its interaction with the
  -- renamings above. `⊑`-style transitivity of guarded extensions, with the
  -- grade bounds composing.

  slice-∘ : ∀ {St St' St'' ρ ρ' ρ''}
          → Slice St' ρ' St'' ρ'' → Slice St ρ St' ρ' → Slice St ρ St'' ρ''

  -- A step, and a run, extend the state along the slice at the unit lock
  -- whenever the grades permit; this is `step-extends-state`/`step-grade-≾`
  -- repackaged as slice data.

  step-slice : ∀ {A B ε ε'} {St St' : 𝕊 []}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ B ‼ ε'}
             → (r : ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩)
             → ≤ₛ-grade (step-extends-state r) ≾ᵣ uᵣ
             → Slice St uᵣ St' uᵣ

  -- Allocating a cell is a slice at the unit lock (`BOX`), and letting time
  -- pass is a slice at the lock it passes (`DELAY`).

  alloc-slice : ∀ {A ρ} {St : 𝕊 []} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
              → Slice St uᵣ (St ∷ₛ V) uᵣ

  delay-slice : ∀ {ρ} {St : 𝕊 []} → Slice St ρ (St ⟨ ρ ⟩ₛ) uᵣ
