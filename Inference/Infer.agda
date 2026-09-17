------------------------------------------------------------------
-- Inference for closed input                                    --
--                                                                --
-- The top-level corollary: for an original context `Γ` and a raw --
-- computation over its variables, a `GroundSolver` yields a      --
-- derivation of the ORIGINAL system, by                          --
--                                                                --
--     groundC ∘ soundC ∘ gsolve ∘ genC ⌜ Γ ⌝ᶜᵗˣ                  --
--                                                                --
-- `Inferred` also keeps the mirrored derivation the original one --
-- is grounded from, together with its erasure equation: erasure  --
-- is defined on mirrored derivations only, so the round-trip     --
-- statement `⌊ D ⌋ᶜ ≡ M` has no counterpart on the original      --
-- side and is reported there.                                    --
------------------------------------------------------------------

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import Inference.Scopes

module Inference.Infer (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts S
open import Syntax.Language S
open import Syntax.Types    S

open import Inference.Open.Grades          S
open import Inference.Open.Types           S
open import Inference.Open.Contexts        S
open import Inference.Open.Subst           S
open import Inference.Open.Hyps            S
open import Inference.Open.Language        S
open import Inference.Open.Grounding       S
open import Inference.Open.GroundingTheorem S
open import Inference.Open.ClosedContexts  S

open import Inference.Raw.Syntax S
open import Inference.Erase      S

open import Inference.Constraints.Syntax       S
open import Inference.Constraints.Satisfaction S

open import Inference.Generate  S
open import Inference.Soundness S
open import Inference.Solver    S

--------------------------------------------------------------
-- The generation instance for a closed context              --
--                                                           --
-- Only the result type and the result effect are unknown, so --
-- generation runs in `∅ˢ +ty +e`; the embedded context needs --
-- no weakening, being scope-polymorphic.                     --
--------------------------------------------------------------

Θ₁ : Scope
Θ₁ = ∅ˢ +ty +e

X̂₁ : OVType Θ₁
X̂₁ = tvar (newᵗ {∅ˢ})

t̂₁ : EExp Θ₁
t̂₁ = evar (newᵉ {∅ˢ +ty})

C∅[_,_] : (Γ : Ctx) → RawC (skel Γ) → Constraint Θ₁
C∅[ Γ , M ] = genC ⌜ Γ ⌝ᶜᵗˣ M (X̂₁ ‼ t̂₁)

-- The unique grounding of the empty scope

θ∅ : Grounding ∅ˢ
θ∅ = grounding (λ ()) (λ ()) (λ ())

--------------------------------------------------------------
-- The result of a successful inference                      --
--------------------------------------------------------------

record Inferred (Γ : Ctx) (M : RawC (skel Γ)) : Set where
  constructor inferred
  field

    -- the ground solution and the mirrored derivation it elaborates to

    σ   : Subst Θ₁ ∅ˢ
    D̂   : ∅ᴴ ∣ ⌜ Γ ⌝ᶜᵗˣ ⊢C⦂ (X̂₁ [ σ ]ᵛ) ‼ (t̂₁ [ σ ]ᵉ)
    ⌊D̂⌋ : ⌊ D̂ ⌋ᶜ ≡ M

    -- the original typing it grounds to

    A    : VType
    ε    : E
    A-is : A ≡ ⟦ X̂₁ [ σ ]ᵛ ⟧ᵛ θ∅
    ε-is : ε ≡ ⟦ t̂₁ [ σ ]ᵉ ⟧ᵉ θ∅
    D    : Γ ⊢C⦂ A ‼ ε

--------------------------------------------------------------
-- Inference                                                 --
--------------------------------------------------------------

private

  -- A ground solution is elaborated, its context collapsed by
  -- `⌜⌝ᶜᵗˣ-subst`, grounded, and its context collapsed again by
  -- `⌜⌝ᶜᵗˣ-ground`.

  build : (Γ : Ctx) → (M : RawC (skel Γ))
        → (σ : Subst Θ₁ ∅ˢ) → σ ⊨[ ∅ᴴ ] C∅[ Γ , M ]
        ------------------------------------------
        → Inferred Γ M
  build Γ M σ sat = inferred σ D̂ ⌊D̂⌋ _ _ refl refl D
    where
      elab = soundC ⌜ Γ ⌝ᶜᵗˣ M X̂₁ t̂₁ sat
      ce   = ⌜⌝ᶜᵗˣ-subst σ Γ

      D̂   = ctx-substᶜ ce (proj₁ elab)
      ⌊D̂⌋ = trans (⌊ctxᶜ⌋ ce (proj₁ elab)) (proj₂ elab)

      D = subst (λ G → G ⊢C⦂ _) (⌜⌝ᶜᵗˣ-ground θ∅ Γ) (groundC θ∅ ∅ᴴ-⊨ D̂)

  -- Split off so that `infer-nothing` can case on the solver's answer

  infer-aux : (Γ : Ctx) → (M : RawC (skel Γ))
            → Maybe (Σ[ σ ∈ Subst Θ₁ ∅ˢ ] (σ ⊨[ ∅ᴴ ] C∅[ Γ , M ]))
            → Maybe (Inferred Γ M)
  infer-aux Γ M nothing          = nothing
  infer-aux Γ M (just (σ , sat)) = just (build Γ M σ sat)

infer : (gs : GroundSolver) → (Γ : Ctx) → (M : RawC (skel Γ))
      -----------------------------------------------------
      → Maybe (Inferred Γ M)
infer gs Γ M = infer-aux Γ M (GroundSolver.gsolve gs C∅[ Γ , M ])

--------------------------------------------------------------
-- Failure                                                   --
--                                                           --
-- Stated at the constraint level: an untypability statement  --
-- about the ORIGINAL system would need an erasure of         --
-- original derivations, which does not exist (erasure is     --
-- defined on mirrored derivations only).                     --
--------------------------------------------------------------

private

  infer-nothing : (gs : GroundSolver) → (Γ : Ctx) → (M : RawC (skel Γ))
                → infer gs Γ M ≡ nothing
                → GroundSolver.gsolve gs C∅[ Γ , M ] ≡ nothing
  infer-nothing gs Γ M p with GroundSolver.gsolve gs C∅[ Γ , M ] | p
  ... | nothing | _ = refl

infer-complete : (gs : GroundSolver) → (Γ : Ctx) → (M : RawC (skel Γ))
               → infer gs Γ M ≡ nothing
               → (σ : Subst Θ₁ ∅ˢ)
               -----------------------------------
               → ¬ (σ ⊨[ ∅ᴴ ] C∅[ Γ , M ])
infer-complete gs Γ M p σ =
  GroundSolver.gsolve-complete gs C∅[ Γ , M ] (infer-nothing gs Γ M p) σ

--------------------------------------------------------------
-- Sanity check: the pipeline computes on closed input       --
--------------------------------------------------------------

private

  ex-Γ : Ctx
  ex-Γ = [] ∷ Unit

  ex-σ : Subst Θ₁ ∅ˢ
  ex-σ = sub (λ _ → Unit) (λ ()) (λ _ → ûₑ)

  ex-sat : ex-σ ⊨[ ∅ᴴ ] C∅[ ex-Γ , return ⋆ ]
  ex-sat = refl , ⊩≾̂ₑ-refl

  ex : Inferred ex-Γ (return ⋆)
  ex = build ex-Γ (return ⋆) ex-σ ex-sat

  -- the inferred type and effect are the expected ones

  ex-A : Inferred.A ex ≡ Unit
  ex-A = refl

  ex-ε : Inferred.ε ex ≡ uₑ
  ex-ε = refl

  -- the mirrored witness erases back to the input

  ex-⌊⌋ : ⌊ Inferred.D̂ ex ⌋ᶜ ≡ return ⋆
  ex-⌊⌋ = refl
