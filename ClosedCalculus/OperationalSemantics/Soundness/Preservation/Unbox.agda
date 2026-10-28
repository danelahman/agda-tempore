open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import ClosedCalculus.DenotationalSemantics.Model.Category
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Future
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Past
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import ClosedCalculus.DenotationalSemantics.Model.GroundTypes
open import ClosedCalculus.DenotationalSemantics.Model.GroundEternal
open import ClosedCalculus.DenotationalSemantics.Model.Monad

module ClosedCalculus.OperationalSemantics.Soundness.Preservation.Unbox
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Language.Types     S
open import ClosedCalculus.Syntax.Contexts  S
open import ClosedCalculus.Syntax.Terms  S
open import ClosedCalculus.Syntax.Renamings S
open import ClosedCalculus.Syntax.RenActions S using (V-rename; C-rename; var-rename)
open import ClosedCalculus.Syntax.Substitutions S

open import ClosedCalculus.OperationalSemantics.State S
open import ClosedCalculus.OperationalSemantics.PreservationTheorem S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-congᶠ; []-idᵐ; []-∘ᵐ; []-≤; []-≤-refl; []-≤-nat;
                       []-ε-nat; []-ε∘ηᵘ≡id; ηᵘ; δ; []-δ-nat; []-monoidal; []-≤-trans;
                       []-monoidal-nat; []-monoidal-fstᵐ; []-monoidal-sndᵐ; []-monoidal-η;
                       []-𝟙-unique) renaming (ε to εᵇ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; μ; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ; ⟨⟩-η-nat; ⟨⟩-μ-nat;
                     ⟨⟩-≤-nat; ⟨⟩-≤-irr; ⟨⟩-≤-refl; ⟨⟩-≤-trans; μ-≤ˡ; μ-≤ʳ;
                     ⟨⟩-μ∘Tη≡id; ⟨⟩-μ∘η≡id)
open Adjunction Adj using (η⊣; η⊣-nat; η⊣-u; η⊣-≤; η⊣-δ; η⊣-monoidal;
                           ε⊣; ε⊣-nat; triangleˡ)
open GroundTypes GTy using (⟦_⟧ᵍ)
open Monad Mon

open import ClosedCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.State S Cat Fut Pst Adj GTy Mon GE

open import ClosedCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import ClosedCalculus.OperationalSemantics.Soundness.Preservation.Base S Cat Fut Pst Adj GTy Mon GE public

-- `UNBOX` = lookup: a cell `x` was allocated by some prefix of the state
-- (`split-state-fst St x`), so reading it has to reach back to that world.
-- `state-past` is that reach-back: the past-view, at the cell's accumulated
-- grade `ρ'`, of the sub-state that allocated it.

state-past : ∀ {A ρ ρ'} → (St : 𝕊 []) → (x : [ ρ ] A ∈[ ρ' ] toCtx St)
           → Paramˢ St
           → ⟦ hist St ⟧ᶜᵗˣ →ᵐ ⟨ ρ' ⟩ᵒ ⟦ toCtx (split-state-fst St x) ⟧ᶜᵗˣ
state-past (St ⟨ σ ⟩ₛ) (Tl-⟨⟩ y) pSt        = μ ∘ᵐ ⟨ σ ⟩ᶠ (state-past St y pSt)
state-past (St ∷ₛ W)   Hd        (pSt , _)  = η ∘ᵐ ⟦ St ⟧ˢ pSt
state-past (St ∷ₛ W)   (Tl-∷ y)  (pSt , _)  = state-past St y pSt

-- Projecting a cell out of the state's environment recovers exactly the value
-- stored in it — boxed by `η⊣` (the `box` morphism, which is what put it
-- there) and viewed from the past in which it was allocated.
--
-- Each case is a naturality law of the modality against the corresponding
-- clause of `⟦_⟧ˢ`: `Hd` is `η`'s naturality against the cell just written,
-- `Tl-∷` drops a later cell by `fstᵐ`, and `Tl-⟨⟩` folds a lock with `μ`'s
-- naturality — the grades multiplying exactly as `ctx-grade` says they must.

state-lookup : ∀ {A ρ ρ'} → (St : 𝕊 []) → (x : [ ρ ] A ∈[ ρ' ] toCtx St)
             → (pSt : Paramˢ St)
             → var-proj x ∘ᵐ ⟦ St ⟧ˢ pSt
             ≈ᵐ ⟨ ρ' ⟩ᶠ ([ ρ ]ᶠ (⟦ resource-lookup St x ⟧ᵛᵗ (resource-lookupᴾ St x pSt)
                                   ∘ᵐ ⟦ eq-ren (++ᶜ-identityˡ
                                        {toCtx (split-state-fst St x) ⟨ ρ ⟩}) ⟧ʳ)
                                 ∘ᵐ η⊣)
                ∘ᵐ state-past St x pSt

state-lookup (St ∷ₛ W) Hd (pSt , pW) =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-η-nat _))
  ∙ ∘ᵐ-assoc _ _ _

state-lookup (St ∷ₛ W) (Tl-∷ y) (pSt , pW) =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-identityˡ _)
  ∙ state-lookup St y pSt

state-lookup (St ⟨ σ ⟩ₛ) (Tl-⟨⟩ y) pSt =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
  ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ (state-lookup St y pSt))
  ∙ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-μ-nat _))
  ∙ ∘ᵐ-assoc _ _ _

-- `unbox-lookup` renames the stored value out of the allocating prefix's
-- context into `toCtx S`, through a composite of transports, a
-- `wk-ren-⟨ρ⟩-ctx`, and the grade relaxation `⟨⟩-≤-ren rel`; that composite
-- denotes `state-past`. The grade coercion is carried explicitly as a `⟨⟩-≤`
-- at an arbitrary witness, since `ρ'` occurs inside `split-state-snd St x`'s
-- own type and so cannot be specialised against `refl`.

-- The grade a cell's suffix accumulates is the cell's own grade. (This is the
-- equality `unbox-lookup` feeds to `wk-ren-⟨ρ⟩-ctx`.)

cell-grade : ∀ {A ρ ρ'} → (St : 𝕊 []) → (x : [ ρ ] A ∈[ ρ' ] toCtx St)
           → ctx-grade (([] ∷ [ ρ ] A) ++ᶜ toCtx (split-state-snd St x)) ≃ᵣ ρ'
cell-grade {A = A} {ρ = ρ} St x =
  ≃ᵣ-trans
    (≃ᵣ-trans
      (≃ᵣ-trans
        (ctx-grade-++ᶜ ([] ∷ [ ρ ] A) (toCtx (split-state-snd St x)))
        (·ᵣ-identityˡ (ctx-grade (toCtx (split-state-snd St x)))))
      (≃ᵣ-reflexive (sym (grades-≡ (split-state-snd St x)))))
    (≃ᵣ-reflexive (snd-split-time≡time-from-head St x))

-- The renaming composite of `unbox-lookup`, minus the grade relaxation and the
-- `[] ++ᶜ_` transport, denotes the reach-back into the allocating prefix.

past-core : ∀ {A ρ ρ'} → (St : 𝕊 []) → (x : [ ρ ] A ∈[ ρ' ] toCtx St)
          → (pSt : Paramˢ St)
          → (p : ρ' ≾ᵣ ctx-grade (([] ∷ [ ρ ] A) ++ᶜ toCtx (split-state-snd St x)))
          → ⟦ wk-ren-⟨ρ⟩-ctx {toCtx (split-state-fst St x)}
                             {([] ∷ [ ρ ] A) ++ᶜ toCtx (split-state-snd St x)} refl ⟧ʳ
              ∘ᵐ ⟦ eq-ren (sym (++ᶜ-assoc (toCtx (split-state-fst St x)) ([] ∷ [ ρ ] A)
                                          (toCtx (split-state-snd St x)))) ⟧ʳ
              ∘ᵐ ⟦ eq-ren (split-state-++ᶜ St x) ⟧ʳ
              ∘ᵐ ⟦ St ⟧ˢ pSt
            ≈ᵐ ⟨⟩-≤ p ∘ᵐ state-past St x pSt

-- the cell was just allocated: drop it with `fstᵐ`, and the reach-back is `η`
past-core (St ∷ₛ W) Hd (pSt , pW) p =
    ∘ᵐ-congʳ (∘ᵐ-identityˡ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-identityˡ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-identityˡ _)
  ∙ ≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩-≤-irr p ≾ᵣ-refl ∙ ⟨⟩-≤-refl) ∙ ∘ᵐ-identityˡ _)

-- a later cell: it sits in the first component of every transport, so `fstᵐ`
-- pushes straight through to the sub-state
past-core {A} {ρ} (_∷ₛ_ {B} {σ} St W) (Tl-∷ y) (pSt , pW) p =
    ∘ᵐ-congʳ (∘ᵐ-congˡ
      (≡→≈ᵐ (cong (λ z → ⟦ eq-ren z ⟧ʳ) (sym-cong {f = _∷ [ σ ] B} assoc))
       ∙ eq-ren-∷ (sym assoc)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (eq-ren-∷ (split-state-++ᶜ St y))))
  -- push the projection `fstᵐ` past each transport, dropping the later cell
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _)))
  ∙ past-core St y pSt p
  where
    assoc = ++ᶜ-assoc (toCtx (split-state-fst St y)) ([] ∷ [ ρ ] A)
                      (toCtx (split-state-snd St y))

-- a lock: fold it with `μ`, the grades multiplying on both sides
past-core {A} {ρ} (St ⟨ σ ⟩ₛ) (Tl-⟨⟩ y) pSt p =
    ∘ᵐ-congʳ (∘ᵐ-congˡ
      (≡→≈ᵐ (cong (λ z → ⟦ eq-ren z ⟧ʳ) (sym-cong {f = _⟨ σ ⟩} assoc))
       ∙ eq-ren-⟨⟩ (sym assoc)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (eq-ren-⟨⟩ (split-state-++ᶜ St y))))
  -- everything under the lock is a `⟨ σ ⟩`-image: collect it
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
  ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ (past-core St y pSt p₀))
  -- and `μ` absorbs the sub-state's grade coercion (`μ-≤ˡ`)
  ∙ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (μ-≤ˡ p₀))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congˡ (⟨⟩-≤-irr _ p)
  where
    assoc = ++ᶜ-assoc (toCtx (split-state-fst St y)) ([] ∷ [ ρ ] A)
                      (toCtx (split-state-snd St y))
    p₀ = ≃ᵣ⇒≿ᵣ (cell-grade St y)

-- The grade equality that `wk-ren-⟨ρ⟩-ctx` carries can be split off as a
-- `⟨⟩-≤` (here `Γ`, `Γ'` and `ρ` are independent, so the equality *can* be
-- matched, unlike inside `past-core`).

wk-lock-≤ : ∀ {Γ Γ' ρ} → (e : ctx-grade Γ' ≡ ρ)
          → ⟦ wk-ren-⟨ρ⟩-ctx {Γ} {Γ'} e ⟧ʳ
          ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive e) ∘ᵐ ⟦ wk-ren-⟨ρ⟩-ctx {Γ} {Γ'} refl ⟧ʳ
wk-lock-≤ refl =
  ≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩-≤-irr _ ≾ᵣ-refl ∙ ⟨⟩-≤-refl) ∙ ∘ᵐ-identityˡ _)

-- `UNBOX`: reading the resource it refers to, out of the state's environment,
-- is exactly the value stored in it. The read is `ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj`,
-- and `ε⊣` cancels the `η⊣` that `box` wrote by the triangle identity; the
-- grade relaxation `rel` gates the read.

-- The looked-up resource is the stored value renamed, so its certificate is
-- the stored one's, renamed the same way.
unbox-lookupᴾ : ∀ {A ρ ρ'} → (St : 𝕊 [])
              → (z : [ ρ ] A ∈[ ρ' ] toCtx St) → (rel : ρ' ≾ᵣ ρ)
              → Paramˢ St → Paramᵛ (unbox-lookup St z rel)
unbox-lookupᴾ {A} {ρ} St z rel pSt =
  renᵛ
    ((((  eq-ren ++ᶜ-identityˡ
       ∘ʳ ⟨⟩-≤-ren rel)
       ∘ʳ (⟨⟩-≤-ren (≃ᵣ⇒≾ᵣ (≃ᵣ-trans (≃ᵣ-trans (≃ᵣ-trans (ctx-grade-++ᶜ ([] ∷ [ ρ ] A) (toCtx (split-state-snd St z))) (·ᵣ-identityˡ (ctx-grade (toCtx (split-state-snd St z))))) (≃ᵣ-reflexive (sym (grades-≡ (split-state-snd St z))))) (≃ᵣ-reflexive (snd-split-time≡time-from-head St z)))) ∘ʳ wk-ren-⟨ρ⟩-ctx refl))
       ∘ʳ eq-ren (sym (++ᶜ-assoc _ ([] ∷ [ ρ ] A) _)))
       ∘ʳ eq-ren (split-state-++ᶜ St z))
    (resource-lookup St z) (resource-lookupᴾ St z pSt)

unbox-lookup-sound : ∀ {A ρ ρ'} → (St : 𝕊 [])
                   → (x : [ ρ ] A ∈[ ρ' ] toCtx St) → (rel : ρ' ≾ᵣ ρ)
                   → (pSt : Paramˢ St)
                   → ⟦ unbox-lookup St x rel ⟧ᵛᵗ (unbox-lookupᴾ St x rel pSt)
                       ∘ᵐ ⟦ St ⟧ˢ pSt
                   ≈ᵐ (ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj x) ∘ᵐ ⟦ St ⟧ˢ pSt
unbox-lookup-sound {A} {ρ} St x rel pSt =
    -- the stored value, reindexed by `unbox-lookup`'s renaming composite
    -- (which `∘ʳ` leaves left-nested, so re-associate it first)
      ∘ᵐ-congˡ (V-rename-nat _ (resource-lookup St x) (resource-lookupᴾ St x pSt))
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
    ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
    ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
    ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
    -- split the grade equality off the `wk-ren-⟨ρ⟩-ctx`, then the rest of the
    -- composite is exactly `past-core`'s reach-back
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (past-core St x pSt p₀))))
    -- the two grade coercions cancel
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
        (⟨⟩-≤-trans _ _ ∙ ⟨⟩-≤-irr _ ≾ᵣ-refl ∙ ⟨⟩-≤-refl))))
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _)))
    ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙ ≈ᵐ-sym rhs
  where
    p₀ = ≃ᵣ⇒≿ᵣ (cell-grade St x)

    g = ⟦ resource-lookup St x ⟧ᵛᵗ (resource-lookupᴾ St x pSt)
          ∘ᵐ ⟦ eq-ren (++ᶜ-identityˡ
                 {toCtx (split-state-fst St x) ⟨ ρ ⟩}) ⟧ʳ

    rhs : (ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj x) ∘ᵐ ⟦ St ⟧ˢ pSt
        ≈ᵐ g ∘ᵐ ⟨⟩-≤ rel ∘ᵐ state-past St x pSt
    rhs =
      -- read the cell out of the environment
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (state-lookup St x pSt))
      -- move the gate past the cell's boxing
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-nat _ rel)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      -- and `ε⊣` cancels the `η⊣` that `box` put there (triangle identity)
      ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ (≈ᵐ-sym (ε⊣-nat g)))
      ∙ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ triangleˡ)
      ∙ ∘ᵐ-congˡ (∘ᵐ-identityʳ _)

-- The interpretation of an `unbox`, named so that the equational-theory
-- soundness proofs can rewrite by it.

unbox-def : ∀ {Γ A A₀ C ρ ρ'} → (x : [ ρ ] A₀ ∈[ ρ' ] Γ) → (rel : ρ' ≾ᵣ ρ)
          → (p : A₀ <:ᵛ A) → (M : Γ ∷ A ⊢C⦂ C) → (pM : Paramᶜ M)
          → ⟦ unbox x rel p M ⟧ᶜᵗ pM
          ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ idᵐ , ⟦ p ⟧<:ᵛ ∘ᵐ ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj x ⟩ᵐ
unbox-def x rel p M pM = ≈ᵐ-refl

-- UNBOX: substituting the looked-up resource is reading the cell, the payload
-- subsumption riding along on both sides.

sound-UNBOX : ∀ {A A₀ C ρ ρ'} → (St : 𝕊 [])
            → (x : [ ρ ] A₀ ∈[ ρ' ] toCtx St) → (rel : ρ' ≾ᵣ ρ) → (p : A₀ <:ᵛ A)
            → (M : toCtx St ∷ A ⊢C⦂ C)
            → (pSt : Paramˢ St) → (pM : Paramᶜ M)
            → ⟦ unbox x rel p M ⟧ᶜᵗ pM ∘ᵐ ⟦ St ⟧ˢ pSt
            ≈ᵐ ⟦ M [ split-[] ↦ subV (unbox-lookup St x rel) p ]c ⟧ᶜᵗ
                 (subᶜ M split-[] (subV (unbox-lookup St x rel) p) pM
                    (unbox-lookupᴾ St x rel pSt))
               ∘ᵐ ⟦ St ⟧ˢ pSt
sound-UNBOX St x rel p M pSt pM =
    ∘ᵐ-congˡ (unbox-def x rel p M pM)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
              ,   ∘ᵐ-assoc _ _ _
                ∙ ∘ᵐ-congʳ (≈ᵐ-sym (unbox-lookup-sound St x rel pSt))
                ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (C-subst-nat M split-[] (subV (unbox-lookup St x rel) p) pM
                        (unbox-lookupᴾ St x rel pSt)))

