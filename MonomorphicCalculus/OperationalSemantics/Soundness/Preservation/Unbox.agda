open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundEternal
open import MonomorphicCalculus.DenotationalSemantics.Model.Monad

module MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Unbox
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

open import MonomorphicCalculus.Syntax.Types S
open import MonomorphicCalculus.Syntax.Contexts  S
open import MonomorphicCalculus.Syntax.Terms  S
open import MonomorphicCalculus.Syntax.Renaming  S
open import MonomorphicCalculus.Syntax.Renaming.Action S using (V-rename; C-rename; var-rename)
open import MonomorphicCalculus.Syntax.Substitution  S

open import MonomorphicCalculus.OperationalSemantics.State S
open import MonomorphicCalculus.OperationalSemantics.Reduction           S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-congᶠ; []-idᵐ; []-∘ᵐ; []-≤; []-≤-refl; []-≤-nat;
                       []-ε-nat; []-ε∘ηᵘ≡id; ηᵘ; δ; []-δ-nat; []-monoidal; []-≤-trans;
                       []-monoidal-nat; []-monoidal-fstᵐ; []-monoidal-sndᵐ; []-monoidal-η;
                       []-𝟙-unique) renaming (ε to εᵇ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; μ; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ; ⟨⟩-η-nat; ⟨⟩-μ-nat;
                     ⟨⟩-≤-nat; ⟨⟩-≤-irr; ⟨⟩-≤-refl; ⟨⟩-≤-trans; μ-≤ˡ; μ-≤ʳ;
                     ⟨⟩-μ∘Tη≡id; ⟨⟩-μ∘η≡id)
open Adjunction Adj using (η⊣; η⊣-nat; η⊣-𝟏; η⊣-≤; η⊣-δ; η⊣-monoidal;
                           ε⊣; ε⊣-nat; triangleˡ)
open GroundTypes GTy using (⟦_⟧ᵍ)
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.State S Cat Fut Pst Adj GTy Mon GE

open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Base S Cat Fut Pst Adj GTy Mon GE public

-- `UNBOX` = lookup: a cell `x` was allocated by some prefix of the state
-- (`split-state-fst 𝕊 x`), so reading it has to reach back to that world.
-- `state-past` is that reach-back: the past-view, at the cell's accumulated
-- grade `ρ'`, of the sub-state that allocated it.

state-past : ∀ {A ρ ρ'} → (𝕊 : State []) → (x : [ ρ ] A ∈[ ρ' ] toCtx 𝕊)
           → Paramˢ 𝕊
           → ⟦ hist 𝕊 ⟧ᶜᵗˣ →ᵐ ⟨ ρ' ⟩ᵒ ⟦ toCtx (split-state-fst 𝕊 x) ⟧ᶜᵗˣ
state-past (𝕊 ⟨ σ ⟩ₛ) (Tl-⟨⟩ y) pSt        = μ ∘ᵐ ⟨ σ ⟩ᶠ (state-past 𝕊 y pSt)
state-past (𝕊 ∷ₛ W)   Hd        (pSt , _)  = η ∘ᵐ ⟦ 𝕊 ⟧ˢ pSt
state-past (𝕊 ∷ₛ W)   (Tl-∷ y)  (pSt , _)  = state-past 𝕊 y pSt

-- Projecting a cell out of the state's environment recovers the value stored
-- in it, boxed by `η⊣` (the `box` morphism, which put it there) and viewed
-- from the past in which it was allocated.
--
-- Each case is a naturality law of the modality against the corresponding
-- clause of `⟦_⟧ˢ`: `Hd` is `η`'s naturality against the cell just written,
-- `Tl-∷` drops a later cell by `fstᵐ`, and `Tl-⟨⟩` folds a modality with `μ`'s
-- naturality, the grades multiplying as `ctx-grade` says.

state-lookup : ∀ {A ρ ρ'} → (𝕊 : State []) → (x : [ ρ ] A ∈[ ρ' ] toCtx 𝕊)
             → (pSt : Paramˢ 𝕊)
             → var-proj x ∘ᵐ ⟦ 𝕊 ⟧ˢ pSt
             ≈ᵐ ⟨ ρ' ⟩ᶠ ([ ρ ]ᶠ (⟦ resource-lookup 𝕊 x ⟧ᵛᵗ (resource-lookupᴾ 𝕊 x pSt)
                                   ∘ᵐ ⟦ eq-ren (++ᶜ-identityˡ
                                        {toCtx (split-state-fst 𝕊 x) ⟨ ρ ⟩}) ⟧ʳ)
                                 ∘ᵐ η⊣)
                ∘ᵐ state-past 𝕊 x pSt

state-lookup (𝕊 ∷ₛ W) Hd (pSt , pW) =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-η-nat _))
  ∙ ∘ᵐ-assoc _ _ _

state-lookup (𝕊 ∷ₛ W) (Tl-∷ y) (pSt , pW) =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-identityˡ _)
  ∙ state-lookup 𝕊 y pSt

state-lookup (𝕊 ⟨ σ ⟩ₛ) (Tl-⟨⟩ y) pSt =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
  ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ (state-lookup 𝕊 y pSt))
  ∙ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-μ-nat _))
  ∙ ∘ᵐ-assoc _ _ _

-- `unbox-lookup` renames the stored value out of the allocating prefix's
-- context into `toCtx 𝕊`, through a composite of transports, a
-- `wk-ren-⟨ρ⟩-ctx`, and the grade relaxation `⟨⟩-≤-ren rel`; that composite
-- denotes `state-past`. The grade coercion is carried explicitly as a `⟨⟩-≤`
-- at an arbitrary witness, since `ρ'` occurs inside `split-state-snd 𝕊 x`'s
-- own type and so cannot be specialised against `refl`.

-- The grade a cell's suffix accumulates is the cell's own grade. (This is the
-- equality `unbox-lookup` feeds to `wk-ren-⟨ρ⟩-ctx`.)

cell-grade : ∀ {A ρ ρ'} → (𝕊 : State []) → (x : [ ρ ] A ∈[ ρ' ] toCtx 𝕊)
           → ctx-grade (([] ∷ [ ρ ] A) ++ᶜ toCtx (split-state-snd 𝕊 x)) ≃ᵣ ρ'
cell-grade {A = A} {ρ = ρ} 𝕊 x =
  ≃ᵣ-trans
    (≃ᵣ-trans
      (≃ᵣ-trans
        (ctx-grade-++ᶜ ([] ∷ [ ρ ] A) (toCtx (split-state-snd 𝕊 x)))
        (·ᵣ-identityˡ (ctx-grade (toCtx (split-state-snd 𝕊 x)))))
      (≃ᵣ-reflexive (sym (grades-≡ (split-state-snd 𝕊 x)))))
    (≃ᵣ-reflexive (snd-split-time≡time-from-head 𝕊 x))

-- The renaming composite of `unbox-lookup`, minus the grade relaxation and the
-- `[] ++ᶜ_` transport, denotes the reach-back into the allocating prefix.

past-core : ∀ {A ρ ρ'} → (𝕊 : State []) → (x : [ ρ ] A ∈[ ρ' ] toCtx 𝕊)
          → (pSt : Paramˢ 𝕊)
          → (p : ρ' ≾ᵣ ctx-grade (([] ∷ [ ρ ] A) ++ᶜ toCtx (split-state-snd 𝕊 x)))
          → ⟦ wk-ren-⟨ρ⟩-ctx {toCtx (split-state-fst 𝕊 x)}
                             {([] ∷ [ ρ ] A) ++ᶜ toCtx (split-state-snd 𝕊 x)} refl ⟧ʳ
              ∘ᵐ ⟦ eq-ren (sym (++ᶜ-assoc (toCtx (split-state-fst 𝕊 x)) ([] ∷ [ ρ ] A)
                                          (toCtx (split-state-snd 𝕊 x)))) ⟧ʳ
              ∘ᵐ ⟦ eq-ren (split-state-++ᶜ 𝕊 x) ⟧ʳ
              ∘ᵐ ⟦ 𝕊 ⟧ˢ pSt
            ≈ᵐ ⟨⟩-≤ p ∘ᵐ state-past 𝕊 x pSt

-- the cell was just allocated: drop it with `fstᵐ`, and the reach-back is `η`
past-core (𝕊 ∷ₛ W) Hd (pSt , pW) p =
    ∘ᵐ-congʳ (∘ᵐ-identityˡ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-identityˡ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-identityˡ _)
  ∙ ≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩-≤-irr p ≾ᵣ-refl ∙ ⟨⟩-≤-refl) ∙ ∘ᵐ-identityˡ _)

-- a later cell: it sits in the first component of every transport, so `fstᵐ`
-- pushes straight through to the sub-state
past-core {A} {ρ} (_∷ₛ_ {B} {σ} 𝕊 W) (Tl-∷ y) (pSt , pW) p =
    ∘ᵐ-congʳ (∘ᵐ-congˡ
      (≡→≈ᵐ (cong (λ z → ⟦ eq-ren z ⟧ʳ) (sym-cong {f = _∷ [ σ ] B} assoc))
       ∙ eq-ren-∷ (sym assoc)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (eq-ren-∷ (split-state-++ᶜ 𝕊 y))))
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
  ∙ past-core 𝕊 y pSt p
  where
    assoc = ++ᶜ-assoc (toCtx (split-state-fst 𝕊 y)) ([] ∷ [ ρ ] A)
                      (toCtx (split-state-snd 𝕊 y))

-- a modality: fold it with `μ`, the grades multiplying on both sides
past-core {A} {ρ} (𝕊 ⟨ σ ⟩ₛ) (Tl-⟨⟩ y) pSt p =
    ∘ᵐ-congʳ (∘ᵐ-congˡ
      (≡→≈ᵐ (cong (λ z → ⟦ eq-ren z ⟧ʳ) (sym-cong {f = _⟨ σ ⟩} assoc))
       ∙ eq-ren-⟨⟩ (sym assoc)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (eq-ren-⟨⟩ (split-state-++ᶜ 𝕊 y))))
  -- everything under the modality is a `⟨ σ ⟩`-image: collect it
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
  ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ (past-core 𝕊 y pSt p₀))
  -- and `μ` absorbs the sub-state's grade coercion (`μ-≤ˡ`)
  ∙ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (μ-≤ˡ p₀))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congˡ (⟨⟩-≤-irr _ p)
  where
    assoc = ++ᶜ-assoc (toCtx (split-state-fst 𝕊 y)) ([] ∷ [ ρ ] A)
                      (toCtx (split-state-snd 𝕊 y))
    p₀ = ≃ᵣ⇒≿ᵣ (cell-grade 𝕊 y)

-- The grade equality that `wk-ren-⟨ρ⟩-ctx` carries can be split off as a
-- `⟨⟩-≤` (here `Γ`, `Γ'` and `ρ` are independent, so the equality can be
-- matched, unlike inside `past-core`).

wk-⟨⟩-≤ : ∀ {Γ Γ' ρ} → (e : ctx-grade Γ' ≡ ρ)
        → ⟦ wk-ren-⟨ρ⟩-ctx {Γ} {Γ'} e ⟧ʳ
        ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive e) ∘ᵐ ⟦ wk-ren-⟨ρ⟩-ctx {Γ} {Γ'} refl ⟧ʳ
wk-⟨⟩-≤ refl =
  ≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩-≤-irr _ ≾ᵣ-refl ∙ ⟨⟩-≤-refl) ∙ ∘ᵐ-identityˡ _)

-- `UNBOX`: reading the resource it refers to, out of the state's environment,
-- is exactly the value stored in it. The read is `ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj`,
-- and `ε⊣` cancels the `η⊣` that `box` wrote by the triangle identity; the
-- grade relaxation `rel` gates the read.

-- The looked-up resource is the stored value renamed, so its certificate is
-- the stored one's, renamed the same way.
unbox-lookupᴾ : ∀ {A ρ ρ'} → (𝕊 : State [])
              → (z : [ ρ ] A ∈[ ρ' ] toCtx 𝕊) → (rel : ρ' ≾ᵣ ρ)
              → Paramˢ 𝕊 → Paramᵛ (unbox-lookup 𝕊 z rel)
unbox-lookupᴾ {A} {ρ} 𝕊 z rel pSt =
  renᵛ
    ((((  eq-ren ++ᶜ-identityˡ
       ∘ʳ ⟨⟩-≤-ren rel)
       ∘ʳ (⟨⟩-≤-ren (≃ᵣ⇒≾ᵣ (≃ᵣ-trans (≃ᵣ-trans (≃ᵣ-trans (ctx-grade-++ᶜ ([] ∷ [ ρ ] A) (toCtx (split-state-snd 𝕊 z))) (·ᵣ-identityˡ (ctx-grade (toCtx (split-state-snd 𝕊 z))))) (≃ᵣ-reflexive (sym (grades-≡ (split-state-snd 𝕊 z))))) (≃ᵣ-reflexive (snd-split-time≡time-from-head 𝕊 z)))) ∘ʳ wk-ren-⟨ρ⟩-ctx refl))
       ∘ʳ eq-ren (sym (++ᶜ-assoc _ ([] ∷ [ ρ ] A) _)))
       ∘ʳ eq-ren (split-state-++ᶜ 𝕊 z))
    (resource-lookup 𝕊 z) (resource-lookupᴾ 𝕊 z pSt)

unbox-lookup-sound : ∀ {A ρ ρ'} → (𝕊 : State [])
                   → (x : [ ρ ] A ∈[ ρ' ] toCtx 𝕊) → (rel : ρ' ≾ᵣ ρ)
                   → (pSt : Paramˢ 𝕊)
                   → ⟦ unbox-lookup 𝕊 x rel ⟧ᵛᵗ (unbox-lookupᴾ 𝕊 x rel pSt)
                       ∘ᵐ ⟦ 𝕊 ⟧ˢ pSt
                   ≈ᵐ (ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj x) ∘ᵐ ⟦ 𝕊 ⟧ˢ pSt
unbox-lookup-sound {A} {ρ} 𝕊 x rel pSt =
    -- the stored value, reindexed by `unbox-lookup`'s renaming composite
    -- (which `∘ʳ` leaves left-nested, so re-associate it first)
      ∘ᵐ-congˡ (V-rename-nat _ (resource-lookup 𝕊 x) (resource-lookupᴾ 𝕊 x pSt))
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
    ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
    ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
    ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
    -- split the grade equality off the `wk-ren-⟨ρ⟩-ctx`, then the rest of the
    -- composite is exactly `past-core`'s reach-back
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (past-core 𝕊 x pSt p₀))))
    -- the two grade coercions cancel
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
        (⟨⟩-≤-trans _ _ ∙ ⟨⟩-≤-irr _ ≾ᵣ-refl ∙ ⟨⟩-≤-refl))))
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _)))
    ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙ ≈ᵐ-sym rhs
  where
    p₀ = ≃ᵣ⇒≿ᵣ (cell-grade 𝕊 x)

    g = ⟦ resource-lookup 𝕊 x ⟧ᵛᵗ (resource-lookupᴾ 𝕊 x pSt)
          ∘ᵐ ⟦ eq-ren (++ᶜ-identityˡ
                 {toCtx (split-state-fst 𝕊 x) ⟨ ρ ⟩}) ⟧ʳ

    rhs : (ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj x) ∘ᵐ ⟦ 𝕊 ⟧ˢ pSt
        ≈ᵐ g ∘ᵐ ⟨⟩-≤ rel ∘ᵐ state-past 𝕊 x pSt
    rhs =
      -- read the cell out of the environment
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (state-lookup 𝕊 x pSt))
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
          → (p : A₀ <:ᵛ A) → (M : Γ ∷ A ⊢ᶜ⦂ C) → (pM : Paramᶜ M)
          → ⟦ unbox x rel p M ⟧ᶜᵗ pM
          ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ idᵐ , ⟦ p ⟧<:ᵛ ∘ᵐ ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj x ⟩ᵐ
unbox-def x rel p M pM = ≈ᵐ-refl

-- UNBOX: substituting the looked-up resource is reading the cell, the payload
-- subsumption riding along on both sides.

sound-UNBOX : ∀ {A A₀ C ρ ρ'} → (𝕊 : State [])
            → (x : [ ρ ] A₀ ∈[ ρ' ] toCtx 𝕊) → (rel : ρ' ≾ᵣ ρ) → (p : A₀ <:ᵛ A)
            → (M : toCtx 𝕊 ∷ A ⊢ᶜ⦂ C)
            → (pSt : Paramˢ 𝕊) → (pM : Paramᶜ M)
            → ⟦ unbox x rel p M ⟧ᶜᵗ pM ∘ᵐ ⟦ 𝕊 ⟧ˢ pSt
            ≈ᵐ ⟦ M [ subV (unbox-lookup 𝕊 x rel) p ]₀ ⟧ᶜᵗ
                 (subᶜ M split-[] (subV (unbox-lookup 𝕊 x rel) p) pM
                    (unbox-lookupᴾ 𝕊 x rel pSt))
               ∘ᵐ ⟦ 𝕊 ⟧ˢ pSt
sound-UNBOX 𝕊 x rel p M pSt pM =
    ∘ᵐ-congˡ (unbox-def x rel p M pM)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
              ,   ∘ᵐ-assoc _ _ _
                ∙ ∘ᵐ-congʳ (≈ᵐ-sym (unbox-lookup-sound 𝕊 x rel pSt))
                ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (C-subst-nat M split-[] (subV (unbox-lookup 𝕊 x rel) p) pM
                        (unbox-lookupᴾ 𝕊 x rel pSt)))

