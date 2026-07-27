open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module OperationalSemantics.Soundness.Preservation.Unbox
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

open import Syntax.Types     S
open import Syntax.Contexts  S
open import Syntax.Language  S
open import Syntax.Renamings S
open import Syntax.RenActions S using (V-rename; C-rename; unbox⇒var; var-rename)
open import Syntax.Substitutions S

open import OperationalSemantics.State S
open import OperationalSemantics.PreservationTheorem S

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

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.State S Cat Fut Pst Adj GTy Mon GE

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)
import DenotationalSemantics.Model.HandlerAlgebra S Cat Fut Pst Adj GTy as HC
open import OperationalSemantics.Soundness.Preservation.HandleOpCont S Cat Fut Pst Adj GTy Mon GE
  using (handle-op-cont)
open import OperationalSemantics.Soundness.Preservation.HandleOpClause S Cat Fut Pst Adj GTy Mon GE
  using (term∅; ∅-terminal; clause-sound)

open import OperationalSemantics.Soundness.Preservation.Base S Cat Fut Pst Adj GTy Mon GE public

-- UNBOX = LOOKUP
--
-- A cell `x` of the store was allocated by some prefix of the state, namely
-- `split-state-fst St x`, and the value it holds lives in *that* prefix's
-- context, locked by the cell's own resource `ρ`. Reading the cell therefore
-- has to reach back to the world where it was allocated. `state-past` is that
-- reach-back: the past-view, at the cell's accumulated grade `ρ'`, of the
-- sub-state that allocated it.

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

-- THE SYNTACTIC BRIDGE
--
-- `unbox-lookup` renames the stored value out of the allocating prefix's
-- context into `toCtx S`, through a composite of transports, a
-- `wk-ren-⟨ρ⟩-ctx`, and the grade relaxation `⟨⟩-≤-ren rel`. That composite
-- denotes `state-past`.
--
-- `wk-ren-⟨ρ⟩-ctx` matches its grade equality against `refl`, but the grade
-- `ρ'` occurs inside `split-state-snd St x`, whose type mentions
-- `x : … ∈[ ρ' ] …`, so specialising it is circular. The grade coercion is
-- therefore carried explicitly as a `⟨⟩-≤` at an arbitrary witness (the order
-- being proof-irrelevant), and the induction reconciles witnesses with
-- `⟨⟩-≤-irr`.

-- The grade a cell's suffix accumulates is the cell's own grade. (This is the
-- equality `unbox-lookup` feeds to `wk-ren-⟨ρ⟩-ctx`.)

cell-grade : ∀ {A ρ ρ'} → (St : 𝕊 []) → (x : [ ρ ] A ∈[ ρ' ] toCtx St)
           → ctx-grade (([] ∷ [ ρ ] A) ++ᶜ toCtx (split-state-snd St x)) ≡ ρ'
cell-grade {A = A} {ρ = ρ} St x =
  trans
    (trans
      (trans
        (ctx-grade-++ᶜ ([] ∷ [ ρ ] A) (toCtx (split-state-snd St x)))
        (·ᵣ-identityˡ (ctx-grade (toCtx (split-state-snd St x)))))
      (sym (grades-≡ (split-state-snd St x))))
    (snd-split-time≡time-from-head St x)

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
    p₀ = ≾ᵣ-reflexive (sym (cell-grade St y))

-- The grade equality that `wk-ren-⟨ρ⟩-ctx` carries can be split off as a
-- `⟨⟩-≤` (here `Γ`, `Γ'` and `ρ` are independent, so the equality *can* be
-- matched, unlike inside `past-core`).

wk-lock-≤ : ∀ {Γ Γ' ρ} → (e : ctx-grade Γ' ≡ ρ)
          → ⟦ wk-ren-⟨ρ⟩-ctx {Γ} {Γ'} e ⟧ʳ
          ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive e) ∘ᵐ ⟦ wk-ren-⟨ρ⟩-ctx {Γ} {Γ'} refl ⟧ʳ
wk-lock-≤ refl =
  ≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩-≤-irr _ ≾ᵣ-refl ∙ ⟨⟩-≤-refl) ∙ ∘ᵐ-identityˡ _)

-- UNBOX
--
-- Reading the resource an `unbox` refers to, out of the state's environment,
-- is exactly the value stored in it. The cell was written by `box`, i.e. by
-- `[ ρ ]ᶠ ⟦V⟧ ∘ᵐ η⊣`; the read is `ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj`, and `ε⊣`
-- cancels the `η⊣` by the triangle identity. The grade relaxation `rel` is
-- what gates the read: it is the proof that enough resources have elapsed.

-- The looked-up resource is the stored value renamed, so its certificate is
-- the stored one's, renamed the same way.
unbox-lookupᴾ : ∀ {A ρ Δ} → (St : 𝕊 [])
              → (w : Ren [] (Δ ⟨ ρ ⟩) (toCtx St)) → (V : Δ ⊢V⦂ [ ρ ] A)
              → Paramˢ St → Paramᵛ (unbox-lookup St w V)
unbox-lookupᴾ {A} {ρ} St w V pSt =
  renᵛ
    (   eq-ren (split-state-++ᶜ St z)
     ∘ʳ eq-ren (sym (++ᶜ-assoc _ ([] ∷ [ ρ ] A) _))
     ∘ʳ wk-ren-⟨ρ⟩-ctx
          (trans
            (trans
              (trans
                (ctx-grade-++ᶜ ([] ∷ [ ρ ] A) (toCtx (split-state-snd St z)))
                (·ᵣ-identityˡ (ctx-grade (toCtx (split-state-snd St z)))))
              (sym (grades-≡ (split-state-snd St z))))
            (snd-split-time≡time-from-head St z))
     ∘ʳ ⟨⟩-≤-ren (proj₂ (proj₂ (unbox⇒var w V)))
     ∘ʳ eq-ren ++ᶜ-identityˡ)
    (resource-lookup St z) (resource-lookupᴾ St z pSt)
  where
    z = proj₁ (proj₂ (unbox⇒var w V))

unbox-lookup-sound : ∀ {A ρ Δ} → (St : 𝕊 [])
                   → (w : Ren [] (Δ ⟨ ρ ⟩) (toCtx St)) → (V : Δ ⊢V⦂ [ ρ ] A)
                   → (pSt : Paramˢ St)
                   → ⟦ unbox-lookup St w V ⟧ᵛᵗ (unbox-lookupᴾ St w V pSt) ∘ᵐ ⟦ St ⟧ˢ pSt
                   ≈ᵐ (ε⊣ ∘ᵐ ⟨⟩-≤ (proj₂ (proj₂ (unbox⇒var w V)))
                          ∘ᵐ var-proj (proj₁ (proj₂ (unbox⇒var w V))))
                      ∘ᵐ ⟦ St ⟧ˢ pSt
unbox-lookup-sound {A} {ρ} St w V pSt with grad-typ⇒var V
... | _ , y , f , refl with var-rename w (Tl-⟨⟩ y)
... | ρ' , bound , x =
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
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (wk-lock-≤ {toCtx (split-state-fst St x)}
                             {([] ∷ [ ρ ] A) ++ᶜ toCtx (split-state-snd St x)}
                             (cell-grade St x)))))
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
    rel : ρ' ≾ᵣ ρ
    rel = ≾ᵣ-trans (bound (λ ()))
            (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (f (λ ()))) (≾ᵣ-reflexive (·ᵣ-identityˡ ρ)))

    p₀ = ≾ᵣ-reflexive (sym (cell-grade St x))

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

-- `⟦_⟧ᶜᵗ` matches on `unbox⇒var`, so name its result to let the clause reduce.

unbox-def : ∀ {Γ A C ρ Δ} → (w : Ren [] (Δ ⟨ ρ ⟩) Γ) → (V : Δ ⊢V⦂ [ ρ ] A)
          → (M : Γ ∷ A ⊢C⦂ C) → (pV : Paramᵛ V) → (pM : Paramᶜ M)
          → ⟦ unbox w V M ⟧ᶜᵗ (pV , pM)
          ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨⟩-≤ (proj₂ (proj₂ (unbox⇒var w V)))
                                      ∘ᵐ var-proj (proj₁ (proj₂ (unbox⇒var w V))) ⟩ᵐ
unbox-def w V M pV pM with unbox⇒var w V
... | _ , _ , _ = ≈ᵐ-refl

-- UNBOX: substituting the looked-up resource is reading the cell.

sound-UNBOX : ∀ {A C ρ Δ} → (St : 𝕊 []) → (w : Ren [] (Δ ⟨ ρ ⟩) (toCtx St))
            → (V : Δ ⊢V⦂ [ ρ ] A) → (M : toCtx St ∷ A ⊢C⦂ C)
            → (pSt : Paramˢ St) → (pV : Paramᵛ V) → (pM : Paramᶜ M)
            → ⟦ unbox w V M ⟧ᶜᵗ (pV , pM) ∘ᵐ ⟦ St ⟧ˢ pSt
            ≈ᵐ ⟦ M [ Hd ↦ unbox-lookup St w V ]c ⟧ᶜᵗ
                 (subᶜ M Hd (unbox-lookup St w V) pM (unbox-lookupᴾ St w V pSt))
               ∘ᵐ ⟦ St ⟧ˢ pSt
sound-UNBOX St w V M pSt pV pM =
    ∘ᵐ-congˡ (unbox-def w V M pV pM)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ≈ᵐ-sym (unbox-lookup-sound St w V pSt) ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (C-subst-nat M Hd (unbox-lookup St w V) pM
                        (unbox-lookupᴾ St w V pSt)))

