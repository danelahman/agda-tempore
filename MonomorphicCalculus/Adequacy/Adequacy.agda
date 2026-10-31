------------------------------------------------------------------------
-- Adequacy of the denotational semantics w.r.t. the operational one. --
--                                                                    --
-- The converse direction of `⟶*-sound`. Assembled from               --
--                                                                    --
--   * whnf existence: `Termination.halts` (syntactic)                --
--   * the whnf denotes the source: `⟶*-sound`                        --
--   * head faithfulness: `HeadFaithful` (model side)                 --
--                                                                    --
-- Stated for two programs: `⟦ M ⟧ ≈ᵐ ⟦ N ⟧` implies they halt with   --
-- the same shape, at the same operation, with the same answer.       --
--                                                                    --
-- Scope: the machine `⟶`, where unhandled operations stop computing  --
-- and denotations live in the tree monad `Tᵒ`.                       --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_)

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

import MonomorphicCalculus.Adequacy.HeadFaithful as HF

module MonomorphicCalculus.Adequacy.Adequacy
         (Spec : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades Spec)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades Spec)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades Spec)) Fut Pst)
         (GTy : GroundTypes Spec Cat Fut)
         (Mon : Monad Spec Cat Fut Pst Adj GTy)
         (GE : GroundEternal Spec Cat Fut Pst Adj GTy)
         -- the two model-side assumptions
         (hf : HF.HeadFaithful  Spec Cat Fut Pst Adj GTy Mon GE)
         (bf : HF.BaseFaithful  Spec Cat Fut Pst Adj GTy Mon GE)
       where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts Spec
open import MonomorphicCalculus.Syntax.Terms    Spec
open import MonomorphicCalculus.Syntax.Types    Spec

open import MonomorphicCalculus.OperationalSemantics.Reduction           Spec
open import MonomorphicCalculus.OperationalSemantics.State               Spec

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ)
open Past Pst using (⟨_⟩ᵒ)
open Adjunction Adj using (η⊣)
open GroundTypes GTy using (⟦_⟧ᵍ; ⟦_⟧ᵇ; ⟦_⟧ᵇᶜ)
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types     Spec Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Subtyping Spec Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts Spec Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms    Spec Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.State    Spec Cat Fut Pst Adj GTy Mon GE

open import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation   Spec Cat Fut Pst Adj GTy Mon GE

open import MonomorphicCalculus.OperationalSemantics.Evaluation               Spec
open import MonomorphicCalculus.Adequacy.HeadFaithful                         Spec Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.OperationalSemantics.Termination              Spec
open import MonomorphicCalculus.OperationalSemantics.Termination.Reducibility Spec

open HF.HeadFaithful hf
open HF.BaseFaithful bf

-- Two programs halt alike: same return-or-stuck shape, same operation.

record Same-whnf {A : VType} {ε : E} (M N : Prog A ε) : Set where

  field

    same-ret : Ret-whnf (⟨ ∅ , M ⟩) → Ret-whnf (⟨ ∅ , N ⟩)

    same-op  : (w : Op-whnf (⟨ ∅ , M ⟩))
             → Σ[ w' ∈ Op-whnf (⟨ ∅ , N ⟩) ] Op-whnf.oper w ≡ Op-whnf.oper w'

-- Post-composing the functorial action passes into a Kleisli composite, and
-- through each of the two head shapes: `ηᵀ` and `opᵀ` are natural.

Tᶠ-⋄ : ∀ {X Y Z Z' : Obj} {ε ε' : E} → (g : Z →ᵐ Z')
     → (h : Y →ᵐ Tᵒ Z ε') → (d : X →ᵐ Tᵒ Y ε)
     → Tᶠ g ∘ᵐ (h ⋄ d) ≈ᵐ (Tᶠ g ∘ᵐ h) ⋄ d
Tᶠ-⋄ g h d =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc (Tᶠ g) μᵀ (Tᶠ h ∘ᵐ d)))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (μᵀ-nat g)))
      (≈ᵐ-trans (∘ᵐ-assoc μᵀ (Tᶠ (Tᶠ g)) (Tᶠ h ∘ᵐ d))
        (∘ᵐ-congʳ (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc (Tᶠ (Tᶠ g)) (Tᶠ h) d))
                            (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ (Tᶠ g) h)))))))

Tᶠ-leafᵐ : ∀ {X Y Z : Obj} → (g : X →ᵐ Z) → (a : Y →ᵐ X)
         → Tᶠ g ∘ᵐ leafᵐ a ≈ᵐ leafᵐ (g ∘ᵐ a)
Tᶠ-leafᵐ g a =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc (Tᶠ g) ηᵀ a))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (ηᵀ-nat g))) (∘ᵐ-assoc ηᵀ g a))

Tᶠ-nodeᵐ : ∀ {X X' Y : Obj} {ε : E} → (g : X →ᵐ X') → (op : Op)
         → (w : Y →ᵐ ⟦ param op ⟧ᵍ)
         → (k : Y →ᵐ [ ∣ op-grade op ∣ᵉ ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ X ε))
         → Tᶠ g ∘ᵐ nodeᵐ op w k
         ≈ᵐ nodeᵐ op w ([ ∣ op-grade op ∣ᵉ ]ᶠ (map⇒ᵐ idᵐ (Tᶠ g)) ∘ᵐ k)
Tᶠ-nodeᵐ g op w k =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc (Tᶠ g) (opᵀ op) ⟨ w , k ⟩ᵐ))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (opᵀ-nat op g)))
      (≈ᵐ-trans (∘ᵐ-assoc (opᵀ op) _ ⟨ w , k ⟩ᵐ)
        (∘ᵐ-congʳ (≈ᵐ-trans (mapˣᵐ-∘⟨⟩ idᵐ _ w k)
                            (⟨ ∘ᵐ-identityˡ w , ≈ᵐ-refl ⟩ᵐ-cong)))))

-- A program is its whnf, coerced along the run's refinement and run after the
-- run's transition, then coerced back to the program's grade: `⟶*-sound` at
-- the empty state (`hist ∅ ≡ []`, so `⟦ [] ⟧ᶜᵗˣ = 𝟙ᵐ` and the empty
-- environment is `idᵐ`).

program-run-sound : ∀ {A B ε ε'} {cf' : Config (B ‼ ε')}
                  → (M : Prog A ε) → (pM : Paramᶜ M)
                  → (rs : ⟨ ∅ , M ⟩ ⟶* cf')
                  → ⟦ M ⟧ᵖ pM
                  ≈ᵐ delayedᵐ (Tᶠ ⟦ run-refines-type rs ⟧<:ᵛ
                                 ∘ᵐ ⟦ cf' ⟧ᶜᶠ (stepsᴾᶜᶠ rs (tt , pM)))
                              (stepsᵀ rs) (steps-≾ rs)

program-run-sound M pM rs =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityʳ (⟦ M ⟧ᵖ pM)))
    (≈ᵐ-trans (⟶*-sound rs (tt , pM) (uniform⟶* rs (tt , pM)))
              (∘ᵐ-congʳ (Tᶠ-⋄ _ _ _)))

-- The value a whnf returns, at the program's own type: a run refines the type,
-- so the value stands at a subtype of it.

ret-value : ∀ {A ε} {M : Prog A ε} → (w : Ret-whnf (⟨ ∅ , M ⟩))
          → toCtx (Ret-whnf.state w) ⊢V⦂ A
ret-value w = subV (Ret-whnf.value w) (run-refines-type (Ret-whnf.run w))

-- The two head presentations of a program, read off a whnf it reaches.

ret-presentation : ∀ {A ε} → (M : Prog A ε) → (pM : Paramᶜ M)
                 → (w : Ret-whnf (⟨ ∅ , M ⟩))
                 → Σ[ Y ∈ Obj ] Σ[ δ ∈ E ] Σ[ a ∈ (Y →ᵐ ⟦ A ⟧ᵛ) ]
                   Σ[ d ∈ (𝟙ᵐ →ᵐ Tᵒ Y δ) ] Σ[ nd ∈ Delaysᵐ d (ret-ticks w) ]
                   Σ[ r ∈ (δ ·ₑ 𝟏ₑ ≾ₑ ε) ]
                     (⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (leafᵐ a) d r)
ret-presentation M pM (ret-whnf St A₀ V rs) =
    _ , _ , _ , _ , stepsᵀ-delays rs , steps-≾ rs
  , ≈ᵐ-trans (program-run-sound M pM rs)
      (delayedᵐ-cong (stepsᵀ rs) (steps-≾ rs)
        (≈ᵐ-trans (∘ᵐ-congʳ (proj₂ (ret-whnf-shape V _ _)))
                  (Tᶠ-leafᵐ _ _)))

op-presentation : ∀ {A ε} → (M : Prog A ε) → (pM : Paramᶜ M)
                → (w : Op-whnf (⟨ ∅ , M ⟩))
                → Σ[ Y ∈ Obj ] Σ[ δ ∈ E ] Σ[ ε₂ ∈ E ]
                  Σ[ v ∈ (Y →ᵐ ⟦ param (Op-whnf.oper w) ⟧ᵍ) ]
                  Σ[ k ∈ (Y →ᵐ [ ∣ op-grade (Op-whnf.oper w) ∣ᵉ ]ᵒ
                                 (⟦ arity (Op-whnf.oper w) ⟧ᵍ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ ε₂)) ]
                  Σ[ d ∈ (𝟙ᵐ →ᵐ Tᵒ Y δ) ] Σ[ nd ∈ Delaysᵐ d (op-ticks w) ]
                  Σ[ r ∈ (δ ·ₑ (op-grade (Op-whnf.oper w) ·ₑ ε₂) ≾ₑ ε) ]
                    (⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (nodeᵐ (Op-whnf.oper w) v k) d r)
op-presentation M pM (op-whnf St op ε' A₀ W M' rs) =
    _ , _ , _ , _ , _ , _ , stepsᵀ-delays rs , steps-≾ rs
  , ≈ᵐ-trans (program-run-sound M pM rs)
      (delayedᵐ-cong (stepsᵀ rs) (steps-≾ rs)
        (≈ᵐ-trans (∘ᵐ-congʳ (proj₂ (proj₂ (op-whnf-shape W M' _ _ _))))
                  (Tᶠ-nodeᵐ _ op _ _)))

-- Equal denotations cannot halt in different shapes, and when both get stuck
-- it is on the same operation: the two presentations meet at `ret≢op`
-- resp. `op-inj`.

ret-vs-op : ∀ {A ε} → {M N : Prog A ε}
          → (pM : Paramᶜ M) → (pN : Paramᶜ N)
          → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
          → Ret-whnf (⟨ ∅ , M ⟩) → Op-whnf (⟨ ∅ , N ⟩)
          -------------------------------------------
          → ⊥
ret-vs-op {M = M} {N = N} pM pN e wM wN
  with ret-presentation M pM wM | op-presentation N pN wN
... | _ , _ , _ , _ , ndM , rM , eM
    | _ , _ , _ , _ , _ , _ , ndN , rN , eN =
  ret≢op ndM ndN rM rN (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN))

same-oper : ∀ {A ε} → {M N : Prog A ε}
          → (pM : Paramᶜ M) → (pN : Paramᶜ N)
          → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
          → (wM : Op-whnf (⟨ ∅ , M ⟩)) → (wN : Op-whnf (⟨ ∅ , N ⟩))
          ---------------------------------------------------------
          → Op-whnf.oper wM ≡ Op-whnf.oper wN
same-oper {M = M} {N = N} pM pN e wM wN
  with op-presentation M pM wM | op-presentation N pN wN
... | _ , _ , _ , _ , _ , _ , ndM , rM , eM
    | _ , _ , _ , _ , _ , _ , ndN , rN , eN =
  op-inj ndM ndN rM rN (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN))

-- Equal denotations halt alike: `halts` supplies a whnf on each side, and the
-- two lemmas above exclude the mismatched pairing.

adequacy : ∀ {A ε} → {M N : Prog A ε}
         → (pM : Paramᶜ M) → (pN : Paramᶜ N)
         → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
         ----------------------------
         → Same-whnf M N

adequacy {M = M} {N = N} pM pN e = record { same-ret = sr ; same-op = so }
  where
    sr : Ret-whnf (⟨ ∅ , M ⟩) → Ret-whnf (⟨ ∅ , N ⟩)
    sr wM with halts N
    ... | halts-ret wN = wN
    ... | halts-op wN  = ⊥-elim (ret-vs-op pM pN e wM wN)

    so : (wM : Op-whnf (⟨ ∅ , M ⟩))
       → Σ[ wN ∈ Op-whnf (⟨ ∅ , N ⟩) ] Op-whnf.oper wM ≡ Op-whnf.oper wN
    so wM with halts N
    ... | halts-ret wN = ⊥-elim (ret-vs-op pN pM (≈ᵐ-sym e) wN wM)
    ... | halts-op wN  = wN , same-oper pM pN e wM wN

-- The head presentation at base type, with the constant it returns.

-- At a base type the run's refinement is `Baseₛ refl`, whose coercion is the
-- identity, so the whnf's leaf survives it unchanged.

base-run-leaf : ∀ {b A₀} {St : 𝕊 []} → (V : toCtx St ⊢V⦂ A₀)
              → (p : A₀ <:ᵛ Base b)
              → (pSt : Paramˢ St) → (pV : Paramᵛ V)
              → Σ[ c ∈ BaseConstants b ]
                  (base-val (subV V p) ≡ const c)
                × (Tᶠ ⟦ p ⟧<:ᵛ ∘ᵐ ⟦ ⟨ St , return V ⟩ ⟧ᶜᶠ (pSt , pV)
                     ≈ᵐ leafᵐ (⟦ c ⟧ᵇᶜ ∘ᵐ terminalᵐ))

base-run-leaf V (Baseₛ refl) pSt pV with base-leaf-const V pSt pV
... | c , sc , qc =
  c , sc , ≈ᵐ-trans (∘ᵐ-congˡ T-idᵐ) (≈ᵐ-trans (∘ᵐ-identityˡ _) qc)

const-presentation : ∀ {b ε} → (M : Prog (Base b) ε) → (pM : Paramᶜ M)
                   → (w : Ret-whnf (⟨ ∅ , M ⟩))
                   → Σ[ c ∈ BaseConstants b ] Σ[ Y ∈ Obj ] Σ[ δ ∈ E ]
                     Σ[ d ∈ (𝟙ᵐ →ᵐ Tᵒ Y δ) ] Σ[ nd ∈ Delaysᵐ d (ret-ticks w) ]
                     Σ[ r ∈ (δ ·ₑ 𝟏ₑ ≾ₑ ε) ]
                       (base-val (ret-value w) ≡ const c)
                     × (⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (leafᵐ (⟦ c ⟧ᵇᶜ ∘ᵐ terminalᵐ)) d r)

const-presentation M pM (ret-whnf St A₀ V rs)
  with base-run-leaf V (run-refines-type rs) _ _
... | c , sc , qc =
    c , _ , _ , _ , stepsᵀ-delays rs , steps-≾ rs , sc
  , ≈ᵐ-trans (program-run-sound M pM rs)
      (delayedᵐ-cong (stepsᵀ rs) (steps-≾ rs) qc)

-- The returned answers are the same constant: `leaf-const` identifies the two
-- denotations and `const-inj` reflects that to the syntax.

adequacy-base : ∀ {b ε} → {M N : Prog (Base b) ε}
              → (pM : Paramᶜ M) → (pN : Paramᶜ N)
              → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
              → (wM : Ret-whnf (⟨ ∅ , M ⟩)) → (wN : Ret-whnf (⟨ ∅ , N ⟩))
              ------------------------------------------------------------
              → Σ[ c ∈ BaseConstants b ]
                  (base-val (ret-value wM) ≡ const c)
                × (base-val (ret-value wN) ≡ const c)

adequacy-base {M = M} {N = N} pM pN e wM wN
  with const-presentation M pM wM | const-presentation N pN wN
... | cM , _ , _ , _ , ndM , rM , sM , eM
    | cN , _ , _ , _ , ndN , rN , sN , eN
  with const-inj (leaf-const ndM ndN rM rN
                    (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN)))
... | refl = cM , sM , sN

-- A `Bool`-typed value's leaf is one of the two constants', read through its
-- subsumption spine by `bool-val`; the state's environment is absorbed by the
-- terminal object, as at a base constant. Which constant it is has to be
-- carried along, since the two give different leaves.

bool-leaf-value : ∀ {St : 𝕊 []} → (V : toCtx St ⊢V⦂ Bool)
                → (pSt : Paramˢ St) → (pV : Paramᵛ V)
                → ((bool-val V ≡ true)
                   × (⟦ ⟨ St , return V ⟩ ⟧ᶜᶠ (pSt , pV)
                        ≈ᵐ leafᵐ (trueᵐ ∘ᵐ terminalᵐ)))
                ⊎ ((bool-val V ≡ false)
                   × (⟦ ⟨ St , return V ⟩ ⟧ᶜᶠ (pSt , pV)
                        ≈ᵐ leafᵐ (falseᵐ ∘ᵐ terminalᵐ)))

bool-leaf-value (var f x) pSt pV = ⊥-elim (Bool-not-in-toCtx x)
bool-leaf-value {St = St} true pSt pV =
  inj₁ (refl
       , ≈ᵐ-trans (∘ᵐ-assoc ηᵀ (trueᵐ ∘ᵐ terminalᵐ) (⟦ St ⟧ˢ pSt))
           (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-assoc trueᵐ terminalᵐ (⟦ St ⟧ˢ pSt))
                               (∘ᵐ-congʳ terminalᵐ-unique))))
bool-leaf-value {St = St} false pSt pV =
  inj₂ (refl
       , ≈ᵐ-trans (∘ᵐ-assoc ηᵀ (falseᵐ ∘ᵐ terminalᵐ) (⟦ St ⟧ˢ pSt))
           (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-assoc falseᵐ terminalᵐ (⟦ St ⟧ˢ pSt))
                               (∘ᵐ-congʳ terminalᵐ-unique))))
bool-leaf-value (subV V Boolₛ) pSt pV with bool-leaf-value V pSt pV
... | inj₁ (sv , qv) =
  inj₁ (sv , ≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-identityˡ _))) qv)
... | inj₂ (sv , qv) =
  inj₂ (sv , ≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-identityˡ _))) qv)

-- The head presentation at `Bool`, with the boolean it returns.

-- The same at `Bool`, where the run's refinement is `Boolₛ`.

bool-run-leaf : ∀ {A₀} {St : 𝕊 []} → (V : toCtx St ⊢V⦂ A₀) → (p : A₀ <:ᵛ Bool)
              → (pSt : Paramˢ St) → (pV : Paramᵛ V)
              → ((bool-val (subV V p) ≡ true)
                 × (Tᶠ ⟦ p ⟧<:ᵛ ∘ᵐ ⟦ ⟨ St , return V ⟩ ⟧ᶜᶠ (pSt , pV)
                      ≈ᵐ leafᵐ (trueᵐ ∘ᵐ terminalᵐ)))
              ⊎ ((bool-val (subV V p) ≡ false)
                 × (Tᶠ ⟦ p ⟧<:ᵛ ∘ᵐ ⟦ ⟨ St , return V ⟩ ⟧ᶜᶠ (pSt , pV)
                      ≈ᵐ leafᵐ (falseᵐ ∘ᵐ terminalᵐ)))

bool-run-leaf V Boolₛ pSt pV with bool-leaf-value V pSt pV
... | inj₁ (sv , qv) =
  inj₁ (sv , ≈ᵐ-trans (∘ᵐ-congˡ T-idᵐ) (≈ᵐ-trans (∘ᵐ-identityˡ _) qv))
... | inj₂ (sv , qv) =
  inj₂ (sv , ≈ᵐ-trans (∘ᵐ-congˡ T-idᵐ) (≈ᵐ-trans (∘ᵐ-identityˡ _) qv))

bool-presentation : ∀ {ε} → (M : Prog Bool ε) → (pM : Paramᶜ M)
                  → (w : Ret-whnf (⟨ ∅ , M ⟩))
                  → Σ[ Y ∈ Obj ] Σ[ δ ∈ E ]
                    Σ[ d ∈ (𝟙ᵐ →ᵐ Tᵒ Y δ) ] Σ[ nd ∈ Delaysᵐ d (ret-ticks w) ]
                    Σ[ r ∈ (δ ·ₑ 𝟏ₑ ≾ₑ ε) ]
                      ( ((bool-val (ret-value w) ≡ true)
                         × (⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (leafᵐ (trueᵐ ∘ᵐ terminalᵐ)) d r))
                      ⊎ ((bool-val (ret-value w) ≡ false)
                         × (⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (leafᵐ (falseᵐ ∘ᵐ terminalᵐ)) d r)) )

bool-presentation M pM (ret-whnf St A₀ V rs)
  with bool-run-leaf V (run-refines-type rs) _ _
... | inj₁ (sv , qv) =
    _ , _ , _ , stepsᵀ-delays rs , steps-≾ rs
  , inj₁ (sv , ≈ᵐ-trans (program-run-sound M pM rs)
                 (delayedᵐ-cong (stepsᵀ rs) (steps-≾ rs) qv))
... | inj₂ (sv , qv) =
    _ , _ , _ , stepsᵀ-delays rs , steps-≾ rs
  , inj₂ (sv , ≈ᵐ-trans (program-run-sound M pM rs)
                 (delayedᵐ-cong (stepsᵀ rs) (steps-≾ rs) qv))

-- The returned answers are the same boolean.

adequacy-bool : ∀ {ε} → {M N : Prog Bool ε}
              → (pM : Paramᶜ M) → (pN : Paramᶜ N)
              → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
              → (wM : Ret-whnf (⟨ ∅ , M ⟩)) → (wN : Ret-whnf (⟨ ∅ , N ⟩))
              ------------------------------------------------------------
              → ((bool-val (ret-value wM) ≡ true)
                 × (bool-val (ret-value wN) ≡ true))
              ⊎ ((bool-val (ret-value wM) ≡ false)
                 × (bool-val (ret-value wN) ≡ false))

adequacy-bool {M = M} {N = N} pM pN e wM wN
  with bool-presentation M pM wM | bool-presentation N pN wN
... | _ , _ , _ , ndM , rM , inj₁ (sM , eM)
    | _ , _ , _ , ndN , rN , inj₁ (sN , eN) = inj₁ (sM , sN)
... | _ , _ , _ , ndM , rM , inj₂ (sM , eM)
    | _ , _ , _ , ndN , rN , inj₂ (sN , eN) = inj₂ (sM , sN)
... | _ , _ , _ , ndM , rM , inj₁ (sM , eM)
    | _ , _ , _ , ndN , rN , inj₂ (sN , eN) =
      ⊥-elim (true≉false
        (leaf-bool ndM ndN rM rN
          (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN))))
... | _ , _ , _ , ndM , rM , inj₂ (sM , eM)
    | _ , _ , _ , ndN , rN , inj₁ (sN , eN) =
      ⊥-elim (true≉false
        (leaf-bool ndN ndM rN rM
          (≈ᵐ-trans (≈ᵐ-sym eN) (≈ᵐ-trans (≈ᵐ-sym e) eM))))

-- A point presented as a delayed leaf, resp. a delayed operation node,
-- dictates how the program halts.

leaf-adequacy : ∀ {A ε Y δ n} → {M : Prog A ε} → (pM : Paramᶜ M)
              → {a : Y →ᵐ ⟦ A ⟧ᵛ}
              → {d : 𝟙ᵐ →ᵐ Tᵒ Y δ} → Delaysᵐ d n
              → (r : δ ·ₑ 𝟏ₑ ≾ₑ ε)
              → ⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (leafᵐ a) d r
              -------------------------------------
              → Ret-whnf (⟨ ∅ , M ⟩)

leaf-adequacy {M = M} pM nd r eq = go (halts M)
  where
    go : Halts (⟨ ∅ , M ⟩) → Ret-whnf (⟨ ∅ , M ⟩)
    go (halts-ret w) = w
    go (halts-op w) with op-presentation M pM w
    ... | _ , _ , _ , _ , _ , _ , ndO , rO , eO =
      ⊥-elim (ret≢op nd ndO r rO (≈ᵐ-trans (≈ᵐ-sym eq) eO))

node-adequacy : ∀ {A ε ε₂ Y δ n op} → {M : Prog A ε} → (pM : Paramᶜ M)
              → {v : Y →ᵐ ⟦ param op ⟧ᵍ}
              → {k : Y →ᵐ [ ∣ op-grade op ∣ᵉ ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ ε₂)}
              → {d : 𝟙ᵐ →ᵐ Tᵒ Y δ} → Delaysᵐ d n
              → (r : δ ·ₑ (op-grade op ·ₑ ε₂) ≾ₑ ε)
              → ⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (nodeᵐ op v k) d r
              ------------------------------------------
              → Σ[ w' ∈ Op-whnf (⟨ ∅ , M ⟩) ] Op-whnf.oper w' ≡ op

node-adequacy {op = op} {M = M} pM nd r eq = go (halts M)
  where
    go : Halts (⟨ ∅ , M ⟩)
       → Σ[ w' ∈ Op-whnf (⟨ ∅ , M ⟩) ] Op-whnf.oper w' ≡ op
    go (halts-ret w) with ret-presentation M pM w
    ... | _ , _ , _ , _ , ndR , rR , eR =
      ⊥-elim (ret≢op ndR nd rR r (≈ᵐ-trans (≈ᵐ-sym eR) eq))
    go (halts-op w) with op-presentation M pM w
    ... | _ , _ , _ , _ , _ , _ , ndO , rO , eO =
      w , sym (op-inj nd ndO r rO (≈ᵐ-trans (≈ᵐ-sym eq) eO))

-- Under `HeadTimed`, equal denotations also take the same time (`ret-ticks-eq`
-- at the presentations' tick totals).

adequacy-ticks : HF.HeadTimed Spec Cat Fut Pst Adj GTy Mon GE
               → ∀ {A ε} → {M N : Prog A ε}
               → (pM : Paramᶜ M) → (pN : Paramᶜ N)
               → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
               → (wM : Ret-whnf (⟨ ∅ , M ⟩)) → (wN : Ret-whnf (⟨ ∅ , N ⟩))
               -----------------------------------------------------------
               → ret-ticks wM ≡ ret-ticks wN

adequacy-ticks ht {M = M} {N = N} pM pN e wM wN
  with ret-presentation M pM wM | ret-presentation N pN wN
... | _ , _ , _ , _ , ndM , rM , eM
    | _ , _ , _ , _ , ndN , rN , eN =
  HF.HeadTimed.ret-ticks-eq ht ndM ndN rM rN
    (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN))

-- Every program halts in exactly one of the two shapes; equal denotations
-- pick the same one.

ret-not-op : ∀ {A ε} → {M N : Prog A ε}
           → (pM : Paramᶜ M) → (pN : Paramᶜ N)
           → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
           → Ret-whnf (⟨ ∅ , M ⟩) → Op-whnf (⟨ ∅ , N ⟩)
           → ⊥
ret-not-op pM pN e wM wN =
  ⇓-exclusive (Same-whnf.same-ret (adequacy pM pN e) wM) wN

-- And the operation a stuck program is stuck on is a denotational invariant.

same-operation : ∀ {A ε} → {M N : Prog A ε}
               → (pM : Paramᶜ M) → (pN : Paramᶜ N)
               → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
               → (w : Op-whnf (⟨ ∅ , M ⟩)) → (w' : Op-whnf (⟨ ∅ , N ⟩))
               → Op-whnf.oper w ≡ Op-whnf.oper w'
same-operation pM pN e w w' with Same-whnf.same-op (adequacy pM pN e) w
... | w'' , eq = trans eq (proj₁ (op-whnf-unique w'' w'))
