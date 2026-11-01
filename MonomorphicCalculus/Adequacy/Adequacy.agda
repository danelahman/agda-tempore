------------------------------------------------------------------------
-- Adequacy of the denotational semantics w.r.t. the operational one. --
--                                                                    --
-- The converse direction of `⟶*-sound`. Assembled from               --
--                                                                    --
--   * halting: `termination` (syntactic)                             --
--   * a run denotes its source: `⟶*-sound`                           --
--   * head faithfulness: `HeadFaithful` (model side)                 --
--                                                                    --
-- Stated for two programs: `⟦ M ⟧ ≈ᵐ ⟦ N ⟧` implies they halt with   --
-- the same outcome, and at an answer type with the same answer.      --
--                                                                    --
-- Scope: the machine `⟶`, where unhandled operations stop computing  --
-- and denotations live in the tree monad `Tᵒ`.                       --
------------------------------------------------------------------------

import Data.Bool.Base as Bool
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
open import MonomorphicCalculus.Syntax.Data     Spec using (⌈_⌉ᵇ)

open import MonomorphicCalculus.OperationalSemantics.Reduction           Spec
open import MonomorphicCalculus.OperationalSemantics.State               Spec

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ)
open Past Pst using (⟨_⟩ᵒ)
open Adjunction Adj using (η⊣)
open GroundTypes GTy using (⟦_⟧ᵍ; ⟦_⟧ᵇ; ⟦_⟧ᵇᶜ)
open Monad Mon
open import MonomorphicCalculus.DenotationalSemantics.Model.Comparison Cat using (⌜_⌝ᵇ)

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

-- Two programs halt alike: however the one halts, the other halts with the
-- same outcome.

Same-outcome : ∀ {A ε} → Closed A ε → Closed A ε → Set
Same-outcome M N = (hM : Halts ∅ M) → Σ[ hN ∈ Halts ∅ N ] outcome hM ≡ outcome hN

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

-- A program is the configuration a run reaches, coerced along the run's
-- refinement and run after the run's transition, then coerced back to the
-- program's grade: `⟶*-sound` at the empty state (`hist ∅ ≡ []`, so
-- `⟦ [] ⟧ᶜᵗˣ = 𝟙ᵐ` and the empty environment is `idᵐ`).

program-run-sound : ∀ {A B ε ε'} {cf' : Config (B ! ε')}
                  → (M : Closed A ε) → (pM : Paramᶜ M)
                  → (rs : ⟨ ∅ ∣ M ⟩ ⟶* cf')
                  → ⟦ M ⟧ᵖ pM
                  ≈ᵐ delayedᵐ (Tᶠ ⟦ run-refines-type rs ⟧<:ᵛ
                                 ∘ᵐ ⟦ cf' ⟧ᶜᶠ (stepsᴾᶜᶠ rs (tt , pM)))
                              (stepsᵀ rs) (steps-≾ rs)

program-run-sound M pM rs =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityʳ (⟦ M ⟧ᵖ pM)))
    (≈ᵐ-trans (⟶*-sound rs (tt , pM) (uniform⟶* rs (tt , pM)))
              (∘ᵐ-congʳ (Tᶠ-⋄ _ _ _)))

-- The value a run returns, at the program's own type: a run refines the type,
-- so the value stands at a subtype of it.

ret-value : ∀ {A B ε} {M : Closed A ε} {𝕊 : State []} {V : toCtx 𝕊 ⊢ᵛ⦂ B}
          → ⟨ ∅ ∣ M ⟩ ⟶* ⟨ 𝕊 ∣ return V ⟩
          → toCtx 𝕊 ⊢ᵛ⦂ A
ret-value {V = V} rs = subV V (run-refines-type rs)

-- The two head presentations of a program, read off a run to a finished
-- computation.

ret-presentation : ∀ {A B ε} {𝕊 : State []} {V : toCtx 𝕊 ⊢ᵛ⦂ B}
                 → (M : Closed A ε) → (pM : Paramᶜ M)
                 → (rs : ⟨ ∅ ∣ M ⟩ ⟶* ⟨ 𝕊 ∣ return V ⟩)
                 → Σ[ Y ∈ Obj ] Σ[ δ ∈ E ] Σ[ a ∈ (Y →ᵐ ⟦ A ⟧ᵛ) ]
                   Σ[ d ∈ (𝟙ᵐ →ᵐ Tᵒ Y δ) ] Σ[ nd ∈ Delaysᵐ d (ticks rs) ]
                   Σ[ r ∈ (δ ·ₑ 𝟏ₑ ≾ₑ ε) ]
                     (⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (leafᵐ a) d r)
ret-presentation {V = V} M pM rs =
    _ , _ , _ , _ , stepsᵀ-delays rs , steps-≾ rs
  , ≈ᵐ-trans (program-run-sound M pM rs)
      (delayedᵐ-cong (stepsᵀ rs) (steps-≾ rs)
        (≈ᵐ-trans (∘ᵐ-congʳ (proj₂ (ret-whnf-shape V _ _)))
                  (Tᶠ-leafᵐ _ _)))

op-presentation : ∀ {A B ε ε'} {𝕊 : State []} {op : Op}
                → {W : toCtx 𝕊 ⊢ᵛ⦂ ⌜ param op ⌝ᵍ}
                → {M' : toCtx 𝕊 ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ B ! ε'}
                → (M : Closed A ε) → (pM : Paramᶜ M)
                → (rs : ⟨ ∅ ∣ M ⟩ ⟶* ⟨ 𝕊 ∣ perform op W M' ⟩)
                → Σ[ Y ∈ Obj ] Σ[ δ ∈ E ] Σ[ ε₂ ∈ E ]
                  Σ[ v ∈ (Y →ᵐ ⟦ param op ⟧ᵍ) ]
                  Σ[ k ∈ (Y →ᵐ [ ∣ op-grade op ∣ᵉ ]ᵒ
                                 (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ ε₂)) ]
                  Σ[ d ∈ (𝟙ᵐ →ᵐ Tᵒ Y δ) ] Σ[ nd ∈ Delaysᵐ d (ticks rs) ]
                  Σ[ r ∈ (δ ·ₑ (op-grade op ·ₑ ε₂) ≾ₑ ε) ]
                    (⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (nodeᵐ op v k) d r)
op-presentation {op = op} {W = W} {M' = M'} M pM rs =
    _ , _ , _ , _ , _ , _ , stepsᵀ-delays rs , steps-≾ rs
  , ≈ᵐ-trans (program-run-sound M pM rs)
      (delayedᵐ-cong (stepsᵀ rs) (steps-≾ rs)
        (≈ᵐ-trans (∘ᵐ-congʳ (proj₂ (proj₂ (op-whnf-shape W M' _ _ _))))
                  (Tᶠ-nodeᵐ _ op _ _)))

-- Equal denotations halt with the same outcome: the two presentations meet at
-- `ret≢op` resp. `op-inj`.

same-outcome : ∀ {A ε} → {M N : Closed A ε}
             → (pM : Paramᶜ M) → (pN : Paramᶜ N)
             → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
             → (hM : Halts ∅ M) → (hN : Halts ∅ N)
             -------------------------------------
             → outcome hM ≡ outcome hN

same-outcome pM pN e (_ , _ , _ , _ , _ , is-return _) (_ , _ , _ , _ , _ , is-return _) = refl
same-outcome {M = M} {N = N} pM pN e
  (_ , _ , _ , _ , rsM , is-return _) (_ , _ , _ , _ , rsN , is-perform _ _ _)
  with ret-presentation M pM rsM | op-presentation N pN rsN
... | _ , _ , _ , _ , ndM , rM , eM
    | _ , _ , _ , _ , _ , _ , ndN , rN , eN =
  ⊥-elim (ret≢op ndM ndN rM rN (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN)))
same-outcome {M = M} {N = N} pM pN e
  (_ , _ , _ , _ , rsM , is-perform _ _ _) (_ , _ , _ , _ , rsN , is-return _)
  with op-presentation M pM rsM | ret-presentation N pN rsN
... | _ , _ , _ , _ , _ , _ , ndM , rM , eM
    | _ , _ , _ , _ , ndN , rN , eN =
  ⊥-elim (ret≢op ndN ndM rN rM (≈ᵐ-trans (≈ᵐ-sym eN) (≈ᵐ-trans (≈ᵐ-sym e) eM)))
same-outcome {M = M} {N = N} pM pN e
  (_ , _ , _ , _ , rsM , is-perform _ _ _) (_ , _ , _ , _ , rsN , is-perform _ _ _)
  with op-presentation M pM rsM | op-presentation N pN rsN
... | _ , _ , _ , _ , _ , _ , ndM , rM , eM
    | _ , _ , _ , _ , _ , _ , ndN , rN , eN =
  cong performed (op-inj ndM ndN rM rN (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN)))

-- Equal denotations halt alike: `termination` supplies a halting of the other
-- program, and `same-outcome` compares the two.

adequacy : ∀ {A ε} → {M N : Closed A ε}
         → (pM : Paramᶜ M) → (pN : Paramᶜ N)
         → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
         ----------------------------
         → Same-outcome M N

adequacy {N = N} pM pN e hM = termination N , same-outcome pM pN e hM (termination N)

-- The head presentation at base type, with the constant it returns.

-- At a base type the run's refinement is `Baseₛ refl`, whose coercion is the
-- identity, so the returned value's leaf survives it unchanged.

base-run-leaf : ∀ {b A₀} {𝕊 : State []} → (V : toCtx 𝕊 ⊢ᵛ⦂ A₀)
              → (p : A₀ <:ᵛ Base b)
              → (pSt : Paramˢ 𝕊) → (pV : Paramᵛ V)
              → Σ[ c ∈ BaseConstants b ]
                  (base-val (subV V p) ≡ const b c)
                × (Tᶠ ⟦ p ⟧<:ᵛ ∘ᵐ ⟦ ⟨ 𝕊 ∣ return V ⟩ ⟧ᶜᶠ (pSt , pV)
                     ≈ᵐ leafᵐ (⟦ c ⟧ᵇᶜ ∘ᵐ terminalᵐ))

base-run-leaf V (Baseₛ refl) pSt pV with base-leaf-const V pSt pV
... | c , sc , qc =
  c , sc , ≈ᵐ-trans (∘ᵐ-congˡ T-idᵐ) (≈ᵐ-trans (∘ᵐ-identityˡ _) qc)

const-presentation : ∀ {b B ε} {𝕊 : State []} {V : toCtx 𝕊 ⊢ᵛ⦂ B}
                   → (M : Closed (Base b) ε) → (pM : Paramᶜ M)
                   → (rs : ⟨ ∅ ∣ M ⟩ ⟶* ⟨ 𝕊 ∣ return V ⟩)
                   → Σ[ c ∈ BaseConstants b ] Σ[ Y ∈ Obj ] Σ[ δ ∈ E ]
                     Σ[ d ∈ (𝟙ᵐ →ᵐ Tᵒ Y δ) ] Σ[ nd ∈ Delaysᵐ d (ticks rs) ]
                     Σ[ r ∈ (δ ·ₑ 𝟏ₑ ≾ₑ ε) ]
                       (base-val (ret-value rs) ≡ const b c)
                     × (⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (leafᵐ (⟦ c ⟧ᵇᶜ ∘ᵐ terminalᵐ)) d r)

const-presentation {V = V} M pM rs
  with base-run-leaf V (run-refines-type rs) _ _
... | c , sc , qc =
    c , _ , _ , _ , stepsᵀ-delays rs , steps-≾ rs , sc
  , ≈ᵐ-trans (program-run-sound M pM rs)
      (delayedᵐ-cong (stepsᵀ rs) (steps-≾ rs) qc)

-- What a halted base-typed program is observed to do: return a constant, the
-- returned value read at the program's type (`ret-value`) through its
-- subsumption spine (`base-canonical`), or call an operation.

base-answer : ∀ {b ε} {M : Closed (Base b) ε} → Halts ∅ M → BaseConstants b ⊎ Op
base-answer (_ , _ , _ , _ , rs , is-return _)       = inj₁ (proj₁ (base-canonical (ret-value rs)))
base-answer (_ , _ , _ , _ , _  , is-perform op _ _) = inj₂ op

-- Equal denotations have the same answer: on returning, `leaf-const`
-- identifies the two denotations and `const-inj` reflects that to the syntax;
-- otherwise `same-outcome` decides.

adequacy-base : ∀ {b ε} → {M N : Closed (Base b) ε}
              → (pM : Paramᶜ M) → (pN : Paramᶜ N)
              → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
              → (hM : Halts ∅ M) → (hN : Halts ∅ N)
              -------------------------------------
              → base-answer hM ≡ base-answer hN

adequacy-base {M = M} {N = N} pM pN e
  (_ , _ , _ , _ , rsM , is-return _) (_ , _ , _ , _ , rsN , is-return _)
  with const-presentation M pM rsM | const-presentation N pN rsN
... | cM , _ , _ , _ , ndM , rM , sM , eM
    | cN , _ , _ , _ , ndN , rN , sN , eN
  with const-inj (leaf-const ndM ndN rM rN
                    (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN)))
... | refl = cong inj₁ (trans (base-canonical-const (ret-value rsM) sM)
                              (sym (base-canonical-const (ret-value rsN) sN)))
adequacy-base pM pN e hM@(_ , _ , _ , _ , _ , is-return _) hN@(_ , _ , _ , _ , _ , is-perform _ _ _)
  with same-outcome pM pN e hM hN
... | ()
adequacy-base pM pN e hM@(_ , _ , _ , _ , _ , is-perform _ _ _) hN@(_ , _ , _ , _ , _ , is-return _)
  with same-outcome pM pN e hM hN
... | ()
adequacy-base pM pN e hM@(_ , _ , _ , _ , _ , is-perform _ _ _) hN@(_ , _ , _ , _ , _ , is-perform _ _ _)
  with same-outcome pM pN e hM hN
... | refl = refl

-- A `bool`-typed value's leaf is one of the two constants', read through its
-- subsumption spine by `bool-val`, a comparison by the constant it decides to;
-- the state's environment is absorbed by the terminal object, as at a base
-- constant. Which constant it is has to be carried along, since the two give
-- different leaves.

bool-leaf-const : ∀ {𝕊 : State []} → (pSt : Paramˢ 𝕊) → (b : Bool.Bool)
                → {f : ⟦ hist 𝕊 ⟧ᶜᵗˣ →ᵐ Tᵒ 𝔹ᵐ 𝟏ₑ}
                → f ≈ᵐ (ηᵀ ∘ᵐ (⌜ b ⌝ᵇ ∘ᵐ terminalᵐ)) ∘ᵐ ⟦ 𝕊 ⟧ˢ pSt
                → ((⌈_⌉ᵇ {toCtx 𝕊} b ≡ true) × (f ≈ᵐ leafᵐ (trueᵐ ∘ᵐ terminalᵐ)))
                ⊎ ((⌈_⌉ᵇ {toCtx 𝕊} b ≡ false) × (f ≈ᵐ leafᵐ (falseᵐ ∘ᵐ terminalᵐ)))
bool-leaf-const {𝕊 = 𝕊} pSt Bool.true e =
  inj₁ (refl
       , ≈ᵐ-trans e (≈ᵐ-trans (∘ᵐ-assoc ηᵀ (trueᵐ ∘ᵐ terminalᵐ) (⟦ 𝕊 ⟧ˢ pSt))
           (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-assoc trueᵐ terminalᵐ (⟦ 𝕊 ⟧ˢ pSt))
                               (∘ᵐ-congʳ terminalᵐ-unique)))))
bool-leaf-const {𝕊 = 𝕊} pSt Bool.false e =
  inj₂ (refl
       , ≈ᵐ-trans e (≈ᵐ-trans (∘ᵐ-assoc ηᵀ (falseᵐ ∘ᵐ terminalᵐ) (⟦ 𝕊 ⟧ˢ pSt))
           (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-assoc falseᵐ terminalᵐ (⟦ 𝕊 ⟧ˢ pSt))
                               (∘ᵐ-congʳ terminalᵐ-unique)))))

bool-leaf-value : ∀ {𝕊 : State []} → (V : toCtx 𝕊 ⊢ᵛ⦂ bool)
                → (pSt : Paramˢ 𝕊) → (pV : Paramᵛ V)
                → ((bool-val V ≡ true)
                   × (⟦ ⟨ 𝕊 ∣ return V ⟩ ⟧ᶜᶠ (pSt , pV)
                        ≈ᵐ leafᵐ (trueᵐ ∘ᵐ terminalᵐ)))
                ⊎ ((bool-val V ≡ false)
                   × (⟦ ⟨ 𝕊 ∣ return V ⟩ ⟧ᶜᶠ (pSt , pV)
                        ≈ᵐ leafᵐ (falseᵐ ∘ᵐ terminalᵐ)))

bool-leaf-value (var x f) pSt pV = ⊥-elim (bool-not-in-toCtx x)
bool-leaf-value true  pSt pV = bool-leaf-const pSt Bool.true ≈ᵐ-refl
bool-leaf-value false pSt pV = bool-leaf-const pSt Bool.false ≈ᵐ-refl
bool-leaf-value {𝕊 = 𝕊} (cmp ⋈ V W et) pSt (pV , pW) =
  bool-leaf-const pSt _
    (∘ᵐ-congˡ (∘ᵐ-congʳ (⌊⌋ᵈ-sound 𝕊 boolₑ (cmp ⋈ V W et) (pV , pW))))
bool-leaf-value (subV V boolₛ) pSt pV with bool-leaf-value V pSt pV
... | inj₁ (sv , qv) =
  inj₁ (sv , ≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-identityˡ _))) qv)
... | inj₂ (sv , qv) =
  inj₂ (sv , ≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-identityˡ _))) qv)

-- The head presentation at `bool`, with the boolean it returns.

-- The same at `bool`, where the run's refinement is `boolₛ`.

bool-run-leaf : ∀ {A₀} {𝕊 : State []} → (V : toCtx 𝕊 ⊢ᵛ⦂ A₀) → (p : A₀ <:ᵛ bool)
              → (pSt : Paramˢ 𝕊) → (pV : Paramᵛ V)
              → ((bool-val (subV V p) ≡ true)
                 × (Tᶠ ⟦ p ⟧<:ᵛ ∘ᵐ ⟦ ⟨ 𝕊 ∣ return V ⟩ ⟧ᶜᶠ (pSt , pV)
                      ≈ᵐ leafᵐ (trueᵐ ∘ᵐ terminalᵐ)))
              ⊎ ((bool-val (subV V p) ≡ false)
                 × (Tᶠ ⟦ p ⟧<:ᵛ ∘ᵐ ⟦ ⟨ 𝕊 ∣ return V ⟩ ⟧ᶜᶠ (pSt , pV)
                      ≈ᵐ leafᵐ (falseᵐ ∘ᵐ terminalᵐ)))

bool-run-leaf V boolₛ pSt pV with bool-leaf-value V pSt pV
... | inj₁ (sv , qv) =
  inj₁ (sv , ≈ᵐ-trans (∘ᵐ-congˡ T-idᵐ) (≈ᵐ-trans (∘ᵐ-identityˡ _) qv))
... | inj₂ (sv , qv) =
  inj₂ (sv , ≈ᵐ-trans (∘ᵐ-congˡ T-idᵐ) (≈ᵐ-trans (∘ᵐ-identityˡ _) qv))

bool-presentation : ∀ {B ε} {𝕊 : State []} {V : toCtx 𝕊 ⊢ᵛ⦂ B}
                  → (M : Closed bool ε) → (pM : Paramᶜ M)
                  → (rs : ⟨ ∅ ∣ M ⟩ ⟶* ⟨ 𝕊 ∣ return V ⟩)
                  → Σ[ Y ∈ Obj ] Σ[ δ ∈ E ]
                    Σ[ d ∈ (𝟙ᵐ →ᵐ Tᵒ Y δ) ] Σ[ nd ∈ Delaysᵐ d (ticks rs) ]
                    Σ[ r ∈ (δ ·ₑ 𝟏ₑ ≾ₑ ε) ]
                      ( ((bool-val (ret-value rs) ≡ true)
                         × (⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (leafᵐ (trueᵐ ∘ᵐ terminalᵐ)) d r))
                      ⊎ ((bool-val (ret-value rs) ≡ false)
                         × (⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (leafᵐ (falseᵐ ∘ᵐ terminalᵐ)) d r)) )

bool-presentation {V = V} M pM rs
  with bool-run-leaf V (run-refines-type rs) _ _
... | inj₁ (sv , qv) =
    _ , _ , _ , stepsᵀ-delays rs , steps-≾ rs
  , inj₁ (sv , ≈ᵐ-trans (program-run-sound M pM rs)
                 (delayedᵐ-cong (stepsᵀ rs) (steps-≾ rs) qv))
... | inj₂ (sv , qv) =
    _ , _ , _ , stepsᵀ-delays rs , steps-≾ rs
  , inj₂ (sv , ≈ᵐ-trans (program-run-sound M pM rs)
                 (delayedᵐ-cong (stepsᵀ rs) (steps-≾ rs) qv))

-- What a halted `bool`-typed program is observed to do: return a boolean, the
-- one its returned value reads as through its subsumption spine
-- (`bool-val-canonical`), or call an operation.

bool-answer : ∀ {ε} {M : Closed bool ε} → Halts ∅ M → Bool.Bool ⊎ Op
bool-answer (_ , _ , _ , _ , rs , is-return _)       = inj₁ (bool-canonical-value (ret-value rs))
bool-answer (_ , _ , _ , _ , _  , is-perform op _ _) = inj₂ op

-- Equal denotations have the same answer: on returning, the two leaves are the
-- same boolean's, by `leaf-bool` and `true≉false`; otherwise `same-outcome`
-- decides.

adequacy-bool : ∀ {ε} → {M N : Closed bool ε}
              → (pM : Paramᶜ M) → (pN : Paramᶜ N)
              → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
              → (hM : Halts ∅ M) → (hN : Halts ∅ N)
              -------------------------------------
              → bool-answer hM ≡ bool-answer hN

adequacy-bool {M = M} {N = N} pM pN e
  (_ , _ , _ , _ , rsM , is-return _) (_ , _ , _ , _ , rsN , is-return _)
  with bool-presentation M pM rsM | bool-presentation N pN rsN
... | _ , _ , _ , ndM , rM , inj₁ (sM , eM)
    | _ , _ , _ , ndN , rN , inj₁ (sN , eN) =
      cong inj₁ (trans (bool-canonical-true (ret-value rsM) sM)
                        (sym (bool-canonical-true (ret-value rsN) sN)))
... | _ , _ , _ , ndM , rM , inj₂ (sM , eM)
    | _ , _ , _ , ndN , rN , inj₂ (sN , eN) =
      cong inj₁ (trans (bool-canonical-false (ret-value rsM) sM)
                        (sym (bool-canonical-false (ret-value rsN) sN)))
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
adequacy-bool pM pN e hM@(_ , _ , _ , _ , _ , is-return _) hN@(_ , _ , _ , _ , _ , is-perform _ _ _)
  with same-outcome pM pN e hM hN
... | ()
adequacy-bool pM pN e hM@(_ , _ , _ , _ , _ , is-perform _ _ _) hN@(_ , _ , _ , _ , _ , is-return _)
  with same-outcome pM pN e hM hN
... | ()
adequacy-bool pM pN e hM@(_ , _ , _ , _ , _ , is-perform _ _ _) hN@(_ , _ , _ , _ , _ , is-perform _ _ _)
  with same-outcome pM pN e hM hN
... | refl = refl

-- A point presented as a delayed leaf, resp. a delayed operation node,
-- dictates how the program halts.

leaf-adequacy : ∀ {A ε Y δ n} → {M : Closed A ε} → (pM : Paramᶜ M)
              → {a : Y →ᵐ ⟦ A ⟧ᵛ}
              → {d : 𝟙ᵐ →ᵐ Tᵒ Y δ} → Delaysᵐ d n
              → (r : δ ·ₑ 𝟏ₑ ≾ₑ ε)
              → ⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (leafᵐ a) d r
              -------------------------------------------
              → Σ[ h ∈ Halts ∅ M ] outcome h ≡ returned

leaf-adequacy {M = M} pM nd r eq = go (termination M)
  where
    go : Halts ∅ M → Σ[ h ∈ Halts ∅ M ] outcome h ≡ returned
    go h@(_ , _ , _ , _ , _ , is-return _) = h , refl
    go (_ , _ , _ , _ , rs , is-perform _ _ _) with op-presentation M pM rs
    ... | _ , _ , _ , _ , _ , _ , ndO , rO , eO =
      ⊥-elim (ret≢op nd ndO r rO (≈ᵐ-trans (≈ᵐ-sym eq) eO))

node-adequacy : ∀ {A ε ε₂ Y δ n op} → {M : Closed A ε} → (pM : Paramᶜ M)
              → {v : Y →ᵐ ⟦ param op ⟧ᵍ}
              → {k : Y →ᵐ [ ∣ op-grade op ∣ᵉ ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ ε₂)}
              → {d : 𝟙ᵐ →ᵐ Tᵒ Y δ} → Delaysᵐ d n
              → (r : δ ·ₑ (op-grade op ·ₑ ε₂) ≾ₑ ε)
              → ⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (nodeᵐ op v k) d r
              ------------------------------------------------
              → Σ[ h ∈ Halts ∅ M ] outcome h ≡ performed op

node-adequacy {op = op} {M = M} pM nd r eq = go (termination M)
  where
    go : Halts ∅ M → Σ[ h ∈ Halts ∅ M ] outcome h ≡ performed op
    go (_ , _ , _ , _ , rs , is-return _) with ret-presentation M pM rs
    ... | _ , _ , _ , _ , ndR , rR , eR =
      ⊥-elim (ret≢op ndR nd rR r (≈ᵐ-trans (≈ᵐ-sym eR) eq))
    go h@(_ , _ , _ , _ , rs , is-perform _ _ _) with op-presentation M pM rs
    ... | _ , _ , _ , _ , _ , _ , ndO , rO , eO =
      h , cong performed (sym (op-inj nd ndO r rO (≈ᵐ-trans (≈ᵐ-sym eq) eO)))

-- Under `HeadTimed`, equal denotations also take the same time: the tick
-- totals of the two presentations agree (`ret-ticks-eq`, `op-ticks-eq`).

adequacy-ticks : HF.HeadTimed Spec Cat Fut Pst Adj GTy Mon GE
               → ∀ {A ε} → {M N : Closed A ε}
               → (pM : Paramᶜ M) → (pN : Paramᶜ N)
               → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
               → (hM : Halts ∅ M) → (hN : Halts ∅ N)
               -------------------------------------
               → halt-ticks hM ≡ halt-ticks hN

adequacy-ticks ht {M = M} {N = N} pM pN e
  (_ , _ , _ , _ , rsM , is-return _) (_ , _ , _ , _ , rsN , is-return _)
  with ret-presentation M pM rsM | ret-presentation N pN rsN
... | _ , _ , _ , _ , ndM , rM , eM
    | _ , _ , _ , _ , ndN , rN , eN =
  HF.HeadTimed.ret-ticks-eq ht ndM ndN rM rN
    (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN))
adequacy-ticks ht {M = M} {N = N} pM pN e
  (_ , _ , _ , _ , rsM , is-perform _ _ _) (_ , _ , _ , _ , rsN , is-perform _ _ _)
  with op-presentation M pM rsM | op-presentation N pN rsN
... | _ , _ , _ , _ , _ , _ , ndM , rM , eM
    | _ , _ , _ , _ , _ , _ , ndN , rN , eN
  with op-inj ndM ndN rM rN (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN))
... | refl =
  HF.HeadTimed.op-ticks-eq ht ndM ndN rM rN
    (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN))
adequacy-ticks ht pM pN e hM@(_ , _ , _ , _ , _ , is-return _) hN@(_ , _ , _ , _ , _ , is-perform _ _ _)
  with same-outcome pM pN e hM hN
... | ()
adequacy-ticks ht pM pN e hM@(_ , _ , _ , _ , _ , is-perform _ _ _) hN@(_ , _ , _ , _ , _ , is-return _)
  with same-outcome pM pN e hM hN
... | ()
