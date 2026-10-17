------------------------------------------------------------------------
-- Soundness of the small-step operational semantics.                   --
--                                                                      --
-- A configuration `⟨ S , M ⟩` denotes `⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ S ⟧ˢ`, a morphism  --
-- out of the state's history `⟦ hist S ⟧ᶜᵗˣ`.                          --
--                                                                      --
-- A reduction step relates the two denotations via a time transition   --
-- (`stepᵀ`) and an effect-refining coercion (`T-≤`).                   --
------------------------------------------------------------------------

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

module OperationalSemantics.Soundness.Preservation
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
open import Syntax.RenActions S using (V-rename; C-rename; var-rename)
open import Syntax.Substitutions S
open import Syntax.Substitutions.Subsumption S

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
open import DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.State S Cat Fut Pst Adj GTy Mon GE

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import OperationalSemantics.Soundness.Preservation.Handle S Cat Fut Pst Adj GTy Mon GE public

-- The coercion carried across a step escapes the bind: reduction's own
-- transitions are `ηᵀ` for every rule but `DELAY`, which uses `delayᵀ-≤`.

-- The grade a delayed computation's `ηᵀ` leaves behind.

delay-z : ∀ (τ : 𝔻) (ε : E) → of-durᵉ τ ·ₑ ε ≾ₑ (of-durᵉ τ ·ₑ uₑ) ·ₑ ε
delay-z τ ε =
  ≾ₑ-trans (·ₑ-monoʳ-≾ₑ (≾ₑ-reflexive (sym (·ₑ-identityˡ ε))))
           (≾ₑ-reflexive (sym (·ₑ-assoc (of-durᵉ τ) uₑ ε)))

-- Binding a computation after a delay is delaying the bound computation. (The
-- `ηᵀ` the transition carries is absorbed, leaving only a regrading.)

delay-nf : ∀ {X Y B ε} → (τ : 𝔻) → (env : X →ᵐ [ of-durʳ τ ]ᵒ Y) → (f : Y →ᵐ Tᵒ B ε)
         → μᵀ ∘ᵐ Tᶠ f ∘ᵐ (delayᵀ τ ∘ᵐ [ of-durʳ τ ]ᶠ ηᵀ ∘ᵐ env)
         ≈ᵐ T-≤ (delay-z τ ε) ∘ᵐ delayᵀ τ ∘ᵐ [ of-durʳ τ ]ᶠ f ∘ᵐ env
delay-nf {ε = ε} τ env f =
  -- push the bind under the delay …
    ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (delayᵀ-nat τ f)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  -- … and the multiplication too (the delay is algebraic)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (delayᵀ-algebraicity τ)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  -- under the box: the transition's `ηᵀ` is absorbed by the multiplication
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
      (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
       ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
       ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
       ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
       ∙ ∘ᵐ-congˡ ([]-congᶠ (∘ᵐ-assoc _ _ _ ∙ ⋄-ηᵀ f ∙ ∘ᵐ-congˡ (T-≤-≡ _)))
       ∙ ∘ᵐ-congˡ ([]-∘ᵐ _ _)
       ∙ ∘ᵐ-assoc _ _ _))
  -- what is left is a coercion under the box, which `delayᵀ-≤` pulls out
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (delayᵀ-≤ τ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ (T-≤-≡ _) ∙ T-≤-trans _ _ (delay-z τ ε))

-- The rules that transition by `ηᵀ`: the coercion simply passes through,
-- both sides collapsing to the same chain of sub-effectings.

ηᵀ-case : ∀ {X B εa εb} → (g : X →ᵐ Tᵒ B εa) → (q : εa ≾ₑ εb)
        → μᵀ ∘ᵐ Tᶠ (T-≤ q ∘ᵐ g) ∘ᵐ ηᵀ
        ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ μᵀ ∘ᵐ Tᶠ g ∘ᵐ ηᵀ
ηᵀ-case {εa = εa} {εb = εb} g q =
    ⋄-ηᵀ (T-≤ q ∘ᵐ g)
  ∙ ∘ᵐ-congˡ (T-≤-≡ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-≤-trans q _ w)
  ∙ ≈ᵐ-sym
      (  ∘ᵐ-congʳ (⋄-ηᵀ g ∙ ∘ᵐ-congˡ (T-≤-≡ _))
       ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
       ∙ ∘ᵐ-congˡ (T-≤-trans _ _ w))
  where
    w : εa ≾ₑ uₑ ·ₑ εb
    w = ≾ₑ-trans q (≾ₑ-reflexive (sym (·ₑ-identityˡ εb)))

-- The coercion escapes the bind, for the transition of any step.

T-≤-stepᵀ : ∀ {ε ε' εa εb A A₀} {S S' : 𝕊 []} → (B : Obj)
          → {M : toCtx S ⊢C⦂ A ‼ ε} → {M' : toCtx S' ⊢C⦂ A₀ ‼ ε'}
          → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
          → (g : ⟦ hist S' ⟧ᶜᵗˣ →ᵐ Tᵒ B εa) → (q : εa ≾ₑ εb)
          → μᵀ ∘ᵐ Tᶠ (T-≤ q ∘ᵐ g) ∘ᵐ stepᵀ r
          ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ μᵀ ∘ᵐ Tᶠ g ∘ᵐ stepᵀ r
T-≤-stepᵀ B APP         g q = ηᵀ-case g q
T-≤-stepᵀ B MATCH       g q = ηᵀ-case g q
T-≤-stepᵀ B IF-TRUE     g q = ηᵀ-case g q
T-≤-stepᵀ B IF-FALSE    g q = ηᵀ-case g q
T-≤-stepᵀ B CASE-INL    g q = ηᵀ-case g q
T-≤-stepᵀ B CASE-INR    g q = ηᵀ-case g q
T-≤-stepᵀ B CASEℕ-ZERO  g q = ηᵀ-case g q
T-≤-stepᵀ B CASEℕ-SUCC  g q = ηᵀ-case g q
T-≤-stepᵀ B SEQ-RET     g q = ηᵀ-case g q
T-≤-stepᵀ B SEQ-OP      g q = ηᵀ-case g q
T-≤-stepᵀ B HANDLE-RET  g q = ηᵀ-case g q
T-≤-stepᵀ B HANDLE-OP   g q = ηᵀ-case g q
T-≤-stepᵀ B BOX         g q = ηᵀ-case g q
T-≤-stepᵀ B UNBOX       g q = ηᵀ-case g q
T-≤-stepᵀ B SUB-APP     g q = ηᵀ-case g q
T-≤-stepᵀ B SUB-IF      g q = ηᵀ-case g q
T-≤-stepᵀ B SUB-CASE    g q = ηᵀ-case g q
T-≤-stepᵀ B SUB-CASEℕ   g q = ηᵀ-case g q
T-≤-stepᵀ B SUB         g q = ηᵀ-case g q
-- the congruences transition exactly as their sub-reduction does
T-≤-stepᵀ B (SEQ-STEP r _)    g q = T-≤-stepᵀ B r g q
T-≤-stepᵀ B (HANDLE-STEP r _) g q = T-≤-stepᵀ B r g q
-- the one rule that advances time
T-≤-stepᵀ {εa = εa} {εb = εb} B (DELAY {τ = τ}) g q =
  -- the coercion is under the delay's box; `delayᵀ-≤` pulls it out, and the two
  -- sub-effectings then collapse to the same one
    delay-nf τ η⊣ (T-≤ q ∘ᵐ g)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-∘ᵐ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (delayᵀ-≤ τ q))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-≤-trans (·ₑ-monoʳ-≾ₑ q) (delay-z τ εb) z)
  ∙ ≈ᵐ-sym
      (  ∘ᵐ-congʳ (delay-nf τ η⊣ g)
       ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
       ∙ ∘ᵐ-congˡ (T-≤-trans (delay-z τ εa) (·ₑ-monoʳ-≾ₑ q) z))
  where
    z : of-durᵉ τ ·ₑ εa ≾ₑ (of-durᵉ τ ·ₑ uₑ) ·ₑ εb
    z = ≾ₑ-trans (·ₑ-monoʳ-≾ₑ q) (delay-z τ εb)

-- A reduction step relates denotationally equal configurations: the source's
-- denotation is the target's, run after the step's time transition and
-- coerced along the effect refinement the step licenses.

-- The handlers a reduction actually reaches must be uniform. `HANDLE-OP` is the
-- only rule that fires a clause, and the only rules that can reach it are the
-- two congruences — so this is a recursion on the *reduction*, not on the term.

-- The clauses' uniformity in the residual effect is carried by the term's own
-- `Paramᶜ`, so a reduction assumes nothing on top of it and every case is `⊤`.
-- It stays a predicate so the soundness statements can take it uniformly.

Uniform↝ : ∀ {ε ε' A A₀} {S S' : 𝕊 []}
         → {M : toCtx S ⊢C⦂ A ‼ ε} → {M' : toCtx S' ⊢C⦂ A₀ ‼ ε'}
         → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩) → Paramᶜ M
         → Set
Uniform↝ HANDLE-OP           _            = ⊤
Uniform↝ (SEQ-STEP r _)      (pM , _)     = Uniform↝ r pM
Uniform↝ (HANDLE-STEP r _)   (pM , _)     = Uniform↝ r pM
Uniform↝ APP                 _            = ⊤
Uniform↝ MATCH               _            = ⊤
Uniform↝ IF-TRUE             _            = ⊤
Uniform↝ IF-FALSE            _            = ⊤
Uniform↝ CASE-INL            _            = ⊤
Uniform↝ CASE-INR            _            = ⊤
Uniform↝ CASEℕ-ZERO          _            = ⊤
Uniform↝ CASEℕ-SUCC          _            = ⊤
Uniform↝ SEQ-RET             _            = ⊤
Uniform↝ SEQ-OP              _            = ⊤
Uniform↝ DELAY               _            = ⊤
Uniform↝ HANDLE-RET          _            = ⊤
Uniform↝ BOX                 _            = ⊤
Uniform↝ UNBOX               _            = ⊤
Uniform↝ SUB-APP             _            = ⊤
Uniform↝ SUB-IF              _            = ⊤
Uniform↝ SUB-CASE            _            = ⊤
Uniform↝ SUB-CASEℕ           _            = ⊤
Uniform↝ SUB                 _            = ⊤

-- The computation's certificate across a step: every reduct is built from the
-- source's pieces by renaming, substitution and retyping, each of which
-- transports parametricity.

stepᴾᶜ : ∀ {ε ε' A A₀} {S S' : 𝕊 []}
       → {M : toCtx S ⊢C⦂ A ‼ ε} → {M' : toCtx S' ⊢C⦂ A₀ ‼ ε'}
       → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩) → Paramˢ S → Paramᶜ M → Paramᶜ M'
stepᴾᶜ (APP {M = M} {V = V})            pS (pM , pV)  = subᶜ M split-[] V pM pV
stepᴾᶜ (MATCH {S = St} {P = P} {M = M}) pS (pP , pM) =
  subᶜ (M [ split-[] ↦ V-rename wk-ren (sndᵛ {S = St} P) ]c) split-[]
    (fstᵛ {S = St} P)
    (subᶜ M split-[] (V-rename wk-ren (sndᵛ {S = St} P)) pM
       (renᵛ wk-ren (sndᵛ {S = St} P) (sndᵛᴾ St P pP)))
    (fstᵛᴾ St P pP)
stepᴾᶜ (SEQ-STEP {N = N} r c)           pS (pM , pN)  =
  stepᴾᶜ r pS pM
  , subCtxᴾ (step-refines-type r)
      (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N)
      (renᶜ (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N pN)
stepᴾᶜ (SEQ-RET {V = V} {N = N})        pS (pV , pN)  = ret-subᴾ V N pV pN
stepᴾᶜ (SEQ-OP {op = op} {S = S} {V = V} {M = M} {N = N}) pS ((pV , pM) , pN) =
  ε-substᴾ (sym (·ₑ-assoc (op-grade op) _ _))
    (perform op V (M ⨟ C-rename (cong-∷-ren ((eq-ren (cong (toCtx S ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren)) N))
    (pV , pM , renᶜ (cong-∷-ren ((eq-ren (cong (toCtx S ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren)) N pN)
stepᴾᶜ IF-TRUE                          pS (_ , pM , pN) = pM
stepᴾᶜ IF-FALSE                         pS (_ , pM , pN) = pN
stepᴾᶜ CASEℕ-ZERO                       pS (_ , pM , pN) = pM
stepᴾᶜ (CASEℕ-SUCC {V = V} {N = N})    pS (pV , pM , pN) = subᶜ N split-[] V pN pV
stepᴾᶜ (CASE-INL {V = V} {M = M})      pS (pV , pM , pN) = subᶜ M split-[] V pM pV
stepᴾᶜ (CASE-INR {V = V} {N = N})      pS (pV , pM , pN) = subᶜ N split-[] V pN pV
stepᴾᶜ DELAY                            pS pM         = pM
stepᴾᶜ (HANDLE-RET {V = V} {N = N})     pS (pV , pN , pH , uH) = ret-subᴾ V N pV pN
stepᴾᶜ (HANDLE-STEP {S = S} {S' = S'} {H = H} {N = N} r c) pS (pM , pN , pH , uH) =
  stepᴾᶜ r pS pM
  , subCtxᴾ (step-refines-type r)
      (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N)
      (renᶜ (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N pN)
  , (λ op ε₃ → renᶜ (cong-∷-ren (cong-∷-ren
                       (suc-comp-ren (step-extends-state r) (≾-⊤ᵣ _))))
                    (H op ε₃) (pH op ε₃))
  , ren-clauses-uniform (suc-comp-ren (step-extends-state r) (≾-⊤ᵣ _)) H pH uH
stepᴾᶜ (HANDLE-OP {ε = ε} {ε'' = ε''} {op = op} {S = S} {V = V} {M = M} {H = H} {N = N})
       pS ((pV , pM) , pN , pH , uH) =
    (pM
    , renᶜ (cong-∷-ren ((eq-ren (cong (toCtx S ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren)) N pN
    , (λ op' ε' → renᶜ (cong-∷-ren (cong-∷-ren (barrier-wk-ren (mapᵉ (op-grade op)) (type-of-gtype (arity op))))) (H op' ε') (pH op' ε'))
    , ren-clauses-uniform
        (barrier-wk-ren (mapᵉ (op-grade op)) (type-of-gtype (arity op))) H pH uH)
  , subᶜ (C-rename (cong-∷-ren (cong-∷-ren (barrier-ren {toCtx S}))) (H op (ε ·ₑ ε'')))
         (split-∷ split-[]) V
         (renᶜ (cong-∷-ren (cong-∷-ren (barrier-ren {toCtx S})))
               (H op (ε ·ₑ ε'')) (pH op (ε ·ₑ ε'')))
         pV
stepᴾᶜ BOX                              pS (pV , pM)  = pM
stepᴾᶜ (UNBOX {S = S} {z = z} {rel = rel} {p = p} {M = M}) pS pM =
  subᶜ M split-[] (subV (unbox-lookup S z rel) p) pM (unbox-lookupᴾ S z rel pS)
stepᴾᶜ SUB-APP                          pS pM         = pM
stepᴾᶜ SUB-IF                           pS pM         = pM
stepᴾᶜ SUB-CASEℕ                        pS pM         = pM
stepᴾᶜ (SUB-CASE {p = p} {q = q} {M = M} {N = N}) pS (pV , pM , pN) =
  pV , subCtxᴾ p M pM , subCtxᴾ q N pN
stepᴾᶜ SUB                              pS pM         = pM

-- Both halves at once, for a configuration.

stepᴾᶜᶠ : ∀ {ε ε' A A₀} {S S' : 𝕊 []}
        → {M : toCtx S ⊢C⦂ A ‼ ε} → {M' : toCtx S' ⊢C⦂ A₀ ‼ ε'}
        → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩) → (p : Paramᶜᶠ (⟨ S , M ⟩))
        → Paramᶜᶠ (⟨ S' , M' ⟩)
stepᴾᶜᶠ r (pS , pM) = stepᴾˢ r pS pM , stepᴾᶜ r pS pM

↝-sound : ∀ {ε ε' A A₀} {S S' : 𝕊 []}
        → {M : toCtx S ⊢C⦂ A ‼ ε} → {M' : toCtx S' ⊢C⦂ A₀ ‼ ε'}
        → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
        → (pS : Paramˢ S) → (pM : Paramᶜ M)
        → Uniform↝ r pM
        → ⟦ ⟨ S , M ⟩ ⟧ᶜᶠ (pS , pM)
        ≈ᵐ T-≤ (step-≾ r)
           ∘ᵐ Tᶠ ⟦ step-refines-type r ⟧<:ᵛ
           ∘ᵐ _⋄_ {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A₀ ⟧ᵛ} {step-grade r} {ε'}
                  (⟦ ⟨ S' , M' ⟩ ⟧ᶜᶠ (stepᴾᶜᶠ r (pS , pM))) (stepᵀ r)

-- The rules that neither advance time nor change the store: a plain equation
-- between the two denotations, with `ηᵀ`'s unit grade absorbed by `T-≤`.

↝-sound {A = A} r@(APP {M = M} {V = V}) pS (pM , pV) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-APP M V pM pV)) ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
↝-sound {A = A} r@(MATCH {S = St} {P = P} {M = M}) pS (pP , pM) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-MATCH St P M pP pM)) ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
↝-sound {A = A} r@(SEQ-OP {op = op} {V = V} {M = M} {N = N}) pS ((pV , pM) , pN) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-SEQ-OP op V M N pV pM pN))
  ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
↝-sound {A = A} r@(IF-TRUE {M = M} {N = N}) pS (_ , pM , pN) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-IF-TRUE M N pM pN)) ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
↝-sound {A = A} r@(IF-FALSE {M = M} {N = N}) pS (_ , pM , pN) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-IF-FALSE M N pM pN)) ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
↝-sound {A = A} r@(CASEℕ-ZERO {M = M} {N = N}) pS (_ , pM , pN) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-CASEℕ-ZERO M N pM pN))
  ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
↝-sound {A = A} r@(CASEℕ-SUCC {V = V} {M = M} {N = N}) pS (pV , pM , pN) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-CASEℕ-SUCC V M N pV pM pN))
  ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
↝-sound {A = A} r@(CASE-INL {V = V} {M = M} {N = N}) pS (pV , pM , pN) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-CASE-INL V M N pV pM pN))
  ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
↝-sound {A = A} r@(CASE-INR {V = V} {M = M} {N = N}) pS (pV , pM , pN) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-CASE-INR V M N pV pM pN))
  ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))

-- Allocation and lookup: also plain equations, but ones that mention the store.

↝-sound {A = A} r@(BOX {S = St} {V = V} {M = M}) pS (pV , pM) _ =
  pure-step-≡ (step-≾ r) (sound-BOX St V M pS pV pM) ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
↝-sound {A = A} r@(UNBOX {S = St} {z = z} {rel = rel} {p = p} {M = M}) pS pM _ =
  pure-step-≡ (step-≾ r) (sound-UNBOX St z rel p M pS pM) ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))

-- The `return` rules: the coercion the substitution leaves behind is `ε-substᵀ`,
-- which `T-≤-≡` turns into the sub-effecting the theorem asks for.

↝-sound {A = A} r@(SEQ-RET {V = V} {N = N}) pS (pV , pN) _ =
  pure-step (step-≾ r) (≾ₑ-reflexive (sym (·ₑ-identityˡ _)))
    (∘ᵐ-congˡ (sound-SEQ-RET V N pV pN) ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congˡ (T-≤-≡ _))
  ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
↝-sound {A = A} r@(HANDLE-RET {V = V} {H = H} {N = N}) pS (pV , pN , pH , uH) _ =
  pure-step (step-≾ r) (≾ₑ-reflexive (sym (·ₑ-identityˡ _)))
    (∘ᵐ-congˡ (sound-HANDLE-RET V H N pV pN pH uH)
     ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congˡ (T-≤-≡ _))
  ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))

-- Peeling a subsumption: at an eliminated function it splits (`SUB-APP`), at a
-- scrutinised boolean or natural number it is the identity (`SUB-IF`,
-- `SUB-CASEℕ`), at a scrutinised sum it moves onto the branches
-- (`SUB-CASE`), and at a computation it is discarded (`SUB`) — in the first
-- and last the codomain half becomes the step's own refinement of both
-- components.

↝-sound {A = A} r@(SUB-APP {V = V} {W = W} {q = q} {r = p ‼ₛ s}) pS (pV , pW) _ =
  pure-step<: (step-≾ r) p s
    (∘ᵐ-congˡ (sound-SUB-APP V W q (p ‼ₛ s) pV pW)
     ∙ ∘ᵐ-assoc _ _ _
     ∙ ∘ᵐ-congˡ (T-≤-nat ⟦ p ⟧<:ᵛ s)
     ∙ ∘ᵐ-assoc _ _ _)
↝-sound {A = A} r@(SUB-IF {V = V} {M = M} {N = N}) pS (pV , pM , pN) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-SUB-IF V M N pV pM pN))
  ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
↝-sound {A = A} r@(SUB-CASEℕ {V = V} {M = M} {N = N}) pS (pV , pM , pN) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-SUB-CASEℕ V M N pV pM pN))
  ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
↝-sound {A = A} r@(SUB-CASE {V = V} {p = p} {q = q} {M = M} {N = N}) pS (pV , pM , pN) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-SUB-CASE V p q M N pV pM pN))
  ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
↝-sound {A = A} {S = St} r@(SUB {M = M₀} {w = p ‼ₛ q}) pS pM _ =
  pure-step<: (step-≾ r) p q (sound-SUB {S = St} {M = M₀} p q pS pM)

-- The one rule that advances time.

↝-sound {A = A} r@(DELAY {τ = τ} {S = St} {M = M}) pS pM _ =
  sound-DELAY τ St M (step-≾ r) pS pM ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))

-- The congruence rules: the inductive hypothesis is pushed through the strength
-- and multiplied, the environment carried across the step by `step-box`.

↝-sound {A = A} (SEQ-STEP {N = N} r c) pS (pM , pN) u =
  sound-SEQ-STEP N r c pS pM pN (stepᴾᶜ r pS pM) (↝-sound r pS pM u)
  ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
↝-sound {A = A} (HANDLE-STEP {H = H} {N = N} r c) pS (pM , pN , pH , uH) u =
  sound-HANDLE-STEP H N r c pS pM pN (stepᴾᶜ r pS pM) pH uH (↝-sound r pS pM u)
  ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))

-- Handling an operation: the clause is applied, with the handled remainder
-- boxed up as its continuation. This is the only rule that reads a clause; its
-- parametricity comes from the term's own `Paramᶜ` certificate.

↝-sound {A = A} {S = S} r@(HANDLE-OP {op = op} {V = V} {M = M} {H = H} {N = N})
        pS ((pV , pM) , pN , pH , uH) u =
  pure-step (step-≾ r) (≾ₑ-reflexive (sym (·ₑ-assoc (op-grade op) _ _)))
    (∘ᵐ-congˡ (sound-HANDLE-OP op V M H N pV pM pN pH uH)
     ∙ ∘ᵐ-assoc _ _ _
     ∙ ∘ᵐ-congˡ (T-≤-≡ _))
  ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))


-- A run of the machine is sound: the source configuration's denotation is
-- the final one's, run after the accumulated transition and coerced along
-- the accumulated refinement.

-- The accumulated effect of a run, its transition, and its refinement.

steps-grade : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
            → cf ↝* cf' → E
steps-grade ε*        = uₑ
steps-grade (r ◅ rs)  = step-grade r ·ₑ steps-grade rs

stepsᵀ : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
       → (rs : cf ↝* cf')
       → ⟦ hist (Config.state cf) ⟧ᶜᵗˣ
       →ᵐ Tᵒ ⟦ hist (Config.state cf') ⟧ᶜᵗˣ (steps-grade rs)
stepsᵀ ε*       = ηᵀ
stepsᵀ (r ◅ rs) = stepsᵀ rs ⋄ stepᵀ r

steps-≾ : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
        → (rs : cf ↝* cf') → steps-grade rs ·ₑ ε' ≾ₑ ε
steps-≾ {ε = ε} ε*       = ≾ₑ-reflexive (·ₑ-identityˡ ε)
steps-≾ {ε' = ε'} (_◅_ {ε₂ = ε₂} r rs) =
  -- the step's own refinement, after the run's, reassociated
  ≾ₑ-trans (≾ₑ-reflexive (·ₑ-assoc (step-grade r) (steps-grade rs) ε'))
  (≾ₑ-trans (·ₑ-monoʳ-≾ₑ (steps-≾ rs)) (step-≾ r))

-- Every handler the run reaches must be uniform.

-- The certificate accumulated along a run.

stepsᴾᶜᶠ : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
         → cf ↝* cf' → Paramᶜᶠ cf → Paramᶜᶠ cf'
stepsᴾᶜᶠ ε*       p = p
stepsᴾᶜᶠ (r ◅ rs) p = stepsᴾᶜᶠ rs (stepᴾᶜᶠ r p)

Uniform↝* : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
          → (rs : cf ↝* cf') → Paramᶜᶠ cf → Set
Uniform↝* ε*       _        = ⊤
Uniform↝* (r ◅ rs) (pS , pM) =
  Uniform↝ r pM × Uniform↝* rs (stepᴾᶜᶠ r (pS , pM))

-- The Kleisli composite is associative: binding a run after a step is binding
-- once, at the product of the two grades. (The monad's associativity, with the
-- functorial actions collected.)

bind-bind : ∀ {X Y Z B ε₁ ε₂ ε₃}
          → (f : Z →ᵐ Tᵒ B ε₃) → (t : Y →ᵐ Tᵒ Z ε₂) → (s : X →ᵐ Tᵒ Y ε₁)
          → μᵀ ∘ᵐ Tᶠ (f ⋄ t) ∘ᵐ s
          ≈ᵐ ε-substᵀ (·ₑ-assoc ε₁ ε₂ ε₃) ∘ᵐ (f ⋄ (t ⋄ s))
bind-bind f t s =
  -- split the bound composite's functorial action …
    ∘ᵐ-congʳ (∘ᵐ-congˡ (T-∘ᵐ _ _ ∙ ∘ᵐ-congʳ (T-∘ᵐ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  -- … and apply the monad's associativity
  ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ T-μ∘μ≡μ∘Tμ)
  ∙ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  -- the inner multiplication is natural, which exposes the second bind
  ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congʳ (μᵀ-nat f)))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))

-- The two refinements a step and the run after it contribute, with the three
-- sub-effectings between them, collapse into the run's own pair.

run-collapse : ∀ {X A B C ε₁ ε₂ ε₃ ε₄}
             → (h₁ : B →ᵐ A) → (h₂ : C →ᵐ B)
             → (a : ε₂ ≾ₑ ε₁) → (m : ε₃ ≾ₑ ε₂) → (c : ε₄ ≾ₑ ε₃) → (w : ε₄ ≾ₑ ε₁)
             → (K : X →ᵐ Tᵒ C ε₄)
             → T-≤ a ∘ᵐ Tᶠ h₁ ∘ᵐ T-≤ m ∘ᵐ Tᶠ h₂ ∘ᵐ T-≤ c ∘ᵐ K
             ≈ᵐ T-≤ w ∘ᵐ Tᶠ (h₁ ∘ᵐ h₂) ∘ᵐ K
run-collapse h₁ h₂ a m c w K =
    ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-nat h₂ c))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-trans c m (≾ₑ-trans c m))))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-nat h₁ (≾ₑ-trans c m)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-≤-trans (≾ₑ-trans c m) a w)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ h₁ h₂)))

↝*-sound : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
         → (rs : cf ↝* cf') → (p : Paramᶜᶠ cf) → Uniform↝* rs p
         → ⟦ cf ⟧ᶜᶠ p
         ≈ᵐ T-≤ (steps-≾ rs)
            ∘ᵐ Tᶠ ⟦ run-refines-type rs ⟧<:ᵛ
            ∘ᵐ _⋄_ {⟦ hist (Config.state cf) ⟧ᶜᵗˣ}
                   {⟦ hist (Config.state cf') ⟧ᶜᵗˣ} {⟦ B ⟧ᵛ}
                   {steps-grade rs} {ε'}
                   (⟦ cf' ⟧ᶜᶠ (stepsᴾᶜᶠ rs p)) (stepsᵀ rs)
-- the empty run: the transition is `ηᵀ`, which the bind absorbs
↝*-sound {A = A} {ε = ε} {cf = cf} ε* p _ =
  pure-step-≡ (steps-≾ (ε* {A} {ε} {cf})) ≈ᵐ-refl ∙ ∘ᵐ-congʳ (insert-coe (<:ᵛ-refl A))
-- a step, then a run
↝*-sound {A = A} {ε' = ε'} (_◅_ {B = B} {ε₂ = ε₂} {cf₃ = cf₃} r rs) (pS , pM) (u , us) =
  -- the step is sound …
    ↝-sound r pS pM u
  -- … and so, inductively, is the run that follows it
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
      (↝*-sound rs (stepᴾᶜᶠ r (pS , pM)) us)))))
  -- the run's coercion escapes the bind, its refinement by naturality alone
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (T-≤-stepᵀ ⟦ B ⟧ᵛ r
       (Tᶠ ⟦ run-refines-type rs ⟧<:ᵛ
          ∘ᵐ (⟦ cf₃ ⟧ᶜᶠ (stepsᴾᶜᶠ rs (stepᴾᶜᶠ r (pS , pM))) ⋄ stepsᵀ rs))
       (steps-≾ rs)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (Tᶠ-bind ⟦ run-refines-type rs ⟧<:ᵛ
       (⟦ cf₃ ⟧ᶜᶠ (stepsᴾᶜᶠ rs (stepᴾᶜᶠ r (pS , pM))) ⋄ stepsᵀ rs) (stepᵀ r))))
  -- the two binds re-associate into one, at the product of their grades …
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (bind-bind (⟦ cf₃ ⟧ᶜᶠ (stepsᴾᶜᶠ rs (stepᴾᶜᶠ r (pS , pM))))
                 (stepsᵀ rs) (stepᵀ r)))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-≡ _)))))
  -- … and the two refinements, with the three sub-effectings between them,
  -- collapse into the run's own pair
  ∙ run-collapse ⟦ step-refines-type r ⟧<:ᵛ ⟦ run-refines-type rs ⟧<:ᵛ
      (step-≾ r) (·ₑ-monoʳ-≾ₑ (steps-≾ rs)) _ (steps-≾ (r ◅ rs))
      (⟦ cf₃ ⟧ᶜᶠ (stepsᴾᶜᶠ rs (stepᴾᶜᶠ r (pS , pM))) ⋄ stepsᵀ (r ◅ rs))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (≈ᵐ-sym (⟦⟧<:ᵛ-trans (run-refines-type rs) (step-refines-type r)))))



-- `cf ⊳ cf'`: `cf` runs to `cf'` denotationally, after some transition and
-- coerced along some refinement. Reflexive (`⊳-refl`) but not transitive —
-- sub-effecting escapes a bind only for reduction's own transitions
-- (`T-≤-stepᵀ`); transitivity along a run is `↝*-sound`'s induction instead.

infix 4 _⊳_

-- The configurations are implicit, carried by their parametricity
-- certificates: interpreting a configuration needs one, so the relation is
-- between certified configurations.

record _⊳_ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
           (p : Paramᶜᶠ cf) (p' : Paramᶜᶠ cf') : Set where
  constructor mk⊳
  field
    -- the effect the transition performs, and the refinement it licenses
    grade : E
    refine : grade ·ₑ ε' ≾ₑ ε
    -- the value type is refined too
    refineᵛ : B <:ᵛ A
    -- the transition itself, between the two states' histories
    tr     : ⟦ hist (Config.state cf) ⟧ᶜᵗˣ
           →ᵐ Tᵒ ⟦ hist (Config.state cf') ⟧ᶜᵗˣ grade
    -- and the equation
    sound  : ⟦ cf ⟧ᶜᶠ p
           ≈ᵐ T-≤ refine
              ∘ᵐ Tᶠ ⟦ refineᵛ ⟧<:ᵛ
              ∘ᵐ _⋄_ {⟦ hist (Config.state cf) ⟧ᶜᵗˣ}
                     {⟦ hist (Config.state cf') ⟧ᶜᵗˣ} {⟦ B ⟧ᵛ} {grade} {ε'}
                     (⟦ cf' ⟧ᶜᶠ p') tr

-- Reflexivity: a configuration runs to itself, taking no time and refining
-- nothing.

⊳-refl : ∀ {A ε} → (cf : Config (A ‼ ε)) → (p : Paramᶜᶠ cf)
       → _⊳_ {cf = cf} {cf' = cf} p p
⊳-refl {ε = ε} cf p =
  mk⊳ uₑ (steps-≾ (ε* {cf = cf})) (run-refines-type (ε* {cf = cf})) ηᵀ
      (↝*-sound (ε* {cf = cf}) p tt)

-- A run of the machine is such a witness. This is the soundness theorem in its
-- final form: reduction never changes what a configuration means.

↝*-⊳ : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
     → (rs : cf ↝* cf') → (p : Paramᶜᶠ cf) → Uniform↝* rs p
     → _⊳_ {cf = cf} {cf' = cf'} p (stepsᴾᶜᶠ rs p)
↝*-⊳ rs p us =
  mk⊳ (steps-grade rs) (steps-≾ rs) (run-refines-type rs) (stepsᵀ rs)
      (↝*-sound rs p us)

-- A program is a closed computation (empty state, so empty history), so its
-- denotation is a global point of `Tᵒ ⟦ A ⟧ᵛ ε`.

Program : VType → E → Set
Program A ε = [] ⊢C⦂ A ‼ ε

⟦_⟧ᵖ : ∀ {A ε} → (M : Program A ε) → Paramᶜ M → 𝟙ᵐ →ᵐ Tᵒ ⟦ A ⟧ᵛ ε
⟦ M ⟧ᵖ p = ⟦ M ⟧ᶜᵗ p

-- Running a program to a value: its denotation is `ηᵀ` of the value's, in the
-- final state's environment, composed with the run's transition.

↝*-value : ∀ {A A₀ ε} {S' : 𝕊 []}
         → (M : Program A ε)
         → (V : toCtx S' ⊢V⦂ A₀)
         → (rs : ⟨ ∅ , M ⟩ ↝* ⟨ S' , return V ⟩)
         → (pM : Paramᶜ M)
         → Uniform↝* rs (tt , pM)
         → ⟦ M ⟧ᵖ pM
         ≈ᵐ T-≤ (steps-≾ rs)
            ∘ᵐ Tᶠ ⟦ run-refines-type rs ⟧<:ᵛ
            ∘ᵐ _⋄_ {𝟙ᵐ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A₀ ⟧ᵛ} {steps-grade rs} {uₑ}
                   (ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ (proj₂ (stepsᴾᶜᶠ rs (tt , pM)))
                       ∘ᵐ ⟦ S' ⟧ˢ (proj₁ (stepsᴾᶜᶠ rs (tt , pM))))
                   (stepsᵀ rs)
↝*-value M V rs pM us =
  -- the empty state is the empty environment
    ≈ᵐ-sym (∘ᵐ-identityʳ _)
  ∙ ↝*-sound rs (tt , pM) us
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (∘ᵐ-assoc _ _ _)))))
