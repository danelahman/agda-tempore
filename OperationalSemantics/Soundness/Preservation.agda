------------------------------------------------------------------------
-- Soundness of the small-step operational semantics.                   --
--                                                                    --
-- A configuration `⟨ S , M ⟩` interprets as the open computation `M`   --
-- with its context plugged by the state:                                --
--                                                                    --
--   ⟦ ⟨ S , M ⟩ ⟧ᶜᶠ = ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ S ⟧ˢ                                --
--                                                                    --
-- The plug is total on the *cells* of `toCtx S` (each carries its       --
-- stored value) but not on the *locks*: `⟨ ρ ⟩ᵒ X` has no global points, --
-- so the passage of time cannot be manufactured. What remains is the     --
-- state's history `hist S`, so a configuration denotes a morphism out of --
-- `⟦ hist S ⟧ᶜᵗˣ` — for an initial state `∅` that is `𝟙ᵐ`, a global      --
-- point.                                                                --
--                                                                    --
-- A reduction step relates the two denotations. The two configurations   --
-- have different histories and different effect grades, so the statement --
-- is mediated by                                                        --
--                                                                    --
--   * a *time transition* `stepᵀ r : ⟦ hist S ⟧ →ᵐ Tᵒ ⟦ hist S' ⟧ δ`,    --
--     which is `ηᵀ` for every rule but `DELAY` — the only rule that adds --
--     a lock — where it is the tick built from `delayᵀ`;                 --
--                                                                    --
--   * a sub-effecting coercion `T-≤`, as reduction refines the effect    --
--     grade (`COERCE` peels a coercion off; `SEQ-STEP` sharpens a        --
--     grade).                                                           --
--                                                                    --
-- `BOX` needs no transition: allocating a resource and extending the     --
-- store are the same morphism (`[ ρ ]ᶠ ⟦ V ⟧ ∘ᵐ η⊣`), used by both       --
-- `⟦_⟧ˢ`'s cell clause and `⟦ box V M ⟧ᶜᵗ`. Nor does `UNBOX`: it is a    --
-- projection out of the environment.                                     --
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
  using (handle-op-cont; ren-ᴱ-∷≡restrict)
open import OperationalSemantics.Soundness.Preservation.HandleOpClause S Cat Fut Pst Adj GTy Mon GE
  using (term∅; ∅-terminal; clause-sound)

open import OperationalSemantics.Soundness.Preservation.Handle S Cat Fut Pst Adj GTy Mon GE public

-- SUB-EFFECTING ACROSS A STEP
--
-- Composing two reduction steps substitutes the target configuration's
-- coercion under the Kleisli bind, so it has to escape from beneath `Tᶠ`: that
-- is sub-effecting in the monad's inner grade. It holds for the transitions
-- reduction produces — `ηᵀ` for every rule but `DELAY`, whose `delayᵀ` obeys
-- the model's `delayᵀ-≤`.

-- The grade a delayed computation's `ηᵀ` leaves behind.

delay-z : ∀ (τ : ℕ) (ε : E) → of-natᵉ τ ·ₑ ε ≾ₑ (of-natᵉ τ ·ₑ uₑ) ·ₑ ε
delay-z τ ε =
  ≾ₑ-trans (·ₑ-monoʳ-≾ₑ (≾ₑ-reflexive (sym (·ₑ-identityˡ ε))))
           (≾ₑ-reflexive (sym (·ₑ-assoc (of-natᵉ τ) uₑ ε)))

-- Binding a computation after a delay is delaying the bound computation. (The
-- `ηᵀ` the transition carries is absorbed, leaving only a regrading.)

delay-nf : ∀ {X Y B ε} → (τ : ℕ) → (env : X →ᵐ [ of-natʳ τ ]ᵒ Y) → (f : Y →ᵐ Tᵒ B ε)
         → μᵀ ∘ᵐ Tᶠ f ∘ᵐ (delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ env)
         ≈ᵐ T-≤ (delay-z τ ε) ∘ᵐ delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ f ∘ᵐ env
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

-- The nine rules that transition by `ηᵀ`: the coercion simply passes through,
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

T-≤-stepᵀ : ∀ {ε ε' εa εb A} {S S' : 𝕊 []} → (B : Obj)
          → {M : toCtx S ⊢C⦂ A ‼ ε} → {M' : toCtx S' ⊢C⦂ A ‼ ε'}
          → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
          → (g : ⟦ hist S' ⟧ᶜᵗˣ →ᵐ Tᵒ B εa) → (q : εa ≾ₑ εb)
          → μᵀ ∘ᵐ Tᶠ (T-≤ q ∘ᵐ g) ∘ᵐ stepᵀ r
          ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ μᵀ ∘ᵐ Tᶠ g ∘ᵐ stepᵀ r
T-≤-stepᵀ B APP         g q = ηᵀ-case g q
T-≤-stepᵀ B MATCH       g q = ηᵀ-case g q
T-≤-stepᵀ B SEQ-RET     g q = ηᵀ-case g q
T-≤-stepᵀ B SEQ-OP      g q = ηᵀ-case g q
T-≤-stepᵀ B HANDLE-RET  g q = ηᵀ-case g q
T-≤-stepᵀ B HANDLE-OP   g q = ηᵀ-case g q
T-≤-stepᵀ B BOX         g q = ηᵀ-case g q
T-≤-stepᵀ B UNBOX       g q = ηᵀ-case g q
T-≤-stepᵀ B COERCE      g q = ηᵀ-case g q
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
    z : of-natᵉ τ ·ₑ εa ≾ₑ (of-natᵉ τ ·ₑ uₑ) ·ₑ εb
    z = ≾ₑ-trans (·ₑ-monoʳ-≾ₑ q) (delay-z τ εb)

------------------------------------------------------------------------
-- THE SOUNDNESS THEOREM
--
-- A reduction step relates denotationally equal configurations: the source's
-- denotation is the target's, run after the step's time transition and coerced
-- along the effect refinement the step licenses. Right to left:
--
--   * `stepᵀ r` is the time the step takes, a map between the two states'
--     histories. Every rule but `DELAY` takes none, transitioning by `ηᵀ`;
--     `DELAY` ticks by its own delay.
--
--   * `⟦ ⟨ S' , M' ⟩ ⟧ᶜᶠ ⋄ stepᵀ r` is the target configuration run over that
--     later history, the two effect grades multiplying (`step-grade r ·ₑ ε'`).
--
--   * `T-≤ (step-≾ r)` puts the result back at the source's grade `ε`, by
--     `step-≾ r : step-grade r ·ₑ ε' ≾ₑ ε`: a step never costs more than the
--     type promised.
--
-- The state does not appear: it is the environment, already plugged into both
-- sides by `⟦_⟧ᶜᶠ`. `BOX` is invisible because extending the store and boxing a
-- resource are the same morphism, `UNBOX` because reading a cell projects out
-- the value the state wrote there.
------------------------------------------------------------------------

-- The handlers a reduction actually reaches must be uniform. `HANDLE-OP` is the
-- only rule that fires a clause, and the only rules that can reach it are the
-- two congruences — so this is a recursion on the *reduction*, not on the term.

-- The clauses' uniformity in the residual effect is carried by the term's own
-- `Paramᶜ`, so a reduction assumes nothing on top of it and every case is `⊤`.
-- It stays a predicate so the soundness statements can take it uniformly.

Uniform↝ : ∀ {ε ε' A} {S S' : 𝕊 []}
         → {M : toCtx S ⊢C⦂ A ‼ ε} → {M' : toCtx S' ⊢C⦂ A ‼ ε'}
         → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩) → Paramᶜ M
         → Set
Uniform↝ HANDLE-OP           _            = ⊤
Uniform↝ (SEQ-STEP r _)      (pM , _)     = Uniform↝ r pM
Uniform↝ (HANDLE-STEP r _)   (pM , _)     = Uniform↝ r pM
Uniform↝ APP                 _            = ⊤
Uniform↝ MATCH               _            = ⊤
Uniform↝ SEQ-RET             _            = ⊤
Uniform↝ SEQ-OP              _            = ⊤
Uniform↝ DELAY               _            = ⊤
Uniform↝ HANDLE-RET          _            = ⊤
Uniform↝ BOX                 _            = ⊤
Uniform↝ UNBOX               _            = ⊤
Uniform↝ COERCE              _            = ⊤

-- The computation's certificate across a step: every reduct is built from the
-- source's pieces by renaming, substitution and retyping, each of which
-- transports parametricity.

stepᴾᶜ : ∀ {ε ε' A} {S S' : 𝕊 []}
       → {M : toCtx S ⊢C⦂ A ‼ ε} → {M' : toCtx S' ⊢C⦂ A ‼ ε'}
       → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩) → Paramˢ S → Paramᶜ M → Paramᶜ M'
stepᴾᶜ (APP {M = M} {V = V})            pS (pM , pV)  = subᶜ M Hd V pM pV
stepᴾᶜ (MATCH {V = V} {W = W} {M = M})  pS ((pV , pW) , pM) =
  subᶜ (M [ Hd ↦ V-rename wk-ren W ]c) Hd V
    (subᶜ M Hd (V-rename wk-ren W) pM (renᵛ wk-ren W pW)) pV
stepᴾᶜ (SEQ-STEP {N = N} r c)           pS (pM , pN)  =
  stepᴾᶜ r pS pM
  , renᶜ (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N pN
stepᴾᶜ (SEQ-RET {V = V} {N = N})        pS (pV , pN)  = ret-subᴾ V N pV pN
stepᴾᶜ (SEQ-OP {op = op} {S = S} {V = V} {M = M} {N = N}) pS ((pV , pM) , pN) =
  ε-substᴾ (sym (·ₑ-assoc (op-grade op) _ _))
    (perform op V (M ⨟ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren ∘ʳ eq-ren (cong (toCtx S ⟨_⟩) map-·ᵉ))) N))
    (pV , pM , renᶜ (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren ∘ʳ eq-ren (cong (toCtx S ⟨_⟩) map-·ᵉ))) N pN)
stepᴾᶜ DELAY                            pS pM         = pM
stepᴾᶜ (HANDLE-RET {V = V} {N = N})     pS (pV , pN , pH , uH) = ret-subᴾ V N pV pN
stepᴾᶜ (HANDLE-STEP {S = S} {S' = S'} {H = H} {N = N} r c) pS (pM , pN , pH , uH) =
  stepᴾᶜ r pS pM
  , renᶜ (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N pN
  , (λ op ε₃ → substᴾᶜ (trans (toCtxᴱ-[] S) (sym (toCtxᴱ-[] S'))) (H op ε₃) (pH op ε₃))
  , subst-clauses-uniform (trans (toCtxᴱ-[] S) (sym (toCtxᴱ-[] S'))) H pH uH
stepᴾᶜ (HANDLE-OP {ε = ε} {ε'' = ε''} {op = op} {S = S} {V = V} {M = M} {H = H} {N = N})
       pS ((pV , pM) , pN , pH , uH) =
    (pM
    , renᶜ (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren ∘ʳ eq-ren (cong (toCtx S ⟨_⟩) map-·ᵉ))) N pN
    , (λ op' ε' → renᶜ (cong-∷-ren (cong-∷-ren (ren-ᴱ-∷ {toCtx S ⟨ mapᵉ (op-grade op) ⟩} (type-of-gtype (arity op))))) (H op' ε') (pH op' ε'))
    , ren-clauses-uniform
        (ren-ᴱ-∷ {toCtx S ⟨ mapᵉ (op-grade op) ⟩} (type-of-gtype (arity op))) H pH uH)
  , subᶜ (C-rename (cong-∷-ren (cong-∷-ren (ᴱ-ren (toCtx S)))) (H op (ε ·ₑ ε'')))
         (Tl-∷ Hd) V
         (renᶜ (cong-∷-ren (cong-∷-ren (ᴱ-ren (toCtx S))))
               (H op (ε ·ₑ ε'')) (pH op (ε ·ₑ ε'')))
         pV
stepᴾᶜ BOX                              pS (pV , pM)  = pM
stepᴾᶜ (UNBOX {S = S} {w = w} {V = V} {M = M}) pS (pV , pM) =
  subᶜ M Hd (unbox-lookup S w V) pM (unbox-lookupᴾ S w V pS)
stepᴾᶜ COERCE                           pS pM         = pM

-- Both halves at once, for a configuration.

stepᴾᶜᶠ : ∀ {ε ε' A} {S S' : 𝕊 []}
        → {M : toCtx S ⊢C⦂ A ‼ ε} → {M' : toCtx S' ⊢C⦂ A ‼ ε'}
        → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩) → (p : Paramᶜᶠ (⟨ S , M ⟩))
        → Paramᶜᶠ (⟨ S' , M' ⟩)
stepᴾᶜᶠ r (pS , pM) = stepᴾˢ r pS pM , stepᴾᶜ r pS pM

↝-sound : ∀ {ε ε' A} {S S' : 𝕊 []}
        → {M : toCtx S ⊢C⦂ A ‼ ε} → {M' : toCtx S' ⊢C⦂ A ‼ ε'}
        → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
        → (pS : Paramˢ S) → (pM : Paramᶜ M)
        → Uniform↝ r pM
        → ⟦ ⟨ S , M ⟩ ⟧ᶜᶠ (pS , pM)
        ≈ᵐ T-≤ (step-≾ r)
           ∘ᵐ _⋄_ {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {step-grade r} {ε'}
                  (⟦ ⟨ S' , M' ⟩ ⟧ᶜᶠ (stepᴾᶜᶠ r (pS , pM))) (stepᵀ r)

-- The rules that neither advance time nor change the store: a plain equation
-- between the two denotations, with `ηᵀ`'s unit grade absorbed by `T-≤`.

↝-sound r@(APP {M = M} {V = V}) pS (pM , pV) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-APP M V pM pV))
↝-sound r@(MATCH {V = V} {W = W} {M = M}) pS ((pV , pW) , pM) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-MATCH V W M pV pW pM))
↝-sound r@(SEQ-OP {op = op} {V = V} {M = M} {N = N}) pS ((pV , pM) , pN) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-SEQ-OP op V M N pV pM pN))

-- Allocation and lookup: also plain equations, but ones that mention the store.

↝-sound r@(BOX {S = St} {V = V} {M = M}) pS (pV , pM) _ =
  pure-step-≡ (step-≾ r) (sound-BOX St V M pS pV pM)
↝-sound r@(UNBOX {S = St} {w = w} {V = V} {M = M}) pS (pV , pM) _ =
  pure-step-≡ (step-≾ r) (sound-UNBOX St w V M pS pV pM)

-- The `return` rules: the coercion the substitution leaves behind is `ε-substᵀ`,
-- which `T-≤-≡` turns into the sub-effecting the theorem asks for.

↝-sound r@(SEQ-RET {V = V} {N = N}) pS (pV , pN) _ =
  pure-step (step-≾ r) (≾ₑ-reflexive (sym (·ₑ-identityˡ _)))
    (∘ᵐ-congˡ (sound-SEQ-RET V N pV pN) ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congˡ (T-≤-≡ _))
↝-sound r@(HANDLE-RET {V = V} {H = H} {N = N}) pS (pV , pN , pH , uH) _ =
  pure-step (step-≾ r) (≾ₑ-reflexive (sym (·ₑ-identityˡ _)))
    (∘ᵐ-congˡ (sound-HANDLE-RET V H N pV pN pH uH)
     ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congˡ (T-≤-≡ _))

-- Peeling a coercion: the step refines the grade by exactly the coercion's own
-- witness, which is what `T-≤` already does.

↝-sound r@(COERCE {M = M} {ε≾ε' = p}) pS pM _ =
  pure-step (step-≾ r) p (∘ᵐ-congˡ (sound-COERCE p M pM) ∙ ∘ᵐ-assoc _ _ _)

-- The one rule that advances time.

↝-sound r@(DELAY {τ = τ} {S = St} {M = M}) pS pM _ =
  sound-DELAY τ St M (step-≾ r) pS pM

-- The congruence rules: the inductive hypothesis is pushed through the strength
-- and multiplied, the environment carried across the step by `step-box`.

↝-sound (SEQ-STEP {N = N} r c) pS (pM , pN) u =
  sound-SEQ-STEP N r c pS pM pN (stepᴾᶜ r pS pM) (↝-sound r pS pM u)
↝-sound (HANDLE-STEP {H = H} {N = N} r c) pS (pM , pN , pH , uH) u =
  sound-HANDLE-STEP H N r c pS pM pN (stepᴾᶜ r pS pM) pH uH (↝-sound r pS pM u)

-- Handling an operation: the clause is applied, with the handled remainder
-- boxed up as its continuation. This is the only rule that reads a clause; its
-- parametricity now comes from the term's own `Paramᶜ` certificate.

↝-sound {S = S} r@(HANDLE-OP {op = op} {V = V} {M = M} {H = H} {N = N})
        pS ((pV , pM) , pN , pH , uH) u =
  pure-step (step-≾ r) (≾ₑ-reflexive (sym (·ₑ-assoc (op-grade op) _ _)))
    (∘ᵐ-congˡ (sound-HANDLE-OP (toCtxᴱ-[] S) op V M H N pV pM pN pH uH)
     ∙ ∘ᵐ-assoc _ _ _
     ∙ ∘ᵐ-congˡ (T-≤-≡ _))


------------------------------------------------------------------------
-- THE MULTI-STEP CLOSURE
--
-- A run of the machine is sound: the source configuration's denotation is the
-- final one's, run after the accumulated transition, coerced along the
-- accumulated refinement. The three components multiply/compose exactly as the
-- single-step ones do, and the induction goes through because the target's
-- coercion escapes the bind (`T-≤-stepᵀ`).
------------------------------------------------------------------------

-- The accumulated effect of a run, its transition, and its refinement.

steps-grade : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
            → cf ↝* cf' → E
steps-grade ε*        = uₑ
steps-grade (r ◅ rs)  = step-grade r ·ₑ steps-grade rs

stepsᵀ : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
       → (rs : cf ↝* cf')
       → ⟦ hist (Config.state cf) ⟧ᶜᵗˣ
       →ᵐ Tᵒ ⟦ hist (Config.state cf') ⟧ᶜᵗˣ (steps-grade rs)
stepsᵀ ε*       = ηᵀ
stepsᵀ (r ◅ rs) = stepsᵀ rs ⋄ stepᵀ r

steps-≾ : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
        → (rs : cf ↝* cf') → steps-grade rs ·ₑ ε' ≾ₑ ε
steps-≾ {ε = ε} ε*       = ≾ₑ-reflexive (·ₑ-identityˡ ε)
steps-≾ {ε' = ε'} (_◅_ {ε₂ = ε₂} r rs) =
  -- the step's own refinement, after the run's, reassociated
  ≾ₑ-trans (≾ₑ-reflexive (·ₑ-assoc (step-grade r) (steps-grade rs) ε'))
  (≾ₑ-trans (·ₑ-monoʳ-≾ₑ (steps-≾ rs)) (step-≾ r))

-- Every handler the run reaches must be uniform.

-- The certificate accumulated along a run.

stepsᴾᶜᶠ : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
         → cf ↝* cf' → Paramᶜᶠ cf → Paramᶜᶠ cf'
stepsᴾᶜᶠ ε*       p = p
stepsᴾᶜᶠ (r ◅ rs) p = stepsᴾᶜᶠ rs (stepᴾᶜᶠ r p)

Uniform↝* : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
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

-- SOUNDNESS OF A RUN

↝*-sound : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
         → (rs : cf ↝* cf') → (p : Paramᶜᶠ cf) → Uniform↝* rs p
         → ⟦ cf ⟧ᶜᶠ p
         ≈ᵐ T-≤ (steps-≾ rs)
            ∘ᵐ _⋄_ {⟦ hist (Config.state cf) ⟧ᶜᵗˣ}
                   {⟦ hist (Config.state cf') ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ}
                   {steps-grade rs} {ε'}
                   (⟦ cf' ⟧ᶜᶠ (stepsᴾᶜᶠ rs p)) (stepsᵀ rs)
-- the empty run: the transition is `ηᵀ`, which the bind absorbs
↝*-sound {A = A} {ε = ε} {cf = cf} ε* p _ =
  pure-step-≡ (steps-≾ (ε* {A} {ε} {cf})) ≈ᵐ-refl
-- a step, then a run
↝*-sound {A = A} {ε' = ε'} (_◅_ {ε₂ = ε₂} {cf₃ = cf₃} r rs) (pS , pM) (u , us) =
  -- the step is sound …
    ↝-sound r pS pM u
  -- … and so, inductively, is the run that follows it
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (↝*-sound rs (stepᴾᶜᶠ r (pS , pM)) us))))
  -- THE KEY STEP: the run's coercion escapes the bind
  ∙ ∘ᵐ-congʳ (T-≤-stepᵀ ⟦ A ⟧ᵛ r
       (⟦ cf₃ ⟧ᶜᶠ (stepsᴾᶜᶠ rs (stepᴾᶜᶠ r (pS , pM))) ⋄ stepsᵀ rs) (steps-≾ rs))
  -- the two binds re-associate into one, at the product of their grades …
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (bind-bind (⟦ cf₃ ⟧ᶜᶠ (stepsᴾᶜᶠ rs (stepᴾᶜᶠ r (pS , pM))))
                          (stepsᵀ rs) (stepᵀ r)))
  -- … and the three coercions collapse into the run's own
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-≡ _)))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-trans _ _ b))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-≤-trans b (step-≾ r) (steps-≾ (r ◅ rs)))
  where
    b : steps-grade (r ◅ rs) ·ₑ ε' ≾ₑ step-grade r ·ₑ ε₂
    b = ≾ₑ-trans (≾ₑ-reflexive (·ₑ-assoc (step-grade r) (steps-grade rs) ε'))
                 (·ₑ-monoʳ-≾ₑ (steps-≾ rs))



------------------------------------------------------------------------
-- DENOTATIONAL RUNNING
--
-- `cf ⊳ cf'` says that `cf` runs to `cf'` denotationally: `cf` is `cf'`,
-- executed after some transition and coerced along some refinement. `↝*-⊳`
-- says a run of the machine witnesses it.
--
-- The relation is directed, not an equivalence: the two sides sit at different
-- effect grades, and `T-≤ refine` only coerces the target's (finer) grade up
-- to the source's, never back.
--
-- It is reflexive (`⊳-refl`) but not transitive: transitivity would have to
-- substitute the middle configuration's coercion under an arbitrary
-- transition's bind, and sub-effecting escapes a bind only for the transitions
-- reduction produces (`T-≤-stepᵀ`). Transitivity along a run is the induction
-- in `↝*-sound`.
------------------------------------------------------------------------

infix 4 _⊳_

-- The configurations are implicit, carried by their parametricity
-- certificates: interpreting a configuration needs one, so the relation is
-- between certified configurations.

record _⊳_ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
           (p : Paramᶜᶠ cf) (p' : Paramᶜᶠ cf') : Set where
  constructor mk⊳
  field
    -- the effect the transition performs, and the refinement it licenses
    grade : E
    refine : grade ·ₑ ε' ≾ₑ ε
    -- the transition itself, between the two states' histories
    tr     : ⟦ hist (Config.state cf) ⟧ᶜᵗˣ
           →ᵐ Tᵒ ⟦ hist (Config.state cf') ⟧ᶜᵗˣ grade
    -- and the equation
    sound  : ⟦ cf ⟧ᶜᶠ p
           ≈ᵐ T-≤ refine
              ∘ᵐ _⋄_ {⟦ hist (Config.state cf) ⟧ᶜᵗˣ}
                     {⟦ hist (Config.state cf') ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {grade} {ε'}
                     (⟦ cf' ⟧ᶜᶠ p') tr

-- Reflexivity: a configuration runs to itself, taking no time and refining
-- nothing.

⊳-refl : ∀ {A ε} → (cf : Config (A ‼ ε)) → (p : Paramᶜᶠ cf)
       → _⊳_ {cf = cf} {cf' = cf} p p
⊳-refl {ε = ε} cf p =
  mk⊳ uₑ (steps-≾ (ε* {cf = cf})) ηᵀ (↝*-sound (ε* {cf = cf}) p tt)

-- A run of the machine is such a witness. This is the soundness theorem in its
-- final form: reduction never changes what a configuration means.

↝*-⊳ : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
     → (rs : cf ↝* cf') → (p : Paramᶜᶠ cf) → Uniform↝* rs p
     → _⊳_ {cf = cf} {cf' = cf'} p (stepsᴾᶜᶠ rs p)
↝*-⊳ rs p us =
  mk⊳ (steps-grade rs) (steps-≾ rs) (stepsᵀ rs) (↝*-sound rs p us)

-- CLOSED PROGRAMS
--
-- A program is a closed computation: the empty state, so the empty history, so
-- its denotation is a global point of `Tᵒ ⟦ A ⟧ᵛ ε`. If it runs to a returned
-- value, the program *is* that value returned — after the run's transition, and
-- at the run's (refined) grade. Nothing of the state survives in the equation:
-- `hist ∅ ≡ []`, so both sides are morphisms out of `𝟙ᵐ`.

Program : VType → E → Set
Program A ε = [] ⊢C⦂ A ‼ ε

⟦_⟧ᵖ : ∀ {A ε} → (M : Program A ε) → Paramᶜ M → 𝟙ᵐ →ᵐ Tᵒ ⟦ A ⟧ᵛ ε
⟦ M ⟧ᵖ p = ⟦ M ⟧ᶜᵗ p

-- Running a program to a value: its denotation is `ηᵀ` of the value's, in the
-- final state's environment, composed with the run's transition.

↝*-value : ∀ {A ε} {S' : 𝕊 []}
         → (M : Program A ε)
         → (V : toCtx S' ⊢V⦂ A)
         → (rs : ⟨ ∅ , M ⟩ ↝* ⟨ S' , return V ⟩)
         → (pM : Paramᶜ M)
         → Uniform↝* rs (tt , pM)
         → ⟦ M ⟧ᵖ pM
         ≈ᵐ T-≤ (steps-≾ rs)
            ∘ᵐ _⋄_ {𝟙ᵐ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {steps-grade rs} {uₑ}
                   (ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ (proj₂ (stepsᴾᶜᶠ rs (tt , pM)))
                       ∘ᵐ ⟦ S' ⟧ˢ (proj₁ (stepsᴾᶜᶠ rs (tt , pM))))
                   (stepsᵀ rs)
↝*-value M V rs pM us =
  -- the empty state is the empty environment
    ≈ᵐ-sym (∘ᵐ-identityʳ _)
  ∙ ↝*-sound rs (tt , pM) us
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (∘ᵐ-assoc _ _ _))))
