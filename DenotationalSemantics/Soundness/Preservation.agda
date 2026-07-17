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

module DenotationalSemantics.Soundness.Preservation
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut GTy)
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
                       []-monoidal-nat) renaming (ε to εᵇ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; μ; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ; ⟨⟩-η-nat; ⟨⟩-μ-nat;
                     ⟨⟩-≤-nat; ⟨⟩-≤-irr; ⟨⟩-≤-refl; ⟨⟩-≤-trans; μ-≤ˡ; μ-≤ʳ;
                     ⟨⟩-μ∘Tη≡id; ⟨⟩-μ∘η≡id)
open Adjunction Adj using (η⊣; η⊣-nat; η⊣-u; η⊣-≤; η⊣-δ; η⊣-monoidal;
                           ε⊣; ε⊣-nat; triangleˡ)
open GroundTypes GTy using (⟦_⟧ᵍ)
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst GTy Mon
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.State S Cat Fut Pst Adj GTy Mon GE

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ; eternalᵒ-boxCoalg)
open import DenotationalSemantics.Model.Modality.BoxCoalg
       Cat (GradeSystem.RGrade Grades) Fut using (BoxCoalg)

-- The `BoxCoalg` on `⟦ Γ ᴱ ⟧` carried by every `handle` interpretation: the
-- eternal-parameter object of the handler's fold.
bcᴱ : ∀ (Γ : Ctx) → BoxCoalg ⟦ Γ ᴱ ⟧ᶜᵗˣ
bcᴱ Γ = eternalᵒ-boxCoalg (⟦ Γ ⟧ᴱ-Eternalᵒ)

-- THE INTERPRETATION OF A CONFIGURATION
--
-- The computation, with its context plugged by the state.

⟦_⟧ᶜᶠ : ∀ {C} → (cf : Config C) → ⟦ hist (Config.state cf) ⟧ᶜᵗˣ →ᵐ ⟦ C ⟧ᶜ
⟦ ⟨ St , M ⟩ ⟧ᶜᶠ = ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ St ⟧ˢ

-- KLEISLI COMPOSITION WITH A TIME TRANSITION
--
-- Running a computation over the later history, after the transition that
-- produces it. The effect grades multiply.

_⋄_ : ∀ {X Y A ε ε'}
    → (Y →ᵐ Tᵒ A ε')
    → (X →ᵐ Tᵒ Y ε)
    → X →ᵐ Tᵒ A (ε ·ₑ ε')
f ⋄ t = μᵀ ∘ᵐ Tᶠ f ∘ᵐ t

infixl 25 _⋄_

-- THE TIME TRANSITION OF A STEP
--
-- The effect it performs. Only `DELAY` does anything: it is the sole rule
-- that advances time, and it does so by exactly its own delay. Resources
-- (cells) are allocated into the *shape* of the store, never into the
-- effect grade, which is why allocation contributes `uₑ`.

step-grade : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
           → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
           → ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩
           → E
step-grade APP                  = uₑ
step-grade MATCH                = uₑ
step-grade (SEQ-STEP r _)       = step-grade r
step-grade SEQ-RET              = uₑ
step-grade SEQ-OP               = uₑ
step-grade (DELAY {τ = τ})      = of-natᵉ τ ·ₑ uₑ
step-grade HANDLE-RET           = uₑ
step-grade (HANDLE-STEP r _)    = step-grade r
step-grade HANDLE-OP            = uₑ
step-grade BOX                  = uₑ
step-grade UNBOX                = uₑ
step-grade COERCE               = uₑ

-- The transition itself. `DELAY` ticks: it names the present as the past of
-- every world one delay ahead (`η⊣`), and `delayᵀ` is what actually reaches
-- those worlds — this is the only way a lock can ever be produced.

stepᵀ : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
      → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
      → (r : ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩)
      → ⟦ hist St ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ hist St' ⟧ᶜᵗˣ (step-grade r)
stepᵀ APP               = ηᵀ
stepᵀ MATCH             = ηᵀ
stepᵀ (SEQ-STEP r _)    = stepᵀ r
stepᵀ SEQ-RET           = ηᵀ
stepᵀ SEQ-OP            = ηᵀ
stepᵀ (DELAY {τ = τ})   = delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣
stepᵀ HANDLE-RET        = ηᵀ
stepᵀ (HANDLE-STEP r _) = stepᵀ r
stepᵀ HANDLE-OP         = ηᵀ
stepᵀ BOX               = ηᵀ
stepᵀ UNBOX             = ηᵀ
stepᵀ COERCE            = ηᵀ

-- The step's effect, composed with the target's, refines the source's. This is
-- `step-grade-≾` in the effect grades.

step-≾ : ∀ {ε ε'} {St St' : 𝕊 []} {A : VType}
       → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
       → (r : ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩)
       → step-grade r ·ₑ ε' ≾ₑ ε
step-≾ {ε = ε} APP    = ≾ₑ-reflexive (·ₑ-identityˡ ε)
step-≾ {ε = ε} MATCH  = ≾ₑ-reflexive (·ₑ-identityˡ ε)
step-≾ (SEQ-STEP {ε₂ = ε₂} {ε₃ = ε₃} r _) =
  ≾ₑ-trans
    (≾ₑ-reflexive (sym (·ₑ-assoc (step-grade r) ε₃ ε₂)))
    (·ₑ-monoˡ-≾ₑ (step-≾ r))
step-≾ SEQ-RET        = ≾ₑ-reflexive refl
step-≾ {ε = ε} SEQ-OP = ≾ₑ-reflexive (·ₑ-identityˡ ε)
step-≾ (DELAY {τ = τ} {ε = ε}) =
  ≾ₑ-reflexive (cong (_·ₑ ε) (·ₑ-identityʳ (of-natᵉ τ)))
step-≾ HANDLE-RET     = ≾ₑ-reflexive refl
step-≾ (HANDLE-STEP {ε₂ = ε₂} {ε₁' = ε₁'} r _) =
  ≾ₑ-trans
    (≾ₑ-reflexive (sym (·ₑ-assoc (step-grade r) ε₁' ε₂)))
    (·ₑ-monoˡ-≾ₑ (step-≾ r))
step-≾ (HANDLE-OP {ε = ε} {ε'' = ε''} {op = op}) =
  ≾ₑ-reflexive
    (trans (·ₑ-identityˡ _) (sym (·ₑ-assoc (op-grade op) ε ε'')))
step-≾ {ε = ε} BOX    = ≾ₑ-reflexive (·ₑ-identityˡ ε)
step-≾ {ε = ε} UNBOX  = ≾ₑ-reflexive (·ₑ-identityˡ ε)
step-≾ (COERCE {ε = ε} {ε≾ε' = ε≾ε'}) =
  ≾ₑ-trans (≾ₑ-reflexive (·ₑ-identityˡ ε)) ε≾ε'

-- Sub-effecting is irrelevant in its witness (the effect order is).

T-≤-irr : ∀ {A ε ε'} → (p q : ε ≾ₑ ε') → T-≤ {A} p ≈ᵐ T-≤ {A} q
T-≤-irr {A} p q =
  subst (λ z → T-≤ {A} p ≈ᵐ T-≤ {A} z) (≾ₑ-irrelevant p q) ≈ᵐ-refl

-- Chaining equational steps (right-associated `≈ᵐ-trans`), so that the long
-- rewriting chains below read as a linear sequence of steps.

infixr 3 _∙_

_∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
_∙_ = ≈ᵐ-trans

-- Composing with the trivial transition just re-grades: `ηᵀ` allocates no
-- time, so the Kleisli composite is the computation itself.

⋄-ηᵀ : ∀ {X A ε'} → (f : X →ᵐ Tᵒ A ε')
     → f ⋄ ηᵀ ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε')) ∘ᵐ f
⋄-ηᵀ f =
  ≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (ηᵀ-nat f)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ T-μ∘η≡id))

-- THE TIME-PRESERVING STEPS
--
-- Every rule but `DELAY` leaves the history alone and transitions by `ηᵀ`.
-- For those the soundness equation collapses to a plain equation between
-- the two computations' denotations, coerced along the effect refinement:
-- the `uₑ` that `ηᵀ` contributes is absorbed by `T-≤`, which the tree
-- equality lets us do precisely because it collapses coercion nodes.

pure-step : ∀ {X A ε ε'}
          → (q : uₑ ·ₑ ε' ≾ₑ ε)
          → {f : X →ᵐ Tᵒ A ε} → {g : X →ᵐ Tᵒ A ε'}
          → (r : ε' ≾ₑ ε)
          → f ≈ᵐ T-≤ r ∘ᵐ g
          → f ≈ᵐ T-≤ q ∘ᵐ (g ⋄ ηᵀ)
pure-step {ε' = ε'} q {f} {g} r e =
  ≈ᵐ-trans e
    (≈ᵐ-sym
      (≈ᵐ-trans (∘ᵐ-congʳ (⋄-ηᵀ g))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-≡ uₑ·ε'≡ε')))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                (∘ᵐ-congˡ (T-≤-trans (≾ₑ-reflexive uₑ·ε'≡ε') q r))))))
  where
    uₑ·ε'≡ε' : ε' ≡ uₑ ·ₑ ε'
    uₑ·ε'≡ε' = sym (·ₑ-identityˡ ε')

-- The special case where the effect grade does not change at all: then the
-- coercion is the identity and only the two denotations need to agree.

pure-step-≡ : ∀ {X A ε}
            → (q : uₑ ·ₑ ε ≾ₑ ε)
            → {f g : X →ᵐ Tᵒ A ε}
            → f ≈ᵐ g
            → f ≈ᵐ T-≤ q ∘ᵐ (g ⋄ ηᵀ)
pure-step-≡ {ε = ε} q {f} {g} e =
  pure-step q (≾ₑ-reflexive refl) e'
  where
    e' : f ≈ᵐ T-≤ (≾ₑ-reflexive {ε} refl) ∘ᵐ g
    e' = ≈ᵐ-trans e
           (≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-congˡ (T-≤-refl (≾ₑ-reflexive {ε} refl)))
                             (∘ᵐ-identityˡ g)))

-- Transporting along a context equality and back is the identity.

eq-ren-inv : ∀ {Γ Γ'} → (e : Γ ≡ Γ')
           → ⟦ eq-ren (sym e) ⟧ʳ ∘ᵐ ⟦ eq-ren e ⟧ʳ ≈ᵐ idᵐ
eq-ren-inv refl = ∘ᵐ-identityˡ idᵐ

-- APP: applying an abstraction is substituting into its body (`βᵐ` plus the
-- substitution coherence, whose environment `sub-env Hd V` is `⟨ idᵐ , ⟦V⟧ ⟩ᵐ`).

sound-APP : ∀ {Γ A B ε} → (M : Γ ∷ A ⊢C⦂ B ‼ ε) → (V : Γ ⊢V⦂ A)
          → ⟦ lam M · V ⟧ᶜᵗ ≈ᵐ ⟦ M [ Hd ↦ V ]c ⟧ᶜᵗ
sound-APP M V =
  ≈ᵐ-trans (βᵐ ⟦ M ⟧ᶜᵗ ⟦ V ⟧ᵛᵗ) (≈ᵐ-sym (C-subst-nat M Hd V))

-- MATCH: destructing a pair is the two substitutions in sequence. The inner
-- one substitutes `W` weakened past `A`, which reindexes it by `fstᵐ`; that
-- projection is then cancelled by the outer environment.

sound-MATCH : ∀ {Γ A B C} → (V : Γ ⊢V⦂ A) → (W : Γ ⊢V⦂ B) → (M : Γ ∷ A ∷ B ⊢C⦂ C)
            → ⟦ match ⦉ V , W ⦊ `in M ⟧ᶜᵗ
            ≈ᵐ ⟦ (M [ Hd ↦ V-rename wk-ren W ]c) [ Hd ↦ V ]c ⟧ᶜᵗ
sound-MATCH V W M =
  ≈ᵐ-trans
    (∘ᵐ-congʳ (⟨ ⟨ ≈ᵐ-refl , ⟨⟩ᵐ-fstᵐ _ _ ⟩ᵐ-cong , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong))
    (≈ᵐ-sym
      (≈ᵐ-trans (C-subst-nat (M [ Hd ↦ V-rename wk-ren W ]c) Hd V)
      (≈ᵐ-trans (∘ᵐ-congˡ (C-subst-nat M Hd (V-rename wk-ren W)))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                (∘ᵐ-congʳ
                  (≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
                            (⟨ ∘ᵐ-identityˡ _
                             , ≈ᵐ-trans (∘ᵐ-congˡ (V-rename-nat wk-ren W))
                               (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                               (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                                         (∘ᵐ-identityʳ _))) ⟩ᵐ-cong)))))))

-- BOX: allocating a resource and extending the store are the *same* morphism,
-- so the two configurations' denotations coincide outright. The stored value
-- is the boxed one reindexed along `[] ++ᶜ Γ ≡ Γ`, which cancels.

sound-BOX : ∀ {A B ρ ε} → (St : 𝕊 []) → (V : toCtx St ⟨ ρ ⟩ ⊢V⦂ A)
          → (M : toCtx St ∷ [ ρ ] A ⊢C⦂ B ‼ ε)
          → ⟦ box V M ⟧ᶜᵗ ∘ᵐ ⟦ St ⟧ˢ
          ≈ᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ St ∷ₛ V-rename (eq-ren (sym ++ᶜ-identityˡ)) V ⟧ˢ
sound-BOX {ρ = ρ} St V M =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (∘ᵐ-congʳ (∘ᵐ-congˡ
      (⟨ ≈ᵐ-refl {f = idᵐ}
       , ∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym stored≈V)) ⟩ᵐ-cong)))
  where
    -- the value the state stores is `V` reindexed along `[] ++ᶜ Γ ≡ Γ`,
    -- and the state's interpretation reindexes it straight back
    stored≈V : ⟦ V-rename (eq-ren (sym (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩}))) V ⟧ᵛᵗ
                 ∘ᵐ ⟦ eq-ren (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩}) ⟧ʳ
             ≈ᵐ ⟦ V ⟧ᵛᵗ
    stored≈V =
      ≈ᵐ-trans (∘ᵐ-congˡ (V-rename-nat (eq-ren (sym (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩}))) V))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (eq-ren-inv (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩})))
                (∘ᵐ-identityʳ _)))

-- COERCE: peeling a coercion off is exactly what `T-≤` does.

sound-COERCE : ∀ {Γ A ε ε'} → (p : ε ≾ₑ ε') → (M : Γ ⊢C⦂ A ‼ ε)
             → ⟦ coerce p M ⟧ᶜᵗ ≈ᵐ T-≤ p ∘ᵐ ⟦ M ⟧ᶜᵗ
sound-COERCE p M = ≈ᵐ-refl

-- TRANSPORT ALONG GRADE EQUALITIES
--
-- `ε-substᵀ` is a transport, so it commutes with everything in sight; each
-- of these follows by matching the equality.

ε-substᵀ-nat : ∀ {A B ε ε'} → (e : ε ≡ ε') → (f : A →ᵐ B)
             → Tᶠ f ∘ᵐ ε-substᵀ e ≈ᵐ ε-substᵀ e ∘ᵐ Tᶠ f
ε-substᵀ-nat refl f =
  ≈ᵐ-trans (∘ᵐ-congʳ ε-substᵀ-refl)
  (≈ᵐ-trans (∘ᵐ-identityʳ _)
            (≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-congˡ ε-substᵀ-refl) (∘ᵐ-identityˡ _))))

delayᵀ-ε-substᵀ : ∀ {A ε ε'} → (τ : ℕ) → (e : ε ≡ ε')
                → delayᵀ {A} {ε'} τ ∘ᵐ [ of-natʳ τ ]ᶠ (ε-substᵀ e)
                ≈ᵐ ε-substᵀ (cong (of-natᵉ τ ·ₑ_) e) ∘ᵐ delayᵀ {A} {ε} τ
delayᵀ-ε-substᵀ τ refl =
  ≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans ([]-congᶠ ε-substᵀ-refl) []-idᵐ))
  (≈ᵐ-trans (∘ᵐ-identityʳ _)
            (≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-congˡ ε-substᵀ-refl) (∘ᵐ-identityˡ _))))

-- A coercion cancels the transport it undoes (both are `T-≤`, and `T-≤` is
-- functorial in the grade).

coe-cancel : ∀ {A ε ε'} → (e : ε ≡ ε') → (q : ε' ≾ₑ ε)
           → T-≤ {A} q ∘ᵐ ε-substᵀ e ≈ᵐ idᵐ
coe-cancel e q =
  ≈ᵐ-trans (∘ᵐ-congʳ (T-≤-≡ e))
  (≈ᵐ-trans (T-≤-trans (≾ₑ-reflexive e) q (≾ₑ-reflexive refl))
            (T-≤-refl (≾ₑ-reflexive refl)))

-- DELAY: the tick.
--
-- This is the only rule that advances time, and the only one whose history
-- grows. `η⊣`-naturality is what does the work: the state's interpretation
-- passes under the new lock (`⟦ St ⟨ ρ ⟩ₛ ⟧ˢ = ⟨ ρ ⟩ᶠ ⟦ St ⟧ˢ`), so the
-- source's `η⊣ ∘ᵐ ⟦ St ⟧ˢ` is the target's environment already boxed up.
-- The transition then supplies exactly the `delayᵀ` that reaches the worlds
-- one delay ahead, and `delayᵀ`'s algebraicity re-associates it out.

sound-DELAY : ∀ {A ε} → (τ : ℕ) → (St : 𝕊 [])
            → (M : toCtx St ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
            → (q : (of-natᵉ τ ·ₑ uₑ) ·ₑ ε ≾ₑ of-natᵉ τ ·ₑ ε)
            → ⟦ delay τ M ⟧ᶜᵗ ∘ᵐ ⟦ St ⟧ˢ
            ≈ᵐ T-≤ q ∘ᵐ ((⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ St ⟨ of-natʳ τ ⟩ₛ ⟧ˢ)
                          ⋄ (delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣))
sound-DELAY {ε = ε} τ St M q =
  lhs≈ ∙ ≈ᵐ-sym (∘ᵐ-congʳ rhs≈ ∙ cancel)
  where
    g : ⟨ of-natʳ τ ⟩ᵒ ⟦ hist St ⟧ᶜᵗˣ →ᵐ Tᵒ _ ε
    g = ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ St ⟨ of-natʳ τ ⟩ₛ ⟧ˢ

    -- the common normal form: delay the whole configuration
    nf : ⟦ hist St ⟧ᶜᵗˣ →ᵐ Tᵒ _ (of-natᵉ τ ·ₑ ε)
    nf = delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ g ∘ᵐ η⊣

    -- the source: `η⊣`-naturality absorbs the state into the boxed body
    lhs≈ : ⟦ delay τ M ⟧ᶜᵗ ∘ᵐ ⟦ St ⟧ˢ ≈ᵐ nf
    lhs≈ =
      ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat ⟦ St ⟧ˢ)))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))

    d : ε ≡ uₑ ·ₑ ε
    d = sym (·ₑ-identityˡ ε)

    c : (of-natᵉ τ ·ₑ uₑ) ·ₑ ε ≡ of-natᵉ τ ·ₑ (uₑ ·ₑ ε)
    c = ·ₑ-assoc (of-natᵉ τ) uₑ ε

    -- the target: `delayᵀ` is natural, then algebraic; the leftover unit
    -- laws are pure transports
    rhs≈ : (g ⋄ (delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣))
         ≈ᵐ ε-substᵀ (sym c) ∘ᵐ ε-substᵀ (cong (of-natᵉ τ ·ₑ_) d) ∘ᵐ nf
    rhs≈ =
      -- pull `Tᶠ g` through the delay (delayᵀ is natural)
        ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (delayᵀ-nat τ g)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym (ηᵀ-nat g)))))
      -- `μᵀ ∘ᵐ delayᵀ` is algebraic: the delay floats out of the bind
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (delayᵀ-algebraicity τ)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
      -- the remaining `μᵀ ∘ᵐ ηᵀ` is a unit law, hence a pure transport
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ
          (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ T-μ∘η≡id))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-∘ᵐ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (delayᵀ-ε-substᵀ τ d))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)

    cancel : T-≤ q ∘ᵐ (ε-substᵀ (sym c) ∘ᵐ ε-substᵀ (cong (of-natᵉ τ ·ₑ_) d) ∘ᵐ nf)
           ≈ᵐ nf
    cancel =
      ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (ε-substᵀ-trans _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (coe-cancel _ q)
      ∙ ∘ᵐ-identityˡ _

-- Box-grade relaxation is irrelevant in its witness.

[]-≤-irr : ∀ {A ρ₁ ρ₂} → (p q : ρ₁ ≾ᵣ ρ₂) → []-≤ {A} p ≈ᵐ []-≤ {A} q
[]-≤-irr {A} p q =
  subst (λ z → []-≤ {A} p ≈ᵐ []-≤ {A} z) (≾ᵣ-irrelevant p q) ≈ᵐ-refl

-- The environment a `return` hands to its continuation.
--
-- `strᵀ-ηᵀ` opens the boxed environment with the box counit at the unit
-- grade; the syntax instead re-locks the context with `⟨⟩-η-ren`. The two
-- agree: at the unit grade the adjunction unit *is* the possibility unit
-- (`η⊣-u`), and the counit cancels it. The grade equality `mapᵉ uₑ ≡ uᵣ` is
-- generalised so that it can be matched.

ret-env : ∀ {Γ ρ} → (e : ρ ≡ uᵣ)
        → εᵇ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym e)) ∘ᵐ η⊣ {⟦ Γ ⟧ᶜᵗˣ} {ρ}
        ≈ᵐ ⟦ eq-ren (cong (Γ ⟨_⟩) e) ⟧ʳ ∘ᵐ η
ret-env refl =
    ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-trans ([]-≤-irr _ ≾ᵣ-refl) []-≤-refl))
  ∙ ∘ᵐ-congʳ (∘ᵐ-identityˡ _)
  ∙ ∘ᵐ-congʳ η⊣-u
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-ε-nat η))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ []-ε∘ηᵘ≡id
  ∙ ∘ᵐ-identityʳ _
  ∙ ≈ᵐ-sym (∘ᵐ-identityˡ _)

-- Substituting into a renamed continuation: the renaming lands in the
-- environment's first component, the substituted value in its second.

sub-ren : ∀ {Γ Γ' A C} → (r : Ren Γ Γ') → (N : Γ ∷ A ⊢C⦂ C) → (V : Γ' ⊢V⦂ A)
        → ⟦ C-rename (cong-∷-ren r) N [ Hd ↦ V ]c ⟧ᶜᵗ
        ≈ᵐ ⟦ N ⟧ᶜᵗ ∘ᵐ ⟨ ⟦ r ⟧ʳ , ⟦ V ⟧ᵛᵗ ⟩ᵐ
sub-ren r N V =
    C-subst-nat (C-rename (cong-∷-ren r) N) Hd V
  ∙ ∘ᵐ-congˡ (C-rename-nat (cong-∷-ren r) N)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)

-- THE `return` RULES
--
-- `⨟` and `handle` thread the environment through the strength in exactly the
-- same way, differing only in the algebra that collapses the two monad layers
-- (`μᵀ`, resp. the handler's `T-alg-of-handlerᵀ`). Both algebras compute on a
-- returned value the same way, so `SEQ-RET` and `HANDLE-RET` share one proof.

ret-step : ∀ {Γ A B ε}
         → (alg : Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε) uₑ →ᵐ Tᵒ ⟦ B ⟧ᵛ (uₑ ·ₑ ε))
         → (alg-η : alg ∘ᵐ ηᵀ ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε)))
         → (V : Γ ⊢V⦂ A)
         → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
         → alg ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ⟩ᵐ
         ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε))
            ∘ᵐ ⟦ C-rename (cong-∷-ren (⟨⟩-η-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-uᵉ))) N
                   [ Hd ↦ V ]c ⟧ᶜᵗ
ret-step {Γ} alg alg-η V N =
    ∘ᵐ-congʳ ret-massage
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ alg-η
  where
    -- the environment-threading part (independent of the algebra): the returned
    -- value's `ηᵀ` opens the boxed environment (`strᵀ-ηᵀ`), which is exactly the
    -- syntax's re-locking renaming (`ret-env`), leaving `ηᵀ ∘ (renamed subst)`.
    ret-massage : Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ⟩ᵐ
                ≈ᵐ ηᵀ ∘ᵐ ⟦ C-rename (cong-∷-ren (⟨⟩-η-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-uᵉ))) N
                            [ Hd ↦ V ]c ⟧ᶜᵗ
    ret-massage =
        ∘ᵐ-congʳ (∘ᵐ-congʳ
          (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ strᵀ-ηᵀ)
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
          (⟨ ∘ᵐ-assoc _ _ _ ∙ ret-env map-uᵉ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ηᵀ-nat ⟦ N ⟧ᶜᵗ))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (sub-ren (⟨⟩-η-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-uᵉ)) N V))

-- `ret-step`, threaded with an eternal parameter `P` supplied by `pv`. The
-- handler's algebra reads its clause-context off `P` (`= ⟦ Γ ᴱ ⟧`, via
-- `projᴱ Γ`); the `ηᵀ` law discards it (`sndᵐ`), so returning ignores `P`.
ret-step-P : ∀ {Γ A B ε P}
           → (pv : ⟦ Γ ⟧ᶜᵗˣ →ᵐ P)
           → (alg : P ×ᵐ Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε) uₑ →ᵐ Tᵒ ⟦ B ⟧ᵛ (uₑ ·ₑ ε))
           → (alg-η : alg ∘ᵐ mapˣᵐ idᵐ (ηᵀ {Tᵒ ⟦ B ⟧ᵛ ε})
                    ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε)) ∘ᵐ sndᵐ)
           → (V : Γ ⊢V⦂ A)
           → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
           → alg ∘ᵐ ⟨ pv , Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ⟩ᵐ ⟩ᵐ
           ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε))
              ∘ᵐ ⟦ C-rename (cong-∷-ren (⟨⟩-η-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-uᵉ))) N
                     [ Hd ↦ V ]c ⟧ᶜᵗ
ret-step-P {Γ} pv alg alg-η V N =
    ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ret-massage ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ alg-η
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
  where
    ret-massage : Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ⟩ᵐ
                ≈ᵐ ηᵀ ∘ᵐ ⟦ C-rename (cong-∷-ren (⟨⟩-η-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-uᵉ))) N
                            [ Hd ↦ V ]c ⟧ᶜᵗ
    ret-massage =
        ∘ᵐ-congʳ (∘ᵐ-congʳ
          (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ strᵀ-ηᵀ)
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
          (⟨ ∘ᵐ-assoc _ _ _ ∙ ret-env map-uᵉ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ηᵀ-nat ⟦ N ⟧ᶜᵗ))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (sub-ren (⟨⟩-η-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-uᵉ)) N V))

-- SEQ-RET and HANDLE-RET: the two instances of `ret-step`, one for the monad
-- multiplication and one for the handler's algebra.

sound-SEQ-RET : ∀ {Γ A B ε} → (V : Γ ⊢V⦂ A) → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
              → ⟦ return V ⨟ N ⟧ᶜᵗ
              ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε))
                 ∘ᵐ ⟦ C-rename (cong-∷-ren (⟨⟩-η-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-uᵉ))) N
                        [ Hd ↦ V ]c ⟧ᶜᵗ
sound-SEQ-RET V N = ret-step μᵀ T-μ∘η≡id V N

sound-HANDLE-RET : ∀ {Γ A B ε}
                 → (V : Γ ⊢V⦂ A)
                 → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
                      → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                           ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                        ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                 → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
                 → ⟦ handle return V `with H `in N ⟧ᶜᵗ
                 ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε))
                    ∘ᵐ ⟦ C-rename (cong-∷-ren (⟨⟩-η-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-uᵉ))) N
                           [ Hd ↦ V ]c ⟧ᶜᵗ
sound-HANDLE-RET {Γ} V H N =
  ret-step-P (projᴱ Γ) (T-alg-of-handlerᵀ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H))
             (T-alg-of-handlerᵀ-ηᵀ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H)) V N

-- UNBOX = LOOKUP
--
-- A cell `x` of the store was allocated by some prefix of the state, namely
-- `split-state-fst St x`, and the value it holds lives in *that* prefix's
-- context, locked by the cell's own resource `ρ`. Reading the cell therefore
-- has to reach back to the world where it was allocated. `state-past` is that
-- reach-back: the past-view, at the cell's accumulated grade `ρ'`, of the
-- sub-state that allocated it.

state-past : ∀ {A ρ ρ'} → (St : 𝕊 []) → (x : [ ρ ] A ∈[ ρ' ] toCtx St)
           → ⟦ hist St ⟧ᶜᵗˣ →ᵐ ⟨ ρ' ⟩ᵒ ⟦ toCtx (split-state-fst St x) ⟧ᶜᵗˣ
state-past (St ⟨ σ ⟩ₛ) (Tl-⟨⟩ y) = μ ∘ᵐ ⟨ σ ⟩ᶠ (state-past St y)
state-past (St ∷ₛ W)   Hd        = η ∘ᵐ ⟦ St ⟧ˢ
state-past (St ∷ₛ W)   (Tl-∷ y)  = state-past St y

-- Projecting a cell out of the state's environment recovers exactly the value
-- stored in it — boxed by `η⊣` (the `box` morphism, which is what put it
-- there) and viewed from the past in which it was allocated.
--
-- Each case is a naturality law of the modality against the corresponding
-- clause of `⟦_⟧ˢ`: `Hd` is `η`'s naturality against the cell just written,
-- `Tl-∷` drops a later cell by `fstᵐ`, and `Tl-⟨⟩` folds a lock with `μ`'s
-- naturality — the grades multiplying exactly as `ctx-grade` says they must.

state-lookup : ∀ {A ρ ρ'} → (St : 𝕊 []) → (x : [ ρ ] A ∈[ ρ' ] toCtx St)
             → var-proj x ∘ᵐ ⟦ St ⟧ˢ
             ≈ᵐ ⟨ ρ' ⟩ᶠ ([ ρ ]ᶠ (⟦ resource-lookup St x ⟧ᵛᵗ
                                   ∘ᵐ ⟦ eq-ren (++ᶜ-identityˡ
                                        {toCtx (split-state-fst St x) ⟨ ρ ⟩}) ⟧ʳ)
                                 ∘ᵐ η⊣)
                ∘ᵐ state-past St x

state-lookup (St ∷ₛ W) Hd =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-η-nat _))
  ∙ ∘ᵐ-assoc _ _ _

state-lookup (St ∷ₛ W) (Tl-∷ y) =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-identityˡ _)
  ∙ state-lookup St y

state-lookup (St ⟨ σ ⟩ₛ) (Tl-⟨⟩ y) =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
  ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ (state-lookup St y))
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
          → (p : ρ' ≾ᵣ ctx-grade (([] ∷ [ ρ ] A) ++ᶜ toCtx (split-state-snd St x)))
          → ⟦ wk-ren-⟨ρ⟩-ctx {toCtx (split-state-fst St x)}
                             {([] ∷ [ ρ ] A) ++ᶜ toCtx (split-state-snd St x)} refl ⟧ʳ
              ∘ᵐ ⟦ eq-ren (sym (++ᶜ-assoc (toCtx (split-state-fst St x)) ([] ∷ [ ρ ] A)
                                          (toCtx (split-state-snd St x)))) ⟧ʳ
              ∘ᵐ ⟦ eq-ren (split-state-++ᶜ St x) ⟧ʳ
              ∘ᵐ ⟦ St ⟧ˢ
            ≈ᵐ ⟨⟩-≤ p ∘ᵐ state-past St x

-- the cell was just allocated: drop it with `fstᵐ`, and the reach-back is `η`
past-core (St ∷ₛ W) Hd p =
    ∘ᵐ-congʳ (∘ᵐ-identityˡ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-identityˡ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-identityˡ _)
  ∙ ≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩-≤-irr p ≾ᵣ-refl ∙ ⟨⟩-≤-refl) ∙ ∘ᵐ-identityˡ _)

-- a later cell: it sits in the first component of every transport, so `fstᵐ`
-- pushes straight through to the sub-state
past-core {A} {ρ} (_∷ₛ_ {B} {σ} St W) (Tl-∷ y) p =
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
  ∙ past-core St y p
  where
    assoc = ++ᶜ-assoc (toCtx (split-state-fst St y)) ([] ∷ [ ρ ] A)
                      (toCtx (split-state-snd St y))

-- a lock: fold it with `μ`, the grades multiplying on both sides
past-core {A} {ρ} (St ⟨ σ ⟩ₛ) (Tl-⟨⟩ y) p =
    ∘ᵐ-congʳ (∘ᵐ-congˡ
      (≡→≈ᵐ (cong (λ z → ⟦ eq-ren z ⟧ʳ) (sym-cong {f = _⟨ σ ⟩} assoc))
       ∙ eq-ren-⟨⟩ (sym assoc)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (eq-ren-⟨⟩ (split-state-++ᶜ St y))))
  -- everything under the lock is a `⟨ σ ⟩`-image: collect it
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
  ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ (past-core St y p₀))
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

unbox-lookup-sound : ∀ {A ρ Δ} → (St : 𝕊 [])
                   → (w : Ren (Δ ⟨ ρ ⟩) (toCtx St)) → (V : Δ ⊢V⦂ [ ρ ] A)
                   → ⟦ unbox-lookup St w V ⟧ᵛᵗ ∘ᵐ ⟦ St ⟧ˢ
                   ≈ᵐ (ε⊣ ∘ᵐ ⟨⟩-≤ (proj₂ (proj₂ (unbox⇒var w V)))
                          ∘ᵐ var-proj (proj₁ (proj₂ (unbox⇒var w V))))
                      ∘ᵐ ⟦ St ⟧ˢ
unbox-lookup-sound {A} {ρ} St w V with grad-typ⇒var V
... | _ , y , f , refl with var-rename w (Tl-⟨⟩ y)
... | ρ' , bound , x =
    -- the stored value, reindexed by `unbox-lookup`'s renaming composite
    -- (which `∘ʳ` leaves left-nested, so re-associate it first)
      ∘ᵐ-congˡ (V-rename-nat _ (resource-lookup St x))
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
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (past-core St x p₀))))
    -- the two grade coercions cancel
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
        (⟨⟩-≤-trans _ _ ∙ ⟨⟩-≤-irr _ ≾ᵣ-refl ∙ ⟨⟩-≤-refl))))
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _)))
    ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙ ≈ᵐ-sym rhs
  where
    rel : ρ' ≾ᵣ ρ
    rel = ≾ᵣ-trans bound
            (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (f (λ ()))) (≾ᵣ-reflexive (·ᵣ-identityˡ ρ)))

    p₀ = ≾ᵣ-reflexive (sym (cell-grade St x))

    g = ⟦ resource-lookup St x ⟧ᵛᵗ
          ∘ᵐ ⟦ eq-ren (++ᶜ-identityˡ
                 {toCtx (split-state-fst St x) ⟨ ρ ⟩}) ⟧ʳ

    rhs : (ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj x) ∘ᵐ ⟦ St ⟧ˢ
        ≈ᵐ g ∘ᵐ ⟨⟩-≤ rel ∘ᵐ state-past St x
    rhs =
      -- read the cell out of the environment
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (state-lookup St x))
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

unbox-def : ∀ {Γ A C ρ Δ} → (w : Ren (Δ ⟨ ρ ⟩) Γ) → (V : Δ ⊢V⦂ [ ρ ] A)
          → (M : Γ ∷ A ⊢C⦂ C)
          → ⟦ unbox w V M ⟧ᶜᵗ
          ≈ᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨⟩-≤ (proj₂ (proj₂ (unbox⇒var w V)))
                                   ∘ᵐ var-proj (proj₁ (proj₂ (unbox⇒var w V))) ⟩ᵐ
unbox-def w V M with unbox⇒var w V
... | _ , _ , _ = ≈ᵐ-refl

-- UNBOX: substituting the looked-up resource is reading the cell.

sound-UNBOX : ∀ {A C ρ Δ} → (St : 𝕊 []) → (w : Ren (Δ ⟨ ρ ⟩) (toCtx St))
            → (V : Δ ⊢V⦂ [ ρ ] A) → (M : toCtx St ∷ A ⊢C⦂ C)
            → ⟦ unbox w V M ⟧ᶜᵗ ∘ᵐ ⟦ St ⟧ˢ
            ≈ᵐ ⟦ M [ Hd ↦ unbox-lookup St w V ]c ⟧ᶜᵗ ∘ᵐ ⟦ St ⟧ˢ
sound-UNBOX St w V M =
    ∘ᵐ-congˡ (unbox-def w V M)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ≈ᵐ-sym (unbox-lookup-sound St w V) ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (C-subst-nat M Hd (unbox-lookup St w V)))

-- Transport along an equality of *grades* is the grade relaxation at the
-- reflexive witness.

eq-ren-grade : ∀ {Γ ρ ρ'} → (g : ρ ≡ ρ')
             → ⟦ eq-ren (cong (Γ ⟨_⟩) g) ⟧ʳ ≈ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᶜᵗˣ} (≾ᵣ-reflexive (sym g))
eq-ren-grade refl = ≈ᵐ-sym (⟨⟩-≤-irr _ ≾ᵣ-refl ∙ ⟨⟩-≤-refl)

-- SPLITTING THE ENVIRONMENT BOX
--
-- A box available `ρ₁`-far ahead, where `ρ₁ ⊒ σ ·ᵣ ρ₃`, can be transposed in
-- two stages: once at `σ` and once at `ρ₃`, the two pasts being folded back
-- together by `μ`. This is `η⊣-δ` packaged with the grade relaxation, and it
-- is the single move that carries an environment across a computation split
-- into two graded phases — which is the shape `strᵀ-μᵀ` forces.

box-split : ∀ {X σ ρ₁ ρ₃} → (a : σ ·ᵣ ρ₃ ≾ᵣ ρ₁)
          → δ ∘ᵐ []-≤ a ∘ᵐ η⊣ {X} {ρ₁}
          ≈ᵐ [ σ ]ᶠ ([ ρ₃ ]ᶠ (⟨⟩-≤ a ∘ᵐ μ) ∘ᵐ η⊣ {⟨ σ ⟩ᵒ X} {ρ₃}) ∘ᵐ η⊣ {X} {σ}
box-split a =
    ∘ᵐ-congʳ (η⊣-≤ a)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-δ-nat (⟨⟩-≤ a)))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ η⊣-δ
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
  ∙ ∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                        ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))

-- `box-split` with an environment postcomposed. The environment is pulled out
-- to the right, the split applied, and `η⊣`-naturality then carries it back
-- under the box — so the transposition ends up at the *environment's* source.
-- This is what lets `DELAY`'s strength components share one `η⊣`.

box-split-env : ∀ {X Y σ ρ₁ ρ₃} → (a : σ ·ᵣ ρ₃ ≾ᵣ ρ₁) → (env : Y →ᵐ X)
              → (δ ∘ᵐ []-≤ a) ∘ᵐ (η⊣ {X} {ρ₁} ∘ᵐ env)
              ≈ᵐ [ σ ]ᶠ (([ ρ₃ ]ᶠ (⟨⟩-≤ a ∘ᵐ μ) ∘ᵐ η⊣ {⟨ σ ⟩ᵒ X} {ρ₃}) ∘ᵐ ⟨ σ ⟩ᶠ env)
                  ∘ᵐ η⊣ {Y} {σ}
box-split-env {ρ₁ = ρ₁} a env =
    ≈ᵐ-sym (∘ᵐ-assoc (δ ∘ᵐ []-≤ a) (η⊣ {_} {ρ₁}) env)
  ∙ ∘ᵐ-congˡ (∘ᵐ-assoc δ ([]-≤ a) (η⊣ {_} {ρ₁}) ∙ box-split a)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat env))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))

-- Pushing an outer box-split through one that has already happened.
--
-- `DELAY` produces a *double* `δ` stack — one `δ` from `step-box`'s own
-- statement, one from `strᵀ-delayᵀ-algebraicity` — and a single split peels
-- only one layer. This pushes the outer layer through (`[]-≤-nat`, then
-- `[]-δ-nat`), exposing a bare `δ ∘ᵐ []-≤ ∘ᵐ η⊣` on which `box-split` fires
-- again. The transposition then sits at `ρ₁` — the tick's own grade — which is
-- what lets `η⊣-⟨⟩` reassemble the strength's two components.

box-push : ∀ {Y Z ρ₁ ρ₂ ρ'} → (e : ρ₁ ·ᵣ ρ₂ ≾ᵣ ρ')
         → (h : ⟨ ρ' ⟩ᵒ Y →ᵐ Z)
         → (δ {Z} {ρ₁} {ρ₂} ∘ᵐ []-≤ e) ∘ᵐ ([ ρ' ]ᶠ h ∘ᵐ η⊣ {Y} {ρ'})
         ≈ᵐ [ ρ₁ ]ᶠ ([ ρ₂ ]ᶠ h
                      ∘ᵐ ([ ρ₂ ]ᶠ (⟨⟩-≤ e ∘ᵐ μ) ∘ᵐ η⊣ {⟨ ρ₁ ⟩ᵒ Y} {ρ₂}))
              ∘ᵐ η⊣ {Y} {ρ₁}
box-push {ρ' = ρ'} e h =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  -- commute the relaxation past the already-split box
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-≤-nat h e)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  -- and commute `δ` past it too
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-δ-nat h))
  ∙ ∘ᵐ-assoc _ _ _
  -- what is left is a bare split
  ∙ ∘ᵐ-congʳ (box-split e)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))

-- Discharging a unit-graded box: at grade `u` the box counit turns a
-- transposition into the possibility unit. (The object-general form of
-- `ret-env`.)

εᵇ-η⊣ : ∀ {X ρ} → (e : ρ ≡ uᵣ)
      → εᵇ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym e)) ∘ᵐ η⊣ {X} {ρ}
      ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym e)) ∘ᵐ η
εᵇ-η⊣ refl =
    ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-≤-irr _ ≾ᵣ-refl ∙ []-≤-refl))
  ∙ ∘ᵐ-congʳ (∘ᵐ-identityˡ _)
  ∙ ∘ᵐ-congʳ η⊣-u
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-ε-nat η))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ []-ε∘ηᵘ≡id
  ∙ ∘ᵐ-identityʳ _
  ∙ ≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩-≤-irr _ ≾ᵣ-refl ∙ ⟨⟩-≤-refl) ∙ ∘ᵐ-identityˡ _)

-- Opening a unit-graded box around an arbitrary map.
--
-- At a grade that *is* the unit (`e : ρ ≡ uᵣ`), the box counit discharges the
-- transposition entirely: what is left is the possibility unit, relaxed to the
-- grade. This is `εᵇ-η⊣` with a map `H` carried through — `[]-≤-nat` and
-- `[]-ε-nat` commute the counit and the relaxation past `[ ρ ]ᶠ H`.

box-open : ∀ {X Z ρ} → (e : ρ ≡ uᵣ) → (H : ⟨ ρ ⟩ᵒ X →ᵐ Z)
         → (εᵇ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym e))) ∘ᵐ [ ρ ]ᶠ H ∘ᵐ η⊣ {X} {ρ}
         ≈ᵐ H ∘ᵐ (⟨⟩-≤ (≾ᵣ-reflexive (sym e)) ∘ᵐ η)
box-open e H =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-≤-nat H (≾ᵣ-reflexive (sym e)))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-ε-nat H))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (εᵇ-η⊣ e)

-- Pairing two transposes is transposing the pair (the derived form of
-- `η⊣-monoidal` that `delayᵀ`'s strength law needs).

η⊣-⟨⟩ : ∀ {X Y Z ρ} → (f : ⟨ ρ ⟩ᵒ X →ᵐ Y) → (g : ⟨ ρ ⟩ᵒ X →ᵐ Z)
      → []-monoidal ∘ᵐ ⟨ [ ρ ]ᶠ f ∘ᵐ η⊣ , [ ρ ]ᶠ g ∘ᵐ η⊣ ⟩ᵐ
      ≈ᵐ [ ρ ]ᶠ ⟨ f , g ⟩ᵐ ∘ᵐ η⊣ {X} {ρ}
η⊣-⟨⟩ f g =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-monoidal-nat f g))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ η⊣-monoidal
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
  ∙ ∘ᵐ-congˡ ([]-congᶠ (mapˣᵐ-∘⟨⟩ _ _ _ _
                        ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))

-- CARRYING THE ENVIRONMENT BOX ACROSS A TRIVIAL TRANSITION
--
-- The nine rules that do not advance time transition by `ηᵀ`. For them the
-- environment box must survive unchanged. `strᵀ-ηᵀ` opens it with the box
-- counit at the unit grade; what has to be shown is that opening it there
-- gives the environment back boxed at the *continuation's* grade `ρ₃` — i.e.
-- that it was carried, not lost. `box-split` is what puts back together what
-- `strᵀ-μᵀ` split with `δ`.

box-η : ∀ {X ρ₁ ρ₃} → (a : mapᵉ uₑ ·ᵣ ρ₃ ≾ᵣ ρ₁) → (w : ρ₃ ≾ᵣ ρ₁)
      → εᵇ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym map-uᵉ)) ∘ᵐ δ ∘ᵐ []-≤ a ∘ᵐ η⊣ {X} {ρ₁}
      ≈ᵐ [ ρ₃ ]ᶠ (⟨⟩-≤ w) ∘ᵐ η⊣ {X} {ρ₃}
box-η {X} {ρ₁} {ρ₃} a w =
    ∘ᵐ-congʳ (∘ᵐ-congʳ (box-split a))
  -- the outer box is at the unit grade, so the counit discharges it
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-≤-nat _ (≾ᵣ-reflexive (sym map-uᵉ)))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-ε-nat _))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (εᵇ-η⊣ map-uᵉ)
  -- and the inner box reassembles, the grade relaxations collapsing
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
  ∙ ∘ᵐ-congˡ ([]-congᶠ collapse)
  where
    collapse : (⟨⟩-≤ a ∘ᵐ μ {X} {ρ₃} {mapᵉ uₑ})
                 ∘ᵐ ⟨ ρ₃ ⟩ᶠ (⟨⟩-≤ (≾ᵣ-reflexive (sym map-uᵉ)) ∘ᵐ η)
             ≈ᵐ ⟨⟩-≤ w
    collapse =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μ-≤ˡ (≾ᵣ-reflexive (sym map-uᵉ)))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ ⟨⟩-μ∘Tη≡id)
      ∙ ∘ᵐ-congʳ (⟨⟩-≤-trans _ _)
      ∙ ⟨⟩-≤-trans _ _
      ∙ ⟨⟩-≤-irr _ w

-- Interpreting an effect-grade coercion is the transport `ε-substᵀ`.

sound-ε-subst : ∀ {Γ A ε ε'} → (e : ε ≡ ε') → (M : Γ ⊢C⦂ A ‼ ε)
              → ⟦ ε-subst e M ⟧ᶜᵗ ≈ᵐ ε-substᵀ e ∘ᵐ ⟦ M ⟧ᶜᵗ
sound-ε-subst refl M = ≈ᵐ-sym (∘ᵐ-congˡ ε-substᵀ-refl ∙ ∘ᵐ-identityˡ _)

-- SEQ-STEP and HANDLE-STEP
--
-- Both step rules have the shape `alg ∘ Tᶠ⟦N⟧ ∘ strᵀ ∘ ⟨ η⊣ , ⟦M⟧ ⟩ᵐ`,
-- differing only in the algebra (`μᵀ` resp. the handler's). The proof pushes
-- the inductive hypothesis' coercion out through the strength and multiplies,
-- bottoming out in `step-box`: the environment carried across the step is the
-- new state's environment, renamed by `suc-comp-ren`.

-- Naturality of the strength in its monadic (tree) component alone — the
-- dual of `strᵀ-natˡ`. Derived from `strᵀ-nat` and `[]-idᵐ`.

strᵀ-natʳ : ∀ {A B B' ε} → (g : B →ᵐ B')
          → strᵀ {A} {B'} {ε} ∘ᵐ mapˣᵐ idᵐ (Tᶠ g)
          ≈ᵐ Tᶠ (mapˣᵐ idᵐ g) ∘ᵐ strᵀ {A} {B} {ε}
strᵀ-natʳ g =
    ∘ᵐ-congʳ (⟨ ∘ᵐ-congˡ (≈ᵐ-sym []-idᵐ) , ≈ᵐ-refl ⟩ᵐ-cong)
  ∙ strᵀ-nat idᵐ g

-- Pushing an environment reindexing into a sequencing/handling composite.
-- Stated generically (over objects) so the associativity metas are pinned.

seq-push : ∀ {Γ Δ A B ε₁ ε₂}
         → (alg : Tᵒ (Tᵒ B ε₂) ε₁ →ᵐ Tᵒ B (ε₁ ·ₑ ε₂))
         → (n : ⟨ mapᵉ ε₁ ⟩ᵒ Γ ×ᵐ A →ᵐ Tᵒ B ε₂) → (m : Γ →ᵐ Tᵒ A ε₁)
         → (env : Δ →ᵐ Γ)
         → (alg ∘ᵐ Tᶠ n ∘ᵐ strᵀ {⟨ mapᵉ ε₁ ⟩ᵒ Γ} {A} {ε₁} ∘ᵐ ⟨ η⊣ , m ⟩ᵐ) ∘ᵐ env
         ≈ᵐ alg ∘ᵐ Tᶠ n ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ ∘ᵐ env , m ∘ᵐ env ⟩ᵐ
seq-push alg n m env =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)))

-- Pulling the IH coercion `T-≤ p` out to the front of a sequencing composite.
-- `strᵀ-≤` moves it past the strength (relaxing the box's grade), then
-- `T-≤-nat` and `T-≤-μᵀ` bubble it up past `Tᶠ n` and `μᵀ`.

coe-out : ∀ {Γ Δ A B ε₀ ε₁ ε₂}
        → (alg : ∀ {ε} → Tᵒ (Tᵒ B ε₂) ε →ᵐ Tᵒ B (ε ·ₑ ε₂))
        → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
                 → alg {εb} ∘ᵐ T-≤ q ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
        → (bx : Δ →ᵐ [ mapᵉ ε₁ ]ᵒ (⟨ mapᵉ ε₁ ⟩ᵒ Γ))
        → (n : ⟨ mapᵉ ε₁ ⟩ᵒ Γ ×ᵐ A →ᵐ Tᵒ B ε₂)
        → (W : Δ →ᵐ Tᵒ A ε₀) → (p : ε₀ ≾ₑ ε₁)
        → alg {ε₁} ∘ᵐ Tᶠ n ∘ᵐ strᵀ {⟨ mapᵉ ε₁ ⟩ᵒ Γ} {A} {ε₁} ∘ᵐ ⟨ bx , T-≤ p ∘ᵐ W ⟩ᵐ
        ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ p)
            ∘ᵐ alg {ε₀} ∘ᵐ Tᶠ n ∘ᵐ strᵀ {⟨ mapᵉ ε₁ ⟩ᵒ Γ} {A} {ε₀}
            ∘ᵐ ⟨ []-≤ (map-monotoneᵉ p) ∘ᵐ bx , W ⟩ᵐ
coe-out alg alg-≤ bx n W p =
    ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ (T-≤ p) bx W
                 ∙ ⟨ ∘ᵐ-identityˡ bx , ≈ᵐ-refl ⟩ᵐ-cong))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-≤ p)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
                                            ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-nat _ p))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (alg-≤ p)
  ∙ ∘ᵐ-assoc _ _ _

-- Splitting the strength across a bind, via `strᵀ-μᵀ` and `strᵀ-nat`.

str-split : ∀ {Γ Δ Δ' A d ε₁ ε₃}
          → (box₂ : Δ →ᵐ [ mapᵉ (d ·ₑ ε₃) ]ᵒ (⟨ mapᵉ ε₁ ⟩ᵒ Γ))
          → (g' : Δ' →ᵐ Tᵒ A ε₃) → (t : Δ →ᵐ Tᵒ Δ' d)
          → strᵀ {⟨ mapᵉ ε₁ ⟩ᵒ Γ} {A} {d ·ₑ ε₃} ∘ᵐ ⟨ box₂ , μᵀ ∘ᵐ Tᶠ g' ∘ᵐ t ⟩ᵐ
          ≈ᵐ μᵀ ∘ᵐ Tᶠ (strᵀ {⟨ mapᵉ ε₁ ⟩ᵒ Γ} {A} {ε₃}) ∘ᵐ Tᶠ (mapˣᵐ idᵐ g')
              ∘ᵐ strᵀ {[ mapᵉ ε₃ ]ᵒ (⟨ mapᵉ ε₁ ⟩ᵒ Γ)} {Δ'} {d}
              ∘ᵐ ⟨ (δ {⟨ mapᵉ ε₁ ⟩ᵒ Γ} {mapᵉ d} {mapᵉ ε₃}
                      ∘ᵐ []-≤ (≾ᵣ-reflexive (sym (map-·ᵉ {d} {ε₃})))) ∘ᵐ box₂ , t ⟩ᵐ
str-split {Γ = Γ} {d = d} {ε₁ = ε₁} {ε₃ = ε₃} box₂ g' t =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ μᵀ box₂ (Tᶠ g' ∘ᵐ t)
                      ∙ ⟨ ∘ᵐ-identityˡ box₂ , ≈ᵐ-refl ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-μᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
                                  ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ (Tᶠ g') _ t
               ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natʳ g')))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ≈ᵐ-refl


-- Pushing the inductive hypothesis' coercion out through the sequencing
-- composite, down to the `strᵀ ∘ ⟨ box , stepᵀ ⟩` core. Generic over objects
-- (so the metas are pinned by the explicit arguments); each step is one of
-- the strength/sub-effecting laws.

push-str : ∀ {Γ Δ Δ' A B d ε₁ ε₂ ε₃}
         → (alg : ∀ {ε} → Tᵒ (Tᵒ B ε₂) ε →ᵐ Tᵒ B (ε ·ₑ ε₂))
         → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
                  → alg {εb} ∘ᵐ T-≤ q ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
         → (bx : Δ →ᵐ [ mapᵉ ε₁ ]ᵒ (⟨ mapᵉ ε₁ ⟩ᵒ Γ))
         → (n : ⟨ mapᵉ ε₁ ⟩ᵒ Γ ×ᵐ A →ᵐ Tᵒ B ε₂)
         → (g' : Δ' →ᵐ Tᵒ A ε₃) → (t : Δ →ᵐ Tᵒ Δ' d)
         → (p : d ·ₑ ε₃ ≾ₑ ε₁)
         → alg {ε₁} ∘ᵐ Tᶠ n ∘ᵐ strᵀ {⟨ mapᵉ ε₁ ⟩ᵒ Γ} {A} {ε₁}
             ∘ᵐ ⟨ bx , T-≤ p ∘ᵐ μᵀ ∘ᵐ Tᶠ g' ∘ᵐ t ⟩ᵐ
         ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ p)
             ∘ᵐ alg {d ·ₑ ε₃} ∘ᵐ Tᶠ n ∘ᵐ μᵀ
             ∘ᵐ Tᶠ (strᵀ {⟨ mapᵉ ε₁ ⟩ᵒ Γ} {A} {ε₃})
             ∘ᵐ Tᶠ (mapˣᵐ idᵐ g')
             ∘ᵐ strᵀ {[ mapᵉ ε₃ ]ᵒ (⟨ mapᵉ ε₁ ⟩ᵒ Γ)} {Δ'} {d}
             ∘ᵐ ⟨ (δ {⟨ mapᵉ ε₁ ⟩ᵒ Γ} {mapᵉ d} {mapᵉ ε₃}
                     ∘ᵐ []-≤ (≾ᵣ-reflexive (sym (map-·ᵉ {d} {ε₃}))))
                    ∘ᵐ ([]-≤ (map-monotoneᵉ p) ∘ᵐ bx)
                , t ⟩ᵐ
push-str alg alg-≤ bx n g' t p =
    coe-out alg alg-≤ bx n (μᵀ ∘ᵐ Tᶠ g' ∘ᵐ t) p
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (str-split ([]-≤ (map-monotoneᵉ p) ∘ᵐ bx) g' t)))

-- The two coercions a sequencing step produces — the re-association of the
-- effect grades, and the step's own refinement — merge into `step-≾`'s.

seq-coe : ∀ {X A d ε₁ ε₂ ε₃}
        → (p : d ·ₑ ε₃ ≾ₑ ε₁)
        → (q : d ·ₑ (ε₃ ·ₑ ε₂) ≾ₑ ε₁ ·ₑ ε₂)
        → (f : X →ᵐ Tᵒ A (d ·ₑ (ε₃ ·ₑ ε₂)))
        → T-≤ (·ₑ-monoˡ-≾ₑ p) ∘ᵐ ε-substᵀ (sym (·ₑ-assoc d ε₃ ε₂)) ∘ᵐ f
        ≈ᵐ T-≤ q ∘ᵐ f
seq-coe {d = d} {ε₂ = ε₂} {ε₃ = ε₃} p q f =
    ∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-≡ (sym (·ₑ-assoc d ε₃ ε₂))))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-≤-trans (≾ₑ-reflexive (sym (·ₑ-assoc d ε₃ ε₂)))
                        (·ₑ-monoˡ-≾ₑ p) q)

-- SEQ-STEP (scaffold: isolating the `step-box` residual).
--
-- Stated in `push-str`'s natural grade `(d ·ₑ ε₃) ·ₑ ε₂`; `seq-coe` re-associates
-- to the goal's `d ·ₑ (ε₃ ·ₑ ε₂)` afterwards.

seq-step-core : ∀ {ε₁ ε₂ ε₃ A B} {S S' : 𝕊 []}
  → (alg : ∀ {ε} → Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε ·ₑ ε₂))
  → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
           → alg {εb} ∘ᵐ T-≤ q ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
  → {M : toCtx S ⊢C⦂ A ‼ ε₁} → (N : toCtx S ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
  → {M' : toCtx S' ⊢C⦂ A ‼ ε₃}
  → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
  → (c : ≤ₛ-grade (step-extends-state r) ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ ε₁)
  → ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ S ⟧ˢ
    ≈ᵐ T-≤ (step-≾ r)
       ∘ᵐ _⋄_ {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {step-grade r} {ε₃}
              (⟦ M' ⟧ᶜᵗ ∘ᵐ ⟦ S' ⟧ˢ) (stepᵀ r)
  → (alg {ε₁} ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ) ∘ᵐ ⟦ S ⟧ˢ
    ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ (step-≾ r))
       ∘ᵐ alg {step-grade r ·ₑ ε₃} ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ μᵀ
       ∘ᵐ Tᶠ (strᵀ {⟨ mapᵉ ε₁ ⟩ᵒ ⟦ toCtx S ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {ε₃})
       ∘ᵐ Tᶠ (mapˣᵐ idᵐ (⟦ M' ⟧ᶜᵗ ∘ᵐ ⟦ S' ⟧ˢ))
       ∘ᵐ strᵀ {[ mapᵉ ε₃ ]ᵒ (⟨ mapᵉ ε₁ ⟩ᵒ ⟦ toCtx S ⟧ᶜᵗˣ)} {⟦ hist S' ⟧ᶜᵗˣ} {step-grade r}
       ∘ᵐ ⟨ (δ {⟨ mapᵉ ε₁ ⟩ᵒ ⟦ toCtx S ⟧ᶜᵗˣ} {mapᵉ (step-grade r)} {mapᵉ ε₃}
               ∘ᵐ []-≤ (≾ᵣ-reflexive (sym (map-·ᵉ {step-grade r} {ε₃}))))
              ∘ᵐ ([]-≤ (map-monotoneᵉ (step-≾ r)) ∘ᵐ (η⊣ ∘ᵐ ⟦ S ⟧ˢ))
          , stepᵀ r ⟩ᵐ
seq-step-core {ε₁} {ε₂} {ε₃} {A} {B} {S} {S'} alg alg-≤ {M} N {M'} r c ih =
    seq-push {⟦ toCtx S ⟧ᶜᵗˣ} {⟦ hist S ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {⟦ B ⟧ᵛ} {ε₁} {ε₂}
             (alg {ε₁}) ⟦ N ⟧ᶜᵗ ⟦ M ⟧ᶜᵗ ⟦ S ⟧ˢ
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (⟨_,_⟩ᵐ-cong {f = η⊣ ∘ᵐ ⟦ S ⟧ˢ} {f' = η⊣ ∘ᵐ ⟦ S ⟧ˢ}
                   {g = ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ S ⟧ˢ}
                   {g' = T-≤ (step-≾ r) ∘ᵐ (μᵀ ∘ᵐ Tᶠ (⟦ M' ⟧ᶜᵗ ∘ᵐ ⟦ S' ⟧ˢ) ∘ᵐ stepᵀ r)}
                   ≈ᵐ-refl ih)))
  ∙ push-str {⟦ toCtx S ⟧ᶜᵗˣ} {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {⟦ B ⟧ᵛ}
             {step-grade r} {ε₁} {ε₂} {ε₃}
             alg alg-≤
             (η⊣ ∘ᵐ ⟦ S ⟧ˢ) ⟦ N ⟧ᶜᵗ (⟦ M' ⟧ᶜᵗ ∘ᵐ ⟦ S' ⟧ˢ) (stepᵀ r) (step-≾ r)

-- THE `id-suc` BOX IDENTITY
--
-- This is the residual left by `strᵀ-ηᵀ` in the nine rules that neither
-- advance time nor allocate. The box arrives carrying *two* grade
-- relaxations — one re-associating `mapᵉ (d ·ₑ ε₃)`, one refining along the
-- step — which merge by `[]-≤-trans` into exactly `box-η`'s hypothesis. The
-- environment `env` rides along and is moved across by `η⊣`'s naturality.

box-core : ∀ {X ρ₂ ρ₄}
         → (a : mapᵉ uₑ ·ᵣ ρ₄ ≾ᵣ ρ₂) → (w : ρ₄ ≾ᵣ ρ₂)
         → (εᵇ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym map-uᵉ)))
             ∘ᵐ ((δ ∘ᵐ []-≤ a) ∘ᵐ η⊣ {X} {ρ₂})
         ≈ᵐ [ ρ₄ ]ᶠ (⟨⟩-≤ w) ∘ᵐ η⊣ {X} {ρ₄}
box-core a w =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc δ ([]-≤ a) η⊣))
  ∙ box-η a w

box-id-suc : ∀ {X Y ρ₂ ρ₄}
           → (a : mapᵉ uₑ ·ᵣ ρ₄ ≾ᵣ ρ₂) → (w : ρ₄ ≾ᵣ ρ₂)
           → (env : Y →ᵐ X)
           → (εᵇ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym map-uᵉ)))
               ∘ᵐ (δ ∘ᵐ []-≤ a) ∘ᵐ (η⊣ {X} {ρ₂} ∘ᵐ env)
           ≈ᵐ [ ρ₄ ]ᶠ (⟨⟩-≤ w ∘ᵐ ⟨ ρ₄ ⟩ᶠ env) ∘ᵐ η⊣ {Y} {ρ₄}
box-id-suc {ρ₂ = ρ₂} a w env =
    ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc (δ ∘ᵐ []-≤ a) (η⊣ {_} {ρ₂}) env))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc (εᵇ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym map-uᵉ)))
                     ((δ ∘ᵐ []-≤ a) ∘ᵐ η⊣ {_} {ρ₂}) env)
  ∙ ∘ᵐ-congˡ (box-core a w)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat env))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))

-- THE TICK'S CONTEXT-MODALITY IDENTITY
--
-- What `DELAY` finally reduces to, once every box has been discharged: a pure
-- statement about the context modality.

-- Folding the unit that the tick's transposition introduced. `μ` against `η`
-- is the graded monad's unit law, so the whole `⟨⟩-≤ ∘ μ ∘ ⟨⟩-≤ ∘ η` collapses
-- to a single grade relaxation (the order being proof-irrelevant).

past-η : ∀ {A ρ σ u'} → (pu : uᵣ ≾ᵣ u') → (e : ρ ·ᵣ u' ≾ᵣ σ) → (k : ρ ≾ᵣ σ)
       → (⟨⟩-≤ e ∘ᵐ μ {A} {u'} {ρ}) ∘ᵐ (⟨⟩-≤ pu ∘ᵐ η)
       ≈ᵐ ⟨⟩-≤ k
past-η pu e k =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μ-≤ʳ pu)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ ⟨⟩-μ∘η≡id)
  ∙ ∘ᵐ-congʳ (⟨⟩-≤-trans _ _)
  ∙ ⟨⟩-≤-trans _ _
  ∙ ⟨⟩-≤-irr _ k

-- The environment commutes past that relaxation (`⟨⟩-≤-nat`) and `μ` absorbs it
-- (`μ-≤ˡ`), leaving the renaming `suc-comp-ren` builds for a `⟨⟩-suc`: the `μ`
-- folding the state's lock with the new tick.

past-tick : ∀ {A B ρ ρ₂ ρ₄ σ u'}
          → (pu : uᵣ ≾ᵣ u') → (e : ρ ·ᵣ u' ≾ᵣ σ) → (k : ρ ≾ᵣ σ)
          → (g : σ ·ᵣ ρ₄ ≾ᵣ ρ₂) → (w : ρ ·ᵣ ρ₄ ≾ᵣ ρ₂)
          → (E : A →ᵐ B)
          → (⟨⟩-≤ g ∘ᵐ μ {B} {ρ₄} {σ})
              ∘ᵐ ⟨ ρ₄ ⟩ᶠ (⟨ σ ⟩ᶠ E ∘ᵐ (⟨⟩-≤ e ∘ᵐ μ {A} {u'} {ρ}) ∘ᵐ (⟨⟩-≤ pu ∘ᵐ η))
          ≈ᵐ (⟨⟩-≤ w ∘ᵐ μ {B} {ρ₄} {ρ}) ∘ᵐ ⟨ ρ₄ ⟩ᶠ (⟨ ρ ⟩ᶠ E)
past-tick pu e k g w E =
    ∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-congʳ (past-η pu e k)))
  ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩-≤-nat E k))
  ∙ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μ-≤ˡ k)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (⟨⟩-≤-trans _ _ ∙ ⟨⟩-≤-irr _ w)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- The grade witness that `suc-comp-ren id-suc` carries.

wk-w : ∀ {ρ₂ ρ₄} → (c : uᵣ ·ᵣ ρ₄ ≾ᵣ ρ₂) → ρ₄ ≾ᵣ ρ₂
wk-w {ρ₄ = ρ₄} c = ≾ᵣ-trans (≾ᵣ-reflexive (sym (·ᵣ-identityˡ ρ₄))) c

-- The `∷-suc` cancellation: `suc-comp-ren` prefixes a `cong-⟨⟩-ren wk-ren`,
-- whose `fstᵐ` projects away exactly the cell that `⟦_⟧ˢ` just allocated. So
-- allocation leaves the *environment* untouched — which is why `BOX` threads
-- the box just like a time-preserving rule.

box-∷-suc : ∀ {X Y Z ρ₂ ρ₄} → (w w' : ρ₄ ≾ᵣ ρ₂)
          → (env : Y →ᵐ X) → (cell : X →ᵐ Z)
          → ⟨⟩-≤ w ∘ᵐ ⟨ ρ₄ ⟩ᶠ env
          ≈ᵐ (⟨⟩-≤ w' ∘ᵐ ⟨ ρ₄ ⟩ᶠ fstᵐ) ∘ᵐ ⟨ ρ₄ ⟩ᶠ (⟨ idᵐ , cell ⟩ᵐ ∘ᵐ env)
box-∷-suc w w' env cell =
    ∘ᵐ-congˡ (⟨⟩-≤-irr w w')
  ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym (≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                                ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
                                ∙ ∘ᵐ-identityˡ _)))
  ∙ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- THREADING THE ENVIRONMENT BOX ACROSS A STEP
--
-- The semantic content of "reduction only extends the state": the boxed
-- environment of the source state, carried along the step's time transition,
-- is the target state's boxed environment reindexed by the renaming
-- `suc-comp-ren` builds.
--
-- Generic in the two resource grades: a reduction's own effect grades only
-- instantiate them, and the recursive cases apply the lemma at the sub-step's
-- grades, not the enclosing sequencing's.

step-box : ∀ {ε₁ ε₃ A} {S S' : 𝕊 []} {ρ₂ ρ₄ : R}
         → {M : toCtx S ⊢C⦂ A ‼ ε₁} → {M' : toCtx S' ⊢C⦂ A ‼ ε₃}
         → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
         → (c : ≤ₛ-grade (step-extends-state r) ·ᵣ ρ₄ ≾ᵣ ρ₂)
         → (g : mapᵉ (step-grade r) ·ᵣ ρ₄ ≾ᵣ ρ₂)
         → strᵀ {[ ρ₄ ]ᵒ (⟨ ρ₂ ⟩ᵒ ⟦ toCtx S ⟧ᶜᵗˣ)} {⟦ hist S' ⟧ᶜᵗˣ} {step-grade r}
             ∘ᵐ ⟨ (δ {⟨ ρ₂ ⟩ᵒ ⟦ toCtx S ⟧ᶜᵗˣ} {mapᵉ (step-grade r)} {ρ₄} ∘ᵐ []-≤ g)
                    ∘ᵐ (η⊣ ∘ᵐ ⟦ S ⟧ˢ)
                , stepᵀ r ⟩ᵐ
           ≈ᵐ Tᶠ ⟨ [ ρ₄ ]ᶠ (⟦ suc-comp-ren (step-extends-state r) c ⟧ʳ
                             ∘ᵐ ⟨ ρ₄ ⟩ᶠ ⟦ S' ⟧ˢ)
                    ∘ᵐ η⊣
                 , idᵐ ⟩ᵐ
              ∘ᵐ stepᵀ r

-- The nine time-preserving rules: `strᵀ-ηᵀ` opens the box, and `box-id-suc`
-- is exactly what is left — the environment survives unchanged.

step-box APP c g =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-id-suc _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box MATCH c g =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-id-suc _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box SEQ-RET c g =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-id-suc _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box SEQ-OP c g =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-id-suc _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box HANDLE-RET c g =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-id-suc _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box HANDLE-OP c g =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-id-suc _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box UNBOX c g =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-id-suc _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

step-box COERCE c g =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-id-suc _ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

-- The recursive rules: `stepᵀ`, `step-extends-state`, and both states are all
-- inherited from the sub-step, so the statement is the sub-step's.

step-box (SEQ-STEP r c') c g = step-box r c g
step-box (HANDLE-STEP r c') c g = step-box r c g

-- BOX: allocation. `stepᵀ` is still `ηᵀ`; the `fstᵐ` that `suc-comp-ren`
-- contributes cancels exactly the cell just written.

step-box (BOX {ρ' = ρ'} {S = St} {V = V}) c g =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ box-id-suc _ (wk-w c) ⟦ St ⟧ˢ
                  ∙ ∘ᵐ-congˡ ([]-congᶠ (box-∷-suc (wk-w c) (wk-w c) ⟦ St ⟧ˢ
                                (  [ ρ' ]ᶠ (⟦ V-rename (eq-ren (sym ++ᶜ-identityˡ)) V ⟧ᵛᵗ
                                            ∘ᵐ ⟦ eq-ren (++ᶜ-identityˡ
                                                  {toCtx St ⟨ ρ' ⟩}) ⟧ʳ)
                                 ∘ᵐ η⊣)))
                , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ηᵀ-nat _

-- DELAY: the tick, the one rule that advances time.
--
-- `strᵀ-delayᵀ-algebraicity` routes the box through `[]-monoidal`, leaving a
-- double `δ` stack on the first component. `box-split-env` peels the inner
-- layer (carrying the environment under the box) and `box-push` pushes the
-- outer one through; both components then transpose at the tick's own grade,
-- so `η⊣-⟨⟩` reassembles them. Inside the resulting box the shape is again the
-- time-preserving one, and `delayᵀ-nat` pulls `Tᶠ` out to match `stepᵀ DELAY`.

step-box (DELAY {τ = τ} {S = St}) c g =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ (delayᵀ τ) _ ([ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣)
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (strᵀ-delayᵀ-algebraicity τ)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
                                  ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (⟨ ∘ᵐ-congʳ (box-split-env _ _) ∙ box-push _ _ , ≈ᵐ-refl ⟩ᵐ-cong)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (η⊣-⟨⟩ _ _))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (
        ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ idᵐ ηᵀ _ idᵐ
                          ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
                  ∙ ⟨   -- merge the two unit-graded boxes, then open them
                        ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
                      ∙ box-open map-uᵉ _
                      -- regroup so the `η⊣` inside can be pulled to the front
                      -- reassociate so the `η⊣` sits second from the left
                      ∙ ∘ᵐ-assoc _ _ _
                      ∙ ∘ᵐ-assoc _ _ _
                      ∙ ∘ᵐ-assoc _ _ _
                      -- pull `η⊣` to the front (its naturality), so both sides
                      -- are `[ ρ₄ ]ᶠ (…) ∘ᵐ η⊣`
                      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat _))
                      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
                      -- and what is left is the pure possibility identity
                      ∙ ∘ᵐ-congˡ ([]-congᶠ
                          (past-tick _ _
                            (≾ᵣ-trans (≾ᵣ-reflexive (sym (·ᵣ-identityʳ (of-natʳ τ))))
                              (≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ (≾ᵣ-reflexive (sym map-uᵉ)))
                                        (≾ᵣ-reflexive (sym (trans map-·ᵉ
                                          (cong (_·ᵣ mapᵉ uₑ) map-of-natᵉ))))))
                            g _ ⟦ St ⟧ˢ))
                    , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
      ∙ ηᵀ-nat _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-∘ᵐ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (delayᵀ-nat τ _)
  ∙ ∘ᵐ-assoc _ _ _

-- Re-associating two multiplications. `T-μ∘μ≡μ∘Tμ` runs the other way (it
-- *produces* the transport), so the inverse direction cancels a transport
-- against its own inverse — which is `refl` by uniqueness of identity proofs.

μμ : ∀ {A ε ε' ε''}
   → μᵀ {A} {ε ·ₑ ε'} {ε''} ∘ᵐ μᵀ {Tᵒ A ε''} {ε} {ε'}
   ≈ᵐ ε-substᵀ (sym (·ₑ-assoc ε ε' ε''))
       ∘ᵐ μᵀ {A} {ε} {ε' ·ₑ ε''} ∘ᵐ Tᶠ (μᵀ {A} {ε'} {ε''})
μμ {ε = ε} {ε' = ε'} {ε'' = ε''} =
  ≈ᵐ-sym
      (∘ᵐ-congʳ T-μ∘μ≡μ∘Tμ
    ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙ ∘ᵐ-congˡ (ε-substᵀ-trans _ _
                ∙ ≡→≈ᵐ (cong (λ z → ε-substᵀ z) uip)
                ∙ ε-substᵀ-refl)
    ∙ ∘ᵐ-identityˡ _)

-- SEQ-STEP
--
-- `seq-step-core` reduces the source to the `strᵀ ∘ ⟨ box , stepᵀ r ⟩` core;
-- `step-box` replaces that core by the *new* state's box, renamed by
-- `suc-comp-ren`; and `seq-coe` reconciles the effect grades (which differ by
-- an associativity, as `step-≾ (SEQ-STEP …)` already anticipates).

-- The box `seq-step-core` produces carries two grade relaxations, which merge
-- into the single one `step-box` expects.

seq-g : ∀ {ε₁ ε₃ A} {S S' : 𝕊 []}
      → {M : toCtx S ⊢C⦂ A ‼ ε₁} → {M' : toCtx S' ⊢C⦂ A ‼ ε₃}
      → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
      → mapᵉ (step-grade r) ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ ε₁
seq-g {ε₃ = ε₃} r =
  ≾ᵣ-trans (≾ᵣ-reflexive (sym (map-·ᵉ {step-grade r} {ε₃})))
           (map-monotoneᵉ (step-≾ r))

box-merge : ∀ {X Y Z ρ₁ ρ₂ ρ₃} → (p : ρ₁ ≾ᵣ ρ₂) → (q : ρ₂ ≾ᵣ ρ₃) → (m : ρ₁ ≾ᵣ ρ₃)
          → (d : [ ρ₁ ]ᵒ X →ᵐ Y) → (h : Z →ᵐ [ ρ₃ ]ᵒ X)
          → (d ∘ᵐ []-≤ p) ∘ᵐ ([]-≤ q ∘ᵐ h) ≈ᵐ (d ∘ᵐ []-≤ m) ∘ᵐ h
box-merge p q m d h =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-≤-trans p q ∙ []-≤-irr _ m))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- The target's denotation, unfolded to the same normal form. The renaming
-- `suc-comp-ren` sits in the continuation, and `strᵀ-natˡ` moves it into the
-- environment box — which is exactly the box `step-box` delivers.

-- The target's denotation, unfolded to the same normal form. Generic in the
-- algebra: `⨟` uses `μᵀ`, `handle` uses the handler's fold, and they thread the
-- environment through the strength in exactly the same way. The renaming
-- `suc-comp-ren` sits in the continuation, and `strᵀ-natˡ` moves it into the
-- environment box — which is exactly the box `step-box` delivers.

seq-target : ∀ {ε₁ ε₂ ε₃ A B} {Γ Γ' : Ctx} {H : Obj}
           → (alg : Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε₃ →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε₃ ·ₑ ε₂))
           → (N : Γ ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
           → (ρ : Ren (Γ ⟨ mapᵉ ε₁ ⟩) (Γ' ⟨ mapᵉ ε₃ ⟩))
           → (M' : Γ' ⊢C⦂ A ‼ ε₃)
           → (env : H →ᵐ ⟦ Γ' ⟧ᶜᵗˣ)
           → (alg ∘ᵐ Tᶠ ⟦ C-rename (cong-∷-ren ρ) N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M' ⟧ᶜᵗ ⟩ᵐ)
               ∘ᵐ env
           ≈ᵐ alg ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ
               ∘ᵐ strᵀ {⟨ mapᵉ ε₁ ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {ε₃}
               ∘ᵐ ⟨ [ mapᵉ ε₃ ]ᶠ (⟦ ρ ⟧ʳ ∘ᵐ ⟨ mapᵉ ε₃ ⟩ᶠ env) ∘ᵐ η⊣
                  , ⟦ M' ⟧ᶜᵗ ∘ᵐ env ⟩ᵐ
seq-target {ε₃ = ε₃} {A = A} {B = B} {Γ' = Γ'} alg N ρ M' env =
    seq-push {⟦ Γ' ⟧ᶜᵗˣ} {_} {⟦ A ⟧ᵛ} {⟦ B ⟧ᵛ} {ε₃} {_}
             alg ⟦ C-rename (cong-∷-ren ρ) N ⟧ᶜᵗ ⟦ M' ⟧ᶜᵗ env
  -- the renaming in the continuation …
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (C-rename-nat (cong-∷-ren ρ) N)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (T-∘ᵐ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  -- … moves into the environment box (`strᵀ-natˡ`)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
                                  ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  -- the environment moves under the box (`η⊣`-naturality), giving exactly the
  -- box that `step-box` delivers
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (⟨ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat env))
         ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
         ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
       , ≈ᵐ-refl ⟩ᵐ-cong)))

sound-SEQ-STEP : ∀ {ε₁ ε₂ ε₃ A B} {S S' : 𝕊 []}
  → {M : toCtx S ⊢C⦂ A ‼ ε₁} → (N : toCtx S ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
  → {M' : toCtx S' ⊢C⦂ A ‼ ε₃}
  → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
  → (c : ≤ₛ-grade (step-extends-state r) ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ ε₁)
  → ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ S ⟧ˢ
    ≈ᵐ T-≤ (step-≾ r)
       ∘ᵐ _⋄_ {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {step-grade r} {ε₃}
              (⟦ M' ⟧ᶜᵗ ∘ᵐ ⟦ S' ⟧ˢ) (stepᵀ r)
  → ⟦ M ⨟ N ⟧ᶜᵗ ∘ᵐ ⟦ S ⟧ˢ
    ≈ᵐ T-≤ (step-≾ (SEQ-STEP {N = N} r c))
       ∘ᵐ _⋄_ {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ B ⟧ᵛ} {step-grade r} {ε₃ ·ₑ ε₂}
              (⟦ M' ⨟ C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N ⟧ᶜᵗ
                 ∘ᵐ ⟦ S' ⟧ˢ)
              (stepᵀ r)
sound-SEQ-STEP {ε₁} {ε₂} {ε₃} {A} {B} {S} {S'} {M} N {M'} r c ih =
    seq-step-core μᵀ T-≤-μᵀ N r c ih
  -- merge the box's two relaxations into the one `step-box` expects
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (⟨ box-merge _ _ (seq-g r) _ _ , ≈ᵐ-refl ⟩ᵐ-cong)))))))
  -- and replace the core by the new state's box
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (step-box r c (seq-g r)))))))
  -- collect the functorial actions under one `Tᶠ`
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _))))))
  -- the inner term is now the target's normal form (`seq-target`)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
      (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))))))
  -- push `Tᶠ ⟦N⟧` past the inner `μᵀ` …
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μᵀ-nat _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  -- … and re-associate the two `μᵀ`s, which is where the `ε-substᵀ` appears
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ μμ)
  -- regroup: the transport floats to the front, and the rest collects under
  -- one `Tᶠ` — which is exactly `seq-target`'s normal form
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)))))
  -- drop the identity the strength's pairing picked up
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
      (∘ᵐ-congʳ ⟨ ≈ᵐ-refl , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))))))
  -- collect the last two functorial actions under one `Tᶠ`
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)))))
  -- what is under it is the target's denotation …
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
      (∘ᵐ-assoc _ _ _
       ∙ ≈ᵐ-sym (seq-target {ε₁} {ε₂} {ε₃} {A} {B}
                            {toCtx S} {toCtx S'} {⟦ hist S' ⟧ᶜᵗˣ}
                            μᵀ N (suc-comp-ren (step-extends-state r) c)
                            M' ⟦ S' ⟧ˢ))))))
  -- … and the `ε-substᵀ` that `μμ` exposed is exactly what `seq-coe` absorbs
  ∙ seq-coe (step-≾ r) (step-≾ (SEQ-STEP {N = N} r c)) _

-- THE HANDLER COMMUTES WITH A STEP TRANSITION
--
-- A reduction step never performs an operation: `stepᵀ r` is `ηᵀ` for every
-- rule but `DELAY`, where it is a tick. So handling the effects a step produces
-- gives the same result whether the handler sits inside the step or outside it,
-- which is what lets `HANDLE-STEP` move the transition out of the handler's
-- argument and into the `⋄` of the target configuration.
--
-- The equation holds only for step transitions: `alg ∘ᵐ μᵀ ≈ᵐ μᵀ ∘ᵐ Tᶠ alg` is
-- false for a general tree, whose outer layer's operations would be handled on
-- one side and merely flattened on the other.

-- The algebra commutes with a grade transport (derivable from `alg-≤`).

alg-ε-subst : ∀ {B ε₂ ε₁' ε₂'}
            → (alg : ∀ {ε} → Tᵒ (Tᵒ B ε₂) ε →ᵐ Tᵒ B (ε ·ₑ ε₂))
            → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
                     → alg {εb} ∘ᵐ T-≤ q ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
            → (e : ε₁' ≡ ε₂')
            → alg {ε₂'} ∘ᵐ ε-substᵀ e
            ≈ᵐ ε-substᵀ (cong (_·ₑ ε₂) e) ∘ᵐ alg {ε₁'}
alg-ε-subst alg alg-≤ e =
    ∘ᵐ-congʳ (T-≤-≡ e)
  ∙ alg-≤ (≾ₑ-reflexive e)
  ∙ ∘ᵐ-congˡ (T-≤-irr _ (≾ₑ-reflexive (cong (_·ₑ _) e)))
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (T-≤-≡ (cong (_·ₑ _) e)))

-- The `ηᵀ` case: a step that performs nothing. Both sides collapse by the
-- monad's left-unit law, and the algebra passes the returned value through
-- (`T-alg-of-handlerᵀ-ηᵀ`).

alg-ηᵀ : ∀ {B Y ε ε₂}
       → (alg : ∀ {ε'} → Tᵒ (Tᵒ B ε₂) ε' →ᵐ Tᵒ B (ε' ·ₑ ε₂))
       → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
                → alg {εb} ∘ᵐ T-≤ q ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
       → (alg-η : alg {uₑ} ∘ᵐ ηᵀ {Tᵒ B ε₂}
                ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε₂)))
       → (f : Y →ᵐ Tᵒ (Tᵒ B ε₂) ε)
       → alg {uₑ ·ₑ ε} ∘ᵐ μᵀ {Tᵒ B ε₂} {uₑ} {ε} ∘ᵐ Tᶠ f ∘ᵐ ηᵀ
       ≈ᵐ ε-substᵀ (sym (·ₑ-assoc uₑ ε ε₂))
           ∘ᵐ μᵀ {B} {uₑ} {ε ·ₑ ε₂} ∘ᵐ Tᶠ (alg {ε} ∘ᵐ f) ∘ᵐ ηᵀ
alg-ηᵀ {ε = ε} {ε₂ = ε₂} alg alg-≤ alg-η f =
  -- pull `ηᵀ` to the front, then the unit law collapses `μᵀ ∘ ηᵀ`
    ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (ηᵀ-nat f)))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ T-μ∘η≡id)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  -- the algebra passes the transport through
  ∙ ∘ᵐ-congˡ (alg-ε-subst alg alg-≤ (sym (·ₑ-identityˡ ε)))
  ∙ ∘ᵐ-assoc _ _ _
  -- and the two accumulated transports agree (`uip`), so the same chain
  -- rebuilds the right-hand side
  ∙ ∘ᵐ-congˡ (≡→≈ᵐ (cong (λ z → ε-substᵀ z) uip))
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ε-substᵀ-trans _ _))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym T-μ∘η≡id))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (ηᵀ-nat (alg ∘ᵐ f)))

-- The step transition commutes with the handler, by induction on the
-- reduction. Ten rules transition by `ηᵀ` (`alg-ηᵀ`); `DELAY` ticks, and the
-- fold *re-delays* (`T-alg-of-handlerᵀ-delayᵀ`), so the tick passes through;
-- the two step rules inherit their transition from the sub-step.

alg-stepᵀ : ∀ {ε ε₂ ε₁' ε₃' A B} {S S' : 𝕊 []}
          → {M : toCtx S ⊢C⦂ A ‼ ε₁'} → {M' : toCtx S' ⊢C⦂ A ‼ ε₃'}
          → (alg : ∀ {ε'} → Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε' →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε' ·ₑ ε₂))
          → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
                   → alg {εb} ∘ᵐ T-≤ q ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
          → (alg-η : alg {uₑ} ∘ᵐ ηᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂}
                   ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε₂)))
          → (alg-delay : ∀ {ε'} → (τ : ℕ)
                       → alg {of-natᵉ τ ·ₑ ε'} ∘ᵐ delayᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂} {ε'} τ
                       ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε₂))
                           ∘ᵐ delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ (alg {ε'}))
          → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
          → (f : ⟦ hist S' ⟧ᶜᵗˣ →ᵐ Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε)
          → alg {step-grade r ·ₑ ε} ∘ᵐ μᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂} {step-grade r} {ε}
              ∘ᵐ Tᶠ f ∘ᵐ stepᵀ r
          ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (step-grade r) ε ε₂))
              ∘ᵐ μᵀ {⟦ B ⟧ᵛ} {step-grade r} {ε ·ₑ ε₂}
              ∘ᵐ Tᶠ (alg {ε} ∘ᵐ f) ∘ᵐ stepᵀ r
alg-stepᵀ alg alg-≤ alg-η alg-delay APP        f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay MATCH      f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay SEQ-RET    f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay SEQ-OP     f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay HANDLE-RET f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay HANDLE-OP  f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay BOX        f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay UNBOX      f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay COERCE     f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ {B = B} alg alg-≤ alg-η alg-delay (SEQ-STEP r c) f =
  alg-stepᵀ {B = B} alg alg-≤ alg-η alg-delay r f
alg-stepᵀ {B = B} alg alg-≤ alg-η alg-delay (HANDLE-STEP r c) f =
  alg-stepᵀ {B = B} alg alg-≤ alg-η alg-delay r f
alg-stepᵀ {ε = ε} {ε₂ = ε₂} {B = B} alg alg-≤ alg-η alg-delay (DELAY {τ = τ}) f =
  -- Both sides reach the same normal form: the tick, with the *whole* bind
  -- carried under the box. `alg-ηᵀ` does the work there — under `[ of-natʳ τ ]`
  -- the step has become the trivial one.
  lhs ∙ ∘ᵐ-congˡ (≡→≈ᵐ (cong (λ z → ε-substᵀ z) uip)) ∙ ≈ᵐ-sym rhs
  where
    -- the common normal form
    NF : _ →ᵐ _
    NF = delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ (μᵀ ∘ᵐ Tᶠ (alg {ε} ∘ᵐ f) ∘ᵐ ηᵀ) ∘ᵐ η⊣

    -- the source: pull the tick out of the bind, collect everything under the
    -- box, then `alg-ηᵀ`
    lhs : alg {of-natᵉ τ ·ₑ uₑ ·ₑ ε} ∘ᵐ μᵀ ∘ᵐ Tᶠ f
            ∘ᵐ (delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣)
        ≈ᵐ ε-substᵀ _ ∘ᵐ NF
    lhs =
        ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (delayᵀ-nat τ f))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (delayᵀ-algebraicity τ))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (alg-ε-subst alg alg-≤ (sym (·ₑ-assoc (of-natᵉ τ) uₑ ε)))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (∘ᵐ-congˡ (alg-delay τ)))
      -- collect the transports, and the `[ of-natʳ τ ]ᶠ`-images into one
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (ε-substᵀ-trans _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
      -- under the box the step has become the trivial one: `alg-ηᵀ` applies
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (alg-ηᵀ alg alg-≤ alg-η f))))
      -- and the transport it produces floats out through the delay
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-∘ᵐ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (delayᵀ-ε-substᵀ τ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (ε-substᵀ-trans _ _)

    -- the target: the same two laws, in the same order
    rhs : ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ ·ₑ uₑ) ε ε₂))
            ∘ᵐ μᵀ ∘ᵐ Tᶠ (alg {ε} ∘ᵐ f)
            ∘ᵐ (delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣)
        ≈ᵐ ε-substᵀ _ ∘ᵐ NF
    rhs =
        ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (delayᵀ-nat τ (alg ∘ᵐ f)))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (delayᵀ-algebraicity τ))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (ε-substᵀ-trans _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))

-- COLLAPSING THE HANDLER'S ETERNAL PARAMETER AT RUNTIME CONTEXTS
--
-- In the operational soundness proofs every `handle` sits at a runtime context
-- `Γ` with `Γ ᴱ ≡ []`, so its eternal-parameter object `⟦ Γ ᴱ ⟧` is terminal.
-- The handler's fold therefore collapses to a plain (parameter-free) algebra
-- `Halg`, letting the `HANDLE-*` proofs reuse the `⨟`/`μᵀ` machinery verbatim.

-- The canonical (terminal) map into `⟦ Γ ᴱ ⟧` when `Γ ᴱ ≡ []`, and the fact
-- that any two such maps agree.
term∅ : ∀ {Γ X} → (e : Γ ᴱ ≡ []) → X →ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ
term∅ {X = X} e = subst (λ Δ → X →ᵐ ⟦ Δ ⟧ᶜᵗˣ) (sym e) terminalᵐ

∅-terminal : ∀ {Γ X} → (e : Γ ᴱ ≡ []) → (f g : X →ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ) → f ≈ᵐ g
∅-terminal {X = X} e =
  subst (λ Δ → (f g : X →ᵐ ⟦ Δ ⟧ᶜᵗˣ) → f ≈ᵐ g) (sym e)
        (λ f g → ≈ᵐ-trans terminalᵐ-unique (≈ᵐ-sym terminalᵐ-unique))

-- The parameter-free algebra a `handle` at a runtime context folds with.
Halg : ∀ {Γ A B ε₂} → (e : Γ ᴱ ≡ [])
     → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
          → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
               ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
            ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
     → ∀ {ε} → Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε ·ₑ ε₂)
Halg {Γ} e H = T-alg-of-handlerᵀ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H) ∘ᵐ ⟨ term∅ e , idᵐ ⟩ᵐ

-- `Halg`'s sub-effecting and unit laws, from the fold's own laws plus the
-- terminality of the (trivial) parameter.
Halg-≤ : ∀ {Γ A B ε₂} → (e : Γ ᴱ ≡ [])
       → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
            → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
              ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
       → ∀ {εa εb} → (q : εa ≾ₑ εb)
       → Halg {ε₂ = ε₂} e H {εb} ∘ᵐ T-≤ q ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ Halg e H {εa}
Halg-≤ {Γ} e H q =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨ ∅-terminal e _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-≤ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H) q)
  ∙ ∘ᵐ-assoc _ _ _

Halg-η : ∀ {Γ A B ε₂} → (e : Γ ᴱ ≡ [])
       → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
            → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
              ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
       → Halg {ε₂ = ε₂} e H {uₑ} ∘ᵐ ηᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂}
       ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε₂))
Halg-η {Γ} e H =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨ ∅-terminal e _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-ηᵀ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
  ∙ ∘ᵐ-identityʳ _

-- The handle interpretation collapses to `Halg` applied to the `⨟`-style
-- environment-threading term: the parameter `projᴱ Γ` is replaced by the
-- terminal map (both agree by `∅-terminal`).
handle-collapse : ∀ {Γ A B ε ε₂} → (e : Γ ᴱ ≡ [])
  → (M : Γ ⊢C⦂ A ‼ ε)
  → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
       → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
  → ⟦ handle M `with H `in N ⟧ᶜᵗ
  ≈ᵐ Halg {ε₂ = ε₂} e H {ε} ∘ᵐ (Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)
handle-collapse {Γ} e M H N =
    ∘ᵐ-congʳ (⟨ ∅-terminal e (projᴱ Γ)
                  (term∅ e ∘ᵐ (Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ))
              , ≈ᵐ-refl ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ≈ᵐ-sym (∘ᵐ-identityˡ _) ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- HANDLE-STEP
--
-- The same assembly as `SEQ-STEP`, with the handler's fold in place of the
-- monad multiplication. Everything is shared: `seq-step-core`, `step-box` and
-- `seq-target` are all generic in the algebra, and the two laws the chain uses
-- of `μᵀ` (`T-≤-μᵀ`, `T-μ∘μ≡μ∘Tμ`) are matched by the handler's own
-- (`T-alg-of-handlerᵀ-≤`, `T-alg-of-handlerᵀ-μᵀ`).

sound-HANDLE-STEP : ∀ {ε₁ ε₂ ε₃ A B} {S S' : 𝕊 []}
  → {M : toCtx S ⊢C⦂ A ‼ ε₁}
  → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
       → Γ' ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (N : toCtx S ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
  → {M' : toCtx S' ⊢C⦂ A ‼ ε₃}
  → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
  → (c : ≤ₛ-grade (step-extends-state r) ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ ε₁)
  → ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ S ⟧ˢ
    ≈ᵐ T-≤ (step-≾ r)
       ∘ᵐ _⋄_ {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {step-grade r} {ε₃}
              (⟦ M' ⟧ᶜᵗ ∘ᵐ ⟦ S' ⟧ˢ) (stepᵀ r)
  → ⟦ handle M `with H `in N ⟧ᶜᵗ ∘ᵐ ⟦ S ⟧ˢ
    ≈ᵐ T-≤ (step-≾ (HANDLE-STEP {H = H} {N = N} r c))
       ∘ᵐ _⋄_ {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ B ⟧ᵛ} {step-grade r} {ε₃ ·ₑ ε₂}
              (⟦ handle M' `with H
                   `in (C-rename (cong-∷-ren
                                   (suc-comp-ren (step-extends-state r) c)) N) ⟧ᶜᵗ
                 ∘ᵐ ⟦ S' ⟧ˢ)
              (stepᵀ r)
sound-HANDLE-STEP {ε₁} {ε₂} {ε₃} {A} {B} {S} {S'} {M} H N {M'} r c ih =
    seq-step-core alg alg-≤ N r c ih
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (⟨ box-merge _ _ (seq-g r) _ _ , ≈ᵐ-refl ⟩ᵐ-cong)))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (step-box r c (seq-g r)))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
      (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μᵀ-nat _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  -- merge the two functorial actions, so the bind is a single `Tᶠ f`
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)))))
  -- THE KEY STEP: the handler commutes with the step transition, because a
  -- reduction step never performs an operation
  ∙ ∘ᵐ-congʳ (alg-stepᵀ {B = B} alg alg-≤ alg-η alg-delay r _)
  -- drop the identity the strength's pairing picked up
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (∘ᵐ-congʳ ⟨ ≈ᵐ-refl , ∘ᵐ-identityʳ _ ⟩ᵐ-cong)))))))
  -- what is under it is the target's denotation …
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (≈ᵐ-sym
      (seq-target {ε₁} {ε₂} {ε₃} {A} {B}
                  {toCtx S} {toCtx S'} {⟦ hist S' ⟧ᶜᵗˣ}
                  (T-alg-of-handlerᵀ ⟦ H ⟧ʰᵗ)
                  N (suc-comp-ren (step-extends-state r) c)
                  M' ⟦ S' ⟧ˢ))))))
  -- … and `seq-coe` fixes the grade
  ∙ seq-coe (step-≾ r) (step-≾ (HANDLE-STEP {H = H} {N = N} r c)) _
  where
    alg : ∀ {ε} → Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε ·ₑ ε₂)
    alg = T-alg-of-handlerᵀ ⟦ H ⟧ʰᵗ

    alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
          → alg {εb} ∘ᵐ T-≤ q ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa}
    alg-≤ q = T-alg-of-handlerᵀ-≤ ⟦ H ⟧ʰᵗ q

    alg-η : alg {uₑ} ∘ᵐ ηᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂}
          ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε₂))
    alg-η = T-alg-of-handlerᵀ-ηᵀ ⟦ H ⟧ʰᵗ

    alg-delay : ∀ {ε'} → (τ : ℕ)
              → alg {of-natᵉ τ ·ₑ ε'} ∘ᵐ delayᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂} {ε'} τ
              ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε₂))
                  ∘ᵐ delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ (alg {ε'})
    alg-delay τ = T-alg-of-handlerᵀ-delayᵀ τ ⟦ H ⟧ʰᵗ

-- SEQ-OP
--
-- The operation commuting conversion: sequencing a computation that begins
-- with an operation is the operation with the sequencing pushed into its
-- continuation. This is the content of the algebraicity laws,
-- `opᵀ-algebraicity` for the multiplication and `strᵀ-opᵀ-algebraicity` for the
-- strength. The rule leaves the state alone, so this is a plain equation
-- between the two denotations, in an arbitrary context.
--
-- The strength is where the environment goes: the operation's continuation is
-- boxed (it may run only once `op-grade op` worth of time has passed), so the
-- environment is pushed under that box, which is what `exp-strᵐ` does.

-- Reassociating the operation's arguments.
--
-- `strᵀ-opᵀ-algebraicity` hands the operation back its parameter and pairs the
-- environment with the (boxed) continuation. Applied to an actual `perform`,
-- whose argument is `⟨ env , ⟨ param , cont ⟩ᵐ ⟩ᵐ`, that reshuffle just puts the
-- parameter back in front and leaves the environment sitting next to the
-- continuation, ready to be pushed under its box.

op-pair : ∀ {X E P Q R} → (v : X →ᵐ P) → (e : X →ᵐ E) → (c : X →ᵐ Q)
        → (F : E ×ᵐ Q →ᵐ R)
        → mapˣᵐ idᵐ F ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
            ∘ᵐ ⟨ e , ⟨ v , c ⟩ᵐ ⟩ᵐ
        ≈ᵐ ⟨ v , F ∘ᵐ ⟨ e , c ⟩ᵐ ⟩ᵐ
op-pair v e c F =
    ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
  ∙ ∘ᵐ-congʳ
      (⟨ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-fstᵐ _ _
       , ⟨⟩ᵐ-∘ _ _ _
         ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _
           , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong ⟩ᵐ-cong)
  ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
  ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong

-- The environment the operation's continuation receives.
--
-- Under the operation's box the environment has already been transposed once
-- (at `mapᵉ (op-grade op)`) and re-locked by `μ`; the continuation then binds
-- the arity value, so the environment must be weakened past it. Doing that
-- *outside* the second transposition (`_ ∘ᵐ fstᵐ`) and doing it *inside* it
-- (the syntax's `cong-⟨⟩-ren wk-ren`) agree, by naturality of `η⊣`.

op-env : ∀ {X Y d ε} → (a : mapᵉ d ·ᵣ mapᵉ ε ≾ᵣ mapᵉ (d ·ₑ ε))
       → ([ mapᵉ ε ]ᶠ (⟨⟩-≤ a ∘ᵐ μ) ∘ᵐ η⊣ {⟨ mapᵉ d ⟩ᵒ X} {mapᵉ ε}) ∘ᵐ fstᵐ {_} {Y}
       ≈ᵐ [ mapᵉ ε ]ᶠ (⟨⟩-≤ a ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ)
            ∘ᵐ η⊣ {⟨ mapᵉ d ⟩ᵒ X ×ᵐ Y} {mapᵉ ε}
op-env a =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat fstᵐ))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
  ∙ ∘ᵐ-congˡ ([]-congᶠ (∘ᵐ-assoc _ _ _))

-- PUSHING THE SEQUENCING UNDER THE OPERATION'S BOX
--
-- This is the heart of `SEQ-OP`. On the left the environment arrives boxed at
-- the *whole* computation's grade `mapᵉ (op-grade op ·ₑ ε)`; `strᵀ-opᵀ-algebra-
-- icity` splits that box with `δ` into `mapᵉ (op-grade op)` (the operation's own
-- delay) and `mapᵉ ε` (the continuation's), pairs the inner half with the boxed
-- continuation via `[]-monoidal`, and pushes it under the exponential with
-- `exp-strᵐ`. On the right the syntax has instead renamed the continuation's
-- context with `⟨⟩-μ-ren`, folding the two locks back into one.
--
-- The two agree: `box-split` is exactly the `δ`-split-then-`μ`-refold, and
-- `η⊣-⟨⟩` is what lets the two transposed halves be re-paired under one box.

seq-op-box : ∀ {X A B ε ε'} → (op : Op)
  → (alg : Tᵒ (Tᵒ B ε') ε →ᵐ Tᵒ B (ε ·ₑ ε'))
  → (m : (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ ⟦ arity op ⟧ᵍ) →ᵐ Tᵒ A ε)
  → (n : (⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X ×ᵐ A) →ᵐ Tᵒ B ε')
  → (rn : ⟨ mapᵉ ε ⟩ᵒ (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ ⟦ arity op ⟧ᵍ)
          →ᵐ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X)
  → rn ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
  → [ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ alg)
      ∘ᵐ [ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (Tᶠ n))
      ∘ᵐ ( [ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (strᵀ {_} {A} {ε}) ∘ᵐ exp-strᵐ)
         ∘ᵐ []-monoidal
         ∘ᵐ mapˣᵐ (δ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym map-·ᵉ))) idᵐ )
      ∘ᵐ ⟨ η⊣ {X} {mapᵉ (op-grade op ·ₑ ε)}
         , [ mapᵉ (op-grade op) ]ᶠ (curryᵐ m) ∘ᵐ η⊣ {X} {mapᵉ (op-grade op)} ⟩ᵐ
  ≈ᵐ [ mapᵉ (op-grade op) ]ᶠ
       (curryᵐ (alg ∘ᵐ Tᶠ (n ∘ᵐ mapˣᵐ rn idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ))
     ∘ᵐ η⊣ {X} {mapᵉ (op-grade op)}
seq-op-box {X} {A} {B} {ε} {ε'} op alg m n rn ern =
  -- bring the strength law's reshuffle up against the operation's arguments
    ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
  -- split the environment's box: once at the operation's grade, once at the
  -- continuation's, the two pasts refolded by `μ`
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (  mapˣᵐ-∘⟨⟩ _ _ _ _
       ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ box-split _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))))
  -- and pair the two transposed halves under one box
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (η⊣-⟨⟩ _ _)))
  -- collect everything under a single box
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
  -- inside the box: the environment is pushed under the exponential, and the
  -- three postcompositions collapse into the sequenced body
  ∙ ∘ᵐ-congˡ ([]-congᶠ
      (  ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (exp-strᵐ-⟨⟩ _ _)))
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (map⇒ᵐ-curryᵐ _ _))
       ∙ ∘ᵐ-congʳ (map⇒ᵐ-curryᵐ _ _)
       ∙ map⇒ᵐ-curryᵐ _ _))
  -- and that body is the target's, once the syntax's renaming is recognised as
  -- the environment the continuation actually receives
  ∙ ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (≈ᵐ-sym
      (  ∘ᵐ-congʳ (∘ᵐ-congˡ (T-∘ᵐ n (mapˣᵐ rn idᵐ)))
       ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
       ∙ body))))
  where
    -- the renaming the syntax applies to the continuation *is* the environment
    -- the strength hands it: a map on the strength's boxed component (`strᵀ-natˡ`),
    -- and that map is `op-env`
    body : alg ∘ᵐ Tᶠ n ∘ᵐ Tᶠ (mapˣᵐ rn idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ
         ≈ᵐ alg ∘ᵐ Tᶠ n ∘ᵐ strᵀ
              ∘ᵐ ⟨ ([ mapᵉ ε ]ᶠ (⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ) ∘ᵐ η⊣)
                     ∘ᵐ fstᵐ
                 , m ⟩ᵐ
    body =
        ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ rn)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
          (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
          (⟨ ∘ᵐ-congˡ ([]-congᶠ ern) ∙ ≈ᵐ-sym (op-env _) , ≈ᵐ-refl ⟩ᵐ-cong)))

-- The commuting conversion, at the level of the model.
--
-- The three moves are the operation's three laws: `strᵀ-opᵀ-algebraicity` puts
-- the environment inside the operation's continuation, `opᵀ-nat` puts the
-- sequel `n` there too, and `opᵀ-algebraicity` puts the multiplication there —
-- leaving the `ε-substᵀ` that reassociates the grades, which is exactly the
-- coercion the syntactic rule carries. The ground-type coercion `ea` is
-- generalised so it can be matched, at which point both `subst`s vanish.

seq-op-core : ∀ {X Y A B ε ε'} → (op : Op)
            -- the algebra that collapses the two monad layers (`μᵀ` for `⨟`,
            -- the handler's fold for `handle`) …
            → (alg : ∀ {ε₀} → Tᵒ (Tᵒ B ε') ε₀ →ᵐ Tᵒ B (ε₀ ·ₑ ε'))
            -- … and what it does to an operation: re-emit it (`opᵀ-algebraicity`)
            -- or apply the matching clause (`T-alg-of-handlerᵀ-opᵀ`). Either way
            -- the algebra is pushed into the operation's continuation.
            → (cl : (⟦ param op ⟧ᵍ
                       ×ᵐ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ B (ε ·ₑ ε')))
                    →ᵐ Tᵒ B (op-grade op ·ₑ (ε ·ₑ ε')))
            → (alg-op : alg {op-grade op ·ₑ ε} ∘ᵐ opᵀ {ε = ε} op
                      ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε'))
                         ∘ᵐ cl
                         ∘ᵐ mapˣᵐ idᵐ
                              ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (alg {ε}))))
            → (ea : Y ≡ ⟦ arity op ⟧ᵍ)
            → (v : X →ᵐ ⟦ param op ⟧ᵍ)
            → (m : (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ Y) →ᵐ Tᵒ A ε)
            → (n : (⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X ×ᵐ A) →ᵐ Tᵒ B ε')
            → (rn : ⟨ mapᵉ ε ⟩ᵒ (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ Y)
                    →ᵐ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X)
            → rn ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
            → alg ∘ᵐ Tᶠ n ∘ᵐ strᵀ
                ∘ᵐ ⟨ η⊣
                   , opᵀ op
                       ∘ᵐ ⟨ v
                          , [ mapᵉ (op-grade op) ]ᶠ
                              (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ O)
                                                    →ᵐ Tᵒ A ε)
                                             ea m))
                              ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
            ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε'))
               ∘ᵐ cl
               ∘ᵐ ⟨ v
                  , [ mapᵉ (op-grade op) ]ᶠ
                      (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ O)
                                            →ᵐ Tᵒ B (ε ·ₑ ε'))
                                     ea
                                     (alg ∘ᵐ Tᶠ (n ∘ᵐ mapˣᵐ rn idᵐ) ∘ᵐ strᵀ
                                        ∘ᵐ ⟨ η⊣ , m ⟩ᵐ)))
                    ∘ᵐ η⊣ ⟩ᵐ
seq-op-core op alg cl alg-op refl v m n rn ern =
  -- the operation is a map on the strength's monadic component …
    ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))))
  -- … so the strength pushes into it, carrying the environment under its box
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-opᵀ-algebraicity op)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  -- the reshuffle just hands the parameter back and pairs environment with
  -- continuation
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ op-pair _ _ _ _)))
  -- the sequel is natural, so it too goes into the continuation
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (opᵀ-nat op n)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  -- and the operation is algebraic for the algebra, so that goes in too —
  -- leaving the grade reassociation behind
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ alg-op
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  -- collect the three maps on the continuation
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
      (  ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)
       ∙ mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
  -- what they amount to is the sequenced continuation
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , seq-op-box op alg m n rn ern ⟩ᵐ-cong))

-- Cancelling the ground-type coercions.
--
-- `⟦_⟧ᶜᵗ` coerces an operation's parameter and arity between their value-type
-- and ground-type interpretations, and `⟦_⟧ʰᵗ` coerces them straight back. The
-- two cancel — which is why the handler's clause may be applied to the very
-- arguments the operation carries.

gty-cancelᵛ : ∀ {X Y Y'} → (e : Y ≡ Y') → (g : X →ᵐ Y)
            → subst (λ O → Y' →ᵐ O) (sym e) idᵐ ∘ᵐ subst (λ O → X →ᵐ O) e g ≈ᵐ g
gty-cancelᵛ refl g = ∘ᵐ-identityˡ _

gty-cancelᶜ : ∀ {Z W Y Y'} → (e : Y ≡ Y') → (f : (Z ×ᵐ Y) →ᵐ W)
            → subst (λ O → (Z ×ᵐ O) →ᵐ W) e f
                ∘ᵐ mapˣᵐ idᵐ (subst (λ O → O →ᵐ Y') (sym e) idᵐ)
            ≈ᵐ f
gty-cancelᶜ refl f = ∘ᵐ-congʳ mapˣᵐ-idᵐ ∙ ∘ᵐ-identityʳ _

-- SEQ-OP: sequencing an operation is the operation with the sequencing pushed
-- into its continuation. The state plays no part — the rule is a plain equation
-- in an arbitrary context.

sound-SEQ-OP : ∀ {Γ A B ε ε'} → (op : Op)
             → (V : Γ ⊢V⦂ type-of-gtype (param op))
             → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
             → (N : Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
             → ⟦ perform op V M ⨟ N ⟧ᶜᵗ
             ≈ᵐ ⟦ ε-subst (sym (·ₑ-assoc (op-grade op) ε ε'))
                    (perform op V
                      (M ⨟ C-rename
                             (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren
                                          ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-·ᵉ)))
                             N)) ⟧ᶜᵗ
sound-SEQ-OP {Γ} {A} {B} {ε} {ε'} op V M N =
    seq-op-core op μᵀ (opᵀ op) (opᵀ-algebraicity op) (ty-gty (arity op))
      (subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) ⟦ V ⟧ᵛᵗ)
      ⟦ M ⟧ᶜᵗ ⟦ N ⟧ᶜᵗ ⟦ ren ⟧ʳ ern
  ∙ ≈ᵐ-sym
      (  sound-ε-subst (sym (·ₑ-assoc (op-grade op) ε ε'))
           (perform op V (M ⨟ C-rename (cong-∷-ren ren) N))
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
           , ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (substᵈ-≈ (ty-gty (arity op))
               (∘ᵐ-congʳ (∘ᵐ-congˡ
                 (T-congᶠ (C-rename-nat (cong-∷-ren ren) N))))))) ⟩ᵐ-cong)))
  where
    ren : Ren (Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩)
              ((Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) ⟨ mapᵉ ε ⟩)
    ren = cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-·ᵉ)

    -- the renaming is the `μ`-refold of the two locks, after weakening past the
    -- arity value the continuation binds
    ern : ⟦ ren ⟧ʳ ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
    ern = ∘ᵐ-congˡ (∘ᵐ-congˡ (eq-ren-grade map-·ᵉ)) ∙ ∘ᵐ-assoc _ _ _

-- HANDLE-OP
--
-- Handling an operation applies the matching clause, with the rest of the
-- handled computation boxed up as the clause's continuation, the box being what
-- stops the continuation running before `op-grade op` worth of time has passed.
-- So the reduct is a `box`, and the equation is `SEQ-OP`'s with the handler's
-- fold in place of the monad multiplication: `T-alg-of-handlerᵀ-opᵀ` (apply a
-- clause) where `SEQ-OP` has `opᵀ-algebraicity` (re-emit the operation).
--
-- THE HANDLER UNIFORMITY CONDITION
--
-- A handler's clauses are one term, well-typed at every context `Γ'`, so they
-- can mention no variable of `Γ'` and their meaning at `Γ'` is their meaning at
-- `[]` with the context discarded. `Uniformʰ` states this semantically, terms
-- here being intrinsically typed. `HANDLE-OP` needs it because the reduct fires
-- the clause at `toCtx S` while `⟦_⟧ʰᵗ` reads the model's context-free
-- `Handlerᵀ` at `[]`.

Uniformʰ : ∀ {B}
         → ((op : Op) → (ε'' : E) → (Γ' : Ctx)
              → Γ' ∷ type-of-gtype (param op)
                   ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
         → Set
Uniformʰ H = ∀ op ε'' Γ'
           → ⟦ H op ε'' Γ' ⟧ᶜᵗ
           ≈ᵐ ⟦ H op ε'' [] ⟧ᶜᵗ ∘ᵐ mapˣᵐ (mapˣᵐ terminalᵐ idᵐ) idᵐ

-- The clause the semantics applies, reached from the clause the reduction fires.
--
-- `⟦_⟧ʰᵗ` coerces the operation's ground-typed parameter and arity; uniformity
-- discards the context. What is left on both sides is the `[]`-clause applied to
-- the parameter and the boxed continuation.

clause-sound : ∀ {Γ B ε''} → (op : Op)
             → (H : (op' : Op) → (ε' : E) → (Γ' : Ctx)
                  → Γ' ∷ type-of-gtype (param op')
                       ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε')
                    ⊢C⦂ B ‼ (op-grade op' ·ₑ ε'))
             → Uniformʰ H
             → (V : Γ ⊢V⦂ type-of-gtype (param op))
             -- the operation's continuation, boxed, at the *ground* arity — the
             -- form `opᵀ` hands to the algebra
             → (W : ⟦ Γ ⟧ᶜᵗˣ →ᵐ [ mapᵉ (op-grade op) ]ᵒ
                      (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ ⟦ B ⟧ᵛ ε''))
             → ⟦ H op ε'' Γ [ Tl-∷ Hd ↦ V ]c ⟧ᶜᵗ
                 ∘ᵐ ⟨ idᵐ
                    , [ mapᵉ (op-grade op) ]ᶠ
                        (map⇒ᵐ (subst (λ O → O →ᵐ ⟦ arity op ⟧ᵍ)
                                      (sym (ty-gty (arity op))) idᵐ) idᵐ)
                      ∘ᵐ W ⟩ᵐ
             ≈ᵐ ⟦ H ⟧ʰᵗ op ε''
                  ∘ᵐ ⟨ subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) ⟦ V ⟧ᵛᵗ
                     , W ⟩ᵐ
clause-sound {Γ} op H u V W =
  -- substituting the parameter into the clause
    ∘ᵐ-congˡ (C-subst-nat (H op _ Γ) (Tl-∷ Hd) V)
  -- the clause ignores its context
  ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ (u op _ Γ))
  ∙ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (mapˣᵐ-∘ _ _ _ _))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)
  -- what reaches the clause is the parameter and the boxed continuation
  ∙ ∘ᵐ-congʳ
      (⟨ ∘ᵐ-identityʳ _
         ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
         ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
       , ∘ᵐ-congˡ (∘ᵐ-identityˡ _) ∙ ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  -- and that is exactly what the semantic handler is applied to: its own
  -- ground-type coercions cancel the ones the operation carries
  ∙ ≈ᵐ-sym
      (  ∘ᵐ-assoc _ _ _
       ∙ ∘ᵐ-congʳ
           (mapˣᵐ-∘⟨⟩ _ _ _ _
            ∙ ⟨ ⟨⟩ᵐ-∘ _ _ _
                ∙ ⟨ terminalᵐ-unique
                  , gty-cancelᵛ (ty-gty (param op)) ⟦ V ⟧ᵛᵗ ⟩ᵐ-cong
              , ≈ᵐ-refl ⟩ᵐ-cong))

-- HANDLE-OP: the operation is handled by its clause, with the rest of the
-- computation boxed up as the clause's continuation.

sound-HANDLE-OP : ∀ {Γ A B ε ε''} → (op : Op)
                → (V : Γ ⊢V⦂ type-of-gtype (param op))
                → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                       ⊢C⦂ A ‼ ε)
                → (H : (op' : Op) → (ε' : E) → (Γ' : Ctx)
                     → Γ' ∷ type-of-gtype (param op')
                          ∷ [ mapᵉ (op-grade op') ]
                              (type-of-gtype (arity op') ⇒ B ‼ ε')
                       ⊢C⦂ B ‼ (op-grade op' ·ₑ ε'))
                → (N : Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε'')
                → Uniformʰ H
                → ⟦ handle perform op V M `with H `in N ⟧ᶜᵗ
                ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε''))
                   ∘ᵐ ⟦ box (lam (handle M `with H
                                   `in (C-rename (cong-∷-ren
                                          (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren
                                           ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-·ᵉ))) N)))
                            (H op (ε ·ₑ ε'') Γ [ Tl-∷ Hd ↦ V ]c) ⟧ᶜᵗ
sound-HANDLE-OP {Γ} {A} {B} {ε} {ε''} op V M H N u =
  -- the commuting conversion, with the handler's fold as the algebra: the
  -- operation is algebraic for it too, and applies a clause
    seq-op-core op (T-alg-of-handlerᵀ ⟦ H ⟧ʰᵗ) (⟦ H ⟧ʰᵗ op (ε ·ₑ ε''))
      (T-alg-of-handlerᵀ-opᵀ op ⟦ H ⟧ʰᵗ) (ty-gty (arity op))
      (subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) ⟦ V ⟧ᵛᵗ)
      ⟦ M ⟧ᶜᵗ ⟦ N ⟧ᶜᵗ ⟦ ren ⟧ʳ ern
  -- what is left is the reduct: the clause fired at `Γ`, applied to the
  -- parameter and to the boxed continuation the `box` allocates
  ∙ ∘ᵐ-congʳ tgt
  where
    ren : Ren (Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩)
              ((Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) ⟨ mapᵉ ε ⟩)
    ren = cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-·ᵉ)

    ern : ⟦ ren ⟧ʳ ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
    ern = ∘ᵐ-congˡ (∘ᵐ-congˡ (eq-ren-grade map-·ᵉ)) ∙ ∘ᵐ-assoc _ _ _

    -- the box the reduct allocates is the operation's continuation: the
    -- handled remainder, abstracted over the arity value. The `map⇒ᵐ` the
    -- semantic handler applies is undone by `map⇒ᵐ-curryᵐˡ`, and the arity
    -- coercions cancel.
    tgt : ⟦ H ⟧ʰᵗ op (ε ·ₑ ε'')
            ∘ᵐ ⟨ subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) ⟦ V ⟧ᵛᵗ
               , [ mapᵉ (op-grade op) ]ᶠ
                   (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ ×ᵐ O)
                                         →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε ·ₑ ε''))
                                  (ty-gty (arity op))
                                  (T-alg-of-handlerᵀ ⟦ H ⟧ʰᵗ
                                     ∘ᵐ Tᶠ (⟦ N ⟧ᶜᵗ ∘ᵐ mapˣᵐ ⟦ ren ⟧ʳ idᵐ)
                                     ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ)))
                 ∘ᵐ η⊣ ⟩ᵐ
        ≈ᵐ ⟦ box (lam (handle M `with H `in (C-rename (cong-∷-ren ren) N)))
                 (H op (ε ·ₑ ε'') Γ [ Tl-∷ Hd ↦ V ]c) ⟧ᶜᵗ
    tgt =
        ≈ᵐ-sym (clause-sound op H u V _)
      ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
          , ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
            ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
            -- undo the semantic handler's arity coercion …
            ∙ ∘ᵐ-congˡ ([]-congᶠ (map⇒ᵐ-curryᵐˡ _ _))
            -- … which cancels the interpretation's own
            ∙ ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (gty-cancelᶜ (ty-gty (arity op)) _)))
            -- and what is boxed is the handled remainder
            ∙ ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
                  (≈ᵐ-sym (C-rename-nat (cong-∷-ren ren) N)))))))
          ⟩ᵐ-cong)

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

Uniform↝ : ∀ {ε ε' A} {S S' : 𝕊 []}
         → {M : toCtx S ⊢C⦂ A ‼ ε} → {M' : toCtx S' ⊢C⦂ A ‼ ε'}
         → ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩
         → Set
Uniform↝ (HANDLE-OP {H = H})   = Uniformʰ H
Uniform↝ (SEQ-STEP r _)        = Uniform↝ r
Uniform↝ (HANDLE-STEP r _)     = Uniform↝ r
Uniform↝ APP                   = ⊤
Uniform↝ MATCH                 = ⊤
Uniform↝ SEQ-RET               = ⊤
Uniform↝ SEQ-OP                = ⊤
Uniform↝ DELAY                 = ⊤
Uniform↝ HANDLE-RET            = ⊤
Uniform↝ BOX                   = ⊤
Uniform↝ UNBOX                 = ⊤
Uniform↝ COERCE                = ⊤

↝-sound : ∀ {ε ε' A} {S S' : 𝕊 []}
        → {M : toCtx S ⊢C⦂ A ‼ ε} → {M' : toCtx S' ⊢C⦂ A ‼ ε'}
        → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
        → Uniform↝ r
        → ⟦ ⟨ S , M ⟩ ⟧ᶜᶠ
        ≈ᵐ T-≤ (step-≾ r)
           ∘ᵐ _⋄_ {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {step-grade r} {ε'}
                  ⟦ ⟨ S' , M' ⟩ ⟧ᶜᶠ (stepᵀ r)

-- The rules that neither advance time nor change the store: a plain equation
-- between the two denotations, with `ηᵀ`'s unit grade absorbed by `T-≤`.

↝-sound r@(APP {M = M} {V = V}) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-APP M V))
↝-sound r@(MATCH {V = V} {W = W} {M = M}) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-MATCH V W M))
↝-sound r@(SEQ-OP {op = op} {V = V} {M = M} {N = N}) _ =
  pure-step-≡ (step-≾ r) (∘ᵐ-congˡ (sound-SEQ-OP op V M N))

-- Allocation and lookup: also plain equations, but ones that mention the store.

↝-sound r@(BOX {S = St} {V = V} {M = M}) _ =
  pure-step-≡ (step-≾ r) (sound-BOX St V M)
↝-sound r@(UNBOX {S = St} {w = w} {V = V} {M = M}) _ =
  pure-step-≡ (step-≾ r) (sound-UNBOX St w V M)

-- The `return` rules: the coercion the substitution leaves behind is `ε-substᵀ`,
-- which `T-≤-≡` turns into the sub-effecting the theorem asks for.

↝-sound r@(SEQ-RET {V = V} {N = N}) _ =
  pure-step (step-≾ r) (≾ₑ-reflexive (sym (·ₑ-identityˡ _)))
    (∘ᵐ-congˡ (sound-SEQ-RET V N) ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congˡ (T-≤-≡ _))
↝-sound r@(HANDLE-RET {V = V} {H = H} {N = N}) _ =
  pure-step (step-≾ r) (≾ₑ-reflexive (sym (·ₑ-identityˡ _)))
    (∘ᵐ-congˡ (sound-HANDLE-RET V H N) ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congˡ (T-≤-≡ _))

-- Peeling a coercion: the step refines the grade by exactly the coercion's own
-- witness, which is what `T-≤` already does.

↝-sound r@(COERCE {M = M} {ε≾ε' = p}) _ =
  pure-step (step-≾ r) p (∘ᵐ-congˡ (sound-COERCE p M) ∙ ∘ᵐ-assoc _ _ _)

-- The one rule that advances time.

↝-sound r@(DELAY {τ = τ} {S = St} {M = M}) _ = sound-DELAY τ St M (step-≾ r)

-- The congruence rules: the inductive hypothesis is pushed through the strength
-- and multiplied, the environment carried across the step by `step-box`.

↝-sound (SEQ-STEP {N = N} r c) u = sound-SEQ-STEP N r c (↝-sound r u)
↝-sound (HANDLE-STEP {H = H} {N = N} r c) u =
  sound-HANDLE-STEP H N r c (↝-sound r u)

-- Handling an operation: the clause is applied, with the handled remainder
-- boxed up as its continuation. This is the only rule that reads a clause, and
-- so the only one that needs the handler's uniformity.

↝-sound r@(HANDLE-OP {op = op} {V = V} {M = M} {H = H} {N = N}) u =
  pure-step (step-≾ r) (≾ₑ-reflexive (sym (·ₑ-assoc (op-grade op) _ _)))
    (∘ᵐ-congˡ (sound-HANDLE-OP op V M H N u)
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

Uniform↝* : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
          → cf ↝* cf' → Set
Uniform↝* ε*       = ⊤
Uniform↝* (r ◅ rs) = Uniform↝ r × Uniform↝* rs

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
         → (rs : cf ↝* cf') → Uniform↝* rs
         → ⟦ cf ⟧ᶜᶠ
         ≈ᵐ T-≤ (steps-≾ rs)
            ∘ᵐ _⋄_ {⟦ hist (Config.state cf) ⟧ᶜᵗˣ}
                   {⟦ hist (Config.state cf') ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ}
                   {steps-grade rs} {ε'}
                   ⟦ cf' ⟧ᶜᶠ (stepsᵀ rs)
-- the empty run: the transition is `ηᵀ`, which the bind absorbs
↝*-sound {A = A} {ε = ε} {cf = cf} ε* _ =
  pure-step-≡ (steps-≾ (ε* {A} {ε} {cf})) ≈ᵐ-refl
-- a step, then a run
↝*-sound {A = A} {ε' = ε'} (_◅_ {ε₂ = ε₂} {cf₃ = cf₃} r rs) (u , us) =
  -- the step is sound …
    ↝-sound r u
  -- … and so, inductively, is the run that follows it
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (↝*-sound rs us))))
  -- THE KEY STEP: the run's coercion escapes the bind
  ∙ ∘ᵐ-congʳ (T-≤-stepᵀ ⟦ A ⟧ᵛ r (⟦ cf₃ ⟧ᶜᶠ ⋄ stepsᵀ rs) (steps-≾ rs))
  -- the two binds re-associate into one, at the product of their grades …
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (bind-bind ⟦ cf₃ ⟧ᶜᶠ (stepsᵀ rs) (stepᵀ r)))
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

record _⊳_ {A ε ε'} (cf : Config (A ‼ ε)) (cf' : Config (A ‼ ε')) : Set where
  constructor mk⊳
  field
    -- the effect the transition performs, and the refinement it licenses
    grade : E
    refine : grade ·ₑ ε' ≾ₑ ε
    -- the transition itself, between the two states' histories
    tr     : ⟦ hist (Config.state cf) ⟧ᶜᵗˣ
           →ᵐ Tᵒ ⟦ hist (Config.state cf') ⟧ᶜᵗˣ grade
    -- and the equation
    sound  : ⟦ cf ⟧ᶜᶠ
           ≈ᵐ T-≤ refine
              ∘ᵐ _⋄_ {⟦ hist (Config.state cf) ⟧ᶜᵗˣ}
                     {⟦ hist (Config.state cf') ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {grade} {ε'}
                     ⟦ cf' ⟧ᶜᶠ tr

-- Reflexivity: a configuration runs to itself, taking no time and refining
-- nothing.

⊳-refl : ∀ {A ε} → (cf : Config (A ‼ ε)) → cf ⊳ cf
⊳-refl {ε = ε} cf =
  mk⊳ uₑ (steps-≾ (ε* {cf = cf})) ηᵀ (↝*-sound (ε* {cf = cf}) tt)

-- A run of the machine is such a witness. This is the soundness theorem in its
-- final form: reduction never changes what a configuration means.

↝*-⊳ : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
     → (rs : cf ↝* cf') → Uniform↝* rs → cf ⊳ cf'
↝*-⊳ rs us = mk⊳ (steps-grade rs) (steps-≾ rs) (stepsᵀ rs) (↝*-sound rs us)

-- CLOSED PROGRAMS
--
-- A program is a closed computation: the empty state, so the empty history, so
-- its denotation is a global point of `Tᵒ ⟦ A ⟧ᵛ ε`. If it runs to a returned
-- value, the program *is* that value returned — after the run's transition, and
-- at the run's (refined) grade. Nothing of the state survives in the equation:
-- `hist ∅ ≡ []`, so both sides are morphisms out of `𝟙ᵐ`.

Program : VType → E → Set
Program A ε = [] ⊢C⦂ A ‼ ε

⟦_⟧ᵖ : ∀ {A ε} → Program A ε → 𝟙ᵐ →ᵐ Tᵒ ⟦ A ⟧ᵛ ε
⟦ M ⟧ᵖ = ⟦ M ⟧ᶜᵗ

-- Running a program to a value: its denotation is `ηᵀ` of the value's, in the
-- final state's environment, composed with the run's transition.

↝*-value : ∀ {A ε} {S' : 𝕊 []}
         → (M : Program A ε)
         → (V : toCtx S' ⊢V⦂ A)
         → (rs : ⟨ ∅ , M ⟩ ↝* ⟨ S' , return V ⟩)
         → Uniform↝* rs
         → ⟦ M ⟧ᵖ
         ≈ᵐ T-≤ (steps-≾ rs)
            ∘ᵐ _⋄_ {𝟙ᵐ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {steps-grade rs} {uₑ}
                   (ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ S' ⟧ˢ) (stepsᵀ rs)
↝*-value M V rs us =
  -- the empty state is the empty environment
    ≈ᵐ-sym (∘ᵐ-identityʳ _)
  ∙ ↝*-sound rs us
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (∘ᵐ-assoc _ _ _))))
