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
-- state's history `hist S`, and a configuration therefore denotes a      --
-- morphism out of `⟦ hist S ⟧ᶜᵗˣ` — for an initial state `∅` that is     --
-- `𝟙ᵐ`, i.e. a genuine global point.                                     --
--                                                                    --
-- A reduction step then relates the two denotations. Since the two       --
-- configurations have different histories and different effect grades,   --
-- the statement is mediated by                                          --
--                                                                    --
--   * a *time transition* `stepᵀ r : ⟦ hist S ⟧ →ᵐ Tᵒ ⟦ hist S' ⟧ δ`,    --
--     which is the identity (`ηᵀ`) for every rule but `DELAY` — the only --
--     rule that adds a lock — where it is the tick built from `delayᵀ`;  --
--                                                                    --
--   * a sub-effecting coercion `T-≤`, because reduction *refines* the    --
--     effect grade (`COERCE` peels a coercion off; `SEQ-STEP` sharpens   --
--     a grade). The tree equality collapses coercion nodes, so `T-≤` is  --
--     functorial in the grade and the relation stays a preorder.         --
--                                                                    --
-- Note `BOX` needs no transition: allocating a resource and extending    --
-- the store are the *same* morphism (`[ ρ ]ᶠ ⟦ V ⟧ ∘ᵐ η⊣`), which is     --
-- what `⟦_⟧ˢ`'s cell clause and `⟦ box V M ⟧ᶜᵗ` both use. Dually `UNBOX` --
-- needs none either: it is already a projection out of the environment.  --
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

open import Data.Product using (_,_; proj₁; proj₂)

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
                       []-ε-nat; []-ε∘ηᵘ≡id; ηᵘ; δ; []-δ-nat; []-monoidal;
                       []-monoidal-nat) renaming (ε to εᵇ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; μ; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ; ⟨⟩-η-nat; ⟨⟩-μ-nat;
                     ⟨⟩-≤-nat; ⟨⟩-≤-irr; ⟨⟩-≤-refl; ⟨⟩-≤-trans; μ-≤ˡ; μ-≤ʳ;
                     ⟨⟩-μ∘Tη≡id; ⟨⟩-μ∘η≡id)
open Adjunction Adj using (η⊣; η⊣-nat; η⊣-u; η⊣-≤; η⊣-δ; η⊣-monoidal;
                           ε⊣; ε⊣-nat; triangleˡ)
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst GTy Mon
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.State S Cat Fut Pst Adj GTy Mon GE

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

-- The step's effect, composed with the target's, refines the source's.
-- (This is the *effect*-graded counterpart of `step-invariants`, whose
-- grade-decrease condition lives in the resource grades.)

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
  -- the returned value is `ηᵀ` in the strength's second component
    ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  -- the strength's unit law opens the boxed environment
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ strᵀ-ηᵀ))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)))
  -- and the opened environment is exactly the syntax's re-locking renaming
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (⟨ ∘ᵐ-assoc _ _ _ ∙ ret-env map-uᵉ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  -- what remains is the algebra's unit law
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (ηᵀ-nat ⟦ N ⟧ᶜᵗ)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ alg-η
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
                      → Γ' ∷ type-of-gtype (param op)
                           ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                        ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                 → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
                 → ⟦ handle return V `with H `in N ⟧ᶜᵗ
                 ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε))
                    ∘ᵐ ⟦ C-rename (cong-∷-ren (⟨⟩-η-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-uᵉ))) N
                           [ Hd ↦ V ]c ⟧ᶜᵗ
sound-HANDLE-RET V H N =
  ret-step (T-alg-of-handlerᵀ ⟦ H ⟧ʰᵗ) (T-alg-of-handlerᵀ-ηᵀ ⟦ H ⟧ʰᵗ) V N

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
-- `unbox-lookup` does not hand back the stored value directly: it renames it
-- out of the allocating prefix's context into `toCtx S`, through a composite
-- of transports, a `wk-ren-⟨ρ⟩-ctx`, and the grade relaxation `⟨⟩-≤-ren rel`.
-- What follows shows that composite denotes exactly `state-past`.
--
-- The delicate point: `wk-ren-⟨ρ⟩-ctx` matches its grade equality against
-- `refl`, but the grade `ρ'` occurs inside `split-state-snd St x`, whose type
-- mentions `x : … ∈[ ρ' ] …` — so specialising it is circular. The fix is to
-- never match that equality: carry the grade coercion *explicitly* as a
-- `⟨⟩-≤`, at an arbitrary witness (the order is proof-irrelevant), and let the
-- induction reconcile witnesses with `⟨⟩-≤-irr`.

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
        → (box : Δ →ᵐ [ mapᵉ ε₁ ]ᵒ (⟨ mapᵉ ε₁ ⟩ᵒ Γ))
        → (n : ⟨ mapᵉ ε₁ ⟩ᵒ Γ ×ᵐ A →ᵐ Tᵒ B ε₂)
        → (W : Δ →ᵐ Tᵒ A ε₀) → (p : ε₀ ≾ₑ ε₁)
        → μᵀ ∘ᵐ Tᶠ n ∘ᵐ strᵀ {⟨ mapᵉ ε₁ ⟩ᵒ Γ} {A} {ε₁} ∘ᵐ ⟨ box , T-≤ p ∘ᵐ W ⟩ᵐ
        ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ p)
            ∘ᵐ μᵀ ∘ᵐ Tᶠ n ∘ᵐ strᵀ {⟨ mapᵉ ε₁ ⟩ᵒ Γ} {A} {ε₀}
            ∘ᵐ ⟨ []-≤ (map-monotoneᵉ p) ∘ᵐ box , W ⟩ᵐ
coe-out bx n W p =
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
  ∙ ∘ᵐ-congˡ (T-≤-μᵀ p)
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
         → (bx : Δ →ᵐ [ mapᵉ ε₁ ]ᵒ (⟨ mapᵉ ε₁ ⟩ᵒ Γ))
         → (n : ⟨ mapᵉ ε₁ ⟩ᵒ Γ ×ᵐ A →ᵐ Tᵒ B ε₂)
         → (g' : Δ' →ᵐ Tᵒ A ε₃) → (t : Δ →ᵐ Tᵒ Δ' d)
         → (p : d ·ₑ ε₃ ≾ₑ ε₁)
         → μᵀ ∘ᵐ Tᶠ n ∘ᵐ strᵀ {⟨ mapᵉ ε₁ ⟩ᵒ Γ} {A} {ε₁}
             ∘ᵐ ⟨ bx , T-≤ p ∘ᵐ μᵀ ∘ᵐ Tᶠ g' ∘ᵐ t ⟩ᵐ
         ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ p)
             ∘ᵐ μᵀ ∘ᵐ Tᶠ n ∘ᵐ μᵀ
             ∘ᵐ Tᶠ (strᵀ {⟨ mapᵉ ε₁ ⟩ᵒ Γ} {A} {ε₃})
             ∘ᵐ Tᶠ (mapˣᵐ idᵐ g')
             ∘ᵐ strᵀ {[ mapᵉ ε₃ ]ᵒ (⟨ mapᵉ ε₁ ⟩ᵒ Γ)} {Δ'} {d}
             ∘ᵐ ⟨ (δ {⟨ mapᵉ ε₁ ⟩ᵒ Γ} {mapᵉ d} {mapᵉ ε₃}
                     ∘ᵐ []-≤ (≾ᵣ-reflexive (sym (map-·ᵉ {d} {ε₃}))))
                    ∘ᵐ ([]-≤ (map-monotoneᵉ p) ∘ᵐ bx)
                , t ⟩ᵐ
push-str bx n g' t p =
    coe-out bx n (μᵀ ∘ᵐ Tᶠ g' ∘ᵐ t) p
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
  → {M : toCtx S ⊢C⦂ A ‼ ε₁} → (N : toCtx S ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
  → {M' : toCtx S' ⊢C⦂ A ‼ ε₃}
  → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
  → (c : ≤ₛ-grade (step-extends-state r) ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ ε₁)
  → ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ S ⟧ˢ
    ≈ᵐ T-≤ (step-≾ r)
       ∘ᵐ _⋄_ {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {step-grade r} {ε₃}
              (⟦ M' ⟧ᶜᵗ ∘ᵐ ⟦ S' ⟧ˢ) (stepᵀ r)
  → ⟦ M ⨟ N ⟧ᶜᵗ ∘ᵐ ⟦ S ⟧ˢ
    ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ (step-≾ r))
       ∘ᵐ μᵀ ∘ᵐ Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ μᵀ
       ∘ᵐ Tᶠ (strᵀ {⟨ mapᵉ ε₁ ⟩ᵒ ⟦ toCtx S ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {ε₃})
       ∘ᵐ Tᶠ (mapˣᵐ idᵐ (⟦ M' ⟧ᶜᵗ ∘ᵐ ⟦ S' ⟧ˢ))
       ∘ᵐ strᵀ {[ mapᵉ ε₃ ]ᵒ (⟨ mapᵉ ε₁ ⟩ᵒ ⟦ toCtx S ⟧ᶜᵗˣ)} {⟦ hist S' ⟧ᶜᵗˣ} {step-grade r}
       ∘ᵐ ⟨ (δ {⟨ mapᵉ ε₁ ⟩ᵒ ⟦ toCtx S ⟧ᶜᵗˣ} {mapᵉ (step-grade r)} {mapᵉ ε₃}
               ∘ᵐ []-≤ (≾ᵣ-reflexive (sym (map-·ᵉ {step-grade r} {ε₃}))))
              ∘ᵐ ([]-≤ (map-monotoneᵉ (step-≾ r)) ∘ᵐ (η⊣ ∘ᵐ ⟦ S ⟧ˢ))
          , stepᵀ r ⟩ᵐ
seq-step-core {ε₁} {ε₂} {ε₃} {A} {B} {S} {S'} {M} N {M'} r c ih =
    seq-push {⟦ toCtx S ⟧ᶜᵗˣ} {⟦ hist S ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {⟦ B ⟧ᵛ} {ε₁} {ε₂}
             μᵀ ⟦ N ⟧ᶜᵗ ⟦ M ⟧ᶜᵗ ⟦ S ⟧ˢ
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (⟨_,_⟩ᵐ-cong {f = η⊣ ∘ᵐ ⟦ S ⟧ˢ} {f' = η⊣ ∘ᵐ ⟦ S ⟧ˢ}
                   {g = ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ S ⟧ˢ}
                   {g' = T-≤ (step-≾ r) ∘ᵐ (μᵀ ∘ᵐ Tᶠ (⟦ M' ⟧ᶜᵗ ∘ᵐ ⟦ S' ⟧ˢ) ∘ᵐ stepᵀ r)}
                   ≈ᵐ-refl ih)))
  ∙ push-str {⟦ toCtx S ⟧ᶜᵗˣ} {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {⟦ B ⟧ᵛ}
             {step-grade r} {ε₁} {ε₂} {ε₃}
             (η⊣ ∘ᵐ ⟦ S ⟧ˢ) ⟦ N ⟧ᶜᵗ (⟦ M' ⟧ᶜᵗ ∘ᵐ ⟦ S' ⟧ˢ) (stepᵀ r) (step-≾ r)
