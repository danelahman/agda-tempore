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

module OperationalSemantics.Soundness.Preservation.Base
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
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj
       using (Eternalᵒ; ⟨⊤⟩-eternalᵒ; ⟨⊤⟩-η)

-- The `Eternalᵒ` on `⟦ Γ ⟨ ⊤ᵣ ⟩ ⟧` carried by every `handle` interpretation: the
-- eternal-parameter object of the handler's fold, free on `⟦ Γ ⟧`.
bcᴱ : ∀ (Γ : Ctx) → Eternalᵒ ⟦ Γ ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ
bcᴱ Γ = ⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ

-- THE INTERPRETATION OF A CONFIGURATION
--
-- The computation, with its context plugged by the state.

Paramᶜᶠ : ∀ {C} → Config C → Set
Paramᶜᶠ ⟨ St , M ⟩ = Paramˢ St × Paramᶜ M

⟦_⟧ᶜᶠ : ∀ {C} → (cf : Config C) → Paramᶜᶠ cf
      → ⟦ hist (Config.state cf) ⟧ᶜᵗˣ →ᵐ ⟦ C ⟧ᶜ
⟦ ⟨ St , M ⟩ ⟧ᶜᶠ (pSt , pM) = ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ St ⟧ˢ pSt

-- THE STATE'S CERTIFICATE ACROSS A STEP
--
-- Only `BOX` changes it: the cell it allocates stores the boxed value, whose
-- certificate is the term's, renamed. Every other rule either keeps the state
-- or only locks it, and the two congruences inherit the sub-step's.

stepᴾˢ : ∀ {ε ε' A} {S S' : 𝕊 []}
       → {M : toCtx S ⊢C⦂ A ‼ ε} → {M' : toCtx S' ⊢C⦂ A ‼ ε'}
       → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩) → Paramˢ S → Paramᶜ M → Paramˢ S'
stepᴾˢ APP                 pS _              = pS
stepᴾˢ MATCH               pS _              = pS
stepᴾˢ IF-TRUE             pS _              = pS
stepᴾˢ IF-FALSE            pS _              = pS
stepᴾˢ (SEQ-STEP r _)      pS (pM , _)       = stepᴾˢ r pS pM
stepᴾˢ SEQ-RET             pS _              = pS
stepᴾˢ SEQ-OP              pS _              = pS
stepᴾˢ DELAY               pS _              = pS
stepᴾˢ HANDLE-RET          pS _              = pS
stepᴾˢ (HANDLE-STEP r _)   pS (pM , _)       = stepᴾˢ r pS pM
stepᴾˢ HANDLE-OP           pS _              = pS
stepᴾˢ (BOX {V = V})       pS (pV , _)       =
  pS , renᵛ (eq-ren (sym ++ᶜ-identityˡ)) V pV
stepᴾˢ UNBOX               pS _              = pS
stepᴾˢ COERCE              pS _              = pS

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
step-grade IF-TRUE              = uₑ
step-grade IF-FALSE             = uₑ
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
stepᵀ IF-TRUE           = ηᵀ
stepᵀ IF-FALSE          = ηᵀ
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
step-≾ {ε = ε} IF-TRUE  = ≾ₑ-reflexive (·ₑ-identityˡ ε)
step-≾ {ε = ε} IF-FALSE = ≾ₑ-reflexive (·ₑ-identityˡ ε)
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
          → (pM : Paramᶜ M) → (pV : Paramᵛ V)
          → ⟦ lam M · V ⟧ᶜᵗ (pM , pV) ≈ᵐ ⟦ M [ split-[] ↦ V ]c ⟧ᶜᵗ (subᶜ M split-[] V pM pV)
sound-APP M V pM pV =
  ≈ᵐ-trans (βᵐ (⟦ M ⟧ᶜᵗ pM) (⟦ V ⟧ᵛᵗ pV)) (≈ᵐ-sym (C-subst-nat M split-[] V pM pV))

-- MATCH: destructing a pair is the two substitutions in sequence. The inner
-- one substitutes `W` weakened past `A`, which reindexes it by `fstᵐ`; that
-- projection is then cancelled by the outer environment.

sound-MATCH : ∀ {Γ A B C} → (V : Γ ⊢V⦂ A) → (W : Γ ⊢V⦂ B) → (M : Γ ∷ A ∷ B ⊢C⦂ C)
            → (pV : Paramᵛ V) → (pW : Paramᵛ W) → (pM : Paramᶜ M)
            → ⟦ match ⦉ V , W ⦊ `in M ⟧ᶜᵗ ((pV , pW) , pM)
            ≈ᵐ ⟦ (M [ split-[] ↦ V-rename wk-ren W ]c) [ split-[] ↦ V ]c ⟧ᶜᵗ
                 (subᶜ (M [ split-[] ↦ V-rename wk-ren W ]c) split-[] V
                    (subᶜ M split-[] (V-rename wk-ren W) pM (renᵛ wk-ren W pW)) pV)
sound-MATCH V W M pV pW pM =
  ≈ᵐ-trans
    (∘ᵐ-congʳ (⟨ ⟨ ≈ᵐ-refl , ⟨⟩ᵐ-fstᵐ _ _ ⟩ᵐ-cong , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong))
    (≈ᵐ-sym
      (≈ᵐ-trans (C-subst-nat (M [ split-[] ↦ V-rename wk-ren W ]c) split-[] V
                   (subᶜ M split-[] (V-rename wk-ren W) pM (renᵛ wk-ren W pW)) pV)
      (≈ᵐ-trans (∘ᵐ-congˡ (C-subst-nat M split-[] (V-rename wk-ren W) pM
                             (renᵛ wk-ren W pW)))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                (∘ᵐ-congʳ
                  (≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
                            (⟨ ∘ᵐ-identityˡ _
                             , ≈ᵐ-trans (∘ᵐ-congˡ (V-rename-nat wk-ren W pW))
                               (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                               (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                                         (∘ᵐ-identityʳ _))) ⟩ᵐ-cong)))))))

-- BOX: allocating a resource and extending the store are the *same* morphism,
-- so the two configurations' denotations coincide outright. The stored value
-- is the boxed one reindexed along `[] ++ᶜ Γ ≡ Γ`, which cancels.

sound-BOX : ∀ {A B ρ ε} → (St : 𝕊 []) → (V : toCtx St ⟨ ρ ⟩ ⊢V⦂ A)
          → (M : toCtx St ∷ [ ρ ] A ⊢C⦂ B ‼ ε)
          → (pSt : Paramˢ St) → (pV : Paramᵛ V) → (pM : Paramᶜ M)
          → ⟦ box V M ⟧ᶜᵗ (pV , pM) ∘ᵐ ⟦ St ⟧ˢ pSt
          ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ St ∷ₛ V-rename (eq-ren (sym ++ᶜ-identityˡ)) V ⟧ˢ
                            (pSt , renᵛ (eq-ren (sym ++ᶜ-identityˡ)) V pV)
sound-BOX {ρ = ρ} St V M pSt pV pM =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (∘ᵐ-congʳ (∘ᵐ-congˡ
      (⟨ ≈ᵐ-refl {f = idᵐ}
       , ∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym stored≈V)) ⟩ᵐ-cong)))
  where
    -- the value the state stores is `V` reindexed along `[] ++ᶜ Γ ≡ Γ`,
    -- and the state's interpretation reindexes it straight back
    stored≈V : ⟦ V-rename (eq-ren (sym (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩}))) V ⟧ᵛᵗ
                 (renᵛ (eq-ren (sym ++ᶜ-identityˡ)) V pV)
                 ∘ᵐ ⟦ eq-ren (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩}) ⟧ʳ
             ≈ᵐ ⟦ V ⟧ᵛᵗ pV
    stored≈V =
      ≈ᵐ-trans (∘ᵐ-congˡ (V-rename-nat
                            (eq-ren (sym (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩}))) V pV))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (eq-ren-inv (++ᶜ-identityˡ {toCtx St ⟨ ρ ⟩})))
                (∘ᵐ-identityʳ _)))

-- COERCE: peeling a coercion off is exactly what `T-≤` does.

sound-COERCE : ∀ {Γ A ε ε'} → (p : ε ≾ₑ ε') → (M : Γ ⊢C⦂ A ‼ ε) → (pM : Paramᶜ M)
             → ⟦ coerce p M ⟧ᶜᵗ pM ≈ᵐ T-≤ p ∘ᵐ ⟦ M ⟧ᶜᵗ pM
sound-COERCE p M pM = ≈ᵐ-refl

-- IF-TRUE / IF-FALSE: taking a branch is the boolean object's beta law.

sound-IF-TRUE : ∀ {Γ C} → (M N : Γ ⊢C⦂ C) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
              → ⟦ if true `then M `else N ⟧ᶜᵗ (tt , pM , pN) ≈ᵐ ⟦ M ⟧ᶜᵗ pM
sound-IF-TRUE M N pM pN = ifᵐ-true (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)

sound-IF-FALSE : ∀ {Γ C} → (M N : Γ ⊢C⦂ C) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
               → ⟦ if false `then M `else N ⟧ᶜᵗ (tt , pM , pN) ≈ᵐ ⟦ N ⟧ᶜᵗ pN
sound-IF-FALSE M N pM pN = ifᵐ-false (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)

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
            → (pSt : Paramˢ St) → (pM : Paramᶜ M)
            → ⟦ delay τ M ⟧ᶜᵗ pM ∘ᵐ ⟦ St ⟧ˢ pSt
            ≈ᵐ T-≤ q ∘ᵐ ((⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ St ⟨ of-natʳ τ ⟩ₛ ⟧ˢ pSt)
                          ⋄ (delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣))
sound-DELAY {ε = ε} τ St M q pSt pM =
  lhs≈ ∙ ≈ᵐ-sym (∘ᵐ-congʳ rhs≈ ∙ cancel)
  where
    g : ⟨ of-natʳ τ ⟩ᵒ ⟦ hist St ⟧ᶜᵗˣ →ᵐ Tᵒ _ ε
    g = ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ St ⟨ of-natʳ τ ⟩ₛ ⟧ˢ pSt

    -- the common normal form: delay the whole configuration
    nf : ⟦ hist St ⟧ᶜᵗˣ →ᵐ Tᵒ _ (of-natᵉ τ ·ₑ ε)
    nf = delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ g ∘ᵐ η⊣

    -- the source: `η⊣`-naturality absorbs the state into the boxed body
    lhs≈ : ⟦ delay τ M ⟧ᶜᵗ pM ∘ᵐ ⟦ St ⟧ˢ pSt ≈ᵐ nf
    lhs≈ =
      ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat (⟦ St ⟧ˢ pSt))))
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

sub-ren : ∀ {Γ Γ' A C} → (r : Ren [] Γ' Γ) → (N : Γ ∷ A ⊢C⦂ C) → (V : Γ' ⊢V⦂ A)
        → (pN : Paramᶜ N) → (pV : Paramᵛ V)
        → ⟦ C-rename (cong-∷-ren r) N [ split-[] ↦ V ]c ⟧ᶜᵗ
             (subᶜ (C-rename (cong-∷-ren r) N) split-[] V (renᶜ (cong-∷-ren r) N pN) pV)
        ≈ᵐ ⟦ N ⟧ᶜᵗ pN ∘ᵐ ⟨ ⟦ r ⟧ʳ , ⟦ V ⟧ᵛᵗ pV ⟩ᵐ
sub-ren r N V pN pV =
    C-subst-nat (C-rename (cong-∷-ren r) N) split-[] V (renᶜ (cong-∷-ren r) N pN) pV
  ∙ ∘ᵐ-congˡ (C-rename-nat (cong-∷-ren r) N pN)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)

-- THE `return` RULES
--
-- `⨟` and `handle` thread the environment through the strength in exactly the
-- same way, differing only in the algebra that collapses the two monad layers
-- (`μᵀ`, resp. the handler's `T-alg-of-handlerᵀ`). Both algebras compute on a
-- returned value the same way, so `SEQ-RET` and `HANDLE-RET` share one proof.

-- The parametricity certificate of the `return`-rules' reduct: the sequel
-- renamed by the re-locking renaming, then substituted into.
ret-subᴾ : ∀ {Γ A B ε} → (V : Γ ⊢V⦂ A) → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
         → Paramᵛ V → Paramᶜ N
         → Paramᶜ (C-rename (cong-∷-ren (eq-ren (cong (Γ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N
                     [ split-[] ↦ V ]c)
ret-subᴾ {Γ} V N pV pN =
  subᶜ (C-rename (cong-∷-ren (eq-ren (cong (Γ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N)
       split-[] V
    (renᶜ (cong-∷-ren (eq-ren (cong (Γ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N pN) pV

ret-step : ∀ {Γ A B ε}
         → (alg : Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε) uₑ →ᵐ Tᵒ ⟦ B ⟧ᵛ (uₑ ·ₑ ε))
         → (alg-η : alg ∘ᵐ ηᵀ ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε)))
         → (V : Γ ⊢V⦂ A)
         → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
         → (pV : Paramᵛ V) → (pN : Paramᶜ N)
         → alg ∘ᵐ Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ pV ⟩ᵐ
         ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε))
            ∘ᵐ ⟦ C-rename (cong-∷-ren (eq-ren (cong (Γ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N
                   [ split-[] ↦ V ]c ⟧ᶜᵗ (ret-subᴾ V N pV pN)
ret-step {Γ} alg alg-η V N pV pN =
    ∘ᵐ-congʳ ret-massage
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ alg-η
  where
    -- the environment-threading part (independent of the algebra): the returned
    -- value's `ηᵀ` opens the boxed environment (`strᵀ-ηᵀ`), which is exactly the
    -- syntax's re-locking renaming (`ret-env`), leaving `ηᵀ ∘ (renamed subst)`.
    ret-massage : Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ pV ⟩ᵐ
                ≈ᵐ ηᵀ ∘ᵐ ⟦ C-rename (cong-∷-ren (eq-ren (cong (Γ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N
                            [ split-[] ↦ V ]c ⟧ᶜᵗ (ret-subᴾ V N pV pN)
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
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ηᵀ-nat (⟦ N ⟧ᶜᵗ pN)))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (sub-ren (eq-ren (cong (Γ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren) N V pN pV))

-- `ret-step`, threaded with an eternal parameter `P` supplied by `pv`. The
-- handler's algebra reads its clause-context off `P` (`= ⟦ Γ ⟨ ⊤ᵣ ⟩ ⟧`, via
-- `⟨⊤⟩-η`); the `ηᵀ` law discards it (`sndᵐ`), so returning ignores `P`.
ret-step-P : ∀ {Γ A B ε P}
           → (pv : ⟦ Γ ⟧ᶜᵗˣ →ᵐ P)
           → (alg : P ×ᵐ Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε) uₑ →ᵐ Tᵒ ⟦ B ⟧ᵛ (uₑ ·ₑ ε))
           → (alg-η : alg ∘ᵐ mapˣᵐ idᵐ (ηᵀ {Tᵒ ⟦ B ⟧ᵛ ε})
                    ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε)) ∘ᵐ sndᵐ)
           → (V : Γ ⊢V⦂ A)
           → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
           → (pV : Paramᵛ V) → (pN : Paramᶜ N)
           → alg ∘ᵐ ⟨ pv , Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ pV ⟩ᵐ ⟩ᵐ
           ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε))
              ∘ᵐ ⟦ C-rename (cong-∷-ren (eq-ren (cong (Γ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N
                     [ split-[] ↦ V ]c ⟧ᶜᵗ (ret-subᴾ V N pV pN)
ret-step-P {Γ} pv alg alg-η V N pV pN =
    ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ret-massage ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ alg-η
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
  where
    ret-massage : Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ pV ⟩ᵐ
                ≈ᵐ ηᵀ ∘ᵐ ⟦ C-rename (cong-∷-ren (eq-ren (cong (Γ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N
                            [ split-[] ↦ V ]c ⟧ᶜᵗ (ret-subᴾ V N pV pN)
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
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ηᵀ-nat (⟦ N ⟧ᶜᵗ pN)))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (sub-ren (eq-ren (cong (Γ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren) N V pN pV))

-- SEQ-RET and HANDLE-RET: the two instances of `ret-step`, one for the monad
-- multiplication and one for the handler's algebra.

sound-SEQ-RET : ∀ {Γ A B ε} → (V : Γ ⊢V⦂ A) → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
              → (pV : Paramᵛ V) → (pN : Paramᶜ N)
              → ⟦ return V ⨟ N ⟧ᶜᵗ (pV , pN)
              ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε))
                 ∘ᵐ ⟦ C-rename (cong-∷-ren (eq-ren (cong (Γ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N
                        [ split-[] ↦ V ]c ⟧ᶜᵗ (ret-subᴾ V N pV pN)
sound-SEQ-RET V N pV pN = ret-step μᵀ T-μ∘η≡id V N pV pN

sound-HANDLE-RET : ∀ {Γ A B ε}
                 → (V : Γ ⊢V⦂ A)
                 → (H : (op : Op) → (ε'' : E)
                      → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                           ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                        ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                 → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
                 → (pV : Paramᵛ V) → (pN : Paramᶜ N)
                 → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
                 → (uH : EffUniformʰ {Γ} H pH)
                 → ⟦ handle return V `with H `in N ⟧ᶜᵗ (pV , pN , pH , uH)
                 ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε))
                    ∘ᵐ ⟦ C-rename (cong-∷-ren (eq-ren (cong (Γ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N
                           [ split-[] ↦ V ]c ⟧ᶜᵗ (ret-subᴾ V N pV pN)
sound-HANDLE-RET {Γ} V H N pV pN pH uH =
  ret-step-P ⟨⊤⟩-η (T-alg-of-handlerᵀ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H pH uH))
             (T-alg-of-handlerᵀ-ηᵀ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H pH uH)) V N pV pN

