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

module MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Base
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

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Language.Comparisons using (Cmp; holds)
open import MonomorphicCalculus.Syntax.Data S using (compareᵈ)
open import MonomorphicCalculus.Syntax.Types S
open import MonomorphicCalculus.Syntax.Contexts  S
open import MonomorphicCalculus.Syntax.Terms  S
open import MonomorphicCalculus.Syntax.Renaming  S
open import MonomorphicCalculus.Syntax.Renaming.Action S using (V-rename; C-rename; var-rename)
open import MonomorphicCalculus.Syntax.Substitution  S
open import MonomorphicCalculus.Syntax.Substitution.Subsumption  S

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
open Adjunction Adj using (η⊣; η⊣-nat; η⊣-u; η⊣-≤; η⊣-δ; η⊣-monoidal;
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
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Recursion S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Comparisons S Cat Fut Pst Adj GTy Mon GE
  using (⌜_⌝ᵈ; ⌜⌝ᵈ-coe)
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Data S Cat Fut Pst Adj GTy Mon GE

open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj
       using (Eternalᵒ; ⟨⊤⟩-eternalᵒ; ⟨⊤⟩-η)

-- The `Eternalᵒ` on `⟦ Γ ⟨ ⊤ᵣ ⟩ ⟧` carried by every `handle` interpretation: the
-- eternal-parameter object of the handler's fold, free on `⟦ Γ ⟧`.
bcᴱ : ∀ (Γ : Ctx) → Eternalᵒ ⟦ Γ ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ
bcᴱ Γ = ⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ

-- The computation, with its context plugged by the state.

Paramᶜᶠ : ∀ {C} → Config C → Set
Paramᶜᶠ ⟨ St , M ⟩ = Paramˢ St × Paramᶜ M

⟦_⟧ᶜᶠ : ∀ {C} → (cf : Config C) → Paramᶜᶠ cf
      → ⟦ hist (Config.state cf) ⟧ᶜᵗˣ →ᵐ ⟦ C ⟧ᶜ
⟦ ⟨ St , M ⟩ ⟧ᶜᶠ (pSt , pM) = ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ St ⟧ˢ pSt

-- The state's certificate across a step. Only `BOX` changes it: the cell it
-- allocates stores the boxed value, whose certificate is the term's,
-- renamed. Every other rule either keeps the state or only locks it, and the
-- two congruences inherit the sub-step's.

stepᴾˢ : ∀ {ε ε' A B} {S S' : 𝕊 []}
       → {M : toCtx S ⊢C⦂ A ‼ ε} → {M' : toCtx S' ⊢C⦂ B ‼ ε'}
       → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩) → Paramˢ S → Paramᶜ M → Paramˢ S'
stepᴾˢ APP                 pS _              = pS
stepᴾˢ MATCH               pS _              = pS
stepᴾˢ CASEL               pS _              = pS
stepᴾˢ RECL                pS _              = pS
stepᴾˢ IF-TRUE             pS _              = pS
stepᴾˢ CMP                 pS _              = pS
stepᴾˢ IF-FALSE            pS _              = pS
stepᴾˢ CASE+               pS _              = pS
stepᴾˢ CASEℕ-ZERO          pS _              = pS
stepᴾˢ CASEℕ-SUCC          pS _              = pS
stepᴾˢ RECℕ-ZERO           pS _              = pS
stepᴾˢ RECℕ-SUCC           pS _              = pS
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
stepᴾˢ SUB-APP             pS _              = pS
stepᴾˢ SUB-HANDLE          pS _              = pS
stepᴾˢ SUB-HANDLE-TRANS    pS _              = pS
stepᴾˢ SUB-IF              pS _              = pS
stepᴾˢ SUB-CASEℕ           pS _              = pS
stepᴾˢ SUB-RECℕ            pS _              = pS
stepᴾˢ SUB                 pS _              = pS

-- Kleisli composition with a time transition: running a computation over
-- the later history, after the transition that produces it.

_⋄_ : ∀ {X Y A ε ε'}
    → (Y →ᵐ Tᵒ A ε')
    → (X →ᵐ Tᵒ Y ε)
    → X →ᵐ Tᵒ A (ε ·ₑ ε')
f ⋄ t = μᵀ ∘ᵐ Tᶠ f ∘ᵐ t

infixl 25 _⋄_

-- A step's effect. Only `DELAY` does anything: it is the sole rule that
-- advances time, by exactly its own delay. Resources (cells) are allocated
-- into the *shape* of the store, never into the effect grade, which is why
-- allocation contributes `uₑ`.

step-grade : ∀ {ε ε'} {St St' : 𝕊 []} {A B : VType}
           → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ B ‼ ε'}
           → ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩
           → E
step-grade APP                  = uₑ
step-grade MATCH                = uₑ
step-grade CASEL                = uₑ
step-grade RECL                 = uₑ
step-grade IF-TRUE              = uₑ
step-grade CMP                  = uₑ
step-grade IF-FALSE             = uₑ
step-grade CASE+                = uₑ
step-grade CASEℕ-ZERO           = uₑ
step-grade CASEℕ-SUCC           = uₑ
step-grade RECℕ-ZERO            = uₑ
step-grade RECℕ-SUCC            = uₑ
step-grade (SEQ-STEP r _)       = step-grade r
step-grade SEQ-RET              = uₑ
step-grade SEQ-OP               = uₑ
step-grade (DELAY {τ = τ})      = of-durᵉ τ ·ₑ uₑ
step-grade HANDLE-RET           = uₑ
step-grade (HANDLE-STEP r _)    = step-grade r
step-grade HANDLE-OP            = uₑ
step-grade BOX                  = uₑ
step-grade UNBOX                = uₑ
step-grade SUB-APP              = uₑ
step-grade SUB-HANDLE           = uₑ
step-grade SUB-HANDLE-TRANS     = uₑ
step-grade SUB-IF               = uₑ
step-grade SUB-CASEℕ            = uₑ
step-grade SUB-RECℕ             = uₑ
step-grade SUB                  = uₑ

-- The transition itself. `DELAY` ticks: it names the present as the past of
-- every world one delay ahead (`η⊣`), and `delayᵀ` is what actually reaches
-- those worlds — this is the only way a lock can ever be produced.

stepᵀ : ∀ {ε ε'} {St St' : 𝕊 []} {A B : VType}
      → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ B ‼ ε'}
      → (r : ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩)
      → ⟦ hist St ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ hist St' ⟧ᶜᵗˣ (step-grade r)
stepᵀ APP               = ηᵀ
stepᵀ MATCH             = ηᵀ
stepᵀ CASEL             = ηᵀ
stepᵀ RECL              = ηᵀ
stepᵀ IF-TRUE           = ηᵀ
stepᵀ CMP               = ηᵀ
stepᵀ IF-FALSE          = ηᵀ
stepᵀ CASE+             = ηᵀ
stepᵀ CASEℕ-ZERO        = ηᵀ
stepᵀ CASEℕ-SUCC        = ηᵀ
stepᵀ RECℕ-ZERO         = ηᵀ
stepᵀ RECℕ-SUCC         = ηᵀ
stepᵀ (SEQ-STEP r _)    = stepᵀ r
stepᵀ SEQ-RET           = ηᵀ
stepᵀ SEQ-OP            = ηᵀ
stepᵀ (DELAY {τ = τ})   = delayᵀ τ ∘ᵐ [ of-durʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣
stepᵀ HANDLE-RET        = ηᵀ
stepᵀ (HANDLE-STEP r _) = stepᵀ r
stepᵀ HANDLE-OP         = ηᵀ
stepᵀ BOX               = ηᵀ
stepᵀ UNBOX             = ηᵀ
stepᵀ SUB-APP           = ηᵀ
stepᵀ SUB-HANDLE        = ηᵀ
stepᵀ SUB-HANDLE-TRANS  = ηᵀ
stepᵀ SUB-IF            = ηᵀ
stepᵀ SUB-CASEℕ         = ηᵀ
stepᵀ SUB-RECℕ          = ηᵀ
stepᵀ SUB               = ηᵀ

-- The step's effect, composed with the target's, refines the source's. This is
-- `step-grade-≾` in the effect grades.

step-≾ : ∀ {ε ε'} {St St' : 𝕊 []} {A B : VType}
       → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ B ‼ ε'}
       → (r : ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩)
       → step-grade r ·ₑ ε' ≾ₑ ε
step-≾ {ε = ε} APP    = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} MATCH  = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} CASEL  = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} RECL   = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} IF-TRUE  = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} CMP      = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} IF-FALSE = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} CASE+    = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} CASEℕ-ZERO = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} CASEℕ-SUCC = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} RECℕ-ZERO = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} RECℕ-SUCC = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ (SEQ-STEP {ε₂ = ε₂} {ε₃ = ε₃} r _) =
  ≾ₑ-trans
    (≃ₑ⇒≿ₑ (·ₑ-assoc (step-grade r) ε₃ ε₂))
    (·ₑ-monoˡ-≾ₑ (step-≾ r))
step-≾ SEQ-RET        = ≾ₑ-reflexive refl
step-≾ {ε = ε} SEQ-OP = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ (DELAY {τ = τ} {ε = ε}) =
  ≃ₑ⇒≾ₑ (·ₑ-cong (·ₑ-identityʳ (of-durᵉ τ)) ≃ₑ-refl)
step-≾ HANDLE-RET     = ≾ₑ-reflexive refl
step-≾ (HANDLE-STEP {ε₂ = ε₂} {ε₁' = ε₁'} r _) =
  ≾ₑ-trans
    (≃ₑ⇒≿ₑ (·ₑ-assoc (step-grade r) ε₁' ε₂))
    (·ₑ-monoˡ-≾ₑ (step-≾ r))
step-≾ (HANDLE-OP {ε = ε} {ε'' = ε''} {op = op}) =
  ≃ₑ⇒≾ₑ
    (≃ₑ-trans (·ₑ-identityˡ _) (≃ₑ-sym (·ₑ-assoc (op-grade op) ε ε'')))
step-≾ {ε = ε} BOX    = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} UNBOX   = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ (SUB-APP {r = _ ‼ₛ s}) = ≾ₑ-trans (≃ₑ⇒≾ₑ (·ₑ-identityˡ _)) s
step-≾ (SUB-HANDLE {q = _ ‼ₛ s}) =
  ≾ₑ-trans (≃ₑ⇒≾ₑ (·ₑ-identityˡ _)) (·ₑ-monoʳ-≾ₑ s)
step-≾ {ε = ε} SUB-HANDLE-TRANS = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} SUB-IF  = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} SUB-CASEℕ = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ {ε = ε} SUB-RECℕ = ≃ₑ⇒≾ₑ (·ₑ-identityˡ ε)
step-≾ (SUB {w = _ ‼ₛ q}) = ≾ₑ-trans (≃ₑ⇒≾ₑ (·ₑ-identityˡ _)) q

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
     → f ⋄ ηᵀ ≈ᵐ T-≤ (≃ₑ⇒≿ₑ (·ₑ-identityˡ ε')) ∘ᵐ f
⋄-ηᵀ f =
  ≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (ηᵀ-nat f)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ T-μ∘η≡id))

-- Every rule but `DELAY` leaves the history alone, transitioning by `ηᵀ`: the
-- soundness equation collapses to a plain equation between the two
-- denotations, coerced along the effect refinement (the `uₑ` that `ηᵀ`
-- contributes is absorbed by `T-≤`).

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
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                (∘ᵐ-congˡ (T-≤-trans (≃ₑ⇒≿ₑ (·ₑ-identityˡ ε')) q r)))))

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

-- Projecting out of a pair-typed value in a state context: the certificate
-- it transports, and the projection it denotes.

fstᵛᴾ : ∀ {Γ A B} → (St : 𝕊 Γ) → (P : toCtx St ⊢V⦂ A |×| B)
      → Paramᵛ P → Paramᵛ (fstᵛ {S = St} P)
fstᵛᴾ St (var f x)           pP        = ⊥-elim (⦉⦊-not-in-toCtx x)
fstᵛᴾ St ⦉ V , W ⦊           (pV , pW) = pV
fstᵛᴾ St (subV P (p |×|ₛ q)) pP        = fstᵛᴾ St P pP

sndᵛᴾ : ∀ {Γ A B} → (St : 𝕊 Γ) → (P : toCtx St ⊢V⦂ A |×| B)
      → Paramᵛ P → Paramᵛ (sndᵛ {S = St} P)
sndᵛᴾ St (var f x)           pP        = ⊥-elim (⦉⦊-not-in-toCtx x)
sndᵛᴾ St ⦉ V , W ⦊           (pV , pW) = pW
sndᵛᴾ St (subV P (p |×|ₛ q)) pP        = sndᵛᴾ St P pP

fstᵛ-sound : ∀ {Γ A B} → (St : 𝕊 Γ) → (P : toCtx St ⊢V⦂ A |×| B) → (pP : Paramᵛ P)
           → ⟦ fstᵛ {S = St} P ⟧ᵛᵗ (fstᵛᴾ St P pP) ≈ᵐ fstᵐ ∘ᵐ ⟦ P ⟧ᵛᵗ pP
fstᵛ-sound St (var f x)           pP        = ⊥-elim (⦉⦊-not-in-toCtx x)
fstᵛ-sound St ⦉ V , W ⦊           (pV , pW) = ≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)
fstᵛ-sound St (subV P (p |×|ₛ q)) pP        =
    ∘ᵐ-congʳ (fstᵛ-sound St P pP)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _))
  ∙ ∘ᵐ-assoc _ _ _

sndᵛ-sound : ∀ {Γ A B} → (St : 𝕊 Γ) → (P : toCtx St ⊢V⦂ A |×| B) → (pP : Paramᵛ P)
           → ⟦ sndᵛ {S = St} P ⟧ᵛᵗ (sndᵛᴾ St P pP) ≈ᵐ sndᵐ ∘ᵐ ⟦ P ⟧ᵛᵗ pP
sndᵛ-sound St (var f x)           pP        = ⊥-elim (⦉⦊-not-in-toCtx x)
sndᵛ-sound St ⦉ V , W ⦊           (pV , pW) = ≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _)
sndᵛ-sound St (subV P (p |×|ₛ q)) pP        =
    ∘ᵐ-congʳ (sndᵛ-sound St P pP)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _))
  ∙ ∘ᵐ-assoc _ _ _

-- MATCH: destructing a pair is substituting its two projections
-- (`C-subst₂-nat`), which denote its components.

sound-MATCH : ∀ {Γ A B C} → (St : 𝕊 Γ) → (P : toCtx St ⊢V⦂ A |×| B)
            → (M : toCtx St ∷ A ∷ B ⊢C⦂ C)
            → (pP : Paramᵛ P) → (pM : Paramᶜ M)
            → ⟦ match P `in M ⟧ᶜᵗ (pP , pM)
            ≈ᵐ ⟦ (M [ split-[] ↦ V-rename wk-ren (sndᵛ {S = St} P) ]c)
                   [ split-[] ↦ fstᵛ {S = St} P ]c ⟧ᶜᵗ
                 (subᶜ₂ M (fstᵛ {S = St} P) (sndᵛ {S = St} P) pM (fstᵛᴾ St P pP) (sndᵛᴾ St P pP))
sound-MATCH St P M pP pM =
    ∘ᵐ-congʳ (⟨ ⟨ ≈ᵐ-refl , ≈ᵐ-sym (fstᵛ-sound St P pP) ⟩ᵐ-cong
             , ≈ᵐ-sym (sndᵛ-sound St P pP) ⟩ᵐ-cong)
  ∙ ≈ᵐ-sym (C-subst₂-nat M (fstᵛ {S = St} P) (sndᵛ {S = St} P) pM (fstᵛᴾ St P pP) (sndᵛᴾ St P pP))

-- The decomposition of a list in a state context: the certificate it
-- transports, and the list it denotes, which is the list itself.

subLᴾ : ∀ {Γ A A₁} → (p : A₁ <:ᵛ A) → (l : ListView Γ A₁)
      → Paramᵛ (unlistᵛ l) → Paramᵛ (unlistᵛ (subL p l))
subLᴾ p (inj₁ tt)      _  = tt
subLᴾ p (inj₂ (W , L)) pl = pl

listᵛᴾ : ∀ {Γ A} → (St : 𝕊 Γ) → (V : toCtx St ⊢V⦂ |List| A)
       → Paramᵛ V → Paramᵛ (unlistᵛ (listᵛ {S = St} V))
listᵛᴾ St (var f x)            pV = ⊥-elim (|List|-not-in-toCtx x)
listᵛᴾ St nil                  pV = tt
listᵛᴾ St (cons V W)           pV = pV
listᵛᴾ St (subV V (|List|ₛ p)) pV = subLᴾ p (listᵛ V) (listᵛᴾ St V pV)

subL-sound : ∀ {Γ A A₁} → (p : A₁ <:ᵛ A) → (l : ListView Γ A₁)
           → (pl : Paramᵛ (unlistᵛ l))
           → ⟦ unlistᵛ (subL p l) ⟧ᵛᵗ (subLᴾ p l pl)
           ≈ᵐ mapListᵐ ⟦ p ⟧<:ᵛ ∘ᵐ ⟦ unlistᵛ l ⟧ᵛᵗ pl
subL-sound p (inj₁ tt)      _  =
  ≈ᵐ-sym (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (mapListᵐ-nil _))
subL-sound p (inj₂ (W , L)) pl =
  ≈ᵐ-sym ( ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
         ∙ ∘ᵐ-congˡ (mapListᵐ-cons _)
         ∙ ∘ᵐ-assoc _ _ _
         ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))

listᵛ-sound : ∀ {Γ A} → (St : 𝕊 Γ) → (V : toCtx St ⊢V⦂ |List| A) → (pV : Paramᵛ V)
            → ⟦ unlistᵛ (listᵛ {S = St} V) ⟧ᵛᵗ (listᵛᴾ St V pV) ≈ᵐ ⟦ V ⟧ᵛᵗ pV
listᵛ-sound St (var f x)            pV = ⊥-elim (|List|-not-in-toCtx x)
listᵛ-sound St nil                  pV = ≈ᵐ-refl
listᵛ-sound St (cons V W)           pV = ≈ᵐ-refl
listᵛ-sound St (subV V (|List|ₛ p)) pV =
    subL-sound p (listᵛ V) (listᵛᴾ St V pV)
  ∙ ∘ᵐ-congʳ (listᵛ-sound St V pV)

-- The reducts of the list eliminators, and their certificates.

caseL-reductᴾ : ∀ {Γ A C} → (l : ListView Γ A) → (M : Γ ⊢C⦂ C)
              → (N : Γ ∷ A ∷ |List| A ⊢C⦂ C)
              → Paramᵛ (unlistᵛ l) → Paramᶜ M → Paramᶜ N
              → Paramᶜ (caseL-reduct l M N)
caseL-reductᴾ (inj₁ tt)      M N pl         pM pN = pM
caseL-reductᴾ (inj₂ (W , L)) M N (pW , pL) pM pN = subᶜ₂ N W L pN pW pL

recL-reductᴾ : ∀ {Γ A B ε} → (l : ListView Γ A) → (M : Γ ⊢C⦂ B ‼ ε)
             → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
             → (p : ε ·ₑ ε ≾ₑ ε)
             → Paramᵛ (unlistᵛ l) → Paramᶜ M → Paramᶜ N
             → Paramᶜ (recL-reduct l M N p)
recL-reductᴾ (inj₁ tt)      M N p pl        pM pN = pM
recL-reductᴾ (inj₂ (W , L)) M N p (pW , pL) pM pN =
  (pL , pM , pN) , recL-stepᴾ W L N pW pL pN

-- The decomposition of a sum in a state context: the certificate it
-- transports, and the sum it denotes, which is the sum itself.

sub⊎ᴾ : ∀ {Γ A A₁ B B₁} → (p : A₁ <:ᵛ A) → (q : B₁ <:ᵛ B)
      → (s : (Γ ⊢V⦂ A₁) ⊎ (Γ ⊢V⦂ B₁))
      → Paramᵛ (uninjᵛ s) → Paramᵛ (uninjᵛ (sub⊎ p q s))
sub⊎ᴾ p q (inj₁ W) pW = pW
sub⊎ᴾ p q (inj₂ W) pW = pW

injᵛᴾ : ∀ {Γ A B} → (St : 𝕊 Γ) → (V : toCtx St ⊢V⦂ A |+| B)
      → Paramᵛ V → Paramᵛ (uninjᵛ (injᵛ {S = St} V))
injᵛᴾ St (var f x)           pV = ⊥-elim (|+|-not-in-toCtx x)
injᵛᴾ St (inl V)             pV = pV
injᵛᴾ St (inr V)             pV = pV
injᵛᴾ St (subV V (p |+|ₛ q)) pV = sub⊎ᴾ p q (injᵛ V) (injᵛᴾ St V pV)

sub⊎-sound : ∀ {Γ A A₁ B B₁} → (p : A₁ <:ᵛ A) → (q : B₁ <:ᵛ B)
           → (s : (Γ ⊢V⦂ A₁) ⊎ (Γ ⊢V⦂ B₁)) → (ps : Paramᵛ (uninjᵛ s))
           → ⟦ uninjᵛ (sub⊎ p q s) ⟧ᵛᵗ (sub⊎ᴾ p q s ps)
           ≈ᵐ map+ᵐ ⟦ p ⟧<:ᵛ ⟦ q ⟧<:ᵛ ∘ᵐ ⟦ uninjᵛ s ⟧ᵛᵗ ps
sub⊎-sound p q (inj₁ W) pW =
  ≈ᵐ-sym (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ ([]ᵐ-inlᵐ _ _) ∙ ∘ᵐ-assoc _ _ _)
sub⊎-sound p q (inj₂ W) pW =
  ≈ᵐ-sym (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ ([]ᵐ-inrᵐ _ _) ∙ ∘ᵐ-assoc _ _ _)

injᵛ-sound : ∀ {Γ A B} → (St : 𝕊 Γ) → (V : toCtx St ⊢V⦂ A |+| B) → (pV : Paramᵛ V)
           → ⟦ uninjᵛ (injᵛ {S = St} V) ⟧ᵛᵗ (injᵛᴾ St V pV) ≈ᵐ ⟦ V ⟧ᵛᵗ pV
injᵛ-sound St (var f x)           pV = ⊥-elim (|+|-not-in-toCtx x)
injᵛ-sound St (inl V)             pV = ≈ᵐ-refl
injᵛ-sound St (inr V)             pV = ≈ᵐ-refl
injᵛ-sound St (subV V (p |+|ₛ q)) pV =
  sub⊎-sound p q (injᵛ V) (injᵛᴾ St V pV) ∙ ∘ᵐ-congʳ (injᵛ-sound St V pV)

case+-reductᴾ : ∀ {Γ A B C} → (s : (Γ ⊢V⦂ A) ⊎ (Γ ⊢V⦂ B))
              → (M : Γ ∷ A ⊢C⦂ C) → (N : Γ ∷ B ⊢C⦂ C)
              → Paramᵛ (uninjᵛ s) → Paramᶜ M → Paramᶜ N
              → Paramᶜ (case+-reduct s M N)
case+-reductᴾ (inj₁ W) M N pW pM pN = subᶜ M split-[] W pM pW
case+-reductᴾ (inj₂ W) M N pW pM pN = subᶜ N split-[] W pN pW

-- CMP: a value of an eternal type denotes the point of its datum, at which
-- the comparison morphism orders as the data are ordered.

⌊⌋ᵈ-sound : ∀ {Γ A} → (St : 𝕊 Γ) → (et : Eternal A) → (V : toCtx St ⊢V⦂ A)
          → (pV : Paramᵛ V) → ⟦ V ⟧ᵛᵗ pV ≈ᵐ ⌜ et ⌝ᵈ (⌊_⌋ᵈ {S = St} et V) ∘ᵐ terminalᵐ
⌊⌋ᵈ-sound St et (var _ x) pV = ⊥-elim (eternal-not-in-toCtx et x)
⌊⌋ᵈ-sound St et (subV V p) pV =
    ∘ᵐ-congʳ (⌊⌋ᵈ-sound St (<:ᵛ-eternalˡ p et) V pV)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (⌜⌝ᵈ-coe p et _)
⌊⌋ᵈ-sound St (Baseₑ _) (const c) pV = ≈ᵐ-refl
⌊⌋ᵈ-sound St Unitₑ ⋆ pV = ≈ᵐ-sym terminalᵐ-unique
⌊⌋ᵈ-sound St Boolₑ true pV = ≈ᵐ-refl
⌊⌋ᵈ-sound St Boolₑ false pV = ≈ᵐ-refl
⌊⌋ᵈ-sound St Natₑ zero pV = ≈ᵐ-refl
⌊⌋ᵈ-sound St Natₑ (succ V) pV =
  ∘ᵐ-congʳ (⌊⌋ᵈ-sound St Natₑ V pV) ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
⌊⌋ᵈ-sound St (et₁ |×|ₑ et₂) ⦉ V , W ⦊ (pV , pW) =
  ⟨ ⌊⌋ᵈ-sound St et₁ V pV , ⌊⌋ᵈ-sound St et₂ W pW ⟩ᵐ-cong ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)
⌊⌋ᵈ-sound St (et₁ |+|ₑ et₂) (inl V) pV =
  ∘ᵐ-congʳ (⌊⌋ᵈ-sound St et₁ V pV) ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
⌊⌋ᵈ-sound St (et₁ |+|ₑ et₂) (inr V) pV =
  ∘ᵐ-congʳ (⌊⌋ᵈ-sound St et₂ V pV) ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
⌊⌋ᵈ-sound St (|List|ₑ et) nil pV = ≈ᵐ-refl
⌊⌋ᵈ-sound St (|List|ₑ et) (cons V W) (pV , pW) =
    ∘ᵐ-congʳ (⟨ ⌊⌋ᵈ-sound St et V pV , ⌊⌋ᵈ-sound St (|List|ₑ et) W pW ⟩ᵐ-cong
              ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

cmp-reductᴾ : ∀ {Γ A} → (St : 𝕊 Γ) → (⋈ : Cmp) → (V W : toCtx St ⊢V⦂ A) → (et : Eternal A)
            → Paramᶜ (cmp-reduct {S = St} ⋈ V W et)
cmp-reductᴾ St ⋈ V W et =
  param-⌈⌉ Boolₑ (holds ⋈ (compareᵈ et (⌊_⌋ᵈ {S = St} et V) (⌊_⌋ᵈ {S = St} et W)))

sound-CMP : ∀ {Γ A} → (St : 𝕊 Γ) → (⋈ : Cmp) → (V W : toCtx St ⊢V⦂ A) → (et : Eternal A)
          → (pV : Paramᵛ V) → (pW : Paramᵛ W)
          → ⟦ cmp ⋈ V W et ⟧ᶜᵗ (pV , pW)
          ≈ᵐ ⟦ cmp-reduct {S = St} ⋈ V W et ⟧ᶜᵗ (cmp-reductᴾ St ⋈ V W et)
sound-CMP St ⋈ V W et pV pW =
  sound-cmp ⋈ et V W pV pW _ _ (⌊⌋ᵈ-sound St et V pV) (⌊⌋ᵈ-sound St et W pW)

-- CASEL / RECL: the scrutinee denotes its decomposition, at which the beta
-- laws apply.

sound-CASEL : ∀ {Γ A C} → (St : 𝕊 Γ) → (V : toCtx St ⊢V⦂ |List| A)
            → (M : toCtx St ⊢C⦂ C) → (N : toCtx St ∷ A ∷ |List| A ⊢C⦂ C)
            → (pV : Paramᵛ V) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
            → ⟦ caseL V `nil M `cons N ⟧ᶜᵗ (pV , pM , pN)
            ≈ᵐ ⟦ caseL-reduct (listᵛ {S = St} V) M N ⟧ᶜᵗ
                 (caseL-reductᴾ (listᵛ V) M N (listᵛᴾ St V pV) pM pN)
sound-CASEL St V M N pV pM pN =
    caseLᵐ-cong (≈ᵐ-sym (listᵛ-sound St V pV)) ≈ᵐ-refl ≈ᵐ-refl
  ∙ go (listᵛ V) (listᵛᴾ St V pV)
  where
    go : (l : ListView (toCtx St) _) → (pl : Paramᵛ (unlistᵛ l))
       → ⟦ caseL (unlistᵛ l) `nil M `cons N ⟧ᶜᵗ (pl , pM , pN)
       ≈ᵐ ⟦ caseL-reduct l M N ⟧ᶜᵗ (caseL-reductᴾ l M N pl pM pN)
    go (inj₁ tt)      pl        = sound-CASEL-NIL M N pM pN
    go (inj₂ (W , L)) (pW , pL) = sound-CASEL-CONS W L M N pW pL pM pN

sound-RECL : ∀ {Γ A B ε} → (St : 𝕊 Γ) → (V : toCtx St ⊢V⦂ |List| A)
           → (M : toCtx St ⊢C⦂ B ‼ ε)
           → (N : (toCtx St ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
           → (p : ε ·ₑ ε ≾ₑ ε)
           → (pV : Paramᵛ V) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
           → ⟦ recL V M N p ⟧ᶜᵗ (pV , pM , pN)
           ≈ᵐ ⟦ recL-reduct (listᵛ {S = St} V) M N p ⟧ᶜᵗ
                (recL-reductᴾ (listᵛ V) M N p (listᵛᴾ St V pV) pM pN)
sound-RECL St V M N p pV pM pN =
    ∘ᵐ-congʳ ⟨ ≈ᵐ-refl , ≈ᵐ-sym (listᵛ-sound St V pV) ⟩ᵐ-cong
  ∙ go (listᵛ V) (listᵛᴾ St V pV)
  where
    go : (l : ListView (toCtx St) _) → (pl : Paramᵛ (unlistᵛ l))
       → ⟦ recL (unlistᵛ l) M N p ⟧ᶜᵗ (pl , pM , pN)
       ≈ᵐ ⟦ recL-reduct l M N p ⟧ᶜᵗ (recL-reductᴾ l M N p pl pM pN)
    go (inj₁ tt)      pl        = sound-RECL-NIL M N p pM pN
    go (inj₂ (W , L)) (pW , pL) = sound-RECL-CONS W L M N p pW pL pM pN

-- CASE+: the scrutinee denotes its decomposition, at which the coproduct's
-- beta laws apply.

sound-CASE+ : ∀ {Γ A B C} → (St : 𝕊 Γ) → (V : toCtx St ⊢V⦂ A |+| B)
            → (M : toCtx St ∷ A ⊢C⦂ C) → (N : toCtx St ∷ B ⊢C⦂ C)
            → (pV : Paramᵛ V) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
            → ⟦ case+ V `inl M `inr N ⟧ᶜᵗ (pV , pM , pN)
            ≈ᵐ ⟦ case+-reduct (injᵛ {S = St} V) M N ⟧ᶜᵗ
                 (case+-reductᴾ (injᵛ V) M N (injᵛᴾ St V pV) pM pN)
sound-CASE+ St V M N pV pM pN =
    caseᵐ-cong (≈ᵐ-sym (injᵛ-sound St V pV)) ≈ᵐ-refl ≈ᵐ-refl
  ∙ go (injᵛ V) (injᵛᴾ St V pV)
  where
    go : (s : (toCtx St ⊢V⦂ _) ⊎ (toCtx St ⊢V⦂ _)) → (ps : Paramᵛ (uninjᵛ s))
       → ⟦ case+ uninjᵛ s `inl M `inr N ⟧ᶜᵗ (ps , pM , pN)
       ≈ᵐ ⟦ case+-reduct s M N ⟧ᶜᵗ (case+-reductᴾ s M N ps pM pN)
    go (inj₁ W) pW = caseᵐ-inl _ _ _ ∙ ≈ᵐ-sym (C-subst-nat M split-[] W pM pW)
    go (inj₂ W) pW = caseᵐ-inr _ _ _ ∙ ≈ᵐ-sym (C-subst-nat N split-[] W pN pW)

-- BOX: allocating a resource and extending the store are the *same* morphism,
-- so the two configurations' denotations coincide outright. The stored value
-- is the boxed one reindexed along `[] ++ᶜ Γ ≡ Γ`, which cancels.

sound-BOX : ∀ {A B ρ ε} → (St : 𝕊 []) → (V : toCtx St ⟨ ρ ⟩ ⊢V⦂ A)
          → (M : toCtx St ∷ [ ρ ] A ⊢C⦂ B ‼ ε)
          → (pSt : Paramˢ St) → (pV : Paramᵛ V) → (pM : Paramᶜ M)
          → ⟦ box _ V M ⟧ᶜᵗ (pV , pM) ∘ᵐ ⟦ St ⟧ˢ pSt
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

-- Applying a reindexed abstraction: the codomain half of the reindexing comes
-- out in front, the domain half lands on the argument.

app-map⇒ᵐ : ∀ {X A A' B B'} → (f : A' →ᵐ A) → (g : B →ᵐ B')
          → (h : X →ᵐ A ⇒ᵐ B) → (k : X →ᵐ A')
          → appᵐ ∘ᵐ ⟨ map⇒ᵐ f g ∘ᵐ h , k ⟩ᵐ ≈ᵐ g ∘ᵐ appᵐ ∘ᵐ ⟨ h , f ∘ᵐ k ⟩ᵐ
app-map⇒ᵐ f g h k =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ (map⇒ᵐ f g) idᵐ h k
                      ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (uncurryᵐ-nat (map⇒ᵐ f g) idᵐ))
  ∙ ∘ᵐ-congˡ (uncurryᵐ-cong (∘ᵐ-identityˡ _))
  ∙ ∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ idᵐ f h k ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))

-- SUB-APP: the subsumption at an eliminated function splits, its codomain
-- half becoming the step's own refinement.

sound-SUB-APP : ∀ {Γ A A₁ C C₁} → (V : Γ ⊢V⦂ A₁ ⇒ C₁) → (W : Γ ⊢V⦂ A)
              → (q : A <:ᵛ A₁) → (r : C₁ <:ᶜ C)
              → (pV : Paramᵛ V) → (pW : Paramᵛ W)
              → ⟦ subV V (q ⇒ₛ r) · W ⟧ᶜᵗ (pV , pW)
              ≈ᵐ ⟦ r ⟧<:ᶜ ∘ᵐ ⟦ V · subV W q ⟧ᶜᵗ (pV , pW)
sound-SUB-APP V W q r pV pW =
  app-map⇒ᵐ ⟦ q ⟧<:ᵛ ⟦ r ⟧<:ᶜ (⟦ V ⟧ᵛᵗ pV) (⟦ W ⟧ᵛᵗ pW)

-- SUB-IF: `Bool <:ᵛ Bool` denotes the identity.

sound-SUB-IF : ∀ {Γ C} → (V : Γ ⊢V⦂ Bool) → (M N : Γ ⊢C⦂ C)
             → (pV : Paramᵛ V) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
             → ⟦ if subV V Boolₛ `then M `else N ⟧ᶜᵗ (pV , pM , pN)
             ≈ᵐ ⟦ if V `then M `else N ⟧ᶜᵗ (pV , pM , pN)
sound-SUB-IF V M N pV pM pN = ifᵐ-cong (∘ᵐ-identityˡ _) ≈ᵐ-refl ≈ᵐ-refl

-- Transporting a composite along an equality of the domain's second factor.

subst-∘ᵐ : ∀ {X Y Z} {O O' : Obj} → (e : O ≡ O') → (g : Y →ᵐ Z) → (f : X ×ᵐ O →ᵐ Y)
         → subst (λ P → X ×ᵐ P →ᵐ Z) e (g ∘ᵐ f)
         ≈ᵐ g ∘ᵐ subst (λ P → X ×ᵐ P →ᵐ Y) e f
subst-∘ᵐ refl g f = ≈ᵐ-refl

-- A step's value refinement, at a type it does not move, denotes the identity.

T⟦⟧<:ᵛ-id : ∀ {A ε} → (t : A <:ᵛ A) → Tᶠ {⟦ A ⟧ᵛ} {⟦ A ⟧ᵛ} {ε} ⟦ t ⟧<:ᵛ ≈ᵐ idᵐ
T⟦⟧<:ᵛ-id t = T-congᶠ (⟦⟧<:ᵛ-id t) ∙ T-idᵐ

insert-coe : ∀ {X A ε} {h : X →ᵐ Tᵒ ⟦ A ⟧ᵛ ε} → (t : A <:ᵛ A)
           → h ≈ᵐ Tᶠ ⟦ t ⟧<:ᵛ ∘ᵐ h
insert-coe {h = h} t = ≈ᵐ-sym (∘ᵐ-congˡ (T⟦⟧<:ᵛ-id t) ∙ ∘ᵐ-identityˡ h)

-- The unit step, with the step's value refinement in front: the same shape as
-- `pure-step`, with the coercion passing the sub-effecting by naturality.

pure-step<: : ∀ {X A B ε ε'}
            → (q : uₑ ·ₑ ε' ≾ₑ ε) → (t : B <:ᵛ A)
            → {f : X →ᵐ Tᵒ ⟦ A ⟧ᵛ ε} → {g : X →ᵐ Tᵒ ⟦ B ⟧ᵛ ε'}
            → (r : ε' ≾ₑ ε)
            → f ≈ᵐ T-≤ r ∘ᵐ Tᶠ ⟦ t ⟧<:ᵛ ∘ᵐ g
            → f ≈ᵐ T-≤ q ∘ᵐ Tᶠ ⟦ t ⟧<:ᵛ ∘ᵐ (g ⋄ ηᵀ)
pure-step<: {ε' = ε'} q t {f} {g} r e =
    e
  ∙ ≈ᵐ-sym
      (  ∘ᵐ-congʳ (∘ᵐ-congʳ (⋄-ηᵀ g))
       ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
       ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-nat ⟦ t ⟧<:ᵛ uₑ·ε'≾ε'))
       ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
       ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
       ∙ ∘ᵐ-congˡ (T-≤-trans uₑ·ε'≾ε' q r))
  where
    uₑ·ε'≾ε' : ε' ≾ₑ uₑ ·ₑ ε'
    uₑ·ε'≾ε' = ≃ₑ⇒≿ₑ (·ₑ-identityˡ ε')

-- A functorial action escapes a bind, by naturality of the multiplication.

Tᶠ-bind : ∀ {X Y A B ε ε'} → (h : A →ᵐ B) → (g : Y →ᵐ Tᵒ A ε') → (s : X →ᵐ Tᵒ Y ε)
        → (Tᶠ h ∘ᵐ g) ⋄ s ≈ᵐ Tᶠ h ∘ᵐ (g ⋄ s)
Tᶠ-bind h g s =
    ∘ᵐ-congʳ (∘ᵐ-congˡ (T-∘ᵐ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (μᵀ-nat h)
  ∙ ∘ᵐ-assoc _ _ _

-- Subsuming a binder is a weakening followed by substituting the subsumed
-- variable, so its certificate and its denotation come from those two.

subCtxᴾ : ∀ {Γ A A₀ C} → (t : A₀ <:ᵛ A) → (N : Γ ∷ A ⊢C⦂ C) → Paramᶜ N
        → Paramᶜ (subCtx t N)
subCtxᴾ t N pN =
  subᶜ (C-rename (cong-∷-ren wk-ren) N) split-[]
       (subV (var (λ _ → ≾ᵣ-refl) Hd) t)
       (renᶜ (cong-∷-ren wk-ren) N pN) tt

subCtx-nat : ∀ {Γ A A₀ C} → (t : A₀ <:ᵛ A) → (N : Γ ∷ A ⊢C⦂ C) → (pN : Paramᶜ N)
           → ⟦ subCtx t N ⟧ᶜᵗ (subCtxᴾ t N pN)
           ≈ᵐ ⟦ N ⟧ᶜᵗ pN ∘ᵐ mapˣᵐ idᵐ ⟦ t ⟧<:ᵛ
subCtx-nat {Γ} {A} {A₀} t N pN =
    C-subst-nat (C-rename (cong-∷-ren wk-ren) N) split-[]
                (subV (var (λ _ → ≾ᵣ-refl) Hd) t)
                (renᶜ (cong-∷-ren wk-ren) N pN) tt
  ∙ ∘ᵐ-congˡ (C-rename-nat (cong-∷-ren wk-ren) N pN)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ ∘ᵐ-identityʳ _ ∙ ≈ᵐ-sym (∘ᵐ-identityˡ _)
                , ∘ᵐ-identityˡ _ ∙ ∘ᵐ-congʳ (var-morphism-Hd {Γ} {A₀} _) ⟩ᵐ-cong)

-- IF-TRUE / IF-FALSE: taking a branch is the boolean object's beta law.

sound-IF-TRUE : ∀ {Γ C} → (M N : Γ ⊢C⦂ C) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
              → ⟦ if true `then M `else N ⟧ᶜᵗ (tt , pM , pN) ≈ᵐ ⟦ M ⟧ᶜᵗ pM
sound-IF-TRUE M N pM pN = ifᵐ-true (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)

sound-IF-FALSE : ∀ {Γ C} → (M N : Γ ⊢C⦂ C) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
               → ⟦ if false `then M `else N ⟧ᶜᵗ (tt , pM , pN) ≈ᵐ ⟦ N ⟧ᶜᵗ pN
sound-IF-FALSE M N pM pN = ifᵐ-false (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)

-- CASEℕ-ZERO / CASEℕ-SUCC: taking a branch is a beta law of `caseℕᵐ`, the
-- successor's followed by the substitution coherence.

sound-CASEℕ-ZERO : ∀ {Γ C} → (M : Γ ⊢C⦂ C) → (N : Γ ∷ Nat ⊢C⦂ C)
                 → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                 → ⟦ caseℕ zero `zero M `succ N ⟧ᶜᵗ (tt , pM , pN) ≈ᵐ ⟦ M ⟧ᶜᵗ pM
sound-CASEℕ-ZERO M N pM pN = caseℕᵐ-zero (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)

sound-CASEℕ-SUCC : ∀ {Γ C} → (V : Γ ⊢V⦂ Nat)
                 → (M : Γ ⊢C⦂ C) → (N : Γ ∷ Nat ⊢C⦂ C)
                 → (pV : Paramᵛ V) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                 → ⟦ caseℕ succ V `zero M `succ N ⟧ᶜᵗ (pV , pM , pN)
                 ≈ᵐ ⟦ N [ split-[] ↦ V ]c ⟧ᶜᵗ (subᶜ N split-[] V pN pV)
sound-CASEℕ-SUCC V M N pV pM pN =
    caseℕᵐ-succ (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  ∙ ≈ᵐ-sym (C-subst-nat N split-[] V pN pV)

-- SUB-CASEℕ: `Nat <:ᵛ Nat` denotes the identity.

sound-SUB-CASEℕ : ∀ {Γ C} → (V : Γ ⊢V⦂ Nat)
                → (M : Γ ⊢C⦂ C) → (N : Γ ∷ Nat ⊢C⦂ C)
                → (pV : Paramᵛ V) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                → ⟦ caseℕ subV V Natₛ `zero M `succ N ⟧ᶜᵗ (pV , pM , pN)
                ≈ᵐ ⟦ caseℕ V `zero M `succ N ⟧ᶜᵗ (pV , pM , pN)
sound-SUB-CASEℕ V M N pV pM pN = caseℕᵐ-cong (∘ᵐ-identityˡ _) ≈ᵐ-refl ≈ᵐ-refl

-- SUB-RECℕ: `Nat <:ᵛ Nat` denotes the identity.

sound-SUB-RECℕ : ∀ {Γ B ε} → (V : Γ ⊢V⦂ Nat) → (M : Γ ⊢C⦂ B ‼ ε)
               → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
               → (p : ε ·ₑ ε ≾ₑ ε)
               → (pV : Paramᵛ V) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
               → ⟦ recℕ (subV V Natₛ) M N p ⟧ᶜᵗ (pV , pM , pN)
               ≈ᵐ ⟦ recℕ V M N p ⟧ᶜᵗ (pV , pM , pN)
sound-SUB-RECℕ V M N p pV pM pN = ∘ᵐ-congʳ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong

delayᵀ-ε-substᵀ : ∀ {A ε ε'} → (τ : 𝔻) → (e : ε ≡ ε')
                → delayᵀ {A} {ε'} τ ∘ᵐ [ of-durʳ τ ]ᶠ (ε-substᵀ e)
                ≈ᵐ ε-substᵀ (cong (of-durᵉ τ ·ₑ_) e) ∘ᵐ delayᵀ {A} {ε} τ
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
-- The only rule that advances time, and the only one whose history grows. The
-- state's interpretation passes under the new lock
-- (`⟦ St ⟨ ρ ⟩ₛ ⟧ˢ = ⟨ ρ ⟩ᶠ ⟦ St ⟧ˢ`), and `delayᵀ`'s algebraicity
-- re-associates the transition's `delayᵀ` out.

sound-DELAY : ∀ {A ε} → (τ : 𝔻) → (St : 𝕊 [])
            → (M : toCtx St ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε)
            → (q : (of-durᵉ τ ·ₑ uₑ) ·ₑ ε ≾ₑ of-durᵉ τ ·ₑ ε)
            → (pSt : Paramˢ St) → (pM : Paramᶜ M)
            → ⟦ delay τ M ⟧ᶜᵗ pM ∘ᵐ ⟦ St ⟧ˢ pSt
            ≈ᵐ T-≤ q ∘ᵐ ((⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ St ⟨ of-durʳ τ ⟩ₛ ⟧ˢ pSt)
                          ⋄ (delayᵀ τ ∘ᵐ [ of-durʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣))
sound-DELAY {ε = ε} τ St M q pSt pM =
  lhs≈ ∙ ≈ᵐ-sym (∘ᵐ-congʳ rhs≈ ∙ cancel)
  where
    g : ⟨ of-durʳ τ ⟩ᵒ ⟦ hist St ⟧ᶜᵗˣ →ᵐ Tᵒ _ ε
    g = ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ St ⟨ of-durʳ τ ⟩ₛ ⟧ˢ pSt

    -- the common normal form: delay the whole configuration
    nf : ⟦ hist St ⟧ᶜᵗˣ →ᵐ Tᵒ _ (of-durᵉ τ ·ₑ ε)
    nf = delayᵀ τ ∘ᵐ [ of-durʳ τ ]ᶠ g ∘ᵐ η⊣

    -- the source: `η⊣`-naturality absorbs the state into the boxed body
    lhs≈ : ⟦ delay τ M ⟧ᶜᵗ pM ∘ᵐ ⟦ St ⟧ˢ pSt ≈ᵐ nf
    lhs≈ =
      ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat (⟦ St ⟧ˢ pSt))))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))

    d : ε ≾ₑ uₑ ·ₑ ε
    d = ≃ₑ⇒≿ₑ (·ₑ-identityˡ ε)

    c : of-durᵉ τ ·ₑ (uₑ ·ₑ ε) ≾ₑ (of-durᵉ τ ·ₑ uₑ) ·ₑ ε
    c = ≃ₑ⇒≿ₑ (·ₑ-assoc (of-durᵉ τ) uₑ ε)

    X : of-durᵉ τ ·ₑ ε ≾ₑ (of-durᵉ τ ·ₑ uₑ) ·ₑ ε
    X = ≾ₑ-trans (·ₑ-monoʳ-≾ₑ d) c

    -- the target: `delayᵀ` is natural, then algebraic; the leftover unit
    -- laws are pure transports
    rhs≈ : (g ⋄ (delayᵀ τ ∘ᵐ [ of-durʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣))
         ≈ᵐ T-≤ c ∘ᵐ T-≤ (·ₑ-monoʳ-≾ₑ d) ∘ᵐ nf
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
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (delayᵀ-≤ τ d))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)

    cancel : T-≤ q ∘ᵐ (T-≤ c ∘ᵐ T-≤ (·ₑ-monoʳ-≾ₑ d) ∘ᵐ nf)
           ≈ᵐ nf
    cancel =
      ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (T-≤-trans _ c X))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (T-≤-trans X q ≾ₑ-refl ∙ T-≤-refl _)
      ∙ ∘ᵐ-identityˡ _

-- Box-grade relaxation is irrelevant in its witness.

[]-≤-irr : ∀ {A ρ₁ ρ₂} → (p q : ρ₁ ≾ᵣ ρ₂) → []-≤ {A} p ≈ᵐ []-≤ {A} q
[]-≤-irr {A} p q =
  subst (λ z → []-≤ {A} p ≈ᵐ []-≤ {A} z) (≾ᵣ-irrelevant p q) ≈ᵐ-refl

-- The environment a `return` hands to its continuation.
--
-- `strᵀ-ηᵀ` opens the boxed environment with the box counit at the unit grade;
-- the syntax instead re-locks the context with `⟨⟩-η-ren`. The two agree by
-- `η⊣-u`. The grade equality `mapᵉ uₑ ≡ uᵣ` is generalised so that it can be
-- matched.

ret-env-u : ∀ {X} → εᵇ ∘ᵐ η⊣ {X} {uᵣ} ≈ᵐ η
ret-env-u =
    ∘ᵐ-congʳ η⊣-u
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-ε-nat η))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ []-ε∘ηᵘ≡id
  ∙ ∘ᵐ-identityʳ _

ret-env : ∀ {ρ} X → (e : ρ ≃ᵣ uᵣ)
        → εᵇ ∘ᵐ []-≤ (≃ᵣ⇒≿ᵣ e) ∘ᵐ η⊣ {X} {ρ}
        ≈ᵐ ⟨⟩-≤ (≃ᵣ⇒≿ᵣ e) ∘ᵐ η
ret-env X e =
    ∘ᵐ-congʳ (η⊣-≤ (≃ᵣ⇒≿ᵣ e))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-ε-nat _))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (ret-env-u {X})

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

-- The `return` rules: `⨟` and `handle` thread the environment through the
-- strength in the same way, differing only in the algebra that collapses the
-- two monad layers (`μᵀ`, resp. `T-alg-of-handlerᵀ`), so `SEQ-RET` and
-- `HANDLE-RET` share one proof.

-- The parametricity certificate of the `return`-rules' reduct: the sequel
-- renamed by the re-locking renaming, then substituted into.
ret-subᴾ : ∀ {Γ A B ε} → (V : Γ ⊢V⦂ A) → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
         → Paramᵛ V → Paramᶜ N
         → Paramᶜ (C-rename (cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N
                     [ split-[] ↦ V ]c)
ret-subᴾ {Γ} V N pV pN =
  subᶜ (C-rename (cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N)
       split-[] V
    (renᶜ (cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N pN) pV

ret-step : ∀ {Γ A B ε}
         → (alg : Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε) uₑ →ᵐ Tᵒ ⟦ B ⟧ᵛ (uₑ ·ₑ ε))
         → (alg-η : alg ∘ᵐ ηᵀ ≈ᵐ T-≤ (≃ₑ⇒≿ₑ (·ₑ-identityˡ ε)))
         → (V : Γ ⊢V⦂ A)
         → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
         → (pV : Paramᵛ V) → (pN : Paramᶜ N)
         → alg ∘ᵐ Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ pV ⟩ᵐ
         ≈ᵐ T-≤ (≃ₑ⇒≿ₑ (·ₑ-identityˡ ε))
            ∘ᵐ ⟦ C-rename (cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N
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
                ≈ᵐ ηᵀ ∘ᵐ ⟦ C-rename (cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N
                            [ split-[] ↦ V ]c ⟧ᶜᵗ (ret-subᴾ V N pV pN)
    ret-massage =
        ∘ᵐ-congʳ (∘ᵐ-congʳ
          (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ strᵀ-ηᵀ)
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
          (⟨ ∘ᵐ-assoc _ _ _ ∙ ret-env ⟦ Γ ⟧ᶜᵗˣ map-uᵉ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ηᵀ-nat (⟦ N ⟧ᶜᵗ pN)))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (sub-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren) N V pN pV))

-- `ret-step`, threaded with an eternal parameter `P` supplied by `pv`. The
-- handler's algebra reads its clause-context off `P` (`= ⟦ Γ ⟨ ⊤ᵣ ⟩ ⟧`, via
-- `⟨⊤⟩-η`); the `ηᵀ` law discards it (`sndᵐ`), so returning ignores `P`.
ret-step-P : ∀ {Γ A B ε P}
           → (pv : ⟦ Γ ⟧ᶜᵗˣ →ᵐ P)
           → (alg : P ×ᵐ Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε) uₑ →ᵐ Tᵒ ⟦ B ⟧ᵛ (uₑ ·ₑ ε))
           → (alg-η : alg ∘ᵐ mapˣᵐ idᵐ (ηᵀ {Tᵒ ⟦ B ⟧ᵛ ε})
                    ≈ᵐ T-≤ (≃ₑ⇒≿ₑ (·ₑ-identityˡ ε)) ∘ᵐ sndᵐ)
           → (V : Γ ⊢V⦂ A)
           → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
           → (pV : Paramᵛ V) → (pN : Paramᶜ N)
           → alg ∘ᵐ ⟨ pv , Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ pV ⟩ᵐ ⟩ᵐ
           ≈ᵐ T-≤ (≃ₑ⇒≿ₑ (·ₑ-identityˡ ε))
              ∘ᵐ ⟦ C-rename (cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N
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
                ≈ᵐ ηᵀ ∘ᵐ ⟦ C-rename (cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N
                            [ split-[] ↦ V ]c ⟧ᶜᵗ (ret-subᴾ V N pV pN)
    ret-massage =
        ∘ᵐ-congʳ (∘ᵐ-congʳ
          (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ strᵀ-ηᵀ)
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
          (⟨ ∘ᵐ-assoc _ _ _ ∙ ret-env ⟦ Γ ⟧ᶜᵗˣ map-uᵉ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ηᵀ-nat (⟦ N ⟧ᶜᵗ pN)))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (sub-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren) N V pN pV))

-- SEQ-RET and HANDLE-RET: the two instances of `ret-step`, one for the monad
-- multiplication and one for the handler's algebra.

sound-SEQ-RET : ∀ {Γ A B ε} → (V : Γ ⊢V⦂ A) → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
              → (pV : Paramᵛ V) → (pN : Paramᶜ N)
              → ⟦ return V ⨟ N ⟧ᶜᵗ (pV , pN)
              ≈ᵐ T-≤ (≃ₑ⇒≿ₑ (·ₑ-identityˡ ε))
                 ∘ᵐ ⟦ C-rename (cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N
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
                 ≈ᵐ T-≤ (≃ₑ⇒≿ₑ (·ₑ-identityˡ ε))
                    ∘ᵐ ⟦ C-rename (cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren)) N
                           [ split-[] ↦ V ]c ⟧ᶜᵗ (ret-subᴾ V N pV pN)
sound-HANDLE-RET {Γ} V H N pV pN pH uH =
    handle-in-β (return V) H N pV pN pH uH
  ∙ ret-step-P ⟨⊤⟩-η (T-alg-of-handlerᵀ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H pH uH))
             (T-alg-of-handlerᵀ-ηᵀ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H pH uH)) V N pV pN

