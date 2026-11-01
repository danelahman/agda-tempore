import Data.Bool.Base as Bool
open import Data.Empty using (⊥)
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.Reduction (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.State S

open import Language.Comparisons
open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Data            S using (compareᵈ; ⌈_⌉ᵇ)
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming.Action S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Substitution    S
open import MonomorphicCalculus.Syntax.Types           S

open import MonomorphicCalculus.Syntax.Substitution.Subsumption  S

-- Configurations that encapsulate time, state and computation

record Config (C : CType) : Set where
  constructor ⟨_∣_⟩
  field
        state       : State []
        computation : toCtx state  ⊢ᶜ⦂ C

-- Looking up the resource that an unboxing computation refers to

unbox-lookup : ∀ {A ρ ρ'}
             → (𝕊 : State [])
             → (z : [ ρ ] A ∈[ ρ' ] toCtx 𝕊)
             → ρ' ≾ᵣ ρ
             → toCtx 𝕊 ⊢ᵛ⦂ A
unbox-lookup {A} {ρ} 𝕊 z ρ'≾ρ =
  V-rename
    ((((  eq-ren ++ᶜ-identityˡ
       ∘ʳ ⟨⟩-≤-ren ρ'≾ρ)
       ∘ʳ (⟨⟩-≤-ren (≃ᵣ⇒≾ᵣ (≃ᵣ-trans (≃ᵣ-trans (≃ᵣ-trans (ctx-grade-++ᶜ ([] ∷ [ ρ ] A) (toCtx (split-state-snd 𝕊 z))) (·ᵣ-identityˡ (ctx-grade (toCtx (split-state-snd 𝕊 z))))) (≃ᵣ-reflexive (sym (grades-≡ (split-state-snd 𝕊 z))))) (≃ᵣ-reflexive (snd-split-time≡time-from-head 𝕊 z)))) ∘ʳ wk-ren-⟨ρ⟩-ctx refl))
       ∘ʳ eq-ren (sym (++ᶜ-assoc _ ([] ∷ [ ρ ] A) _)))
       ∘ʳ eq-ren (split-state-++ᶜ 𝕊 z))
    (resource-lookup 𝕊 z)

-- The reducts of the list eliminators at a decomposed scrutinee: at the empty
-- list the `nil` branch, resp. the base; at a head and a tail the `cons`
-- branch with both substituted, as for `match`, resp. the recursion at the tail
-- sequenced with one unfolding of the step.

matchL-reduct : ∀ {Γ A C} → ListView Γ A → Γ ⊢ᶜ⦂ C → Γ ∷ A ∷ list A ⊢ᶜ⦂ C
              → Γ ⊢ᶜ⦂ C
matchL-reduct (inj₁ _)       M N = M
matchL-reduct (inj₂ (W , L)) M N =
  (N [ V-rename wk-ren L ]₀) [ W ]₀

recL-reduct : ∀ {Γ A B ε} → ListView Γ A → Γ ⊢ᶜ⦂ B ! ε
            → (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε
            → ε ·ₑ ε ≾ₑ ε
            → Γ ⊢ᶜ⦂ B ! ε
recL-reduct (inj₁ _)       M N p = M
recL-reduct (inj₂ (W , L)) M N p = coerce p (recL L M N p ⨟ recL-step W L N)

-- The reduct of sum elimination at a decomposed scrutinee: the branch the
-- injection names, with the payload substituted.

match+-reduct : ∀ {Γ A B C} → (Γ ⊢ᵛ⦂ A) ⊎ (Γ ⊢ᵛ⦂ B) → Γ ∷ A ⊢ᶜ⦂ C → Γ ∷ B ⊢ᶜ⦂ C
              → Γ ⊢ᶜ⦂ C
match+-reduct (inj₁ W) M N = M [ W ]₀
match+-reduct (inj₂ W) M N = N [ W ]₀

-- The boolean constant a comparison decides to: the relation's truth on the
-- operands' data

decide : ∀ {Γ A} {𝕊 : State Γ} → Cmp → (V W : toCtx 𝕊 ⊢ᵛ⦂ A) → Et A
       → toCtx 𝕊 ⊢ᵛ⦂ bool
decide {𝕊 = 𝕊} ⋈ V W et =
  ⌈ holds ⋈ (compareᵈ et (⌊_⌋ᵈ {𝕊 = 𝕊} et V) (⌊_⌋ᵈ {𝕊 = 𝕊} et W)) ⌉ᵇ

decided : ∀ {Γ A} {𝕊 : State Γ} → (⋈ : Cmp) → (V W : toCtx 𝕊 ⊢ᵛ⦂ A) → (et : Et A)
        → (decide {𝕊 = 𝕊} ⋈ V W et ≡ true) ⊎ (decide {𝕊 = 𝕊} ⋈ V W et ≡ false)
decided {𝕊 = 𝕊} ⋈ V W et =
  constant {toCtx 𝕊} (holds ⋈ (compareᵈ et (⌊_⌋ᵈ {𝕊 = 𝕊} et V) (⌊_⌋ᵈ {𝕊 = 𝕊} et W)))
  where
    constant : ∀ {Δ} → (b : Bool.Bool) → (⌈_⌉ᵇ {Δ} b ≡ true) ⊎ (⌈_⌉ᵇ {Δ} b ≡ false)
    constant Bool.true  = inj₁ refl
    constant Bool.false = inj₂ refl

infix 3 _⟶_

mutual

    -- Small-step operational semantics; being typed, it is also preservation
    data _⟶_ :  {C D : CType} → Config C → Config D → Set where

        -- application: substitute the argument into the abstraction's body
        APP        : ∀ {A B ε}
                   → {𝕊 : State []}
                   → {M : ((toCtx 𝕊) ∷ A) ⊢ᶜ⦂ B ! ε}
                   → {V : (toCtx 𝕊) ⊢ᵛ⦂ A}
                     -----------------------------------------
                   → ⟨ 𝕊 ∣ fun M · V ⟩ ⟶ ⟨ 𝕊 ∣ M [ V ]₀ ⟩

        -- matching: substitute the pair's two components, read off the
        -- scrutinee by `fstᵛ`/`sndᵛ`
        MATCH      : ∀ {A B C}
                   → {𝕊 : State []}
                   → {P : toCtx 𝕊 ⊢ᵛ⦂ A |×| B}
                   → {M : toCtx 𝕊 ∷ A ∷ B ⊢ᶜ⦂ C}
                     ---------------------------------------------------
                   → ⟨ 𝕊 ∣ match P `with M ⟩ ⟶
                     ⟨ 𝕊 ∣ (M [ V-rename wk-ren (sndᵛ P) ]₀)
                             [ fstᵛ P ]₀ ⟩

        -- list elimination: the reduct at the scrutinee's canonical
        -- decomposition (`listᵛ`), which pushes its coercions into the head
        -- and the tail
        MATCHL     : ∀ {A C}
                   → {𝕊 : State []}
                   → {V : toCtx 𝕊 ⊢ᵛ⦂ list A}
                   → {M : toCtx 𝕊 ⊢ᶜ⦂ C}
                   → {N : toCtx 𝕊 ∷ A ∷ list A ⊢ᶜ⦂ C}
                     ------------------------------------------------------------
                   → ⟨ 𝕊 ∣ matchL V `nil M `cons N ⟩ ⟶ ⟨ 𝕊 ∣ matchL-reduct (listᵛ V) M N ⟩

        -- primitive recursion on lists: at the empty list the base; at a head
        -- and a tail the recursion at the tail sequenced with one unfolding of
        -- the step, the effect absorbing its own iteration
        RECL       : ∀ {A B ε}
                   → {𝕊 : State []}
                   → {V : toCtx 𝕊 ⊢ᵛ⦂ list A}
                   → {M : toCtx 𝕊 ⊢ᶜ⦂ B ! ε}
                   → {N : (toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
                   → {p : ε ·ₑ ε ≾ₑ ε}
                     ------------------------------------------------------------
                   → ⟨ 𝕊 ∣ recL V M N p ⟩ ⟶ ⟨ 𝕊 ∣ recL-reduct (listᵛ V) M N p ⟩

        -- boolean elimination: a comparison decides to a boolean constant
        CMP        : ∀ {A C}
                   → {𝕊 : State []}
                   → {⋈ : Cmp}
                   → {V W : toCtx 𝕊 ⊢ᵛ⦂ A}
                   → {et : Et A}
                   → {M N : toCtx 𝕊 ⊢ᶜ⦂ C}
                     ------------------------------------------------------------
                   → ⟨ 𝕊 ∣ if cmp ⋈ V W et `then M `else N ⟩ ⟶
                     ⟨ 𝕊 ∣ if decide {𝕊 = 𝕊} ⋈ V W et `then M `else N ⟩

        -- boolean elimination: take the branch the scrutinee names
        IF-TRUE    : ∀ {C}
                   → {𝕊 : State []}
                   → {M N : toCtx 𝕊 ⊢ᶜ⦂ C}
                     -------------------------------------------
                   → ⟨ 𝕊 ∣ if true `then M `else N ⟩ ⟶ ⟨ 𝕊 ∣ M ⟩

        IF-FALSE   : ∀ {C}
                   → {𝕊 : State []}
                   → {M N : toCtx 𝕊 ⊢ᶜ⦂ C}
                     --------------------------------------------
                   → ⟨ 𝕊 ∣ if false `then M `else N ⟩ ⟶ ⟨ 𝕊 ∣ N ⟩

        -- natural-number elimination: take the branch the scrutinee names,
        -- substituting the predecessor into the successor branch
        MATCHℕ-ZERO : ∀ {C}
                    → {𝕊 : State []}
                    → {M : toCtx 𝕊 ⊢ᶜ⦂ C}
                    → {N : toCtx 𝕊 ∷ nat ⊢ᶜ⦂ C}
                      ------------------------------------------------
                    → ⟨ 𝕊 ∣ matchℕ zero `zero M `succ N ⟩ ⟶ ⟨ 𝕊 ∣ M ⟩

        MATCHℕ-SUCC : ∀ {C}
                    → {𝕊 : State []}
                    → {V : toCtx 𝕊 ⊢ᵛ⦂ nat}
                    → {M : toCtx 𝕊 ⊢ᶜ⦂ C}
                    → {N : toCtx 𝕊 ∷ nat ⊢ᶜ⦂ C}
                      ------------------------------------------------------------
                    → ⟨ 𝕊 ∣ matchℕ succ V `zero M `succ N ⟩ ⟶ ⟨ 𝕊 ∣ N [ V ]₀ ⟩

        -- primitive recursion: at zero, the base; at a successor, the
        -- recursion at the predecessor sequenced with one unfolding of the
        -- step, the effect absorbing its own iteration
        RECℕ-ZERO  : ∀ {B ε}
                   → {𝕊 : State []}
                   → {M : toCtx 𝕊 ⊢ᶜ⦂ B ! ε}
                   → {N : (toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
                   → {p : ε ·ₑ ε ≾ₑ ε}
                     --------------------------------------
                   → ⟨ 𝕊 ∣ recℕ zero M N p ⟩ ⟶ ⟨ 𝕊 ∣ M ⟩

        RECℕ-SUCC  : ∀ {B ε}
                   → {𝕊 : State []}
                   → {V : toCtx 𝕊 ⊢ᵛ⦂ nat}
                   → {M : toCtx 𝕊 ⊢ᶜ⦂ B ! ε}
                   → {N : (toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
                   → {p : ε ·ₑ ε ≾ₑ ε}
                     ------------------------------------------------------------
                   → ⟨ 𝕊 ∣ recℕ (succ V) M N p ⟩ ⟶
                     ⟨ 𝕊 ∣ coerce p (recℕ V M N p ⨟ recℕ-step V N) ⟩

        -- sum elimination: the reduct at the scrutinee's canonical
        -- decomposition (`injᵛ`), which pushes its coercions into the payload
        MATCH+     : ∀ {A B C}
                   → {𝕊 : State []}
                   → {V : toCtx 𝕊 ⊢ᵛ⦂ A |+| B}
                   → {M : toCtx 𝕊 ∷ A ⊢ᶜ⦂ C}
                   → {N : toCtx 𝕊 ∷ B ⊢ᶜ⦂ C}
                     ----------------------------------------------------------
                   → ⟨ 𝕊 ∣ match+ V `inl M `inr N ⟩ ⟶ ⟨ 𝕊 ∣ match+-reduct (injᵛ V) M N ⟩

        -- sequencing: step the scrutinee, carrying time and state forward and
        -- subsuming the sequel's binder to the scrutinee's refined type
        SEQ-STEP   : ∀ {ε₁ ε₂ ε₃}
                   → {A A₀ B : VType}
                   → {𝕊 𝕊' : State []}
                   → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε₁}
                   → {N : ((toCtx 𝕊) ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A) ⊢ᶜ⦂ B ! ε₂}
                   → {M' : toCtx 𝕊' ⊢ᶜ⦂ A₀ ! ε₃}
                   → (M⟶M' : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩)
                   → (δε₃≾ε₁ : κₛ (step-extends-state M⟶M') ·ᵣ ∣ ε₃ ∣ᵉ ≾ᵣ ∣ ε₁ ∣ᵉ)
                    --------------------------------------------------------------------
                   → ⟨ 𝕊 ∣ M ⨟ N ⟩ ⟶
                     ⟨ 𝕊' ∣ M' ⨟ subCtx (step-refines-type M⟶M')
                                 (C-rename
                                   (cong-∷-ren (suc-comp-ren (step-extends-state M⟶M') δε₃≾ε₁))
                                   N) ⟩

        -- sequencing a returned value: substitute it into the sequel
        SEQ-RET    : ∀ {A B ε}
                   → {𝕊 : State []}
                   → {V : toCtx 𝕊 ⊢ᵛ⦂ A}
                   → {N : (toCtx 𝕊 ⟨ ∣ 𝟏ₑ ∣ᵉ ⟩ ∷ A) ⊢ᶜ⦂ B ! ε}
                     --------------------------------------------
                   → ⟨ 𝕊 ∣ return V ⨟ N ⟩ ⟶
                     ⟨ 𝕊 ∣ (C-rename
                             (cong-∷-ren
                               ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-𝟏ᵉ) ∘ʳ ⟨⟩-η-ren)))
                              N) [ V ]₀ ⟩

        -- sequencing an operation: float it out, the sequel joining its
        -- continuation
        SEQ-OP     : ∀ {A B ε ε' op} 
                   → {𝕊 : State []} 
                   → {V : (toCtx 𝕊) ⊢ᵛ⦂ ⌜ param op ⌝ᵍ} 
                   → {M : toCtx 𝕊 ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ A ! ε} 
                   → {N : toCtx 𝕊 ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'} 
                    -----------------------------------------------------------------------------------
                   → ⟨ 𝕊 ∣ (perform op V M) ⨟ N  ⟩ ⟶
                     ⟨ 𝕊 ∣ ε-≃ (≃ₑ-sym (·ₑ-assoc (op-grade op) ε ε'))
                             (perform op V
                               (M ⨟ C-rename
                                      (cong-∷-ren ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren))
                                      N)) ⟩

        -- delay: let time pass, moving the lock into the state
        DELAY      : ∀ {A τ ε}
                   → {𝕊 : State []}
                   → {M : toCtx 𝕊 ⟨ ιᵣ τ ⟩ ⊢ᶜ⦂ A ! ε} → 
                     -------------------------------------------------------------
                     ⟨ 𝕊 ∣ (delay τ M) ⟩ ⟶ ⟨ grade-pass 𝕊 (ιᵣ τ) ∣ M ⟩

        -- handling a returned value: run the return clause
        HANDLE-RET : ∀ {A B ε}
                   → {𝕊 : State []}
                   → {V : toCtx 𝕊 ⊢ᵛ⦂ A}
                   →
                     {H : (op : Op)
                        → (ε' : E)
                        → toCtx 𝕊 ⟨ ⊤ᵣ ⟩
                                  ∷ ⌜ param op ⌝ᵍ
                                  ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε')
                          ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε')}
                   → {N : toCtx 𝕊 ⟨ ∣ 𝟏ₑ ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε}
                     --------------------------------------------------------------------------
                   → ⟨ 𝕊 ∣ handle return V `with handler N H ⟩ ⟶
                     ⟨ 𝕊 ∣ (C-rename
                             (cong-∷-ren
                               (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-𝟏ᵉ) ∘ʳ ⟨⟩-η-ren))
                             N) [ V ]₀ ⟩
                     
        -- handling: step the handled computation, carrying time and state forward
        HANDLE-STEP : ∀ {A A₀ B ε₁ ε₂ ε₁'}
                    → {𝕊 𝕊' : State []}
                    → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε₁}
                    → {H : (op : Op) → (ε₃ : E) →
                         toCtx 𝕊 ⟨ ⊤ᵣ ⟩
                                 ∷ ⌜ param op ⌝ᵍ
                                 ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε₃)
                               ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε₃)}
                    → {N : toCtx 𝕊 ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε₂}
                    → {M' : toCtx 𝕊' ⊢ᶜ⦂ A₀ ! ε₁'}
                    → (M⟶M' : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩)
                    → (δε₁'≾ε₁ : κₛ (step-extends-state M⟶M') ·ᵣ ∣ ε₁' ∣ᵉ ≾ᵣ ∣ ε₁ ∣ᵉ)
                      -----------------------------------------------------------------------
                    → ⟨ 𝕊  ∣ handle M `with handler N H ⟩ ⟶
                      ⟨ 𝕊' ∣ handle M'
                            `with handler
                                    (subCtx (step-refines-type M⟶M')
                                      (C-rename
                                        (cong-∷-ren (suc-comp-ren (step-extends-state M⟶M') δε₁'≾ε₁))
                                        N))
                                    (λ op ε₃ →
                                       C-rename
                                         (cong-∷-ren (cong-∷-ren
                                           (suc-comp-ren (step-extends-state M⟶M') (≾-⊤ᵣ _))))
                                         (H op ε₃)) ⟩

        -- handling an operation: apply its clause, with the rest of the handled
        -- computation boxed up, so that its resources are not used before enough
        -- time has passed
        HANDLE-OP   : ∀ {A B ε ε'' op}
                    → {𝕊 : State []} 
                    → {V : toCtx 𝕊 ⊢ᵛ⦂ ⌜ param op ⌝ᵍ}
                    → {M : toCtx 𝕊 ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ A ! ε}
                    → {H : (op' : Op) → (ε' : E) →
                             toCtx 𝕊 ⟨ ⊤ᵣ ⟩
                                     ∷ ⌜ param op' ⌝ᵍ
                                     ∷ [ ∣ op-grade op' ∣ᵉ ] (⌜ arity op' ⌝ᵍ ⇒ B ! ε')
                                   ⊢ᶜ⦂ B ! (op-grade op' ·ₑ ε')}
                    → {N : toCtx 𝕊 ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε''}
                      --------------------------------------------------------------------------
                    → ⟨ 𝕊 ∣ handle perform op V M `with handler N H ⟩ ⟶
                      ⟨ 𝕊 ∣ box _ (fun
                              (handle M
                              `with handler
                                      (C-rename
                                        (  cong-∷-ren ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ)
                                        ∘ʳ ⟨⟩-μ-ren)
                                        ∘ʳ cong-⟨⟩-ren wk-ren))
                                        N)
                                      (λ op' ε' →
                                         C-rename
                                           (cong-∷-ren (cong-∷-ren
                                             (barrier-wk-ren ∣ op-grade op ∣ᵉ
                                                             ⌜ arity op ⌝ᵍ)))
                                           (H op' ε'))))
                             -- the clause is included into the context reached
                             -- when the operation is handled
                             (C-rename (cong-∷-ren (cong-∷-ren barrier-ren))
                                       (H op (ε ·ₑ ε''))
                              [ V ]₁) ⟩

        -- box: extend the state with a new resource
        BOX         : ∀ {A B ρ' ε} → {𝕊 : State []}
                    → {V : toCtx 𝕊 ⟨ ρ' ⟩ ⊢ᵛ⦂ A}
                    → {M : toCtx 𝕊 ∷ [ ρ' ] A ⊢ᶜ⦂ B ! ε}
                      -------------------------------------------------------
                    → ⟨ 𝕊 ∣ (box _ V M) ⟩ ⟶
                      ⟨ extend-state 𝕊 (V-rename (eq-ren (sym ++ᶜ-identityˡ)) V) ∣ M ⟩


        -- unbox: look the resource up in the state and substitute it into the
        -- continuation
        UNBOX       : ∀ {A A₀ C ρ ρ'}
                    → {𝕊 : State []}
                    → {z : [ ρ ] A₀ ∈[ ρ' ] toCtx 𝕊}
                    → {rel : ρ' ≾ᵣ ρ}
                    → {p : A₀ <:ᵛ A}
                    → {M : toCtx 𝕊 ∷ A ⊢ᶜ⦂ C}
                      ----------------------------------------------------------
                    → ⟨ 𝕊 ∣ unbox z rel p M ⟩ ⟶
                      ⟨ 𝕊 ∣ M [ subV (unbox-lookup 𝕊 z rel) p ]₀ ⟩

        -- subsumption at an eliminated function: the coercion splits, the
        -- domain half moving onto the argument and the codomain half becoming
        -- the step's own refinement
        SUB-APP     : ∀ {A A₁ C C₁}
                    → {𝕊 : State []}
                    → {V : toCtx 𝕊 ⊢ᵛ⦂ A₁ ⇒ C₁}
                    → {W : toCtx 𝕊 ⊢ᵛ⦂ A}
                    → {q : A <:ᵛ A₁}
                    → {r : C₁ <:ᶜ C}
                      ------------------------------------------------------
                    → ⟨ 𝕊 ∣ subV V (q ⇒ₛ r) · W ⟩ ⟶ ⟨ 𝕊 ∣ V · subV W q ⟩

        -- subsumption at a handler literal: the coercion splits, the input
        -- half moving into the return clause (its lock lowered to the smaller
        -- handled effect, its binder subsumed) and the output half becoming
        -- the step's own refinement; the operation clauses do not mention the
        -- handled computation
        SUB-HANDLE  : ∀ {A A₁ B B₁ ε ε₁ ε' ε₁'}
                    → {𝕊 : State []}
                    → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
                    → {N : toCtx 𝕊 ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A₁ ⊢ᶜ⦂ B₁ ! ε₁'}
                    → {H : (op : Op) → (ε₃ : E) →
                         toCtx 𝕊 ⟨ ⊤ᵣ ⟩
                                 ∷ ⌜ param op ⌝ᵍ
                                 ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B₁ ! ε₃)
                               ⊢ᶜ⦂ B₁ ! (op-grade op ·ₑ ε₃)}
                    → {p : A <:ᵛ A₁}
                    → {pε : ε ≾ₑ ε₁}
                    → {q : (B₁ ! ε₁') <:ᶜ (B ! ε')}
                      ------------------------------------------------------------
                    → ⟨ 𝕊 ∣ handle M `with subV (handler N H) ((p !ₛ pε) ⇛ₛ q) ⟩ ⟶
                      ⟨ 𝕊 ∣ handle M
                            `with handler
                                    (subCtx p
                                      (C-rename
                                        (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ pε)))
                                        N))
                                    H ⟩

        -- nested subsumption at a handler: the two coercions compose
        SUB-HANDLE-TRANS
                    : ∀ {A₀ A' A B ε ε'}
                    → {𝕊 : State []}
                    → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
                    → {V : toCtx 𝕊 ⊢ᵛ⦂ A₀}
                    → {p : A₀ <:ᵛ A'}
                    → {p' : A' <:ᵛ (A ! ε) ⇛ (B ! ε')}
                      ------------------------------------------------------------
                    → ⟨ 𝕊 ∣ handle M `with subV (subV V p) p' ⟩ ⟶
                      ⟨ 𝕊 ∣ handle M `with subV V (<:ᵛ-trans p p') ⟩

        -- subsumption at a scrutinised boolean: `bool <:ᵛ bool` is the
        -- identity, so it is dropped
        SUB-IF      : ∀ {C}
                    → {𝕊 : State []}
                    → {V : toCtx 𝕊 ⊢ᵛ⦂ bool}
                    → {M N : toCtx 𝕊 ⊢ᶜ⦂ C}
                      -------------------------------------------------------
                    → ⟨ 𝕊 ∣ if subV V boolₛ `then M `else N ⟩ ⟶
                      ⟨ 𝕊 ∣ if V `then M `else N ⟩

        -- subsumption at a scrutinised natural number: `nat <:ᵛ nat` is the
        -- identity, so it is dropped
        SUB-MATCHℕ  : ∀ {C}
                    → {𝕊 : State []}
                    → {V : toCtx 𝕊 ⊢ᵛ⦂ nat}
                    → {M : toCtx 𝕊 ⊢ᶜ⦂ C}
                    → {N : toCtx 𝕊 ∷ nat ⊢ᶜ⦂ C}
                      ---------------------------------------------------------
                    → ⟨ 𝕊 ∣ matchℕ subV V natₛ `zero M `succ N ⟩ ⟶
                      ⟨ 𝕊 ∣ matchℕ V `zero M `succ N ⟩

        -- subsumption at a recursion's natural number: dropped, as for `matchℕ`
        SUB-RECℕ    : ∀ {B ε}
                    → {𝕊 : State []}
                    → {V : toCtx 𝕊 ⊢ᵛ⦂ nat}
                    → {M : toCtx 𝕊 ⊢ᶜ⦂ B ! ε}
                    → {N : (toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
                    → {p : ε ·ₑ ε ≾ₑ ε}
                      ---------------------------------------------------------
                    → ⟨ 𝕊 ∣ recℕ (subV V natₛ) M N p ⟩ ⟶ ⟨ 𝕊 ∣ recℕ V M N p ⟩

        -- subsumption at a computation: discarded, the reduct landing at the
        -- subtype the step is free to refine to
        SUB         : ∀ {C C'}
                    → {𝕊 : State []}
                    → {M : toCtx 𝕊 ⊢ᶜ⦂ C}
                    → {w : C <:ᶜ C'}
                      ---------------------------------
                    → ⟨ 𝕊 ∣ subC M w ⟩ ⟶ ⟨ 𝕊 ∣ M ⟩

    -- reduction steps only extend states
    --
    -- The two value types are independent here (they are related by
    -- `step-refines-type`), so that `step-grade-≾` can speak about
    -- `step-extends-state` without first knowing how the types relate.
    step-extends-state : ∀ {ε ε'}
                       → {𝕊 𝕊' : State []}
                       → {A B : VType}
                       → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
                       → {M' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε'}
                       → (M⟶M' : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩ )
                       -----------------------------------
                       → 𝕊 ≤ₛ 𝕊'

    step-extends-state APP                  = ≤ₛ-refl
    step-extends-state MATCH                = ≤ₛ-refl
    step-extends-state MATCHL               = ≤ₛ-refl
    step-extends-state RECL                 = ≤ₛ-refl
    step-extends-state IF-TRUE              = ≤ₛ-refl
    step-extends-state CMP                  = ≤ₛ-refl
    step-extends-state IF-FALSE             = ≤ₛ-refl
    step-extends-state MATCH+               = ≤ₛ-refl
    step-extends-state MATCHℕ-ZERO          = ≤ₛ-refl
    step-extends-state MATCHℕ-SUCC          = ≤ₛ-refl
    step-extends-state RECℕ-ZERO            = ≤ₛ-refl
    step-extends-state RECℕ-SUCC            = ≤ₛ-refl
    step-extends-state (SEQ-STEP M⟶M' _)    = step-extends-state M⟶M'
    step-extends-state SEQ-RET              = ≤ₛ-refl
    step-extends-state SEQ-OP               = ≤ₛ-refl
    step-extends-state DELAY                = ≤ₛ-lock ≤ₛ-refl
    step-extends-state HANDLE-RET           = ≤ₛ-refl
    step-extends-state (HANDLE-STEP M⟶M' _) = step-extends-state M⟶M'
    step-extends-state HANDLE-OP            = ≤ₛ-refl
    step-extends-state BOX                  = ≤ₛ-res ≤ₛ-refl
    step-extends-state UNBOX                = ≤ₛ-refl
    step-extends-state SUB-APP              = ≤ₛ-refl
    step-extends-state SUB-HANDLE           = ≤ₛ-refl
    step-extends-state SUB-HANDLE-TRANS     = ≤ₛ-refl
    step-extends-state SUB-IF               = ≤ₛ-refl
    step-extends-state SUB-MATCHℕ           = ≤ₛ-refl
    step-extends-state SUB-RECℕ             = ≤ₛ-refl
    step-extends-state SUB                  = ≤ₛ-refl

    -- reduction steps refine the value type, as they refine the effect
    step-refines-type : ∀ {A B ε ε'}
                      → {𝕊 𝕊' : State []}
                      → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
                      → {M' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε'}
                      → ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩
                      ---------------------------
                      → B <:ᵛ A

    step-refines-type {A = A} APP               = <:ᵛ-refl A
    step-refines-type {A = A} MATCH             = <:ᵛ-refl A
    step-refines-type {A = A} MATCHL            = <:ᵛ-refl A
    step-refines-type {A = A} RECL              = <:ᵛ-refl A
    step-refines-type {A = A} IF-TRUE           = <:ᵛ-refl A
    step-refines-type {A = A} CMP               = <:ᵛ-refl A
    step-refines-type {A = A} IF-FALSE          = <:ᵛ-refl A
    step-refines-type {A = A} MATCH+            = <:ᵛ-refl A
    step-refines-type {A = A} MATCHℕ-ZERO       = <:ᵛ-refl A
    step-refines-type {A = A} MATCHℕ-SUCC       = <:ᵛ-refl A
    step-refines-type {A = A} RECℕ-ZERO         = <:ᵛ-refl A
    step-refines-type {A = A} RECℕ-SUCC         = <:ᵛ-refl A
    step-refines-type {A = A} (SEQ-STEP _ _)    = <:ᵛ-refl A
    step-refines-type {A = A} SEQ-RET           = <:ᵛ-refl A
    step-refines-type {A = A} SEQ-OP            = <:ᵛ-refl A
    step-refines-type {A = A} DELAY             = <:ᵛ-refl A
    step-refines-type {A = A} HANDLE-RET        = <:ᵛ-refl A
    step-refines-type {A = A} (HANDLE-STEP _ _) = <:ᵛ-refl A
    step-refines-type {A = A} HANDLE-OP         = <:ᵛ-refl A
    step-refines-type {A = A} BOX               = <:ᵛ-refl A
    step-refines-type {A = A} UNBOX             = <:ᵛ-refl A
    step-refines-type (SUB-APP {r = p !ₛ _})    = p
    step-refines-type (SUB-HANDLE {q = p !ₛ _}) = p
    step-refines-type {A = A} SUB-HANDLE-TRANS  = <:ᵛ-refl A
    step-refines-type {A = A} SUB-IF            = <:ᵛ-refl A
    step-refines-type {A = A} SUB-MATCHℕ        = <:ᵛ-refl A
    step-refines-type {A = A} SUB-RECℕ          = <:ᵛ-refl A
    step-refines-type (SUB {w = p !ₛ _})        = p

-- Reduction steps make effects more precise, in cancelled form: the grade δ by
-- which the state grew, composed with the residual effect ε', stays below the
-- original effect ε. This is the form the SEQ-STEP and HANDLE-STEP premises
-- take, so those premises are derivable. The total form, about the two states'
-- grades, follows by `cancelled⇒total`.

step-grade-≾ : ∀ {A B ε ε'}
             → {𝕊 𝕊' : State []}
             → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
             → {M' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε'}
             → (r : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩)
             -------------------------------------------------
             → κₛ (step-extends-state r) ·ᵣ ∣ ε' ∣ᵉ ≾ᵣ ∣ ε ∣ᵉ

step-grade-≾ APP    = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ MATCH  = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ MATCHL = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ RECL = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ IF-TRUE = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ CMP = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ IF-FALSE = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ MATCH+ = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ MATCHℕ-ZERO = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ MATCHℕ-SUCC = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ RECℕ-ZERO = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ RECℕ-SUCC = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ (SEQ-STEP {ε₁ = ε₁} {ε₂ = ε₂} {ε₃ = ε₃} step _) =
  ≾ᵣ-trans
    (≃ᵣ⇒≾ᵣ
      (≃ᵣ-trans (·ᵣ-cong ≃ᵣ-refl (map-·ᵉ {ε₃} {ε₂})) (≃ᵣ-sym (·ᵣ-assoc (κₛ (step-extends-state step)) ∣ ε₃ ∣ᵉ ∣ ε₂ ∣ᵉ))))
    (≾ᵣ-trans
      (·ᵣ-monoˡ-≾ᵣ (step-grade-≾ step))
      (≃ᵣ⇒≿ᵣ (map-·ᵉ {ε₁} {ε₂})))
step-grade-≾ (SEQ-RET {ε = ε}) =
  ≃ᵣ⇒≿ᵣ (≃ᵣ-trans (map-·ᵉ {𝟏ₑ} {ε}) (·ᵣ-cong map-𝟏ᵉ ≃ᵣ-refl))
step-grade-≾ SEQ-OP = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ (DELAY {τ = τ} {ε = ε}) =
  ≃ᵣ⇒≾ᵣ
    (≃ᵣ-trans (·ᵣ-cong (·ᵣ-identityˡ (ιᵣ τ)) ≃ᵣ-refl) (≃ᵣ-sym (≃ᵣ-trans (map-·ᵉ {ιₑ τ} {ε}) (·ᵣ-cong map-ιᵉ ≃ᵣ-refl))))
step-grade-≾ (HANDLE-RET {ε = ε}) =
  ≃ᵣ⇒≿ᵣ (≃ᵣ-trans (map-·ᵉ {𝟏ₑ} {ε}) (·ᵣ-cong map-𝟏ᵉ ≃ᵣ-refl))
step-grade-≾ (HANDLE-STEP {ε₁ = ε₁} {ε₂ = ε₂} {ε₁' = ε₁'} step _) =
  ≾ᵣ-trans
    (≃ᵣ⇒≾ᵣ
      (≃ᵣ-trans (·ᵣ-cong ≃ᵣ-refl (map-·ᵉ {ε₁'} {ε₂})) (≃ᵣ-sym (·ᵣ-assoc (κₛ (step-extends-state step)) ∣ ε₁' ∣ᵉ ∣ ε₂ ∣ᵉ))))
    (≾ᵣ-trans
      (·ᵣ-monoˡ-≾ᵣ (step-grade-≾ step))
      (≃ᵣ⇒≿ᵣ (map-·ᵉ {ε₁} {ε₂})))
step-grade-≾ (HANDLE-OP {ε = ε} {ε'' = ε''} {op = op}) =
  ≃ᵣ⇒≾ᵣ
    (≃ᵣ-trans (·ᵣ-identityˡ _) (map-≃ᵉ (≃ₑ-sym (·ₑ-assoc (op-grade op) ε ε''))))
step-grade-≾ BOX     = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ UNBOX   = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ (SUB-APP {r = _ !ₛ s}) =
  ≾ᵣ-trans (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)) (map-monotoneᵉ s)
step-grade-≾ (SUB-HANDLE {q = _ !ₛ s}) =
  ≾ᵣ-trans (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)) (map-monotoneᵉ (·ₑ-monoʳ-≾ₑ s))
step-grade-≾ SUB-HANDLE-TRANS = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ SUB-IF  = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ SUB-MATCHℕ = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ SUB-RECℕ = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)
step-grade-≾ (SUB {w = _ !ₛ q}) =
  ≾ᵣ-trans (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ _)) (map-monotoneᵉ q)

-- A finished computation: a returned value or an operation call

data Final {Γ : Ctx} : {C : CType} → Γ ⊢ᶜ⦂ C → Set where
  is-return  : ∀ {A} → (V : Γ ⊢ᵛ⦂ A) → Final (return V)
  is-perform : ∀ {A ε} → (op : Op) → (V : Γ ⊢ᵛ⦂ ⌜ param op ⌝ᵍ)
             → (M : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ A ! ε)
             → Final (perform op V M)

-- A finished computation makes no step

final-no-step : ∀ {A ε} {D : CType} {𝕊 : State []} {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} {cf : Config D}
              → Final M → ⟨ 𝕊 ∣ M ⟩ ⟶ cf → ⊥
final-no-step (is-return _)      ()
final-no-step (is-perform _ _ _) ()

-- Reflexive-transitive closure: a run of the machine. Every step refines both
-- components of the computation type, so both are free at each link.

infix  3 _⟶*_
infixr 5 _▸_

data _⟶*_ : ∀ {A B ε ε'} → Config (A ! ε) → Config (B ! ε') → Set where
  done : ∀ {A ε} {cf : Config (A ! ε)}
       → cf ⟶* cf
  _▸_  : ∀ {A B C ε₁ ε₂ ε₃}
       → {cf₁ : Config (A ! ε₁)} → {cf₂ : Config (B ! ε₂)} → {cf₃ : Config (C ! ε₃)}
       → cf₁ ⟶ cf₂ → cf₂ ⟶* cf₃ → cf₁ ⟶* cf₃

-- The refinement a run accumulates.

run-refines-type : ∀ {A B ε ε'}
                 → {cf : Config (A ! ε)} → {cf' : Config (B ! ε')}
                 → cf ⟶* cf' → B <:ᵛ A
run-refines-type {A = A} done = <:ᵛ-refl A
run-refines-type (r ▸ rs)   = <:ᵛ-trans (run-refines-type rs) (step-refines-type r)

-- Sum elimination at an injection: `MATCH+`, by computation of `injᵛ`.

MATCH+-INL : ∀ {A B C} {𝕊 : State []} {V : toCtx 𝕊 ⊢ᵛ⦂ A}
           {M : toCtx 𝕊 ∷ A ⊢ᶜ⦂ C} {N : toCtx 𝕊 ∷ B ⊢ᶜ⦂ C}
           → ⟨ 𝕊 ∣ match+ inl V `inl M `inr N ⟩ ⟶ ⟨ 𝕊 ∣ M [ V ]₀ ⟩
MATCH+-INL = MATCH+

MATCH+-INR : ∀ {A B C} {𝕊 : State []} {V : toCtx 𝕊 ⊢ᵛ⦂ B}
           {M : toCtx 𝕊 ∷ A ⊢ᶜ⦂ C} {N : toCtx 𝕊 ∷ B ⊢ᶜ⦂ C}
           → ⟨ 𝕊 ∣ match+ inr V `inl M `inr N ⟩ ⟶ ⟨ 𝕊 ∣ N [ V ]₀ ⟩
MATCH+-INR = MATCH+

-- The list eliminators at `nil` and at a `cons`: `MATCHL` and `RECL`, by
-- computation of `listᵛ`.

MATCHL-NIL : ∀ {A C} {𝕊 : State []} {M : toCtx 𝕊 ⊢ᶜ⦂ C} {N : toCtx 𝕊 ∷ A ∷ list A ⊢ᶜ⦂ C}
           → ⟨ 𝕊 ∣ matchL nil `nil M `cons N ⟩ ⟶ ⟨ 𝕊 ∣ M ⟩
MATCHL-NIL = MATCHL

MATCHL-CONS : ∀ {A C} {𝕊 : State []} {V : toCtx 𝕊 ⊢ᵛ⦂ A} {W : toCtx 𝕊 ⊢ᵛ⦂ list A}
              {M : toCtx 𝕊 ⊢ᶜ⦂ C} {N : toCtx 𝕊 ∷ A ∷ list A ⊢ᶜ⦂ C}
            → ⟨ 𝕊 ∣ matchL cons V W `nil M `cons N ⟩ ⟶
              ⟨ 𝕊 ∣ (N [ V-rename wk-ren W ]₀) [ V ]₀ ⟩
MATCHL-CONS = MATCHL

RECL-NIL   : ∀ {A B ε} {𝕊 : State []} {M : toCtx 𝕊 ⊢ᶜ⦂ B ! ε}
             {N : (toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
             {p : ε ·ₑ ε ≾ₑ ε}
           → ⟨ 𝕊 ∣ recL nil M N p ⟩ ⟶ ⟨ 𝕊 ∣ M ⟩
RECL-NIL = RECL

RECL-CONS  : ∀ {A B ε} {𝕊 : State []} {V : toCtx 𝕊 ⊢ᵛ⦂ A} {W : toCtx 𝕊 ⊢ᵛ⦂ list A}
             {M : toCtx 𝕊 ⊢ᶜ⦂ B ! ε}
             {N : (toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
             {p : ε ·ₑ ε ≾ₑ ε}
           → ⟨ 𝕊 ∣ recL (cons V W) M N p ⟩ ⟶
             ⟨ 𝕊 ∣ coerce p (recL W M N p ⨟ recL-step V W N) ⟩
RECL-CONS = RECL
