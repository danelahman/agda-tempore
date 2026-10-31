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
  constructor ⟨_,_⟩
  field
        state       : 𝕊 []
        computation : toCtx state  ⊢C⦂ C

-- Looking up the resource that an unboxing computation refers to

unbox-lookup : ∀ {A ρ ρ'}
             → (S : 𝕊 [])
             → (z : [ ρ ] A ∈[ ρ' ] toCtx S)
             → ρ' ≾ᵣ ρ
             → toCtx S ⊢V⦂ A
unbox-lookup {A} {ρ} S z ρ'≾ρ =
  V-rename
    ((((  eq-ren ++ᶜ-identityˡ
       ∘ʳ ⟨⟩-≤-ren ρ'≾ρ)
       ∘ʳ (⟨⟩-≤-ren (≃ᵣ⇒≾ᵣ (≃ᵣ-trans (≃ᵣ-trans (≃ᵣ-trans (ctx-grade-++ᶜ ([] ∷ [ ρ ] A) (toCtx (split-state-snd S z))) (·ᵣ-identityˡ (ctx-grade (toCtx (split-state-snd S z))))) (≃ᵣ-reflexive (sym (grades-≡ (split-state-snd S z))))) (≃ᵣ-reflexive (snd-split-time≡time-from-head S z)))) ∘ʳ wk-ren-⟨ρ⟩-ctx refl))
       ∘ʳ eq-ren (sym (++ᶜ-assoc _ ([] ∷ [ ρ ] A) _)))
       ∘ʳ eq-ren (split-state-++ᶜ S z))
    (resource-lookup S z)

-- The reducts of the list eliminators at a decomposed scrutinee: at the empty
-- list the `nil` branch, resp. the base; at a head and a tail the `cons`
-- branch with both substituted, as for `match`, resp. the recursion at the tail
-- sequenced with one unfolding of the step.

matchL-reduct : ∀ {Γ A C} → ListView Γ A → Γ ⊢C⦂ C → Γ ∷ A ∷ list A ⊢C⦂ C
              → Γ ⊢C⦂ C
matchL-reduct (inj₁ _)       M N = M
matchL-reduct (inj₂ (W , L)) M N =
  (N [ split-[] ↦ V-rename wk-ren L ]c) [ split-[] ↦ W ]c

recL-reduct : ∀ {Γ A B ε} → ListView Γ A → Γ ⊢C⦂ B ! ε
            → (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε
            → ε ·ₑ ε ≾ₑ ε
            → Γ ⊢C⦂ B ! ε
recL-reduct (inj₁ _)       M N p = M
recL-reduct (inj₂ (W , L)) M N p = coerce p (recL L M N p ⨟ recL-step W L N)

-- The reduct of sum elimination at a decomposed scrutinee: the branch the
-- injection names, with the payload substituted.

match+-reduct : ∀ {Γ A B C} → (Γ ⊢V⦂ A) ⊎ (Γ ⊢V⦂ B) → Γ ∷ A ⊢C⦂ C → Γ ∷ B ⊢C⦂ C
              → Γ ⊢C⦂ C
match+-reduct (inj₁ W) M N = M [ split-[] ↦ W ]c
match+-reduct (inj₂ W) M N = N [ split-[] ↦ W ]c

-- The reduct of a comparison: the relation's truth on the operands' data

cmp-reduct : ∀ {Γ A} {S : 𝕊 Γ} → Cmp → (V W : toCtx S ⊢V⦂ A) → Et A
           → toCtx S ⊢C⦂ bool ! 𝟏ₑ
cmp-reduct ⋈ V W et = return ⌈ holds ⋈ (compareᵈ et (⌊ et ⌋ᵈ V) (⌊ et ⌋ᵈ W)) ⌉ᵇ

mutual

    -- Small-step operational semantics; being typed, it is also preservation
    data _⟶_ :  {C D : CType} → Config C → Config D → Set where

        -- application: substitute the argument into the abstraction's body
        APP        : ∀ {A B ε}
                   → {S : 𝕊 []}
                   → {M : ((toCtx S) ∷ A) ⊢C⦂ B ! ε}
                   → {V : (toCtx S) ⊢V⦂ A}
                     -----------------------------------------
                   → ⟨ S , fun M · V ⟩ ⟶ ⟨ S , M [ split-[] ↦ V ]c ⟩

        -- matching: substitute the pair's two components, read off the
        -- scrutinee by `fstᵛ`/`sndᵛ`
        MATCH      : ∀ {A B C}
                   → {S : 𝕊 []}
                   → {P : toCtx S ⊢V⦂ A |×| B}
                   → {M : toCtx S ∷ A ∷ B ⊢C⦂ C}
                     ---------------------------------------------------
                   → ⟨ S , match P `with M ⟩ ⟶
                     ⟨ S , (M [ split-[] ↦ V-rename wk-ren (sndᵛ P) ]c)
                             [ split-[] ↦ fstᵛ P ]c ⟩

        -- list elimination: the reduct at the scrutinee's canonical
        -- decomposition (`listᵛ`), which pushes its coercions into the head
        -- and the tail
        MATCHL     : ∀ {A C}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ list A}
                   → {M : toCtx S ⊢C⦂ C}
                   → {N : toCtx S ∷ A ∷ list A ⊢C⦂ C}
                     ------------------------------------------------------------
                   → ⟨ S , matchL V `nil M `cons N ⟩ ⟶ ⟨ S , matchL-reduct (listᵛ V) M N ⟩

        -- primitive recursion on lists: at the empty list the base; at a head
        -- and a tail the recursion at the tail sequenced with one unfolding of
        -- the step, the effect absorbing its own iteration
        RECL       : ∀ {A B ε}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ list A}
                   → {M : toCtx S ⊢C⦂ B ! ε}
                   → {N : (toCtx S ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε}
                   → {p : ε ·ₑ ε ≾ₑ ε}
                     ------------------------------------------------------------
                   → ⟨ S , recL V M N p ⟩ ⟶ ⟨ S , recL-reduct (listᵛ V) M N p ⟩

        -- comparison: the relation's truth on the operands' data
        CMP        : ∀ {A}
                   → {S : 𝕊 []}
                   → {⋈ : Cmp}
                   → {V W : toCtx S ⊢V⦂ A}
                   → {et : Et A}
                     ------------------------------------------------------------
                   → ⟨ S , cmp ⋈ V W et ⟩ ⟶ ⟨ S , cmp-reduct ⋈ V W et ⟩

        -- boolean elimination: take the branch the scrutinee names
        IF-TRUE    : ∀ {C}
                   → {S : 𝕊 []}
                   → {M N : toCtx S ⊢C⦂ C}
                     -------------------------------------------
                   → ⟨ S , if true `then M `else N ⟩ ⟶ ⟨ S , M ⟩

        IF-FALSE   : ∀ {C}
                   → {S : 𝕊 []}
                   → {M N : toCtx S ⊢C⦂ C}
                     --------------------------------------------
                   → ⟨ S , if false `then M `else N ⟩ ⟶ ⟨ S , N ⟩

        -- natural-number elimination: take the branch the scrutinee names,
        -- substituting the predecessor into the successor branch
        MATCHℕ-ZERO : ∀ {C}
                    → {S : 𝕊 []}
                    → {M : toCtx S ⊢C⦂ C}
                    → {N : toCtx S ∷ nat ⊢C⦂ C}
                      ------------------------------------------------
                    → ⟨ S , matchℕ zero `zero M `succ N ⟩ ⟶ ⟨ S , M ⟩

        MATCHℕ-SUCC : ∀ {C}
                    → {S : 𝕊 []}
                    → {V : toCtx S ⊢V⦂ nat}
                    → {M : toCtx S ⊢C⦂ C}
                    → {N : toCtx S ∷ nat ⊢C⦂ C}
                      ------------------------------------------------------------
                    → ⟨ S , matchℕ succ V `zero M `succ N ⟩ ⟶ ⟨ S , N [ split-[] ↦ V ]c ⟩

        -- primitive recursion: at zero, the base; at a successor, the
        -- recursion at the predecessor sequenced with one unfolding of the
        -- step, the effect absorbing its own iteration
        RECℕ-ZERO  : ∀ {B ε}
                   → {S : 𝕊 []}
                   → {M : toCtx S ⊢C⦂ B ! ε}
                   → {N : (toCtx S ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε}
                   → {p : ε ·ₑ ε ≾ₑ ε}
                     --------------------------------------
                   → ⟨ S , recℕ zero M N p ⟩ ⟶ ⟨ S , M ⟩

        RECℕ-SUCC  : ∀ {B ε}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ nat}
                   → {M : toCtx S ⊢C⦂ B ! ε}
                   → {N : (toCtx S ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε}
                   → {p : ε ·ₑ ε ≾ₑ ε}
                     ------------------------------------------------------------
                   → ⟨ S , recℕ (succ V) M N p ⟩ ⟶
                     ⟨ S , coerce p (recℕ V M N p ⨟ recℕ-step V N) ⟩

        -- sum elimination: the reduct at the scrutinee's canonical
        -- decomposition (`injᵛ`), which pushes its coercions into the payload
        MATCH+     : ∀ {A B C}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ A |+| B}
                   → {M : toCtx S ∷ A ⊢C⦂ C}
                   → {N : toCtx S ∷ B ⊢C⦂ C}
                     ----------------------------------------------------------
                   → ⟨ S , match+ V `inl M `inr N ⟩ ⟶ ⟨ S , match+-reduct (injᵛ V) M N ⟩

        -- sequencing: step the scrutinee, carrying time and state forward and
        -- subsuming the sequel's binder to the scrutinee's refined type
        SEQ-STEP   : ∀ {ε₁ ε₂ ε₃}
                   → {A A₀ B : VType}
                   → {S S' : 𝕊 []}
                   → {M : toCtx S ⊢C⦂ A ! ε₁}
                   → {N : ((toCtx S) ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A) ⊢C⦂ B ! ε₂}
                   → {M' : toCtx S' ⊢C⦂ A₀ ! ε₃}
                   → (M⟶M' : ⟨ S , M ⟩ ⟶ ⟨ S' , M' ⟩)
                   → (δε₃≾ε₁ : ≤ₛ-grade (step-extends-state M⟶M') ·ᵣ ∣ ε₃ ∣ᵉ ≾ᵣ ∣ ε₁ ∣ᵉ)
                    --------------------------------------------------------------------
                   → ⟨ S , M ⨟ N ⟩ ⟶
                     ⟨ S' , M' ⨟ subCtx (step-refines-type M⟶M')
                                 (C-rename
                                   (cong-∷-ren (suc-comp-ren (step-extends-state M⟶M') δε₃≾ε₁))
                                   N) ⟩

        -- sequencing a returned value: substitute it into the sequel
        SEQ-RET    : ∀ {A B ε}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ A}
                   → {N : (toCtx S ⟨ ∣ 𝟏ₑ ∣ᵉ ⟩ ∷ A) ⊢C⦂ B ! ε}
                     --------------------------------------------
                   → ⟨ S , return V ⨟ N ⟩ ⟶
                     ⟨ S , (C-rename
                             (cong-∷-ren
                               ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-𝟏ᵉ) ∘ʳ ⟨⟩-η-ren)))
                              N) [ split-[] ↦ V ]c ⟩

        -- sequencing an operation: float it out, the sequel joining its
        -- continuation
        SEQ-OP     : ∀ {A B ε ε' op} 
                   → {S : 𝕊 []} 
                   → {V : (toCtx S) ⊢V⦂ ⌜ param op ⌝ᵍ} 
                   → {M : toCtx S ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ A ! ε} 
                   → {N : toCtx S ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε'} 
                    -----------------------------------------------------------------------------------
                   → ⟨ S , (perform op V M) ⨟ N  ⟩ ⟶
                     ⟨ S , ε-≃ (≃ₑ-sym (·ₑ-assoc (op-grade op) ε ε'))
                             (perform op V
                               (M ⨟ C-rename
                                      (cong-∷-ren ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren))
                                      N)) ⟩

        -- delay: let time pass, moving the lock into the state
        DELAY      : ∀ {A τ ε}
                   → {S : 𝕊 []}
                   → {M : toCtx S ⟨ ιᵣ τ ⟩ ⊢C⦂ A ! ε} → 
                     -------------------------------------------------------------
                     ⟨ S , (delay τ M) ⟩ ⟶ ⟨ grade-pass S (ιᵣ τ) , M ⟩

        -- handling a returned value: run the return clause
        HANDLE-RET : ∀ {A B ε}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ A}
                   →
                     {H : (op : Op)
                        → (ε' : E)
                        → toCtx S ⟨ ⊤ᵣ ⟩
                                  ∷ ⌜ param op ⌝ᵍ
                                  ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε')
                          ⊢C⦂ B ! (op-grade op ·ₑ ε')}
                   → {N : toCtx S ⟨ ∣ 𝟏ₑ ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε}
                     --------------------------------------------------------------------------
                   → ⟨ S , handle return V `with handler N H ⟩ ⟶
                     ⟨ S , (C-rename
                             (cong-∷-ren
                               (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-𝟏ᵉ) ∘ʳ ⟨⟩-η-ren))
                             N) [ split-[] ↦ V ]c ⟩
                     
        -- handling: step the handled computation, carrying time and state forward
        HANDLE-STEP : ∀ {A A₀ B ε₁ ε₂ ε₁'}
                    → {S S' : 𝕊 []}
                    → {M : toCtx S ⊢C⦂ A ! ε₁}
                    → {H : (op : Op) → (ε₃ : E) →
                         toCtx S ⟨ ⊤ᵣ ⟩
                                 ∷ ⌜ param op ⌝ᵍ
                                 ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε₃)
                               ⊢C⦂ B ! (op-grade op ·ₑ ε₃)}
                    → {N : toCtx S ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε₂}
                    → {M' : toCtx S' ⊢C⦂ A₀ ! ε₁'}
                    → (M⟶M' : ⟨ S , M ⟩ ⟶ ⟨ S' , M' ⟩)
                    → (δε₁'≾ε₁ : ≤ₛ-grade (step-extends-state M⟶M') ·ᵣ ∣ ε₁' ∣ᵉ ≾ᵣ ∣ ε₁ ∣ᵉ)
                      -----------------------------------------------------------------------
                    → ⟨ S  , handle M `with handler N H ⟩ ⟶
                      ⟨ S' , handle M'
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
                    → {S : 𝕊 []} 
                    → {V : toCtx S ⊢V⦂ ⌜ param op ⌝ᵍ}
                    → {M : toCtx S ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ A ! ε}
                    → {H : (op' : Op) → (ε' : E) →
                             toCtx S ⟨ ⊤ᵣ ⟩
                                     ∷ ⌜ param op' ⌝ᵍ
                                     ∷ [ ∣ op-grade op' ∣ᵉ ] (⌜ arity op' ⌝ᵍ ⇒ B ! ε')
                                   ⊢C⦂ B ! (op-grade op' ·ₑ ε')}
                    → {N : toCtx S ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε''}
                      --------------------------------------------------------------------------
                    → ⟨ S , handle perform op V M `with handler N H ⟩ ⟶
                      ⟨ S , box _ (fun
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
                              [ split-∷ split-[] ↦ V ]c) ⟩

        -- box: extend the state with a new resource
        BOX         : ∀ {A B ρ' ε} → {S : 𝕊 []}
                    → {V : toCtx S ⟨ ρ' ⟩ ⊢V⦂ A}
                    → {M : toCtx S ∷ [ ρ' ] A ⊢C⦂ B ! ε}
                      -------------------------------------------------------
                    → ⟨ S , (box _ V M) ⟩ ⟶
                      ⟨ extend-state S (V-rename (eq-ren (sym ++ᶜ-identityˡ)) V) , M ⟩


        -- unbox: look the resource up in the state and substitute it into the
        -- continuation
        UNBOX       : ∀ {A A₀ C ρ ρ'}
                    → {S : 𝕊 []}
                    → {z : [ ρ ] A₀ ∈[ ρ' ] toCtx S}
                    → {rel : ρ' ≾ᵣ ρ}
                    → {p : A₀ <:ᵛ A}
                    → {M : toCtx S ∷ A ⊢C⦂ C}
                      ----------------------------------------------------------
                    → ⟨ S , unbox z rel p M ⟩ ⟶
                      ⟨ S , M [ split-[] ↦ subV (unbox-lookup S z rel) p ]c ⟩

        -- subsumption at an eliminated function: the coercion splits, the
        -- domain half moving onto the argument and the codomain half becoming
        -- the step's own refinement
        SUB-APP     : ∀ {A A₁ C C₁}
                    → {S : 𝕊 []}
                    → {V : toCtx S ⊢V⦂ A₁ ⇒ C₁}
                    → {W : toCtx S ⊢V⦂ A}
                    → {q : A <:ᵛ A₁}
                    → {r : C₁ <:ᶜ C}
                      ------------------------------------------------------
                    → ⟨ S , subV V (q ⇒ₛ r) · W ⟩ ⟶ ⟨ S , V · subV W q ⟩

        -- subsumption at a handler literal: the coercion splits, the input
        -- half moving into the return clause (its lock lowered to the smaller
        -- handled effect, its binder subsumed) and the output half becoming
        -- the step's own refinement; the operation clauses do not mention the
        -- handled computation
        SUB-HANDLE  : ∀ {A A₁ B B₁ ε ε₁ ε' ε₁'}
                    → {S : 𝕊 []}
                    → {M : toCtx S ⊢C⦂ A ! ε}
                    → {N : toCtx S ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A₁ ⊢C⦂ B₁ ! ε₁'}
                    → {H : (op : Op) → (ε₃ : E) →
                         toCtx S ⟨ ⊤ᵣ ⟩
                                 ∷ ⌜ param op ⌝ᵍ
                                 ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B₁ ! ε₃)
                               ⊢C⦂ B₁ ! (op-grade op ·ₑ ε₃)}
                    → {p : A <:ᵛ A₁}
                    → {pε : ε ≾ₑ ε₁}
                    → {q : (B₁ ! ε₁') <:ᶜ (B ! ε')}
                      ------------------------------------------------------------
                    → ⟨ S , handle M `with subV (handler N H) ((p !ₛ pε) ⇛ₛ q) ⟩ ⟶
                      ⟨ S , handle M
                            `with handler
                                    (subCtx p
                                      (C-rename
                                        (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ pε)))
                                        N))
                                    H ⟩

        -- nested subsumption at a handler: the two coercions compose
        SUB-HANDLE-TRANS
                    : ∀ {A₀ A' A B ε ε'}
                    → {S : 𝕊 []}
                    → {M : toCtx S ⊢C⦂ A ! ε}
                    → {V : toCtx S ⊢V⦂ A₀}
                    → {p : A₀ <:ᵛ A'}
                    → {p' : A' <:ᵛ (A ! ε) ⇛ (B ! ε')}
                      ------------------------------------------------------------
                    → ⟨ S , handle M `with subV (subV V p) p' ⟩ ⟶
                      ⟨ S , handle M `with subV V (<:ᵛ-trans p p') ⟩

        -- subsumption at a scrutinised boolean: `bool <:ᵛ bool` is the
        -- identity, so it is dropped
        SUB-IF      : ∀ {C}
                    → {S : 𝕊 []}
                    → {V : toCtx S ⊢V⦂ bool}
                    → {M N : toCtx S ⊢C⦂ C}
                      -------------------------------------------------------
                    → ⟨ S , if subV V boolₛ `then M `else N ⟩ ⟶
                      ⟨ S , if V `then M `else N ⟩

        -- subsumption at a scrutinised natural number: `nat <:ᵛ nat` is the
        -- identity, so it is dropped
        SUB-MATCHℕ  : ∀ {C}
                    → {S : 𝕊 []}
                    → {V : toCtx S ⊢V⦂ nat}
                    → {M : toCtx S ⊢C⦂ C}
                    → {N : toCtx S ∷ nat ⊢C⦂ C}
                      ---------------------------------------------------------
                    → ⟨ S , matchℕ subV V natₛ `zero M `succ N ⟩ ⟶
                      ⟨ S , matchℕ V `zero M `succ N ⟩

        -- subsumption at a recursion's natural number: dropped, as for `matchℕ`
        SUB-RECℕ    : ∀ {B ε}
                    → {S : 𝕊 []}
                    → {V : toCtx S ⊢V⦂ nat}
                    → {M : toCtx S ⊢C⦂ B ! ε}
                    → {N : (toCtx S ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε}
                    → {p : ε ·ₑ ε ≾ₑ ε}
                      ---------------------------------------------------------
                    → ⟨ S , recℕ (subV V natₛ) M N p ⟩ ⟶ ⟨ S , recℕ V M N p ⟩

        -- subsumption at a computation: discarded, the reduct landing at the
        -- subtype the step is free to refine to
        SUB         : ∀ {C C'}
                    → {S : 𝕊 []}
                    → {M : toCtx S ⊢C⦂ C}
                    → {w : C <:ᶜ C'}
                      ---------------------------------
                    → ⟨ S , subC M w ⟩ ⟶ ⟨ S , M ⟩

    -- reduction steps only extend states
    --
    -- The two value types are independent here (they are related by
    -- `step-refines-type`), so that `step-grade-≾` can speak about
    -- `step-extends-state` without first knowing how the types relate.
    step-extends-state : ∀ {ε ε'}
                       → {S S' : 𝕊 []}
                       → {A B : VType}
                       → {M : toCtx S ⊢C⦂ A ! ε}
                       → {M' : toCtx S' ⊢C⦂ B ! ε'}
                       → (M⟶M' : ⟨ S , M ⟩ ⟶ ⟨ S' , M' ⟩ )
                       -----------------------------------
                       → S ≤ₛ S'

    step-extends-state APP                  = id-suc
    step-extends-state MATCH                = id-suc
    step-extends-state MATCHL               = id-suc
    step-extends-state RECL                 = id-suc
    step-extends-state IF-TRUE              = id-suc
    step-extends-state CMP                  = id-suc
    step-extends-state IF-FALSE             = id-suc
    step-extends-state MATCH+               = id-suc
    step-extends-state MATCHℕ-ZERO          = id-suc
    step-extends-state MATCHℕ-SUCC          = id-suc
    step-extends-state RECℕ-ZERO            = id-suc
    step-extends-state RECℕ-SUCC            = id-suc
    step-extends-state (SEQ-STEP M⟶M' _)    = step-extends-state M⟶M'
    step-extends-state SEQ-RET              = id-suc
    step-extends-state SEQ-OP               = id-suc
    step-extends-state DELAY                = ⟨⟩-suc (ιᵣ _) id-suc
    step-extends-state HANDLE-RET           = id-suc
    step-extends-state (HANDLE-STEP M⟶M' _) = step-extends-state M⟶M'
    step-extends-state HANDLE-OP            = id-suc
    step-extends-state BOX                  = ∷-suc (V-rename (eq-ren (sym ++ᶜ-identityˡ)) _) id-suc
    step-extends-state UNBOX                = id-suc
    step-extends-state SUB-APP              = id-suc
    step-extends-state SUB-HANDLE           = id-suc
    step-extends-state SUB-HANDLE-TRANS     = id-suc
    step-extends-state SUB-IF               = id-suc
    step-extends-state SUB-MATCHℕ           = id-suc
    step-extends-state SUB-RECℕ             = id-suc
    step-extends-state SUB                  = id-suc

    -- reduction steps refine the value type, as they refine the effect
    step-refines-type : ∀ {A B ε ε'}
                      → {S S' : 𝕊 []}
                      → {M : toCtx S ⊢C⦂ A ! ε}
                      → {M' : toCtx S' ⊢C⦂ B ! ε'}
                      → ⟨ S , M ⟩ ⟶ ⟨ S' , M' ⟩
                      ---------------------------
                      → B <:ᵛ A

    step-refines-type {A = A} APP               = <:ᵛ-refl A
    step-refines-type {A = A} MATCH             = <:ᵛ-refl A
    step-refines-type {A = A} MATCHL            = <:ᵛ-refl A
    step-refines-type {A = A} RECL              = <:ᵛ-refl A
    step-refines-type {A = A} IF-TRUE           = <:ᵛ-refl A
    step-refines-type CMP                       = boolₛ
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
             → {S S' : 𝕊 []}
             → {M : toCtx S ⊢C⦂ A ! ε}
             → {M' : toCtx S' ⊢C⦂ B ! ε'}
             → (r : ⟨ S , M ⟩ ⟶ ⟨ S' , M' ⟩)
             -------------------------------------------------
             → ≤ₛ-grade (step-extends-state r) ·ᵣ ∣ ε' ∣ᵉ ≾ᵣ ∣ ε ∣ᵉ

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
      (≃ᵣ-trans (·ᵣ-cong ≃ᵣ-refl (map-·ᵉ {ε₃} {ε₂})) (≃ᵣ-sym (·ᵣ-assoc (≤ₛ-grade (step-extends-state step)) ∣ ε₃ ∣ᵉ ∣ ε₂ ∣ᵉ))))
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
      (≃ᵣ-trans (·ᵣ-cong ≃ᵣ-refl (map-·ᵉ {ε₁'} {ε₂})) (≃ᵣ-sym (·ᵣ-assoc (≤ₛ-grade (step-extends-state step)) ∣ ε₁' ∣ᵉ ∣ ε₂ ∣ᵉ))))
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

-- invariants preserved by the small-step operational semantics, stated in
-- terms of the two states' grades

step-invariants : ∀ {A B ε ε'}
                → {S S' : 𝕊 []}
                → {M : toCtx S ⊢C⦂ A ! ε}
                → {M' : toCtx S' ⊢C⦂ B ! ε'}
                → (r : ⟨ S , M ⟩ ⟶ ⟨ S' , M' ⟩)
                → B <:ᵛ A                                               -- return types become more precise
                × state-grade S' ·ᵣ ∣ ε' ∣ᵉ ≾ᵣ state-grade S ·ᵣ ∣ ε ∣ᵉ  -- effects become more precise

step-invariants r =
  step-refines-type r ,
  cancelled⇒total (step-extends-state r) (step-grade-≾ r)

-- Reflexive-transitive closure: a run of the machine. Every step refines both
-- components of the computation type, so both are free at each link.

infixr 5 _◅_

data _⟶*_ : ∀ {A B ε ε'} → Config (A ! ε) → Config (B ! ε') → Set where
  ε*   : ∀ {A ε} {cf : Config (A ! ε)}
       → cf ⟶* cf
  _◅_  : ∀ {A B C ε₁ ε₂ ε₃}
       → {cf₁ : Config (A ! ε₁)} → {cf₂ : Config (B ! ε₂)} → {cf₃ : Config (C ! ε₃)}
       → cf₁ ⟶ cf₂ → cf₂ ⟶* cf₃ → cf₁ ⟶* cf₃

-- The refinement a run accumulates.

run-refines-type : ∀ {A B ε ε'}
                 → {cf : Config (A ! ε)} → {cf' : Config (B ! ε')}
                 → cf ⟶* cf' → B <:ᵛ A
run-refines-type {A = A} ε* = <:ᵛ-refl A
run-refines-type (r ◅ rs)   = <:ᵛ-trans (run-refines-type rs) (step-refines-type r)

-- Sum elimination at an injection: `MATCH+`, by computation of `injᵛ`.

MATCH+-INL : ∀ {A B C} {S : 𝕊 []} {V : toCtx S ⊢V⦂ A}
           {M : toCtx S ∷ A ⊢C⦂ C} {N : toCtx S ∷ B ⊢C⦂ C}
           → ⟨ S , match+ inl V `inl M `inr N ⟩ ⟶ ⟨ S , M [ split-[] ↦ V ]c ⟩
MATCH+-INL = MATCH+

MATCH+-INR : ∀ {A B C} {S : 𝕊 []} {V : toCtx S ⊢V⦂ B}
           {M : toCtx S ∷ A ⊢C⦂ C} {N : toCtx S ∷ B ⊢C⦂ C}
           → ⟨ S , match+ inr V `inl M `inr N ⟩ ⟶ ⟨ S , N [ split-[] ↦ V ]c ⟩
MATCH+-INR = MATCH+

-- The list eliminators at `nil` and at a `cons`: `MATCHL` and `RECL`, by
-- computation of `listᵛ`.

MATCHL-NIL : ∀ {A C} {S : 𝕊 []} {M : toCtx S ⊢C⦂ C} {N : toCtx S ∷ A ∷ list A ⊢C⦂ C}
           → ⟨ S , matchL nil `nil M `cons N ⟩ ⟶ ⟨ S , M ⟩
MATCHL-NIL = MATCHL

MATCHL-CONS : ∀ {A C} {S : 𝕊 []} {V : toCtx S ⊢V⦂ A} {W : toCtx S ⊢V⦂ list A}
              {M : toCtx S ⊢C⦂ C} {N : toCtx S ∷ A ∷ list A ⊢C⦂ C}
            → ⟨ S , matchL cons V W `nil M `cons N ⟩ ⟶
              ⟨ S , (N [ split-[] ↦ V-rename wk-ren W ]c) [ split-[] ↦ V ]c ⟩
MATCHL-CONS = MATCHL

RECL-NIL   : ∀ {A B ε} {S : 𝕊 []} {M : toCtx S ⊢C⦂ B ! ε}
             {N : (toCtx S ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε}
             {p : ε ·ₑ ε ≾ₑ ε}
           → ⟨ S , recL nil M N p ⟩ ⟶ ⟨ S , M ⟩
RECL-NIL = RECL

RECL-CONS  : ∀ {A B ε} {S : 𝕊 []} {V : toCtx S ⊢V⦂ A} {W : toCtx S ⊢V⦂ list A}
             {M : toCtx S ⊢C⦂ B ! ε}
             {N : (toCtx S ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε}
             {p : ε ·ₑ ε ≾ₑ ε}
           → ⟨ S , recL (cons V W) M N p ⟩ ⟶
             ⟨ S , coerce p (recL W M N p ⨟ recL-step V W N) ⟩
RECL-CONS = RECL
