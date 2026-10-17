open import Data.Product
open import Data.Sum using (inj₁; inj₂)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.PreservationTheorem (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.State S

open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.RenActions    S
open import Syntax.Renamings     S
open import Syntax.Substitutions S
open import Syntax.Types         S

open import Syntax.Substitutions.Subsumption S

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
       ∘ʳ wk-ren-⟨ρ⟩-ctx
            (trans
              (trans
                (trans
                  (ctx-grade-++ᶜ ([] ∷ [ ρ ] A) (toCtx (split-state-snd S z)))
                  (·ᵣ-identityˡ (ctx-grade (toCtx (split-state-snd S z)))))
                (sym (grades-≡ (split-state-snd S z))))
              (snd-split-time≡time-from-head S z)))
       ∘ʳ eq-ren (sym (++ᶜ-assoc _ ([] ∷ [ ρ ] A) _)))
       ∘ʳ eq-ren (split-state-++ᶜ S z))
    (resource-lookup S z)

-- The reducts of the list eliminators at a decomposed scrutinee: at the empty
-- list the `nil` branch, resp. the base; at a head and a tail the `cons`
-- branch with both substituted, as for `match`, resp. the recursion at the tail
-- sequenced with one unfolding of the step.

caseL-reduct : ∀ {Γ A C} → ListView Γ A → Γ ⊢C⦂ C → Γ ∷ A ∷ |List| A ⊢C⦂ C
             → Γ ⊢C⦂ C
caseL-reduct (inj₁ _)       M N = M
caseL-reduct (inj₂ (W , L)) M N =
  (N [ split-[] ↦ V-rename wk-ren L ]c) [ split-[] ↦ W ]c

recL-reduct : ∀ {Γ A B ε} → ListView Γ A → Γ ⊢C⦂ B ‼ ε
            → (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε
            → ε ·ₑ ε ≾ₑ ε
            → Γ ⊢C⦂ B ‼ ε
recL-reduct (inj₁ _)       M N p = M
recL-reduct (inj₂ (W , L)) M N p = coerce p (recL L M N p ⨟ recL-step W L N)

mutual

    -- Small-step operational semantics aka Preservation theorem
    data _↝_ :  {C D : CType} → Config C → Config D → Set where

        -- application: substitute the argument into the abstraction's body
        APP        : ∀ {A B ε}
                   → {S : 𝕊 []}
                   → {M : ((toCtx S) ∷ A) ⊢C⦂ B ‼ ε}
                   → {V : (toCtx S) ⊢V⦂ A}
                     -----------------------------------------
                   → ⟨ S , lam M · V ⟩ ↝ ⟨ S , M [ split-[] ↦ V ]c ⟩

        -- matching: substitute the pair's two components, read off the
        -- scrutinee by `fstᵛ`/`sndᵛ`
        MATCH      : ∀ {A B C}
                   → {S : 𝕊 []}
                   → {P : toCtx S ⊢V⦂ A |×| B}
                   → {M : toCtx S ∷ A ∷ B ⊢C⦂ C}
                     ---------------------------------------------------
                   → ⟨ S , match P `in M ⟩ ↝
                     ⟨ S , (M [ split-[] ↦ V-rename wk-ren (sndᵛ P) ]c)
                             [ split-[] ↦ fstᵛ P ]c ⟩

        -- list elimination: the reduct at the scrutinee's canonical
        -- decomposition (`listᵛ`), which pushes its coercions into the head
        -- and the tail
        CASEL      : ∀ {A C}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ |List| A}
                   → {M : toCtx S ⊢C⦂ C}
                   → {N : toCtx S ∷ A ∷ |List| A ⊢C⦂ C}
                     ------------------------------------------------------------
                   → ⟨ S , caseL V `nil M `cons N ⟩ ↝ ⟨ S , caseL-reduct (listᵛ V) M N ⟩

        -- primitive recursion on lists: at the empty list the base; at a head
        -- and a tail the recursion at the tail sequenced with one unfolding of
        -- the step, the effect absorbing its own iteration
        RECL       : ∀ {A B ε}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ |List| A}
                   → {M : toCtx S ⊢C⦂ B ‼ ε}
                   → {N : (toCtx S ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε}
                   → {p : ε ·ₑ ε ≾ₑ ε}
                     ------------------------------------------------------------
                   → ⟨ S , recL V M N p ⟩ ↝ ⟨ S , recL-reduct (listᵛ V) M N p ⟩

        -- boolean elimination: take the branch the scrutinee names
        IF-TRUE    : ∀ {C}
                   → {S : 𝕊 []}
                   → {M N : toCtx S ⊢C⦂ C}
                     -------------------------------------------
                   → ⟨ S , if true `then M `else N ⟩ ↝ ⟨ S , M ⟩

        IF-FALSE   : ∀ {C}
                   → {S : 𝕊 []}
                   → {M N : toCtx S ⊢C⦂ C}
                     --------------------------------------------
                   → ⟨ S , if false `then M `else N ⟩ ↝ ⟨ S , N ⟩

        -- natural-number elimination: take the branch the scrutinee names,
        -- substituting the predecessor into the successor branch
        CASEℕ-ZERO : ∀ {C}
                   → {S : 𝕊 []}
                   → {M : toCtx S ⊢C⦂ C}
                   → {N : toCtx S ∷ Nat ⊢C⦂ C}
                     ------------------------------------------------
                   → ⟨ S , caseℕ zero `zero M `succ N ⟩ ↝ ⟨ S , M ⟩

        CASEℕ-SUCC : ∀ {C}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ Nat}
                   → {M : toCtx S ⊢C⦂ C}
                   → {N : toCtx S ∷ Nat ⊢C⦂ C}
                     ------------------------------------------------------------
                   → ⟨ S , caseℕ succ V `zero M `succ N ⟩ ↝ ⟨ S , N [ split-[] ↦ V ]c ⟩

        -- primitive recursion: at zero, the base; at a successor, the
        -- recursion at the predecessor sequenced with one unfolding of the
        -- step, the effect absorbing its own iteration
        RECℕ-ZERO  : ∀ {B ε}
                   → {S : 𝕊 []}
                   → {M : toCtx S ⊢C⦂ B ‼ ε}
                   → {N : (toCtx S ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε}
                   → {p : ε ·ₑ ε ≾ₑ ε}
                     --------------------------------------
                   → ⟨ S , recℕ zero M N p ⟩ ↝ ⟨ S , M ⟩

        RECℕ-SUCC  : ∀ {B ε}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ Nat}
                   → {M : toCtx S ⊢C⦂ B ‼ ε}
                   → {N : (toCtx S ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε}
                   → {p : ε ·ₑ ε ≾ₑ ε}
                     ------------------------------------------------------------
                   → ⟨ S , recℕ (succ V) M N p ⟩ ↝
                     ⟨ S , coerce p (recℕ V M N p ⨟ recℕ-step V N) ⟩

        -- sum elimination: substitute the injected value into the branch the
        -- injection names
        CASE-INL   : ∀ {A B C}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ A}
                   → {M : toCtx S ∷ A ⊢C⦂ C}
                   → {N : toCtx S ∷ B ⊢C⦂ C}
                     ----------------------------------------------------------
                   → ⟨ S , case+ inl V `inl M `inr N ⟩ ↝ ⟨ S , M [ split-[] ↦ V ]c ⟩

        CASE-INR   : ∀ {A B C}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ B}
                   → {M : toCtx S ∷ A ⊢C⦂ C}
                   → {N : toCtx S ∷ B ⊢C⦂ C}
                     ----------------------------------------------------------
                   → ⟨ S , case+ inr V `inl M `inr N ⟩ ↝ ⟨ S , N [ split-[] ↦ V ]c ⟩

        -- sequencing: step the scrutinee, carrying time and state forward and
        -- subsuming the sequel's binder to the scrutinee's refined type
        SEQ-STEP   : ∀ {ε₁ ε₂ ε₃}
                   → {A A₀ B : VType}
                   → {S S' : 𝕊 []}
                   → {M : toCtx S ⊢C⦂ A ‼ ε₁}
                   → {N : ((toCtx S) ⟨ mapᵉ ε₁ ⟩ ∷ A) ⊢C⦂ B ‼ ε₂}
                   → {M' : toCtx S' ⊢C⦂ A₀ ‼ ε₃}
                   → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
                   → (δε₃≾ε₁ : ≤ₛ-grade (step-extends-state M↝M') ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ ε₁)
                    --------------------------------------------------------------------
                   → ⟨ S , M ⨟ N ⟩ ↝
                     ⟨ S' , M' ⨟ subCtx (step-refines-type M↝M')
                                 (C-rename
                                   (cong-∷-ren (suc-comp-ren (step-extends-state M↝M') δε₃≾ε₁))
                                   N) ⟩

        -- sequencing a returned value: substitute it into the sequel
        SEQ-RET    : ∀ {A B ε}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ A}
                   → {N : (toCtx S ⟨ mapᵉ uₑ ⟩ ∷ A) ⊢C⦂ B ‼ ε}
                     --------------------------------------------
                   → ⟨ S , return V ⨟ N ⟩ ↝
                     ⟨ S , (C-rename
                             (cong-∷-ren
                               ((eq-ren (cong (toCtx S ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren)))
                              N) [ split-[] ↦ V ]c ⟩

        -- sequencing an operation: float it out, the sequel joining its
        -- continuation
        SEQ-OP     : ∀ {A B ε ε' op} 
                   → {S : 𝕊 []} 
                   → {V : (toCtx S) ⊢V⦂ type-of-gtype (param op)} 
                   → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε} 
                   → {N : toCtx S ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε'} 
                    -----------------------------------------------------------------------------------
                   → ⟨ S , (perform op V M) ⨟ N  ⟩ ↝
                     ⟨ S , ε-subst (sym (·ₑ-assoc (op-grade op) ε ε'))
                             (perform op V
                               (M ⨟ C-rename
                                      (cong-∷-ren ((eq-ren (cong (toCtx S ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren))
                                      N)) ⟩

        -- delay: let time pass, moving the lock into the state
        DELAY      : ∀ {A τ ε}
                   → {S : 𝕊 []}
                   → {M : toCtx S ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε} → 
                     -------------------------------------------------------------
                     ⟨ S , (delay τ M) ⟩ ↝ ⟨ grade-pass S (of-durʳ τ) , M ⟩

        -- handling a returned value: run the return clause
        HANDLE-RET : ∀ {A B ε}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ A}
                   →
                     {H : (op : Op)
                        → (ε' : E)
                        → toCtx S ⟨ ⊤ᵣ ⟩
                                  ∷ type-of-gtype (param op)
                                  ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε')
                          ⊢C⦂ B ‼ (op-grade op ·ₑ ε')}
                   → {N : toCtx S ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε}
                     --------------------------------------------------------------------------
                   → ⟨ S , handle return V `with H `in N ⟩ ↝
                     ⟨ S , (C-rename
                             (cong-∷-ren
                               (eq-ren (cong (toCtx S ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren))
                             N) [ split-[] ↦ V ]c ⟩
                     
        -- handling: step the handled computation, carrying time and state forward
        HANDLE-STEP : ∀ {A A₀ B ε₁ ε₂ ε₁'}
                    → {S S' : 𝕊 []}
                    → {M : toCtx S ⊢C⦂ A ‼ ε₁}
                    → {H : (op : Op) → (ε₃ : E) →
                         toCtx S ⟨ ⊤ᵣ ⟩
                                 ∷ type-of-gtype (param op)
                                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₃)
                               ⊢C⦂ B ‼ (op-grade op ·ₑ ε₃)}
                    → {N : toCtx S ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂}
                    → {M' : toCtx S' ⊢C⦂ A₀ ‼ ε₁'}
                    → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
                    → (δε₁'≾ε₁ : ≤ₛ-grade (step-extends-state M↝M') ·ᵣ mapᵉ ε₁' ≾ᵣ mapᵉ ε₁)
                      -----------------------------------------------------------------------
                    → ⟨ S  , handle M `with H `in N ⟩ ↝
                      ⟨ S' , handle M'
                            `with (λ op ε₃ →
                                     C-rename
                                       (cong-∷-ren (cong-∷-ren
                                         (suc-comp-ren (step-extends-state M↝M') (≾-⊤ᵣ _))))
                                       (H op ε₃))
                            `in (subCtx (step-refines-type M↝M')
                                  (C-rename
                                    (cong-∷-ren (suc-comp-ren (step-extends-state M↝M') δε₁'≾ε₁))
                                    N))⟩

        -- handling an operation: apply its clause, with the rest of the handled
        -- computation boxed up, so that its resources are not used before enough
        -- time has passed
        HANDLE-OP   : ∀ {A B ε ε'' op}
                    → {S : 𝕊 []} 
                    → {V : toCtx S ⊢V⦂ type-of-gtype (param op)}
                    → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
                    → {H : (op' : Op) → (ε' : E) →
                             toCtx S ⟨ ⊤ᵣ ⟩
                                     ∷ type-of-gtype (param op')
                                     ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε')
                                   ⊢C⦂ B ‼ (op-grade op' ·ₑ ε')}
                    → {N : toCtx S ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε''}
                      --------------------------------------------------------------------------
                    → ⟨ S , handle perform op V M `with H `in N ⟩ ↝
                      ⟨ S , box (lam
                              (handle M
                              `with (λ op' ε' →
                                       C-rename
                                         (cong-∷-ren (cong-∷-ren
                                           (barrier-wk-ren (mapᵉ (op-grade op))
                                                           (type-of-gtype (arity op)))))
                                         (H op' ε'))
                              `in (C-rename
                                    (  cong-∷-ren ((eq-ren (cong (toCtx S ⟨_⟩) map-·ᵉ)
                                    ∘ʳ ⟨⟩-μ-ren)
                                    ∘ʳ cong-⟨⟩-ren wk-ren))
                                    N)))
                             -- the clause is included into the context reached
                             -- when the operation is handled
                             (C-rename (cong-∷-ren (cong-∷-ren barrier-ren))
                                       (H op (ε ·ₑ ε''))
                              [ split-∷ split-[] ↦ V ]c) ⟩

        -- box: extend the state with a new resource
        BOX         : ∀ {A B ρ' ε} → {S : 𝕊 []}
                    → {V : toCtx S ⟨ ρ' ⟩ ⊢V⦂ A}
                    → {M : toCtx S ∷ [ ρ' ] A ⊢C⦂ B ‼ ε}
                      -------------------------------------------------------
                    → ⟨ S , (box V M) ⟩ ↝
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
                    → ⟨ S , unbox z rel p M ⟩ ↝
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
                    → ⟨ S , subV V (q ⇒ₛ r) · W ⟩ ↝ ⟨ S , V · subV W q ⟩

        -- subsumption at a scrutinised boolean: `Bool <:ᵛ Bool` is the
        -- identity, so it is simply dropped
        SUB-IF      : ∀ {C}
                    → {S : 𝕊 []}
                    → {V : toCtx S ⊢V⦂ Bool}
                    → {M N : toCtx S ⊢C⦂ C}
                      -------------------------------------------------------
                    → ⟨ S , if subV V Boolₛ `then M `else N ⟩ ↝
                      ⟨ S , if V `then M `else N ⟩

        -- subsumption at a scrutinised natural number: `Nat <:ᵛ Nat` is the
        -- identity, so it is simply dropped
        SUB-CASEℕ   : ∀ {C}
                    → {S : 𝕊 []}
                    → {V : toCtx S ⊢V⦂ Nat}
                    → {M : toCtx S ⊢C⦂ C}
                    → {N : toCtx S ∷ Nat ⊢C⦂ C}
                      ---------------------------------------------------------
                    → ⟨ S , caseℕ subV V Natₛ `zero M `succ N ⟩ ↝
                      ⟨ S , caseℕ V `zero M `succ N ⟩

        -- subsumption at a recursion's natural number: dropped, as for `caseℕ`
        SUB-RECℕ    : ∀ {B ε}
                    → {S : 𝕊 []}
                    → {V : toCtx S ⊢V⦂ Nat}
                    → {M : toCtx S ⊢C⦂ B ‼ ε}
                    → {N : (toCtx S ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε}
                    → {p : ε ·ₑ ε ≾ₑ ε}
                      ---------------------------------------------------------
                    → ⟨ S , recℕ (subV V Natₛ) M N p ⟩ ↝ ⟨ S , recℕ V M N p ⟩

        -- subsumption at a scrutinised sum: the coercion splits, each half
        -- moving onto the binder of its branch
        SUB-CASE    : ∀ {A A₁ B B₁ C}
                    → {S : 𝕊 []}
                    → {V : toCtx S ⊢V⦂ A₁ |+| B₁}
                    → {p : A₁ <:ᵛ A}
                    → {q : B₁ <:ᵛ B}
                    → {M : toCtx S ∷ A ⊢C⦂ C}
                    → {N : toCtx S ∷ B ⊢C⦂ C}
                      ---------------------------------------------------------
                    → ⟨ S , case+ subV V (p |+|ₛ q) `inl M `inr N ⟩ ↝
                      ⟨ S , case+ V `inl subCtx p M `inr subCtx q N ⟩

        -- subsumption at a computation: discarded, the reduct landing at the
        -- subtype the step is free to refine to
        SUB         : ∀ {C C'}
                    → {S : 𝕊 []}
                    → {M : toCtx S ⊢C⦂ C}
                    → {w : C <:ᶜ C'}
                      ---------------------------------
                    → ⟨ S , subC M w ⟩ ↝ ⟨ S , M ⟩

    -- reduction steps only extend states
    --
    -- The two value types are independent here (they are related by
    -- `step-refines-type`), so that `step-grade-≾` can speak about
    -- `step-extends-state` without first knowing how the types relate.
    step-extends-state : ∀ {ε ε'}
                       → {S S' : 𝕊 []}
                       → {A B : VType}
                       → {M : toCtx S ⊢C⦂ A ‼ ε}
                       → {M' : toCtx S' ⊢C⦂ B ‼ ε'}
                       → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩ )
                       -----------------------------------
                       → S ≤ₛ S'

    step-extends-state APP                  = id-suc
    step-extends-state MATCH                = id-suc
    step-extends-state CASEL                = id-suc
    step-extends-state RECL                 = id-suc
    step-extends-state IF-TRUE              = id-suc
    step-extends-state IF-FALSE             = id-suc
    step-extends-state CASE-INL             = id-suc
    step-extends-state CASE-INR             = id-suc
    step-extends-state CASEℕ-ZERO           = id-suc
    step-extends-state CASEℕ-SUCC           = id-suc
    step-extends-state RECℕ-ZERO            = id-suc
    step-extends-state RECℕ-SUCC            = id-suc
    step-extends-state (SEQ-STEP M↝M' _)    = step-extends-state M↝M'
    step-extends-state SEQ-RET              = id-suc
    step-extends-state SEQ-OP               = id-suc
    step-extends-state DELAY                = ⟨⟩-suc (of-durʳ _) id-suc
    step-extends-state HANDLE-RET           = id-suc
    step-extends-state (HANDLE-STEP M↝M' _) = step-extends-state M↝M'
    step-extends-state HANDLE-OP            = id-suc
    step-extends-state BOX                  = ∷-suc (V-rename (eq-ren (sym ++ᶜ-identityˡ)) _) id-suc
    step-extends-state UNBOX                = id-suc
    step-extends-state SUB-APP              = id-suc
    step-extends-state SUB-IF               = id-suc
    step-extends-state SUB-CASE             = id-suc
    step-extends-state SUB-CASEℕ            = id-suc
    step-extends-state SUB-RECℕ             = id-suc
    step-extends-state SUB                  = id-suc

    -- reduction steps refine the value type, just as they refine the effect
    step-refines-type : ∀ {A B ε ε'}
                      → {S S' : 𝕊 []}
                      → {M : toCtx S ⊢C⦂ A ‼ ε}
                      → {M' : toCtx S' ⊢C⦂ B ‼ ε'}
                      → ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩
                      ---------------------------
                      → B <:ᵛ A

    step-refines-type {A = A} APP               = <:ᵛ-refl A
    step-refines-type {A = A} MATCH             = <:ᵛ-refl A
    step-refines-type {A = A} CASEL             = <:ᵛ-refl A
    step-refines-type {A = A} RECL              = <:ᵛ-refl A
    step-refines-type {A = A} IF-TRUE           = <:ᵛ-refl A
    step-refines-type {A = A} IF-FALSE          = <:ᵛ-refl A
    step-refines-type {A = A} CASE-INL          = <:ᵛ-refl A
    step-refines-type {A = A} CASE-INR          = <:ᵛ-refl A
    step-refines-type {A = A} CASEℕ-ZERO        = <:ᵛ-refl A
    step-refines-type {A = A} CASEℕ-SUCC        = <:ᵛ-refl A
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
    step-refines-type (SUB-APP {r = p ‼ₛ _})    = p
    step-refines-type {A = A} SUB-IF            = <:ᵛ-refl A
    step-refines-type {A = A} SUB-CASE          = <:ᵛ-refl A
    step-refines-type {A = A} SUB-CASEℕ         = <:ᵛ-refl A
    step-refines-type {A = A} SUB-RECℕ          = <:ᵛ-refl A
    step-refines-type (SUB {w = p ‼ₛ _})        = p

-- Reduction steps make effects more precise, in cancelled form: the grade δ by
-- which the state grew, composed with the residual effect ε', stays below the
-- original effect ε. This is the form the SEQ-STEP and HANDLE-STEP premises
-- take, so those premises are derivable. The total form, about the two states'
-- grades, follows by `cancelled⇒total`.

step-grade-≾ : ∀ {A B ε ε'}
             → {S S' : 𝕊 []}
             → {M : toCtx S ⊢C⦂ A ‼ ε}
             → {M' : toCtx S' ⊢C⦂ B ‼ ε'}
             → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
             -------------------------------------------------
             → ≤ₛ-grade (step-extends-state r) ·ᵣ mapᵉ ε' ≾ᵣ mapᵉ ε

step-grade-≾ APP   = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ MATCH = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ CASEL = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ RECL = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ IF-TRUE = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ IF-FALSE = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ CASE-INL = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ CASE-INR = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ CASEℕ-ZERO = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ CASEℕ-SUCC = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ RECℕ-ZERO = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ RECℕ-SUCC = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ (SEQ-STEP {ε₁ = ε₁} {ε₂ = ε₂} {ε₃ = ε₃} step _) =
  ≾ᵣ-trans
    (≾ᵣ-reflexive
      (trans
        (cong (≤ₛ-grade (step-extends-state step) ·ᵣ_) (map-·ᵉ {ε₃} {ε₂}))
        (sym (·ᵣ-assoc (≤ₛ-grade (step-extends-state step)) (mapᵉ ε₃) (mapᵉ ε₂)))))
    (≾ᵣ-trans
      (·ᵣ-monoˡ-≾ᵣ (step-grade-≾ step))
      (≾ᵣ-reflexive (sym (map-·ᵉ {ε₁} {ε₂}))))
step-grade-≾ (SEQ-RET {ε = ε}) =
  ≾ᵣ-reflexive (sym (trans (map-·ᵉ {uₑ} {ε}) (cong (_·ᵣ mapᵉ ε) map-uᵉ)))
step-grade-≾ SEQ-OP = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ (DELAY {τ = τ} {ε = ε}) =
  ≾ᵣ-reflexive
    (trans
      (cong (_·ᵣ mapᵉ ε) (·ᵣ-identityˡ (of-durʳ τ)))
      (sym (trans (map-·ᵉ {of-durᵉ τ} {ε}) (cong (_·ᵣ mapᵉ ε) map-of-durᵉ))))
step-grade-≾ (HANDLE-RET {ε = ε}) =
  ≾ᵣ-reflexive (sym (trans (map-·ᵉ {uₑ} {ε}) (cong (_·ᵣ mapᵉ ε) map-uᵉ)))
step-grade-≾ (HANDLE-STEP {ε₁ = ε₁} {ε₂ = ε₂} {ε₁' = ε₁'} step _) =
  ≾ᵣ-trans
    (≾ᵣ-reflexive
      (trans
        (cong (≤ₛ-grade (step-extends-state step) ·ᵣ_) (map-·ᵉ {ε₁'} {ε₂}))
        (sym (·ᵣ-assoc (≤ₛ-grade (step-extends-state step)) (mapᵉ ε₁') (mapᵉ ε₂)))))
    (≾ᵣ-trans
      (·ᵣ-monoˡ-≾ᵣ (step-grade-≾ step))
      (≾ᵣ-reflexive (sym (map-·ᵉ {ε₁} {ε₂}))))
step-grade-≾ (HANDLE-OP {ε = ε} {ε'' = ε''} {op = op}) =
  ≾ᵣ-reflexive
    (trans
      (·ᵣ-identityˡ _)
      (cong mapᵉ (sym (·ₑ-assoc (op-grade op) ε ε''))))
step-grade-≾ BOX     = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ UNBOX   = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ (SUB-APP {r = _ ‼ₛ s}) =
  ≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ _)) (map-monotoneᵉ s)
step-grade-≾ SUB-IF  = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ SUB-CASE = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ SUB-CASEℕ = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ SUB-RECℕ = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ (SUB {w = _ ‼ₛ q}) =
  ≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ _)) (map-monotoneᵉ q)

-- invariants preserved by the small-step operational semantics, stated in
-- terms of the two states' grades

step-invariants : ∀ {A B ε ε'}
                → {S S' : 𝕊 []}
                → {M : toCtx S ⊢C⦂ A ‼ ε}
                → {M' : toCtx S' ⊢C⦂ B ‼ ε'}
                → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
                → B <:ᵛ A                                               -- return types become more precise
                × state-grade S' ·ᵣ mapᵉ ε' ≾ᵣ state-grade S ·ᵣ mapᵉ ε  -- effects become more precise

step-invariants r =
  step-refines-type r ,
  cancelled⇒total (step-extends-state r) (step-grade-≾ r)

-- Reflexive-transitive closure: a run of the machine. Every step refines both
-- components of the computation type, so both are free at each link.

infixr 5 _◅_

data _↝*_ : ∀ {A B ε ε'} → Config (A ‼ ε) → Config (B ‼ ε') → Set where
  ε*   : ∀ {A ε} {cf : Config (A ‼ ε)}
       → cf ↝* cf
  _◅_  : ∀ {A B C ε₁ ε₂ ε₃}
       → {cf₁ : Config (A ‼ ε₁)} → {cf₂ : Config (B ‼ ε₂)} → {cf₃ : Config (C ‼ ε₃)}
       → cf₁ ↝ cf₂ → cf₂ ↝* cf₃ → cf₁ ↝* cf₃

-- The refinement a run accumulates.

run-refines-type : ∀ {A B ε ε'}
                 → {cf : Config (A ‼ ε)} → {cf' : Config (B ‼ ε')}
                 → cf ↝* cf' → B <:ᵛ A
run-refines-type {A = A} ε* = <:ᵛ-refl A
run-refines-type (r ◅ rs)   = <:ᵛ-trans (run-refines-type rs) (step-refines-type r)

-- The list eliminators at `nil` and at a `cons`: `CASEL` and `RECL`, by
-- computation of `listᵛ`.

CASEL-NIL  : ∀ {A C} {S : 𝕊 []} {M : toCtx S ⊢C⦂ C} {N : toCtx S ∷ A ∷ |List| A ⊢C⦂ C}
           → ⟨ S , caseL nil `nil M `cons N ⟩ ↝ ⟨ S , M ⟩
CASEL-NIL = CASEL

CASEL-CONS : ∀ {A C} {S : 𝕊 []} {V : toCtx S ⊢V⦂ A} {W : toCtx S ⊢V⦂ |List| A}
             {M : toCtx S ⊢C⦂ C} {N : toCtx S ∷ A ∷ |List| A ⊢C⦂ C}
           → ⟨ S , caseL cons V W `nil M `cons N ⟩ ↝
             ⟨ S , (N [ split-[] ↦ V-rename wk-ren W ]c) [ split-[] ↦ V ]c ⟩
CASEL-CONS = CASEL

RECL-NIL   : ∀ {A B ε} {S : 𝕊 []} {M : toCtx S ⊢C⦂ B ‼ ε}
             {N : (toCtx S ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε}
             {p : ε ·ₑ ε ≾ₑ ε}
           → ⟨ S , recL nil M N p ⟩ ↝ ⟨ S , M ⟩
RECL-NIL = RECL

RECL-CONS  : ∀ {A B ε} {S : 𝕊 []} {V : toCtx S ⊢V⦂ A} {W : toCtx S ⊢V⦂ |List| A}
             {M : toCtx S ⊢C⦂ B ‼ ε}
             {N : (toCtx S ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε}
             {p : ε ·ₑ ε ≾ₑ ε}
           → ⟨ S , recL (cons V W) M N p ⟩ ↝
             ⟨ S , coerce p (recL W M N p ⨟ recL-step V W N) ⟩
RECL-CONS = RECL
