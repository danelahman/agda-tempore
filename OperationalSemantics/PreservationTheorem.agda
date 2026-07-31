open import Data.Product

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

mutual 
    
    -- Small-step operational semantics aka Preservation theorem
    data _↝_ :  {C D : CType} → Config C → Config D → Set where

        -- usual step for function aplication
        APP        : ∀ {A B ε}
                   → {S : 𝕊 []}
                   → {M : ((toCtx S) ∷ A) ⊢C⦂ B ‼ ε}
                   → {V : (toCtx S) ⊢V⦂ A}
                     -----------------------------------------
                   → ⟨ S , lam M · V ⟩ ↝ ⟨ S , M [ split-[] ↦ V ]c ⟩

        -- usual step for match on pair 
        MATCH      : ∀ {A B C}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ A }
                   → {W : toCtx S ⊢V⦂ B }
                   → {M : toCtx S ∷ A ∷ B ⊢C⦂ C} 
                     ---------------------------------------------------
                   → ⟨ S , match ⦉ V , W ⦊ `in M ⟩ ↝ 
                     ⟨ S , (M [ split-[] ↦ V-rename wk-ren W ]c) [ split-[] ↦ V ]c ⟩

        -- step for sequencing (time and state must go on)
        SEQ-STEP   : ∀ {ε₁ ε₂ ε₃}
                   → {A B : VType}
                   → {S S' : 𝕊 []}
                   → {M : toCtx S ⊢C⦂ A ‼ ε₁}
                   → {N : ((toCtx S) ⟨ mapᵉ ε₁ ⟩ ∷ A) ⊢C⦂ B ‼ ε₂}
                   → {M' : toCtx S' ⊢C⦂ A ‼ ε₃}
                   → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
                   → (δε₃≾ε₁ : ≤ₛ-grade (step-extends-state M↝M') ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ ε₁)
                    --------------------------------------------------------------------
                   → ⟨ S , M ⨟ N ⟩ ↝
                     ⟨ S' , M' ⨟ C-rename
                                   (cong-∷-ren (suc-comp-ren (step-extends-state M↝M') δε₃≾ε₁))
                                   N ⟩

        -- usual step for return in sequencing
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

        -- usual performing operation in sequencing
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

        -- delay just pass time further
        DELAY      : ∀ {A τ ε}
                   → {S : 𝕊 []}
                   → {M : toCtx S ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε} → 
                     -------------------------------------------------------------
                     ⟨ S , (delay τ M) ⟩ ↝ ⟨ grade-pass S (of-natʳ τ) , M ⟩

        -- usual step for handle return
        HANDLE-RET : ∀ {A B ε}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ A}
                   →
                     {H : (op : Op)
                        → (ε' : E)
                        → toCtx S ᴱ
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
                     
        -- step on computation in handle. time and state must go on
        HANDLE-STEP : ∀ {A B ε₁ ε₂ ε₁'}
                    → {S S' : 𝕊 []}
                    → {M : toCtx S ⊢C⦂ A ‼ ε₁}
                    → {H : (op : Op) → (ε₃ : E) →
                         toCtx S ᴱ
                                 ∷ type-of-gtype (param op)
                                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₃)
                               ⊢C⦂ B ‼ (op-grade op ·ₑ ε₃)}
                    → {N : toCtx S ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂}
                    → {M' : toCtx S' ⊢C⦂ A ‼ ε₁'}
                    → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
                    → (δε₁'≾ε₁ : ≤ₛ-grade (step-extends-state M↝M') ·ᵣ mapᵉ ε₁' ≾ᵣ mapᵉ ε₁)
                      -----------------------------------------------------------------------
                    → ⟨ S  , handle M `with H `in N ⟩ ↝
                      ⟨ S' , handle M'
                            `with (λ op ε₃ →
                                     subst
                                       (λ Γ₀ → Γ₀
                                                 ∷ type-of-gtype (param op)
                                                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₃)
                                               ⊢C⦂ B ‼ (op-grade op ·ₑ ε₃))
                                       (trans (toCtxᴱ-[] S) (sym (toCtxᴱ-[] S')))
                                       (H op ε₃))
                            `in (C-rename
                                  (cong-∷-ren (suc-comp-ren (step-extends-state M↝M') δε₁'≾ε₁))
                                  N)⟩

        -- operation handle where we box up result so that the resources
        -- in the result are not used before enough time has passed
        HANDLE-OP   : ∀ {A B ε ε'' op}
                    → {S : 𝕊 []} 
                    → {V : toCtx S ⊢V⦂ type-of-gtype (param op)}
                    → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
                    → {H : (op' : Op) → (ε' : E) →
                             toCtx S ᴱ
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
                                           (ren-ᴱ-∷ {toCtx S ⟨ mapᵉ (op-grade op) ⟩}
                                                    (type-of-gtype (arity op)))))
                                         (H op' ε'))
                              `in (C-rename
                                    (  cong-∷-ren ((eq-ren (cong (toCtx S ⟨_⟩) map-·ᵉ)
                                    ∘ʳ ⟨⟩-μ-ren)
                                    ∘ʳ cong-⟨⟩-ren wk-ren))
                                    N)))
                             -- the clause is included into the context reached
                             -- when the operation is handled
                             (C-rename (cong-∷-ren (cong-∷-ren (ᴱ-ren (toCtx S))))
                                       (H op (ε ·ₑ ε''))
                              [ split-∷ split-[] ↦ V ]c) ⟩

        -- step for box: we just extend our state with new resource
        BOX         : ∀ {A B ρ' ε} → {S : 𝕊 []}
                    → {V : toCtx S ⟨ ρ' ⟩ ⊢V⦂ A}
                    → {M : toCtx S ∷ [ ρ' ] A ⊢C⦂ B ‼ ε}
                      -------------------------------------------------------
                    → ⟨ S , (box V M) ⟩ ↝
                      ⟨ extend-state S (V-rename (eq-ren (sym ++ᶜ-identityˡ)) V) , M ⟩


        -- step for unbox: we look up the unboxed resource in the state and
        -- substitute it into the continuation M
        UNBOX       : ∀ {A C ρ ρ'}
                    → {S : 𝕊 []}
                    → {z : [ ρ ] A ∈[ ρ' ] toCtx S}
                    → {rel : ρ' ≾ᵣ ρ}
                    → {M : toCtx S ∷ A ⊢C⦂ C}
                      ----------------------------------------------------------
                    → ⟨ S , unbox z rel M ⟩ ↝
                      ⟨ S , M [ split-[] ↦ unbox-lookup S z rel ]c ⟩

        -- during execution coerces are peeled off and
        -- the computation's effect becomes more precise
        COERCE      : ∀ {A ε ε'}
                    → {S : 𝕊 []}
                    → {M : toCtx S ⊢C⦂ A ‼ ε}
                    → {ε≾ε' : ε ≾ₑ ε'}
                      ----------------------------------
                    → ⟨ S , coerce ε≾ε' M ⟩ ↝ ⟨ S , M ⟩
 
    -- reduction steps only extend states
    --
    -- The two value types are independent here (they are equal, by
    -- `step-preserves-type`), so that `step-grade-≾` can speak about
    -- `step-extends-state` without first knowing the types agree.
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
    step-extends-state (SEQ-STEP M↝M' _)    = step-extends-state M↝M'
    step-extends-state SEQ-RET              = id-suc
    step-extends-state SEQ-OP               = id-suc
    step-extends-state DELAY                = ⟨⟩-suc (of-natʳ _) id-suc
    step-extends-state HANDLE-RET           = id-suc
    step-extends-state (HANDLE-STEP M↝M' _) = step-extends-state M↝M'
    step-extends-state HANDLE-OP            = id-suc
    step-extends-state BOX                  = ∷-suc (V-rename (eq-ren (sym ++ᶜ-identityˡ)) _) id-suc
    step-extends-state UNBOX                = id-suc
    step-extends-state COERCE               = id-suc

-- reduction steps preserve the value type

step-preserves-type : ∀ {A B ε ε'}
                    → {S S' : 𝕊 []}
                    → {M : toCtx S ⊢C⦂ A ‼ ε}
                    → {M' : toCtx S' ⊢C⦂ B ‼ ε'}
                    → ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩
                    ---------------------------
                    → A ≡ B

step-preserves-type APP              = refl
step-preserves-type MATCH            = refl
step-preserves-type (SEQ-STEP _ _)   = refl
step-preserves-type SEQ-RET          = refl
step-preserves-type SEQ-OP           = refl
step-preserves-type DELAY            = refl
step-preserves-type HANDLE-RET       = refl
step-preserves-type (HANDLE-STEP _ _) = refl
step-preserves-type HANDLE-OP        = refl
step-preserves-type BOX              = refl
step-preserves-type UNBOX            = refl
step-preserves-type COERCE           = refl

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
      (cong (_·ᵣ mapᵉ ε) (·ᵣ-identityˡ (of-natʳ τ)))
      (sym (trans (map-·ᵉ {of-natᵉ τ} {ε}) (cong (_·ᵣ mapᵉ ε) map-of-natᵉ))))
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
step-grade-≾ BOX   = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ UNBOX = ≾ᵣ-reflexive (·ᵣ-identityˡ _)
step-grade-≾ (COERCE {ε≾ε' = ε≾ε'}) =
  ≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ _)) (map-monotoneᵉ ε≾ε')

-- invariants preserved by the small-step operational semantics, stated in
-- terms of the two states' grades

step-invariants : ∀ {A B ε ε'}
                → {S S' : 𝕊 []}
                → {M : toCtx S ⊢C⦂ A ‼ ε}
                → {M' : toCtx S' ⊢C⦂ B ‼ ε'}
                → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
                → A ≡ B                                                 -- return types are preserved
                × state-grade S' ·ᵣ mapᵉ ε' ≾ᵣ state-grade S ·ᵣ mapᵉ ε  -- effects become more precise

step-invariants r =
  step-preserves-type r ,
  cancelled⇒total (step-extends-state r) (step-grade-≾ r)

-- Reflexive-transitive closure: a run of the machine. Every step preserves the
-- value type, but refines the effect grade, so the grade is free at each link.

infixr 5 _◅_

data _↝*_ : ∀ {A ε ε'} → Config (A ‼ ε) → Config (A ‼ ε') → Set where
  ε*   : ∀ {A ε} {cf : Config (A ‼ ε)}
       → cf ↝* cf
  _◅_  : ∀ {A ε₁ ε₂ ε₃}
       → {cf₁ : Config (A ‼ ε₁)} → {cf₂ : Config (A ‼ ε₂)} → {cf₃ : Config (A ‼ ε₃)}
       → cf₁ ↝ cf₂ → cf₂ ↝* cf₃ → cf₁ ↝* cf₃
