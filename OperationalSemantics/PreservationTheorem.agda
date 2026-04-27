open import Syntax.Grades

module OperationalSemantics.PreservationTheorem (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import OperationalSemantics.State (Grades)

open import Syntax.Contexts (Grades)
open import Syntax.Language (Grades)
open import Syntax.Renamings (Grades)
open import Syntax.RenActions (Grades)
open import Syntax.Substitutions (Grades)
open import Syntax.Types (Grades)

open import Data.Product

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 

open import Util.Operations (Grades)

-- Configurations that encapsulate time, state and computation

record Config (C : CType) : Set where
  constructor ⟨_,_⟩
  field
        state       : 𝕊 []
        computation : toCtx state  ⊢C⦂ C

mutual 
    
    -- Small-step operational semantics aka Preservation theorem
    data _↝_ :  {C D : CType} → Config C → Config D → Set where

        -- usual step for function aplication
        APP        : ∀ {A B ε}
                   → {S : 𝕊 []}
                   → {M : ((toCtx S) ∷ A) ⊢C⦂ B ‼ ε}
                   → {V : (toCtx S) ⊢V⦂ A}
                     -----------------------------------------
                   → ⟨ S , lam M · V ⟩ ↝ ⟨ S , M [ Hd ↦ V ]c ⟩

        -- usual step for match on pair 
        MATCH      : ∀ {A B C}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ A }
                   → {W : toCtx S ⊢V⦂ B }
                   → {M : toCtx S ∷ A ∷ B ⊢C⦂ C} 
                     ---------------------------------------------------
                   → ⟨ S , match ⦉ V , W ⦊ `in M ⟩ ↝ 
                     ⟨ S , (M [ Hd ↦ V-rename wk-ren W ]c) [ Hd ↦ V ]c ⟩

        -- step for sequencing (time and state must go on)
        SEQ-STEP   : ∀ {ε₁ ε₂ ε₃}
                   → {A B : VType}
                   → {S S' : 𝕊 []}
                   → {M : toCtx S ⊢C⦂ A ‼ ε₁}
                   → {N : ((toCtx S) ⟨ mapᵉ ε₁ ⟩ ∷ A) ⊢C⦂ B ‼ ε₂}
                   → {M' : toCtx S' ⊢C⦂ A ‼ ε₃}
                   → (S'·ε₃≾S·ε₁ : state-grade S' ·ᵣ mapᵉ ε₃ ≾ᵣ state-grade S ·ᵣ mapᵉ ε₁)
                   → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
                    --------------------------------------------------------------------
                   → ⟨ S , M ⨟ N ⟩ ↝ 
                     ⟨ S' , M' ⨟ C-rename
                                   (cong-∷-ren (suc-comp-ren (step-extends-state M↝M') S'·ε₃≾S·ε₁))
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
                               ((⟨⟩-η-ren ∘ʳ eq-ren (cong (toCtx S ⟨_⟩) map-uᵉ))))
                              N) [ Hd ↦ V ]c ⟩

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
                                      (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren ∘ʳ eq-ren (cong (toCtx S ⟨_⟩) map-·ᵉ)))
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
                        → (Γ' : Ctx)
                        → toCtx S ++ᶜ Γ'
                                  ∷ type-of-gtype (param op)
                                  ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε')
                          ⊢C⦂ B ‼ (op-grade op ·ₑ ε')}
                   → {N : toCtx S ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε}
                     --------------------------------------------------------------------------
                   → ⟨ S , handle return V `with H `in N ⟩ ↝
                     ⟨ S , (C-rename
                             (cong-∷-ren
                               (⟨⟩-η-ren ∘ʳ eq-ren (cong (toCtx S ⟨_⟩) map-uᵉ)))
                             N) [ Hd ↦ V ]c ⟩
                     
        -- step on computation in handle. time and state must go on
        HANDLE-STEP : ∀ {A B ε₁ ε₂ ε₁'}
                    → {S S' : 𝕊 []}
                    → {M : toCtx S ⊢C⦂ A ‼ ε₁}
                    → {H : (op : Op) → (ε₃ : E) → (Γ' : Ctx) →
                         toCtx S ++ᶜ Γ'
                                 ∷ type-of-gtype (param op)
                                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₃)
                               ⊢C⦂ B ‼ (op-grade op ·ₑ ε₃)} 
                    → {N : toCtx S ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂}
                    → {M' : toCtx S' ⊢C⦂ A ‼ ε₁'}
                    → (S'·ε₁'≾S·ε₁ : state-grade S' ·ᵣ mapᵉ ε₁' ≾ᵣ state-grade S ·ᵣ mapᵉ ε₁)
                    → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
                      -----------------------------------------------------------------------
                    → ⟨ S  , handle M `with H `in N ⟩ ↝ 
                      ⟨ S' , handle M' 
                            `with 
                                (λ op' ε₃' Γ'' →
                                    let S'eqS·S'' = ≤ₛ-comp (step-extends-state M↝M')
                                    in
                                    C-rename
                                      (cong-∷-ren
                                        (cong-∷-ren
                                          (eq-ren
                                            (trans
                                              (sym (++ᶜ-assoc (toCtx S) (proj₁ S'eqS·S'') Γ''))
                                              (cong (_++ᶜ Γ'') (sym (proj₂ S'eqS·S'')))))))
                                      (H op' ε₃' (proj₁ S'eqS·S'' ++ᶜ Γ'')))
                            `in (C-rename
                                  (cong-∷-ren (suc-comp-ren (step-extends-state M↝M') S'·ε₁'≾S·ε₁))
                                  N)⟩

        -- operation handle where we box up result so that the resources
        -- in the result are not used before enough time has passed
        HANDLE-OP   : ∀ {A B ε ε'' op}
                    → {S : 𝕊 []} 
                    → {V : toCtx S ⊢V⦂ type-of-gtype (param op)}
                    → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
                    → {H : (op' : Op) → (ε' : E) → (Γ' : Ctx) →
                             toCtx S ++ᶜ Γ'
                                     ∷ type-of-gtype (param op')
                                     ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε')
                                   ⊢C⦂ B ‼ (op-grade op' ·ₑ ε')}
                    → {N : toCtx S ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε''} 
                      --------------------------------------------------------------------------
                    → ⟨ S , handle perform op V M `with H `in N ⟩ ↝
                      ⟨ S , box (lam
                              (handle M
                              `with (λ op₁ ε''' Γ'' →
                                  C-rename
                                    (   cong-∷-ren (cong-∷-ren (cong-ren wk-ren
                                     ∘ʳ eq-ren (sym (++ᶜ-assoc (toCtx S) ([] ⟨ mapᵉ (op-grade op) ⟩) Γ'')))))
                                    (H op₁ ε''' ([] ⟨ mapᵉ (op-grade op) ⟩ ++ᶜ Γ'')))
                              `in (C-rename
                                    (  cong-∷-ren (cong-⟨⟩-ren wk-ren
                                    ∘ʳ ⟨⟩-μ-ren
                                    ∘ʳ eq-ren (cong (toCtx S ⟨_⟩) map-·ᵉ)))
                                    N)))
                             (H op (ε ·ₑ ε'') [] [ Tl-∷ Hd ↦ V ]c) ⟩ 

        -- step for box: we just extend our state with new resource
        BOX         : ∀ {A B ρ' ε} → {S : 𝕊 []}
                    → {V : toCtx S ⟨ ρ' ⟩ ⊢V⦂ A}
                    → {M : toCtx S ∷ [ ρ' ] A ⊢C⦂ B ‼ ε}
                      -------------------------------------------------------
                    → ⟨ S , (box V M) ⟩ ↝
                      ⟨ extend-state S (V-rename (eq-ren (sym ++ᶜ-identityˡ)) V) , M ⟩


        -- step for unbox: we just substitute in M with unboxed resource
        UNBOX       : ∀ {A C ρ ρ'} 
                    → {S : 𝕊 []}
                    → {x : [ ρ ] A ∈[ ρ' ] (toCtx S)}
                    → {ρ'≾ρ : ρ' ≾ᵣ ρ}
                    → {M : toCtx S ∷ A ⊢C⦂ C}
                      ----------------------------------------------------------
                    → ⟨ S , unbox x ρ'≾ρ M ⟩ ↝
                      ⟨ S , M [ Hd ↦ V-rename
                                       (   eq-ren (split-state-++ᶜ S x)
                                        ∘ʳ eq-ren (sym (++ᶜ-assoc _ ([] ∷ [ ρ ] A) _))
                                        ∘ʳ wk-ren-⟨ρ⟩-ctx
                                             (trans
                                               (trans
                                                 (trans
                                                   (ctx-grade-++ᶜ ([] ∷ [ ρ ] A) (toCtx (split-state-snd S x)))
                                                   (·ᵣ-identityˡ (ctx-grade (toCtx (split-state-snd S x)))))
                                                 (sym (grades-≡ (split-state-snd S x))))
                                               (snd-split-time≡time-from-head S x))
                                        ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
                                        ∘ʳ eq-ren ++ᶜ-identityˡ)
                                       (resource-lookup S x) ]c ⟩

        -- during execution coerces are peeled off and
        -- the computation's effect becomes more precise
        COERCE      : ∀ {A ε ε'}
                    → {S : 𝕊 []}
                    → {M : toCtx S ⊢C⦂ A ‼ ε}
                    → {ε≾ε' : ε ≾ₑ ε'}
                      ----------------------------------
                    → ⟨ S , coerce ε≾ε' M ⟩ ↝ ⟨ S , M ⟩
 
    -- reduction steps only extend states
    step-extends-state : ∀ {ε ε'}
                       → {S S' : 𝕊 []}
                       → {A : VType}
                       → {M : toCtx S ⊢C⦂ A ‼ ε}
                       → {M' : toCtx S' ⊢C⦂ A ‼ ε'}
                       → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩ )
                       -----------------------------------
                       → S ≤ₛ S'
                       
    step-extends-state APP                  = id-suc
    step-extends-state MATCH                = id-suc
    step-extends-state (SEQ-STEP _ M↝M')    = step-extends-state M↝M'
    step-extends-state SEQ-RET              = id-suc
    step-extends-state SEQ-OP               = id-suc
    step-extends-state DELAY                = ⟨⟩-suc (of-natʳ _) id-suc
    step-extends-state HANDLE-RET           = id-suc
    step-extends-state (HANDLE-STEP _ M↝M') = step-extends-state M↝M'
    step-extends-state HANDLE-OP            = id-suc
    step-extends-state BOX                  = ∷-suc (V-rename (eq-ren (sym ++ᶜ-identityˡ)) _) id-suc
    step-extends-state UNBOX                = id-suc
    step-extends-state COERCE               = id-suc

-- invariants preserved by the small-step operational semantics
step-invariants : ∀ {A B ε'' ε'''}
                → {S S' : 𝕊 []}
                → {M : toCtx S ⊢C⦂ A ‼ ε''}
                → {M' : toCtx S' ⊢C⦂ B ‼ ε'''}
                → ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩
                → A ≡ B                                                     -- return types are preserved
                × state-grade S' ·ᵣ mapᵉ ε''' ≾ᵣ state-grade S ·ᵣ mapᵉ ε''  -- effects become more precise
                     
step-invariants APP   = refl , ≾ᵣ-refl
step-invariants MATCH = refl , ≾ᵣ-refl
step-invariants {S = S} {S' = S'} (SEQ-STEP {ε₁ = ε₁} {ε₂ = ε₂} {ε₃ = ε₃} S'·ε₃≾S·ε₁ step) =
  refl ,
  ≾ᵣ-trans
    (≾ᵣ-reflexive (trans (cong (state-grade S' ·ᵣ_) map-·ᵉ) (sym (·ᵣ-assoc (state-grade S') (mapᵉ ε₃) (mapᵉ ε₂)))))
    (≾ᵣ-trans
      (·ᵣ-monoˡ-≾ᵣ S'·ε₃≾S·ε₁)
      (≾ᵣ-reflexive
        (trans
          (·ᵣ-assoc (state-grade S) (mapᵉ ε₁) (mapᵉ ε₂))
          (sym (cong (state-grade S ·ᵣ_) map-·ᵉ)))))
step-invariants {ε''' = ε'''} SEQ-RET =
  refl ,
  ·ᵣ-monoʳ-≾ᵣ
    (≾ᵣ-trans
      (≾ᵣ-reflexive (sym (·ᵣ-identityˡ (mapᵉ ε'''))))
      (≾ᵣ-trans
        (·ᵣ-monoˡ-≾ᵣ (≾ᵣ-reflexive (sym map-uᵉ)))
        (≾ᵣ-reflexive (sym map-·ᵉ))))
step-invariants SEQ-OP = refl , ≾ᵣ-refl
step-invariants {ε''' = ε'''} {S = S} DELAY =
  refl ,
  ≾ᵣ-trans
    (≾ᵣ-reflexive
      (trans
        (·ᵣ-assoc (state-grade S) (of-natʳ _) (mapᵉ ε'''))
        (cong (state-grade S ·ᵣ_) (cong ((_·ᵣ mapᵉ ε''')) (sym map-of-natᵉ)))))
    (·ᵣ-monoʳ-≾ᵣ (≾ᵣ-reflexive (sym map-·ᵉ)))
step-invariants {ε''' = ε'''} HANDLE-RET =
  refl ,
  ·ᵣ-monoʳ-≾ᵣ
    (≾ᵣ-trans
      (≾ᵣ-reflexive (sym (·ᵣ-identityˡ (mapᵉ ε'''))))
      (≾ᵣ-trans
        (·ᵣ-monoˡ-≾ᵣ (≾ᵣ-reflexive (sym map-uᵉ)))
        (≾ᵣ-reflexive (sym map-·ᵉ))))
step-invariants {S = S} {S' = S'} (HANDLE-STEP {ε₁ = ε₁} {ε₂ = ε₂} {ε₁' = ε₁'} S'·ε₁'≾S·ε₁ step) =
  refl ,
    ≾ᵣ-trans
    (≾ᵣ-reflexive (trans (cong (state-grade S' ·ᵣ_) map-·ᵉ) (sym (·ᵣ-assoc (state-grade S') (mapᵉ ε₁') (mapᵉ ε₂)))))
    (≾ᵣ-trans
      (·ᵣ-monoˡ-≾ᵣ S'·ε₁'≾S·ε₁)
      (≾ᵣ-reflexive
        (trans
          (·ᵣ-assoc (state-grade S) (mapᵉ ε₁) (mapᵉ ε₂))
          (sym (cong (state-grade S ·ᵣ_) map-·ᵉ)))))
step-invariants {S = S} HANDLE-OP =
  refl ,
  ≾ᵣ-reflexive (cong (state-grade S ·ᵣ_) (cong (λ x → mapᵉ x) (sym (·ₑ-assoc (op-grade _) _ _))))
step-invariants BOX                    = refl , ≾ᵣ-refl
step-invariants UNBOX                  = refl , ≾ᵣ-refl
step-invariants (COERCE {ε≾ε' = ε≾ε'}) = refl , ·ᵣ-monoʳ-≾ᵣ (map-monotoneᵉ ε≾ε')
