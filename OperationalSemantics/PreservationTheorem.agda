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
open import Util.Time -- TODO: remove

-- record type for Configuration that encapsulates time, state and computation

record Config (C : CType) : Set where
  constructor ⟨_,_⟩
  field
        state       : 𝕊 []
        computation : toCtx state  ⊢C⦂ C

mutual 
    
    -- small-step operational semantics
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
        SEQ-FST    : ∀ {ε₁ ε₂ ε₃}
                   → {A B : VType}
                   → {S S' : 𝕊 []}
                   → {M : toCtx S ⊢C⦂ A ‼ ε₁}
                   → {N : ((toCtx S) ⟨ mapᵉ ε₁ ⟩ ∷ A) ⊢C⦂ B ‼ ε₂}
                   → {M' : toCtx S' ⊢C⦂ A ‼ ε₃}
                   → (S·ε₁≡S'·ε₃ : state-grade S ·ᵣ mapᵉ ε₁ ≡ state-grade S' ·ᵣ mapᵉ ε₃)
                   → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
                    --------------------------------------------------------------------
                   → ⟨ S , M ; N ⟩ ↝ 
                     ⟨ S' , M' ; C-rename
                                   (cong-∷-ren (suc-comp-ren (step-extends-state M↝M') S·ε₁≡S'·ε₃))
                                   N ⟩

        -- usual step for return in sequencing
        SEQ-RET    : ∀ {A B ε ε'}
                   → {S : 𝕊 []}
                   → {V : (toCtx S) ⊢V⦂ A}
                   → {u≾ε : uₑ ≾ₑ ε}
                   → {N : ((toCtx S) ∷ A) ⊢C⦂ B ‼ ε'}
                     --------------------------------------------
                   → ⟨ S , return u≾ε V ⟩ ↝ ⟨ S , N [ Hd ↦ V ]c ⟩

        -- usual performing operation in sequencing
        SEQ-OP     : ∀ {A B ε ε' op} 
                   → {S : 𝕊 []} 
                   → {V : (toCtx S) ⊢V⦂ type-of-gtype (param op)} 
                   → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε} 
                   → {N : toCtx S ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε'} 
                    -----------------------------------------------------------------------------------
                   → ⟨ S , (perform op V M) ; N  ⟩ ↝
                     ⟨ S , ε-subst (sym (·ₑ-assoc (op-grade op) ε ε'))
                     (perform op V
                       (M ; C-rename
                              (cong-∷-ren (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren ∘ʳ eq-ren (cong (toCtx S ⟨_⟩) ·-mapᵉ)))
                              N)) ⟩

        -- delay just pass time further
        DELAY      : ∀ {A τ ε}
                   → {S : 𝕊 []}
                   → {M : toCtx S ⟨ embedR τ ⟩ ⊢C⦂ A ‼ ε} → 
                     -------------------------------------------------------------
                     ⟨ S , (delay {ε = ε} τ M) ⟩ ↝ ⟨ grade-pass S (embedR τ) , M ⟩

        -- usual step for handle return
        HANDLE-RET : ∀ {A B ε ε'}
                   → {S : 𝕊 []}
                   → {V : toCtx S ⊢V⦂ A}
                   → {u≾ε : uₑ ≾ₑ ε}
                   →
                     {H : (op : Op)
                        → (ε'' : E)
                        → (Γ' : Ctx)
                        → ⟨⟩-Ctx Γ'
                        → toCtx S ++ᶜ Γ'
                                  ∷ type-of-gtype (param op)
                                  ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                          ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
                   → {N : toCtx S ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
                     --------------------------------------------------------------------------
                   → ⟨ S , handle return u≾ε V `with H `in N ⟩ ↝
                     ⟨ S , (C-rename
                             (cong-∷-ren
                               (⟨⟩-η-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-trans (≾ᵣ-reflexive (sym uₑ≡ᵣuᵣ)) (pres-≾ᵉ u≾ε))))
                             N) [ Hd ↦ V ]c ⟩
                     
        -- step on computation in handle. time and state must go on
        HANDLE-STEP : ∀ {A B ε₁ ε₂ ε₁'}
                    → {S S' : 𝕊 []}
                    → {M : toCtx S ⊢C⦂ A ‼ ε₁}
                    → {H : (op : Op) → (ε₃ : E) → (Γ' : Ctx) → ⟨⟩-Ctx Γ' →
                         toCtx S ++ᶜ Γ'
                                 ∷ type-of-gtype (param op)
                                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₃)
                               ⊢C⦂ B ‼ (op-grade op ·ₑ ε₃)} 
                    → {N : toCtx S ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂}
                    → {M' : toCtx S' ⊢C⦂ A ‼ ε₁'}
                    → (S·ε₁≡S'·ε₁' : state-grade S ·ᵣ mapᵉ ε₁ ≡ state-grade S' ·ᵣ mapᵉ ε₁')
                    → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
                      -----------------------------------------------------------------------
                    → ⟨ S , handle M `with H `in N ⟩ ↝ 
                      ⟨ S' , handle M' 
                            `with 
                                (λ op τ'' Γ' Γ'' → 
                                    C-rename
                                      (cong-∷-ren (cong-∷-ren (cong-ren ((≤ₛ⇒Ren (step-extends-state M↝M'))))))
                                      (H op τ'' Γ' Γ'') )
                            `in (C-rename 
                                    (cong-∷-ren (suc-comp-ren (step-extends-state M↝M') S·ε₁≡S'·ε₁'))
                                N) ⟩

        -- operation handle where we box up result so that the resources
        -- in the result are not used before enough time has passed
        HANDLE-OP   : ∀ {A B ε ε'' op Γ'}
                    → {Γ''' : ⟨⟩-Ctx Γ'}
                    → {S : 𝕊 []} 
                    → {V : toCtx S ⊢V⦂ type-of-gtype (param op)}
                    → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
                    → {H : (op' : Op) → (ε' : E) → (Γ' : Ctx) → ⟨⟩-Ctx Γ' →
                             toCtx S ++ᶜ Γ'
                                     ∷ type-of-gtype (param op')
                                     ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε')
                                   ⊢C⦂ B ‼ (op-grade op' ·ₑ ε')}
                    → {N : toCtx S ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε''} 
                      --------------------------------------------------------------------------
                    → ⟨ S , handle perform op V M `with H `in N ⟩ ↝
                      ⟨ S , box (lam
                              (handle M
                              `with (λ op₁ ε''' Γ'' Γ''' →
                                  C-rename
                                    (cong-∷-ren (cong-∷-ren (cong-ren wk-ren
                                         ∘ʳ eq-ren (sym (++ᶜ-assoc (toCtx S) ([] ⟨ mapᵉ (op-grade op) ⟩) Γ'')))))
                                    (H op₁ ε''' ([] ⟨ mapᵉ (op-grade op) ⟩ ++ᶜ Γ'')
                                      (++ᶜ-⟨⟩ (is-⟨⟩ {ρ = mapᵉ (op-grade op)} is-[]) Γ''')))
                              `in (C-rename
                                    (cong-∷-ren (cong-⟨⟩-ren wk-ren
                                    ∘ʳ ⟨⟩-μ-ren
                                    ∘ʳ eq-ren (cong (toCtx S ⟨_⟩) ·-mapᵉ)))
                                    N)))
                             (H op (ε ·ₑ ε'') [] is-[] [ Tl-∷ Hd ↦ V ]c) ⟩ 

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
                    → (ρ'≾ρ : ρ' ≾ᵣ ρ)
                    → (u≾ρ : uᵣ ≾ᵣ ρ) -- required condition to have the renaming
                    → {M : toCtx S ∷ A ⊢C⦂ C} 
                      ----------------------------------------------------------
                    → ⟨ S , unbox x ρ'≾ρ M ⟩ ↝
                      ⟨ S , M [ Hd ↦
                                V-rename
                                  (eq-ren ++ᶜ-identityˡ)
                                  (resource-pass-to-ctx
                                    S
                                    x
                                    u≾ρ
                                    (≾ᵣ-trans (≾ᵣ-reflexive
                                      (trans
                                        (cong ctx-grade (snd-split-state≡split-ctx S x))
                                        (proj₂ (proj₂ (proj₂ (var-split x)))))) ρ'≾ρ)
                                    (resource-lookup S x)) ]c ⟩ 
                {-
                let v-in-c = var-in-ctx V in 
                let x = proj₂ v-in-c in 
                let y = ? in --var-ᶜ-+ {τ = τ'} x in 
                ⟨ S , unbox p V M ⟩ 
                    ↝ ⟨ S , 
                        M [ Hd ↦ V-rename (eq-ren ++ᶜ-identityˡ)
                            (resource-pass-to-ctx
                                S 
                                y 
                                (τ-≤-substᵣ 
                                    (sym (grades-≡ (split-state-snd S y))) 
                                    ?) --(τ'≤snd-state V)) 
                                (resource-lookup S y)) ]c ⟩ -}

-- step for coerce terms in a sequence of computations
        COERCE-RET  : ∀ {A ε ε'} 
                    → {S : 𝕊 []}
                    → {V : toCtx S ⊢V⦂ A}
                    → {uₑ≾ε : uₑ ≾ₑ ε}
                    → {ε≾ε' : ε ≾ₑ ε'}
                      ----------------------------------------------------------
                    → ⟨ S , coerce ε≾ε' (return uₑ≾ε V) ⟩ ↝
                      ⟨ S , return (≾ₑ-trans uₑ≾ε ε≾ε') V ⟩

    -- Theorem: Step only extends state
    step-extends-state : ∀ {ε ε'}
                       → {S S' : 𝕊 []}
                       → {A : VType}
                       → {M : toCtx S ⊢C⦂ A ‼ ε}
                       → {M' : toCtx S' ⊢C⦂ A ‼ ε'}
                       → (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩ )
                       -----------------------------------
                       → S ≤ₛ S'
                       
    step-extends-state APP =
      id-suc
    step-extends-state MATCH =
      id-suc
    step-extends-state (SEQ-FST _ x) =
      step-extends-state x
    step-extends-state SEQ-RET =
      id-suc
    step-extends-state SEQ-OP =
      id-suc
    step-extends-state {S = S} {S' = .(S ⟨ embedR τ ⟩ₛ)} {A} (DELAY {τ = τ}) =
      {!!}
    step-extends-state HANDLE-RET =
      id-suc
    step-extends-state (HANDLE-STEP _ x) =
      step-extends-state x
    step-extends-state HANDLE-OP =
      id-suc
    step-extends-state BOX =
      ∷-suc (V-rename (eq-ren (sym ++ᶜ-identityˡ)) _) id-suc
    step-extends-state (UNBOX ρ'≾ρ u≾ρ) =
      id-suc
    step-extends-state COERCE-RET =
      {!!}

-- preservation theorem

preservation-theorem : ∀ {A B ε'' ε'''}
                     → {S S' : 𝕊 []}
                     → {M : toCtx S ⊢C⦂ A ‼ ε''}
                     → {M' : toCtx S' ⊢C⦂ B ‼ ε'''}
                     → ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩
                     → A ≡ B × state-grade S ·ᵣ (mapᵉ ε'') ≡ state-grade S' ·ᵣ (mapᵉ ε''')

preservation-theorem step = {!!}

{-
preservation-theorem APP = refl , refl
preservation-theorem MATCH = refl , refl
preservation-theorem {S = S} {S' = S'} (SEQ-FST {τ₂ = τ₂} {τ₃} {τ₄} τ+τ₂≡τ₁+τ₄ M↝M') = 
    refl , τ+τ₂≡τ₁+τ₄⇒τ+[τ₂+τ₃]≡τ₁+[τ₄+τ₃] (state-grade S) (state-grade S') τ₂ τ₃ τ₄ τ+τ₂≡τ₁+τ₄
preservation-theorem SEQ-RET = refl , refl
preservation-theorem SEQ-OP = refl , refl
preservation-theorem {τ''' = τ'''} {S = S} (DELAY {τ' = τ'}) = 
    refl , sym (+-assoc (state-grade S) τ' τ''')
preservation-theorem HANDLE-RET = refl , refl
preservation-theorem {S = S} {S' = S'} (HANDLE-STEP {τ₁ = τ₁} {τ₂} {τ₃} τ+τ₂≡τ₄+τ₃ M↝M') = 
    refl , τ+τ₂≡τ₁+τ₄⇒τ+[τ₂+τ₃]≡τ₁+[τ₄+τ₃] (state-grade S) (state-grade S') τ₂ τ₁ τ₃ τ+τ₂≡τ₄+τ₃
preservation-theorem {S = S} (HANDLE-OP {τ' = τ'} {τ'' = τ''} {op = op}) = 
    refl , cong ((state-grade S) +_) (+-assoc (op-time op) τ'' τ')
preservation-theorem BOX = refl , refl
preservation-theorem (UNBOX p) = refl , refl 
-}
