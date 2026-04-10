open import Syntax.Grades

module OperationalSemantics.PreservationTheorem (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import OperationalSemantics.State (Grades)

open import Syntax.Contexts (Grades)
open import Syntax.Language (Grades)
open import Syntax.Renamings (Grades)
open import Syntax.Substitutions (Grades)
open import Syntax.Types (Grades)

open import Data.Product

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 

open import Util.Operations
open import Util.Time -- TODO: remove

-- record type for Configuratin that encapsulates time, state and computation

record Config (C : CType) : Set where
  constructor ⟨_,_⟩
  field
        state       : 𝕊 []
        computation : toCtx state  ⊢C⦂ C

{-
mutual 
    
    -- small-step operational semantics
    data _↝_ :  {C D : CType} → Config C → Config D → Set where

        -- usual step for function aplication
        APP :   ∀ {A B τ'}
                {S : 𝕊 []} → {M : ((toCtx S) ∷ A) ⊢C⦂ B ‼ τ'} → {V : (toCtx S) ⊢V⦂ A} →
                -------------------------------------------------------------
                ⟨ S , lam M · V ⟩ ↝ ⟨ S , M [ Hd ↦ V ]c ⟩

        -- usual step for match on pair 
        MATCH : ∀ {A B C} →
                {S : 𝕊 []} →  
                {V : toCtx S ⊢V⦂ A } →
                {W : toCtx S ⊢V⦂ B } → 
                {M : toCtx S ∷ A ∷ B ⊢C⦂ C} → 
                -------------------------------------------------------
                ⟨ S , match ⦉ V , W ⦊ `in M ⟩ ↝ 
                ⟨ S , (M [ Hd ↦ V-rename wk-ren W ]c) [ Hd ↦ V ]c ⟩

        -- step for sequencing (time and state must go on)
        SEQ-FST : ∀ {τ₂ τ₃ τ₄} → 
                {A B : VType} → {S S₁ : 𝕊 []} → 
                {M : toCtx S ⊢C⦂ A ‼ τ₂} → 
                {N : ((toCtx S) ⟨ τ₂ ⟩ ∷ A) ⊢C⦂ B ‼ τ₃} → 
                {M₁ : toCtx S₁ ⊢C⦂ A ‼ τ₄} →
                (Sτ+τ₂≡Sτ₁+τ₄ : state-grade S + τ₂ ≡ state-grade S₁ + τ₄) →   
                (M↝M₁ : ⟨ S , M ⟩ ↝ ⟨ S₁ , M₁ ⟩) →
                --------------------------------------------------------------------
                ⟨ S , M ; N ⟩ ↝ 
                ⟨ S₁ , M₁ ;  
                    C-rename 
                        (cong-∷-ren (suc-comp-ren (step-extends-state M↝M₁) (m≡n⇒m≤n Sτ+τ₂≡Sτ₁+τ₄))) 
                        N ⟩ 
        
        -- usual step for return in sequencing
        SEQ-RET : ∀ {A B τ'} → 
                {S : 𝕊 []} → 
                {V : (toCtx S) ⊢V⦂ A} 
                {N : ((toCtx S) ⟨ 0 ⟩ ∷ A) ⊢C⦂ B ‼ τ'} →  
                -----------------------------------------------------------------------------------
                ⟨ S , return V ; N ⟩ ↝ ⟨ S , C-rename (cong-∷-ren ⟨⟩-η-ren) N [ Hd ↦ V ]c ⟩


        -- usual performing operation in sequencing
        SEQ-OP : ∀ {A B τ τ' op} →  
                {S : 𝕊 []} → 
                {V : (toCtx S) ⊢V⦂ type-of-gtype (param op)} 
                {M : toCtx S ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ} →  
                {N : toCtx S ⟨ op-time op + τ ⟩ ∷ A ⊢C⦂ B ‼ τ'} → 
                -----------------------------------------------------------------------------------
                ⟨ S , perform op V M ; N  ⟩ ↝ ⟨ S ,  τ-subst (sym (+-assoc (op-time op) τ τ'))
                             (perform op V
                                (M ;
                                 C-rename (cong-∷-ren (exch-⟨⟩-var-ren ∘ʳ wk-ren ∘ʳ ⟨⟩-μ-ren)) N))  ⟩

        -- delay just pass time further
        DELAY : ∀ {A τ' τ''} → 
                {S : 𝕊 []} →
                {M : toCtx S ⟨ τ' ⟩ ⊢C⦂ A ‼ τ''} → 
                ---------------------------------------------------------------------
                ⟨ S , (delay {τ' = τ''} τ' M) ⟩ ↝ ⟨ time-pass S τ' , M ⟩

        -- usual step for handle return
        HANDLE-RET : ∀ {A B τ'} →
                {S : 𝕊 []} → 
                {V : toCtx S ⊢V⦂ A} →
                {H : (op : Op) → (τ'' : Time) →
                    toCtx S ∷ type-of-gtype (param op)
                      ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ'')
                    ⊢C⦂ B ‼ (op-time op + τ'')} → 
                {N : toCtx S ⟨ 0 ⟩ ∷ A ⊢C⦂ B ‼ τ'} → 
                --------------------------------------------------------------------------
                ⟨ S , handle return V `with H `in N ⟩ ↝ 
                ⟨ S , (C-rename (cong-∷-ren ⟨⟩-η-ren) N) [ Hd ↦ V ]c ⟩ 

        -- step on computation in handle. time and state must go on
        HANDLE-STEP : ∀ {A B τ₁ τ₂ τ₃} → 
                {S S₁ : 𝕊 []} → 
                {M : toCtx S ⊢C⦂ A ‼ τ₂} → 
                {H : (op : Op) → 
                     (τ₃ : Time) →
                     toCtx S ∷ type-of-gtype (param op)
                       ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ₃)
                     ⊢C⦂ B ‼ (op-time op + τ₃)} → 
                {N : toCtx S ⟨ τ₂ ⟩ ∷ A ⊢C⦂ B ‼ τ₁} → 
                {M₁ : toCtx S₁  ⊢C⦂ A ‼ τ₃ } →  
                (Sτ+τ₂≡Sτ₁+τ₃ : state-grade S + τ₂ ≡ state-grade S₁ + τ₃) → 
                (M↝M₁ : ⟨ S , M ⟩ ↝ ⟨ S₁ , M₁ ⟩) →
                -----------------------------------------------------------------------
                ⟨ S , handle M `with H `in N ⟩ ↝ 
                ⟨ S₁ , handle M₁ 
                            `with 
                                (λ op τ'' → 
                                    C-rename 
                                        (cong-∷-ren (cong-∷-ren (≤ₛ⇒Ren (step-extends-state M↝M₁)))) 
                                    (H op τ'')) 
                            `in (C-rename 
                                    (cong-∷-ren (suc-comp-ren (step-extends-state M↝M₁) (m≡n⇒m≤n Sτ+τ₂≡Sτ₁+τ₃))) 
                                N) ⟩

        -- operation handle where we box up result so that the resources
        -- in the result are not used before enough time has passed
        HANDLE-OP : ∀ {A B τ' τ'' op} →
                {S : 𝕊 []} →  
                {V : toCtx S ⊢V⦂ type-of-gtype (param op)} →
                {M : toCtx S ⟨ op-time op ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ τ''} →
                {H : (op : Op) → (τ₁ : Time) →
                    toCtx S ∷ type-of-gtype (param op)
                      ∷ [ op-time op ] (type-of-gtype (arity op) ⇒ B ‼ τ₁)
                    ⊢C⦂ B ‼ (op-time op + τ₁)} → 
                {N : toCtx S ⟨ op-time op + τ'' ⟩ ∷ A ⊢C⦂ B ‼ τ'} → 
                --------------------------------------------------------------------------
                ⟨ S , handle perform op V M `with H `in N ⟩ ↝
                ⟨ S , box (lam (handle M 
                            `with (λ op₁ τ''' → 
                                    C-rename (cong-∷-ren (cong-∷-ren (wk-ren ∘ʳ wk-⟨⟩-ren))) 
                                (H op₁ τ''')) 
                            `in (C-rename ((cong-∷-ren (exch-⟨⟩-var-ren ∘ʳ wk-ren ∘ʳ ⟨⟩-μ-ren)))
                                N))) 
                            ((H op (τ'' + τ')) [ Tl-∷ Hd ↦ V ]c) ⟩

        -- step for box: we just extend our state with new resource
        BOX :   ∀ {A B τ' τ''} → {S : 𝕊 []} → 
                {V : toCtx S ⟨ τ' ⟩ ⊢V⦂ A} →  
                {M : toCtx S ∷ [ τ' ] A ⊢C⦂ B ‼ τ''} →
                -------------------------------------------------------
                ⟨ S , (box V M) ⟩ 
                    ↝ ⟨ extend-state S (V-rename (cong-⟨⟩-ren wk-ctx-renₗ) V) , 
                        M ⟩

        -- step for unbox: we just substitute in M with unboxed resource
        UNBOX : ∀ {A C τ'} → 
                {S : 𝕊 []} → 
                (p : τ' ≤ ctx-time (toCtx S)) → 
                {V : (toCtx S -ᶜ τ' ⊢V⦂ [ τ' ] A)} →
                {M : toCtx S ∷ A ⊢C⦂ C } → 
                ---------------------------------------------------------------------------------------------
                let v-in-c = var-in-ctx V in 
                let x = proj₂ v-in-c in 
                let y = var-ᶜ-+ {τ = τ'} x in 
                ⟨ S , unbox p V M ⟩ 
                    ↝ ⟨ S , 
                        M [ Hd ↦ V-rename (eq-ren ++ᶜ-identityˡ)
                            (resource-pass-to-ctx
                                S 
                                y 
                                (τ-≤-substᵣ 
                                    (sym (grades-≡ (split-state-snd S y))) 
                                    (τ'≤snd-state V)) 
                                (resource-lookup S y)) ]c ⟩
 
    -- Theorem: Step only extends state
    step-extends-state : ∀ {τ'' τ'''} → 
                {S : 𝕊 []} → {S' : 𝕊 []} → 
                {A : VType} → 
                {M : toCtx S ⊢C⦂ A ‼ τ''} → 
                {M' : toCtx S' ⊢C⦂ A ‼ τ'''} → 
                (M↝M' : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩ ) → 
                S ≤ₛ S'
    step-extends-state APP = id-suc
    step-extends-state MATCH = id-suc
    step-extends-state SEQ-RET = id-suc
    step-extends-state SEQ-OP = id-suc
    step-extends-state HANDLE-RET = id-suc
    step-extends-state (UNBOX p) = id-suc 
    step-extends-state HANDLE-OP = id-suc
    step-extends-state DELAY = ⟨⟩-suc _ id-suc
    step-extends-state BOX = ∷-suc _ id-suc
    step-extends-state (SEQ-FST {M = M} {M₁ = M'} τ+τ₂≡τ₁+τ₄ M↝M') = step-extends-state  M↝M'
    step-extends-state (HANDLE-STEP {M = M} {M₁ = M'} τ+τ₄≡τ₇+τ₆ M↝M') = step-extends-state M↝M'


-- preservation theorem

preservation-theorem : ∀ {A B τ'' τ'''}
                → {S S' : 𝕊 []}
                → {M : toCtx S ⊢C⦂ A ‼ τ''}
                → {M' : toCtx S' ⊢C⦂ B ‼ τ'''}
                → ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩
                → A ≡ B × state-grade S + τ'' ≡ state-grade S' + τ'''
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
