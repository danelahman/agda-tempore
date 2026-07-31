open import Data.Product

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.CompContext (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.RenActions S
open import Syntax.Renamings  S
open import Syntax.Types      S

-- Computation term context flags. They characterise whether
-- it is an arbitrary term context, an evaluation context, or
-- a state-induced context. Flags come together with a simple
-- lattice structure that is used in the def. of contexts.

data Flag : Set where
  all  : Flag
  eval : Flag
  state : Flag

data _≤ᶠ_ : Flag → Flag → Set where
  f≤ᶠf : ∀ {f : Flag} → f ≤ᶠ f
  e≤ᶠa : eval ≤ᶠ all
  s≤ᶠa : state ≤ᶠ all

infixl 31 _≤ᶠ_

≤ᶠ-trans : ∀ {f f' f''}
         → f ≤ᶠ f'
         → f' ≤ᶠ f''
         → f ≤ᶠ f''
≤ᶠ-trans f≤ᶠf q = q
≤ᶠ-trans e≤ᶠa f≤ᶠf = e≤ᶠa
≤ᶠ-trans s≤ᶠa f≤ᶠf = s≤ᶠa

_∨ᶠ_ : Flag → Flag → Flag
all   ∨ᶠ all = all
all   ∨ᶠ eval = all
all   ∨ᶠ state = all
eval  ∨ᶠ all = all
eval  ∨ᶠ eval = eval
eval  ∨ᶠ state = all
state ∨ᶠ all = all
state ∨ᶠ eval = all
state ∨ᶠ state = state

infixl 32 _∨ᶠ_

∨ᶠ-inl : ∀ {f f'}
       → f ≤ᶠ f ∨ᶠ f'
∨ᶠ-inl {all} {all} = f≤ᶠf
∨ᶠ-inl {all} {eval} = f≤ᶠf
∨ᶠ-inl {all} {state} = f≤ᶠf
∨ᶠ-inl {eval} {all} = e≤ᶠa
∨ᶠ-inl {eval} {eval} = f≤ᶠf
∨ᶠ-inl {eval} {state} = e≤ᶠa
∨ᶠ-inl {state} {all} = s≤ᶠa
∨ᶠ-inl {state} {eval} = s≤ᶠa
∨ᶠ-inl {state} {state} = f≤ᶠf

∨ᶠ-inr : ∀ {f f'}
       → f' ≤ᶠ f ∨ᶠ f'
∨ᶠ-inr {all} {all} = f≤ᶠf
∨ᶠ-inr {all} {eval} = e≤ᶠa
∨ᶠ-inr {all} {state} = s≤ᶠa
∨ᶠ-inr {eval} {all} = f≤ᶠf
∨ᶠ-inr {eval} {eval} = f≤ᶠf
∨ᶠ-inr {eval} {state} = s≤ᶠa
∨ᶠ-inr {state} {all} = f≤ᶠf
∨ᶠ-inr {state} {eval} = e≤ᶠa
∨ᶠ-inr {state} {state} = f≤ᶠf

-- Computation term contexts. The allowed cases depend on the
-- given flag.

data _⊢K[_◁_]⦂_ (Γ : Ctx) (f : Flag) (CH : CType) : CType → Set where

    -- holes in computation term contexts

    []ₖ :  
        --------------------
          Γ ⊢K[ f ◁ CH ]⦂ CH

    -- sub-effecting coercions
    --
    -- Neither an evaluation nor a state-induced former, hence available only
    -- at `all`: reduction discards a coercion outright (`COERCE`) rather than
    -- descending into it, and a state's telescope carries no coercion.

    coerce[_]ₖ : ∀ {A ε ε'}
        → all ≤ᶠ f
        → ε ≾ₑ ε'
        → Γ ⊢K[ f ◁ CH ]⦂ A ‼ ε
        --------------------------
        → Γ ⊢K[ f ◁ CH ]⦂ A ‼ ε'

    -- state specific computation term contexts

    perform[_]ₖ : ∀ {A ε}
        → state ≤ᶠ f
        → (op : Op)
        → Γ ⊢V⦂ type-of-gtype (param op)
        → Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢K[ f ◁ CH ]⦂ A ‼ ε
        -------------------------------------------------------------------------------
        → Γ ⊢K[ f ◁ CH ]⦂ A ‼ (op-grade op ·ₑ ε)
    
    delay[_]ₖ : ∀ {A ε}
        → state ≤ᶠ f
        → (τ : ℕ)
        → Γ ⟨ of-natʳ τ ⟩ ⊢K[ f ◁ CH ]⦂ A ‼ ε
        -----------------------------------------
        → Γ ⊢K[ f ◁ CH ]⦂ A ‼ (of-natᵉ τ ·ₑ ε)

    unbox[_]ₖ : ∀ {A C ρ ρ'}
        → state ≤ᶠ f
        → [ ρ ] A ∈[ ρ' ] Γ
        → ρ' ≾ᵣ ρ
        → Γ ∷ A ⊢K[ f ◁ CH ]⦂ C
        -------------------------
        → Γ ⊢K[ f ◁ CH ]⦂ C
    
    box[_]ₖ : ∀ {A C ρ}
        → state ≤ᶠ f
        → Γ ⟨ ρ ⟩ ⊢V⦂ A
        → Γ ∷ [ ρ ] A ⊢K[ f ◁ CH ]⦂ C
        --------------------------------
        → Γ ⊢K[ f ◁ CH ]⦂ C

    -- evaluation specific computation term contexts

    _ₖ[_]⨟_ : ∀ {Aₖ A εₖ ε}
        → Γ ⊢K[ f ◁ CH ]⦂ Aₖ ‼ εₖ
        → eval ≤ᶠ f
        → Γ ⟨ mapᵉ εₖ ⟩ ∷ Aₖ ⊢C⦂ A ‼ ε
        ----------------------------------
        → Γ ⊢K[ f ◁ CH ]⦂ A ‼ (εₖ ·ₑ ε)
    
    handle[_]ₖ_`with_`in
        : ∀ {A B ε ε'}
        → eval ≤ᶠ f
        → Γ ⊢K[ f ◁ CH ]⦂ A ‼ ε
        → ((op : Op) → (ε'' : E) →
             Γ ᴱ ∷ type-of-gtype (param op)
               ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
             ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
        → Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'
        --------------------------------------------------------------
        → Γ ⊢K[ f ◁ CH ]⦂ B ‼ (ε ·ₑ ε')


-- Contexts of the hole in a computation term context
-- (the relative version, against arbitrary ctx Γ')
-- (turns a computation term contexts into a Hughes list)

rel-hole-ctx : ∀ {Γ f CH C} → Γ ⊢K[ f ◁ CH ]⦂ C → Ctx → Ctx

rel-hole-ctx []ₖ Γ' =
  Γ'
rel-hole-ctx (coerce[ p ]ₖ q K) Γ' =
  rel-hole-ctx K Γ'
rel-hole-ctx (K ₖ[ p ]⨟ N) Γ' =
  rel-hole-ctx K Γ'
rel-hole-ctx (perform[_]ₖ p op V K) Γ' =
  rel-hole-ctx K (Γ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op))
rel-hole-ctx (handle[ p ]ₖ K `with H `in N) Γ' =
  rel-hole-ctx K Γ'
rel-hole-ctx (delay[ p ]ₖ τ K) Γ' =
  rel-hole-ctx K (Γ' ⟨ of-natʳ τ ⟩)
rel-hole-ctx (unbox[_]ₖ {A = A} p x rel K) Γ' =
  rel-hole-ctx K (Γ' ∷ A)
rel-hole-ctx (box[_]ₖ {A = A} {ρ = ρ} p V K) Γ' =
  rel-hole-ctx K (Γ' ∷ [ ρ ] A)

-- Contexts of the hole in a computation term context
-- (the relative version, with only the vars bound in K)

hole-ctx : ∀ {Γ f CH C} → Γ ⊢K[ f ◁ CH ]⦂ C → Ctx
hole-ctx K = rel-hole-ctx K []

-- Relating the absolute and relative versions of hole-ctx

rel-hole-ctx-++ᶜ : ∀ {Γ Γ' Γ'' f CH C}
                 → (K : Γ ⊢K[ f ◁ CH ]⦂ C)
                 → rel-hole-ctx K (Γ' ++ᶜ Γ'') ≡ Γ' ++ᶜ rel-hole-ctx K Γ''

rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} []ₖ =
  refl
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (coerce[ p ]ₖ q K) =
  rel-hole-ctx-++ᶜ K
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (K ₖ[ p ]⨟ N) =
  rel-hole-ctx-++ᶜ K
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (perform[ p ]ₖ op V K) =
  rel-hole-ctx-++ᶜ K
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (handle[ p ]ₖ K `with H `in N) =
  rel-hole-ctx-++ᶜ K
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (delay[ p ]ₖ τ K) =
  rel-hole-ctx-++ᶜ K
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (unbox[ p ]ₖ x rel K) =
  rel-hole-ctx-++ᶜ K
rel-hole-ctx-++ᶜ {Γ} {Γ'} {Γ''} (box[ p ]ₖ V K) =
  rel-hole-ctx-++ᶜ K

-- Monotonicity of computation term contexts with respect to flags

◁-mon : ∀ {Γ CH C f f'}
      → f ≤ᶠ f'
      → Γ ⊢K[ f ◁ CH ]⦂ C
      → Γ ⊢K[ f' ◁ CH ]⦂ C
      
◁-mon {f = f} {f' = f'} p []ₖ =
  []ₖ
◁-mon {f = f} {f' = f'} p (coerce[ q ]ₖ r K) =
  coerce[ ≤ᶠ-trans q p ]ₖ r (◁-mon p K)
◁-mon {f = f} {f' = f'} p (K ₖ[ q ]⨟ N) =
  (◁-mon p K) ₖ[ ≤ᶠ-trans q p ]⨟ N
◁-mon {f = f} {f' = f'} p (perform[ q ]ₖ op V K) =
  perform[ ≤ᶠ-trans q p ]ₖ op V (◁-mon p K)
◁-mon {f = f} {f' = f'} p (handle[ q ]ₖ K `with H `in N) =
  handle[ ≤ᶠ-trans q p ]ₖ (◁-mon p K) `with H `in N
◁-mon {f = f} {f' = f'} p (delay[ q ]ₖ τ K) =
  delay[ ≤ᶠ-trans q p ]ₖ τ (◁-mon p K)
◁-mon {f = f} {f' = f'} p (unbox[ q ]ₖ x rel K) =
  unbox[ ≤ᶠ-trans q p ]ₖ x rel (◁-mon p K)
◁-mon {f = f} {f' = f'} p (box[ q ]ₖ V K) =
  box[ ≤ᶠ-trans q p ]ₖ V (◁-mon p K)

-- Renaming of computation term contexts

K-rename : ∀ {Γ Γ' CH C f}
         → Ren [] Γ' Γ
         → Γ ⊢K[ f ◁ CH ]⦂ C
         ---------------
         → Γ' ⊢K[ f ◁ CH ]⦂ C

K-rename r []ₖ =
  []ₖ
K-rename r (coerce[ p ]ₖ q K) =
  coerce[ p ]ₖ q (K-rename r K)
K-rename r (K ₖ[ p ]⨟ N) =
  (K-rename r K) ₖ[ p ]⨟ (C-rename (cong-ren r) N)
K-rename r (perform[ p ]ₖ op V K) =
  perform[ p ]ₖ op (V-rename r V) (K-rename (cong-ren r) K)
K-rename r (handle[ p ]ₖ K `with H `in N) =
  handle[ p ]ₖ K-rename r K
    `with (λ op ε'' →
             C-rename (cong-∷-ren (cong-∷-ren (restrict-ren r))) (H op ε''))
    `in (C-rename (cong-ren r) N)
K-rename r (delay[ p ]ₖ τ K) =
  delay[ p ]ₖ τ (K-rename (cong-ren r) K)
K-rename r (unbox[ p ]ₖ x rel K) =
  unbox[ p ]ₖ (proj₁ (proj₂ (rvar-rename r x)))
              (≾ᵣ-trans (proj₂ (proj₂ (rvar-rename r x))) rel)
              (K-rename (cong-ren r) K)
K-rename r (box[ p ]ₖ V K) =
  box[ p ]ₖ (V-rename (cong-ren r) V) (K-rename (cong-ren r) K)

-- Composition of computation term contexts

_[_]ₖ : ∀ {Γ CH CH' C f f'}
      → (K : Γ ⊢K[ f ◁ CH ]⦂ C)
      → (L : Γ ++ᶜ hole-ctx K ⊢K[ f' ◁ CH' ]⦂ CH)
      → Γ ⊢K[ f ∨ᶠ f' ◁ CH' ]⦂ C

[]ₖ [ L ]ₖ =
  ◁-mon ∨ᶠ-inr L
coerce[ p ]ₖ q K [ L ]ₖ =
  coerce[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ q (K [ L ]ₖ)
(K ₖ[ p ]⨟ N) [ L ]ₖ =
  (K [ L ]ₖ) ₖ[ ≤ᶠ-trans p ∨ᶠ-inl ]⨟ N
perform[ p ]ₖ op V K [ L ]ₖ =
  perform[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ op V
    (K [ K-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ⟨ _ ⟩ ∷ _) (hole-ctx K))))) L ]ₖ)
handle[ p ]ₖ K `with H `in N [ L ]ₖ =
  handle[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ (K [ L ]ₖ) `with H `in N
delay[ p ]ₖ τ K [ L ]ₖ =
  delay[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ τ
    (K [ K-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ⟨ _ ⟩) (hole-ctx K))))) L ]ₖ)
unbox[ p ]ₖ x rel K [ L ]ₖ =
  unbox[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ x rel
    (K [ K-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ∷ _) (hole-ctx K))))) L ]ₖ)
box[ p ]ₖ V K [ L ]ₖ =
  box[ ≤ᶠ-trans p ∨ᶠ-inl ]ₖ V
    (K [ K-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ∷ _) (hole-ctx K))))) L ]ₖ)

-- Filling a computation term context hole with a computation

_[_] : ∀ {Γ CH C f} 
     → (K : Γ ⊢K[ f ◁ CH ]⦂ C) 
     → (M : Γ ++ᶜ hole-ctx K ⊢C⦂ CH) 
     → Γ ⊢C⦂ C

[]ₖ [ N ] =
  N
coerce[ p ]ₖ q K [ N ] =
  coerce q (K [ N ])
(K ₖ[ p ]⨟ M) [ N ] =
  (K [ N ]) ⨟ M
perform[ p ]ₖ op V K [ N ] =
  perform op V
    (K [ C-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ⟨ _ ⟩ ∷ _) (hole-ctx K))))) N ])
handle[ p ]ₖ K `with H `in M [ N ] =
  handle (K [ N ]) `with H `in M
delay[ p ]ₖ τ K [ N ] =
  delay τ
    (K [ C-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ⟨ _ ⟩) (hole-ctx K))))) N ])
unbox[ p ]ₖ x rel K [ N ] =
  unbox x rel
    (K [ C-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ∷ _) (hole-ctx K))))) N ])
box[ p ]ₖ V K [ N ] =
  box V
    (K [ C-rename (eq-ren
           (trans
             (cong (_ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
             (sym (++ᶜ-assoc _ ([] ∷ _) (hole-ctx K))))) N ])
