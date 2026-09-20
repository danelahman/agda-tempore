------------------------------------------------------------------
-- Principality and refutation for the driver, against the       --
-- biased satisfaction of `TypeInference.Solver.Fragment`.       --
------------------------------------------------------------------

open import Data.Bool.Base using (true) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (suc-injective) renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_; mapMaybe)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.Open.Hyps as H

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Principal
  (S : LanguageSpec)
  (_≾ᵣ?_ : Decidable (Grade._≾_ (GradeSystem.RGrade (LanguageSpec.Grades S))))
  (_≾ₑ?_ : Decidable (Grade._≾_ (GradeSystem.EGrade (LanguageSpec.Grades S))))
  (opEnum : OpEnum S)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S
open import TypeInference.Open.Hyps   S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S
open import TypeInference.Constraints.Properties   S using (≐ˢ-sym)

open import TypeInference.Solver.Fragment S

open import TypeInference.SolverImpl.Enum S using (AllOp; all-lookup)

open import TypeInference.SolverImpl.Core.AList S using (AList; anil; ⟦_⟧ᴬ)
open import TypeInference.SolverImpl.Core.Eqn   S using (Eqn; eqᵛ; Eqns; Unifies)
open import TypeInference.SolverImpl.Core.Rigid S
  using (strʳ⁺; strᵉ⁺; strᵛ⁺; popˢ; strSub; unpopˢ; pop-unpop; strSub-escape)
open import TypeInference.SolverImpl.Core.Unify S using (Rig; _∈ᶠ_; unify)
open import TypeInference.SolverImpl.Core.UnifyMGU S
  using (Fixing; fixing; fixᵉ; injᵉ; Fixing-id; unify-max; unify-fail;
         evar-inj; ∨-true; ∨-left; ∨-right; dec-true; true-dec)

open import TypeInference.SolverImpl.Resid  S
open import TypeInference.SolverImpl.State  S
open import TypeInference.SolverImpl.Normal S _≾ᵣ?_ _≾ₑ?_ umin?ᵣ umin?ₑ
open import TypeInference.SolverImpl.Solve  S _≾ᵣ?_ _≾ₑ?_ opEnum umin?ᵣ umin?ₑ

open OpEnum opEnum

⊥just : ∀ {X Y : Set} {x : X} → nothing ≡ just x → Y
⊥just ()

⊥nothing : ∀ {X Y : Set} {x : X} → just x ≡ nothing → Y
⊥nothing ()

-- A weakening is undone by an extension

wk-,ᵗ : ∀ {Ψ Ψ'} → (δ : Subst Ψ Ψ') → (B : OVType Ψ') → (wkˢᵗ ⨟ˢ (δ ,ᵗ B)) ≐ˢ δ
wk-,ᵗ δ B = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

wk-,ʳ : ∀ {Ψ Ψ'} → (δ : Subst Ψ Ψ') → (ρ : RExp Ψ') → (wkˢʳ ⨟ˢ (δ ,ʳ ρ)) ≐ˢ δ
wk-,ʳ δ ρ = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

wk-,ᵉ : ∀ {Ψ Ψ'} → (δ : Subst Ψ Ψ') → (ε : EExp Ψ') → (wkˢᵉ ⨟ˢ (δ ,ᵉ ε)) ≐ˢ δ
wk-,ᵉ δ ε = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

-- A lift absorbs a following extension

↑-,ᵗˢ : ∀ {Θ Θ₁ Θ'} → (δ : Subst Θ Θ₁) → (σ : Subst Θ₁ Θ') → (B : OVType Θ')
      → ((δ ↑ᵗ) ⨟ˢ (σ ,ᵗ B)) ≐ˢ ((δ ⨟ˢ σ) ,ᵗ B)
↑-,ᵗˢ δ σ B = mk≐ˢ (λ { zero → refl ; (suc α) → wk-,ᵗ-v σ B (sTy δ α) })
                   (λ i → wk-,ᵗ-r σ B (sR δ i))
                   (λ i → wk-,ᵗ-e σ B (sE δ i))

↑-,ʳˢ : ∀ {Θ Θ₁ Θ'} → (δ : Subst Θ Θ₁) → (σ : Subst Θ₁ Θ') → (ρ : RExp Θ')
      → ((δ ↑ʳ) ⨟ˢ (σ ,ʳ ρ)) ≐ˢ ((δ ⨟ˢ σ) ,ʳ ρ)
↑-,ʳˢ δ σ ρ = mk≐ˢ (λ α → wk-,ʳ-v σ ρ (sTy δ α))
                   (λ { zero → refl ; (suc i) → wk-,ʳ-r σ ρ (sR δ i) })
                   (λ i → wk-,ʳ-e σ ρ (sE δ i))

↑-,ᵉˢ : ∀ {Θ Θ₁ Θ'} → (δ : Subst Θ Θ₁) → (σ : Subst Θ₁ Θ') → (ε : EExp Θ')
      → ((δ ↑ᵉ) ⨟ˢ (σ ,ᵉ ε)) ≐ˢ ((δ ⨟ˢ σ) ,ᵉ ε)
↑-,ᵉˢ δ σ ε = mk≐ˢ (λ α → wk-,ᵉ-v σ ε (sTy δ α))
                   (λ i → wk-,ᵉ-r σ ε (sR δ i))
                   (λ { zero → refl ; (suc i) → wk-,ᵉ-e σ ε (sE δ i) })

-- `κᵉ` sends the newest effect-grade variable to the unit, fixing the
-- rest; being a substitution, entailment survives it.

κᵉ : ∀ {Ψ} → Subst (Ψ +e) Ψ
κᵉ = sub tvar rvar (λ { zero → ûₑ ; (suc i) → evar i })

wk-κᵉ : ∀ {Ψ} → (wkˢᵉ {Ψ} ⨟ˢ κᵉ) ≐ˢ idˢ
wk-κᵉ = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

κᵉ-wkᵛ : ∀ {Ψ} → (A : OVType Ψ) → wkᵉ-v A [ κᵉ ]ᵛ ≡ A
κᵉ-wkᵛ A = trans (cong (_[ κᵉ ]ᵛ) (sym (wkˢᵉ-v A)))
                 (trans ([⨟]ᵛ A wkˢᵉ κᵉ) (trans ([≐]ᵛ wk-κᵉ A) ([id]ᵛ A)))

κᵉ-wkʳ : ∀ {Ψ} → (ρ : RExp Ψ) → wkᵉ-r ρ [ κᵉ ]ʳ ≡ ρ
κᵉ-wkʳ ρ = trans (cong (_[ κᵉ ]ʳ) (sym (wkˢᵉ-r ρ)))
                 (trans ([⨟]ʳ ρ wkˢᵉ κᵉ) (trans ([≐]ʳ wk-κᵉ ρ) ([id]ʳ ρ)))

κᵉ-wkᵉ : ∀ {Ψ} → (ε : EExp Ψ) → wkᵉ-e ε [ κᵉ ]ᵉ ≡ ε
κᵉ-wkᵉ ε = trans (cong (_[ κᵉ ]ᵉ) (sym (wkˢᵉ-e ε)))
                 (trans ([⨟]ᵉ ε wkˢᵉ κᵉ) (trans ([≐]ᵉ wk-κᵉ ε) ([id]ᵉ ε)))

-- Every weakened hypothesis is entailed back by the original set

⊩ᴴ-κᵉ : ∀ {Ψ} {Q : Hyps Ψ} → Q ⊩ᴴ (wkᵉ-H Q) [ κᵉ ]
⊩ᴴ-κᵉ {Ψ} {Q} = mk⊩ᴴ ets' ordᵣ' ordₑ' disj'
  where
    ets' : ∀ {α} → α ∈ ets (wkᵉ-H Q) → Q ⊩ᴱ sTy κᵉ α
    ets' m with ∈-map⁻ (wkᵉ-tv Ψ) m
    ... | α₀ , m₀ , refl = et-hyp m₀

    ordᵣ' : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ (wkᵉ-H Q) → Q ⊩ ρ [ κᵉ ]ʳ ≾̂ᵣ ρ' [ κᵉ ]ʳ
    ordᵣ' m with ∈-map⁻ (mapᵖ wkᵉ-r) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
      subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym (κᵉ-wkʳ ρ₀)) (sym (κᵉ-wkʳ ρ₀')) (hypᵣ m₀)

    ordₑ' : ∀ {ε ε'} → (ε , ε') ∈ ordₑ (wkᵉ-H Q) → Q ⊩ ε [ κᵉ ]ᵉ ≾̂ₑ ε' [ κᵉ ]ᵉ
    ordₑ' m with ∈-map⁻ (mapᵖ wkᵉ-e) m
    ... | (ε₀ , ε₀') , m₀ , refl =
      subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym (κᵉ-wkᵉ ε₀)) (sym (κᵉ-wkᵉ ε₀')) (hypₑ m₀)

    disj' : ∀ {A ρ} → (A , ρ) ∈ disj (wkᵉ-H Q) → VarOK Q (A [ κᵉ ]ᵛ) (ρ [ κᵉ ]ʳ)
    disj' m with ∈-map⁻ (mapᵈ wkᵉ-v wkᵉ-r) m
    ... | (A₀ , ρ₀) , m₀ , refl =
      subst₂ (VarOK Q) (sym (κᵉ-wkᵛ A₀)) (sym (κᵉ-wkʳ ρ₀)) (hyp-ok m₀)

-- The converse of `⊩ᴿ-subst`

⊩ᴿ-subst⁻ : ∀ {Ψ Ψ₁ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ}
              {σ : Subst Ψ Ψ₁} {δ : Subst Ψ₁ Ψ'}
          → Q ⊩ᴿ R [ σ ⨟ˢ δ ] → Q ⊩ᴿ (R [ σ ]ᴿ) [ δ ]
⊩ᴿ-subst⁻ {Q = Q} {R = R} {σ = σ} {δ = δ} h = mk⊩ᴿ rs' es' ts' ds'
  where
    rs' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs (R [ σ ]ᴿ) → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    rs' m with ∈-map⁻ (mapᵖ (_[ σ ]ʳ)) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
      subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym ([⨟]ʳ ρ₀ σ δ)) (sym ([⨟]ʳ ρ₀' σ δ)) (⊩rs h m₀)

    es' : ∀ {ε ε'} → (ε , ε') ∈ es (R [ σ ]ᴿ) → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
    es' m with ∈-map⁻ (mapᵖ (_[ σ ]ᵉ)) m
    ... | (ε₀ , ε₀') , m₀ , refl =
      subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym ([⨟]ᵉ ε₀ σ δ)) (sym ([⨟]ᵉ ε₀' σ δ)) (⊩es h m₀)

    ts' : ∀ {A} → A ∈ ts (R [ σ ]ᴿ) → Q ⊩ᴱ A [ δ ]ᵛ
    ts' m with ∈-map⁻ (_[ σ ]ᵛ) m
    ... | A₀ , m₀ , refl = subst (Q ⊩ᴱ_) (sym ([⨟]ᵛ A₀ σ δ)) (⊩ts h m₀)

    ds' : ∀ {A ρ} → (A , ρ) ∈ ds (R [ σ ]ᴿ) → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ)
    ds' m with ∈-map⁻ (mapᵈ (_[ σ ]ᵛ) (_[ σ ]ʳ)) m
    ... | (A₀ , ρ₀) , m₀ , refl =
      subst₂ (VarOK Q) (sym ([⨟]ᵛ A₀ σ δ)) (sym ([⨟]ʳ ρ₀ σ δ)) (⊩ds h m₀)

-- Both components of a union

∪ᴿ-both : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R R' : Resid Ψ} {δ : Subst Ψ Ψ'}
        → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ R' [ δ ] → Q ⊩ᴿ (R ∪ᴿ R') [ δ ]
∪ᴿ-both {R = R} h h' =
  mk⊩ᴿ (λ m → [ ⊩rs h , ⊩rs h' ]′ (∈-++⁻ (rs R) m))
       (λ m → [ ⊩es h , ⊩es h' ]′ (∈-++⁻ (es R) m))
       (λ m → [ ⊩ts h , ⊩ts h' ]′ (∈-++⁻ (ts R) m))
       (λ m → [ ⊩ds h , ⊩ds h' ]′ (∈-++⁻ (ds R) m))

-- Pushing one atom

pushʳ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {ρ ρ' : RExp Ψ} {δ : Subst Ψ Ψ'}
        → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushʳ ρ ρ' R) [ δ ]
pushʳ-⊩ p h =
  mk⊩ᴿ (λ { (here refl) → p ; (there m) → ⊩rs h m }) (⊩es h) (⊩ts h) (⊩ds h)

pushᵉ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {ε ε' : EExp Ψ} {δ : Subst Ψ Ψ'}
        → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushᵉ ε ε' R) [ δ ]
pushᵉ-⊩ p h =
  mk⊩ᴿ (⊩rs h) (λ { (here refl) → p ; (there m) → ⊩es h m }) (⊩ts h) (⊩ds h)

pushᵗ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {A : OVType Ψ} {δ : Subst Ψ Ψ'}
        → Q ⊩ᴱ A [ δ ]ᵛ → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushᵗ A R) [ δ ]
pushᵗ-⊩ p h =
  mk⊩ᴿ (⊩rs h) (⊩es h) (λ { (here refl) → p ; (there m) → ⊩ts h m }) (⊩ds h)

pushᵈ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {A : OVType Ψ} {ρ : RExp Ψ}
            {δ : Subst Ψ Ψ'}
        → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ) → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushᵈ A ρ R) [ δ ]
pushᵈ-⊩ p h =
  mk⊩ᴿ (⊩rs h) (⊩es h) (⊩ts h) (λ { (here refl) → p ; (there m) → ⊩ds h m })

varᵉ?-just : ∀ {Ψ} → (ε : EExp Ψ) → {k : EVar Ψ} → varᵉ? ε ≡ just k → ε ≡ evar k
varᵉ?-just (evar i)   refl = refl
varᵉ?-just (econst c) ()
varᵉ?-just (ε ·̂ₑ ε')  ()

∈-transRig : ∀ {Ψ Ψ₁} → (σ : Subst Ψ Ψ₁) → (rg : Rig Ψ) → (k : EVar Ψ₁)
           → k ∈ᶠ transRig σ rg ≡ true
           → Σ[ i ∈ EVar Ψ ] ((i ∈ᶠ rg ≡ true) × (sE σ i ≡ evar k))
∈-transRig σ []         k ()
∈-transRig σ (i₀ ∷ rg) k q with varᵉ? (sE σ i₀) in r
... | nothing with ∈-transRig σ rg k q
...   | i , m , r' = i , ∨-right ⌊ i ≟ᶠ i₀ ⌋ (i ∈ᶠ rg) m , r'
∈-transRig σ (i₀ ∷ rg) k q
    | just k₀ with ∨-true ⌊ k ≟ᶠ k₀ ⌋ (k ∈ᶠ transRig σ rg) q
... | inj₁ s = i₀ , ∨-left ⌊ i₀ ≟ᶠ i₀ ⌋ (i₀ ∈ᶠ rg) (dec-true (i₀ ≟ᶠ i₀) refl) ,
                    trans (varᵉ?-just (sE σ i₀) r)
                          (cong evar (sym (true-dec (k ≟ᶠ k₀) s)))
... | inj₂ s with ∈-transRig σ rg k s
...   | i , m , r' = i , ∨-right ⌊ i ≟ᶠ i₀ ⌋ (i ∈ᶠ rg) m , r'

-- A substitution that factors a rigid-fixing one is rigid-fixing
-- for the transported rigids

Fixing-trans : ∀ {Ψ Ψ₁ Ψ''} {rg : Rig Ψ} → (σ : Subst Ψ Ψ₁) → (δ : Subst Ψ₁ Ψ'')
             → {δ₀ : Subst Ψ Ψ''} → (σ ⨟ˢ δ) ≐ˢ δ₀ → Fixing rg δ₀
             → Fixing (transRig σ rg) δ
Fixing-trans {Ψ} {Ψ₁} {Ψ''} {rg} σ δ {δ₀} p fx = fixing v n
  where
    v : (k : EVar Ψ₁) → k ∈ᶠ transRig σ rg ≡ true
      → Σ[ j ∈ EVar Ψ'' ] (sE δ k ≡ evar j)
    v k m with ∈-transRig σ rg k m
    ... | i , mi , r with fixᵉ fx i mi
    ...   | j , rj = j , trans (sym (cong (_[ δ ]ᵉ) r)) (trans (≐ᵉ p i) rj)

    n : (k k' : EVar Ψ₁) → k ∈ᶠ transRig σ rg ≡ true → k' ∈ᶠ transRig σ rg ≡ true
      → sE δ k ≡ sE δ k' → k ≡ k'
    n k k' m m' r with ∈-transRig σ rg k m | ∈-transRig σ rg k' m'
    ... | i , mi , ri | i' , mi' , ri' =
      evar-inj (trans (sym ri) (trans (cong (sE σ) ii) ri'))
      where
        ii : i ≡ i'
        ii = injᵉ fx i i' mi mi'
               (trans (sym (≐ᵉ p i))
                 (trans (cong (_[ δ ]ᵉ) ri)
                   (trans r (trans (sym (cong (_[ δ ]ᵉ) ri')) (≐ᵉ p i')))))

-- A rigid whose image is a variable is never dropped: `transRig` cannot
-- fail on a rigid-fixing substitution.

∈-transRig⁺ : ∀ {Ψ Ψ₁} → (σ : Subst Ψ Ψ₁) → (rg : Rig Ψ) → (i : EVar Ψ)
            → i ∈ᶠ rg ≡ true → (k : EVar Ψ₁) → sE σ i ≡ evar k
            → k ∈ᶠ transRig σ rg ≡ true
∈-transRig⁺ σ []        i () k rk
∈-transRig⁺ σ (i₀ ∷ rg) i m  k rk with varᵉ? (sE σ i₀) in r
... | just k₀ with ∨-true ⌊ i ≟ᶠ i₀ ⌋ (i ∈ᶠ rg) m
...   | inj₁ s = ∨-left ⌊ k ≟ᶠ k₀ ⌋ (k ∈ᶠ transRig σ rg) (dec-true (k ≟ᶠ k₀) kk)
        where
          kk : k ≡ k₀
          kk = evar-inj (trans (sym rk)
                          (trans (cong (sE σ) (true-dec (i ≟ᶠ i₀) s))
                                 (varᵉ?-just (sE σ i₀) r)))
...   | inj₂ s = ∨-right ⌊ k ≟ᶠ k₀ ⌋ (k ∈ᶠ transRig σ rg) (∈-transRig⁺ σ rg i s k rk)
∈-transRig⁺ σ (i₀ ∷ rg) i m k rk
    | nothing with ∨-true ⌊ i ≟ᶠ i₀ ⌋ (i ∈ᶠ rg) m
... | inj₁ s = ⊥nothing (trans (sym (cong varᵉ? eqi)) r)
      where
        eqi : sE σ i₀ ≡ evar k
        eqi = trans (sym (cong (sE σ) (true-dec (i ≟ᶠ i₀) s))) rk
... | inj₂ s = ∈-transRig⁺ σ rg i s k rk

transRig-total : ∀ {Ψ Ψ₁} → (σ : Subst Ψ Ψ₁) → (rg : Rig Ψ) → Fixing rg σ
               → (i : EVar Ψ) → i ∈ᶠ rg ≡ true
               → Σ[ k ∈ EVar Ψ₁ ] ((sE σ i ≡ evar k) × (k ∈ᶠ transRig σ rg ≡ true))
transRig-total σ rg fx i m with fixᵉ fx i m
... | k , rk = k , rk , ∈-transRig⁺ σ rg i m k rk

-- A rigid lift fixes the rigid it declares — by computation — as well
-- as the ones it transports

Fixing-⇑ᵉ : ∀ {Ψ Ψ''} {rg : Rig Ψ} → (δ₀ : Subst Ψ Ψ'')
          → Fixing rg δ₀ → Fixing (newᵉ {Ψ} ∷ transRig (wkˢᵉ {Ψ}) rg) (δ₀ ↑ᵉ)
Fixing-⇑ᵉ {Ψ} {Ψ''} {rg} δ₀ fx = fixing v n
  where
    im : (k : EVar (Ψ +e)) → k ∈ᶠ transRig (wkˢᵉ {Ψ}) rg ≡ true
       → Σ[ i ∈ EVar Ψ ] Σ[ j ∈ EVar Ψ'' ]
           ((i ∈ᶠ rg ≡ true) × (k ≡ suc i) × (sE δ₀ i ≡ evar j))
    im k m with ∈-transRig (wkˢᵉ {Ψ}) rg k m
    ... | i , mi , ri with fixᵉ fx i mi
    ...   | j , rj = i , j , mi , sym (evar-inj ri) , rj

    cls : (k : EVar (Ψ +e)) → k ∈ᶠ (newᵉ {Ψ} ∷ transRig (wkˢᵉ {Ψ}) rg) ≡ true
        → (k ≡ newᵉ {Ψ})
          ⊎ (Σ[ i ∈ EVar Ψ ] Σ[ j ∈ EVar Ψ'' ]
               ((i ∈ᶠ rg ≡ true) × (k ≡ suc i) × (sE δ₀ i ≡ evar j)))
    cls k m with ∨-true ⌊ k ≟ᶠ newᵉ {Ψ} ⌋ (k ∈ᶠ transRig (wkˢᵉ {Ψ}) rg) m
    ... | inj₁ s = inj₁ (true-dec (k ≟ᶠ newᵉ {Ψ}) s)
    ... | inj₂ s = inj₂ (im k s)

    v : (k : EVar (Ψ +e)) → k ∈ᶠ (newᵉ {Ψ} ∷ transRig (wkˢᵉ {Ψ}) rg) ≡ true
      → Σ[ l ∈ EVar (Ψ'' +e) ] (sE (δ₀ ↑ᵉ) k ≡ evar l)
    v k m with cls k m
    ... | inj₁ refl                     = newᵉ {Ψ''} , refl
    ... | inj₂ (i , j , mi , refl , rj) = wkᵉ-ev Ψ'' j , cong wkᵉ-e rj

    n : (k k' : EVar (Ψ +e)) → k ∈ᶠ (newᵉ {Ψ} ∷ transRig (wkˢᵉ {Ψ}) rg) ≡ true
      → k' ∈ᶠ (newᵉ {Ψ} ∷ transRig (wkˢᵉ {Ψ}) rg) ≡ true
      → sE (δ₀ ↑ᵉ) k ≡ sE (δ₀ ↑ᵉ) k' → k ≡ k'
    n k k' mk mk' r with cls k mk | cls k' mk'
    ... | inj₁ refl | inj₁ refl = refl
    ... | inj₁ refl | inj₂ (i' , j' , mi' , refl , rj')
          with evar-inj (trans r (cong wkᵉ-e rj'))
    ...     | ()
    n k k' mk mk' r | inj₂ (i , j , mi , refl , rj) | inj₁ refl
          with evar-inj (trans (sym (cong wkᵉ-e rj)) r)
    ...     | ()
    n k k' mk mk' r | inj₂ (i , j , mi , refl , rj)
                    | inj₂ (i' , j' , mi' , refl , rj') =
      cong suc (injᵉ fx i i' mi mi' (trans rj (trans (cong evar jj) (sym rj'))))
      where
        jj : j ≡ j'
        jj = suc-injective
               (evar-inj (trans (sym (cong wkᵉ-e rj)) (trans r (cong wkᵉ-e rj'))))

-- A store never binds a rigid: substitution preserves an expression's
-- head, so an image instantiable to a variable already was one.

varᵉ-inst : ∀ {Φ Ξ} → (ε : EExp Φ) → (δ : Subst Φ Ξ) → {k : EVar Ξ}
          → ε [ δ ]ᵉ ≡ evar k → Σ[ j ∈ EVar Φ ] (ε ≡ evar j)
varᵉ-inst (evar j)   δ q = j , refl
varᵉ-inst (econst c) δ ()
varᵉ-inst (ε ·̂ₑ ε')  δ ()

Princ : ∀ {Θ} → (s s' : St Θ) → s ⟶ s' → Constraint Θ → Set
Princ s s' m C =
  ∀ {Ψ''} → (δ₀ : Subst (Ψ s) Ψ'') → (Q : Hyps Ψ'')
  → (θ s ⨟ˢ δ₀) ⊨ᴿ[ Q ] C → Q ⊩ᴿ (res s) [ δ₀ ]
  → Σ[ δ ∈ Subst (Ψ s') Ψ'' ]
      (((mδ m ⨟ˢ δ) ≐ˢ δ₀)
        × (Q ⊩ᴿ (res s') [ δ ])
        × (Fixing (rig s) δ₀ → Fixing (rig s') δ))

Refut : ∀ {Θ} → St Θ → Constraint Θ → Set
Refut s C =
  ∀ {Ψ''} → (δ₀ : Subst (Ψ s) Ψ'') → (Q : Hyps Ψ'')
  → Fixing (rig s) δ₀ → Q ⊩ᴿ (res s) [ δ₀ ]
  → ¬ ((θ s ⨟ˢ δ₀) ⊨ᴿ[ Q ] C)

-- An atom kept at the boundary is the strengthening of an inner one; its
-- instance along the factorisation is the inner instance with the
-- eigenvariable sent to the unit.

keyʳ : ∀ {Φ Φ'} → (j : EVar (Φ +e)) → (ρ : RExp (Φ +e)) → {ρ₀ : RExp Φ}
     → ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀ → (γ : Subst (Φ +e) (Φ' +e))
     → ρ [ popˢ j ⨟ˢ γ ]ʳ ≡ ρ₀ [ wkˢᵉ ⨟ˢ γ ]ʳ
keyʳ j ρ {ρ₀} q γ =
  trans (sym ([⨟]ʳ ρ (popˢ j) γ))
        (trans (cong (_[ γ ]ʳ) q)
               (trans (cong (_[ γ ]ʳ) (sym (wkˢᵉ-r ρ₀))) ([⨟]ʳ ρ₀ wkˢᵉ γ)))

keyᵉ : ∀ {Φ Φ'} → (j : EVar (Φ +e)) → (ε : EExp (Φ +e)) → {ε₀ : EExp Φ}
     → ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀ → (γ : Subst (Φ +e) (Φ' +e))
     → ε [ popˢ j ⨟ˢ γ ]ᵉ ≡ ε₀ [ wkˢᵉ ⨟ˢ γ ]ᵉ
keyᵉ j ε {ε₀} q γ =
  trans (sym ([⨟]ᵉ ε (popˢ j) γ))
        (trans (cong (_[ γ ]ᵉ) q)
               (trans (cong (_[ γ ]ᵉ) (sym (wkˢᵉ-e ε₀))) ([⨟]ᵉ ε₀ wkˢᵉ γ)))

keyᵛ : ∀ {Φ Φ'} → (j : EVar (Φ +e)) → (A : OVType (Φ +e)) → {A₀ : OVType Φ}
     → A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀ → (γ : Subst (Φ +e) (Φ' +e))
     → A [ popˢ j ⨟ˢ γ ]ᵛ ≡ A₀ [ wkˢᵉ ⨟ˢ γ ]ᵛ
keyᵛ j A {A₀} q γ =
  trans (sym ([⨟]ᵛ A (popˢ j) γ))
        (trans (cong (_[ γ ]ᵛ) q)
               (trans (cong (_[ γ ]ᵛ) (sym (wkˢᵉ-v A₀))) ([⨟]ᵛ A₀ wkˢᵉ γ)))

bndʳ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (ρ ρ' : RExp (Φ +e))
     → {ρ₀ ρ₀' : RExp Φ} → ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀ → ρ' [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀'
     → (γ : Subst (Φ +e) (Φ' +e))
     → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ
     → Q ⊩ ρ₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ ρ₀' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
bndʳ {Q = Q} j ρ ρ' {ρ₀} {ρ₀'} q q' γ p =
  subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y)
         ([⨟]ʳ ρ₀ (wkˢᵉ ⨟ˢ γ) κᵉ) ([⨟]ʳ ρ₀' (wkˢᵉ ⨟ˢ γ) κᵉ)
         (⊩-substᵣ ⊩ᴴ-κᵉ
           (subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y) (keyʳ j ρ q γ) (keyʳ j ρ' q' γ) p))

bndᵉ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (ε ε' : EExp (Φ +e))
     → {ε₀ ε₀' : EExp Φ} → ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀ → ε' [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀'
     → (γ : Subst (Φ +e) (Φ' +e))
     → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ
     → Q ⊩ ε₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ ε₀' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
bndᵉ {Q = Q} j ε ε' {ε₀} {ε₀'} q q' γ p =
  subst₂ (λ x y → Q ⊩ x ≾̂ₑ y)
         ([⨟]ᵉ ε₀ (wkˢᵉ ⨟ˢ γ) κᵉ) ([⨟]ᵉ ε₀' (wkˢᵉ ⨟ˢ γ) κᵉ)
         (⊩-substₑ ⊩ᴴ-κᵉ
           (subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y) (keyᵉ j ε q γ) (keyᵉ j ε' q' γ) p))

bndᵗ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (A : OVType (Φ +e))
     → {A₀ : OVType Φ} → A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀
     → (γ : Subst (Φ +e) (Φ' +e))
     → wkᵉ-H Q ⊩ᴱ A [ popˢ j ⨟ˢ γ ]ᵛ
     → Q ⊩ᴱ A₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ
bndᵗ {Q = Q} j A {A₀} q γ p =
  subst (Q ⊩ᴱ_) ([⨟]ᵛ A₀ (wkˢᵉ ⨟ˢ γ) κᵉ)
        (⊩ᴱ-subst ⊩ᴴ-κᵉ (subst (wkᵉ-H Q ⊩ᴱ_) (keyᵛ j A q γ) p))

bndᵈ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (A : OVType (Φ +e))
     → (ρ : RExp (Φ +e)) → {A₀ : OVType Φ} {ρ₀ : RExp Φ}
     → A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀ → ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀
     → (γ : Subst (Φ +e) (Φ' +e))
     → VarOK (wkᵉ-H Q) (A [ popˢ j ⨟ˢ γ ]ᵛ) (ρ [ popˢ j ⨟ˢ γ ]ʳ)
     → VarOK Q (A₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ) (ρ₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ)
bndᵈ {Q = Q} j A ρ {A₀} {ρ₀} q q' γ p =
  subst₂ (VarOK Q) ([⨟]ᵛ A₀ (wkˢᵉ ⨟ˢ γ) κᵉ) ([⨟]ʳ ρ₀ (wkˢᵉ ⨟ˢ γ) κᵉ)
         (VarOK-subst ⊩ᴴ-κᵉ
           (subst₂ (VarOK (wkᵉ-H Q)) (keyᵛ j A q γ) (keyʳ j ρ q' γ) p))

atomʳ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (ρ ρ' : RExp (Φ +e))
            → ∀ {a} → atomʳ j ρ ρ' ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e))
            → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ
            → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
            → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
atomʳ-princ j ρ ρ' eq γ p with strʳ⁺ j ρ | strʳ⁺ j ρ'
... | just (ρ₀ , e₁) | just (ρ₀' , e₂) with eq
...   | refl = λ { (here refl) → bndʳ j ρ ρ' e₁ e₂ γ p }
atomʳ-princ j ρ ρ' eq γ p | just _ | nothing with decide≾ᵣ {Q = ∅ᴴ} ρ ρ'
... | just _  with eq
...   | refl = λ ()
atomʳ-princ j ρ ρ' eq γ p | just _ | nothing | nothing = ⊥just eq
atomʳ-princ j ρ ρ' eq γ p | nothing | _ with decide≾ᵣ {Q = ∅ᴴ} ρ ρ'
... | just _  with eq
...   | refl = λ ()
atomʳ-princ j ρ ρ' eq γ p | nothing | _ | nothing = ⊥just eq

atomᵉ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (ε ε' : EExp (Φ +e))
            → ∀ {a} → atomᵉ j ε ε' ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e))
            → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ
            → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
            → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
atomᵉ-princ j ε ε' eq γ p with strᵉ⁺ j ε | strᵉ⁺ j ε'
... | just (ε₀ , e₁) | just (ε₀' , e₂) with eq
...   | refl = λ { (here refl) → bndᵉ j ε ε' e₁ e₂ γ p }
atomᵉ-princ j ε ε' eq γ p | just _ | nothing with decide≾ₑ {Q = ∅ᴴ} ε ε'
... | just _  with eq
...   | refl = λ ()
atomᵉ-princ j ε ε' eq γ p | just _ | nothing | nothing = ⊥just eq
atomᵉ-princ j ε ε' eq γ p | nothing | _ with decide≾ₑ {Q = ∅ᴴ} ε ε'
... | just _  with eq
...   | refl = λ ()
atomᵉ-princ j ε ε' eq γ p | nothing | _ | nothing = ⊥just eq

atomᵗ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (A : OVType (Φ +e))
            → ∀ {a} → atomᵗ j A ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e))
            → wkᵉ-H Q ⊩ᴱ A [ popˢ j ⨟ˢ γ ]ᵛ
            → ∀ {B} → B ∈ proj₁ a → Q ⊩ᴱ B [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ
atomᵗ-princ j A eq γ p with strᵛ⁺ j A
... | just (A₀ , e₁) with eq
...   | refl = λ { (here refl) → bndᵗ j A e₁ γ p }
atomᵗ-princ j A eq γ p | nothing with et₀? A
... | just _  with eq
...   | refl = λ ()
atomᵗ-princ j A eq γ p | nothing | nothing = ⊥just eq

atomᵈ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (A : OVType (Φ +e))
            → (ρ : RExp (Φ +e))
            → ∀ {a} → atomᵈ j A ρ ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e))
            → VarOK (wkᵉ-H Q) (A [ popˢ j ⨟ˢ γ ]ᵛ) (ρ [ popˢ j ⨟ˢ γ ]ʳ)
            → ∀ {B τ} → (B , τ) ∈ proj₁ a
            → VarOK Q (B [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ) (τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ)
atomᵈ-princ j A ρ eq γ p with strᵛ⁺ j A | strʳ⁺ j ρ
... | just (A₀ , e₁) | just (ρ₀ , e₂) with eq
...   | refl = λ { (here refl) → bndᵈ j A ρ e₁ e₂ γ p }
atomᵈ-princ j A ρ eq γ p | just _ | nothing with discᵈ j A ρ
... | just _  with eq
...   | refl = λ ()
atomᵈ-princ j A ρ eq γ p | just _ | nothing | nothing = ⊥just eq
atomᵈ-princ j A ρ eq γ p | nothing | _ with discᵈ j A ρ
... | just _  with eq
...   | refl = λ ()
atomᵈ-princ j A ρ eq γ p | nothing | _ | nothing = ⊥just eq

listʳ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e))
            → (l : List (RExp (Φ +e) × RExp (Φ +e)))
            → ∀ {a} → listʳ j l ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e))
            → (∀ {ρ ρ'} → (ρ , ρ') ∈ l
                 → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ)
            → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
            → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
listʳ-princ j []              refl γ k = λ ()
listʳ-princ j ((ρ , ρ') ∷ l) eq γ k with atomʳ j ρ ρ' in e₁ | listʳ j l in e₂
... | just (a , fa) | just (l₁ , f) with eq
...   | refl = λ m → [ atomʳ-princ j ρ ρ' e₁ γ (k (here refl))
                     , listʳ-princ j l e₂ γ (λ m' → k (there m')) ]′ (∈-++⁻ a m)
listʳ-princ j ((ρ , ρ') ∷ l) eq γ k | just _  | nothing = ⊥just eq
listʳ-princ j ((ρ , ρ') ∷ l) eq γ k | nothing | _       = ⊥just eq

listᵉ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e))
            → (l : List (EExp (Φ +e) × EExp (Φ +e)))
            → ∀ {a} → listᵉ j l ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e))
            → (∀ {ε ε'} → (ε , ε') ∈ l
                 → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ)
            → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
            → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
listᵉ-princ j []              refl γ k = λ ()
listᵉ-princ j ((ε , ε') ∷ l) eq γ k with atomᵉ j ε ε' in e₁ | listᵉ j l in e₂
... | just (a , fa) | just (l₁ , f) with eq
...   | refl = λ m → [ atomᵉ-princ j ε ε' e₁ γ (k (here refl))
                     , listᵉ-princ j l e₂ γ (λ m' → k (there m')) ]′ (∈-++⁻ a m)
listᵉ-princ j ((ε , ε') ∷ l) eq γ k | just _  | nothing = ⊥just eq
listᵉ-princ j ((ε , ε') ∷ l) eq γ k | nothing | _       = ⊥just eq

listᵗ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e))
            → (l : List (OVType (Φ +e)))
            → ∀ {a} → listᵗ j l ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e))
            → (∀ {A} → A ∈ l → wkᵉ-H Q ⊩ᴱ A [ popˢ j ⨟ˢ γ ]ᵛ)
            → ∀ {B} → B ∈ proj₁ a → Q ⊩ᴱ B [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ
listᵗ-princ j []      refl γ k = λ ()
listᵗ-princ j (A ∷ l) eq γ k with atomᵗ j A in e₁ | listᵗ j l in e₂
... | just (a , fa) | just (l₁ , f) with eq
...   | refl = λ m → [ atomᵗ-princ j A e₁ γ (k (here refl))
                     , listᵗ-princ j l e₂ γ (λ m' → k (there m')) ]′ (∈-++⁻ a m)
listᵗ-princ j (A ∷ l) eq γ k | just _  | nothing = ⊥just eq
listᵗ-princ j (A ∷ l) eq γ k | nothing | _       = ⊥just eq

listᵈ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e))
            → (l : List (OVType (Φ +e) × RExp (Φ +e)))
            → ∀ {a} → listᵈ j l ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e))
            → (∀ {A ρ} → (A , ρ) ∈ l
                 → VarOK (wkᵉ-H Q) (A [ popˢ j ⨟ˢ γ ]ᵛ) (ρ [ popˢ j ⨟ˢ γ ]ʳ))
            → ∀ {B τ} → (B , τ) ∈ proj₁ a
            → VarOK Q (B [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ) (τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ)
listᵈ-princ j []             refl γ k = λ ()
listᵈ-princ j ((A , ρ) ∷ l) eq γ k with atomᵈ j A ρ in e₁ | listᵈ j l in e₂
... | just (a , fa) | just (l₁ , f) with eq
...   | refl = λ m → [ atomᵈ-princ j A ρ e₁ γ (k (here refl))
                     , listᵈ-princ j l e₂ γ (λ m' → k (there m')) ]′ (∈-++⁻ a m)
listᵈ-princ j ((A , ρ) ∷ l) eq γ k | just _  | nothing = ⊥just eq
listᵈ-princ j ((A , ρ) ∷ l) eq γ k | nothing | _       = ⊥just eq

splitᴿ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (R : Resid (Φ +e))
             → ∀ {a} → splitᴿ j R ≡ just a
             → (γ : Subst (Φ +e) (Φ' +e))
             → wkᵉ-H Q ⊩ᴿ R [ popˢ j ⨟ˢ γ ]
             → Q ⊩ᴿ proj₁ a [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]
splitᴿ-princ j R eq γ h
  with listʳ j (rs R) in e₁ | listᵉ j (es R) in e₂
     | listᵗ j (ts R) in e₃ | listᵈ j (ds R) in e₄
... | just (lr , fr) | just (le , fe) | just (lt , ft) | just (ld , fd) with eq
...   | refl = mk⊩ᴿ (listʳ-princ j (rs R) e₁ γ (⊩rs h))
                    (listᵉ-princ j (es R) e₂ γ (⊩es h))
                    (listᵗ-princ j (ts R) e₃ γ (⊩ts h))
                    (listᵈ-princ j (ds R) e₄ γ (⊩ds h))
splitᴿ-princ j R eq γ h | just _  | just _  | just _  | nothing = ⊥just eq
splitᴿ-princ j R eq γ h | just _  | just _  | nothing | _       = ⊥just eq
splitᴿ-princ j R eq γ h | just _  | nothing | _       | _       = ⊥just eq
splitᴿ-princ j R eq γ h | nothing | _       | _       | _       = ⊥just eq

-- The inner run is entered at `δ₀ ↑ᵉ`; what comes back is turned into a
-- substitution out of the outer scope by undoing the rigid's move and
-- sending the rigid to the unit.

popᵉ-princ : ∀ {Θ} → (s : St Θ) → (C : Constraint (Θ +e))
           → (Φ : Scope) → (θ'' : Subst (Θ +e) Φ) → (R'' : Resid Φ) → (rg'' : Rig Φ)
           → (m'' : ⇑ᵉˢ s ⟶ st Φ θ'' R'' rg'') → (w'' : Wit (st Φ θ'' R'' rg'') C)
           → Princ (⇑ᵉˢ s) (st Φ θ'' R'' rg'') m'' C
           → ∀ {s' : St Θ} {m : s ⟶ s'} {w : Wit s' (∀ᵉ C)}
           → popᵉ s C Φ θ'' R'' rg'' m'' w'' ≡ just (s' , m , w)
           → Princ s s' m (∀ᵉ C)
popᵉ-princ s C (scope nt nr nzero) θ'' R'' rg'' m'' w'' ip ()
popᵉ-princ s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' ip eq δ₀ Q sat h
  with evar? (sE (mδ m'') (newᵉ {Ψ s}))
... | nothing = ⊥just eq
... | just (j , eqj) with strSub j (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') | splitᴿ j R'' in eqsp
...   | just (δ₀ₛ , pδ) | just (R₀ , tr) with eq
...     | refl = δ , tri ,
                 ∪ᴿ-both (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym tri) h))
                         (splitᴿ-princ j R'' eqsp γ
                           (⊩ᴿ-resp-≐ˢ (≐ˢ-sym popγ) hres'')) ,
                 (λ fx → Fixing-trans δ₀ₛ δ tri fx)
  where
    ires = ip (δ₀ ↑ᵉ) (wkᵉ-H Q)
              (⊨ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉ (θ s) δ₀)) C sat) ⊩ᴿ-empty

    δ''    = proj₁ ires
    tri''  = proj₁ (proj₂ ires)
    hres'' = proj₁ (proj₂ (proj₂ ires))

    γ    = unpopˢ j ⨟ˢ δ''
    popγ = ≐ˢ-trans (≐ˢ-sym (⨟-assoc (popˢ j) (unpopˢ j) δ''))
                    (≐ˢ-trans (⨟-congˡ (pop-unpop j) δ'') (⨟-idˡ δ''))

    δ = (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ

    inner = ≐ˢ-trans (≐ˢ-sym (⨟-assoc δ₀ₛ wkˢᵉ γ))
            (≐ˢ-trans (⨟-congˡ (≐ˢ-sym pδ) γ)
            (≐ˢ-trans (⨟-assoc (wkˢᵉ ⨟ˢ mδ m'') (popˢ j) γ)
            (≐ˢ-trans (⨟-congʳ (wkˢᵉ ⨟ˢ mδ m'') popγ)
            (≐ˢ-trans (⨟-assoc wkˢᵉ (mδ m'') δ'')
            (≐ˢ-trans (⨟-congʳ wkˢᵉ tri'') (wkˢᵉ-↑ᵉ δ₀))))))

    tri = ≐ˢ-trans (≐ˢ-sym (⨟-assoc δ₀ₛ (wkˢᵉ ⨟ˢ γ) κᵉ))
          (≐ˢ-trans (⨟-congˡ inner κᵉ)
          (≐ˢ-trans (⨟-assoc δ₀ wkˢᵉ κᵉ)
          (≐ˢ-trans (⨟-congʳ δ₀ wk-κᵉ) (⨟-idʳ δ₀))))
popᵉ-princ s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' ip eq δ₀ Q sat h
  | just (j , eqj) | just _ | nothing = ⊥just eq
popᵉ-princ s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' ip eq δ₀ Q sat h
  | just (j , eqj) | nothing | _ = ⊥just eq

threadOps-princ : ∀ {Θ} {f : Op → Constraint Θ}
   → (g : (s : St Θ) → (op : Op)
            → Maybe (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' (f op))))
   → ((s : St Θ) → (op : Op) → {s' : St Θ} {m : s ⟶ s'} {w : Wit s' (f op)}
        → g s op ≡ just (s' , m , w) → Princ s s' m (f op))
   → (l : List Op) → (s : St Θ)
   → {s' : St Θ} {m : s ⟶ s'} {ws : AllOp (λ op → Wit s' (f op)) l}
   → threadOps {f = f} g l s ≡ just (s' , m , ws)
   → Princ s s' m (⋀ᵒᵖ f)
threadOps-princ g gp []       s refl δ₀ Q sat h = δ₀ , ≐ˢ-refl , h , (λ fx → fx)
threadOps-princ {f = f} g gp (op ∷ l) s eq δ₀ Q sat h with g s op in e₁
... | nothing = ⊥just eq
... | just (s₁ , m₁ , w₁) with threadOps {f = f} g l s₁ in e₂
...   | nothing = ⊥just eq
...   | just (s₂ , m₂ , ws) with eq
...     | refl = δ₂ ,
                 ≐ˢ-trans (⨟-assoc (mδ m₁) (mδ m₂) δ₂)
                          (≐ˢ-trans (⨟-congʳ (mδ m₁) tri₂) tri₁) ,
                 h₂ , (λ fx → fx₂ (fx₁ fx))
  where
    f₁  = gp s op e₁ δ₀ Q (sat op) h
    δ₁  = proj₁ f₁
    tri₁ = proj₁ (proj₂ f₁)
    h₁  = proj₁ (proj₂ (proj₂ f₁))
    fx₁ = proj₂ (proj₂ (proj₂ f₁))

    chain = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₁)) δ₁)
            (≐ˢ-trans (⨟-assoc (θ s) (mδ m₁) δ₁) (⨟-congʳ (θ s) tri₁))

    f₂  = threadOps-princ g gp l s₁ e₂ δ₁ Q
            (λ op' → ⊨ᴿ-resp-≐ˢ (≐ˢ-sym chain) (f op') (sat op')) h₁
    δ₂  = proj₁ f₂
    tri₂ = proj₁ (proj₂ f₂)
    h₂  = proj₁ (proj₂ (proj₂ f₂))
    fx₂ = proj₂ (proj₂ (proj₂ f₂))

solve-principal : ∀ {Θ} → (s : St Θ) → (C : Constraint Θ)
                → {s' : St Θ} {m : s ⟶ s'} {w : Wit s' C}
                → solve s C ≡ just (s' , m , w)
                → Princ s s' m C

solve-principal s ⊤̂ refl δ₀ Q sat h = δ₀ , ≐ˢ-refl , h , (λ fx → fx)

solve-principal s ⊥̂ ()

solve-principal s (C ∧̂ D) eq δ₀ Q (sc , sd) h with solve s C in e₁
... | nothing = ⊥just eq
... | just (s₁ , m₁ , w₁) with solve s₁ D in e₂
...   | nothing = ⊥just eq
...   | just (s₂ , m₂ , w₂) with eq
...     | refl = δ₂ ,
                 ≐ˢ-trans (⨟-assoc (mδ m₁) (mδ m₂) δ₂)
                          (≐ˢ-trans (⨟-congʳ (mδ m₁) tri₂) tri₁) ,
                 h₂ , (λ fx → fx₂ (fx₁ fx))
  where
    f₁  = solve-principal s C e₁ δ₀ Q sc h
    δ₁  = proj₁ f₁
    tri₁ = proj₁ (proj₂ f₁)
    h₁  = proj₁ (proj₂ (proj₂ f₁))
    fx₁ = proj₂ (proj₂ (proj₂ f₁))

    chain = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₁)) δ₁)
            (≐ˢ-trans (⨟-assoc (θ s) (mδ m₁) δ₁) (⨟-congʳ (θ s) tri₁))

    f₂  = solve-principal s₁ D e₂ δ₁ Q (⊨ᴿ-resp-≐ˢ (≐ˢ-sym chain) D sd) h₁
    δ₂  = proj₁ f₂
    tri₂ = proj₁ (proj₂ f₂)
    h₂  = proj₁ (proj₂ (proj₂ f₂))
    fx₂ = proj₂ (proj₂ (proj₂ f₂))

solve-principal s (A ≐ᵥ B) eq δ₀ Q sat h
  with unify* (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ [])
... | nothing = ⊥just eq
... | just (Ψ⁺ , ρ , equ) with eq
...   | refl = δ , tri , ⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym tri) h) ,
                (λ fx → Fixing-trans ⟦ ρ ⟧ᴬ δ tri fx)
  where
    u = trans ([⨟]ᵛ A (θ s) δ₀) (trans sat (sym ([⨟]ᵛ B (θ s) δ₀))) , tt

    fac = unify-max (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ []) equ δ₀ u
    δ   = proj₁ fac
    tri = proj₂ fac

solve-principal s (ρ ≾̂ᵣᶜ ρ') refl δ₀ Q sat h =
  δ₀ , ≐ˢ-refl ,
  pushʳ-⊩ (subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y)
                  (sym ([⨟]ʳ ρ (θ s) δ₀)) (sym ([⨟]ʳ ρ' (θ s) δ₀)) sat) h ,
  (λ fx → fx)

solve-principal s (ε ≾̂ₑᶜ ε') refl δ₀ Q sat h =
  δ₀ , ≐ˢ-refl ,
  pushᵉ-⊩ (subst₂ (λ x y → Q ⊩ x ≾̂ₑ y)
                  (sym ([⨟]ᵉ ε (θ s) δ₀)) (sym ([⨟]ᵉ ε' (θ s) δ₀)) sat) h ,
  (λ fx → fx)

solve-principal s (Etᶜ A) refl δ₀ Q sat h =
  δ₀ , ≐ˢ-refl ,
  pushᵗ-⊩ (subst (Q ⊩ᴱ_) (sym ([⨟]ᵛ A (θ s) δ₀)) sat) h ,
  (λ fx → fx)

solve-principal s (Et∨≾ᵘ A ρ) eq δ₀ Q sat h
  with decide≾ᵣ {Q = ∅ᴴ} (ρ [ θ s ]ʳ) ûᵣ
... | just p  with eq
...   | refl = δ₀ , ≐ˢ-refl , h , (λ fx → fx)
solve-principal s (Et∨≾ᵘ A ρ) eq δ₀ Q sat h | nothing with eq
... | refl = δ₀ , ≐ˢ-refl ,
             pushᵈ-⊩ (≾ᵘ-ok (subst (λ x → Q ⊩ x ≾̂ᵣ ûᵣ)
                                   (sym ([⨟]ʳ ρ (θ s) δ₀)) sat)) h ,
             (λ fx → fx)

solve-principal s (∃ᵗ C) eq δ₀ Q (B , sat) h with solve (s ↑ᵗˢ) C in e
... | nothing = ⊥just eq
... | just (s'' , m'' , w'') with eq
...   | refl = δ'' ,
               ≐ˢ-trans (⨟-assoc wkˢᵗ (mδ m'') δ'')
                        (≐ˢ-trans (⨟-congʳ wkˢᵗ tri'') (wk-,ᵗ δ₀ B)) ,
               h'' , (λ fx → fx'' (Fixing-trans wkˢᵗ (δ₀ ,ᵗ B) (wk-,ᵗ δ₀ B) fx))
  where
    ih = solve-principal (s ↑ᵗˢ) C e (δ₀ ,ᵗ B) Q
           (⊨ᴿ-resp-≐ˢ (≐ˢ-sym (↑-,ᵗˢ (θ s) δ₀ B)) C sat)
           (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ᵗ δ₀ B)) h))
    δ''   = proj₁ ih
    tri'' = proj₁ (proj₂ ih)
    h''   = proj₁ (proj₂ (proj₂ ih))
    fx''  = proj₂ (proj₂ (proj₂ ih))

solve-principal s (∃ʳ C) eq δ₀ Q (ρ , sat) h with solve (s ↑ʳˢ) C in e
... | nothing = ⊥just eq
... | just (s'' , m'' , w'') with eq
...   | refl = δ'' ,
               ≐ˢ-trans (⨟-assoc wkˢʳ (mδ m'') δ'')
                        (≐ˢ-trans (⨟-congʳ wkˢʳ tri'') (wk-,ʳ δ₀ ρ)) ,
               h'' , (λ fx → fx'' (Fixing-trans wkˢʳ (δ₀ ,ʳ ρ) (wk-,ʳ δ₀ ρ) fx))
  where
    ih = solve-principal (s ↑ʳˢ) C e (δ₀ ,ʳ ρ) Q
           (⊨ᴿ-resp-≐ˢ (≐ˢ-sym (↑-,ʳˢ (θ s) δ₀ ρ)) C sat)
           (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ʳ δ₀ ρ)) h))
    δ''   = proj₁ ih
    tri'' = proj₁ (proj₂ ih)
    h''   = proj₁ (proj₂ (proj₂ ih))
    fx''  = proj₂ (proj₂ (proj₂ ih))

solve-principal s (∃ᵉ C) eq δ₀ Q (ε , sat) h with solve (s ↑ᵉˢ) C in e
... | nothing = ⊥just eq
... | just (s'' , m'' , w'') with eq
...   | refl = δ'' ,
               ≐ˢ-trans (⨟-assoc wkˢᵉ (mδ m'') δ'')
                        (≐ˢ-trans (⨟-congʳ wkˢᵉ tri'') (wk-,ᵉ δ₀ ε)) ,
               h'' , (λ fx → fx'' (Fixing-trans wkˢᵉ (δ₀ ,ᵉ ε) (wk-,ᵉ δ₀ ε) fx))
  where
    ih = solve-principal (s ↑ᵉˢ) C e (δ₀ ,ᵉ ε) Q
           (⊨ᴿ-resp-≐ˢ (≐ˢ-sym (↑-,ᵉˢ (θ s) δ₀ ε)) C sat)
           (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ᵉ δ₀ ε)) h))
    δ''   = proj₁ ih
    tri'' = proj₁ (proj₂ ih)
    h''   = proj₁ (proj₂ (proj₂ ih))
    fx''  = proj₂ (proj₂ (proj₂ ih))

solve-principal s (∀ᵉ C) eq with solve (⇑ᵉˢ s) C in e
... | nothing = ⊥just eq
... | just (s'' , m'' , w'') =
      popᵉ-princ s C (Ψ s'') (θ s'') (res s'') (rig s'') m'' w''
                 (solve-principal (⇑ᵉˢ s) C e) eq

solve-principal s (⋀ᵒᵖ f) eq
  with threadOps {f = f} (λ s' op → solve s' (f op)) ops s in e
... | nothing = ⊥just eq
... | just (s₁ , m₁ , ws) with eq
...   | refl = threadOps-princ (λ s' op → solve s' (f op))
                               (λ s' op e' → solve-principal s' (f op) e') ops s e

-- `Discharges`: `Normal`'s failure on the eigenvariable-mentioning atoms
-- at a rigid binder is assumed to be a refutation, for instances that
-- keep the eigenvariable an eigenvariable.

Discharges : Set
Discharges = ∀ {Φ Ψ'} → (j : EVar (Φ +e)) → (R : Resid (Φ +e))
           → splitᴿ j R ≡ nothing
           → (γ : Subst (Φ +e) (Ψ' +e)) → sE γ j ≡ evar (newᵉ {Ψ'})
           → (Q : Hyps Ψ') → ¬ (wkᵉ-H Q ⊩ᴿ R [ γ ])

-- The refutation guard: `NoRig` relaxed at a rigid binder, which is
-- crossed under the assumption above and nowhere else.

Refutable : ∀ {Θ} → Constraint Θ → Set
Refutable ⊤̂            = ⊤
Refutable ⊥̂            = ⊤
Refutable (C ∧̂ D)      = Refutable C × Refutable D
Refutable (A ≐ᵥ B)     = ⊤
Refutable (ρ ≾̂ᵣᶜ ρ')   = ⊤
Refutable (ε ≾̂ₑᶜ ε')   = ⊤
Refutable (Etᶜ A)      = ⊤
Refutable (Et∨≾ᵘ A ρ)  = ⊤
Refutable (∃ᵗ C)       = Refutable C
Refutable (∃ʳ C)       = Refutable C
Refutable (∃ᵉ C)       = Refutable C
Refutable (∀ᵉ C)       = Discharges × Refutable C
Refutable (⋀ᵒᵖ f)      = (op : Op) → Refutable (f op)

NoRig→Refutable : ∀ {Θ} → (C : Constraint Θ) → NoRig C → Refutable C
NoRig→Refutable ⊤̂            ⊤ⁿ         = tt
NoRig→Refutable ⊥̂            ⊥ⁿ         = tt
NoRig→Refutable (C ∧̂ D)      (nc ∧ⁿ nd) = NoRig→Refutable C nc , NoRig→Refutable D nd
NoRig→Refutable (A ≐ᵥ B)     ≐ⁿ         = tt
NoRig→Refutable (ρ ≾̂ᵣᶜ ρ')   ≾ᵣⁿ        = tt
NoRig→Refutable (ε ≾̂ₑᶜ ε')   ≾ₑⁿ        = tt
NoRig→Refutable (Etᶜ A)      Etⁿ        = tt
NoRig→Refutable (Et∨≾ᵘ A ρ)  Et∨ⁿ       = tt
NoRig→Refutable (∃ᵗ C)       (∃ᵗⁿ nc)   = NoRig→Refutable C nc
NoRig→Refutable (∃ʳ C)       (∃ʳⁿ nc)   = NoRig→Refutable C nc
NoRig→Refutable (∃ᵉ C)       (∃ᵉⁿ nc)   = NoRig→Refutable C nc
NoRig→Refutable (⋀ᵒᵖ f)      (⋀ⁿ nf)    = λ op → NoRig→Refutable (f op) (nf op)

-- The rigid's image under the inner factorisation is the outer
-- scope's own eigenvariable, and the outer unknowns' images are those
-- the outer substitution gives, weakened

bnd-var : ∀ {Ψ Φ Ψ''} → (γ : Subst (Ψ +e) Φ) → (δ : Subst Φ (Ψ'' +e))
        → {δ₀ : Subst Ψ Ψ''} → (γ ⨟ˢ δ) ≐ˢ (δ₀ ↑ᵉ)
        → {j : EVar Φ} → sE γ (newᵉ {Ψ}) ≡ evar j
        → sE δ j ≡ evar (newᵉ {Ψ''})
bnd-var {Ψ} γ δ tri eqj = trans (sym (cong (_[ δ ]ᵉ) eqj)) (≐ᵉ tri (newᵉ {Ψ}))

bnd-out : ∀ {Ψ Φ Ψ''} → (γ : Subst (Ψ +e) Φ) → (δ : Subst Φ (Ψ'' +e))
        → (δ₀ : Subst Ψ Ψ'') → (γ ⨟ˢ δ) ≐ˢ (δ₀ ↑ᵉ)
        → ((wkˢᵉ {Ψ} ⨟ˢ γ) ⨟ˢ δ) ≐ˢ (δ₀ ⨟ˢ wkˢᵉ)
bnd-out γ δ δ₀ tri =
  ≐ˢ-trans (⨟-assoc wkˢᵉ γ δ) (≐ˢ-trans (⨟-congʳ wkˢᵉ tri) (wkˢᵉ-↑ᵉ δ₀))

popᵉ-fail′ : ∀ {Θ Ψ''} → (s : St Θ) → (C : Constraint (Θ +e))
           → (Φ : Scope) → (θ'' : Subst (Θ +e) Φ) → (R'' : Resid Φ) → (rg'' : Rig Φ)
           → (m'' : ⇑ᵉˢ s ⟶ st Φ θ'' R'' rg'') → (w'' : Wit (st Φ θ'' R'' rg'') C)
           → Discharges
           → popᵉ s C Φ θ'' R'' rg'' m'' w'' ≡ nothing
           → (δ₀ : Subst (Ψ s) Ψ'') → (Q : Hyps Ψ'')
           → (δ'' : Subst Φ (Ψ'' +e)) → (mδ m'' ⨟ˢ δ'') ≐ˢ (δ₀ ↑ᵉ)
           → wkᵉ-H Q ⊩ᴿ R'' [ δ'' ] → ⊥
popᵉ-fail′ s C (scope nt nr nzero) θ'' R'' rg'' m'' w'' dis eq δ₀ Q δ'' tri hres
  with varᵉ-inst (sE (mδ m'') (newᵉ {Ψ s})) δ'' (≐ᵉ tri (newᵉ {Ψ s}))
... | () , _
popᵉ-fail′ s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' dis eq δ₀ Q δ'' tri hres
  with evar? (sE (mδ m'') (newᵉ {Ψ s})) in eqv
... | nothing =
      subst (λ ε → evar? ε ≡ nothing → ⊥) (sym (proj₂ isvar)) (λ ()) eqv
      where
        isvar = varᵉ-inst (sE (mδ m'') (newᵉ {Ψ s})) δ'' (≐ᵉ tri (newᵉ {Ψ s}))
... | just (j , eqj)
      with strSub j (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') in eqstr | splitᴿ j R'' in eqsp
...     | just _  | just _  = ⊥nothing eq
...     | just _  | nothing =
          dis j R'' eqsp δ'' (bnd-var (mδ m'') δ'' tri eqj) Q hres
...     | nothing | _       =
          strSub-escape j (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') δ''
                        (bnd-var (mδ m'') δ'' tri eqj)
                        δ₀ (bnd-out (mδ m'') δ'' δ₀ tri) eqstr

popᵉ-fail : ∀ {Θ} → (s : St Θ) → (C : Constraint (Θ +e))
          → (Φ : Scope) → (θ'' : Subst (Θ +e) Φ) → (R'' : Resid Φ) → (rg'' : Rig Φ)
          → (m'' : ⇑ᵉˢ s ⟶ st Φ θ'' R'' rg'') → (w'' : Wit (st Φ θ'' R'' rg'') C)
          → Princ (⇑ᵉˢ s) (st Φ θ'' R'' rg'') m'' C → Discharges
          → popᵉ s C Φ θ'' R'' rg'' m'' w'' ≡ nothing
          → Refut s (∀ᵉ C)
popᵉ-fail s C Φ θ'' R'' rg'' m'' w'' ip dis eq δ₀ Q fx h sat =
  popᵉ-fail′ s C Φ θ'' R'' rg'' m'' w'' dis eq δ₀ Q δ'' tri'' hres''
  where
    ires = ip (δ₀ ↑ᵉ) (wkᵉ-H Q)
              (⊨ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉ (θ s) δ₀)) C sat) ⊩ᴿ-empty

    δ''    = proj₁ ires
    tri''  = proj₁ (proj₂ ires)
    hres'' = proj₁ (proj₂ (proj₂ ires))

-- Refutes unconditionally, except at a rigid binder, where it needs
-- `Discharges`.

threadOps-fail : ∀ {Θ} {f : Op → Constraint Θ}
   → (g : (s : St Θ) → (op : Op)
            → Maybe (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' (f op))))
   → ((s : St Θ) → (op : Op) → {s' : St Θ} {m : s ⟶ s'} {w : Wit s' (f op)}
        → g s op ≡ just (s' , m , w) → Princ s s' m (f op))
   → ((s : St Θ) → (op : Op) → g s op ≡ nothing → Refut s (f op))
   → (l : List Op) → (s : St Θ)
   → threadOps {f = f} g l s ≡ nothing
   → Refut s (⋀ᵒᵖ f)
threadOps-fail g gp gf [] s ()
threadOps-fail {f = f} g gp gf (op ∷ l) s eq δ₀ Q fx h sat with g s op in e₁
... | nothing = gf s op e₁ δ₀ Q fx h (sat op)
... | just (s₁ , m₁ , w₁) with threadOps {f = f} g l s₁ in e₂
...   | just _  = ⊥nothing eq
...   | nothing =
        threadOps-fail g gp gf l s₁ e₂ δ₁ Q fx₁ h₁
          (λ op' → ⊨ᴿ-resp-≐ˢ (≐ˢ-sym chain) (f op') (sat op'))
  where
    f₁   = gp s op e₁ δ₀ Q (sat op) h
    δ₁   = proj₁ f₁
    tri₁ = proj₁ (proj₂ f₁)
    h₁   = proj₁ (proj₂ (proj₂ f₁))
    fx₁  = proj₂ (proj₂ (proj₂ f₁)) fx

    chain = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₁)) δ₁)
            (≐ˢ-trans (⨟-assoc (θ s) (mδ m₁) δ₁) (⨟-congʳ (θ s) tri₁))

solve-fail⁺ : ∀ {Θ} → (s : St Θ) → (C : Constraint Θ) → Refutable C
            → solve s C ≡ nothing → Refut s C

solve-fail⁺ s ⊤̂ nr ()

solve-fail⁺ s ⊥̂ nr eq δ₀ Q fx h sat = sat

solve-fail⁺ s (C ∧̂ D) (nc , nd) eq δ₀ Q fx h (sc , sd) with solve s C in e₁
... | nothing = solve-fail⁺ s C nc e₁ δ₀ Q fx h sc
... | just (s₁ , m₁ , w₁) with solve s₁ D in e₂
...   | just _  = ⊥nothing eq
...   | nothing =
        solve-fail⁺ s₁ D nd e₂ δ₁ Q fx₁ h₁ (⊨ᴿ-resp-≐ˢ (≐ˢ-sym chain) D sd)
  where
    f₁   = solve-principal s C e₁ δ₀ Q sc h
    δ₁   = proj₁ f₁
    tri₁ = proj₁ (proj₂ f₁)
    h₁   = proj₁ (proj₂ (proj₂ f₁))
    fx₁  = proj₂ (proj₂ (proj₂ f₁)) fx

    chain = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₁)) δ₁)
            (≐ˢ-trans (⨟-assoc (θ s) (mδ m₁) δ₁) (⨟-congʳ (θ s) tri₁))

solve-fail⁺ s (A ≐ᵥ B) nr eq δ₀ Q fx h sat
  with unify* (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ []) in equ*
... | just _  = ⊥nothing eq
... | nothing =
      unify-fail (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ [])
                 (unify*-nothing (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ []) equ*)
                 δ₀ fx
                 (trans ([⨟]ᵛ A (θ s) δ₀) (trans sat (sym ([⨟]ᵛ B (θ s) δ₀))) , tt)

solve-fail⁺ s (ρ ≾̂ᵣᶜ ρ') nr ()

solve-fail⁺ s (ε ≾̂ₑᶜ ε') nr ()

solve-fail⁺ s (Etᶜ A) nr ()

solve-fail⁺ s (Et∨≾ᵘ A ρ) nr eq with decide≾ᵣ {Q = ∅ᴴ} (ρ [ θ s ]ʳ) ûᵣ
... | just _  = ⊥nothing eq
... | nothing = ⊥nothing eq

solve-fail⁺ s (∃ᵗ C) nc eq δ₀ Q fx h (B , sat) with solve (s ↑ᵗˢ) C in e
... | just _  = ⊥nothing eq
... | nothing =
      solve-fail⁺ (s ↑ᵗˢ) C nc e (δ₀ ,ᵗ B) Q
        (Fixing-trans wkˢᵗ (δ₀ ,ᵗ B) (wk-,ᵗ δ₀ B) fx)
        (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ᵗ δ₀ B)) h))
        (⊨ᴿ-resp-≐ˢ (≐ˢ-sym (↑-,ᵗˢ (θ s) δ₀ B)) C sat)

solve-fail⁺ s (∃ʳ C) nc eq δ₀ Q fx h (ρ , sat) with solve (s ↑ʳˢ) C in e
... | just _  = ⊥nothing eq
... | nothing =
      solve-fail⁺ (s ↑ʳˢ) C nc e (δ₀ ,ʳ ρ) Q
        (Fixing-trans wkˢʳ (δ₀ ,ʳ ρ) (wk-,ʳ δ₀ ρ) fx)
        (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ʳ δ₀ ρ)) h))
        (⊨ᴿ-resp-≐ˢ (≐ˢ-sym (↑-,ʳˢ (θ s) δ₀ ρ)) C sat)

solve-fail⁺ s (∃ᵉ C) nc eq δ₀ Q fx h (ε , sat) with solve (s ↑ᵉˢ) C in e
... | just _  = ⊥nothing eq
... | nothing =
      solve-fail⁺ (s ↑ᵉˢ) C nc e (δ₀ ,ᵉ ε) Q
        (Fixing-trans wkˢᵉ (δ₀ ,ᵉ ε) (wk-,ᵉ δ₀ ε) fx)
        (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ᵉ δ₀ ε)) h))
        (⊨ᴿ-resp-≐ˢ (≐ˢ-sym (↑-,ᵉˢ (θ s) δ₀ ε)) C sat)

solve-fail⁺ s (∀ᵉ C) (dis , nc) eq with solve (⇑ᵉˢ s) C in e
... | nothing = λ δ₀ Q fx h sat →
      solve-fail⁺ (⇑ᵉˢ s) C nc e (δ₀ ↑ᵉ) (wkᵉ-H Q) (Fixing-⇑ᵉ δ₀ fx) ⊩ᴿ-empty
        (⊨ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉ (θ s) δ₀)) C sat)
... | just (s'' , m'' , w'') =
      popᵉ-fail s C (Ψ s'') (θ s'') (res s'') (rig s'') m'' w''
                (solve-principal (⇑ᵉˢ s) C e) dis eq

solve-fail⁺ s (⋀ᵒᵖ f) nf eq
  with threadOps {f = f} (λ s' op → solve s' (f op)) ops s in e
... | just _  = ⊥nothing eq
... | nothing =
      threadOps-fail (λ s' op → solve s' (f op))
                     (λ s' op e' → solve-principal s' (f op) e')
                     (λ s' op e' → solve-fail⁺ s' (f op) (nf op) e') ops s e

-- Without a rigid binder, no assumption is needed

solve-fail : ∀ {Θ} → (s : St Θ) → (C : Constraint Θ) → NoRig C
           → solve s C ≡ nothing → Refut s C
solve-fail s C nr = solve-fail⁺ s C (NoRig→Refutable C nr)
