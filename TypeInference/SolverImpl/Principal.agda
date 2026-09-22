------------------------------------------------------------------
-- Principality and refutation for the driver, against plain     --
-- satisfaction.                                                  --
------------------------------------------------------------------

open import Data.Bool.Base using (true) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (suc-injective) renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_; map; mapMaybe)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps as H

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Principal
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S
open import TypeInference.Constraints.Properties   S using (⊨-resp-≐ˢ; ≐ˢ-sym)

open import TypeInference.Solver.Fragment S

open import TypeInference.SolverImpl.Enum S using (AllOp; all-lookup)

open import TypeInference.SolverImpl.Core.AList S using (AList; anil; ⟦_⟧ᴬ)
open import TypeInference.SolverImpl.Core.Eqn   S using (Eqn; eqᵛ; Eqns; Unifies)
open import TypeInference.SolverImpl.Core.Rigid S
  using (strʳ⁺; strᵉ⁺; strᵛ⁺; popˢ; popˢ-hit; strSub; unpopˢ; pop-unpop; strSub-escape)
open import TypeInference.SolverImpl.Core.Unify S using (Rig; _∈ᶠ_; unify)
open import TypeInference.SolverImpl.Core.UnifyMGU S
  using (Fixing; fixing; fixᵉ; injᵉ; Fixing-id; unify-max; unify-fail;
         evar-inj; ∨-true; ∨-left; ∨-right; dec-true; true-dec)

open import TypeInference.SolverImpl.Core.Decorate S using (expandSub)

open import TypeInference.SolverImpl.Expand S
  using (ExpMax; ExpDec; expandSub-max; expandSub-dec)

open import TypeInference.SolverImpl.Resid  S
open import TypeInference.SolverImpl.State  S
open import TypeInference.SolverImpl.Normal S umin?ᵣ umin?ₑ
open import TypeInference.SolverImpl.Solve  S opEnum umin?ᵣ umin?ₑ
open import TypeInference.SolverImpl.Close  S umin?ᵣ umin?ₑ using (updᵉ)
open import TypeInference.SolverImpl.Localise S umin?ᵣ umin?ₑ
  using (Localised; localise; lσ; lfix; lcpl; updᵉ-absorb)

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
⊩ᴴ-κᵉ {Ψ} {Q} = mk⊩ᴴ ets' subᵥ' ordᵣ' ordₑ' disj'
  where
    ets' : ∀ {α} → α ∈ ets (wkᵉ-H Q) → Q ⊩ᴱ sTy κᵉ α
    ets' m with ∈-map⁻ (wkᵉ-tv Ψ) m
    ... | α₀ , m₀ , refl = et-hyp m₀

    subᵥ' : ∀ {α β} → (α , β) ∈ subᵥ (wkᵉ-H Q) → Q ∣ sTy κᵉ α <:̂ᵛ sTy κᵉ β
    subᵥ' m with ∈-map⁻ (mapᵖ (wkᵉ-tv Ψ)) m
    ... | (α₀ , β₀) , m₀ , refl = tvarₛ (hypᵗᵛ m₀)

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

-- Both components of a union

∪ᴿ-both : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R R' : Resid Ψ} {δ : Subst Ψ Ψ'}
        → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ R' [ δ ] → Q ⊩ᴿ (R ∪ᴿ R') [ δ ]
∪ᴿ-both {R = R} h h' =
  mk⊩ᴿ (λ m → [ ⊩rs h , ⊩rs h' ]′ (∈-++⁻ (rs R) m))
       (λ m → [ ⊩es h , ⊩es h' ]′ (∈-++⁻ (es R) m))
       (λ m → [ ⊩ts h , ⊩ts h' ]′ (∈-++⁻ (ts R) m))
       (λ m → [ ⊩ss h , ⊩ss h' ]′ (∈-++⁻ (ss R) m))
       (λ m → [ ⊩ds h , ⊩ds h' ]′ (∈-++⁻ (ds R) m))

-- Pushing one atom

pushʳ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {ρ ρ' : RExp Ψ} {δ : Subst Ψ Ψ'}
        → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushʳ ρ ρ' R) [ δ ]
pushʳ-⊩ p h =
  mk⊩ᴿ (λ { (here refl) → p ; (there m) → ⊩rs h m })
       (⊩es h) (⊩ts h) (⊩ss h) (⊩ds h)

pushᵉ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {ε ε' : EExp Ψ} {δ : Subst Ψ Ψ'}
        → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushᵉ ε ε' R) [ δ ]
pushᵉ-⊩ p h =
  mk⊩ᴿ (⊩rs h) (λ { (here refl) → p ; (there m) → ⊩es h m })
       (⊩ts h) (⊩ss h) (⊩ds h)

pushᵗ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {A : OVType Ψ} {δ : Subst Ψ Ψ'}
        → Q ⊩ᴱ A [ δ ]ᵛ → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushᵗ A R) [ δ ]
pushᵗ-⊩ p h =
  mk⊩ᴿ (⊩rs h) (⊩es h) (λ { (here refl) → p ; (there m) → ⊩ts h m })
       (⊩ss h) (⊩ds h)

pushᵈ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {A : OVType Ψ} {ρ : RExp Ψ}
            {δ : Subst Ψ Ψ'}
        → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ) → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushᵈ A ρ R) [ δ ]
pushᵈ-⊩ p h =
  mk⊩ᴿ (⊩rs h) (⊩es h) (⊩ts h) (⊩ss h)
       (λ { (here refl) → p ; (there m) → ⊩ds h m })

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
  → (θ s ⨟ˢ δ₀) ⊨[ Q ] C → Q ⊩ᴿ (res s) [ δ₀ ]
  → Σ[ δ ∈ Subst (Ψ s') Ψ'' ]
      (((mδ m ⨟ˢ δ) ≐ˢ δ₀)
        × (Q ⊩ᴿ (res s') [ δ ])
        × (Fixing (rig s) δ₀ → Fixing (rig s') δ))

Refut : ∀ {Θ} → St Θ → Constraint Θ → Set
Refut s C =
  ∀ {Ψ''} → (δ₀ : Subst (Ψ s) Ψ'') → (Q : Hyps Ψ'')
  → Fixing (rig s) δ₀ → Q ⊩ᴿ (res s) [ δ₀ ]
  → ¬ ((θ s ⨟ˢ δ₀) ⊨[ Q ] C)

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

bndˢ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (A B : OVType (Φ +e))
     → {A₀ B₀ : OVType Φ} → A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀ → B [ popˢ j ]ᵛ ≡ wkᵉ-v B₀
     → (γ : Subst (Φ +e) (Φ' +e))
     → wkᵉ-H Q ∣ A [ popˢ j ⨟ˢ γ ]ᵛ <:̂ᵛ B [ popˢ j ⨟ˢ γ ]ᵛ
     → Q ∣ A₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ <:̂ᵛ B₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ
bndˢ {Q = Q} j A B {A₀} {B₀} q q' γ p =
  subst₂ (Q ∣_<:̂ᵛ_) ([⨟]ᵛ A₀ (wkˢᵉ ⨟ˢ γ) κᵉ) ([⨟]ᵛ B₀ (wkˢᵉ ⨟ˢ γ) κᵉ)
         (<:̂ᵛ-subst ⊩ᴴ-κᵉ
           (subst₂ (wkᵉ-H Q ∣_<:̂ᵛ_) (keyᵛ j A q γ) (keyᵛ j B q' γ) p))

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

-- A stripped ordering: the inner instance, with the eigenvariable sent
-- to the unit, is the instance of the kept one

stripʳ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (um? : Maybe UnitMinₑ) → (j : EVar (Φ +e))
             → (ρ ρ' : RExp (Φ +e)) → (ρ₀ : RExp Φ) → (e₁ : ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀)
             → ∀ {a} → stripʳ um? j ρ ρ' ρ₀ e₁ ≡ just a
             → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
             → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ
             → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
             → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
stripʳ-princ nothing   j ρ ρ' ρ₀ e₁ () γ hγ p
stripʳ-princ {Q = Q} (just um) j ρ ρ' ρ₀ e₁ eq γ hγ p
  with strʳ⁺ j (ρ' [ updᵉ j ûₑ ]ʳ)
... | nothing          = ⊥just eq
... | just (ρ₀' , e₂) with eq
...   | refl = λ { (here refl) → goal }
  where
    X = popˢ j ⨟ˢ γ

    unit : sE (X ⨟ˢ κᵉ) j ≡ ûₑ [ X ⨟ˢ κᵉ ]ᵉ
    unit = cong (_[ κᵉ ]ᵉ) (trans (cong (_[ γ ]ᵉ) (popˢ-hit j)) hγ)

    rhs : ρ' [ X ]ʳ [ κᵉ ]ʳ ≡ ρ₀' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
    rhs = trans ([⨟]ʳ ρ' X κᵉ)
          (trans (sym ([≐]ʳ (updᵉ-absorb j ûₑ (X ⨟ˢ κᵉ) unit) ρ'))
          (trans (sym ([⨟]ʳ ρ' (updᵉ j ûₑ) (X ⨟ˢ κᵉ)))
          (trans (sym ([⨟]ʳ (ρ' [ updᵉ j ûₑ ]ʳ) X κᵉ))
          (trans (cong (_[ κᵉ ]ʳ) (keyʳ j (ρ' [ updᵉ j ûₑ ]ʳ) e₂ γ))
                 ([⨟]ʳ ρ₀' (wkˢᵉ ⨟ˢ γ) κᵉ)))))

    goal : Q ⊩ ρ₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ ρ₀' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
    goal = subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y)
                  (trans (cong (_[ κᵉ ]ʳ) (keyʳ j ρ e₁ γ)) ([⨟]ʳ ρ₀ (wkˢᵉ ⨟ˢ γ) κᵉ)) rhs
                  (⊩-substᵣ ⊩ᴴ-κᵉ p)

stripᵉ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (um? : Maybe UnitMinₑ) → (j : EVar (Φ +e))
             → (ε ε' : EExp (Φ +e)) → (ε₀ : EExp Φ) → (e₁ : ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀)
             → ∀ {a} → stripᵉ um? j ε ε' ε₀ e₁ ≡ just a
             → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
             → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ
             → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
             → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
stripᵉ-princ nothing   j ε ε' ε₀ e₁ () γ hγ p
stripᵉ-princ {Q = Q} (just um) j ε ε' ε₀ e₁ eq γ hγ p
  with strᵉ⁺ j (ε' [ updᵉ j ûₑ ]ᵉ)
... | nothing          = ⊥just eq
... | just (ε₀' , e₂) with eq
...   | refl = λ { (here refl) → goal }
  where
    X = popˢ j ⨟ˢ γ

    unit : sE (X ⨟ˢ κᵉ) j ≡ ûₑ [ X ⨟ˢ κᵉ ]ᵉ
    unit = cong (_[ κᵉ ]ᵉ) (trans (cong (_[ γ ]ᵉ) (popˢ-hit j)) hγ)

    rhs : ε' [ X ]ᵉ [ κᵉ ]ᵉ ≡ ε₀' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
    rhs = trans ([⨟]ᵉ ε' X κᵉ)
          (trans (sym ([≐]ᵉ (updᵉ-absorb j ûₑ (X ⨟ˢ κᵉ) unit) ε'))
          (trans (sym ([⨟]ᵉ ε' (updᵉ j ûₑ) (X ⨟ˢ κᵉ)))
          (trans (sym ([⨟]ᵉ (ε' [ updᵉ j ûₑ ]ᵉ) X κᵉ))
          (trans (cong (_[ κᵉ ]ᵉ) (keyᵉ j (ε' [ updᵉ j ûₑ ]ᵉ) e₂ γ))
                 ([⨟]ᵉ ε₀' (wkˢᵉ ⨟ˢ γ) κᵉ)))))

    goal : Q ⊩ ε₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ ε₀' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
    goal = subst₂ (λ x y → Q ⊩ x ≾̂ₑ y)
                  (trans (cong (_[ κᵉ ]ᵉ) (keyᵉ j ε e₁ γ)) ([⨟]ᵉ ε₀ (wkˢᵉ ⨟ˢ γ) κᵉ)) rhs
                  (⊩-substₑ ⊩ᴴ-κᵉ p)

atomʳ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (ρ ρ' : RExp (Φ +e))
            → ∀ {a} → atomʳ j ρ ρ' ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ
            → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
            → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
atomʳ-princ j ρ ρ' eq γ hγ p with strʳ⁺ j ρ | strʳ⁺ j ρ'
... | just (ρ₀ , e₁) | just (ρ₀' , e₂) with eq
...   | refl = λ { (here refl) → bndʳ j ρ ρ' e₁ e₂ γ p }
atomʳ-princ j ρ ρ' eq γ hγ p | just (ρ₀ , e₁) | nothing with decide≾ᵣ {Q = ∅ᴴ} ρ ρ'
... | just _  with eq
...   | refl = λ ()
atomʳ-princ j ρ ρ' eq γ hγ p | just (ρ₀ , e₁) | nothing | nothing =
  stripʳ-princ umin?ₑ j ρ ρ' ρ₀ e₁ eq γ hγ p
atomʳ-princ j ρ ρ' eq γ hγ p | nothing | _ with decide≾ᵣ {Q = ∅ᴴ} ρ ρ'
... | just _  with eq
...   | refl = λ ()
atomʳ-princ j ρ ρ' eq γ hγ p | nothing | _ | nothing = ⊥just eq

atomᵉ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (ε ε' : EExp (Φ +e))
            → ∀ {a} → atomᵉ j ε ε' ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ
            → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
            → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
atomᵉ-princ j ε ε' eq γ hγ p with strᵉ⁺ j ε | strᵉ⁺ j ε'
... | just (ε₀ , e₁) | just (ε₀' , e₂) with eq
...   | refl = λ { (here refl) → bndᵉ j ε ε' e₁ e₂ γ p }
atomᵉ-princ j ε ε' eq γ hγ p | just (ε₀ , e₁) | nothing with decide≾ₑ {Q = ∅ᴴ} ε ε'
... | just _  with eq
...   | refl = λ ()
atomᵉ-princ j ε ε' eq γ hγ p | just (ε₀ , e₁) | nothing | nothing =
  stripᵉ-princ umin?ₑ j ε ε' ε₀ e₁ eq γ hγ p
atomᵉ-princ j ε ε' eq γ hγ p | nothing | _ with decide≾ₑ {Q = ∅ᴴ} ε ε'
... | just _  with eq
...   | refl = λ ()
atomᵉ-princ j ε ε' eq γ hγ p | nothing | _ | nothing = ⊥just eq

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

atomˢ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (A B : OVType (Φ +e))
            → ∀ {a} → atomˢ j A B ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e))
            → wkᵉ-H Q ∣ A [ popˢ j ⨟ˢ γ ]ᵛ <:̂ᵛ B [ popˢ j ⨟ˢ γ ]ᵛ
            → ∀ {X Y} → (X , Y) ∈ proj₁ a
            → Q ∣ X [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ <:̂ᵛ Y [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ
atomˢ-princ j A B eq γ p with strᵛ⁺ j A | strᵛ⁺ j B
... | just (A₀ , e₁) | just (B₀ , e₂) with eq
...   | refl = λ { (here refl) → bndˢ j A B e₁ e₂ γ p }
atomˢ-princ j A B eq γ p | just _  | nothing = ⊥just eq
atomˢ-princ j A B eq γ p | nothing | _       = ⊥just eq

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
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → (∀ {ρ ρ'} → (ρ , ρ') ∈ l
                 → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ)
            → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
            → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
listʳ-princ j []              refl γ hγ k = λ ()
listʳ-princ j ((ρ , ρ') ∷ l) eq γ hγ k with atomʳ j ρ ρ' in e₁ | listʳ j l in e₂
... | just (a , fa) | just (l₁ , f) with eq
...   | refl = λ m → [ atomʳ-princ j ρ ρ' e₁ γ hγ (k (here refl))
                     , listʳ-princ j l e₂ γ hγ (λ m' → k (there m')) ]′ (∈-++⁻ a m)
listʳ-princ j ((ρ , ρ') ∷ l) eq γ hγ k | just _  | nothing = ⊥just eq
listʳ-princ j ((ρ , ρ') ∷ l) eq γ hγ k | nothing | _       = ⊥just eq

listᵉ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e))
            → (l : List (EExp (Φ +e) × EExp (Φ +e)))
            → ∀ {a} → listᵉ j l ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → (∀ {ε ε'} → (ε , ε') ∈ l
                 → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ)
            → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
            → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
listᵉ-princ j []              refl γ hγ k = λ ()
listᵉ-princ j ((ε , ε') ∷ l) eq γ hγ k with atomᵉ j ε ε' in e₁ | listᵉ j l in e₂
... | just (a , fa) | just (l₁ , f) with eq
...   | refl = λ m → [ atomᵉ-princ j ε ε' e₁ γ hγ (k (here refl))
                     , listᵉ-princ j l e₂ γ hγ (λ m' → k (there m')) ]′ (∈-++⁻ a m)
listᵉ-princ j ((ε , ε') ∷ l) eq γ hγ k | just _  | nothing = ⊥just eq
listᵉ-princ j ((ε , ε') ∷ l) eq γ hγ k | nothing | _       = ⊥just eq

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

listˢ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e))
            → (l : List (OVType (Φ +e) × OVType (Φ +e)))
            → ∀ {a} → listˢ j l ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e))
            → (∀ {A B} → (A , B) ∈ l
                 → wkᵉ-H Q ∣ A [ popˢ j ⨟ˢ γ ]ᵛ <:̂ᵛ B [ popˢ j ⨟ˢ γ ]ᵛ)
            → ∀ {X Y} → (X , Y) ∈ proj₁ a
            → Q ∣ X [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ <:̂ᵛ Y [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ
listˢ-princ j []             refl γ k = λ ()
listˢ-princ j ((A , B) ∷ l) eq γ k with atomˢ j A B in e₁ | listˢ j l in e₂
... | just (a , fa) | just (l₁ , f) with eq
...   | refl = λ m → [ atomˢ-princ j A B e₁ γ (k (here refl))
                     , listˢ-princ j l e₂ γ (λ m' → k (there m')) ]′ (∈-++⁻ a m)
listˢ-princ j ((A , B) ∷ l) eq γ k | just _  | nothing = ⊥just eq
listˢ-princ j ((A , B) ∷ l) eq γ k | nothing | _       = ⊥just eq

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
             → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
             → wkᵉ-H Q ⊩ᴿ R [ popˢ j ⨟ˢ γ ]
             → Q ⊩ᴿ proj₁ a [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]
splitᴿ-princ j R eq γ hγ h
  with listʳ j (rs R) in e₁ | listᵉ j (es R) in e₂ | listᵗ j (ts R) in e₃
     | listˢ j (ss R) in e₄ | listᵈ j (ds R) in e₅
... | just (lr , fr) | just (le , fe) | just (lt , ft) | just (ls , fs)
    | just (ld , fd) with eq
...   | refl = mk⊩ᴿ (listʳ-princ j (rs R) e₁ γ hγ (⊩rs h))
                    (listᵉ-princ j (es R) e₂ γ hγ (⊩es h))
                    (listᵗ-princ j (ts R) e₃ γ (⊩ts h))
                    (listˢ-princ j (ss R) e₄ γ (⊩ss h))
                    (listᵈ-princ j (ds R) e₅ γ (⊩ds h))
splitᴿ-princ j R eq γ hγ h | just _ | just _ | just _  | just _  | nothing = ⊥just eq
splitᴿ-princ j R eq γ hγ h | just _ | just _ | just _  | nothing | _       = ⊥just eq
splitᴿ-princ j R eq γ hγ h | just _ | just _ | nothing | _       | _       = ⊥just eq
splitᴿ-princ j R eq γ hγ h | just _ | nothing | _      | _       | _       = ⊥just eq
splitᴿ-princ j R eq γ hγ h | nothing | _      | _      | _       | _       = ⊥just eq

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
                         (splitᴿ-princ j R'' eqsp γ (bnd-var (mδ m'') δ'' tri'' eqj)
                           (⊩ᴿ-resp-≐ˢ (≐ˢ-sym popγ) hres'')) ,
                 (λ fx → Fixing-trans δ₀ₛ δ tri fx)
  where
    ires = ip (δ₀ ↑ᵉ) (wkᵉ-H Q)
              (⊨-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉ (θ s) δ₀)) C sat) ⊩ᴿ-empty

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

-- Localisation keeps every instance: the factor found for the inner
-- state serves the localised one, the local unknowns being in no image
-- of the outer ones, and the lowering lemma keeping the residual.

localise-princ : ∀ {Θ} {s₀ s'' : St Θ} {m : s₀ ⟶ s''} {C : Constraint Θ}
               → Princ s₀ s'' m C
               → Princ s₀ (proj₁ (localiseˢ m)) (⟶-⨟ m (proj₂ (localiseˢ m))) C
localise-princ {s'' = s''} {m} ip δ₀ Q sat h =
  δ , ≐ˢ-trans (⨟-congˡ (lfix L) δ) tri , lcpl L δ Q hres , fx
  where
    L : Localised (mδ m) (res s'')
    L = localise (mδ m) (res s'')

    f    = ip δ₀ Q sat h
    δ    = proj₁ f
    tri  = proj₁ (proj₂ f)
    hres = proj₁ (proj₂ (proj₂ f))
    fx   = proj₂ (proj₂ (proj₂ f))

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
            (λ op' → ⊨-resp-≐ˢ (≐ˢ-sym chain) (f op') (sat op')) h₁
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

    f₂  = solve-principal s₁ D e₂ δ₁ Q (⊨-resp-≐ˢ (≐ˢ-sym chain) D sd) h₁
    δ₂  = proj₁ f₂
    tri₂ = proj₁ (proj₂ f₂)
    h₂  = proj₁ (proj₂ (proj₂ f₂))
    fx₂ = proj₂ (proj₂ (proj₂ f₂))

solve-principal s (A ≐ᵥ B) eq δ₀ Q sat h
  with unify* (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ [])
... | nothing = ⊥just eq
... | just (Ψ⁺ , ρ , equ) with expandSub (ss (res s [ ⟦ ρ ⟧ᴬ ]ᴿ)) in eqx
...   | nothing = ⊥just eq
...   | just (Ψ' , δₑ) with eq
...     | refl = δ₂ , tri₂ , ⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym trix) h₁) ,
                  (λ fx → Fixing-trans δₑ δ₂ trix (Fixing-trans ⟦ ρ ⟧ᴬ δ₁ tri₁ fx))
  where
    u = trans ([⨟]ᵛ A (θ s) δ₀) (trans sat (sym ([⨟]ᵛ B (θ s) δ₀))) , tt

    fac = unify-max (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ []) equ δ₀ u
    δ₁   = proj₁ fac
    tri₁ = proj₂ fac

    h₁ : Q ⊩ᴿ (res s [ ⟦ ρ ⟧ᴬ ]ᴿ) [ δ₁ ]
    h₁ = ⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym tri₁) h)

    facx = subst (ExpMax δ₁) eqx
                 (expandSub-max (ss (res s [ ⟦ ρ ⟧ᴬ ]ᴿ)) δ₁ (⊩ss h₁))
    δ₂   = proj₁ facx
    trix = proj₂ facx

    tri₂ = ≐ˢ-trans (⨟-assoc ⟦ ρ ⟧ᴬ δₑ δ₂)
                    (≐ˢ-trans (⨟-congʳ ⟦ ρ ⟧ᴬ trix) tri₁)

solve-principal s (A ≾̂ᵥᶜ B) eq δ₀ Q sat h
  with expandSub ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) in eqx
... | nothing = ⊥just eq
... | just (Ψ' , δₑ) with subDec (A [ θ s ]ᵛ [ δₑ ]ᵛ) (B [ θ s ]ᵛ [ δₑ ]ᵛ)
...   | nothing = ⊥just eq
...   | just d with eq
...     | refl = δ , trix ,
                 ∪ᴿ-both (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym trix) h))
                         (atomsᴿ-⊩ (atomsOf d)
                           (elim d δ (subst₂ (Q ∣_<:̂ᵛ_) (sym (inst A)) (sym (inst B))
                                             sat))) ,
                 (λ fx → Fixing-trans δₑ δ trix fx)
  where
    dem : ∀ {X Y} → (X , Y) ∈ ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s))
        → Q ∣ X [ δ₀ ]ᵛ <:̂ᵛ Y [ δ₀ ]ᵛ
    dem (here refl) = subst₂ (Q ∣_<:̂ᵛ_) (sym ([⨟]ᵛ A (θ s) δ₀))
                                        (sym ([⨟]ᵛ B (θ s) δ₀)) sat
    dem (there m)   = ⊩ss h m

    facx = subst (ExpMax δ₀) eqx
                 (expandSub-max ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) δ₀ dem)
    δ    = proj₁ facx
    trix = proj₂ facx

    inst : (X : OVType _) → X [ θ s ]ᵛ [ δₑ ]ᵛ [ δ ]ᵛ ≡ X [ θ s ⨟ˢ δ₀ ]ᵛ
    inst X = trans (chain₂ᵛ X (θ s) δₑ δ)
                   ([≐]ᵛ (≐ˢ-trans (⨟-assoc (θ s) δₑ δ) (⨟-congʳ (θ s) trix)) X)

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
             pushᵈ-⊩ (subst₂ (VarOK Q) (sym ([⨟]ᵛ A (θ s) δ₀))
                             (sym ([⨟]ʳ ρ (θ s) δ₀)) sat) h ,
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
           (⊨-resp-≐ˢ (≐ˢ-sym (↑-,ᵗˢ (θ s) δ₀ B)) C sat)
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
           (⊨-resp-≐ˢ (≐ˢ-sym (↑-,ʳˢ (θ s) δ₀ ρ)) C sat)
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
           (⊨-resp-≐ˢ (≐ˢ-sym (↑-,ᵉˢ (θ s) δ₀ ε)) C sat)
           (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ᵉ δ₀ ε)) h))
    δ''   = proj₁ ih
    tri'' = proj₁ (proj₂ ih)
    h''   = proj₁ (proj₂ (proj₂ ih))
    fx''  = proj₂ (proj₂ (proj₂ ih))

solve-principal s (∀ᵉ C) eq with solve (⇑ᵉˢ s) C in e
... | nothing = ⊥just eq
... | just (s'' , m'' , w'') =
      popᵉ-princ s C (Ψ (proj₁ (localiseˢ m''))) (θ (proj₁ (localiseˢ m'')))
                 (res (proj₁ (localiseˢ m''))) (rig (proj₁ (localiseˢ m'')))
                 (⟶-⨟ m'' (proj₂ (localiseˢ m''))) (wit-mono (proj₂ (localiseˢ m'')) C w'')
                 (localise-princ {s₀ = ⇑ᵉˢ s} {s''} {m''} {C} (solve-principal (⇑ᵉˢ s) C e)) eq

solve-principal s (⋀ᵒᵖ f) eq
  with threadOps {f = f} (λ s' op → solve s' (f op)) ops s in e
... | nothing = ⊥just eq
... | just (s₁ , m₁ , ws) with eq
...   | refl = threadOps-princ (λ s' op → solve s' (f op))
                               (λ s' op e' → solve-principal s' (f op) e') ops s e

-- Refutation holds on the fragment without a rigid binder. At a rigid
-- binder the atoms that mention the rigid are settled by a decision
-- against no hypotheses, and a declined one refutes nothing: a
-- satisfiable constraint whose least solution localisation cannot
-- reach, such as `∀j ∃e. (c · e ≾ e) ∧ (j ≾ e)`, is declined all the
-- same. What a rigid binder does refute is an escape: an outer
-- unknown whose image keeps the rigid.

popᵉ-escape : ∀ {Θ Φ} → (s : St Θ) → (C : Constraint (Θ +e))
            → (θ'' : Subst (Θ +e) (Φ +e)) → (R'' : Resid (Φ +e)) → (rg'' : Rig (Φ +e))
            → (m'' : ⇑ᵉˢ s ⟶ st (Φ +e) θ'' R'' rg'')
            → Princ (⇑ᵉˢ s) (st (Φ +e) θ'' R'' rg'') m'' C
            → (j : EVar (Φ +e)) → sE (mδ m'') (newᵉ {Ψ s}) ≡ evar j
            → strSub j (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') ≡ nothing
            → Refut s (∀ᵉ C)
popᵉ-escape s C θ'' R'' rg'' m'' ip j eqj eqstr δ₀ Q fx h sat =
  strSub-escape j (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') δ'' (bnd-var (mδ m'') δ'' tri'' eqj)
                δ₀ (bnd-out (mδ m'') δ'' δ₀ tri'') eqstr
  where
    ires = ip (δ₀ ↑ᵉ) (wkᵉ-H Q)
              (⊨-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉ (θ s) δ₀)) C sat) ⊩ᴿ-empty

    δ''   = proj₁ ires
    tri'' = proj₁ (proj₂ ires)

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
          (λ op' → ⊨-resp-≐ˢ (≐ˢ-sym chain) (f op') (sat op'))
  where
    f₁   = gp s op e₁ δ₀ Q (sat op) h
    δ₁   = proj₁ f₁
    tri₁ = proj₁ (proj₂ f₁)
    h₁   = proj₁ (proj₂ (proj₂ f₁))
    fx₁  = proj₂ (proj₂ (proj₂ f₁)) fx

    chain = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₁)) δ₁)
            (≐ˢ-trans (⨟-assoc (θ s) (mδ m₁) δ₁) (⨟-congʳ (θ s) tri₁))

solve-fail : ∀ {Θ} → (s : St Θ) → (C : Constraint Θ) → NoRig C
           → solve s C ≡ nothing → Refut s C

solve-fail s ⊤̂ nr ()

solve-fail s ⊥̂ nr eq δ₀ Q fx h sat = sat

solve-fail s (C ∧̂ D) (nc ∧ⁿ nd) eq δ₀ Q fx h (sc , sd) with solve s C in e₁
... | nothing = solve-fail s C nc e₁ δ₀ Q fx h sc
... | just (s₁ , m₁ , w₁) with solve s₁ D in e₂
...   | just _  = ⊥nothing eq
...   | nothing =
        solve-fail s₁ D nd e₂ δ₁ Q fx₁ h₁ (⊨-resp-≐ˢ (≐ˢ-sym chain) D sd)
  where
    f₁   = solve-principal s C e₁ δ₀ Q sc h
    δ₁   = proj₁ f₁
    tri₁ = proj₁ (proj₂ f₁)
    h₁   = proj₁ (proj₂ (proj₂ f₁))
    fx₁  = proj₂ (proj₂ (proj₂ f₁)) fx

    chain = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₁)) δ₁)
            (≐ˢ-trans (⨟-assoc (θ s) (mδ m₁) δ₁) (⨟-congʳ (θ s) tri₁))

solve-fail s (A ≐ᵥ B) nr eq δ₀ Q fx h sat
  with unify* (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ []) in equ*
... | nothing =
      unify-fail (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ [])
                 (unify*-nothing (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ []) equ*)
                 δ₀ fx
                 (trans ([⨟]ᵛ A (θ s) δ₀) (trans sat (sym ([⨟]ᵛ B (θ s) δ₀))) , tt)
... | just (Ψ⁺ , ρ , equ) with expandSub (ss (res s [ ⟦ ρ ⟧ᴬ ]ᴿ)) in eqx
...   | just _  = ⊥nothing eq
...   | nothing =
        subst (ExpMax δ₁) eqx
              (expandSub-max (ss (res s [ ⟦ ρ ⟧ᴬ ]ᴿ)) δ₁ (⊩ss h₁))
  where
    u = trans ([⨟]ᵛ A (θ s) δ₀) (trans sat (sym ([⨟]ᵛ B (θ s) δ₀))) , tt

    fac = unify-max (rig s) (eqᵛ (A [ θ s ]ᵛ) (B [ θ s ]ᵛ) ∷ []) equ δ₀ u
    δ₁   = proj₁ fac
    tri₁ = proj₂ fac

    h₁ : Q ⊩ᴿ (res s [ ⟦ ρ ⟧ᴬ ]ᴿ) [ δ₁ ]
    h₁ = ⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym tri₁) h)

solve-fail s (A ≾̂ᵥᶜ B) nr eq δ₀ Q fx h sat
  with expandSub ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) in eqx
... | nothing =
      subst (ExpMax δ₀) eqx
            (expandSub-max ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) δ₀ dem)
  where
    dem : ∀ {X Y} → (X , Y) ∈ ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s))
        → Q ∣ X [ δ₀ ]ᵛ <:̂ᵛ Y [ δ₀ ]ᵛ
    dem (here refl) = subst₂ (Q ∣_<:̂ᵛ_) (sym ([⨟]ᵛ A (θ s) δ₀))
                                        (sym ([⨟]ᵛ B (θ s) δ₀)) sat
    dem (there m)   = ⊩ss h m
... | just (Ψ' , δₑ)
      with subDec (A [ θ s ]ᵛ [ δₑ ]ᵛ) (B [ θ s ]ᵛ [ δₑ ]ᵛ) in eqd
...     | just _  = ⊥nothing eq
...     | nothing =
          ⊥nothing (trans (sym (proj₂ (dec (here refl)))) eqd)
  where
    dec = subst (ExpDec ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s))) eqx
                (expandSub-dec ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)))

solve-fail s (ρ ≾̂ᵣᶜ ρ') nr ()

solve-fail s (ε ≾̂ₑᶜ ε') nr ()

solve-fail s (Etᶜ A) nr ()

solve-fail s (Et∨≾ᵘ A ρ) nr eq with decide≾ᵣ {Q = ∅ᴴ} (ρ [ θ s ]ʳ) ûᵣ
... | just _  = ⊥nothing eq
... | nothing = ⊥nothing eq

solve-fail s (∃ᵗ C) (∃ᵗⁿ nc) eq δ₀ Q fx h (B , sat) with solve (s ↑ᵗˢ) C in e
... | just _  = ⊥nothing eq
... | nothing =
      solve-fail (s ↑ᵗˢ) C nc e (δ₀ ,ᵗ B) Q
        (Fixing-trans wkˢᵗ (δ₀ ,ᵗ B) (wk-,ᵗ δ₀ B) fx)
        (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ᵗ δ₀ B)) h))
        (⊨-resp-≐ˢ (≐ˢ-sym (↑-,ᵗˢ (θ s) δ₀ B)) C sat)

solve-fail s (∃ʳ C) (∃ʳⁿ nc) eq δ₀ Q fx h (ρ , sat) with solve (s ↑ʳˢ) C in e
... | just _  = ⊥nothing eq
... | nothing =
      solve-fail (s ↑ʳˢ) C nc e (δ₀ ,ʳ ρ) Q
        (Fixing-trans wkˢʳ (δ₀ ,ʳ ρ) (wk-,ʳ δ₀ ρ) fx)
        (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ʳ δ₀ ρ)) h))
        (⊨-resp-≐ˢ (≐ˢ-sym (↑-,ʳˢ (θ s) δ₀ ρ)) C sat)

solve-fail s (∃ᵉ C) (∃ᵉⁿ nc) eq δ₀ Q fx h (ε , sat) with solve (s ↑ᵉˢ) C in e
... | just _  = ⊥nothing eq
... | nothing =
      solve-fail (s ↑ᵉˢ) C nc e (δ₀ ,ᵉ ε) Q
        (Fixing-trans wkˢᵉ (δ₀ ,ᵉ ε) (wk-,ᵉ δ₀ ε) fx)
        (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ᵉ δ₀ ε)) h))
        (⊨-resp-≐ˢ (≐ˢ-sym (↑-,ᵉˢ (θ s) δ₀ ε)) C sat)

solve-fail s (∀ᵉ C) ()

solve-fail s (⋀ᵒᵖ f) (⋀ⁿ nf) eq
  with threadOps {f = f} (λ s' op → solve s' (f op)) ops s in e
... | just _  = ⊥nothing eq
... | nothing =
      threadOps-fail (λ s' op → solve s' (f op))
                     (λ s' op e' → solve-principal s' (f op) e')
                     (λ s' op e' → solve-fail s' (f op) (nf op) e') ops s e

-- The closing expansion: it factors every satisfying instance, and
-- its failure refutes the residual.

reexpand-princ : ∀ {Θ Ψ''} → (s : St Θ) → {s' : St Θ} {m : s ⟶ s'}
               → reexpand s ≡ just (s' , m)
               → (δ₀ : Subst (Ψ s) Ψ'') → (Q : Hyps Ψ'')
               → Q ⊩ᴿ (res s) [ δ₀ ]
               → Σ[ δ ∈ Subst (Ψ s') Ψ'' ]
                   (((mδ m ⨟ˢ δ) ≐ˢ δ₀) × (Q ⊩ᴿ (res s') [ δ ]))
reexpand-princ s eq δ₀ Q h with expandSub (ss (res s)) in eqx
... | nothing = ⊥just eq
... | just (Ψ' , δₑ) with eq
...   | refl = δ , trix , ⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym trix) h)
  where
    facx = subst (ExpMax δ₀) eqx (expandSub-max (ss (res s)) δ₀ (⊩ss h))
    δ    = proj₁ facx
    trix = proj₂ facx

reexpand-fail : ∀ {Θ Ψ''} → (s : St Θ) → reexpand s ≡ nothing
              → (δ₀ : Subst (Ψ s) Ψ'') → (Q : Hyps Ψ'')
              → Q ⊩ᴿ (res s) [ δ₀ ] → ⊥
reexpand-fail s eq δ₀ Q h with expandSub (ss (res s)) in eqx
... | nothing = subst (ExpMax δ₀) eqx (expandSub-max (ss (res s)) δ₀ (⊩ss h))
... | just _  = ⊥nothing eq

-- After it, every subtyping demand of the residual decomposes

reexpand-dec : ∀ {Θ} → (s : St Θ) → {s' : St Θ} {m : s ⟶ s'}
             → reexpand s ≡ just (s' , m)
             → ∀ {A B} → (A , B) ∈ ss (res s') → Σ[ d ∈ SubDec A B ] (subDec A B ≡ just d)
reexpand-dec s eq with expandSub (ss (res s)) in eqx
... | nothing = ⊥just eq
... | just (Ψ' , δₑ) with eq
...   | refl = f
  where
    dec = subst (ExpDec (ss (res s))) eqx (expandSub-dec (ss (res s)))

    f : ∀ {A B} → (A , B) ∈ map (mapᵖ (_[ δₑ ]ᵛ)) (ss (res s))
      → Σ[ d ∈ SubDec A B ] (subDec A B ≡ just d)
    f m with ∈-map⁻ (mapᵖ (_[ δₑ ]ᵛ)) m
    ... | (A₀ , B₀) , m₀ , refl = dec m₀
