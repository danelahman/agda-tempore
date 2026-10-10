------------------------------------------------------------------
-- Principality and refutation for the driver, against plain    --
-- satisfaction.                                                --
--                                                              --
-- `Princ s s' m C`: every instance of `s` that solves `C` from --
-- no hypotheses and discharges the residual of `s` factors     --
-- through `m` into one discharging the residual of `s'`, a     --
-- rigid-fixing instance staying so. `Refut s C`: no            --
-- rigid-fixing instance discharging the residual of `s` solves --
-- `C`. `solve-principal` and `solve-fail` prove them for       --
-- `solve`, from the same facts for each stage:                 --
-- `solveEt-princ`/`-fail`, `solveDisj-princ`/`-fail`,          --
-- `reexpand-princ`/`reexpand-fail`, `localise-princ`,          --
-- `splitᴿ-princ`/`splitᴿ-fail`,                                --
-- `popᵉ-princ`/`popᵉ-escape`/`popᵉ-fail`,                      --
-- `retry-princ`/`retry-fail`.                                  --
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
open import Data.Maybe using (Is-just)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.Outcome

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Principal
  (S : LanguageSpec)
  (opEnum : OpEnum S)
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
open import TypeInference.Constraints.Properties   S using (⊨-resp-≐ˢ)


open import TypeInference.SolverImpl.Enum S using (AllOp; all-lookup)

open import TypeInference.SolverImpl.Core.Rigid S
  using (strʳ⁺; strᵉ⁺; strᵛ⁺; popˢ; popˢ-hit; strSub; unpopˢ; pop-unpop; strSub-escape;
         strᵛ⁺-just; strʳ⁺-just; strʳ-upd; ∨-true; ∨-left; ∨-right; dec-true; true-dec)

open import TypeInference.SolverImpl.Core.Decorate S using (expandSub)

open import TypeInference.SolverImpl.Expand S
  using (ExpMax; ExpDec; expandSub-max; expandSub-dec)

open import TypeInference.OpenSyntax.Instances S using (_+eⁿ_; _↑ᵉⁿ_; wkᵉⁿ-H; ≐ˢ-↑ᵉⁿ)
open import TypeInference.SolverImpl.Deferred S
open import TypeInference.SolverImpl.Resid  S
open import TypeInference.SolverImpl.State  S
open import TypeInference.SolverImpl.Normal S
open import TypeInference.SolverImpl.Entail S using (decideᵣ; decideₑ; derive)
open import TypeInference.SolverImpl.Solve  S opEnum
open import TypeInference.SolverImpl.Localise S
  using (Localised; localise; lσ; lfix; lcpl; latom; localise-ds; updᵉ-absorb; freeᵉ; freeʳ; anyᶠ; anyᶠ-true;
         outerₑ?; outerᵣ?; Outerₑ; Outerᵣ; κᵉ; κ⊤; ⊩ᴴ-κᵉ; κᵉ≾κ⊤;
         Agree; agreeₑ; agreeᵣ; agree-out; evar?)
open import TypeInference.SolverImpl.Core.Occurs S
  using (occᵉ-e; occᵉ-r; occᵉ-v; occᵉ-c; occʳ-r; occʳ-v; occʳ-c)

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

-- A substitution is uniform on the unknowns `O` mentions when, at each
-- of them, its image reads the same with the eigenvariable at the unit
-- as at the top. The images of an outer scope's unknowns are
-- weakenings, so it is (`uniform-out`); an unknown local to the scope
-- may stand for a function of the eigenvariable, and is excluded.

Uniform : ∀ {Θ Φ Ψ} → Subst Θ Φ → Subst Φ (Ψ +e) → Set
Uniform O X = Agree O X κ⊤ κᵉ

uniform-out : ∀ {Θ Φ Ψ} → (O : Subst Θ Φ) → (X : Subst Φ (Ψ +e)) → (δ₀ : Subst Θ Ψ)
            → (O ⨟ˢ X) ≐ˢ (δ₀ ⨟ˢ wkˢᵉ) → Uniform O X
uniform-out O X δ₀ =
  agree-out O X κ⊤ κᵉ wkˢᵉ δ₀
    (λ y → trans (κ-wkᵛ (econst ⊤ₑ) y) (sym (κ-wkᵛ ûₑ y)))
    (λ y → trans (κ-wkʳ (econst ⊤ₑ) y) (sym (κ-wkʳ ûₑ y)))
    (λ y → trans (κ-wkᵉ (econst ⊤ₑ) y) (sym (κ-wkᵉ ûₑ y)))

-- Both components of a union

∪ᴿ-both : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R R' : Resid Ψ} {δ : Subst Ψ Ψ'}
        → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ R' [ δ ] → Q ⊩ᴿ (R ∪ᴿ R') [ δ ]
∪ᴿ-both {R = R} h h' =
  mk⊩ᴿ (λ m → [ ⊩rs h , ⊩rs h' ]′ (∈-++⁻ (rs R) m))
       (λ m → [ ⊩es h , ⊩es h' ]′ (∈-++⁻ (es R) m))
       (λ m → [ ⊩ts h , ⊩ts h' ]′ (∈-++⁻ (ts R) m))
       (λ m → [ ⊩ss h , ⊩ss h' ]′ (∈-++⁻ (ss R) m))
       (λ m → [ ⊩ds h , ⊩ds h' ]′ (∈-++⁻ (ds R) m))
       (λ m → [ ⊩dfs h , ⊩dfs h' ]′ (∈-++⁻ (dfs R) m))

-- Pushing one atom

pushʳ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {ρ ρ' : RExp Ψ} {δ : Subst Ψ Ψ'}
        → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushʳ ρ ρ' R) [ δ ]
pushʳ-⊩ p h =
  mk⊩ᴿ (λ { (here refl) → p ; (there m) → ⊩rs h m })
       (⊩es h) (⊩ts h) (⊩ss h) (⊩ds h) (⊩dfs h)

pushᵉ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {ε ε' : EExp Ψ} {δ : Subst Ψ Ψ'}
        → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushᵉ ε ε' R) [ δ ]
pushᵉ-⊩ p h =
  mk⊩ᴿ (⊩rs h) (λ { (here refl) → p ; (there m) → ⊩es h m })
       (⊩ts h) (⊩ss h) (⊩ds h) (⊩dfs h)

pushᵗ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {αs : List (TyVar Ψ)} {δ : Subst Ψ Ψ'}
        → (∀ {α} → α ∈ αs → Q ⊩ᴱ tvar α [ δ ]ᵛ) → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushᵗ αs R) [ δ ]
pushᵗ-⊩ {Q = Q} {R = R} {αs = αs} {δ = δ} p h =
  mk⊩ᴿ (⊩rs h) (⊩es h) ts' (⊩ss h) (⊩ds h) (⊩dfs h)
  where
    ts' : ∀ {A} → A ∈ ts (pushᵗ αs R) → Q ⊩ᴱ A [ δ ]ᵛ
    ts' m with ∈-++⁻ (map tvar αs) m
    ... | inj₂ m' = ⊩ts h m'
    ... | inj₁ m' with ∈-map⁻ tvar m'
    ...   | α , m₀ , refl = p m₀

pushᵈ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {A : OVType Ψ} {ρ : RExp Ψ}
            {δ : Subst Ψ Ψ'}
        → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ) → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushᵈ A ρ R) [ δ ]
pushᵈ-⊩ p h =
  mk⊩ᴿ (⊩rs h) (⊩es h) (⊩ts h) (⊩ss h)
       (λ { (here refl) → p ; (there m) → ⊩ds h m }) (⊩dfs h)

evar-inj : ∀ {Θ} {i j : EVar Θ} → evar {Θ} i ≡ evar j → i ≡ j
evar-inj refl = refl

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

-- Principality and refutation are semantic: they concern the
-- instances solving the constraint from no hypotheses, every rigid a
-- parameter. Under hypotheses a var-rule disjunction could be met by
-- one assumed; from none it is met by one of its sides.

PrincAt : ∀ {Θ Ψ''} → (s s' : St Θ) → s ⟶ s' → Constraint Θ → Subst (Ψ s) Ψ'' → Set
PrincAt {Ψ'' = Ψ''} s s' m C δ₀ =
  (θ s ⨟ˢ δ₀) ⊨[ ∅ᴴ ] C → ∅ᴴ ⊩ᴿ (res s) [ δ₀ ]
  → Σ[ δ ∈ Subst (Ψ s') Ψ'' ]
      (((mδ m ⨟ˢ δ) ≐ˢ δ₀)
        × (∅ᴴ ⊩ᴿ (res s') [ δ ])
        × (Fixing (rig s) δ₀ → Fixing (rig s') δ))

Princ : ∀ {Θ} → (s s' : St Θ) → s ⟶ s' → Constraint Θ → Set
Princ s s' m C = ∀ {Ψ''} → (δ₀ : Subst (Ψ s) Ψ'') → PrincAt s s' m C δ₀

-- Principality for the instances entering a rigid scope: the rigid at
-- a fresh eigenvariable

Princ⇑ : ∀ {Θ} → (s : St Θ) → (s' : St (Θ +e)) → ⇑ᵉˢ s ⟶ s' → Constraint (Θ +e) → Set
Princ⇑ s s' m C = ∀ {Ψ''} → (δ₀ : Subst (Ψ s) Ψ'') → PrincAt (⇑ᵉˢ s) s' m C (δ₀ ↑ᵉ)

Refut : ∀ {Θ} → St Θ → Constraint Θ → Set
Refut s C =
  ∀ {Ψ''} → (δ₀ : Subst (Ψ s) Ψ'')
  → Fixing (rig s) δ₀ → ∅ᴴ ⊩ᴿ (res s) [ δ₀ ]
  → ¬ ((θ s ⨟ˢ δ₀) ⊨[ ∅ᴴ ] C)

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

-- A stripped ordering. With the rigid on the right, the inner instance
-- with the eigenvariable sent to the unit is the instance of the kept
-- one. With the rigid on the left, it is the inner instance with the
-- eigenvariable sent to the top that bounds the kept one: from below,
-- by monotonicity, the unit being below the top; from above, by
-- equality, the right side mentioning only outer unknowns.

stripʳ-unit-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (ij? : Maybe (Is-just uₑ-least?))
             → (j : EVar (Φ +e))
             → (ρ ρ' : RExp (Φ +e)) → (ρ₀ : RExp Φ) → (e₁ : ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀)
             → ∀ {a} → stripʳ-unit ij? j ρ ρ' ρ₀ e₁ ≡ just a
             → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
             → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ
             → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
             → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
stripʳ-unit-princ nothing    j ρ ρ' ρ₀ e₁ () γ hγ p
stripʳ-unit-princ {Q = Q} (just ij) j ρ ρ' ρ₀ e₁ eq γ hγ p
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

stripᵉ-unit-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (ij? : Maybe (Is-just uₑ-least?))
             → (j : EVar (Φ +e))
             → (ε ε' : EExp (Φ +e)) → (ε₀ : EExp Φ) → (e₁ : ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀)
             → ∀ {a} → stripᵉ-unit ij? j ε ε' ε₀ e₁ ≡ just a
             → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
             → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ
             → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
             → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
stripᵉ-unit-princ nothing    j ε ε' ε₀ e₁ () γ hγ p
stripᵉ-unit-princ {Q = Q} (just ij) j ε ε' ε₀ e₁ eq γ hγ p
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

stripʳ-top-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O : Subst Θ (Φ +e)) → (j : EVar (Φ +e))
                 → (ρ ρ' : RExp (Φ +e)) → (ρ₀' : RExp Φ) → (e₁ : ρ' [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀')
                 → ∀ {a} → stripʳ-top O j ρ ρ' ρ₀' e₁ ≡ just a
                 → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
                 → Uniform O (popˢ j ⨟ˢ γ)
                 → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ
                 → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
                 → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
stripʳ-top-princ {Φ = Φ} {Φ'} {Q} O j ρ ρ' ρ₀' e₁ eq γ hγ u p
  with outerᵣ? O ρ' | strʳ⁺ j (ρ [ updᵉ j (econst ⊤ₑ) ]ʳ)
... | just o  | just (ρ₀ , e₂) with eq
...   | refl = λ { (here refl) → goal }
  where
    X = popˢ j ⨟ˢ γ
    W = wkˢᵉ ⨟ˢ γ
    ρ⊤ = ρ [ updᵉ j (econst ⊤ₑ) ]ʳ

    top : sE (X ⨟ˢ κ⊤) j ≡ econst ⊤ₑ [ X ⨟ˢ κ⊤ ]ᵉ
    top = cong (_[ κ⊤ ]ᵉ) (trans (cong (_[ γ ]ᵉ) (popˢ-hit j)) hγ)

    at⊤ : ρ⊤ [ X ]ʳ [ κ⊤ ]ʳ ≡ ρ [ X ]ʳ [ κ⊤ ]ʳ
    at⊤ = trans ([⨟]ʳ ρ⊤ X κ⊤)
          (trans ([⨟]ʳ ρ (updᵉ j (econst ⊤ₑ)) (X ⨟ˢ κ⊤))
          (trans ([≐]ʳ (updᵉ-absorb j (econst ⊤ₑ) (X ⨟ˢ κ⊤) top) ρ)
                 (sym ([⨟]ʳ ρ X κ⊤))))

    lhs : Q ⊩ ρ₀ [ W ⨟ˢ κᵉ ]ʳ ≾̂ᵣ ρ [ X ]ʳ [ κ⊤ ]ʳ
    lhs = subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y)
                 (trans (cong (_[ κᵉ ]ʳ) (keyʳ j ρ⊤ e₂ γ)) ([⨟]ʳ ρ₀ W κᵉ)) at⊤
                 (mono-substᵣ κᵉ≾κ⊤ (ρ⊤ [ X ]ʳ))

    rhs : ρ' [ X ]ʳ [ κ⊤ ]ʳ ≡ ρ₀' [ W ⨟ˢ κᵉ ]ʳ
    rhs = trans ([⨟]ʳ ρ' X κ⊤)
          (trans (agreeᵣ {O = O} {X = X} {σ₁ = κ⊤} {σ₂ = κᵉ} u ρ' o)
          (trans (sym ([⨟]ʳ ρ' X κᵉ))
          (trans (cong (_[ κᵉ ]ʳ) (keyʳ j ρ' e₁ γ)) ([⨟]ʳ ρ₀' W κᵉ))))

    -- the inner instance with the eigenvariable at the top
    p⊤ : Q ⊩ ρ [ X ]ʳ [ κ⊤ ]ʳ ≾̂ᵣ ρ' [ X ]ʳ [ κ⊤ ]ʳ
    p⊤ = ⊩-substᵣ {σ = κ⊤} (⊩ᴴ-κ (econst ⊤ₑ)) p

    goal : Q ⊩ ρ₀ [ W ⨟ˢ κᵉ ]ʳ ≾̂ᵣ ρ₀' [ W ⨟ˢ κᵉ ]ʳ
    goal = transᵣ lhs (subst (λ y → Q ⊩ ρ [ X ]ʳ [ κ⊤ ]ʳ ≾̂ᵣ y) rhs p⊤)
stripʳ-top-princ O j ρ ρ' ρ₀' e₁ eq γ hγ u p | just _  | nothing = ⊥just eq
stripʳ-top-princ O j ρ ρ' ρ₀' e₁ eq γ hγ u p | nothing | _       = ⊥just eq

stripᵉ-top-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O : Subst Θ (Φ +e)) → (j : EVar (Φ +e))
                 → (ε ε' : EExp (Φ +e)) → (ε₀' : EExp Φ) → (e₁ : ε' [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀')
                 → ∀ {a} → stripᵉ-top O j ε ε' ε₀' e₁ ≡ just a
                 → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
                 → Uniform O (popˢ j ⨟ˢ γ)
                 → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ
                 → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
                 → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
stripᵉ-top-princ {Φ = Φ} {Φ'} {Q} O j ε ε' ε₀' e₁ eq γ hγ u p
  with outerₑ? O ε' | strᵉ⁺ j (ε [ updᵉ j (econst ⊤ₑ) ]ᵉ)
... | just o  | just (ε₀ , e₂) with eq
...   | refl = λ { (here refl) → goal }
  where
    X = popˢ j ⨟ˢ γ
    W = wkˢᵉ ⨟ˢ γ
    ε⊤ = ε [ updᵉ j (econst ⊤ₑ) ]ᵉ

    top : sE (X ⨟ˢ κ⊤) j ≡ econst ⊤ₑ [ X ⨟ˢ κ⊤ ]ᵉ
    top = cong (_[ κ⊤ ]ᵉ) (trans (cong (_[ γ ]ᵉ) (popˢ-hit j)) hγ)

    at⊤ : ε⊤ [ X ]ᵉ [ κ⊤ ]ᵉ ≡ ε [ X ]ᵉ [ κ⊤ ]ᵉ
    at⊤ = trans ([⨟]ᵉ ε⊤ X κ⊤)
          (trans ([⨟]ᵉ ε (updᵉ j (econst ⊤ₑ)) (X ⨟ˢ κ⊤))
          (trans ([≐]ᵉ (updᵉ-absorb j (econst ⊤ₑ) (X ⨟ˢ κ⊤) top) ε)
                 (sym ([⨟]ᵉ ε X κ⊤))))

    lhs : Q ⊩ ε₀ [ W ⨟ˢ κᵉ ]ᵉ ≾̂ₑ ε [ X ]ᵉ [ κ⊤ ]ᵉ
    lhs = subst₂ (λ x y → Q ⊩ x ≾̂ₑ y)
                 (trans (cong (_[ κᵉ ]ᵉ) (keyᵉ j ε⊤ e₂ γ)) ([⨟]ᵉ ε₀ W κᵉ)) at⊤
                 (mono-substₑ κᵉ≾κ⊤ (ε⊤ [ X ]ᵉ))

    rhs : ε' [ X ]ᵉ [ κ⊤ ]ᵉ ≡ ε₀' [ W ⨟ˢ κᵉ ]ᵉ
    rhs = trans ([⨟]ᵉ ε' X κ⊤)
          (trans (agreeₑ {O = O} {X = X} {σ₁ = κ⊤} {σ₂ = κᵉ} u ε' o)
          (trans (sym ([⨟]ᵉ ε' X κᵉ))
          (trans (cong (_[ κᵉ ]ᵉ) (keyᵉ j ε' e₁ γ)) ([⨟]ᵉ ε₀' W κᵉ))))

    -- the inner instance with the eigenvariable at the top
    p⊤ : Q ⊩ ε [ X ]ᵉ [ κ⊤ ]ᵉ ≾̂ₑ ε' [ X ]ᵉ [ κ⊤ ]ᵉ
    p⊤ = ⊩-substₑ {σ = κ⊤} (⊩ᴴ-κ (econst ⊤ₑ)) p

    goal : Q ⊩ ε₀ [ W ⨟ˢ κᵉ ]ᵉ ≾̂ₑ ε₀' [ W ⨟ˢ κᵉ ]ᵉ
    goal = transₑ lhs (subst (λ y → Q ⊩ ε [ X ]ᵉ [ κ⊤ ]ᵉ ≾̂ₑ y) rhs p⊤)
stripᵉ-top-princ O j ε ε' ε₀' e₁ eq γ hγ u p | just _  | nothing = ⊥just eq
stripᵉ-top-princ O j ε ε' ε₀' e₁ eq γ hγ u p | nothing | _       = ⊥just eq

atomʳ-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O : Subst Θ (Φ +e)) → (j : EVar (Φ +e))
            → (ρ ρ' : RExp (Φ +e))
            → ∀ {a} → atomʳ O j ρ ρ' ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → Uniform O (popˢ j ⨟ˢ γ)
            → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ
            → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
            → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
atomʳ-princ O j ρ ρ' eq γ hγ u p with strʳ⁺ j ρ | strʳ⁺ j ρ'
... | just (ρ₀ , e₁) | just (ρ₀' , e₂) with eq
...   | refl = λ { (here refl) → bndʳ j ρ ρ' e₁ e₂ γ p }
atomʳ-princ O j ρ ρ' eq γ hγ u p | just (ρ₀ , e₁) | nothing with decideᵣ derive ∅ᴴ ρ ρ'
... | just _  with eq
...   | refl = λ ()
atomʳ-princ O j ρ ρ' eq γ hγ u p | just (ρ₀ , e₁) | nothing | nothing =
  stripʳ-unit-princ (Is-just? uₑ-least?) j ρ ρ' ρ₀ e₁ eq γ hγ p
atomʳ-princ O j ρ ρ' eq γ hγ u p | nothing | just (ρ₀' , e₂) with decideᵣ derive ∅ᴴ ρ ρ'
... | just _  with eq
...   | refl = λ ()
atomʳ-princ O j ρ ρ' eq γ hγ u p | nothing | just (ρ₀' , e₂) | nothing =
  stripʳ-top-princ O j ρ ρ' ρ₀' e₂ eq γ hγ u p
atomʳ-princ O j ρ ρ' eq γ hγ u p | nothing | nothing with decideᵣ derive ∅ᴴ ρ ρ'
... | just _  with eq
...   | refl = λ ()
atomʳ-princ O j ρ ρ' eq γ hγ u p | nothing | nothing | nothing = ⊥just eq

atomᵉ-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O : Subst Θ (Φ +e)) → (j : EVar (Φ +e))
            → (ε ε' : EExp (Φ +e))
            → ∀ {a} → atomᵉ O j ε ε' ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → Uniform O (popˢ j ⨟ˢ γ)
            → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ
            → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
            → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
atomᵉ-princ O j ε ε' eq γ hγ u p with strᵉ⁺ j ε | strᵉ⁺ j ε'
... | just (ε₀ , e₁) | just (ε₀' , e₂) with eq
...   | refl = λ { (here refl) → bndᵉ j ε ε' e₁ e₂ γ p }
atomᵉ-princ O j ε ε' eq γ hγ u p | just (ε₀ , e₁) | nothing with decideₑ derive ∅ᴴ ε ε'
... | just _  with eq
...   | refl = λ ()
atomᵉ-princ O j ε ε' eq γ hγ u p | just (ε₀ , e₁) | nothing | nothing =
  stripᵉ-unit-princ (Is-just? uₑ-least?) j ε ε' ε₀ e₁ eq γ hγ p
atomᵉ-princ O j ε ε' eq γ hγ u p | nothing | just (ε₀' , e₂) with decideₑ derive ∅ᴴ ε ε'
... | just _  with eq
...   | refl = λ ()
atomᵉ-princ O j ε ε' eq γ hγ u p | nothing | just (ε₀' , e₂) | nothing =
  stripᵉ-top-princ O j ε ε' ε₀' e₂ eq γ hγ u p
atomᵉ-princ O j ε ε' eq γ hγ u p | nothing | nothing with decideₑ derive ∅ᴴ ε ε'
... | just _  with eq
...   | refl = λ ()
atomᵉ-princ O j ε ε' eq γ hγ u p | nothing | nothing | nothing = ⊥just eq

atomᵗ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (A : OVType (Φ +e))
            → ∀ {a} → atomᵗ j A ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e))
            → wkᵉ-H Q ⊩ᴱ A [ popˢ j ⨟ˢ γ ]ᵛ
            → ∀ {B} → B ∈ proj₁ a → Q ⊩ᴱ B [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ
atomᵗ-princ j A eq γ p with strᵛ⁺ j A
... | just (A₀ , e₁) with eq
...   | refl = λ { (here refl) → bndᵗ j A e₁ γ p }
atomᵗ-princ j A eq γ p | nothing = ⊥just eq

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

-- A kept disjunction, from no hypotheses: an eternal type is the
-- instance's with the eigenvariable at the unit; a grade below the unit
-- bounds, as for `stripʳ-top`, the kept grade from above, with the
-- eigenvariable at the top.

atomᵈ-princ : ∀ {Φ Φ'} → (j : EVar (Φ +e)) → (A : OVType (Φ +e))
            → (ρ : RExp (Φ +e))
            → ∀ {a} → atomᵈ j A ρ ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → VarOK ∅ᴴ (A [ popˢ j ⨟ˢ γ ]ᵛ) (ρ [ popˢ j ⨟ˢ γ ]ʳ)
            → ∀ {B τ} → (B , τ) ∈ proj₁ a
            → VarOK ∅ᴴ (B [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ) (τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ)
atomᵈ-princ j A ρ eq γ hγ p with strᵛ⁺ j A | strʳ⁺ j (ρ [ updᵉ j (econst ⊤ₑ) ]ʳ)
... | just (A₀ , e₁) | just (ρ₀ , e₂) with eq
...   | refl = λ { (here refl) → kept p }
  where
    X = popˢ j ⨟ˢ γ
    W = wkˢᵉ ⨟ˢ γ
    ρ⊤ = ρ [ updᵉ j (econst ⊤ₑ) ]ʳ

    top : sE (X ⨟ˢ κ⊤) j ≡ econst ⊤ₑ [ X ⨟ˢ κ⊤ ]ᵉ
    top = cong (_[ κ⊤ ]ᵉ) (trans (cong (_[ γ ]ᵉ) (popˢ-hit j)) hγ)

    at⊤ : ρ⊤ [ X ]ʳ [ κ⊤ ]ʳ ≡ ρ [ X ]ʳ [ κ⊤ ]ʳ
    at⊤ = trans ([⨟]ʳ ρ⊤ X κ⊤)
          (trans ([⨟]ʳ ρ (updᵉ j (econst ⊤ₑ)) (X ⨟ˢ κ⊤))
          (trans ([≐]ʳ (updᵉ-absorb j (econst ⊤ₑ) (X ⨟ˢ κ⊤) top) ρ)
                 (sym ([⨟]ʳ ρ X κ⊤))))

    lhs : ∅ᴴ ⊩ ρ₀ [ W ⨟ˢ κᵉ ]ʳ ≾̂ᵣ ρ [ X ]ʳ [ κ⊤ ]ʳ
    lhs = subst₂ (λ x y → ∅ᴴ ⊩ x ≾̂ᵣ y)
                 (trans (cong (_[ κᵉ ]ʳ) (keyʳ j ρ⊤ e₂ γ)) ([⨟]ʳ ρ₀ W κᵉ)) at⊤
                 (mono-substᵣ κᵉ≾κ⊤ (ρ⊤ [ X ]ʳ))

    kept : VarOK ∅ᴴ (A [ X ]ᵛ) (ρ [ X ]ʳ)
         → VarOK ∅ᴴ (A₀ [ W ⨟ˢ κᵉ ]ᵛ) (ρ₀ [ W ⨟ˢ κᵉ ]ʳ)
    kept (et-ok et)      = et-ok (bndᵗ j A e₁ γ et)
    kept (≾ᵘ-ok le)      = ≾ᵘ-ok (transᵣ lhs (⊩-substᵣ {σ = κ⊤} (⊩ᴴ-κ (econst ⊤ₑ)) le))
    kept (hyp-ok () _ _)
atomᵈ-princ j A ρ eq γ hγ p | just _  | nothing = ⊥just eq
atomᵈ-princ j A ρ eq γ hγ p | nothing | _       = ⊥just eq

-- Two substitutions after which `O` reads the same agree on every
-- expression mentioning only unknowns `O`'s images mention

agree-≐ : ∀ {Θ Φ Ψ} {O : Subst Θ Φ} {X₁ X₂ : Subst Φ Ψ}
        → (O ⨟ˢ X₁) ≐ˢ (O ⨟ˢ X₂) → Agree O idˢ X₁ X₂
agree-≐ {O = O} {X₁} {X₂} eq =
  agree-out O idˢ X₁ X₂ O idˢ
    (λ y → trans ([⨟]ᵛ y O X₁) (trans ([≐]ᵛ eq y) (sym ([⨟]ᵛ y O X₂))))
    (λ y → trans ([⨟]ʳ y O X₁) (trans ([≐]ʳ eq y) (sym ([⨟]ʳ y O X₂))))
    (λ y → trans ([⨟]ᵉ y O X₁) (trans ([≐]ᵉ eq y) (sym ([⨟]ᵉ y O X₂))))
    (≐ˢ-trans (⨟-idʳ O) (≐ˢ-sym (⨟-idˡ O)))

agree-≡ʳ : ∀ {Θ Φ Ψ} {O : Subst Θ Φ} {X₁ X₂ : Subst Φ Ψ}
         → (O ⨟ˢ X₁) ≐ˢ (O ⨟ˢ X₂) → (x : RExp Φ) → Outerᵣ O x → x [ X₁ ]ʳ ≡ x [ X₂ ]ʳ
agree-≡ʳ {O = O} {X₁} {X₂} eq x o =
  trans (sym ([≐]ʳ (⨟-idˡ X₁) x))
        (trans (agreeᵣ {O = O} {X = idˢ} {σ₁ = X₁} {σ₂ = X₂} (agree-≐ {O = O} {X₁} {X₂} eq) x o)
               ([≐]ʳ (⨟-idˡ X₂) x))

agree-≡ᵉ : ∀ {Θ Φ Ψ} {O : Subst Θ Φ} {X₁ X₂ : Subst Φ Ψ}
         → (O ⨟ˢ X₁) ≐ˢ (O ⨟ˢ X₂) → (x : EExp Φ) → Outerₑ O x → x [ X₁ ]ᵉ ≡ x [ X₂ ]ᵉ
agree-≡ᵉ {O = O} {X₁} {X₂} eq x o =
  trans (sym ([≐]ᵉ (⨟-idˡ X₁) x))
        (trans (agreeₑ {O = O} {X = idˢ} {σ₁ = X₁} {σ₂ = X₂} (agree-≐ {O = O} {X₁} {X₂} eq) x o)
               ([≐]ᵉ (⨟-idˡ X₂) x))

-- An entry mentioning only such unknowns, under its binders, holds
-- after the one when it holds after the other

⊩ᵈ-agree : ∀ {Θ Φ Ψ} {Q : Hyps Ψ} {O : Subst Θ Φ} {X₁ X₂ : Subst Φ Ψ} → (E : Dfr Φ)
         → Outerᵒ (O ↑ᵉⁿ nb E) (body E) → (O ⨟ˢ X₁) ≐ˢ (O ⨟ˢ X₂)
         → Q ⊩ᵈ E [ X₁ ] → Q ⊩ᵈ E [ X₂ ]
⊩ᵈ-agree {Q = Q} {O} {X₁} {X₂} (dfr l k o) (or , oe) eq h = mk⊩ᵒ r e
  where
    eq' : ((O ↑ᵉⁿ k) ⨟ˢ (X₁ ↑ᵉⁿ k)) ≐ˢ ((O ↑ᵉⁿ k) ⨟ˢ (X₂ ↑ᵉⁿ k))
    eq' = ≐ˢ-trans (⨟-↑ᵉⁿ O X₁ k) (≐ˢ-trans (≐ˢ-↑ᵉⁿ eq k) (≐ˢ-sym (⨟-↑ᵉⁿ O X₂ k)))

    r : ∀ {x y} → (x , y) ∈ ors o → wkᵉⁿ-H k Q ⊩ x [ X₂ ↑ᵉⁿ k ]ʳ ≾̂ᵣ y [ X₂ ↑ᵉⁿ k ]ʳ
    r {x} {y} m = subst₂ (λ a b → wkᵉⁿ-H k Q ⊩ a ≾̂ᵣ b)
                         (agree-≡ʳ {O = O ↑ᵉⁿ k} eq' x (proj₁ (or m))) (agree-≡ʳ {O = O ↑ᵉⁿ k} eq' y (proj₂ (or m)))
                         (⊩ors h m)

    e : ∀ {x y} → (x , y) ∈ oes o → wkᵉⁿ-H k Q ⊩ x [ X₂ ↑ᵉⁿ k ]ᵉ ≾̂ₑ y [ X₂ ↑ᵉⁿ k ]ᵉ
    e {x} {y} m = subst₂ (λ a b → wkᵉⁿ-H k Q ⊩ a ≾̂ₑ b)
                         (agree-≡ᵉ {O = O ↑ᵉⁿ k} eq' x (proj₁ (oe m))) (agree-≡ᵉ {O = O ↑ᵉⁿ k} eq' y (proj₂ (oe m)))
                         (⊩oes h m)

-- The kept orderings hold at the instance of the outer scope; the
-- deferred ones, which mention only the rigid and outer unknowns, at
-- that instance lifted over the rigid, the outer unknowns' images
-- being uniform in it (`eqO`)

listʳ-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O : Subst Θ (Φ +e)) → (O⁺ : Subst (Θ +e) (Φ +e))
            → (j : EVar (Φ +e)) → (l : List (RExp (Φ +e) × RExp (Φ +e)))
            → ∀ {a} → listʳ O O⁺ j l ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → Uniform O (popˢ j ⨟ˢ γ)
            → (O⁺ ⨟ˢ (popˢ j ⨟ˢ γ)) ≐ˢ (O⁺ ⨟ˢ (popˢ j ⨟ˢ (((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ)))
            → (∀ {ρ ρ'} → (ρ , ρ') ∈ l
                 → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ)
            → (∀ {τ τ'} → (τ , τ') ∈ proj₁ a
                 → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ)
            × (∀ {τ τ'} → (τ , τ') ∈ proj₁ (proj₂ a)
                 → wkᵉ-H Q ⊩ τ [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ʳ ≾̂ᵣ τ' [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ʳ)
listʳ-princ O O⁺ j []              refl γ hγ u eqO k = (λ ()) , (λ ())
listʳ-princ O O⁺ j ((ρ , ρ') ∷ l) eq γ hγ u eqO k with listʳ O O⁺ j l in e₂
... | nothing = ⊥just eq
... | just (l₀ , d₀ , f) with atomʳ O j ρ ρ' in e₁
...   | just (a , fa) with eq
...     | refl = (λ m → [ atomʳ-princ O j ρ ρ' e₁ γ hγ u (k (here refl)) , proj₁ ih ]′ (∈-++⁻ a m))
               , proj₂ ih
  where
    ih = listʳ-princ O O⁺ j l e₂ γ hγ u eqO (λ m' → k (there m'))
listʳ-princ {Q = Q} O O⁺ j ((ρ , ρ') ∷ l) eq γ hγ u eqO k | just (l₀ , d₀ , f) | nothing
  with outerᵣ? O⁺ ρ | outerᵣ? O⁺ ρ'
... | just o | just o' with eq
...   | refl = proj₁ ih , (λ { (here refl) → deferred ; (there m) → proj₂ ih m })
  where
    ih = listʳ-princ O O⁺ j l e₂ γ hγ u eqO (λ m' → k (there m'))

    X = ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ

    at : (x : RExp _) → Outerᵣ O⁺ x → x [ popˢ j ⨟ˢ γ ]ʳ ≡ x [ popˢ j ]ʳ [ X ]ʳ
    at x ox = trans (agree-≡ʳ {O = O⁺} eqO x ox) (sym ([⨟]ʳ x (popˢ j) X))

    deferred : wkᵉ-H Q ⊩ ρ [ popˢ j ]ʳ [ X ]ʳ ≾̂ᵣ ρ' [ popˢ j ]ʳ [ X ]ʳ
    deferred = subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y) (at ρ o) (at ρ' o') (k (here refl))
listʳ-princ O O⁺ j ((ρ , ρ') ∷ l) eq γ hγ u eqO k | just _ | nothing | just _  | nothing = ⊥just eq
listʳ-princ O O⁺ j ((ρ , ρ') ∷ l) eq γ hγ u eqO k | just _ | nothing | nothing | _       = ⊥just eq

listᵉ-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O : Subst Θ (Φ +e)) → (O⁺ : Subst (Θ +e) (Φ +e))
            → (j : EVar (Φ +e)) → (l : List (EExp (Φ +e) × EExp (Φ +e)))
            → ∀ {a} → listᵉ O O⁺ j l ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → Uniform O (popˢ j ⨟ˢ γ)
            → (O⁺ ⨟ˢ (popˢ j ⨟ˢ γ)) ≐ˢ (O⁺ ⨟ˢ (popˢ j ⨟ˢ (((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ)))
            → (∀ {ε ε'} → (ε , ε') ∈ l
                 → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ)
            → (∀ {τ τ'} → (τ , τ') ∈ proj₁ a
                 → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ)
            × (∀ {τ τ'} → (τ , τ') ∈ proj₁ (proj₂ a)
                 → wkᵉ-H Q ⊩ τ [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ᵉ ≾̂ₑ τ' [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ᵉ)
listᵉ-princ O O⁺ j []              refl γ hγ u eqO k = (λ ()) , (λ ())
listᵉ-princ O O⁺ j ((ε , ε') ∷ l) eq γ hγ u eqO k with listᵉ O O⁺ j l in e₂
... | nothing = ⊥just eq
... | just (l₀ , d₀ , f) with atomᵉ O j ε ε' in e₁
...   | just (a , fa) with eq
...     | refl = (λ m → [ atomᵉ-princ O j ε ε' e₁ γ hγ u (k (here refl)) , proj₁ ih ]′ (∈-++⁻ a m))
               , proj₂ ih
  where
    ih = listᵉ-princ O O⁺ j l e₂ γ hγ u eqO (λ m' → k (there m'))
listᵉ-princ {Q = Q} O O⁺ j ((ε , ε') ∷ l) eq γ hγ u eqO k | just (l₀ , d₀ , f) | nothing
  with outerₑ? O⁺ ε | outerₑ? O⁺ ε'
... | just o | just o' with eq
...   | refl = proj₁ ih , (λ { (here refl) → deferred ; (there m) → proj₂ ih m })
  where
    ih = listᵉ-princ O O⁺ j l e₂ γ hγ u eqO (λ m' → k (there m'))

    X = ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ

    at : (x : EExp _) → Outerₑ O⁺ x → x [ popˢ j ⨟ˢ γ ]ᵉ ≡ x [ popˢ j ]ᵉ [ X ]ᵉ
    at x ox = trans (agree-≡ᵉ {O = O⁺} eqO x ox) (sym ([⨟]ᵉ x (popˢ j) X))

    deferred : wkᵉ-H Q ⊩ ε [ popˢ j ]ᵉ [ X ]ᵉ ≾̂ₑ ε' [ popˢ j ]ᵉ [ X ]ᵉ
    deferred = subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y) (at ε o) (at ε' o') (k (here refl))
listᵉ-princ O O⁺ j ((ε , ε') ∷ l) eq γ hγ u eqO k | just _ | nothing | just _  | nothing = ⊥just eq
listᵉ-princ O O⁺ j ((ε , ε') ∷ l) eq γ hγ u eqO k | just _ | nothing | nothing | _       = ⊥just eq

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

listᵈ-princ : ∀ {Φ Φ'} → (j : EVar (Φ +e))
            → (l : List (OVType (Φ +e) × RExp (Φ +e)))
            → ∀ {a} → listᵈ j l ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → (∀ {A ρ} → (A , ρ) ∈ l
                 → VarOK ∅ᴴ (A [ popˢ j ⨟ˢ γ ]ᵛ) (ρ [ popˢ j ⨟ˢ γ ]ʳ))
            → ∀ {B τ} → (B , τ) ∈ proj₁ a
            → VarOK ∅ᴴ (B [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ) (τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ)
listᵈ-princ j []             refl γ hγ k = λ ()
listᵈ-princ j ((A , ρ) ∷ l) eq γ hγ k with atomᵈ j A ρ in e₁ | listᵈ j l in e₂
... | just (a , fa) | just (l₁ , f) with eq
...   | refl = λ m → [ atomᵈ-princ j A ρ e₁ γ hγ (k (here refl))
                     , listᵈ-princ j l e₂ γ hγ (λ m' → k (there m')) ]′ (∈-++⁻ a m)
listᵈ-princ j ((A , ρ) ∷ l) eq γ hγ k | just _  | nothing = ⊥just eq
listᵈ-princ j ((A , ρ) ∷ l) eq γ hγ k | nothing | _       = ⊥just eq

-- A lifted inner entry holds at the outer instance: under the new
-- binder it is the inner entry at the inner instance, read the same

liftᵈ-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O⁺ : Subst (Θ +e) (Φ +e)) → (j : EVar (Φ +e))
            → (γ : Subst (Φ +e) (Φ' +e)) → (δ : Subst Φ Φ') → (E : Dfr (Φ +e))
            → Outerᵒ (O⁺ ↑ᵉⁿ nb E) (body E)
            → (O⁺ ⨟ˢ (popˢ j ⨟ˢ γ)) ≐ˢ (O⁺ ⨟ˢ (popˢ j ⨟ˢ (δ ↑ᵉ)))
            → wkᵉ-H Q ⊩ᵈ E [ popˢ j ⨟ˢ γ ] → Q ⊩ᵈ liftᵈ j E [ δ ]
liftᵈ-princ O⁺ j γ δ E oo eqO h =
  closeᵈ-princ (E [ popˢ j ]ᵈ) (⊩ᵈ-subst⁻ E (⊩ᵈ-agree E oo eqO h))

splitᴿ-princ : ∀ {Θ Φ Φ'} → (O : Subst Θ (Φ +e)) → (O⁺ : Subst (Θ +e) (Φ +e))
             → (j : EVar (Φ +e)) → (R : Resid (Φ +e))
             → ∀ {a} → splitᴿ O O⁺ j R ≡ solved a
             → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
             → Uniform O (popˢ j ⨟ˢ γ)
             → (O⁺ ⨟ˢ (popˢ j ⨟ˢ γ)) ≐ˢ (O⁺ ⨟ˢ (popˢ j ⨟ˢ (((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ)))
             → ∅ᴴ ⊩ᴿ R [ popˢ j ⨟ˢ γ ]
             → ∅ᴴ ⊩ᴿ proj₁ a [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]
splitᴿ-princ O O⁺ j R eq γ hγ u eqO h
  with listᵗ j (ts R) in e₃ | listˢ j (ss R) in e₄ | listᵈ j (ds R) in e₅
     | listʳ O O⁺ j (rs R) in e₁ | listᵉ O O⁺ j (es R) in e₂ | outerD? O⁺ (dfs R)
... | just (lt , ft) | just (ls , fs) | just (ld , fd)
    | just (lr , dr , fr) | just (le , de , fe) | just od with eq
...   | refl = mk⊩ᴿ (proj₁ pr) (proj₁ pe)
                    (listᵗ-princ j (ts R) e₃ γ (⊩ts h))
                    (listˢ-princ j (ss R) e₄ γ (⊩ss h))
                    (listᵈ-princ j (ds R) e₅ γ hγ (⊩ds h))
                    (λ { (here refl) → closeᵈ-princ (dfr nothing 0 (ords dr de))
                                                    (mk⊩ᵒ (proj₂ pr) (proj₂ pe))
                       ; (there m) → lifted m })
  where
    pr = listʳ-princ O O⁺ j (rs R) e₁ γ hγ u eqO (⊩rs h)
    pe = listᵉ-princ O O⁺ j (es R) e₂ γ hγ u eqO (⊩es h)

    lifted : ∀ {E} → E ∈ map (liftᵈ j) (dfs R) → ∅ᴴ ⊩ᵈ E [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]
    lifted m with ∈-map⁻ (liftᵈ j) m
    ... | E₀ , m₀ , refl = liftᵈ-princ O⁺ j γ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) E₀ (od m₀) eqO (⊩dfs h m₀)
splitᴿ-princ O O⁺ j R eq γ hγ u eqO h | nothing | _       | _       | _      | _      | _       = ⊥refuted eq
splitᴿ-princ O O⁺ j R eq γ hγ u eqO h | just _  | nothing | _       | _      | _      | _       = ⊥refuted eq
splitᴿ-princ O O⁺ j R eq γ hγ u eqO h | just _  | just _  | nothing | _      | _      | _       = ⊥refuted eq
splitᴿ-princ O O⁺ j R eq γ hγ u eqO h | just _  | just _  | just _  | nothing | _     | _       = ⊥stuck eq
splitᴿ-princ O O⁺ j R eq γ hγ u eqO h | just _  | just _  | just _  | just _ | nothing | _      = ⊥stuck eq
splitᴿ-princ O O⁺ j R eq γ hγ u eqO h | just _  | just _  | just _  | just _ | just _ | nothing = ⊥stuck eq

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
           → Princ⇑ s (st Φ θ'' R'' rg'') m'' C
           → ∀ {s' : St Θ} {m : s ⟶ s'} {w : Wit s' (∀ᵉ C)}
           → popᵉ s C Φ θ'' R'' rg'' m'' w'' ≡ solved (s' , m , w)
           → Princ s s' m (∀ᵉ C)
popᵉ-princ s C (scope nt nr nzero) θ'' R'' rg'' m'' w'' ip ()
popᵉ-princ s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' ip eq δ₀ sat h
  with evar? (sE (mδ m'') (newᵉ {Ψ s}))
... | nothing = ⊥refuted eq
... | just (j , eqj) with strSub j (wkˢᵉ {Ψ s} ⨟ˢ mδ m'')
                        | splitᴿ (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') (mδ m'') j R'' in eqsp
...   | just (δ₀ₛ , pδ) | solved (R₀ , tr) with eq
...     | refl = δ , tri ,
                 ∪ᴿ-both (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym tri) h))
                         (splitᴿ-princ (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') (mδ m'') j R'' eqsp γ
                           (bnd-var (mδ m'') δ'' tri'' eqj) uni eqO
                           (⊩ᴿ-resp-≐ˢ (≐ˢ-sym popγ) hres'')) ,
                 (λ fx → Fixing-trans δ₀ₛ δ tri fx)
  where
    ires = ip δ₀ (⊨-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉ (θ s) δ₀)) C sat) ⊩ᴿ-empty

    δ''    = proj₁ ires
    tri''  = proj₁ (proj₂ ires)
    hres'' = proj₁ (proj₂ (proj₂ ires))

    γ    = unpopˢ j ⨟ˢ δ''
    popγ = ≐ˢ-trans (≐ˢ-sym (⨟-assoc (popˢ j) (unpopˢ j) δ''))
                    (≐ˢ-trans (⨟-congˡ (pop-unpop j) δ'') (⨟-idˡ δ''))

    δ = (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ

    -- the outer unknowns' images are uniform in the eigenvariable
    uni : Uniform (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') (popˢ j ⨟ˢ γ)
    uni = uniform-out (wkˢᵉ ⨟ˢ mδ m'') (popˢ j ⨟ˢ γ) δ₀
            (≐ˢ-trans (⨟-congʳ (wkˢᵉ ⨟ˢ mδ m'') popγ) (bnd-out (mδ m'') δ'' δ₀ tri''))

    inner = ≐ˢ-trans (≐ˢ-sym (⨟-assoc δ₀ₛ wkˢᵉ γ))
            (≐ˢ-trans (⨟-congˡ (≐ˢ-sym pδ) γ)
            (≐ˢ-trans (⨟-assoc (wkˢᵉ ⨟ˢ mδ m'') (popˢ j) γ)
            (≐ˢ-trans (⨟-congʳ (wkˢᵉ ⨟ˢ mδ m'') popγ)
            (≐ˢ-trans (⨟-assoc wkˢᵉ (mδ m'') δ'')
            (≐ˢ-trans (⨟-congʳ wkˢᵉ tri'') (wkˢᵉ-↑ᵉ δ₀))))))

    tri = ≐ˢ-trans (≐ˢ-sym (⨟-assoc δ₀ₛ (wkˢᵉ ⨟ˢ γ) κᵉ))
          (≐ˢ-trans (⨟-congˡ inner κᵉ)
          (≐ˢ-trans (⨟-assoc δ₀ wkˢᵉ κᵉ)
          (≐ˢ-trans (⨟-congʳ δ₀ (wk-κ ûₑ)) (⨟-idʳ δ₀))))

    -- the unknowns the scope was entered with read the same at the
    -- inner instance as at the outer one lifted over the rigid
    eqO : (mδ m'' ⨟ˢ (popˢ j ⨟ˢ γ)) ≐ˢ (mδ m'' ⨟ˢ (popˢ j ⨟ˢ (δ ↑ᵉ)))
    eqO = ≐ˢ-trans (⨟-congʳ (mδ m'') popγ)
          (≐ˢ-trans tri''
          (≐ˢ-sym (≐ˢ-trans (≐ˢ-sym (⨟-assoc (mδ m'') (popˢ j) (δ ↑ᵉ)))
                  (≐ˢ-trans (⨟-congˡ (pop-key (mδ m'') eqj pδ) (δ ↑ᵉ))
                  (≐ˢ-trans (⨟-↑ᵉ δ₀ₛ δ) (≐ˢ-↑ᵉ tri))))))

popᵉ-princ s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' ip eq δ₀ sat h
  | just (j , eqj) | just _ | refuted = ⊥refuted eq
popᵉ-princ s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' ip eq δ₀ sat h
  | just (j , eqj) | just _ | stuck = ⊥stuck eq
popᵉ-princ s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' ip eq δ₀ sat h
  | just (j , eqj) | nothing | _ = ⊥refuted eq

-- Localisation keeps every instance entering the scope: the factor
-- found for the inner state serves the localised one, the local
-- unknowns being in no image of the outer ones, and each step keeping
-- the residual.

localise-princ : ∀ {Θ} {s : St Θ} {s'' : St (Θ +e)} {m : ⇑ᵉˢ s ⟶ s''} {C : Constraint (Θ +e)}
               → Princ⇑ s s'' m C
               → Princ⇑ s (proj₁ (localiseˢ s m)) (⟶-⨟ m (proj₂ (localiseˢ s m))) C
localise-princ {s'' = s''} {m} ip δ₀ sat h =
  δ , ≐ˢ-trans (⨟-congˡ (lfix L) δ) tri , lcpl L δ (δ₀ , tri) hres , fx
  where
    L : Localised (mδ m) (res s'')
    L = localise (mδ m) (res s'')

    f    = ip δ₀ sat h
    δ    = proj₁ f
    tri  = proj₁ (proj₂ f)
    hres = proj₁ (proj₂ (proj₂ f))
    fx   = proj₂ (proj₂ (proj₂ f))

-- A retry keeps every instance: it drops only orderings and entries
-- that one discharging the residual discharges

retry-princ : ∀ {Θ} → (s : St Θ) → {s' : St Θ} {m : s ⟶ s'} → retry s ≡ just (s' , m)
            → ∀ {Ψ''} → (δ₀ : Subst (Ψ s) Ψ'') → ∅ᴴ ⊩ᴿ (res s) [ δ₀ ]
            → Σ[ δ ∈ Subst (Ψ s') Ψ'' ]
                (((mδ m ⨟ˢ δ) ≐ˢ δ₀) × (∅ᴴ ⊩ᴿ (res s') [ δ ])
                  × (Fixing (rig s) δ₀ → Fixing (rig s') δ))
retry-princ s eq δ₀ h with retryᴰ (ordsOf (res s)) (dfs (res s))
... | inj₁ _                 = ⊥just eq
... | inj₂ (retriedL D' b f) with eq
...   | refl = δ₀ , ⨟-idˡ δ₀ ,
               mk⊩ᴿ (⊩rs h) (⊩es h) (⊩ts h) (⊩ss h) (⊩ds h) (f δ₀ (⊩dfs h)) ,
               (λ fx → fx)

-- and it refuses only where an entry fails at a closed witness, which
-- refutes every instance: closed further, it would be a closed one

retry-fail : ∀ {Θ Ψ''} → (s : St Θ) → retry s ≡ nothing
           → (δ₀ : Subst (Ψ s) Ψ'') → ∅ᴴ ⊩ᴿ (res s) [ δ₀ ] → ⊥
retry-fail s eq δ₀ h with retryᴰ (ordsOf (res s)) (dfs (res s))
... | inj₁ (E , m , r) = r (δ₀ ⨟ˢ groundˢ) (⊩dfs (⊩ᴿ-⨟ {δ' = groundˢ} ∅ᴴ-⊩ᴴ h) m)
... | inj₂ _           = ⊥nothing eq

thenRetry-princ : ∀ {Θ} {s : St Θ} {C : Constraint Θ}
                → (x : Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C)))
                → (∀ {s₁ : St Θ} {m₁ : s ⟶ s₁} {w₁ : Wit s₁ C}
                     → x ≡ solved (s₁ , m₁ , w₁) → Princ s s₁ m₁ C)
                → ∀ {s' : St Θ} {m : s ⟶ s'} {w : Wit s' C}
                → thenRetry {C = C} x ≡ solved (s' , m , w) → Princ s s' m C
thenRetry-princ refuted p ()
thenRetry-princ stuck   p ()
thenRetry-princ {C = C} (solved (s₁ , m₁ , w₁)) p eq δ₀ sat h with retry s₁ in e
... | nothing = ⊥refuted eq
... | just (s₂ , m₂) with eq
...   | refl = δ₂ ,
               ≐ˢ-trans (⨟-assoc (mδ m₁) (mδ m₂) δ₂)
                        (≐ˢ-trans (⨟-congʳ (mδ m₁) tri₂) tri₁) ,
               h₂ , (λ fx → fx₂ (fx₁ fx))
  where
    f₁   = p refl δ₀ sat h
    δ₁   = proj₁ f₁
    tri₁ = proj₁ (proj₂ f₁)
    h₁   = proj₁ (proj₂ (proj₂ f₁))
    fx₁  = proj₂ (proj₂ (proj₂ f₁))

    f₂   = retry-princ s₁ e δ₁ h₁
    δ₂   = proj₁ f₂
    tri₂ = proj₁ (proj₂ f₂)
    h₂   = proj₁ (proj₂ (proj₂ f₂))
    fx₂  = proj₂ (proj₂ (proj₂ f₂))

-- Labelling changes no meaning

relabel-⊩⁻ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (op : Op) → (E : Dfr Ψ)
           → Q ⊩ᵈ E [ δ ] → Q ⊩ᵈ relabel op E [ δ ]
relabel-⊩⁻ op (dfr nothing  k o) h = h
relabel-⊩⁻ op (dfr (just l) k o) h = h

labelled-princ : ∀ {Θ} {s : St Θ} {C : Constraint Θ} → (op : Op)
               → (x : Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C)))
               → (∀ {s₁ : St Θ} {m₁ : s ⟶ s₁} {w₁ : Wit s₁ C}
                    → x ≡ solved (s₁ , m₁ , w₁) → Princ s s₁ m₁ C)
               → ∀ {s' : St Θ} {m : s ⟶ s'} {w : Wit s' C}
               → labelled {C = C} op x ≡ solved (s' , m , w) → Princ s s' m C
labelled-princ op refuted p ()
labelled-princ op stuck   p ()
labelled-princ op (solved (s₁ , m₁ , w₁)) p refl δ₀ sat h =
  δ₁ , ≐ˢ-trans (⨟-assoc (mδ m₁) idˢ δ₁) (≐ˢ-trans (⨟-congʳ (mδ m₁) (⨟-idˡ δ₁)) tri₁) ,
  mk⊩ᴿ (⊩rs h₁) (⊩es h₁) (⊩ts h₁) (⊩ss h₁) (⊩ds h₁) dfs' , fx₁
  where
    f₁   = p refl δ₀ sat h
    δ₁   = proj₁ f₁
    tri₁ = proj₁ (proj₂ f₁)
    h₁   = proj₁ (proj₂ (proj₂ f₁))
    fx₁  = proj₂ (proj₂ (proj₂ f₁))

    dfs' : ∀ {E} → E ∈ map (relabel op) (dfs (res s₁)) → ∅ᴴ ⊩ᵈ E [ δ₁ ]
    dfs' m with ∈-map⁻ (relabel op) m
    ... | E₀ , m₀ , refl = relabel-⊩⁻ op E₀ (⊩dfs h₁ m₀)

labelled-refuted : ∀ {Θ} {s : St Θ} {C : Constraint Θ} → (op : Op)
                 → (x : Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C)))
                 → labelled {C = C} op x ≡ refuted → x ≡ refuted
labelled-refuted op refuted    eq = refl
labelled-refuted op stuck      ()
labelled-refuted op (solved _) ()

threadOps-princ : ∀ {Θ} {f : Op → Constraint Θ}
   → (g : (s : St Θ) → (op : Op)
            → Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' (f op))))
   → ((s : St Θ) → (op : Op) → {s' : St Θ} {m : s ⟶ s'} {w : Wit s' (f op)}
        → g s op ≡ solved (s' , m , w) → Princ s s' m (f op))
   → (l : List Op) → (s : St Θ)
   → {s' : St Θ} {m : s ⟶ s'} {ws : AllOp (λ op → Wit s' (f op)) l}
   → threadOps {f = f} g l s ≡ solved (s' , m , ws)
   → Princ s s' m (⋀ᵒᵖ f)
threadOps-princ g gp []       s refl δ₀ sat h = δ₀ , ≐ˢ-refl , h , (λ fx → fx)
threadOps-princ {f = f} g gp (op ∷ l) s eq δ₀ sat h with g s op in e₁
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (s₁ , m₁ , w₁) with threadOps {f = f} g l s₁ in e₂
...   | refuted = ⊥refuted eq
...   | stuck   = ⊥stuck eq
...   | solved (s₂ , m₂ , ws) with eq
...     | refl = δ₂ ,
                 ≐ˢ-trans (⨟-assoc (mδ m₁) (mδ m₂) δ₂)
                          (≐ˢ-trans (⨟-congʳ (mδ m₁) tri₂) tri₁) ,
                 h₂ , (λ fx → fx₂ (fx₁ fx))
  where
    f₁  = gp s op e₁ δ₀ (sat op) h
    δ₁  = proj₁ f₁
    tri₁ = proj₁ (proj₂ f₁)
    h₁  = proj₁ (proj₂ (proj₂ f₁))
    fx₁ = proj₂ (proj₂ (proj₂ f₁))

    chain = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₁)) δ₁)
            (≐ˢ-trans (⨟-assoc (θ s) (mδ m₁) δ₁) (⨟-congʳ (θ s) tri₁))

    f₂  = threadOps-princ g gp l s₁ e₂ δ₁
            (λ op' → ⊨-resp-≐ˢ (≐ˢ-sym chain) (f op') (sat op')) h₁
    δ₂  = proj₁ f₂
    tri₂ = proj₁ (proj₂ f₂)
    h₂  = proj₁ (proj₂ (proj₂ f₂))
    fx₂ = proj₂ (proj₂ (proj₂ f₂))

-- After an expansion, the decomposition of the demands it was asked
-- about cannot fail

subsList-exp : ∀ {Ψ Ψ'} → (l : List (OVType Ψ × OVType Ψ)) → (δ : Subst Ψ Ψ')
             → (∀ {A B} → (A , B) ∈ l
                  → Σ[ d ∈ SubDec (A [ δ ]ᵛ) (B [ δ ]ᵛ) ] (subDec (A [ δ ]ᵛ) (B [ δ ]ᵛ) ≡ just d))
             → subsList (map (mapᵖ (_[ δ ]ᵛ)) l) ≡ nothing → ⊥
subsList-exp l δ dec q with subsList-nothing (map (mapᵖ (_[ δ ]ᵛ)) l) q
... | A , B , m , r with ∈-map⁻ (mapᵖ (_[ δ ]ᵛ)) m
...   | (A₀ , B₀) , m₀ , refl = ⊥just (trans (sym r) (proj₂ (dec m₀)))

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
... | just (Ψ' , δₑ) with subsList (ss (res s [ δₑ ]ᴿ)) | etsDec (ts (res s [ δₑ ]ᴿ))
...   | nothing | _       = ⊥just eq
...   | just _  | nothing = ⊥just eq
...   | just e  | just t with eq
...     | refl = δ , trix , atomiseᴿ-compl _ e t (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym trix) h))
  where
    facx = subst (ExpMax δ₀) eqx (expandSub-max (ss (res s)) δ₀ (⊩ss h))
    δ    = proj₁ facx
    trix = proj₂ facx

reexpand-fail : ∀ {Θ Ψ''} → (s : St Θ) → reexpand s ≡ nothing
              → (δ₀ : Subst (Ψ s) Ψ'') → (Q : Hyps Ψ'')
              → Q ⊩ᴿ (res s) [ δ₀ ] → ⊥
reexpand-fail s eq δ₀ Q h with expandSub (ss (res s)) in eqx
... | nothing = subst (ExpMax δ₀) eqx (expandSub-max (ss (res s)) δ₀ (⊩ss h))
... | just (Ψ' , δₑ) with subsList (ss (res s [ δₑ ]ᴿ)) in eqs | etsDec (ts (res s [ δₑ ]ᴿ)) in eqt
...   | just _  | just _  = ⊥nothing eq
...   | just _  | nothing =
        etsDec-refute (ts (res s [ δₑ ]ᴿ)) eqt δ
          (⊩ts (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym trix) h)))
  where
    facx = subst (ExpMax δ₀) eqx (expandSub-max (ss (res s)) δ₀ (⊩ss h))
    δ    = proj₁ facx
    trix = proj₂ facx
...   | nothing | _       =
        subsList-exp (ss (res s)) δₑ
          (subst (ExpDec (ss (res s))) eqx (expandSub-dec (ss (res s)))) eqs

-- and keeps the rigids fixed

reexpand-fix : ∀ {Θ Ψ''} → (s : St Θ) → {s' : St Θ} {m : s ⟶ s'}
             → reexpand s ≡ just (s' , m)
             → {δ₀ : Subst (Ψ s) Ψ''} → (δ : Subst (Ψ s') Ψ'') → (mδ m ⨟ˢ δ) ≐ˢ δ₀
             → Fixing (rig s) δ₀ → Fixing (rig s') δ
reexpand-fix s eq δ tri fx with expandSub (ss (res s))
... | nothing = ⊥just eq
... | just (Ψ' , δₑ) with subsList (ss (res s [ δₑ ]ᴿ)) | etsDec (ts (res s [ δₑ ]ᴿ))
...   | nothing | _       = ⊥just eq
...   | just _  | nothing = ⊥just eq
...   | just e  | just t with eq
...     | refl = Fixing-trans δₑ δ tri fx

-- Closing a scope re-expands its residual first: every instance
-- entering it is kept

reexpand-Princ⇑ : ∀ {Θ} {s : St Θ} {s'' : St (Θ +e)} {m : ⇑ᵉˢ s ⟶ s''} {C : Constraint (Θ +e)}
                → Princ⇑ s s'' m C
                → ∀ {s₃ : St (Θ +e)} {m₃ : s'' ⟶ s₃} → reexpand s'' ≡ just (s₃ , m₃)
                → Princ⇑ s s₃ (⟶-⨟ m m₃) C
reexpand-Princ⇑ {s'' = s''} {m} ip {m₃ = m₃} e δ₀ sat h =
  δ₂ , ≐ˢ-trans (⨟-assoc (mδ m) (mδ m₃) δ₂) (≐ˢ-trans (⨟-congʳ (mδ m) tri₂) tri₁) ,
  h₂ , (λ fx → reexpand-fix s'' e δ₂ tri₂ (fx₁ fx))
  where
    f₁   = ip δ₀ sat h
    δ₁   = proj₁ f₁
    tri₁ = proj₁ (proj₂ f₁)
    h₁   = proj₁ (proj₂ (proj₂ f₁))
    fx₁  = proj₂ (proj₂ (proj₂ f₁))

    f₂   = reexpand-princ s'' e δ₁ ∅ᴴ h₁
    δ₂   = proj₁ f₂
    tri₂ = proj₁ (proj₂ f₂)
    h₂   = proj₂ (proj₂ f₂)

-- An eternality demand and a var-rule disjunction, decided when pushed

solveEt-princ : ∀ {Θ} → (s : St Θ) → (A : OVType Θ)
              → (x : Maybe (List (TyVar (Ψ s)))) → (e : etDec (A [ θ s ]ᵛ) ≡ x)
              → {s' : St Θ} {m : s ⟶ s'} {w : Wit s' (Etᶜ A)}
              → solveEt s A x e ≡ solved (s' , m , w) → Princ s s' m (Etᶜ A)
solveEt-princ s A nothing   e ()
solveEt-princ s A (just αs) e refl δ₀ sat h =
  δ₀ , ≐ˢ-refl ,
  pushᵗ-⊩ (etDec-compl (A [ θ s ]ᵛ) e δ₀ (subst (∅ᴴ ⊩ᴱ_) (sym ([⨟]ᵛ A (θ s) δ₀)) sat)) h ,
  (λ fx → fx)

solveEt-fail : ∀ {Θ} → (s : St Θ) → (A : OVType Θ)
             → (x : Maybe (List (TyVar (Ψ s)))) → (e : etDec (A [ θ s ]ᵛ) ≡ x)
             → solveEt s A x e ≡ refuted → Refut s (Etᶜ A)
solveEt-fail s A nothing  e eq δ₀ fx h sat =
  etDec-refute (A [ θ s ]ᵛ) e δ₀ (subst (∅ᴴ ⊩ᴱ_) (sym ([⨟]ᵛ A (θ s) δ₀)) sat)
solveEt-fail s A (just _) e ()

solveDisj-princ : ∀ {Θ} → (s : St Θ) → (A : OVType Θ) → (ρ : RExp Θ)
                → (x : Maybe (List (TyVar (Ψ s)))) → (e : etDec (A [ θ s ]ᵛ) ≡ x)
                → {s' : St Θ} {m : s ⟶ s'} {w : Wit s' (Et∨≾ᵘ A ρ)}
                → solveDisj s A ρ x e ≡ solved (s' , m , w) → Princ s s' m (Et∨≾ᵘ A ρ)
solveDisj-princ s A ρ nothing        e refl δ₀ sat h =
  δ₀ , ≐ˢ-refl ,
  pushʳ-⊩ (etDec-grade (A [ θ s ]ᵛ) e δ₀
             (subst₂ (VarOK ∅ᴴ) (sym ([⨟]ᵛ A (θ s) δ₀)) (sym ([⨟]ʳ ρ (θ s) δ₀)) sat)) h ,
  (λ fx → fx)
solveDisj-princ s A ρ (just [])      e refl δ₀ sat h = δ₀ , ≐ˢ-refl , h , (λ fx → fx)
solveDisj-princ s A ρ (just (_ ∷ _)) e refl δ₀ sat h =
  δ₀ , ≐ˢ-refl ,
  pushᵈ-⊩ (subst₂ (VarOK ∅ᴴ) (sym ([⨟]ᵛ A (θ s) δ₀)) (sym ([⨟]ʳ ρ (θ s) δ₀)) sat) h ,
  (λ fx → fx)

solveDisj-fail : ∀ {Θ} → (s : St Θ) → (A : OVType Θ) → (ρ : RExp Θ)
               → (x : Maybe (List (TyVar (Ψ s)))) → (e : etDec (A [ θ s ]ᵛ) ≡ x)
               → solveDisj s A ρ x e ≡ refuted → Refut s (Et∨≾ᵘ A ρ)
solveDisj-fail s A ρ nothing        e ()
solveDisj-fail s A ρ (just [])      e ()
solveDisj-fail s A ρ (just (_ ∷ _)) e ()

solve-principal : ∀ {Θ} → (s : St Θ) → (C : Constraint Θ)
                → {s' : St Θ} {m : s ⟶ s'} {w : Wit s' C}
                → solve s C ≡ solved (s' , m , w)
                → Princ s s' m C

solve-principal s ⊤̂ refl δ₀ sat h = δ₀ , ≐ˢ-refl , h , (λ fx → fx)

solve-principal s ⊥̂ ()

solve-principal s (C ∧̂ D) eq δ₀ (sc , sd) h with solve s C in e₁
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (s₁ , m₁ , w₁) with solve s₁ D in e₂
...   | refuted = ⊥refuted eq
...   | stuck   = ⊥stuck eq
...   | solved (s₂ , m₂ , w₂) with eq
...     | refl = δ₂ ,
                 ≐ˢ-trans (⨟-assoc (mδ m₁) (mδ m₂) δ₂)
                          (≐ˢ-trans (⨟-congʳ (mδ m₁) tri₂) tri₁) ,
                 h₂ , (λ fx → fx₂ (fx₁ fx))
  where
    f₁  = solve-principal s C e₁ δ₀ sc h
    δ₁  = proj₁ f₁
    tri₁ = proj₁ (proj₂ f₁)
    h₁  = proj₁ (proj₂ (proj₂ f₁))
    fx₁ = proj₂ (proj₂ (proj₂ f₁))

    chain = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₁)) δ₁)
            (≐ˢ-trans (⨟-assoc (θ s) (mδ m₁) δ₁) (⨟-congʳ (θ s) tri₁))

    f₂  = solve-principal s₁ D e₂ δ₁ (⊨-resp-≐ˢ (≐ˢ-sym chain) D sd) h₁
    δ₂  = proj₁ f₂
    tri₂ = proj₁ (proj₂ f₂)
    h₂  = proj₁ (proj₂ (proj₂ f₂))
    fx₂ = proj₂ (proj₂ (proj₂ f₂))

solve-principal s (A ≾̂ᵥᶜ B) eq δ₀ sat h
  with expandSub ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) in eqx
... | nothing = ⊥refuted eq
... | just (Ψ' , δₑ) with subDec (A [ θ s ]ᵛ [ δₑ ]ᵛ) (B [ θ s ]ᵛ [ δₑ ]ᵛ)
...   | nothing = ⊥refuted eq
...   | just d with subsList (ss (res s [ δₑ ]ᴿ)) | etsDec (ts (res s [ δₑ ]ᴿ))
...     | nothing | _       = ⊥refuted eq
...     | just _  | nothing = ⊥refuted eq
...     | just e  | just t with eq
...       | refl = δ , trix ,
                 ∪ᴿ-both (atomiseᴿ-compl _ e t (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym trix) h)))
                         (atomsᴿ-⊩ (atomsOf d)
                           (elim d δ (subst₂ (∅ᴴ ∣_<:̂ᵛ_) (sym (inst A)) (sym (inst B))
                                             sat))) ,
                 (λ fx → Fixing-trans δₑ δ trix fx)
  where
    dem : ∀ {X Y} → (X , Y) ∈ ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s))
        → ∅ᴴ ∣ X [ δ₀ ]ᵛ <:̂ᵛ Y [ δ₀ ]ᵛ
    dem (here refl) = subst₂ (∅ᴴ ∣_<:̂ᵛ_) (sym ([⨟]ᵛ A (θ s) δ₀))
                                        (sym ([⨟]ᵛ B (θ s) δ₀)) sat
    dem (there m)   = ⊩ss h m

    facx = subst (ExpMax δ₀) eqx
                 (expandSub-max ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) δ₀ dem)
    δ    = proj₁ facx
    trix = proj₂ facx

    inst : (X : OVType _) → X [ θ s ]ᵛ [ δₑ ]ᵛ [ δ ]ᵛ ≡ X [ θ s ⨟ˢ δ₀ ]ᵛ
    inst X = trans (chain₂ᵛ X (θ s) δₑ δ)
                   ([≐]ᵛ (≐ˢ-trans (⨟-assoc (θ s) δₑ δ) (⨟-congʳ (θ s) trix)) X)

solve-principal s (ρ ≾̂ᵣᶜ ρ') refl δ₀ sat h =
  δ₀ , ≐ˢ-refl ,
  pushʳ-⊩ (subst₂ (λ x y → ∅ᴴ ⊩ x ≾̂ᵣ y)
                  (sym ([⨟]ʳ ρ (θ s) δ₀)) (sym ([⨟]ʳ ρ' (θ s) δ₀)) sat) h ,
  (λ fx → fx)

solve-principal s (ε ≾̂ₑᶜ ε') refl δ₀ sat h =
  δ₀ , ≐ˢ-refl ,
  pushᵉ-⊩ (subst₂ (λ x y → ∅ᴴ ⊩ x ≾̂ₑ y)
                  (sym ([⨟]ᵉ ε (θ s) δ₀)) (sym ([⨟]ᵉ ε' (θ s) δ₀)) sat) h ,
  (λ fx → fx)

solve-principal s (Etᶜ A) eq = solveEt-princ s A _ refl eq

solve-principal s (Et∨≾ᵘ A ρ) eq
  with decideᵣ derive ∅ᴴ (ρ [ θ s ]ʳ) ûᵣ
... | just p  with eq
...   | refl = λ δ₀ sat h → δ₀ , ≐ˢ-refl , h , (λ fx → fx)
solve-principal s (Et∨≾ᵘ A ρ) eq | nothing = solveDisj-princ s A ρ _ refl eq

solve-principal s (∃ᵗ C) eq δ₀ (B , sat) h with solve (s ↑ᵗˢ) C in e
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (s'' , m'' , w'') with eq
...   | refl = δ'' ,
               ≐ˢ-trans (⨟-assoc wkˢᵗ (mδ m'') δ'')
                        (≐ˢ-trans (⨟-congʳ wkˢᵗ tri'') (wk-,ᵗ δ₀ B)) ,
               h'' , (λ fx → fx'' (Fixing-trans wkˢᵗ (δ₀ ,ᵗ B) (wk-,ᵗ δ₀ B) fx))
  where
    ih = solve-principal (s ↑ᵗˢ) C e (δ₀ ,ᵗ B)
           (⊨-resp-≐ˢ (≐ˢ-sym (↑-,ᵗˢ (θ s) δ₀ B)) C sat)
           (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ᵗ δ₀ B)) h))
    δ''   = proj₁ ih
    tri'' = proj₁ (proj₂ ih)
    h''   = proj₁ (proj₂ (proj₂ ih))
    fx''  = proj₂ (proj₂ (proj₂ ih))

solve-principal s (∃ʳ C) eq δ₀ (ρ , sat) h with solve (s ↑ʳˢ) C in e
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (s'' , m'' , w'') with eq
...   | refl = δ'' ,
               ≐ˢ-trans (⨟-assoc wkˢʳ (mδ m'') δ'')
                        (≐ˢ-trans (⨟-congʳ wkˢʳ tri'') (wk-,ʳ δ₀ ρ)) ,
               h'' , (λ fx → fx'' (Fixing-trans wkˢʳ (δ₀ ,ʳ ρ) (wk-,ʳ δ₀ ρ) fx))
  where
    ih = solve-principal (s ↑ʳˢ) C e (δ₀ ,ʳ ρ)
           (⊨-resp-≐ˢ (≐ˢ-sym (↑-,ʳˢ (θ s) δ₀ ρ)) C sat)
           (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ʳ δ₀ ρ)) h))
    δ''   = proj₁ ih
    tri'' = proj₁ (proj₂ ih)
    h''   = proj₁ (proj₂ (proj₂ ih))
    fx''  = proj₂ (proj₂ (proj₂ ih))

solve-principal s (∃ᵉ C) eq δ₀ (ε , sat) h with solve (s ↑ᵉˢ) C in e
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (s'' , m'' , w'') with eq
...   | refl = δ'' ,
               ≐ˢ-trans (⨟-assoc wkˢᵉ (mδ m'') δ'')
                        (≐ˢ-trans (⨟-congʳ wkˢᵉ tri'') (wk-,ᵉ δ₀ ε)) ,
               h'' , (λ fx → fx'' (Fixing-trans wkˢᵉ (δ₀ ,ᵉ ε) (wk-,ᵉ δ₀ ε) fx))
  where
    ih = solve-principal (s ↑ᵉˢ) C e (δ₀ ,ᵉ ε)
           (⊨-resp-≐ˢ (≐ˢ-sym (↑-,ᵉˢ (θ s) δ₀ ε)) C sat)
           (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ᵉ δ₀ ε)) h))
    δ''   = proj₁ ih
    tri'' = proj₁ (proj₂ ih)
    h''   = proj₁ (proj₂ (proj₂ ih))
    fx''  = proj₂ (proj₂ (proj₂ ih))

solve-principal s (∀ᵉ C) eq with solve (⇑ᵉˢ s) C in e
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (s'' , m'' , w'') with reexpand s'' in e₃
...   | nothing = ⊥refuted eq
...   | just (s₃ , m₃) =
      thenRetry-princ {C = ∀ᵉ C}
        (popᵉ s C (Ψ (proj₁ (localiseˢ s m₃'))) (θ (proj₁ (localiseˢ s m₃')))
                  (res (proj₁ (localiseˢ s m₃'))) (rig (proj₁ (localiseˢ s m₃')))
                  (⟶-⨟ m₃' (proj₂ (localiseˢ s m₃')))
                  (wit-mono (proj₂ (localiseˢ s m₃')) C (wit-mono m₃ C w'')))
        (popᵉ-princ s C (Ψ (proj₁ (localiseˢ s m₃'))) (θ (proj₁ (localiseˢ s m₃')))
                    (res (proj₁ (localiseˢ s m₃'))) (rig (proj₁ (localiseˢ s m₃')))
                    (⟶-⨟ m₃' (proj₂ (localiseˢ s m₃')))
                    (wit-mono (proj₂ (localiseˢ s m₃')) C (wit-mono m₃ C w''))
                    (localise-princ {s = s} {s₃} {m₃'} {C}
                      (reexpand-Princ⇑ {s = s} {s''} {m''} {C}
                        (λ δ₀ → solve-principal (⇑ᵉˢ s) C e (δ₀ ↑ᵉ)) e₃))) eq
  where
    m₃' = ⟶-⨟ m'' m₃

solve-principal s (⋀ᵒᵖ f) eq
  with threadOps {f = f} (λ s' op → labelled {C = f op} op (solve s' (f op))) ops s in e
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (s₁ , m₁ , ws) with eq
...   | refl = threadOps-princ (λ s' op → labelled {C = f op} op (solve s' (f op)))
                               (λ s' op e' → labelled-princ op (solve s' (f op))
                                               (solve-principal s' (f op)) e') ops s e

-- Refutation, for every constraint: a refused constraint has no
-- solution at an instance that keeps the rigids distinct variables
-- and meets the residual. At a rigid binder, the refusals are an
-- escape, an outer unknown whose image keeps the rigid; an eternality
-- demand naming the rigid, eternal at no instance; and a failed
-- retry. The subtyping demands and the disjunctions that the scope
-- close meets cannot be refused: the first are pairs of type
-- variables, the second have types eternal at some instance, hence
-- free of the rigid.

popᵉ-escape : ∀ {Θ Φ} → (s : St Θ) → (C : Constraint (Θ +e))
            → (θ'' : Subst (Θ +e) (Φ +e)) → (R'' : Resid (Φ +e)) → (rg'' : Rig (Φ +e))
            → (m'' : ⇑ᵉˢ s ⟶ st (Φ +e) θ'' R'' rg'')
            → Princ⇑ s (st (Φ +e) θ'' R'' rg'') m'' C
            → (j : EVar (Φ +e)) → sE (mδ m'') (newᵉ {Ψ s}) ≡ evar j
            → strSub j (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') ≡ nothing
            → Refut s (∀ᵉ C)
popᵉ-escape s C θ'' R'' rg'' m'' ip j eqj eqstr δ₀ fx h sat =
  strSub-escape j (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') δ'' (bnd-var (mδ m'') δ'' tri'' eqj)
                δ₀ (bnd-out (mδ m'') δ'' δ₀ tri'') eqstr
  where
    ires = ip δ₀ (⊨-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉ (θ s) δ₀)) C sat) ⊩ᴿ-empty

    δ''   = proj₁ ires
    tri'' = proj₁ (proj₂ ires)

-- An eternality demand that `splitᴿ` refuses names the rigid, so its
-- type is eternal at no instance

atomᵗ-fail : ∀ {Φ Ψ''} → (j : EVar (Φ +e)) → (A : OVType (Φ +e)) → atomᵗ j A ≡ nothing
           → (δ : Subst (Φ +e) Ψ'') → ¬ (∅ᴴ ⊩ᴱ A [ δ ]ᵛ)
atomᵗ-fail {Φ} j A eq δ et with strᵛ⁺ j A in r
... | just _  = ⊥just (sym eq)
... | nothing = aux (etDec A) refl
  where
    aux : (x : Maybe (List (TyVar (Φ +e)))) → etDec A ≡ x → ⊥
    aux nothing   e = etDec-refute A e δ et
    aux (just αs) e = ⊥just (trans (sym r) (proj₂ (strᵛ⁺-just j A (proj₂ (etDec-str j A e)))))

listᵗ-fail : ∀ {Φ Ψ''} → (j : EVar (Φ +e)) → (l : List (OVType (Φ +e))) → listᵗ j l ≡ nothing
           → (δ : Subst (Φ +e) Ψ'') → (∀ {A} → A ∈ l → ∅ᴴ ⊩ᴱ A [ δ ]ᵛ) → ⊥
listᵗ-fail j []      () δ k
listᵗ-fail j (A ∷ l) eq δ k with atomᵗ j A in e₁ | listᵗ j l in e₂
... | just _  | just _  = ⊥just (sym eq)
... | just _  | nothing = listᵗ-fail j l e₂ δ (λ m → k (there m))
... | nothing | _       = atomᵗ-fail j A e₁ δ (k (here refl))

-- A pair of type variables is always kept

listˢ-fail : ∀ {Φ} → (j : EVar (Φ +e)) → (l : List (OVType (Φ +e) × OVType (Φ +e)))
           → Atomicˢ l → listˢ j l ≡ nothing → ⊥
listˢ-fail j []            at ()
listˢ-fail j ((A , B) ∷ l) at eq with at (here refl)
... | α , β , refl , refl with listˢ j l in e₂
...   | just _  = ⊥just (sym eq)
...   | nothing = listˢ-fail j l (λ m → at (there m)) e₂

-- A disjunction whose type is eternal at some instance is always kept

atomᵈ-ok : ∀ {Φ} → (j : EVar (Φ +e)) → (A : OVType (Φ +e)) → (ρ : RExp (Φ +e))
         → {αs : List (TyVar (Φ +e))} → etDec A ≡ just αs
         → Σ[ a ∈ Atomᵈ j A ρ ] (atomᵈ j A ρ ≡ just a)
atomᵈ-ok j A ρ e with strᵛ⁺ j A in r | strʳ⁺ j (ρ [ updᵉ j (econst ⊤ₑ) ]ʳ) in r'
... | just _  | just _  = _ , refl
... | just _  | nothing =
      ⊥just (trans (sym r') (proj₂ (strʳ⁺-just j _ (proj₂ (strʳ-upd j ⊤ₑ ρ)))))
... | nothing | _       = ⊥just (trans (sym r) (proj₂ (strᵛ⁺-just j A (proj₂ (etDec-str j A e)))))

listᵈ-fail : ∀ {Φ} → (j : EVar (Φ +e)) → (l : List (OVType (Φ +e) × RExp (Φ +e)))
           → (∀ {A ρ} → (A , ρ) ∈ l → Σ[ αs ∈ List (TyVar (Φ +e)) ] (etDec A ≡ just αs))
           → listᵈ j l ≡ nothing → ⊥
listᵈ-fail j []            et ()
listᵈ-fail j ((A , ρ) ∷ l) et eq with atomᵈ j A ρ in e₁ | listᵈ j l in e₂
... | just _  | just _  = ⊥just (sym eq)
... | just _  | nothing = listᵈ-fail j l (λ m → et (there m)) e₂
... | nothing | _       = ⊥just (trans (sym e₁) (proj₂ (atomᵈ-ok j A ρ (proj₂ (et (here refl))))))

-- `splitᴿ` refutes only where the residual is met at no instance

splitᴿ-fail : ∀ {Θ Φ Ψ''} → (O : Subst Θ (Φ +e)) → (O⁺ : Subst (Θ +e) (Φ +e))
            → (j : EVar (Φ +e)) → (R : Resid (Φ +e))
            → Atomicˢ (ss R)
            → (∀ {A ρ} → (A , ρ) ∈ ds R → Σ[ αs ∈ List (TyVar (Φ +e)) ] (etDec A ≡ just αs))
            → splitᴿ O O⁺ j R ≡ refuted
            → (δ : Subst (Φ +e) Ψ'') → ∅ᴴ ⊩ᴿ R [ δ ] → ⊥
splitᴿ-fail O O⁺ j R at et eq δ h
  with listᵗ j (ts R) in e₃ | listˢ j (ss R) in e₄ | listᵈ j (ds R) in e₅
     | listʳ O O⁺ j (rs R) | listᵉ O O⁺ j (es R) | outerD? O⁺ (dfs R)
... | just _  | just _  | just _  | just _  | just _  | just _  = ⊥solved eq
... | nothing | _       | _       | _       | _       | _       = listᵗ-fail j (ts R) e₃ δ (⊩ts h)
... | just _  | nothing | _       | _       | _       | _       = listˢ-fail j (ss R) at e₄
... | just _  | just _  | nothing | _       | _       | _       = listᵈ-fail j (ds R) et e₅
... | just _  | just _  | just _  | nothing | _       | _       = ⊥stuck-refuted eq
... | just _  | just _  | just _  | just _  | nothing | _       = ⊥stuck-refuted eq
... | just _  | just _  | just _  | just _  | just _  | nothing = ⊥stuck-refuted eq

-- A rigid's image is a variable wherever an instance exists

evar?-var : ∀ {Φ} → (ε : EExp Φ) → {j : EVar Φ} → ε ≡ evar j → evar? ε ≡ nothing → ⊥
evar?-var (evar j) refl ()

-- The rigid's image under an instance entering the scope

rigid-var : ∀ {Θ Ψ''} → (s : St Θ) → (C : Constraint (Θ +e)) → {s'' : St (Θ +e)}
          → (m'' : ⇑ᵉˢ s ⟶ s'') → Princ⇑ s s'' m'' C
          → (δ₀ : Subst (Ψ s) Ψ'') → (θ s ⨟ˢ δ₀) ⊨[ ∅ᴴ ] (∀ᵉ C)
          → Σ[ j ∈ EVar (Ψ s'') ] (sE (mδ m'') (newᵉ {Ψ s}) ≡ evar j)
rigid-var s C m'' ip δ₀ sat =
  varᵉ-inst (sE (mδ m'') (newᵉ {Ψ s})) (proj₁ ires) (≐ᵉ (proj₁ (proj₂ ires)) (newᵉ {Ψ s}))
  where
    ires = ip δ₀ (⊨-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉ (θ s) δ₀)) C sat) ⊩ᴿ-empty

-- Closing a scope refutes only where no instance entering it meets
-- what it leaves

popᵉ-fail : ∀ {Θ} → (s : St Θ) → (C : Constraint (Θ +e))
          → (Φ : Scope) → (θ'' : Subst (Θ +e) Φ) → (R'' : Resid Φ) → (rg'' : Rig Φ)
          → (m'' : ⇑ᵉˢ s ⟶ st Φ θ'' R'' rg'') → (w'' : Wit (st Φ θ'' R'' rg'') C)
          → Princ⇑ s (st Φ θ'' R'' rg'') m'' C
          → Atomicˢ (ss R'')
          → (∀ {A ρ} → (A , ρ) ∈ ds R'' → Σ[ αs ∈ List (TyVar Φ) ] (etDec A ≡ just αs))
          → popᵉ s C Φ θ'' R'' rg'' m'' w'' ≡ refuted
          → Refut s (∀ᵉ C)
popᵉ-fail s C (scope nt nr nzero) θ'' R'' rg'' m'' w'' ip at et eq δ₀ fx h sat
  with rigid-var s C m'' ip δ₀ sat
... | () , _
popᵉ-fail s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' ip at et eq δ₀ fx h sat
  with evar? (sE (mδ m'') (newᵉ {Ψ s})) in ev
... | nothing = evar?-var _ (proj₂ (rigid-var s C m'' ip δ₀ sat)) ev
... | just (j , eqj) with strSub j (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') in es
                        | splitᴿ (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') (mδ m'') j R'' in esp
...   | just _ | solved _ = ⊥solved eq
...   | just _ | stuck    = ⊥stuck-refuted eq
...   | just _ | refuted  =
        splitᴿ-fail (wkˢᵉ {Ψ s} ⨟ˢ mδ m'') (mδ m'') j R'' at et esp
                    (proj₁ ires) (proj₁ (proj₂ (proj₂ ires)))
  where
    ires = ip δ₀ (⊨-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉ (θ s) δ₀)) C sat) ⊩ᴿ-empty
...   | nothing | _       = popᵉ-escape s C θ'' R'' rg'' m'' ip j eqj es δ₀ fx h sat

-- A retry after a close refutes, and so does the close

thenRetry-fail : ∀ {Θ} {s : St Θ} {C : Constraint Θ}
               → (x : Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C)))
               → (∀ {s₁ : St Θ} {m₁ : s ⟶ s₁} {w₁ : Wit s₁ C}
                    → x ≡ solved (s₁ , m₁ , w₁) → Princ s s₁ m₁ C)
               → (x ≡ refuted → Refut s C)
               → thenRetry {C = C} x ≡ refuted → Refut s C
thenRetry-fail refuted p r eq = r refl
thenRetry-fail stuck   p r ()
thenRetry-fail {C = C} (solved (s₁ , m₁ , w₁)) p r eq δ₀ fx h sat with retry s₁ in e
... | just _  = ⊥solved eq
... | nothing = retry-fail s₁ e (proj₁ f₁) (proj₁ (proj₂ (proj₂ f₁)))
  where
    f₁ = p refl δ₀ sat h

threadOps-fail : ∀ {Θ} {f : Op → Constraint Θ}
   → (g : (s : St Θ) → (op : Op)
            → Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' (f op))))
   → ((s : St Θ) → (op : Op) → {s' : St Θ} {m : s ⟶ s'} {w : Wit s' (f op)}
        → g s op ≡ solved (s' , m , w) → Princ s s' m (f op))
   → ((s : St Θ) → (op : Op) → g s op ≡ refuted → Refut s (f op))
   → (l : List Op) → (s : St Θ)
   → threadOps {f = f} g l s ≡ refuted
   → Refut s (⋀ᵒᵖ f)
threadOps-fail g gp gf [] s ()
threadOps-fail {f = f} g gp gf (op ∷ l) s eq δ₀ fx h sat with g s op in e₁
... | refuted = gf s op e₁ δ₀ fx h (sat op)
... | stuck   = ⊥stuck-refuted eq
... | solved (s₁ , m₁ , w₁) with threadOps {f = f} g l s₁ in e₂
...   | solved _ = ⊥solved eq
...   | stuck    = ⊥stuck-refuted eq
...   | refuted  =
        threadOps-fail g gp gf l s₁ e₂ δ₁ fx₁ h₁
          (λ op' → ⊨-resp-≐ˢ (≐ˢ-sym chain) (f op') (sat op'))
  where
    f₁   = gp s op e₁ δ₀ (sat op) h
    δ₁   = proj₁ f₁
    tri₁ = proj₁ (proj₂ f₁)
    h₁   = proj₁ (proj₂ (proj₂ f₁))
    fx₁  = proj₂ (proj₂ (proj₂ f₁)) fx

    chain = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₁)) δ₁)
            (≐ˢ-trans (⨟-assoc (θ s) (mδ m₁) δ₁) (⨟-congʳ (θ s) tri₁))

-- After it, the subtyping demands of the residual are pairs of type
-- variables

reexpand-atomic : ∀ {Θ} → (s : St Θ) → {s' : St Θ} {m : s ⟶ s'}
                → reexpand s ≡ just (s' , m) → Atomicˢ (ss (res s'))
reexpand-atomic s eq with expandSub (ss (res s))
... | nothing = ⊥just eq
... | just (Ψ' , δₑ) with subsList (ss (res s [ δₑ ]ᴿ)) | etsDec (ts (res s [ δₑ ]ᴿ))
...   | nothing | _       = ⊥just eq
...   | just _  | nothing = ⊥just eq
...   | just e  | just t with eq
...     | refl = f
  where
    f : Atomicˢ (map (mapᵖ tvar) (asubᵥ (atomsOfˢ e)))
    f m with ∈-map⁻ (mapᵖ tvar) m
    ... | (α , β) , m₀ , refl = α , β , refl , refl

solve-fail : ∀ {Θ} → (s : St Θ) → (C : Constraint Θ)
           → solve s C ≡ refuted → Refut s C

solve-fail s ⊤̂ ()

solve-fail s ⊥̂ eq δ₀ fx h sat = sat

solve-fail s (C ∧̂ D) eq δ₀ fx h (sc , sd) with solve s C in e₁
... | refuted = solve-fail s C e₁ δ₀ fx h sc
... | stuck   = ⊥stuck-refuted eq
... | solved (s₁ , m₁ , w₁) with solve s₁ D in e₂
...   | solved _ = ⊥solved eq
...   | stuck    = ⊥stuck-refuted eq
...   | refuted  =
        solve-fail s₁ D e₂ δ₁ fx₁ h₁ (⊨-resp-≐ˢ (≐ˢ-sym chain) D sd)
  where
    f₁   = solve-principal s C e₁ δ₀ sc h
    δ₁   = proj₁ f₁
    tri₁ = proj₁ (proj₂ f₁)
    h₁   = proj₁ (proj₂ (proj₂ f₁))
    fx₁  = proj₂ (proj₂ (proj₂ f₁)) fx

    chain = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₁)) δ₁)
            (≐ˢ-trans (⨟-assoc (θ s) (mδ m₁) δ₁) (⨟-congʳ (θ s) tri₁))
solve-fail s (A ≾̂ᵥᶜ B) eq δ₀ fx h sat
  with expandSub ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) in eqx
... | nothing =
      subst (ExpMax δ₀) eqx
            (expandSub-max ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) δ₀ dem)
  where
    dem : ∀ {X Y} → (X , Y) ∈ ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s))
        → ∅ᴴ ∣ X [ δ₀ ]ᵛ <:̂ᵛ Y [ δ₀ ]ᵛ
    dem (here refl) = subst₂ (∅ᴴ ∣_<:̂ᵛ_) (sym ([⨟]ᵛ A (θ s) δ₀))
                                        (sym ([⨟]ᵛ B (θ s) δ₀)) sat
    dem (there m)   = ⊩ss h m
... | just (Ψ' , δₑ)
      with subDec (A [ θ s ]ᵛ [ δₑ ]ᵛ) (B [ θ s ]ᵛ [ δₑ ]ᵛ) in eqd
...     | nothing =
          ⊥nothing (trans (sym (proj₂ (dec (here refl)))) eqd)
  where
    dec = subst (ExpDec ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s))) eqx
                (expandSub-dec ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)))
...     | just _ with subsList (ss (res s [ δₑ ]ᴿ)) in eqs | etsDec (ts (res s [ δₑ ]ᴿ)) in eqt
...       | just _  | just _  = ⊥solved eq
...       | just _  | nothing =
            etsDec-refute (ts (res s [ δₑ ]ᴿ)) eqt δ
              (⊩ts (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym trix) h)))
  where
    dem : ∀ {X Y} → (X , Y) ∈ ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s))
        → ∅ᴴ ∣ X [ δ₀ ]ᵛ <:̂ᵛ Y [ δ₀ ]ᵛ
    dem (here refl) = subst₂ (∅ᴴ ∣_<:̂ᵛ_) (sym ([⨟]ᵛ A (θ s) δ₀))
                                        (sym ([⨟]ᵛ B (θ s) δ₀)) sat
    dem (there m)   = ⊩ss h m

    facx = subst (ExpMax δ₀) eqx
                 (expandSub-max ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) δ₀ dem)
    δ    = proj₁ facx
    trix = proj₂ facx
...       | nothing | _       = subsList-exp (ss (res s)) δₑ (λ m → dec (there m)) eqs
  where
    dec = subst (ExpDec ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s))) eqx
                (expandSub-dec ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)))

solve-fail s (ρ ≾̂ᵣᶜ ρ') ()

solve-fail s (ε ≾̂ₑᶜ ε') ()

solve-fail s (Etᶜ A) eq = solveEt-fail s A _ refl eq

solve-fail s (Et∨≾ᵘ A ρ) eq with decideᵣ derive ∅ᴴ (ρ [ θ s ]ʳ) ûᵣ
... | just _  = ⊥solved eq
... | nothing = solveDisj-fail s A ρ _ refl eq

solve-fail s (∃ᵗ C) eq δ₀ fx h (B , sat) with solve (s ↑ᵗˢ) C in e
... | solved _ = ⊥solved eq
... | stuck    = ⊥stuck-refuted eq
... | refuted  =
      solve-fail (s ↑ᵗˢ) C e (δ₀ ,ᵗ B)
        (Fixing-trans wkˢᵗ (δ₀ ,ᵗ B) (wk-,ᵗ δ₀ B) fx)
        (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ᵗ δ₀ B)) h))
        (⊨-resp-≐ˢ (≐ˢ-sym (↑-,ᵗˢ (θ s) δ₀ B)) C sat)

solve-fail s (∃ʳ C) eq δ₀ fx h (ρ , sat) with solve (s ↑ʳˢ) C in e
... | solved _ = ⊥solved eq
... | stuck    = ⊥stuck-refuted eq
... | refuted  =
      solve-fail (s ↑ʳˢ) C e (δ₀ ,ʳ ρ)
        (Fixing-trans wkˢʳ (δ₀ ,ʳ ρ) (wk-,ʳ δ₀ ρ) fx)
        (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ʳ δ₀ ρ)) h))
        (⊨-resp-≐ˢ (≐ˢ-sym (↑-,ʳˢ (θ s) δ₀ ρ)) C sat)

solve-fail s (∃ᵉ C) eq δ₀ fx h (ε , sat) with solve (s ↑ᵉˢ) C in e
... | solved _ = ⊥solved eq
... | stuck    = ⊥stuck-refuted eq
... | refuted  =
      solve-fail (s ↑ᵉˢ) C e (δ₀ ,ᵉ ε)
        (Fixing-trans wkˢᵉ (δ₀ ,ᵉ ε) (wk-,ᵉ δ₀ ε) fx)
        (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wk-,ᵉ δ₀ ε)) h))
        (⊨-resp-≐ˢ (≐ˢ-sym (↑-,ᵉˢ (θ s) δ₀ ε)) C sat)

-- At a rigid binder: the inner refutation at the instance lifted over a
-- fresh eigenvariable, the re-expansion's at the inner instance, and
-- the close's and the retry's

solve-fail s (∀ᵉ C) eq δ₀ fx h sat with solve (⇑ᵉˢ s) C in e
... | refuted = solve-fail (⇑ᵉˢ s) C e (δ₀ ↑ᵉ) (Fixing-⇑ᵉ δ₀ fx) ⊩ᴿ-empty sat'
  where
    sat' = ⊨-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉ (θ s) δ₀)) C sat
... | stuck   = ⊥stuck-refuted eq
... | solved (s'' , m'' , w'') with reexpand s'' in e₃
...   | nothing = reexpand-fail s'' e₃ (proj₁ ires) ∅ᴴ (proj₁ (proj₂ (proj₂ ires)))
  where
    ires = solve-principal (⇑ᵉˢ s) C e (δ₀ ↑ᵉ)
             (⊨-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉ (θ s) δ₀)) C sat) ⊩ᴿ-empty
...   | just (s₃ , m₃) =
      thenRetry-fail {C = ∀ᵉ C}
        (popᵉ s C (Ψ sL) (θ sL) (res sL) (rig sL) mL wL)
        (popᵉ-princ s C (Ψ sL) (θ sL) (res sL) (rig sL) mL wL ipL)
        (popᵉ-fail s C (Ψ sL) (θ sL) (res sL) (rig sL) mL wL ipL
          (latom (localise (mδ m₃') (res s₃)) (reexpand-atomic s'' e₃))
          (localise-ds (mδ m₃') (res s₃)))
        eq δ₀ fx h sat
  where
    m₃' = ⟶-⨟ m'' m₃
    sL  = proj₁ (localiseˢ s m₃')
    mL  = ⟶-⨟ m₃' (proj₂ (localiseˢ s m₃'))
    wL  = wit-mono (proj₂ (localiseˢ s m₃')) C (wit-mono m₃ C w'')
    ipL = localise-princ {s = s} {s₃} {m₃'} {C}
            (reexpand-Princ⇑ {s = s} {s''} {m''} {C}
              (λ δ₀ → solve-principal (⇑ᵉˢ s) C e (δ₀ ↑ᵉ)) e₃)

solve-fail s (⋀ᵒᵖ f) eq
  with threadOps {f = f} (λ s' op → labelled {C = f op} op (solve s' (f op))) ops s in e
... | solved _ = ⊥solved eq
... | stuck    = ⊥stuck-refuted eq
... | refuted  =
      threadOps-fail (λ s' op → labelled {C = f op} op (solve s' (f op)))
                     (λ s' op e' → labelled-princ op (solve s' (f op))
                                     (solve-principal s' (f op)) e')
                     (λ s' op e' → solve-fail s' (f op)
                                     (labelled-refuted op (solve s' (f op)) e')) ops s e

-- After it, every subtyping demand of the residual decomposes

reexpand-dec : ∀ {Θ} → (s : St Θ) → {s' : St Θ} {m : s ⟶ s'}
             → reexpand s ≡ just (s' , m)
             → ∀ {A B} → (A , B) ∈ ss (res s') → Σ[ d ∈ SubDec A B ] (subDec A B ≡ just d)
reexpand-dec s eq with expandSub (ss (res s))
... | nothing = ⊥just eq
... | just (Ψ' , δₑ) with subsList (ss (res s [ δₑ ]ᴿ)) | etsDec (ts (res s [ δₑ ]ᴿ))
...   | nothing | _       = ⊥just eq
...   | just _  | nothing = ⊥just eq
...   | just e  | just t with eq
...     | refl = f
  where
    f : ∀ {A B} → (A , B) ∈ map (mapᵖ tvar) (asubᵥ (atomsOfˢ e))
      → Σ[ d ∈ SubDec A B ] (subDec A B ≡ just d)
    f m with ∈-map⁻ (mapᵖ tvar) m
    ... | (α , β) , m₀ , refl = _ , refl
