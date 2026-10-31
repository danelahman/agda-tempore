------------------------------------------------------------------
-- Principality and refutation for the driver                   --
--                                                              --
-- `Princ s s' m C`: every instance of `s` solving `C` from no  --
-- hypotheses and discharging the residual of `s` factors       --
-- through `m` into one discharging the residual of `s'`,       --
-- rigids staying fixed. `Refut s C`: no rigid-fixing instance  --
-- discharging the residual of `s` solves `C`.                  --
-- `solve-principal` and `solve-fail` prove them for `solve`    --
-- from the same facts for each stage (`solveEt-princ`,         --
-- `solveDisj-princ`, `reexpand-princ`, `localise-princ`,       --
-- `splitᴿ-princ`, `popᵉ-princ`, `retry-princ`, and their       --
-- `-fail` and `-escape` counterparts).                         --
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
open import Data.Maybe using (Is-just; to-witness)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base using (ℕ) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Grades.Base
open import Grades.Hints using (SystemHints; module SystemHintsInterface)
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.Outcome

open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Inference.SolverImpl.Principal
  (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S))
  (opEnum : OpEnum S)
  where

open LanguageSpec S
open GradeSystemInterface Grades
open SystemHintsInterface hints
open Operations Ops

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses               S

open import PolymorphicCalculus.Inference.Constraints.Syntax       S
open import PolymorphicCalculus.Inference.Constraints.Satisfaction S
open import PolymorphicCalculus.Inference.Constraints.Properties   S using (⊨-resp-≐ˢ)


open import PolymorphicCalculus.Inference.SolverImpl.Enum S using (AllOp; all-lookup)

open import PolymorphicCalculus.Inference.SolverImpl.Core.Rigid S
  using (strʳ⁺; strᵉ⁺; strᵛ⁺; popˢ; popˢ-hit; strSub; unpopˢ; pop-unpop; strSub-escape;
         strᵛ⁺-just; strʳ⁺-just; strʳ-upd; ∨-true; ∨-left; ∨-right; dec-true; true-dec)

open import PolymorphicCalculus.Inference.SolverImpl.Core.Decorate S using (expandSub)

open import PolymorphicCalculus.Inference.SolverImpl.Expand S
  using (ExpMax; ExpDec; expandSub-max; expandSub-dec)

open import PolymorphicCalculus.Inference.SolverImpl.Deferred S hints
open import PolymorphicCalculus.Inference.SolverImpl.Resid  S
open import PolymorphicCalculus.Inference.SolverImpl.State  S
open import PolymorphicCalculus.Inference.SolverImpl.Normal S hints
open import PolymorphicCalculus.Inference.SolverImpl.Entail S hints using (decideᵣ; decideₑ; full)
open import PolymorphicCalculus.Inference.SolverImpl.Solve  S hints opEnum
open import PolymorphicCalculus.Inference.SolverImpl.Localise S hints
  using (Localised; localise; lσ; lfix; lcpl; latom; localise-ds; updᵉ-absorb; freeᵉ; freeʳ; anyᶠ; anyᶠ-true;
         outerₑ?; outerᵣ?; Outerₑ; Outerᵣ; κᵉ; κ⊤; ⊩ᴴ-κᵉ; κᵉ≾κ⊤;
         Agree; agreeₑ; agreeᵣ; agree-out; evar?)
open import PolymorphicCalculus.Inference.SolverImpl.Core.Occurs S
  using (occᵉ-e; occᵉ-r; occᵉ-v; occᵉ-c; occʳ-r; occʳ-v; occʳ-c)

open OpEnum opEnum

⊥just : ∀ {X Y : Set} {x : X} → nothing ≡ just x → Y
⊥just ()

⊥nothing : ∀ {X Y : Set} {x : X} → just x ≡ nothing → Y
⊥nothing ()

-- A weakening is undone by an extension

wk-,ᵗ : ∀ {Ω Ω'} → (δ : Subst Ω Ω') → (B : OVType Ω') → (wkˢᵗ ⨟ˢ (δ ,ᵗ B)) ≐ˢ δ
wk-,ᵗ δ B = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

wk-,ʳ : ∀ {Ω Ω'} → (δ : Subst Ω Ω') → (ρ : RExp Ω') → (wkˢʳ ⨟ˢ (δ ,ʳ ρ)) ≐ˢ δ
wk-,ʳ δ ρ = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

wk-,ᵉ : ∀ {Ω Ω'} → (δ : Subst Ω Ω') → (ε : EExp Ω') → (wkˢᵉ ⨟ˢ (δ ,ᵉ ε)) ≐ˢ δ
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

-- A substitution is uniform on the unknowns `O` mentions when each image reads
-- the same with the eigenvariable at the unit as at the top; the outer images
-- are weakenings, so it is (`uniform-out`)

Uniform : ∀ {Θ Φ Ω} → Subst Θ Φ → Subst Φ (Ω +e) → Set
Uniform O X = Agree O X κ⊤ κᵉ

uniform-out : ∀ {Θ Φ Ω} → (O : Subst Θ Φ) → (X : Subst Φ (Ω +e)) → (δ₀ : Subst Θ Ω)
            → (O ⨟ˢ X) ≐ˢ (δ₀ ⨟ˢ wkˢᵉ) → Uniform O X
uniform-out O X δ₀ =
  agree-out O X κ⊤ κᵉ wkˢᵉ δ₀
    (λ y → trans (κ-wkᵛ (econst ⊤ₑ) y) (sym (κ-wkᵛ 𝟏̂ₑ y)))
    (λ y → trans (κ-wkʳ (econst ⊤ₑ) y) (sym (κ-wkʳ 𝟏̂ₑ y)))
    (λ y → trans (κ-wkᵉ (econst ⊤ₑ) y) (sym (κ-wkᵉ 𝟏̂ₑ y)))

-- Both components of a union

∪ᴿ-both : ∀ {Ω Ω'} {Q : Hyps Ω'} {R R' : Resid Ω} {δ : Subst Ω Ω'}
        → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ R' [ δ ] → Q ⊩ᴿ (R ∪ᴿ R') [ δ ]
∪ᴿ-both {R = R} h h' =
  mk⊩ᴿ (λ m → [ ⊩rs h , ⊩rs h' ]′ (∈-++⁻ (rs R) m))
       (λ m → [ ⊩es h , ⊩es h' ]′ (∈-++⁻ (es R) m))
       (λ m → [ ⊩ts h , ⊩ts h' ]′ (∈-++⁻ (ts R) m))
       (λ m → [ ⊩ss h , ⊩ss h' ]′ (∈-++⁻ (ss R) m))
       (λ m → [ ⊩ds h , ⊩ds h' ]′ (∈-++⁻ (ds R) m))
       (λ m → [ ⊩dfs h , ⊩dfs h' ]′ (∈-++⁻ (dfs R) m))

-- Pushing one atom

pushʳ-⊩ : ∀ {Ω Ω'} {Q : Hyps Ω'} {R : Resid Ω} {ρ ρ' : RExp Ω} {δ : Subst Ω Ω'}
        → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushʳ ρ ρ' R) [ δ ]
pushʳ-⊩ p h =
  mk⊩ᴿ (λ { (here refl) → p ; (there m) → ⊩rs h m })
       (⊩es h) (⊩ts h) (⊩ss h) (⊩ds h) (⊩dfs h)

pushᵉ-⊩ : ∀ {Ω Ω'} {Q : Hyps Ω'} {R : Resid Ω} {ε ε' : EExp Ω} {δ : Subst Ω Ω'}
        → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushᵉ ε ε' R) [ δ ]
pushᵉ-⊩ p h =
  mk⊩ᴿ (⊩rs h) (λ { (here refl) → p ; (there m) → ⊩es h m })
       (⊩ts h) (⊩ss h) (⊩ds h) (⊩dfs h)

pushᵗ-⊩ : ∀ {Ω Ω'} {Q : Hyps Ω'} {R : Resid Ω} {αs : List (TyVar Ω)} {δ : Subst Ω Ω'}
        → (∀ {α} → α ∈ αs → Q ⊩Et tvar α [ δ ]ᵛ) → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushᵗ αs R) [ δ ]
pushᵗ-⊩ {Q = Q} {R = R} {αs = αs} {δ = δ} p h =
  mk⊩ᴿ (⊩rs h) (⊩es h) ts' (⊩ss h) (⊩ds h) (⊩dfs h)
  where
    ts' : ∀ {A} → A ∈ ts (pushᵗ αs R) → Q ⊩Et A [ δ ]ᵛ
    ts' m with ∈-++⁻ (map tvar αs) m
    ... | inj₂ m' = ⊩ts h m'
    ... | inj₁ m' with ∈-map⁻ tvar m'
    ...   | α , m₀ , refl = p m₀

pushᵈ-⊩ : ∀ {Ω Ω'} {Q : Hyps Ω'} {R : Resid Ω} {A : OVType Ω} {ρ : RExp Ω}
            {δ : Subst Ω Ω'}
        → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ) → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (pushᵈ A ρ R) [ δ ]
pushᵈ-⊩ p h =
  mk⊩ᴿ (⊩rs h) (⊩es h) (⊩ts h) (⊩ss h)
       (λ { (here refl) → p ; (there m) → ⊩ds h m }) (⊩dfs h)

evar-inj : ∀ {Θ} {i j : EVar Θ} → evar {Θ} i ≡ evar j → i ≡ j
evar-inj refl = refl

varᵉ?-just : ∀ {Ω} → (ε : EExp Ω) → {k : EVar Ω} → varᵉ? ε ≡ just k → ε ≡ evar k
varᵉ?-just (evar i)   refl = refl
varᵉ?-just (econst c) ()
varᵉ?-just (ε ·̂ₑ ε')  ()

∈-transRig : ∀ {Ω Ω₁} → (σ : Subst Ω Ω₁) → (rg : Rig Ω) → (k : EVar Ω₁)
           → k ∈ᶠ transRig σ rg ≡ true
           → Σ[ i ∈ EVar Ω ] ((i ∈ᶠ rg ≡ true) × (sE σ i ≡ evar k))
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

Fixing-trans : ∀ {Ω Ω₁ Ω''} {rg : Rig Ω} → (σ : Subst Ω Ω₁) → (δ : Subst Ω₁ Ω'')
             → {δ₀ : Subst Ω Ω''} → (σ ⨟ˢ δ) ≐ˢ δ₀ → Fixing rg δ₀
             → Fixing (transRig σ rg) δ
Fixing-trans {Ω} {Ω₁} {Ω''} {rg} σ δ {δ₀} p fx = fixing v n
  where
    v : (k : EVar Ω₁) → k ∈ᶠ transRig σ rg ≡ true
      → Σ[ j ∈ EVar Ω'' ] (sE δ k ≡ evar j)
    v k m with ∈-transRig σ rg k m
    ... | i , mi , r with fixᵉ fx i mi
    ...   | j , rj = j , trans (sym (cong (_[ δ ]ᵉ) r)) (trans (≐ᵉ p i) rj)

    n : (k k' : EVar Ω₁) → k ∈ᶠ transRig σ rg ≡ true → k' ∈ᶠ transRig σ rg ≡ true
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

∈-transRig⁺ : ∀ {Ω Ω₁} → (σ : Subst Ω Ω₁) → (rg : Rig Ω) → (i : EVar Ω)
            → i ∈ᶠ rg ≡ true → (k : EVar Ω₁) → sE σ i ≡ evar k
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

transRig-total : ∀ {Ω Ω₁} → (σ : Subst Ω Ω₁) → (rg : Rig Ω) → Fixing rg σ
               → (i : EVar Ω) → i ∈ᶠ rg ≡ true
               → Σ[ k ∈ EVar Ω₁ ] ((sE σ i ≡ evar k) × (k ∈ᶠ transRig σ rg ≡ true))
transRig-total σ rg fx i m with fixᵉ fx i m
... | k , rk = k , rk , ∈-transRig⁺ σ rg i m k rk

-- A rigid lift fixes the rigid it declares, by computation, and those it transports

Fixing-⇑ᵉ : ∀ {Ω Ω''} {rg : Rig Ω} → (δ₀ : Subst Ω Ω'')
          → Fixing rg δ₀ → Fixing (newᵉ {Ω} ∷ transRig (wkˢᵉ {Ω}) rg) (δ₀ ↑ᵉ)
Fixing-⇑ᵉ {Ω} {Ω''} {rg} δ₀ fx = fixing v n
  where
    im : (k : EVar (Ω +e)) → k ∈ᶠ transRig (wkˢᵉ {Ω}) rg ≡ true
       → Σ[ i ∈ EVar Ω ] Σ[ j ∈ EVar Ω'' ]
           ((i ∈ᶠ rg ≡ true) × (k ≡ suc i) × (sE δ₀ i ≡ evar j))
    im k m with ∈-transRig (wkˢᵉ {Ω}) rg k m
    ... | i , mi , ri with fixᵉ fx i mi
    ...   | j , rj = i , j , mi , sym (evar-inj ri) , rj

    cls : (k : EVar (Ω +e)) → k ∈ᶠ (newᵉ {Ω} ∷ transRig (wkˢᵉ {Ω}) rg) ≡ true
        → (k ≡ newᵉ {Ω})
          ⊎ (Σ[ i ∈ EVar Ω ] Σ[ j ∈ EVar Ω'' ]
               ((i ∈ᶠ rg ≡ true) × (k ≡ suc i) × (sE δ₀ i ≡ evar j)))
    cls k m with ∨-true ⌊ k ≟ᶠ newᵉ {Ω} ⌋ (k ∈ᶠ transRig (wkˢᵉ {Ω}) rg) m
    ... | inj₁ s = inj₁ (true-dec (k ≟ᶠ newᵉ {Ω}) s)
    ... | inj₂ s = inj₂ (im k s)

    v : (k : EVar (Ω +e)) → k ∈ᶠ (newᵉ {Ω} ∷ transRig (wkˢᵉ {Ω}) rg) ≡ true
      → Σ[ l ∈ EVar (Ω'' +e) ] (sE (δ₀ ↑ᵉ) k ≡ evar l)
    v k m with cls k m
    ... | inj₁ refl                     = newᵉ {Ω''} , refl
    ... | inj₂ (i , j , mi , refl , rj) = wkᵉ-ev Ω'' j , cong wkᵉ-e rj

    n : (k k' : EVar (Ω +e)) → k ∈ᶠ (newᵉ {Ω} ∷ transRig (wkˢᵉ {Ω}) rg) ≡ true
      → k' ∈ᶠ (newᵉ {Ω} ∷ transRig (wkˢᵉ {Ω}) rg) ≡ true
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

-- Principality and refutation concern the instances solving a constraint from
-- no hypotheses (`∅ᴴ`), where a var-rule disjunction is met by one of its sides

PrincAt : ∀ {Θ Ω''} → (s s' : St Θ) → s ⟶ s' → Constraint Θ → Subst (Ω s) Ω'' → Set
PrincAt {Ω'' = Ω''} s s' m C δ₀ =
  (θ s ⨟ˢ δ₀) ⊨[ ∅ᴴ ] C → ∅ᴴ ⊩ᴿ (res s) [ δ₀ ]
  → Σ[ δ ∈ Subst (Ω s') Ω'' ]
      (((mδ m ⨟ˢ δ) ≐ˢ δ₀)
        × (∅ᴴ ⊩ᴿ (res s') [ δ ])
        × (Fixing (rig s) δ₀ → Fixing (rig s') δ))

Princ : ∀ {Θ} → (s s' : St Θ) → s ⟶ s' → Constraint Θ → Set
Princ s s' m C = ∀ {Ω''} → (δ₀ : Subst (Ω s) Ω'') → PrincAt s s' m C δ₀

-- Principality for the instances entering a rigid scope: the rigid at
-- a fresh eigenvariable

Princ⇑ : ∀ {Θ} → (s : St Θ) → (s' : St (Θ +e)) → ⇑ᵉˢ s ⟶ s' → Constraint (Θ +e) → Set
Princ⇑ s s' m C = ∀ {Ω''} → (δ₀ : Subst (Ω s) Ω'') → PrincAt (⇑ᵉˢ s) s' m C (δ₀ ↑ᵉ)

Refut : ∀ {Θ} → St Θ → Constraint Θ → Set
Refut s C =
  ∀ {Ω''} → (δ₀ : Subst (Ω s) Ω'')
  → Fixing (rig s) δ₀ → ∅ᴴ ⊩ᴿ (res s) [ δ₀ ]
  → ¬ ((θ s ⨟ˢ δ₀) ⊨[ ∅ᴴ ] C)

-- Principality transported along an equation of solved outcomes, and that of
-- the identity

solved-inj : ∀ {A : Set} {a b : A} → solved a ≡ solved b → a ≡ b
solved-inj refl = refl

solved-princ : ∀ {Θ} {s : St Θ} {C : Constraint Θ} {s₁ s₂ : St Θ} {m₁ : s ⟶ s₁} {m₂ : s ⟶ s₂}
                 {w₁ : Wit s₁ C} {w₂ : Wit s₂ C}
             → solved {Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C)} (s₁ , m₁ , w₁) ≡ solved (s₂ , m₂ , w₂)
             → Princ s s₁ m₁ C → Princ s s₂ m₂ C
solved-princ {Θ} {s = s} {C} eq p =
  subst (λ (q : Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C)) → Princ s (proj₁ q) (proj₁ (proj₂ q)) C)
        (solved-inj eq) p

id-princ : ∀ {Θ} → (s : St Θ) → (C : Constraint Θ) → Princ s s ⟶-id C
id-princ s C δ₀ sat h = δ₀ , ≐ˢ-refl , h , (λ fx → fx)

-- An atom kept at the boundary is the strengthening of an inner one, its
-- instance the inner instance with the eigenvariable at the unit

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
     → wkᵉ-H Q ⊩Et A [ popˢ j ⨟ˢ γ ]ᵛ
     → Q ⊩Et A₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ
bndᵗ {Q = Q} j A {A₀} q γ p =
  subst (Q ⊩Et_) ([⨟]ᵛ A₀ (wkˢᵉ ⨟ˢ γ) κᵉ)
        (⊩Et-subst ⊩ᴴ-κᵉ (subst (wkᵉ-H Q ⊩Et_) (keyᵛ j A q γ) p))

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

-- The atoms a solved step keeps, read off its equation: none, or one

just-none : ∀ {X : Set} {P : List X → Set} {p : P []} {a : Σ[ l ∈ List X ] P l}
          → just ([] , p) ≡ just a → ∀ {y} → y ∈ proj₁ a → ⊥
just-none refl ()

just-one : ∀ {X : Set} {P : List X → Set} {x : X} {p : P (x ∷ [])} {a : Σ[ l ∈ List X ] P l}
         → (F : X → Set) → just (x ∷ [] , p) ≡ just a → F x → ∀ {y} → y ∈ proj₁ a → F y
just-one F refl f (here refl) = f

just-one₂ : ∀ {X Y : Set} {P : List (X × Y) → Set} {x : X} {y : Y} {p : P ((x , y) ∷ [])}
              {a : Σ[ l ∈ List (X × Y) ] P l}
          → (F : X → Y → Set) → just ((x , y) ∷ [] , p) ≡ just a → F x y
          → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a → F τ τ'
just-one₂ F refl f (here refl) = f

-- A stripped ordering. With the rigid on the right, its instance is the inner
-- one with the eigenvariable at the unit; with the rigid on the left, the inner
-- one with the eigenvariable at the top bounds it.

stripʳ-unit-bnd : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (ρ ρ' : RExp (Φ +e))
                → {ρ₀ ρ₀' : RExp Φ} → ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀
                → ρ' [ updᵉ j 𝟏̂ₑ ]ʳ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀'
                → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
                → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ
                → Q ⊩ ρ₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ ρ₀' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
stripʳ-unit-bnd {Q = Q} j ρ ρ' {ρ₀} {ρ₀'} e₁ e₂ γ hγ p =
  subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y)
         (trans (cong (_[ κᵉ ]ʳ) (keyʳ j ρ e₁ γ)) ([⨟]ʳ ρ₀ (wkˢᵉ ⨟ˢ γ) κᵉ)) rhs
         (⊩-substᵣ ⊩ᴴ-κᵉ p)
  where
    X = popˢ j ⨟ˢ γ

    j↦𝟏 : sE (X ⨟ˢ κᵉ) j ≡ 𝟏̂ₑ [ X ⨟ˢ κᵉ ]ᵉ
    j↦𝟏 = cong (_[ κᵉ ]ᵉ) (trans (cong (_[ γ ]ᵉ) (popˢ-hit j)) hγ)

    rhs : ρ' [ X ]ʳ [ κᵉ ]ʳ ≡ ρ₀' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
    rhs = trans ([⨟]ʳ ρ' X κᵉ)
          (trans (sym ([≐]ʳ (updᵉ-absorb j 𝟏̂ₑ (X ⨟ˢ κᵉ) j↦𝟏) ρ'))
          (trans (sym ([⨟]ʳ ρ' (updᵉ j 𝟏̂ₑ) (X ⨟ˢ κᵉ)))
          (trans (sym ([⨟]ʳ (ρ' [ updᵉ j 𝟏̂ₑ ]ʳ) X κᵉ))
          (trans (cong (_[ κᵉ ]ʳ) (keyʳ j (ρ' [ updᵉ j 𝟏̂ₑ ]ʳ) e₂ γ))
                 ([⨟]ʳ ρ₀' (wkˢᵉ ⨟ˢ γ) κᵉ)))))

stripᵉ-unit-bnd : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (ε ε' : EExp (Φ +e))
                → {ε₀ ε₀' : EExp Φ} → ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀
                → ε' [ updᵉ j 𝟏̂ₑ ]ᵉ [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀'
                → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
                → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ
                → Q ⊩ ε₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ ε₀' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
stripᵉ-unit-bnd {Q = Q} j ε ε' {ε₀} {ε₀'} e₁ e₂ γ hγ p =
  subst₂ (λ x y → Q ⊩ x ≾̂ₑ y)
         (trans (cong (_[ κᵉ ]ᵉ) (keyᵉ j ε e₁ γ)) ([⨟]ᵉ ε₀ (wkˢᵉ ⨟ˢ γ) κᵉ)) rhs
         (⊩-substₑ ⊩ᴴ-κᵉ p)
  where
    X = popˢ j ⨟ˢ γ

    j↦𝟏 : sE (X ⨟ˢ κᵉ) j ≡ 𝟏̂ₑ [ X ⨟ˢ κᵉ ]ᵉ
    j↦𝟏 = cong (_[ κᵉ ]ᵉ) (trans (cong (_[ γ ]ᵉ) (popˢ-hit j)) hγ)

    rhs : ε' [ X ]ᵉ [ κᵉ ]ᵉ ≡ ε₀' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
    rhs = trans ([⨟]ᵉ ε' X κᵉ)
          (trans (sym ([≐]ᵉ (updᵉ-absorb j 𝟏̂ₑ (X ⨟ˢ κᵉ) j↦𝟏) ε'))
          (trans (sym ([⨟]ᵉ ε' (updᵉ j 𝟏̂ₑ) (X ⨟ˢ κᵉ)))
          (trans (sym ([⨟]ᵉ (ε' [ updᵉ j 𝟏̂ₑ ]ᵉ) X κᵉ))
          (trans (cong (_[ κᵉ ]ᵉ) (keyᵉ j (ε' [ updᵉ j 𝟏̂ₑ ]ᵉ) e₂ γ))
                 ([⨟]ᵉ ε₀' (wkˢᵉ ⨟ˢ γ) κᵉ)))))

stripʳ-top-bnd : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O : Subst Θ (Φ +e)) → (j : EVar (Φ +e))
               → (ρ ρ' : RExp (Φ +e)) → {ρ₀ ρ₀' : RExp Φ} → ρ' [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀'
               → Outerᵣ O ρ' → ρ [ updᵉ j (econst ⊤ₑ) ]ʳ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀
               → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
               → Uniform O (popˢ j ⨟ˢ γ)
               → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ
               → Q ⊩ ρ₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ ρ₀' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
stripʳ-top-bnd {Q = Q} O j ρ ρ' {ρ₀} {ρ₀'} e₁ o e₂ γ hγ u p =
  transᵣ lhs (subst (λ y → Q ⊩ ρ [ X ]ʳ [ κ⊤ ]ʳ ≾̂ᵣ y) rhs p⊤)
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

stripᵉ-top-bnd : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O : Subst Θ (Φ +e)) → (j : EVar (Φ +e))
               → (ε ε' : EExp (Φ +e)) → {ε₀ ε₀' : EExp Φ} → ε' [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀'
               → Outerₑ O ε' → ε [ updᵉ j (econst ⊤ₑ) ]ᵉ [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀
               → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
               → Uniform O (popˢ j ⨟ˢ γ)
               → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ
               → Q ⊩ ε₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ ε₀' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
stripᵉ-top-bnd {Q = Q} O j ε ε' {ε₀} {ε₀'} e₁ o e₂ γ hγ u p =
  transₑ lhs (subst (λ y → Q ⊩ ε [ X ]ᵉ [ κ⊤ ]ᵉ ≾̂ₑ y) rhs p⊤)
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

stripʳ-unit-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (ij? : Maybe (Is-just 𝟏ₑ-least?))
             → (j : EVar (Φ +e))
             → (ρ ρ' : RExp (Φ +e)) → (ρ₀ : RExp Φ) → (e₁ : ρ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀)
             → ∀ {a} → stripʳ-unit ij? j ρ ρ' ρ₀ e₁ ≡ just a
             → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
             → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ
             → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
             → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
stripʳ-unit-princ nothing    j ρ ρ' ρ₀ e₁ ()
stripʳ-unit-princ {Q = Q} (just ij) j ρ ρ' ρ₀ e₁ eq
  with strʳ⁺ j (ρ' [ updᵉ j 𝟏̂ₑ ]ʳ)
... | nothing          = ⊥just eq
... | just (ρ₀' , e₂) = λ γ hγ p →
      just-one₂ (λ τ τ' → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ) eq
                (stripʳ-unit-bnd j ρ ρ' e₁ e₂ γ hγ p)

stripᵉ-unit-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (ij? : Maybe (Is-just 𝟏ₑ-least?))
             → (j : EVar (Φ +e))
             → (ε ε' : EExp (Φ +e)) → (ε₀ : EExp Φ) → (e₁ : ε [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀)
             → ∀ {a} → stripᵉ-unit ij? j ε ε' ε₀ e₁ ≡ just a
             → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
             → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ
             → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
             → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
stripᵉ-unit-princ nothing    j ε ε' ε₀ e₁ ()
stripᵉ-unit-princ {Q = Q} (just ij) j ε ε' ε₀ e₁ eq
  with strᵉ⁺ j (ε' [ updᵉ j 𝟏̂ₑ ]ᵉ)
... | nothing          = ⊥just eq
... | just (ε₀' , e₂) = λ γ hγ p →
      just-one₂ (λ τ τ' → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ) eq
                (stripᵉ-unit-bnd j ε ε' e₁ e₂ γ hγ p)

stripʳ-top-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O : Subst Θ (Φ +e)) → (j : EVar (Φ +e))
                 → (ρ ρ' : RExp (Φ +e)) → (ρ₀' : RExp Φ) → (e₁ : ρ' [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀')
                 → ∀ {a} → stripʳ-top O j ρ ρ' ρ₀' e₁ ≡ just a
                 → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
                 → Uniform O (popˢ j ⨟ˢ γ)
                 → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ
                 → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
                 → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
stripʳ-top-princ {Q = Q} O j ρ ρ' ρ₀' e₁ eq
  with outerᵣ? O ρ' | strʳ⁺ j (ρ [ updᵉ j (econst ⊤ₑ) ]ʳ)
... | just o  | just (ρ₀ , e₂) = λ γ hγ u p →
      just-one₂ (λ τ τ' → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ) eq
                (stripʳ-top-bnd O j ρ ρ' e₁ o e₂ γ hγ u p)
... | just _  | nothing = ⊥just eq
... | nothing | _       = ⊥just eq

stripᵉ-top-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O : Subst Θ (Φ +e)) → (j : EVar (Φ +e))
                 → (ε ε' : EExp (Φ +e)) → (ε₀' : EExp Φ) → (e₁ : ε' [ popˢ j ]ᵉ ≡ wkᵉ-e ε₀')
                 → ∀ {a} → stripᵉ-top O j ε ε' ε₀' e₁ ≡ just a
                 → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
                 → Uniform O (popˢ j ⨟ˢ γ)
                 → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ
                 → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
                 → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
stripᵉ-top-princ {Q = Q} O j ε ε' ε₀' e₁ eq
  with outerₑ? O ε' | strᵉ⁺ j (ε [ updᵉ j (econst ⊤ₑ) ]ᵉ)
... | just o  | just (ε₀ , e₂) = λ γ hγ u p →
      just-one₂ (λ τ τ' → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ) eq
                (stripᵉ-top-bnd O j ε ε' e₁ o e₂ γ hγ u p)
... | just _  | nothing = ⊥just eq
... | nothing | _       = ⊥just eq

-- A stripped ordering kept as an atom

fromStripʳ-princ : ∀ {Φ} {j : EVar (Φ +e)} {H : Hyps (Φ +e)} {ρ ρ' : RExp (Φ +e)}
                 → (F : RExp Φ → RExp Φ → Set) → (x : Maybe (Stripʳ j ρ ρ'))
                 → ∀ {a} → fromStripʳ {j = j} {H = H} {ρ = ρ} {ρ' = ρ'} x ≡ just a
                 → (∀ {b} → x ≡ just b → ∀ {τ τ'} → (τ , τ') ∈ proj₁ b → F τ τ')
                 → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a → F τ τ'
fromStripʳ-princ F (just b) refl k = k refl
fromStripʳ-princ F nothing  ()

fromStripᵉ-princ : ∀ {Φ} {j : EVar (Φ +e)} {H : Hyps (Φ +e)} {ε ε' : EExp (Φ +e)}
                 → (F : EExp Φ → EExp Φ → Set) → (x : Maybe (Stripᵉ j ε ε'))
                 → ∀ {a} → fromStripᵉ {j = j} {H = H} {ε = ε} {ε' = ε'} x ≡ just a
                 → (∀ {b} → x ≡ just b → ∀ {τ τ'} → (τ , τ') ∈ proj₁ b → F τ τ')
                 → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a → F τ τ'
fromStripᵉ-princ F (just b) refl k = k refl
fromStripᵉ-princ F nothing  ()

atomʳ-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O : Subst Θ (Φ +e)) → (H : Hyps (Φ +e)) → (j : EVar (Φ +e))
            → (ρ ρ' : RExp (Φ +e))
            → ∀ {a} → atomʳ O H j ρ ρ' ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → Uniform O (popˢ j ⨟ˢ γ)
            → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ
            → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
            → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ
atomʳ-princ {Q = Q} O H j ρ ρ' eq with strʳ⁺ j ρ | strʳ⁺ j ρ'
... | just _ | just _ = ⊥just eq
... | just (ρ₀ , e₁) | nothing with decideᵣ full H ρ ρ'
...   | just _  = λ γ hγ u p m → ⊥-elim (just-none eq m)
...   | nothing = λ γ hγ u p →
        fromStripʳ-princ (λ τ τ' → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ) _ eq
          (λ es → stripʳ-unit-princ (Is-just? 𝟏ₑ-least?) j ρ ρ' ρ₀ e₁ es γ hγ p)
atomʳ-princ {Q = Q} O H j ρ ρ' eq | nothing | just (ρ₀' , e₂) with decideᵣ full H ρ ρ'
... | just _  = λ γ hγ u p m → ⊥-elim (just-none eq m)
... | nothing = λ γ hγ u p →
      fromStripʳ-princ (λ τ τ' → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ) _ eq
        (λ es → stripʳ-top-princ O j ρ ρ' ρ₀' e₂ es γ hγ u p)
atomʳ-princ O H j ρ ρ' eq | nothing | nothing with decideᵣ full H ρ ρ'
... | just _  = λ γ hγ u p m → ⊥-elim (just-none eq m)
... | nothing = ⊥just eq

atomᵉ-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O : Subst Θ (Φ +e)) → (H : Hyps (Φ +e)) → (j : EVar (Φ +e))
            → (ε ε' : EExp (Φ +e))
            → ∀ {a} → atomᵉ O H j ε ε' ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → Uniform O (popˢ j ⨟ˢ γ)
            → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ
            → ∀ {τ τ'} → (τ , τ') ∈ proj₁ a
            → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ
atomᵉ-princ {Q = Q} O H j ε ε' eq with strᵉ⁺ j ε | strᵉ⁺ j ε'
... | just _ | just _ = ⊥just eq
... | just (ε₀ , e₁) | nothing with decideₑ full H ε ε'
...   | just _  = λ γ hγ u p m → ⊥-elim (just-none eq m)
...   | nothing = λ γ hγ u p →
        fromStripᵉ-princ (λ τ τ' → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ) _ eq
          (λ es → stripᵉ-unit-princ (Is-just? 𝟏ₑ-least?) j ε ε' ε₀ e₁ es γ hγ p)
atomᵉ-princ {Q = Q} O H j ε ε' eq | nothing | just (ε₀' , e₂) with decideₑ full H ε ε'
... | just _  = λ γ hγ u p m → ⊥-elim (just-none eq m)
... | nothing = λ γ hγ u p →
      fromStripᵉ-princ (λ τ τ' → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ) _ eq
        (λ es → stripᵉ-top-princ O j ε ε' ε₀' e₂ es γ hγ u p)
atomᵉ-princ O H j ε ε' eq | nothing | nothing with decideₑ full H ε ε'
... | just _  = λ γ hγ u p m → ⊥-elim (just-none eq m)
... | nothing = ⊥just eq

atomᵗ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (A : OVType (Φ +e))
            → ∀ {a} → atomᵗ j A ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e))
            → wkᵉ-H Q ⊩Et A [ popˢ j ⨟ˢ γ ]ᵛ
            → ∀ {B} → B ∈ proj₁ a → Q ⊩Et B [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ
atomᵗ-princ {Q = Q} j A eq with strᵛ⁺ j A
... | just (A₀ , e₁) = λ γ p →
      just-one (λ B → Q ⊩Et B [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ) eq (bndᵗ j A e₁ γ p)
... | nothing = ⊥just eq

atomˢ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e)) → (A B : OVType (Φ +e))
            → ∀ {a} → atomˢ j A B ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e))
            → wkᵉ-H Q ∣ A [ popˢ j ⨟ˢ γ ]ᵛ <:̂ᵛ B [ popˢ j ⨟ˢ γ ]ᵛ
            → ∀ {X Y} → (X , Y) ∈ proj₁ a
            → Q ∣ X [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ <:̂ᵛ Y [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ
atomˢ-princ {Q = Q} j A B eq with strᵛ⁺ j A | strᵛ⁺ j B
... | just (A₀ , e₁) | just (B₀ , e₂) = λ γ p →
      just-one₂ (λ X Y → Q ∣ X [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ <:̂ᵛ Y [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ) eq
                (bndˢ j A B e₁ e₂ γ p)
... | just _  | nothing = ⊥just eq
... | nothing | _       = ⊥just eq

-- A kept disjunction: an eternal type is the instance's with the eigenvariable
-- at the unit; a grade below the unit is bounded as for `stripʳ-top`

atomᵈ-bnd : ∀ {Φ Φ'} → (j : EVar (Φ +e)) → (A : OVType (Φ +e)) → (ρ : RExp (Φ +e))
          → {A₀ : OVType Φ} {ρ₀ : RExp Φ} → A [ popˢ j ]ᵛ ≡ wkᵉ-v A₀
          → ρ [ updᵉ j (econst ⊤ₑ) ]ʳ [ popˢ j ]ʳ ≡ wkᵉ-r ρ₀
          → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
          → VarOK ∅ᴴ (A [ popˢ j ⨟ˢ γ ]ᵛ) (ρ [ popˢ j ⨟ˢ γ ]ʳ)
          → VarOK ∅ᴴ (A₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ) (ρ₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ)
atomᵈ-bnd j A ρ {A₀} {ρ₀} e₁ e₂ γ hγ ok =
  [ (λ et → et-ok (bndᵗ j A e₁ γ et))
  , (λ le → ≾ᵘ-ok (transᵣ lhs (⊩-substᵣ {σ = κ⊤} (⊩ᴴ-κ (econst ⊤ₑ)) le))) ]′
  (VarOK-∅ᴴ ok)
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

atomᵈ-princ : ∀ {Φ Φ'} → (j : EVar (Φ +e)) → (A : OVType (Φ +e))
            → (ρ : RExp (Φ +e))
            → ∀ {a} → atomᵈ j A ρ ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → VarOK ∅ᴴ (A [ popˢ j ⨟ˢ γ ]ᵛ) (ρ [ popˢ j ⨟ˢ γ ]ʳ)
            → ∀ {B τ} → (B , τ) ∈ proj₁ a
            → VarOK ∅ᴴ (B [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ) (τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ)
atomᵈ-princ j A ρ eq with strᵛ⁺ j A | strʳ⁺ j (ρ [ updᵉ j (econst ⊤ₑ) ]ʳ)
... | just (A₀ , e₁) | just (ρ₀ , e₂) = λ γ hγ p →
      just-one₂ (λ B τ → VarOK ∅ᴴ (B [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ) (τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ)) eq
                (atomᵈ-bnd j A ρ e₁ e₂ γ hγ p)
... | just _  | nothing = ⊥just eq
... | nothing | _       = ⊥just eq

-- Two substitutions after which `O` reads the same agree on every
-- expression mentioning only unknowns `O`'s images mention

agree-≐ : ∀ {Θ Φ Ω} {O : Subst Θ Φ} {X₁ X₂ : Subst Φ Ω}
        → (O ⨟ˢ X₁) ≐ˢ (O ⨟ˢ X₂) → Agree O idˢ X₁ X₂
agree-≐ {O = O} {X₁} {X₂} eq =
  agree-out O idˢ X₁ X₂ O idˢ
    (λ y → trans ([⨟]ᵛ y O X₁) (trans ([≐]ᵛ eq y) (sym ([⨟]ᵛ y O X₂))))
    (λ y → trans ([⨟]ʳ y O X₁) (trans ([≐]ʳ eq y) (sym ([⨟]ʳ y O X₂))))
    (λ y → trans ([⨟]ᵉ y O X₁) (trans ([≐]ᵉ eq y) (sym ([⨟]ᵉ y O X₂))))
    (≐ˢ-trans (⨟-idʳ O) (≐ˢ-sym (⨟-idˡ O)))

agree-≡ʳ : ∀ {Θ Φ Ω} {O : Subst Θ Φ} {X₁ X₂ : Subst Φ Ω}
         → (O ⨟ˢ X₁) ≐ˢ (O ⨟ˢ X₂) → (x : RExp Φ) → Outerᵣ O x → x [ X₁ ]ʳ ≡ x [ X₂ ]ʳ
agree-≡ʳ {O = O} {X₁} {X₂} eq x o =
  trans (sym ([≐]ʳ (⨟-idˡ X₁) x))
        (trans (agreeᵣ {O = O} {X = idˢ} {σ₁ = X₁} {σ₂ = X₂} (agree-≐ {O = O} {X₁} {X₂} eq) x o)
               ([≐]ʳ (⨟-idˡ X₂) x))

agree-≡ᵉ : ∀ {Θ Φ Ω} {O : Subst Θ Φ} {X₁ X₂ : Subst Φ Ω}
         → (O ⨟ˢ X₁) ≐ˢ (O ⨟ˢ X₂) → (x : EExp Φ) → Outerₑ O x → x [ X₁ ]ᵉ ≡ x [ X₂ ]ᵉ
agree-≡ᵉ {O = O} {X₁} {X₂} eq x o =
  trans (sym ([≐]ᵉ (⨟-idˡ X₁) x))
        (trans (agreeₑ {O = O} {X = idˢ} {σ₁ = X₁} {σ₂ = X₂} (agree-≐ {O = O} {X₁} {X₂} eq) x o)
               ([≐]ᵉ (⨟-idˡ X₂) x))

-- An entry mentioning only such unknowns, under its binders, holds
-- after the one when it holds after the other

⊩ᴼ-agree : ∀ {Θ Φ Ω} {Q : Hyps Ω} {O : Subst Θ Φ} {X₁ X₂ : Subst Φ Ω} → (E : QOrd Φ)
         → Outerᵒ (O ↑ᵉⁿ rigids E) (body E) → (O ⨟ˢ X₁) ≐ˢ (O ⨟ˢ X₂)
         → Q ⊩ᴼ E [ X₁ ] → Q ⊩ᴼ E [ X₂ ]
⊩ᴼ-agree {Q = Q} {O} {X₁} {X₂} (qord l k o) (or , oe) eq h = mk⊩ᵒ r e
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

-- The two lists a solved split keeps, read off its equation

just-proj₁ : ∀ {X Y : Set} {Z : X → Y → Set} {x : X} {y : Y} {z : Z x y}
               {a : Σ[ x' ∈ X ] Σ[ y' ∈ Y ] Z x' y'}
           → just (x , y , z) ≡ just a → x ≡ proj₁ a
just-proj₁ refl = refl

just-proj₂ : ∀ {X Y : Set} {Z : X → Y → Set} {x : X} {y : Y} {z : Z x y}
               {a : Σ[ x' ∈ X ] Σ[ y' ∈ Y ] Z x' y'}
           → just (x , y , z) ≡ just a → y ≡ proj₁ (proj₂ a)
just-proj₂ refl = refl

-- A property of every pair of a list built by `∷` or `++`

∈-≡₂ : ∀ {X Y : Set} {l l' : List (X × Y)} → (F : X → Y → Set) → l ≡ l'
     → (∀ {τ τ'} → (τ , τ') ∈ l → F τ τ') → ∀ {τ τ'} → (τ , τ') ∈ l' → F τ τ'
∈-≡₂ F refl g m = g m

∈-∷₂ : ∀ {X Y : Set} {x : X} {y : Y} {l l' : List (X × Y)} → (F : X → Y → Set)
     → (x , y) ∷ l ≡ l' → F x y → (∀ {τ τ'} → (τ , τ') ∈ l → F τ τ')
     → ∀ {τ τ'} → (τ , τ') ∈ l' → F τ τ'
∈-∷₂ F refl f g (here refl) = f
∈-∷₂ F refl f g (there m)   = g m

∈-++₂ : ∀ {X Y : Set} {l₁ l₂ l' : List (X × Y)} → (F : X → Y → Set)
      → l₁ ++ l₂ ≡ l' → (∀ {τ τ'} → (τ , τ') ∈ l₁ → F τ τ')
      → (∀ {τ τ'} → (τ , τ') ∈ l₂ → F τ τ') → ∀ {τ τ'} → (τ , τ') ∈ l' → F τ τ'
∈-++₂ {l₁ = l₁} F refl f g m = [ f , g ]′ (∈-++⁻ l₁ m)

-- A deferred ordering holds at the outer instance lifted over the rigid

deferredʳ-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O⁺ : Subst (Θ +e) (Φ +e)) → (j : EVar (Φ +e))
                → (γ : Subst (Φ +e) (Φ' +e)) → (ρ ρ' : RExp (Φ +e))
                → Outerᵣ O⁺ ρ → Outerᵣ O⁺ ρ'
                → (O⁺ ⨟ˢ (popˢ j ⨟ˢ γ)) ≐ˢ (O⁺ ⨟ˢ (popˢ j ⨟ˢ (((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ)))
                → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ
                → wkᵉ-H Q ⊩ ρ [ popˢ j ]ʳ [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ʳ
                            ≾̂ᵣ ρ' [ popˢ j ]ʳ [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ʳ
deferredʳ-princ {Q = Q} O⁺ j γ ρ ρ' o o' eqO p =
  subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y) (at ρ o) (at ρ' o') p
  where
    X = ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ

    at : (x : RExp _) → Outerᵣ O⁺ x → x [ popˢ j ⨟ˢ γ ]ʳ ≡ x [ popˢ j ]ʳ [ X ]ʳ
    at x ox = trans (agree-≡ʳ {O = O⁺} eqO x ox) (sym ([⨟]ʳ x (popˢ j) X))

deferredᵉ-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O⁺ : Subst (Θ +e) (Φ +e)) → (j : EVar (Φ +e))
                → (γ : Subst (Φ +e) (Φ' +e)) → (ε ε' : EExp (Φ +e))
                → Outerₑ O⁺ ε → Outerₑ O⁺ ε'
                → (O⁺ ⨟ˢ (popˢ j ⨟ˢ γ)) ≐ˢ (O⁺ ⨟ˢ (popˢ j ⨟ˢ (((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ)))
                → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ
                → wkᵉ-H Q ⊩ ε [ popˢ j ]ᵉ [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ᵉ
                            ≾̂ₑ ε' [ popˢ j ]ᵉ [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ᵉ
deferredᵉ-princ {Q = Q} O⁺ j γ ε ε' o o' eqO p =
  subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ₑ y) (at ε o) (at ε' o') p
  where
    X = ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ

    at : (x : EExp _) → Outerₑ O⁺ x → x [ popˢ j ⨟ˢ γ ]ᵉ ≡ x [ popˢ j ]ᵉ [ X ]ᵉ
    at x ox = trans (agree-≡ᵉ {O = O⁺} eqO x ox) (sym ([⨟]ᵉ x (popˢ j) X))

-- The kept orderings hold at the outer instance; the deferred ones at it lifted
-- over the rigid, the outer images being uniform in it (`eqO`)

listʳ-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O : Subst Θ (Φ +e)) → (O⁺ : Subst (Θ +e) (Φ +e))
            → (H : Hyps (Φ +e)) → (j : EVar (Φ +e)) → (l : List (RExp (Φ +e) × RExp (Φ +e)))
            → ∀ {a} → listʳ O O⁺ H j l ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → Uniform O (popˢ j ⨟ˢ γ)
            → (O⁺ ⨟ˢ (popˢ j ⨟ˢ γ)) ≐ˢ (O⁺ ⨟ˢ (popˢ j ⨟ˢ (((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ)))
            → (∀ {ρ ρ'} → (ρ , ρ') ∈ l
                 → wkᵉ-H Q ⊩ ρ [ popˢ j ⨟ˢ γ ]ʳ ≾̂ᵣ ρ' [ popˢ j ⨟ˢ γ ]ʳ)
            → (∀ {τ τ'} → (τ , τ') ∈ proj₁ a
                 → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ)
            × (∀ {τ τ'} → (τ , τ') ∈ proj₁ (proj₂ a)
                 → wkᵉ-H Q ⊩ τ [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ʳ ≾̂ᵣ τ' [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ʳ)
listʳ-princ O O⁺ H j []              refl γ hγ u eqO k = (λ ()) , (λ ())
listʳ-princ {Q = Q} O O⁺ H j ((ρ , ρ') ∷ l) eq with listʳ O O⁺ H j l in e₂
... | nothing = ⊥just eq
... | just (l₀ , d₀ , f) with freeʳ? j ρ ρ'
...   | yes (a , b) = λ γ hγ u eqO k →
        let ih = listʳ-princ O O⁺ H j l e₂ γ hγ u eqO (λ m' → k (there m')) in
        ∈-∷₂ (λ τ τ' → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ)
             (just-proj₁ eq)
             (bndʳ j ρ ρ' (proj₂ (to-witness a)) (proj₂ (to-witness b)) γ (k (here refl)))
             (proj₁ ih)
        , ∈-≡₂ (λ τ τ' → wkᵉ-H Q ⊩ τ [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ʳ ≾̂ᵣ τ' [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ʳ)
               (just-proj₂ eq) (proj₂ ih)
...   | no nf with atomʳ O H j ρ ρ' in e₁
...     | just (a , fa) = λ γ hγ u eqO k →
          let ih = listʳ-princ O O⁺ H j l e₂ γ hγ u eqO (λ m' → k (there m')) in
          ∈-++₂ (λ τ τ' → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ)
                (just-proj₁ eq) (atomʳ-princ O H j ρ ρ' e₁ γ hγ u (k (here refl))) (proj₁ ih)
          , ∈-≡₂ (λ τ τ' → wkᵉ-H Q ⊩ τ [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ʳ ≾̂ᵣ τ' [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ʳ)
                 (just-proj₂ eq) (proj₂ ih)
...     | nothing with outerᵣ? O⁺ ρ | outerᵣ? O⁺ ρ'
...       | just o | just o' = λ γ hγ u eqO k →
            let ih = listʳ-princ O O⁺ H j l e₂ γ hγ u eqO (λ m' → k (there m')) in
            ∈-≡₂ (λ τ τ' → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ ≾̂ᵣ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ʳ)
                 (just-proj₁ eq) (proj₁ ih)
            , ∈-∷₂ (λ τ τ' → wkᵉ-H Q ⊩ τ [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ʳ ≾̂ᵣ τ' [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ʳ)
                   (just-proj₂ eq) (deferredʳ-princ O⁺ j γ ρ ρ' o o' eqO (k (here refl))) (proj₂ ih)
...       | just _  | nothing = ⊥just eq
...       | nothing | _       = ⊥just eq

listᵉ-princ : ∀ {Θ Φ Φ'} {Q : Hyps Φ'} → (O : Subst Θ (Φ +e)) → (O⁺ : Subst (Θ +e) (Φ +e))
            → (H : Hyps (Φ +e)) → (j : EVar (Φ +e)) → (l : List (EExp (Φ +e) × EExp (Φ +e)))
            → ∀ {a} → listᵉ O O⁺ H j l ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
            → Uniform O (popˢ j ⨟ˢ γ)
            → (O⁺ ⨟ˢ (popˢ j ⨟ˢ γ)) ≐ˢ (O⁺ ⨟ˢ (popˢ j ⨟ˢ (((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ)))
            → (∀ {ε ε'} → (ε , ε') ∈ l
                 → wkᵉ-H Q ⊩ ε [ popˢ j ⨟ˢ γ ]ᵉ ≾̂ₑ ε' [ popˢ j ⨟ˢ γ ]ᵉ)
            → (∀ {τ τ'} → (τ , τ') ∈ proj₁ a
                 → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ)
            × (∀ {τ τ'} → (τ , τ') ∈ proj₁ (proj₂ a)
                 → wkᵉ-H Q ⊩ τ [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ᵉ ≾̂ₑ τ' [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ᵉ)
listᵉ-princ O O⁺ H j []              refl γ hγ u eqO k = (λ ()) , (λ ())
listᵉ-princ {Q = Q} O O⁺ H j ((ε , ε') ∷ l) eq with listᵉ O O⁺ H j l in e₂
... | nothing = ⊥just eq
... | just (l₀ , d₀ , f) with freeᵉ? j ε ε'
...   | yes (a , b) = λ γ hγ u eqO k →
        let ih = listᵉ-princ O O⁺ H j l e₂ γ hγ u eqO (λ m' → k (there m')) in
        ∈-∷₂ (λ τ τ' → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ)
             (just-proj₁ eq)
             (bndᵉ j ε ε' (proj₂ (to-witness a)) (proj₂ (to-witness b)) γ (k (here refl)))
             (proj₁ ih)
        , ∈-≡₂ (λ τ τ' → wkᵉ-H Q ⊩ τ [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ᵉ ≾̂ₑ τ' [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ᵉ)
               (just-proj₂ eq) (proj₂ ih)
...   | no nf with atomᵉ O H j ε ε' in e₁
...     | just (a , fa) = λ γ hγ u eqO k →
          let ih = listᵉ-princ O O⁺ H j l e₂ γ hγ u eqO (λ m' → k (there m')) in
          ∈-++₂ (λ τ τ' → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ)
                (just-proj₁ eq) (atomᵉ-princ O H j ε ε' e₁ γ hγ u (k (here refl))) (proj₁ ih)
          , ∈-≡₂ (λ τ τ' → wkᵉ-H Q ⊩ τ [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ᵉ ≾̂ₑ τ' [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ᵉ)
                 (just-proj₂ eq) (proj₂ ih)
...     | nothing with outerₑ? O⁺ ε | outerₑ? O⁺ ε'
...       | just o | just o' = λ γ hγ u eqO k →
            let ih = listᵉ-princ O O⁺ H j l e₂ γ hγ u eqO (λ m' → k (there m')) in
            ∈-≡₂ (λ τ τ' → Q ⊩ τ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ ≾̂ₑ τ' [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵉ)
                 (just-proj₁ eq) (proj₁ ih)
            , ∈-∷₂ (λ τ τ' → wkᵉ-H Q ⊩ τ [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ᵉ ≾̂ₑ τ' [ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ ]ᵉ)
                   (just-proj₂ eq) (deferredᵉ-princ O⁺ j γ ε ε' o o' eqO (k (here refl))) (proj₂ ih)
...       | just _  | nothing = ⊥just eq
...       | nothing | _       = ⊥just eq

listᵗ-princ : ∀ {Φ Φ'} {Q : Hyps Φ'} → (j : EVar (Φ +e))
            → (l : List (OVType (Φ +e)))
            → ∀ {a} → listᵗ j l ≡ just a
            → (γ : Subst (Φ +e) (Φ' +e))
            → (∀ {A} → A ∈ l → wkᵉ-H Q ⊩Et A [ popˢ j ⨟ˢ γ ]ᵛ)
            → ∀ {B} → B ∈ proj₁ a → Q ⊩Et B [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]ᵛ
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
            → (γ : Subst (Φ +e) (Φ' +e)) → (δ : Subst Φ Φ') → (E : QOrd (Φ +e))
            → Outerᵒ (O⁺ ↑ᵉⁿ rigids E) (body E)
            → (O⁺ ⨟ˢ (popˢ j ⨟ˢ γ)) ≐ˢ (O⁺ ⨟ˢ (popˢ j ⨟ˢ (δ ↑ᵉ)))
            → wkᵉ-H Q ⊩ᴼ E [ popˢ j ⨟ˢ γ ] → Q ⊩ᴼ liftᵈ j E [ δ ]
liftᵈ-princ O⁺ j γ δ E oo eqO h =
  closeᵈ-princ (E [ popˢ j ]ᵠ) (⊩ᴼ-subst⁻ E (⊩ᴼ-agree E oo eqO h))

liftedᵈ-princ : ∀ {Θ Φ Φ'} → (O⁺ : Subst (Θ +e) (Φ +e)) → (j : EVar (Φ +e))
              → (γ : Subst (Φ +e) (Φ' +e)) → (R : Resid (Φ +e)) → OuterD O⁺ (dfs R)
              → (O⁺ ⨟ˢ (popˢ j ⨟ˢ γ)) ≐ˢ (O⁺ ⨟ˢ (popˢ j ⨟ˢ (((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ)))
              → ∅ᴴ ⊩ᴿ R [ popˢ j ⨟ˢ γ ]
              → ∀ {E} → E ∈ map (liftᵈ j) (dfs R) → ∅ᴴ ⊩ᴼ E [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]
liftedᵈ-princ O⁺ j γ R od eqO h m with ∈-map⁻ (liftᵈ j) m
... | E₀ , m₀ , refl = liftᵈ-princ O⁺ j γ ((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) E₀ (od m₀) eqO (⊩dfs h m₀)

splitᴿ-princ : ∀ {Θ Φ Φ'} → (O : Subst Θ (Φ +e)) → (O⁺ : Subst (Θ +e) (Φ +e))
             → (j : EVar (Φ +e)) → (R : Resid (Φ +e))
             → ∀ {a} → splitᴿ O O⁺ j R ≡ solved a
             → (γ : Subst (Φ +e) (Φ' +e)) → sE γ (newᵉ {Φ}) ≡ evar (newᵉ {Φ'})
             → Uniform O (popˢ j ⨟ˢ γ)
             → (O⁺ ⨟ˢ (popˢ j ⨟ˢ γ)) ≐ˢ (O⁺ ⨟ˢ (popˢ j ⨟ˢ (((wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ) ↑ᵉ)))
             → ∅ᴴ ⊩ᴿ R [ popˢ j ⨟ˢ γ ]
             → ∅ᴴ ⊩ᴿ proj₁ a [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]
splitᴿ-princ O O⁺ j R eq
  with listᵗ j (ts R) in e₃ | listˢ j (ss R) in e₄ | listᵈ j (ds R) in e₅
     | listʳ O O⁺ (freeᴴ j R) j (rs R) in e₁ | listᵉ O O⁺ (freeᴴ j R) j (es R) in e₂
     | outerD? O⁺ (dfs R)
... | just (lt , ft) | just (ls , fs) | just (ld , fd)
    | just (lr , dr , fr) | just (le , de , fe) | just od = λ γ hγ u eqO h →
      let pr = listʳ-princ O O⁺ (freeᴴ j R) j (rs R) e₁ γ hγ u eqO (⊩rs h)
          pe = listᵉ-princ O O⁺ (freeᴴ j R) j (es R) e₂ γ hγ u eqO (⊩es h)
      in subst (λ R₀ → ∅ᴴ ⊩ᴿ R₀ [ (wkˢᵉ ⨟ˢ γ) ⨟ˢ κᵉ ]) (cong proj₁ (solved-inj eq))
           (mk⊩ᴿ (proj₁ pr) (proj₁ pe)
                 (listᵗ-princ j (ts R) e₃ γ (⊩ts h))
                 (listˢ-princ j (ss R) e₄ γ (⊩ss h))
                 (listᵈ-princ j (ds R) e₅ γ hγ (⊩ds h))
                 (λ { (here refl) → closeᵈ-princ (qord nothing 0 (ords dr de))
                                                 (mk⊩ᵒ (proj₂ pr) (proj₂ pe))
                    ; (there m) → liftedᵈ-princ O⁺ j γ R od eqO h m }))
splitᴿ-princ O O⁺ j R eq | nothing | _       | _       | _      | _      | _       = ⊥refuted eq
splitᴿ-princ O O⁺ j R eq | just _  | nothing | _       | _      | _      | _       = ⊥refuted eq
splitᴿ-princ O O⁺ j R eq | just _  | just _  | nothing | _      | _      | _       = ⊥refuted eq
splitᴿ-princ O O⁺ j R eq | just _  | just _  | just _  | nothing | _     | _       = ⊥stuck eq
splitᴿ-princ O O⁺ j R eq | just _  | just _  | just _  | just _ | nothing | _      = ⊥stuck eq
splitᴿ-princ O O⁺ j R eq | just _  | just _  | just _  | just _ | just _ | nothing = ⊥stuck eq

-- Under the inner factorisation the rigid's image is the outer eigenvariable,
-- and the outer unknowns' images are the outer ones, weakened

bnd-var : ∀ {Ω Φ Ω''} → (γ : Subst (Ω +e) Φ) → (δ : Subst Φ (Ω'' +e))
        → {δ₀ : Subst Ω Ω''} → (γ ⨟ˢ δ) ≐ˢ (δ₀ ↑ᵉ)
        → {j : EVar Φ} → sE γ (newᵉ {Ω}) ≡ evar j
        → sE δ j ≡ evar (newᵉ {Ω''})
bnd-var {Ω} γ δ tri eqj = trans (sym (cong (_[ δ ]ᵉ) eqj)) (≐ᵉ tri (newᵉ {Ω}))

bnd-out : ∀ {Ω Φ Ω''} → (γ : Subst (Ω +e) Φ) → (δ : Subst Φ (Ω'' +e))
        → (δ₀ : Subst Ω Ω'') → (γ ⨟ˢ δ) ≐ˢ (δ₀ ↑ᵉ)
        → ((wkˢᵉ {Ω} ⨟ˢ γ) ⨟ˢ δ) ≐ˢ (δ₀ ⨟ˢ wkˢᵉ)
bnd-out γ δ δ₀ tri =
  ≐ˢ-trans (⨟-assoc wkˢᵉ γ δ) (≐ˢ-trans (⨟-congʳ wkˢᵉ tri) (wkˢᵉ-↑ᵉ δ₀))

-- The inner run is entered at `δ₀ ↑ᵉ`; its result is undone at the rigid,
-- which is sent to the unit

popᵉ-princ : ∀ {Θ} → (s : St Θ) → (C : Constraint (Θ +e))
           → (Φ : Scope) → (θ'' : Subst (Θ +e) Φ) → (R'' : Resid Φ) → (rg'' : Rig Φ)
           → (m'' : ⇑ᵉˢ s ⟶ st Φ θ'' R'' rg'') → (w'' : Wit (st Φ θ'' R'' rg'') C)
           → Princ⇑ s (st Φ θ'' R'' rg'') m'' C
           → ∀ {s' : St Θ} {m : s ⟶ s'} {w : Wit s' (∀ᵉ C)}
           → popᵉ s C Φ θ'' R'' rg'' m'' w'' ≡ solved (s' , m , w)
           → Princ s s' m (∀ᵉ C)
popᵉ-princ s C (scope nt nr nzero) θ'' R'' rg'' m'' w'' ip ()
popᵉ-princ s C (scope nt nr (nsuc n)) θ'' R'' rg'' m'' w'' ip eq δ₀ sat h
  with evar? (sE (mδ m'') (newᵉ {Ω s}))
... | nothing = ⊥refuted eq
... | just (j , eqj) with strSub j (wkˢᵉ {Ω s} ⨟ˢ mδ m'')
                        | splitᴿ (wkˢᵉ {Ω s} ⨟ˢ mδ m'') (mδ m'') j R'' in eqsp
...   | just (δ₀ₛ , pδ) | solved (R₀ , tr) with eq
...     | refl = δ , tri ,
                 ∪ᴿ-both (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym tri) h))
                         (splitᴿ-princ (wkˢᵉ {Ω s} ⨟ˢ mδ m'') (mδ m'') j R'' eqsp γ
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
    uni : Uniform (wkˢᵉ {Ω s} ⨟ˢ mδ m'') (popˢ j ⨟ˢ γ)
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
          (≐ˢ-trans (⨟-congʳ δ₀ (wk-κ 𝟏̂ₑ)) (⨟-idʳ δ₀))))

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

-- Localisation keeps every instance entering the scope: the local unknowns are
-- in no outer image, and each step keeps the residual

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

-- A retry keeps every instance: it drops only what such an instance discharges

retry-princ : ∀ {Θ} → (s : St Θ) → {s' : St Θ} {m : s ⟶ s'} → retry s ≡ just (s' , m)
            → ∀ {Ω''} → (δ₀ : Subst (Ω s) Ω'') → ∅ᴴ ⊩ᴿ (res s) [ δ₀ ]
            → Σ[ δ ∈ Subst (Ω s') Ω'' ]
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

retry-fail : ∀ {Θ Ω''} → (s : St Θ) → retry s ≡ nothing
           → (δ₀ : Subst (Ω s) Ω'') → ∅ᴴ ⊩ᴿ (res s) [ δ₀ ] → ⊥
retry-fail s eq δ₀ h with retryᴰ (ordsOf (res s)) (dfs (res s))
... | inj₁ (E , m , r) = r (δ₀ ⨟ˢ groundˢ) (⊩dfs (⊩ᴿ-⨟ {δ' = groundˢ} ⊩ᴴ-∅ h) m)
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

-- The same, the close read off the equation

thenRetry-princᵉ : ∀ {Θ} {s : St Θ} {C : Constraint Θ}
                 → (x : Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C)))
                 → ∀ {s' : St Θ} {m : s ⟶ s'} {w : Wit s' C}
                 → thenRetry {C = C} x ≡ solved (s' , m , w)
                 → (∀ {s₁ : St Θ} {m₁ : s ⟶ s₁} {w₁ : Wit s₁ C}
                      → x ≡ solved (s₁ , m₁ , w₁) → Princ s s₁ m₁ C)
                 → Princ s s' m C
thenRetry-princᵉ x eq p = thenRetry-princ x p eq

-- Labelling changes no meaning

relabel-⊩⁻ : ∀ {Ω Ω'} {Q : Hyps Ω'} {δ : Subst Ω Ω'} → (op : Op) → (E : QOrd Ω)
           → Q ⊩ᴼ E [ δ ] → Q ⊩ᴼ relabel op E [ δ ]
relabel-⊩⁻ op (qord nothing  k o) h = h
relabel-⊩⁻ op (qord (just l) k o) h = h

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

    dfs' : ∀ {E} → E ∈ map (relabel op) (dfs (res s₁)) → ∅ᴴ ⊩ᴼ E [ δ₁ ]
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

subsList-exp : ∀ {Ω Ω'} → (l : List (OVType Ω × OVType Ω)) → (δ : Subst Ω Ω')
             → (∀ {A B} → (A , B) ∈ l
                  → Σ[ d ∈ SubDec (A [ δ ]ᵛ) (B [ δ ]ᵛ) ] (subDec (A [ δ ]ᵛ) (B [ δ ]ᵛ) ≡ just d))
             → subsList (map (mapᵖ (_[ δ ]ᵛ)) l) ≡ nothing → ⊥
subsList-exp l δ dec q with subsList-nothing (map (mapᵖ (_[ δ ]ᵛ)) l) q
... | A , B , m , r with ∈-map⁻ (mapᵖ (_[ δ ]ᵛ)) m
...   | (A₀ , B₀) , m₀ , refl = ⊥just (trans (sym r) (proj₂ (dec m₀)))

-- The closing expansion: it factors every satisfying instance, and
-- its failure refutes the residual.

reexpand-princ : ∀ {Θ Ω''} → (s : St Θ) → {s' : St Θ} {m : s ⟶ s'}
               → reexpand s ≡ just (s' , m)
               → (δ₀ : Subst (Ω s) Ω'') → (Q : Hyps Ω'')
               → Q ⊩ᴿ (res s) [ δ₀ ]
               → Σ[ δ ∈ Subst (Ω s') Ω'' ]
                   (((mδ m ⨟ˢ δ) ≐ˢ δ₀) × (Q ⊩ᴿ (res s') [ δ ]))
reexpand-princ s eq δ₀ Q h with expandSub (ss (res s)) in eqx
... | nothing = ⊥just eq
... | just (Ω' , δₑ) with subsList (ss (res s [ δₑ ]ᴿ)) | etsDec (ts (res s [ δₑ ]ᴿ))
...   | nothing | _       = ⊥just eq
...   | just _  | nothing = ⊥just eq
...   | just e  | just t with eq
...     | refl = δ , trix , atomiseᴿ-compl _ e t (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym trix) h))
  where
    facx = subst (ExpMax δ₀) eqx (expandSub-max (ss (res s)) δ₀ (⊩ss h))
    δ    = proj₁ facx
    trix = proj₂ facx

reexpand-fail : ∀ {Θ Ω''} → (s : St Θ) → reexpand s ≡ nothing
              → (δ₀ : Subst (Ω s) Ω'') → (Q : Hyps Ω'')
              → Q ⊩ᴿ (res s) [ δ₀ ] → ⊥
reexpand-fail s eq δ₀ Q h with expandSub (ss (res s)) in eqx
... | nothing = subst (ExpMax δ₀) eqx (expandSub-max (ss (res s)) δ₀ (⊩ss h))
... | just (Ω' , δₑ) with subsList (ss (res s [ δₑ ]ᴿ)) in eqs | etsDec (ts (res s [ δₑ ]ᴿ)) in eqt
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

reexpand-fix : ∀ {Θ Ω''} → (s : St Θ) → {s' : St Θ} {m : s ⟶ s'}
             → reexpand s ≡ just (s' , m)
             → {δ₀ : Subst (Ω s) Ω''} → (δ : Subst (Ω s') Ω'') → (mδ m ⨟ˢ δ) ≐ˢ δ₀
             → Fixing (rig s) δ₀ → Fixing (rig s') δ
reexpand-fix s eq δ tri fx with expandSub (ss (res s))
... | nothing = ⊥just eq
... | just (Ω' , δₑ) with subsList (ss (res s [ δₑ ]ᴿ)) | etsDec (ts (res s [ δₑ ]ᴿ))
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
              → (x : Maybe (List (TyVar (Ω s)))) → (e : etDec (A [ θ s ]ᵛ) ≡ x)
              → {s' : St Θ} {m : s ⟶ s'} {w : Wit s' (Etᶜ A)}
              → solveEt s A x e ≡ solved (s' , m , w) → Princ s s' m (Etᶜ A)
solveEt-princ s A nothing   e ()
solveEt-princ s A (just αs) e refl δ₀ sat h =
  δ₀ , ≐ˢ-refl ,
  pushᵗ-⊩ (etDec-compl (A [ θ s ]ᵛ) e δ₀ (subst (∅ᴴ ⊩Et_) (sym ([⨟]ᵛ A (θ s) δ₀)) sat)) h ,
  (λ fx → fx)

solveEt-fail : ∀ {Θ} → (s : St Θ) → (A : OVType Θ)
             → (x : Maybe (List (TyVar (Ω s)))) → (e : etDec (A [ θ s ]ᵛ) ≡ x)
             → solveEt s A x e ≡ refuted → Refut s (Etᶜ A)
solveEt-fail s A nothing  e eq δ₀ fx h sat =
  etDec-refute (A [ θ s ]ᵛ) e δ₀ (subst (∅ᴴ ⊩Et_) (sym ([⨟]ᵛ A (θ s) δ₀)) sat)
solveEt-fail s A (just _) e ()

solveDisj-princ : ∀ {Θ} → (s : St Θ) → (A : OVType Θ) → (ρ : RExp Θ)
                → (x : Maybe (List (TyVar (Ω s)))) → (e : etDec (A [ θ s ]ᵛ) ≡ x)
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
               → (x : Maybe (List (TyVar (Ω s)))) → (e : etDec (A [ θ s ]ᵛ) ≡ x)
               → solveDisj s A ρ x e ≡ refuted → Refut s (Et∨≾ᵘ A ρ)
solveDisj-fail s A ρ nothing        e ()
solveDisj-fail s A ρ (just [])      e ()
solveDisj-fail s A ρ (just (_ ∷ _)) e ()

-- The demands an expansion for a subtyping constraint is asked about hold at
-- every instance meeting it and the residual

sub-dem : ∀ {Θ Ω''} → (s : St Θ) → (A B : OVType Θ) → (δ₀ : Subst (Ω s) Ω'')
        → (θ s ⨟ˢ δ₀) ⊨[ ∅ᴴ ] (A ≾̂ᵥᶜ B) → ∅ᴴ ⊩ᴿ (res s) [ δ₀ ]
        → ∀ {X Y} → (X , Y) ∈ ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s))
        → ∅ᴴ ∣ X [ δ₀ ]ᵛ <:̂ᵛ Y [ δ₀ ]ᵛ
sub-dem s A B δ₀ sat h (here refl) =
  subst₂ (∅ᴴ ∣_<:̂ᵛ_) (sym ([⨟]ᵛ A (θ s) δ₀)) (sym ([⨟]ᵛ B (θ s) δ₀)) sat
sub-dem s A B δ₀ sat h (there m)   = ⊩ss h m

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
... | just (Ω' , δₑ) with subDec (A [ θ s ]ᵛ [ δₑ ]ᵛ) (B [ θ s ]ᵛ [ δₑ ]ᵛ)
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
    facx = subst (ExpMax δ₀) eqx
                 (expandSub-max ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) δ₀ (sub-dem s A B δ₀ sat h))
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

solve-principal s (Et∨≾ᵘ A ρ) {s'} {m} {w} eq
  with decideᵣ full ∅ᴴ (ρ [ θ s ]ʳ) 𝟏̂ᵣ
... | just p  = solved-princ {s = s} {C = Et∨≾ᵘ A ρ} {s₂ = s'} {m₂ = m} {w₂ = w} eq
                             (id-princ s (Et∨≾ᵘ A ρ))
... | nothing = solveDisj-princ s A ρ _ refl eq

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
      thenRetry-princᵉ _ eq
        (popᵉ-princ s C _ _ _ _ _ _
          (localise-princ {s = s} {s₃} {⟶-⨟ m'' m₃} {C}
            (reexpand-Princ⇑ {s = s} {s''} {m''} {C}
              (λ δ₀ → solve-principal (⇑ᵉˢ s) C e (δ₀ ↑ᵉ)) e₃)))

solve-principal s (⋀ᵒᵖ f) eq
  with threadOps {f = f} (λ s' op → labelled {C = f op} op (solve s' (f op))) ops s in e
... | refuted = ⊥refuted eq
... | stuck   = ⊥stuck eq
... | solved (s₁ , m₁ , ws) with eq
...   | refl = threadOps-princ (λ s' op → labelled {C = f op} op (solve s' (f op)))
                               (λ s' op e' → labelled-princ op (solve s' (f op))
                                               (solve-principal s' (f op)) e') ops s e

-- Refutation: a refused constraint has no solution at an instance keeping the
-- rigids distinct variables and meeting the residual. A rigid binder refuses
-- on an escape, an eternality demand naming the rigid, or a failed retry.

popᵉ-escape : ∀ {Θ Φ} → (s : St Θ) → (C : Constraint (Θ +e))
            → (θ'' : Subst (Θ +e) (Φ +e)) → (R'' : Resid (Φ +e)) → (rg'' : Rig (Φ +e))
            → (m'' : ⇑ᵉˢ s ⟶ st (Φ +e) θ'' R'' rg'')
            → Princ⇑ s (st (Φ +e) θ'' R'' rg'') m'' C
            → (j : EVar (Φ +e)) → sE (mδ m'') (newᵉ {Ω s}) ≡ evar j
            → strSub j (wkˢᵉ {Ω s} ⨟ˢ mδ m'') ≡ nothing
            → Refut s (∀ᵉ C)
popᵉ-escape s C θ'' R'' rg'' m'' ip j eqj eqstr δ₀ fx h sat =
  strSub-escape j (wkˢᵉ {Ω s} ⨟ˢ mδ m'') δ'' (bnd-var (mδ m'') δ'' tri'' eqj)
                δ₀ (bnd-out (mδ m'') δ'' δ₀ tri'') eqstr
  where
    ires = ip δ₀ (⊨-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉ (θ s) δ₀)) C sat) ⊩ᴿ-empty

    δ''   = proj₁ ires
    tri'' = proj₁ (proj₂ ires)

-- An eternality demand that `splitᴿ` refuses names the rigid, so its
-- type is eternal at no instance

atomᵗ-fail : ∀ {Φ Ω''} → (j : EVar (Φ +e)) → (A : OVType (Φ +e)) → atomᵗ j A ≡ nothing
           → (δ : Subst (Φ +e) Ω'') → ¬ (∅ᴴ ⊩Et A [ δ ]ᵛ)
atomᵗ-fail {Φ} j A eq δ et with strᵛ⁺ j A in r
... | just _  = ⊥just (sym eq)
... | nothing = aux (etDec A) refl
  where
    aux : (x : Maybe (List (TyVar (Φ +e)))) → etDec A ≡ x → ⊥
    aux nothing   e = etDec-refute A e δ et
    aux (just αs) e = ⊥just (trans (sym r) (proj₂ (strᵛ⁺-just j A (proj₂ (etDec-str j A e)))))

listᵗ-fail : ∀ {Φ Ω''} → (j : EVar (Φ +e)) → (l : List (OVType (Φ +e))) → listᵗ j l ≡ nothing
           → (δ : Subst (Φ +e) Ω'') → (∀ {A} → A ∈ l → ∅ᴴ ⊩Et A [ δ ]ᵛ) → ⊥
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

splitᴿ-fail : ∀ {Θ Φ Ω''} → (O : Subst Θ (Φ +e)) → (O⁺ : Subst (Θ +e) (Φ +e))
            → (j : EVar (Φ +e)) → (R : Resid (Φ +e))
            → Atomicˢ (ss R)
            → (∀ {A ρ} → (A , ρ) ∈ ds R → Σ[ αs ∈ List (TyVar (Φ +e)) ] (etDec A ≡ just αs))
            → splitᴿ O O⁺ j R ≡ refuted
            → (δ : Subst (Φ +e) Ω'') → ∅ᴴ ⊩ᴿ R [ δ ] → ⊥
splitᴿ-fail O O⁺ j R at et eq δ h
  with listᵗ j (ts R) in e₃ | listˢ j (ss R) in e₄ | listᵈ j (ds R) in e₅
     | listʳ O O⁺ (freeᴴ j R) j (rs R) | listᵉ O O⁺ (freeᴴ j R) j (es R) | outerD? O⁺ (dfs R)
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

rigid-var : ∀ {Θ Ω''} → (s : St Θ) → (C : Constraint (Θ +e)) → {s'' : St (Θ +e)}
          → (m'' : ⇑ᵉˢ s ⟶ s'') → Princ⇑ s s'' m'' C
          → (δ₀ : Subst (Ω s) Ω'') → (θ s ⨟ˢ δ₀) ⊨[ ∅ᴴ ] (∀ᵉ C)
          → Σ[ j ∈ EVar (Ω s'') ] (sE (mδ m'') (newᵉ {Ω s}) ≡ evar j)
rigid-var s C m'' ip δ₀ sat =
  varᵉ-inst (sE (mδ m'') (newᵉ {Ω s})) (proj₁ ires) (≐ᵉ (proj₁ (proj₂ ires)) (newᵉ {Ω s}))
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
  with evar? (sE (mδ m'') (newᵉ {Ω s})) in ev
... | nothing = evar?-var _ (proj₂ (rigid-var s C m'' ip δ₀ sat)) ev
... | just (j , eqj) with strSub j (wkˢᵉ {Ω s} ⨟ˢ mδ m'') in es
                        | splitᴿ (wkˢᵉ {Ω s} ⨟ˢ mδ m'') (mδ m'') j R'' in esp
...   | just _ | solved _ = ⊥solved eq
...   | just _ | stuck    = ⊥stuck-refuted eq
...   | just _ | refuted  =
        splitᴿ-fail (wkˢᵉ {Ω s} ⨟ˢ mδ m'') (mδ m'') j R'' at et esp
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

thenRetry-failᵉ : ∀ {Θ} {s : St Θ} {C : Constraint Θ}
                → (x : Outcome (Σ[ s' ∈ St Θ ] ((s ⟶ s') × Wit s' C)))
                → thenRetry {C = C} x ≡ refuted
                → (∀ {s₁ : St Θ} {m₁ : s ⟶ s₁} {w₁ : Wit s₁ C}
                     → x ≡ solved (s₁ , m₁ , w₁) → Princ s s₁ m₁ C)
                → (x ≡ refuted → Refut s C)
                → Refut s C
thenRetry-failᵉ x eq p r = thenRetry-fail x p r eq

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

-- Demands between type variables are atomic, and decompose

tvars-atomic : ∀ {Ω} → (l : List (TyVar Ω × TyVar Ω)) → Atomicˢ (map (mapᵖ (tvar {Ω})) l)
tvars-atomic {Ω} l m with ∈-map⁻ (mapᵖ (tvar {Ω})) m
... | (α , β) , m₀ , refl = α , β , refl , refl

tvars-dec : ∀ {Ω} → (l : List (TyVar Ω × TyVar Ω))
          → ∀ {A B} → (A , B) ∈ map (mapᵖ (tvar {Ω})) l → Σ[ d ∈ SubDec A B ] (subDec A B ≡ just d)
tvars-dec {Ω} l m with ∈-map⁻ (mapᵖ (tvar {Ω})) m
... | (α , β) , m₀ , refl = _ , refl

-- After it, the subtyping demands of the residual are pairs of type
-- variables

reexpand-atomic : ∀ {Θ} → (s : St Θ) → {s' : St Θ} {m : s ⟶ s'}
                → reexpand s ≡ just (s' , m) → Atomicˢ (ss (res s'))
reexpand-atomic s eq with expandSub (ss (res s))
... | nothing = ⊥just eq
... | just (Ω' , δₑ) with subsList (ss (res s [ δₑ ]ᴿ)) | etsDec (ts (res s [ δₑ ]ᴿ))
...   | nothing | _       = ⊥just eq
...   | just _  | nothing = ⊥just eq
...   | just e  | just t  =
        subst (λ s' → Atomicˢ (ss (res s'))) (cong proj₁ (just-injective eq))
              (tvars-atomic {Ω'} (asubᵥ (atomsOfˢ e)))

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
            (expandSub-max ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) δ₀ (sub-dem s A B δ₀ sat h))
... | just (Ω' , δₑ)
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
    facx = subst (ExpMax δ₀) eqx
                 (expandSub-max ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) δ₀ (sub-dem s A B δ₀ sat h))
    δ    = proj₁ facx
    trix = proj₂ facx
...       | nothing | _       = subsList-exp (ss (res s)) δₑ (λ m → dec (there m)) eqs
  where
    dec = subst (ExpDec ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s))) eqx
                (expandSub-dec ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)))

solve-fail s (ρ ≾̂ᵣᶜ ρ') ()

solve-fail s (ε ≾̂ₑᶜ ε') ()

solve-fail s (Etᶜ A) eq = solveEt-fail s A _ refl eq

solve-fail s (Et∨≾ᵘ A ρ) eq with decideᵣ full ∅ᴴ (ρ [ θ s ]ʳ) 𝟏̂ᵣ
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
      thenRetry-failᵉ _ eq
        (popᵉ-princ s C _ _ _ _ _ _ ipL)
        (popᵉ-fail s C _ _ _ _ _ _ ipL
          (latom (localise (mδ m₃') (res s₃)) (reexpand-atomic s'' e₃))
          (localise-ds (mδ m₃') (res s₃)))
        δ₀ fx h sat
  where
    m₃' = ⟶-⨟ m'' m₃
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
... | just (Ω' , δₑ) with subsList (ss (res s [ δₑ ]ᴿ)) | etsDec (ts (res s [ δₑ ]ᴿ))
...   | nothing | _       = ⊥just eq
...   | just _  | nothing = ⊥just eq
...   | just e  | just t  =
        subst (λ s' → ∀ {A B} → (A , B) ∈ ss (res s') → Σ[ d ∈ SubDec A B ] (subDec A B ≡ just d))
              (cong proj₁ (just-injective eq)) (tvars-dec {Ω'} (asubᵥ (atomsOfˢ e)))
