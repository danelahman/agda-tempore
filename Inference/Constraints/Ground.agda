------------------------------------------------------------------
-- Ground satisfaction of constraints                             --
--                                                                --
-- `θ ⊨ᵍ C` reads: the grounding `θ` makes the constraint `C`     --
-- true in the closed language. Every clause is the *semantic*    --
-- counterpart of the corresponding clause of `_⊨[_]_`: the       --
-- entailments become the closed orders, `_⊩ᴱ_` becomes           --
-- `Eternal`, and the existentials range over closed types and    --
-- grades rather than over open expressions.                       --
--                                                                --
-- The bridge `⊨-ground` grounds a solution-with-residue: a       --
-- grounding of the residual hypotheses turns `σ ⊨[ Q ] C` into   --
-- ground satisfaction along the composite `σ ⨟ᵍ θ`. This is the  --
-- semantics a `GroundSolver` is sound for.                        --
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import Inference.Scopes

module Inference.Constraints.Ground (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

-- The closed types and contexts the interpretations land in; their
-- constructors overlap with the mirrored ones and are disambiguated by
-- the expected type, as in `Inference.Open.Grounding`.

open import Syntax.Contexts S
open import Syntax.Types    S

open import Inference.Open.Grades    S
open import Inference.Open.Types     S
open import Inference.Open.Contexts  S
open import Inference.Open.Subst     S
open import Inference.Open.Hyps      S
open import Inference.Open.Grounding S

open import Inference.Constraints.Syntax       S
open import Inference.Constraints.Satisfaction S

--------------------------------------------------------------
-- Ground satisfaction                                       --
--------------------------------------------------------------

infix 4 _⊨ᵍ_

_⊨ᵍ_ : ∀ {Θ} → Grounding Θ → Constraint Θ → Set
θ ⊨ᵍ ⊤̂          = ⊤
θ ⊨ᵍ ⊥̂          = ⊥
θ ⊨ᵍ (C ∧̂ D)    = θ ⊨ᵍ C × θ ⊨ᵍ D
θ ⊨ᵍ (A ≐ᵥ B)   = ⟦ A ⟧ᵛ θ ≡ ⟦ B ⟧ᵛ θ
θ ⊨ᵍ (ρ ≾̂ᵣᶜ ρ') = ⟦ ρ ⟧ʳ θ ≾ᵣ ⟦ ρ' ⟧ʳ θ
θ ⊨ᵍ (ε ≾̂ₑᶜ ε') = ⟦ ε ⟧ᵉ θ ≾ₑ ⟦ ε' ⟧ᵉ θ
θ ⊨ᵍ Etᶜ A      = Eternal (⟦ A ⟧ᵛ θ)
θ ⊨ᵍ Et∨≾ᵘ A ρ  = Eternal (⟦ A ⟧ᵛ θ) ⊎ (⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)
θ ⊨ᵍ (∃ᵗ C)     = Σ[ A ∈ VType ] ((θ ,ᵍᵗ A) ⊨ᵍ C)
θ ⊨ᵍ (∃ʳ C)     = Σ[ ρ ∈ R ]     ((θ ,ᵍʳ ρ) ⊨ᵍ C)
θ ⊨ᵍ (∃ᵉ C)     = Σ[ ε ∈ E ]     ((θ ,ᵍᵉ ε) ⊨ᵍ C)
θ ⊨ᵍ (∀ᵉ C)     = (ε : E) → (θ ,ᵍᵉ ε) ⊨ᵍ C
θ ⊨ᵍ ⋀ᵒᵖ f      = (op : Op) → θ ⊨ᵍ f op

--------------------------------------------------------------
-- Pointwise equality of groundings                          --
--                                                           --
-- Groundings are records of functions, and the binder cases  --
-- below build two groundings that agree only pointwise; the  --
-- mirror of `_≐ˢ_` avoids appealing to extensionality.       --
--------------------------------------------------------------

infix 20 _≐ᵍ_

record _≐ᵍ_ {Θ : Scope} (θ θ' : Grounding Θ) : Set where
  constructor mk≐ᵍ
  field
    ≐ᵍᵗ : (α : TyVar Θ) → gTy θ α ≡ gTy θ' α
    ≐ᵍʳ : (i : RVar Θ) → gR θ i ≡ gR θ' i
    ≐ᵍᵉ : (i : EVar Θ) → gE θ i ≡ gE θ' i

open _≐ᵍ_ public

-- The interpretations respect pointwise equality

⟦≐⟧ᵉ : ∀ {Θ} {θ θ' : Grounding Θ} → θ ≐ᵍ θ' → (ε : EExp Θ)
     → ⟦ ε ⟧ᵉ θ ≡ ⟦ ε ⟧ᵉ θ'
⟦≐⟧ᵉ p (evar i)   = ≐ᵍᵉ p i
⟦≐⟧ᵉ p (econst ε) = refl
⟦≐⟧ᵉ p (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (⟦≐⟧ᵉ p ε) (⟦≐⟧ᵉ p ε')

⟦≐⟧ʳ : ∀ {Θ} {θ θ' : Grounding Θ} → θ ≐ᵍ θ' → (ρ : RExp Θ)
     → ⟦ ρ ⟧ʳ θ ≡ ⟦ ρ ⟧ʳ θ'
⟦≐⟧ʳ p (rvar i)   = ≐ᵍʳ p i
⟦≐⟧ʳ p (rconst ρ) = refl
⟦≐⟧ʳ p (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (⟦≐⟧ʳ p ρ) (⟦≐⟧ʳ p ρ')
⟦≐⟧ʳ p ∣ ε ∣̂ᵉ     = cong mapᵉ (⟦≐⟧ᵉ p ε)

mutual

  ⟦≐⟧ᵛ : ∀ {Θ} {θ θ' : Grounding Θ} → θ ≐ᵍ θ' → (A : OVType Θ)
       → ⟦ A ⟧ᵛ θ ≡ ⟦ A ⟧ᵛ θ'
  ⟦≐⟧ᵛ p (tvar α)  = ≐ᵍᵗ p α
  ⟦≐⟧ᵛ p (Base b)  = refl
  ⟦≐⟧ᵛ p Unit      = refl
  ⟦≐⟧ᵛ p Bool      = refl
  ⟦≐⟧ᵛ p (A |×| B) = cong₂ _|×|_ (⟦≐⟧ᵛ p A) (⟦≐⟧ᵛ p B)
  ⟦≐⟧ᵛ p Empty     = refl
  ⟦≐⟧ᵛ p (A ⇒ C)   = cong₂ _⇒_ (⟦≐⟧ᵛ p A) (⟦≐⟧ᶜ p C)
  ⟦≐⟧ᵛ p ([ ρ ] A) = cong₂ [_]_ (⟦≐⟧ʳ p ρ) (⟦≐⟧ᵛ p A)

  ⟦≐⟧ᶜ : ∀ {Θ} {θ θ' : Grounding Θ} → θ ≐ᵍ θ' → (C : OCType Θ)
       → ⟦ C ⟧ᶜ θ ≡ ⟦ C ⟧ᶜ θ'
  ⟦≐⟧ᶜ p (A ‼ ε) = cong₂ _‼_ (⟦≐⟧ᵛ p A) (⟦≐⟧ᵉ p ε)

-- Compatibility with the three grounding extensions

≐ᵍ-,ᵍᵗ : ∀ {Θ} {θ θ' : Grounding Θ} → θ ≐ᵍ θ' → (A : VType)
       → (θ ,ᵍᵗ A) ≐ᵍ (θ' ,ᵍᵗ A)
≐ᵍ-,ᵍᵗ p A = mk≐ᵍ (λ { zero → refl ; (suc α) → ≐ᵍᵗ p α }) (≐ᵍʳ p) (≐ᵍᵉ p)

≐ᵍ-,ᵍʳ : ∀ {Θ} {θ θ' : Grounding Θ} → θ ≐ᵍ θ' → (ρ : R)
       → (θ ,ᵍʳ ρ) ≐ᵍ (θ' ,ᵍʳ ρ)
≐ᵍ-,ᵍʳ p ρ = mk≐ᵍ (≐ᵍᵗ p) (λ { zero → refl ; (suc i) → ≐ᵍʳ p i }) (≐ᵍᵉ p)

≐ᵍ-,ᵍᵉ : ∀ {Θ} {θ θ' : Grounding Θ} → θ ≐ᵍ θ' → (ε : E)
       → (θ ,ᵍᵉ ε) ≐ᵍ (θ' ,ᵍᵉ ε)
≐ᵍ-,ᵍᵉ p ε = mk≐ᵍ (≐ᵍᵗ p) (≐ᵍʳ p) (λ { zero → refl ; (suc i) → ≐ᵍᵉ p i })

--------------------------------------------------------------
-- Ground satisfaction respects pointwise equality           --
--------------------------------------------------------------

⊨ᵍ-resp : ∀ {Θ} {θ θ' : Grounding Θ}
        → θ ≐ᵍ θ' → (C : Constraint Θ) → θ ⊨ᵍ C → θ' ⊨ᵍ C
⊨ᵍ-resp p ⊤̂           s        = s
⊨ᵍ-resp p ⊥̂           s        = s
⊨ᵍ-resp p (C ∧̂ D)     (s , t)  = ⊨ᵍ-resp p C s , ⊨ᵍ-resp p D t
⊨ᵍ-resp p (A ≐ᵥ B)    s        =
  trans (sym (⟦≐⟧ᵛ p A)) (trans s (⟦≐⟧ᵛ p B))
⊨ᵍ-resp p (ρ ≾̂ᵣᶜ ρ')  s        = subst₂ _≾ᵣ_ (⟦≐⟧ʳ p ρ) (⟦≐⟧ʳ p ρ') s
⊨ᵍ-resp p (ε ≾̂ₑᶜ ε')  s        = subst₂ _≾ₑ_ (⟦≐⟧ᵉ p ε) (⟦≐⟧ᵉ p ε') s
⊨ᵍ-resp p (Etᶜ A)     s        = subst Eternal (⟦≐⟧ᵛ p A) s
⊨ᵍ-resp p (Et∨≾ᵘ A ρ) (inj₁ s) = inj₁ (subst Eternal (⟦≐⟧ᵛ p A) s)
⊨ᵍ-resp p (Et∨≾ᵘ A ρ) (inj₂ s) = inj₂ (subst (_≾ᵣ uᵣ) (⟦≐⟧ʳ p ρ) s)
⊨ᵍ-resp p (∃ᵗ C)      (A , s)  = A , ⊨ᵍ-resp (≐ᵍ-,ᵍᵗ p A) C s
⊨ᵍ-resp p (∃ʳ C)      (ρ , s)  = ρ , ⊨ᵍ-resp (≐ᵍ-,ᵍʳ p ρ) C s
⊨ᵍ-resp p (∃ᵉ C)      (ε , s)  = ε , ⊨ᵍ-resp (≐ᵍ-,ᵍᵉ p ε) C s
⊨ᵍ-resp p (∀ᵉ C)      s        = λ ε → ⊨ᵍ-resp (≐ᵍ-,ᵍᵉ p ε) C (s ε)
⊨ᵍ-resp p (⋀ᵒᵖ f)     s        = λ op → ⊨ᵍ-resp p (f op) (s op)

--------------------------------------------------------------
-- Composing a substitution with a grounding                 --
--------------------------------------------------------------

infixl 25 _⨟ᵍ_

_⨟ᵍ_ : ∀ {Θ Θ'} → Subst Θ Θ' → Grounding Θ' → Grounding Θ
σ ⨟ᵍ θ = grounding (λ α → ⟦ sTy σ α ⟧ᵛ θ)
                   (λ i → ⟦ sR  σ i ⟧ʳ θ)
                   (λ i → ⟦ sE  σ i ⟧ᵉ θ)

-- Substituting and then grounding is grounding along the composite

⟦⟧-⨟ᵍ-e : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (θ : Grounding Θ') → (ε : EExp Θ)
        → ⟦ ε [ σ ]ᵉ ⟧ᵉ θ ≡ ⟦ ε ⟧ᵉ (σ ⨟ᵍ θ)
⟦⟧-⨟ᵍ-e σ θ (evar i)   = refl
⟦⟧-⨟ᵍ-e σ θ (econst ε) = refl
⟦⟧-⨟ᵍ-e σ θ (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (⟦⟧-⨟ᵍ-e σ θ ε) (⟦⟧-⨟ᵍ-e σ θ ε')

⟦⟧-⨟ᵍ-r : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (θ : Grounding Θ') → (ρ : RExp Θ)
        → ⟦ ρ [ σ ]ʳ ⟧ʳ θ ≡ ⟦ ρ ⟧ʳ (σ ⨟ᵍ θ)
⟦⟧-⨟ᵍ-r σ θ (rvar i)   = refl
⟦⟧-⨟ᵍ-r σ θ (rconst ρ) = refl
⟦⟧-⨟ᵍ-r σ θ (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (⟦⟧-⨟ᵍ-r σ θ ρ) (⟦⟧-⨟ᵍ-r σ θ ρ')
⟦⟧-⨟ᵍ-r σ θ ∣ ε ∣̂ᵉ     = cong mapᵉ (⟦⟧-⨟ᵍ-e σ θ ε)

mutual

  ⟦⟧-⨟ᵍ-v : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (θ : Grounding Θ') → (A : OVType Θ)
          → ⟦ A [ σ ]ᵛ ⟧ᵛ θ ≡ ⟦ A ⟧ᵛ (σ ⨟ᵍ θ)
  ⟦⟧-⨟ᵍ-v σ θ (tvar α)  = refl
  ⟦⟧-⨟ᵍ-v σ θ (Base b)  = refl
  ⟦⟧-⨟ᵍ-v σ θ Unit      = refl
  ⟦⟧-⨟ᵍ-v σ θ Bool      = refl
  ⟦⟧-⨟ᵍ-v σ θ (A |×| B) = cong₂ _|×|_ (⟦⟧-⨟ᵍ-v σ θ A) (⟦⟧-⨟ᵍ-v σ θ B)
  ⟦⟧-⨟ᵍ-v σ θ Empty     = refl
  ⟦⟧-⨟ᵍ-v σ θ (A ⇒ C)   = cong₂ _⇒_ (⟦⟧-⨟ᵍ-v σ θ A) (⟦⟧-⨟ᵍ-c σ θ C)
  ⟦⟧-⨟ᵍ-v σ θ ([ ρ ] A) = cong₂ [_]_ (⟦⟧-⨟ᵍ-r σ θ ρ) (⟦⟧-⨟ᵍ-v σ θ A)

  ⟦⟧-⨟ᵍ-c : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (θ : Grounding Θ') → (C : OCType Θ)
          → ⟦ C [ σ ]ᶜ ⟧ᶜ θ ≡ ⟦ C ⟧ᶜ (σ ⨟ᵍ θ)
  ⟦⟧-⨟ᵍ-c σ θ (A ‼ ε) = cong₂ _‼_ (⟦⟧-⨟ᵍ-v σ θ A) (⟦⟧-⨟ᵍ-e σ θ ε)

⟦⟧-⨟ᵍ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (θ : Grounding Θ') → (Γ : OCtx Θ n)
          → ⟦ Γ [ σ ]ᶜᵗˣ ⟧ᶜᵗˣ θ ≡ ⟦ Γ ⟧ᶜᵗˣ (σ ⨟ᵍ θ)
⟦⟧-⨟ᵍ-ctx σ θ []        = refl
⟦⟧-⨟ᵍ-ctx σ θ (Γ ∷ A)   = cong₂ _∷_ (⟦⟧-⨟ᵍ-ctx σ θ Γ) (⟦⟧-⨟ᵍ-v σ θ A)
⟦⟧-⨟ᵍ-ctx σ θ (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (⟦⟧-⨟ᵍ-ctx σ θ Γ) (⟦⟧-⨟ᵍ-r σ θ ρ)
⟦⟧-⨟ᵍ-ctx σ θ (Γ ᴱ̂)     = cong _ᴱ (⟦⟧-⨟ᵍ-ctx σ θ Γ)

-- How the composite interacts with the formers the binder cases build

⨟ᵍ-,ᵗ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B : OVType Θ') → (θ : Grounding Θ')
      → ((σ ,ᵗ B) ⨟ᵍ θ) ≐ᵍ ((σ ⨟ᵍ θ) ,ᵍᵗ ⟦ B ⟧ᵛ θ)
⨟ᵍ-,ᵗ σ B θ = mk≐ᵍ (λ { zero → refl ; (suc α) → refl }) (λ i → refl) (λ i → refl)

⨟ᵍ-,ʳ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ρ : RExp Θ') → (θ : Grounding Θ')
      → ((σ ,ʳ ρ) ⨟ᵍ θ) ≐ᵍ ((σ ⨟ᵍ θ) ,ᵍʳ ⟦ ρ ⟧ʳ θ)
⨟ᵍ-,ʳ σ ρ θ = mk≐ᵍ (λ α → refl) (λ { zero → refl ; (suc i) → refl }) (λ i → refl)

⨟ᵍ-,ᵉ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ε : EExp Θ') → (θ : Grounding Θ')
      → ((σ ,ᵉ ε) ⨟ᵍ θ) ≐ᵍ ((σ ⨟ᵍ θ) ,ᵍᵉ ⟦ ε ⟧ᵉ θ)
⨟ᵍ-,ᵉ σ ε θ = mk≐ᵍ (λ α → refl) (λ i → refl) (λ { zero → refl ; (suc i) → refl })

-- The rigid quantifier: a lift composed with an extended grounding

⨟ᵍ-↑ᵉ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (θ : Grounding Θ') → (ε₀ : E)
      → ((σ ↑ᵉ) ⨟ᵍ (θ ,ᵍᵉ ε₀)) ≐ᵍ ((σ ⨟ᵍ θ) ,ᵍᵉ ε₀)
⨟ᵍ-↑ᵉ σ θ ε₀ = mk≐ᵍ (λ α → ground-wkᵉ-v (sTy σ α))
                    (λ i → ground-wkᵉ-r (sR σ i))
                    (λ { zero → refl ; (suc i) → ground-wkᵉ-e (sE σ i) })

-- The identity substitution is the unit of the composite

idˢ-⨟ᵍ : ∀ {Θ} → (θ : Grounding Θ) → (idˢ ⨟ᵍ θ) ≐ᵍ θ
idˢ-⨟ᵍ θ = mk≐ᵍ (λ α → refl) (λ i → refl) (λ i → refl)

--------------------------------------------------------------
-- The bridge                                                --
--                                                           --
-- A grounding of the residual hypotheses turns a solution     --
-- with residue into a ground solution along the composite.    --
--------------------------------------------------------------

⊨-ground : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
         → (θ : Grounding Θ') → θ ⊨ᴴ Q
         → (C : Constraint Θ) → σ ⊨[ Q ] C → (σ ⨟ᵍ θ) ⊨ᵍ C
⊨-ground θ h ⊤̂       s       = s
⊨-ground θ h ⊥̂       s       = s
⊨-ground θ h (C ∧̂ D) (s , t) = ⊨-ground θ h C s , ⊨-ground θ h D t
⊨-ground {σ = σ} θ h (A ≐ᵥ B) s =
  trans (sym (⟦⟧-⨟ᵍ-v σ θ A))
        (trans (cong (λ X → ⟦ X ⟧ᵛ θ) s) (⟦⟧-⨟ᵍ-v σ θ B))
⊨-ground {σ = σ} θ h (ρ ≾̂ᵣᶜ ρ') s =
  subst₂ _≾ᵣ_ (⟦⟧-⨟ᵍ-r σ θ ρ) (⟦⟧-⨟ᵍ-r σ θ ρ') (ground-≾ᵣ h s)
⊨-ground {σ = σ} θ h (ε ≾̂ₑᶜ ε') s =
  subst₂ _≾ₑ_ (⟦⟧-⨟ᵍ-e σ θ ε) (⟦⟧-⨟ᵍ-e σ θ ε') (ground-≾ₑ h s)
⊨-ground {σ = σ} θ h (Etᶜ A) s =
  subst Eternal (⟦⟧-⨟ᵍ-v σ θ A) (ground-Et h s)
⊨-ground {σ = σ} θ h (Et∨≾ᵘ A ρ) (inj₁ s) =
  inj₁ (subst Eternal (⟦⟧-⨟ᵍ-v σ θ A) (ground-Et h s))
⊨-ground {σ = σ} θ h (Et∨≾ᵘ A ρ) (inj₂ s) =
  inj₂ (subst (_≾ᵣ uᵣ) (⟦⟧-⨟ᵍ-r σ θ ρ) (ground-≾ᵣ h s))
⊨-ground {σ = σ} θ h (∃ᵗ C) (B , s) =
  ⟦ B ⟧ᵛ θ , ⊨ᵍ-resp (⨟ᵍ-,ᵗ σ B θ) C (⊨-ground θ h C s)
⊨-ground {σ = σ} θ h (∃ʳ C) (ρ , s) =
  ⟦ ρ ⟧ʳ θ , ⊨ᵍ-resp (⨟ᵍ-,ʳ σ ρ θ) C (⊨-ground θ h C s)
⊨-ground {σ = σ} θ h (∃ᵉ C) (ε , s) =
  ⟦ ε ⟧ᵉ θ , ⊨ᵍ-resp (⨟ᵍ-,ᵉ σ ε θ) C (⊨-ground θ h C s)
⊨-ground {σ = σ} θ h (∀ᵉ C) s = λ ε →
  ⊨ᵍ-resp (⨟ᵍ-↑ᵉ σ θ ε) C (⊨-ground (θ ,ᵍᵉ ε) (⊨ᴴ-wkᵉ-ground h) C s)
⊨-ground θ h (⋀ᵒᵖ f) s = λ op → ⊨-ground θ h (f op) (s op)

-- The closed instance: a solution that substitutes nothing

⊨ᵍ-of-idˢ : ∀ {Θ} {θ : Grounding Θ} {Q : Hyps Θ}
          → θ ⊨ᴴ Q → (C : Constraint Θ) → idˢ ⊨[ Q ] C → θ ⊨ᵍ C
⊨ᵍ-of-idˢ {θ = θ} h C s = ⊨ᵍ-resp (idˢ-⨟ᵍ θ) C (⊨-ground θ h C s)
