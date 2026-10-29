------------------------------------------------------------------
-- Declarative instances and the meaning of open types          --
--                                                              --
-- A declarative instance `σ : DInst Θ` sends the type          --
-- variables of `Θ` to arbitrary closed value types and its     --
-- resource-grade and effect-grade variables to arbitrary       --
-- grades. Open types and contexts are interpreted at `σ`       --
-- structurally (`⟦_⟧ᵛ`, `⟦_⟧ᶜ`, `⟦_⟧ᶜᵗˣ`): a variable is       --
-- looked up in `σ`, each former goes to its closed             --
-- counterpart, and a grade expression is evaluated in the      --
-- carrier (`⟦_⟧ʳ`, `⟦_⟧ᵉ`). A handler type, which has no       --
-- closed counterpart, means the fixed non-eternal type         --
-- `handlerᴰ`.                                                  --
--                                                              --
-- Closed open syntax means its interpretation at the empty     --
-- instance (`⌞_⌟`), on grades the value; the embedding of a    --
-- closed type, each grade a constant, is a section of it       --
-- (`⌜_⌝ᵛ`, `⌞⌜_⌝⌟ᵛ`). A closed instance `δ : Subst Θ ∅ˢ`       --
-- determines the declarative instance `⌞ δ ⌟ˢ`, and every      --
-- declarative instance `σ` is pointwise the one determined by  --
-- `⌜ σ ⌝ˢ`, which sends each variable to a constant            --
-- (`⌞⌜_⌝ˢ⌟`).                                                  --
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Vec.Base using (Vec) renaming (map to mapᵛ; [] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Unit using (⊤; tt)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module Bridge.Instantiation.Types (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Language.Types                 S
open import ClosedCalculus.Syntax.Contexts S

open import OpenCalculus.Syntax.Grades   S
open import OpenCalculus.Syntax.Types    S
open import OpenCalculus.Syntax.Contexts S
open import OpenCalculus.Syntax.Subst    S
open import OpenCalculus.Hypotheses.Quantified S using (_+eⁿ_; _,ᵉⁿ_)

------------------------------------------------------------------------
-- Declarative instances

record DInst (Θ : Scope) : Set where
  constructor dinst
  field
    ty  : TyVar Θ → VType                  -- type variables to closed types
    res : RVar Θ → R                       -- resource-grade variables
    eff : EVar Θ → E                       -- effect-grade variables

open DInst public

-- Extension by an effect grade for the newly bound variable

infixl 30 _,ᵉᴰ_

_,ᵉᴰ_ : ∀ {Θ} → DInst Θ → E → DInst (Θ +e)
σ ,ᵉᴰ c = dinst (ty σ) (res σ) (λ { zero → c ; (suc i) → eff σ i })

------------------------------------------------------------------------
-- Interpretation

-- The meaning of every handler type. Instantiation covers the terms
-- whose handlers are second-class (`SecondClassᶜ`), where no handler is
-- a value; the type is not eternal, as no handler type is.

handlerᴰ : VType
handlerᴰ = Unit ⇒ Unit ‼ uₑ

⟦_⟧ᵉ : ∀ {Θ} → EExp Θ → DInst Θ → E
⟦ evar i ⟧ᵉ    σ = eff σ i
⟦ econst c ⟧ᵉ  σ = c
⟦ ε ·̂ₑ ε' ⟧ᵉ   σ = ⟦ ε ⟧ᵉ σ ·ₑ ⟦ ε' ⟧ᵉ σ
⟦ ε ⊔̂ₑ ε' ⟧ᵉ   σ = ⟦ ε ⟧ᵉ σ ⊔ₑ ⟦ ε' ⟧ᵉ σ

⟦_⟧ʳ : ∀ {Θ} → RExp Θ → DInst Θ → R
⟦ rvar i ⟧ʳ    σ = res σ i
⟦ rconst c ⟧ʳ  σ = c
⟦ ρ ·̂ᵣ ρ' ⟧ʳ   σ = ⟦ ρ ⟧ʳ σ ·ᵣ ⟦ ρ' ⟧ʳ σ
⟦ ρ ⊔̂ᵣ ρ' ⟧ʳ   σ = ⟦ ρ ⟧ʳ σ ⊔ᵣ ⟦ ρ' ⟧ʳ σ
⟦ ∣ ε ∣̂ᵉ ⟧ʳ    σ = mapᵉ (⟦ ε ⟧ᵉ σ)

mutual

  ⟦_⟧ᵛ : ∀ {Θ} → OVType Θ → DInst Θ → VType
  ⟦ tvar α ⟧ᵛ   σ = ty σ α
  ⟦ Base b ⟧ᵛ   σ = Base b
  ⟦ Unit ⟧ᵛ     σ = Unit
  ⟦ Bool ⟧ᵛ     σ = Bool
  ⟦ Nat ⟧ᵛ      σ = Nat
  ⟦ A |×| B ⟧ᵛ  σ = ⟦ A ⟧ᵛ σ |×| ⟦ B ⟧ᵛ σ
  ⟦ A |+| B ⟧ᵛ  σ = ⟦ A ⟧ᵛ σ |+| ⟦ B ⟧ᵛ σ
  ⟦ |List| A ⟧ᵛ σ = |List| (⟦ A ⟧ᵛ σ)
  ⟦ Empty ⟧ᵛ    σ = Empty
  ⟦ A ⇒ C ⟧ᵛ    σ = ⟦ A ⟧ᵛ σ ⇒ ⟦ C ⟧ᶜ σ
  ⟦ C ⇛ D ⟧ᵛ    σ = handlerᴰ
  ⟦ [ ρ ] A ⟧ᵛ  σ = [ ⟦ ρ ⟧ʳ σ ] ⟦ A ⟧ᵛ σ

  ⟦_⟧ᶜ : ∀ {Θ} → OCType Θ → DInst Θ → CType
  ⟦ A ‼ ε ⟧ᶜ σ = ⟦ A ⟧ᵛ σ ‼ ⟦ ε ⟧ᵉ σ

⟦_⟧ᶜᵗˣ : ∀ {Θ n} → OCtx Θ n → DInst Θ → Ctx
⟦ [] ⟧ᶜᵗˣ      σ = []
⟦ Γ ∷ A ⟧ᶜᵗˣ   σ = ⟦ Γ ⟧ᶜᵗˣ σ ∷ ⟦ A ⟧ᵛ σ
⟦ Γ ⟨ ρ ⟩ ⟧ᶜᵗˣ σ = ⟦ Γ ⟧ᶜᵗˣ σ ⟨ ⟦ ρ ⟧ʳ σ ⟩

-- Ground types mean their closed images

⟦⌜_⌝ᵍ⟧ : ∀ {Θ} → (g : GType) → (σ : DInst Θ) → ⟦ ⌜ g ⌝ᵍ ⟧ᵛ σ ≡ type-of-gtype g
⟦⌜ Base b ⌝ᵍ⟧ σ    = refl
⟦⌜ Unit ⌝ᵍ⟧ σ      = refl
⟦⌜ Bool ⌝ᵍ⟧ σ      = refl
⟦⌜ Nat ⌝ᵍ⟧ σ       = refl
⟦⌜ Empty ⌝ᵍ⟧ σ     = refl
⟦⌜ A |×|ᵍ B ⌝ᵍ⟧ σ  = cong₂ _|×|_ (⟦⌜ A ⌝ᵍ⟧ σ) (⟦⌜ B ⌝ᵍ⟧ σ)
⟦⌜ A |+|ᵍ B ⌝ᵍ⟧ σ  = cong₂ _|+|_ (⟦⌜ A ⌝ᵍ⟧ σ) (⟦⌜ B ⌝ᵍ⟧ σ)
⟦⌜ |List|ᵍ A ⌝ᵍ⟧ σ = cong |List| (⟦⌜ A ⌝ᵍ⟧ σ)
⟦⌜ [ ρ ]ᵍ A ⌝ᵍ⟧ σ  = cong ([ ρ ]_) (⟦⌜ A ⌝ᵍ⟧ σ)

------------------------------------------------------------------------
-- Types and contexts in which no handler type occurs: those whose
-- meaning is their closed counterpart

mutual

  NoHandlerTypeᵛ : ∀ {Θ} → OVType Θ → Set
  NoHandlerTypeᵛ (A |×| B)  = NoHandlerTypeᵛ A × NoHandlerTypeᵛ B
  NoHandlerTypeᵛ (A |+| B)  = NoHandlerTypeᵛ A × NoHandlerTypeᵛ B
  NoHandlerTypeᵛ (|List| A) = NoHandlerTypeᵛ A
  NoHandlerTypeᵛ (A ⇒ C)    = NoHandlerTypeᵛ A × NoHandlerTypeᶜ C
  NoHandlerTypeᵛ (C ⇛ D)    = ⊥
  NoHandlerTypeᵛ ([ ρ ] A)  = NoHandlerTypeᵛ A
  NoHandlerTypeᵛ _          = ⊤

  NoHandlerTypeᶜ : ∀ {Θ} → OCType Θ → Set
  NoHandlerTypeᶜ (A ‼ ε) = NoHandlerTypeᵛ A

NoHandlerTypeᶜᵗˣ : ∀ {Θ n} → OCtx Θ n → Set
NoHandlerTypeᶜᵗˣ []        = ⊤
NoHandlerTypeᶜᵗˣ (Γ ∷ A)   = NoHandlerTypeᶜᵗˣ Γ × NoHandlerTypeᵛ A
NoHandlerTypeᶜᵗˣ (Γ ⟨ ρ ⟩) = NoHandlerTypeᶜᵗˣ Γ

-- the type of a variable of such a context, and a ground type, have no
-- handler type

∈̂-noHandler : ∀ {Θ n A ρ} {Γ : OCtx Θ n} → NoHandlerTypeᶜᵗˣ Γ → A ∈̂[ ρ ] Γ
            → NoHandlerTypeᵛ A
∈̂-noHandler (h , k) Hd        = k
∈̂-noHandler (h , k) (Tl-∷ x)  = ∈̂-noHandler h x
∈̂-noHandler h       (Tl-⟨⟩ x) = ∈̂-noHandler h x

⌜⌝ᵍ-noHandler : ∀ {Θ} → (g : GType) → NoHandlerTypeᵛ {Θ} ⌜ g ⌝ᵍ
⌜⌝ᵍ-noHandler (Base b)    = tt
⌜⌝ᵍ-noHandler Unit        = tt
⌜⌝ᵍ-noHandler Bool        = tt
⌜⌝ᵍ-noHandler Nat         = tt
⌜⌝ᵍ-noHandler Empty       = tt
⌜⌝ᵍ-noHandler (A |×|ᵍ B)  = ⌜⌝ᵍ-noHandler A , ⌜⌝ᵍ-noHandler B
⌜⌝ᵍ-noHandler (A |+|ᵍ B)  = ⌜⌝ᵍ-noHandler A , ⌜⌝ᵍ-noHandler B
⌜⌝ᵍ-noHandler (|List|ᵍ A) = ⌜⌝ᵍ-noHandler A
⌜⌝ᵍ-noHandler ([ ρ ]ᵍ A)  = ⌜⌝ᵍ-noHandler A

------------------------------------------------------------------------
-- Weakening by an effect-grade variable, at an extended instance

module _ {Θ} (σ : DInst Θ) (c : E) where

  ⟦wkᵉ⟧ᵉ : (ε : EExp Θ) → ⟦ wkᵉ-e ε ⟧ᵉ (σ ,ᵉᴰ c) ≡ ⟦ ε ⟧ᵉ σ
  ⟦wkᵉ⟧ᵉ (evar i)   = refl
  ⟦wkᵉ⟧ᵉ (econst e) = refl
  ⟦wkᵉ⟧ᵉ (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (⟦wkᵉ⟧ᵉ ε) (⟦wkᵉ⟧ᵉ ε')
  ⟦wkᵉ⟧ᵉ (ε ⊔̂ₑ ε')  = cong₂ _⊔ₑ_ (⟦wkᵉ⟧ᵉ ε) (⟦wkᵉ⟧ᵉ ε')

  ⟦wkᵉ⟧ʳ : (ρ : RExp Θ) → ⟦ wkᵉ-r ρ ⟧ʳ (σ ,ᵉᴰ c) ≡ ⟦ ρ ⟧ʳ σ
  ⟦wkᵉ⟧ʳ (rvar i)   = refl
  ⟦wkᵉ⟧ʳ (rconst r) = refl
  ⟦wkᵉ⟧ʳ (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (⟦wkᵉ⟧ʳ ρ) (⟦wkᵉ⟧ʳ ρ')
  ⟦wkᵉ⟧ʳ (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔ᵣ_ (⟦wkᵉ⟧ʳ ρ) (⟦wkᵉ⟧ʳ ρ')
  ⟦wkᵉ⟧ʳ ∣ ε ∣̂ᵉ     = cong mapᵉ (⟦wkᵉ⟧ᵉ ε)

  mutual

    ⟦wkᵉ⟧ᵛ : (A : OVType Θ) → ⟦ wkᵉ-v A ⟧ᵛ (σ ,ᵉᴰ c) ≡ ⟦ A ⟧ᵛ σ
    ⟦wkᵉ⟧ᵛ (tvar α)   = refl
    ⟦wkᵉ⟧ᵛ (Base b)   = refl
    ⟦wkᵉ⟧ᵛ Unit       = refl
    ⟦wkᵉ⟧ᵛ Bool       = refl
    ⟦wkᵉ⟧ᵛ Nat        = refl
    ⟦wkᵉ⟧ᵛ (A |×| B)  = cong₂ _|×|_ (⟦wkᵉ⟧ᵛ A) (⟦wkᵉ⟧ᵛ B)
    ⟦wkᵉ⟧ᵛ (A |+| B)  = cong₂ _|+|_ (⟦wkᵉ⟧ᵛ A) (⟦wkᵉ⟧ᵛ B)
    ⟦wkᵉ⟧ᵛ (|List| A) = cong |List| (⟦wkᵉ⟧ᵛ A)
    ⟦wkᵉ⟧ᵛ Empty      = refl
    ⟦wkᵉ⟧ᵛ (A ⇒ C)    = cong₂ _⇒_ (⟦wkᵉ⟧ᵛ A) (⟦wkᵉ⟧ᶜ C)
    ⟦wkᵉ⟧ᵛ (C ⇛ D)    = refl
    ⟦wkᵉ⟧ᵛ ([ ρ ] A)  = cong₂ [_]_ (⟦wkᵉ⟧ʳ ρ) (⟦wkᵉ⟧ᵛ A)

    ⟦wkᵉ⟧ᶜ : (C : OCType Θ) → ⟦ wkᵉ-c C ⟧ᶜ (σ ,ᵉᴰ c) ≡ ⟦ C ⟧ᶜ σ
    ⟦wkᵉ⟧ᶜ (A ‼ ε) = cong₂ _‼_ (⟦wkᵉ⟧ᵛ A) (⟦wkᵉ⟧ᵉ ε)

  ⟦wkᵉ⟧ᶜᵗˣ : ∀ {n} → (Γ : OCtx Θ n) → ⟦ wkᵉ-ctx Γ ⟧ᶜᵗˣ (σ ,ᵉᴰ c) ≡ ⟦ Γ ⟧ᶜᵗˣ σ
  ⟦wkᵉ⟧ᶜᵗˣ []        = refl
  ⟦wkᵉ⟧ᶜᵗˣ (Γ ∷ A)   = cong₂ _∷_ (⟦wkᵉ⟧ᶜᵗˣ Γ) (⟦wkᵉ⟧ᵛ A)
  ⟦wkᵉ⟧ᶜᵗˣ (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (⟦wkᵉ⟧ᶜᵗˣ Γ) (⟦wkᵉ⟧ʳ ρ)

------------------------------------------------------------------------
-- Pointwise equal instances interpret grades alike

infix 4 _≗ᴰ_

record _≗ᴰ_ {Θ} (σ σ' : DInst Θ) : Set where
  constructor mk≗ᴰ
  field
    ty≗  : ∀ α → ty σ α ≡ ty σ' α
    res≗ : ∀ i → res σ i ≡ res σ' i
    eff≗ : ∀ i → eff σ i ≡ eff σ' i

open _≗ᴰ_ public

module _ {Θ} {σ σ' : DInst Θ} (p : σ ≗ᴰ σ') where

  ⟦≗⟧ᵉ : (ε : EExp Θ) → ⟦ ε ⟧ᵉ σ ≡ ⟦ ε ⟧ᵉ σ'
  ⟦≗⟧ᵉ (evar i)   = eff≗ p i
  ⟦≗⟧ᵉ (econst c) = refl
  ⟦≗⟧ᵉ (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (⟦≗⟧ᵉ ε) (⟦≗⟧ᵉ ε')
  ⟦≗⟧ᵉ (ε ⊔̂ₑ ε')  = cong₂ _⊔ₑ_ (⟦≗⟧ᵉ ε) (⟦≗⟧ᵉ ε')

  ⟦≗⟧ʳ : (ρ : RExp Θ) → ⟦ ρ ⟧ʳ σ ≡ ⟦ ρ ⟧ʳ σ'
  ⟦≗⟧ʳ (rvar i)   = res≗ p i
  ⟦≗⟧ʳ (rconst c) = refl
  ⟦≗⟧ʳ (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (⟦≗⟧ʳ ρ) (⟦≗⟧ʳ ρ')
  ⟦≗⟧ʳ (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔ᵣ_ (⟦≗⟧ʳ ρ) (⟦≗⟧ʳ ρ')
  ⟦≗⟧ʳ ∣ ε ∣̂ᵉ     = cong mapᵉ (⟦≗⟧ᵉ ε)

≗ᴰ-refl : ∀ {Θ} {σ : DInst Θ} → σ ≗ᴰ σ
≗ᴰ-refl = mk≗ᴰ (λ α → refl) (λ i → refl) (λ i → refl)

≗ᴰ-sym : ∀ {Θ} {σ σ' : DInst Θ} → σ ≗ᴰ σ' → σ' ≗ᴰ σ
≗ᴰ-sym p = mk≗ᴰ (λ α → sym (ty≗ p α)) (λ i → sym (res≗ p i)) (λ i → sym (eff≗ p i))

≗ᴰ-trans : ∀ {Θ} {σ σ' σ'' : DInst Θ} → σ ≗ᴰ σ' → σ' ≗ᴰ σ'' → σ ≗ᴰ σ''
≗ᴰ-trans p q = mk≗ᴰ (λ α → trans (ty≗ p α) (ty≗ q α)) (λ i → trans (res≗ p i) (res≗ q i))
                    (λ i → trans (eff≗ p i) (eff≗ q i))

≗ᴰ-,ᵉ : ∀ {Θ} {σ σ' : DInst Θ} → σ ≗ᴰ σ' → (c : E) → (σ ,ᵉᴰ c) ≗ᴰ (σ' ,ᵉᴰ c)
≗ᴰ-,ᵉ p c = mk≗ᴰ (ty≗ p) (res≗ p) (λ { zero → refl ; (suc i) → eff≗ p i })

------------------------------------------------------------------------
-- Substitution: interpreting a grade expression `X [ δ ]` at `σ` is
-- interpreting `X` at the composite `δ ⨟ᴰ σ`

infixl 25 _⨟ᴰ_

_⨟ᴰ_ : ∀ {Θ Θ'} → Subst Θ Θ' → DInst Θ' → DInst Θ
δ ⨟ᴰ σ = dinst (λ α → ⟦ sTy δ α ⟧ᵛ σ) (λ i → ⟦ sR δ i ⟧ʳ σ) (λ i → ⟦ sE δ i ⟧ᵉ σ)

module _ {Θ Θ'} (δ : Subst Θ Θ') (σ : DInst Θ') where

  ⟦[]⟧ᵉ : (ε : EExp Θ) → ⟦ ε [ δ ]ᵉ ⟧ᵉ σ ≡ ⟦ ε ⟧ᵉ (δ ⨟ᴰ σ)
  ⟦[]⟧ᵉ (evar i)   = refl
  ⟦[]⟧ᵉ (econst c) = refl
  ⟦[]⟧ᵉ (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (⟦[]⟧ᵉ ε) (⟦[]⟧ᵉ ε')
  ⟦[]⟧ᵉ (ε ⊔̂ₑ ε')  = cong₂ _⊔ₑ_ (⟦[]⟧ᵉ ε) (⟦[]⟧ᵉ ε')

  ⟦[]⟧ʳ : (ρ : RExp Θ) → ⟦ ρ [ δ ]ʳ ⟧ʳ σ ≡ ⟦ ρ ⟧ʳ (δ ⨟ᴰ σ)
  ⟦[]⟧ʳ (rvar i)   = refl
  ⟦[]⟧ʳ (rconst c) = refl
  ⟦[]⟧ʳ (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (⟦[]⟧ʳ ρ) (⟦[]⟧ʳ ρ')
  ⟦[]⟧ʳ (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔ᵣ_ (⟦[]⟧ʳ ρ) (⟦[]⟧ʳ ρ')
  ⟦[]⟧ʳ ∣ ε ∣̂ᵉ     = cong mapᵉ (⟦[]⟧ᵉ ε)

↑ᵉ-⨟ᴰ : ∀ {Θ Θ'} → (δ : Subst Θ Θ') → (τ : DInst Θ') → (c : E)
      → ((δ ↑ᵉ) ⨟ᴰ (τ ,ᵉᴰ c)) ≗ᴰ ((δ ⨟ᴰ τ) ,ᵉᴰ c)
↑ᵉ-⨟ᴰ δ τ c = mk≗ᴰ (λ α → ⟦wkᵉ⟧ᵛ τ c (sTy δ α)) (λ i → ⟦wkᵉ⟧ʳ τ c (sR δ i))
                   (λ { zero → refl ; (suc i) → ⟦wkᵉ⟧ᵉ τ c (sE δ i) })

idˢ-⨟ᴰ : ∀ {Θ} → (σ : DInst Θ) → (idˢ ⨟ᴰ σ) ≗ᴰ σ
idˢ-⨟ᴰ σ = ≗ᴰ-refl

-- Extension by grades for the rigids, the outermost first

infixl 30 _,ᵉᴰⁿ_

_,ᵉᴰⁿ_ : ∀ {Θ k} → DInst Θ → Vec E k → DInst (Θ +eⁿ k)
σ ,ᵉᴰⁿ []ᵛ        = σ
σ ,ᵉᴰⁿ (c ∷ᵛ cs) = (σ ,ᵉᴰ c) ,ᵉᴰⁿ cs

≗ᴰ-,ᵉᴰⁿ : ∀ {Θ k} {σ σ' : DInst Θ} → σ ≗ᴰ σ' → (cs : Vec E k) → (σ ,ᵉᴰⁿ cs) ≗ᴰ (σ' ,ᵉᴰⁿ cs)
≗ᴰ-,ᵉᴰⁿ p []ᵛ        = p
≗ᴰ-,ᵉᴰⁿ p (c ∷ᵛ cs) = ≗ᴰ-,ᵉᴰⁿ (≗ᴰ-,ᵉ p c) cs

,ᵉ-⨟ᴰ : ∀ {Θ Θ'} → (τ : Subst Θ Θ') → (ε : EExp Θ') → (σ : DInst Θ')
      → ((τ ,ᵉ ε) ⨟ᴰ σ) ≗ᴰ ((τ ⨟ᴰ σ) ,ᵉᴰ ⟦ ε ⟧ᵉ σ)
,ᵉ-⨟ᴰ τ ε σ = mk≗ᴰ (λ α → refl) (λ i → refl) (λ { zero → refl ; (suc i) → refl })

,ᵉⁿ-⨟ᴰ : ∀ {Θ Θ' k} → (τ : Subst Θ Θ') → (es : Vec (EExp Θ') k) → (σ : DInst Θ')
       → ((τ ,ᵉⁿ es) ⨟ᴰ σ) ≗ᴰ ((τ ⨟ᴰ σ) ,ᵉᴰⁿ mapᵛ (λ e → ⟦ e ⟧ᵉ σ) es)
,ᵉⁿ-⨟ᴰ τ []ᵛ        σ = ≗ᴰ-refl
,ᵉⁿ-⨟ᴰ τ (ε ∷ᵛ es) σ =
  ≗ᴰ-trans (,ᵉⁿ-⨟ᴰ (τ ,ᵉ ε) es σ) (≗ᴰ-,ᵉᴰⁿ (,ᵉ-⨟ᴰ τ ε σ) (mapᵛ (λ e → ⟦ e ⟧ᵉ σ) es))

------------------------------------------------------------------------
-- The empty instance; a closed grade expression means its value

∅ᴰ : DInst ∅ˢ
∅ᴰ = dinst (λ ()) (λ ()) (λ ())

⟦⟧∅-valᵉ : (ε : EExp ∅ˢ) → ⟦ ε ⟧ᵉ ∅ᴰ ≡ valᵉ ε
⟦⟧∅-valᵉ (evar ())
⟦⟧∅-valᵉ (econst c) = refl
⟦⟧∅-valᵉ (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (⟦⟧∅-valᵉ ε) (⟦⟧∅-valᵉ ε')
⟦⟧∅-valᵉ (ε ⊔̂ₑ ε')  = cong₂ _⊔ₑ_ (⟦⟧∅-valᵉ ε) (⟦⟧∅-valᵉ ε')

⟦⟧∅-valʳ : (ρ : RExp ∅ˢ) → ⟦ ρ ⟧ʳ ∅ᴰ ≡ valʳ ρ
⟦⟧∅-valʳ (rvar ())
⟦⟧∅-valʳ (rconst c) = refl
⟦⟧∅-valʳ (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (⟦⟧∅-valʳ ρ) (⟦⟧∅-valʳ ρ')
⟦⟧∅-valʳ (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔ᵣ_ (⟦⟧∅-valʳ ρ) (⟦⟧∅-valʳ ρ')
⟦⟧∅-valʳ ∣ ε ∣̂ᵉ     = cong mapᵉ (⟦⟧∅-valᵉ ε)

------------------------------------------------------------------------
-- Closed open syntax: the interpretation at the empty instance

⌞_⌟ᵉ : EExp ∅ˢ → E
⌞ ε ⌟ᵉ = ⟦ ε ⟧ᵉ ∅ᴰ

⌞_⌟ʳ : RExp ∅ˢ → R
⌞ ρ ⌟ʳ = ⟦ ρ ⟧ʳ ∅ᴰ

⌞_⌟ᵛ : OVType ∅ˢ → VType
⌞ A ⌟ᵛ = ⟦ A ⟧ᵛ ∅ᴰ

⌞_⌟ᶜ : OCType ∅ˢ → CType
⌞ C ⌟ᶜ = ⟦ C ⟧ᶜ ∅ᴰ

⌞_⌟ᶜᵗˣ : ∀ {n} → OCtx ∅ˢ n → Ctx
⌞ Γ ⌟ᶜᵗˣ = ⟦ Γ ⟧ᶜᵗˣ ∅ᴰ

-- on grades, the values

⌞⌟-valᵉ : (ε : EExp ∅ˢ) → ⌞ ε ⌟ᵉ ≡ valᵉ ε
⌞⌟-valᵉ = ⟦⟧∅-valᵉ

⌞⌟-valʳ : (ρ : RExp ∅ˢ) → ⌞ ρ ⌟ʳ ≡ valʳ ρ
⌞⌟-valʳ = ⟦⟧∅-valʳ

-- Every closed type arises: the embedding, each grade a constant, is a
-- section of `⌞_⌟`


mutual

  ⌜_⌝ᵛ : VType → OVType ∅ˢ
  ⌜ Base b ⌝ᵛ     = Base b
  ⌜ Unit ⌝ᵛ       = Unit
  ⌜ Bool ⌝ᵛ       = Bool
  ⌜ Nat ⌝ᵛ        = Nat
  ⌜ A |×| B ⌝ᵛ    = ⌜ A ⌝ᵛ |×| ⌜ B ⌝ᵛ
  ⌜ A |+| B ⌝ᵛ    = ⌜ A ⌝ᵛ |+| ⌜ B ⌝ᵛ
  ⌜ |List| A ⌝ᵛ   = |List| ⌜ A ⌝ᵛ
  ⌜ Empty ⌝ᵛ      = Empty
  ⌜ A ⇒ C ⌝ᵛ      = ⌜ A ⌝ᵛ ⇒ ⌜ C ⌝ᶜ
  ⌜ [ ρ ] A ⌝ᵛ    = [ rconst ρ ] ⌜ A ⌝ᵛ

  ⌜_⌝ᶜ : CType → OCType ∅ˢ
  ⌜ A ‼ ε ⌝ᶜ = ⌜ A ⌝ᵛ ‼ econst ε

mutual

  ⌞⌜_⌝⌟ᵛ : (A : VType) → ⌞ ⌜ A ⌝ᵛ ⌟ᵛ ≡ A
  ⌞⌜ Base b ⌝⌟ᵛ   = refl
  ⌞⌜ Unit ⌝⌟ᵛ     = refl
  ⌞⌜ Bool ⌝⌟ᵛ     = refl
  ⌞⌜ Nat ⌝⌟ᵛ      = refl
  ⌞⌜ A |×| B ⌝⌟ᵛ  = cong₂ _|×|_ ⌞⌜ A ⌝⌟ᵛ ⌞⌜ B ⌝⌟ᵛ
  ⌞⌜ A |+| B ⌝⌟ᵛ  = cong₂ _|+|_ ⌞⌜ A ⌝⌟ᵛ ⌞⌜ B ⌝⌟ᵛ
  ⌞⌜ |List| A ⌝⌟ᵛ = cong |List| ⌞⌜ A ⌝⌟ᵛ
  ⌞⌜ Empty ⌝⌟ᵛ    = refl
  ⌞⌜ A ⇒ C ⌝⌟ᵛ    = cong₂ _⇒_ ⌞⌜ A ⌝⌟ᵛ ⌞⌜ C ⌝⌟ᶜ
  ⌞⌜ [ ρ ] A ⌝⌟ᵛ  = cong ([ ρ ]_) ⌞⌜ A ⌝⌟ᵛ

  ⌞⌜_⌝⌟ᶜ : (C : CType) → ⌞ ⌜ C ⌝ᶜ ⌟ᶜ ≡ C
  ⌞⌜ A ‼ ε ⌝⌟ᶜ = cong (_‼ ε) ⌞⌜ A ⌝⌟ᵛ

-- A closed instance of the open syntax determines a declarative one

⌞_⌟ˢ : ∀ {Θ} → Subst Θ ∅ˢ → DInst Θ
⌞ δ ⌟ˢ = δ ⨟ᴰ ∅ᴰ

-- Every declarative instance arises so, from the closed instance
-- sending each variable to a constant

⌜_⌝ˢ : ∀ {Θ} → DInst Θ → Subst Θ ∅ˢ
⌜ σ ⌝ˢ = sub (λ α → ⌜ ty σ α ⌝ᵛ) (λ i → rconst (res σ i)) (λ i → econst (eff σ i))

⌞⌜_⌝ˢ⌟ : ∀ {Θ} → (σ : DInst Θ) → ⌞ ⌜ σ ⌝ˢ ⌟ˢ ≗ᴰ σ
⌞⌜ σ ⌝ˢ⌟ = mk≗ᴰ (λ α → ⌞⌜ ty σ α ⌝⌟ᵛ) (λ _ → refl) (λ _ → refl)
