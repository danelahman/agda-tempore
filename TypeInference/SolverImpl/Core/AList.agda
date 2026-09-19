------------------------------------------------------------------
-- Triangular substitutions                                     --
--                                                              --
-- An `AList Θ Θ'` is a list of single-variable bindings, each  --
-- eliminating one variable of the scope it is read in: the     --
-- head is the binding applied first, and every binding's image --
-- lives in the scope of the bindings that follow it. It        --
-- denotes the composite substitution `⟦_⟧ᴬ`, and the three     --
-- sorts are kept apart by three constructors.                  --
--                                                              --
-- `AList` follows McBride (JFP 2003); substitutions of this    --
-- shape are the unification literature's triangular form       --
-- (Baader and Snyder, 2001).                                   --
------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Core.AList (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S

open import TypeInference.SolverImpl.Core.For S

--------------------------------------------------------------
-- The store                                                 --
--------------------------------------------------------------

infixr 20 _/ᵗ_∷_ _/ʳ_∷_ _/ᵉ_∷_

data AList : Scope → Scope → Set where
  anil   : ∀ {Θ} → AList Θ Θ
  _/ᵗ_∷_ : ∀ {Θ Θ'} → OVType Θ → TyVar (Θ +ty) → AList Θ Θ' → AList (Θ +ty) Θ'
  _/ʳ_∷_ : ∀ {Θ Θ'} → RExp Θ   → RVar  (Θ +r)  → AList Θ Θ' → AList (Θ +r)  Θ'
  _/ᵉ_∷_ : ∀ {Θ Θ'} → EExp Θ   → EVar  (Θ +e)  → AList Θ Θ' → AList (Θ +e)  Θ'

--------------------------------------------------------------
-- What a store denotes                                      --
--------------------------------------------------------------

⟦_⟧ᴬ : ∀ {Θ Θ'} → AList Θ Θ' → Subst Θ Θ'
⟦ anil ⟧ᴬ         = idˢ
⟦ A /ᵗ α ∷ ρ ⟧ᴬ   = (A forᵗ α) ⨟ˢ ⟦ ρ ⟧ᴬ
⟦ ρ' /ʳ i ∷ ρ ⟧ᴬ  = (ρ' forʳ i) ⨟ˢ ⟦ ρ ⟧ᴬ
⟦ ε /ᵉ i ∷ ρ ⟧ᴬ   = (ε forᵉ i) ⨟ˢ ⟦ ρ ⟧ᴬ

--------------------------------------------------------------
-- Composition of stores                                     --
--------------------------------------------------------------

infixr 18 _++ᴬ_

_++ᴬ_ : ∀ {Θ Θ' Θ''} → AList Θ' Θ'' → AList Θ Θ' → AList Θ Θ''
ρ' ++ᴬ anil         = ρ'
ρ' ++ᴬ (A /ᵗ α ∷ ρ) = A /ᵗ α ∷ (ρ' ++ᴬ ρ)
ρ' ++ᴬ (X /ʳ i ∷ ρ) = X /ʳ i ∷ (ρ' ++ᴬ ρ)
ρ' ++ᴬ (ε /ᵉ i ∷ ρ) = ε /ᵉ i ∷ (ρ' ++ᴬ ρ)

-- and what it denotes.  The three cons cases differ only in the sort
-- of the head binding, so they share the following three steps.

splitᵛ : ∀ {Θ Θ' Θ''} {γ : Subst Θ Θ''} → (τ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
       → γ ≐ˢ (τ ⨟ˢ δ) → (A : OVType Θ) → A [ γ ]ᵛ ≡ A [ τ ]ᵛ [ δ ]ᵛ
splitᵛ τ δ q A = trans ([≐]ᵛ q A) (sym ([⨟]ᵛ A τ δ))

splitʳ : ∀ {Θ Θ' Θ''} {γ : Subst Θ Θ''} → (τ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
       → γ ≐ˢ (τ ⨟ˢ δ) → (ρ : RExp Θ) → ρ [ γ ]ʳ ≡ ρ [ τ ]ʳ [ δ ]ʳ
splitʳ τ δ q ρ = trans ([≐]ʳ q ρ) (sym ([⨟]ʳ ρ τ δ))

splitᵉ : ∀ {Θ Θ' Θ''} {γ : Subst Θ Θ''} → (τ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
       → γ ≐ˢ (τ ⨟ˢ δ) → (ε : EExp Θ) → ε [ γ ]ᵉ ≡ ε [ τ ]ᵉ [ δ ]ᵉ
splitᵉ τ δ q ε = trans ([≐]ᵉ q ε) (sym ([⨟]ᵉ ε τ δ))

⟦++⟧ᴬ : ∀ {Θ Θ' Θ''} → (ρ' : AList Θ' Θ'') → (ρ : AList Θ Θ')
      → ⟦ ρ' ++ᴬ ρ ⟧ᴬ ≐ˢ (⟦ ρ ⟧ᴬ ⨟ˢ ⟦ ρ' ⟧ᴬ)
⟦++⟧ᴬ ρ' anil = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)
⟦++⟧ᴬ ρ' (A /ᵗ α ∷ ρ) =
  mk≐ˢ (λ β → splitᵛ ⟦ ρ ⟧ᴬ ⟦ ρ' ⟧ᴬ (⟦++⟧ᴬ ρ' ρ) (sTy (A forᵗ α) β))
       (λ i → splitʳ ⟦ ρ ⟧ᴬ ⟦ ρ' ⟧ᴬ (⟦++⟧ᴬ ρ' ρ) (sR  (A forᵗ α) i))
       (λ i → splitᵉ ⟦ ρ ⟧ᴬ ⟦ ρ' ⟧ᴬ (⟦++⟧ᴬ ρ' ρ) (sE  (A forᵗ α) i))
⟦++⟧ᴬ ρ' (X /ʳ i ∷ ρ) =
  mk≐ˢ (λ β → splitᵛ ⟦ ρ ⟧ᴬ ⟦ ρ' ⟧ᴬ (⟦++⟧ᴬ ρ' ρ) (sTy (X forʳ i) β))
       (λ j → splitʳ ⟦ ρ ⟧ᴬ ⟦ ρ' ⟧ᴬ (⟦++⟧ᴬ ρ' ρ) (sR  (X forʳ i) j))
       (λ j → splitᵉ ⟦ ρ ⟧ᴬ ⟦ ρ' ⟧ᴬ (⟦++⟧ᴬ ρ' ρ) (sE  (X forʳ i) j))
⟦++⟧ᴬ ρ' (ε /ᵉ i ∷ ρ) =
  mk≐ˢ (λ β → splitᵛ ⟦ ρ ⟧ᴬ ⟦ ρ' ⟧ᴬ (⟦++⟧ᴬ ρ' ρ) (sTy (ε forᵉ i) β))
       (λ j → splitʳ ⟦ ρ ⟧ᴬ ⟦ ρ' ⟧ᴬ (⟦++⟧ᴬ ρ' ρ) (sR  (ε forᵉ i) j))
       (λ j → splitᵉ ⟦ ρ ⟧ᴬ ⟦ ρ' ⟧ᴬ (⟦++⟧ᴬ ρ' ρ) (sE  (ε forᵉ i) j))
