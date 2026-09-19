------------------------------------------------------------------
-- Equations between the four syntactic categories               --
--                                                               --
-- The unifier's input is a list of equations, one constructor    --
-- per category. A substitution unifies a list when it makes      --
-- both sides of every equation literally equal: satisfaction of  --
-- a type equation is syntactic, so nothing here is up to any     --
-- grade theory.                                                  --
------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Core.Eqn (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S

data Eqn (Θ : Scope) : Set where
  eqᵛ : OVType Θ → OVType Θ → Eqn Θ
  eqᶜ : OCType Θ → OCType Θ → Eqn Θ
  eqʳ : RExp Θ   → RExp Θ   → Eqn Θ
  eqᵉ : EExp Θ   → EExp Θ   → Eqn Θ

Eqns : Scope → Set
Eqns Θ = List (Eqn Θ)

infixl 50 _[_]ᴱ _[_]ᴱˢ

_[_]ᴱ : ∀ {Θ Θ'} → Eqn Θ → Subst Θ Θ' → Eqn Θ'
eqᵛ A B [ σ ]ᴱ = eqᵛ (A [ σ ]ᵛ) (B [ σ ]ᵛ)
eqᶜ C D [ σ ]ᴱ = eqᶜ (C [ σ ]ᶜ) (D [ σ ]ᶜ)
eqʳ ρ ρ' [ σ ]ᴱ = eqʳ (ρ [ σ ]ʳ) (ρ' [ σ ]ʳ)
eqᵉ ε ε' [ σ ]ᴱ = eqᵉ (ε [ σ ]ᵉ) (ε' [ σ ]ᵉ)

_[_]ᴱˢ : ∀ {Θ Θ'} → Eqns Θ → Subst Θ Θ' → Eqns Θ'
es [ σ ]ᴱˢ = map (_[ σ ]ᴱ) es

Unifies¹ : ∀ {Θ Θ'} → Eqn Θ → Subst Θ Θ' → Set
Unifies¹ (eqᵛ A B)  σ = A [ σ ]ᵛ ≡ B [ σ ]ᵛ
Unifies¹ (eqᶜ C D)  σ = C [ σ ]ᶜ ≡ D [ σ ]ᶜ
Unifies¹ (eqʳ ρ ρ') σ = ρ [ σ ]ʳ ≡ ρ' [ σ ]ʳ
Unifies¹ (eqᵉ ε ε') σ = ε [ σ ]ᵉ ≡ ε' [ σ ]ᵉ

Unifies : ∀ {Θ Θ'} → Eqns Θ → Subst Θ Θ' → Set
Unifies []       σ = ⊤
Unifies (e ∷ es) σ = Unifies¹ e σ × Unifies es σ

Unifies¹-resp-≐ˢ : ∀ {Θ Θ'} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ
                 → (e : Eqn Θ) → Unifies¹ e σ → Unifies¹ e δ
Unifies¹-resp-≐ˢ q (eqᵛ A B)  u = trans (sym ([≐]ᵛ q A)) (trans u ([≐]ᵛ q B))
Unifies¹-resp-≐ˢ q (eqᶜ C D)  u = trans (sym ([≐]ᶜ q C)) (trans u ([≐]ᶜ q D))
Unifies¹-resp-≐ˢ q (eqʳ ρ ρ') u = trans (sym ([≐]ʳ q ρ)) (trans u ([≐]ʳ q ρ'))
Unifies¹-resp-≐ˢ q (eqᵉ ε ε') u = trans (sym ([≐]ᵉ q ε)) (trans u ([≐]ᵉ q ε'))

Unifies-resp-≐ˢ : ∀ {Θ Θ'} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ
                → (es : Eqns Θ) → Unifies es σ → Unifies es δ
Unifies-resp-≐ˢ q []       u        = tt
Unifies-resp-≐ˢ q (e ∷ es) (u , us) = Unifies¹-resp-≐ˢ q e u , Unifies-resp-≐ˢ q es us

Unifies¹-mono : ∀ {Θ Θ' Θ''} {σ : Subst Θ Θ'} → (δ : Subst Θ' Θ'')
              → (e : Eqn Θ) → Unifies¹ e σ → Unifies¹ e (σ ⨟ˢ δ)
Unifies¹-mono {σ = σ} δ (eqᵛ A B) u =
  trans (sym ([⨟]ᵛ A σ δ)) (trans (cong (_[ δ ]ᵛ) u) ([⨟]ᵛ B σ δ))
Unifies¹-mono {σ = σ} δ (eqᶜ C D) u =
  trans (sym ([⨟]ᶜ C σ δ)) (trans (cong (_[ δ ]ᶜ) u) ([⨟]ᶜ D σ δ))
Unifies¹-mono {σ = σ} δ (eqʳ ρ ρ') u =
  trans (sym ([⨟]ʳ ρ σ δ)) (trans (cong (_[ δ ]ʳ) u) ([⨟]ʳ ρ' σ δ))
Unifies¹-mono {σ = σ} δ (eqᵉ ε ε') u =
  trans (sym ([⨟]ᵉ ε σ δ)) (trans (cong (_[ δ ]ᵉ) u) ([⨟]ᵉ ε' σ δ))

Unifies-mono : ∀ {Θ Θ' Θ''} {σ : Subst Θ Θ'} → (δ : Subst Θ' Θ'')
             → (es : Eqns Θ) → Unifies es σ → Unifies es (σ ⨟ˢ δ)
Unifies-mono δ []       u        = tt
Unifies-mono δ (e ∷ es) (u , us) = Unifies¹-mono δ e u , Unifies-mono δ es us
