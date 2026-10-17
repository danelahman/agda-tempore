--------------------------------------------------------------------
-- Decoration: a skeleton back into an open type                  --
--                                                                --
-- `decorate` builds the most general open type of a given shape: --
-- the scope grows by one fresh resource-grade variable per box,  --
-- one fresh effect-grade variable per arrow, and one fresh type  --
-- variable per skeleton variable left. Fresh means fresh per     --
-- occurrence.                                                    --
--                                                                --
-- `expandSub` is what a subtyping demand asks for: a list of     --
-- demands is first a unification problem on their skeletons,     --
-- whose solution then refines every type variable whose shape it --
-- has determined, leaving the others alone.                      --
--                                                                --
-- Contract (proved in `SolverImpl.Expand`): after the expansion  --
-- every demand of the list decomposes (`expandSub-dec`); every   --
-- substitution meeting the demands, under any hypotheses,        --
-- factors through it, and a failure refutes the demands at every --
-- substitution (`expandSub-max`).                                --
--                                                                --
-- Match-then-decompose, as in Fuh and Mishra's structural        --
-- subtyping inference (TCS 1990).                                --
--------------------------------------------------------------------

open import Data.List.Base using (List; map)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′) renaming (map to mmap)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; tabulate)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Core.Decorate (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S

open import TypeInference.SolverImpl.Core.Skel      S
open import TypeInference.SolverImpl.Core.SkelUnify S

-- The extension a decoration performs is recorded as the
-- substitution that renames the old scope into the new one.

decorate : ∀ {m} → (Ψ : Scope) → Skel m
         → Σ[ Ψ' ∈ Scope ] (Subst Ψ Ψ' × OVType Ψ')
decorate Ψ (svar γ)  = Ψ +ty , wkˢᵗ , tvar (newᵗ {Ψ})
decorate Ψ (sBase b) = Ψ , idˢ , Base b
decorate Ψ sUnit     = Ψ , idˢ , Unit
decorate Ψ sBool     = Ψ , idˢ , Bool
decorate Ψ sNat      = Ψ , idˢ , Nat
decorate Ψ sEmpty    = Ψ , idˢ , Empty
decorate Ψ (t s× u) with decorate Ψ t
... | Ψ₁ , w₁ , A with decorate Ψ₁ u
...   | Ψ₂ , w₂ , B = Ψ₂ , w₁ ⨟ˢ w₂ , (A [ w₂ ]ᵛ |×| B)
decorate Ψ (t s⇒ u) with decorate Ψ t
... | Ψ₁ , w₁ , A with decorate Ψ₁ u
...   | Ψ₂ , w₂ , B =
        Ψ₂ +e , (w₁ ⨟ˢ w₂ ⨟ˢ wkˢᵉ) ,
        (wkᵉ-v (A [ w₂ ]ᵛ) ⇒ (wkᵉ-v B ‼ evar (newᵉ {Ψ₂})))
decorate Ψ (sBox t) with decorate Ψ t
... | Ψ₁ , w₁ , A = Ψ₁ +r , (w₁ ⨟ˢ wkˢʳ) , ([ rvar (newʳ {Ψ₁}) ] wkʳ-v A)

-- A whole vector of skeletons, sharing one scope extension. A
-- skeleton that is still a variable determines no shape, and its
-- type variable is kept rather than renamed.

decorate* : ∀ {m k} → (Ψ : Scope) → Vec (Skel m) k
          → Σ[ Ψ' ∈ Scope ] (Subst Ψ Ψ' × Vec (Maybe (OVType Ψ')) k)
decorate* Ψ []       = Ψ , idˢ , []
decorate* Ψ (t ∷ ts) with svar? t
... | just γ  with decorate* Ψ ts
...   | Ψ' , w , As = Ψ' , w , (nothing ∷ As)
decorate* Ψ (t ∷ ts) | nothing with decorate Ψ t
... | Ψ₁ , w₁ , A with decorate* Ψ₁ ts
...   | Ψ₂ , w₂ , As = Ψ₂ , w₁ ⨟ˢ w₂ , (just (A [ w₂ ]ᵛ) ∷ As)

-- Refining every type variable to the shape a skeleton solution
-- gives it

expandᵏ : ∀ {m} → (Ψ : Scope) → SSub (nTy Ψ) m → Σ[ Ψ' ∈ Scope ] (Subst Ψ Ψ')
expandᵏ Ψ σ with decorate* Ψ (tabulate σ)
... | Ψ' , w , As =
      Ψ' , sub (λ α → maybe′ (λ A → A) (sTy w α) (lookup As α)) (sR w) (sE w)

-- The expansion a list of subtyping demands calls for

skelEqns : ∀ {Ψ} → List (OVType Ψ × OVType Ψ) → SEqns (nTy Ψ)
skelEqns = map (λ { (A , B) → skelᵛ A , skelᵛ B })

expandSub : ∀ {Ψ} → List (OVType Ψ × OVType Ψ)
          → Maybe (Σ[ Ψ' ∈ Scope ] (Subst Ψ Ψ'))
expandSub {Ψ} l = mmap (λ { (m , τ) → expandᵏ Ψ ⟦ τ ⟧ᴷ }) (unifyᵏ (skelEqns l))
