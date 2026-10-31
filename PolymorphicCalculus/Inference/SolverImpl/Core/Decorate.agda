--------------------------------------------------------------------
-- Decoration: a skeleton back into an open type                  --
--                                                                --
-- `decorate` builds the most general open type of a given shape, --
-- with a fresh grade variable per grade slot (one per box and    --
-- arrow, two per handler type) and a fresh type variable per     --
-- skeleton variable left. `expandSub` unifies the skeletons of a --
-- list of subtyping demands and refines each type variable whose --
-- shape the solution determines.                                 --
--                                                                --
-- Contract (`SolverImpl.Expand`): afterwards every demand        --
-- decomposes (`expandSub-dec`); every substitution meeting the   --
-- demands factors through it, and a failure refutes them         --
-- (`expandSub-max`).                                             --
--                                                                --
-- Match-then-decompose, as in Fuh and Mishra's structural        --
-- subtyping inference.                                           --
--------------------------------------------------------------------

open import Data.List.Base using (List; map)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′) renaming (map to mmap)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; tabulate)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.SolverImpl.Core.Decorate (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S

open import PolymorphicCalculus.Inference.SolverImpl.Core.Skel      S
open import PolymorphicCalculus.Inference.SolverImpl.Core.SkelUnify S

-- The extension a decoration performs, as the renaming of the old scope into
-- the new

decorate : ∀ {m} → (Ω : Scope) → Skel m
         → Σ[ Ω' ∈ Scope ] (Subst Ω Ω' × OVType Ω')
decorate Ω (svar γ)  = Ω +ty , wkˢᵗ , tvar (newᵗ {Ω})
decorate Ω (sBase b) = Ω , idˢ , Base b
decorate Ω sUnit     = Ω , idˢ , Unit
decorate Ω sBool     = Ω , idˢ , Bool
decorate Ω sNat      = Ω , idˢ , Nat
decorate Ω sEmpty    = Ω , idˢ , Empty
decorate Ω (t s× u) with decorate Ω t
... | Ω₁ , w₁ , A with decorate Ω₁ u
...   | Ω₂ , w₂ , B = Ω₂ , w₁ ⨟ˢ w₂ , (A [ w₂ ]ᵛ |×| B)
decorate Ω (t s+ u) with decorate Ω t
... | Ω₁ , w₁ , A with decorate Ω₁ u
...   | Ω₂ , w₂ , B = Ω₂ , w₁ ⨟ˢ w₂ , (A [ w₂ ]ᵛ |+| B)
decorate Ω (sList t) with decorate Ω t
... | Ω₁ , w₁ , A = Ω₁ , w₁ , |List| A
decorate Ω (t s⇒ u) with decorate Ω t
... | Ω₁ , w₁ , A with decorate Ω₁ u
...   | Ω₂ , w₂ , B =
        Ω₂ +e , (w₁ ⨟ˢ w₂ ⨟ˢ wkˢᵉ) ,
        (wkᵉ-v (A [ w₂ ]ᵛ) ⇒ (wkᵉ-v B ‼ evar (newᵉ {Ω₂})))
decorate Ω (t s⇛ u) with decorate Ω t
... | Ω₁ , w₁ , A with decorate Ω₁ u
...   | Ω₂ , w₂ , B =
        Ω₂ +e +e , (w₁ ⨟ˢ w₂ ⨟ˢ wkˢᵉ ⨟ˢ wkˢᵉ) ,
        (wkᵉ-v (wkᵉ-v (A [ w₂ ]ᵛ)) ‼ wkᵉ-e (evar (newᵉ {Ω₂}))
          ⇛ wkᵉ-v (wkᵉ-v B) ‼ evar (newᵉ {Ω₂ +e}))
decorate Ω (sBox t) with decorate Ω t
... | Ω₁ , w₁ , A = Ω₁ +r , (w₁ ⨟ˢ wkˢʳ) , ([ rvar (newʳ {Ω₁}) ] wkʳ-v A)

-- A whole vector of skeletons, sharing one scope extension; a variable skeleton
-- determines no shape, and its type variable is kept

decorate* : ∀ {m k} → (Ω : Scope) → Vec (Skel m) k
          → Σ[ Ω' ∈ Scope ] (Subst Ω Ω' × Vec (Maybe (OVType Ω')) k)
decorate* Ω []       = Ω , idˢ , []
decorate* Ω (t ∷ ts) with svar? t
... | just γ  with decorate* Ω ts
...   | Ω' , w , As = Ω' , w , (nothing ∷ As)
decorate* Ω (t ∷ ts) | nothing with decorate Ω t
... | Ω₁ , w₁ , A with decorate* Ω₁ ts
...   | Ω₂ , w₂ , As = Ω₂ , w₁ ⨟ˢ w₂ , (just (A [ w₂ ]ᵛ) ∷ As)

-- Refining every type variable to the shape a skeleton solution gives it

expandᵏ : ∀ {m} → (Ω : Scope) → SSub (nTy Ω) m → Σ[ Ω' ∈ Scope ] (Subst Ω Ω')
expandᵏ Ω σ with decorate* Ω (tabulate σ)
... | Ω' , w , As =
      Ω' , sub (λ α → maybe′ (λ A → A) (sTy w α) (lookup As α)) (sR w) (sE w)

-- The expansion a list of subtyping demands calls for

skelEqns : ∀ {Ω} → List (OVType Ω × OVType Ω) → SEqns (nTy Ω)
skelEqns = map (λ { (A , B) → skelᵛ A , skelᵛ B })

expandSub : ∀ {Ω} → List (OVType Ω × OVType Ω)
          → Maybe (Σ[ Ω' ∈ Scope ] (Subst Ω Ω'))
expandSub {Ω} l = mmap (λ { (m , τ) → expandᵏ Ω ⟦ τ ⟧ᴷ }) (unifyᵏ (skelEqns l))
