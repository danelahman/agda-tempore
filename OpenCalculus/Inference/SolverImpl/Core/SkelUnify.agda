--------------------------------------------------------------------
-- First-order unification of skeletons                           --
--                                                                --
-- Solves a list of skeleton equations by eliminating one         --
-- skeleton variable at a time. `amguᵏ` descends through the      --
-- store one binding at a time, and the scope of skeleton         --
-- variables is a bare `ℕ`, so the descent is structural.         --
--                                                                --
-- No skeleton variable is rigid: the rigid effect-grade          --
-- variables sit in grade slots, which a skeleton does not have.  --
--                                                                --
-- Contract. A success returns a store whose substitution unifies --
-- the equations (`unifyᵏ-sound`, `Core.SkelUnifySound`) and      --
-- through which every unifier factors (`unifyᵏ-max`,             --
-- `Core.SkelUnifyMGU`); a failure refutes them at every          --
-- substitution (`unifyᵏ-fail`).                                  --
--                                                                --
-- Follows McBride's structural-recursion unifier (JFP 2003);     --
-- "rigid"/"flexible" are Huet's (1975).                          --
--------------------------------------------------------------------

open import Data.Bool.Base using (if_then_else_) renaming (Bool to 𝔹)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_) renaming (map to mmap)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)

open import Relation.Nullary.Decidable using (⌊_⌋)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Inference.SolverImpl.Core.SkelUnify (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Language.Types S using (_≡ᵇ?_)

open import OpenCalculus.Inference.SolverImpl.Core.Thick
open import OpenCalculus.Inference.SolverImpl.Core.Skel S

-- A substitution unifies a list of equations when it makes both
-- sides of every one of them literally equal.

SEqn : ℕ → Set
SEqn n = Skel n × Skel n

SEqns : ℕ → Set
SEqns n = List (SEqn n)

Unifies¹ᵏ : ∀ {n m} → SEqn n → SSub n m → Set
Unifies¹ᵏ (t , u) σ = t [ σ ]ᵏ ≡ u [ σ ]ᵏ

Unifiesᵏ : ∀ {n m} → SEqns n → SSub n m → Set
Unifiesᵏ []       σ = ⊤
Unifiesᵏ (e ∷ es) σ = Unifies¹ᵏ e σ × Unifiesᵏ es σ

-- Triangular substitutions: each binding eliminates one skeleton
-- variable of the scope it is read in.

infixr 20 _/ᵏ_∷_

data SAList : ℕ → ℕ → Set where
  anilᵏ  : ∀ {n} → SAList n n
  _/ᵏ_∷_ : ∀ {n m} → Skel n → Fin (suc n) → SAList n m → SAList (suc n) m

⟦_⟧ᴷ : ∀ {n m} → SAList n m → SSub n m
⟦ anilᵏ ⟧ᴷ      = idᵏ
⟦ t /ᵏ α ∷ τ ⟧ᴷ = (t forᵏ α) ⨟ᵏ ⟦ τ ⟧ᴷ

infixr 18 _++ᴷ_

_++ᴷ_ : ∀ {n m l} → SAList m l → SAList n m → SAList n l
τ' ++ᴷ anilᵏ        = τ'
τ' ++ᴷ (t /ᵏ α ∷ τ) = t /ᵏ α ∷ (τ' ++ᴷ τ)

⟦++⟧ᴷ : ∀ {n m l} → (τ' : SAList m l) → (τ : SAList n m)
      → ⟦ τ' ++ᴷ τ ⟧ᴷ ≐ᵏ (⟦ τ ⟧ᴷ ⨟ᵏ ⟦ τ' ⟧ᴷ)
⟦++⟧ᴷ τ' anilᵏ        α = refl
⟦++⟧ᴷ τ' (t /ᵏ β ∷ τ) α =
  trans ([≐]ᵏ (⟦++⟧ᴷ τ' τ) ((t forᵏ β) α)) (sym ([⨟]ᵏ ((t forᵏ β) α) ⟦ τ ⟧ᴷ ⟦ τ' ⟧ᴷ))

-- A store, together with the scope it lands in

Solᵏ : ℕ → Set
Solᵏ n = Σ[ m ∈ ℕ ] SAList n m

consᵏ : ∀ {n} → Skel n → Fin (suc n) → Solᵏ n → Solᵏ (suc n)
consᵏ t α (m , τ) = m , t /ᵏ α ∷ τ

-- Binding a variable, and the two-variable case in which equal
-- variables need no binding

flexᵏ : ∀ {n} → Fin n → Skel n → Maybe (Solᵏ n)
flexᵏ {zero}  ()
flexᵏ {suc n} α t = mmap (λ t' → n , t' /ᵏ α ∷ anilᵏ) (checkᵏ α t)

flexFlexᵏ : ∀ {n} → Fin n → Fin n → Maybe (Solᵏ n)
flexFlexᵏ {n} α β = if ⌊ α ≟ᶠ β ⌋ then just (n , anilᵏ) else flexᵏ α (svar β)

amguᵏ : ∀ {n} → Skel n → Skel n → Solᵏ n → Maybe (Solᵏ n)
amguᵏ t u (m , r /ᵏ α ∷ τ) =
  mmap (consᵏ r α)
       (amguᵏ (t [ r forᵏ α ]ᵏ) (u [ r forᵏ α ]ᵏ) (m , τ))
amguᵏ (svar α)   (svar β)     (_ , anilᵏ)  = flexFlexᵏ α β
amguᵏ (svar α)   u            (_ , anilᵏ)  = flexᵏ α u
amguᵏ t          (svar β)     (_ , anilᵏ)  = flexᵏ β t
amguᵏ (sBase b)  (sBase b')  s@(_ , anilᵏ) = if ⌊ b ≡ᵇ? b' ⌋ then just s else nothing
amguᵏ sUnit      sUnit       s@(_ , anilᵏ) = just s
amguᵏ sBool      sBool       s@(_ , anilᵏ) = just s
amguᵏ sNat       sNat        s@(_ , anilᵏ) = just s
amguᵏ sEmpty     sEmpty      s@(_ , anilᵏ) = just s
amguᵏ (t s× u)   (t' s× u')  s@(_ , anilᵏ) = amguᵏ t t' s >>= amguᵏ u u'
amguᵏ (t s+ u)   (t' s+ u')  s@(_ , anilᵏ) = amguᵏ t t' s >>= amguᵏ u u'
amguᵏ (t s⇛ u)   (t' s⇛ u')  s@(_ , anilᵏ) = amguᵏ t t' s >>= amguᵏ u u'
amguᵏ (sList t)  (sList t')  s@(_ , anilᵏ) = amguᵏ t t' s
amguᵏ (t s⇒ u)   (t' s⇒ u')  s@(_ , anilᵏ) = amguᵏ t t' s >>= amguᵏ u u'
amguᵏ (sBox t)   (sBox t')   s@(_ , anilᵏ) = amguᵏ t t' s
amguᵏ t          u            (_ , anilᵏ)  = nothing

unifyᴷ : ∀ {n} → SEqns n → Solᵏ n → Maybe (Solᵏ n)
unifyᴷ []             s = just s
unifyᴷ ((t , u) ∷ es) s = amguᵏ t u s >>= unifyᴷ es

unifyᵏ : ∀ {n} → SEqns n → Maybe (Solᵏ n)
unifyᵏ {n} es = unifyᴷ es (n , anilᵏ)

private

  -- a variable is bound to the shape it is matched against

  ex-var : unifyᵏ {1} ((svar Fin.zero , sBox sUnit) ∷ [])
         ≡ just (0 , sBox sUnit /ᵏ Fin.zero ∷ anilᵏ)
  ex-var = refl

  -- two variables are merged, without either being decorated

  ex-merge : unifyᵏ {2} ((svar Fin.zero , svar (Fin.suc Fin.zero)) ∷ [])
           ≡ just (1 , svar Fin.zero /ᵏ Fin.zero ∷ anilᵏ)
  ex-merge = refl

  -- the second demand grows the first's solution

  ex-fix : unifyᵏ {2} ((svar Fin.zero , svar (Fin.suc Fin.zero)) ∷
                       (svar (Fin.suc Fin.zero) , sUnit) ∷ [])
         ≡ just (0 , svar Fin.zero /ᵏ Fin.zero ∷ sUnit /ᵏ Fin.zero ∷ anilᵏ)
  ex-fix = refl

  -- a shape clash is refused

  ex-clash : unifyᵏ {0} ((sUnit , sBool) ∷ []) ≡ nothing
  ex-clash = refl

  -- and so is a cyclic demand

  ex-occurs : unifyᵏ {1} ((svar Fin.zero , svar Fin.zero s× sUnit) ∷ []) ≡ nothing
  ex-occurs = refl
