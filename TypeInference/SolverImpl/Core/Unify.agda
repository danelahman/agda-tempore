------------------------------------------------------------------
-- Solves a list of equations by eliminating one variable at a   --
-- time; a rigid effect-grade variable is never bound.           --
-- `amgu*` descend through the store one binding at a time,      --
-- terminating on the derived size index `Sz`.                   --
-- Follows McBride's structural-recursion unifier (JFP 2003);    --
-- "rigid"/"flexible" are Huet's (1975).                         --
------------------------------------------------------------------

open import Data.Bool.Base using (if_then_else_; _∨_; true; false) renaming (Bool to 𝔹)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; mapMaybe)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_; _<∣>_)
  renaming (map to mmap)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (Σ-syntax; _,_)

open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Core.Unify (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (_≡ᵇ?_)

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S

open import TypeInference.SolverImpl.Core.Thick
open import TypeInference.SolverImpl.Core.For    S
open import TypeInference.SolverImpl.Core.AList  S
open import TypeInference.SolverImpl.Core.Eqn    S
open import TypeInference.SolverImpl.Core.Occurs S
open import TypeInference.SolverImpl.Core.Size   S

-- The effect-grade variables that may not be bound

Rig : Scope → Set
Rig Θ = List (EVar Θ)

-- Membership, at the bare `Fin` a variable of a scope is

_∈ᶠ_ : ∀ {n} → Fin n → List (Fin n) → 𝔹
i ∈ᶠ []       = false
i ∈ᶠ (j ∷ js) = ⌊ i ≟ᶠ j ⌋ ∨ (i ∈ᶠ js)

-- Eliminating an effect-grade variable renumbers the rigids. The
-- eliminated variable is never rigid, so none of them is dropped.
-- The two other sorts leave the effect-grade counter alone. The
-- store names the scope, which the variable alone does not.

popʳᵍ : ∀ {Θ Θ'} → AList Θ Θ' → EVar (Θ +e) → Rig (Θ +e) → Rig Θ
popʳᵍ {Θ} τ i rg = mapMaybe (thickᵉ {Θ} i) rg

-- A store, together with the scope it lands in

Sol : Scope → Set
Sol Θ = Σ[ Θ' ∈ Scope ] AList Θ Θ'

consᵗ : ∀ {Θ} → OVType Θ → TyVar (Θ +ty) → Sol Θ → Sol (Θ +ty)
consᵗ A α (Θ' , ρ) = Θ' , A /ᵗ α ∷ ρ

consʳ : ∀ {Θ} → RExp Θ → RVar (Θ +r) → Sol Θ → Sol (Θ +r)
consʳ X i (Θ' , ρ) = Θ' , X /ʳ i ∷ ρ

consᵉ : ∀ {Θ} → EExp Θ → EVar (Θ +e) → Sol Θ → Sol (Θ +e)
consᵉ ε i (Θ' , ρ) = Θ' , ε /ᵉ i ∷ ρ

no-suc : ∀ {X : Set} {n : ℕ} → suc n ≡ zero → X
no-suc ()

-- As for the rigids, the store names the scope

szᵗ : ∀ {Θ Θ' k} → AList Θ Θ' → Sz (Θ +ty) ≡ suc k → Sz Θ ≡ k
szᵗ τ p = suc-injective p

szʳ : ∀ {Θ Θ' k} → AList Θ Θ' → Sz (Θ +r) ≡ suc k → Sz Θ ≡ k
szʳ {Θ} τ p = suc-injective (trans (sym (Sz-+r Θ)) p)

szᵉ : ∀ {Θ Θ' k} → AList Θ Θ' → Sz (Θ +e) ≡ suc k → Sz Θ ≡ k
szᵉ {Θ} τ p = suc-injective (trans (sym (Sz-+e Θ)) p)

sz0ᵗ : ∀ {X : Set} {Θ Θ'} → AList Θ Θ' → Sz (Θ +ty) ≡ zero → X
sz0ᵗ τ ()

sz0ʳ : ∀ {X : Set} {Θ Θ'} → AList Θ Θ' → Sz (Θ +r) ≡ zero → X
sz0ʳ {Θ = Θ} τ p = no-suc (trans (sym (Sz-+r Θ)) p)

sz0ᵉ : ∀ {X : Set} {Θ Θ'} → AList Θ Θ' → Sz (Θ +e) ≡ zero → X
sz0ᵉ {Θ = Θ} τ p = no-suc (trans (sym (Sz-+e Θ)) p)

-- The scope is matched on, as the variable to be eliminated is the one
-- its counter counts.

flexᵗ : ∀ {Θ} → TyVar Θ → OVType Θ → Maybe (Sol Θ)
flexᵗ {scope zero    nr ne} ()  A
flexᵗ {scope (suc nt) nr ne} α A =
  mmap (λ A' → scope nt nr ne , A' /ᵗ α ∷ anil) (chkᵗ-v {scope nt nr ne} α A)

flexʳ : ∀ {Θ} → RVar Θ → RExp Θ → Maybe (Sol Θ)
flexʳ {scope nt zero    ne} ()  ρ
flexʳ {scope nt (suc nr) ne} i ρ =
  mmap (λ ρ' → scope nt nr ne , ρ' /ʳ i ∷ anil) (chkʳ-r {scope nt nr ne} i ρ)

flexᵉ : ∀ {Θ} → Rig Θ → EVar Θ → EExp Θ → Maybe (Sol Θ)
flexᵉ {scope nt nr zero}    rg ()  ε
flexᵉ {scope nt nr (suc ne)} rg i ε =
  if i ∈ᶠ rg then nothing
  else mmap (λ ε' → scope nt nr ne , ε' /ᵉ i ∷ anil) (chkᵉ-e {scope nt nr ne} i ε)

-- Two variables of the same sort: equal ones need no binding, and
-- of two distinct effect-grade variables the flexible one is bound

flexFlexᵗ : ∀ {Θ} → TyVar Θ → TyVar Θ → Maybe (Sol Θ)
flexFlexᵗ {Θ} α β = if ⌊ α ≟ᶠ β ⌋ then just (Θ , anil) else flexᵗ α (tvar β)

flexFlexʳ : ∀ {Θ} → RVar Θ → RVar Θ → Maybe (Sol Θ)
flexFlexʳ {Θ} i j = if ⌊ i ≟ᶠ j ⌋ then just (Θ , anil) else flexʳ i (rvar j)

flexFlexᵉ : ∀ {Θ} → Rig Θ → EVar Θ → EVar Θ → Maybe (Sol Θ)
flexFlexᵉ {Θ} rg i j =
  if ⌊ i ≟ᶠ j ⌋ then just (Θ , anil)
  else (flexᵉ rg i (evar j) <∣> flexᵉ rg j (evar i))

mutual

  amguᵛ : ∀ {Θ} → (k : ℕ) → Sz Θ ≡ k → Rig Θ
        → OVType Θ → OVType Θ → Sol Θ → Maybe (Sol Θ)

  amguᶜ : ∀ {Θ} → (k : ℕ) → Sz Θ ≡ k → Rig Θ
        → OCType Θ → OCType Θ → Sol Θ → Maybe (Sol Θ)

  amguʳ : ∀ {Θ} → (k : ℕ) → Sz Θ ≡ k → Rig Θ
        → RExp Θ → RExp Θ → Sol Θ → Maybe (Sol Θ)

  amguᵉ : ∀ {Θ} → (k : ℕ) → Sz Θ ≡ k → Rig Θ
        → EExp Θ → EExp Θ → Sol Θ → Maybe (Sol Θ)

  -- value types

  amguᵛ (suc k) p rg A B (Θ' , X /ᵗ α ∷ τ) =
    mmap (consᵗ X α)
         (amguᵛ k (szᵗ τ p) rg (A [ X forᵗ α ]ᵛ) (B [ X forᵗ α ]ᵛ) (Θ' , τ))
  amguᵛ (suc k) p rg A B (Θ' , X /ʳ i ∷ τ) =
    mmap (consʳ X i)
         (amguᵛ k (szʳ τ p) rg (A [ X forʳ i ]ᵛ) (B [ X forʳ i ]ᵛ) (Θ' , τ))
  amguᵛ (suc k) p rg A B (Θ' , ε /ᵉ i ∷ τ) =
    mmap (consᵉ ε i)
         (amguᵛ k (szᵉ τ p) (popʳᵍ τ i rg) (A [ ε forᵉ i ]ᵛ) (B [ ε forᵉ i ]ᵛ) (Θ' , τ))
  amguᵛ zero p rg A B (Θ' , X /ᵗ α ∷ τ) = sz0ᵗ τ p
  amguᵛ zero p rg A B (Θ' , X /ʳ i ∷ τ) = sz0ʳ τ p
  amguᵛ zero p rg A B (Θ' , ε /ᵉ i ∷ τ) = sz0ᵉ τ p
  amguᵛ k p rg (tvar α)   (tvar β)    (_ , anil)   = flexFlexᵗ α β
  amguᵛ k p rg (tvar α)   B           (_ , anil)   = flexᵗ α B
  amguᵛ k p rg A          (tvar β)    (_ , anil)   = flexᵗ β A
  amguᵛ k p rg (Base b)   (Base b')  s@(_ , anil)  = if ⌊ b ≡ᵇ? b' ⌋ then just s else nothing
  amguᵛ k p rg Unit       Unit       s@(_ , anil)  = just s
  amguᵛ k p rg Bool       Bool       s@(_ , anil)  = just s
  amguᵛ k p rg Empty      Empty      s@(_ , anil)  = just s
  amguᵛ k p rg (A |×| A') (B |×| B') s@(_ , anil)  = amguᵛ k p rg A B s >>= amguᵛ k p rg A' B'
  amguᵛ k p rg (A ⇒ C)    (B ⇒ D)    s@(_ , anil)  = amguᵛ k p rg A B s >>= amguᶜ k p rg C D
  amguᵛ k p rg ([ ρ ] A)  ([ ρ' ] B) s@(_ , anil)  = amguʳ k p rg ρ ρ' s >>= amguᵛ k p rg A B
  amguᵛ k p rg A          B           (_ , anil)   = nothing

  -- computation types

  amguᶜ (suc k) p rg C D (Θ' , X /ᵗ α ∷ τ) =
    mmap (consᵗ X α)
         (amguᶜ k (szᵗ τ p) rg (C [ X forᵗ α ]ᶜ) (D [ X forᵗ α ]ᶜ) (Θ' , τ))
  amguᶜ (suc k) p rg C D (Θ' , X /ʳ i ∷ τ) =
    mmap (consʳ X i)
         (amguᶜ k (szʳ τ p) rg (C [ X forʳ i ]ᶜ) (D [ X forʳ i ]ᶜ) (Θ' , τ))
  amguᶜ (suc k) p rg C D (Θ' , ε /ᵉ i ∷ τ) =
    mmap (consᵉ ε i)
         (amguᶜ k (szᵉ τ p) (popʳᵍ τ i rg) (C [ ε forᵉ i ]ᶜ) (D [ ε forᵉ i ]ᶜ) (Θ' , τ))
  amguᶜ zero p rg C D (Θ' , X /ᵗ α ∷ τ) = sz0ᵗ τ p
  amguᶜ zero p rg C D (Θ' , X /ʳ i ∷ τ) = sz0ʳ τ p
  amguᶜ zero p rg C D (Θ' , ε /ᵉ i ∷ τ) = sz0ᵉ τ p
  amguᶜ k p rg (A ‼ ε) (B ‼ ε') s@(_ , anil) = amguᵛ k p rg A B s >>= amguᵉ k p rg ε ε'

  -- resource grades

  amguʳ (suc k) p rg ρ ρ' (Θ' , X /ᵗ α ∷ τ) =
    mmap (consᵗ X α)
         (amguʳ k (szᵗ τ p) rg (ρ [ X forᵗ α ]ʳ) (ρ' [ X forᵗ α ]ʳ) (Θ' , τ))
  amguʳ (suc k) p rg ρ ρ' (Θ' , X /ʳ i ∷ τ) =
    mmap (consʳ X i)
         (amguʳ k (szʳ τ p) rg (ρ [ X forʳ i ]ʳ) (ρ' [ X forʳ i ]ʳ) (Θ' , τ))
  amguʳ (suc k) p rg ρ ρ' (Θ' , ε /ᵉ i ∷ τ) =
    mmap (consᵉ ε i)
         (amguʳ k (szᵉ τ p) (popʳᵍ τ i rg) (ρ [ ε forᵉ i ]ʳ) (ρ' [ ε forᵉ i ]ʳ) (Θ' , τ))
  amguʳ zero p rg ρ ρ' (Θ' , X /ᵗ α ∷ τ) = sz0ᵗ τ p
  amguʳ zero p rg ρ ρ' (Θ' , X /ʳ i ∷ τ) = sz0ʳ τ p
  amguʳ zero p rg ρ ρ' (Θ' , ε /ᵉ i ∷ τ) = sz0ᵉ τ p
  amguʳ k p rg (rvar i)    (rvar j)      (_ , anil)  = flexFlexʳ i j
  amguʳ k p rg (rvar i)    ρ             (_ , anil)  = flexʳ i ρ
  amguʳ k p rg ρ           (rvar j)      (_ , anil)  = flexʳ j ρ
  amguʳ k p rg (rconst c)  (rconst d)   s@(_ , anil) = if ⌊ c ≡ᵣ? d ⌋ then just s else nothing
  amguʳ k p rg (ρ₁ ·̂ᵣ ρ₂) (ρ₁' ·̂ᵣ ρ₂') s@(_ , anil) = amguʳ k p rg ρ₁ ρ₁' s >>= amguʳ k p rg ρ₂ ρ₂'
  amguʳ k p rg (ρ₁ ⊔̂ᵣ ρ₂) (ρ₁' ⊔̂ᵣ ρ₂') s@(_ , anil) = amguʳ k p rg ρ₁ ρ₁' s >>= amguʳ k p rg ρ₂ ρ₂'
  amguʳ k p rg ∣ ε ∣̂ᵉ      ∣ ε' ∣̂ᵉ      s@(_ , anil) = amguᵉ k p rg ε ε' s
  amguʳ k p rg ρ           ρ'            (_ , anil)  = nothing

  -- effect grades

  amguᵉ (suc k) p rg ε ε' (Θ' , X /ᵗ α ∷ τ) =
    mmap (consᵗ X α)
         (amguᵉ k (szᵗ τ p) rg (ε [ X forᵗ α ]ᵉ) (ε' [ X forᵗ α ]ᵉ) (Θ' , τ))
  amguᵉ (suc k) p rg ε ε' (Θ' , X /ʳ i ∷ τ) =
    mmap (consʳ X i)
         (amguᵉ k (szʳ τ p) rg (ε [ X forʳ i ]ᵉ) (ε' [ X forʳ i ]ᵉ) (Θ' , τ))
  amguᵉ (suc k) p rg ε ε' (Θ' , ε'' /ᵉ i ∷ τ) =
    mmap (consᵉ ε'' i)
         (amguᵉ k (szᵉ τ p) (popʳᵍ τ i rg) (ε [ ε'' forᵉ i ]ᵉ) (ε' [ ε'' forᵉ i ]ᵉ) (Θ' , τ))
  amguᵉ zero p rg ε ε' (Θ' , X /ᵗ α ∷ τ)   = sz0ᵗ τ p
  amguᵉ zero p rg ε ε' (Θ' , X /ʳ i ∷ τ)   = sz0ʳ τ p
  amguᵉ zero p rg ε ε' (Θ' , ε'' /ᵉ i ∷ τ) = sz0ᵉ τ p
  amguᵉ k p rg (evar i)    (evar j)      (_ , anil)  = flexFlexᵉ rg i j
  amguᵉ k p rg (evar i)    ε             (_ , anil)  = flexᵉ rg i ε
  amguᵉ k p rg ε           (evar j)      (_ , anil)  = flexᵉ rg j ε
  amguᵉ k p rg (econst c)  (econst d)   s@(_ , anil) = if ⌊ c ≡ₑ? d ⌋ then just s else nothing
  amguᵉ k p rg (ε₁ ·̂ₑ ε₂) (ε₁' ·̂ₑ ε₂') s@(_ , anil) = amguᵉ k p rg ε₁ ε₁' s >>= amguᵉ k p rg ε₂ ε₂'
  amguᵉ k p rg (ε₁ ⊔̂ₑ ε₂) (ε₁' ⊔̂ₑ ε₂') s@(_ , anil) = amguᵉ k p rg ε₁ ε₁' s >>= amguᵉ k p rg ε₂ ε₂'
  amguᵉ k p rg ε           ε'            (_ , anil)  = nothing

amguᴱ : ∀ {Θ} → Rig Θ → Eqn Θ → Sol Θ → Maybe (Sol Θ)
amguᴱ {Θ} rg (eqᵛ A B)  s = amguᵛ (Sz Θ) refl rg A B s
amguᴱ {Θ} rg (eqᶜ C D)  s = amguᶜ (Sz Θ) refl rg C D s
amguᴱ {Θ} rg (eqʳ ρ ρ') s = amguʳ (Sz Θ) refl rg ρ ρ' s
amguᴱ {Θ} rg (eqᵉ ε ε') s = amguᵉ (Sz Θ) refl rg ε ε' s

unifyᴬ : ∀ {Θ} → Rig Θ → Eqns Θ → Sol Θ → Maybe (Sol Θ)
unifyᴬ rg []       s = just s
unifyᴬ rg (e ∷ es) s = amguᴱ rg e s >>= unifyᴬ rg es

unify : ∀ {Θ} → Rig Θ → Eqns Θ → Maybe (Σ[ Θ⁺ ∈ Scope ] AList Θ Θ⁺)
unify {Θ} rg es = unifyᴬ rg es (Θ , anil)

private

  -- one variable of each sort

  Θ₁ : Scope
  Θ₁ = ∅ˢ +ty +r +e

  -- a type variable is bound, and leaves the scope

  ex-tvar : unify {Θ₁} [] (eqᵛ (tvar (newᵗ {∅ˢ +r +e})) Unit ∷ [])
          ≡ just (∅ˢ +r +e , Unit /ᵗ newᵗ {∅ˢ +r +e} ∷ anil)
  ex-tvar = refl

  -- a resource-grade variable is bound to the image of an effect grade

  ex-rvar : unify {Θ₁} [] (eqʳ ∣ evar (newᵉ {∅ˢ +ty +r}) ∣̂ᵉ (rvar (newʳ {∅ˢ +ty})) ∷ [])
          ≡ just (∅ˢ +ty +e , ∣ evar (newᵉ {∅ˢ +ty}) ∣̂ᵉ /ʳ newʳ {∅ˢ +ty} ∷ anil)
  ex-rvar = refl

  -- the same image against a resource constant is a clash

  ex-clash : unify {Θ₁} [] (eqʳ ∣ evar (newᵉ {∅ˢ +ty +r}) ∣̂ᵉ ûᵣ ∷ []) ≡ nothing
  ex-clash = refl

  -- an effect-grade variable is bound, unless it is declared rigid

  ex-evar : unify {Θ₁} [] (eqᵉ (evar (newᵉ {∅ˢ +ty +r})) ûₑ ∷ [])
          ≡ just (∅ˢ +ty +r , ûₑ /ᵉ newᵉ {∅ˢ +ty +r} ∷ anil)
  ex-evar = refl

  ex-rigid : unify {Θ₁} (newᵉ {∅ˢ +ty +r} ∷ []) (eqᵉ (evar (newᵉ {∅ˢ +ty +r})) ûₑ ∷ [])
           ≡ nothing
  ex-rigid = refl
