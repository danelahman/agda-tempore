------------------------------------------------------------------
-- Syntactic equality, and the witness probe                     --
--                                                                --
-- Two proof-free ingredients of the solver.                      --
--                                                                --
-- `_≟ᵛ_` and friends are `Maybe`-valued equality tests: a `just`  --
-- carries the equation, a `nothing` says nothing. Full           --
-- decidability is not needed — the solver only ever consumes the  --
-- positive answer — and the negative clauses would treble the     --
-- size.                                                          --
--                                                                --
-- The probe reads a witness for a variable off the constraint it  --
-- occurs in. Exactly one variable is the hole, the variables      --
-- already fixed by the substitution so far carry their values,    --
-- and the variables bound by inner existentials are unknown. A    --
-- pattern equation with the hole on one side and an evaluable     --
-- other side then yields the witness.                             --
--                                                                --
-- Evaluating the other side may itself meet an unknown — the      --
-- result type of a `lam` is the *whole* pattern `α₁ ⇒ (α₂ ‼ e)`,  --
-- none of whose variables is fixed yet — so evaluation resolves   --
-- an unknown by probing for it in turn, and defaults it when that --
-- fails. The recursion is staged (`Stage`, `res`): stage `n + 1`  --
-- resolves with stage `n`, so it terminates outright rather than  --
-- on fuel, and stage `0` resolves nothing.                        --
--                                                                --
-- Every probe runs twice: once strictly, where an unknown blocks  --
-- evaluation, and only then laxly, where it is resolved or        --
-- defaulted. A defaulted guess must not pre-empt an equation that --
-- pins the hole outright. Moving the hole blocks the old one      --
-- (`blk`), so a resolution cannot cycle back through the variable --
-- it is being run for.                                            --
--                                                                --
-- Nothing here is certified: every candidate the probe returns is --
-- checked by the solver proper.                                   --
------------------------------------------------------------------

open import Data.Bool.Base using () renaming (Bool to 𝔹; true to lax; false to strict)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)

open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import Inference.Scopes

module Inference.SolverImpl.Match (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (BaseType; _≡ᵇ?_)

open import Inference.Open.Grades S
open import Inference.Open.Types  S
open import Inference.Open.Subst  S

open import Inference.Constraints.Syntax S

--------------------------------------------------------------
-- `Maybe` plumbing                                          --
--------------------------------------------------------------

orElse : ∀ {A : Set} → Maybe A → Maybe A → Maybe A
orElse (just x) _ = just x
orElse nothing  m = m

mbind : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
mbind nothing  f = nothing
mbind (just x) f = f x

orDefault : ∀ {A : Set} → A → Maybe A → A
orDefault d nothing  = d
orDefault d (just x) = x

-- What an unknown variable evaluates to: nothing in a strict pass,
-- its resolution — or the default — in a lax one

onUnk : ∀ {A : Set} → 𝔹 → A → Maybe A → Maybe A
onUnk strict d m = nothing
onUnk lax    d m = just (orDefault d m)

-- A guess is only a guess: it must not pre-empt a strict answer

whenLax : ∀ {A : Set} → 𝔹 → Maybe A → Maybe A
whenLax strict m = nothing
whenLax lax    m = m

--------------------------------------------------------------
-- `Maybe`-valued syntactic equality                         --
--------------------------------------------------------------

infix 4 _≟ᵉ_ _≟ʳ_ _≟ᵛ_ _≟ᶜ_

_≟ᵉ_ : ∀ {Θ} → (ε ε' : EExp Θ) → Maybe (ε ≡ ε')
evar i ≟ᵉ evar j with i ≟ᶠ j
... | yes refl = just refl
... | no _     = nothing
econst c ≟ᵉ econst d with c ≡ₑ? d
... | yes refl = just refl
... | no _     = nothing
(ε₁ ·̂ₑ ε₂) ≟ᵉ (ε₁' ·̂ₑ ε₂') with ε₁ ≟ᵉ ε₁' | ε₂ ≟ᵉ ε₂'
... | just refl | just refl = just refl
... | _         | _         = nothing
_ ≟ᵉ _ = nothing

_≟ʳ_ : ∀ {Θ} → (ρ ρ' : RExp Θ) → Maybe (ρ ≡ ρ')
rvar i ≟ʳ rvar j with i ≟ᶠ j
... | yes refl = just refl
... | no _     = nothing
rconst c ≟ʳ rconst d with c ≡ᵣ? d
... | yes refl = just refl
... | no _     = nothing
(ρ₁ ·̂ᵣ ρ₂) ≟ʳ (ρ₁' ·̂ᵣ ρ₂') with ρ₁ ≟ʳ ρ₁' | ρ₂ ≟ʳ ρ₂'
... | just refl | just refl = just refl
... | _         | _         = nothing
∣ ε ∣̂ᵉ ≟ʳ ∣ ε' ∣̂ᵉ with ε ≟ᵉ ε'
... | just refl = just refl
... | nothing   = nothing
_ ≟ʳ _ = nothing

mutual

  _≟ᵛ_ : ∀ {Θ} → (A B : OVType Θ) → Maybe (A ≡ B)
  tvar α ≟ᵛ tvar β with α ≟ᶠ β
  ... | yes refl = just refl
  ... | no _     = nothing
  Base b ≟ᵛ Base b' with b ≡ᵇ? b'
  ... | yes refl = just refl
  ... | no _     = nothing
  Unit ≟ᵛ Unit = just refl
  Bool ≟ᵛ Bool = just refl
  Empty ≟ᵛ Empty = just refl
  (A₁ |×| A₂) ≟ᵛ (B₁ |×| B₂) with A₁ ≟ᵛ B₁ | A₂ ≟ᵛ B₂
  ... | just refl | just refl = just refl
  ... | _         | _         = nothing
  (A ⇒ C) ≟ᵛ (B ⇒ D) with A ≟ᵛ B | C ≟ᶜ D
  ... | just refl | just refl = just refl
  ... | _         | _         = nothing
  ([ ρ ] A) ≟ᵛ ([ ρ' ] B) with ρ ≟ʳ ρ' | A ≟ᵛ B
  ... | just refl | just refl = just refl
  ... | _         | _         = nothing
  _ ≟ᵛ _ = nothing

  _≟ᶜ_ : ∀ {Θ} → (C D : OCType Θ) → Maybe (C ≡ D)
  (A ‼ ε) ≟ᶜ (B ‼ ε') with A ≟ᵛ B | ε ≟ᵉ ε'
  ... | just refl | just refl = just refl
  ... | _         | _         = nothing

--------------------------------------------------------------
-- Probe environments                                        --
--------------------------------------------------------------

data Kn (X : Set) : Set where
  hole : Kn X                  -- the variable being probed for
  kn   : X → Kn X              -- fixed by the substitution so far
  unk  : Kn X                  -- bound by an inner existential
  blk  : Kn X                  -- the hole of an enclosing probe

record PEnv (Θ' Ξ : Scope) : Set where
  constructor penv
  field
    kTy : TyVar Ξ → Kn (OVType Θ')
    kR  : RVar Ξ → Kn (RExp Θ')
    kE  : EVar Ξ → Kn (EExp Θ')

open PEnv

-- Everything the substitution so far fixes is known

knownˢ : ∀ {Θ Θ'} → Subst Θ Θ' → PEnv Θ' Θ
knownˢ σ = penv (λ α → kn (sTy σ α)) (λ i → kn (sR σ i)) (λ i → kn (sE σ i))

-- Passing under an existential binder: the bound variable is unknown

extᵗ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → PEnv Θ' (Ξ +ty)
extᵗ η = penv (λ { zero → unk ; (suc α) → kTy η α }) (kR η) (kE η)

extʳ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → PEnv Θ' (Ξ +r)
extʳ η = penv (kTy η) (λ { zero → unk ; (suc i) → kR η i }) (kE η)

extᵉ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → PEnv Θ' (Ξ +e)
extᵉ η = penv (kTy η) (kR η) (λ { zero → unk ; (suc i) → kE η i })

-- Moving the hole: the previous hole becomes blocked, so that
-- resolving the new one cannot cycle back through it

demote : ∀ {X : Set} → Kn X → Kn X
demote hole   = blk
demote blk    = blk
demote (kn x) = kn x
demote unk    = unk

pick : ∀ {n} {X : Set} → Fin n → Fin n → Kn X → Kn X
pick α β k with α ≟ᶠ β
... | yes _ = hole
... | no _  = k

setᵗ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → TyVar Ξ → PEnv Θ' Ξ
setᵗ η α = penv (λ β → pick α β (demote (kTy η β)))
                (λ i → demote (kR η i)) (λ i → demote (kE η i))

setʳ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → RVar Ξ → PEnv Θ' Ξ
setʳ η i = penv (λ β → demote (kTy η β))
                (λ j → pick i j (demote (kR η j))) (λ j → demote (kE η j))

setᵉ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → EVar Ξ → PEnv Θ' Ξ
setᵉ η i = penv (λ β → demote (kTy η β))
                (λ j → demote (kR η j)) (λ j → pick i j (demote (kE η j)))

-- The environments the solver starts a probe from: the newly bound
-- variable is the hole, everything else comes from the substitution

env⊙ᵗ : ∀ {Θ Θ'} → Subst Θ Θ' → PEnv Θ' (Θ +ty)
env⊙ᵗ σ = setᵗ (extᵗ (knownˢ σ)) zero

env⊙ʳ : ∀ {Θ Θ'} → Subst Θ Θ' → PEnv Θ' (Θ +r)
env⊙ʳ σ = setʳ (extʳ (knownˢ σ)) zero

env⊙ᵉ : ∀ {Θ Θ'} → Subst Θ Θ' → PEnv Θ' (Θ +e)
env⊙ᵉ σ = setᵉ (extᵉ (knownˢ σ)) zero

-- The environment a variable of the constraint's own scope is probed
-- in: that variable is the hole, the others keep their current values

env♯ᵗ : ∀ {Θ Θ'} → Subst Θ Θ' → TyVar Θ → PEnv Θ' Θ
env♯ᵗ σ α = setᵗ (knownˢ σ) α

env♯ʳ : ∀ {Θ Θ'} → Subst Θ Θ' → RVar Θ → PEnv Θ' Θ
env♯ʳ σ i = setʳ (knownˢ σ) i

env♯ᵉ : ∀ {Θ Θ'} → Subst Θ Θ' → EVar Θ → PEnv Θ' Θ
env♯ᵉ σ i = setᵉ (knownˢ σ) i

--------------------------------------------------------------
-- One-hole matching against a known type                    --
--------------------------------------------------------------

-- the hole is a type variable

mutual

  mVᵗ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → OVType Ξ → OVType Θ' → Maybe (OVType Θ')
  mVᵗ η (tvar α) T with kTy η α
  ... | hole = just T
  ... | _    = nothing
  mVᵗ η (A |×| B) (X |×| Y)  = orElse (mVᵗ η A X) (mVᵗ η B Y)
  mVᵗ η (A ⇒ C)   (X ⇒ D)    = orElse (mVᵗ η A X) (mCᵗ η C D)
  mVᵗ η ([ ρ ] A) ([ ρ' ] X) = mVᵗ η A X
  mVᵗ η _ _ = nothing

  mCᵗ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → OCType Ξ → OCType Θ' → Maybe (OVType Θ')
  mCᵗ η (A ‼ ε) (X ‼ ε') = mVᵗ η A X

-- the hole is a resource-grade variable

mRʳ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → RExp Ξ → RExp Θ' → Maybe (RExp Θ')
mRʳ η (rvar i) ρ' with kR η i
... | hole = just ρ'
... | _    = nothing
mRʳ η (ρ₁ ·̂ᵣ ρ₂) (ρ₁' ·̂ᵣ ρ₂') = orElse (mRʳ η ρ₁ ρ₁') (mRʳ η ρ₂ ρ₂')
mRʳ η _ _ = nothing

mutual

  mVʳ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → OVType Ξ → OVType Θ' → Maybe (RExp Θ')
  mVʳ η (A |×| B) (X |×| Y)  = orElse (mVʳ η A X) (mVʳ η B Y)
  mVʳ η (A ⇒ C)   (X ⇒ D)    = orElse (mVʳ η A X) (mCʳ η C D)
  mVʳ η ([ ρ ] A) ([ ρ' ] X) = orElse (mRʳ η ρ ρ') (mVʳ η A X)
  mVʳ η _ _ = nothing

  mCʳ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → OCType Ξ → OCType Θ' → Maybe (RExp Θ')
  mCʳ η (A ‼ ε) (X ‼ ε') = mVʳ η A X

-- the hole is an effect-grade variable

mEᵉ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → EExp Ξ → EExp Θ' → Maybe (EExp Θ')
mEᵉ η (evar i) ε' with kE η i
... | hole = just ε'
... | _    = nothing
mEᵉ η (ε₁ ·̂ₑ ε₂) (ε₁' ·̂ₑ ε₂') = orElse (mEᵉ η ε₁ ε₁') (mEᵉ η ε₂ ε₂')
mEᵉ η _ _ = nothing

mRᵉ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → RExp Ξ → RExp Θ' → Maybe (EExp Θ')
mRᵉ η (ρ₁ ·̂ᵣ ρ₂) (ρ₁' ·̂ᵣ ρ₂') = orElse (mRᵉ η ρ₁ ρ₁') (mRᵉ η ρ₂ ρ₂')
mRᵉ η ∣ ε ∣̂ᵉ ∣ ε' ∣̂ᵉ = mEᵉ η ε ε'
mRᵉ η _ _ = nothing

mutual

  mVᵉ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → OVType Ξ → OVType Θ' → Maybe (EExp Θ')
  mVᵉ η (A |×| B) (X |×| Y)  = orElse (mVᵉ η A X) (mVᵉ η B Y)
  mVᵉ η (A ⇒ C)   (X ⇒ D)    = orElse (mVᵉ η A X) (mCᵉ η C D)
  mVᵉ η ([ ρ ] A) ([ ρ' ] X) = orElse (mRᵉ η ρ ρ') (mVᵉ η A X)
  mVᵉ η _ _ = nothing

  mCᵉ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → OCType Ξ → OCType Θ' → Maybe (EExp Θ')
  mCᵉ η (A ‼ ε) (X ‼ ε') = orElse (mVᵉ η A X) (mEᵉ η ε ε')

--------------------------------------------------------------
-- Reading a value off an atom whose other side is the hole  --
--------------------------------------------------------------

atHoleᵗ : ∀ {Θ' Ξ} {X : Set} → PEnv Θ' Ξ → OVType Ξ → Maybe X → Maybe X
atHoleᵗ η (tvar α) m with kTy η α
... | hole = m
... | _    = nothing
atHoleᵗ η _ m = nothing

atHoleʳ : ∀ {Θ' Ξ} {X : Set} → PEnv Θ' Ξ → RExp Ξ → Maybe X → Maybe X
atHoleʳ η (rvar i) m with kR η i
... | hole = m
... | _    = nothing
atHoleʳ η _ m = nothing

atHoleᵉ : ∀ {Θ' Ξ} {X : Set} → PEnv Θ' Ξ → EExp Ξ → Maybe X → Maybe X
atHoleᵉ η (evar i) m with kE η i
... | hole = m
... | _    = nothing
atHoleᵉ η _ m = nothing

--------------------------------------------------------------
-- Staged resolution of the unknowns                         --
--------------------------------------------------------------

record Resolver (Θ' : Scope) : Set where
  constructor resolver
  field
    rᵗ : ∀ {Ξ} → PEnv Θ' Ξ → Constraint Ξ → TyVar Ξ → Maybe (OVType Θ')
    rʳ : ∀ {Ξ} → PEnv Θ' Ξ → Constraint Ξ → RVar Ξ → Maybe (RExp Θ')
    rᵉ : ∀ {Ξ} → PEnv Θ' Ξ → Constraint Ξ → EVar Ξ → Maybe (EExp Θ')

noRes : ∀ {Θ'} → Resolver Θ'
noRes = resolver (λ _ _ _ → nothing) (λ _ _ _ → nothing) (λ _ _ _ → nothing)

module Stage (Θ' : Scope) (r : Resolver Θ') where

  open Resolver r

  ------------------------------------------------------------
  -- Evaluating an expression into the target scope           --
  --                                                          --
  -- A known variable gives its value, the hole gives none,    --
  -- an unknown one is resolved against the enclosing          --
  -- constraint and defaulted if that fails.                   --
  ------------------------------------------------------------

  evE : ∀ {Ξ} → 𝔹 → PEnv Θ' Ξ → Constraint Ξ → EExp Ξ → Maybe (EExp Θ')
  evE l η Φ (evar i) with kE η i
  ... | kn ε = just ε
  ... | unk  = onUnk l ûₑ (rᵉ η Φ i)
  ... | _    = nothing
  evE l η Φ (econst c) = just (econst c)
  evE l η Φ (ε ·̂ₑ ε') with evE l η Φ ε | evE l η Φ ε'
  ... | just a | just b = just (a ·̂ₑ b)
  ... | _      | _      = nothing

  evR : ∀ {Ξ} → 𝔹 → PEnv Θ' Ξ → Constraint Ξ → RExp Ξ → Maybe (RExp Θ')
  evR l η Φ (rvar i) with kR η i
  ... | kn ρ = just ρ
  ... | unk  = onUnk l ûᵣ (rʳ η Φ i)
  ... | _    = nothing
  evR l η Φ (rconst c) = just (rconst c)
  evR l η Φ (ρ ·̂ᵣ ρ') with evR l η Φ ρ | evR l η Φ ρ'
  ... | just a | just b = just (a ·̂ᵣ b)
  ... | _      | _      = nothing
  evR l η Φ ∣ ε ∣̂ᵉ with evE l η Φ ε
  ... | just a  = just ∣ a ∣̂ᵉ
  ... | nothing = nothing

  mutual

    evV : ∀ {Ξ} → 𝔹 → PEnv Θ' Ξ → Constraint Ξ → OVType Ξ → Maybe (OVType Θ')
    evV l η Φ (tvar α) with kTy η α
    ... | kn A = just A
    ... | unk  = onUnk l Unit (rᵗ η Φ α)
    ... | _    = nothing
    evV l η Φ (Base b) = just (Base b)
    evV l η Φ Unit     = just Unit
    evV l η Φ Bool     = just Bool
    evV l η Φ Empty    = just Empty
    evV l η Φ (A |×| B) with evV l η Φ A | evV l η Φ B
    ... | just X | just Y = just (X |×| Y)
    ... | _      | _      = nothing
    evV l η Φ (A ⇒ C) with evV l η Φ A | evC l η Φ C
    ... | just X | just D = just (X ⇒ D)
    ... | _      | _      = nothing
    evV l η Φ ([ ρ ] A) with evR l η Φ ρ | evV l η Φ A
    ... | just ρ' | just X = just ([ ρ' ] X)
    ... | _       | _      = nothing

    evC : ∀ {Ξ} → 𝔹 → PEnv Θ' Ξ → Constraint Ξ → OCType Ξ → Maybe (OCType Θ')
    evC l η Φ (A ‼ ε) with evV l η Φ A | evE l η Φ ε
    ... | just X | just ε' = just (X ‼ ε')
    ... | _      | _       = nothing

  ------------------------------------------------------------
  -- The probes                                               --
  --                                                          --
  -- A probe walks the conjunctive structure and the           --
  -- existentials of a constraint, carrying the enclosing      --
  -- constraint of the current scope as the context that       --
  -- unknowns are resolved against. It stops at `∀ᵉ` (the      --
  -- target scope changes there) and at `⋀ᵒᵖ`.                 --
  ------------------------------------------------------------

  probeᵗ' : ∀ {Ξ} → 𝔹 → PEnv Θ' Ξ → Constraint Ξ → Constraint Ξ
          → Maybe (OVType Θ')
  probeᵗ' l η Φ (C ∧̂ D)     = orElse (probeᵗ' l η Φ C) (probeᵗ' l η Φ D)
  probeᵗ' l η Φ (A ≐ᵥ B)    = orElse (mbind (evV l η Φ B) (mVᵗ η A))
                                     (mbind (evV l η Φ A) (mVᵗ η B))
  probeᵗ' l η Φ (Etᶜ A)     = whenLax l (atHoleᵗ η A (just Unit))
  probeᵗ' l η Φ (Et∨≾ᵘ A ρ) = whenLax l (atHoleᵗ η A (just Unit))
  probeᵗ' l η Φ (∃ᵗ C)      = probeᵗ' l (extᵗ η) C C
  probeᵗ' l η Φ (∃ʳ C)      = probeᵗ' l (extʳ η) C C
  probeᵗ' l η Φ (∃ᵉ C)      = probeᵗ' l (extᵉ η) C C
  probeᵗ' l η Φ _           = nothing

  probeᵗ : ∀ {Ξ} → PEnv Θ' Ξ → Constraint Ξ → Maybe (OVType Θ')
  probeᵗ η C = orElse (probeᵗ' strict η C C) (probeᵗ' lax η C C)

  probeʳ' : ∀ {Ξ} → 𝔹 → PEnv Θ' Ξ → Constraint Ξ → Constraint Ξ
          → Maybe (RExp Θ')
  probeʳ' l η Φ (C ∧̂ D)     = orElse (probeʳ' l η Φ C) (probeʳ' l η Φ D)
  probeʳ' l η Φ (A ≐ᵥ B)    = orElse (mbind (evV l η Φ B) (mVʳ η A))
                                     (mbind (evV l η Φ A) (mVʳ η B))
  probeʳ' l η Φ (ρ ≾̂ᵣᶜ ρ')  = orElse (atHoleʳ η ρ' (evR l η Φ ρ))
                                     (atHoleʳ η ρ (evR l η Φ ρ'))
  probeʳ' l η Φ (Et∨≾ᵘ A ρ) = whenLax l (atHoleʳ η ρ (just ûᵣ))
  probeʳ' l η Φ (∃ᵗ C)      = probeʳ' l (extᵗ η) C C
  probeʳ' l η Φ (∃ʳ C)      = probeʳ' l (extʳ η) C C
  probeʳ' l η Φ (∃ᵉ C)      = probeʳ' l (extᵉ η) C C
  probeʳ' l η Φ _           = nothing

  probeʳ : ∀ {Ξ} → PEnv Θ' Ξ → Constraint Ξ → Maybe (RExp Θ')
  probeʳ η C = orElse (probeʳ' strict η C C) (probeʳ' lax η C C)

  probeᵉ' : ∀ {Ξ} → 𝔹 → PEnv Θ' Ξ → Constraint Ξ → Constraint Ξ
          → Maybe (EExp Θ')
  probeᵉ' l η Φ (C ∧̂ D)    = orElse (probeᵉ' l η Φ C) (probeᵉ' l η Φ D)
  probeᵉ' l η Φ (A ≐ᵥ B)   = orElse (mbind (evV l η Φ B) (mVᵉ η A))
                                    (mbind (evV l η Φ A) (mVᵉ η B))
  probeᵉ' l η Φ (ε ≾̂ₑᶜ ε') = orElse (atHoleᵉ η ε' (evE l η Φ ε))
                                    (atHoleᵉ η ε (evE l η Φ ε'))
  probeᵉ' l η Φ (∃ᵗ C)     = probeᵉ' l (extᵗ η) C C
  probeᵉ' l η Φ (∃ʳ C)     = probeᵉ' l (extʳ η) C C
  probeᵉ' l η Φ (∃ᵉ C)     = probeᵉ' l (extᵉ η) C C
  probeᵉ' l η Φ _          = nothing

  probeᵉ : ∀ {Ξ} → PEnv Θ' Ξ → Constraint Ξ → Maybe (EExp Θ')
  probeᵉ η C = orElse (probeᵉ' strict η C C) (probeᵉ' lax η C C)

  -- What this stage offers the next one

  next : Resolver Θ'
  next = resolver (λ η Φ α → probeᵗ (setᵗ η α) Φ)
                  (λ η Φ i → probeʳ (setʳ η i) Φ)
                  (λ η Φ i → probeᵉ (setᵉ η i) Φ)

--------------------------------------------------------------
-- The probes, at a fixed number of stages                   --
--------------------------------------------------------------

res : ℕ → (Θ' : Scope) → Resolver Θ'
res zero    Θ' = noRes
res (suc n) Θ' = Stage.next Θ' (res n Θ')

stages : ℕ
stages = 3

probeᵗ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → Constraint Ξ → Maybe (OVType Θ')
probeᵗ {Θ'} = Stage.probeᵗ Θ' (res stages Θ')

probeʳ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → Constraint Ξ → Maybe (RExp Θ')
probeʳ {Θ'} = Stage.probeʳ Θ' (res stages Θ')

probeᵉ : ∀ {Θ' Ξ} → PEnv Θ' Ξ → Constraint Ξ → Maybe (EExp Θ')
probeᵉ {Θ'} = Stage.probeᵉ Θ' (res stages Θ')
