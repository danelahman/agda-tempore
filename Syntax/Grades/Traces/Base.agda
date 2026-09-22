------------------------------------------------------------------------
-- Timed traces and their monoid structure.                            --
--                                                                     --
-- A timed trace is one run of a computation as it is observed from     --
-- outside: an alternation of positive delays and operations. The       --
-- monoid sequences two runs, merging the trailing delay of the first   --
-- with the leading delay of the second, so that a trace has a unique   --
-- representation with no two adjacent delays.                          --
--                                                                     --
-- This is the trace layer alone. The sets of traces the grades are     --
-- built from live in `Traces.Sets`, and the positive durations a delay --
-- carries in `Traces.Positive`, which is re-exported here.             --
------------------------------------------------------------------------

open import Util.Equality

-- Trace-based grades are parameterised by a set `Op` of operation names.

module Syntax.Grades.Traces.Base (Op : Set) where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no)

-- a delay carries a strictly positive duration

open import Syntax.Grades.Traces.Positive public

------------------------------------------------------------------------
-- Timed traces
--
-- The empty trace is `ε`; `operation o t` prepends an operation (with
-- no delay before it); and `delay d t` prepends a positive delay before
-- a delay-free-headed trace `t`. A delay node thus carries only its
-- duration, an operation node only its operation, and the `Trace⁻`
-- continuation of a delay rules out adjacent delays.

mutual

  data Trace : Set where
    ε         : Trace
    operation : Op → Trace → Trace
    delay     : ℕ⁺ → Trace⁻ → Trace

  -- timed traces that do not begin with a delay

  data Trace⁻ : Set where
    ε⁻         : Trace⁻
    operation⁻ : Op → Trace → Trace⁻

-- the pure delay of duration n (a zero delay is just the empty trace)

⟨_⟩ : ℕ → Trace
⟨ zero  ⟩ = ε
⟨ suc n ⟩ = delay (1+ n) ε⁻

-- a single operation event (no surrounding delay)

⌈_⌉ : Op → Trace
⌈ op ⌉ = operation op ε

-- the delay-free injection of `Trace⁻` into `Trace`

inj⁻ : Trace⁻ → Trace
inj⁻ ε⁻               = ε
inj⁻ (operation⁻ o t) = operation o t

-- it is injective, the two shapes it lands on being distinct

inj⁻-inj : {s⁻ t⁻ : Trace⁻} → inj⁻ s⁻ ≡ inj⁻ t⁻ → s⁻ ≡ t⁻
inj⁻-inj {ε⁻}             {ε⁻}             _    = refl
inj⁻-inj {ε⁻}             {operation⁻ _ _} ()
inj⁻-inj {operation⁻ _ _} {ε⁻}             ()
inj⁻-inj {operation⁻ _ _} {operation⁻ _ _} refl = refl

------------------------------------------------------------------------
-- The monoid structure

-- prepending a positive delay to a trace,
-- merging it with the leading delay of the trace

prepend : ℕ⁺ → Trace → Trace
prepend d ε                = delay d ε⁻
prepend d (operation op t) = delay d (operation⁻ op t)
prepend d (delay e t)      = delay (d +⁺ e) t

-- sequencing of two timed traces; the trailing delay of the first trace
-- is merged with the leading delay of the second trace

infixl 7 _∙_

_∙_ : Trace → Trace → Trace
ε                        ∙ t = t
operation o s            ∙ t = operation o (s ∙ t)
delay d ε⁻               ∙ t = prepend d t
delay d (operation⁻ o s) ∙ t = delay d (operation⁻ o (s ∙ t))

-- the monoid laws

∙-identityˡ : (t : Trace) → (ε ∙ t) ≡ t
∙-identityˡ t = refl

∙-identityʳ : (t : Trace) → (t ∙ ε) ≡ t
∙-identityʳ ε                          = refl
∙-identityʳ (operation o t)            = cong (operation o) (∙-identityʳ t)
∙-identityʳ (delay d ε⁻)               = refl
∙-identityʳ (delay d (operation⁻ o t)) = cong (λ z → delay d (operation⁻ o z)) (∙-identityʳ t)

-- prepending commutes with the additive merging of delays

prepend-+⁺ : (d e : ℕ⁺) (u : Trace) → prepend (d +⁺ e) u ≡ prepend d (prepend e u)
prepend-+⁺ d e ε                = refl
prepend-+⁺ d e (operation o u)  = refl
prepend-+⁺ d e (delay f u)      = cong (λ z → delay z u) (+⁺-assoc d e f)

-- prepending commutes with sequencing on the right

prepend-∙ : (d : ℕ⁺) (t u : Trace) → ((prepend d t) ∙ u) ≡ prepend d (t ∙ u)
prepend-∙ d ε                        u = refl
prepend-∙ d (operation o t)          u = refl
prepend-∙ d (delay e ε⁻)             u = prepend-+⁺ d e u
prepend-∙ d (delay e (operation⁻ o t)) u = refl

∙-assoc : (s t u : Trace) → ((s ∙ t) ∙ u) ≡ (s ∙ (t ∙ u))
∙-assoc ε                          t u = refl
∙-assoc (operation o s)            t u = cong (operation o) (∙-assoc s t u)
∙-assoc (delay d ε⁻)               t u = prepend-∙ d t u
∙-assoc (delay d (operation⁻ o s)) t u = cong (λ z → delay d (operation⁻ o z)) (∙-assoc s t u)

------------------------------------------------------------------------
-- Conicality
--
-- The monoid is conical: a product is the empty trace only if both
-- factors are. This is what the grades' zero-product properties, and
-- hence the "no time passes" grade, rest on.

∙-conicalˡ : {s t : Trace} → (s ∙ t) ≡ ε → s ≡ ε
∙-conicalˡ {ε}                          _  = refl
∙-conicalˡ {operation _ _}              ()
∙-conicalˡ {delay _ (operation⁻ _ _)}   ()
∙-conicalˡ {delay _ ε⁻} {ε}             ()
∙-conicalˡ {delay _ ε⁻} {operation _ _} ()
∙-conicalˡ {delay _ ε⁻} {delay _ _}     ()

∙-conicalʳ : {s t : Trace} → (s ∙ t) ≡ ε → t ≡ ε
∙-conicalʳ {ε}                          eq = eq
∙-conicalʳ {operation _ _}              ()
∙-conicalʳ {delay _ (operation⁻ _ _)}   ()
∙-conicalʳ {delay _ ε⁻} {ε}             ()
∙-conicalʳ {delay _ ε⁻} {operation _ _} ()
∙-conicalʳ {delay _ ε⁻} {delay _ _}     ()

------------------------------------------------------------------------
-- Left cancellation
--
-- Sequencing a fixed prefix on the left is injective in the
-- continuation.

-- injectivity of the `delay`, `operation`, and delayed-operation heads

delay-inj₁ : ∀ {d d' u u'} → delay d u ≡ delay d' u' → d ≡ d'
delay-inj₁ refl = refl

delay-inj₂ : ∀ {d d' u u'} → delay d u ≡ delay d' u' → u ≡ u'
delay-inj₂ refl = refl

operation-inj : ∀ {o u v} → operation o u ≡ operation o v → u ≡ v
operation-inj refl = refl

delay-operation-inj : ∀ {d o u v}
                    → delay d (operation⁻ o u) ≡ delay d (operation⁻ o v) → u ≡ v
delay-operation-inj refl = refl

-- prepending a fixed delay is injective in the continuation

prepend-injʳ : (d : ℕ⁺) {t t' : Trace} → prepend d t ≡ prepend d t' → t ≡ t'
prepend-injʳ d {ε}             {ε}             _  = refl
prepend-injʳ d {ε}             {operation _ _} ()
prepend-injʳ d {ε}             {delay e' u'}   eq =
  ⊥-elim (d≢d+⁺e d e' (sym (delay-inj₁ eq)))
prepend-injʳ d {operation _ _} {ε}             ()
prepend-injʳ d {operation _ _} {operation _ _} refl = refl
prepend-injʳ d {operation _ _} {delay e' u'}   eq =
  ⊥-elim (d≢d+⁺e d e' (sym (delay-inj₁ eq)))
prepend-injʳ d {delay e u}     {ε}             eq =
  ⊥-elim (d≢d+⁺e d e (delay-inj₁ eq))
prepend-injʳ d {delay e u}     {operation _ _} eq =
  ⊥-elim (d≢d+⁺e d e (delay-inj₁ eq))
prepend-injʳ d {delay e u}     {delay e' u'}   eq =
  cong₂ delay (+⁺-cancelˡ d (delay-inj₁ eq)) (delay-inj₂ eq)

-- sequencing on the left is injective in the right factor

∙-cancelˡ : (s : Trace) {t t' : Trace} → (s ∙ t) ≡ (s ∙ t') → t ≡ t'
∙-cancelˡ ε                          eq = eq
∙-cancelˡ (operation o s)            eq = ∙-cancelˡ s (operation-inj eq)
∙-cancelˡ (delay d ε⁻)               eq = prepend-injʳ d eq
∙-cancelˡ (delay d (operation⁻ o s)) eq = ∙-cancelˡ s (delay-operation-inj eq)

------------------------------------------------------------------------
-- Pure delays are a monoid homomorphism
--
-- Adding durations corresponds to sequencing the pure delays, which is
-- what the inclusion of ℕ into the trace-based grades is built on.

⟨⟩-hom : (m n : ℕ) → ⟨ m + n ⟩ ≡ (⟨ m ⟩ ∙ ⟨ n ⟩)
⟨⟩-hom zero    n       = refl
⟨⟩-hom (suc m) zero    = cong (λ z → delay (1+ z) ε⁻) (+-identityʳ m)
⟨⟩-hom (suc m) (suc n) = cong (λ z → delay z ε⁻) (sym (1+-+⁺ m n))

------------------------------------------------------------------------
-- Traces have decidable equality, given decidable equality of the
-- operation symbols they mention.

module DecTrace (_≟ₒ_ : DecidableEquality Op) where

  mutual

    _≟ᵀ_ : DecidableEquality Trace
    ε           ≟ᵀ ε           = yes refl
    ε           ≟ᵀ operation _ _ = no λ ()
    ε           ≟ᵀ delay _ _    = no λ ()
    operation _ _ ≟ᵀ ε          = no λ ()
    operation o s ≟ᵀ operation o' s' with o ≟ₒ o' | s ≟ᵀ s'
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ { refl → ¬p refl }
    ... | _        | no ¬q    = no λ { refl → ¬q refl }
    operation _ _ ≟ᵀ delay _ _  = no λ ()
    delay _ _   ≟ᵀ ε            = no λ ()
    delay _ _   ≟ᵀ operation _ _ = no λ ()
    delay d s   ≟ᵀ delay d' s'  with d ≟⁺ d' | s ≟ᵀ⁻ s'
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ { refl → ¬p refl }
    ... | _        | no ¬q    = no λ { refl → ¬q refl }

    -- decidable equality of delay-free-headed traces

    _≟ᵀ⁻_ : DecidableEquality Trace⁻
    ε⁻            ≟ᵀ⁻ ε⁻            = yes refl
    ε⁻            ≟ᵀ⁻ operation⁻ _ _ = no λ ()
    operation⁻ _ _ ≟ᵀ⁻ ε⁻           = no λ ()
    operation⁻ o s ≟ᵀ⁻ operation⁻ o' s' with o ≟ₒ o' | s ≟ᵀ s'
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ { refl → ¬p refl }
    ... | _        | no ¬q    = no λ { refl → ¬q refl }
