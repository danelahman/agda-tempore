------------------------------------------------------------------------
-- The free graded tick monad on setoid-valued unit-monotone presheaves. --
--                                                                    --
-- Trees are built from                                                  --
--                                                                    --
--   * `leaf`      : a returned value of `A` (grade `uₑ`);              --
--   * `tick-node` : `δ` worth of time passes and nothing is observed. It --
--                   stores its Kripke continuation over every world      --
--                   reachable by `mapᵉ δ`;                              --
--   * `sub`       : sub-effecting.                                      --
--                                                                    --
-- A tick records nothing, so a coercion may be pushed under it: hence    --
-- `sub-tick` in the quotient below.                                      --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import DenotationalSemantics.Model.World
import DenotationalSemantics.Model.Example.PSh.Base as B
import DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module DenotationalSemantics.Model.Example.PSh.TickMonad
         (S : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
       where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)

open import Util.Equality

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops
open World Wld
open import DenotationalSemantics.Model.Example.PSh.Base Grades Wld
open import DenotationalSemantics.Model.Example.PSh.Modality.Future Grades Wld

mutual

  data Tᵏˢ (A : PSh) : E → W → Set where
    leaf      : ∀ {w} → carrier A w → Tᵏˢ A uₑ w
    tick-node : ∀ {ε w} → (δ : E)
              → (k : ∀ {w'} → w ⊑[ mapᵉ δ ] w' → Tᵏˢ A ε w')
              → (k-nat : ∀ {w' w''} (q : w ⊑[ mapᵉ δ ] w') (r : w' ⊑[ uᵣ ] w'')
                       → k (⊑ρ∘ᵘ q r) ≈ᵏ transportᵏ r (k q))
              → Tᵏˢ A (δ ·ₑ ε) w
    sub       : ∀ {ε ε' w} → ε ≾ₑ ε' → Tᵏˢ A ε w → Tᵏˢ A ε' w

  data _≈ᵏ_ {A : PSh} : {ε : E} {w : W} → Tᵏˢ A ε w → Tᵏˢ A ε w → Set where
    leaf-≈ : ∀ {w} {x y : carrier A w} → _≈_ A x y → leaf x ≈ᵏ leaf y
    tick-≈ : ∀ {ε w} {δ : E}
               {k k' : ∀ {w'} → w ⊑[ mapᵉ δ ] w' → Tᵏˢ A ε w'}
               {kn  : ∀ {w' w''} (q : w ⊑[ mapᵉ δ ] w') (r : w' ⊑[ uᵣ ] w'')
                    → k (⊑ρ∘ᵘ q r) ≈ᵏ transportᵏ r (k q)}
               {kn' : ∀ {w' w''} (q : w ⊑[ mapᵉ δ ] w') (r : w' ⊑[ uᵣ ] w'')
                    → k' (⊑ρ∘ᵘ q r) ≈ᵏ transportᵏ r (k' q)}
           → (∀ {w'} (q : w ⊑[ mapᵉ δ ] w') → k q ≈ᵏ k' q)
           → tick-node δ k kn ≈ᵏ tick-node δ k' kn'
    sub-≈  : ∀ {ε ε' w} {e e' : ε ≾ₑ ε'} {t t' : Tᵏˢ A ε w}
           → t ≈ᵏ t' → sub e t ≈ᵏ sub e' t'

    -- sub-effecting nodes are invisible …
    sub-u  : ∀ {ε w} {t : Tᵏˢ A ε w} → sub ≾ₑ-refl t ≈ᵏ t
    sub-∘  : ∀ {ε ε' ε'' w} {e : ε ≾ₑ ε'} {e' : ε' ≾ₑ ε''} {t : Tᵏˢ A ε w}
           → sub e' (sub e t) ≈ᵏ sub (≾ₑ-trans e e') t

    -- … and they pass under a tick: a tick stores nothing but the time it
    -- takes, so coercing its continuation and coercing the whole computation
    -- agree.
    sub-tick : ∀ {ε ε' w} {δ : E} {e : ε ≾ₑ ε'}
                 {k : ∀ {w'} → w ⊑[ mapᵉ δ ] w' → Tᵏˢ A ε w'}
                 {kn  : ∀ {w' w''} (q : w ⊑[ mapᵉ δ ] w') (r : w' ⊑[ uᵣ ] w'')
                      → k (⊑ρ∘ᵘ q r) ≈ᵏ transportᵏ r (k q)}
                 {kn' : ∀ {w' w''} (q : w ⊑[ mapᵉ δ ] w') (r : w' ⊑[ uᵣ ] w'')
                      → sub e (k (⊑ρ∘ᵘ q r)) ≈ᵏ transportᵏ r (sub e (k q))}
             → sub (·ₑ-monoʳ-≾ₑ e) (tick-node δ k kn)
             ≈ᵏ tick-node δ (λ q → sub e (k q)) kn'

    -- A tick that takes no time is no tick, and two consecutive ticks are the
    -- one tick by the product of their times. The image of the free monad's
    -- `delay-zero`/`delay-plus` under `implˢ`, and for the same reason: a tick
    -- records only the passage of time.

    tick-u : ∀ {ε w} {δ : E}
               {k : ∀ {w'} → w ⊑[ mapᵉ δ ] w' → Tᵏˢ A ε w'}
               {kn : ∀ {w' w''} (q : w ⊑[ mapᵉ δ ] w') (r : w' ⊑[ uᵣ ] w'')
                   → k (⊑ρ∘ᵘ q r) ≈ᵏ transportᵏ r (k q)}
               {q₀ : w ⊑[ mapᵉ δ ] w}
           → (u : δ ≃ₑ uₑ)
           → (e : ε ≾ₑ δ ·ₑ ε)
           → tick-node δ k kn ≈ᵏ sub e (k q₀)

    tick-· : ∀ {ε w} {δ δ₁ δ₂ : E}
               {k : ∀ {w'} → w ⊑[ mapᵉ δ ] w' → Tᵏˢ A ε w'}
               {kn : ∀ {w' w''} (q : w ⊑[ mapᵉ δ ] w') (r : w' ⊑[ uᵣ ] w'')
                   → k (⊑ρ∘ᵘ q r) ≈ᵏ transportᵏ r (k q)}
               {k' : ∀ {w'} → w ⊑[ mapᵉ δ₁ ] w'
                   → ∀ {w''} → w' ⊑[ mapᵉ δ₂ ] w'' → Tᵏˢ A ε w''}
               {kn₂ : ∀ {w'} (q₁ : w ⊑[ mapᵉ δ₁ ] w')
                    → ∀ {w'' w'''} (q₂ : w' ⊑[ mapᵉ δ₂ ] w'') (r : w'' ⊑[ uᵣ ] w''')
                    → k' q₁ (⊑ρ∘ᵘ q₂ r) ≈ᵏ transportᵏ r (k' q₁ q₂)}
               {kn₁ : ∀ {w' w''} (q₁ : w ⊑[ mapᵉ δ₁ ] w') (r : w' ⊑[ uᵣ ] w'')
                    → tick-node δ₂ (k' (⊑ρ∘ᵘ q₁ r)) (kn₂ (⊑ρ∘ᵘ q₁ r))
                    ≈ᵏ transportᵏ r (tick-node δ₂ (k' q₁) (kn₂ q₁))}
           → (m : δ ≃ₑ δ₁ ·ₑ δ₂)
           → (∀ {w' w''} (q₁ : w ⊑[ mapᵉ δ₁ ] w') (q₂ : w' ⊑[ mapᵉ δ₂ ] w'')
              → k' q₁ q₂
              ≈ᵏ k (⊑-mono (≃ᵣ⇒≾ᵣ (≃ᵣ-trans (≃ᵣ-sym map-·ᵉ) (map-≃ᵉ (≃ₑ-sym m))))
                     (⊑-trans q₁ q₂)))
           → (e : δ ·ₑ ε ≾ₑ δ₁ ·ₑ (δ₂ ·ₑ ε))
           → tick-node δ₁ (λ q₁ → tick-node δ₂ (k' q₁) (kn₂ q₁)) kn₁
           ≈ᵏ sub e (tick-node δ k kn)

    ≈ᵏ-sym   : ∀ {ε w} {t t' : Tᵏˢ A ε w} → t ≈ᵏ t' → t' ≈ᵏ t
    ≈ᵏ-trans : ∀ {ε w} {t t' t'' : Tᵏˢ A ε w} → t ≈ᵏ t' → t' ≈ᵏ t'' → t ≈ᵏ t''

  transportᵏ : ∀ {A ε w w'} → w ⊑[ uᵣ ] w' → Tᵏˢ A ε w → Tᵏˢ A ε w'
  transportᵏ {A} p (leaf x)          = leaf (transport A p x)
  transportᵏ p (tick-node δ k kn) =
    tick-node δ (λ q → k (⊑ᵘ∘ρ p q))
      (λ q r → subst (λ z → k z ≈ᵏ transportᵏ r (k (⊑ᵘ∘ρ p q)))
                 (⊑-irrelevant _ _) (kn (⊑ᵘ∘ρ p q) r))
  transportᵏ p (sub e t)             = sub e (transportᵏ p t)

infix 4 _≈ᵏ_

≈ᵏ-refl : ∀ {A ε w} (t : Tᵏˢ A ε w) → t ≈ᵏ t
≈ᵏ-refl {A} (leaf x)          = leaf-≈ (≈-refl A)
≈ᵏ-refl (tick-node δ k kn)    = tick-≈ (λ q → ≈ᵏ-refl (k q))
≈ᵏ-refl (sub e t)             = sub-≈ (≈ᵏ-refl t)

≡→≈ᵏ : ∀ {A ε w} {t t' : Tᵏˢ A ε w} → t ≡ t' → t ≈ᵏ t'
≡→≈ᵏ refl = ≈ᵏ-refl _

-- A sub-effecting node respects `_≈ᵏ_` at a fixed witness.

sub-congᵏ : ∀ {A ε ε' w} {e : ε ≾ₑ ε'} {t t' : Tᵏˢ A ε w} → t ≈ᵏ t' → sub e t ≈ᵏ sub e t'
sub-congᵏ = sub-≈

-- `sub-u`/`sub-∘` at *any* witnesses of the required orderings; the
-- constructors are stated at `≾ₑ-refl`/`≾ₑ-trans`, and sub-effecting witnesses
-- are proof-irrelevant.

sub-uᵏ : ∀ {A ε w} → (e : ε ≾ₑ ε) → (t : Tᵏˢ A ε w) → sub e t ≈ᵏ t
sub-uᵏ e t rewrite ≾ₑ-irrelevant e ≾ₑ-refl = sub-u

sub-∘ᵏ : ∀ {A ε ε' ε'' w} → (e : ε ≾ₑ ε') → (e' : ε' ≾ₑ ε'') → (e'' : ε ≾ₑ ε'')
       → (t : Tᵏˢ A ε w) → sub e' (sub e t) ≈ᵏ sub e'' t
sub-∘ᵏ e e' e'' t rewrite ≾ₑ-irrelevant e'' (≾ₑ-trans e e') = sub-∘

-- Two composites of sub-effecting nodes with the same endpoints agree.

sub-swapᵏ : ∀ {A ε₀ ε₁ ε₁' ε₂ w} (b : ε₀ ≾ₑ ε₁) (a : ε₁ ≾ₑ ε₂) (d : ε₀ ≾ₑ ε₁') (c : ε₁' ≾ₑ ε₂)
          → (t : Tᵏˢ A ε₀ w) → sub a (sub b t) ≈ᵏ sub c (sub d t)
sub-swapᵏ b a d c t =
  ≈ᵏ-trans (sub-∘ᵏ b a (≾ₑ-trans d c) t) (≈ᵏ-sym (sub-∘ᵏ d c (≾ₑ-trans d c) t))

-- Three sub-effecting nodes against two, with the same endpoints.

sub3ᵏ : ∀ {A ε₀ ε₁ ε₂ ε₃ ε₅ w}
      → (d : ε₀ ≾ₑ ε₁) (a : ε₁ ≾ₑ ε₅) (c : ε₀ ≾ₑ ε₂) (Y : ε₂ ≾ₑ ε₃) (X : ε₃ ≾ₑ ε₅)
      → (t : Tᵏˢ A ε₀ w) → sub a (sub d t) ≈ᵏ sub X (sub Y (sub c t))
sub3ᵏ d a c Y X t =
  ≈ᵏ-trans (sub-∘ᵏ d a (≾ₑ-trans (≾ₑ-trans c Y) X) t)
    (≈ᵏ-sym (≈ᵏ-trans (sub-≈ (sub-∘ᵏ c Y (≾ₑ-trans c Y) t))
                      (sub-∘ᵏ (≾ₑ-trans c Y) X _ t)))

-- `sub-tick` with its coherence witness pinned (never inferable from a goal).

sub-tickᵏ : ∀ {A ε ε' w} {δ : E} → (e : ε ≾ₑ ε')
          → (k : ∀ {w'} → w ⊑[ mapᵉ δ ] w' → Tᵏˢ A ε w')
          → (kn : ∀ {w' w''} (q : w ⊑[ mapᵉ δ ] w') (r : w' ⊑[ uᵣ ] w'')
                → k (⊑ρ∘ᵘ q r) ≈ᵏ transportᵏ r (k q))
          → sub (·ₑ-monoʳ-≾ₑ e) (tick-node δ k kn)
          ≈ᵏ tick-node δ (λ q → sub e (k q)) (λ q r → sub-≈ (kn q r))
sub-tickᵏ e k kn = sub-tick

-- Transport of a tree along an equality of grades.

ε-substᵏˢ : ∀ {A ε ε' w} → ε ≡ ε' → Tᵏˢ A ε w → Tᵏˢ A ε' w
ε-substᵏˢ {A} {w = w} e = subst (λ z → Tᵏˢ A z w) e

ε-substᵏˢ-cong : ∀ {A ε ε' w} (p : ε ≡ ε') {t t' : Tᵏˢ A ε w}
               → t ≈ᵏ t' → ε-substᵏˢ p t ≈ᵏ ε-substᵏˢ p t'
ε-substᵏˢ-cong refl e = e

transportᵏ-ε-substᵏˢ : ∀ {A ε ε' w w'} (p : w ⊑[ uᵣ ] w') (e : ε ≡ ε') (t : Tᵏˢ A ε w)
                     → transportᵏ p (ε-substᵏˢ e t) ≡ ε-substᵏˢ e (transportᵏ p t)
transportᵏ-ε-substᵏˢ p refl t = refl

-- The no-time step from a world to itself.

⊑-tick0 : ∀ {δ w} → δ ≃ₑ uₑ → w ⊑[ mapᵉ δ ] w
⊑-tick0 u = ⊑-mono (≃ᵣ⇒≿ᵣ (≃ᵣ-trans (map-≃ᵉ u) map-uᵉ)) ⊑-refl

-- A tick node is independent of its stored coherence witness.

tick-irrᵏ : ∀ {A ε w} {δ : E}
          → (k : ∀ {w'} → w ⊑[ mapᵉ δ ] w' → Tᵏˢ A ε w')
          → (kn kn' : ∀ {w' w''} (q : w ⊑[ mapᵉ δ ] w') (r : w' ⊑[ uᵣ ] w'')
                    → k (⊑ρ∘ᵘ q r) ≈ᵏ transportᵏ r (k q))
          → tick-node δ k kn ≈ᵏ tick-node δ k kn'
tick-irrᵏ k kn kn' = tick-≈ (λ q → ≈ᵏ-refl (k q))

-- `tick-·` when the inner node sits under a sub-effecting node — the shape the
-- structural recursions produce, with every witness explicit.

tick-·-out :
  ∀ {A ε ε₂ ε₃ w} {δ δ₁ δ₂ : E}
  → (p : δ₂ ·ₑ ε ≾ₑ ε₂)
  → (k' : ∀ {w'} → w ⊑[ mapᵉ δ₁ ] w' → ∀ {w''} → w' ⊑[ mapᵉ δ₂ ] w'' → Tᵏˢ A ε w'')
  → (kn₂ : ∀ {w'} (q₁ : w ⊑[ mapᵉ δ₁ ] w')
         → ∀ {w'' w'''} (q₂ : w' ⊑[ mapᵉ δ₂ ] w'') (r : w'' ⊑[ uᵣ ] w''')
         → k' q₁ (⊑ρ∘ᵘ q₂ r) ≈ᵏ transportᵏ r (k' q₁ q₂))
  → (kn₁ : ∀ {w' w''} (q₁ : w ⊑[ mapᵉ δ₁ ] w') (r : w' ⊑[ uᵣ ] w'')
         → sub p (tick-node δ₂ (k' (⊑ρ∘ᵘ q₁ r)) (kn₂ (⊑ρ∘ᵘ q₁ r)))
         ≈ᵏ transportᵏ r (sub p (tick-node δ₂ (k' q₁) (kn₂ q₁))))
  → (k : ∀ {w'} → w ⊑[ mapᵉ δ ] w' → Tᵏˢ A ε w')
  → (kn : ∀ {w' w''} (q : w ⊑[ mapᵉ δ ] w') (r : w' ⊑[ uᵣ ] w'')
        → k (⊑ρ∘ᵘ q r) ≈ᵏ transportᵏ r (k q))
  → (m : δ ≃ₑ δ₁ ·ₑ δ₂)
  → (∀ {w' w''} (q₁ : w ⊑[ mapᵉ δ₁ ] w') (q₂ : w' ⊑[ mapᵉ δ₂ ] w'')
     → k' q₁ q₂
     ≈ᵏ k (⊑-mono (≃ᵣ⇒≾ᵣ (≃ᵣ-trans (≃ᵣ-sym map-·ᵉ) (map-≃ᵉ (≃ₑ-sym m))))
            (⊑-trans q₁ q₂)))
  → (e : δ ·ₑ ε ≾ₑ δ₁ ·ₑ (δ₂ ·ₑ ε))
  → (P : δ ·ₑ ε ≾ₑ ε₃)
  → (P' : δ₁ ·ₑ ε₂ ≾ₑ ε₃)
  → sub P' (tick-node δ₁ (λ q₁ → sub p (tick-node δ₂ (k' q₁) (kn₂ q₁))) kn₁)
  ≈ᵏ sub P (tick-node δ k kn)
tick-·-out {w = w} {δ = δ} {δ₁} {δ₂} p k' kn₂ kn₁ k kn m hk e P P' =
  ≈ᵏ-trans (sub-congᵏ (≈ᵏ-sym (sub-tick {e = p} {kn = kn₁'} {kn' = kn₁})))
  (≈ᵏ-trans (sub-congᵏ (sub-congᵏ (tick-· m hk e)))
  (≈ᵏ-trans (sub-congᵏ (sub-∘ᵏ e (·ₑ-monoʳ-≾ₑ p) X _))
            (sub-∘ᵏ X P' P _)))
  where
    X = ≾ₑ-trans e (·ₑ-monoʳ-≾ₑ p)
    kn₁' : ∀ {w' w''} (q₁ : w ⊑[ mapᵉ δ₁ ] w') (r : w' ⊑[ uᵣ ] w'')
         → tick-node δ₂ (k' (⊑ρ∘ᵘ q₁ r)) (kn₂ (⊑ρ∘ᵘ q₁ r))
         ≈ᵏ transportᵏ r (tick-node δ₂ (k' q₁) (kn₂ q₁))
    kn₁' q₁ r = tick-≈ (λ q₂ →
                  ≈ᵏ-trans (hk _ _)
                    (≈ᵏ-trans (≡→≈ᵏ (cong k (⊑-irrelevant _ _))) (≈ᵏ-sym (hk _ _))))

transportᵏ-cong : ∀ {A ε w w'} (p : w ⊑[ uᵣ ] w') {t t' : Tᵏˢ A ε w}
                → t ≈ᵏ t' → transportᵏ p t ≈ᵏ transportᵏ p t'
transportᵏ-cong {A} p (leaf-≈ e)     = leaf-≈ (transport-cong A p e)
transportᵏ-cong p (tick-≈ ek)        = tick-≈ (λ q → ek (⊑ᵘ∘ρ p q))
transportᵏ-cong p (sub-≈ et)         = sub-≈ (transportᵏ-cong p et)
transportᵏ-cong p sub-u              = sub-uᵏ _ _
transportᵏ-cong p sub-∘              = sub-∘ᵏ _ _ _ _
transportᵏ-cong p sub-tick           = sub-tick
-- transport commutes with both tick collapses definitionally on the nodes;
-- what is left is the zero-tick's own naturality, resp. witness irrelevance
transportᵏ-cong p (tick-u {k = k} {kn = kn} {q₀ = q₀} u e) =
  ≈ᵏ-trans (tick-u {q₀ = ⊑-tick0 u} u e)
    (sub-congᵏ (≈ᵏ-trans (≡→≈ᵏ (cong k (⊑-irrelevant _ _))) (kn q₀ p)))
transportᵏ-cong p (tick-· {δ = δ} {k = k} {kn = kn} m hk e) =
  tick-· m (λ q₁ q₂ → ≈ᵏ-trans (hk (⊑ᵘ∘ρ p q₁) q₂)
                               (≡→≈ᵏ (cong k (⊑-irrelevant _ _)))) e
transportᵏ-cong p (≈ᵏ-sym et)        = ≈ᵏ-sym (transportᵏ-cong p et)
transportᵏ-cong p (≈ᵏ-trans et et')  =
  ≈ᵏ-trans (transportᵏ-cong p et) (transportᵏ-cong p et')

transportᵏ-refl : ∀ {A ε w} (t : Tᵏˢ A ε w) → transportᵏ ⊑-refl t ≈ᵏ t
transportᵏ-refl {A} (leaf x)       = leaf-≈ (transport-refl A x)
transportᵏ-refl (tick-node δ k kn) = tick-≈ (λ q → ≡→≈ᵏ (cong k (⊑-irrelevant _ _)))
transportᵏ-refl (sub e t)          = sub-≈ (transportᵏ-refl t)

transportᵏ-trans : ∀ {A ε w w' w''} (p : w ⊑[ uᵣ ] w') (q : w' ⊑[ uᵣ ] w'')
                   (t : Tᵏˢ A ε w)
                 → transportᵏ (⊑ᵘ-trans p q) t ≈ᵏ transportᵏ q (transportᵏ p t)
transportᵏ-trans {A} p q (leaf x)       = leaf-≈ (transport-trans A p q x)
transportᵏ-trans p q (tick-node δ k kn) =
  tick-≈ (λ q' → ≡→≈ᵏ (cong k (⊑-irrelevant _ _)))
transportᵏ-trans p q (sub e t)          = sub-≈ (transportᵏ-trans p q t)

Tᵏ : PSh → E → PSh
Tᵏ A ε = record
  { carrier         = Tᵏˢ A ε
  ; _≈_             = _≈ᵏ_
  ; ≈-refl          = λ {w} {t} → ≈ᵏ-refl t
  ; ≈-sym           = ≈ᵏ-sym
  ; ≈-trans         = ≈ᵏ-trans
  ; transport       = transportᵏ
  ; transport-cong  = transportᵏ-cong
  ; transport-refl  = transportᵏ-refl
  ; transport-trans = transportᵏ-trans
  }

ε-substᵏ : ∀ {A ε ε'} → ε ≡ ε' → Tᵏ A ε →ᵖ Tᵏ A ε'
ε-substᵏ p =
  pmap (ε-substᵏˢ p) (ε-substᵏˢ-cong p)
       (λ q t → ≡→≈ᵏ (sym (transportᵏ-ε-substᵏˢ q p t)))

ε-substᵏ-refl : ∀ {A ε} → ε-substᵏ {A} {ε} refl ≈ᵖ idᵖ
ε-substᵏ-refl t = ≈ᵏ-refl _

mutual

  {-# TERMINATING #-}

  Tᵏˢᶠ : ∀ {A B ε w} → A →ᵖ B → Tᵏˢ A ε w → Tᵏˢ B ε w
  Tᵏˢᶠ f (leaf x)          = leaf (app f x)
  Tᵏˢᶠ f (tick-node δ k kn) =
    tick-node δ (λ q → Tᵏˢᶠ f (k q))
      (λ q r → ≈ᵏ-trans (Tᵏˢᶠ-cong f (kn q r)) (Tᵏˢᶠ-nat f r (k q)))
  Tᵏˢᶠ f (sub p t)         = sub p (Tᵏˢᶠ f t)

  Tᵏˢᶠ-cong : ∀ {A B ε w} (f : A →ᵖ B) {t t' : Tᵏˢ A ε w}
            → t ≈ᵏ t' → Tᵏˢᶠ f t ≈ᵏ Tᵏˢᶠ f t'
  Tᵏˢᶠ-cong f (leaf-≈ e)   = leaf-≈ (app-cong f e)
  Tᵏˢᶠ-cong f (tick-≈ ek)  = tick-≈ (λ q → Tᵏˢᶠ-cong f (ek q))
  Tᵏˢᶠ-cong f (sub-≈ et)   = sub-≈ (Tᵏˢᶠ-cong f et)
  Tᵏˢᶠ-cong f sub-u        = sub-uᵏ _ _
  Tᵏˢᶠ-cong f sub-∘        = sub-∘ᵏ _ _ _ _
  Tᵏˢᶠ-cong f sub-tick     = sub-tick
  -- the functorial action pushes into the continuations and leaves the
  -- sub-effecting node, so both collapses are reapplied at the mapped tree
  Tᵏˢᶠ-cong f (tick-u {k = k} {q₀ = q₀} u e) = tick-u {q₀ = q₀} u e
  Tᵏˢᶠ-cong f (tick-· {δ = δ} {k = k} {kn = kn} m hk e) =
    tick-· m (λ q₁ q₂ → Tᵏˢᶠ-cong f (hk q₁ q₂)) e
  Tᵏˢᶠ-cong f (≈ᵏ-sym et)  = ≈ᵏ-sym (Tᵏˢᶠ-cong f et)
  Tᵏˢᶠ-cong f (≈ᵏ-trans et et') =
    ≈ᵏ-trans (Tᵏˢᶠ-cong f et) (Tᵏˢᶠ-cong f et')

  Tᵏˢᶠ-nat : ∀ {A B ε w w'} (f : A →ᵖ B) (p : w ⊑[ uᵣ ] w') (t : Tᵏˢ A ε w)
           → Tᵏˢᶠ f (transportᵏ p t) ≈ᵏ transportᵏ p (Tᵏˢᶠ f t)
  Tᵏˢᶠ-nat f p (leaf x)          = leaf-≈ (nat f p x)
  Tᵏˢᶠ-nat f p (tick-node δ k kn) = tick-≈ (λ q → ≈ᵏ-refl _)
  Tᵏˢᶠ-nat f p (sub e t)         = sub-≈ (Tᵏˢᶠ-nat f p t)

Tᵏᶠ : ∀ {A B ε} → A →ᵖ B → Tᵏ A ε →ᵖ Tᵏ B ε
Tᵏᶠ f = pmap (Tᵏˢᶠ f) (Tᵏˢᶠ-cong f) (λ p t → Tᵏˢᶠ-nat f p t)

Tᵏˢᶠ-id : ∀ {A ε w} (t : Tᵏˢ A ε w) → Tᵏˢᶠ idᵖ t ≈ᵏ t
Tᵏˢᶠ-id {A} (leaf x)          = leaf-≈ (≈-refl A)
Tᵏˢᶠ-id (tick-node δ k kn)    = tick-≈ (λ q → Tᵏˢᶠ-id (k q))
Tᵏˢᶠ-id (sub p t)             = sub-≈ (Tᵏˢᶠ-id t)

Tᵏ-idᵐ : ∀ {A ε} → Tᵏᶠ {A} {A} {ε} idᵖ ≈ᵖ idᵖ
Tᵏ-idᵐ t = Tᵏˢᶠ-id t

Tᵏˢᶠ-∘ : ∀ {A B C ε w} (g : B →ᵖ C) (f : A →ᵖ B) (t : Tᵏˢ A ε w)
       → Tᵏˢᶠ (g ∘ᵖ f) t ≈ᵏ Tᵏˢᶠ g (Tᵏˢᶠ f t)
Tᵏˢᶠ-∘ {C = C} g f (leaf x)       = leaf-≈ (≈-refl C)
Tᵏˢᶠ-∘ g f (tick-node δ k kn)     = tick-≈ (λ q → Tᵏˢᶠ-∘ g f (k q))
Tᵏˢᶠ-∘ g f (sub p t)              = sub-≈ (Tᵏˢᶠ-∘ g f t)

Tᵏ-∘ᵐ : ∀ {A B C ε} → (g : B →ᵖ C) → (f : A →ᵖ B)
      → Tᵏᶠ {A} {C} {ε} (g ∘ᵖ f) ≈ᵖ Tᵏᶠ g ∘ᵖ Tᵏᶠ f
Tᵏ-∘ᵐ g f t = Tᵏˢᶠ-∘ g f t

Tᵏˢᶠ-cong-fg : ∀ {A B ε w} {f g : A →ᵖ B} → f ≈ᵖ g → (t : Tᵏˢ A ε w)
             → Tᵏˢᶠ f t ≈ᵏ Tᵏˢᶠ g t
Tᵏˢᶠ-cong-fg e (leaf x)          = leaf-≈ (e x)
Tᵏˢᶠ-cong-fg e (tick-node δ k kn) = tick-≈ (λ q → Tᵏˢᶠ-cong-fg e (k q))
Tᵏˢᶠ-cong-fg e (sub p t)         = sub-≈ (Tᵏˢᶠ-cong-fg e t)

Tᵏ-congᶠ : ∀ {A B ε} {f g : A →ᵖ B} → f ≈ᵖ g → Tᵏᶠ {A} {B} {ε} f ≈ᵖ Tᵏᶠ g
Tᵏ-congᶠ e t = Tᵏˢᶠ-cong-fg e t

-- SUB-EFFECTING

T-≤ᵏ : ∀ {A ε ε'} → ε ≾ₑ ε' → Tᵏ A ε →ᵖ Tᵏ A ε'
T-≤ᵏ p = pmap (sub p) sub-≈ (λ q t → ≈ᵏ-refl _)

T-≤ᵏ-nat : ∀ {A B ε ε'} → (f : A →ᵖ B) → (p : ε ≾ₑ ε')
         → Tᵏᶠ f ∘ᵖ T-≤ᵏ {A} p ≈ᵖ T-≤ᵏ {B} p ∘ᵖ Tᵏᶠ f
T-≤ᵏ-nat f p t = ≈ᵏ-refl _

T-≤ᵏ-refl : ∀ {A ε} → (p : ε ≾ₑ ε) → T-≤ᵏ {A} p ≈ᵖ idᵖ
T-≤ᵏ-refl p t = sub-uᵏ p t

T-≤ᵏ-trans : ∀ {A ε₁ ε₂ ε₃} → (p : ε₁ ≾ₑ ε₂) → (q : ε₂ ≾ₑ ε₃) → (r : ε₁ ≾ₑ ε₃)
           → T-≤ᵏ {A} q ∘ᵖ T-≤ᵏ {A} p ≈ᵖ T-≤ᵏ {A} r
T-≤ᵏ-trans p q r t = sub-∘ᵏ p q r t

T-≤ᵏ-≡ : ∀ {A ε ε'} → (e : ε ≡ ε')
       → ε-substᵏ {A} e ≈ᵖ T-≤ᵏ (≾ₑ-reflexive e)
T-≤ᵏ-≡ refl t = ≈ᵏ-sym sub-u

ηᵏ : ∀ {A} → A →ᵖ Tᵏ A uₑ
ηᵏ = pmap leaf leaf-≈ (λ p x → ≈ᵏ-refl _)

ηᵏ-nat : ∀ {A B} → (f : A →ᵖ B) → ηᵏ ∘ᵖ f ≈ᵖ Tᵏᶠ f ∘ᵖ ηᵏ
ηᵏ-nat f x = ≈ᵏ-refl _

mutual

  {-# TERMINATING #-}

  μᵏˢ : ∀ {A ε ε' w} → Tᵏˢ (Tᵏ A ε') ε w → Tᵏˢ A (ε ·ₑ ε') w
  μᵏˢ {ε' = ε'} (leaf t) = sub (≃ₑ⇒≿ₑ (·ₑ-identityˡ ε')) t
  μᵏˢ {ε' = ε'} (tick-node {ε = ε₀} δ k kn) =
    sub (≃ₑ⇒≿ₑ (·ₑ-assoc δ ε₀ ε'))
      (tick-node δ (λ q → μᵏˢ (k q))
        (λ q r → ≈ᵏ-trans (μᵏˢ-cong (kn q r)) (μᵏˢ-nat r (k q))))
  μᵏˢ (sub p t) = sub (·ₑ-monoˡ-≾ₑ p) (μᵏˢ t)

  μᵏˢ-cong : ∀ {A ε ε' w} {t t' : Tᵏˢ (Tᵏ A ε') ε w} → t ≈ᵏ t' → μᵏˢ t ≈ᵏ μᵏˢ t'
  μᵏˢ-cong (leaf-≈ e)  = sub-congᵏ e
  μᵏˢ-cong (tick-≈ ek) = sub-congᵏ (tick-≈ (λ q → μᵏˢ-cong (ek q)))
  μᵏˢ-cong (sub-≈ et)  = sub-≈ (μᵏˢ-cong et)
  μᵏˢ-cong sub-u       = sub-uᵏ _ _
  μᵏˢ-cong sub-∘       = sub-∘ᵏ _ _ _ _
  μᵏˢ-cong {ε' = ε'} (sub-tick {ε = ε₁} {ε' = ε₁'} {δ = δ} {e = e}) =
    ≈ᵏ-trans
      (sub-swapᵏ _ _ (·ₑ-monoʳ-≾ₑ (·ₑ-monoˡ-≾ₑ e)) (≃ₑ⇒≿ₑ (·ₑ-assoc δ ε₁' ε')) _)
      (sub-congᵏ sub-tick)
  -- `μᵏˢ` regrades a tick node but leaves the node itself, so both collapses
  -- are reapplied to the folded continuations; the regradings agree by proof
  -- irrelevance of the order
  μᵏˢ-cong {ε' = ε'} (tick-u {ε = ε₀} {δ = δ} {k = k} {q₀ = q₀} u e) =
    ≈ᵏ-trans (sub-congᵏ (tick-u {q₀ = q₀} u (≃ₑ⇒≿ₑ (≃ₑ-trans (·ₑ-cong u ≃ₑ-refl) (·ₑ-identityˡ _))))) (sub-∘ᵏ _ _ _ _)
  μᵏˢ-cong {ε' = ε'} (tick-· {ε = ε₀} {δ = δ} {δ₁ = δ₁} {δ₂ = δ₂}
                             {k = k} {kn = kn} {k' = k'} m hk e) =
    ≈ᵏ-trans
      (tick-·-out (≃ₑ⇒≿ₑ (·ₑ-assoc δ₂ ε₀ ε')) (λ q₁ q₂ → μᵏˢ (k' q₁ q₂)) _ _
                  (λ q → μᵏˢ (k q)) _ m (λ q₁ q₂ → μᵏˢ-cong (hk q₁ q₂))
                  (≾ₑ-trans (·ₑ-monoˡ-≾ₑ (≃ₑ⇒≾ₑ m)) (≃ₑ⇒≾ₑ (·ₑ-assoc δ₁ δ₂ (ε₀ ·ₑ ε'))))
                  (≾ₑ-trans (≃ₑ⇒≿ₑ (·ₑ-assoc δ ε₀ ε')) (·ₑ-monoˡ-≾ₑ e)) _)
      (≈ᵏ-sym (sub-∘ᵏ _ _ _ _))
  μᵏˢ-cong (≈ᵏ-sym et)       = ≈ᵏ-sym (μᵏˢ-cong et)
  μᵏˢ-cong (≈ᵏ-trans et et') = ≈ᵏ-trans (μᵏˢ-cong et) (μᵏˢ-cong et')

  μᵏˢ-nat : ∀ {A ε ε' w w'} (p : w ⊑[ uᵣ ] w') (t : Tᵏˢ (Tᵏ A ε') ε w)
          → μᵏˢ (transportᵏ p t) ≈ᵏ transportᵏ p (μᵏˢ t)
  μᵏˢ-nat p (leaf t) = ≈ᵏ-refl _
  μᵏˢ-nat p (tick-node δ k kn) = sub-congᵏ (tick-≈ (λ q → ≈ᵏ-refl _))
  μᵏˢ-nat p (sub e t) = sub-≈ (μᵏˢ-nat p t)

μᵏ : ∀ {A ε ε'} → Tᵏ (Tᵏ A ε') ε →ᵖ Tᵏ A (ε ·ₑ ε')
μᵏ = pmap μᵏˢ μᵏˢ-cong (λ p t → μᵏˢ-nat p t)

μᵏˢ-nat-f : ∀ {A B ε ε' w} (f : A →ᵖ B) (t : Tᵏˢ (Tᵏ A ε') ε w)
          → μᵏˢ (Tᵏˢᶠ (Tᵏᶠ f) t) ≈ᵏ Tᵏˢᶠ f (μᵏˢ t)
μᵏˢ-nat-f f (leaf s) = ≈ᵏ-refl _
μᵏˢ-nat-f f (tick-node δ k kn) = sub-congᵏ (tick-≈ (λ q → μᵏˢ-nat-f f (k q)))
μᵏˢ-nat-f f (sub p t) = sub-≈ (μᵏˢ-nat-f f t)

μᵏ-nat : ∀ {A B ε ε'} → (f : A →ᵖ B)
       → μᵏ {ε = ε} {ε' = ε'} ∘ᵖ Tᵏᶠ (Tᵏᶠ f) ≈ᵖ Tᵏᶠ f ∘ᵖ μᵏ
μᵏ-nat f t = μᵏˢ-nat-f f t

-- SUB-EFFECTING COMMUTES WITH MULTIPLICATION (OUTER GRADE)

T-≤ᵏ-μᵏ : ∀ {A ε₁ ε₂ ε'} → (p : ε₁ ≾ₑ ε₂)
        → μᵏ {A} {ε₂} {ε'} ∘ᵖ T-≤ᵏ p ≈ᵖ T-≤ᵏ (·ₑ-monoˡ-≾ₑ p) ∘ᵖ μᵏ {A} {ε₁} {ε'}
T-≤ᵏ-μᵏ p t = ≈ᵏ-refl _

Tᵏ-μ∘η≡id : ∀ {A ε} → μᵏ {A} {uₑ} {ε} ∘ᵖ ηᵏ {Tᵏ A ε} ≈ᵖ T-≤ᵏ (≃ₑ⇒≿ₑ (·ₑ-identityˡ ε))
Tᵏ-μ∘η≡id t = ≈ᵏ-refl _

μᵏˢ-identity₂ : ∀ {A ε w} → (t : Tᵏˢ A ε w)
              → μᵏˢ (Tᵏˢᶠ ηᵏ t) ≈ᵏ sub (≃ₑ⇒≿ₑ (·ₑ-identityʳ ε)) t
μᵏˢ-identity₂ (leaf x) = sub-≈ (≈ᵏ-refl _)
μᵏˢ-identity₂ (tick-node {ε = ε₀} δ k kn) =
  ≈ᵏ-trans
    (sub-congᵏ (≈ᵏ-trans (tick-≈ (λ q → μᵏˢ-identity₂ (k q)))
                         (≈ᵏ-sym (sub-tickᵏ (≃ₑ⇒≿ₑ (·ₑ-identityʳ ε₀)) k kn))))
    (sub-∘ᵏ _ _ _ _)
μᵏˢ-identity₂ (sub p t) =
  ≈ᵏ-trans (sub-congᵏ (μᵏˢ-identity₂ t)) (sub-swapᵏ _ _ _ _ t)

Tᵏ-μ∘Tη≡id : ∀ {A ε} → μᵏ {A} {ε} {uₑ} ∘ᵖ Tᵏᶠ (ηᵏ {A}) ≈ᵖ T-≤ᵏ (≃ₑ⇒≿ₑ (·ₑ-identityʳ ε))
Tᵏ-μ∘Tη≡id t = μᵏˢ-identity₂ t

μᵏˢ-assoc : ∀ {A ε ε' ε'' w} → (t : Tᵏˢ (Tᵏ (Tᵏ A ε'') ε') ε w)
          → μᵏˢ {ε = ε} {ε' = ε' ·ₑ ε''} (Tᵏˢᶠ (μᵏ {A} {ε'} {ε''}) t)
          ≈ᵏ sub (≃ₑ⇒≾ₑ (·ₑ-assoc ε ε' ε'')) (μᵏˢ (μᵏˢ t))
μᵏˢ-assoc {ε' = ε'} {ε'' = ε''} (leaf s) = ≈ᵏ-sym (sub-∘ᵏ _ _ _ _)
μᵏˢ-assoc {ε' = ε'} {ε'' = ε''} (tick-node {ε = ε₀} δ k kn) =
  ≈ᵏ-trans
    (sub-congᵏ (≈ᵏ-trans (tick-≈ (λ q → μᵏˢ-assoc (k q)))
                         (≈ᵏ-sym (sub-tickᵏ (≃ₑ⇒≾ₑ (·ₑ-assoc ε₀ ε' ε'')) _ _))))
    (sub3ᵏ _ _ _ _ _ _)
μᵏˢ-assoc {ε' = ε'} {ε'' = ε''} (sub p t) =
  ≈ᵏ-trans (sub-congᵏ (μᵏˢ-assoc t)) (sub-swapᵏ _ _ _ _ _)

Tᵏ-μ∘μ≡μ∘Tμ : ∀ {A ε ε' ε''}
            → μᵏ {A} {ε} {ε' ·ₑ ε''} ∘ᵖ Tᵏᶠ (μᵏ {A} {ε'} {ε''})
            ≈ᵖ T-≤ᵏ (≃ₑ⇒≾ₑ (·ₑ-assoc ε ε' ε'')) ∘ᵖ μᵏ ∘ᵖ μᵏ
Tᵏ-μ∘μ≡μ∘Tμ t = μᵏˢ-assoc t

-- `δ` worth of time passes; the computation resumes in the future the box
-- reaches. The box sits at the node's own grade `mapᵉ δ`.

tickᵏ : ∀ {A ε} → (δ : E) → [ mapᵉ δ ]ᵒ (Tᵏ A ε) →ᵖ Tᵏ A (δ ·ₑ ε)
tickᵏ δ = pmap
  (λ x → tick-node δ (λ q → fun x q) (λ q r → fun-nat x q r))
  (λ e → tick-≈ (λ q → e q))
  (λ p x → tick-≈ (λ q → []-fun-irr x _ _))

tickᵏ-nat : ∀ {A B ε} → (δ : E) → (f : A →ᵖ B)
          → tickᵏ {ε = ε} δ ∘ᵖ [ mapᵉ δ ]ᶠ (Tᵏᶠ f) ≈ᵖ Tᵏᶠ f ∘ᵖ tickᵏ δ
tickᵏ-nat δ f x = tick-≈ (λ q → ≈ᵏ-refl _)

tickᵏ-algebraicity : ∀ {A ε ε'} → (δ : E)
                   → μᵏ {A} {δ ·ₑ ε} {ε'} ∘ᵖ tickᵏ {ε = ε} δ
                   ≈ᵖ T-≤ᵏ (≃ₑ⇒≿ₑ (·ₑ-assoc δ ε ε'))
                     ∘ᵖ tickᵏ δ ∘ᵖ [ mapᵉ δ ]ᶠ (μᵏ {A} {ε} {ε'})
tickᵏ-algebraicity δ x = sub-congᵏ (tick-≈ (λ q → ≈ᵏ-refl _))

-- SUB-EFFECTING PASSES UNDER A TICK

tickᵏ-≤ : ∀ {A ε ε'} → (δ : E) → (p : ε ≾ₑ ε')
        → tickᵏ {A} {ε'} δ ∘ᵖ [ mapᵉ δ ]ᶠ (T-≤ᵏ p)
        ≈ᵖ T-≤ᵏ (·ₑ-monoʳ-≾ₑ p) ∘ᵖ tickᵏ {A} {ε} δ
tickᵏ-≤ δ p x =
  ≈ᵏ-trans (tick-≈ (λ q → ≈ᵏ-refl _)) (≈ᵏ-sym (sub-tickᵏ p _ _))
