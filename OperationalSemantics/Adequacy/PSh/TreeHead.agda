------------------------------------------------------------------------
-- Head shapes of effect trees, at an arbitrary tick total.            --
--                                                                    --
-- `_≈ᵗ_` is generated with `sub-u`/`sub-∘`/`sub-delay`/`sub-op`, the  --
-- two delay collapses, and explicit `≈ᵗ-sym`/`≈ᵗ-trans`, so no-       --
-- confusion is proved against an observation invariant under all of   --
-- them, by induction on the derivation.                               --
--                                                                    --
-- The observation descends delays along a **path of unit ticks**      --
-- supplied in advance. That is the whole design, and what it buys is  --
-- both directions of `delay-plus` without asking the frame to         --
-- interpolate: a `τ₁ + τ₂` node consumes `τ₁ + τ₂` unit steps and the --
-- nested pair consumes `τ₁` then `τ₂`, so splitting the rule is       --
-- splitting the *chain*, never inverting a composite witness. The     --
-- tick total is therefore observable too, which is `HeadTimed`.       --
--                                                                    --
-- The path is a parameter, not an existential: two observations of    --
-- one tree then descend to the same world, which is what makes the    --
-- shape (and the count) unique.                                       --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Data.Product
open import Data.Unit using (⊤; tt)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.GroundTypes
import DenotationalSemantics.Model.Example.PSh.Base as B
import DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module OperationalSemantics.Adequacy.PSh.TreeHead
         (Spec : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades Spec)))
         (GTy : GroundTypes Spec (B.PShCat (LanguageSpec.Grades Spec) Wld)
                                 (F.PShFut (LanguageSpec.Grades Spec) Wld))
       where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops
open World Wld

open import DenotationalSemantics.Model.Example.PSh.Base Grades Wld
open import DenotationalSemantics.Model.Example.PSh.Modality.Future Grades Wld
open GroundTypes GTy

open import DenotationalSemantics.Model.Example.PSh.Monad.Core Spec Wld GTy

------------------------------------------------------------------------
-- WHAT A HEAD IS
--
-- A returned value, or an operation. The observation is parameterised by a
-- *predicate* on this rather than fixed at the shape alone, so that one
-- development serves both the shape statements (`ret≢op`, `op-inj`) and the
-- one that reads the returned value (`leaf-const`). The predicate has to be
-- closed under the carrier's own equality, which is all `leaf-≈` gives.
------------------------------------------------------------------------

data Res (A : PSh) : W → Set where
  ret-res : ∀ {w} → carrier A w → Res A w
  op-res  : ∀ {w} → Op → Res A w

Pred : PSh → Set₁
Pred A = ∀ {w} → Res A w → Set

-- closure under the carrier's equality

≈-closed : (A : PSh) → Pred A → Set
≈-closed A P = ∀ {w} {x y : carrier A w} → _≈_ A x y → P (ret-res x) → P (ret-res y)

-- the three predicates the statements below are read at

isRet : ∀ {A} → Pred A
isRet (ret-res _) = ⊤
isRet (op-res _)  = ⊥

isOp : ∀ {A} → Op → Pred A
isOp op (ret-res _)  = ⊥
isOp op (op-res op') = op ≡ op'

isRet-closed : ∀ {A} → ≈-closed A isRet
isRet-closed e p = tt

isOp-closed : ∀ {A op} → ≈-closed A (isOp op)
isOp-closed e ()

------------------------------------------------------------------------
-- PATHS OF UNIT TICKS
------------------------------------------------------------------------

data Path : W → W → Set where
  pnil  : ∀ {w} → Path w w
  pcons : ∀ {w w' w''} → w ⊑[ mapᵉ (of-natᵉ 1) ] w' → Path w' w'' → Path w w''

p-len : ∀ {w w'} → Path w w' → ℕ
p-len pnil        = 0
p-len (pcons q p) = suc (p-len p)


------------------------------------------------------------------------
-- THE HEAD OBSERVATION
--
-- `Head P t p n` — descending `t` along `p` reaches, after `n` ticks, a head
-- satisfying `P`. `Headᵏ` is the same for a delay node's *continuation*, so
-- that descending never has to rebuild a node (and hence never has to
-- fabricate a node's naturality witness).
------------------------------------------------------------------------

mutual

  data Head {A : PSh} (P : Pred A) : ∀ {ε w we} → Tˢ A ε w → Path w we → ℕ → Set where

    h-leaf  : ∀ {w we} {x : carrier A w} {p : Path w we}
            → P (ret-res x)
            ---------------------
            → Head P (leaf x) p 0

    h-op    : ∀ {ε w we} {op : Op} {v : carrier ⟦ param op ⟧ᵍ w}
            → {k : ∀ {w'} → w ⊑[ mapᵉ (op-grade op) ] w'
                 → carrier ⟦ arity op ⟧ᵍ w' → Tˢ A ε w'}
            → {kc : ∀ {w'} (q : w ⊑[ mapᵉ (op-grade op) ] w')
                      {y y' : carrier ⟦ arity op ⟧ᵍ w'}
                  → _≈_ ⟦ arity op ⟧ᵍ y y' → k q y ≈ᵗ k q y'}
            → {kn : ∀ {w' w''} (q : w ⊑[ mapᵉ (op-grade op) ] w') (r : w' ⊑[ uᵣ ] w'')
                      (y : carrier ⟦ arity op ⟧ᵍ w')
                  → k (⊑ρ∘ᵘ q r) (transport ⟦ arity op ⟧ᵍ r y) ≈ᵗ transportᵗ r (k q y)}
            → {p : Path w we}
            → P (op-res {w = w} op)
            ------------------------------------
            → Head P (op-node op v k kc kn) p 0

    h-sub   : ∀ {ε ε' w we n} {e : ε ≾ₑ ε'} {t : Tˢ A ε w} {p : Path w we}
            → Head P t p n
            ----------------------
            → Head P (sub e t) p n

    h-delay : ∀ {ε w we n} {τ : ℕ}
            → {k : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ τ) ] w' → Tˢ A ε w'}
            → {kn : ∀ {w' w''} (q : w ⊑[ mapᵉ (of-natᵉ τ) ] w') (r : w' ⊑[ uᵣ ] w'')
                  → k (⊑ρ∘ᵘ q r) ≈ᵗ transportᵗ r (k q)}
            → {p : Path w we}
            → Headᵏ P τ k p n
            --------------------------------
            → Head P (delay-node τ k kn) p n

  data Headᵏ {A : PSh} (P : Pred A) : ∀ {ε w we} → (τ : ℕ)
           → (∀ {w'} → w ⊑[ mapᵉ (of-natᵉ τ) ] w' → Tˢ A ε w')
           → Path w we → ℕ → Set where

    -- a delay by nothing is descended at the canonical zero-step, at no cost
    hk-zero : ∀ {ε w we n}
            → {k : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ 0) ] w' → Tˢ A ε w'}
            → {p : Path w we}
            → Head P (k ⊑-delay0) p n
            -------------------------
            → Headᵏ P 0 k p n

    -- and a delay that delays consumes one step of the path per tick
    hk-suc  : ∀ {ε w w₁ we n} {τ : ℕ}
            → {k : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ (suc τ)) ] w' → Tˢ A ε w'}
            → (q : w ⊑[ mapᵉ (of-natᵉ 1) ] w₁) → {p : Path w₁ we}
            → Headᵏ P τ (λ {w'} q' → k (⊑-split q q')) p n
            ----------------------------------------------
            → Headᵏ P (suc τ) k (pcons q p) (suc n)

-- The witness a continuation is read at is irrelevant.

head-⊑ : ∀ {A} {P : Pred A} {ε ρ w w₁ we n} → (k : ∀ {w'} → w ⊑[ ρ ] w' → Tˢ A ε w')
       → (q q' : w ⊑[ ρ ] w₁) → {p : Path w₁ we}
       → Head P (k q) p n
       -------------------
       → Head P (k q') p n
head-⊑ k q q' {p} h = subst (λ z → Head _ (k z) p _) (⊑-irrelevant q q') h

-- Grade transports are invisible.

head-ε-subst : ∀ {A} {P : Pred A} {ε ε' w we n} → (e : ε ≡ ε')
             → {t : Tˢ A ε w} → {p : Path w we}
             → Head P (ε-substˢ e t) p n → Head P t p n
head-ε-subst refl h = h

head-ε-subst⁺ : ∀ {A} {P : Pred A} {ε ε' w we n} → (e : ε ≡ ε')
              → {t : Tˢ A ε w} → {p : Path w we}
              → Head P t p n → Head P (ε-substˢ e t) p n
head-ε-subst⁺ refl h = h

-- A sub-effecting node pushed into a delay's continuation is invisible, in
-- both directions: what `sub-delay` needs.

headᵏ-sub : ∀ {A} {P : Pred A} {ε ε' w we τ n} {e : ε ≾ₑ ε'}
          → {k : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ τ) ] w' → Tˢ A ε w'}
          → {p : Path w we}
          → Headᵏ P τ k p n
          → Headᵏ P τ (λ {w'} q → sub e (k q)) p n
headᵏ-sub (hk-zero h)  = hk-zero (h-sub h)
headᵏ-sub (hk-suc q h) = hk-suc q (headᵏ-sub h)

headᵏ-sub⁻ : ∀ {A} {P : Pred A} {ε ε' w we τ n} {e : ε ≾ₑ ε'}
           → {k : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ τ) ] w' → Tˢ A ε w'}
           → {p : Path w we}
           → Headᵏ P τ (λ {w'} q → sub e (k q)) p n
           → Headᵏ P τ k p n
headᵏ-sub⁻ (hk-zero (h-sub h)) = hk-zero h
headᵏ-sub⁻ (hk-suc q h)        = hk-suc q (headᵏ-sub⁻ h)

------------------------------------------------------------------------
-- UNIQUENESS
--
-- One tree, one path: one tick total, and one head — the two observations
-- are zipped into an observation of their conjunction, which is what lets
-- two *different* predicates be compared at the same head.
------------------------------------------------------------------------

mutual

  head-zip : ∀ {A ε w we n n'} {P Q : Pred A} {t : Tˢ A ε w} {p : Path w we}
           → Head P t p n → Head Q t p n'
           -------------------------------------------------------
           → (n ≡ n') × Head (λ r → P r × Q r) t p n

  head-zip (h-leaf px)  (h-leaf qx)  = refl , h-leaf (px , qx)
  head-zip (h-op px)    (h-op qx)    = refl , h-op (px , qx)
  head-zip (h-sub h)    (h-sub h')   with head-zip h h'
  ... | en , hz = en , h-sub hz
  head-zip (h-delay h)  (h-delay h') with headᵏ-zip h h'
  ... | en , hz = en , h-delay hz

  headᵏ-zip : ∀ {A ε w we τ n n'} {P Q : Pred A}
            → {k : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ τ) ] w' → Tˢ A ε w'}
            → {p : Path w we}
            → Headᵏ P τ k p n → Headᵏ Q τ k p n'
            -------------------------------------------------------
            → (n ≡ n') × Headᵏ (λ r → P r × Q r) τ k p n

  headᵏ-zip (hk-zero h)  (hk-zero h')   with head-zip h h'
  ... | en , hz = en , hk-zero hz
  headᵏ-zip (hk-suc q h) (hk-suc .q h') with headᵏ-zip h h'
  ... | en , hz = cong suc en , hk-suc q hz

-- Every observation ends at a head, at a world the start can reach.

mutual

  head-reach : ∀ {A ε w we n} {P : Pred A} {t : Tˢ A ε w} {p : Path w we}
             → Head P t p n
             -----------------------------------------------------------
             → Σ[ w' ∈ W ] Σ[ ρ ∈ R ] (w ⊑[ ρ ] w') × Σ[ r ∈ Res A w' ] P r

  head-reach (h-leaf {x = x} px) = _ , _ , ⊑-refl , ret-res x , px
  head-reach (h-op {op = op} px) = _ , _ , ⊑-refl , op-res op , px
  head-reach (h-sub h)           = head-reach h
  head-reach (h-delay h)         = headᵏ-reach h

  headᵏ-reach : ∀ {A ε w we τ n} {P : Pred A}
              → {k : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ τ) ] w' → Tˢ A ε w'}
              → {p : Path w we}
              → Headᵏ P τ k p n
              -----------------------------------------------------------
              → Σ[ w' ∈ W ] Σ[ ρ ∈ R ] (w ⊑[ ρ ] w') × Σ[ r ∈ Res A w' ] P r

  headᵏ-reach (hk-zero h)  = head-reach h
  headᵏ-reach (hk-suc q h) with headᵏ-reach h
  ... | w' , ρ , acc , r , pr = w' , _ , ⊑-trans q acc , r , pr

------------------------------------------------------------------------
-- INVARIANCE
--
-- Bisimilar trees have the same head *and the same tick total*. Mutual with
-- its converse, since `≈ᵗ-sym` is a constructor, and with the two
-- `delay-plus` transfers, which are inductions on the outer delay's `τ₁`.
------------------------------------------------------------------------

module _ {A : PSh} {P : Pred A} (Pcl : ≈-closed A P) where

  mutual

    {-# TERMINATING #-}

    head-≈ᵗ : ∀ {ε w we n} {t t' : Tˢ A ε w} {p : Path w we}
            → t ≈ᵗ t' → Head P t p n
            ------------------------
            → Head P t' p n

    head-≈ᵗ (leaf-≈ e)   (h-leaf px)         = h-leaf (Pcl e px)
    head-≈ᵗ (op-≈ _ _)   (h-op px)           = h-op px
    head-≈ᵗ (delay-≈ ek) (h-delay h)         = h-delay (headᵏ-≈ ek h)
    head-≈ᵗ (sub-≈ et)   (h-sub h)           = h-sub (head-≈ᵗ et h)
    head-≈ᵗ sub-u        (h-sub h)           = h
    head-≈ᵗ sub-∘        (h-sub (h-sub h))   = h-sub h
    head-≈ᵗ sub-delay    (h-sub (h-delay h)) = h-delay (headᵏ-sub h)
    head-≈ᵗ sub-op       (h-sub (h-op px))   = h-op px

    -- a zero delay *is* its own continuation, at the only zero-step there is
    head-≈ᵗ (delay-zero {k = k} {q₀ = q₀} e) (h-delay (hk-zero h)) =
      head-ε-subst⁺ e (head-⊑ k ⊑-delay0 q₀ h)

    -- and consecutive delays are the one delay by their sum
    head-≈ᵗ (delay-plus {τ₁ = τ₁} {τ₂ = τ₂} hk e) (h-delay h) =
      head-ε-subst⁺ e (h-delay (plus-fwd τ₁ τ₂ hk h))

    head-≈ᵗ (≈ᵗ-sym et)       h = head-≈ᵗ⁻ et h
    head-≈ᵗ (≈ᵗ-trans et et') h = head-≈ᵗ et' (head-≈ᵗ et h)

    head-≈ᵗ⁻ : ∀ {ε w we n} {t t' : Tˢ A ε w} {p : Path w we}
             → t ≈ᵗ t' → Head P t' p n
             -------------------------
             → Head P t p n

    head-≈ᵗ⁻ (leaf-≈ e)   (h-leaf px)         = h-leaf (Pcl (≈-sym A e) px)
    head-≈ᵗ⁻ (op-≈ _ _)   (h-op px)           = h-op px
    head-≈ᵗ⁻ (delay-≈ ek) (h-delay h)         = h-delay (headᵏ-≈⁻ ek h)
    head-≈ᵗ⁻ (sub-≈ et)   (h-sub h)           = h-sub (head-≈ᵗ⁻ et h)
    head-≈ᵗ⁻ sub-u        h                   = h-sub h
    head-≈ᵗ⁻ sub-∘        (h-sub h)           = h-sub (h-sub h)
    head-≈ᵗ⁻ sub-delay    (h-delay h)         = h-sub (h-delay (headᵏ-sub⁻ h))
    head-≈ᵗ⁻ sub-op       (h-op px)           = h-sub (h-op px)

    head-≈ᵗ⁻ (delay-zero {k = k} {q₀ = q₀} e) h =
      h-delay (hk-zero (head-⊑ k q₀ ⊑-delay0 (head-ε-subst e h)))

    head-≈ᵗ⁻ (delay-plus {τ₁ = τ₁} {τ₂ = τ₂} hk e) h with head-ε-subst e h
    ... | h-delay h' = h-delay (plus-bwd τ₁ τ₂ hk h')

    head-≈ᵗ⁻ (≈ᵗ-sym et)       h = head-≈ᵗ et h
    head-≈ᵗ⁻ (≈ᵗ-trans et et') h = head-≈ᵗ⁻ et (head-≈ᵗ⁻ et' h)

    -- Continuations related pointwise are descended alike.

    headᵏ-≈ : ∀ {ε w we τ n}
            → {k k' : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ τ) ] w' → Tˢ A ε w'}
            → {p : Path w we}
            → (∀ {w'} (q : w ⊑[ mapᵉ (of-natᵉ τ) ] w') → k q ≈ᵗ k' q)
            → Headᵏ P τ k p n
            ------------------
            → Headᵏ P τ k' p n

    headᵏ-≈ ek (hk-zero h)  = hk-zero (head-≈ᵗ (ek ⊑-delay0) h)
    headᵏ-≈ ek (hk-suc q h) = hk-suc q (headᵏ-≈ (λ q' → ek (⊑-split q q')) h)

    headᵏ-≈⁻ : ∀ {ε w we τ n}
             → {k k' : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ τ) ] w' → Tˢ A ε w'}
             → {p : Path w we}
             → (∀ {w'} (q : w ⊑[ mapᵉ (of-natᵉ τ) ] w') → k q ≈ᵗ k' q)
             → Headᵏ P τ k' p n
             -------------------
             → Headᵏ P τ k p n

    headᵏ-≈⁻ ek (hk-zero h)  = hk-zero (head-≈ᵗ⁻ (ek ⊑-delay0) h)
    headᵏ-≈⁻ ek (hk-suc q h) = hk-suc q (headᵏ-≈⁻ (λ q' → ek (⊑-split q q')) h)

    -- THE TWO `delay-plus` TRANSFERS
    --
    -- Induction on the *outer* delay, not on the path: at `zero` the two
    -- continuations meet at the canonical zero-step, and at `suc` one unit
    -- step is peeled off both sides at once. No accessibility witness is ever
    -- split — which is why the tick total survives and the frame is not asked
    -- to interpolate.

    plus-fwd : ∀ {ε w we n} → (τ₁ τ₂ : ℕ)
             → {k : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ (τ₁ + τ₂)) ] w' → Tˢ A ε w'}
             → {k' : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ τ₁) ] w'
                   → ∀ {w''} → w' ⊑[ mapᵉ (of-natᵉ τ₂) ] w'' → Tˢ A ε w''}
             → {kn₂ : ∀ {w'} (q₁ : w ⊑[ mapᵉ (of-natᵉ τ₁) ] w')
                    → ∀ {w'' w'''} (q₂ : w' ⊑[ mapᵉ (of-natᵉ τ₂) ] w'')
                        (r : w'' ⊑[ uᵣ ] w''')
                    → k' q₁ (⊑ρ∘ᵘ q₂ r) ≈ᵗ transportᵗ r (k' q₁ q₂)}
             → (∀ {w' w''} (q₁ : w ⊑[ mapᵉ (of-natᵉ τ₁) ] w')
                  (q₂ : w' ⊑[ mapᵉ (of-natᵉ τ₂) ] w'')
                → k' q₁ q₂ ≈ᵗ k (⊑-split q₁ q₂))
             → {p : Path w we}
             → Headᵏ P τ₁ (λ {w'} q₁ → delay-node τ₂ (k' q₁) (kn₂ q₁)) p n
             --------------------------------------------------------------
             → Headᵏ P (τ₁ + τ₂) k p n

    plus-fwd zero τ₂ {k = k} hk (hk-zero (h-delay h)) =
      headᵏ-≈ (λ q₂ → ≈ᵗ-trans (hk ⊑-delay0 q₂)
                (≡→≈ᵗ (cong k (⊑-irrelevant (⊑-split ⊑-delay0 q₂) q₂))))
              h

    plus-fwd (suc τ₁) τ₂ {k = k} hk (hk-suc q h) =
      hk-suc q
        (plus-fwd τ₁ τ₂
          (λ q₁ q₂ → ≈ᵗ-trans (hk (⊑-split q q₁) q₂)
            (≡→≈ᵗ (cong k (⊑-irrelevant (⊑-split (⊑-split q q₁) q₂)
                                        (⊑-split q (⊑-split q₁ q₂))))))
          h)

    plus-bwd : ∀ {ε w we n} → (τ₁ τ₂ : ℕ)
             → {k : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ (τ₁ + τ₂)) ] w' → Tˢ A ε w'}
             → {k' : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ τ₁) ] w'
                   → ∀ {w''} → w' ⊑[ mapᵉ (of-natᵉ τ₂) ] w'' → Tˢ A ε w''}
             → {kn₂ : ∀ {w'} (q₁ : w ⊑[ mapᵉ (of-natᵉ τ₁) ] w')
                    → ∀ {w'' w'''} (q₂ : w' ⊑[ mapᵉ (of-natᵉ τ₂) ] w'')
                        (r : w'' ⊑[ uᵣ ] w''')
                    → k' q₁ (⊑ρ∘ᵘ q₂ r) ≈ᵗ transportᵗ r (k' q₁ q₂)}
             → (∀ {w' w''} (q₁ : w ⊑[ mapᵉ (of-natᵉ τ₁) ] w')
                  (q₂ : w' ⊑[ mapᵉ (of-natᵉ τ₂) ] w'')
                → k' q₁ q₂ ≈ᵗ k (⊑-split q₁ q₂))
             → {p : Path w we}
             → Headᵏ P (τ₁ + τ₂) k p n
             --------------------------------------------------------------
             → Headᵏ P τ₁ (λ {w'} q₁ → delay-node τ₂ (k' q₁) (kn₂ q₁)) p n

    plus-bwd zero τ₂ {k = k} hk h =
      hk-zero
        (h-delay
          (headᵏ-≈⁻ (λ q₂ → ≈ᵗ-trans (hk ⊑-delay0 q₂)
                      (≡→≈ᵗ (cong k (⊑-irrelevant (⊑-split ⊑-delay0 q₂) q₂))))
                    h))

    plus-bwd (suc τ₁) τ₂ {k = k} hk (hk-suc q h) =
      hk-suc q
        (plus-bwd τ₁ τ₂
          (λ q₁ q₂ → ≈ᵗ-trans (hk (⊑-split q q₁) q₂)
            (≡→≈ᵗ (cong k (⊑-irrelevant (⊑-split (⊑-split q q₁) q₂)
                                        (⊑-split q (⊑-split q₁ q₂))))))
          h)

------------------------------------------------------------------------
-- DELAY CHAINS
--
-- What a run's time transition denotes: leaves, reached after some number of
-- ticks. The morphism-level class `stepsᵀ` builds (`Delaysᵐ`) unfolds to
-- this, and this is the form the bind below consumes.
------------------------------------------------------------------------

data Delaysᵗ {Y : PSh} : ∀ {δ w} → Tˢ Y δ w → ℕ → Set where

  d-leaf  : ∀ {w} {y : carrier Y w}
          --------------------------
          → Delaysᵗ (leaf y) 0

  d-delay : ∀ {δ w n} → (τ : ℕ)
          → {k : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ τ) ] w' → Tˢ Y δ w'}
          → {kn : ∀ {w' w''} (q : w ⊑[ mapᵉ (of-natᵉ τ) ] w') (r : w' ⊑[ uᵣ ] w'')
                → k (⊑ρ∘ᵘ q r) ≈ᵗ transportᵗ r (k q)}
          → (∀ {w'} (q : w ⊑[ mapᵉ (of-natᵉ τ) ] w') → Delaysᵗ (k q) n)
          -------------------------------------------------------------
          → Delaysᵗ (delay-node τ k kn) (τ + n)

  d-sub   : ∀ {δ δ' w n} {e : δ ≾ₑ δ'} {t : Tˢ Y δ w}
          → Delaysᵗ t n
          --------------------
          → Delaysᵗ (sub e t) n

  d-≈     : ∀ {δ w n} {t t' : Tˢ Y δ w}
          → t ≈ᵗ t' → Delaysᵗ t n
          -----------------------
          → Delaysᵗ t' n

d-ε : ∀ {Y δ δ' w n} → (e : δ ≡ δ') → {t : Tˢ Y δ w}
    → Delaysᵗ t n → Delaysᵗ (ε-substˢ e t) n
d-ε refl d = d

d-≡ : ∀ {Y δ w n n'} {t : Tˢ Y δ w} → n ≡ n' → Delaysᵗ t n → Delaysᵗ t n'
d-≡ refl d = d

-- Binding a chain after a chain is a chain, of the sum of their lengths.

delays-bind : ∀ {Y X : PSh} {δ ε' n m} {h : Y →ᵖ Tᵒ X ε'}
            → (∀ {w} (y : carrier Y w) → Delaysᵗ (app h y) m)
            → ∀ {w} {t : Tˢ Y δ w} → Delaysᵗ t n
            ------------------------------------
            → Delaysᵗ (μˢ (Tˢᶠ h t)) (n + m)

delays-bind pH (d-leaf {y = y}) = d-ε _ (pH y)

delays-bind {m = m} pH (d-delay τ {k = k} f) =
  d-ε _ (d-≡ (sym (+-assoc τ _ m)) (d-delay τ (λ q → delays-bind pH (f q))))

delays-bind pH (d-sub d) = d-sub (delays-bind pH d)

delays-bind {h = h} pH (d-≈ e d) =
  d-≈ (μˢ-congᵗ (Tˢᶠ-congᵗ h e)) (delays-bind pH d)

-- Descending a whole delay node: one step of the path per tick, and the
-- continuation observed at whatever remains.

headᵏ-walk : ∀ {A} {P : Pred A} {ε w we n} → (τ : ℕ)
           → {k : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ τ) ] w' → Tˢ A ε w'}
           → (p : Path w we) → (τ + n) ≤ p-len p
           → (∀ {w'} (q : w ⊑[ mapᵉ (of-natᵉ τ) ] w') (p' : Path w' we)
                → n ≤ p-len p' → Head P (k q) p' n)
           ------------------------------------------------------------
           → Headᵏ P τ k p (τ + n)

headᵏ-walk zero    p            le       φ = hk-zero (φ ⊑-delay0 p le)
headᵏ-walk (suc τ) pnil         ()       φ
headᵏ-walk (suc τ) (pcons q p) (s≤s le) φ =
  hk-suc q (headᵏ-walk τ p le (λ q' p' le' → φ (⊑-split q q') p' le'))

------------------------------------------------------------------------
-- BINDING PAST A DELAY CHAIN
--
-- Running `h` after a chain of delays finds `h`'s own head, `n` ticks in.
-- `μˢ` and `Tˢᶠ` are structural — they regrade a node and push into its
-- continuations — so each case is the corresponding case of the chain.
------------------------------------------------------------------------

bind-head : ∀ {Y X : PSh} {δ ε' n} {P : Pred X} {h : Y →ᵖ Tᵒ X ε'}
          → ≈-closed X P
          → (∀ {w we} (y : carrier Y w) (p : Path w we) → Head P (app h y) p 0)
          → ∀ {w we} {t : Tˢ Y δ w} → Delaysᵗ t n
          → (p : Path w we) → n ≤ p-len p
          --------------------------------------
          → Head P (μˢ (Tˢᶠ h t)) p n

bind-head Pcl pH (d-leaf {y = y}) p le = head-ε-subst⁺ _ (pH y p)

bind-head Pcl pH (d-delay τ f) p le =
  head-ε-subst⁺ _
    (h-delay (headᵏ-walk τ p le (λ q p' le' → bind-head Pcl pH (f q) p' le')))

bind-head Pcl pH (d-sub d) p le = h-sub (bind-head Pcl pH d p le)

bind-head {h = h} Pcl pH (d-≈ e d) p le =
  head-≈ᵗ Pcl (μˢ-congᵗ (Tˢᶠ-congᵗ h e)) (bind-head Pcl pH d p le)

------------------------------------------------------------------------
-- NO-CONFUSION, AT AN ARBITRARY TICK TOTAL
------------------------------------------------------------------------

-- Two observations of bisimilar trees along one path meet: at one world,
-- reached in one number of ticks, at one head.

heads-meet : ∀ {A ε w we n₁ n₂} {P Q : Pred A} → ≈-closed A P
           → {t t' : Tˢ A ε w} {p : Path w we}
           → t ≈ᵗ t' → Head P t p n₁ → Head Q t' p n₂
           -----------------------------------------------------------
           → (n₁ ≡ n₂)
           × (Σ[ w' ∈ W ] Σ[ ρ ∈ R ] (w ⊑[ ρ ] w') × Σ[ r ∈ Res A w' ] (P r × Q r))

heads-meet Pcl et h h' with head-zip (head-≈ᵗ Pcl et h) h'
... | en , hz = en , head-reach hz

-- A returned value is never an operation.

ret≉op : ∀ {A : PSh} {ε w we n₁ n₂} {op : Op} {t t' : Tˢ A ε w} {p : Path w we}
       → t ≈ᵗ t'
       → Head isRet t p n₁ → Head (isOp op) t' p n₂
       --------------------------------------------
       → ⊥
ret≉op {A} et h h' with heads-meet (isRet-closed {A}) et h h'
... | _ , _ , _ , _ , ret-res _ , (_  , ())
... | _ , _ , _ , _ , op-res _ , (() , _)

-- Distinct operations are distinct nodes.

op-inj : ∀ {A : PSh} {ε w we n₁ n₂} {op op' : Op} {t t' : Tˢ A ε w} {p : Path w we}
       → t ≈ᵗ t'
       → Head (isOp op) t p n₁ → Head (isOp op') t' p n₂
       -------------------------------------------------
       → op ≡ op'
op-inj {A} {op = op} et h h' with heads-meet (isOp-closed {A} {op}) et h h'
... | _ , _ , _ , _ , ret-res _ , (() , _)
... | _ , _ , _ , _ , op-res _ , (e₁ , e₂) = trans e₁ (sym e₂)

-- And the tick total is observable: the path is descended equally far on both
-- sides. This is what the zero-delay observation could not see, and it comes
-- for free here — no case of the invariance above changes `n`.

ticks-eq : ∀ {A ε w we n₁ n₂} {P Q : Pred A} → ≈-closed A P
         → {t t' : Tˢ A ε w} {p : Path w we}
         → t ≈ᵗ t' → Head P t p n₁ → Head Q t' p n₂
         ------------------------------------------
         → n₁ ≡ n₂
ticks-eq Pcl et h h' = proj₁ (heads-meet Pcl et h h')
