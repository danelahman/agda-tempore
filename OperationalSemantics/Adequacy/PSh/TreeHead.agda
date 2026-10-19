------------------------------------------------------------------------
-- Head shapes of effect trees, at an arbitrary tick total.            --
--                                                                     --
-- The durations are stepped, a duration being a number of unit        --
-- ticks. Delays are descended along a fixed path of unit ticks, so    --
-- `delay-plus` splits without the frame ever interpolating.           --
-- The tick total is therefore observable too (`HeadTimed`).           --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Product
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Syntax.Durations using (Stepped)
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
         (st : Stepped (GradeSystem.Dur (LanguageSpec.Grades Spec)))
       where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops
open World Wld
open Stepped st

open import DenotationalSemantics.Model.Example.PSh.Base Grades Wld
open import DenotationalSemantics.Model.Example.PSh.Modality.Future Grades Wld
open GroundTypes GTy

open import DenotationalSemantics.Model.Example.PSh.Monad.Core Spec Wld GTy

-- A returned value, or an operation. The observation is parameterised by a
-- *predicate* on this rather than fixed at the shape alone.

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

data Path : W → W → Set where
  pnil  : ∀ {w} → Path w w
  pcons : ∀ {w w' w''} → w ⊑[ mapᵉ (of-durᵉ 1ᴰ) ] w' → Path w' w'' → Path w w''

p-len : ∀ {w w'} → Path w w' → ℕ
p-len pnil        = 0
p-len (pcons q p) = suc (p-len p)


-- Steps at equal durations, and the step by no time.

⊑-cast : ∀ {τ τ' w w'} → τ ≡ τ' → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → w ⊑[ mapᵉ (of-durᵉ τ') ] w'
⊑-cast refl q = q

⊑-zero : ∀ {τ w} → τ ≡ 0ᴰ → w ⊑[ mapᵉ (of-durᵉ τ) ] w
⊑-zero z = ⊑-cast (sym z) ⊑-delay0

-- `Head P t p n` — descending `t` along `p` reaches, after `n` ticks, a head
-- satisfying `P`. `Headᵏ` is the same for a delay node's *continuation*.

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

    h-delay : ∀ {ε w we n} {τ : 𝔻}
            → {k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w'}
            → {kn : ∀ {w' w''} (q : w ⊑[ mapᵉ (of-durᵉ τ) ] w') (r : w' ⊑[ uᵣ ] w'')
                  → k (⊑ρ∘ᵘ q r) ≈ᵗ transportᵗ r (k q)}
            → {p : Path w we}
            → Headᵏ P τ k p n
            --------------------------------
            → Head P (delay-node τ k kn) p n

  data Headᵏ {A : PSh} (P : Pred A) : ∀ {ε w we} → (τ : 𝔻)
           → (∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w')
           → Path w we → ℕ → Set where

    -- a delay by nothing is descended at a zero-step, at no cost
    hk-zero : ∀ {ε w we n τ}
            → {k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w'}
            → {p : Path w we}
            → (z : τ ≡ 0ᴰ)
            → Head P (k (⊑-zero z)) p n
            ---------------------------
            → Headᵏ P τ k p n

    -- and a delay that delays consumes one step of the path per tick
    hk-suc  : ∀ {ε w w₁ we n τ} (τ' : 𝔻)
            → {k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w'}
            → (e : τ ≡ 1ᴰ +ᴰ τ')
            → (q : w ⊑[ mapᵉ (of-durᵉ 1ᴰ) ] w₁) → {p : Path w₁ we}
            → Headᵏ P τ' (λ {w'} q' → k (⊑-cast (sym e) (⊑-split q q'))) p n
            ----------------------------------------------------------------
            → Headᵏ P τ k (pcons q p) (suc n)

-- The witness a continuation is read at is irrelevant.

head-⊑ : ∀ {A} {P : Pred A} {ε ρ w w₁ we n} → (k : ∀ {w'} → w ⊑[ ρ ] w' → Tˢ A ε w')
       → (q q' : w ⊑[ ρ ] w₁) → {p : Path w₁ we}
       → Head P (k q) p n
       -------------------
       → Head P (k q') p n
head-⊑ k q q' {p} h = subst (λ z → Head _ (k z) p _) (⊑-irrelevant q q') h

-- Equal continuations are descended alike.

headᵏ-≡ : ∀ {A} {P : Pred A} {ε w we τ n}
        → {k k' : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w'}
        → {p : Path w we}
        → (∀ {w'} (q : w ⊑[ mapᵉ (of-durᵉ τ) ] w') → k q ≡ k' q)
        → Headᵏ P τ k p n
        ------------------
        → Headᵏ P τ k' p n
headᵏ-≡ ek (hk-zero z h)      = hk-zero z (subst (λ t → Head _ t _ _) (ek _) h)
headᵏ-≡ ek (hk-suc τ' e q h)  = hk-suc τ' e q (headᵏ-≡ (λ q' → ek _) h)

-- Transport along an equation of tick totals.

head-≡ : ∀ {A} {P : Pred A} {ε w we n n'} {t : Tˢ A ε w} {p : Path w we}
       → n ≡ n' → Head P t p n → Head P t p n'
head-≡ refl h = h

headᵏ-≡ⁿ : ∀ {A} {P : Pred A} {ε w we τ n n'}
         → {k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w'}
         → {p : Path w we}
         → n ≡ n' → Headᵏ P τ k p n → Headᵏ P τ k p n'
headᵏ-≡ⁿ refl h = h

-- A sub-effecting node is invisible.

head-sub⁻ : ∀ {A} {P : Pred A} {ε ε' w we n} {e : ε ≾ₑ ε'}
          → {t : Tˢ A ε w} → {p : Path w we}
          → Head P (sub e t) p n → Head P t p n
head-sub⁻ (h-sub h) = h

-- A sub-effecting node pushed into a delay's continuation is invisible, in
-- both directions: what `sub-delay` needs.

headᵏ-sub : ∀ {A} {P : Pred A} {ε ε' w we τ n} {e : ε ≾ₑ ε'}
          → {k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w'}
          → {p : Path w we}
          → Headᵏ P τ k p n
          → Headᵏ P τ (λ {w'} q → sub e (k q)) p n
headᵏ-sub (hk-zero z h)      = hk-zero z (h-sub h)
headᵏ-sub (hk-suc τ' e q h)  = hk-suc τ' e q (headᵏ-sub h)

headᵏ-sub⁻ : ∀ {A} {P : Pred A} {ε ε' w we τ n} {e : ε ≾ₑ ε'}
           → {k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w'}
           → {p : Path w we}
           → Headᵏ P τ (λ {w'} q → sub e (k q)) p n
           → Headᵏ P τ k p n
headᵏ-sub⁻ (hk-zero z (h-sub h)) = hk-zero z h
headᵏ-sub⁻ (hk-suc τ' e q h)     = hk-suc τ' e q (headᵏ-sub⁻ h)

-- One tree, one path: one tick total, and one head.

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
            → {k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w'}
            → {p : Path w we}
            → Headᵏ P τ k p n → Headᵏ Q τ k p n'
            -------------------------------------------------------
            → (n ≡ n') × Headᵏ (λ r → P r × Q r) τ k p n

  headᵏ-zip {k = k} (hk-zero z h) (hk-zero z' h')
    with head-zip h (subst (λ q → Head _ (k q) _ _) (⊑-irrelevant _ _) h')
  ... | en , hz = en , hk-zero z hz
  headᵏ-zip (hk-zero z h) (hk-suc τ' e q h') = ⊥-elim (1+≢0ᴰ (trans (sym e) z))
  headᵏ-zip (hk-suc τ' e q h) (hk-zero z h') = ⊥-elim (1+≢0ᴰ (trans (sym e) z))
  headᵏ-zip {k = k} (hk-suc τ₁ e₁ q h) (hk-suc τ₂ e₂ .q h')
    with 1+-cancel (trans (sym e₂) e₁)
  ... | refl
    with headᵏ-zip h (headᵏ-≡ (λ q' → cong k (⊑-irrelevant _ _)) h')
  ...   | en , hz = cong suc en , hk-suc τ₁ e₁ q hz

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
              → {k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w'}
              → {p : Path w we}
              → Headᵏ P τ k p n
              -----------------------------------------------------------
              → Σ[ w' ∈ W ] Σ[ ρ ∈ R ] (w ⊑[ ρ ] w') × Σ[ r ∈ Res A w' ] P r

  headᵏ-reach (hk-zero z h)     = head-reach h
  headᵏ-reach (hk-suc τ' e q h) with headᵏ-reach h
  ... | w' , ρ , acc , r , pr = w' , _ , ⊑-trans q acc , r , pr

-- Bisimilar trees have the same head *and the same tick total*. Mutual
-- with its converse, since `≈ᵗ-sym` is a constructor.

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
    head-≈ᵗ (delay-zero {k = k} {q₀ = q₀} e) (h-delay (hk-zero z h)) =
      h-sub (head-⊑ k (⊑-zero z) q₀ h)
    head-≈ᵗ (delay-zero e) (h-delay (hk-suc τ' e' q h)) = ⊥-elim (1+≢0ᴰ (sym e'))

    -- and consecutive delays are the one delay by their sum
    head-≈ᵗ (delay-plus {τ₁ = τ₁} {τ₂ = τ₂} hk e) (h-delay h) =
      h-sub (h-delay (plus-fwd τ₁ τ₂ hk h))

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
      h-delay (hk-zero refl (head-⊑ k q₀ (⊑-zero refl) (head-sub⁻ h)))

    head-≈ᵗ⁻ (delay-plus {τ₁ = τ₁} {τ₂ = τ₂} hk e) h with head-sub⁻ h
    ... | h-delay h' = h-delay (plus-bwd τ₁ τ₂ hk h')

    head-≈ᵗ⁻ (≈ᵗ-sym et)       h = head-≈ᵗ et h
    head-≈ᵗ⁻ (≈ᵗ-trans et et') h = head-≈ᵗ⁻ et (head-≈ᵗ⁻ et' h)

    -- Continuations related pointwise are descended alike.

    headᵏ-≈ : ∀ {ε w we τ n}
            → {k k' : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w'}
            → {p : Path w we}
            → (∀ {w'} (q : w ⊑[ mapᵉ (of-durᵉ τ) ] w') → k q ≈ᵗ k' q)
            → Headᵏ P τ k p n
            ------------------
            → Headᵏ P τ k' p n

    headᵏ-≈ ek (hk-zero z h)     = hk-zero z (head-≈ᵗ (ek (⊑-zero z)) h)
    headᵏ-≈ ek (hk-suc τ' e q h) =
      hk-suc τ' e q (headᵏ-≈ (λ q' → ek (⊑-cast (sym e) (⊑-split q q'))) h)

    headᵏ-≈⁻ : ∀ {ε w we τ n}
             → {k k' : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w'}
             → {p : Path w we}
             → (∀ {w'} (q : w ⊑[ mapᵉ (of-durᵉ τ) ] w') → k q ≈ᵗ k' q)
             → Headᵏ P τ k' p n
             -------------------
             → Headᵏ P τ k p n

    headᵏ-≈⁻ ek (hk-zero z h)     = hk-zero z (head-≈ᵗ⁻ (ek (⊑-zero z)) h)
    headᵏ-≈⁻ ek (hk-suc τ' e q h) =
      hk-suc τ' e q (headᵏ-≈⁻ (λ q' → ek (⊑-cast (sym e) (⊑-split q q'))) h)

    -- A continuation is descended alike at an equal duration.

    headᵏ-cast : ∀ {ε w we τ τ' n}
               → {k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w'}
               → {k' : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ') ] w' → Tˢ A ε w'}
               → {p : Path w we}
               → (c : τ ≡ τ')
               → (∀ {w'} (q : w ⊑[ mapᵉ (of-durᵉ τ) ] w') → k q ≈ᵗ k' (⊑-cast c q))
               → Headᵏ P τ k p n
               -------------------
               → Headᵏ P τ' k' p n

    headᵏ-cast {k' = k'} c ek (hk-zero z h) =
      hk-zero (trans (sym c) z)
        (head-≈ᵗ (≈ᵗ-trans (ek _) (≡→≈ᵗ (cong k' (⊑-irrelevant _ _)))) h)
    headᵏ-cast {k' = k'} c ek (hk-suc τ'' e q h) =
      hk-suc τ'' (trans (sym c) e) q
        (headᵏ-≈ (λ q' → ≈ᵗ-trans (ek _) (≡→≈ᵗ (cong k' (⊑-irrelevant _ _)))) h)

    -- Induction on the *outer* delay, not on the path.

    plus-fwd : ∀ {ε w we n} → (τ₁ τ₂ : 𝔻)
             → {k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ (τ₁ +ᴰ τ₂)) ] w' → Tˢ A ε w'}
             → {k' : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ₁) ] w'
                   → ∀ {w''} → w' ⊑[ mapᵉ (of-durᵉ τ₂) ] w'' → Tˢ A ε w''}
             → {kn₂ : ∀ {w'} (q₁ : w ⊑[ mapᵉ (of-durᵉ τ₁) ] w')
                    → ∀ {w'' w'''} (q₂ : w' ⊑[ mapᵉ (of-durᵉ τ₂) ] w'')
                        (r : w'' ⊑[ uᵣ ] w''')
                    → k' q₁ (⊑ρ∘ᵘ q₂ r) ≈ᵗ transportᵗ r (k' q₁ q₂)}
             → (∀ {w' w''} (q₁ : w ⊑[ mapᵉ (of-durᵉ τ₁) ] w')
                  (q₂ : w' ⊑[ mapᵉ (of-durᵉ τ₂) ] w'')
                → k' q₁ q₂ ≈ᵗ k (⊑-split q₁ q₂))
             → {p : Path w we}
             → Headᵏ P τ₁ (λ {w'} q₁ → delay-node τ₂ (k' q₁) (kn₂ q₁)) p n
             --------------------------------------------------------------
             → Headᵏ P (τ₁ +ᴰ τ₂) k p n

    plus-fwd τ₁ τ₂ {k = k} hk (hk-zero z (h-delay h)) =
      headᵏ-cast (sym (trans (cong (_+ᴰ τ₂) z) (+ᴰ-identityˡ τ₂)))
        (λ q₂ → ≈ᵗ-trans (hk (⊑-zero z) q₂) (≡→≈ᵗ (cong k (⊑-irrelevant _ _))))
        h

    plus-fwd τ₁ τ₂ {k = k} hk (hk-suc τ₁' e q h) =
      hk-suc (τ₁' +ᴰ τ₂) (trans (cong (_+ᴰ τ₂) e) (+ᴰ-assoc 1ᴰ τ₁' τ₂)) q
        (plus-fwd τ₁' τ₂
          (λ q₁ q₂ → ≈ᵗ-trans (hk _ q₂) (≡→≈ᵗ (cong k (⊑-irrelevant _ _))))
          h)

    plus-bwd : ∀ {ε w we n} → (τ₁ τ₂ : 𝔻)
             → {k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ (τ₁ +ᴰ τ₂)) ] w' → Tˢ A ε w'}
             → {k' : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ₁) ] w'
                   → ∀ {w''} → w' ⊑[ mapᵉ (of-durᵉ τ₂) ] w'' → Tˢ A ε w''}
             → {kn₂ : ∀ {w'} (q₁ : w ⊑[ mapᵉ (of-durᵉ τ₁) ] w')
                    → ∀ {w'' w'''} (q₂ : w' ⊑[ mapᵉ (of-durᵉ τ₂) ] w'')
                        (r : w'' ⊑[ uᵣ ] w''')
                    → k' q₁ (⊑ρ∘ᵘ q₂ r) ≈ᵗ transportᵗ r (k' q₁ q₂)}
             → (∀ {w' w''} (q₁ : w ⊑[ mapᵉ (of-durᵉ τ₁) ] w')
                  (q₂ : w' ⊑[ mapᵉ (of-durᵉ τ₂) ] w'')
                → k' q₁ q₂ ≈ᵗ k (⊑-split q₁ q₂))
             → {p : Path w we}
             → Headᵏ P (τ₁ +ᴰ τ₂) k p n
             --------------------------------------------------------------
             → Headᵏ P τ₁ (λ {w'} q₁ → delay-node τ₂ (k' q₁) (kn₂ q₁)) p n

    plus-bwd τ₁ τ₂ hk h with zero-or-step τ₁
    plus-bwd τ₁ τ₂ {k = k} {k' = k'} hk h | inj₁ z =
      hk-zero z
        (h-delay
          (headᵏ-cast (trans (cong (_+ᴰ τ₂) z) (+ᴰ-identityˡ τ₂))
            (λ q → ≈ᵗ-trans (≡→≈ᵗ (cong k (⊑-irrelevant _ _)))
                     (≈ᵗ-sym (hk (⊑-zero z) _)))
            h))
    plus-bwd τ₁ τ₂ hk (hk-zero z h) | inj₂ (τ₁' , e₁) =
      ⊥-elim (1+≢0ᴰ (trans (sym (trans (cong (_+ᴰ τ₂) e₁) (+ᴰ-assoc 1ᴰ τ₁' τ₂))) z))
    plus-bwd τ₁ τ₂ {k = k} hk (hk-suc σ e q h) | inj₂ (τ₁' , e₁)
      with 1+-cancel (trans (sym e) (trans (cong (_+ᴰ τ₂) e₁) (+ᴰ-assoc 1ᴰ τ₁' τ₂)))
    ... | refl =
      hk-suc τ₁' e₁ q
        (plus-bwd τ₁' τ₂
          (λ q₁ q₂ → ≈ᵗ-trans (hk _ q₂) (≡→≈ᵗ (cong k (⊑-irrelevant _ _))))
          h)

-- What a run's time transition denotes: leaves, reached after some
-- duration. `Delaysᵐ` unfolds to this.

data Delaysᵗ {Y : PSh} : ∀ {δ w} → Tˢ Y δ w → 𝔻 → Set where

  d-leaf  : ∀ {w} {y : carrier Y w}
          ---------------------------
          → Delaysᵗ (leaf y) 0ᴰ

  d-delay : ∀ {δ w n} → (τ : 𝔻)
          → {k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ Y δ w'}
          → {kn : ∀ {w' w''} (q : w ⊑[ mapᵉ (of-durᵉ τ) ] w') (r : w' ⊑[ uᵣ ] w'')
                → k (⊑ρ∘ᵘ q r) ≈ᵗ transportᵗ r (k q)}
          → (∀ {w'} (q : w ⊑[ mapᵉ (of-durᵉ τ) ] w') → Delaysᵗ (k q) n)
          -------------------------------------------------------------
          → Delaysᵗ (delay-node τ k kn) (τ +ᴰ n)

  d-sub   : ∀ {δ δ' w n} {e : δ ≾ₑ δ'} {t : Tˢ Y δ w}
          → Delaysᵗ t n
          --------------------
          → Delaysᵗ (sub e t) n

  d-≈     : ∀ {δ w n} {t t' : Tˢ Y δ w}
          → t ≈ᵗ t' → Delaysᵗ t n
          -----------------------
          → Delaysᵗ t' n

d-≡ : ∀ {Y δ w n n'} {t : Tˢ Y δ w} → n ≡ n' → Delaysᵗ t n → Delaysᵗ t n'
d-≡ refl d = d

-- Binding a chain after a chain is a chain, of the sum of their lengths.

delays-bind : ∀ {Y X : PSh} {δ ε' n m} {h : Y →ᵖ Tᵒ X ε'}
            → (∀ {w} (y : carrier Y w) → Delaysᵗ (app h y) m)
            → ∀ {w} {t : Tˢ Y δ w} → Delaysᵗ t n
            ------------------------------------
            → Delaysᵗ (μˢ (Tˢᶠ h t)) (n +ᴰ m)

delays-bind {m = m} pH (d-leaf {y = y}) = d-sub (d-≡ (sym (+ᴰ-identityˡ m)) (pH y))

delays-bind {m = m} pH (d-delay τ {k = k} f) =
  d-sub (d-≡ (sym (+ᴰ-assoc τ _ m)) (d-delay τ (λ q → delays-bind pH (f q))))

delays-bind pH (d-sub d) = d-sub (delays-bind pH d)

delays-bind {h = h} pH (d-≈ e d) =
  d-≈ (μˢ-congᵗ (Tˢᶠ-congᵗ h e)) (delays-bind pH d)

-- Descending a whole delay node: one step of the path per tick, and the
-- continuation observed at whatever remains. By induction on the path.

headᵏ-walk : ∀ {A} {P : Pred A} {ε w we n} → (τ : 𝔻)
           → {k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w'}
           → (p : Path w we) → (toℕ τ + n) ≤ p-len p
           → (∀ {w'} (q : w ⊑[ mapᵉ (of-durᵉ τ) ] w') (p' : Path w' we)
                → n ≤ p-len p' → Head P (k q) p' n)
           ------------------------------------------------------------
           → Headᵏ P τ k p (toℕ τ + n)

headᵏ-walk {n = n} τ p le φ with zero-or-step τ
... | inj₁ z =
  headᵏ-≡ⁿ (cong (_+ n) (sym toℕτ))
    (hk-zero z (φ (⊑-zero z) p (subst (_≤ p-len p) (cong (_+ n) toℕτ) le)))
  where
    toℕτ : toℕ τ ≡ 0
    toℕτ = trans (cong toℕ z) toℕ-0
headᵏ-walk {n = n} τ pnil le φ | inj₂ (τ' , e)
  with subst (λ m → m + n ≤ 0) (trans (cong toℕ e) (toℕ-1+ τ')) le
... | ()
headᵏ-walk {n = n} τ (pcons q p) le φ | inj₂ (τ' , e)
  with subst (λ m → m + n ≤ suc (p-len p)) (trans (cong toℕ e) (toℕ-1+ τ')) le
... | s≤s le' =
  headᵏ-≡ⁿ (cong (_+ n) (sym (trans (cong toℕ e) (toℕ-1+ τ'))))
    (hk-suc τ' e q
      (headᵏ-walk τ' p le' (λ q' p' le'' → φ (⊑-cast (sym e) (⊑-split q q')) p' le'')))

-- Running `h` after a chain of delays finds `h`'s own head, `toℕ n` ticks in.

bind-head : ∀ {Y X : PSh} {δ ε' n} {P : Pred X} {h : Y →ᵖ Tᵒ X ε'}
          → ≈-closed X P
          → (∀ {w we} (y : carrier Y w) (p : Path w we) → Head P (app h y) p 0)
          → ∀ {w we} {t : Tˢ Y δ w} → Delaysᵗ t n
          → (p : Path w we) → toℕ n ≤ p-len p
          --------------------------------------
          → Head P (μˢ (Tˢᶠ h t)) p (toℕ n)

bind-head Pcl pH (d-leaf {y = y}) p le =
  head-≡ (sym toℕ-0) (h-sub (pH y p))

bind-head Pcl pH (d-delay {n = n} τ f) p le =
  head-≡ (sym (toℕ-+ τ n))
    (h-sub
      (h-delay (headᵏ-walk τ p (subst (_≤ p-len p) (toℕ-+ τ n) le)
                 (λ q p' le' → bind-head Pcl pH (f q) p' le'))))

bind-head Pcl pH (d-sub d) p le = h-sub (bind-head Pcl pH d p le)

bind-head {h = h} Pcl pH (d-≈ e d) p le =
  head-≈ᵗ Pcl (μˢ-congᵗ (Tˢᶠ-congᵗ h e)) (bind-head Pcl pH d p le)

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

-- And the tick total is observable: the path is descended equally far on
-- both sides. This is what the zero-delay observation could not see.

ticks-eq : ∀ {A ε w we n₁ n₂} {P Q : Pred A} → ≈-closed A P
         → {t t' : Tˢ A ε w} {p : Path w we}
         → t ≈ᵗ t' → Head P t p n₁ → Head Q t' p n₂
         ------------------------------------------
         → n₁ ≡ n₂
ticks-eq Pcl et h h' = proj₁ (heads-meet Pcl et h h')
