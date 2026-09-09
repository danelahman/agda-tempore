------------------------------------------------------------------------
-- The presheaf model is head-faithful.                                --
--                                                                    --
-- Discharges `Adequacy.HeadFaithful`'s record — the model-side        --
-- assumption of the adequacy theorem — for the free graded tree monad --
-- on presheaves, and `HeadTimed` with it.                             --
--                                                                    --
-- Two frame assumptions are needed, both stated as records below.     --
--                                                                    --
--   * `TickFrame`: the worlds are inhabited, and time can always pass --
--     by one tick. Without the first nothing is observable at all     --
--     (every pair of morphisms is `≈ᵐ` over an empty frame); without  --
--     the second a delay node cannot be descended.                    --
--                                                                    --
--   * `ConstFrame`: whether two base constants agree does not depend  --
--     on when one looks. Needed only for `leaf-const`, and needed at  --
--     all because a head is read at a *later* world than the one the  --
--     statement is about — the delays moved there — and a presheaf    --
--     map is natural, not reflective.                                 --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (+-identityʳ; m≤m+n; m≤n+m)
open import Data.Product
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal

import DenotationalSemantics.Model.Example.PSh.Base                as B
import DenotationalSemantics.Model.Example.PSh.Modality.Future     as F
import DenotationalSemantics.Model.Example.PSh.Modality.Past       as P
import DenotationalSemantics.Model.Example.PSh.Modality.Adjunction as A
import DenotationalSemantics.Model.Example.PSh.Monad.Instance      as M

module OperationalSemantics.Adequacy.PSh.HeadFaithful
         (Spec : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades Spec)))
         (GTy : GroundTypes Spec (B.PShCat (LanguageSpec.Grades Spec) Wld)
                                 (F.PShFut (LanguageSpec.Grades Spec) Wld))
         (GE : GroundEternal Spec (B.PShCat (LanguageSpec.Grades Spec) Wld)
                                  (F.PShFut (LanguageSpec.Grades Spec) Wld)
                                  (P.PShPast (LanguageSpec.Grades Spec) Wld)
                                  (A.PShAdj (LanguageSpec.Grades Spec) Wld)
                                  GTy)
       where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops
open World Wld

open import Syntax.Types Spec

open import DenotationalSemantics.Model.Example.PSh.Base Grades Wld
open import DenotationalSemantics.Model.Example.PSh.Modality.Future Grades Wld
open GroundTypes GTy

open import DenotationalSemantics.Model.Example.PSh.Monad.Core Spec Wld GTy
open import DenotationalSemantics.Model.Example.PSh.Monad.Effects Spec Wld GTy
open import DenotationalSemantics.Model.Example.PSh.Modality.Adjunction Grades Wld
  using (η⊣)
open import DenotationalSemantics.Model.Example.PSh.Modality.Past Grades Wld
  using (⟨_⟩ᵒ; mk⟨⟩)

open import OperationalSemantics.Adequacy.PSh.TreeHead Spec Wld GTy

open import OperationalSemantics.Adequacy.HeadFaithful
             Spec (B.PShCat Grades Wld) (F.PShFut Grades Wld)
             (P.PShPast Grades Wld) (A.PShAdj Grades Wld) GTy
             (M.PShMonad Spec Wld GTy) GE

------------------------------------------------------------------------
-- THE FRAME ASSUMPTIONS
------------------------------------------------------------------------

record TickFrame : Set where
  field
    -- there is a world to observe at
    some-world : W

    -- and time can always pass by one tick
    ⊑-tick : (w : W) → Σ[ w' ∈ W ] w ⊑[ mapᵉ (of-natᵉ 1) ] w'

record ConstFrame : Set where
  field
    const-≈-reflect : ∀ {b : BaseType} {c₁ c₂ : BaseConstants b} {ρ : R} {w w' : W}
                    → w ⊑[ ρ ] w'
                    → _≈_ ⟦ b ⟧ᵇ {w'} (app ⟦ c₁ ⟧ᵇᶜ tt) (app ⟦ c₂ ⟧ᵇᶜ tt)
                    ----------------------------------------------------
                    → _≈_ ⟦ b ⟧ᵇ {w}  (app ⟦ c₁ ⟧ᵇᶜ tt) (app ⟦ c₂ ⟧ᵇᶜ tt)

-- `TickFrame` from a frame in which any grade can be spent from any world.
-- That is what the concrete tick frames have — see `PSh.TickFrames` — so the
-- assumption is not vacuous.

reachable⇒tick : W → (∀ (ρ : R) (w : W) → Σ[ w' ∈ W ] w ⊑[ ρ ] w') → TickFrame
reachable⇒tick w₀ f =
  record { some-world = w₀ ; ⊑-tick = f (mapᵉ (of-natᵉ 1)) }

------------------------------------------------------------------------
-- A RUN'S TRANSITION IS A DELAY CHAIN
--
-- `Delaysᵐ` describes a morphism as `ηᵀ` bound after `delayᵀ`s; at the
-- presheaf model each of its three shapes computes to the corresponding
-- shape of `Delaysᵗ`. Only the `τ`-step does anything: `η⊣` names the
-- present world, `[ ρ ]ᶠ ηᵀ` puts a leaf at every world the box reaches,
-- and `delayᵀ` wraps them in the node.
------------------------------------------------------------------------

-- one tick's worth of transition, spelled out at the concrete operations

tick-delays : ∀ {X : PSh} → (τ : ℕ) → ∀ {w} (x : carrier X w)
            → Delaysᵗ {⟨ of-natʳ τ ⟩ᵒ X}
                (app (delayᵀ τ ∘ᵖ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵖ η⊣) x) (τ + 0)
tick-delays {X} τ {w} x =
  d-delay τ {k = λ q → leaf (mk⟨⟩ (⊑-coe map-of-natᵉ q) x)} (λ q → d-leaf)

delaysᵐ→ᵗ : ∀ {X Y : PSh} {δ n} {d : X →ᵖ Tᵒ Y δ}
          → Delaysᵐ d n → ∀ {w} (x : carrier X w)
          --------------------------------------
          → Delaysᵗ (app d x) n

delaysᵐ→ᵗ no-delay              x = d-leaf
delaysᵐ→ᵗ (η-step {t = t} dm)   x =
  delays-bind {h = t} (delaysᵐ→ᵗ dm) (d-leaf {y = x})
delaysᵐ→ᵗ (τ-step {n = n} τ {t = t} dm) x =
  d-≡ (cong (_+ n) (+-identityʳ τ))
      (delays-bind {h = t} (delaysᵐ→ᵗ dm) (tick-delays τ x))
delaysᵐ→ᵗ (delays-≈ e dm)       x = d-≈ (e x) (delaysᵐ→ᵗ dm x)

------------------------------------------------------------------------
-- THE TWO HEADS, AS PREDICATES
------------------------------------------------------------------------

-- A leaf morphism has a `ret` head at every world, immediately.

leafᵐ-head : ∀ {X Y : PSh} → (a : Y →ᵖ X)
           → ∀ {w we} (y : carrier Y w) (p : Path w we)
           → Head isRet (app (leafᵐ a) y) p 0
leafᵐ-head a y p = h-leaf tt

-- and an operation morphism an `op` head, at its own operation.

nodeᵐ-head : ∀ {X Y : PSh} {ε : E} → (op : Op)
           → (v : Y →ᵖ ⟦ param op ⟧ᵍ)
           → (k : Y →ᵖ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ X ε))
           → ∀ {w we} (y : carrier Y w) (p : Path w we)
           → Head (isOp op) (app (nodeᵐ op v k) y) p 0
nodeᵐ-head op v k y p = h-op refl

------------------------------------------------------------------------
-- THE OBSERVATION OF A `delayedᵐ` SHAPE
--
-- `delayedᵐ h d r` is `h` bound after `d`, coerced: a `sub` node over the
-- bind, which `bind-head` descends.
------------------------------------------------------------------------

delayedᵐ-head : ∀ {X Y : PSh} {ε ε' δ : E} {n : ℕ} {P : Pred X}
              → ≈-closed X P
              → {h : Y →ᵖ Tᵒ X ε'}
              → (∀ {w we} (y : carrier Y w) (p : Path w we) → Head P (app h y) p 0)
              → {d : 𝟙ᵖ →ᵖ Tᵒ Y δ} → Delaysᵐ d n
              → (r : δ ·ₑ ε' ≾ₑ ε)
              → ∀ {w we} (p : Path w we) → n ≤ p-len p
              -------------------------------------------------
              → Head P (app (delayedᵐ h d r) tt) p n

delayedᵐ-head Pcl pH dm r p le =
  h-sub (bind-head Pcl pH (delaysᵐ→ᵗ dm tt) p le)

------------------------------------------------------------------------
-- THE INSTANCE
------------------------------------------------------------------------

module _ (TF : TickFrame) where

  open TickFrame TF

  -- A path of any prescribed length, out of any world.

  mk-path : (w : W) → (n : ℕ) → Σ[ w' ∈ W ] Σ[ p ∈ Path w w' ] (p-len p ≡ n)
  mk-path w zero    = w , pnil , refl
  mk-path w (suc n) with ⊑-tick w
  ... | w₁ , q with mk-path w₁ n
  ...   | w' , p , e = w' , pcons q p , cong suc e

  -- One path long enough for two observations at once.

  two-paths : (w : W) → (n₁ n₂ : ℕ)
            → Σ[ w' ∈ W ] Σ[ p ∈ Path w w' ] ((n₁ ≤ p-len p) × (n₂ ≤ p-len p))
  two-paths w n₁ n₂ with mk-path w (n₁ + n₂)
  ... | w' , p , e = w' , p
                   , subst (n₁ ≤_) (sym e) (m≤m+n n₁ n₂)
                   , subst (n₂ ≤_) (sym e) (m≤n+m n₂ n₁)

  -- A LEAF IS NEVER AN OPERATION

  rno : ∀ {X Y₁ Y₂ : PSh} {ε ε₂ δ₁ δ₂ : E} {n₁ n₂ : ℕ} {op : Op}
      → {a : Y₁ →ᵖ X}
      → {v : Y₂ →ᵖ ⟦ param op ⟧ᵍ}
      → {k : Y₂ →ᵖ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ X ε₂)}
      → {d₁ : 𝟙ᵖ →ᵖ Tᵒ Y₁ δ₁} → Delaysᵐ d₁ n₁
      → {d₂ : 𝟙ᵖ →ᵖ Tᵒ Y₂ δ₂} → Delaysᵐ d₂ n₂
      → (r₁ : δ₁ ·ₑ uₑ ≾ₑ ε)
      → (r₂ : δ₂ ·ₑ (op-grade op ·ₑ ε₂) ≾ₑ ε)
      --------------------------------------------------------------------
      → ¬ (delayedᵐ (leafᵐ a) d₁ r₁ ≈ᵖ delayedᵐ (nodeᵐ op v k) d₂ r₂)

  rno {X} {n₁ = n₁} {n₂ = n₂} {op = op} {a = a} {v = v} {k = k} nd₁ nd₂ r₁ r₂ eq
    with two-paths some-world n₁ n₂
  ... | _ , p , le₁ , le₂ =
    ret≉op (eq tt)
      (delayedᵐ-head (isRet-closed {X}) (leafᵐ-head a) nd₁ r₁ p le₁)
      (delayedᵐ-head (isOp-closed {X} {op}) (nodeᵐ-head op v k) nd₂ r₂ p le₂)

  -- DISTINCT OPERATIONS ARE DISTINCT NODES

  oinj : ∀ {X Y₁ Y₂ : PSh} {ε ε₁ ε₂ δ₁ δ₂ : E} {n₁ n₂ : ℕ} {op₁ op₂ : Op}
       → {v₁ : Y₁ →ᵖ ⟦ param op₁ ⟧ᵍ}
       → {k₁ : Y₁ →ᵖ [ mapᵉ (op-grade op₁) ]ᵒ (⟦ arity op₁ ⟧ᵍ ⇒ᵖ Tᵒ X ε₁)}
       → {v₂ : Y₂ →ᵖ ⟦ param op₂ ⟧ᵍ}
       → {k₂ : Y₂ →ᵖ [ mapᵉ (op-grade op₂) ]ᵒ (⟦ arity op₂ ⟧ᵍ ⇒ᵖ Tᵒ X ε₂)}
       → {d₁ : 𝟙ᵖ →ᵖ Tᵒ Y₁ δ₁} → Delaysᵐ d₁ n₁
       → {d₂ : 𝟙ᵖ →ᵖ Tᵒ Y₂ δ₂} → Delaysᵐ d₂ n₂
       → (r₁ : δ₁ ·ₑ (op-grade op₁ ·ₑ ε₁) ≾ₑ ε)
       → (r₂ : δ₂ ·ₑ (op-grade op₂ ·ₑ ε₂) ≾ₑ ε)
       → delayedᵐ (nodeᵐ op₁ v₁ k₁) d₁ r₁ ≈ᵖ delayedᵐ (nodeᵐ op₂ v₂ k₂) d₂ r₂
       ------------------------------------------------------------------
       → op₁ ≡ op₂

  oinj {X} {n₁ = n₁} {n₂ = n₂} {op₁ = op₁} {op₂ = op₂}
       {v₁ = v₁} {k₁ = k₁} {v₂ = v₂} {k₂ = k₂} nd₁ nd₂ r₁ r₂ eq
    with two-paths some-world n₁ n₂
  ... | _ , p , le₁ , le₂ =
    op-inj (eq tt)
      (delayedᵐ-head (isOp-closed {X} {op₁}) (nodeᵐ-head op₁ v₁ k₁) nd₁ r₁ p le₁)
      (delayedᵐ-head (isOp-closed {X} {op₂}) (nodeᵐ-head op₂ v₂ k₂) nd₂ r₂ p le₂)

  -- THE RETURNED ANSWER
  --
  -- The predicate says the leaf *is* that global element, which the
  -- observation carries to whatever world the delays reach. Stated for an
  -- arbitrary `g : 𝟙ᵖ →ᵖ X`, since both answer types return one: a base
  -- constant `⟦ c ⟧ᵇᶜ` and a boolean `trueᵖ`/`falseᵖ`.

  isG : ∀ {X : PSh} → (g : 𝟙ᵖ →ᵖ X) → Pred X
  isG {X} g (ret-res x) = _≈_ X x (app g tt)
  isG     g (op-res _)  = ⊥

  isG-closed : ∀ {X : PSh} → (g : 𝟙ᵖ →ᵖ X) → ≈-closed X (isG g)
  isG-closed {X} g e px = ≈-trans X (≈-sym X e) px

  isG-head : ∀ {X Y : PSh} → (g : 𝟙ᵖ →ᵖ X)
           → ∀ {w we} (y : carrier Y w) (p : Path w we)
           → Head (isG g) (app (leafᵐ (g ∘ᵖ terminalᵖ {Y})) y) p 0
  isG-head {X} g y p = h-leaf (≈-refl X)

  -- THE RETURNED BOOLEAN
  --
  -- `𝔹ᵖ` is the constant presheaf on `Bool`, so `app trueᵖ tt` is `true` at
  -- every world and its equivalence is `_≡_`. The comparison the observation
  -- lands on is therefore already world-independent, and no reflection
  -- assumption (the `ConstFrame` the base constants need) arises.

  -- Two leaves with the same delayed denotation carry the same answer, at
  -- *some* world the delays reach. Both answer types read their observation
  -- off this; what separates them is whether that world can be left again.

  globals-meet : ∀ {X Y₁ Y₂ : PSh} {ε δ₁ δ₂ : E} {n₁ n₂ : ℕ}
               → {g₁ g₂ : 𝟙ᵖ →ᵖ X}
               → {d₁ : 𝟙ᵖ →ᵖ Tᵒ Y₁ δ₁} → Delaysᵐ d₁ n₁
               → {d₂ : 𝟙ᵖ →ᵖ Tᵒ Y₂ δ₂} → Delaysᵐ d₂ n₂
               → (r₁ : δ₁ ·ₑ uₑ ≾ₑ ε)
               → (r₂ : δ₂ ·ₑ uₑ ≾ₑ ε)
               → delayedᵐ (leafᵐ (g₁ ∘ᵖ terminalᵖ {Y₁})) d₁ r₁
               ≈ᵖ delayedᵐ (leafᵐ (g₂ ∘ᵖ terminalᵖ {Y₂})) d₂ r₂
               → (w : W)
               ------------------------------------------------------------
               → Σ[ w' ∈ W ] Σ[ ρ ∈ R ]
                   (w ⊑[ ρ ] w') × _≈_ X {w'} (app g₁ tt) (app g₂ tt)

  globals-meet {X} {Y₁} {Y₂} {n₁ = n₁} {n₂ = n₂} {g₁ = g₁} {g₂ = g₂}
               nd₁ nd₂ r₁ r₂ eq w
    with two-paths w n₁ n₂
  ... | _ , p , le₁ , le₂
    with heads-meet (isG-closed g₁) (eq tt)
           (delayedᵐ-head (isG-closed g₁) (isG-head {Y = Y₁} g₁) nd₁ r₁ p le₁)
           (delayedᵐ-head (isG-closed g₂) (isG-head {Y = Y₂} g₂) nd₂ r₂ p le₂)
  ...   | _ , w' , ρ , acc , ret-res x , (e₁ , e₂) =
          w' , ρ , acc , ≈-trans X (≈-sym X e₁) e₂
  ...   | _ , _ , _ , acc , op-res _ , (() , _)

  -- At `𝔹ᵖ` the answer is world-independent — the carrier is `Bool` at every
  -- world and its equivalence is `_≡_` — so the world `globals-meet` lands at
  -- does not matter and no reflection assumption arises.

  lbool : ∀ {Y₁ Y₂ : PSh} {ε δ₁ δ₂ : E} {n₁ n₂ : ℕ}
        → {d₁ : 𝟙ᵖ →ᵖ Tᵒ Y₁ δ₁} → Delaysᵐ d₁ n₁
        → {d₂ : 𝟙ᵖ →ᵖ Tᵒ Y₂ δ₂} → Delaysᵐ d₂ n₂
        → (r₁ : δ₁ ·ₑ uₑ ≾ₑ ε)
        → (r₂ : δ₂ ·ₑ uₑ ≾ₑ ε)
        → delayedᵐ (leafᵐ (trueᵖ  ∘ᵖ terminalᵖ {Y₁})) d₁ r₁
        ≈ᵖ delayedᵐ (leafᵐ (falseᵖ ∘ᵖ terminalᵖ {Y₂})) d₂ r₂
        ------------------------------------------------------------
        → trueᵖ ≈ᵖ falseᵖ

  lbool {Y₁} {Y₂} nd₁ nd₂ r₁ r₂ eq {w} tt =
    proj₂ (proj₂ (proj₂ (globals-meet {𝔹ᵖ} {Y₁} {Y₂} {g₁ = trueᵖ} {g₂ = falseᵖ}
                                      nd₁ nd₂ r₁ r₂ eq w)))

  module _ (CF : ConstFrame) where

    open ConstFrame CF

    lconst : ∀ {Y₁ Y₂ : PSh} {b : BaseType} {ε δ₁ δ₂ : E} {n₁ n₂ : ℕ}
           → {c₁ c₂ : BaseConstants b}
           → {d₁ : 𝟙ᵖ →ᵖ Tᵒ Y₁ δ₁} → Delaysᵐ d₁ n₁
           → {d₂ : 𝟙ᵖ →ᵖ Tᵒ Y₂ δ₂} → Delaysᵐ d₂ n₂
           → (r₁ : δ₁ ·ₑ uₑ ≾ₑ ε)
           → (r₂ : δ₂ ·ₑ uₑ ≾ₑ ε)
           → delayedᵐ (leafᵐ (⟦ c₁ ⟧ᵇᶜ ∘ᵖ terminalᵖ {Y₁})) d₁ r₁
           ≈ᵖ delayedᵐ (leafᵐ (⟦ c₂ ⟧ᵇᶜ ∘ᵖ terminalᵖ {Y₂})) d₂ r₂
           ------------------------------------------------------------
           → ⟦ c₁ ⟧ᵇᶜ ≈ᵖ ⟦ c₂ ⟧ᵇᶜ

    lconst {Y₁} {Y₂} {b} {c₁ = c₁} {c₂ = c₂} nd₁ nd₂ r₁ r₂ eq {w} tt
      with globals-meet {⟦ b ⟧ᵇ} {Y₁} {Y₂} {g₁ = ⟦ c₁ ⟧ᵇᶜ} {g₂ = ⟦ c₂ ⟧ᵇᶜ}
                        nd₁ nd₂ r₁ r₂ eq w
    ... | _ , _ , acc , e = const-≈-reflect acc e

    -- The two `op`-shaped fields must have their implicits bound explicitly:
    -- `k` occurs only under `nodeᵐ`, which applies it, so a metavariable in
    -- that position is not solvable and η-expansion has to be done by hand.

    PShHeadFaithful : HeadFaithful
    PShHeadFaithful = record
      { ret≢op = λ {X} {Y₁} {Y₂} {ε} {ε₂} {δ₁} {δ₂} {n₁} {n₂} {op} {a} {v} {k} →
                   rno {X} {Y₁} {Y₂} {ε} {ε₂} {δ₁} {δ₂} {n₁} {n₂} {op} {a} {v} {k}
      ; op-inj = λ {X} {Y₁} {Y₂} {ε} {ε₁} {ε₂} {δ₁} {δ₂} {n₁} {n₂}
                   {op₁} {op₂} {v₁} {k₁} {v₂} {k₂} →
                   oinj {X} {Y₁} {Y₂} {ε} {ε₁} {ε₂} {δ₁} {δ₂} {n₁} {n₂}
                        {op₁} {op₂} {v₁} {k₁} {v₂} {k₂}
      ; leaf-const = lconst
      ; leaf-bool  = lbool
      }

  -- THE TIMED REFINEMENT
  --
  -- The tick total is observable too, since no case of the invariance changes
  -- it: the path is descended equally far on both sides.

  rte : ∀ {X Y₁ Y₂ : PSh} {ε δ₁ δ₂ : E} {n₁ n₂ : ℕ}
      → {a₁ : Y₁ →ᵖ X} → {a₂ : Y₂ →ᵖ X}
      → {d₁ : 𝟙ᵖ →ᵖ Tᵒ Y₁ δ₁} → Delaysᵐ d₁ n₁
      → {d₂ : 𝟙ᵖ →ᵖ Tᵒ Y₂ δ₂} → Delaysᵐ d₂ n₂
      → (r₁ : δ₁ ·ₑ uₑ ≾ₑ ε)
      → (r₂ : δ₂ ·ₑ uₑ ≾ₑ ε)
      → delayedᵐ (leafᵐ a₁) d₁ r₁ ≈ᵖ delayedᵐ (leafᵐ a₂) d₂ r₂
      ------------------------------------------------------
      → n₁ ≡ n₂

  rte {X} {n₁ = n₁} {n₂ = n₂} {a₁ = a₁} {a₂ = a₂} nd₁ nd₂ r₁ r₂ eq
    with two-paths some-world n₁ n₂
  ... | _ , p , le₁ , le₂ =
    ticks-eq (isRet-closed {X}) (eq tt)
      (delayedᵐ-head (isRet-closed {X}) (leafᵐ-head a₁) nd₁ r₁ p le₁)
      (delayedᵐ-head (isRet-closed {X}) (leafᵐ-head a₂) nd₂ r₂ p le₂)

  ote : ∀ {X Y₁ Y₂ : PSh} {ε ε₁ ε₂ δ₁ δ₂ : E} {n₁ n₂ : ℕ} {op : Op}
      → {v₁ : Y₁ →ᵖ ⟦ param op ⟧ᵍ}
      → {k₁ : Y₁ →ᵖ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ X ε₁)}
      → {v₂ : Y₂ →ᵖ ⟦ param op ⟧ᵍ}
      → {k₂ : Y₂ →ᵖ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ X ε₂)}
      → {d₁ : 𝟙ᵖ →ᵖ Tᵒ Y₁ δ₁} → Delaysᵐ d₁ n₁
      → {d₂ : 𝟙ᵖ →ᵖ Tᵒ Y₂ δ₂} → Delaysᵐ d₂ n₂
      → (r₁ : δ₁ ·ₑ (op-grade op ·ₑ ε₁) ≾ₑ ε)
      → (r₂ : δ₂ ·ₑ (op-grade op ·ₑ ε₂) ≾ₑ ε)
      → delayedᵐ (nodeᵐ op v₁ k₁) d₁ r₁ ≈ᵖ delayedᵐ (nodeᵐ op v₂ k₂) d₂ r₂
      -------------------------------------------------------------------
      → n₁ ≡ n₂

  ote {X} {n₁ = n₁} {n₂ = n₂} {op = op} {v₁ = v₁} {k₁ = k₁} {v₂ = v₂} {k₂ = k₂}
      nd₁ nd₂ r₁ r₂ eq
    with two-paths some-world n₁ n₂
  ... | _ , p , le₁ , le₂ =
    ticks-eq (isOp-closed {X} {op}) (eq tt)
      (delayedᵐ-head (isOp-closed {X} {op}) (nodeᵐ-head op v₁ k₁) nd₁ r₁ p le₁)
      (delayedᵐ-head (isOp-closed {X} {op}) (nodeᵐ-head op v₂ k₂) nd₂ r₂ p le₂)

  PShHeadTimed : HeadTimed
  PShHeadTimed = record
    { ret-ticks-eq = rte
    ; op-ticks-eq  = λ {X} {Y₁} {Y₂} {ε} {ε₁} {ε₂} {δ₁} {δ₂} {n₁} {n₂}
                       {op} {v₁} {k₁} {v₂} {k₂} →
                       ote {X} {Y₁} {Y₂} {ε} {ε₁} {ε₂} {δ₁} {δ₂} {n₁} {n₂}
                           {op} {v₁} {k₁} {v₂} {k₂}
    }
