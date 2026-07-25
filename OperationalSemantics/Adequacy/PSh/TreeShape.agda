------------------------------------------------------------------------
-- Head shapes of effect trees, at zero delay.                          --
--                                                                    --
-- The presheaf model's tree setoid `_≈ᵗ_` is not structural            --
-- bisimulation: it is generated with `sub-u`/`sub-∘`/`sub-delay`/       --
-- `sub-op`, the two delay collapses, and explicit `≈ᵗ-sym`/`≈ᵗ-trans`.  --
-- So no-confusion has to be proved against an observation that survives --
-- every one of those rules, by induction on the derivation.             --
--                                                                    --
-- `Head0 t s` says: descending `t`'s delay nodes through *no* time at    --
-- all, its head is a leaf, resp. an operation node for a given `op`.     --
-- Two things make this work where a tick-counting observation would      --
-- struggle:                                                            --
--                                                                    --
--   * a zero delay has a *canonical* witness `⊑-delay0` (the frame       --
--     needs no future world for it), so the observation quantifies over  --
--     no witness at all and everything is witness-irrelevant;           --
--                                                                    --
--   * splitting a `τ₁ + τ₂` step — `delay-plus` read backwards — would   --
--     need the frame to interpolate, which it does not in general; at    --
--     `τ₁ + τ₂ ≡ 0` the split is `⊑-delay0` twice.                      --
--                                                                    --
-- This is the base case of `HeadFaithful` (`ret≢op` and `op-inj` at zero  --
-- delay). The general case is the same argument at a tick-indexed        --
-- observation, and needs the interpolation axiom.                        --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Nat using (ℕ; zero; suc; _+_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.GroundTypes
import DenotationalSemantics.Model.Example.PSh.Base as B
import DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module OperationalSemantics.Adequacy.PSh.TreeShape
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

-- THE TWO HEAD SHAPES

data Shape : Set where
  ret-shape : Shape
  op-shape  : Op → Shape

ret≢op-shape : ∀ {op} → ret-shape ≡ op-shape op → ⊥
ret≢op-shape ()

op-shape-inj : ∀ {op op'} → op-shape op ≡ op-shape op' → op ≡ op'
op-shape-inj refl = refl

-- THE ZERO-DELAY HEAD OBSERVATION
--
-- `sub` nodes are transparent (reduction discards a `coerce`); a delay may be
-- descended only when it delays by nothing, and then along the canonical
-- zero-step.

data Head0 {A : PSh} : ∀ {ε w} → Tˢ A ε w → Shape → Set where

  h-leaf  : ∀ {w} {x : carrier A w}
          ---------------------------
          → Head0 (leaf x) ret-shape

  h-op    : ∀ {ε w} {op : Op} {v : carrier ⟦ param op ⟧ᵍ w}
          → {k : ∀ {w'} → w ⊑[ mapᵉ (op-grade op) ] w'
               → carrier ⟦ arity op ⟧ᵍ w' → Tˢ A ε w'}
          → {kc : ∀ {w'} (q : w ⊑[ mapᵉ (op-grade op) ] w')
                    {y y' : carrier ⟦ arity op ⟧ᵍ w'}
                → _≈_ ⟦ arity op ⟧ᵍ y y' → k q y ≈ᵗ k q y'}
          → {kn : ∀ {w' w''} (q : w ⊑[ mapᵉ (op-grade op) ] w') (r : w' ⊑[ uᵣ ] w'')
                    (y : carrier ⟦ arity op ⟧ᵍ w')
                → k (⊑ρ∘ᵘ q r) (transport ⟦ arity op ⟧ᵍ r y) ≈ᵗ transportᵗ r (k q y)}
          --------------------------------------------
          → Head0 (op-node op v k kc kn) (op-shape op)

  h-delay : ∀ {ε w s}
          → {k : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ 0) ] w' → Tˢ A ε w'}
          → {kn : ∀ {w' w''} (q : w ⊑[ mapᵉ (of-natᵉ 0) ] w') (r : w' ⊑[ uᵣ ] w'')
                → k (⊑ρ∘ᵘ q r) ≈ᵗ transportᵗ r (k q)}
          → Head0 (k ⊑-delay0) s
          ------------------------------
          → Head0 (delay-node 0 k kn) s

  h-sub   : ∀ {ε ε' w s} {e : ε ≾ₑ ε'} {t : Tˢ A ε w}
          → Head0 t s
          -------------------
          → Head0 (sub e t) s

-- A tree has at most one zero-delay head shape.

head0-unique : ∀ {A ε w s s'} {t : Tˢ A ε w}
             → Head0 t s → Head0 t s'
             ------------------------
             → s ≡ s'

head0-unique h-leaf      h-leaf      = refl
head0-unique h-op        h-op        = refl
head0-unique (h-sub h)   (h-sub h')  = head0-unique h h'
head0-unique (h-delay h) (h-delay h') = head0-unique h h'

-- Grade substitution is invisible.

head0-ε-subst : ∀ {A ε ε' w s} → (e : ε ≡ ε') → {t : Tˢ A ε w}
              → Head0 (ε-substˢ e t) s
              -----------------------
              → Head0 t s
head0-ε-subst refl h = h

head0-ε-subst⁺ : ∀ {A ε ε' w s} → (e : ε ≡ ε') → {t : Tˢ A ε w}
               → Head0 t s
               ------------------------
               → Head0 (ε-substˢ e t) s
head0-ε-subst⁺ refl h = h

-- Retargeting the canonical step: all zero-steps out of a world into the same
-- world agree (`⊑-irrelevant`), which is what the two delay collapses need.

head0-⊑ : ∀ {A ε w s}
        → (k : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ 0) ] w' → Tˢ A ε w')
        → (q q' : w ⊑[ mapᵉ (of-natᵉ 0) ] w)
        → Head0 (k q) s
        ----------------
        → Head0 (k q') s
head0-⊑ k q q' h = subst (λ z → Head0 (k z) _) (⊑-irrelevant q q') h

------------------------------------------------------------------------
-- INVARIANCE
--
-- Bisimilar trees have the same zero-delay head shape. Mutually with its
-- converse, since `≈ᵗ-sym` is a constructor. Every case recurses on a
-- sub-derivation of `_≈ᵗ_` — including the two delay collapses, whose
-- continuation coherences (`ek`, `hk`) are fields of the derivation.
------------------------------------------------------------------------

mutual

  head0-≈ᵗ : ∀ {A ε w s} {t t' : Tˢ A ε w}
           → t ≈ᵗ t' → Head0 t s
           ---------------------
           → Head0 t' s

  head0-≈ᵗ (leaf-≈ _)   h-leaf              = h-leaf
  head0-≈ᵗ (op-≈ _ _)   h-op                = h-op
  head0-≈ᵗ (delay-≈ ek) (h-delay h)         = h-delay (head0-≈ᵗ (ek ⊑-delay0) h)
  head0-≈ᵗ (sub-≈ et)   (h-sub h)           = h-sub (head0-≈ᵗ et h)
  head0-≈ᵗ sub-u        (h-sub h)           = h
  head0-≈ᵗ sub-∘        (h-sub (h-sub h))   = h-sub h
  head0-≈ᵗ sub-delay    (h-sub (h-delay h)) = h-delay (h-sub h)
  head0-≈ᵗ sub-op       (h-sub h-op)        = h-op

  -- a zero delay *is* its own continuation, at the only zero-step there is
  head0-≈ᵗ (delay-zero {k = k} {q₀ = q₀} e) (h-delay h) =
    head0-ε-subst⁺ e (head0-⊑ k ⊑-delay0 q₀ h)

  -- two zero delays are the one zero delay: the split of the canonical step is
  -- the canonical step
  head0-≈ᵗ (delay-plus {τ₁ = zero} {τ₂ = zero} {k = k} hk e) (h-delay (h-delay h)) =
    head0-ε-subst⁺ e
      (h-delay (head0-⊑ k (⊑-split ⊑-delay0 ⊑-delay0) ⊑-delay0
                          (head0-≈ᵗ (hk ⊑-delay0 ⊑-delay0) h)))
  -- a delay that delays cannot be descended
  head0-≈ᵗ (delay-plus {τ₁ = zero} {τ₂ = suc _} hk e) (h-delay ())
  head0-≈ᵗ (delay-plus {τ₁ = suc _} hk e) ()

  head0-≈ᵗ (≈ᵗ-sym et)       h = head0-≈ᵗ⁻ et h
  head0-≈ᵗ (≈ᵗ-trans et et') h = head0-≈ᵗ et' (head0-≈ᵗ et h)

  head0-≈ᵗ⁻ : ∀ {A ε w s} {t t' : Tˢ A ε w}
            → t ≈ᵗ t' → Head0 t' s
            ----------------------
            → Head0 t s

  head0-≈ᵗ⁻ (leaf-≈ _)   h-leaf              = h-leaf
  head0-≈ᵗ⁻ (op-≈ _ _)   h-op                = h-op
  head0-≈ᵗ⁻ (delay-≈ ek) (h-delay h)         = h-delay (head0-≈ᵗ⁻ (ek ⊑-delay0) h)
  head0-≈ᵗ⁻ (sub-≈ et)   (h-sub h)           = h-sub (head0-≈ᵗ⁻ et h)
  head0-≈ᵗ⁻ sub-u        h                   = h-sub h
  head0-≈ᵗ⁻ sub-∘        (h-sub h)           = h-sub (h-sub h)
  head0-≈ᵗ⁻ sub-delay    (h-delay (h-sub h)) = h-sub (h-delay h)
  head0-≈ᵗ⁻ sub-op       h-op                = h-sub h-op

  head0-≈ᵗ⁻ (delay-zero {k = k} {q₀ = q₀} e) h =
    h-delay (head0-⊑ k q₀ ⊑-delay0 (head0-ε-subst e h))

  head0-≈ᵗ⁻ (delay-plus {τ₁ = zero} {τ₂ = zero} {k = k} hk e) h
    with head0-ε-subst e h
  ... | h-delay h' =
    h-delay (h-delay
      (head0-≈ᵗ⁻ (hk ⊑-delay0 ⊑-delay0)
        (head0-⊑ k ⊑-delay0 (⊑-split ⊑-delay0 ⊑-delay0) h')))
  head0-≈ᵗ⁻ (delay-plus {τ₁ = zero} {τ₂ = suc _} hk e) h
    with head0-ε-subst e h
  ... | ()
  head0-≈ᵗ⁻ (delay-plus {τ₁ = suc _} hk e) h
    with head0-ε-subst e h
  ... | ()

  head0-≈ᵗ⁻ (≈ᵗ-sym et)       h = head0-≈ᵗ et h
  head0-≈ᵗ⁻ (≈ᵗ-trans et et') h = head0-≈ᵗ⁻ et (head0-≈ᵗ⁻ et' h)

------------------------------------------------------------------------
-- NO-CONFUSION AT ZERO DELAY
------------------------------------------------------------------------

-- A returned value is never an operation. Stated at the head observation: a
-- leaf and an operation node sit at different effect grades, and whichever
-- `ε-substˢ`/`sub` the two denotations are presented with, `Head0` sees
-- through it.

ret≉op : ∀ {A ε w} {op : Op} {t t' : Tˢ A ε w}
       → t ≈ᵗ t'
       → Head0 t ret-shape → Head0 t' (op-shape op)
       --------------------------------------------
       → ⊥
ret≉op et h h' = ret≢op-shape (head0-unique (head0-≈ᵗ et h) h')

-- Distinct operations are distinct nodes.

op-inj : ∀ {A ε w} {op op' : Op} {t t' : Tˢ A ε w}
       → t ≈ᵗ t'
       → Head0 t (op-shape op) → Head0 t' (op-shape op')
       -------------------------------------------------
       → op ≡ op'
op-inj et h h' = op-shape-inj (head0-unique (head0-≈ᵗ et h) h')
