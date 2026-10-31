------------------------------------------------------------------------
-- Head shapes of effect trees, at zero delay.                        --
--                                                                    --
-- `Head0 t s` reads off `t`'s head, descending only structure that   --
-- takes no time. This is `HeadFaithful`'s `ret≢op`/`op-inj` at zero  --
-- delay. The durations are stepped, so that no time is a sum only of --
-- no time.                                                           --
------------------------------------------------------------------------

open import Data.Empty

open import Grades.Durations using (Stepped)
open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base as B
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module MonomorphicCalculus.Adequacy.PSh.TreeShape
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
open Stepped st using (zero-sumˡ; zero-sumʳ)

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base Grades Wld
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future Grades Wld
open GroundTypes GTy

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Core Spec Wld GTy

data Shape : Set where
  ret-shape : Shape
  op-shape  : Op → Shape

ret≢op-shape : ∀ {op} → ret-shape ≡ op-shape op → ⊥
ret≢op-shape ()

op-shape-inj : ∀ {op op'} → op-shape op ≡ op-shape op' → op ≡ op'
op-shape-inj refl = refl

-- `sub` nodes are transparent (reduction discards a `coerce`); a delay is
-- descended only when it delays by nothing, along a zero-step.

⊑-zero : ∀ {τ w} → τ ≡ 0ᴰ → w ⊑[ mapᵉ (of-durᵉ τ) ] w
⊑-zero refl = ⊑-delay0

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

  h-delay : ∀ {ε w s τ}
          → {k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w'}
          → {kn : ∀ {w' w''} (q : w ⊑[ mapᵉ (of-durᵉ τ) ] w') (r : w' ⊑[ uᵣ ] w'')
                → k (⊑ρ∘ᵘ q r) ≈ᵗ transportᵗ r (k q)}
          → (z : τ ≡ 0ᴰ)
          → Head0 (k (⊑-zero z)) s
          -----------------------------
          → Head0 (delay-node τ k kn) s

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
head0-unique {t = delay-node _ k _} (h-delay z h) (h-delay z' h') =
  head0-unique h (subst (λ q → Head0 (k q) _) (⊑-irrelevant _ _) h')

-- A sub-effecting node is invisible.

head0-sub⁻ : ∀ {A ε ε' w s} {e : ε ≾ₑ ε'} {t : Tˢ A ε w}
           → Head0 (sub e t) s
           -------------------
           → Head0 t s
head0-sub⁻ (h-sub h) = h

-- All zero-steps out of a world into the same world agree (`⊑-irrelevant`),
-- which is what the two delay collapses need.

head0-⊑ : ∀ {A ε w s τ}
        → (k : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε w')
        → (q q' : w ⊑[ mapᵉ (of-durᵉ τ) ] w)
        → Head0 (k q) s
        ----------------
        → Head0 (k q') s
head0-⊑ k q q' h = subst (λ z → Head0 (k z) _) (⊑-irrelevant q q') h

-- Bisimilar trees have the same zero-delay head shape. Mutual with its
-- converse, since `≈ᵗ-sym` is a constructor.

mutual

  head0-≈ᵗ : ∀ {A ε w s} {t t' : Tˢ A ε w}
           → t ≈ᵗ t' → Head0 t s
           ---------------------
           → Head0 t' s

  head0-≈ᵗ (leaf-≈ _)   h-leaf              = h-leaf
  head0-≈ᵗ (op-≈ _ _)   h-op                = h-op
  head0-≈ᵗ (delay-≈ ek) (h-delay z h)       = h-delay z (head0-≈ᵗ (ek _) h)
  head0-≈ᵗ (sub-≈ et)   (h-sub h)           = h-sub (head0-≈ᵗ et h)
  head0-≈ᵗ sub-u        (h-sub h)           = h
  head0-≈ᵗ sub-∘        (h-sub (h-sub h))   = h-sub h
  head0-≈ᵗ sub-delay    (h-sub (h-delay z h)) = h-delay z (h-sub h)
  head0-≈ᵗ sub-op       (h-sub h-op)        = h-op

  -- a zero delay is its own continuation, at the only zero-step there is
  head0-≈ᵗ (delay-zero {k = k} {q₀ = q₀} e) (h-delay z h) =
    h-sub (head0-⊑ k _ q₀ h)

  -- two zero delays are the one zero delay: the split of a zero-step is a
  -- zero-step
  head0-≈ᵗ (delay-plus {k = k} hk e) (h-delay z₁ (h-delay z₂ h)) =
    h-sub
      (h-delay (trans (cong₂ _+ᴰ_ z₁ z₂) (+ᴰ-identityˡ 0ᴰ))
               (head0-⊑ k _ _ (head0-≈ᵗ (hk _ _) h)))

  head0-≈ᵗ (≈ᵗ-sym et)       h = head0-≈ᵗ⁻ et h
  head0-≈ᵗ (≈ᵗ-trans et et') h = head0-≈ᵗ et' (head0-≈ᵗ et h)

  head0-≈ᵗ⁻ : ∀ {A ε w s} {t t' : Tˢ A ε w}
            → t ≈ᵗ t' → Head0 t' s
            ----------------------
            → Head0 t s

  head0-≈ᵗ⁻ (leaf-≈ _)   h-leaf              = h-leaf
  head0-≈ᵗ⁻ (op-≈ _ _)   h-op                = h-op
  head0-≈ᵗ⁻ (delay-≈ ek) (h-delay z h)       = h-delay z (head0-≈ᵗ⁻ (ek _) h)
  head0-≈ᵗ⁻ (sub-≈ et)   (h-sub h)           = h-sub (head0-≈ᵗ⁻ et h)
  head0-≈ᵗ⁻ sub-u        h                   = h-sub h
  head0-≈ᵗ⁻ sub-∘        (h-sub h)           = h-sub (h-sub h)
  head0-≈ᵗ⁻ sub-delay    (h-delay z (h-sub h)) = h-sub (h-delay z h)
  head0-≈ᵗ⁻ sub-op       h-op                = h-sub h-op

  head0-≈ᵗ⁻ (delay-zero {k = k} {q₀ = q₀} e) h =
    h-delay refl (head0-⊑ k q₀ _ (head0-sub⁻ h))

  head0-≈ᵗ⁻ (delay-plus {k = k} hk e) h
    with head0-sub⁻ h
  ... | h-delay z h' =
    h-delay (zero-sumˡ z) (h-delay (zero-sumʳ z)
      (head0-≈ᵗ⁻ (hk _ _) (head0-⊑ k _ _ h')))

  head0-≈ᵗ⁻ (≈ᵗ-sym et)       h = head0-≈ᵗ et h
  head0-≈ᵗ⁻ (≈ᵗ-trans et et') h = head0-≈ᵗ⁻ et (head0-≈ᵗ⁻ et' h)

-- A returned value is never an operation. Stated at the head observation,
-- which sees through the `sub` nodes the two denotations carry (a leaf
-- and an operation node sit at different effect grades).

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
