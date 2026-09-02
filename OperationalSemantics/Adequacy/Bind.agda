------------------------------------------------------------------------
-- Bind: sequencing preserves reducibility.                           --
--                                                                    --
-- Stated about `CRed` alone — over the sequel *term* and its effect,  --
-- at an arbitrary state — rather than over closing environments,     --
-- because `SEQ-OP` floats the operation out and leaves the sequel at  --
-- a context no environment reaches. Above `Environment` because the   --
-- `cred-op` case needs `sub-wk-C`.                                    --
------------------------------------------------------------------------

open import Data.Product

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.Bind (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem Spec
open import OperationalSemantics.State               Spec

open import Syntax.Contexts      Spec
open import Syntax.Language      Spec
open import Syntax.RenActions    Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

open import OperationalSemantics.Adequacy.Environment    Spec
open import OperationalSemantics.Adequacy.Reducibility   Spec
open import Syntax.Renamings.Equivalence Spec
open import Syntax.Renamings.Coherence   Spec
open import Syntax.Terms.Equivalence     Spec
open import Syntax.Terms.Transport       Spec
open import Syntax.Substitutions.Variables Spec
open import Syntax.Substitutions.At        Spec
open import OperationalSemantics.Adequacy.GradedReach          Spec
open import Syntax.Substitutions.Equivalence Spec

------------------------------------------------------------------------
-- BIND
--
-- Induction on the scrutinee's `CRed` derivation, recursing on the `pk` field
-- exactly as `CRed-≐ˢ` does.
--
--   * `cred-ret` runs the scrutinee to a `return` (`seq-steps`), fires
--     `SEQ-RET`, and hands the value to the sequel premise. The run's own reach
--     lands at `mapᵉ uₑ` where a graded reach wants `uᵣ`, which `suc-comp-ren-grade`
--     reconciles.
--   * `cred-op` runs it to a `perform`, floats the operation out with `SEQ-OP`
--     and recurses at the resumption. The sequel the recursion needs is the
--     original one weakened past the operation's arity variable, so firing the
--     outer sequel premise means *undoing* that weakening — which is `sub-wk-C`.
------------------------------------------------------------------------

seq-CRed : ∀ {A B ε₁ ε₂} {St : 𝕊 []}
         → {M : toCtx St ⊢C⦂ A ‼ ε₁}
         → (N : toCtx St ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
         → CRed' A ε₁ St M
         → (∀ {St₁ : 𝕊 []} → (q : St ⊑ₛ[ mapᵉ ε₁ ] St₁)
              → (V : toCtx St₁ ⊢V⦂ A) → VRed A St₁ V
              → CRed' B ε₂ St₁
                  ((C-rename (cong-∷-ren (unbox-ren q)) N) [ split-[] ↦ V ]c))
         ------------------------------------------------------------------
         → CRed' B (ε₁ ·ₑ ε₂) St (M ⨟ N)

-- The scrutinee returns.

seq-CRed {A} {B} {ε₁} {ε₂} {St} N (cred-ret {St₁ = St₁} {V = V} rs pV) hN
  with seq-steps rs N

... | N₁ , rs' , eN₁ =
  CRed-expand* rs'
    (CRed-expand SEQ-RET
      (CRed-≡ᶜ (sub-≡ᶜ split-[] (refl) shift) (hN q V pV)))
  where
    E₀  = steps-extends-state rs
    srs = suc-comp-ren E₀ (steps-grade-≾ rs)

    b : ≤ₛ-grade E₀ ≾ᵣ mapᵉ ε₁
    b = ≾ᵣ-trans
          (≾ᵣ-reflexive
            (trans (sym (·ᵣ-identityʳ (≤ₛ-grade E₀)))
                   (cong (≤ₛ-grade E₀ ·ᵣ_) (sym map-uᵉ))))
          (steps-grade-≾ rs)

    q = reach E₀ b

    -- the renaming `SEQ-RET` puts in front of the sequel it reached
    R₁ : Ren [] (toCtx St₁) (toCtx St₁ ⟨ mapᵉ uₑ ⟩)
    R₁ = eq-ren (cong (toCtx St₁ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren

    eqr : (srs ∘ʳ R₁) ≐ʳ unbox-ren q
    eqr = ≐ʳ-trans (≐ʳ-sym (∘ʳ-assoc-≐ʳ srs (eq-ren (cong (toCtx St₁ ⟨_⟩) map-uᵉ))
                                       ⟨⟩-η-ren))
                   (∘ʳ-≐ʳ (suc-comp-ren-grade E₀ map-uᵉ (steps-grade-≾ rs)
                                             (reach-bound q))
                         ≐ʳ-refl)

    shift : C-rename (cong-∷-ren (unbox-ren q)) N
          ≡ C-rename (cong-∷-ren R₁) N₁
    shift =
      sym
        (trans (C-rename-cong (cong-∷-ren R₁) eN₁)
          (trans (sym (C-rename-∘ (cong-∷-ren srs) (cong-∷-ren R₁) N))
            (C-rename-≡ (≐ʳ-trans (≐ʳ-sym (cong-∷-ren-∘-≐ʳ srs R₁))
                                  (cong-∷-ren-≐ʳ eqr)) N)))

-- The scrutinee gets stuck on an operation.

seq-CRed {A} {B} {ε₁} {ε₂} {St} N
         (cred-op {ε₁ = ε₃} {St₁ = St₁} {op = op} {W = W} {M' = M'} rs pW pk) hN
  with seq-steps rs N

... | N₁ , rs' , eN₁ =
  CRed-expand* rs'
    (CRed-expand SEQ-OP
      (CRed-ε-subst (sym (·ₑ-assoc (op-grade op) ε₃ ε₂))
        (cred-op ε* pW resump)))
  where
    ρₒ  = mapᵉ (op-grade op)
    Ar  = type-of-gtype (arity op)
    E₀  = steps-extends-state rs
    b₀  = steps-grade-≾ rs
    srs = suc-comp-ren E₀ b₀

    emap : toCtx St₁ ⟨ mapᵉ (op-grade op ·ₑ ε₃) ⟩
         ≡ toCtx St₁ ⟨ ρₒ ·ᵣ mapᵉ ε₃ ⟩
    emap = cong (toCtx St₁ ⟨_⟩) map-·ᵉ

    -- the renaming `SEQ-OP` puts in front of the sequel it reached
    κ : Ren [] ((toCtx St₁ ⟨ ρₒ ⟩ ∷ Ar) ⟨ mapᵉ ε₃ ⟩)
              (toCtx St₁ ⟨ mapᵉ (op-grade op ·ₑ ε₃) ⟩)
    κ = (eq-ren emap ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren

    N₂ = C-rename (cong-∷-ren κ) N₁

    resump : ∀ {St₂ : 𝕊 []} → (q : St₁ ⊑ₛ[ ρₒ ] St₂)
           → (W' : toCtx St₂ ⊢V⦂ Ar)
           → VRedᵍ (arity op) St₂ W'
           → CRed' B (ε₃ ·ₑ ε₂) St₂ (resume q (M' ⨟ N₂) W')

    resump {St₂} q W' pW' = seq-CRed N₃ (pk q W' pW') hN₃
      where
        sq = unbox-ren q

        N₃ = (C-rename (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq))) N₂)
               [ split-∷ (split-⟨⟩ split-[]) ↦ W' ]c

        B₁' : ≤ₛ-grade (ext q) ·ᵣ mapᵉ ε₃ ≾ᵣ ρₒ ·ᵣ mapᵉ ε₃
        B₁' = ·ᵣ-monoˡ-≾ᵣ (bound q)

        B₁ : ≤ₛ-grade (ext q) ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ (op-grade op ·ₑ ε₃)
        B₁ = ≾ᵣ-trans B₁' (≾ᵣ-reflexive (sym map-·ᵉ))

        -- what is left of the sequel's renaming once the arity variable is gone
        W₁ : Ren [] (toCtx St₂ ⟨ mapᵉ ε₃ ⟩)
                  (toCtx St₁ ⟨ mapᵉ (op-grade op ·ₑ ε₃) ⟩)
        W₁ = (eq-ren emap ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren sq

        eW₁ : W₁ ≐ʳ suc-comp-ren (ext q) B₁
        eW₁ =
          ≐ʳ-trans (∘ʳ-assoc-≐ʳ (eq-ren emap) ⟨⟩-μ-ren (cong-⟨⟩-ren sq))
            (≐ʳ-trans (∘ʳ-≐ʳ ≐ʳ-refl (unbox-ren-μ-≐ʳ q B₁'))
                      (suc-comp-ren-grade-src (ext q) map-·ᵉ B₁' B₁))

        -- the sequel the recursion needs is the original one, renamed
        eN₃ : N₃ ≡ C-rename (cong-∷-ren (srs ∘ʳ W₁)) N
        eN₃ =
          trans (sub-≡ᶜ (split-∷ (split-⟨⟩ split-[])) (refl) split-off)
            (trans (sub-wk-C ([] ⟨ mapᵉ ε₃ ⟩ ∷ A)
                                (C-rename (cong-∷-ren W₁) N₁) W')
              (trans (C-rename-cong (cong-∷-ren W₁) eN₁)
                (trans (sym (C-rename-∘ (cong-∷-ren srs) (cong-∷-ren W₁) N))
                          (C-rename-≡ (≐ʳ-sym (cong-∷-ren-∘-≐ʳ srs W₁)) N))))
          where
            inner : (κ ∘ʳ cong-⟨⟩-ren (cong-∷-ren sq))
                  ≐ʳ (W₁ ∘ʳ cong-⟨⟩-ren wk-ren)
            inner =
              ≐ʳ-trans (∘ʳ-assoc-≐ʳ (eq-ren emap ∘ʳ ⟨⟩-μ-ren)
                                   (cong-⟨⟩-ren wk-ren)
                                   (cong-⟨⟩-ren (cong-∷-ren sq)))
                (≐ʳ-trans
                  (∘ʳ-≐ʳ ≐ʳ-refl
                    (≐ʳ-trans (≐ʳ-sym (cong-⟨⟩-ren-∘-≐ʳ wk-ren (cong-∷-ren sq)))
                      (≐ʳ-trans (cong-⟨⟩-ren-≐ʳ (wk-ren-nat-≐ʳ sq))
                                (cong-⟨⟩-ren-∘-≐ʳ sq wk-ren))))
                  (≐ʳ-sym (∘ʳ-assoc-≐ʳ (eq-ren emap ∘ʳ ⟨⟩-μ-ren)
                                      (cong-⟨⟩-ren sq)
                                      (cong-⟨⟩-ren wk-ren))))

            split-off : C-rename (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq))) N₂
                      ≡ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren))
                           (C-rename (cong-∷-ren W₁) N₁)
            split-off =
              trans
                (sym (C-rename-∘ (cong-∷-ren κ)
                                    (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq))) N₁))
                (trans
                  (C-rename-≡
                    (≐ʳ-trans
                      (≐ʳ-sym (cong-∷-ren-∘-≐ʳ κ (cong-⟨⟩-ren (cong-∷-ren sq))))
                      (≐ʳ-trans (cong-∷-ren-≐ʳ inner)
                                (cong-∷-ren-∘-≐ʳ W₁ (cong-⟨⟩-ren wk-ren))))
                    N₁)
                  (C-rename-∘ (cong-∷-ren W₁) (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N₁))

        hN₃ : ∀ {St₃ : 𝕊 []} → (q' : St₂ ⊑ₛ[ mapᵉ ε₃ ] St₃)
            → (V : toCtx St₃ ⊢V⦂ A) → VRed A St₃ V
            → CRed' B ε₂ St₃
                ((C-rename (cong-∷-ren (unbox-ren q')) N₃) [ split-[] ↦ V ]c)

        hN₃ {St₃} q' V pV =
          CRed-≡ᶜ (sub-≡ᶜ split-[] (refl) shift) (hN q₁ V pV)
          where
            -- the run and the clause's own reach accumulate: the grades multiply
            -- and each is bounded, so the composite stays under `ε₁`
            B₂ : ≤ₛ-grade (≤ₛ-trans E₀ (ext q)) ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ ε₁
            B₂ =
              ≾ᵣ-trans
                (≾ᵣ-reflexive
                  (trans (cong (_·ᵣ mapᵉ ε₃) (≤ₛ-grade-trans E₀ (ext q)))
                         (·ᵣ-assoc (≤ₛ-grade E₀) (≤ₛ-grade (ext q)) (mapᵉ ε₃))))
                (≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ B₁) b₀)

            q₁ : St ⊑ₛ[ mapᵉ ε₁ ] St₃
            q₁ = reach (≤ₛ-trans (≤ₛ-trans E₀ (ext q)) (ext q'))
                   (≾ᵣ-trans
                     (≾ᵣ-reflexive
                       (≤ₛ-grade-trans (≤ₛ-trans E₀ (ext q)) (ext q')))
                     (≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ (bound q')) B₂))

            composite : suc-comp-ren (ext q₁) (reach-bound q₁)
                      ≐ʳ ((srs ∘ʳ W₁) ∘ʳ suc-comp-ren (ext q') (reach-bound q'))
            composite =
              ≐ʳ-trans
                (suc-comp-ren-∘-≐ʳ (≤ₛ-trans E₀ (ext q)) (ext q')
                                  (reach-bound q₁) B₂ (reach-bound q'))
                (∘ʳ-≐ʳ (≐ʳ-trans (suc-comp-ren-∘-≐ʳ E₀ (ext q) B₂ b₀ B₁)
                                (∘ʳ-≐ʳ ≐ʳ-refl (≐ʳ-sym eW₁)))
                      ≐ʳ-refl)

            finalEq : unbox-ren q₁ ≐ʳ ((srs ∘ʳ W₁) ∘ʳ unbox-ren q')
            finalEq =
              ≐ʳ-trans (∘ʳ-≐ʳ composite (≐ʳ-refl {r = ⟨⟩-η-ren}))
                (∘ʳ-assoc-≐ʳ (srs ∘ʳ W₁)
                            (suc-comp-ren (ext q') (reach-bound q')) ⟨⟩-η-ren)

            shift : C-rename (cong-∷-ren (unbox-ren q₁)) N
                  ≡ C-rename (cong-∷-ren (unbox-ren q')) N₃
            shift =
              trans
                (C-rename-≡
                  (≐ʳ-trans (cong-∷-ren-≐ʳ finalEq)
                            (cong-∷-ren-∘-≐ʳ (srs ∘ʳ W₁) (unbox-ren q'))) N)
                (trans
                  (C-rename-∘ (cong-∷-ren (srs ∘ʳ W₁))
                              (cong-∷-ren (unbox-ren q')) N)
                  (C-rename-cong (cong-∷-ren (unbox-ren q')) (sym eN₃)))
