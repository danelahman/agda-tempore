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

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.Termination.Bind (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           Spec
open import MonomorphicCalculus.OperationalSemantics.State               Spec

open import MonomorphicCalculus.Syntax.Contexts        Spec
open import MonomorphicCalculus.Syntax.Terms           Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming        Spec
open import MonomorphicCalculus.Syntax.Substitution    Spec
open import MonomorphicCalculus.Syntax.Types           Spec

open import MonomorphicCalculus.OperationalSemantics.Termination.Environment Spec
open import MonomorphicCalculus.OperationalSemantics.Termination.Reducibility Spec
open import MonomorphicCalculus.Syntax.Renaming.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Renaming.Coherence    Spec
open import MonomorphicCalculus.Syntax.Terms.Equivalence     Spec
open import MonomorphicCalculus.Syntax.Terms.Transport       Spec
open import MonomorphicCalculus.Syntax.Substitution.Variables  Spec
open import MonomorphicCalculus.Syntax.Substitution.At         Spec
open import MonomorphicCalculus.OperationalSemantics.GradedReach Spec
open import MonomorphicCalculus.Syntax.Substitution.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Substitution.Subsumption  Spec

-- Induction on the scrutinee's `CRed` derivation, recursing on the `pk` field
-- exactly as `CRed-≐ˢ` does. The scrutinee is taken at a skeleton rather than
-- at its own type: `pk` stands at the skeleton its own `CRed` was indexed by,
-- which is what the recursive call is handed.

seq-CRed : ∀ {s A B ε₁ ε₂} {e : shapeᵛ A ≡ s} {St : 𝕊 []}
         → {M : toCtx St ⊢C⦂ A ‼ ε₁}
         → (N : toCtx St ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
         → CRedˢ' s e ε₁ St M
         → (∀ {St₁ : 𝕊 []} → (q : St ⊑ₛ[ mapᵉ ε₁ ] St₁)
              → (V : toCtx St₁ ⊢V⦂ A) → VRed A St₁ V
              → CRed' B ε₂ St₁
                  ((C-rename (cong-∷-ren (unbox-ren q)) N) [ split-[] ↦ V ]c))
         ------------------------------------------------------------------
         → CRed' B (ε₁ ·ₑ ε₂) St (M ⨟ N)

-- The scrutinee returns.

seq-CRed {A = A} {B = B} {ε₁ = ε₁} {ε₂ = ε₂} {St = St} N
         (cred-ret {St₁ = St₁} {V = V} e₀ rs pV) hN
  with seq-steps rs N

... | N₁ , rs' , eN₁ =
  CRed-expand* {e₀ = refl} rs'
    (CRed-expand SEQ-RET
      (CRed-≡ᶜ shift (hN q (spine rs V) (VRed-spine rs V (VRedˢ-≡ˢ pV)))))
  where
    E₀  = steps-extends-state rs
    srs = suc-comp-ren E₀ (steps-grade-≾ rs)

    b : ≤ₛ-grade E₀ ≾ᵣ mapᵉ ε₁
    b = ≾ᵣ-trans
          (≃ᵣ⇒≾ᵣ
            (≃ᵣ-trans (≃ᵣ-sym (·ᵣ-identityʳ (≤ₛ-grade E₀))) (·ᵣ-cong ≃ᵣ-refl (≃ᵣ-sym map-uᵉ))))
          (steps-grade-≾ rs)

    q = reach E₀ b

    -- the renaming `SEQ-RET` puts in front of the sequel it reached
    R₁ : Ren [] (toCtx St₁) (toCtx St₁ ⟨ mapᵉ uₑ ⟩)
    R₁ = ⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren

    eqr : (srs ∘ʳ R₁) ≐ʳ unbox-ren q
    eqr = ≐ʳ-trans (≐ʳ-sym (∘ʳ-assoc-≐ʳ srs (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ))
                                       ⟨⟩-η-ren))
                   (∘ʳ-≐ʳ (≐ʳ-sym (suc-comp-ren-≤ E₀ (reach-bound q) (steps-grade-≾ rs) (≃ᵣ⇒≿ᵣ map-uᵉ)))
                         ≐ʳ-refl)

    ren-shift : C-rename (cong-∷-ren R₁) (C-rename (cong-∷-ren srs) N)
              ≡ C-rename (cong-∷-ren (unbox-ren q)) N
    ren-shift =
      trans (sym (C-rename-∘ (cong-∷-ren srs) (cong-∷-ren R₁) N))
            (C-rename-≡ (≐ʳ-trans (≐ʳ-sym (cong-∷-ren-∘-≐ʳ srs R₁))
                                  (cong-∷-ren-≐ʳ eqr)) N)

    -- the sequel the run reached takes the whnf where the original takes its
    -- spine
    shift : (C-rename (cong-∷-ren (unbox-ren q)) N) [ split-[] ↦ spine rs V ]c
          ≡ (C-rename (cong-∷-ren R₁) N₁) [ split-[] ↦ V ]c
    shift =
      sym
        (trans
          (sub-≡ᶜ split-[] refl
            (trans (C-rename-cong (cong-∷-ren R₁) eN₁)
              (trans (subCtx-run-ren rs R₁ (C-rename (cong-∷-ren srs) N))
                     (cong (subCtx-run rs) ren-shift))))
          (subCtx-run-sub rs (C-rename (cong-∷-ren (unbox-ren q)) N) V))

-- The scrutinee gets stuck on an operation.

seq-CRed {A = A} {B = B} {ε₁ = ε₁} {ε₂ = ε₂} {St = St} N
         (cred-op {A₀ = A₀} {ε₁ = ε₃} {St₁ = St₁} {op = op} {W = W} {M' = M'}
                  e₀ rs pW pk) hN
  with seq-steps rs N

... | N₁ , rs' , eN₁ =
  CRed-expand* {e₀ = refl} rs'
    (CRed-expand {e₀ = refl} SEQ-OP
      (CRed-coerce (≃ₑ⇒≿ₑ (·ₑ-assoc (op-grade op) ε₃ ε₂))
        (cred-op refl ε* pW resump)))
  where
    ρₒ  = mapᵉ (op-grade op)
    Ar  = type-of-gtype (arity op)
    E₀  = steps-extends-state rs
    b₀  = steps-grade-≾ rs
    srs = suc-comp-ren E₀ b₀


    -- the renaming `SEQ-OP` puts in front of the sequel it reached
    κ : Ren [] ((toCtx St₁ ⟨ ρₒ ⟩ ∷ Ar) ⟨ mapᵉ ε₃ ⟩)
              (toCtx St₁ ⟨ mapᵉ (op-grade op ·ₑ ε₃) ⟩)
    κ = (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren

    N₂ = C-rename (cong-∷-ren κ) N₁

    resump : ∀ {St₂ : 𝕊 []} → (q : St₁ ⊑ₛ[ ρₒ ] St₂)
           → (W' : toCtx St₂ ⊢V⦂ Ar)
           → VRedᵍ (arity op) St₂ W'
           → CRed' B (ε₃ ·ₑ ε₂) St₂ (resume q (M' ⨟ N₂) W')

    resump {St₂} q W' pW' = seq-CRed {e = e₀} N₃ (pk q W' pW') hN₃
      where
        sq = unbox-ren q

        N₃ = (C-rename (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq))) N₂)
               [ split-∷ (split-⟨⟩ split-[]) ↦ W' ]c

        B₁' : ≤ₛ-grade (ext q) ·ᵣ mapᵉ ε₃ ≾ᵣ ρₒ ·ᵣ mapᵉ ε₃
        B₁' = ·ᵣ-monoˡ-≾ᵣ (bound q)

        B₁ : ≤ₛ-grade (ext q) ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ (op-grade op ·ₑ ε₃)
        B₁ = ≾ᵣ-trans B₁' (≃ᵣ⇒≿ᵣ map-·ᵉ)

        -- what is left of the sequel's renaming once the arity variable is gone
        W₁ : Ren [] (toCtx St₂ ⟨ mapᵉ ε₃ ⟩)
                  (toCtx St₁ ⟨ mapᵉ (op-grade op ·ₑ ε₃) ⟩)
        W₁ = (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren sq

        eW₁ : W₁ ≐ʳ suc-comp-ren (ext q) B₁
        eW₁ =
          ≐ʳ-trans (∘ʳ-assoc-≐ʳ (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ)) ⟨⟩-μ-ren (cong-⟨⟩-ren sq))
            (≐ʳ-trans (∘ʳ-≐ʳ ≐ʳ-refl (unbox-ren-μ-≐ʳ q B₁'))
                      (≐ʳ-sym (suc-comp-ren-≤ˡ (ext q) B₁ B₁' (≃ᵣ⇒≿ᵣ map-·ᵉ))))

        -- the sequel the recursion needs is the original one, renamed and
        -- subsumed along the run
        eN₃ : N₃ ≡ subCtx-run rs (C-rename (cong-∷-ren (srs ∘ʳ W₁)) N)
        eN₃ =
          trans (sub-≡ᶜ (split-∷ (split-⟨⟩ split-[])) (refl) split-off)
            (trans (sub-wk-C ([] ⟨ mapᵉ ε₃ ⟩ ∷ A₀)
                                (C-rename (cong-∷-ren W₁) N₁) W')
              (trans (C-rename-cong (cong-∷-ren W₁) eN₁)
                (trans (subCtx-run-ren rs W₁ (C-rename (cong-∷-ren srs) N))
                  (cong (subCtx-run rs)
                    (trans (sym (C-rename-∘ (cong-∷-ren srs) (cong-∷-ren W₁) N))
                           (C-rename-≡ (≐ʳ-sym (cong-∷-ren-∘-≐ʳ srs W₁)) N))))))
          where
            inner : (κ ∘ʳ cong-⟨⟩-ren (cong-∷-ren sq))
                  ≐ʳ (W₁ ∘ʳ cong-⟨⟩-ren wk-ren)
            inner =
              ≐ʳ-trans (∘ʳ-assoc-≐ʳ (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ) ∘ʳ ⟨⟩-μ-ren)
                                   (cong-⟨⟩-ren wk-ren)
                                   (cong-⟨⟩-ren (cong-∷-ren sq)))
                (≐ʳ-trans
                  (∘ʳ-≐ʳ ≐ʳ-refl
                    (≐ʳ-trans (≐ʳ-sym (cong-⟨⟩-ren-∘-≐ʳ wk-ren (cong-∷-ren sq)))
                      (≐ʳ-trans (cong-⟨⟩-ren-≐ʳ (wk-ren-nat-≐ʳ sq))
                                (cong-⟨⟩-ren-∘-≐ʳ sq wk-ren))))
                  (≐ʳ-sym (∘ʳ-assoc-≐ʳ (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ) ∘ʳ ⟨⟩-μ-ren)
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
            → (V : toCtx St₃ ⊢V⦂ A₀) → VRed A₀ St₃ V
            → CRed' B ε₂ St₃
                ((C-rename (cong-∷-ren (unbox-ren q')) N₃) [ split-[] ↦ V ]c)

        hN₃ {St₃} q' V pV =
          CRed-≡ᶜ shift (hN q₁ (spine rs V) (VRed-spine rs V pV))
          where
            -- the run and the clause's own reach accumulate: the grades multiply
            -- and each is bounded, so the composite stays under `ε₁`
            B₂ : ≤ₛ-grade (≤ₛ-trans E₀ (ext q)) ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ ε₁
            B₂ =
              ≾ᵣ-trans
                (≃ᵣ⇒≾ᵣ
                  (≃ᵣ-trans (·ᵣ-cong (≤ₛ-grade-trans E₀ (ext q)) ≃ᵣ-refl) (·ᵣ-assoc (≤ₛ-grade E₀) (≤ₛ-grade (ext q)) (mapᵉ ε₃))))
                (≾ᵣ-trans (·ᵣ-monoʳ-≾ᵣ B₁) b₀)

            q₁ : St ⊑ₛ[ mapᵉ ε₁ ] St₃
            q₁ = reach (≤ₛ-trans (≤ₛ-trans E₀ (ext q)) (ext q'))
                   (≾ᵣ-trans
                     (≃ᵣ⇒≾ᵣ
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

            ren-shift : C-rename (cong-∷-ren (unbox-ren q'))
                          (C-rename (cong-∷-ren (srs ∘ʳ W₁)) N)
                      ≡ C-rename (cong-∷-ren (unbox-ren q₁)) N
            ren-shift =
              sym
                (trans
                  (C-rename-≡
                    (≐ʳ-trans (cong-∷-ren-≐ʳ finalEq)
                              (cong-∷-ren-∘-≐ʳ (srs ∘ʳ W₁) (unbox-ren q'))) N)
                  (C-rename-∘ (cong-∷-ren (srs ∘ʳ W₁))
                              (cong-∷-ren (unbox-ren q')) N))

            shift : (C-rename (cong-∷-ren (unbox-ren q₁)) N)
                      [ split-[] ↦ spine rs V ]c
                  ≡ (C-rename (cong-∷-ren (unbox-ren q')) N₃)
                      [ split-[] ↦ V ]c
            shift =
              sym
                (trans
                  (sub-≡ᶜ split-[] refl
                    (trans (C-rename-cong (cong-∷-ren (unbox-ren q')) eN₃)
                      (trans (subCtx-run-ren rs (unbox-ren q')
                                (C-rename (cong-∷-ren (srs ∘ʳ W₁)) N))
                             (cong (subCtx-run rs) ren-shift))))
                  (subCtx-run-sub rs
                    (C-rename (cong-∷-ren (unbox-ren q₁)) N) V))
