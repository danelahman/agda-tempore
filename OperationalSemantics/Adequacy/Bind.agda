------------------------------------------------------------------------
-- Bind: sequencing preserves reducibility.                           --
--                                                                    --
-- Stated about `Comp` alone — over the sequel *term* and its effect,  --
-- at an arbitrary state — rather than over closing environments,     --
-- because `SEQ-OP` floats the operation out and leaves the sequel at  --
-- a context no environment reaches. Above `Environment` because the   --
-- `comp-op` case needs `sub-wk-C`.                                    --
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
open import Syntax.Substitutions.Weakening Spec
open import OperationalSemantics.Adequacy.GradedReach          Spec
open import Syntax.Substitutions.Equivalence Spec

------------------------------------------------------------------------
-- BIND
--
-- Induction on the scrutinee's `Comp` derivation, recursing on the `pk` field
-- exactly as `Comp-≐` does.
--
--   * `comp-ret` runs the scrutinee to a `return` (`seq-steps`), fires
--     `SEQ-RET`, and hands the value to the sequel premise. The run's own reach
--     lands at `mapᵉ uₑ` where a graded reach wants `uᵣ`, which `suc-comp-ren-grade`
--     reconciles.
--   * `comp-op` runs it to a `perform`, floats the operation out with `SEQ-OP`
--     and recurses at the resumption. The sequel the recursion needs is the
--     original one weakened past the operation's arity variable, so firing the
--     outer sequel premise means *undoing* that weakening — which is `sub-wk-C`.
------------------------------------------------------------------------

seq-Comp : ∀ {A B ε₁ ε₂} {St : 𝕊 []}
         → {M : toCtx St ⊢C⦂ A ‼ ε₁}
         → (N : toCtx St ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
         → Comp' A ε₁ St M
         → (∀ {St₁ : 𝕊 []} → (q : St ⊑ₛ[ mapᵉ ε₁ ] St₁)
              → (V : toCtx St₁ ⊢V⦂ A) → Val A St₁ V
              → Comp' B ε₂ St₁
                  ((C-rename (cong-∷-ren (unbox-ren q)) N) [ Hd ↦ V ]c))
         ------------------------------------------------------------------
         → Comp' B (ε₁ ·ₑ ε₂) St (M ⨟ N)

-- The scrutinee returns.

seq-Comp {A} {B} {ε₁} {ε₂} {St} N (comp-ret {St₁ = St₁} {V = V} rs pV) hN
  with seq-steps rs N

... | N₁ , rs' , eN₁ =
  Comp-expand* rs'
    (Comp-expand SEQ-RET
      (Comp-≐ᶜ (sub-≐ᶜ Hd (≐ᵛ-refl V) shift) (hN q V pV)))
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
    R₁ : Ren [] (toCtx St₁ ⟨ mapᵉ uₑ ⟩) (toCtx St₁)
    R₁ = ⟨⟩-η-ren ∘ʳ eq-ren (cong (toCtx St₁ ⟨_⟩) map-uᵉ)

    eqr : (R₁ ∘ʳ srs) ≐ʳ unbox-ren q
    eqr = ≐ʳ-trans (∘ʳ-assoc-≐ ⟨⟩-η-ren (eq-ren (cong (toCtx St₁ ⟨_⟩) map-uᵉ)) srs)
                   (∘ʳ-≐ ≐ʳ-refl
                     (suc-comp-ren-grade E₀ map-uᵉ (steps-grade-≾ rs)
                                         (reach-bound q)))

    shift : C-rename (cong-∷-ren (unbox-ren q)) N
          ≐ᶜ C-rename (cong-∷-ren R₁) N₁
    shift =
      ≐ᶜ-sym
        (≐ᶜ-trans (C-rename-cong (cong-∷-ren R₁) eN₁)
          (≐ᶜ-trans (≐ᶜ-sym (C-rename-∘ (cong-∷-ren R₁) (cong-∷-ren srs) N))
            (C-rename-≐ (≐ʳ-trans (≐ʳ-sym (cong-∷-ren-∘-≐ R₁ srs))
                                  (cong-∷-ren-≐ eqr)) N)))

-- The scrutinee gets stuck on an operation.

seq-Comp {A} {B} {ε₁} {ε₂} {St} N
         (comp-op {ε₁ = ε₃} {St₁ = St₁} {op = op} {W = W} {M' = M'} rs pW pk) hN
  with seq-steps rs N

... | N₁ , rs' , eN₁ =
  Comp-expand* rs'
    (Comp-expand SEQ-OP
      (Comp-ε-subst (sym (·ₑ-assoc (op-grade op) ε₃ ε₂))
        (comp-op ε* pW resump)))
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
    κ : Ren [] (toCtx St₁ ⟨ mapᵉ (op-grade op ·ₑ ε₃) ⟩)
              ((toCtx St₁ ⟨ ρₒ ⟩ ∷ Ar) ⟨ mapᵉ ε₃ ⟩)
    κ = cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren ∘ʳ eq-ren emap

    N₂ = C-rename (cong-∷-ren κ) N₁

    resump : ∀ {St₂ : 𝕊 []} → (q : St₁ ⊑ₛ[ ρₒ ] St₂)
           → (W' : toCtx St₂ ⊢V⦂ Ar)
           → Valᵍ (arity op) St₂ W'
           → Comp' B (ε₃ ·ₑ ε₂) St₂ (resume q (M' ⨟ N₂) W')

    resump {St₂} q W' pW' = seq-Comp N₃ (pk q W' pW') hN₃
      where
        sq = unbox-ren q

        N₃ = (C-rename (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq))) N₂)
               [ Tl-∷ (Tl-⟨⟩ Hd) ↦ W' ]c

        B₁' : ≤ₛ-grade (ext q) ·ᵣ mapᵉ ε₃ ≾ᵣ ρₒ ·ᵣ mapᵉ ε₃
        B₁' = ·ᵣ-monoˡ-≾ᵣ (bound q)

        B₁ : ≤ₛ-grade (ext q) ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ (op-grade op ·ₑ ε₃)
        B₁ = ≾ᵣ-trans B₁' (≾ᵣ-reflexive (sym map-·ᵉ))

        -- what is left of the sequel's renaming once the arity variable is gone
        W₁ : Ren [] (toCtx St₁ ⟨ mapᵉ (op-grade op ·ₑ ε₃) ⟩)
                  (toCtx St₂ ⟨ mapᵉ ε₃ ⟩)
        W₁ = cong-⟨⟩-ren sq ∘ʳ ⟨⟩-μ-ren ∘ʳ eq-ren emap

        eW₁ : W₁ ≐ʳ suc-comp-ren (ext q) B₁
        eW₁ =
          ≐ʳ-trans (≐ʳ-sym (∘ʳ-assoc-≐ (cong-⟨⟩-ren sq) ⟨⟩-μ-ren (eq-ren emap)))
            (≐ʳ-trans (∘ʳ-≐ (unbox-ren-μ-≐ q B₁') ≐ʳ-refl)
                      (suc-comp-ren-grade-src (ext q) map-·ᵉ B₁' B₁))

        -- the sequel the recursion needs is the original one, renamed
        eN₃ : N₃ ≐ᶜ C-rename (cong-∷-ren (W₁ ∘ʳ srs)) N
        eN₃ =
          ≐ᶜ-trans (sub-≐ᶜ (Tl-∷ (Tl-⟨⟩ Hd)) (≐ᵛ-refl W') split-off)
            (≐ᶜ-trans (sub-wk-C ([] ⟨ mapᵉ ε₃ ⟩ ∷ A)
                                (C-rename (cong-∷-ren W₁) N₁) W')
              (≐ᶜ-trans (C-rename-cong (cong-∷-ren W₁) eN₁)
                (≐ᶜ-trans (≐ᶜ-sym (C-rename-∘ (cong-∷-ren W₁) (cong-∷-ren srs) N))
                          (C-rename-≐ (≐ʳ-sym (cong-∷-ren-∘-≐ W₁ srs)) N))))
          where
            inner : (cong-⟨⟩-ren (cong-∷-ren sq) ∘ʳ κ)
                  ≐ʳ (cong-⟨⟩-ren wk-ren ∘ʳ W₁)
            inner =
              ≐ʳ-trans (≐ʳ-sym (∘ʳ-assoc-≐ (cong-⟨⟩-ren (cong-∷-ren sq))
                                           (cong-⟨⟩-ren wk-ren)
                                           (⟨⟩-μ-ren ∘ʳ eq-ren emap)))
                (≐ʳ-trans
                  (∘ʳ-≐ (≐ʳ-trans (≐ʳ-sym (cong-⟨⟩-ren-∘-≐ (cong-∷-ren sq) wk-ren))
                          (≐ʳ-trans (cong-⟨⟩-ren-≐ (wk-ren-nat-≐ sq))
                                    (cong-⟨⟩-ren-∘-≐ wk-ren sq)))
                        ≐ʳ-refl)
                  (∘ʳ-assoc-≐ (cong-⟨⟩-ren wk-ren) (cong-⟨⟩-ren sq)
                              (⟨⟩-μ-ren ∘ʳ eq-ren emap)))

            split-off : C-rename (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq))) N₂
                      ≐ᶜ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren))
                           (C-rename (cong-∷-ren W₁) N₁)
            split-off =
              ≐ᶜ-trans
                (≐ᶜ-sym (C-rename-∘ (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren sq)))
                                    (cong-∷-ren κ) N₁))
                (≐ᶜ-trans
                  (C-rename-≐
                    (≐ʳ-trans
                      (≐ʳ-sym (cong-∷-ren-∘-≐ (cong-⟨⟩-ren (cong-∷-ren sq)) κ))
                      (≐ʳ-trans (cong-∷-ren-≐ inner)
                                (cong-∷-ren-∘-≐ (cong-⟨⟩-ren wk-ren) W₁)))
                    N₁)
                  (C-rename-∘ (cong-∷-ren (cong-⟨⟩-ren wk-ren)) (cong-∷-ren W₁) N₁))

        hN₃ : ∀ {St₃ : 𝕊 []} → (q' : St₂ ⊑ₛ[ mapᵉ ε₃ ] St₃)
            → (V : toCtx St₃ ⊢V⦂ A) → Val A St₃ V
            → Comp' B ε₂ St₃
                ((C-rename (cong-∷-ren (unbox-ren q')) N₃) [ Hd ↦ V ]c)

        hN₃ {St₃} q' V pV =
          Comp-≐ᶜ (sub-≐ᶜ Hd (≐ᵛ-refl V) shift) (hN q₁ V pV)
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
                      ≐ʳ (suc-comp-ren (ext q') (reach-bound q') ∘ʳ (W₁ ∘ʳ srs))
            composite =
              ≐ʳ-trans
                (suc-comp-ren-∘-≐ (≤ₛ-trans E₀ (ext q)) (ext q')
                                  (reach-bound q₁) B₂ (reach-bound q'))
                (∘ʳ-≐ ≐ʳ-refl
                  (≐ʳ-trans (suc-comp-ren-∘-≐ E₀ (ext q) B₂ b₀ B₁)
                            (∘ʳ-≐ (≐ʳ-sym eW₁) ≐ʳ-refl)))

            finalEq : unbox-ren q₁ ≐ʳ (unbox-ren q' ∘ʳ (W₁ ∘ʳ srs))
            finalEq =
              ≐ʳ-trans (∘ʳ-≐ (≐ʳ-refl {r = ⟨⟩-η-ren}) composite)
                (≐ʳ-sym (∘ʳ-assoc-≐ ⟨⟩-η-ren
                           (suc-comp-ren (ext q') (reach-bound q')) (W₁ ∘ʳ srs)))

            shift : C-rename (cong-∷-ren (unbox-ren q₁)) N
                  ≐ᶜ C-rename (cong-∷-ren (unbox-ren q')) N₃
            shift =
              ≐ᶜ-trans
                (C-rename-≐
                  (≐ʳ-trans (cong-∷-ren-≐ finalEq)
                            (cong-∷-ren-∘-≐ (unbox-ren q') (W₁ ∘ʳ srs))) N)
                (≐ᶜ-trans
                  (C-rename-∘ (cong-∷-ren (unbox-ren q'))
                              (cong-∷-ren (W₁ ∘ʳ srs)) N)
                  (C-rename-cong (cong-∷-ren (unbox-ren q')) (≐ᶜ-sym eN₃)))
