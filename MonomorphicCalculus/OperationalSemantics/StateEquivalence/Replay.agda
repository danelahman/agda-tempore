------------------------------------------------------------------------
-- Replaying an extension across the equivalence.
------------------------------------------------------------------------

open import Data.Product

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Relation.Nullary using (¬_)

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.StateEquivalence.Replay (Spec : LanguageSpec) where
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

open import MonomorphicCalculus.Syntax.Renaming.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Renaming.Coherence    Spec
open import MonomorphicCalculus.Syntax.Terms.Equivalence     Spec
open import MonomorphicCalculus.Syntax.Terms.Transport       Spec
open import MonomorphicCalculus.Syntax.Substitution.Variables  Spec
open import MonomorphicCalculus.OperationalSemantics.GradedReach Spec
open import MonomorphicCalculus.Syntax.Substitution.Equivalence  Spec

open import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Core Spec
open import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Extensions Spec
open import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Bisimulation Spec

-- `VRed`'s Kripke clauses quantify over extensions of the state, so
-- transporting one along `_≐ˢ_` means replaying its extension on the other
-- state: the shape is copied, and each cell's value is transported along the
-- contexts' equality.

castᵛ-castᵛ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (e' : Γ' ≡ Γ) → (V : Γ ⊢ᵛ⦂ A)
            → castᵛ e' (castᵛ e V) ≡ V
castᵛ-castᵛ refl e' V = cong (λ z → castᵛ z V) (uip {p = e'} {q = refl})

castᶜ-castᶜ : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → (e' : Γ' ≡ Γ) → (M : Γ ⊢ᶜ⦂ C)
            → castᶜ e' (castᶜ e M) ≡ M
castᶜ-castᶜ refl e' M = cong (λ z → castᶜ z M) (uip {p = e'} {q = refl})

replay : ∀ {𝕊 𝕊' 𝕊₂ : State []} → (es : 𝕊 ≐ˢ 𝕊') → (q : 𝕊 ≤ₛ 𝕊₂)
       → Σ[ 𝕊₂' ∈ State [] ] Σ[ q' ∈ 𝕊' ≤ₛ 𝕊₂' ] Σ[ es₂ ∈ 𝕊₂ ≐ˢ 𝕊₂' ]
           (q ≤≐ q')

replay {𝕊' = 𝕊'} es ≤ₛ-refl = 𝕊' , ≤ₛ-refl , es , id-≤≐

replay es (≤ₛ-lock {ρ = ρ} q) with replay es q
... | 𝕊₂' , q' , es₂ , h =
  𝕊₂' ⟨ ρ ⟩ₛ , ≤ₛ-lock q' , ⟨⟩-≐ˢ ρ es₂ , ⟨⟩-≤≐ ρ h

replay es (≤ₛ-res {ρ = ρ} {V = V} q) with replay es q
... | 𝕊₂' , q' , es₂ , h =
    𝕊₂' ∷ₛ V'
  , ≤ₛ-res q'
  , ∷-≐ˢ es₂ (subst (λ z → V ≡ z)
                    (sym (castᵛ-castᵛ
                           (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩) (toCtx-≐ˢ es₂))
                           (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩) (sym (toCtx-≐ˢ es₂)))
                           V))
                    (refl {x = V}))
  , ∷-≤≐ h
  where
    V' = castᵛ (cong (λ Γ₀ → [] ++ᶜ Γ₀ ⟨ ρ ⟩) (toCtx-≐ˢ es₂)) V

-- The same at the reach level: the grade bound transports along the shape's
-- grade equality (`κₛ-≤≐`).

reach-replay : ∀ {𝕊 𝕊' 𝕊₂ : State []} {ρ : R}
             → (es : 𝕊 ≐ˢ 𝕊') → (q : 𝕊 ⊑ₛ[ ρ ] 𝕊₂)
             → Σ[ 𝕊₂' ∈ State [] ] Σ[ q' ∈ 𝕊' ⊑ₛ[ ρ ] 𝕊₂' ]
               Σ[ es₂ ∈ 𝕊₂ ≐ˢ 𝕊₂' ]
                 (ext q ≤≐ ext q')
reach-replay es (reach e b) with replay es e
... | 𝕊₂' , e' , es₂ , h =
    𝕊₂' , reach e' (subst (_≾ᵣ _) (κₛ-≤≐ h) b) , es₂ , h

-- What a replayed reach does to an `unbox`: the two consulted renamings agree,
-- up to the two states' context equalities. This is `suc-comp-ren-≐ʳ` with the
-- `⟨⟩-η-ren` that `unbox-ren` puts in front pushed through the cast.

⟨⟩-η-ren-cast : ∀ {Γ Γ'} → (e : Γ' ≡ Γ)
              → ⟨⟩-η-ren {Δ = Γ}
              ≐ʳ castʳ² (cong (_⟨ 𝟏ᵣ ⟩) e) e ⟨⟩-η-ren
⟨⟩-η-ren-cast refl = ≐ʳ-refl

unbox-ren-≐ˢ : ∀ {ρ} {𝕊 𝕊' 𝕊₂ 𝕊₂' : State []}
             → (es : 𝕊 ≐ˢ 𝕊') → (es₂ : 𝕊₂ ≐ˢ 𝕊₂')
             → {q : 𝕊 ⊑ₛ[ ρ ] 𝕊₂} → {q' : 𝕊' ⊑ₛ[ ρ ] 𝕊₂'}
             → ext q ≤≐ ext q'
             -------------------------------------------------------------
             → unbox-ren q
             ≐ʳ castʳ² (cong (_⟨ ρ ⟩) (sym (toCtx-≐ˢ es)))
                       (sym (toCtx-≐ˢ es₂)) (unbox-ren q')

unbox-ren-≐ˢ {ρ} es es₂ {q} {q'} h =
  ≐ʳ-trans
    (∘ʳ-≐ʳ (suc-comp-ren-≐ʳ h es es₂ (reach-bound q) (reach-bound q'))
          (⟨⟩-η-ren-cast (sym (toCtx-≐ˢ es₂))))
    (≐ʳ-sym
      (castʳ²-∘ʳ (sym (toCtx-≐ˢ es₂))
                 (cong (_⟨ 𝟏ᵣ ⟩) (sym (toCtx-≐ˢ es₂)))
                 (cong (_⟨ ρ ⟩) (sym (toCtx-≐ˢ es)))
                 (suc-comp-ren (ext q') (reach-bound q')) ⟨⟩-η-ren))

-- The form the Kripke clauses use. A clause transported along `_≐ˢ_` moves its
-- boxed value to the other state too, so the renaming consulted there is
-- precomposed with that context equality, which cancels against the source
-- cast the bridge introduces.

castʳ²-cancel : ∀ {Γ Γ' Δ Δ' ρ} → (a : Γ ≡ Γ') → (b : Δ ≡ Δ')
              → (r : Ren [] Δ (Γ ⟨ ρ ⟩))
              → (cong-⟨⟩-ren (eq-ren a) ∘ʳ castʳ² (cong (_⟨ ρ ⟩) a) b r)
              ≐ʳ castʳ b r
castʳ²-cancel refl refl r = ∘ʳ-idˡ-≐ʳ r (cong-⟨⟩-ren-id-≐ʳ ≐ʳ-refl)

unbox-ren-bridge : ∀ {ρ} {𝕊 𝕊' 𝕊'' 𝕊₂ : State []}
                 → (es : 𝕊 ≐ˢ 𝕊') → (es₂ : 𝕊'' ≐ˢ 𝕊₂)
                 → {q' : 𝕊' ⊑ₛ[ ρ ] 𝕊''} → {q : 𝕊 ⊑ₛ[ ρ ] 𝕊₂}
                 → ext q' ≤≐ ext q
                 -------------------------------------------------------------
                 → (cong-⟨⟩-ren (eq-ren (toCtx-≐ˢ es)) ∘ʳ unbox-ren q')
                 ≐ʳ castʳ (sym (toCtx-≐ˢ es₂)) (unbox-ren q)

unbox-ren-bridge {ρ} es es₂ {q'} {q} h
  rewrite uip {p = toCtx-≐ˢ es} {q = sym (toCtx-≐ˢ (≐ˢ-sym es))} =
  ≐ʳ-trans
    (∘ʳ-≐ʳ ≐ʳ-refl (unbox-ren-≐ˢ (≐ˢ-sym es) es₂ h))
    (castʳ²-cancel (sym (toCtx-≐ˢ (≐ˢ-sym es))) (sym (toCtx-≐ˢ es₂))
                   (unbox-ren q))

-- The unit-reach analogue: a replayed reach renames the state's own context
-- the same way, up to the two states' context equalities. As `unbox-ren-≐ˢ`,
-- with the two `⟨⟩-η` renamings pushed through the cast.

⟨⟩-η⁻¹-ren-cast : ∀ {Γ Γ'} → (e : Γ' ≡ Γ)
                → ⟨⟩-η⁻¹-ren {Δ = Γ}
                ≐ʳ castʳ² e (cong (_⟨ 𝟏ᵣ ⟩) e) ⟨⟩-η⁻¹-ren
⟨⟩-η⁻¹-ren-cast refl = ≐ʳ-refl

reach-renᵘ-≐ˢ : ∀ {𝕊 𝕊' 𝕊₂ 𝕊₂' : State []}
              → (es : 𝕊 ≐ˢ 𝕊') → (es₂ : 𝕊₂ ≐ˢ 𝕊₂')
              → {q : 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊₂} → {q' : 𝕊' ⊑ₛ[ 𝟏ᵣ ] 𝕊₂'}
              → ext q ≤≐ ext q'
              -------------------------------------------------------------
              → reach-renᵘ q
              ≐ʳ castʳ² (sym (toCtx-≐ˢ es)) (sym (toCtx-≐ˢ es₂)) (reach-renᵘ q')

reach-renᵘ-≐ˢ es es₂ {q} {q'} h =
  ≐ʳ-trans
    (∘ʳ-≐ʳ (⟨⟩-η⁻¹-ren-cast (sym (toCtx-≐ˢ es)))
      (∘ʳ-≐ʳ (suc-comp-ren-≐ʳ h es es₂ (reach-bound q) (reach-bound q'))
            (⟨⟩-η-ren-cast (sym (toCtx-≐ˢ es₂)))))
    (≐ʳ-trans
      (∘ʳ-≐ʳ ≐ʳ-refl
        (≐ʳ-sym
          (castʳ²-∘ʳ (sym (toCtx-≐ˢ es₂))
                     (cong (_⟨ 𝟏ᵣ ⟩) (sym (toCtx-≐ˢ es₂)))
                     (cong (_⟨ 𝟏ᵣ ⟩) (sym (toCtx-≐ˢ es)))
                     (suc-comp-ren (ext q') (reach-bound q')) ⟨⟩-η-ren)))
      (≐ʳ-sym
        (castʳ²-∘ʳ (sym (toCtx-≐ˢ es₂))
                   (cong (_⟨ 𝟏ᵣ ⟩) (sym (toCtx-≐ˢ es)))
                   (sym (toCtx-≐ˢ es))
                   ⟨⟩-η⁻¹-ren
                   (suc-comp-ren (ext q') (reach-bound q') ∘ʳ ⟨⟩-η-ren))))

-- The `≤ₛ`-level counterpart of `unbox-ren-bridge`.

var-img-castʳ : ∀ {Γ Γ' Δ ρ A σ} → (e : Γ' ≡ Γ) → (r : Ren [] Γ' (Δ ⟨ ρ ⟩))
              → (y : A ∈[ σ ] (Δ ⟨ ρ ⟩))
              → var-img (castʳ e r) y ≡ Var-cast e (var-img r y)
var-img-castʳ refl r y = refl

cong-⟨⟩-eq-img : ∀ {Γ Γ' ρ A σ} → (e : Γ ≡ Γ') → (x : A ∈[ σ ] Γ)
               → var-img (cong-⟨⟩-ren {ρ = ρ} (eq-ren e)) (Tl-⟨⟩ x)
               ≡ (σ ·ᵣ ρ , Tl-⟨⟩ (subst (λ Γ₀ → A ∈[ σ ] Γ₀) e x))
cong-⟨⟩-eq-img refl x = refl

≤ₛ-embed-≐ˢ : ∀ {A σ} {𝕊 𝕊' 𝕊'' 𝕊₂ : State []}
            → (es : 𝕊 ≐ˢ 𝕊') → (es₂ : 𝕊'' ≐ˢ 𝕊₂)
            → {e' : 𝕊' ≤ₛ 𝕊''} → {e : 𝕊 ≤ₛ 𝕊₂}
            → (h : e' ≤≐ e)
            → (x : A ∈[ σ ] toCtx 𝕊)
            -------------------------------------------------------------
            → ≤ₛ-embed e' (subst (λ Γ₀ → A ∈[ σ ] Γ₀) (toCtx-≐ˢ es) x)
            ≡ Var-cast (sym (toCtx-≐ˢ es₂)) (≤ₛ-embed e x)

≤ₛ-embed-≐ˢ {σ = σ} es es₂ {e'} {e} h x =
  trans (sym stepL) (trans (at (unbox-ren-bridge es es₂ {q'} {q} h) (Tl-⟨⟩ x))
                           stepR)
  where
    q' = reach e' (≾ᵣ-refl {κₛ e'})
    q  = reach e  (≾ᵣ-reflexive (sym (κₛ-≤≐ h)))

    stepL : var-img (cong-⟨⟩-ren (eq-ren (toCtx-≐ˢ es)) ∘ʳ unbox-ren q')
                    (Tl-⟨⟩ x)
          ≡ ≤ₛ-embed e' (subst (λ Γ₀ → _ ∈[ σ ] Γ₀) (toCtx-≐ˢ es) x)
    stepL =
      trans (cong (var-img′ (unbox-ren q')) (cong-⟨⟩-eq-img (toCtx-≐ˢ es) x))
            (unbox-ren-img q' (subst (λ Γ₀ → _ ∈[ σ ] Γ₀) (toCtx-≐ˢ es) x))

    stepR : var-img (castʳ (sym (toCtx-≐ˢ es₂)) (unbox-ren q)) (Tl-⟨⟩ x)
          ≡ Var-cast (sym (toCtx-≐ˢ es₂)) (≤ₛ-embed e x)
    stepR =
      trans (var-img-castʳ (sym (toCtx-≐ˢ es₂)) (unbox-ren q) (Tl-⟨⟩ x))
            (cong (Var-cast (sym (toCtx-≐ˢ es₂))) (unbox-ren-img q x))
