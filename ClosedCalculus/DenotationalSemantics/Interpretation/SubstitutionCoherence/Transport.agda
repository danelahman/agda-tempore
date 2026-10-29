------------------------------------------------------------------------
-- Context-equality transports, and clause retyping.
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import ClosedCalculus.DenotationalSemantics.Model.Category
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Future
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Past
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import ClosedCalculus.DenotationalSemantics.Model.GroundTypes
open import ClosedCalculus.DenotationalSemantics.Model.GroundEternal
open import ClosedCalculus.DenotationalSemantics.Model.Monad
module ClosedCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Transport
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where
open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import ClosedCalculus.Syntax.Types           S
open import ClosedCalculus.Syntax.Contexts        S
open import ClosedCalculus.Syntax.Terms           S
open import ClosedCalculus.Syntax.Renaming        S
open import ClosedCalculus.Syntax.Renaming.Action S
open import ClosedCalculus.Syntax.Substitution    S

open Category Cat
open Future Fut
open Past Pst
open Adjunction Adj
open GroundTypes GTy
open GroundEternal GE
open Monad Mon

open import ClosedCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Base S Cat Fut Pst Adj GTy Mon GE

-- Interpreting a context-equality transport of a computation: the transport
-- becomes the corresponding equality renaming (both are the identity when the
-- equality is `refl`). Used to strip the `subst`s that retyping a clause
-- family's ambient context inserts.

-- Retyping a clause along a context equality preserves parametricity.

substᴾᶜ : ∀ {Δ Δ' D C} → (e : Δ ≡ Δ') → (t : Δ ++ᶜ D ⊢C⦂ C)
        → Paramᶜ t → Paramᶜ (subst (λ Γ₀ → Γ₀ ++ᶜ D ⊢C⦂ C) e t)
substᴾᶜ refl t p = p

substᴾᶜ′ : ∀ {Δ Δ' C} → {e : Δ ≡ Δ'} → (t : Δ ⊢C⦂ C)
         → Paramᶜ t → Paramᶜ (subst (_⊢C⦂ C) e t)
substᴾᶜ′ {e = refl} t p = p

substᴾᵛ : ∀ {Δ Δ' A} → {e : Δ ≡ Δ'} → (t : Δ ⊢V⦂ A)
        → Paramᵛ t → Paramᵛ (subst (_⊢V⦂ A) e t)
substᴾᵛ {e = refl} t p = p

subst-ctx-interp : ∀ {Δ Δ' C} → (e : Δ ≡ Δ') → (t : Δ ⊢C⦂ C) → (p : Paramᶜ t)
                 → ⟦ subst (_⊢C⦂ C) e t ⟧ᶜᵗ (substᴾᶜ′ {e = e} t p)
                 ≈ᵐ ⟦ t ⟧ᶜᵗ p ∘ᵐ ⟦ eq-ren e ⟧ʳ
subst-ctx-interp refl t p = ≈ᵐ-sym (∘ᵐ-identityʳ _)

subst-val-interp : ∀ {Δ Δ' A} → (e : Δ ≡ Δ') → (t : Δ ⊢V⦂ A) → (p : Paramᵛ t)
                 → ⟦ subst (_⊢V⦂ A) e t ⟧ᵛᵗ (substᴾᵛ {e = e} t p)
                 ≈ᵐ ⟦ t ⟧ᵛᵗ p ∘ᵐ ⟦ eq-ren e ⟧ʳ
subst-val-interp refl t p = ≈ᵐ-sym (∘ᵐ-identityʳ _)

subst-clause-interp : ∀ {Δ Δ' D C} → (e : Δ ≡ Δ') → (t : Δ ++ᶜ D ⊢C⦂ C)
                    → (p : Paramᶜ t)
                    → ⟦ subst (λ Γ₀ → Γ₀ ++ᶜ D ⊢C⦂ C) e t ⟧ᶜᵗ (substᴾᶜ e t p)
                    ≈ᵐ ⟦ t ⟧ᶜᵗ p ∘ᵐ ⟦ eq-ren (cong (_++ᶜ D) e) ⟧ʳ
subst-clause-interp refl t p = ≈ᵐ-sym (∘ᵐ-identityʳ _)

-- A clause-context retyping is a nested product reindexing, and in particular
-- acts only on the ambient part — it is independent of the residual grade the
-- continuation slot carries.

eq-ren-clause : ∀ {Δ Δ'} → (e : Δ ≡ Δ') → (Γ' : Ctx) → (pt kt : VType)
              → ⟦ eq-ren (cong (_++ᶜ (Γ' ∷ pt ∷ kt)) e) ⟧ʳ
              ≈ᵐ mapˣᵐ (mapˣᵐ ⟦ eq-ren (cong (_++ᶜ Γ') e) ⟧ʳ idᵐ) idᵐ
eq-ren-clause e Γ' pt kt =
  ≈ᵐ-trans (eq-ren-irr (cong (_++ᶜ (Γ' ∷ pt ∷ kt)) e)
                       (cong (_∷ kt) (cong (_∷ pt) (cong (_++ᶜ Γ') e))))
  (≈ᵐ-trans (eq-ren-∷ (cong (_∷ pt) (cong (_++ᶜ Γ') e)))
            (mapˣᵐ-cong (eq-ren-∷ (cong (_++ᶜ Γ') e)) ≈ᵐ-refl))


-- Retyping a clause family's ambient context preserves the clauses' uniformity
-- in the residual grade: the retyping acts on the ambient context only, so it
-- commutes with the continuation's coercion (`mapˣ-swapᵐ`), after which the
-- original uniformity applies.

subst-clauses-uniform :
  ∀ {Δ Δ' B} → (e : Δ ≡ Δ')
  → (H : (op : Op) → (ε'' : E)
       → Δ ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
  → (∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'')
       → ⟦ H op ε₂'' ⟧ᶜᵗ (pH op ε₂'')
           ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
       ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H op ε₁'' ⟧ᶜᵗ (pH op ε₁''))
  → (∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'')
       → ⟦ subst (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₂'')
                          ⊢C⦂ B ‼ (op-grade op ·ₑ ε₂''))
                 e (H op ε₂'') ⟧ᶜᵗ (substᴾᶜ e (H op ε₂'') (pH op ε₂''))
           ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
       ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q)
           ∘ᵐ ⟦ subst (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₁'')
                               ⊢C⦂ B ‼ (op-grade op ·ₑ ε₁''))
                      e (H op ε₁'') ⟧ᶜᵗ (substᴾᶜ e (H op ε₁'') (pH op ε₁'')))
subst-clauses-uniform e H pH uH op q =
  ≈ᵐ-trans (∘ᵐ-congˡ (subst-clause-interp e (H op _) (pH op _)))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ
    (≈ᵐ-trans (∘ᵐ-congˡ (eq-ren-clause e [] _ _))
    (≈ᵐ-trans (mapˣ-swapᵐ _ _)
              (∘ᵐ-congʳ (≈ᵐ-sym (eq-ren-clause e [] _ _))))))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (uH op q))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
            (∘ᵐ-congʳ (≈ᵐ-sym (subst-clause-interp e (H op _) (pH op _)))))))))
