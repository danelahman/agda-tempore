---------------------------------------------------------------------------
-- Infrastructure for the denotational soundness of the equational       --
-- theory.                                                               --
--                                                                       --
-- The interpretation is indexed by a parametricity certificate          --
-- (`Paramᵛ`/`Paramᶜ`), which the equational theory knows nothing about. --
-- The interpretation does not depend on the certificate                 --
-- (`⟦⟧ᵛᵗ-irr`/`⟦⟧ᶜᵗ-irr`), so soundness is stated for arbitrary         --
-- certificates on the two sides.                                        --
---------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundEternal
open import MonomorphicCalculus.DenotationalSemantics.Model.Monad

module MonomorphicCalculus.EquationalTheory.Soundness.Base
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

open import MonomorphicCalculus.Syntax.Types     S
open import MonomorphicCalculus.Syntax.Contexts  S
open import MonomorphicCalculus.Syntax.Terms     S
open import MonomorphicCalculus.Syntax.Renaming  S

open import MonomorphicCalculus.EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-∘ᵐ; []-congᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-≤)
open Adjunction Adj using (η⊣; ε⊣)
open GroundTypes GTy
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE

open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (⟨⊤⟩-eternalᵒ)

infixr 3 _∙_

_∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
_∙_ = ≈ᵐ-trans


-- A handler literal's denotation is a congruence in its return clause and
-- clauses, whatever their certificates.

handler-≈ : ∀ {Γ A B ε ε'}
          → {N N' : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ‼ ε'}
          → {H H' : (op : Op) → (ε'' : E)
                  → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                       ∷ [ ∣ op-grade op ∣ᵉ ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                    ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
          → (pN : Paramᶜ N) → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
          → (uH : EffUniformʰ {Γ} {B} H pH)
          → (pN' : Paramᶜ N') → (pH' : ∀ op ε'' → Paramᶜ (H' op ε''))
          → (uH' : EffUniformʰ {Γ} {B} H' pH')
          → ⟦ N ⟧ᶜᵗ pN ≈ᵐ ⟦ N' ⟧ᶜᵗ pN'
          → (∀ op ε'' → ⟦ H op ε'' ⟧ᶜᵗ (pH op ε'') ≈ᵐ ⟦ H' op ε'' ⟧ᶜᵗ (pH' op ε''))
          → ⟦ handler N H ⟧ᵛᵗ (pN , pH , uH) ≈ᵐ ⟦ handler N' H' ⟧ᵛᵗ (pN' , pH' , uH')
handler-≈ {Γ} {N = N} {N'} {H} {H'} pN pH uH pN' pH' uH' eN eH =
  curryʰ-cong (handler-famᵗ-nat h n) (handler-famᵗ-nat h' n') λ p →
    ∘ᵐ-cong (T-alg-of-handlerᵀ-cong (⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ) {h} {h'}
               (λ op ε'' → ∘ᵐ-congˡ (eH op ε'')))
            ⟨ ≈ᵐ-refl , ∘ᵐ-congˡ (T-congᶠ (∘ᵐ-congˡ eN)) ⟩ᵐ-cong
  where
    h  = ⟦_⟧ʰᵗ {Γ} H pH uH
    h' = ⟦_⟧ʰᵗ {Γ} H' pH' uH'
    n  = ⟦ N ⟧ᶜᵗ pN
    n' = ⟦ N' ⟧ᶜᵗ pN'

-- Only the handler clause family uses the certificate; the fold is a congruence in it.

mutual

  ⟦⟧ᵛᵗ-irr : ∀ {Γ A} → (V : Γ ⊢V⦂ A) → (p p' : Paramᵛ V)
           → ⟦ V ⟧ᵛᵗ p ≈ᵐ ⟦ V ⟧ᵛᵗ p'
  ⟦⟧ᵛᵗ-irr (var f x)  _ _ = ≈ᵐ-refl
  ⟦⟧ᵛᵗ-irr (const c)  _ _ = ≈ᵐ-refl
  ⟦⟧ᵛᵗ-irr ⋆          _ _ = ≈ᵐ-refl
  ⟦⟧ᵛᵗ-irr true       _ _ = ≈ᵐ-refl
  ⟦⟧ᵛᵗ-irr false      _ _ = ≈ᵐ-refl
  ⟦⟧ᵛᵗ-irr ⦉ V , W ⦊ (pV , pW) (pV' , pW') =
    ⟨ ⟦⟧ᵛᵗ-irr V pV pV' , ⟦⟧ᵛᵗ-irr W pW pW' ⟩ᵐ-cong
  ⟦⟧ᵛᵗ-irr zero      _ _ = ≈ᵐ-refl
  ⟦⟧ᵛᵗ-irr (succ V)  pV pV' = ∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr V pV pV')
  ⟦⟧ᵛᵗ-irr (inl V)   pV pV' = ∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr V pV pV')
  ⟦⟧ᵛᵗ-irr (inr V)   pV pV' = ∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr V pV pV')
  ⟦⟧ᵛᵗ-irr nil       _ _ = ≈ᵐ-refl
  ⟦⟧ᵛᵗ-irr (cons V W) (pV , pW) (pV' , pW') =
    ∘ᵐ-congʳ ⟨ ⟦⟧ᵛᵗ-irr V pV pV' , ⟦⟧ᵛᵗ-irr W pW pW' ⟩ᵐ-cong
  ⟦⟧ᵛᵗ-irr (lam M)   pM pM' = curryᵐ-cong (⟦⟧ᶜᵗ-irr M pM pM')
  ⟦⟧ᵛᵗ-irr (handler N H) (pN , pH , uH) (pN' , pH' , uH') =
    handler-≈ {N = N} {N} {H} {H} pN pH uH pN' pH' uH' (⟦⟧ᶜᵗ-irr N pN pN')
      (λ op ε'' → ⟦⟧ᶜᵗ-irr (H op ε'') (pH op ε'') (pH' op ε''))
  ⟦⟧ᵛᵗ-irr (subV V w) pV pV' = ∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr V pV pV')

  ⟦⟧ᶜᵗ-irr : ∀ {Γ C} → (M : Γ ⊢C⦂ C) → (p p' : Paramᶜ M)
           → ⟦ M ⟧ᶜᵗ p ≈ᵐ ⟦ M ⟧ᶜᵗ p'
  ⟦⟧ᶜᵗ-irr (return V) pV pV' = ∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr V pV pV')
  ⟦⟧ᶜᵗ-irr (M ⨟ N) (pM , pN) (pM' , pN') =
    ∘ᵐ-congʳ (∘ᵐ-cong (T-congᶠ (⟦⟧ᶜᵗ-irr N pN pN'))
                      (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ⟦⟧ᶜᵗ-irr M pM pM' ⟩ᵐ-cong)))
  ⟦⟧ᶜᵗ-irr (V · W) (pV , pW) (pV' , pW') =
    ∘ᵐ-congʳ (⟨ ⟦⟧ᵛᵗ-irr V pV pV' , ⟦⟧ᵛᵗ-irr W pW pW' ⟩ᵐ-cong)
  ⟦⟧ᶜᵗ-irr (match V `in M) (pV , pM) (pV' , pM') =
    ∘ᵐ-cong (⟦⟧ᶜᵗ-irr M pM pM')
            (⟨ ⟨ ≈ᵐ-refl , ∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr V pV pV') ⟩ᵐ-cong
             , ∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr V pV pV') ⟩ᵐ-cong)
  ⟦⟧ᶜᵗ-irr (absurd V) pV pV' = ∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr V pV pV')
  ⟦⟧ᶜᵗ-irr (cmp ⋈ V W et) (pV , pW) (pV' , pW') =
    ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ⟦⟧ᵛᵗ-irr V pV pV' , ⟦⟧ᵛᵗ-irr W pW pW' ⟩ᵐ-cong)))
  ⟦⟧ᶜᵗ-irr (if V `then M `else N) (pV , pM , pN) (pV' , pM' , pN') =
    ifᵐ-cong (⟦⟧ᵛᵗ-irr V pV pV') (⟦⟧ᶜᵗ-irr M pM pM') (⟦⟧ᶜᵗ-irr N pN pN')
  ⟦⟧ᶜᵗ-irr (caseℕ V `zero M `succ N) (pV , pM , pN) (pV' , pM' , pN') =
    caseℕᵐ-cong (⟦⟧ᵛᵗ-irr V pV pV') (⟦⟧ᶜᵗ-irr M pM pM') (⟦⟧ᶜᵗ-irr N pN pN')
  ⟦⟧ᶜᵗ-irr (recℕ V M N p) (pV , pM , pN) (pV' , pM' , pN') =
    ∘ᵐ-cong (recℕᵐ-cong (⟦⟧ᶜᵗ-irr M pM pM')
                        (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (⟦⟧ᶜᵗ-irr N pN pN'))))))
            ⟨ ≈ᵐ-refl , ⟦⟧ᵛᵗ-irr V pV pV' ⟩ᵐ-cong
  ⟦⟧ᶜᵗ-irr (caseL V `nil M `cons N) (pV , pM , pN) (pV' , pM' , pN') =
    caseLᵐ-cong (⟦⟧ᵛᵗ-irr V pV pV') (⟦⟧ᶜᵗ-irr M pM pM') (⟦⟧ᶜᵗ-irr N pN pN')
  ⟦⟧ᶜᵗ-irr (recL V M N p) (pV , pM , pN) (pV' , pM' , pN') =
    ∘ᵐ-cong (recLᵐ-cong (⟦⟧ᶜᵗ-irr M pM pM')
                        (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (⟦⟧ᶜᵗ-irr N pN pN'))))))
            ⟨ ≈ᵐ-refl , ⟦⟧ᵛᵗ-irr V pV pV' ⟩ᵐ-cong
  ⟦⟧ᶜᵗ-irr (case+ V `inl M `inr N) (pV , pM , pN) (pV' , pM' , pN') =
    caseᵐ-cong (⟦⟧ᵛᵗ-irr V pV pV') (⟦⟧ᶜᵗ-irr M pM pM') (⟦⟧ᶜᵗ-irr N pN pN')
  ⟦⟧ᶜᵗ-irr (perform op V M) (pV , pM) (pV' , pM') =
    ∘ᵐ-congʳ (⟨ substᶜ-≈ (ty-gty (param op)) (⟦⟧ᵛᵗ-irr V pV pV')
              , ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                  (substᵈ-≈ (ty-gty (arity op)) (⟦⟧ᶜᵗ-irr M pM pM')))) ⟩ᵐ-cong)
  ⟦⟧ᶜᵗ-irr (delay τ M) pM pM' =
    ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (⟦⟧ᶜᵗ-irr M pM pM')))
  ⟦⟧ᶜᵗ-irr (handle M `with V) (pM , pV) (pM' , pV') =
    ∘ᵐ-congʳ ⟨ ⟦⟧ᵛᵗ-irr V pV pV' , ⟦⟧ᶜᵗ-irr M pM pM' ⟩ᵐ-cong
  ⟦⟧ᶜᵗ-irr (unbox x rel w M) pM pM' = ∘ᵐ-congˡ (⟦⟧ᶜᵗ-irr M pM pM')
  ⟦⟧ᶜᵗ-irr (box _ V M) (pV , pM) (pV' , pM') =
    ∘ᵐ-cong (⟦⟧ᶜᵗ-irr M pM pM')
            (⟨ ≈ᵐ-refl , ∘ᵐ-congˡ ([]-congᶠ (⟦⟧ᵛᵗ-irr V pV pV')) ⟩ᵐ-cong)
  ⟦⟧ᶜᵗ-irr (subC M w) pM pM' = ∘ᵐ-congʳ (⟦⟧ᶜᵗ-irr M pM pM')


Soundᵛ== : ∀ {Γ A} {V W : Γ ⊢V⦂ A} → Γ ⊢V⦂ V == W → Set
Soundᵛ== {V = V} {W = W} _ =
  (pV : Paramᵛ V) → (pW : Paramᵛ W) → ⟦ V ⟧ᵛᵗ pV ≈ᵐ ⟦ W ⟧ᵛᵗ pW

Soundᶜ== : ∀ {Γ C} {M N : Γ ⊢C⦂ C} → Γ ⊢C⦂ M == N → Set
Soundᶜ== {M = M} {N = N} _ =
  (pM : Paramᶜ M) → (pN : Paramᶜ N) → ⟦ M ⟧ᶜᵗ pM ≈ᵐ ⟦ N ⟧ᶜᵗ pN
