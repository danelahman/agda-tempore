------------------------------------------------------------------------
-- Infrastructure for the denotational soundness of the equational      --
-- theory.                                                             --
--                                                                    --
-- The interpretation is indexed by a parametricity certificate         --
-- (`Paramᵛ`/`Paramᶜ`), which the equational theory knows nothing about. --
-- The interpretation does not depend on the certificate                 --
-- (`⟦⟧ᵛᵗ-irr`/`⟦⟧ᶜᵗ-irr`), so soundness is stated for arbitrary          --
-- certificates on the two sides.                                        --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module EquationalTheory.Soundness.Base
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

open import Syntax.Types      S
open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.Renamings  S

open import EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-∘ᵐ; []-congᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-≤)
open Adjunction Adj using (η⊣; ε⊣)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE

infixr 3 _∙_

_∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
_∙_ = ≈ᵐ-trans


-- CERTIFICATE IRRELEVANCE
--
-- The interpretation does not depend on the parametricity certificate: the
-- certificate's only computational use is the clause family of a handler,
-- and the fold is a congruence in its handler (`T-alg-of-handlerᵀ-cong`),
-- which in particular ignores the handler's `Monoᵀ` component.

mutual

  {-# TERMINATING #-}

  ⟦⟧ᵛᵗ-irr : ∀ {Γ A} → (V : Γ ⊢V⦂ A) → (p p' : Paramᵛ V)
           → ⟦ V ⟧ᵛᵗ p ≈ᵐ ⟦ V ⟧ᵛᵗ p'
  ⟦⟧ᵛᵗ-irr (var f x)  _ _ = ≈ᵐ-refl
  ⟦⟧ᵛᵗ-irr (const c)  _ _ = ≈ᵐ-refl
  ⟦⟧ᵛᵗ-irr ⋆          _ _ = ≈ᵐ-refl
  ⟦⟧ᵛᵗ-irr true       _ _ = ≈ᵐ-refl
  ⟦⟧ᵛᵗ-irr false      _ _ = ≈ᵐ-refl
  ⟦⟧ᵛᵗ-irr ⦉ V , W ⦊ (pV , pW) (pV' , pW') =
    ⟨ ⟦⟧ᵛᵗ-irr V pV pV' , ⟦⟧ᵛᵗ-irr W pW pW' ⟩ᵐ-cong
  ⟦⟧ᵛᵗ-irr (lam M)   pM pM' = curryᵐ-cong (⟦⟧ᶜᵗ-irr M pM pM')

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
  ⟦⟧ᶜᵗ-irr (if V `then M `else N) (pV , pM , pN) (pV' , pM' , pN') =
    ifᵐ-cong (⟦⟧ᵛᵗ-irr V pV pV') (⟦⟧ᶜᵗ-irr M pM pM') (⟦⟧ᶜᵗ-irr N pN pN')
  ⟦⟧ᶜᵗ-irr (perform op V M) (pV , pM) (pV' , pM') =
    ∘ᵐ-congʳ (⟨ substᶜ-≈ (ty-gty (param op)) (⟦⟧ᵛᵗ-irr V pV pV')
              , ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                  (substᵈ-≈ (ty-gty (arity op)) (⟦⟧ᶜᵗ-irr M pM pM')))) ⟩ᵐ-cong)
  ⟦⟧ᶜᵗ-irr (delay τ M) pM pM' =
    ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (⟦⟧ᶜᵗ-irr M pM pM')))
  ⟦⟧ᶜᵗ-irr (handle M `with H `in N)
           (pM , pN , pH , uH) (pM' , pN' , pH' , uH') =
    ∘ᵐ-cong (T-alg-of-handlerᵀ-cong _
              (λ op ε'' → ∘ᵐ-congˡ
                            (⟦⟧ᶜᵗ-irr (H op ε'') (pH op ε'') (pH' op ε''))))
            (⟨ ≈ᵐ-refl
             , ∘ᵐ-cong (T-congᶠ (⟦⟧ᶜᵗ-irr N pN pN'))
                       (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ⟦⟧ᶜᵗ-irr M pM pM' ⟩ᵐ-cong)) ⟩ᵐ-cong)
  ⟦⟧ᶜᵗ-irr (unbox x rel M) pM pM' = ∘ᵐ-congˡ (⟦⟧ᶜᵗ-irr M pM pM')
  ⟦⟧ᶜᵗ-irr (box V M) (pV , pM) (pV' , pM') =
    ∘ᵐ-cong (⟦⟧ᶜᵗ-irr M pM pM')
            (⟨ ≈ᵐ-refl , ∘ᵐ-congˡ ([]-congᶠ (⟦⟧ᵛᵗ-irr V pV pV')) ⟩ᵐ-cong)
  ⟦⟧ᶜᵗ-irr (coerce p M) pM pM' = ∘ᵐ-congʳ (⟦⟧ᶜᵗ-irr M pM pM')


-- THE SOUNDNESS STATEMENT, PER EQUATION
--
-- `Soundᵛ== p` / `Soundᶜ== p` is "the equation `p` is denotationally valid":
-- its two sides denote the same morphism, for *any* certificates. Naming it
-- lets each axiom of the theory be discharged by a lemma whose statement
-- mentions only the axiom's own arguments, rather than a spelled-out copy of
-- its right-hand side.

Soundᵛ== : ∀ {Γ A} {V W : Γ ⊢V⦂ A} → Γ ⊢V⦂ V == W → Set
Soundᵛ== {V = V} {W = W} _ =
  (pV : Paramᵛ V) → (pW : Paramᵛ W) → ⟦ V ⟧ᵛᵗ pV ≈ᵐ ⟦ W ⟧ᵛᵗ pW

Soundᶜ== : ∀ {Γ C} {M N : Γ ⊢C⦂ C} → Γ ⊢C⦂ M == N → Set
Soundᶜ== {M = M} {N = N} _ =
  (pM : Paramᶜ M) → (pN : Paramᶜ N) → ⟦ M ⟧ᶜᵗ pM ≈ᵐ ⟦ N ⟧ᶜᵗ pN
