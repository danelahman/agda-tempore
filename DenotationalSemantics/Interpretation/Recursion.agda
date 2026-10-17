------------------------------------------------------------------------
-- Primitive recursion: the denotation of one unfolding of the step,   --
-- and the recursors' beta laws read at the interpretation, with the   --
-- list eliminator's. Shared by the soundness of the reduction and of  --
-- the equational theory.                                              --
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

module DenotationalSemantics.Interpretation.Recursion
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open LanguageSpec S
open GradeSystemInterface Grades

open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S using (V-rename; C-rename)
open import Syntax.Substitutions S

open Category Cat
open Future Fut using ([_]ᶠ)
open Past Pst using (⟨_⟩ᶠ; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ)
open Adjunction Adj using (η⊣; η⊣-nat)
open Monad Mon

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (⟨⊤⟩-η)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE

private
  infixr 3 _∙_
  _∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙_ = ≈ᵐ-trans

-- One unfolding of a primitive recursion's step denotes the step's body with
-- its context rebuilt from the ambient one: the barred part by `⟨⊤⟩-η`, the
-- predecessor by the value, both under the lock binding the recursive call's
-- result. The renaming and the substitution coherences, composed.

recℕ-stepᴾ : ∀ {Γ B ε} → (V : Γ ⊢V⦂ Nat)
           → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
           → Paramᵛ V → Paramᶜ N → Paramᶜ (recℕ-step V N)
recℕ-stepᴾ V N pV pN =
  subᶜ (C-rename (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren barrier-ren))) N)
       (split-∷ (split-⟨⟩ split-[])) V
       (renᶜ (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren barrier-ren))) N pN) pV

sound-recℕ-step : ∀ {Γ B ε} → (V : Γ ⊢V⦂ Nat)
                → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
                → (pV : Paramᵛ V) → (pN : Paramᶜ N)
                → ⟦ recℕ-step V N ⟧ᶜᵗ (recℕ-stepᴾ V N pV pN)
                ≈ᵐ ⟦ N ⟧ᶜᵗ pN
                     ∘ᵐ mapˣᵐ (⟨ mapᵉ ε ⟩ᶠ (mapˣᵐ ⟨⊤⟩-η idᵐ ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ pV ⟩ᵐ)) idᵐ
sound-recℕ-step V N pV pN =
    C-subst-nat (C-rename r N) (split-∷ (split-⟨⟩ split-[])) V (renᶜ r N pN) pV
  ∙ ∘ᵐ-congˡ (C-rename-nat r N pN)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ ( mapˣᵐ-∘ _ _ _ _
             ∙ mapˣᵐ-cong (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)) (∘ᵐ-identityˡ _))
  where
    r = cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren barrier-ren))

-- RECℕ-ZERO / RECℕ-SUCC: the recursor's beta laws. At a successor the step
-- is the recursive call sequenced with the step's body, which, its context
-- carried under `η⊣` and through the strength, is the unfolding.

sound-RECℕ-ZERO : ∀ {Γ B ε} → (M : Γ ⊢C⦂ B ‼ ε)
                → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
                → (p : ε ·ₑ ε ≾ₑ ε) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                → ⟦ recℕ zero M N p ⟧ᶜᵗ (tt , pM , pN) ≈ᵐ ⟦ M ⟧ᶜᵗ pM
sound-RECℕ-ZERO M N p pM pN = recℕᵐ-zero _ _

sound-RECℕ-SUCC : ∀ {Γ B ε} → (V : Γ ⊢V⦂ Nat) → (M : Γ ⊢C⦂ B ‼ ε)
                → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
                → (p : ε ·ₑ ε ≾ₑ ε)
                → (pV : Paramᵛ V) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                → ⟦ recℕ (succ V) M N p ⟧ᶜᵗ (pV , pM , pN)
                ≈ᵐ ⟦ coerce p (recℕ V M N p ⨟ recℕ-step V N) ⟧ᶜᵗ
                     ((pV , pM , pN) , recℕ-stepᴾ V N pV pN)
sound-RECℕ-SUCC {B = B} V M N p pV pM pN =
  -- the recursor's successor law, at the scrutinee
    ∘ᵐ-congʳ (⟨⟩ᵐ-mapˣᵐ succᵐ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (recℕᵐ-succ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)
  -- the step at that context is the sequencing with the unfolding
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ ctx)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
        ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (strᵀ-natˡ _))
                  ∙ ∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)
                  ∙ T-congᶠ (≈ᵐ-sym (sound-recℕ-step V N pV pN)))))
  -- the coercion is the sub-effecting alone
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-congˡ (T-congᶠ (⟦⟧<:ᵛ-refl B) ∙ T-idᵐ) ∙ ∘ᵐ-identityˡ _))
  where
    ctx : mapˣᵐ (η⊣ ∘ᵐ mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ
            ∘ᵐ ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ pV ⟩ᵐ , ⟦ recℕ V M N p ⟧ᶜᵗ (pV , pM , pN) ⟩ᵐ
        ≈ᵐ mapˣᵐ ([ _ ]ᶠ (⟨ _ ⟩ᶠ (mapˣᵐ ⟨⊤⟩-η idᵐ ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ pV ⟩ᵐ))) idᵐ
            ∘ᵐ ⟨ η⊣ , ⟦ recℕ V M N p ⟧ᶜᵗ (pV , pM , pN) ⟩ᵐ
    ctx =
        mapˣᵐ-∘⟨⟩ _ _ _ _
      ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ ≈ᵐ-sym (η⊣-nat _) , ≈ᵐ-refl ⟩ᵐ-cong
      ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _)

-- One unfolding of a list recursion's step, likewise: the barred part by
-- `⟨⊤⟩-η`, the head and the tail by the values, under the lock.

recL-stepᴾ : ∀ {Γ A B ε} → (V : Γ ⊢V⦂ A) → (W : Γ ⊢V⦂ |List| A)
           → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
           → Paramᵛ V → Paramᵛ W → Paramᶜ N → Paramᶜ (recL-step V W N)
recL-stepᴾ V W N pV pW pN =
  subᶜ (C-rename r N [ split-∷ (split-⟨⟩ (split-∷ split-[])) ↦ V ]c)
       (split-∷ (split-⟨⟩ split-[])) W
       (subᶜ (C-rename r N) (split-∷ (split-⟨⟩ (split-∷ split-[]))) V (renᶜ r N pN) pV)
       pW
  where
    r = cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren (cong-∷-ren barrier-ren)))

sound-recL-step : ∀ {Γ A B ε} → (V : Γ ⊢V⦂ A) → (W : Γ ⊢V⦂ |List| A)
                → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
                → (pV : Paramᵛ V) → (pW : Paramᵛ W) → (pN : Paramᶜ N)
                → ⟦ recL-step V W N ⟧ᶜᵗ (recL-stepᴾ V W N pV pW pN)
                ≈ᵐ ⟦ N ⟧ᶜᵗ pN
                     ∘ᵐ mapˣᵐ (⟨ mapᵉ ε ⟩ᶠ (mapˣᵐ (mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ
                                            ∘ᵐ ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ pV ⟩ᵐ , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ))
                              idᵐ
sound-recL-step V W N pV pW pN =
    C-subst-nat (C-rename r N [ s₁ ↦ V ]c) s₂ W
                (subᶜ (C-rename r N) s₁ V (renᶜ r N pN) pV) pW
  ∙ ∘ᵐ-congˡ (C-subst-nat (C-rename r N) s₁ V (renᶜ r N pN) pV)
  ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ (C-rename-nat r N pN))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ ( ∘ᵐ-congʳ ( mapˣᵐ-∘ _ _ _ _
                         ∙ mapˣᵐ-cong (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)) (∘ᵐ-identityˡ _))
             ∙ mapˣᵐ-∘ _ _ _ _
             ∙ mapˣᵐ-cong (≈ᵐ-sym (⟨⟩-∘ᵐ _ _) ∙ ⟨⟩-congᶠ inner) (∘ᵐ-identityˡ _))
  where
    r  = cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren (cong-∷-ren barrier-ren)))
    s₁ = split-∷ (split-⟨⟩ (split-∷ split-[]))
    s₂ = split-∷ (split-⟨⟩ split-[])

    inner : mapˣᵐ (mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ ∘ᵐ (mapˣᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ pV ⟩ᵐ idᵐ
              ∘ᵐ ⟨ idᵐ , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ)
          ≈ᵐ mapˣᵐ (mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ
              ∘ᵐ ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ pV ⟩ᵐ , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ
    inner = ∘ᵐ-congʳ ( mapˣᵐ-∘⟨⟩ _ _ _ _
                     ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)

-- The list recursor's beta laws, at `nil` and at a `cons`.

sound-RECL-NIL : ∀ {Γ A B ε} → (M : Γ ⊢C⦂ B ‼ ε)
               → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
               → (p : ε ·ₑ ε ≾ₑ ε) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
               → ⟦ recL nil M N p ⟧ᶜᵗ (tt , pM , pN) ≈ᵐ ⟦ M ⟧ᶜᵗ pM
sound-RECL-NIL M N p pM pN = recLᵐ-nil _ _

sound-RECL-CONS : ∀ {Γ A B ε} → (V : Γ ⊢V⦂ A) → (W : Γ ⊢V⦂ |List| A)
                → (M : Γ ⊢C⦂ B ‼ ε)
                → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
                → (p : ε ·ₑ ε ≾ₑ ε)
                → (pV : Paramᵛ V) → (pW : Paramᵛ W) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                → ⟦ recL (cons V W) M N p ⟧ᶜᵗ ((pV , pW) , pM , pN)
                ≈ᵐ ⟦ coerce p (recL W M N p ⨟ recL-step V W N) ⟧ᶜᵗ
                     ((pW , pM , pN) , recL-stepᴾ V W N pV pW pN)
sound-RECL-CONS {B = B} V W M N p pV pW pM pN =
  -- the recursor's cons law, at the scrutinee
    ∘ᵐ-congʳ (⟨⟩ᵐ-mapˣᵐ consᵐ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (recLᵐ-cons _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ ( ⟨⟩ᵐ-∘ _ _ _
             ∙ ⟨ ×ᵐ-assoc⁻¹-⟨⟩ _ _ _
               , ∘ᵐ-assoc _ _ _
                 ∙ ∘ᵐ-congʳ ( mapˣᵐ-∘⟨⟩ _ _ _ _
                            ∙ ⟨ ∘ᵐ-identityˡ _ , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong) ⟩ᵐ-cong)
  -- the step at that context is the sequencing with the unfolding
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ ctx)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
        ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (strᵀ-natˡ _))
                  ∙ ∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)
                  ∙ T-congᶠ (≈ᵐ-sym (sound-recL-step V W N pV pW pN)))))
  -- the coercion is the sub-effecting alone
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-congˡ (T-congᶠ (⟦⟧<:ᵛ-refl B) ∙ T-idᵐ) ∙ ∘ᵐ-identityˡ _))
  where
    c = ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ pV ⟩ᵐ , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ
    rec = ⟦ recL W M N p ⟧ᶜᵗ (pW , pM , pN)

    ctx : mapˣᵐ (η⊣ ∘ᵐ mapˣᵐ (mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ) idᵐ ∘ᵐ ⟨ c , rec ⟩ᵐ
        ≈ᵐ mapˣᵐ ([ _ ]ᶠ (⟨ _ ⟩ᶠ (mapˣᵐ (mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ ∘ᵐ c))) idᵐ
            ∘ᵐ ⟨ η⊣ , rec ⟩ᵐ
    ctx =
        mapˣᵐ-∘⟨⟩ _ _ _ _
      ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ ≈ᵐ-sym (η⊣-nat _) , ≈ᵐ-refl ⟩ᵐ-cong
      ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _)

-- The list eliminator's beta laws: at `nil` the `nil` branch, at a `cons`
-- the `cons` branch with the head and the tail substituted, as for `match`.

sound-CASEL-NIL : ∀ {Γ A C} → (M : Γ ⊢C⦂ C) → (N : Γ ∷ A ∷ |List| A ⊢C⦂ C)
                → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                → ⟦ caseL nil `nil M `cons N ⟧ᶜᵗ (tt , pM , pN) ≈ᵐ ⟦ M ⟧ᶜᵗ pM
sound-CASEL-NIL M N pM pN = caseLᵐ-nil _ _

sound-CASEL-CONS : ∀ {Γ A C} → (V : Γ ⊢V⦂ A) → (W : Γ ⊢V⦂ |List| A)
                 → (M : Γ ⊢C⦂ C) → (N : Γ ∷ A ∷ |List| A ⊢C⦂ C)
                 → (pV : Paramᵛ V) → (pW : Paramᵛ W) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                 → ⟦ caseL cons V W `nil M `cons N ⟧ᶜᵗ ((pV , pW) , pM , pN)
                 ≈ᵐ ⟦ (N [ split-[] ↦ V-rename wk-ren W ]c) [ split-[] ↦ V ]c ⟧ᶜᵗ
                      (subᶜ (N [ split-[] ↦ V-rename wk-ren W ]c) split-[] V
                         (subᶜ N split-[] (V-rename wk-ren W) pN (renᵛ wk-ren W pW)) pV)
sound-CASEL-CONS V W M N pV pW pM pN =
    caseLᵐ-cons _ _ _ _
  ∙ ≈ᵐ-sym (  C-subst-nat (N [ split-[] ↦ V-rename wk-ren W ]c) split-[] V
                (subᶜ N split-[] (V-rename wk-ren W) pN (renᵛ wk-ren W pW)) pV
            ∙ ∘ᵐ-congˡ (  C-subst-nat N split-[] (V-rename wk-ren W) pN (renᵛ wk-ren W pW)
                        ∙ ∘ᵐ-congʳ ⟨ ≈ᵐ-refl , V-rename-nat wk-ren W pW ⟩ᵐ-cong)
            ∙ ∘ᵐ-assoc _ _ _
            ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                        ∙ ⟨ ∘ᵐ-identityˡ _
                          , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                            ∙ ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
