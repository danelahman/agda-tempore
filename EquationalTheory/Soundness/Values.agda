------------------------------------------------------------------------
-- Soundness of the beta/eta equations of the pure fragment.            --
-- These are the cartesian closed structure: `unit-eta` is the terminal --
-- object's uniqueness, `fun-beta`/`fun-eta` the exponential's,         --
-- `match-beta`/`match-eta` the product's, `absurd-eta` the initial     --
-- object's strictness, and the boolean equations are the boolean       --
-- object's own laws.                                                   --
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

module EquationalTheory.Soundness.Values
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; yes; no)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S using (V-rename; C-rename)
open import Syntax.Substitutions S

open import EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; ⟨⟩-≤; ⟨⟩-≤-refl; ⟨⟩-εᵘ∘η≡id; εᵘ)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE

-- (`var-morphism-Hd` lives in `Interpretation.Variables`,
--  `exch-ren-mor` in `Interpretation.Renaming`.)

sound-unit-eta : ∀ {Γ} → (V : Γ ⊢V⦂ Unit) → Soundᵛ== (unit-eta V)
sound-unit-eta V pV _ = terminalᵐ-unique

sound-fun-eta : ∀ {Γ A C} → (V : Γ ⊢V⦂ A ⇒ C) → Soundᵛ== (fun-eta V)
sound-fun-eta {Γ} {A} V pV (p₁ , _) =
    ≈ᵐ-sym (uncurryᵐ-curryᵐ-iso (⟦ V ⟧ᵛᵗ pV))
  ∙ curryᵐ-cong (  ≈ᵐ-sym (uncurryᵐ-cong (∘ᵐ-identityˡ (⟦ V ⟧ᵛᵗ pV)))
                 ∙ uncurryᵐ-nat (⟦ V ⟧ᵛᵗ pV) idᵐ
                 ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
                 ∙ ∘ᵐ-congʳ (≈ᵐ-sym
                     (⟨ ⟦⟧ᵛᵗ-irr (V-rename wk-ren V) p₁ (renᵛ wk-ren V pV)
                        ∙ V-rename-nat wk-ren V pV
                      , var-morphism-Hd {Γ} {A} (λ _ → ≾ᵣ-refl) ⟩ᵐ-cong)))

sound-fun-beta : ∀ {Γ A C} → (M : Γ ∷ A ⊢C⦂ C) → (W : Γ ⊢V⦂ A)
               → Soundᶜ== (fun-beta M W)
sound-fun-beta M W (pM , pW) pR =
    βᵐ (⟦ M ⟧ᶜᵗ pM) (⟦ W ⟧ᵛᵗ pW)
  ∙ ≈ᵐ-sym (C-subst-nat M split-[] W pM pW)
  ∙ ⟦⟧ᶜᵗ-irr (M [ split-[] ↦ W ]c) (subᶜ M split-[] W pM pW) pR

sound-absurd-eta : ∀ {Γ C} → (V : Γ ⊢V⦂ Empty) → (M : Γ ∷ Empty ⊢C⦂ C)
                 → Soundᶜ== (absurd-eta V M)
sound-absurd-eta V M pV pR = 𝟘ᵐ-strict (⟦ V ⟧ᵛᵗ pV) _ _

-- The two boolean betas are the boolean object's own beta laws, read at the
-- interpretation `⟦ true ⟧ᵛᵗ = trueᵐ ∘ᵐ terminalᵐ` of the scrutinee.

sound-if-beta-true : ∀ {Γ C} → (M N : Γ ⊢C⦂ C) → Soundᶜ== (if-beta-true M N)
sound-if-beta-true M N (_ , pM , pN) pM' =
    ifᵐ-true (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  ∙ ⟦⟧ᶜᵗ-irr M pM pM'

sound-if-beta-false : ∀ {Γ C} → (M N : Γ ⊢C⦂ C) → Soundᶜ== (if-beta-false M N)
sound-if-beta-false M N (_ , pM , pN) pN' =
    ifᵐ-false (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  ∙ ⟦⟧ᶜᵗ-irr N pN pN'

-- `if-eta`: the two branches substitute the two booleans into the same body,
-- and `sub-env split-[] true` is `⟨ idᵐ , trueᵐ ∘ᵐ terminalᵐ ⟩ᵐ` — exactly the
-- shape `ifᵐ-η` speaks about. As with `match-eta`, `M` occurs only under a
-- substitution on both sides, so its certificate comes in separately.

sound-if-eta : ∀ {Γ C} → (V : Γ ⊢V⦂ Bool) → (M : Γ ∷ Bool ⊢C⦂ C)
             → Paramᶜ M → Soundᶜ== (if-eta V M)
sound-if-eta V M pM (pV , pT , pF) pR =
    ifᵐ-cong ≈ᵐ-refl
      (  ⟦⟧ᶜᵗ-irr (M [ split-[] ↦ true ]c) pT (subᶜ M split-[] true pM tt)
       ∙ C-subst-nat M split-[] true pM tt)
      (  ⟦⟧ᶜᵗ-irr (M [ split-[] ↦ false ]c) pF (subᶜ M split-[] false pM tt)
       ∙ C-subst-nat M split-[] false pM tt)
  ∙ ≈ᵐ-sym (ifᵐ-η (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM))
  ∙ ≈ᵐ-sym (C-subst-nat M split-[] V pM pV)
  ∙ ⟦⟧ᶜᵗ-irr (M [ split-[] ↦ V ]c) (subᶜ M split-[] V pM pV) pR

-- `match-eta`: re-pairing the two bound components rebuilds the matched value
-- (the product's eta, `⟨⟩ᵐ-unique`). Both sides mention `M` only under a
-- substitution, so its certificate comes in separately (this is the axiom's
-- `Midᶜ` payload).

sound-match-eta : ∀ {Γ A B C} → (V : Γ ⊢V⦂ A |×| B) → (M : Γ ∷ A |×| B ⊢C⦂ C)
                → Paramᶜ M → Soundᶜ== (match-eta V M)
sound-match-eta {Γ} {A} {B} {C} V M pM (pV , pB) pR =
    ∘ᵐ-congˡ (  ⟦⟧ᶜᵗ-irr ((C-rename ρ M) [ split-[] ↦ pair ]c) pB
                  (subᶜ (C-rename ρ M) split-[] pair (renᶜ ρ M pM) (tt , tt))
              ∙ C-subst-nat (C-rename ρ M) split-[] pair (renᶜ ρ M pM) (tt , tt)
              ∙ ∘ᵐ-congˡ (C-rename-nat ρ M pM))
  ∙ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ cart)
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (M [ split-[] ↦ V ]c) pR (subᶜ M split-[] V pM pV)
            ∙ C-subst-nat M split-[] V pM pV)
  where
    ρ    = wk-ren ∘ʳ exch-ren ∘ʳ wk-ren ∘ʳ exch-ren
    pair = ⦉ var (λ _ → ≾ᵣ-refl) (Tl-∷ Hd) , var (λ _ → ≾ᵣ-refl) Hd ⦊

    v = ⟦ V ⟧ᵛᵗ pV

    -- The whole renaming forgets the two components it re-bound: two
    -- exchanges each followed by a weakening leave the environment untouched
    -- apart from dropping `A` and `B`.
    ρ-mor : ⟦ ρ ⟧ʳ ≈ᵐ mapˣᵐ (fstᵐ ∘ᵐ fstᵐ) idᵐ
    ρ-mor =
        ∘ᵐ-congʳ (∘ᵐ-congʳ (  ∘ᵐ-congʳ (exch-ren-mor {Γ ∷ A} {B} {A |×| B})
                            ∙ ⟨⟩ᵐ-fstᵐ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (exch-ren-mor {Γ} {A} {A |×| B}))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
      ∙ mapˣᵐ-∘ _ _ _ _
      ∙ mapˣᵐ-cong ≈ᵐ-refl (∘ᵐ-identityˡ _)

    -- Substituting the re-paired components into the matched environment
    -- rebuilds the matched value: this is the product's eta.
    re-pair : sub-env split-[] pair (tt , tt)
                ∘ᵐ ⟨ ⟨ idᵐ , fstᵐ ∘ᵐ v ⟩ᵐ , sndᵐ ∘ᵐ v ⟩ᵐ
            ≈ᵐ ⟨ ⟨ ⟨ idᵐ , fstᵐ ∘ᵐ v ⟩ᵐ , sndᵐ ∘ᵐ v ⟩ᵐ , v ⟩ᵐ
    re-pair =
        ⟨⟩ᵐ-∘ _ _ _
      ∙ ⟨ ∘ᵐ-identityˡ _
        ,   ⟨⟩ᵐ-∘ _ _ _
          ∙ ⟨   ∘ᵐ-congˡ (  var-morphism-Tl-∷ {Γ ∷ A} {B} {A} Hd _
                          ∙ ∘ᵐ-congˡ (var-morphism-Hd {Γ} {A} _))
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
              ∙ ⟨⟩ᵐ-sndᵐ _ _
            , ∘ᵐ-congˡ (var-morphism-Hd {Γ ∷ A} {B} _) ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong
          ∙ ≈ᵐ-sym (⟨⟩ᵐ-unique _ _ v ≈ᵐ-refl ≈ᵐ-refl) ⟩ᵐ-cong

    cart : ⟦ ρ ⟧ʳ ∘ᵐ sub-env split-[] pair (tt , tt)
                     ∘ᵐ ⟨ ⟨ idᵐ , fstᵐ ∘ᵐ v ⟩ᵐ , sndᵐ ∘ᵐ v ⟩ᵐ
         ≈ᵐ sub-env split-[] V pV
    cart =
        ∘ᵐ-congˡ ρ-mor
      ∙ ∘ᵐ-congʳ re-pair
      ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
      ∙ ⟨   ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
          ∙ ⟨⟩ᵐ-fstᵐ _ _
        , ∘ᵐ-identityˡ _ ⟩ᵐ-cong

sound-match-beta : ∀ {Γ A B C} → (V : Γ ⊢V⦂ A) → (W : Γ ⊢V⦂ B) → (M : Γ ∷ A ∷ B ⊢C⦂ C)
                 → Soundᶜ== (match-beta V W M)
sound-match-beta V W M ((pV , pW) , pM) pR =
    ∘ᵐ-congʳ (⟨ ⟨ ≈ᵐ-refl , ⟨⟩ᵐ-fstᵐ _ _ ⟩ᵐ-cong , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr ((M [ split-[] ↦ V-rename wk-ren W ]c) [ split-[] ↦ V ]c) pR
                (subᶜ (M [ split-[] ↦ V-rename wk-ren W ]c) split-[] V
                   (subᶜ M split-[] (V-rename wk-ren W) pM (renᵛ wk-ren W pW)) pV)
            ∙ C-subst-nat (M [ split-[] ↦ V-rename wk-ren W ]c) split-[] V
                (subᶜ M split-[] (V-rename wk-ren W) pM (renᵛ wk-ren W pW)) pV
            ∙ ∘ᵐ-congˡ (  C-subst-nat M split-[] (V-rename wk-ren W) pM (renᵛ wk-ren W pW)
                        ∙ ∘ᵐ-congʳ ⟨ ≈ᵐ-refl , V-rename-nat wk-ren W pW ⟩ᵐ-cong)
            ∙ ∘ᵐ-assoc _ _ _
            ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                        ∙ ⟨ ∘ᵐ-identityˡ _
                          , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                            ∙ ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
