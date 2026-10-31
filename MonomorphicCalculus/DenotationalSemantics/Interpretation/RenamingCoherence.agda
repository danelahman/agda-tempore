--------------------------------------------------------------------------
-- The interpretation is natural in renamings:                          --
--   ⟦ C-rename r M ⟧ᶜᵗ ≈ ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ r ⟧ʳ    (and dually for values). --
--                                                                      --
-- Proved by mutual induction on the term. The `var` case is            --
-- `var-morphism-nat`; the environment-threading formers push `⟦ r ⟧ʳ`  --
-- through the modality structure using `η⊣`/`strᵀ`/box naturality.     --
--------------------------------------------------------------------------

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

module MonomorphicCalculus.DenotationalSemantics.Interpretation.RenamingCoherence
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Types           S
open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Renaming.Action S using (V-rename; C-rename; var-rename; rvar-rename)

open Category Cat
open Future Fut
open Past Pst
open Adjunction Adj
open GroundTypes GTy
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj
       using (Eternalᵒ; ⟨⊤⟩-η; ⟨⊤⟩-η-nat; ⟨⊤⟩-eternalᵒ; ⟨⊤⟩-free-necᵉ-nat)

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE

private
  infixr 3 _∙_
  _∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙_ = ≈ᵐ-trans

-- The resource an `unbox` names is stable under renaming: renaming the
-- variable reindexes the looked-up resource exactly along `⟦ r ⟧ʳ`. The two
-- grade bounds are witnesses of the same relation, so they are interchangeable
-- by `⟨⟩-≤-irr`.

unbox-env-nat′ : ∀ {Γ Γ' A ρ ρ'} → (r : Ren [] Γ' Γ)
               → (x : [ ρ ] A ∈[ ρ' ] Γ) → (rel : ρ' ≾ᵣ ρ)
               → (ε⊣ ∘ᵐ ⟨⟩-≤ (≾ᵣ-trans (proj₂ (proj₂ (rvar-rename r x))) rel)
                     ∘ᵐ var-proj (proj₁ (proj₂ (rvar-rename r x))))
                 ≈ᵐ (ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj x) ∘ᵐ ⟦ r ⟧ʳ
unbox-env-nat′ r x rel with var-rename r x | var-proj-nat r x (λ ())
... | ρ'' , p'' , y | vpn =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr _ (≾ᵣ-trans (p'' (λ ())) rel))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-trans (p'' (λ ())) rel))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ vpn))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))

-- and at whichever bound the renamed node stores

unbox-env-nat : ∀ {Γ Γ' A ρ ρ'} → (r : Ren [] Γ' Γ)
              → (x : [ ρ ] A ∈[ ρ' ] Γ) → (rel : ρ' ≾ᵣ ρ)
              → (rel' : proj₁ (rvar-rename r x) ≾ᵣ ρ)
              → (ε⊣ ∘ᵐ ⟨⟩-≤ rel' ∘ᵐ var-proj (proj₁ (proj₂ (rvar-rename r x))))
                ≈ᵐ (ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj x) ∘ᵐ ⟦ r ⟧ʳ
unbox-env-nat r x rel rel' =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr rel' _))) (unbox-env-nat′ r x rel)

-- Naturality of the (inverse) associator in its first component: both sides
-- are `⟨ ⟨ f ∘ fstᵐ , fstᵐ ∘ sndᵐ ⟩ , sndᵐ ∘ sndᵐ ⟩`.

×ᵐ-assoc⁻¹-natˡ : ∀ {A A' B C} → (f : A →ᵐ A')
               → ×ᵐ-assoc⁻¹ {A'} {B} {C} ∘ᵐ mapˣᵐ f idᵐ
               ≈ᵐ mapˣᵐ (mapˣᵐ f idᵐ) idᵐ ∘ᵐ ×ᵐ-assoc⁻¹ {A} {B} {C}
×ᵐ-assoc⁻¹-natˡ f =
  ≈ᵐ-trans lhs≈canon (≈ᵐ-sym rhs≈canon)
  where
    sndᵐ-mapˣ : sndᵐ ∘ᵐ mapˣᵐ f idᵐ ≈ᵐ sndᵐ
    sndᵐ-mapˣ = ≈ᵐ-trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _)
    lhs≈canon =
      ≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
        (⟨ ≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
             (⟨ ⟨⟩ᵐ-fstᵐ _ _
              , ≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ sndᵐ-mapˣ) ⟩ᵐ-cong)
         , ≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ sndᵐ-mapˣ) ⟩ᵐ-cong)
    rhs≈canon =
      ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
        (⟨ ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _) (⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
         , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)

-- A left map `mapˣᵐ g idᵐ` commutes past the reassociating adapter
-- `mapˣᵐ (mapˣᵐ idᵐ p) a ∘ᵐ ×ᵐ-assoc⁻¹`: the naturality in the first factor of
-- the ground-type adapter used by `⟦_⟧ʰᵗ`.

adapt-commute : ∀ {D D' P Q R S} → (g : D →ᵐ D') → (p : Q →ᵐ P) → (a : S →ᵐ R)
              → mapˣᵐ (mapˣᵐ g idᵐ) idᵐ ∘ᵐ (mapˣᵐ (mapˣᵐ (idᵐ {D}) p) a ∘ᵐ ×ᵐ-assoc⁻¹)
              ≈ᵐ (mapˣᵐ (mapˣᵐ (idᵐ {D'}) p) a ∘ᵐ ×ᵐ-assoc⁻¹) ∘ᵐ mapˣᵐ g idᵐ
adapt-commute g p a =
  ≈ᵐ-trans (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ab≈canon))
  (≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
          (≈ᵐ-trans (∘ᵐ-congʳ (×ᵐ-assoc⁻¹-natˡ g))
          (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                    (∘ᵐ-congˡ ba≈canon)))))
  where
    ab≈canon = ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
      (mapˣᵐ-cong (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                            (mapˣᵐ-cong (∘ᵐ-identityʳ _) (∘ᵐ-identityˡ _)))
                  (∘ᵐ-identityˡ _))
    ba≈canon = ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
      (mapˣᵐ-cong (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                            (mapˣᵐ-cong (∘ᵐ-identityˡ _) (∘ᵐ-identityʳ _)))
                  (∘ᵐ-identityʳ _))

-- Reindexings acting on disjoint product components commute.

mapˣ-swapᵐ : ∀ {A A' B B'} → (a : A →ᵐ A') → (c : B →ᵐ B')
           → mapˣᵐ a idᵐ ∘ᵐ mapˣᵐ idᵐ c ≈ᵐ mapˣᵐ idᵐ c ∘ᵐ mapˣᵐ a idᵐ
mapˣ-swapᵐ a c =
  ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
  (≈ᵐ-trans (mapˣᵐ-cong (∘ᵐ-identityʳ a) (∘ᵐ-identityˡ c))
  (≈ᵐ-trans (mapˣᵐ-cong (≈ᵐ-sym (∘ᵐ-identityˡ a)) (≈ᵐ-sym (∘ᵐ-identityʳ c)))
            (≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _))))

-- A primitive recursion's step is natural in its context: reindexing the
-- context `X` reindexes the body's context under both locks.

recℕ-stepᵗ-nat : ∀ {X X' B ε} → (p : ε ·ₑ ε ≾ₑ ε)
               → (n : ⟨ ∣ ε ∣ᵉ ⟩ᵒ (⟨ ⊤ᵣ ⟩ᵒ X ×ᵐ ℕᵐ) ×ᵐ B →ᵐ Tᵒ B ε)
               → (n' : ⟨ ∣ ε ∣ᵉ ⟩ᵒ (⟨ ⊤ᵣ ⟩ᵒ X' ×ᵐ ℕᵐ) ×ᵐ B →ᵐ Tᵒ B ε)
               → (h : X' →ᵐ X)
               → n' ≈ᵐ n ∘ᵐ mapˣᵐ (⟨ ∣ ε ∣ᵉ ⟩ᶠ (mapˣᵐ (⟨ ⊤ᵣ ⟩ᶠ h) idᵐ)) idᵐ
               → recℕ-stepᵗ p n' ≈ᵐ recℕ-stepᵗ p n ∘ᵐ mapˣᵐ (mapˣᵐ h idᵐ) idᵐ
recℕ-stepᵗ-nat {B = B} {ε = ε} p n n' h e =
    ∘ᵐ-congʳ (∘ᵐ-congʳ core ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  where
    pre : (η⊣ ∘ᵐ mapˣᵐ ⟨⊤⟩-η idᵐ) ∘ᵐ mapˣᵐ h idᵐ
        ≈ᵐ [ ∣ ε ∣ᵉ ]ᶠ (⟨ ∣ ε ∣ᵉ ⟩ᶠ (mapˣᵐ (⟨ ⊤ᵣ ⟩ᶠ h) idᵐ))
             ∘ᵐ (η⊣ ∘ᵐ mapˣᵐ ⟨⊤⟩-η (idᵐ {ℕᵐ}))
    pre =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ ( mapˣᵐ-∘ _ _ _ _
                 ∙ mapˣᵐ-cong (≈ᵐ-sym (⟨⊤⟩-η-nat h)) ≈ᵐ-refl
                 ∙ ≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (η⊣-nat _))
      ∙ ∘ᵐ-assoc _ _ _
    ctx : mapˣᵐ (η⊣ ∘ᵐ mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ ∘ᵐ mapˣᵐ (mapˣᵐ h idᵐ) (idᵐ {Tᵒ B ε})
        ≈ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (⟨ ∣ ε ∣ᵉ ⟩ᶠ (mapˣᵐ (⟨ ⊤ᵣ ⟩ᶠ h) idᵐ))) idᵐ
             ∘ᵐ mapˣᵐ (η⊣ ∘ᵐ mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ
    ctx = mapˣᵐ-∘ _ _ _ _ ∙ mapˣᵐ-cong pre ≈ᵐ-refl ∙ ≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _)
    core =
        ∘ᵐ-congˡ (T-congᶠ e)
      ∙ ∘ᵐ-congˡ (T-∘ᵐ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ ( ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                 ∙ ∘ᵐ-congˡ (strᵀ-natˡ _)
                 ∙ ∘ᵐ-assoc _ _ _
                 ∙ ∘ᵐ-congʳ (≈ᵐ-sym ctx)
                 ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- The step of a primitive recursion on lists is natural in its context
-- likewise.

recL-stepᵗ-nat : ∀ {X X' A B ε} → (p : ε ·ₑ ε ≾ₑ ε)
               → (n : ⟨ ∣ ε ∣ᵉ ⟩ᵒ ((⟨ ⊤ᵣ ⟩ᵒ X ×ᵐ A) ×ᵐ Listᵐ A) ×ᵐ B →ᵐ Tᵒ B ε)
               → (n' : ⟨ ∣ ε ∣ᵉ ⟩ᵒ ((⟨ ⊤ᵣ ⟩ᵒ X' ×ᵐ A) ×ᵐ Listᵐ A) ×ᵐ B →ᵐ Tᵒ B ε)
               → (h : X' →ᵐ X)
               → n' ≈ᵐ n ∘ᵐ mapˣᵐ (⟨ ∣ ε ∣ᵉ ⟩ᶠ (mapˣᵐ (mapˣᵐ (⟨ ⊤ᵣ ⟩ᶠ h) idᵐ) idᵐ)) idᵐ
               → recL-stepᵗ p n' ≈ᵐ recL-stepᵗ p n ∘ᵐ mapˣᵐ (mapˣᵐ (mapˣᵐ h idᵐ) idᵐ) idᵐ
recL-stepᵗ-nat {A = A} {B = B} {ε = ε} p n n' h e =
    ∘ᵐ-congʳ (∘ᵐ-congʳ core ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  where
    pre : (η⊣ ∘ᵐ mapˣᵐ (mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ) ∘ᵐ mapˣᵐ (mapˣᵐ h idᵐ) idᵐ
        ≈ᵐ [ ∣ ε ∣ᵉ ]ᶠ (⟨ ∣ ε ∣ᵉ ⟩ᶠ (mapˣᵐ (mapˣᵐ (⟨ ⊤ᵣ ⟩ᶠ h) idᵐ) idᵐ))
             ∘ᵐ (η⊣ ∘ᵐ mapˣᵐ (mapˣᵐ ⟨⊤⟩-η (idᵐ {A})) (idᵐ {Listᵐ A}))
    pre =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ ( mapˣᵐ-∘ _ _ _ _
                 ∙ mapˣᵐ-cong ( mapˣᵐ-∘ _ _ _ _
                              ∙ mapˣᵐ-cong (≈ᵐ-sym (⟨⊤⟩-η-nat h)) ≈ᵐ-refl
                              ∙ ≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _))
                              ≈ᵐ-refl
                 ∙ ≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (η⊣-nat _))
      ∙ ∘ᵐ-assoc _ _ _
    ctx : mapˣᵐ (η⊣ ∘ᵐ mapˣᵐ (mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ) idᵐ
            ∘ᵐ mapˣᵐ (mapˣᵐ (mapˣᵐ h idᵐ) idᵐ) (idᵐ {Tᵒ B ε})
        ≈ᵐ mapˣᵐ ([ ∣ ε ∣ᵉ ]ᶠ (⟨ ∣ ε ∣ᵉ ⟩ᶠ (mapˣᵐ (mapˣᵐ (⟨ ⊤ᵣ ⟩ᶠ h) idᵐ) idᵐ))) idᵐ
             ∘ᵐ mapˣᵐ (η⊣ ∘ᵐ mapˣᵐ (mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ) idᵐ
    ctx = mapˣᵐ-∘ _ _ _ _ ∙ mapˣᵐ-cong pre ≈ᵐ-refl ∙ ≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _)
    core =
        ∘ᵐ-congˡ (T-congᶠ e)
      ∙ ∘ᵐ-congˡ (T-∘ᵐ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ ( ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                 ∙ ∘ᵐ-congˡ (strᵀ-natˡ _)
                 ∙ ∘ᵐ-assoc _ _ _
                 ∙ ∘ᵐ-congʳ (≈ᵐ-sym ctx)
                 ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- Renaming preserves parametricity, and the interpretation is natural in the
-- renaming. The two are defined simultaneously: transporting a handler's
-- clause-uniformity across a renaming (`renᵛ`'s `handler` case) needs the
-- naturality lemma for the clauses themselves.

mutual

  renᵛ : ∀ {Γ Γ' A} → (r : Ren [] Γ' Γ) → (V : Γ ⊢V⦂ A) → Paramᵛ V → Paramᵛ (V-rename r V)
  renᵛ r (var f x) _ = tt
  renᵛ r (const c) _ = tt
  renᵛ r ⋆        _ = tt
  renᵛ r true     _ = tt
  renᵛ r false    _ = tt
  renᵛ r zero     _ = tt
  renᵛ r (succ V)  pV = renᵛ r V pV
  renᵛ r nil      _ = tt
  renᵛ r (cons V W) (pV , pW) = renᵛ r V pV , renᵛ r W pW
  renᵛ r ⦉ V , W ⦊ (pV , pW) = renᵛ r V pV , renᵛ r W pW
  renᵛ r (inl V)   pV = renᵛ r V pV
  renᵛ r (inr V)   pV = renᵛ r V pV
  renᵛ r (lam M)   pM = renᶜ (cong-∷-ren r) M pM
  -- the clauses' uniformity transports by `ren-clauses-uniform`
  renᵛ r (handler N H) (pN , pH , uH) =
      renᶜ (cong-∷-ren (cong-⟨⟩-ren r)) N pN
    , (λ op ε'' → renᶜ (cong-∷-ren (cong-∷-ren (cong-⟨⟩-ren r)))
                     (H op ε'') (pH op ε''))
    , ren-clauses-uniform (cong-⟨⟩-ren r) H pH uH
  renᵛ r (subV V p) pV = renᵛ r V pV

  renᶜ : ∀ {Γ Γ' C} → (r : Ren [] Γ' Γ) → (M : Γ ⊢C⦂ C) → Paramᶜ M → Paramᶜ (C-rename r M)
  renᶜ r (return V)       pV        = renᵛ r V pV
  renᶜ r (M ⨟ N)          (pM , pN) =
    renᶜ r M pM , renᶜ (cong-∷-ren (cong-⟨⟩-ren r)) N pN
  renᶜ r (V · W)          (pV , pW) = renᵛ r V pV , renᵛ r W pW
  renᶜ r (match V `in M)  (pV , pM) =
    renᵛ r V pV , renᶜ (cong-∷-ren (cong-∷-ren r)) M pM
  renᶜ r (absurd V)       pV        = renᵛ r V pV
  renᶜ r (cmp ⋈ V W et)   (pV , pW) = renᵛ r V pV , renᵛ r W pW
  renᶜ r (if V `then M `else N) (pV , pM , pN) =
    renᵛ r V pV , renᶜ r M pM , renᶜ r N pN
  renᶜ r (caseL V `nil M `cons N) (pV , pM , pN) =
    renᵛ r V pV , renᶜ r M pM , renᶜ (cong-∷-ren (cong-∷-ren r)) N pN
  renᶜ r (recL V M N p) (pV , pM , pN) =
      renᵛ r V pV , renᶜ r M pM
    , renᶜ (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren (cong-∷-ren (cong-⟨⟩-ren r))))) N pN
  renᶜ r (caseℕ V `zero M `succ N) (pV , pM , pN) =
    renᵛ r V pV , renᶜ r M pM , renᶜ (cong-∷-ren r) N pN
  renᶜ r (recℕ V M N p) (pV , pM , pN) =
      renᵛ r V pV , renᶜ r M pM
    , renᶜ (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren (cong-⟨⟩-ren r)))) N pN
  renᶜ r (case+ V `inl M `inr N) (pV , pM , pN) =
    renᵛ r V pV , renᶜ (cong-∷-ren r) M pM , renᶜ (cong-∷-ren r) N pN
  renᶜ r (perform op V M) (pV , pM) =
    renᵛ r V pV , renᶜ (cong-∷-ren (cong-⟨⟩-ren r)) M pM
  renᶜ r (delay τ M)      pM        = renᶜ (cong-⟨⟩-ren r) M pM
  renᶜ r (unbox x rel p M) pM       = renᶜ (cong-∷-ren r) M pM
  renᶜ r (box _ V M)        (pV , pM) =
    renᵛ (cong-⟨⟩-ren r) V pV , renᶜ (cong-∷-ren r) M pM
  renᶜ r (subC M p)       pM        = renᶜ r M pM
  renᶜ r (handle M `with V) (pM , pV) = renᶜ r M pM , renᵛ r V pV

  -- Renaming a clause family's ambient context preserves the clauses'
  -- uniformity in the residual grade: the renaming acts on the ambient context
  -- only, so it commutes with the continuation's coercion (`mapˣ-swapᵐ`), after
  -- which the original uniformity applies.
  ren-clauses-uniform :
    ∀ {Δ Δ' B} → (rr : Ren [] Δ' Δ)
    → (H : (op : Op) → (ε'' : E)
         → Δ ∷ type-of-gtype (param op)
              ∷ [ ∣ op-grade op ∣ᵉ ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
           ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
    → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
    → (∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'')
         → ⟦ H op ε₂'' ⟧ᶜᵗ (pH op ε₂'')
             ∘ᵐ mapˣᵐ idᵐ ([ ∣ op-grade op ∣ᵉ ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
         ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H op ε₁'' ⟧ᶜᵗ (pH op ε₁''))
    → (∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'')
         → ⟦ C-rename (cong-∷-ren (cong-∷-ren rr)) (H op ε₂'') ⟧ᶜᵗ
              (renᶜ (cong-∷-ren (cong-∷-ren rr)) (H op ε₂'') (pH op ε₂''))
             ∘ᵐ mapˣᵐ idᵐ ([ ∣ op-grade op ∣ᵉ ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
         ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q)
              ∘ᵐ ⟦ C-rename (cong-∷-ren (cong-∷-ren rr)) (H op ε₁'') ⟧ᶜᵗ
                   (renᶜ (cong-∷-ren (cong-∷-ren rr)) (H op ε₁'') (pH op ε₁'')))
  ren-clauses-uniform rr H pH uH op q =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-rename-nat (cong-∷-ren (cong-∷-ren rr))
                          (H op _) (pH op _)))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣ-swapᵐ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (uH op q))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
              (∘ᵐ-congʳ (≈ᵐ-sym (C-rename-nat (cong-∷-ren (cong-∷-ren rr))
                                   (H op _) (pH op _)))))))))

  V-rename-nat : ∀ {Γ Γ' A} → (r : Ren [] Γ' Γ) → (V : Γ ⊢V⦂ A) → (p : Paramᵛ V)
               → ⟦ V-rename r V ⟧ᵛᵗ (renᵛ r V p) ≈ᵐ ⟦ V ⟧ᵛᵗ p ∘ᵐ ⟦ r ⟧ʳ
  V-rename-nat r (var f x) _ with var-rename r x | var-morphism-nat r f x
  ... | ρ' , ρ'≾ρ , y | vmn = vmn
  V-rename-nat r (const c) _ =
    ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
  V-rename-nat r ⋆ _ = ≈ᵐ-sym terminalᵐ-unique
  V-rename-nat r true _ =
    ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
  V-rename-nat r false _ =
    ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
  V-rename-nat r zero _ =
    ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
  V-rename-nat r (succ V) pV =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-rename-nat r V pV)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  V-rename-nat r nil _ =
    ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
  V-rename-nat r (cons V W) (pV , pW) =
    ≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (⟨ V-rename-nat r V pV , V-rename-nat r W pW ⟩ᵐ-cong)
                                 (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))))
             (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  V-rename-nat r ⦉ V , W ⦊ (pV , pW) =
    ≈ᵐ-trans (⟨ V-rename-nat r V pV , V-rename-nat r W pW ⟩ᵐ-cong)
             (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  V-rename-nat r (inl V) pV =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-rename-nat r V pV)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  V-rename-nat r (inr V) pV =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-rename-nat r V pV)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  V-rename-nat r (lam M) pM =
    ≈ᵐ-trans (curryᵐ-cong (C-rename-nat (cong-∷-ren r) M pM))
             (curryᵐ-nat ⟦ r ⟧ʳ (⟦ M ⟧ᶜᵗ pM))
  -- the denoted family is natural in the context (`handler-famᵗ-reindex`): the
  -- clauses are renamed under the barrier lock, the return clause under the
  -- lock of the handled effect
  V-rename-nat {Γ} {Γ'} r (handler N H) (pN , pH , uH) =
    ≈ᵐ-trans (curryʰ-cong _ _ λ p →
               handler-famᵗ-reindex ⟦ r ⟧ʳ h _ ⟦⟧ʰᵗ-nat _ _
                 (C-rename-nat (cong-∷-ren (cong-⟨⟩-ren r)) N pN) p)
             (≈ᵐ-sym (curryʰ-nat (handler-famᵗ h (⟦ N ⟧ᶜᵗ pN))
                                 (handler-famᵗ-nat h (⟦ N ⟧ᶜᵗ pN)) ⟦ r ⟧ʳ))
    where
      h = ⟦_⟧ʰᵗ {Γ} H pH uH
      ⟦⟧ʰᵗ-nat : ∀ op ε''
               → clauseᵀ (⟦_⟧ʰᵗ {Γ'}
                    (λ op ε'' → C-rename (cong-∷-ren (cong-∷-ren (cong-⟨⟩-ren r)))
                                  (H op ε''))
                    (λ op ε'' →
                       renᶜ (cong-∷-ren (cong-∷-ren (cong-⟨⟩-ren r)))
                         (H op ε'') (pH op ε''))
                    (ren-clauses-uniform (cong-⟨⟩-ren r) H pH uH)) op ε''
               ≈ᵐ clauseᵀ h op ε'' ∘ᵐ mapˣᵐ ⟦ cong-⟨⟩-ren {ρ = ⊤ᵣ} r ⟧ʳ idᵐ
      ⟦⟧ʰᵗ-nat op ε'' =
        ≈ᵐ-trans (∘ᵐ-congˡ (C-rename-nat (cong-∷-ren (cong-∷-ren (cong-⟨⟩-ren r)))
                              (H op ε'') (pH op ε'')))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (adapt-commute _ _ _))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  V-rename-nat r (subV V p) pV =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-rename-nat r V pV)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))

  C-rename-nat : ∀ {Γ Γ' C} → (r : Ren [] Γ' Γ) → (M : Γ ⊢C⦂ C) → (p : Paramᶜ M)
               → ⟦ C-rename r M ⟧ᶜᵗ (renᶜ r M p) ≈ᵐ ⟦ M ⟧ᶜᵗ p ∘ᵐ ⟦ r ⟧ʳ
  C-rename-nat r (return V) pV =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-rename-nat r V pV)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  C-rename-nat r (M ⨟ N) (pM , pN) =
    ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (C-rename-nat (cong-∷-ren (cong-⟨⟩-ren r)) N pN))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
                (⟨ η⊣-nat ⟦ r ⟧ʳ
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-rename-nat r M pM) ⟩ᵐ-cong))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))))))))
  C-rename-nat r (V · W) (pV , pW) =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ V-rename-nat r V pV , V-rename-nat r W pW ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-rename-nat r (match V `in M) (pV , pM) =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-rename-nat (cong-∷-ren (cong-∷-ren r)) M pM))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
                   (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                    , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                      (≈ᵐ-trans (∘ᵐ-congʳ (V-rename-nat r V pV))
                                (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong)
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (V-rename-nat r V pV))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _) , ≈ᵐ-refl ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
  C-rename-nat r (absurd V) pV =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-rename-nat r V pV)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  C-rename-nat r (cmp ⋈ V W et) (pV , pW) =
    ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
               (≈ᵐ-trans (⟨ V-rename-nat r V pV , V-rename-nat r W pW ⟩ᵐ-cong)
                         (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  -- the renaming distributes over the branches: `ifᵐ-∘`
  C-rename-nat r (if V `then M `else N) (pV , pM , pN) =
    ≈ᵐ-trans (ifᵐ-cong (V-rename-nat r V pV)
                       (C-rename-nat r M pM) (C-rename-nat r N pN))
             (≈ᵐ-sym (ifᵐ-∘ _ _ _ _))
  -- likewise for `caseℕ` and `case+`: `caseℕᵐ-∘`, `caseᵐ-∘`
  C-rename-nat r (caseℕ V `zero M `succ N) (pV , pM , pN) =
    ≈ᵐ-trans (caseℕᵐ-cong (V-rename-nat r V pV)
                          (C-rename-nat r M pM)
                          (C-rename-nat (cong-∷-ren r) N pN))
             (≈ᵐ-sym (caseℕᵐ-∘ _ _ _ _))
  -- the recursor is natural in its context: `recℕᵐ-∘`, the step by
  -- `recℕ-stepᵗ-nat`
  C-rename-nat r (recℕ V M N p) (pV , pM , pN) =
      ∘ᵐ-cong (recℕᵐ-cong (C-rename-nat r M pM)
                (recℕ-stepᵗ-nat p _ _ ⟦ r ⟧ʳ
                  (C-rename-nat (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren (cong-⟨⟩-ren r))))
                                N pN)))
              ⟨ ≈ᵐ-refl , V-rename-nat r V pV ⟩ᵐ-cong
    ∙ ∘ᵐ-congˡ (≈ᵐ-sym (recℕᵐ-∘ _ _ _))
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ ( mapˣᵐ-∘⟨⟩ _ _ _ _
               ∙ ⟨ ∘ᵐ-identityʳ _ ∙ ≈ᵐ-sym (∘ᵐ-identityˡ _) , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
               ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
    ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  -- lists: `caseLᵐ-∘`, and for the recursor `recLᵐ-∘` with `recL-stepᵗ-nat`
  C-rename-nat r (caseL V `nil M `cons N) (pV , pM , pN) =
    ≈ᵐ-trans (caseLᵐ-cong (V-rename-nat r V pV)
                          (C-rename-nat r M pM)
                          (C-rename-nat (cong-∷-ren (cong-∷-ren r)) N pN))
             (≈ᵐ-sym (caseLᵐ-∘ _ _ _ _))
  C-rename-nat r (recL V M N p) (pV , pM , pN) =
      ∘ᵐ-cong (recLᵐ-cong (C-rename-nat r M pM)
                (recL-stepᵗ-nat p _ _ ⟦ r ⟧ʳ
                  (C-rename-nat (cong-∷-ren (cong-⟨⟩-ren (cong-∷-ren (cong-∷-ren
                                   (cong-⟨⟩-ren r)))))
                                N pN)))
              ⟨ ≈ᵐ-refl , V-rename-nat r V pV ⟩ᵐ-cong
    ∙ ∘ᵐ-congˡ (≈ᵐ-sym (recLᵐ-∘ _ _ _))
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ ( mapˣᵐ-∘⟨⟩ _ _ _ _
               ∙ ⟨ ∘ᵐ-identityʳ _ ∙ ≈ᵐ-sym (∘ᵐ-identityˡ _) , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
               ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
    ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  C-rename-nat r (case+ V `inl M `inr N) (pV , pM , pN) =
    ≈ᵐ-trans (caseᵐ-cong (V-rename-nat r V pV)
                         (C-rename-nat (cong-∷-ren r) M pM)
                         (C-rename-nat (cong-∷-ren r) N pN))
             (≈ᵐ-sym (caseᵐ-∘ _ _ _ _))
  C-rename-nat r (perform op V M) (pV , pM) =
    ≈ᵐ-trans (∘ᵐ-congʳ
      (⟨ ≈ᵐ-trans (substᶜ-≈ (ty-gty (param op)) (V-rename-nat r V pV))
                  (≡→≈ᵐ (sym (substᶜ-∘ (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV) ⟦ r ⟧ʳ)))
       , ≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                    (≈ᵐ-trans (substᵈ-≈ (ty-gty (arity op))
                                (C-rename-nat (cong-∷-ren (cong-⟨⟩-ren r)) M pM))
                              (≡→≈ᵐ (sym (substᵈ-∘ (ty-gty (arity op)) (⟦ M ⟧ᶜᵗ pM)
                                           (⟨ ∣ op-grade op ∣ᵉ ⟩ᶠ ⟦ r ⟧ʳ))))))))
         (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-nat _ _)))
         (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
         (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat ⟦ r ⟧ʳ))
                   (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-rename-nat r (delay τ M) pM =
    ≈ᵐ-sym
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat ⟦ r ⟧ʳ))))
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
                (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ
                  (≈ᵐ-sym (C-rename-nat (cong-⟨⟩-ren r) M pM))))))))))
  C-rename-nat r (handle M `with V) (pM , pV) =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ V-rename-nat r V pV , C-rename-nat r M pM ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-rename-nat r (unbox x rel p M) pM =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-rename-nat (cong-∷-ren r) M pM))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (unbox-env-nat r x rel _))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
  C-rename-nat r (box _ V M) (pV , pM) =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-rename-nat (cong-∷-ren r) M pM))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (V-rename-nat (cong-⟨⟩-ren r) V pV)))
                   (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
                   (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat ⟦ r ⟧ʳ))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ idᵐ ([ _ ]ᶠ (⟦ V ⟧ᵛᵗ pV) ∘ᵐ η⊣) ⟦ r ⟧ʳ)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
  C-rename-nat r (subC M p) pM =
    ≈ᵐ-trans (∘ᵐ-congʳ (C-rename-nat r M pM)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
