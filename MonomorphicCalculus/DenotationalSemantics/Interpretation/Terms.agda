------------------------------------------------------------------------
-- Interpretation of the well-typed terms (values and computations).  --
--                                                                    --
-- A value `Γ ⊢ᵛ⦂ A` is a morphism `⟦ Γ ⟧ →ᵐ ⟦ A ⟧ᵛ`; a computation   --
-- `Γ ⊢ᶜ⦂ C` is `⟦ Γ ⟧ →ᵐ ⟦ C ⟧ᶜ`. Variables use the machinery of     --
-- `Interpretation.Variables`, the effectful formers the graded       --
-- monad, and the Fitch formers the adjunction. Subsumption           --
-- post-composes the coercion of its witness.                         --
--                                                                    --
-- `perform`'s parameter/arity are ground types, interpreted via the  --
-- coercion `⟦ ⌜ G ⌝ᵍ ⟧ᵛ ≡ ⟦ G ⟧ᵍ` (`ty-gty`).                        --
------------------------------------------------------------------------

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

module MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms
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

open import MonomorphicCalculus.Syntax.Types S
open import MonomorphicCalculus.Syntax.Contexts S
open import MonomorphicCalculus.Syntax.Terms S
open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-∘ᵐ; []-congᶠ; []-≤)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-≤; εᵘ; ⟨⟩-≤-nat; ⟨⟩-≤-refl; ⟨⟩-≤-trans; ⟨⟩-≤-irr)
open Adjunction Adj using (η⊣; ε⊣; η⊣-nat; η⊣-≤)
open GroundTypes GTy
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj
       using (Eternalᵒ; ⟨⊤⟩-η; ⟨⊤⟩-η-nat; ⟨⊤⟩-eternalᵒ; ⟨⊤⟩-free-necᵉ-nat)

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Comparisons S Cat Fut Pst Adj GTy Mon GE
  using (holdsᵐ; cmpᵐ)

-- The value-type interpretation of a ground type coincides with its
-- ground-type interpretation.

ty-gty : ∀ (G : GType) → ⟦ ⌜ G ⌝ᵍ ⟧ᵛ ≡ ⟦ G ⟧ᵍ
ty-gty (Base b)     = refl
ty-gty unit         = refl
ty-gty bool         = refl
ty-gty nat          = refl
ty-gty empty        = refl
ty-gty (G₁ |×|ᵍ G₂) = cong₂ _×ᵐ_ (ty-gty G₁) (ty-gty G₂)
ty-gty (G₁ |+|ᵍ G₂) = cong₂ _+ᵐ_ (ty-gty G₁) (ty-gty G₂)
ty-gty (listᵍ G)    = cong Listᵐ (ty-gty G)
ty-gty ([ ρ ]ᵍ G)   = cong (λ O → [ ρ ]ᵒ O) (ty-gty G)

-- Naturality of `×ᵐ-assoc⁻¹` in its third component, and commutation of
-- domain- and codomain-reindexing of an exponential. Both are needed to push a
-- continuation coercion through `⟦_⟧ʰᵗ`'s adapter.

×ᵐ-assoc⁻¹-nat³ : ∀ {A B C C'} → (h : C →ᵐ C')
               → ×ᵐ-assoc⁻¹ {A} {B} {C'} ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ h)
               ≈ᵐ mapˣᵐ idᵐ h ∘ᵐ ×ᵐ-assoc⁻¹ {A} {B} {C}
×ᵐ-assoc⁻¹-nat³ h = ≈ᵐ-trans lhs≈canon (≈ᵐ-sym rhs≈canon)
  where
    fm : fstᵐ ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ h) ≈ᵐ fstᵐ
    fm = ≈ᵐ-trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-identityˡ _)
    sm : sndᵐ ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ h) ≈ᵐ mapˣᵐ idᵐ h ∘ᵐ sndᵐ
    sm = ⟨⟩ᵐ-sndᵐ _ _
    fm' : fstᵐ ∘ᵐ mapˣᵐ idᵐ h ≈ᵐ fstᵐ
    fm' = ≈ᵐ-trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-identityˡ _)
    sm' : sndᵐ ∘ᵐ mapˣᵐ idᵐ h ≈ᵐ h ∘ᵐ sndᵐ
    sm' = ⟨⟩ᵐ-sndᵐ _ _
    lhs≈canon =
      ≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
        (⟨ ≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
             (⟨ fm
              , ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                (≈ᵐ-trans (∘ᵐ-congʳ sm)
                (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ fm'))) ⟩ᵐ-cong)
         , ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
           (≈ᵐ-trans (∘ᵐ-congʳ sm)
           (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
           (≈ᵐ-trans (∘ᵐ-congˡ sm') (∘ᵐ-assoc _ _ _)))) ⟩ᵐ-cong)
    rhs≈canon =
      ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _) (⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)

map⇒ᵐ-swap : ∀ {A B C D} → (f : A →ᵐ B) → (g : C →ᵐ D)
           → map⇒ᵐ f idᵐ ∘ᵐ map⇒ᵐ idᵐ g ≈ᵐ map⇒ᵐ idᵐ g ∘ᵐ map⇒ᵐ f idᵐ
map⇒ᵐ-swap f g =
  ≈ᵐ-trans (map⇒ᵐ-curryᵐˡ f _)
  (≈ᵐ-trans (curryᵐ-cong
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
              (∘ᵐ-congʳ (∘ᵐ-congʳ
                (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                          (mapˣᵐ-cong (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))))))))
            (≈ᵐ-sym (≈ᵐ-trans (map⇒ᵐ-curryᵐ g _)
                              (curryᵐ-cong (∘ᵐ-congʳ (∘ᵐ-identityˡ _))))))

-- The step of a primitive recursion at `T B ε`: the recursive call's result
-- sequenced with the step's body `n` exactly as `_⨟_` is interpreted, the
-- context reaching `n` through `⟨⊤⟩-η` as a handler clause's does, followed
-- by the sub-effecting that absorbs the iteration.

recℕ-stepᵗ : ∀ {X B ε}
           → ε ·ₑ ε ≾ₑ ε
           → ⟨ ∣ ε ∣ᵉ ⟩ᵒ (⟨ ⊤ᵣ ⟩ᵒ X ×ᵐ ℕᵐ) ×ᵐ B →ᵐ Tᵒ B ε
           → (X ×ᵐ ℕᵐ) ×ᵐ Tᵒ B ε →ᵐ Tᵒ B ε
recℕ-stepᵗ p n =
  T-≤ p ∘ᵐ μᵀ ∘ᵐ Tᶠ n ∘ᵐ strᵀ ∘ᵐ mapˣᵐ (η⊣ ∘ᵐ mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ

-- The step of a primitive recursion on lists, likewise; the barred part of the
-- context is the ambient one, the head and the tail sit beside it.

recL-stepᵗ : ∀ {X A B ε}
           → ε ·ₑ ε ≾ₑ ε
           → ⟨ ∣ ε ∣ᵉ ⟩ᵒ ((⟨ ⊤ᵣ ⟩ᵒ X ×ᵐ A) ×ᵐ Listᵐ A) ×ᵐ B →ᵐ Tᵒ B ε
           → ((X ×ᵐ A) ×ᵐ Listᵐ A) ×ᵐ Tᵒ B ε →ᵐ Tᵒ B ε
recL-stepᵗ p n =
  T-≤ p ∘ᵐ μᵀ ∘ᵐ Tᶠ n ∘ᵐ strᵀ ∘ᵐ mapˣᵐ (η⊣ ∘ᵐ mapˣᵐ (mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ) idᵐ

-- Handling by a fold: the return clause `n` is sequenced after the handled
-- computation as the continuation of `_⨟_`, and the result folded by `h`,
-- whose clauses see the context through `⟨⊤⟩-η`.

private
  infixr 3 _∙_
  _∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙_ = ≈ᵐ-trans

handle-foldᵗ : ∀ {X A B ε ε'} → Handlerᵀ (⟨ ⊤ᵣ ⟩ᵒ X) B
             → ⟨ ∣ ε ∣ᵉ ⟩ᵒ X ×ᵐ A →ᵐ Tᵒ B ε'
             → X ×ᵐ Tᵒ A ε →ᵐ Tᵒ B (ε ·ₑ ε')
handle-foldᵗ {X} h n =
  T-alg-of-handlerᵀ (⟨⊤⟩-eternalᵒ X) h
    ∘ᵐ ⟨ ⟨⊤⟩-η ∘ᵐ fstᵐ , Tᶠ n ∘ᵐ strᵀ ∘ᵐ mapˣᵐ η⊣ idᵐ ⟩ᵐ

handle-foldᵗ-cong : ∀ {X A B ε ε'} → (h : Handlerᵀ (⟨ ⊤ᵣ ⟩ᵒ X) B)
                  → {n n' : ⟨ ∣ ε ∣ᵉ ⟩ᵒ X ×ᵐ A →ᵐ Tᵒ B ε'} → n ≈ᵐ n'
                  → handle-foldᵗ h n ≈ᵐ handle-foldᵗ h n'
handle-foldᵗ-cong h e = ∘ᵐ-congʳ ⟨ ≈ᵐ-refl , ∘ᵐ-congˡ (T-congᶠ e) ⟩ᵐ-cong

-- At a paired environment it is the inline form of handling.

handle-foldᵗ-⟨⟩ : ∀ {Y X A B ε ε'} → (h : Handlerᵀ (⟨ ⊤ᵣ ⟩ᵒ X) B)
                → (n : ⟨ ∣ ε ∣ᵉ ⟩ᵒ X ×ᵐ A →ᵐ Tᵒ B ε')
                → (g : Y →ᵐ X) → (m : Y →ᵐ Tᵒ A ε)
                → handle-foldᵗ h n ∘ᵐ ⟨ g , m ⟩ᵐ
                ≈ᵐ T-alg-of-handlerᵀ (⟨⊤⟩-eternalᵒ X) h
                     ∘ᵐ ⟨ ⟨⊤⟩-η ∘ᵐ g , Tᶠ n ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ ∘ᵐ g , m ⟩ᵐ ⟩ᵐ
handle-foldᵗ-⟨⟩ h n g m =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ ( ⟨⟩ᵐ-∘ _ _ _
             ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
               , ∘ᵐ-assoc _ _ _
                 ∙ ∘ᵐ-congʳ ( ∘ᵐ-assoc _ _ _
                            ∙ ∘ᵐ-congʳ ( mapˣᵐ-∘⟨⟩ _ _ _ _
                                       ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)) ⟩ᵐ-cong)

-- The fold commutes with relaxing the handled grade, the return clause
-- reaching its context through the relaxed lock.

handle-foldᵗ-≤ : ∀ {X A B ε₀ ε₁ ε'} → (h : Handlerᵀ (⟨ ⊤ᵣ ⟩ᵒ X) B)
               → (n : ⟨ ∣ ε₁ ∣ᵉ ⟩ᵒ X ×ᵐ A →ᵐ Tᵒ B ε') → (q : ε₀ ≾ₑ ε₁)
               → handle-foldᵗ h n ∘ᵐ mapˣᵐ idᵐ (T-≤ q)
               ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q)
                    ∘ᵐ handle-foldᵗ h (n ∘ᵐ mapˣᵐ (⟨⟩-≤ (map-monotoneᵉ q)) idᵐ)
handle-foldᵗ-≤ {X} h n q =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _ ∙ ⟨ fst-eq , snd-eq ⟩ᵐ-cong ∙ pair-eq)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-≤ (⟨⊤⟩-eternalᵒ X) h q)
  ∙ ∘ᵐ-assoc _ _ _
  where
    m = map-monotoneᵉ q
    fst-eq = ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _ ∙ ∘ᵐ-identityˡ _)
    -- the box relaxation `strᵀ-≤` leaves is the lock relaxation under `η⊣`
    unit-eq : mapˣᵐ ([]-≤ m) idᵐ ∘ᵐ mapˣᵐ η⊣ (idᵐ {Tᵒ _ _})
            ≈ᵐ mapˣᵐ ([ _ ]ᶠ (⟨⟩-≤ m)) idᵐ ∘ᵐ mapˣᵐ η⊣ idᵐ
    unit-eq = mapˣᵐ-∘ _ _ _ _
            ∙ mapˣᵐ-cong (η⊣-≤ m) ≈ᵐ-refl
            ∙ ≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _)
    snd-eq =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ ( ∘ᵐ-assoc _ _ _
                 ∙ ∘ᵐ-congʳ (mapˣᵐ-comm _ _)
                 ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                 ∙ ∘ᵐ-congˡ (strᵀ-≤ q)
                 ∙ ∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (T-≤-nat _ q)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ ( ∘ᵐ-congʳ ( ∘ᵐ-assoc _ _ _
                            ∙ ∘ᵐ-congʳ unit-eq
                            ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                            ∙ ∘ᵐ-congˡ (≈ᵐ-sym (strᵀ-natˡ _)))
                 ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
                 ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                 ∙ ∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)))
    pair-eq = ≈ᵐ-sym ( mapˣᵐ-∘⟨⟩ _ _ _ _
                     ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)

-- The fold is natural in the context, given clauses and a return clause that
-- are.

handle-foldᵗ-nat : ∀ {X Y A B ε ε'} → (g : Y →ᵐ X)
                 → (h : Handlerᵀ (⟨ ⊤ᵣ ⟩ᵒ X) B) → (h' : Handlerᵀ (⟨ ⊤ᵣ ⟩ᵒ Y) B)
                 → (∀ op ε'' → clauseᵀ h' op ε''
                             ≈ᵐ clauseᵀ h op ε'' ∘ᵐ mapˣᵐ (⟨ ⊤ᵣ ⟩ᶠ g) idᵐ)
                 → (n : ⟨ ∣ ε ∣ᵉ ⟩ᵒ X ×ᵐ A →ᵐ Tᵒ B ε')
                 → (n' : ⟨ ∣ ε ∣ᵉ ⟩ᵒ Y ×ᵐ A →ᵐ Tᵒ B ε')
                 → n' ≈ᵐ n ∘ᵐ mapˣᵐ (⟨ ∣ ε ∣ᵉ ⟩ᶠ g) idᵐ
                 → handle-foldᵗ h' n' ≈ᵐ handle-foldᵗ h n ∘ᵐ mapˣᵐ g idᵐ
handle-foldᵗ-nat {X} {Y} g h h' eh n n' en =
    ∘ᵐ-congˡ (T-alg-of-handlerᵀ-natᴾ (⟨⊤⟩-eternalᵒ X) (⟨⊤⟩-eternalᵒ Y)
                (⟨ ⊤ᵣ ⟩ᶠ g) (⟨⊤⟩-free-necᵉ-nat g) h h' eh)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ ( mapˣᵐ-∘⟨⟩ _ _ _ _
             ∙ ⟨ fst-eq , ∘ᵐ-identityˡ _ ∙ snd-eq ⟩ᵐ-cong
             ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  where
    fst-eq =
        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (⟨⊤⟩-η-nat g)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    unit-eq : mapˣᵐ ([ _ ]ᶠ (⟨ ∣ _ ∣ᵉ ⟩ᶠ g)) idᵐ ∘ᵐ mapˣᵐ η⊣ (idᵐ {Tᵒ _ _})
            ≈ᵐ mapˣᵐ η⊣ idᵐ ∘ᵐ mapˣᵐ g idᵐ
    unit-eq = mapˣᵐ-∘ _ _ _ _
            ∙ mapˣᵐ-cong (η⊣-nat g) ≈ᵐ-refl
            ∙ ≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _)
    snd-eq =
        ∘ᵐ-congˡ (T-congᶠ en ∙ T-∘ᵐ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ ( ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                 ∙ ∘ᵐ-congˡ (strᵀ-natˡ _)
                 ∙ ∘ᵐ-assoc _ _ _
                 ∙ ∘ᵐ-congʳ unit-eq
                 ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- The family a handler value denotes: at an index `ε₀ ≾ₑ ε`, the return
-- clause reaches its context through the relaxed lock `⟨⟩-≤`.

handler-famᵗ : ∀ {X A B ε ε'} → Handlerᵀ (⟨ ⊤ᵣ ⟩ᵒ X) B
             → ⟨ ∣ ε ∣ᵉ ⟩ᵒ X ×ᵐ A →ᵐ Tᵒ B ε'
             → Familyʰ X A ε B ε'
handler-famᵗ h n p = handle-foldᵗ h (n ∘ᵐ mapˣᵐ (⟨⟩-≤ (map-monotoneᵉ p)) idᵐ)

-- Composing two lock relaxations under the return clause

relax-∘ : ∀ {X A C ρ₀ ρ₁ ρ} → (n : ⟨ ρ ⟩ᵒ X ×ᵐ A →ᵐ C)
        → (a : ρ₁ ≾ᵣ ρ) → (b : ρ₀ ≾ᵣ ρ₁) → (c : ρ₀ ≾ᵣ ρ)
        → (n ∘ᵐ mapˣᵐ (⟨⟩-≤ a) idᵐ) ∘ᵐ mapˣᵐ (⟨⟩-≤ b) idᵐ
        ≈ᵐ n ∘ᵐ mapˣᵐ (⟨⟩-≤ c) idᵐ
relax-∘ n a b c =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ ( mapˣᵐ-∘ _ _ _ _
             ∙ mapˣᵐ-cong (⟨⟩-≤-trans b a ∙ ⟨⟩-≤-irr _ c) (∘ᵐ-identityˡ _))

handler-famᵗ-nat : ∀ {X A B ε ε'} → (h : Handlerᵀ (⟨ ⊤ᵣ ⟩ᵒ X) B)
                 → (n : ⟨ ∣ ε ∣ᵉ ⟩ᵒ X ×ᵐ A →ᵐ Tᵒ B ε')
                 → Naturalʰ (handler-famᵗ h n)
handler-famᵗ-nat h n p₀ p₁ q =
    handle-foldᵗ-≤ h _ q
  ∙ ∘ᵐ-congʳ (handle-foldᵗ-cong h (relax-∘ n _ _ _))

-- and is natural in the context

handler-famᵗ-reindex : ∀ {X Y A B ε ε' ε₀} → (g : Y →ᵐ X)
                     → (h : Handlerᵀ (⟨ ⊤ᵣ ⟩ᵒ X) B) → (h' : Handlerᵀ (⟨ ⊤ᵣ ⟩ᵒ Y) B)
                     → (∀ op ε'' → clauseᵀ h' op ε''
                                 ≈ᵐ clauseᵀ h op ε'' ∘ᵐ mapˣᵐ (⟨ ⊤ᵣ ⟩ᶠ g) idᵐ)
                     → (n : ⟨ ∣ ε ∣ᵉ ⟩ᵒ X ×ᵐ A →ᵐ Tᵒ B ε')
                     → (n' : ⟨ ∣ ε ∣ᵉ ⟩ᵒ Y ×ᵐ A →ᵐ Tᵒ B ε')
                     → n' ≈ᵐ n ∘ᵐ mapˣᵐ (⟨ ∣ ε ∣ᵉ ⟩ᶠ g) idᵐ
                     → (p : ε₀ ≾ₑ ε)
                     → handler-famᵗ h' n' p ≈ᵐ handler-famᵗ h n p ∘ᵐ mapˣᵐ g idᵐ
handler-famᵗ-reindex g h h' eh n n' en p =
  handle-foldᵗ-nat g h h' eh _ _
    ( ∘ᵐ-congˡ en
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ ( mapˣᵐ-∘ _ _ _ _
               ∙ mapˣᵐ-cong (⟨⟩-≤-nat g _) ≈ᵐ-refl
               ∙ ≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _))
    ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _))

-- The interpretation is defined only for parametric terms: a term whose
-- handlers are uniform in the residual effect grade the clauses are quantified
-- over. `Paramᶜ`/`Paramᵛ` is that certificate, and it is defined simultaneously
-- with the interpretation (induction-recursion) because the handler case has to
-- speak about the denotations of the clauses.
--
-- Every case but `handler` only collects the sub-terms' certificates.

mutual

  Paramᵛ : ∀ {Γ A} → Γ ⊢ᵛ⦂ A → Set
  Paramᵛ (var x f)   = ⊤
  Paramᵛ (const B c) = ⊤
  Paramᵛ ⋆           = ⊤
  Paramᵛ true        = ⊤
  Paramᵛ false       = ⊤
  Paramᵛ zero        = ⊤
  Paramᵛ (succ V)    = Paramᵛ V
  Paramᵛ nil         = ⊤
  Paramᵛ (cons V W)  = Paramᵛ V × Paramᵛ W
  Paramᵛ ⦉ V , W ⦊   = Paramᵛ V × Paramᵛ W
  Paramᵛ (inl V)     = Paramᵛ V
  Paramᵛ (inr V)     = Paramᵛ V
  Paramᵛ (cmp ⋈ V W et) = Paramᵛ V × Paramᵛ W
  Paramᵛ (fun M)     = Paramᶜ M
  -- the return clause, every operation clause, and the clauses' uniformity in
  -- the residual grade
  Paramᵛ {Γ} (handler {B = B} N H) =
    Paramᶜ N × Σ[ pH ∈ (∀ op ε'' → Paramᶜ (H op ε'')) ] EffUniformʰ {Γ} {B} H pH
  Paramᵛ (subV V p) = Paramᵛ V

  Paramᶜ : ∀ {Γ C} → Γ ⊢ᶜ⦂ C → Set
  Paramᶜ (return V)         = Paramᵛ V
  Paramᶜ (M ⨟ N)            = Paramᶜ M × Paramᶜ N
  Paramᶜ (V · W)            = Paramᵛ V × Paramᵛ W
  Paramᶜ (match V `with M)  = Paramᵛ V × Paramᶜ M
  Paramᶜ (absurd V)         = Paramᵛ V
  Paramᶜ (if V `then M `else N) = Paramᵛ V × Paramᶜ M × Paramᶜ N
  Paramᶜ (matchℕ V `zero M `succ N) = Paramᵛ V × Paramᶜ M × Paramᶜ N
  Paramᶜ (recℕ V M N p) = Paramᵛ V × Paramᶜ M × Paramᶜ N
  Paramᶜ (matchL V `nil M `cons N) = Paramᵛ V × Paramᶜ M × Paramᶜ N
  Paramᶜ (recL V M N p) = Paramᵛ V × Paramᶜ M × Paramᶜ N
  Paramᶜ (match+ V `inl M `inr N) = Paramᵛ V × Paramᶜ M × Paramᶜ N
  Paramᶜ (perform op V M) = Paramᵛ V × Paramᶜ M
  Paramᶜ (delay τ M)      = Paramᶜ M
  Paramᶜ (unbox x rel p M) = Paramᶜ M
  Paramᶜ (box _ V M)        = Paramᵛ V × Paramᶜ M
  Paramᶜ (subC M p)       = Paramᶜ M
  Paramᶜ (handle M `with V) = Paramᶜ M × Paramᵛ V

  -- Naturality of a handler's clauses in the residual effect `ε''`: the clause
  -- commutes with sub-effecting the boxed continuation's residual, landing on
  -- `·ₑ-monoʳ`. This is what `Paramᵛ` carries for a `handler` and what becomes
  -- the semantic handler's `Monoᵀ` field (built by `⟦_⟧ʰᵗ`).
  EffUniformʰ : ∀ {Γ B}
              → (H : (op : Op) → (ε'' : E)
                   → Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                        ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                     ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε''))
              → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
              → Set
  EffUniformʰ H pH = ∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'')
               → ⟦ H op ε₂'' ⟧ᶜᵗ (pH op ε₂'')
                   ∘ᵐ mapˣᵐ idᵐ ([ ∣ op-grade op ∣ᵉ ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
               ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H op ε₁'' ⟧ᶜᵗ (pH op ε₁'')

  ⟦_⟧ᵛᵗ : ∀ {Γ A} → (V : Γ ⊢ᵛ⦂ A) → Paramᵛ V → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ
  ⟦ var x f   ⟧ᵛᵗ _ = var-morphism x f
  ⟦ const B c ⟧ᵛᵗ _ = ⟦ c ⟧ᵇᶜ ∘ᵐ terminalᵐ
  ⟦ ⋆         ⟧ᵛᵗ _ = terminalᵐ
  ⟦ true      ⟧ᵛᵗ _ = trueᵐ ∘ᵐ terminalᵐ
  ⟦ false     ⟧ᵛᵗ _ = falseᵐ ∘ᵐ terminalᵐ
  ⟦ zero      ⟧ᵛᵗ _ = zeroᵐ ∘ᵐ terminalᵐ
  ⟦ succ V    ⟧ᵛᵗ pV = succᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ pV
  ⟦ nil       ⟧ᵛᵗ _ = nilᵐ ∘ᵐ terminalᵐ
  ⟦ cons V W  ⟧ᵛᵗ (pV , pW) = consᵐ ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ pV , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ
  ⟦ ⦉ V , W ⦊ ⟧ᵛᵗ (pV , pW) = ⟨ ⟦ V ⟧ᵛᵗ pV , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ
  ⟦ inl V     ⟧ᵛᵗ pV = inlᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ pV
  ⟦ inr V     ⟧ᵛᵗ pV = inrᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ pV
  -- the relation's truth on the comparison of the operands
  ⟦ cmp ⋈ V W et ⟧ᵛᵗ (pV , pW) =
    holdsᵐ ⋈ ∘ᵐ cmpᵐ et ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ pV , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ
  ⟦ fun M     ⟧ᵛᵗ pM = curryᵐ (⟦ M ⟧ᶜᵗ pM)
  ⟦ handler N H ⟧ᵛᵗ (pN , pH , uH) =
    curryʰ (handler-famᵗ (⟦ H ⟧ʰᵗ pH uH) (⟦ N ⟧ᶜᵗ pN))
           (handler-famᵗ-nat (⟦ H ⟧ʰᵗ pH uH) (⟦ N ⟧ᶜᵗ pN))
  ⟦ subV V p ⟧ᵛᵗ pV = ⟦ p ⟧<:ᵛ ∘ᵐ ⟦ V ⟧ᵛᵗ pV

  ⟦_⟧ᶜᵗ : ∀ {Γ C} → (M : Γ ⊢ᶜ⦂ C) → Paramᶜ M → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ C ⟧ᶜ
  ⟦ return V ⟧ᶜᵗ pV = ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ pV
  ⟦ _⨟_ {ε = ε} M N ⟧ᶜᵗ (pM , pN) =
    μᵀ ∘ᵐ Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ
  ⟦ V · W    ⟧ᶜᵗ (pV , pW) = appᵐ ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ pV , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ
  ⟦ match V `with M ⟧ᶜᵗ (pV , pM) =
    ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ ⟨ idᵐ , fstᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ pV ⟩ᵐ , sndᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ pV ⟩ᵐ
  ⟦ absurd V ⟧ᶜᵗ pV = initialᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ pV
  ⟦ if V `then M `else N ⟧ᶜᵗ (pV , pM , pN) =
    ifᵐ (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  ⟦ matchℕ V `zero M `succ N ⟧ᶜᵗ (pV , pM , pN) =
    matchℕᵐ (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  -- primitive recursion at `T ⟦ B ⟧ ε`, from the scrutinee
  ⟦ recℕ V M N p ⟧ᶜᵗ (pV , pM , pN) =
    recℕᵐ (⟦ M ⟧ᶜᵗ pM) (recℕ-stepᵗ p (⟦ N ⟧ᶜᵗ pN)) ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ pV ⟩ᵐ
  ⟦ matchL V `nil M `cons N ⟧ᶜᵗ (pV , pM , pN) =
    matchLᵐ (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  -- primitive recursion on lists at `T ⟦ B ⟧ ε`, from the scrutinee
  ⟦ recL V M N p ⟧ᶜᵗ (pV , pM , pN) =
    recLᵐ (⟦ M ⟧ᶜᵗ pM) (recL-stepᵗ p (⟦ N ⟧ᶜᵗ pN)) ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ pV ⟩ᵐ
  ⟦ match+ V `inl M `inr N ⟧ᶜᵗ (pV , pM , pN) =
    match+ᵐ (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  ⟦_⟧ᶜᵗ {Γ} (perform {A} {ε} op V M) (pV , pM) =
    opᵀ op ∘ᵐ
      ⟨ subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV)
      , [ ∣ op-grade op ∣ᵉ ]ᶠ
          (curryᵐ (subst (λ O → (⟨ ∣ op-grade op ∣ᵉ ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ ×ᵐ O) →ᵐ Tᵒ ⟦ A ⟧ᵛ ε)
                         (ty-gty (arity op)) (⟦ M ⟧ᶜᵗ pM)))
        ∘ᵐ η⊣ ⟩ᵐ
  ⟦ delay τ M ⟧ᶜᵗ pM = delayᵀ τ ∘ᵐ [ ιᵣ τ ]ᶠ (⟦ M ⟧ᶜᵗ pM) ∘ᵐ η⊣
  -- application at the handled computation's own grade
  ⟦ handle M `with V ⟧ᶜᵗ (pM , pV) =
    appʰ ≾ₑ-refl ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ pV , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ
  ⟦ unbox x rel p M ⟧ᶜᵗ pM =
    ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ idᵐ , ⟦ p ⟧<:ᵛ ∘ᵐ ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj x ⟩ᵐ
  ⟦ box ρ V M ⟧ᶜᵗ (pV , pM) =
    ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ idᵐ , [ ρ ]ᶠ (⟦ V ⟧ᵛᵗ pV) ∘ᵐ η⊣ ⟩ᵐ
  ⟦ subC M p ⟧ᶜᵗ pM = ⟦ p ⟧<:ᶜ ∘ᵐ ⟦ M ⟧ᶜᵗ pM

  -- The semantic handler of a syntactic one. Each clause sees the ambient
  -- context barred by `⟨ ⊤ᵣ ⟩`, so it interprets to a morphism parameterised
  -- by `⟨ ⊤ᵣ ⟩ᵒ ⟦ Γ ⟧`, the free `⟨⊤⟩`-algebra, hence eternal in every model.
  -- The `ty-gty` coercions adapt the ground-type parameter/arity to their
  -- value-type interpretations, and `×ᵐ-assoc⁻¹` reassociates the parameter.
  -- The handler's ambivalence is the clauses' uniformity `uH`, transported
  -- along that adapter.
  ⟦_⟧ʰᵗ : ∀ {Γ B}
        → (H : (op : Op) → (ε'' : E)
             → Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                  ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
               ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε''))
        → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
        → EffUniformʰ {Γ} {B} H pH
        → Handlerᵀ ⟦ Γ ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ ⟦ B ⟧ᵛ
  ⟦_⟧ʰᵗ {Γ} {B} H pH uH =
      (λ op ε'' → ⟦ H op ε'' ⟧ᶜᵗ (pH op ε'')
                    ∘ᵐ mapˣᵐ
                         (mapˣᵐ idᵐ (subst (λ O → ⟦ param op ⟧ᵍ →ᵐ O)
                                           (sym (ty-gty (param op))) idᵐ))
                         ([ ∣ op-grade op ∣ᵉ ]ᶠ
                           (map⇒ᵐ (subst (λ O → O →ᵐ ⟦ arity op ⟧ᵍ)
                                         (sym (ty-gty (arity op))) idᵐ) idᵐ))
                    ∘ᵐ ×ᵐ-assoc⁻¹)
    , (λ op q →
        ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ
          (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
          (≈ᵐ-trans (∘ᵐ-congʳ (×ᵐ-assoc⁻¹-nat³ _))
          (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
          (≈ᵐ-trans (∘ᵐ-congˡ
            (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
            (≈ᵐ-trans (mapˣᵐ-cong (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
                        (≈ᵐ-trans (≈ᵐ-sym ([]-∘ᵐ _ _))
                        (≈ᵐ-trans ([]-congᶠ (map⇒ᵐ-swap _ _)) ([]-∘ᵐ _ _))))
                      (≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _)))))
                    (∘ᵐ-assoc _ _ _))))))
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congˡ (uH op q))
                  (∘ᵐ-assoc _ _ _)))))


-- The syntactic grade coercion `ε-subst` denotes the monad's `ε-substᵀ`. It
-- carries no computational content, so it also transports a term's
-- parametricity certificate.

ε-substᴾ : ∀ {Γ A ε ε'} → (e : ε ≡ ε') → (M : Γ ⊢ᶜ⦂ A ! ε)
         → Paramᶜ M → Paramᶜ (ε-subst e M)
ε-substᴾ refl M p = p

sound-ε-subst : ∀ {Γ A ε ε'} → (e : ε ≡ ε') → (M : Γ ⊢ᶜ⦂ A ! ε) → (pM : Paramᶜ M)
              → ⟦ ε-subst e M ⟧ᶜᵗ (ε-substᴾ e M pM) ≈ᵐ ε-substᵀ e ∘ᵐ ⟦ M ⟧ᶜᵗ pM
sound-ε-subst refl M pM =
  ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-congˡ ε-substᵀ-refl) (∘ᵐ-identityˡ _))

-- Regrading along an equivalence of effects is a sub-effecting, so it denotes
-- the monad's `T-≤`, and the certificate is the term's own.

sound-ε-≃ : ∀ {Γ A ε ε'} → (e : ε ≃ₑ ε') → (M : Γ ⊢ᶜ⦂ A ! ε) → (pM : Paramᶜ M)
          → ⟦ ε-≃ e M ⟧ᶜᵗ pM ≈ᵐ T-≤ (proj₁ e) ∘ᵐ ⟦ M ⟧ᶜᵗ pM
sound-ε-≃ {A = A} e M pM =
  ∘ᵐ-congˡ (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (T-congᶠ (⟦⟧<:ᵛ-refl A)) T-idᵐ))
                     (∘ᵐ-identityˡ _))

-- Handling with a handler written in place denotes the fold of its clauses
-- after the return clause is sequenced: `curryʰ-β` at the reflexive index.

handle-in-β : ∀ {Γ A B ε ε'} → (M : Γ ⊢ᶜ⦂ A ! ε)
            → (H : (op : Op) → (ε'' : E)
                 → Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                      ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                   ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε''))
            → (N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε')
            → (pM : Paramᶜ M) → (pN : Paramᶜ N)
            → (pH : ∀ op ε'' → Paramᶜ (H op ε'')) → (uH : EffUniformʰ {Γ} {B} H pH)
            → ⟦ handle M `with H `in N ⟧ᶜᵗ (pM , pN , pH , uH)
            ≈ᵐ T-alg-of-handlerᵀ (⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ) (⟦_⟧ʰᵗ {Γ} H pH uH)
                 ∘ᵐ ⟨ ⟨⊤⟩-η , Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ ⟩ᵐ
handle-in-β {Γ} M H N pM pN pH uH =
    ∘ᵐ-congʳ (≈ᵐ-sym ( mapˣᵐ-∘⟨⟩ _ _ _ _
                     ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ ( curryʰ-β (handler-famᵗ h n) (handler-famᵗ-nat h n) ≾ₑ-refl
             ∙ handle-foldᵗ-cong h
                 ( ∘ᵐ-congʳ ( mapˣᵐ-cong (⟨⟩-≤-irr _ _ ∙ ⟨⟩-≤-refl) ≈ᵐ-refl
                            ∙ mapˣᵐ-idᵐ)
                 ∙ ∘ᵐ-identityʳ _))
  ∙ handle-foldᵗ-⟨⟩ h n idᵐ (⟦ M ⟧ᶜᵗ pM)
  ∙ ∘ᵐ-congʳ ⟨ ∘ᵐ-identityʳ _
             , ∘ᵐ-congʳ (∘ᵐ-congʳ ⟨ ∘ᵐ-identityʳ _ , ≈ᵐ-refl ⟩ᵐ-cong) ⟩ᵐ-cong
  where
    h = ⟦_⟧ʰᵗ {Γ} H pH uH
    n = ⟦ N ⟧ᶜᵗ pN
