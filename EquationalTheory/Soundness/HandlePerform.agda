------------------------------------------------------------------------
-- Soundness of the `handle-perform` equation (the last axiom).          --
--                                                                      --
-- Development module (not yet in Everything.agda). General renaming     --
-- lemmas proved here (`contract-mor`) will move to their proper homes    --
-- once the whole axiom is green.                                        --
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

module EquationalTheory.Soundness.HandlePerform
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
open import Relation.Nullary using (¬_; yes; no)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S using (V-rename; C-rename; unbox⇒var; var-rename)
open import Syntax.Substitutions S

open Category Cat
open Future Fut
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-idᵐ; ⟨⟩-congᶠ; μ)
open Adjunction Adj using (η⊣; ε⊣; η⊣-nat; η⊣-monoidal)
open GroundTypes GTy
open GroundEternal GE using (×-eternalᵒ; ×-eternalᵒ-extᵉ)
open Monad Mon

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE

open import EquationalTheory.EquationalTheory S

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE
       using (⟦⟧ᶜᵗ-irr; ⟦⟧ᵛᵗ-irr; Soundᶜ==)
open import OperationalSemantics.Soundness.Preservation.Step S Cat Fut Pst Adj GTy Mon GE
       using (box-split; η⊣-⟨⟩)
open import OperationalSemantics.Soundness.Preservation.Handle S Cat Fut Pst Adj GTy Mon GE
       using (op-pair; op-env)
open import OperationalSemantics.Soundness.Preservation.HandleOpCont S Cat Fut Pst Adj GTy Mon GE
       using (ren-ᴱ-∷≡restrict)

private
  infixr 3 _∙_
  _∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙_ = ≈ᵐ-trans

-- ═══════════════════════════════════════════════════════════════════════════
-- BRICK 2: pushing a sequel under an operation, WITHOUT an algebra.
--
-- `seq-op-box`/`seq-op-core` (Preservation/Handle) bake in a parameter-free
-- algebra `alg`, which a handler with a live eternal parameter is not. These
-- are the same two moves with that layer removed: what is left is exactly the
-- strength's own algebraicity, so the sequel `n` ends up inside the
-- operation's (boxed) continuation and nothing else changes.
-- ═══════════════════════════════════════════════════════════════════════════

str-op-box : ∀ {X A B ε ε'} → (op : Op)
  → (m : (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ ⟦ arity op ⟧ᵍ) →ᵐ Tᵒ A ε)
  → (n : (⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X ×ᵐ A) →ᵐ Tᵒ B ε')
  → (rn : ⟨ mapᵉ ε ⟩ᵒ (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ ⟦ arity op ⟧ᵍ)
          →ᵐ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X)
  → rn ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
  → [ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (Tᶠ n))
      ∘ᵐ ( [ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (strᵀ {_} {A} {ε}) ∘ᵐ exp-strᵐ)
         ∘ᵐ []-monoidal
         ∘ᵐ mapˣᵐ (δ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym map-·ᵉ))) idᵐ )
      ∘ᵐ ⟨ η⊣ {X} {mapᵉ (op-grade op ·ₑ ε)}
         , [ mapᵉ (op-grade op) ]ᶠ (curryᵐ m) ∘ᵐ η⊣ {X} {mapᵉ (op-grade op)} ⟩ᵐ
  ≈ᵐ [ mapᵉ (op-grade op) ]ᶠ
       (curryᵐ (Tᶠ (n ∘ᵐ mapˣᵐ rn idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ))
     ∘ᵐ η⊣ {X} {mapᵉ (op-grade op)}
str-op-box {X} {A} {B} {ε} {ε'} op m n rn ern =
  -- bring the strength law's reshuffle up against the operation's arguments
    ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  -- split the environment's box, and pair the two transposed halves under one
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (  mapˣᵐ-∘⟨⟩ _ _ _ _
       ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ box-split _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (η⊣-⟨⟩ _ _))
  -- collect everything under a single box
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
  -- inside the box: push the environment under the exponential and collapse
  ∙ ∘ᵐ-congˡ ([]-congᶠ
      (  ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (exp-strᵐ-⟨⟩ _ _))
       ∙ ∘ᵐ-congʳ (map⇒ᵐ-curryᵐ _ _)
       ∙ map⇒ᵐ-curryᵐ _ _))
  -- and recognise the syntax's renaming as the environment `n` receives
  ∙ ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (≈ᵐ-sym
      (  ∘ᵐ-congˡ (T-∘ᵐ n (mapˣᵐ rn idᵐ))
       ∙ ∘ᵐ-assoc _ _ _
       ∙ body))))
  where
    body : Tᶠ n ∘ᵐ Tᶠ (mapˣᵐ rn idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ
         ≈ᵐ Tᶠ n ∘ᵐ strᵀ
              ∘ᵐ ⟨ ([ mapᵉ ε ]ᶠ (⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ) ∘ᵐ η⊣)
                     ∘ᵐ fstᵐ
                 , m ⟩ᵐ
    body =
        ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ rn))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
          (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
          (⟨ ∘ᵐ-congˡ ([]-congᶠ ern) ∙ ≈ᵐ-sym (op-env _) , ≈ᵐ-refl ⟩ᵐ-cong))

str-op : ∀ {X Y A B ε ε'} → (op : Op)
  → (ea : Y ≡ ⟦ arity op ⟧ᵍ)
  → (v : X →ᵐ ⟦ param op ⟧ᵍ)
  → (m : (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ Y) →ᵐ Tᵒ A ε)
  → (n : (⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X ×ᵐ A) →ᵐ Tᵒ B ε')
  → (rn : ⟨ mapᵉ ε ⟩ᵒ (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ Y)
          →ᵐ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X)
  → rn ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
  → Tᶠ n ∘ᵐ strᵀ
      ∘ᵐ ⟨ η⊣
         , opᵀ op
             ∘ᵐ ⟨ v
                , [ mapᵉ (op-grade op) ]ᶠ
                    (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ O)
                                          →ᵐ Tᵒ A ε)
                                   ea m))
                    ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
  ≈ᵐ opᵀ op
     ∘ᵐ ⟨ v
        , [ mapᵉ (op-grade op) ]ᶠ
            (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ O)
                                  →ᵐ Tᵒ (Tᵒ B ε') ε)
                           ea
                           (Tᶠ (n ∘ᵐ mapˣᵐ rn idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ)))
          ∘ᵐ η⊣ ⟩ᵐ
str-op op refl v m n rn ern =
  -- the operation is a map on the strength's monadic component …
    ∘ᵐ-congʳ (∘ᵐ-congʳ
        (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))
  -- … so the strength pushes into it, carrying the environment under its box
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-opᵀ-algebraicity op))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  -- the reshuffle hands the parameter back and pairs environment with cont.
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ op-pair _ _ _ _))
  -- the sequel is natural, so it too goes into the continuation
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (opᵀ-nat op n))
  ∙ ∘ᵐ-assoc _ _ _
  -- collect the map on the continuation, and fire the box lemma
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , str-op-box op m n rn ern ⟩ᵐ-cong)


-- ═══════════════════════════════════════════════════════════════════════════
-- BRICK 3: transporting the fold along an eternal-skeleton extension, with a
-- LIVE parameter.
--
-- `HandleOpCont.handle-op-cont` does this only at a runtime configuration
-- (`Γ ᴱ ≡ []`), where the parameter collapses by terminality. Here the
-- parameter is carried, so the reconciliation is `T-alg-of-handlerᵀ-natᴾ`
-- along `ren-ᴱ-∷ A₀` — as in `sound-handle-unbox`, but over an arbitrary base.
-- ═══════════════════════════════════════════════════════════════════════════

private
  -- the ground-type adapter commutes with reindexing the eternal parameter
  adapt-comm : ∀ {D D' P Q R Sₒ} → (g : D →ᵐ D') → (p : Q →ᵐ P) → (a : Sₒ →ᵐ R)
             → mapˣᵐ (mapˣᵐ g idᵐ) idᵐ ∘ᵐ (mapˣᵐ (mapˣᵐ (idᵐ {D}) p) a ∘ᵐ ×ᵐ-assoc⁻¹)
             ≈ᵐ (mapˣᵐ (mapˣᵐ (idᵐ {D'}) p) a ∘ᵐ ×ᵐ-assoc⁻¹) ∘ᵐ mapˣᵐ g idᵐ
  adapt-comm g p a =
      ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙ ∘ᵐ-congˡ (  mapˣᵐ-∘ _ _ _ _
                ∙ mapˣᵐ-cong (  mapˣᵐ-∘ _ _ _ _
                              ∙ mapˣᵐ-cong (∘ᵐ-identityʳ _) (∘ᵐ-identityˡ _))
                             (∘ᵐ-identityˡ _))
    ∙ ≈ᵐ-sym (  ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (×ᵐ-assoc⁻¹-natˡ g)
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (  mapˣᵐ-∘ _ _ _ _
                          ∙ mapˣᵐ-cong (  mapˣᵐ-∘ _ _ _ _
                                        ∙ mapˣᵐ-cong (∘ᵐ-identityˡ _) (∘ᵐ-identityʳ _))
                                       (∘ᵐ-identityʳ _)))

module _ {Γ₀ : Ctx} {B : VType} (A₀ : VType)
         (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
            → Γ₀ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
              ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
         (pH : ∀ op ε'' Γ' → Paramᶜ (H op ε'' Γ'))
         (uH : EffUniformʰ {Γ₀} H pH)
       where

  -- the clauses reindexed to the extended eternal skeleton
  Hᴿ : (op : Op) → (ε'' : E) → (Γ' : Ctx)
     → (Γ₀ ∷ A₀) ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
          ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
       ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')
  Hᴿ op ε'' Γ' = C-rename (cong-ren (ren-ᴱ-∷ {Γ₀} A₀)) (H op ε'' Γ')

  fᴿ : ⟦ (Γ₀ ∷ A₀) ᴱ ⟧ᶜᵗˣ →ᵐ ⟦ Γ₀ ᴱ ⟧ᶜᵗˣ
  fᴿ = ⟦ ren-ᴱ-∷ {Γ₀} A₀ ⟧ʳ

  -- `ren-ᴱ-∷ A₀` *is* `restrict-ren wk-ren`, so the two coherences transport
  necᵉ-commᴿ : ∀ {ρ₀}
             → [ ρ₀ ]ᶠ fᴿ ∘ᵐ Eternalᵒ.necᵉ (⟦ Γ₀ ∷ A₀ ⟧ᴱ-Eternalᵒ) {ρ₀}
             ≈ᵐ Eternalᵒ.necᵉ (⟦ Γ₀ ⟧ᴱ-Eternalᵒ) {ρ₀} ∘ᵐ fᴿ
  necᵉ-commᴿ {ρ₀} =
    subst (λ z → [ ρ₀ ]ᶠ ⟦ z ⟧ʳ ∘ᵐ Eternalᵒ.necᵉ (⟦ Γ₀ ∷ A₀ ⟧ᴱ-Eternalᵒ) {ρ₀}
               ≈ᵐ Eternalᵒ.necᵉ (⟦ Γ₀ ⟧ᴱ-Eternalᵒ) {ρ₀} ∘ᵐ ⟦ z ⟧ʳ)
          (sym (ren-ᴱ-∷≡restrict {Γ₀} A₀))
          (restrict-ren-necᵉ (wk-ren {Γ₀} {A₀}))

  projᴱ-wkᴿ : projᴱ Γ₀ ∘ᵐ fstᵐ ≈ᵐ fᴿ ∘ᵐ projᴱ (Γ₀ ∷ A₀)
  projᴱ-wkᴿ =
    subst (λ z → projᴱ Γ₀ ∘ᵐ ⟦ wk-ren {Γ₀} {A₀} ⟧ʳ ≈ᵐ ⟦ z ⟧ʳ ∘ᵐ projᴱ (Γ₀ ∷ A₀))
          (sym (ren-ᴱ-∷≡restrict {Γ₀} A₀))
          (projᴱ-nat (wk-ren {Γ₀} {A₀}))

  module _ (pHᴿ : ∀ op ε'' Γ' → Paramᶜ (Hᴿ op ε'' Γ'))
           (uHᴿ : EffUniformʰ {Γ₀ ∷ A₀} Hᴿ pHᴿ)
         where

    clause-natᴿ : ∀ op ε''
                → clauseᵀ (⟦_⟧ʰᵗ {Γ₀ ∷ A₀} Hᴿ pHᴿ uHᴿ) op ε''
                ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {Γ₀} H pH uH) op ε'' ∘ᵐ mapˣᵐ fᴿ idᵐ
    clause-natᴿ op ε'' =
        ∘ᵐ-congˡ (  ⟦⟧ᶜᵗ-irr (Hᴿ op ε'' []) (pHᴿ op ε'' [])
                      (renᶜ (cong-ren (ren-ᴱ-∷ {Γ₀} A₀)) (H op ε'' []) (pH op ε'' []))
                  ∙ C-rename-nat (cong-ren (ren-ᴱ-∷ {Γ₀} A₀))
                      (H op ε'' []) (pH op ε'' []))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (adapt-comm _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

    alg-natᴿ : ∀ {ε ε'}
             → T-alg-of-handlerᵀ {_} {_} {ε} {ε'}
                 (⟦ Γ₀ ∷ A₀ ⟧ᴱ-Eternalᵒ) (⟦_⟧ʰᵗ {Γ₀ ∷ A₀} Hᴿ pHᴿ uHᴿ)
             ≈ᵐ T-alg-of-handlerᵀ {_} {_} {ε} {ε'}
                  (⟦ Γ₀ ⟧ᴱ-Eternalᵒ) (⟦_⟧ʰᵗ {Γ₀} H pH uH)
                ∘ᵐ mapˣᵐ fᴿ idᵐ
    alg-natᴿ =
      T-alg-of-handlerᵀ-natᴾ (⟦ Γ₀ ⟧ᴱ-Eternalᵒ) (⟦ Γ₀ ∷ A₀ ⟧ᴱ-Eternalᵒ)
        fᴿ necᵉ-commᴿ (⟦_⟧ʰᵗ {Γ₀} H pH uH) (⟦_⟧ʰᵗ {Γ₀ ∷ A₀} Hᴿ pHᴿ uHᴿ)
        clause-natᴿ


-- ═══════════════════════════════════════════════════════════════════════════
-- BRICK 4: the clause at `Γ' = Γ`, contracted, is the clause at `Γ' = []`.
--
-- The fold's operation law hands back `clauseᵀ h op _`, which is the clause at
-- the EMPTY extension; the axiom's right-hand side instead uses the clause at
-- `Γ' = Γ`, reindexed by `contract Γ`. `CtxUniformʰ` (naturality in the
-- extension) at the terminal map bridges them: `⋉-proj` turns the lifted
-- terminal map into `sndᵐ ∘ᵐ splitᴱ`, which cancels `contract Γ`'s re-glue
-- (`contract-mor` + `splitᴱ-iso`), leaving exactly `projᴱ Γ`.
-- ═══════════════════════════════════════════════════════════════════════════

contract-clause : ∀ {Γ B}
  → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
       → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (pH : ∀ op ε'' Γ' → Paramᶜ (H op ε'' Γ'))
  → (cH : CtxUniformʰ {Γ} H pH)
  → ∀ op ε''
  → ⟦ H op ε'' Γ ⟧ᶜᵗ (pH op ε'' Γ) ∘ᵐ mapˣᵐ (mapˣᵐ ⟦ contract Γ ⟧ʳ idᵐ) idᵐ
  ≈ᵐ ⟦ H op ε'' [] ⟧ᶜᵗ (pH op ε'' []) ∘ᵐ mapˣᵐ (mapˣᵐ (projᴱ Γ) idᵐ) idᵐ
contract-clause {Γ} H pH cH op ε'' =
    ∘ᵐ-congˡ (≈ᵐ-sym (cH op ε'' {Γ} {[]} terminalᵐ))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘ _ _ _ _
              ∙ mapˣᵐ-cong (  mapˣᵐ-∘ _ _ _ _
                            ∙ mapˣᵐ-cong bridge (∘ᵐ-identityˡ _))
                           (∘ᵐ-identityˡ _))
  where
    -- lifting the terminal map is the eternal projection, once `contract`'s
    -- re-glue is cancelled against `splitᴱ`
    bridge : _⋉_ Γ {Γ} {[]} terminalᵐ ∘ᵐ ⟦ contract Γ ⟧ʳ ≈ᵐ projᴱ Γ
    bridge =
        ∘ᵐ-cong (⋉-proj Γ Γ) (contract-mor Γ)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ (splitᴱ-iso Γ Γ)
                  ∙ ∘ᵐ-identityˡ _)
      ∙ ⟨⟩ᵐ-sndᵐ _ _


-- Applying the fold's boxed continuation to the actual (curried) continuation:
-- the `appᵐ` of the law's body meets the `curryᵐ` the operation carries, and the
-- exponential β-rule collapses them.
private
  cont-collapse : ∀ {P X Y Z W} → (alg : P ×ᵐ Z →ᵐ W) → (p : X →ᵐ P)
                → (c : X ×ᵐ Y →ᵐ Z)
                → curryᵐ (alg ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ
                                 , appᵐ ∘ᵐ ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ)
                    ∘ᵐ ⟨ p , curryᵐ c ⟩ᵐ
                ≈ᵐ curryᵐ (alg ∘ᵐ ⟨ p ∘ᵐ fstᵐ , c ⟩ᵐ)
  cont-collapse alg p c =
      ≈ᵐ-sym (curryᵐ-nat ⟨ p , curryᵐ c ⟩ᵐ _)
    ∙ curryᵐ-cong
        (  ∘ᵐ-assoc _ _ _
         ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                     ∙ ⟨   ∘ᵐ-assoc _ _ _
                         ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                         ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                         ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
                       ,   ∘ᵐ-assoc _ _ _
                         ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                                     ∙ ⟨   ∘ᵐ-assoc _ _ _
                                         ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                                         ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                                         ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)
                                       , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)
                         ∙ ≈ᵐ-sym (uncurryᵐ-nat (curryᵐ c) idᵐ)
                         ∙ uncurryᵐ-cong (∘ᵐ-identityˡ _)
                         ∙ curryᵐ-uncurryᵐ-iso c ⟩ᵐ-cong))

-- Cancelling the ground-type coercions: `⟦_⟧ᶜᵗ` coerces the operation's
-- parameter and arity between their value-type and ground-type
-- interpretations, and `⟦_⟧ʰᵗ` coerces them straight back.
private
  gty-cancelᵛ : ∀ {X Y Y'} → (e : Y ≡ Y') → (f : X →ᵐ Y)
              → subst (λ O → Y' →ᵐ O) (sym e) idᵐ ∘ᵐ subst (λ O → X →ᵐ O) e f
              ≈ᵐ f
  gty-cancelᵛ refl f = ∘ᵐ-identityˡ f

  arity-box : ∀ {Z W W' P Yv Yg} → (e : Yv ≡ Yg)
            → (alg : P ×ᵐ W' →ᵐ W) → (p : Z →ᵐ P) → (c : Z ×ᵐ Yv →ᵐ W')
            → map⇒ᵐ (subst (λ O → O →ᵐ Yg) (sym e) idᵐ) idᵐ
                ∘ᵐ curryᵐ (alg ∘ᵐ ⟨ p ∘ᵐ fstᵐ
                                  , subst (λ O → Z ×ᵐ O →ᵐ W') e c ⟩ᵐ)
            ≈ᵐ curryᵐ (alg ∘ᵐ ⟨ p ∘ᵐ fstᵐ , c ⟩ᵐ)
  arity-box refl alg p c = ∘ᵐ-congˡ map⇒ᵐ-idᵐ ∙ ∘ᵐ-identityˡ _

-- ═══════════════════════════════════════════════════════════════════════════
-- THE AXIOM: handling an operation applies the matching clause, with the rest
-- of the handled computation boxed up as the clause's continuation.
-- ═══════════════════════════════════════════════════════════════════════════

sound-handle-perform : ∀ {Γ A B ε ε' op}
  → (V : Γ ⊢V⦂ type-of-gtype (param op))
  → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
  → (H : (op' : Op) → (ε'' : E) → (Γ' : Ctx)
       → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op')
            ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op' ·ₑ ε''))
  → (N : Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
  → Soundᶜ== (handle-perform V M H N)
sound-handle-perform {Γ} {A} {B} {ε} {ε'} {op} V M H N
                     ((pV , pM) , pN , pH , uH , cH) pR = assembly
  where
    ren : Ren (Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩)
              ((Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) ⟨ mapᵉ ε ⟩)
    ren = cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-μ-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-·ᵉ)

    ern : ⟦ ren ⟧ʳ ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
    ern = ∘ᵐ-congˡ (∘ᵐ-congˡ (eq-ren-grade {Γ} map-·ᵉ)) ∙ ∘ᵐ-assoc _ _ _

    Vp = subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV)

    e = sym (·ₑ-assoc (op-grade op) ε ε')

    -- the reduct's pieces, with their certificates
    H' : (op' : Op) → (ε'' : E) → (Γ' : Ctx)
       → (Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) ᴱ
           ++ᶜ Γ' ∷ type-of-gtype (param op')
                  ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op' ·ₑ ε'')
    H' op' ε'' Γ' =
      C-rename (cong-ren (ren-ᴱ-∷ {Γ ⟨ mapᵉ (op-grade op) ⟩}
                                  (type-of-gtype (arity op))))
               (H op' ε'' Γ')

    pH' : ∀ op' ε'' Γ' → Paramᶜ (H' op' ε'' Γ')
    pH' op' ε'' Γ' =
      renᶜ (cong-ren (ren-ᴱ-∷ {Γ ⟨ mapᵉ (op-grade op) ⟩}
                              (type-of-gtype (arity op))))
           (H op' ε'' Γ') (pH op' ε'' Γ')

    uH' : EffUniformʰ {Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)} H' pH'
    uH' = ren-clauses-uniform
            (ren-ᴱ-∷ {Γ ⟨ mapᵉ (op-grade op) ⟩} (type-of-gtype (arity op))) H pH uH

    cH' : CtxUniformʰ {Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)} H' pH'
    cH' = subst (λ rr → CtxUniformʰ
                          {Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)}
                          (λ op' ε'' Γ' → C-rename (cong-ren rr) (H op' ε'' Γ'))
                          (λ op' ε'' Γ' → renᶜ (cong-ren rr) (H op' ε'' Γ')
                                            (pH op' ε'' Γ')))
                (sym (ren-ᴱ-∷≡restrict (type-of-gtype (arity op))))
                (ren-clauses-ctxuniform
                  (wk-ren {Γ = Γ ⟨ mapᵉ (op-grade op) ⟩}
                          {A = type-of-gtype (arity op)}) H pH cH)

    Cren = cong-∷-ren (cong-∷-ren (contract Γ))
    CL   = C-rename Cren (H op (ε ·ₑ ε') Γ)
    pCL  = renᶜ Cren (H op (ε ·ₑ ε') Γ) (pH op (ε ·ₑ ε') Γ)

    pBody : Paramᶜ (handle M `with H' `in (C-rename (cong-∷-ren ren) N))
    pBody = pM , renᶜ (cong-∷-ren ren) N pN , pH' , uH' , cH'

    pBox : Paramᶜ (box (lam (handle M `with H' `in (C-rename (cong-∷-ren ren) N)))
                       (CL [ Tl-∷ Hd ↦ V ]c))
    pBox = pBody , subᶜ CL (Tl-∷ Hd) V pCL pV

    -- the clause, contracted and substituted, is the clause at the empty
    -- extension applied to the eternal projection and the operation's value
    rhs-left =
        ∘ᵐ-congˡ (  C-subst-nat CL (Tl-∷ Hd) V pCL pV
                  ∙ ∘ᵐ-congˡ (  C-rename-nat Cren (H op (ε ·ₑ ε') Γ)
                                  (pH op (ε ·ₑ ε') Γ)
                              ∙ contract-clause {Γ} {B} H pH cH op (ε ·ₑ ε')))
      ∙ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (  ∘ᵐ-congˡ (  mapˣᵐ-∘ _ _ _ _
                              ∙ mapˣᵐ-cong (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                            ∙ ⟨ ∘ᵐ-identityʳ _
                                              , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
                                           (∘ᵐ-identityˡ _))
                  ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
                  ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)

    -- the operation's boxed continuation on the reduct side: the arity
    -- coercions cancel (`arity-box`), the inner handle's fold is transported
    -- to the ambient eternal base (`alg-natᴿ`/`projᴱ-wkᴿ`, brick 3), and the
    -- sequel's renaming is recognised (`C-rename-nat`)
    boxeq =
      -- merge the coercion into the box and cancel it against the arity subst
        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
      ∙ ∘ᵐ-congˡ ([]-congᶠ (arity-box (ty-gty (arity op)) _ _ _))
      -- and what is left is the reduct's inner handle, once its fold is
      -- transported to the ambient eternal base
      ∙ ≈ᵐ-sym (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (
            ∘ᵐ-congˡ (alg-natᴿ {Γ ⟨ mapᵉ (op-grade op) ⟩}
                        (type-of-gtype (arity op)) H pH uH pH' uH')
          ∙ ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)
          ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-sym (projᴱ-wkᴿ {Γ ⟨ mapᵉ (op-grade op) ⟩}
                                 (type-of-gtype (arity op)) H pH uH)
                      , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
          ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                      , ∘ᵐ-congˡ (T-congᶠ
                          (C-rename-nat (cong-∷-ren ren) N pN)) ⟩ᵐ-cong)))))

    rhs-inner =
        rhs-left
      ∙ ≈ᵐ-sym (
            ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (
                ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                          ∙ ⟨   ⟨⟩ᵐ-∘ _ _ _
                              ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _
                                ,   ∘ᵐ-assoc _ _ _
                                  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
                                  ∙ ⟨⟩ᵐ-fstᵐ _ _ ⟩ᵐ-cong
                            ,   ∘ᵐ-assoc _ _ _
                              ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
                              ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)
              ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨   mapˣᵐ-∘⟨⟩ _ _ _ _
                  ∙ ⟨ ∘ᵐ-identityˡ _ , gty-cancelᵛ (ty-gty (param op)) _ ⟩ᵐ-cong
                , boxeq ⟩ᵐ-cong))

    -- the operation's boxed continuation: the eternal parameter is carried
    -- under the box by `necᵉ` (its mate `η⊣`), pairs up with the continuation
    -- by `η⊣-⟨⟩`, and the fold is applied inside by `cont-collapse`
    boxpart =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (
            ⟨⟩ᵐ-∘ _ _ _
          ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _
            , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
            mapˣᵐ-∘⟨⟩ _ _ _ _
          ∙ ⟨   ∘ᵐ-congˡ (Eternalᵒ.necᵉ-mate (⟦ Γ ⟧ᴱ-Eternalᵒ))
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat (projᴱ Γ)))
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
            , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ ∘ᵐ-congʳ (η⊣-⟨⟩ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
      ∙ ∘ᵐ-congˡ ([]-congᶠ (cont-collapse _ _ _))

    assembly =
      -- the operation push (brick 2): the sequel `N` moves into the
      -- operation's boxed continuation
        ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                  , str-op op (ty-gty (arity op)) Vp (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
                      ⟦ ren ⟧ʳ ern ⟩ᵐ-cong)
      -- re-form `mapˣᵐ idᵐ (opᵀ op)` and fire the fold's operation law
      ∙ ∘ᵐ-congʳ (  ⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _) , ≈ᵐ-refl ⟩ᵐ-cong
                  ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-opᵀ op (⟦ Γ ⟧ᴱ-Eternalᵒ) (⟦_⟧ʰᵗ {Γ} H pH uH))
      -- feed the operation's arguments to the law's reshuffle: the eternal
      -- parameter and the operation's parameter come back untouched, and the
      -- continuation is where all the work happens
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
            ⟨⟩ᵐ-∘ _ _ _
          ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _
            , ⟨⟩ᵐ-∘ _ _ _
              ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-fstᵐ _ _
                , boxpart ⟩ᵐ-cong ⟩ᵐ-cong))
      -- … and that is the reduct: the clause fired at `Γ`, applied to the
      -- parameter and to the boxed continuation the `box` allocates
      ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr
                    (ε-subst e
                      (box (lam (handle M `with H' `in (C-rename (cong-∷-ren ren) N)))
                           (CL [ Tl-∷ Hd ↦ V ]c)))
                    pR (ε-substᴾ e _ pBox)
                ∙ sound-ε-subst e
                    (box (lam (handle M `with H' `in (C-rename (cong-∷-ren ren) N)))
                         (CL [ Tl-∷ Hd ↦ V ]c))
                    pBox
                ∙ ∘ᵐ-congʳ rhs-inner)
