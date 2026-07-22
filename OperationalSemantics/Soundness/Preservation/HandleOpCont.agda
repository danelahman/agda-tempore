------------------------------------------------------------------------
-- The HANDLE-OP continuation lemma.                                     --
--                                                                      --
-- `sound-HANDLE-OP`'s reduct boxes up the handled remainder as a        --
-- continuation: `handle M with H' in N'`, where `H'` is `H` renamed by  --
-- `ren-ᴱ-∷` (its clauses now close over the extended eternal context)   --
-- and `N'` is `N` renamed by the commuting conversion. This lemma        --
-- reconciles that inner handle's interpretation with the collapsed       --
-- handler algebra `Halg` at the ambient runtime context (`Γ ᴱ ≡ []`).    --
-- The reconciliation is the `HANDLE-STEP` pattern: `⟦H'⟧ʰᵗ`-naturality   --
-- for the renaming, `T-alg-of-handlerᵀ-natᴾ`, and terminality of         --
-- `⟦ Γ ᴱ ⟧`. Split off into its own (interpretation-only) module so it    --
-- compiles fast and its goals are readable.                             --
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

module OperationalSemantics.Soundness.Preservation.HandleOpCont
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
open import Relation.Nullary using (yes; no)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types      S
open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.Renamings  S
open import Syntax.RenActions S using (C-rename)

open Category Cat
open Future Fut
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η)
open Adjunction Adj using (η⊣)
open GroundTypes GTy using (⟦_⟧ᵍ)
open Monad Mon

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE

infixr 3 _∙_
_∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
_∙_ = ≈ᵐ-trans

bcᴱ : ∀ (Γ : Ctx) → Eternalᵒ ⟦ Γ ᴱ ⟧ᶜᵗˣ
bcᴱ Γ = (⟦ Γ ⟧ᴱ-Eternalᵒ)

-- The reduct renames the handler's clauses by `ren-ᴱ-∷ A₀`, which is
-- definitionally the eternal restriction of `wk-ren` (both split on
-- `eternal? A₀`) — so the renaming coherence machinery applies to it.
ren-ᴱ-∷≡restrict : ∀ {Γ₀} → (A : VType)
                 → ren-ᴱ-∷ {Γ₀} A ≡ restrict-ren (wk-ren {Γ = Γ₀} {A = A})
ren-ᴱ-∷≡restrict A with eternal? A
... | yes _ = refl
... | no  _ = refl

term∅ : ∀ {Γ X} → (e : Γ ᴱ ≡ []) → X →ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ
term∅ {X = X} e = subst (λ Δ → X →ᵐ ⟦ Δ ⟧ᶜᵗˣ) (sym e) terminalᵐ

∅-terminal : ∀ {Γ X} → (e : Γ ᴱ ≡ []) → (f g : X →ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ) → f ≈ᵐ g
∅-terminal {X = X} e =
  subst (λ Δ → (f g : X →ᵐ ⟦ Δ ⟧ᶜᵗˣ) → f ≈ᵐ g) (sym e)
        (λ f g → ≈ᵐ-trans terminalᵐ-unique (≈ᵐ-sym terminalᵐ-unique))

-- The inner handle's interpretation equals the collapsed algebra applied to the
-- (renamed) sequel. `H'` renames `H`'s clauses along `ren-ᴱ-∷ A₀` (= the eternal
-- restriction of `wk-ren`), so this is the renaming coherence of the handler at
-- `wk-ren`, reconciled with the terminal parameter of the outer context.
module _ {Γ : Ctx} {A₀ A B : VType} {ρ σ : _} {ε ε' : E}
         (e : Γ ᴱ ≡ [])
         (H : (op' : Op) → (ε₀ : E) → (Γ' : Ctx)
              → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op')
                   ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε₀)
                ⊢C⦂ B ‼ (op-grade op' ·ₑ ε₀))
         (M : Γ ⟨ ρ ⟩ ∷ A₀ ⊢C⦂ A ‼ ε)
         (N : Γ ⟨ σ ⟩ ∷ A ⊢C⦂ B ‼ ε')
         (ren : Ren (Γ ⟨ σ ⟩) ((Γ ⟨ ρ ⟩ ∷ A₀) ⟨ mapᵉ ε ⟩))
         (pM : Paramᶜ M) (pN : Paramᶜ N)
         (pH : ∀ op' ε₀ Γ' → Paramᶜ (H op' ε₀ Γ'))
         (uH : ∀ (op' : Op) {ε₁ ε₂} → (q : ε₁ ≾ₑ ε₂) → (Γ' : Ctx)
             → ⟦ H op' ε₂ Γ' ⟧ᶜᵗ (pH op' ε₂ Γ')
                 ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op') ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
             ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H op' ε₁ Γ' ⟧ᶜᵗ (pH op' ε₁ Γ'))
         (cH : CtxUniformʰ {Γ} H pH)
       where

  -- The reduct's clause family: `H` renamed along `ren-ᴱ-∷ A₀`, with the
  -- renamed parametricity and uniformity certificates.
  H' : (op' : Op) → (ε₀ : E) → (Γ' : Ctx)
     → ((Γ ⟨ ρ ⟩) ∷ A₀) ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op')
          ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε₀)
       ⊢C⦂ B ‼ (op-grade op' ·ₑ ε₀)
  H' op' ε₀ Γ' = C-rename (cong-ren (ren-ᴱ-∷ {Γ ⟨ ρ ⟩} A₀)) (H op' ε₀ Γ')

  pH' : ∀ op' ε₀ Γ' → Paramᶜ (H' op' ε₀ Γ')
  pH' op' ε₀ Γ' =
    renᶜ (cong-ren (ren-ᴱ-∷ {Γ ⟨ ρ ⟩} A₀)) (H op' ε₀ Γ') (pH op' ε₀ Γ')

  uH' = ren-clauses-uniform (ren-ᴱ-∷ {Γ ⟨ ρ ⟩} A₀) H pH uH

  -- `ren-clauses-ctxuniform` is stated for the *full* renaming (via `restrict-ren`);
  -- here the base renaming is `ren-ᴱ-∷ A₀ = restrict-ren (wk-ren)`, so transport
  -- the `wk-ren` instance along `ren-ᴱ-∷≡restrict`.
  cH' = subst (λ rr → CtxUniformʰ {(Γ ⟨ ρ ⟩) ∷ A₀}
                        (λ op' ε₀ Γ' → C-rename (cong-ren rr) (H op' ε₀ Γ'))
                        (λ op' ε₀ Γ' → renᶜ (cong-ren rr) (H op' ε₀ Γ') (pH op' ε₀ Γ')))
              (sym (ren-ᴱ-∷≡restrict A₀))
              (ren-clauses-ctxuniform (wk-ren {Γ = Γ ⟨ ρ ⟩} {A = A₀}) H pH cH)

  handle-op-cont :
      ⟦ handle M `with H' `in (C-rename (cong-∷-ren ren) N) ⟧ᶜᵗ
        (pM , renᶜ (cong-∷-ren ren) N pN , pH' , uH' , cH')
    ≈ᵐ (T-alg-of-handlerᵀ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H pH uH) ∘ᵐ ⟨ term∅ {Γ} e , idᵐ ⟩ᵐ)
       ∘ᵐ Tᶠ (⟦ N ⟧ᶜᵗ pN ∘ᵐ mapˣᵐ ⟦ ren ⟧ʳ idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ
  handle-op-cont =
      ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , seq-eq ⟩ᵐ-cong)
    ∙ ∘ᵐ-congˡ alg-nat
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)
    ∙ ∘ᵐ-congʳ (⟨ ∅-terminal {Γ} e _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
    ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _ ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
    ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    where
      f : ⟦ ((Γ ⟨ ρ ⟩) ∷ A₀) ᴱ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ
      f = ⟦ ren-ᴱ-∷ {Γ ⟨ ρ ⟩} A₀ ⟧ʳ

      -- the renamed sequel commutes back to the un-renamed one under `Tᶠ`
      seq-eq : Tᶠ (⟦ C-rename (cong-∷-ren ren) N ⟧ᶜᵗ (renᶜ (cong-∷-ren ren) N pN))
                 ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ
             ≈ᵐ Tᶠ (⟦ N ⟧ᶜᵗ pN ∘ᵐ mapˣᵐ ⟦ ren ⟧ʳ idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ
      seq-eq = ∘ᵐ-congˡ (T-congᶠ (C-rename-nat (cong-∷-ren ren) N pN))

      -- the `⟦_⟧ʰᵗ` adapter commutes past the eternal-parameter reindexing
      adapt-commute : ∀ {D D' P Q R Sₒ} → (g : D →ᵐ D') → (p : Q →ᵐ P) → (a : Sₒ →ᵐ R)
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

      -- the inner (renamed) handler equals the outer one reindexed by `f`
      ⟦H'⟧ʰᵗ-nat : ∀ op ε''
                 → clauseᵀ (⟦_⟧ʰᵗ {(Γ ⟨ ρ ⟩) ∷ A₀} H' pH' uH') op ε''
                 ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {Γ} H pH uH) op ε'' ∘ᵐ mapˣᵐ f idᵐ
      ⟦H'⟧ʰᵗ-nat op ε'' =
          ∘ᵐ-congˡ (C-rename-nat (cong-ren (ren-ᴱ-∷ {Γ ⟨ ρ ⟩} A₀))
                      (H op ε'' []) (pH op ε'' []))
        ∙ ∘ᵐ-assoc _ _ _
        ∙ ∘ᵐ-congʳ (adapt-commute _ _ _)
        ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

      alg-nat : T-alg-of-handlerᵀ (bcᴱ ((Γ ⟨ ρ ⟩) ∷ A₀)) (⟦_⟧ʰᵗ {(Γ ⟨ ρ ⟩) ∷ A₀} H' pH' uH')
              ≈ᵐ T-alg-of-handlerᵀ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H pH uH) ∘ᵐ mapˣᵐ f idᵐ
      f-necᵉ : ∀ {ρ₁} → [ ρ₁ ]ᶠ f ∘ᵐ Eternalᵒ.necᵉ (bcᴱ ((Γ ⟨ ρ ⟩) ∷ A₀))
                      ≈ᵐ Eternalᵒ.necᵉ (bcᴱ Γ) ∘ᵐ f
      f-necᵉ =
        subst (λ r → ∀ {ρ₁} → [ ρ₁ ]ᶠ ⟦ r ⟧ʳ ∘ᵐ Eternalᵒ.necᵉ (bcᴱ ((Γ ⟨ ρ ⟩) ∷ A₀))
                            ≈ᵐ Eternalᵒ.necᵉ (bcᴱ Γ) ∘ᵐ ⟦ r ⟧ʳ)
              (sym (ren-ᴱ-∷≡restrict A₀))
              (restrict-ren-necᵉ (wk-ren {Γ = Γ ⟨ ρ ⟩} {A = A₀}))

      alg-nat =
        T-alg-of-handlerᵀ-natᴾ (bcᴱ Γ) (bcᴱ ((Γ ⟨ ρ ⟩) ∷ A₀)) f f-necᵉ
          (⟦_⟧ʰᵗ {Γ} H pH uH) _ ⟦H'⟧ʰᵗ-nat
