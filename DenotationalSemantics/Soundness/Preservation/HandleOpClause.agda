------------------------------------------------------------------------
-- The handler-uniformity condition and the clause the semantics applies --
-- to a handled operation.                                               --
--                                                                      --
-- Split off from `Preservation` because it is interpretation-only (no    --
-- operational machinery) and its normalisation is heavy: keeping it in    --
-- its own module lets `Preservation` import `clause-sound` rather than    --
-- re-elaborate its body. `HANDLE-OP` fires the handler's clause at the    --
-- runtime context `Γ` (`Γ ᴱ ≡ []`); `CtxUniformʰ` says a clause's meaning --
-- is context-free, so applying it at `Γ` equals the model's `[]`-clause,  --
-- the eternal parameter carried terminally (`term∅`).                     --
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

module DenotationalSemantics.Soundness.Preservation.HandleOpClause
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

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types      S
open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.Renamings  S
open import Syntax.RenActions S using (C-rename)
open import Syntax.Substitutions S

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
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
  using (C-subst-nat; subst-clause-interp; eq-ren-irr; eq-ren-∷; subᶜ; substᴾᶜ)

infixr 3 _∙_
_∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
_∙_ = ≈ᵐ-trans

term∅ : ∀ {Γ X} → (e : Γ ᴱ ≡ []) → X →ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ
term∅ {X = X} e = subst (λ Δ → X →ᵐ ⟦ Δ ⟧ᶜᵗˣ) (sym e) terminalᵐ

∅-terminal : ∀ {Γ X} → (e : Γ ᴱ ≡ []) → (f g : X →ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ) → f ≈ᵐ g
∅-terminal {X = X} e =
  subst (λ Δ → (f g : X →ᵐ ⟦ Δ ⟧ᶜᵗˣ) → f ≈ᵐ g) (sym e)
        (λ f g → ≈ᵐ-trans terminalᵐ-unique (≈ᵐ-sym terminalᵐ-unique))

gty-cancelᵛ : ∀ {X Y Y'} → (e : Y ≡ Y') → (g : X →ᵐ Y)
            → subst (λ O → Y' →ᵐ O) (sym e) idᵐ ∘ᵐ subst (λ O → X →ᵐ O) e g ≈ᵐ g
gty-cancelᵛ refl g = ∘ᵐ-identityˡ _

-- `×ᵐ-assoc⁻¹` on a canonical pairing.
assoc⁻¹-⟨⟩ : ∀ {X A B C} → (a : X →ᵐ A) → (b : X →ᵐ B) → (c : X →ᵐ C)
           → ×ᵐ-assoc⁻¹ ∘ᵐ ⟨ a , ⟨ b , c ⟩ᵐ ⟩ᵐ ≈ᵐ ⟨ ⟨ a , b ⟩ᵐ , c ⟩ᵐ
assoc⁻¹-⟨⟩ a b c =
    ⟨⟩ᵐ-∘ _ _ _
  ∙ ⟨ ⟨⟩ᵐ-∘ _ _ _
      ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _
        , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-fstᵐ _ _ ⟩ᵐ-cong
    , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong

-- Uniformity of a clause family in the context extension `Γ'`: the clause does
-- not depend on `Γ'`, so its meaning factors through discarding it.
CtxUniformʰ : ∀ {Γ B} → Γ ᴱ ≡ []
            → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
                 → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                      ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                   ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
            → (∀ op ε'' Γ' → Paramᶜ (H op ε'' Γ'))
            → Set
CtxUniformʰ {Γ} e H pH = ∀ op ε'' Γ'
             → ⟦ H op ε'' Γ' ⟧ᶜᵗ (pH op ε'' Γ')
             ≈ᵐ ⟦ H op ε'' [] ⟧ᶜᵗ (pH op ε'' []) ∘ᵐ mapˣᵐ (mapˣᵐ (term∅ {Γ} e) idᵐ) idᵐ

-- Uniformity of a clause family in the residual effect `ε''`: the clause
-- commutes with sub-effecting the continuation's residual, landing on `·ₑ-monoʳ`.
EffUniformʰ : ∀ {Γ B}
            → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
                 → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                      ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                   ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
            → (∀ op ε'' Γ' → Paramᶜ (H op ε'' Γ'))
            → Set
EffUniformʰ H pH = ∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'') → (Γ' : Ctx)
             → ⟦ H op ε₂'' Γ' ⟧ᶜᵗ (pH op ε₂'' Γ')
                 ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
             ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H op ε₁'' Γ' ⟧ᶜᵗ (pH op ε₁'' Γ')

-- A handler is *parametric* when each clause's meaning is uniform in the two
-- indices the clause is externally quantified over. The two conjuncts have the
-- same shape — reindexing an index of the clause equals reindexing its meaning:
--
--   * `ctx-uniform` : `CtxUniformʰ` — uniform in the context extension `Γ'`.
--                     The meaning at `Γ'` factors through discarding `Γ'`
--                     (project to the `[]`-clause). This is precisely the former
--                     stand-alone assumption, now subsumed here.
--   * `eff-uniform` : `EffUniformʰ` — uniform in the residual effect `ε''`.
--                     Transported along `⟦_⟧ʰᵗ`'s adapter to the model handler
--                     `⟦ H ⟧ʰᵗ`, this is exactly the ambivalence premise that the
--                     handler-fold inner-grade law (`T-alg-of-handlerᵀ-≤ⁱ`) takes.
--
-- It is the single standing assumption on interpreted handlers: operational
-- soundness reads `ctx-uniform`, the denotational inner-grade reasoning reads
-- `eff-uniform`.
record Parametricʰ {Γ B} (e : Γ ᴱ ≡ [])
                   (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
                      → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                           ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                        ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                   (pH : ∀ op ε'' Γ' → Paramᶜ (H op ε'' Γ'))
                 : Set where
  field
    ctx-uniform : CtxUniformʰ {Γ} e H pH
    eff-uniform : EffUniformʰ {Γ} H pH

open Parametricʰ public

clause-sound : ∀ {Γ B ε''} → (e : Γ ᴱ ≡ []) → (op : Op)
             → (H : (op' : Op) → (ε' : E) → (Γ' : Ctx)
                  → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op')
                       ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε')
                    ⊢C⦂ B ‼ (op-grade op' ·ₑ ε'))
             → (pH : ∀ op' ε' Γ' → Paramᶜ (H op' ε' Γ'))
             → (par : Parametricʰ {Γ} e H pH)
             → (V : Γ ⊢V⦂ type-of-gtype (param op)) → (pV : Paramᵛ V)
             → (W : ⟦ Γ ⟧ᶜᵗˣ →ᵐ [ mapᵉ (op-grade op) ]ᵒ
                      (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ ⟦ B ⟧ᵛ ε''))
             → ⟦ (subst (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                                  ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                                ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                        (trans (cong (_++ᶜ Γ) e) ++ᶜ-identityˡ) (H op ε'' Γ))
                     [ Tl-∷ Hd ↦ V ]c ⟧ᶜᵗ
                 (subᶜ (subst (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                                        ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                                      ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                              (trans (cong (_++ᶜ Γ) e) ++ᶜ-identityˡ) (H op ε'' Γ))
                       (Tl-∷ Hd) V
                       (substᴾᶜ {D = [] ∷ type-of-gtype (param op)
                                        ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')}
                          (trans (cong (_++ᶜ Γ) e) ++ᶜ-identityˡ) (H op ε'' Γ) (pH op ε'' Γ))
                       pV)
                 ∘ᵐ ⟨ idᵐ
                    , [ mapᵉ (op-grade op) ]ᶠ
                        (map⇒ᵐ (subst (λ O → O →ᵐ ⟦ arity op ⟧ᵍ)
                                      (sym (ty-gty (arity op))) idᵐ) idᵐ)
                      ∘ᵐ W ⟩ᵐ
             ≈ᵐ (clauseᵀ (⟦_⟧ʰᵗ {Γ} H pH (eff-uniform par)) op ε''
                   ∘ᵐ ⟨ term∅ {Γ} e , idᵐ ⟩ᵐ)
                  ∘ᵐ ⟨ subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV)
                     , W ⟩ᵐ
clause-sound {Γ} {B} {ε''} e op H pH par V pV W =
    ∘ᵐ-congˡ (C-subst-nat Hcl (Tl-∷ Hd) V pHcl pV)
  ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ mid)
  ∙ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (mapˣᵐ-∘ _ _ _ _))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)
  ∙ ∘ᵐ-congʳ
      (⟨ ∘ᵐ-identityʳ _
         ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
         ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
       , ∘ᵐ-congˡ (∘ᵐ-identityˡ _) ∙ ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  -- the semantic clause unfolds through its adapter: the eternal parameter is
  -- terminal (`∅-terminal`), the associator rearranges the pairing
  -- (`assoc⁻¹-⟨⟩`), and the parameter's ground coercions cancel (`gty-cancelᵛ`)
  ∙ ≈ᵐ-sym
      (  ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
       ∙ ∘ᵐ-assoc _ _ _
       ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
       ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
           (⟨⟩ᵐ-∘ _ _ _
            ∙ ⟨ ∅-terminal {Γ} e _ (term∅ {Γ} e) , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (assoc⁻¹-⟨⟩ (term∅ {Γ} e) _ _))
       ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)
       ∙ ∘ᵐ-congʳ (⟨ mapˣᵐ-∘⟨⟩ _ _ _ _
                     ∙ ⟨ ∘ᵐ-identityˡ _
                       , gty-cancelᵛ (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV) ⟩ᵐ-cong
                   , ≈ᵐ-refl ⟩ᵐ-cong))
  where
    pt = type-of-gtype (param op)
    kt = [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
    eq : Γ ᴱ ++ᶜ Γ ≡ Γ
    eq = trans (cong (_++ᶜ Γ) e) ++ᶜ-identityˡ
    Hcl = subst (λ Γ₀ → Γ₀ ∷ pt ∷ kt ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')) eq (H op ε'' Γ)
    pHcl = substᴾᶜ {D = [] ∷ pt ∷ kt} eq (H op ε'' Γ) (pH op ε'' Γ)
    mid : ⟦ Hcl ⟧ᶜᵗ pHcl
        ≈ᵐ ⟦ H op ε'' [] ⟧ᶜᵗ (pH op ε'' []) ∘ᵐ mapˣᵐ (mapˣᵐ (term∅ {Γ} e) idᵐ) idᵐ
    mid =
        subst-clause-interp {D = [] ∷ pt ∷ kt} eq (H op ε'' Γ) (pH op ε'' Γ)
      ∙ ∘ᵐ-congˡ (ctx-uniform par op ε'' Γ)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ
          (   ∘ᵐ-congʳ (eq-ren-irr (cong (_++ᶜ ([] ∷ pt ∷ kt)) eq)
                                   (cong (_∷ kt) (cong (_∷ pt) eq))
                        ∙ eq-ren-∷ (cong (_∷ pt) eq)
                        ∙ mapˣᵐ-cong (eq-ren-∷ eq) ≈ᵐ-refl)
            ∙ mapˣᵐ-∘ _ _ _ _
            ∙ mapˣᵐ-cong
                (mapˣᵐ-∘ _ _ _ _
                 ∙ mapˣᵐ-cong (∅-terminal {Γ} e _ _) (∘ᵐ-identityˡ _))
                (∘ᵐ-identityˡ _))

