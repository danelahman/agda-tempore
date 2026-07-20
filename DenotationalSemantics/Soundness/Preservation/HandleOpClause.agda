------------------------------------------------------------------------
-- The handler-uniformity condition and the clause the semantics applies --
-- to a handled operation.                                               --
--                                                                      --
-- Split off from `Preservation` because it is interpretation-only (no    --
-- operational machinery) and its normalisation is heavy: keeping it in    --
-- its own module lets `Preservation` import `clause-sound` rather than    --
-- re-elaborate its body. `HANDLE-OP` fires the handler's clause at the    --
-- runtime context `Γ` (`Γ ᴱ ≡ []`); `CtxUniformʰ` — naturality in the      --
-- extension — says a clause reads nothing of it, so applying it at `Γ`     --
-- equals the model's `[]`-clause, the eternal parameter carried            --
-- terminally (`term∅`).                                                    --
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

-- HANDLER UNIFORMITY, IN ONE SHAPE
--
-- A clause is quantified over two indices, the context extension `Γ'` and the
-- residual effect `ε''`, and its interpretation
--
--   ⟦ H op ε'' Γ' ⟧ᶜᵗ : ⟦ Γ ᴱ ++ᶜ Γ' ∷ pt ∷ kt ε'' ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ B ⟧ᵛ (op-grade op ·ₑ ε'')
--
-- is a functor of both: covariant in `ε''` in the domain (the continuation's
-- residual) and in the codomain (the clause's own effect), covariant in `Γ'` in
-- the domain and *constant* in `Γ'` in the codomain.
--
-- Uniformity is naturality in these indices: reindexing an index of the clause
-- is reindexing its meaning. `Uniformʰ` is the single square, moving both at
-- once; `EffUniformʰ` and `CtxUniformʰ` are its two instances (`ρ = idᵐ`, resp.
-- `q = ≾ₑ-refl`), and `uniformʰ` pastes them back together. The `Γ'` square has
-- no coercion on the right precisely because the codomain is constant there.

Uniformʰ : ∀ {Γ B}
         → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
              → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                   ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
         → (∀ op ε'' Γ' → Paramᶜ (H op ε'' Γ'))
         → Set
Uniformʰ {Γ} H pH =
  ∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'') → {Γ' Γ'' : Ctx}
    → (ρ : ⟦ Γ ᴱ ++ᶜ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ ᴱ ++ᶜ Γ'' ⟧ᶜᵗˣ)
  → ⟦ H op ε₂'' Γ'' ⟧ᶜᵗ (pH op ε₂'' Γ'')
      ∘ᵐ mapˣᵐ (mapˣᵐ ρ idᵐ) ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
  ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H op ε₁'' Γ' ⟧ᶜᵗ (pH op ε₁'' Γ')

-- Naturality in the context extension `Γ'`. Quantifying over an arbitrary
-- reindexing `ρ` is what says the clause reads nothing of `Γ'`; it is
-- satisfiable exactly when `⟦ Γ ᴱ ⟧ᶜᵗˣ` is terminal, i.e. for the runtime
-- contexts (`Γ ᴱ ≡ []`) that `HANDLE-OP` fires a clause in. Taking `Γ'' = []`
-- and `ρ = term∅` recovers the `[]`-clause the model uses (`ctx-uniform-[]`);
-- conversely that instance implies all the others, by terminal uniqueness.

CtxUniformʰ : ∀ {Γ B}
            → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
                 → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                      ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                   ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
            → (∀ op ε'' Γ' → Paramᶜ (H op ε'' Γ'))
            → Set
CtxUniformʰ {Γ} H pH =
  ∀ (op : Op) (ε'' : E) {Γ' Γ'' : Ctx}
    → (ρ : ⟦ Γ ᴱ ++ᶜ Γ' ⟧ᶜᵗˣ →ᵐ ⟦ Γ ᴱ ++ᶜ Γ'' ⟧ᶜᵗˣ)
  → ⟦ H op ε'' Γ'' ⟧ᶜᵗ (pH op ε'' Γ'') ∘ᵐ mapˣᵐ (mapˣᵐ ρ idᵐ) idᵐ
  ≈ᵐ ⟦ H op ε'' Γ' ⟧ᶜᵗ (pH op ε'' Γ')

-- Reindexing an exponential by an identity-up-to-`≈ᵐ` map is the identity.
map⇒ᵐ-id : ∀ {A B} {h : B →ᵐ B} → h ≈ᵐ idᵐ → map⇒ᵐ (idᵐ {A}) h ≈ᵐ idᵐ
map⇒ᵐ-id h≈ =
    curryᵐ-cong (  ∘ᵐ-congˡ h≈
                 ∙ ∘ᵐ-identityˡ _
                 ∙ ∘ᵐ-congʳ mapˣᵐ-idᵐ
                 ∙ ∘ᵐ-identityʳ _)
  ∙ uncurryᵐ-curryᵐ-iso idᵐ

-- The two instances, and the paste that recovers the joint square: reindex the
-- extension first (at `ε₂''`), then the residual (at `Γ'`).

uniformʰ-eff : ∀ {Γ B H pH} → Uniformʰ {Γ} {B} H pH → EffUniformʰ {Γ} H pH
uniformʰ-eff u op q Γ' =
    ∘ᵐ-congʳ (mapˣᵐ-cong (≈ᵐ-sym mapˣᵐ-idᵐ) ≈ᵐ-refl)
  ∙ u op q {Γ'} {Γ'} idᵐ

uniformʰ-ctx : ∀ {Γ B H pH} → Uniformʰ {Γ} {B} H pH → CtxUniformʰ {Γ} H pH
uniformʰ-ctx u op ε'' ρ =
    ∘ᵐ-congʳ (mapˣᵐ-cong ≈ᵐ-refl
                (≈ᵐ-sym (  []-congᶠ (map⇒ᵐ-id (T-≤-refl ≾ₑ-refl))
                         ∙ []-idᵐ)))
  ∙ u op ≾ₑ-refl ρ
  ∙ ∘ᵐ-congˡ (T-≤-refl _)
  ∙ ∘ᵐ-identityˡ _

uniformʰ : ∀ {Γ B H pH}
         → EffUniformʰ {Γ} {B} H pH → CtxUniformʰ {Γ} H pH → Uniformʰ {Γ} H pH
uniformʰ {pH = pH} ue uc op q {Γ'} {Γ''} ρ =
    ∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘ _ _ _ _
                      ∙ mapˣᵐ-cong (∘ᵐ-identityʳ _) (∘ᵐ-identityˡ _)))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (uc op _ ρ)
  ∙ ue op q Γ'

-- The `[]`-instance the model's clause is read at.

ctx-uniform-[] : ∀ {Γ B} → (e : Γ ᴱ ≡ [])
               → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
                    → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                      ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
               → (pH : ∀ op ε'' Γ' → Paramᶜ (H op ε'' Γ'))
               → CtxUniformʰ {Γ} H pH
               → ∀ op ε'' Γ'
               → ⟦ H op ε'' Γ' ⟧ᶜᵗ (pH op ε'' Γ')
               ≈ᵐ ⟦ H op ε'' [] ⟧ᶜᵗ (pH op ε'' [])
                    ∘ᵐ mapˣᵐ (mapˣᵐ (term∅ {Γ} e) idᵐ) idᵐ
ctx-uniform-[] {Γ} e H pH u op ε'' Γ' = ≈ᵐ-sym (u op ε'' (term∅ {Γ} e))

-- … and conversely, so the naturality form is exactly the old `[]`-form, not a
-- stronger assumption: any two maps into `⟦ Γ ᴱ ⟧ᶜᵗˣ` agree (`∅-terminal`), so
-- reindexing by an arbitrary `ρ` first changes nothing.

ctx-uniform-from-[] : ∀ {Γ B} → (e : Γ ᴱ ≡ [])
                    → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
                         → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                           ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                    → (pH : ∀ op ε'' Γ' → Paramᶜ (H op ε'' Γ'))
                    → (∀ op ε'' Γ'
                         → ⟦ H op ε'' Γ' ⟧ᶜᵗ (pH op ε'' Γ')
                         ≈ᵐ ⟦ H op ε'' [] ⟧ᶜᵗ (pH op ε'' [])
                              ∘ᵐ mapˣᵐ (mapˣᵐ (term∅ {Γ} e) idᵐ) idᵐ)
                    → CtxUniformʰ {Γ} H pH
ctx-uniform-from-[] {Γ} e H pH u₀ op ε'' ρ =
    ∘ᵐ-congˡ (u₀ op ε'' _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘ _ _ _ _
              ∙ mapˣᵐ-cong (  mapˣᵐ-∘ _ _ _ _
                            ∙ mapˣᵐ-cong (∅-terminal {Γ} e _ _) (∘ᵐ-identityˡ _))
                           (∘ᵐ-identityˡ _))
  ∙ ≈ᵐ-sym (u₀ op ε'' _)

-- The `[]`-instance derived from the TOTAL parametricity certificate: at a
-- runtime config (`Γ ᴱ ≡ []`) the lifted terminal map `Γ ⋉ terminalᵐ` and the
-- terminal factoring `term∅` agree by `∅-terminal`, so the naturality square
-- collapses to exactly the `[]`-clause the model reads. This is what lets
-- `CtxParamʰ` (in `Paramᶜ`) replace the runtime-only `CtxUniformʰ` premise.
ctx-param-[] : ∀ {Γ B} → (e : Γ ᴱ ≡ [])
             → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
                  → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                       ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                    ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
             → (pH : ∀ op ε'' Γ' → Paramᶜ (H op ε'' Γ'))
             → CtxParamʰ {Γ} H pH
             → ∀ op ε'' Γ'
             → ⟦ H op ε'' Γ' ⟧ᶜᵗ (pH op ε'' Γ')
             ≈ᵐ ⟦ H op ε'' [] ⟧ᶜᵗ (pH op ε'' [])
                  ∘ᵐ mapˣᵐ (mapˣᵐ (term∅ {Γ} e) idᵐ) idᵐ
ctx-param-[] {Γ} e H pH cH op ε'' Γ' =
  ≈ᵐ-sym (  ∘ᵐ-congʳ (mapˣᵐ-cong (mapˣᵐ-cong (∅-terminal {Γ} e _ _) ≈ᵐ-refl) ≈ᵐ-refl)
          ∙ cH op ε'' {Γ'} {[]} (terminalᵐ {⟦ Γ' ⟧ᶜᵗˣ}))

clause-sound : ∀ {Γ B ε''} → (e : Γ ᴱ ≡ []) → (op : Op)
             → (H : (op' : Op) → (ε' : E) → (Γ' : Ctx)
                  → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op')
                       ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε')
                    ⊢C⦂ B ‼ (op-grade op' ·ₑ ε'))
             → (pH : ∀ op' ε' Γ' → Paramᶜ (H op' ε' Γ'))
             → (uH : EffUniformʰ {Γ} H pH)
             → (u : CtxUniformʰ {Γ} H pH)
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
             ≈ᵐ (clauseᵀ (⟦_⟧ʰᵗ {Γ} H pH uH) op ε''
                   ∘ᵐ ⟨ term∅ {Γ} e , idᵐ ⟩ᵐ)
                  ∘ᵐ ⟨ subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV)
                     , W ⟩ᵐ
clause-sound {Γ} {B} {ε''} e op H pH uH u V pV W =
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
      ∙ ∘ᵐ-congˡ (ctx-uniform-[] {Γ = Γ} e H pH u op ε'' Γ)
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

