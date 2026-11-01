-------------------------------------------------------------------------
-- Soundness of the subsumption equations.                             --
-- A subsumption denotes the coercion `⟦_⟧<:ᵛ`/`⟦_⟧<:ᶜ`; each equation --
-- is a law of that coercion: `subV`/`subC-refl` and `-trans` its      --
-- functoriality, `subC-perform`/`-delay` the naturality and           --
-- sub-effecting of `opᵀ`/`delayᵀ`, and `subC-seq`/`-handle` are       --
-- `strᵀ-≤` then `T-≤-μᵀ` resp. `T-alg-of-handlerᵀ-≤`, crossing the    --
-- modality via `η⊣-≤` and the binder via `subCtx-str`.                --
-------------------------------------------------------------------------

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

module MonomorphicCalculus.EquationalTheory.Soundness.Coerce
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

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Types           S
open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Renaming.Action S using (C-rename)

open import MonomorphicCalculus.EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-∘ᵐ; []-congᶠ; []-≤)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-≤)
open Adjunction Adj using (η⊣; η⊣-≤)
open GroundTypes GTy
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE

open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (⟨⊤⟩-eternalᵒ)

open import MonomorphicCalculus.Syntax.Substitution.Subsumption  S using (subCtx)
open import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Base S Cat Fut Pst Adj GTy Mon GE
       using (subCtxᴾ; subCtx-nat)
open import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Step S Cat Fut Pst Adj GTy Mon GE
       using (subCtx-str)

open import MonomorphicCalculus.EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE

-- Postcomposition commutes with a transport in the second component of a
-- morphism's product domain (the `ty-gty` coercion of an operation's arity).

substᵈ-post : ∀ {X Z Z' A B} → (e : A ≡ B) → (h : Z →ᵐ Z') → (g : (X ×ᵐ A) →ᵐ Z)
            → h ∘ᵐ subst (λ O → (X ×ᵐ O) →ᵐ Z) e g
            ≡ subst (λ O → (X ×ᵐ O) →ᵐ Z') e (h ∘ᵐ g)
substᵈ-post refl h g = refl

-- The exponential's action on the codomain composes.

map⇒ᵐ-fuse : ∀ {A C D D'} → (g : C →ᵐ D) → (g' : D →ᵐ D')
           → map⇒ᵐ (idᵐ {A}) g' ∘ᵐ map⇒ᵐ idᵐ g ≈ᵐ map⇒ᵐ idᵐ (g' ∘ᵐ g)
map⇒ᵐ-fuse g g' =
    ≈ᵐ-sym (map⇒ᵐ-∘ idᵐ idᵐ g g')
  ∙ map⇒ᵐ-cong (∘ᵐ-identityˡ idᵐ) ≈ᵐ-refl

-- A coercion of the result escapes an operation node: the effect half by
-- `opᵀ-≤`, the value half by `opᵀ-nat`.

opᵀ-push : ∀ {X A B ε ε'} → (op : Op)
         → (v : X →ᵐ ⟦ param op ⟧ᵍ)
         → (k : X →ᵐ [ ∣ op-grade op ∣ᵉ ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ A ε))
         → (h : A →ᵐ B) → (q : ε ≾ₑ ε')
         → (Tᶠ h ∘ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q)) ∘ᵐ opᵀ {A} {ε} op ∘ᵐ ⟨ v , k ⟩ᵐ
         ≈ᵐ opᵀ {B} {ε'} op
              ∘ᵐ ⟨ v
                 , [ ∣ op-grade op ∣ᵉ ]ᶠ (map⇒ᵐ idᵐ (Tᶠ h ∘ᵐ T-≤ q)) ∘ᵐ k ⟩ᵐ
opᵀ-push op v k h q =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym (opᵀ-≤ op q))
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                          ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (opᵀ-nat op h))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ ∘ᵐ-identityˡ _
                ,   ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym ([]-∘ᵐ _ _)
                              ∙ []-congᶠ (map⇒ᵐ-fuse (T-≤ q) (Tᶠ h))) ⟩ᵐ-cong)

-- The same for a delay: `delayᵀ-≤` and `delayᵀ-nat`.

delayᵀ-push : ∀ {X A B ε ε'} → (τ : 𝔻)
            → (k : X →ᵐ [ ιᵣ τ ]ᵒ (Tᵒ A ε))
            → (h : A →ᵐ B) → (q : ε ≾ₑ ε')
            → (Tᶠ h ∘ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q)) ∘ᵐ delayᵀ {A} {ε} τ ∘ᵐ k
            ≈ᵐ delayᵀ {B} {ε'} τ ∘ᵐ [ ιᵣ τ ]ᶠ (Tᶠ h ∘ᵐ T-≤ q) ∘ᵐ k
delayᵀ-push τ k h q =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym (delayᵀ-≤ τ q))
              ∙ ∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (delayᵀ-nat τ h))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))

-- Sub-effecting at the outer type is the coercion of a reflexive witness,
-- which `⟦⟧<:ᵛ-refl` collapses.

coe-refl-≈ : ∀ {X ε ε'} → (A : VType) → (q : ε ≾ₑ ε') → (m : X →ᵐ Tᵒ ⟦ A ⟧ᵛ ε)
           → T-≤ q ∘ᵐ m ≈ᵐ ⟦ <:ᵛ-refl A !ₛ q ⟧<:ᶜ ∘ᵐ m
coe-refl-≈ A q m =
  ∘ᵐ-congˡ (≈ᵐ-sym (  ∘ᵐ-congˡ (T-congᶠ (⟦⟧<:ᵛ-refl A) ∙ T-idᵐ)
                    ∙ ∘ᵐ-identityˡ _))


-- Functoriality

sound-subV-refl : ∀ {Γ A} → (w : A <:ᵛ A) → (V : Γ ⊢ᵛ⦂ A)
                → Soundᵛ≡ᵗʰ (subV-refl w V)
sound-subV-refl w V pL pR =
  ∘ᵐ-congˡ (⟦⟧<:ᵛ-id w) ∙ ∘ᵐ-identityˡ _ ∙ ⟦⟧ᵛᵗ-irr V pL pR

sound-subV-trans : ∀ {Γ A₁ A₂ A₃}
                 → (w : A₁ <:ᵛ A₂) → (w' : A₂ <:ᵛ A₃) → (w'' : A₁ <:ᵛ A₃)
                 → (V : Γ ⊢ᵛ⦂ A₁)
                 → Soundᵛ≡ᵗʰ (subV-trans w w' w'' V)
sound-subV-trans w w' w'' V pL pR =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟦⟧<:ᵛ-trans w w') ∙ ⟦⟧<:ᵛ-irr (<:ᵛ-trans w w') w'')
  ∙ ∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr V pL pR)

sound-subC-refl : ∀ {Γ C} → (w : C <:ᶜ C) → (M : Γ ⊢ᶜ⦂ C)
                → Soundᶜ≡ᵗʰ (subC-refl w M)
sound-subC-refl w M pL pR =
  ∘ᵐ-congˡ (⟦⟧<:ᶜ-id w) ∙ ∘ᵐ-identityˡ _ ∙ ⟦⟧ᶜᵗ-irr M pL pR

sound-subC-trans : ∀ {Γ C₁ C₂ C₃}
                 → (w : C₁ <:ᶜ C₂) → (w' : C₂ <:ᶜ C₃) → (w'' : C₁ <:ᶜ C₃)
                 → (M : Γ ⊢ᶜ⦂ C₁)
                 → Soundᶜ≡ᵗʰ (subC-trans w w' w'' M)
sound-subC-trans w w' w'' M pL pR =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟦⟧<:ᶜ-trans w w') ∙ ⟦⟧<:ᶜ-irr (<:ᶜ-trans w w') w'')
  ∙ ∘ᵐ-congʳ (⟦⟧ᶜᵗ-irr M pL pR)


-- Naturality in the value formers: functoriality of `_|×|_`, `_|+|_`, `list`
-- and `_⇒_`

sound-subV-pair : ∀ {Γ A A' B B'}
                → (p : A <:ᵛ A') → (q : B <:ᵛ B')
                → (V : Γ ⊢ᵛ⦂ A) → (W : Γ ⊢ᵛ⦂ B)
                → Soundᵛ≡ᵗʰ (subV-pair p q V W)
sound-subV-pair p q V W (pV , pW) (pV' , pW') =
    mapˣᵐ-∘⟨⟩ _ _ _ _
  ∙ ⟨ ∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr V pV pV')
    , ∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr W pW pW') ⟩ᵐ-cong

sound-subV-inl : ∀ {Γ A A' B B'}
               → (p : A <:ᵛ A') → (q : B <:ᵛ B')
               → (V : Γ ⊢ᵛ⦂ A)
               → Soundᵛ≡ᵗʰ (subV-inl p q V)
sound-subV-inl p q V pV pV' =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ ([]ᵐ-inlᵐ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr V pV pV'))

sound-subV-nil : ∀ {Γ A A'} → (p : A <:ᵛ A')
               → Soundᵛ≡ᵗʰ (subV-nil {Γ = Γ} p)
sound-subV-nil p pV pV' =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (mapListᵐ-nil _)

sound-subV-cons : ∀ {Γ A A'} → (p : A <:ᵛ A')
                → (V : Γ ⊢ᵛ⦂ A) → (W : Γ ⊢ᵛ⦂ list A)
                → Soundᵛ≡ᵗʰ (subV-cons p V W)
sound-subV-cons p V W (pV , pW) (pV' , pW') =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (mapListᵐ-cons _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ ( mapˣᵐ-∘⟨⟩ _ _ _ _
             ∙ ⟨ ∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr V pV pV') , ∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr W pW pW') ⟩ᵐ-cong)

sound-subV-inr : ∀ {Γ A A' B B'}
               → (p : A <:ᵛ A') → (q : B <:ᵛ B')
               → (V : Γ ⊢ᵛ⦂ B)
               → Soundᵛ≡ᵗʰ (subV-inr p q V)
sound-subV-inr p q V pV pV' =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ ([]ᵐ-inrᵐ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟦⟧ᵛᵗ-irr V pV pV'))

sound-subV-fun : ∀ {Γ A A' C C'}
               → (p : A' <:ᵛ A) → (w : C <:ᶜ C')
               → (M : Γ ∷ A ⊢ᶜ⦂ C)
               → Soundᵛ≡ᵗʰ (subV-fun p w M)
sound-subV-fun p w M pM pR =
    map⇒ᵐ-curryᵐˡʳ ⟦ p ⟧<:ᵛ ⟦ w ⟧<:ᶜ (⟦ M ⟧ᶜᵗ pM)
  ∙ curryᵐ-cong (∘ᵐ-congʳ
      (≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (subCtx p M) pR (subCtxᴾ p M pM)
               ∙ subCtx-nat p M pM)))


-- Naturality in the Fitch formers: both are precomposition, so the coercion
-- passes by associativity alone.

sound-subC-box : ∀ {Γ A C C' ρ}
               → (w : C <:ᶜ C')
               → (V : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A)
               → (M : Γ ∷ [ ρ ] A ⊢ᶜ⦂ C)
               → Soundᶜ≡ᵗʰ (subC-box w V M)
sound-subC-box w V M (pV , pM) (pV' , pM') =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-cong (∘ᵐ-congʳ (⟦⟧ᶜᵗ-irr M pM pM'))
            (⟨ ≈ᵐ-refl
             , ∘ᵐ-congˡ ([]-congᶠ (⟦⟧ᵛᵗ-irr V pV pV')) ⟩ᵐ-cong)

sound-subC-unbox : ∀ {Γ A A₀ C C' ρ₀ ρ'}
                 → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ)
                 → (rel : ρ' ≾ᵣ ρ₀)
                 → (v : A₀ <:ᵛ A)
                 → (w : C <:ᶜ C')
                 → (M : Γ ∷ A ⊢ᶜ⦂ C)
                 → Soundᶜ≡ᵗʰ (subC-unbox x rel v w M)
sound-subC-unbox x rel v w M pM pM' =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (⟦⟧ᶜᵗ-irr M pM pM'))


-- Sub-effecting the result of a bind is the multiplication's inner-grade law.

sound-coerce-seq-in : ∀ {Γ A B ε ε₁' ε₂'}
                    → (rel : ε₁' ≾ₑ ε₂')
                    → (M : Γ ⊢ᶜ⦂ A ! ε)
                    → (N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε₁')
                    → Soundᶜ≡ᵗʰ (coerce-seq-in rel M N)
sound-coerce-seq-in {B = B} rel M N (pM , pN) (pM' , pN') =
    ≈ᵐ-sym (coe-refl-≈ B (·ₑ-monoʳ-≾ₑ rel) _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (T-≤-μᵀⁱ rel))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)))
  ∙ ∘ᵐ-congʳ (  ∘ᵐ-congˡ (T-congᶠ (  ∘ᵐ-congʳ (⟦⟧ᶜᵗ-irr N pN pN')
                                   ∙ coe-refl-≈ B rel (⟦ N ⟧ᶜᵗ pN')))
              ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ⟦⟧ᶜᵗ-irr M pM pM' ⟩ᵐ-cong)))


-- Applying a coerced handler value: `curryʰ-nat`, then `curryʰ-β`.

app-mapʰ : ∀ {X A A' ε ε₂ B B' ε' ε₂' ε₀}
         → (p : ε₀ ≾ₑ ε₂) → (a : A' →ᵐ A) → (b : B →ᵐ B')
         → (r : ε₂ ≾ₑ ε) → (s : ε' ≾ₑ ε₂')
         → (k : X →ᵐ Hᵒ A ε B ε') → (m : X →ᵐ Tᵒ A' ε₀)
         → appʰ p ∘ᵐ ⟨ mapʰ a b r s ∘ᵐ k , m ⟩ᵐ
         ≈ᵐ Tᶠ b ∘ᵐ T-≤ (·ₑ-monoʳ-≾ₑ s) ∘ᵐ appʰ (≾ₑ-trans p r)
              ∘ᵐ ⟨ k , Tᶠ a ∘ᵐ m ⟩ᵐ
app-mapʰ p a b r s k m =
    ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ
      ( ∘ᵐ-congʳ (mapˣᵐ-cong (curryʰ-nat (mapʰ-fam a b r s) (mapʰ-fam-nat a b r s) k)
                             ≈ᵐ-refl)
      ∙ curryʰ-β (λ e → mapʰ-fam a b r s e ∘ᵐ mapˣᵐ k idᵐ)
                 (Naturalʰ-∘ (mapʰ-fam-nat a b r s) k) p)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ ( ∘ᵐ-assoc _ _ _
             ∙ ∘ᵐ-congʳ ( ∘ᵐ-assoc _ _ _
                        ∙ ∘ᵐ-congʳ ( mapˣᵐ-∘⟨⟩ _ _ _ _
                                   ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))

-- Handling with a coerced handler value is `app-mapʰ` at the reflexive index.

sound-subV-handle : ∀ {Γ A A₁ B B₁ ε ε' ε₁'}
                  → (p : A <:ᵛ A₁) → (pε : ε ≾ₑ ε)
                  → (q : B₁ <:ᵛ B) → (s : ε₁' ≾ₑ ε')
                  → (M : Γ ⊢ᶜ⦂ A ! ε)
                  → (V : Γ ⊢ᵛ⦂ (A₁ ! ε) ⇛ (B₁ ! ε₁'))
                  → Soundᶜ≡ᵗʰ (subV-handle p pε q s M V)
sound-subV-handle p pε q s M V (pM , pV) (pM' , pV') =
    app-mapʰ ≾ₑ-refl ⟦ p ⟧<:ᵛ ⟦ q ⟧<:ᵛ pε s (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM)
  ∙ ≈ᵐ-sym (  ∘ᵐ-assoc _ _ _
            ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
                (∘ᵐ-cong (appʰ-irr _ _)
                         ⟨ ⟦⟧ᵛᵗ-irr V pV' pV
                         ,   ∘ᵐ-congˡ (∘ᵐ-congʳ (T-≤-refl _) ∙ ∘ᵐ-identityʳ _)
                           ∙ ∘ᵐ-congʳ (⟦⟧ᶜᵗ-irr M pM' pM) ⟩ᵐ-cong)))

-- Commutation with the effect formers

sound-subC-perform : ∀ {Γ A A' ε ε' op}
                   → (w : A <:ᵛ A')
                   → (rel : ε ≾ₑ ε')
                   → (V : Γ ⊢ᵛ⦂ ⌜ param op ⌝ᵍ)
                   → (M : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ
                          ⊢ᶜ⦂ A ! ε)
                   → Soundᶜ≡ᵗʰ (subC-perform w rel V M)
sound-subC-perform {op = op} w rel V M (pV , pM) (pV' , pM') =
    ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ substᶜ-≈ (ty-gty (param op)) (⟦⟧ᵛᵗ-irr V pV pV')
                        , ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                            (substᵈ-≈ (ty-gty (arity op)) (⟦⟧ᶜᵗ-irr M pM pM'))))
                        ⟩ᵐ-cong))
  ∙ opᵀ-push op _ _ ⟦ w ⟧<:ᵛ rel
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
              ,   ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym ([]-∘ᵐ _ _)
                            ∙ []-congᶠ (  map⇒ᵐ-curryᵐ _ _
                                        ∙ curryᵐ-cong (≡→≈ᵐ (substᵈ-post
                                            (ty-gty (arity op))
                                            ⟦ w !ₛ rel ⟧<:ᶜ
                                            (⟦ M ⟧ᶜᵗ pM'))))) ⟩ᵐ-cong)

sound-subC-delay : ∀ {Γ A A' τ ε ε'}
                 → (w : A <:ᵛ A')
                 → (rel : ε ≾ₑ ε')
                 → (M : Γ ⟨ ιᵣ τ ⟩ ⊢ᶜ⦂ A ! ε)
                 → Soundᶜ≡ᵗʰ (subC-delay w rel M)
sound-subC-delay {τ = τ} w rel M pM pM' =
    ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (⟦⟧ᶜᵗ-irr M pM pM'))))
  ∙ delayᵀ-push τ _ ⟦ w ⟧<:ᵛ rel
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))


-- Commutation with a bind: the coercion of the scrutinee crosses the modality
-- and the binder, and lands outside as sub-effecting of the composite.

-- The continuation lives under the modality the coercion relaxes; transposes
-- across it.

coe-str : ∀ {Γ A B ε₁ ε₂ ε'}
        → (rel : ε₁ ≾ₑ ε₂)
        → (N : Γ ⟨ ∣ ε₂ ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε')
        → (pN : Paramᶜ N)
        → (m : ⟦ Γ ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ A ⟧ᵛ ε₁)
        →    Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , T-≤ rel ∘ᵐ m ⟩ᵐ
        ≈ᵐ T-≤ rel
             ∘ᵐ Tᶠ (⟦ C-rename (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N ⟧ᶜᵗ
                      (renᶜ (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N pN))
             ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ
coe-str rel N pN m =
    ∘ᵐ-congʳ (  ∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                  ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (strᵀ-≤ rel)
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                      ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-≤-nat _ rel)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ∘ᵐ-congʳ (  ∘ᵐ-congʳ (⟨ η⊣-≤ (map-monotoneᵉ rel) , ≈ᵐ-refl ⟩ᵐ-cong)
                          ∙ ∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                              ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
                          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                          ∙ ∘ᵐ-congˡ (≈ᵐ-sym (strᵀ-natˡ _))
                          ∙ ∘ᵐ-assoc _ _ _)
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym (T-∘ᵐ _ _)
                          ∙ T-congᶠ (≈ᵐ-sym (C-rename-nat _ N pN))))

sound-subC-seq : ∀ {Γ A A' B ε₁ ε₂ ε'}
               → (w : A <:ᵛ A')
               → (rel : ε₁ ≾ₑ ε₂)
               → (M : Γ ⊢ᶜ⦂ A ! ε₁)
               → (N : Γ ⟨ ∣ ε₂ ∣ᵉ ⟩ ∷ A' ⊢ᶜ⦂ B ! ε')
               → Soundᶜ≡ᵗʰ (subC-seq w rel M N)
sound-subC-seq {B = B} w rel M N (pM , pN) (pM' , pR) =
    ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (⟨ ≈ᵐ-refl
         ,   ∘ᵐ-congʳ (⟦⟧ᶜᵗ-irr M pM pM')
           ∙ ∘ᵐ-congˡ (T-≤-nat ⟦ w ⟧<:ᵛ rel)
           ∙ ∘ᵐ-assoc _ _ _ ⟩ᵐ-cong)))
  ∙ ∘ᵐ-congʳ (coe-str rel N pN (Tᶠ ⟦ w ⟧<:ᵛ ∘ᵐ ⟦ M ⟧ᶜᵗ pM'))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (subCtx-str {t = w} (C-rename r N)
                                 (renᶜ r N pN) η⊣ (⟦ M ⟧ᶜᵗ pM'))))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-≤-μᵀ rel)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
      (⟦⟧ᶜᵗ-irr (subCtx w (C-rename r N))
                (subCtxᴾ w (C-rename r N) (renᶜ r N pN)) pR))))
  ∙ coe-refl-≈ B (·ₑ-monoˡ-≾ₑ rel) _
  where
    r = cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))

-- Moving the handled computation's subsumption onto the handler value: both
-- sides are the application at the smaller index (`appʰ-nat`).

sound-subC-handle : ∀ {Γ A A' B ε₁ ε₂ ε'}
                  → (w : A <:ᵛ A')
                  → (rel : ε₁ ≾ₑ ε₂)
                  → (M : Γ ⊢ᶜ⦂ A ! ε₁)
                  → (V : Γ ⊢ᵛ⦂ (A' ! ε₂) ⇛ (B ! ε'))
                  → Soundᶜ≡ᵗʰ (subC-handle w rel M V)
sound-subC-handle {B = B} {ε' = ε'} w rel M V (pM , pV) (pM' , pV') =
    ∘ᵐ-congʳ (  ⟨ ≈ᵐ-refl , ∘ᵐ-congˡ (T-≤-nat ⟦ w ⟧<:ᵛ rel) ∙ ∘ᵐ-assoc _ _ _ ⟩ᵐ-cong
              ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (appʰ-nat rel ≾ₑ-refl rel)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ≈ᵐ-sym (  ≈ᵐ-sym (coe-refl-≈ B (·ₑ-monoˡ-≾ₑ rel) _)
            ∙ ∘ᵐ-congʳ (  app-mapʰ ≾ₑ-refl ⟦ w ⟧<:ᵛ ⟦ <:ᵛ-refl B ⟧<:ᵛ rel ≾ₑ-refl
                            (⟦ V ⟧ᵛᵗ pV') (⟦ M ⟧ᶜᵗ pM')
                        ∙ ∘ᵐ-congˡ (T-congᶠ (⟦⟧<:ᵛ-refl B) ∙ T-idᵐ)
                        ∙ ∘ᵐ-identityˡ _
                        ∙ ∘ᵐ-congˡ (T-≤-refl _)
                        ∙ ∘ᵐ-identityˡ _
                        ∙ ∘ᵐ-cong (appʰ-irr _ _)
                            ⟨ ⟦⟧ᵛᵗ-irr V pV' pV
                            , ∘ᵐ-congʳ (⟦⟧ᶜᵗ-irr M pM' pM) ⟩ᵐ-cong))
