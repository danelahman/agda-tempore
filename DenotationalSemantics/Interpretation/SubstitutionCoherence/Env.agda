------------------------------------------------------------------------
-- The environment morphism of a substitution, and the coherence theorem.
--
-- A `Sub₀ [] Γ Γ'` rewrites a `Γ'`-typed term into a `Γ`-typed one, so on
-- environments it runs covariantly, as `⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ`. Each generator
-- is a structural map of the model: a renaming is its own reindexing, `val-sub`
-- pairs the substituted value on, and the two congruences are the product and
-- the modality applied to the recursive one.
--
-- It needs a parametricity certificate, since it interprets a stored *value*;
-- `Paramˢ₀` collects those.
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
module DenotationalSemantics.Interpretation.SubstitutionCoherence.Env
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; yes; no; Dec)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S
open import Syntax.Substitutions S

open import Syntax.Substitutions.Base   S
open import Syntax.Substitutions.Lookup S
open import Syntax.Substitutions.Action S

open Category Cat
open Future Fut
open Past Pst
open Adjunction Adj
open GroundTypes GTy
open GroundEternal GE
open Monad Mon

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Base S Cat Fut Pst Adj GTy Mon GE

------------------------------------------------------------------------
-- PARAMETRIC SUBSTITUTIONS, AND WHAT THEY DO TO AN ENVIRONMENT
------------------------------------------------------------------------

Paramˢ₀ : ∀ {Γ Γ'} → Sub₀ [] Γ Γ' → Set
Paramˢ₀ ⌜ r ⌝           = ⊤
Paramˢ₀ (val-sub V)     = Paramᵛ V
Paramˢ₀ (cong-∷-sub s)  = Paramˢ₀ s
Paramˢ₀ (cong-⟨⟩-sub s) = Paramˢ₀ s

⟦_⟧ˢ₀ : ∀ {Γ Γ'} → (s : Sub₀ [] Γ Γ') → Paramˢ₀ s → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ
⟦ ⌜ r ⌝ ⟧ˢ₀                   _  = ⟦ r ⟧ʳ
⟦ val-sub V ⟧ˢ₀               pV = ⟨ idᵐ , ⟦ V ⟧ᵛᵗ pV ⟩ᵐ
⟦ cong-∷-sub s ⟧ˢ₀            p  = mapˣᵐ (⟦ s ⟧ˢ₀ p) idᵐ
⟦ cong-⟨⟩-sub {ρ = ρ} s ⟧ˢ₀   p  = ⟨ ρ ⟩ᶠ (⟦ s ⟧ˢ₀ p)

-- Replacing the entry a splitting names is a parametric substitution, and at a
-- variable's own splitting its environment morphism is `sub-env` — on the nose,
-- both recursions being `var-split`'s.

sub-split₀ᴾ : ∀ {Γ Γ₁ Γ₂ A} → (s : Γ₁ ∷ A , Γ₂ split Γ) → (W : Γ₁ ⊢V⦂ A)
            → Paramᵛ W → Paramˢ₀ (sub-split₀ s W)
sub-split₀ᴾ split-[]     W pW = pW
sub-split₀ᴾ (split-∷ s)  W pW = sub-split₀ᴾ s W pW
sub-split₀ᴾ (split-⟨⟩ s) W pW = sub-split₀ᴾ s W pW

sub-env-is-⟦⟧ˢ₀ : ∀ {Γ Γ₁ Γ₂ A} → (s : Γ₁ ∷ A , Γ₂ split Γ) → (W : Γ₁ ⊢V⦂ A)
               → (pW : Paramᵛ W)
               → ⟦ sub-split₀ s W ⟧ˢ₀ (sub-split₀ᴾ s W pW)
               ≈ᵐ sub-env s W pW
sub-env-is-⟦⟧ˢ₀ split-[]     W pW = ≈ᵐ-refl
sub-env-is-⟦⟧ˢ₀ (split-∷ s)  W pW = mapˣᵐ-cong (sub-env-is-⟦⟧ˢ₀ s W pW) ≈ᵐ-refl
sub-env-is-⟦⟧ˢ₀ (split-⟨⟩ s) W pW = ⟨⟩-congᶠ (sub-env-is-⟦⟧ˢ₀ s W pW)

------------------------------------------------------------------------
-- THE ETERNAL RESTRICTION
------------------------------------------------------------------------

-- The restricted substitution stores only restrictions of stored values, and
-- those are parametric outright.

restrict-val-subᴾ : ∀ {Γ₀ A} → (dec : Dec (Eternal A)) → (V : Γ₀ ⊢V⦂ A)
                  → Paramˢ₀ (restrict-val-sub {[]} {Γ₀} {A} dec V)
restrict-val-subᴾ (yes et) V = eternal-val-restrictᴾ et V
restrict-val-subᴾ (no  _)  V = tt

restrict-∷-subᴾ : ∀ {B} → (Γ Δ : Ctx) → (dec : Dec (Eternal B))
                → {s : Sub₀ [] (Δ ᴱ) (Γ ᴱ)} → Paramˢ₀ s
                → Paramˢ₀ (restrict-∷-sub {Ξ = []} {Δ = Δ} {Δ' = Γ} dec s)
restrict-∷-subᴾ Γ Δ (yes _) p = p
restrict-∷-subᴾ Γ Δ (no  _) p = p

restrict-sub₀ᴾ : ∀ {Γ Γ'} → (s : Sub₀ [] Γ Γ') → Paramˢ₀ s
               → Paramˢ₀ (restrict-sub₀ s)
restrict-sub₀ᴾ ⌜ r ⌝ p = tt
restrict-sub₀ᴾ {Γ} (val-sub {A = A} V) pV =
  restrict-val-subᴾ {Γ} {A} (eternal? A) V
restrict-sub₀ᴾ (cong-∷-sub {Δ} {Δ'} {A} s) p =
  restrict-∷-subᴾ Δ' Δ (eternal? A) (restrict-sub₀ᴾ s p)
restrict-sub₀ᴾ (cong-⟨⟩-sub s) p = restrict-sub₀ᴾ s p

------------------------------------------------------------------------
-- WHAT A SUBSTITUTION DOES TO A VARIABLE
--
-- Both statements recurse on the substitution alone, as `sub-var₀`/`sub-tgt₀`
-- do. The renaming generator is the corresponding renaming fact
-- (`var-morphism-nat`, `var-proj-nat`); the other three are the model's
-- structural maps.
------------------------------------------------------------------------

mutual

  sub-varᴾ : ∀ {Γ Γ' A ρ} → (s : Sub₀ [] Γ Γ') → Paramˢ₀ s
           → (x : A ∈[ ρ ] Γ') → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
           → Paramᵛ (sub-var₀ s x f)
  sub-varᴾ ⌜ r ⌝          p  x         f = tt
  sub-varᴾ (val-sub V)    pV Hd        f = pV
  sub-varᴾ (val-sub V)    pV (Tl-∷ y)  f = tt
  sub-varᴾ (cong-∷-sub s) p  Hd        f = tt
  sub-varᴾ (cong-∷-sub s) p  (Tl-∷ y)  f =
    renᵛ wk-ren (sub-var₀ s y f) (sub-varᴾ s p y f)
  sub-varᴾ {A = A} (cong-⟨⟩-sub s) p (Tl-⟨⟩ y) f =
    sub-varᴾ-⟨⟩ s p y f (eternal? A)

  sub-varᴾ-⟨⟩ : ∀ {Γ Γ' A ρ ρ'} → (s : Sub₀ [] Γ Γ') → Paramˢ₀ s
              → (y : A ∈[ ρ' ] Γ') → (f : ¬ Eternal A → ρ' ·ᵣ ρ ≾ᵣ uᵣ)
              → (dec : Dec (Eternal A))
              → Paramᵛ (sub-var₀-⟨⟩ {ρ = ρ} s y f dec)
  sub-varᴾ-⟨⟩ s p y f (yes et) =
    eternal-val-extᴾ et (sub-var₀ s y (λ ¬et → ⊥-elim (¬et et)))
  sub-varᴾ-⟨⟩ s p y f (no ¬et) =
    renᵛ _ (sub-var₀ s y (λ ¬et' → ≾ᵣ-zero-productˡ (f ¬et')))
           (sub-varᴾ s p y (λ ¬et' → ≾ᵣ-zero-productˡ (f ¬et')))
sub-var-natˢ : ∀ {Γ Γ' A ρ} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s)
             → (x : A ∈[ ρ ] Γ') → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
             → ⟦ sub-var₀ s x f ⟧ᵛᵗ (sub-varᴾ s p x f)
             ≈ᵐ var-morphism f x ∘ᵐ ⟦ s ⟧ˢ₀ p

-- an embedded renaming acts as itself
sub-var-natˢ ⌜ r ⌝ p x f = var-morphism-nat r f x

-- the variable being replaced: the substituted value, read off the pairing
sub-var-natˢ {A = B} (val-sub W) pW Hd f with eternal? B
... | yes et =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-u et)) ⟨⟩-εᵘ∘η≡id))
              (∘ᵐ-identityˡ _))))))
... | no ¬et =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-trans (⟨⟩-≤-irr (f ¬et) ≾ᵣ-refl) ⟨⟩-≤-refl)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-εᵘ∘η≡id)
              (∘ᵐ-identityˡ _)))))))))

-- a variable the substitution passes through
sub-var-natˢ {A = B} (val-sub W) pW (Tl-∷ y) f with eternal? B
... | yes et =
  ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)))
                   (∘ᵐ-congʳ (∘ᵐ-identityʳ _)))))
... | no ¬et =
  ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))))
                   (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityʳ _)))))))

-- under one more binder, the new variable is untouched
sub-var-natˢ {A = B} (cong-∷-sub s) p Hd f with eternal? B
... | yes et =
  ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)))
                   (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _))))))
... | no ¬et =
  ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))
                   (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-identityˡ _))))))))

sub-var-natˢ (cong-∷-sub s) p (Tl-∷ y) f =
  ≈ᵐ-trans (V-rename-nat wk-ren (sub-var₀ s y f) (sub-varᴾ s p y f))
  (≈ᵐ-trans (∘ᵐ-congˡ (sub-var-natˢ s p y f))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (≈ᵐ-sym (var-morphism-Tl-∷ y f)))))))

-- crossing a lock
sub-var-natˢ {A = B} (cong-⟨⟩-sub s) p (Tl-⟨⟩ y) f with eternal? B
... | yes et =
  ≈ᵐ-trans (eternal-val-ext-nat et (sub-var₀ s y _) (sub-varᴾ s p y _))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (sub-var-natˢ s p y _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-congˡ (var-morphism-et y _ et))))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (eternalᵛ-extᵉ-μ et)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))))))
... | no ¬et =
  ≈ᵐ-trans (V-rename-nat (⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et)))
                         (sub-var₀ s y _) (sub-varᴾ s p y _))
  (≈ᵐ-trans (∘ᵐ-congˡ (sub-var-natˢ s p y _))
  (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (var-morphism-¬et y _ ¬et)))
  (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (ext-nat _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (ext-alg _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))))))))))))))

------------------------------------------------------------------------
-- WHAT A SUBSTITUTION DOES TO A RESOURCE VARIABLE
--
-- A box-typed variable is not read as a value, so this is a statement about
-- its projection alone: relaxing the substituted variable's projection back to
-- the original grade is the original projection reindexed by the substitution.
------------------------------------------------------------------------

sub-rvar-natˢ : ∀ {Γ Γ' A ρ σ} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s)
              → (y : [ ρ ] A ∈[ σ ] Γ')
              → ⟨⟩-≤ (proj₂ (proj₂ (sub-tgt₀ s y)))
                  ∘ᵐ var-proj (proj₁ (proj₂ (sub-tgt₀ s y)))
              ≈ᵐ var-proj y ∘ᵐ ⟦ s ⟧ˢ₀ p

sub-rvar-natˢ ⌜ r ⌝ p y = var-proj-nat r y (λ ())
sub-rvar-natˢ (val-sub W) pW Hd with grad-typ⇒var W
... | σ' , v , f , refl =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityˡ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ⟨⟩-η∘εᵘ≡id))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
sub-rvar-natˢ (val-sub W) pW (Tl-∷ y) =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityʳ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
sub-rvar-natˢ (cong-∷-sub s) p Hd =
  ≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (≈ᵐ-trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
sub-rvar-natˢ (cong-∷-sub s) p (Tl-∷ y) with sub-tgt₀ s y | sub-rvar-natˢ s p y
... | σ' , v , p | ih =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ ih)
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
sub-rvar-natˢ (cong-⟨⟩-sub s) p (Tl-⟨⟩ y) with sub-tgt₀ s y | sub-rvar-natˢ s p y
... | σ' , v , p | ih =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (μ-≤ˡ p))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ ih))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
-- hence the resource lookup commutes with the substitution

sub-lkˢ : ∀ {Γ Γ' A ρ σ} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s)
        → (y : [ ρ ] A ∈[ σ ] Γ') → (rel : σ ≾ᵣ ρ)
        → lk (proj₁ (proj₂ (sub-tgt₀ s y)))
             (≾ᵣ-trans (proj₂ (proj₂ (sub-tgt₀ s y))) rel)
        ≈ᵐ lk y rel ∘ᵐ ⟦ s ⟧ˢ₀ p
sub-lkˢ s p y rel =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-trans _ rel))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (sub-rvar-natˢ s p y)))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))

-- and so does the whole unboxing.

unbox-subst-natˢ : ∀ {Γ Γ' A C ρ σ} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s)
                 → (y : [ ρ ] A ∈[ σ ] Γ') → (rel : σ ≾ᵣ ρ)
                 → (M : Γ' ∷ A ⊢C⦂ C)
                 → {pM : Paramᶜ M} → {pM' : Paramᶜ (C-sub₀ (cong-∷-sub s) M)}
                 → ⟦ C-sub₀ (cong-∷-sub s) M ⟧ᶜᵗ pM'
                   ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ mapˣᵐ (⟦ s ⟧ˢ₀ p) idᵐ
                 → ⟦ unbox (proj₁ (proj₂ (sub-tgt₀ s y)))
                           (≾ᵣ-trans (proj₂ (proj₂ (sub-tgt₀ s y))) rel)
                           (C-sub₀ (cong-∷-sub s) M) ⟧ᶜᵗ pM'
                   ≈ᵐ (⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ idᵐ , lk y rel ⟩ᵐ) ∘ᵐ ⟦ s ⟧ˢ₀ p
unbox-subst-natˢ s p y rel M ih =
  unbox-step {M' = C-sub₀ (cong-∷-sub s) M} {M = M} {σ = ⟦ s ⟧ˢ₀ p}
             {lk' = lk (proj₁ (proj₂ (sub-tgt₀ s y)))
                       (≾ᵣ-trans (proj₂ (proj₂ (sub-tgt₀ s y))) rel)}
             {lkᵒ = lk y rel} ih (sub-lkˢ s p y rel)

------------------------------------------------------------------------
-- THE ETERNAL RESTRICTION AGAINST THE ETERNAL PROJECTION
--
-- The restricted substitution is a morphism of eternal objects, and the
-- eternal projection is natural along a substitution. Both recurse on the
-- substitution; the embedded-renaming generator is the corresponding renaming
-- fact (`restrict-ren-mor`, `projᴱ-nat`).
------------------------------------------------------------------------
restrict-sub-env-extᵉˢ : ∀ {Γ Γ'} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s) → ∀ {ρ}
                       → projᴱ-extᵉ Γ' {ρ}
                           ∘ᵐ ⟨ ρ ⟩ᶠ (⟦ restrict-sub₀ s ⟧ˢ₀ (restrict-sub₀ᴾ s p))
                       ≈ᵐ ⟦ restrict-sub₀ s ⟧ˢ₀ (restrict-sub₀ᴾ s p)
                            ∘ᵐ projᴱ-extᵉ Γ {ρ}

restrict-sub-env-extᵉˢ ⌜ r ⌝ p = restrict-ren-mor r
restrict-sub-env-extᵉˢ {Γ} (val-sub {A = A} V) pV {ρ} with eternal? A
... | yes et =
  prod-ext
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (projᴱ-extᵉ-fst {Γ} {A} et {ρ}))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
    (≈ᵐ-trans (∘ᵐ-identityʳ _)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityˡ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)))
              (∘ᵐ-assoc _ _ _))))))))))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (×-eternalᵒ-sndᵉ {Γ} {A} et {ρ}))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)))
    (≈ᵐ-trans (restrict-val-mor et V)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)))
              (∘ᵐ-assoc _ _ _))))))))
... | no  _  =
  ≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
restrict-sub-env-extᵉˢ (cong-∷-sub {Γ₀} {Γ₀'} {B} s) p {ρ} with eternal? B
... | yes etB =
  prod-ext
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (projᴱ-extᵉ-fst {Γ₀'} {B} etB {ρ}))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (restrict-sub-env-extᵉˢ s p))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (projᴱ-extᵉ-fst {Γ₀} {B} etB {ρ})))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)))
              (∘ᵐ-assoc _ _ _)))))))))))))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (×-eternalᵒ-sndᵉ {Γ₀'} {B} etB {ρ}))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-identityˡ _)))
    (≈ᵐ-sym (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
            (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-identityˡ _))
                      (×-eternalᵒ-sndᵉ {Γ₀} {B} etB {ρ})))))))))))
... | no  _  = restrict-sub-env-extᵉˢ s p
restrict-sub-env-extᵉˢ (cong-⟨⟩-sub s) p = restrict-sub-env-extᵉˢ s p

-- The `necᵉ`/`Future` mate.

restrict-sub-env-necᵉˢ : ∀ {Γ Γ'} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s) → ∀ {ρ}
                       → [ ρ ]ᶠ (⟦ restrict-sub₀ s ⟧ˢ₀ (restrict-sub₀ᴾ s p))
                           ∘ᵐ Eternalᵒ.necᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) {ρ}
                       ≈ᵐ Eternalᵒ.necᵉ (⟦ Γ' ⟧ᴱ-Eternalᵒ) {ρ}
                            ∘ᵐ ⟦ restrict-sub₀ s ⟧ˢ₀ (restrict-sub₀ᴾ s p)
restrict-sub-env-necᵉˢ {Γ} {Γ'} s p {ρ} =
  ≈ᵐ-trans (∘ᵐ-congʳ (Eternalᵒ.necᵉ-mate (⟦ Γ ⟧ᴱ-Eternalᵒ)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym (restrict-sub-env-extᵉˢ s p))))
  (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (≈ᵐ-sym (Eternalᵒ.necᵉ-mate (⟦ Γ' ⟧ᴱ-Eternalᵒ)))))))))))

-- Naturality of the eternal projection along a substitution.

projᴱ-natˢ : ∀ {Γ Γ'} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s)
           → projᴱ Γ' ∘ᵐ ⟦ s ⟧ˢ₀ p
           ≈ᵐ ⟦ restrict-sub₀ s ⟧ˢ₀ (restrict-sub₀ᴾ s p) ∘ᵐ projᴱ Γ

projᴱ-natˢ ⌜ r ⌝ p = projᴱ-nat r
projᴱ-natˢ {Γ} (val-sub {A = A} V) pV with eternal? A
... | yes et =
  ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
  (≈ᵐ-trans (⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  (≈ᵐ-trans (⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _) , eternal-val-restrict-nat et V pV ⟩ᵐ-cong)
            (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))))
... | no  _ =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))))
projᴱ-natˢ (cong-∷-sub {Γ₀} {Γ₀'} {B} s) p with eternal? B
... | yes _ =
  ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
  (≈ᵐ-trans (mapˣᵐ-cong (projᴱ-natˢ s p) ≈ᵐ-refl)
            (≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _)))
... | no  _ =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (projᴱ-natˢ s p))
            (∘ᵐ-assoc _ _ _))))
projᴱ-natˢ (cong-⟨⟩-sub s) p =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (projᴱ-natˢ s p)))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (restrict-sub-env-extᵉˢ s p))
            (∘ᵐ-assoc _ _ _))))))

------------------------------------------------------------------------
-- THE SUBSTITUTION COHERENCE THEOREM
--
-- Substituting preserves parametricity, and the interpretation is natural in
-- the substitution. The two are defined simultaneously, for the same reason as
-- for renamings: transporting a handler's clause-uniformity across a
-- substitution needs the naturality lemma for the clauses themselves.
--
-- The recursion is on the term and never inspects the substitution, exactly as
-- `V-sub₀`/`C-sub₀`'s is; what the substitution does is confined to the `var`
-- and `unbox` cases, which are the lemmas above.
------------------------------------------------------------------------

mutual

  -- `TERMINATING`: the recursion is structural on the term, but it passes
  -- through the simultaneously-defined naturality lemma (the `handle` case of
  -- `subᶜˢ` appeals to `C-subst-natˢ` on the clauses), which masks that from
  -- the termination checker.

  {-# TERMINATING #-}

  subᵛˢ : ∀ {Γ Γ' A} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s)
        → (V : Γ' ⊢V⦂ A) → Paramᵛ V → Paramᵛ (V-sub₀ s V)
  subᵛˢ s p (var f x)   _         = sub-varᴾ s p x f
  subᵛˢ s p (const c)   _         = tt
  subᵛˢ s p ⋆           _         = tt
  subᵛˢ s p true        _         = tt
  subᵛˢ s p false       _         = tt
  subᵛˢ s p ⦉ V , W ⦊   (pV , pW) = subᵛˢ s p V pV , subᵛˢ s p W pW
  subᵛˢ s p (lam M)     pM        = subᶜˢ (cong-∷-sub s) p M pM

  subᶜˢ : ∀ {Γ Γ' C} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s)
        → (M : Γ' ⊢C⦂ C) → Paramᶜ M → Paramᶜ (C-sub₀ s M)
  subᶜˢ s p (return V)       pV        = subᵛˢ s p V pV
  subᶜˢ s p (M ⨟ N)          (pM , pN) =
    subᶜˢ s p M pM , subᶜˢ (cong-∷-sub (cong-⟨⟩-sub s)) p N pN
  subᶜˢ s p (V · W)          (pV , pW) = subᵛˢ s p V pV , subᵛˢ s p W pW
  subᶜˢ s p (match V `in M)  (pV , pM) =
    subᵛˢ s p V pV , subᶜˢ (cong-∷-sub (cong-∷-sub s)) p M pM
  subᶜˢ s p (absurd V)       pV        = subᵛˢ s p V pV
  subᶜˢ s p (if V `then M `else N) (pV , pM , pN) =
    subᵛˢ s p V pV , subᶜˢ s p M pM , subᶜˢ s p N pN
  subᶜˢ s p (perform op V M) (pV , pM) =
    subᵛˢ s p V pV , subᶜˢ (cong-∷-sub (cong-⟨⟩-sub s)) p M pM
  subᶜˢ s p (delay τ M)      pM        = subᶜˢ (cong-⟨⟩-sub s) p M pM
  subᶜˢ s p (unbox x rel M)  pM        = subᶜˢ (cong-∷-sub s) p M pM
  subᶜˢ s p (box V M)        (pV , pM) =
    subᵛˢ (cong-⟨⟩-sub s) p V pV , subᶜˢ (cong-∷-sub s) p M pM
  subᶜˢ s p (coerce rel M)   pM        = subᶜˢ s p M pM
  -- the clauses are substituted into by the eternal restriction, which acts on
  -- the ambient context only, so the clauses' uniformity transports
  subᶜˢ s p (handle M `with H `in N) (pM , pN , pH , uH) =
      subᶜˢ s p M pM
    , subᶜˢ (cong-∷-sub (cong-⟨⟩-sub s)) p N pN
    , (λ op ε'' → subᶜˢ (cong-∷-sub (cong-∷-sub (restrict-sub₀ s)))
                    (restrict-sub₀ᴾ s p) (H op ε'') (pH op ε''))
    , sub-clauses-uniformˢ (restrict-sub₀ s) (restrict-sub₀ᴾ s p) H pH uH

  -- Substituting in a clause family's ambient context preserves the clauses'
  -- uniformity in the residual grade: the substitution acts on the ambient
  -- context only, so it commutes with the continuation's coercion
  -- (`mapˣ-swapᵐ`), after which the original uniformity applies.
  sub-clauses-uniformˢ :
    ∀ {Δ Δ' B} → (ss : Sub₀ [] Δ Δ') → (ps : Paramˢ₀ ss)
    → (H : (op : Op) → (ε'' : E)
         → Δ' ∷ type-of-gtype (param op)
              ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
           ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
    → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
    → (∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'')
         → ⟦ H op ε₂'' ⟧ᶜᵗ (pH op ε₂'')
             ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
         ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H op ε₁'' ⟧ᶜᵗ (pH op ε₁''))
    → (∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'')
         → ⟦ C-sub₀ (cong-∷-sub (cong-∷-sub ss)) (H op ε₂'') ⟧ᶜᵗ
              (subᶜˢ (cong-∷-sub (cong-∷-sub ss)) ps (H op ε₂'') (pH op ε₂''))
             ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
         ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q)
              ∘ᵐ ⟦ C-sub₀ (cong-∷-sub (cong-∷-sub ss)) (H op ε₁'') ⟧ᶜᵗ
                   (subᶜˢ (cong-∷-sub (cong-∷-sub ss)) ps (H op ε₁'') (pH op ε₁'')))
  sub-clauses-uniformˢ ss ps H pH uH op q =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-subst-natˢ (cong-∷-sub (cong-∷-sub ss)) ps
                          (H op _) (pH op _)))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣ-swapᵐ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (uH op q))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
              (∘ᵐ-congʳ (≈ᵐ-sym (C-subst-natˢ (cong-∷-sub (cong-∷-sub ss)) ps
                                   (H op _) (pH op _)))))))))

  V-subst-natˢ : ∀ {Γ Γ' A} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s)
               → (V : Γ' ⊢V⦂ A) → (pV : Paramᵛ V)
               → ⟦ V-sub₀ s V ⟧ᵛᵗ (subᵛˢ s p V pV) ≈ᵐ ⟦ V ⟧ᵛᵗ pV ∘ᵐ ⟦ s ⟧ˢ₀ p
  V-subst-natˢ s p (var f x) _ = sub-var-natˢ s p x f
  V-subst-natˢ s p (const c) _ =
    ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
  V-subst-natˢ s p ⋆ _ = ≈ᵐ-sym terminalᵐ-unique
  V-subst-natˢ s p true _ =
    ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
  V-subst-natˢ s p false _ =
    ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
  V-subst-natˢ s p ⦉ V , W ⦊ (pV , pW) =
    ≈ᵐ-trans (⟨ V-subst-natˢ s p V pV , V-subst-natˢ s p W pW ⟩ᵐ-cong)
             (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  V-subst-natˢ s p (lam M) pM =
    ≈ᵐ-trans (curryᵐ-cong (C-subst-natˢ (cong-∷-sub s) p M pM))
             (curryᵐ-nat (⟦ s ⟧ˢ₀ p) (⟦ M ⟧ᶜᵗ pM))

  C-subst-natˢ : ∀ {Γ Γ' C} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s)
               → (M : Γ' ⊢C⦂ C) → (pM : Paramᶜ M)
               → ⟦ C-sub₀ s M ⟧ᶜᵗ (subᶜˢ s p M pM) ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ s ⟧ˢ₀ p
  C-subst-natˢ s p (return V) pV =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-subst-natˢ s p V pV)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  C-subst-natˢ s p (M ⨟ N) (pM , pN) =
    ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
                (C-subst-natˢ (cong-∷-sub (cong-⟨⟩-sub s)) p N pN))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
                (⟨ η⊣-nat (⟦ s ⟧ˢ₀ p)
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-subst-natˢ s p M pM) ⟩ᵐ-cong))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))))))))
  C-subst-natˢ s p (V · W) (pV , pW) =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ V-subst-natˢ s p V pV , V-subst-natˢ s p W pW ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-subst-natˢ s p (match V `in M) (pV , pM) =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-subst-natˢ (cong-∷-sub (cong-∷-sub s)) p M pM))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
                   (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                    , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                      (≈ᵐ-trans (∘ᵐ-congʳ (V-subst-natˢ s p V pV))
                                (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong)
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (V-subst-natˢ s p V pV))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _) , ≈ᵐ-refl ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
  C-subst-natˢ s p (absurd V) pV =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-subst-natˢ s p V pV)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  -- the substitution distributes over the branches: `ifᵐ-∘`
  C-subst-natˢ s p (if V `then M `else N) (pV , pM , pN) =
    ≈ᵐ-trans (ifᵐ-cong (V-subst-natˢ s p V pV)
                       (C-subst-natˢ s p M pM) (C-subst-natˢ s p N pN))
             (≈ᵐ-sym (ifᵐ-∘ _ _ _ _))
  C-subst-natˢ s p (perform op V M) (pV , pM) =
    ≈ᵐ-trans (∘ᵐ-congʳ
      (⟨ ≈ᵐ-trans (substᶜ-≈ (ty-gty (param op)) (V-subst-natˢ s p V pV))
                  (≡→≈ᵐ (sym (substᶜ-∘ (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV) (⟦ s ⟧ˢ₀ p))))
       , ≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                    (≈ᵐ-trans (substᵈ-≈ (ty-gty (arity op))
                                (C-subst-natˢ (cong-∷-sub (cong-⟨⟩-sub s)) p M pM))
                              (≡→≈ᵐ (sym (substᵈ-∘ (ty-gty (arity op)) (⟦ M ⟧ᶜᵗ pM)
                                           (⟨ mapᵉ (op-grade op) ⟩ᶠ (⟦ s ⟧ˢ₀ p)))))))))
         (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-nat _ _)))
         (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
         (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat (⟦ s ⟧ˢ₀ p)))
                   (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-subst-natˢ s p (delay τ M) pM =
    ≈ᵐ-sym
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat (⟦ s ⟧ˢ₀ p)))))
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
                (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ
                  (≈ᵐ-sym (C-subst-natˢ (cong-⟨⟩-sub s) p M pM))))))))))
  -- `unbox-step` splits the goal into the continuation (the IH) and the
  -- resource lookup (`sub-lkˢ`).
  C-subst-natˢ s p (unbox x rel M) pM =
    unbox-subst-natˢ s p x rel M (C-subst-natˢ (cong-∷-sub s) p M pM)
  C-subst-natˢ s p (box V M) (pV , pM) =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-subst-natˢ (cong-∷-sub s) p M pM))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ
                                (V-subst-natˢ (cong-⟨⟩-sub s) p V pV)))
                   (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
                   (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat (⟦ s ⟧ˢ₀ p)))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
  C-subst-natˢ s p (coerce rel M) pM =
    ≈ᵐ-trans (∘ᵐ-congʳ (C-subst-natˢ s p M pM)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  -- The environment-threading second component commutes as for `⨟`
  -- (`seq-nat`), and the handler algebra is reindexed by the restricted
  -- substitution (`alg-nat`, via `T-alg-of-handlerᵀ`'s naturality-in-P). The
  -- clause family is substituted into uniformly, so `⟦⟧ʰᵗ-nat` is the clauses'
  -- own naturality with the adapter moved past it (`adapt-commute`).
  C-subst-natˢ {Γ} {Γ'} s p (handle_`with_`in {A} {B} {ε} {ε'} M H N)
               (pM , pN , pH , uH) =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , seq-nat ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congˡ alg-nat)
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (projᴱ-natˢ s p) , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
    where
      f : ⟦ Γ ᴱ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ᴱ ⟧ᶜᵗˣ
      f = ⟦ restrict-sub₀ s ⟧ˢ₀ (restrict-sub₀ᴾ s p)
      seq-nat : Tᶠ (⟦ C-sub₀ (cong-∷-sub (cong-⟨⟩-sub s)) N ⟧ᶜᵗ
                      (subᶜˢ (cong-∷-sub (cong-⟨⟩-sub s)) p N pN)) ∘ᵐ strᵀ
                  ∘ᵐ ⟨ η⊣ , ⟦ C-sub₀ s M ⟧ᶜᵗ (subᶜˢ s p M pM) ⟩ᵐ
              ≈ᵐ (Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ) ∘ᵐ ⟦ s ⟧ˢ₀ p
      seq-nat =
        ≈ᵐ-trans (∘ᵐ-congˡ (T-congᶠ
                    (C-subst-natˢ (cong-∷-sub (cong-⟨⟩-sub s)) p N pN)))
        (≈ᵐ-trans (∘ᵐ-congˡ (T-∘ᵐ _ _))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ
                    (⟨ η⊣-nat (⟦ s ⟧ˢ₀ p)
                     , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-subst-natˢ s p M pM) ⟩ᵐ-cong)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))))
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))))))
      ⟦⟧ʰᵗ-nat : ∀ op ε''
               → clauseᵀ (⟦_⟧ʰᵗ {Γ}
                    (λ op ε'' → C-sub₀ (cong-∷-sub (cong-∷-sub (restrict-sub₀ s)))
                                  (H op ε''))
                    (λ op ε'' →
                       subᶜˢ (cong-∷-sub (cong-∷-sub (restrict-sub₀ s)))
                         (restrict-sub₀ᴾ s p) (H op ε'') (pH op ε''))
                    (sub-clauses-uniformˢ (restrict-sub₀ s) (restrict-sub₀ᴾ s p)
                       H pH uH)) op ε''
               ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {Γ'} H pH uH) op ε'' ∘ᵐ mapˣᵐ f idᵐ
      ⟦⟧ʰᵗ-nat op ε'' =
        ≈ᵐ-trans (∘ᵐ-congˡ (C-subst-natˢ
                    (cong-∷-sub (cong-∷-sub (restrict-sub₀ s)))
                    (restrict-sub₀ᴾ s p) (H op ε'') (pH op ε'')))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (adapt-commute _ _ _))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      alg-nat = T-alg-of-handlerᵀ-natᴾ ((⟦ Γ' ⟧ᴱ-Eternalᵒ)) ((⟦ Γ ⟧ᴱ-Eternalᵒ))
                  f (restrict-sub-env-necᵉˢ s p) (⟦_⟧ʰᵗ {Γ'} H pH uH) _ ⟦⟧ʰᵗ-nat
