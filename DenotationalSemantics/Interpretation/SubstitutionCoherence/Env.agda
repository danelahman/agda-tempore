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
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj
       using (Eternalᵒ; ⟨⊤⟩-η-nat; ⟨⊤⟩-eternalᵒ; ⟨⊤⟩-free-necᵉ-nat)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Base S Cat Fut Pst Adj GTy Mon GE

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

-- What a substitution does to a variable: both statements recurse on the
-- substitution alone, as `sub-var₀`/`sub-tgt₀` do.

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

-- What a substitution does to a resource (box-typed) variable: a statement
-- about its projection alone, since a box-typed variable is not read as a
-- value. The image occurs at its *declared* box type, so the projections
-- only agree after the declared type is coerced to the named one.

sub-rvar-natˢ : ∀ {Γ Γ' A ρ σ} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s)
              → (y : [ ρ ] A ∈[ σ ] Γ')
              → ⟨ σ ⟩ᶠ ⟦ tgt-<:₀ s y ⟧<:ᵛ
                  ∘ᵐ ⟨⟩-≤ (tgt-≾₀ s y) ∘ᵐ var-proj (tgt-var₀ s y)
              ≈ᵐ var-proj y ∘ᵐ ⟦ s ⟧ˢ₀ p

sub-rvar-natˢ {A = A} {ρ = ρ} ⌜ r ⌝ p y =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (⟨⟩-congᶠ (⟦⟧<:ᵛ-refl ([ ρ ] A))) ⟨⟩-idᵐ))
  (≈ᵐ-trans (∘ᵐ-identityˡ _) (var-proj-nat r y (λ ())))
-- the substituted value is an occurrence up to subsumption
sub-rvar-natˢ (val-sub W) pW Hd =
  ≈ᵐ-trans (grad-typ-var-nat W pW)
           (≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _))))
sub-rvar-natˢ {A = A} {ρ = ρ} (val-sub W) pW (Tl-∷ y) =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (⟨⟩-congᶠ (⟦⟧<:ᵛ-refl ([ ρ ] A))) ⟨⟩-idᵐ))
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityʳ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
sub-rvar-natˢ {A = A} {ρ = ρ} (cong-∷-sub s) p Hd =
  ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (⟨⟩-congᶠ (⟦⟧<:ᵛ-refl ([ ρ ] A))) ⟨⟩-idᵐ))
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-≤-refl)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (≈ᵐ-trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
sub-rvar-natˢ (cong-∷-sub s) p (Tl-∷ y) with sub-tgt₀ s y | sub-rvar-natˢ s p y
... | _ , _ , _ , v , w , b | ih =
  ≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ ih)
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
sub-rvar-natˢ (cong-⟨⟩-sub s) p (Tl-⟨⟩ y) with sub-tgt₀ s y | sub-rvar-natˢ s p y
... | _ , _ , _ , v , w , b | ih =
  ≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (μ-≤ˡ b)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-μ-nat _))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                      (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
                      (≈ᵐ-trans (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
                      (≈ᵐ-trans (⟨⟩-congᶠ (∘ᵐ-assoc _ _ _))
                      (≈ᵐ-trans (⟨⟩-congᶠ ih) (⟨⟩-∘ᵐ _ _)))))))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))))

-- hence the resource lookup commutes with the substitution: the two grade
-- bounds meet at the declared grade (`ε⊣-≤`) and the payload coercions compose.

sub-lkˢ : ∀ {Γ Γ' A A' ρ σ} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s)
        → (y : [ ρ ] A ∈[ σ ] Γ') → (rel : σ ≾ᵣ ρ) → (w : A <:ᵛ A')
        → lk (tgt-var₀ s y)
             (≾ᵣ-trans (≾ᵣ-trans (tgt-≾₀ s y) rel) (tgt-grade-≾₀ s y))
             (<:ᵛ-trans (tgt-type-<:₀ s y) w)
        ≈ᵐ lk y rel w ∘ᵐ ⟦ s ⟧ˢ₀ p
sub-lkˢ s p y rel w =
  ≈ᵐ-trans (∘ᵐ-congˡ (⟦⟧<:ᵛ-trans (tgt-type-<:₀ s y) w))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (sub-lk₀ˢ s p y rel))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  where
    sub-lk₀ˢ : ∀ {Γ Γ' A ρ σ} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s)
             → (y : [ ρ ] A ∈[ σ ] Γ') → (rel : σ ≾ᵣ ρ)
             → lk (tgt-var₀ s y)
                  (≾ᵣ-trans (≾ᵣ-trans (tgt-≾₀ s y) rel) (tgt-grade-≾₀ s y))
                  (tgt-type-<:₀ s y)
             ≈ᵐ (ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj y) ∘ᵐ ⟦ s ⟧ˢ₀ p
    sub-lk₀ˢ s p y rel =
      ≈ᵐ-sym
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (sub-rvar-natˢ s p y))))
         (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-nat _ rel))))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (⟨⟩-congᶠ (⟦⟧<:ᵛ-box (tgt-<:₀ s y)))))
         (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)))
         (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
         (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (≈ᵐ-sym (ε⊣-nat _))))
         (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (≈ᵐ-sym (ε⊣-≤ (tgt-grade-≾₀ s y)))))
         (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-trans _ _)))))
         (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
         (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-trans _ _))))))))))))))))))))))

-- and so does the whole unboxing.

unbox-subst-natˢ : ∀ {Γ Γ' A A' C ρ σ} → (s : Sub₀ [] Γ Γ') → (p : Paramˢ₀ s)
                 → (y : [ ρ ] A ∈[ σ ] Γ') → (rel : σ ≾ᵣ ρ) → (w : A <:ᵛ A')
                 → (M : Γ' ∷ A' ⊢C⦂ C)
                 → {pM : Paramᶜ M} → {pM' : Paramᶜ (C-sub₀ (cong-∷-sub s) M)}
                 → ⟦ C-sub₀ (cong-∷-sub s) M ⟧ᶜᵗ pM'
                   ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ mapˣᵐ (⟦ s ⟧ˢ₀ p) idᵐ
                 → ⟦ unbox (tgt-var₀ s y)
                           (≾ᵣ-trans (≾ᵣ-trans (tgt-≾₀ s y) rel) (tgt-grade-≾₀ s y))
                           (<:ᵛ-trans (tgt-type-<:₀ s y) w)
                           (C-sub₀ (cong-∷-sub s) M) ⟧ᶜᵗ pM'
                   ≈ᵐ (⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ idᵐ , lk y rel w ⟩ᵐ) ∘ᵐ ⟦ s ⟧ˢ₀ p
unbox-subst-natˢ s p y rel w M ih =
  unbox-step {M' = C-sub₀ (cong-∷-sub s) M} {M = M} {σ = ⟦ s ⟧ˢ₀ p}
             {lk' = lk (tgt-var₀ s y)
                       (≾ᵣ-trans (≾ᵣ-trans (tgt-≾₀ s y) rel) (tgt-grade-≾₀ s y))
                       (<:ᵛ-trans (tgt-type-<:₀ s y) w)}
             {lkᵒ = lk y rel w} ih (sub-lkˢ s p y rel w)

-- The substitution coherence theorem: substituting preserves parametricity,
-- and the interpretation is natural in the substitution, defined
-- simultaneously (as for renamings). The recursion is on the term alone;
-- what the substitution does is confined to the `var` and `unbox` cases,
-- the lemmas above.

mutual

  -- `{-# TERMINATING #-}`: the recursion is structural on the term, but it
  -- passes through the mutually-defined naturality lemma, which hides that
  -- from the checker.

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
  subᵛˢ s p (subV V q)  pV        = subᵛˢ s p V pV

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
  subᶜˢ s p (unbox x rel q M) pM       = subᶜˢ (cong-∷-sub s) p M pM
  subᶜˢ s p (box V M)        (pV , pM) =
    subᵛˢ (cong-⟨⟩-sub s) p V pV , subᶜˢ (cong-∷-sub s) p M pM
  subᶜˢ s p (subC M q)       pM        = subᶜˢ s p M pM
  -- the clauses are substituted into under the barrier lock, which acts on the
  -- ambient context only, so the clauses' uniformity transports
  subᶜˢ s p (handle M `with H `in N) (pM , pN , pH , uH) =
      subᶜˢ s p M pM
    , subᶜˢ (cong-∷-sub (cong-⟨⟩-sub s)) p N pN
    , (λ op ε'' → subᶜˢ (cong-∷-sub (cong-∷-sub (cong-⟨⟩-sub s)))
                    p (H op ε'') (pH op ε''))
    , sub-clauses-uniformˢ (cong-⟨⟩-sub s) p H pH uH

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
  V-subst-natˢ s p (subV V q) pV =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-subst-natˢ s p V pV)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))

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
  C-subst-natˢ s p (unbox x rel q M) pM =
    unbox-subst-natˢ s p x rel q M (C-subst-natˢ (cong-∷-sub s) p M pM)
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
  C-subst-natˢ s p (subC M q) pM =
    ≈ᵐ-trans (∘ᵐ-congʳ (C-subst-natˢ s p M pM)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  -- The environment-threading second component commutes as for `⨟`
  -- (`seq-nat`), and the handler algebra is reindexed by the substitution under
  -- the barrier lock (`alg-nat`, via `T-alg-of-handlerᵀ`'s naturality-in-P). The
  -- clause family is substituted into uniformly, so `⟦⟧ʰᵗ-nat` is the clauses'
  -- own naturality with the adapter moved past it (`adapt-commute`).
  C-subst-natˢ {Γ} {Γ'} s p (handle_`with_`in {A} {B} {ε} {ε'} M H N)
               (pM , pN , pH , uH) =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , seq-nat ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congˡ alg-nat)
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ⟨⊤⟩-η-nat (⟦ s ⟧ˢ₀ p) , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
    where
      f : ⟦ Γ ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ
      f = ⟦ cong-⟨⟩-sub {ρ = ⊤ᵣ} s ⟧ˢ₀ p
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
                    (λ op ε'' → C-sub₀ (cong-∷-sub (cong-∷-sub (cong-⟨⟩-sub s)))
                                  (H op ε''))
                    (λ op ε'' →
                       subᶜˢ (cong-∷-sub (cong-∷-sub (cong-⟨⟩-sub s)))
                         p (H op ε'') (pH op ε''))
                    (sub-clauses-uniformˢ (cong-⟨⟩-sub s) p H pH uH)) op ε''
               ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {Γ'} H pH uH) op ε'' ∘ᵐ mapˣᵐ f idᵐ
      ⟦⟧ʰᵗ-nat op ε'' =
        ≈ᵐ-trans (∘ᵐ-congˡ (C-subst-natˢ
                    (cong-∷-sub (cong-∷-sub (cong-⟨⟩-sub s)))
                    p (H op ε'') (pH op ε'')))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (adapt-commute _ _ _))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      alg-nat = T-alg-of-handlerᵀ-natᴾ (⟨⊤⟩-eternalᵒ ⟦ Γ' ⟧ᶜᵗˣ) (⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ)
                  f (⟨⊤⟩-free-necᵉ-nat (⟦ s ⟧ˢ₀ p)) (⟦_⟧ʰᵗ {Γ'} H pH uH) _ ⟦⟧ʰᵗ-nat
