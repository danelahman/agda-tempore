------------------------------------------------------------------------
-- The interpretation is natural in substitutions:                      --
--   ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ≈ ⟦ M ⟧ᶜᵗ ∘ᵐ sub-env x W   (dually for values). --
--                                                                    --
-- `sub-env x W : ⟦ split-l x ++ᶜ split-r x ⟧ →ᵐ ⟦ Γ ⟧` is the semantic  --
-- counterpart of the substitution: it reconstructs the environment for   --
-- `Γ` by inserting `⟦ W ⟧` at the position of `x`. It is defined by       --
-- structural recursion on `x` (the context splitting computes on `x`,     --
-- and the context interpretation distributes over `++ᶜ`), so no           --
-- transports along context equalities are needed.                         --
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

module DenotationalSemantics.Interpretation.SubstitutionCoherence
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S
open import Syntax.Substitutions S

open Category Cat
open Future Fut
open Past Pst
open Adjunction Adj
open GroundTypes GTy
open GroundEternal GE
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE

import DenotationalSemantics.Model.Modality.Past Cat (GradeSystem.RGrade Grades) as P
  using (·-mono-≾)

-- The environment morphism realising the substitution of `W` for `x`:
-- rebuild a `Γ`-environment from one for `Γ` with `x` removed, by
-- computing the missing component with `⟦ W ⟧`.

sub-env : ∀ {Γ A ρ} → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
        → ⟦ split-l x ++ᶜ split-r x ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ
sub-env Hd                W = ⟨ idᵐ , ⟦ W ⟧ᵛᵗ ⟩ᵐ
sub-env (Tl-∷ x)          W = mapˣᵐ (sub-env x W) idᵐ
sub-env (Tl-⟨⟩ {ρ = ρ} x) W = ⟨ ρ ⟩ᶠ (sub-env x W)

-- Weakening a variable past a `∷` projects the environment (both sides of
-- the equation mention `var-morphism` at the same type, so the `eternal?`
-- split reduces them simultaneously).

var-morphism-Tl-∷ : ∀ {Γ A B ρ'} → (y : B ∈[ ρ' ] Γ) → (f : ¬ Eternal B → ρ' ≾ᵣ uᵣ)
                  → var-morphism {Γ ∷ A} f (Tl-∷ y) ≈ᵐ var-morphism f y ∘ᵐ fstᵐ
var-morphism-Tl-∷ {B = B} y f with eternal? B
... | yes et = ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
... | no ¬et = ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))

-- Weakening a value of *eternal* type under a lock: denotationally this is
-- the eternal extraction applied to the locked environment. Proved by
-- induction on the value (only the eternal formers can occur).

eternal-val-ext-nat : ∀ {Γ A ρ} → (et : Eternal A) → (V : Γ ⊢V⦂ A)
                    → ⟦ eternal-val-ext {ρ = ρ} et V ⟧ᵛᵗ
                      ≈ᵐ eternalᵛ-extᵉ et ∘ᵐ ⟨ ρ ⟩ᶠ ⟦ V ⟧ᵛᵗ

eternal-val-ext-nat {A = A} et (var f y) with eternal? A
... | yes et' =
  ≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (eternalᵛ-extᵉ-μ et))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
            (∘ᵐ-congʳ (⟨⟩-congᶠ (∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et et'))))))))
... | no ¬et' = ⊥-elim (¬et' et)
eternal-val-ext-nat (Baseₑ b eb) (const c) =
  ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (⟦⟧ᵏ-eternal eb c))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
              (∘ᵐ-congʳ terminalᵐ-unique)))))
eternal-val-ext-nat Unitₑ ⋆ =
  ≈ᵐ-trans terminalᵐ-unique (≈ᵐ-sym terminalᵐ-unique)
eternal-val-ext-nat (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ =
  ≈ᵐ-trans (⟨ eternal-val-ext-nat et₁ V₁ , eternal-val-ext-nat et₂ V₂ ⟩ᵐ-cong)
  (≈ᵐ-trans (⟨ ∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
             , ∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _))) ⟩ᵐ-cong)
  (≈ᵐ-trans (⟨ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _) , ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _) ⟩ᵐ-cong)
  (≈ᵐ-trans (⟨ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) , ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ⟩ᵐ-cong)
  (≈ᵐ-trans (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
            (∘ᵐ-congˡ (≈ᵐ-sym (×-eternalᵒ-extᵉ (eternalᵛ-Eternalᵒ et₁)
                                              (eternalᵛ-Eternalᵒ et₂))))))))

-- The *ordinary* (non-eternal) extraction `εᵘ ∘ᵐ ⟨⟩-≤ _` is a graded
-- `⟨_⟩`-algebra, exactly as the eternal one is (`extᵉ-μ`). Here it is
-- derivable — the grades involved are all below the unit — from `μ-εᵘ`,
-- the grade-compatibility of `μ`, and the naturality of `εᵘ`.

-- and it is natural (this is `εᵘ`'s naturality together with that of `⟨⟩-≤`)

ext-nat : ∀ {X Y ρ} → (p : ρ ≾ᵣ uᵣ) → (g : X →ᵐ Y)
        → g ∘ᵐ (εᵘ ∘ᵐ ⟨⟩-≤ p) ≈ᵐ (εᵘ ∘ᵐ ⟨⟩-≤ p) ∘ᵐ ⟨ _ ⟩ᶠ g
ext-nat p g =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (εᵘ-nat g))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-≤-nat g p))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))

ext-alg : ∀ {X ρ₁ ρ₂} → (p : ρ₁ ≾ᵣ uᵣ) → (q : ρ₂ ≾ᵣ uᵣ) → (r : ρ₂ ·ᵣ ρ₁ ≾ᵣ uᵣ)
        → (εᵘ ∘ᵐ ⟨⟩-≤ r) ∘ᵐ μ {X} {ρ₁} {ρ₂}
        ≈ᵐ (εᵘ ∘ᵐ ⟨⟩-≤ q) ∘ᵐ (εᵘ ∘ᵐ ⟨⟩-≤ p)
ext-alg {X} {ρ₁} {ρ₂} p q r =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr r w)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-trans (P.·-mono-≾ q p) uu))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-μ-≤ p q)))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ μ-εᵘ))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (εᵘ-nat (⟨⟩-≤ q)))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))))))
  where
    uu : uᵣ ·ᵣ uᵣ ≾ᵣ uᵣ
    uu = ≾ᵣ-reflexive (·ᵣ-identityʳ uᵣ)

    w : ρ₂ ·ᵣ ρ₁ ≾ᵣ uᵣ
    w = ≾ᵣ-trans (P.·-mono-≾ q p) uu

-- Unfoldings of `var-morphism` once eternality has been decided. (Stating
-- them as lemmas is what lets the `eternal?` split reduce `var-morphism`
-- inside a recursive call's type.)

var-morphism-et : ∀ {Γ B ρ'} → (y : B ∈[ ρ' ] Γ) → (f : ¬ Eternal B → ρ' ≾ᵣ uᵣ)
                → (et : Eternal B)
                → var-morphism f y ≈ᵐ eternalᵛ-extᵉ et ∘ᵐ var-proj y
var-morphism-et {B = B} y f et with eternal? B
... | yes et' = ∘ᵐ-congˡ (eternalᵛ-extᵉ-irr et' et)
... | no ¬et' = ⊥-elim (¬et' et)

var-morphism-¬et : ∀ {Γ B ρ'} → (y : B ∈[ ρ' ] Γ) → (f : ¬ Eternal B → ρ' ≾ᵣ uᵣ)
                 → (¬et : ¬ Eternal B)
                 → var-morphism f y ≈ᵐ εᵘ ∘ᵐ ⟨⟩-≤ (f ¬et) ∘ᵐ var-proj y
var-morphism-¬et {B = B} y f ¬et with eternal? B
... | yes et'  = ⊥-elim (¬et et')
... | no ¬et'' = ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr _ _))

-- Substitution in a variable.

sub-var-nat : ∀ {Γ A B ρ ρ'}
            → (y : B ∈[ ρ' ] Γ) → (f : ¬ Eternal B → ρ' ≾ᵣ uᵣ)
            → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
            → ⟦ ⟨ y , f ⟩[ x ↦ W ]var ⟧ᵛᵗ ≈ᵐ var-morphism f y ∘ᵐ sub-env x W

-- the substituted variable is the one being replaced
sub-var-nat {B = B} Hd f Hd W with eternal? B
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

-- the variable is the head, the substitution acts deeper: the head component
-- of the environment is untouched (`sub-env (Tl-∷ x)` is `mapˣᵐ … idᵐ`)
sub-var-nat {B = B} Hd f (Tl-∷ x) W with eternal? B
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

-- the variable is deeper, the substitution replaces the head: the variable's
-- projection discards the substituted component
sub-var-nat {B = B} (Tl-∷ y) f Hd W with eternal? B
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

-- both deeper: recurse, weakening the substituted value (uses `V-rename-nat`)
sub-var-nat (Tl-∷ y) f (Tl-∷ x) W =
  ≈ᵐ-trans (V-rename-nat wk-ren ⟨ y , f ⟩[ x ↦ W ]var)
  (≈ᵐ-trans (∘ᵐ-congˡ (sub-var-nat y f x W))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (≈ᵐ-sym (var-morphism-Tl-∷ y f)))))))

sub-var-nat {B = B} (Tl-⟨⟩ y) f (Tl-⟨⟩ x) W with eternal? B
... | yes et =
  ≈ᵐ-trans (eternal-val-ext-nat et ⟨ y , _ ⟩[ x ↦ W ]var)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (sub-var-nat y _ x W)))
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
  ≈ᵐ-trans (V-rename-nat (⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et)) ∘ʳ ⟨⟩-η⁻¹-ren)
                         ⟨ y , _ ⟩[ x ↦ W ]var)
  (≈ᵐ-trans (∘ᵐ-congˡ (sub-var-nat y _ x W))
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

mutual

  V-subst-nat : ∀ {Γ A B ρ} → (V : Γ ⊢V⦂ B) → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
              → ⟦ V [ x ↦ W ]v ⟧ᵛᵗ ≈ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ sub-env x W
  V-subst-nat (var f y) x W = sub-var-nat y f x W
  V-subst-nat (const c) x W =
    ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
  V-subst-nat ⋆ x W = ≈ᵐ-sym terminalᵐ-unique
  V-subst-nat ⦉ V₁ , V₂ ⦊ x W =
    ≈ᵐ-trans (⟨ V-subst-nat V₁ x W , V-subst-nat V₂ x W ⟩ᵐ-cong)
             (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  V-subst-nat (lam M) x W =
    ≈ᵐ-trans (curryᵐ-cong (C-subst-nat M (Tl-∷ x) W))
             (curryᵐ-nat (sub-env x W) ⟦ M ⟧ᶜᵗ)

  C-subst-nat : ∀ {Γ A C ρ} → (M : Γ ⊢C⦂ C) → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
              → ⟦ M [ x ↦ W ]c ⟧ᶜᵗ ≈ᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ sub-env x W
  C-subst-nat (return V) x W =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  C-subst-nat (M ⨟ N) x W =
    ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (C-subst-nat N (Tl-∷ (Tl-⟨⟩ x)) W))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
                (⟨ η⊣-nat (sub-env x W)
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-subst-nat M x W) ⟩ᵐ-cong))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))))))))
  C-subst-nat (V₁ · V₂) x W =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ V-subst-nat V₁ x W , V-subst-nat V₂ x W ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-subst-nat (match V `in N) x W =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-subst-nat N (Tl-∷ (Tl-∷ x)) W))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
                   (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                    , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                      (≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W))
                                (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong)
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _) , ≈ᵐ-refl ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
  C-subst-nat (absurd V) x W =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  C-subst-nat (perform op V M) x W =
    ≈ᵐ-trans (∘ᵐ-congʳ
      (⟨ ≈ᵐ-trans (substᶜ-≈ (ty-gty (param op)) (V-subst-nat V x W))
                  (≡→≈ᵐ (sym (substᶜ-∘ (ty-gty (param op)) ⟦ V ⟧ᵛᵗ (sub-env x W))))
       , ≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                    (≈ᵐ-trans (substᵈ-≈ (ty-gty (arity op))
                                (C-subst-nat M (Tl-∷ (Tl-⟨⟩ x)) W))
                              (≡→≈ᵐ (sym (substᵈ-∘ (ty-gty (arity op)) ⟦ M ⟧ᶜᵗ
                                           (⟨ mapᵉ (op-grade op) ⟩ᶠ (sub-env x W)))))))))
         (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-nat _ _)))
         (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
         (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat (sub-env x W)))
                   (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-subst-nat (delay τ M) x W =
    ≈ᵐ-sym
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat (sub-env x W)))))
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
                (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym (C-subst-nat M (Tl-⟨⟩ x) W))))))))))
  C-subst-nat (handle M `with H `in N) x W =
    ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (C-subst-nat N (Tl-∷ (Tl-⟨⟩ x)) W))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
                (⟨ η⊣-nat (sub-env x W)
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-subst-nat M x W) ⟩ᵐ-cong))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))))))))
  C-subst-nat (unbox w V M) x W = {!!}
  C-subst-nat (box V N) x W =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-subst-nat N (Tl-∷ x) W))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (V-subst-nat V (Tl-⟨⟩ x) W)))
                   (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
                   (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat (sub-env x W)))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
  C-subst-nat (coerce rel M) x W =
    ≈ᵐ-trans (∘ᵐ-congʳ (C-subst-nat M x W)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
