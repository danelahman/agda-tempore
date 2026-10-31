--------------------------------------------------------------------------
-- Soundness of the beta/eta equations of the pure fragment.            --
-- These are the cartesian closed structure: `unit-eta` is the terminal --
-- object's uniqueness, `fun-beta`/`fun-eta` the exponential's,         --
-- `match-beta`/`match-eta` the product's, `absurd-eta` the initial     --
-- object's strictness, the boolean equations are the boolean object's  --
-- own laws, the natural-number equations those of `matchℕᵐ` and of     --
-- the recursor `recℕᵐ`, the sum equations the coproduct's (`match+ᵐ`), --
-- and the list equations those of `matchLᵐ` and of `recLᵐ`.            --
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

module MonomorphicCalculus.EquationalTheory.Soundness.Values
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
open import Relation.Nullary using (¬_; yes; no)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Language.Comparisons using (Cmp; holds)
open import MonomorphicCalculus.Syntax.Types S
open import MonomorphicCalculus.Syntax.Data          S using (⟪_⟫; compareᵈ; ⌈_⌉; ⌈_⌉ᵇ)
open import MonomorphicCalculus.Syntax.Contexts      S
open import MonomorphicCalculus.Syntax.Terms      S
open import MonomorphicCalculus.Syntax.Renaming      S
open import MonomorphicCalculus.Syntax.Renaming.Action S using (V-rename; C-rename)
open import MonomorphicCalculus.Syntax.Substitution  S

open import MonomorphicCalculus.EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; ⟨⟩-≤; ⟨⟩-≤-refl; ⟨⟩-εᵘ∘η≡id; εᵘ)
open GroundTypes GTy
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Data S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Recursion S Cat Fut Pst Adj GTy Mon GE

open import MonomorphicCalculus.EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE

-- (`var-morphism-Hd` lives in `Interpretation.Variables`,
--  `exch-ren-mor` in `Interpretation.Renaming`.)

sound-unit-eta : ∀ {Γ} → (V : Γ ⊢ᵛ⦂ unit) → Soundᵛ≡ᵗʰ (unit-eta V)
sound-unit-eta V pV _ = terminalᵐ-unique

sound-fun-eta : ∀ {Γ A C} → (V : Γ ⊢ᵛ⦂ A ⇒ C) → Soundᵛ≡ᵗʰ (fun-eta V)
sound-fun-eta {Γ} {A} V pV (p₁ , _) =
    ≈ᵐ-sym (uncurryᵐ-curryᵐ-iso (⟦ V ⟧ᵛᵗ pV))
  ∙ curryᵐ-cong (  ≈ᵐ-sym (uncurryᵐ-cong (∘ᵐ-identityˡ (⟦ V ⟧ᵛᵗ pV)))
                 ∙ uncurryᵐ-nat (⟦ V ⟧ᵛᵗ pV) idᵐ
                 ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
                 ∙ ∘ᵐ-congʳ (≈ᵐ-sym
                     (⟨ ⟦⟧ᵛᵗ-irr (V-rename wk-ren V) p₁ (renᵛ wk-ren V pV)
                        ∙ V-rename-nat wk-ren V pV
                      , var-morphism-Hd {Γ} {A} (≾ᵘ-ok ≾ᵣ-refl) ⟩ᵐ-cong)))

sound-fun-beta : ∀ {Γ A C} → (M : Γ ∷ A ⊢ᶜ⦂ C) → (W : Γ ⊢ᵛ⦂ A)
               → Soundᶜ≡ᵗʰ (fun-beta M W)
sound-fun-beta M W (pM , pW) pR =
    βᵐ (⟦ M ⟧ᶜᵗ pM) (⟦ W ⟧ᵛᵗ pW)
  ∙ ≈ᵐ-sym (C-subst-nat M split-[] W pM pW)
  ∙ ⟦⟧ᶜᵗ-irr (M [ W ]₀) (subᶜ M split-[] W pM pW) pR

sound-absurd-eta : ∀ {Γ C} → (V : Γ ⊢ᵛ⦂ empty) → (M : Γ ∷ empty ⊢ᶜ⦂ C)
                 → Soundᶜ≡ᵗʰ (absurd-eta V M)
sound-absurd-eta V M pV pR = 𝟘ᵐ-strict (⟦ V ⟧ᵛᵗ pV) _ _

-- The comparison beta: the embedded data denote their points, at which the
-- comparison morphism orders as the data are ordered.

sound-cmp-beta : ∀ {Γ A} → (⋈ : Cmp) → (et : Et A) → (d e : ⟪ A ⟫)
               → Soundᶜ≡ᵗʰ (cmp-beta {Γ = Γ} ⋈ et d e)
sound-cmp-beta ⋈ et d e (pV , pW) pR =
    sound-cmp ⋈ et (⌈ et ⌉ d) (⌈ et ⌉ e) pV pW d e
      (⟦⟧ᵛᵗ-irr (⌈ et ⌉ d) pV (param-⌈⌉ et d) ∙ ⟦⌈⌉⟧ et d)
      (⟦⟧ᵛᵗ-irr (⌈ et ⌉ e) pW (param-⌈⌉ et e) ∙ ⟦⌈⌉⟧ et e)
  ∙ ⟦⟧ᶜᵗ-irr (return ⌈ holds ⋈ (compareᵈ et d e) ⌉ᵇ) _ pR

-- The two boolean betas are the boolean object's own beta laws, read at the
-- interpretation `⟦ true ⟧ᵛᵗ = trueᵐ ∘ᵐ terminalᵐ` of the scrutinee.

sound-if-beta-true : ∀ {Γ C} → (M N : Γ ⊢ᶜ⦂ C) → Soundᶜ≡ᵗʰ (if-beta-true M N)
sound-if-beta-true M N (_ , pM , pN) pM' =
    ifᵐ-true (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  ∙ ⟦⟧ᶜᵗ-irr M pM pM'

sound-if-beta-false : ∀ {Γ C} → (M N : Γ ⊢ᶜ⦂ C) → Soundᶜ≡ᵗʰ (if-beta-false M N)
sound-if-beta-false M N (_ , pM , pN) pN' =
    ifᵐ-false (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  ∙ ⟦⟧ᶜᵗ-irr N pN pN'

-- `if-eta`: the two branches substitute the two booleans into the same body,
-- and `sub-env split-[] true` is `⟨ idᵐ , trueᵐ ∘ᵐ terminalᵐ ⟩ᵐ`, the
-- shape `ifᵐ-η` speaks about. As with `match-eta`, `M` occurs only under a
-- substitution on both sides, so its certificate comes in separately.

sound-if-eta : ∀ {Γ C} → (V : Γ ⊢ᵛ⦂ bool) → (M : Γ ∷ bool ⊢ᶜ⦂ C)
             → Paramᶜ M → Soundᶜ≡ᵗʰ (if-eta V M)
sound-if-eta V M pM (pV , pT , pF) pR =
    ifᵐ-cong ≈ᵐ-refl
      (  ⟦⟧ᶜᵗ-irr (M [ true ]₀) pT (subᶜ M split-[] true pM tt)
       ∙ C-subst-nat M split-[] true pM tt)
      (  ⟦⟧ᶜᵗ-irr (M [ false ]₀) pF (subᶜ M split-[] false pM tt)
       ∙ C-subst-nat M split-[] false pM tt)
  ∙ ≈ᵐ-sym (ifᵐ-η (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM))
  ∙ ≈ᵐ-sym (C-subst-nat M split-[] V pM pV)
  ∙ ⟦⟧ᶜᵗ-irr (M [ V ]₀) (subᶜ M split-[] V pM pV) pR

-- The natural-number betas are those of `matchℕᵐ`; at a successor the branch
-- is then the substitution of the predecessor.

sound-matchℕ-beta-zero : ∀ {Γ C} → (M : Γ ⊢ᶜ⦂ C) → (N : Γ ∷ nat ⊢ᶜ⦂ C)
                       → Soundᶜ≡ᵗʰ (matchℕ-beta-zero M N)
sound-matchℕ-beta-zero M N (pV , pM , pN) pR =
    matchℕᵐ-zero (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  ∙ ⟦⟧ᶜᵗ-irr M pM pR

sound-matchℕ-beta-succ : ∀ {Γ C} → (V : Γ ⊢ᵛ⦂ nat)
                       → (M : Γ ⊢ᶜ⦂ C) → (N : Γ ∷ nat ⊢ᶜ⦂ C)
                       → Soundᶜ≡ᵗʰ (matchℕ-beta-succ V M N)
sound-matchℕ-beta-succ V M N (pV , pM , pN) pR =
    matchℕᵐ-succ (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  ∙ ≈ᵐ-sym (C-subst-nat N split-[] V pN pV)
  ∙ ⟦⟧ᶜᵗ-irr (N [ V ]₀) (subᶜ N split-[] V pN pV) pR

-- `matchℕ-eta`: the zero branch is the body at `zero`, the successor branch
-- the body restricted along `succᵐ`, the shape `matchℕᵐ-η` speaks about.

sound-matchℕ-eta : ∀ {Γ C} → (V : Γ ⊢ᵛ⦂ nat) → (M : Γ ∷ nat ⊢ᶜ⦂ C)
                 → Paramᶜ M → Soundᶜ≡ᵗʰ (matchℕ-eta V M)
sound-matchℕ-eta {Γ} {C} V M pM (pV , pZ , pS) pR =
    matchℕᵐ-cong ≈ᵐ-refl
      (⟦⟧ᶜᵗ-irr (M [ zero ]₀) pZ (subᶜ M split-[] zero pM tt)
       ∙ C-subst-nat M split-[] zero pM tt)
      (⟦⟧ᶜᵗ-irr (C-rename (cong-∷-ren wk-ren) M [ U ]₀) pS
                (subᶜ (C-rename (cong-∷-ren wk-ren) M) split-[] U
                      (renᶜ (cong-∷-ren wk-ren) M pM) tt)
       ∙ C-subst-nat (C-rename (cong-∷-ren wk-ren) M) split-[] U
                     (renᶜ (cong-∷-ren wk-ren) M pM) tt
       ∙ ∘ᵐ-congˡ (C-rename-nat (cong-∷-ren wk-ren) M pM)
       ∙ ∘ᵐ-assoc _ _ _
       ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
                   ∙ ⟨ ∘ᵐ-identityʳ _ ∙ ≈ᵐ-sym (∘ᵐ-identityˡ _)
                     , ∘ᵐ-identityˡ _
                       ∙ ∘ᵐ-congʳ (var-morphism-Hd {Γ} {nat} (≾ᵘ-ok ≾ᵣ-refl)) ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (matchℕᵐ-η (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM))
  ∙ ≈ᵐ-sym (C-subst-nat M split-[] V pM pV)
  ∙ ⟦⟧ᶜᵗ-irr (M [ V ]₀) (subᶜ M split-[] V pM pV) pR
  where
    U : Γ ∷ nat ⊢ᵛ⦂ nat
    U = succ (var Hd (≾ᵘ-ok ≾ᵣ-refl))

-- The recursor's betas, as for the reductions `RECℕ-ZERO`/`RECℕ-SUCC`.

sound-recℕ-beta-zero : ∀ {Γ B ε} → (M : Γ ⊢ᶜ⦂ B ! ε)
                     → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε)
                     → (p : ε ·ₑ ε ≾ₑ ε)
                     → Soundᶜ≡ᵗʰ (recℕ-beta-zero M N p)
sound-recℕ-beta-zero M N p (_ , pM , pN) pR =
  sound-RECℕ-ZERO M N p pM pN ∙ ⟦⟧ᶜᵗ-irr M pM pR

sound-recℕ-beta-succ : ∀ {Γ B ε} → (V : Γ ⊢ᵛ⦂ nat) → (M : Γ ⊢ᶜ⦂ B ! ε)
                     → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε)
                     → (p : ε ·ₑ ε ≾ₑ ε)
                     → Soundᶜ≡ᵗʰ (recℕ-beta-succ V M N p)
sound-recℕ-beta-succ V M N p (pV , pM , pN) pR =
    sound-RECℕ-SUCC V M N p pV pM pN
  ∙ ⟦⟧ᶜᵗ-irr (coerce p (recℕ V M N p ⨟ recℕ-step V N)) _ pR

-- The two sum betas are the coproduct's, read at the interpretation
-- `⟦ inl V ⟧ᵛᵗ = inlᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ` of the scrutinee, after which the branch is
-- the substitution of the payload.

sound-match+-beta-inl : ∀ {Γ A B C} → (V : Γ ⊢ᵛ⦂ A)
                      → (M : Γ ∷ A ⊢ᶜ⦂ C) → (N : Γ ∷ B ⊢ᶜ⦂ C)
                      → Soundᶜ≡ᵗʰ (match+-beta-inl V M N)
sound-match+-beta-inl V M N (pV , pM , pN) pR =
    match+ᵐ-inl (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  ∙ ≈ᵐ-sym (C-subst-nat M split-[] V pM pV)
  ∙ ⟦⟧ᶜᵗ-irr (M [ V ]₀) (subᶜ M split-[] V pM pV) pR

sound-match+-beta-inr : ∀ {Γ A B C} → (V : Γ ⊢ᵛ⦂ B)
                      → (M : Γ ∷ A ⊢ᶜ⦂ C) → (N : Γ ∷ B ⊢ᶜ⦂ C)
                      → Soundᶜ≡ᵗʰ (match+-beta-inr V M N)
sound-match+-beta-inr V M N (pV , pM , pN) pR =
    match+ᵐ-inr (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  ∙ ≈ᵐ-sym (C-subst-nat N split-[] V pN pV)
  ∙ ⟦⟧ᶜᵗ-irr (N [ V ]₀) (subᶜ N split-[] V pN pV) pR

-- `match+-eta`: each branch is the body restricted along an injection, which
-- is the shape `match+ᵐ-η` speaks about. As with `if-eta`, `M` occurs only under
-- a substitution on both sides, so its certificate comes in separately.

sound-match+-eta : ∀ {Γ A B C} → (V : Γ ⊢ᵛ⦂ A |+| B) → (M : Γ ∷ A |+| B ⊢ᶜ⦂ C)
                 → Paramᶜ M → Soundᶜ≡ᵗʰ (match+-eta V M)
sound-match+-eta {Γ} {A} {B} {C} V M pM (pV , pL , pR') pR =
    match+ᵐ-cong ≈ᵐ-refl
      (restrict (inl (var Hd (≾ᵘ-ok ≾ᵣ-refl))) tt inlᵐ refl pL)
      (restrict (inr (var Hd (≾ᵘ-ok ≾ᵣ-refl))) tt inrᵐ refl pR')
  ∙ ≈ᵐ-sym (match+ᵐ-η (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM))
  ∙ ≈ᵐ-sym (C-subst-nat M split-[] V pM pV)
  ∙ ⟦⟧ᶜᵗ-irr (M [ V ]₀) (subᶜ M split-[] V pM pV) pR
  where
    -- the body weakened past the bound payload, then restricted along the
    -- injection that rebuilds the scrutinee from it
    restrict : ∀ {A₀} → (U : Γ ∷ A₀ ⊢ᵛ⦂ A |+| B) → (pU₀ : Paramᵛ U)
             → (ι : ⟦ A₀ ⟧ᵛ →ᵐ ⟦ A |+| B ⟧ᵛ)
             → ⟦ U ⟧ᵛᵗ pU₀ ≡ ι ∘ᵐ var-morphism {Γ ∷ A₀} {A₀} Hd (≾ᵘ-ok ≾ᵣ-refl)
             → (pU : Paramᶜ (C-rename (cong-∷-ren wk-ren) M [ U ]₀))
             → ⟦ C-rename (cong-∷-ren wk-ren) M [ U ]₀ ⟧ᶜᵗ pU
               ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ mapˣᵐ idᵐ ι
    restrict {A₀} U pU₀ ι e pU =
        ⟦⟧ᶜᵗ-irr (C-rename (cong-∷-ren wk-ren) M [ U ]₀) pU
                 (subᶜ (C-rename (cong-∷-ren wk-ren) M) split-[] U
                       (renᶜ (cong-∷-ren wk-ren) M pM) pU₀)
      ∙ C-subst-nat (C-rename (cong-∷-ren wk-ren) M) split-[] U
                    (renᶜ (cong-∷-ren wk-ren) M pM) pU₀
      ∙ ∘ᵐ-congˡ (C-rename-nat (cong-∷-ren wk-ren) M pM)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
                  ∙ ⟨ ∘ᵐ-identityʳ _ ∙ ≈ᵐ-sym (∘ᵐ-identityˡ _)
                    , ∘ᵐ-identityˡ _ ∙ ≡→≈ᵐ e
                      ∙ ∘ᵐ-congʳ (var-morphism-Hd {Γ} {A₀} _) ⟩ᵐ-cong)

-- `match-eta`: re-pairing the two bound components rebuilds the matched value
-- (the product's eta, `⟨⟩ᵐ-unique`). Both sides mention `M` only under a
-- substitution, so its certificate comes in separately (this is the axiom's
-- `Midᶜ` payload).

sound-match-eta : ∀ {Γ A B C} → (V : Γ ⊢ᵛ⦂ A |×| B) → (M : Γ ∷ A |×| B ⊢ᶜ⦂ C)
                → Paramᶜ M → Soundᶜ≡ᵗʰ (match-eta V M)
sound-match-eta {Γ} {A} {B} {C} V M pM (pV , pB) pR =
    ∘ᵐ-congˡ (  ⟦⟧ᶜᵗ-irr ((C-rename ρ M) [ pair ]₀) pB
                  (subᶜ (C-rename ρ M) split-[] pair (renᶜ ρ M pM) (tt , tt))
              ∙ C-subst-nat (C-rename ρ M) split-[] pair (renᶜ ρ M pM) (tt , tt)
              ∙ ∘ᵐ-congˡ (C-rename-nat ρ M pM))
  ∙ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ cart)
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (M [ V ]₀) pR (subᶜ M split-[] V pM pV)
            ∙ C-subst-nat M split-[] V pM pV)
  where
    ρ    = wk-ren ∘ʳ exch-ren ∘ʳ wk-ren ∘ʳ exch-ren
    pair = ⦉ var (Tl-∷ Hd) (≾ᵘ-ok ≾ᵣ-refl) , var Hd (≾ᵘ-ok ≾ᵣ-refl) ⦊

    v = ⟦ V ⟧ᵛᵗ pV

    -- The whole renaming forgets the two components it re-bound: two
    -- exchanges each followed by a weakening leave the environment untouched
    -- apart from dropping `A` and `B`.
    ρ-mor : ⟦ ρ ⟧ʳ ≈ᵐ mapˣᵐ (fstᵐ ∘ᵐ fstᵐ) idᵐ
    ρ-mor =
        ∘ᵐ-congʳ (∘ᵐ-congʳ (  ∘ᵐ-congʳ (exch-ren-mor {Γ ∷ A} {B} {A |×| B})
                            ∙ ⟨⟩ᵐ-fstᵐ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (exch-ren-mor {Γ} {A} {A |×| B}))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
      ∙ mapˣᵐ-∘ _ _ _ _
      ∙ mapˣᵐ-cong ≈ᵐ-refl (∘ᵐ-identityˡ _)

    -- Substituting the re-paired components into the matched environment
    -- rebuilds the matched value: this is the product's eta.
    re-pair : sub-env split-[] pair (tt , tt)
                ∘ᵐ ⟨ ⟨ idᵐ , fstᵐ ∘ᵐ v ⟩ᵐ , sndᵐ ∘ᵐ v ⟩ᵐ
            ≈ᵐ ⟨ ⟨ ⟨ idᵐ , fstᵐ ∘ᵐ v ⟩ᵐ , sndᵐ ∘ᵐ v ⟩ᵐ , v ⟩ᵐ
    re-pair =
        ⟨⟩ᵐ-∘ _ _ _
      ∙ ⟨ ∘ᵐ-identityˡ _
        ,   ⟨⟩ᵐ-∘ _ _ _
          ∙ ⟨   ∘ᵐ-congˡ (  var-morphism-Tl-∷ {Γ ∷ A} {B} {A} Hd _
                          ∙ ∘ᵐ-congˡ (var-morphism-Hd {Γ} {A} _))
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
              ∙ ⟨⟩ᵐ-sndᵐ _ _
            , ∘ᵐ-congˡ (var-morphism-Hd {Γ ∷ A} {B} _) ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong
          ∙ ≈ᵐ-sym (⟨⟩ᵐ-unique _ _ v ≈ᵐ-refl ≈ᵐ-refl) ⟩ᵐ-cong

    cart : ⟦ ρ ⟧ʳ ∘ᵐ sub-env split-[] pair (tt , tt)
                     ∘ᵐ ⟨ ⟨ idᵐ , fstᵐ ∘ᵐ v ⟩ᵐ , sndᵐ ∘ᵐ v ⟩ᵐ
         ≈ᵐ sub-env split-[] V pV
    cart =
        ∘ᵐ-congˡ ρ-mor
      ∙ ∘ᵐ-congʳ re-pair
      ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
      ∙ ⟨   ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
          ∙ ⟨⟩ᵐ-fstᵐ _ _
        , ∘ᵐ-identityˡ _ ⟩ᵐ-cong

sound-match-beta : ∀ {Γ A B C} → (V : Γ ⊢ᵛ⦂ A) → (W : Γ ⊢ᵛ⦂ B) → (M : Γ ∷ A ∷ B ⊢ᶜ⦂ C)
                 → Soundᶜ≡ᵗʰ (match-beta V W M)
sound-match-beta V W M ((pV , pW) , pM) pR =
    ∘ᵐ-congʳ (⟨ ⟨ ≈ᵐ-refl , ⟨⟩ᵐ-fstᵐ _ _ ⟩ᵐ-cong , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr ((M [ V-rename wk-ren W ]₀) [ V ]₀) pR
                (subᶜ₂ M V W pM pV pW)
            ∙ C-subst₂-nat M V W pM pV pW)


-- The list eliminator's betas, as for the reductions at `nil` and `cons`.

sound-matchL-beta-nil : ∀ {Γ A C} → (M : Γ ⊢ᶜ⦂ C) → (N : Γ ∷ A ∷ list A ⊢ᶜ⦂ C)
                      → Soundᶜ≡ᵗʰ (matchL-beta-nil M N)
sound-matchL-beta-nil M N (_ , pM , pN) pR =
  sound-MATCHL-NIL M N pM pN ∙ ⟦⟧ᶜᵗ-irr M pM pR

sound-matchL-beta-cons : ∀ {Γ A C} → (V : Γ ⊢ᵛ⦂ A) → (W : Γ ⊢ᵛ⦂ list A)
                       → (M : Γ ⊢ᶜ⦂ C) → (N : Γ ∷ A ∷ list A ⊢ᶜ⦂ C)
                       → Soundᶜ≡ᵗʰ (matchL-beta-cons V W M N)
sound-matchL-beta-cons V W M N ((pV , pW) , pM , pN) pR =
    sound-MATCHL-CONS V W M N pV pW pM pN
  ∙ ⟦⟧ᶜᵗ-irr ((N [ V-rename wk-ren W ]₀) [ V ]₀) _ pR

-- `matchL-eta`: the `nil` branch is the body at `nil`, the `cons` branch the
-- body at the re-consed components, the shape `matchLᵐ-η` speaks about. `M`
-- occurs only under a substitution on both sides.

sound-matchL-eta : ∀ {Γ A C} → (V : Γ ⊢ᵛ⦂ list A) → (M : Γ ∷ list A ⊢ᶜ⦂ C)
                 → Paramᶜ M → Soundᶜ≡ᵗʰ (matchL-eta V M)
sound-matchL-eta {Γ} {A} {C} V M pM (pV , pZ , pS) pR =
    matchLᵐ-cong ≈ᵐ-refl
      (⟦⟧ᶜᵗ-irr (M [ nil ]₀) pZ (subᶜ M split-[] nil pM tt)
       ∙ C-subst-nat M split-[] nil pM tt)
      (⟦⟧ᶜᵗ-irr ((C-rename ρ M) [ U ]₀) pS
                (subᶜ (C-rename ρ M) split-[] U (renᶜ ρ M pM) (tt , tt))
       ∙ C-subst-nat (C-rename ρ M) split-[] U (renᶜ ρ M pM) (tt , tt)
       ∙ ∘ᵐ-congˡ (C-rename-nat ρ M pM)
       ∙ ∘ᵐ-assoc _ _ _
       ∙ ∘ᵐ-congʳ cart)
  ∙ ≈ᵐ-sym (matchLᵐ-η (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM))
  ∙ ≈ᵐ-sym (C-subst-nat M split-[] V pM pV)
  ∙ ⟦⟧ᶜᵗ-irr (M [ V ]₀) (subᶜ M split-[] V pM pV) pR
  where
    ρ = wk-ren ∘ʳ exch-ren ∘ʳ wk-ren ∘ʳ exch-ren
    U = cons (var (Tl-∷ Hd) (≾ᵘ-ok ≾ᵣ-refl)) (var Hd (≾ᵘ-ok ≾ᵣ-refl))

    -- the renaming forgets the two re-bound components
    ρ-mor : ⟦ ρ ⟧ʳ ≈ᵐ mapˣᵐ (fstᵐ ∘ᵐ fstᵐ) idᵐ
    ρ-mor =
        ∘ᵐ-congʳ (∘ᵐ-congʳ (  ∘ᵐ-congʳ (exch-ren-mor {Γ ∷ A} {list A} {list A})
                            ∙ ⟨⟩ᵐ-fstᵐ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (exch-ren-mor {Γ} {A} {list A}))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
      ∙ mapˣᵐ-∘ _ _ _ _
      ∙ mapˣᵐ-cong ≈ᵐ-refl (∘ᵐ-identityˡ _)

    cart : ⟦ ρ ⟧ʳ ∘ᵐ sub-env split-[] U (tt , tt)
         ≈ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , consᵐ ∘ᵐ mapˣᵐ sndᵐ idᵐ ⟩ᵐ
    cart =
        ∘ᵐ-congˡ ρ-mor
      ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
      ∙ ⟨ ∘ᵐ-identityʳ _
        , ∘ᵐ-identityˡ _
          ∙ ∘ᵐ-congʳ ⟨ var-morphism-Tl-∷ {Γ ∷ A} {list A} {A} Hd _
                       ∙ ∘ᵐ-congˡ (var-morphism-Hd {Γ} {A} _)
                     , var-morphism-Hd {Γ ∷ A} {list A} _
                       ∙ ≈ᵐ-sym (∘ᵐ-identityˡ _) ⟩ᵐ-cong ⟩ᵐ-cong

-- The list recursor's betas, as for the reductions.

sound-recL-beta-nil : ∀ {Γ A B ε} → (M : Γ ⊢ᶜ⦂ B ! ε)
                    → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε)
                    → (p : ε ·ₑ ε ≾ₑ ε)
                    → Soundᶜ≡ᵗʰ (recL-beta-nil M N p)
sound-recL-beta-nil M N p (_ , pM , pN) pR =
  sound-RECL-NIL M N p pM pN ∙ ⟦⟧ᶜᵗ-irr M pM pR

sound-recL-beta-cons : ∀ {Γ A B ε} → (V : Γ ⊢ᵛ⦂ A) → (W : Γ ⊢ᵛ⦂ list A)
                     → (M : Γ ⊢ᶜ⦂ B ! ε)
                     → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε)
                     → (p : ε ·ₑ ε ≾ₑ ε)
                     → Soundᶜ≡ᵗʰ (recL-beta-cons V W M N p)
sound-recL-beta-cons V W M N p ((pV , pW) , pM , pN) pR =
    sound-RECL-CONS V W M N p pV pW pM pN
  ∙ ⟦⟧ᶜᵗ-irr (coerce p (recL W M N p ⨟ recL-step V W N)) _ pR
