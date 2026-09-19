------------------------------------------------------------------
-- Grade-naturality of grounding, for the covariant fragment      --
--                                                                --
-- The fundamental lemma: a mirrored derivation certified by      --
-- `CovD` denotes, at the two instantiations `θ ,ᵍᵉ ε₁` and       --
-- `θ ,ᵍᵉ ε₂` of the rigid grade variable, two morphisms that      --
-- commute with the covariance coercions of                        --
-- `Inference.ParamGround.Covariance`.                             --
--                                                                --
-- `CovD` excludes a *nested* `handle` (the handler algebra's      --
-- fold is not known to be natural in the ambient instantiation),  --
-- a `var` reaching across the `_ᴱ̂` barrier, and a `_⨟_` whose     --
-- continuation grade mentions the rigid variable (the model       --
-- interface has `T-≤-μᵀ` only in the *outer* grade). Every other  --
-- former is covered.                                             --
------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import Inference.Scopes

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module Inference.ParamGround.Uniform
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_; Dec; yes; no)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types    S
open import Syntax.Contexts S
open import Syntax.Language S

open import Inference.Open.Grades           S
open import Inference.Open.Types            S
open import Inference.Open.Contexts         S
open import Inference.Open.Hyps             S
open import Inference.Open.Language         S
open import Inference.Open.GroundingTheorem S

open import Inference.Open.Grounding S
  renaming (⟦_⟧ᵛ to ⟦_⟧ᵒᵛ; ⟦_⟧ᶜ to ⟦_⟧ᵒᶜ; ⟦_⟧ᶜᵗˣ to ⟦_⟧ᵒᶜᵗˣ)

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-≤; []-idᵐ; []-∘ᵐ; []-congᶠ;
                       []-≤-refl; []-≤-trans; []-≤-nat)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-≤; ⟨⟩-idᵐ; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ;
                     ⟨⟩-≤-refl; ⟨⟩-≤-trans; ⟨⟩-≤-nat; ⟨⟩-≤-irr)
open Adjunction Adj using (η⊣; ε⊣; η⊣-nat; ε⊣-nat; η⊣-≤; ε⊣-≤)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types     S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts  S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms     S Cat Fut Pst Adj GTy Mon GE

open import Inference.ParamGround S Cat Fut Pst Adj GTy Mon GE
  using (ground-mono-e; ground-mono-r; ground-mono-clause)

open import Inference.ParamGround.Covariance S Cat Fut Pst Adj GTy Mon GE

--------------------------------------------------------------
-- Transports                                                --
--------------------------------------------------------------

-- Object-level coercions, and the two shapes of `subst` the interpretation
-- of `perform` inserts around its ground-typed parameter and arity.

coeᵒ⁺ : ∀ {O O' : Obj} → O ≡ O' → O →ᵐ O'
coeᵒ⁺ refl = idᵐ

coeᵒ⁻ : ∀ {O O' : Obj} → O ≡ O' → O' →ᵐ O
coeᵒ⁻ refl = idᵐ

subst-cod : ∀ {X : Obj} {O O' : Obj} → (e : O ≡ O') → (f : X →ᵐ O)
          → subst (λ Z → X →ᵐ Z) e f ≈ᵐ coeᵒ⁺ e ∘ᵐ f
subst-cod refl f = ≈ᵐ-sym (∘ᵐ-identityˡ _)

subst-dom : ∀ {W Z : Obj} {O O' : Obj} → (e : O ≡ O') → (g : (W ×ᵐ O) →ᵐ Z)
          → subst (λ P → (W ×ᵐ P) →ᵐ Z) e g ≈ᵐ g ∘ᵐ mapˣᵐ idᵐ (coeᵒ⁻ e)
subst-dom refl g = ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-congʳ mapˣᵐ-idᵐ) (∘ᵐ-identityʳ _))

-- The type-level transports `groundV`/`groundC` insert, read off a
-- denotation. Each is stated with the *transported* certificate as the
-- argument, so that the caller need not construct the original one.

ty-Paramᵛ⁻ : ∀ {Δ A A'} → (e : A ≡ A') → (V : Δ ⊢V⦂ A)
           → Paramᵛ (subst (λ A₀ → Δ ⊢V⦂ A₀) e V) → Paramᵛ V
ty-Paramᵛ⁻ refl V p = p

ty-den : ∀ {Δ A A'} → (e : A ≡ A') → (V : Δ ⊢V⦂ A)
       → (p : Paramᵛ (subst (λ A₀ → Δ ⊢V⦂ A₀) e V))
       → ⟦ subst (λ A₀ → Δ ⊢V⦂ A₀) e V ⟧ᵛᵗ p
       ≈ᵐ inv⁺ e ∘ᵐ ⟦ V ⟧ᵛᵗ (ty-Paramᵛ⁻ e V p)
ty-den refl V p = ≈ᵐ-sym (∘ᵐ-identityˡ _)

∷-Paramᶜ⁻ : ∀ {Δ A A' C} → (e : A ≡ A') → (M : Δ ∷ A ⊢C⦂ C)
          → Paramᶜ (subst (λ A₀ → Δ ∷ A₀ ⊢C⦂ C) e M) → Paramᶜ M
∷-Paramᶜ⁻ refl M p = p

∷-den : ∀ {Δ A A' C} → (e : A ≡ A') → (M : Δ ∷ A ⊢C⦂ C)
      → (p : Paramᶜ (subst (λ A₀ → Δ ∷ A₀ ⊢C⦂ C) e M))
      → ⟦ subst (λ A₀ → Δ ∷ A₀ ⊢C⦂ C) e M ⟧ᶜᵗ p
      ≈ᵐ ⟦ M ⟧ᶜᵗ (∷-Paramᶜ⁻ e M p) ∘ᵐ mapˣᵐ idᵐ (inv⁻ e)
∷-den refl M p = ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-congʳ mapˣᵐ-idᵐ) (∘ᵐ-identityʳ _))

subst₂-Paramᶜ⁻ : ∀ {Δ Δ' C C'} → (e₁ : Δ ≡ Δ') → (e₂ : C ≡ C') → (M : Δ ⊢C⦂ C)
               → Paramᶜ (subst₂ _⊢C⦂_ e₁ e₂ M) → Paramᶜ M
subst₂-Paramᶜ⁻ refl refl M p = p

invˣ⁻ : ∀ {Γ Δ : Ctx} → Γ ≡ Δ → ⟦ Δ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟧ᶜᵗˣ
invˣ⁻ refl = idᵐ

subst₂-den : ∀ {Δ Δ' C C'} → (e₁ : Δ ≡ Δ') → (e₂ : C ≡ C') → (M : Δ ⊢C⦂ C)
           → (p : Paramᶜ (subst₂ _⊢C⦂_ e₁ e₂ M))
           → ⟦ subst₂ _⊢C⦂_ e₁ e₂ M ⟧ᶜᵗ p
           ≈ᵐ invᶜ⁺ e₂ ∘ᵐ ⟦ M ⟧ᶜᵗ (subst₂-Paramᶜ⁻ e₁ e₂ M p) ∘ᵐ invˣ⁻ e₁
subst₂-den refl refl M p =
  ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-identityʳ _)) (∘ᵐ-identityˡ _))

inv⁻≈inv⁺ : ∀ {A B : VType} → (e : A ≡ B) → inv⁻ e ≈ᵐ inv⁺ (sym e)
inv⁻≈inv⁺ refl = ≈ᵐ-refl

inv⁺-sym-trans : ∀ {A B C : VType} → (e : A ≡ B) → (e' : A ≡ C)
               → inv⁺ e' ∘ᵐ inv⁻ e ≈ᵐ inv⁻ (trans (sym e') e)
inv⁺-sym-trans refl refl = ∘ᵐ-identityˡ _

--------------------------------------------------------------
-- Derived model laws                                        --
--------------------------------------------------------------

-- Application reindexed by the exponential's functorial action.

appᵐ-curryᵐ : ∀ {X A B} → (k : X ×ᵐ A →ᵐ B)
            → appᵐ ∘ᵐ mapˣᵐ (curryᵐ k) idᵐ ≈ᵐ k
appᵐ-curryᵐ k =
     ≈ᵐ-sym (uncurryᵐ-nat (curryᵐ k) idᵐ)
  ∙≈ uncurryᵐ-cong (∘ᵐ-identityˡ _)
  ∙≈ curryᵐ-uncurryᵐ-iso k

appᵐ-map⇒ᵐ : ∀ {X A B C D} → (f : A →ᵐ B) → (g : C →ᵐ D) → (b : X →ᵐ A)
           → appᵐ ∘ᵐ mapˣᵐ (map⇒ᵐ f g) b
           ≈ᵐ g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ (f ∘ᵐ b)
appᵐ-map⇒ᵐ f g b =
     ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘ (map⇒ᵐ f g) idᵐ idᵐ b
                        ∙≈ mapˣᵐ-cong (∘ᵐ-identityʳ _) (∘ᵐ-identityˡ _)))
  ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙≈ ∘ᵐ-congˡ (appᵐ-curryᵐ _)
  ∙≈ ∘ᵐ-assoc _ _ _
  ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘ idᵐ f idᵐ b
                          ∙≈ mapˣᵐ-cong (∘ᵐ-identityˡ _) ≈ᵐ-refl))

-- Precomposing an abstraction, with both components reindexed.

map⇒ᵐ-curryᵐ₂ : ∀ {X A A' C D} → (f : A' →ᵐ A) → (g : C →ᵐ D) → (k : X ×ᵐ A →ᵐ C)
              → map⇒ᵐ f g ∘ᵐ curryᵐ k ≈ᵐ curryᵐ (g ∘ᵐ (k ∘ᵐ mapˣᵐ idᵐ f))
map⇒ᵐ-curryᵐ₂ f g k =
     ≈ᵐ-sym (curryᵐ-nat (curryᵐ k) (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f))
  ∙≈ curryᵐ-cong
       (   ∘ᵐ-assoc _ _ _
        ∙≈ ∘ᵐ-congʳ (   ∘ᵐ-assoc _ _ _
                     ∙≈ ∘ᵐ-congʳ (   mapˣᵐ-∘ idᵐ f (curryᵐ k) idᵐ
                                  ∙≈ mapˣᵐ-cong (∘ᵐ-identityˡ _) (∘ᵐ-identityʳ _)
                                  ∙≈ ≈ᵐ-sym (   mapˣᵐ-∘ (curryᵐ k) idᵐ idᵐ f
                                             ∙≈ mapˣᵐ-cong (∘ᵐ-identityʳ _)
                                                           (∘ᵐ-identityˡ _)))
                     ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                     ∙≈ ∘ᵐ-congˡ (appᵐ-curryᵐ k)))

-- The exponential's action on the codomain is functorial.

map⇒ᵐ-∘ʳ : ∀ {A B C D} → (g : C →ᵐ D) → (h : B →ᵐ C)
         → map⇒ᵐ (idᵐ {A}) (g ∘ᵐ h) ≈ᵐ map⇒ᵐ idᵐ g ∘ᵐ map⇒ᵐ idᵐ h
map⇒ᵐ-∘ʳ g h = ≈ᵐ-sym (map⇒ᵐ-curryᵐ g _ ∙≈ curryᵐ-cong (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))

-- Postcomposing a boolean elimination (only precomposition is a field).

ifᵐ-post : ∀ {X A B} → (b : X →ᵐ 𝔹ᵐ) → (m n : X →ᵐ A) → (g : A →ᵐ B)
         → g ∘ᵐ ifᵐ b m n ≈ᵐ ifᵐ b (g ∘ᵐ m) (g ∘ᵐ n)
ifᵐ-post {X} {A} b m n g =
     ≈ᵐ-sym lhs
  ∙≈ ifᵐ-η b (g ∘ᵐ ifᵐ sndᵐ (m ∘ᵐ fstᵐ) (n ∘ᵐ fstᵐ))
  ∙≈ ifᵐ-cong ≈ᵐ-refl (branch ∙≈ ∘ᵐ-congʳ (ifᵐ-true m n))
                      (branch ∙≈ ∘ᵐ-congʳ (ifᵐ-false m n))
  where
    step : ∀ {Y} → (u : Y →ᵐ X) → (c : Y →ᵐ 𝔹ᵐ)
         → ifᵐ sndᵐ (m ∘ᵐ fstᵐ) (n ∘ᵐ fstᵐ) ∘ᵐ ⟨ u , c ⟩ᵐ ≈ᵐ ifᵐ c (m ∘ᵐ u) (n ∘ᵐ u)
    step u c =
         ifᵐ-∘ _ _ _ _
      ∙≈ ifᵐ-cong (⟨⟩ᵐ-sndᵐ _ _)
                  (∘ᵐ-assoc _ _ _ ∙≈ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                  (∘ᵐ-assoc _ _ _ ∙≈ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))

    lhs : (g ∘ᵐ ifᵐ sndᵐ (m ∘ᵐ fstᵐ) (n ∘ᵐ fstᵐ)) ∘ᵐ ⟨ idᵐ , b ⟩ᵐ
        ≈ᵐ g ∘ᵐ ifᵐ b m n
    lhs =
         ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ (step idᵐ b)
      ∙≈ ∘ᵐ-congʳ (ifᵐ-cong ≈ᵐ-refl (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _))

    branch : ∀ {c : 𝟙ᵐ →ᵐ 𝔹ᵐ}
           → (g ∘ᵐ ifᵐ sndᵐ (m ∘ᵐ fstᵐ) (n ∘ᵐ fstᵐ))
               ∘ᵐ ⟨ idᵐ , c ∘ᵐ terminalᵐ ⟩ᵐ
           ≈ᵐ g ∘ᵐ ifᵐ (c ∘ᵐ terminalᵐ) m n
    branch =
         ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ (step idᵐ _)
      ∙≈ ∘ᵐ-congʳ (ifᵐ-cong ≈ᵐ-refl (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _))

-- The inner grade of `μᵀ` may be relaxed along an *equality* of grades.

μᵀ-inner-≡ : ∀ {A ε ϵ₁ ϵ₂} → (e : ϵ₁ ≡ ϵ₂)
           → (w : ϵ₁ ≾ₑ ϵ₂) → (w' : ε ·ₑ ϵ₁ ≾ₑ ε ·ₑ ϵ₂)
           → μᵀ {A} {ε} {ϵ₂} ∘ᵐ Tᶠ (T-≤ w) ≈ᵐ T-≤ w' ∘ᵐ μᵀ {A} {ε} {ϵ₁}
μᵀ-inner-≡ refl w w' =
     ∘ᵐ-congʳ (T-congᶠ (T-≤-refl w) ∙≈ T-idᵐ)
  ∙≈ ∘ᵐ-identityʳ _
  ∙≈ ≈ᵐ-sym (∘ᵐ-congˡ (T-≤-refl w') ∙≈ ∘ᵐ-identityˡ _)

--------------------------------------------------------------
-- Covariance certificates for derivations                   --
--------------------------------------------------------------

-- Which variable uses are admitted: those that stay on this side of the
-- `_ᴱ̂` barrier (across one the grounded witness is built by `∈-ᴱ`, whose
-- two readings the coercions of `Covariance` do not relate).

NoCross : 𝔹 → Set
NoCross false = ⊤
NoCross true  = ⊥

mutual

  CovDV : ∀ {Θ m} {Q : Hyps (Θ +e)} {Γ : OCtx (Θ +e) m} {A : OVType (Θ +e)}
        → Q ∣ Γ ⊢V⦂ A → Set
  CovDV (var x ok)  = NoCross (crossesᴱ̂ x)
  CovDV (const B c) = ⊤
  CovDV ⋆           = ⊤
  CovDV true        = ⊤
  CovDV false       = ⊤
  CovDV ⦉ V , W ⦊    = CovDV V × CovDV W
  CovDV (lam {A} M) = NoNewV A × CovDC M

  CovDC : ∀ {Θ m} {Q : Hyps (Θ +e)} {Γ : OCtx (Θ +e) m} {C : OCType (Θ +e)}
        → Q ∣ Γ ⊢C⦂ C → Set
  CovDC (return V)              = CovDV V
  CovDC (_⨟_ {A} {B} {ε'} M N)  = NoNewE ε' × CovV A × CovDC M × CovDC N
  CovDC (_·_ {A} V W)           = NoNewV A × CovDV V × CovDV W
  CovDC (match_`in_ {A} {B} V M) = CovV A × CovV B × CovDV V × CovDC M
  CovDC (absurd V)              = CovDV V
  CovDC (if V `then M `else N)  = CovDV V × CovDC M × CovDC N
  CovDC (perform op V M)        = CovDV V × CovDC M
  CovDC (delay τ M)             = CovDC M
  CovDC (handle M `with H `in N) = ⊥
  CovDC (unbox x ok N)          = NoCross (crossesᴱ̂ x) × CovDC N
  CovDC (box {A} ρ V N)         = NoNewR ρ × CovV A × CovDV V × CovDC N
  CovDC (coerce le M)           = CovDC M

--------------------------------------------------------------
-- The fundamental lemma                                     --
--------------------------------------------------------------

module Fund {Θ : Scope} (θ : Grounding Θ) {ε₁ ε₂ : E} (q : ε₁ ≾ₑ ε₂) where

  open Cov θ q

  mutual

    Cov-groundV :
        ∀ {m} {Q : Hyps (Θ +e)} {Γ : OCtx (Θ +e) m} {A : OVType (Θ +e)}
      → (h₁ : θ₁ ⊨ᴴ Q) → (h₂ : θ₂ ⊨ᴴ Q) → (D : Q ∣ Γ ⊢V⦂ A)
      → (cΓ : CovCtx Γ) → (cA : CovV A) → (cD : CovDV D)
      → (p₁ : Paramᵛ (groundV θ₁ h₁ D)) → (p₂ : Paramᵛ (groundV θ₂ h₂ D))
      → ⟦ groundV θ₂ h₂ D ⟧ᵛᵗ p₂ ∘ᵐ covCtx Γ cΓ
      ≈ᵐ covV A cA ∘ᵐ ⟦ groundV θ₁ h₁ D ⟧ᵛᵗ p₁

    Cov-groundV h₁ h₂ (var x ok) cΓ cA cD p₁ p₂ =
      cov-var-D h₁ h₂ cΓ cA (crossesᴱ̂ x) x refl ok cD
    Cov-groundV h₁ h₂ (const B c) cΓ cA cD p₁ p₂ =
         ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ terminalᵐ-unique
      ∙≈ ≈ᵐ-sym (∘ᵐ-identityˡ _)
    Cov-groundV h₁ h₂ ⋆ cΓ cA cD p₁ p₂ =
      terminalᵐ-unique ∙≈ ≈ᵐ-sym (∘ᵐ-identityˡ _)
    Cov-groundV h₁ h₂ true cΓ cA cD p₁ p₂ =
         ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ terminalᵐ-unique
      ∙≈ ≈ᵐ-sym (∘ᵐ-identityˡ _)
    Cov-groundV h₁ h₂ false cΓ cA cD p₁ p₂ =
         ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ terminalᵐ-unique
      ∙≈ ≈ᵐ-sym (∘ᵐ-identityˡ _)
    Cov-groundV h₁ h₂ ⦉ V , W ⦊ cΓ (cA , cB) (cV , cW) (pv₁ , pw₁) (pv₂ , pw₂) =
         ⟨⟩ᵐ-∘ _ _ _
      ∙≈ ⟨ Cov-groundV h₁ h₂ V cΓ cA cV pv₁ pv₂
         , Cov-groundV h₁ h₂ W cΓ cB cW pw₁ pw₂ ⟩ᵐ-cong
      ∙≈ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _)
    Cov-groundV h₁ h₂ (lam {A} {C} M) cΓ (nA , cC) (nA' , cM) p₁ p₂ =
         ≈ᵐ-sym (curryᵐ-nat _ _)
      ∙≈ curryᵐ-cong
           (   ∘ᵐ-congʳ (≈ᵐ-sym (   mapˣᵐ-∘ _ _ _ _
                                 ∙≈ mapˣᵐ-cong (∘ᵐ-identityʳ _)
                                               (inv⁺∘inv⁻ (nonew-v A nA))))
            ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
            ∙≈ ∘ᵐ-congˡ (∘ᵐ-congʳ (mapˣᵐ-cong ≈ᵐ-refl
                                     (≈ᵐ-sym (covV-nn A (nn⇒CovV A nA) nA)))
                          ∙≈ Cov-groundC h₁ h₂ M (cΓ , nn⇒CovV A nA) cC cM p₁ p₂)
            ∙≈ ∘ᵐ-assoc _ _ _)
      ∙≈ ≈ᵐ-sym (map⇒ᵐ-curryᵐ₂ _ _ _)

    Cov-groundC :
        ∀ {m} {Q : Hyps (Θ +e)} {Γ : OCtx (Θ +e) m} {C : OCType (Θ +e)}
      → (h₁ : θ₁ ⊨ᴴ Q) → (h₂ : θ₂ ⊨ᴴ Q) → (D : Q ∣ Γ ⊢C⦂ C)
      → (cΓ : CovCtx Γ) → (cC : CovC C) → (cD : CovDC D)
      → (p₁ : Paramᶜ (groundC θ₁ h₁ D)) → (p₂ : Paramᶜ (groundC θ₂ h₂ D))
      → ⟦ groundC θ₂ h₂ D ⟧ᶜᵗ p₂ ∘ᵐ covCtx Γ cΓ
      ≈ᵐ covC C cC ∘ᵐ ⟦ groundC θ₁ h₁ D ⟧ᶜᵗ p₁

    Cov-groundC h₁ h₂ (return V) cΓ cA cV p₁ p₂ =
         ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ (Cov-groundV h₁ h₂ V cΓ cA cV p₁ p₂)
      ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congˡ (ηᵀ-nat _)
      ∙≈ ∘ᵐ-assoc _ _ _
      ∙≈ ≈ᵐ-sym (∘ᵐ-congˡ (∘ᵐ-congʳ (T-≤-refl _) ∙≈ ∘ᵐ-identityʳ _))

    Cov-groundC {Γ = Γ} h₁ h₂ (absurd V) cΓ cC cV p₁ p₂ =
      𝟘ᵐ-strict (⟦ groundV θ₂ h₂ V ⟧ᵛᵗ p₂ ∘ᵐ covCtx Γ cΓ) _ _

    Cov-groundC h₁ h₂ (if V `then M `else N) cΓ cC (cV , cM , cN)
                (pv₁ , pm₁ , pn₁) (pv₂ , pm₂ , pn₂) =
         ifᵐ-∘ _ _ _ _
      ∙≈ ifᵐ-cong (Cov-groundV h₁ h₂ V cΓ tt cV pv₁ pv₂ ∙≈ ∘ᵐ-identityˡ _)
                  (Cov-groundC h₁ h₂ M cΓ cC cM pm₁ pm₂)
                  (Cov-groundC h₁ h₂ N cΓ cC cN pn₁ pn₂)
      ∙≈ ≈ᵐ-sym (ifᵐ-post _ _ _ _)

    Cov-groundC h₁ h₂ (coerce {A} {ε} {ε'} le M) cΓ cA cM p₁ p₂ =
         ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ (Cov-groundC h₁ h₂ M cΓ cA cM p₁ p₂)
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym (T-≤-nat _ _))
      ∙≈ ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ
           (   T-≤-trans _ _ (≾ₑ-trans (ground-mono-e {θ = θ} q ε) (ground-≾ₑ h₂ le))
            ∙≈ T-≤-irr _ (≾ₑ-trans (ground-≾ₑ h₁ le) (ground-mono-e {θ = θ} q ε'))
            ∙≈ ≈ᵐ-sym (T-≤-trans (ground-≾ₑ h₁ le) (ground-mono-e {θ = θ} q ε') _)))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

    Cov-groundC h₁ h₂ (_·_ {A} {C} V W) cΓ cC (nA , cV , cW)
                (pv₁ , pw₁) (pv₂ , pw₂) =
         ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
      ∙≈ ∘ᵐ-congʳ ⟨ Cov-groundV h₁ h₂ V cΓ (nA , cC) cV pv₁ pv₂
                  , Cov-groundV h₁ h₂ W cΓ (nn⇒CovV A nA) cW pw₁ pw₂
                      ∙≈ ∘ᵐ-congˡ (covV-nn A (nn⇒CovV A nA) nA) ⟩ᵐ-cong
      ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))
      ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congˡ (appᵐ-map⇒ᵐ (inv⁻ (nonew-v A nA)) (covC C cC)
                             (inv⁺ (nonew-v A nA)))
      ∙≈ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congʳ
           (mapˣᵐ-cong ≈ᵐ-refl (inv⁻∘inv⁺ (nonew-v A nA)) ∙≈ mapˣᵐ-idᵐ)))
      ∙≈ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-identityʳ _))
      ∙≈ ∘ᵐ-assoc _ _ _

    Cov-groundC {Γ = Γ} h₁ h₂ (match_`in_ {A} {B} V M) cΓ cC (cA , cB , cV , cM)
                (pv₁ , pm₁) (pv₂ , pm₂) =
         ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ (   ⟨⟩ᵐ-∘ _ _ _
                   ∙≈ ⟨    ⟨⟩ᵐ-∘ _ _ _
                        ∙≈ ⟨ ∘ᵐ-identityˡ _ , fst-step ⟩ᵐ-cong
                        ∙≈ ≈ᵐ-sym (   mapˣᵐ-∘⟨⟩ _ _ _ _
                                   ∙≈ ⟨ ∘ᵐ-identityʳ _ , ≈ᵐ-refl ⟩ᵐ-cong)
                      , snd-step ⟩ᵐ-cong
                   ∙≈ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))
      ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congˡ (Cov-groundC h₁ h₂ M ((cΓ , cA) , cB) cC cM pm₁ pm₂)
      ∙≈ ∘ᵐ-assoc _ _ _
      where
        fst-step :
            (fstᵐ ∘ᵐ ⟦ groundV θ₂ h₂ V ⟧ᵛᵗ pv₂) ∘ᵐ covCtx Γ cΓ
          ≈ᵐ covV A cA ∘ᵐ (fstᵐ ∘ᵐ ⟦ groundV θ₁ h₁ V ⟧ᵛᵗ pv₁)
        fst-step =
             ∘ᵐ-assoc _ _ _
          ∙≈ ∘ᵐ-congʳ (Cov-groundV h₁ h₂ V cΓ (cA , cB) cV pv₁ pv₂)
          ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙≈ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
          ∙≈ ∘ᵐ-assoc _ _ _

        snd-step :
            (sndᵐ ∘ᵐ ⟦ groundV θ₂ h₂ V ⟧ᵛᵗ pv₂) ∘ᵐ covCtx Γ cΓ
          ≈ᵐ covV B cB ∘ᵐ (sndᵐ ∘ᵐ ⟦ groundV θ₁ h₁ V ⟧ᵛᵗ pv₁)
        snd-step =
             ∘ᵐ-assoc _ _ _
          ∙≈ ∘ᵐ-congʳ (Cov-groundV h₁ h₂ V cΓ (cA , cB) cV pv₁ pv₂)
          ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙≈ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)
          ∙≈ ∘ᵐ-assoc _ _ _

    Cov-groundC h₁ h₂ (delay τ M) cΓ cA cM p₁ p₂ =
         ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat _)))
      ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ
           (   ≈ᵐ-sym (∘ᵐ-congʳ (   ∘ᵐ-congˡ (⟨⟩-≤-irr _ ≾ᵣ-refl ∙≈ ⟨⟩-≤-refl)
                                 ∙≈ ∘ᵐ-identityˡ _))
            ∙≈ Cov-groundC h₁ h₂ M cΓ cA cM p₁ p₂)))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-∘ᵐ _ _ ∙≈ ∘ᵐ-congˡ ([]-∘ᵐ _ _)))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙≈ ∘ᵐ-congˡ (∘ᵐ-congˡ (delayᵀ-nat τ _))
      ∙≈ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congˡ (∘ᵐ-congʳ (delayᵀ-≤ τ _))
      ∙≈ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-irr _ _)))
      ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙≈ ∘ᵐ-assoc _ _ _

    Cov-groundC h₁ h₂ (perform op V M) cΓ cA (cV , cM)
                (pv₁ , pm₁) (pv₂ , pm₂) =
      cov-perform h₁ h₂ op V M cΓ cA cV cM pv₁ pm₁ pv₂ pm₂

    Cov-groundC h₁ h₂ (_⨟_ {A} {B} {ε'} {ε} M N) cΓ cB (nε' , cA , cM , cN)
                (pm₁ , pn₁) (pm₂ , pn₂) =
      cov-seq h₁ h₂ M N cΓ cB nε' cA cM cN pm₁ pn₁ pm₂ pn₂

    Cov-groundC h₁ h₂ (unbox x ok N) cΓ cC (nc , cN) p₁ p₂ =
      cov-unbox h₁ h₂ cΓ cC (crossesᴱ̂ x) x refl ok nc N cN p₁ p₂

    Cov-groundC h₁ h₂ (box ρ V N) cΓ cC (nρ , cA , cV , cN)
                (pv₁ , pn₁) (pv₂ , pn₂) =
      cov-box h₁ h₂ ρ V N cΓ cC nρ cA cV cN pv₁ pn₁ pv₂ pn₂

    ----------------------------------------------------------
    -- The cases with content                                --
    ----------------------------------------------------------

    -- A variable. `ground-var`'s crossing flag is generalised, exactly as in
    -- `groundV`, so that the two grounded witnesses are `ground-∈`.

    cov-var-D :
        ∀ {m} {Q : Hyps (Θ +e)} {Γ : OCtx (Θ +e) m} {A : OVType (Θ +e)}
          {ρ : RExp (Θ +e)}
      → (h₁ : θ₁ ⊨ᴴ Q) → (h₂ : θ₂ ⊨ᴴ Q)
      → (cΓ : CovCtx Γ) → (cA : CovV A)
      → (b : 𝔹) → (x : A ∈̂[ ρ ] Γ) → (eq : crossesᴱ̂ x ≡ b)
      → (ok : VarOK Q A ρ b) → NoCross b
      → var-morphism (proj₁ (proj₂ (ground-var θ₂ h₂ b x eq ok)))
                     (proj₂ (proj₂ (ground-var θ₂ h₂ b x eq ok))) ∘ᵐ covCtx Γ cΓ
      ≈ᵐ covV A cA ∘ᵐ var-morphism (proj₁ (proj₂ (ground-var θ₁ h₁ b x eq ok)))
                                   (proj₂ (proj₂ (ground-var θ₁ h₁ b x eq ok)))
    cov-var-D h₁ h₂ cΓ cA false x eq (inj₁ et) nc =
         cov-var cΓ x eq _ _
      ∙≈ ∘ᵐ-congˡ (covV-irr _ (cov-∈ cΓ x eq) cA)
    cov-var-D h₁ h₂ cΓ cA false x eq (inj₂ le) nc =
         cov-var cΓ x eq _ _
      ∙≈ ∘ᵐ-congˡ (covV-irr _ (cov-∈ cΓ x eq) cA)

    -- Sequencing. The strength's box component is relaxed by `strᵀ-≤`, which
    -- is where the lock's grade `∣ ε ∣̂ᵉ` meets `map-monotoneᵉ`.

    cov-seq :
        ∀ {m} {Q : Hyps (Θ +e)} {Γ : OCtx (Θ +e) m}
          {A B : OVType (Θ +e)} {ε' ε : EExp (Θ +e)}
      → (h₁ : θ₁ ⊨ᴴ Q) → (h₂ : θ₂ ⊨ᴴ Q)
      → (M : Q ∣ Γ ⊢C⦂ A ‼ ε) → (N : Q ∣ Γ ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ A ⊢C⦂ B ‼ ε')
      → (cΓ : CovCtx Γ) → (cB : CovV B) → (nε' : NoNewE ε') → (cA : CovV A)
      → (cM : CovDC M) → (cN : CovDC N)
      → (pm₁ : Paramᶜ (groundC θ₁ h₁ M)) → (pn₁ : Paramᶜ (groundC θ₁ h₁ N))
      → (pm₂ : Paramᶜ (groundC θ₂ h₂ M)) → (pn₂ : Paramᶜ (groundC θ₂ h₂ N))
      → ⟦ groundC θ₂ h₂ M ⨟ groundC θ₂ h₂ N ⟧ᶜᵗ (pm₂ , pn₂) ∘ᵐ covCtx Γ cΓ
      ≈ᵐ covC (B ‼ (ε ·̂ₑ ε')) cB
           ∘ᵐ ⟦ groundC θ₁ h₁ M ⨟ groundC θ₁ h₁ N ⟧ᶜᵗ (pm₁ , pn₁)
    cov-seq {Γ = Γ} {A} {B} {ε'} {ε} h₁ h₂ M N cΓ cB nε' cA cM cN pm₁ pn₁ pm₂ pn₂ =
         ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ str-step)
      ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-nat _ _))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
           (   ≈ᵐ-sym (T-∘ᵐ _ _)
            ∙≈ T-congᶠ (Cov-groundC h₁ h₂ N (cΓ , cA) cB cN pn₁ pn₂))))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
           (   T-congᶠ (∘ᵐ-assoc _ _ _)
            ∙≈ T-∘ᵐ _ _
            ∙≈ ∘ᵐ-congʳ (T-∘ᵐ _ _))))
      ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congˡ (T-≤-μᵀ (ground-mono-e {θ = θ} q ε))
      ∙≈ ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ (μᵀ-nat _))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ
           (μᵀ-inner-≡ (nonew-e ε' nε') (ground-mono-e {θ = θ} q ε')
                       (·ₑ-monoʳ-≾ₑ (ground-mono-e {θ = θ} q ε')))))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙≈ ∘ᵐ-congˡ (∘ᵐ-congˡ (≈ᵐ-sym (T-≤-nat _ _)))
      ∙≈ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congˡ (∘ᵐ-congʳ (T-≤-trans _ _ (ground-mono-e {θ = θ} q (ε ·̂ₑ ε'))))
      where
        str-step :
            strᵀ ∘ᵐ (⟨ η⊣ , ⟦ groundC θ₂ h₂ M ⟧ᶜᵗ pm₂ ⟩ᵐ ∘ᵐ covCtx Γ cΓ)
          ≈ᵐ T-≤ (ground-mono-e {θ = θ} q ε)
               ∘ᵐ (   Tᶠ (covCtx (Γ ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ A) (cΓ , cA))
                   ∘ᵐ (strᵀ ∘ᵐ ⟨ η⊣ , ⟦ groundC θ₁ h₁ M ⟧ᶜᵗ pm₁ ⟩ᵐ))
        str-step =
             ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
          ∙≈ ∘ᵐ-congʳ ⟨ ≈ᵐ-sym (η⊣-nat _)
                      , Cov-groundC h₁ h₂ M cΓ cA cM pm₁ pm₂ ∙≈ ∘ᵐ-assoc _ _ _ ⟩ᵐ-cong
          ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))
          ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙≈ ∘ᵐ-congˡ (strᵀ-nat _ _)
          ∙≈ ∘ᵐ-assoc _ _ _
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (   mapˣᵐ-∘⟨⟩ _ _ _ _
                                         ∙≈ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))
          ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-≤ (ground-mono-e {θ = θ} q ε)))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
               (   mapˣᵐ-∘⟨⟩ _ _ _ _
                ∙≈ ⟨ η⊣-≤ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
                ∙≈ ≈ᵐ-sym (   mapˣᵐ-∘⟨⟩ _ _ _ _
                           ∙≈ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (strᵀ-natˡ _))))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
          ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙≈ ∘ᵐ-congˡ (T-≤-nat _ _)
          ∙≈ ∘ᵐ-assoc _ _ _
          ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
               (   mapˣᵐ-∘ _ _ _ _
                ∙≈ mapˣᵐ-cong (⟨⟩-≤-nat _ _) (∘ᵐ-identityʳ _))))

    -- Unboxing. The unboxed variable's own coercion (a box) is turned inside
    -- out by `[]-≤-nat` and absorbed by the counit's grade law `ε⊣-≤`.

    cov-unbox :
        ∀ {m} {Q : Hyps (Θ +e)} {Γ : OCtx (Θ +e) m}
          {A : OVType (Θ +e)} {C : OCType (Θ +e)} {ρ ρ' : RExp (Θ +e)}
      → (h₁ : θ₁ ⊨ᴴ Q) → (h₂ : θ₂ ⊨ᴴ Q)
      → (cΓ : CovCtx Γ) → (cC : CovC C)
      → (b : 𝔹) → (x : [ ρ ] A ∈̂[ ρ' ] Γ) → (eq : crossesᴱ̂ x ≡ b)
      → (ok : UnboxOK Q ρ' ρ b) → NoCross b
      → (N : Q ∣ Γ ∷ A ⊢C⦂ C) → (cN : CovDC N)
      → (p₁ : Paramᶜ (groundC θ₁ h₁ N)) → (p₂ : Paramᶜ (groundC θ₂ h₂ N))
      → (   ⟦ groundC θ₂ h₂ N ⟧ᶜᵗ p₂
          ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨⟩-≤ (proj₁ (ground-unbox θ₂ h₂ b x eq ok))
                        ∘ᵐ var-proj (proj₂ (ground-unbox θ₂ h₂ b x eq ok)) ⟩ᵐ)
          ∘ᵐ covCtx Γ cΓ
      ≈ᵐ covC C cC
          ∘ᵐ ⟦ groundC θ₁ h₁ N ⟧ᶜᵗ p₁
          ∘ᵐ ⟨ idᵐ , ε⊣ ∘ᵐ ⟨⟩-≤ (proj₁ (ground-unbox θ₁ h₁ b x eq ok))
                        ∘ᵐ var-proj (proj₂ (ground-unbox θ₁ h₁ b x eq ok)) ⟩ᵐ
    cov-unbox {Γ = Γ} {A} h₁ h₂ cΓ cC false x eq le nc N cN p₁ p₂ =
         ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ (   ⟨⟩ᵐ-∘ _ _ _
                   ∙≈ ⟨ ∘ᵐ-identityˡ _ , snd-step ⟩ᵐ-cong
                   ∙≈ ≈ᵐ-sym (   mapˣᵐ-∘⟨⟩ _ _ _ _
                              ∙≈ ⟨ ∘ᵐ-identityʳ _ , ≈ᵐ-refl ⟩ᵐ-cong))
      ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congˡ (Cov-groundC h₁ h₂ N (cΓ , proj₂ (cov-∈ cΓ x eq)) cC cN p₁ p₂)
      ∙≈ ∘ᵐ-assoc _ _ _
      where
        snd-step :
            (ε⊣ ∘ᵐ ⟨⟩-≤ (ground-≾ᵣ h₂ le) ∘ᵐ var-proj (ground-∈ θ₂ x eq))
              ∘ᵐ covCtx Γ cΓ
          ≈ᵐ covV A (proj₂ (cov-∈ cΓ x eq))
              ∘ᵐ (ε⊣ ∘ᵐ ⟨⟩-≤ (ground-≾ᵣ h₁ le) ∘ᵐ var-proj (ground-∈ θ₁ x eq))
        snd-step =
             ∘ᵐ-assoc _ _ _
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (cov-var-proj cΓ x eq))
          ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-trans _ _))
          ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙≈ ∘ᵐ-congˡ (ε⊣-≤ _)
          ∙≈ ∘ᵐ-assoc _ _ _
          ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-congᶠ
               (   ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym ([]-≤-nat _ _))
                ∙≈ ∘ᵐ-assoc _ _ _
                ∙≈ ∘ᵐ-congʳ ([]-≤-trans _ _)
                ∙≈ ∘ᵐ-congʳ ([]-≤-irr _ (ground-≾ᵣ h₁ le)))))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
          ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym (ε⊣-nat _))
          ∙≈ ∘ᵐ-assoc _ _ _
          ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (ε⊣-≤ _)))
          ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)

    -- Boxing. The boxed value's lock grade is `newᵉ`-free, so the two locks
    -- agree up to an order coercion that cancels.

    cov-box :
        ∀ {m} {Q : Hyps (Θ +e)} {Γ : OCtx (Θ +e) m}
          {A : OVType (Θ +e)} {C : OCType (Θ +e)}
      → (h₁ : θ₁ ⊨ᴴ Q) → (h₂ : θ₂ ⊨ᴴ Q)
      → (ρ : RExp (Θ +e)) → (V : Q ∣ Γ ⟨ ρ ⟩ ⊢V⦂ A) → (N : Q ∣ Γ ∷ [ ρ ] A ⊢C⦂ C)
      → (cΓ : CovCtx Γ) → (cC : CovC C) → (nρ : NoNewR ρ) → (cA : CovV A)
      → (cV : CovDV V) → (cN : CovDC N)
      → (pv₁ : Paramᵛ (groundV θ₁ h₁ V)) → (pn₁ : Paramᶜ (groundC θ₁ h₁ N))
      → (pv₂ : Paramᵛ (groundV θ₂ h₂ V)) → (pn₂ : Paramᶜ (groundC θ₂ h₂ N))
      → ⟦ box (groundV θ₂ h₂ V) (groundC θ₂ h₂ N) ⟧ᶜᵗ (pv₂ , pn₂) ∘ᵐ covCtx Γ cΓ
      ≈ᵐ covC C cC ∘ᵐ ⟦ box (groundV θ₁ h₁ V) (groundC θ₁ h₁ N) ⟧ᶜᵗ (pv₁ , pn₁)
    cov-box {Γ = Γ} {A} h₁ h₂ ρ V N cΓ cC nρ cA cV cN pv₁ pn₁ pv₂ pn₂ =
         ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ (   ⟨⟩ᵐ-∘ _ _ _
                   ∙≈ ⟨ ∘ᵐ-identityˡ _ , snd-step ⟩ᵐ-cong
                   ∙≈ ≈ᵐ-sym (   mapˣᵐ-∘⟨⟩ _ _ _ _
                              ∙≈ ⟨ ∘ᵐ-identityʳ _ , ≈ᵐ-refl ⟩ᵐ-cong))
      ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congˡ (Cov-groundC h₁ h₂ N (cΓ , (nρ , cA)) cC cN pn₁ pn₂)
      ∙≈ ∘ᵐ-assoc _ _ _
      where
        snd-step :
            ([ ⟦ ρ ⟧ʳ θ₂ ]ᶠ (⟦ groundV θ₂ h₂ V ⟧ᵛᵗ pv₂) ∘ᵐ η⊣) ∘ᵐ covCtx Γ cΓ
          ≈ᵐ covV ([ ρ ] A) (nρ , cA)
              ∘ᵐ ([ ⟦ ρ ⟧ʳ θ₁ ]ᶠ (⟦ groundV θ₁ h₁ V ⟧ᵛᵗ pv₁) ∘ᵐ η⊣)
        snd-step =
             ∘ᵐ-assoc _ _ _
          ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat _))
          ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
          ∙≈ ≈ᵐ-sym
               (   ∘ᵐ-assoc _ _ _
                ∙≈ ∘ᵐ-congʳ (   ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                             ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym ([]-≤-nat _ _))
                             ∙≈ ∘ᵐ-assoc _ _ _
                             ∙≈ ∘ᵐ-congʳ (η⊣-≤ _)
                             ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                             ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
                ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                ∙≈ ∘ᵐ-congˡ (   ≈ᵐ-sym ([]-∘ᵐ _ _)
                             ∙≈ []-congᶠ
                                  (   ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                                   ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym (Cov-groundV h₁ h₂ V cΓ cA cV pv₁ pv₂))
                                   ∙≈ ∘ᵐ-assoc _ _ _
                                   ∙≈ ∘ᵐ-congʳ (   ∘ᵐ-assoc _ _ _
                                                ∙≈ ∘ᵐ-congʳ (⟨⟩-≤-nat _ _)
                                                ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                                                ∙≈ ∘ᵐ-congˡ (   ⟨⟩-≤-trans _ _
                                                             ∙≈ ⟨⟩-≤-irr _ ≾ᵣ-refl
                                                             ∙≈ ⟨⟩-≤-refl)
                                                ∙≈ ∘ᵐ-identityˡ _))))

    -- Performing an operation. Its parameter and arity are ground types, so
    -- the two readings differ only by the transports `groundC` and `⟦_⟧ᶜᵗ`
    -- insert; the continuation's residual grade is relaxed by `opᵀ-≤`.

    cov-perform :
        ∀ {m} {Q : Hyps (Θ +e)} {Γ : OCtx (Θ +e) m}
          {A : OVType (Θ +e)} {ε : EExp (Θ +e)}
      → (h₁ : θ₁ ⊨ᴴ Q) → (h₂ : θ₂ ⊨ᴴ Q)
      → (op : Op) → (V : Q ∣ Γ ⊢V⦂ ⌜ param op ⌝ᵍ)
      → (M : Q ∣ Γ ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ A ‼ ε)
      → (cΓ : CovCtx Γ) → (cA : CovV A)
      → (cV : CovDV V) → (cM : CovDC M)
      → (pv₁ : Paramᵛ (subst (λ A₀ → ⟦ Γ ⟧ᵒᶜᵗˣ θ₁ ⊢V⦂ A₀)
                            (⌜⌝ᵍ-ground (param op)) (groundV θ₁ h₁ V)))
      → (pm₁ : Paramᶜ (subst (λ A₀ → ⟦ Γ ⟧ᵒᶜᵗˣ θ₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ A₀
                                       ⊢C⦂ ⟦ A ⟧ᵒᵛ θ₁ ‼ ⟦ ε ⟧ᵉ θ₁)
                            (⌜⌝ᵍ-ground (arity op)) (groundC θ₁ h₁ M)))
      → (pv₂ : Paramᵛ (subst (λ A₀ → ⟦ Γ ⟧ᵒᶜᵗˣ θ₂ ⊢V⦂ A₀)
                            (⌜⌝ᵍ-ground (param op)) (groundV θ₂ h₂ V)))
      → (pm₂ : Paramᶜ (subst (λ A₀ → ⟦ Γ ⟧ᵒᶜᵗˣ θ₂ ⟨ mapᵉ (op-grade op) ⟩ ∷ A₀
                                       ⊢C⦂ ⟦ A ⟧ᵒᵛ θ₂ ‼ ⟦ ε ⟧ᵉ θ₂)
                            (⌜⌝ᵍ-ground (arity op)) (groundC θ₂ h₂ M)))
      → ⟦ perform op
            (subst (λ A₀ → ⟦ Γ ⟧ᵒᶜᵗˣ θ₂ ⊢V⦂ A₀)
                   (⌜⌝ᵍ-ground (param op)) (groundV θ₂ h₂ V))
            (subst (λ A₀ → ⟦ Γ ⟧ᵒᶜᵗˣ θ₂ ⟨ mapᵉ (op-grade op) ⟩ ∷ A₀
                             ⊢C⦂ ⟦ A ⟧ᵒᵛ θ₂ ‼ ⟦ ε ⟧ᵉ θ₂)
                   (⌜⌝ᵍ-ground (arity op)) (groundC θ₂ h₂ M)) ⟧ᶜᵗ (pv₂ , pm₂)
          ∘ᵐ covCtx Γ cΓ
      ≈ᵐ covC (A ‼ (econst (op-grade op) ·̂ₑ ε)) cA
          ∘ᵐ ⟦ perform op
                 (subst (λ A₀ → ⟦ Γ ⟧ᵒᶜᵗˣ θ₁ ⊢V⦂ A₀)
                        (⌜⌝ᵍ-ground (param op)) (groundV θ₁ h₁ V))
                 (subst (λ A₀ → ⟦ Γ ⟧ᵒᶜᵗˣ θ₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ A₀
                                  ⊢C⦂ ⟦ A ⟧ᵒᵛ θ₁ ‼ ⟦ ε ⟧ᵉ θ₁)
                        (⌜⌝ᵍ-ground (arity op)) (groundC θ₁ h₁ M)) ⟧ᶜᵗ (pv₁ , pm₁)
    cov-perform {Γ = Γ} {A} {ε} h₁ h₂ op V M cΓ cA cV cM pv₁ pm₁ pv₂ pm₂ =
         ∘ᵐ-assoc _ _ _
      ∙≈ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _ ∙≈ ⟨ fst-step , snd-step ⟩ᵐ-cong)
      ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (   mapˣᵐ-∘⟨⟩ _ _ _ _
                           ∙≈ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
      ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ
           (   mapˣᵐ-cong ≈ᵐ-refl ([]-congᶠ (map⇒ᵐ-∘ʳ _ _) ∙≈ []-∘ᵐ _ _)
            ∙≈ ≈ᵐ-sym (   mapˣᵐ-∘ _ _ _ _
                       ∙≈ mapˣᵐ-cong (∘ᵐ-identityʳ _) ≈ᵐ-refl)))
      ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙≈ ∘ᵐ-congˡ (∘ᵐ-congˡ (opᵀ-nat op _))
      ∙≈ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
      ∙≈ ∘ᵐ-congˡ (∘ᵐ-congʳ (opᵀ-≤ op _))
      ∙≈ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-≤-irr _ _)))
      ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙≈ ∘ᵐ-assoc _ _ _
      where
        e₁ᵖ = ⌜⌝ᵍ-ground {θ = θ₁} (param op)
        e₂ᵖ = ⌜⌝ᵍ-ground {θ = θ₂} (param op)
        e₁ᵃ = ⌜⌝ᵍ-ground {θ = θ₁} (arity op)
        e₂ᵃ = ⌜⌝ᵍ-ground {θ = θ₂} (arity op)

        fst-step :
            subst (λ O → ⟦ ⟦ Γ ⟧ᵒᶜᵗˣ θ₂ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op))
                  (⟦ subst (λ A₀ → ⟦ Γ ⟧ᵒᶜᵗˣ θ₂ ⊢V⦂ A₀) e₂ᵖ (groundV θ₂ h₂ V) ⟧ᵛᵗ pv₂)
              ∘ᵐ covCtx Γ cΓ
          ≈ᵐ subst (λ O → ⟦ ⟦ Γ ⟧ᵒᶜᵗˣ θ₁ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op))
                 (⟦ subst (λ A₀ → ⟦ Γ ⟧ᵒᶜᵗˣ θ₁ ⊢V⦂ A₀) e₁ᵖ (groundV θ₁ h₁ V) ⟧ᵛᵗ pv₁)
        fst-step =
             ∘ᵐ-congˡ (subst-cod _ _ ∙≈ ∘ᵐ-congʳ (ty-den e₂ᵖ _ pv₂))
          ∙≈ ∘ᵐ-assoc _ _ _
          ∙≈ ∘ᵐ-congʳ (   ∘ᵐ-assoc _ _ _
                       ∙≈ ∘ᵐ-congʳ (Cov-groundV h₁ h₂ V cΓ (nn⇒CovV _ (nn-⌜⌝ᵍ (param op)))
                                                cV (ty-Paramᵛ⁻ e₁ᵖ _ pv₁)
                                                   (ty-Paramᵛ⁻ e₂ᵖ _ pv₂))
                       ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                       ∙≈ ∘ᵐ-congˡ
                            (   ∘ᵐ-congʳ (covV-nn _ _ (nn-⌜⌝ᵍ (param op)))
                             ∙≈ inv⁺-trans (nonew-v ⌜ param op ⌝ᵍ (nn-⌜⌝ᵍ (param op))) e₂ᵖ
                             ∙≈ inv⁺-irr
                                  (trans (nonew-v ⌜ param op ⌝ᵍ (nn-⌜⌝ᵍ (param op))) e₂ᵖ)
                                  e₁ᵖ))
          ∙≈ ≈ᵐ-sym (subst-cod _ _ ∙≈ ∘ᵐ-congʳ (ty-den e₁ᵖ _ pv₁))

        snd-step :
            ([ mapᵉ (op-grade op) ]ᶠ
               (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ ⟦ Γ ⟧ᵒᶜᵗˣ θ₂ ⟧ᶜᵗˣ ×ᵐ O)
                                →ᵐ Tᵒ ⟦ ⟦ A ⟧ᵒᵛ θ₂ ⟧ᵛ (⟦ ε ⟧ᵉ θ₂))
                              (ty-gty (arity op))
                              (⟦ subst (λ A₀ → ⟦ Γ ⟧ᵒᶜᵗˣ θ₂ ⟨ mapᵉ (op-grade op) ⟩ ∷ A₀
                                                 ⊢C⦂ ⟦ A ⟧ᵒᵛ θ₂ ‼ ⟦ ε ⟧ᵉ θ₂)
                                       e₂ᵃ (groundC θ₂ h₂ M) ⟧ᶜᵗ pm₂)))
              ∘ᵐ η⊣) ∘ᵐ covCtx Γ cΓ
          ≈ᵐ [ mapᵉ (op-grade op) ]ᶠ
               (map⇒ᵐ idᵐ (Tᶠ (covV A cA) ∘ᵐ T-≤ (ground-mono-e {θ = θ} q ε)))
              ∘ᵐ ([ mapᵉ (op-grade op) ]ᶠ
                    (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ ⟦ Γ ⟧ᵒᶜᵗˣ θ₁ ⟧ᶜᵗˣ ×ᵐ O)
                                     →ᵐ Tᵒ ⟦ ⟦ A ⟧ᵒᵛ θ₁ ⟧ᵛ (⟦ ε ⟧ᵉ θ₁))
                                   (ty-gty (arity op))
                                   (⟦ subst (λ A₀ → ⟦ Γ ⟧ᵒᶜᵗˣ θ₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ A₀
                                                      ⊢C⦂ ⟦ A ⟧ᵒᵛ θ₁ ‼ ⟦ ε ⟧ᵉ θ₁)
                                            e₁ᵃ (groundC θ₁ h₁ M) ⟧ᶜᵗ pm₁)))
                   ∘ᵐ η⊣)
        snd-step =
             ∘ᵐ-assoc _ _ _
          ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat _))
          ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _) ∙≈ []-congᶠ body)
          ∙≈ ∘ᵐ-congˡ ([]-∘ᵐ _ _)
          ∙≈ ∘ᵐ-assoc _ _ _
          where
            arity-step :
                covV ⌜ arity op ⌝ᵍ (nn⇒CovV _ (nn-⌜⌝ᵍ (arity op)))
                  ∘ᵐ (inv⁻ e₁ᵃ ∘ᵐ coeᵒ⁻ (ty-gty (arity op)))
              ≈ᵐ inv⁻ e₂ᵃ ∘ᵐ coeᵒ⁻ (ty-gty (arity op))
            arity-step =
                 ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙≈ ∘ᵐ-congˡ
                   (   ∘ᵐ-congˡ (covV-nn _ _ (nn-⌜⌝ᵍ (arity op)))
                    ∙≈ inv⁺-sym-trans e₁ᵃ (nonew-v ⌜ arity op ⌝ᵍ (nn-⌜⌝ᵍ (arity op)))
                    ∙≈ inv⁻-irr
                         (trans (sym (nonew-v ⌜ arity op ⌝ᵍ (nn-⌜⌝ᵍ (arity op)))) e₁ᵃ)
                         e₂ᵃ)

            body :
                curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ ⟦ Γ ⟧ᵒᶜᵗˣ θ₂ ⟧ᶜᵗˣ ×ᵐ O)
                                →ᵐ Tᵒ ⟦ ⟦ A ⟧ᵒᵛ θ₂ ⟧ᵛ (⟦ ε ⟧ᵉ θ₂))
                              (ty-gty (arity op))
                              (⟦ subst (λ A₀ → ⟦ Γ ⟧ᵒᶜᵗˣ θ₂ ⟨ mapᵉ (op-grade op) ⟩ ∷ A₀
                                                 ⊢C⦂ ⟦ A ⟧ᵒᵛ θ₂ ‼ ⟦ ε ⟧ᵉ θ₂)
                                       e₂ᵃ (groundC θ₂ h₂ M) ⟧ᶜᵗ pm₂))
                  ∘ᵐ ⟨ mapᵉ (op-grade op) ⟩ᶠ (covCtx Γ cΓ)
              ≈ᵐ map⇒ᵐ idᵐ (Tᶠ (covV A cA) ∘ᵐ T-≤ (ground-mono-e {θ = θ} q ε))
                  ∘ᵐ curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ ⟦ Γ ⟧ᵒᶜᵗˣ θ₁ ⟧ᶜᵗˣ ×ᵐ O)
                                     →ᵐ Tᵒ ⟦ ⟦ A ⟧ᵒᵛ θ₁ ⟧ᵛ (⟦ ε ⟧ᵉ θ₁))
                                   (ty-gty (arity op))
                                   (⟦ subst (λ A₀ → ⟦ Γ ⟧ᵒᶜᵗˣ θ₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ A₀
                                                      ⊢C⦂ ⟦ A ⟧ᵒᵛ θ₁ ‼ ⟦ ε ⟧ᵉ θ₁)
                                            e₁ᵃ (groundC θ₁ h₁ M) ⟧ᶜᵗ pm₁))
            body =
                 ≈ᵐ-sym (curryᵐ-nat _ _)
              ∙≈ curryᵐ-cong
                   (   ∘ᵐ-congˡ (   subst-dom _ _
                                 ∙≈ ∘ᵐ-congˡ (∷-den e₂ᵃ _ pm₂)
                                 ∙≈ ∘ᵐ-assoc _ _ _
                                 ∙≈ ∘ᵐ-congʳ (   mapˣᵐ-∘ _ _ _ _
                                              ∙≈ mapˣᵐ-cong (∘ᵐ-identityˡ _) ≈ᵐ-refl))
                    ∙≈ ∘ᵐ-assoc _ _ _
                    ∙≈ ∘ᵐ-congʳ (   mapˣᵐ-∘ _ _ _ _
                                 ∙≈ mapˣᵐ-cong (∘ᵐ-identityˡ _) (∘ᵐ-identityʳ _))
                    ∙≈ ∘ᵐ-congʳ (mapˣᵐ-cong
                          (≈ᵐ-sym (   ∘ᵐ-congˡ (⟨⟩-≤-irr _ ≾ᵣ-refl ∙≈ ⟨⟩-≤-refl)
                                   ∙≈ ∘ᵐ-identityˡ _))
                          (≈ᵐ-sym arity-step))
                    ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (   mapˣᵐ-∘ _ _ _ _
                                         ∙≈ mapˣᵐ-cong (∘ᵐ-identityʳ _) ≈ᵐ-refl))
                    ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                    ∙≈ ∘ᵐ-congˡ (Cov-groundC h₁ h₂ M
                                   (cΓ , nn⇒CovV _ (nn-⌜⌝ᵍ (arity op))) cA cM
                                   (∷-Paramᶜ⁻ e₁ᵃ _ pm₁) (∷-Paramᶜ⁻ e₂ᵃ _ pm₂))
                    ∙≈ ∘ᵐ-assoc _ _ _
                    ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (   subst-dom _ _
                                         ∙≈ ∘ᵐ-congˡ (∷-den e₁ᵃ _ pm₁)
                                         ∙≈ ∘ᵐ-assoc _ _ _
                                         ∙≈ ∘ᵐ-congʳ (   mapˣᵐ-∘ _ _ _ _
                                                      ∙≈ mapˣᵐ-cong (∘ᵐ-identityˡ _)
                                                                    ≈ᵐ-refl))))
              ∙≈ ≈ᵐ-sym (map⇒ᵐ-curryᵐ _ _)


--------------------------------------------------------------
-- Discharging `EffUniformʰ` for a covariant clause family    --
--------------------------------------------------------------

-- The clause context and result type that `ground-clause` transports along.

clause-ctx : (r : R) → Ctx → VType → VType → VType → E → Ctx
clause-ctx r Δ P A Bv ϵ = Δ ⟨ ⊤ᵣ ⟩ ∷ P ∷ [ r ] (A ⇒ Bv ‼ ϵ)

ctxE : (r : R) → {Δ' Δ : Ctx} → Δ' ≡ Δ → {P' P : VType} → P' ≡ P
     → {A' A : VType} → A' ≡ A → {B' B : VType} → B' ≡ B → (ϵ : E)
     → clause-ctx r Δ' P' A' B' ϵ ≡ clause-ctx r Δ P A B ϵ
ctxE r eΔ eP eA eB ϵ =
  cong₂ _∷_ (cong₂ _∷_ (cong (_⟨ ⊤ᵣ ⟩) eΔ) eP)
            (cong₂ (λ A₀ B₀ → [ r ] (A₀ ⇒ B₀ ‼ ϵ)) eA eB)

-- The context square: the continuation coercion that `EffUniformʰ` names,
-- transported to the mirrored side, *is* the covariance coercion of the
-- clause's context (everything but the residual grade being `newᵉ`-free).

ctx-square :
  ∀ {Δ₁ Δ₂ Δ : Ctx} {P₁ P₂ P : VType} {A₁ A₂ A : VType} {Bv₁ Bv₂ Bv : VType}
    {ϵ₁ ϵ₂ : E} {r : R}
  → (eΔ₁ : Δ₁ ≡ Δ) → (eΔ₂ : Δ₂ ≡ Δ) → (dΔ : Δ₁ ≡ Δ₂)
  → (eP₁ : P₁ ≡ P) → (eP₂ : P₂ ≡ P) → (dP : P₁ ≡ P₂)
  → (eA₁ : A₁ ≡ A) → (eA₂ : A₂ ≡ A) → (dA : A₁ ≡ A₂)
  → (eB₁ : Bv₁ ≡ Bv) → (eB₂ : Bv₂ ≡ Bv) → (dB : Bv₁ ≡ Bv₂)
  → (w : ϵ₁ ≾ₑ ϵ₂) → (u : r ≾ᵣ r)
  →    invˣ⁻ (ctxE r eΔ₂ eP₂ eA₂ eB₂ ϵ₂)
         ∘ᵐ mapˣᵐ idᵐ ([ r ]ᶠ (map⇒ᵐ idᵐ (T-≤ w)))
  ≈ᵐ    mapˣᵐ (mapˣᵐ (invˣ⁺ (cong (_⟨ ⊤ᵣ ⟩) dΔ)) (inv⁺ dP))
              ([ r ]ᶠ (map⇒ᵐ (inv⁻ dA) (Tᶠ (inv⁺ dB) ∘ᵐ T-≤ w)) ∘ᵐ []-≤ u)
         ∘ᵐ invˣ⁻ (ctxE r eΔ₁ eP₁ eA₁ eB₁ ϵ₁)
ctx-square refl refl refl refl refl refl refl refl refl refl refl refl w u =
     ∘ᵐ-identityˡ _
  ∙≈ ≈ᵐ-sym
       (   ∘ᵐ-identityʳ _
        ∙≈ mapˣᵐ-cong mapˣᵐ-idᵐ
             (   ∘ᵐ-congʳ ([]-≤-irr u ≾ᵣ-refl ∙≈ []-≤-refl)
              ∙≈ ∘ᵐ-identityʳ _
              ∙≈ []-congᶠ (map⇒ᵐ-cong ≈ᵐ-refl (∘ᵐ-congˡ T-idᵐ ∙≈ ∘ᵐ-identityˡ _))))

-- The result-type square.

ty-square :
  ∀ {Bv₁ Bv₂ Bv : VType} {ϵ₁ ϵ₂ ge : E}
  → (eB₁ : Bv₁ ≡ Bv) → (eB₂ : Bv₂ ≡ Bv) → (dB : Bv₁ ≡ Bv₂)
  → (w : ϵ₁ ≾ₑ ϵ₂) → (w' : ge ·ₑ ϵ₁ ≾ₑ ge ·ₑ ϵ₂)
  →    invᶜ⁺ (cong (_‼ (ge ·ₑ ϵ₂)) eB₂) ∘ᵐ (Tᶠ (inv⁺ dB) ∘ᵐ T-≤ w')
  ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ w) ∘ᵐ invᶜ⁺ (cong (_‼ (ge ·ₑ ϵ₁)) eB₁)
ty-square refl refl refl w w' =
     ∘ᵐ-identityˡ _
  ∙≈ ∘ᵐ-congˡ T-idᵐ
  ∙≈ ∘ᵐ-identityˡ _
  ∙≈ T-≤-irr w' (·ₑ-monoʳ-≾ₑ w)
  ∙≈ ≈ᵐ-sym (∘ᵐ-identityʳ _)

module _ {Θ : Scope} {m} {Q : Hyps Θ} {Γ : OCtx Θ m} {B : OVType Θ}
         (θ : Grounding Θ) (h : θ ⊨ᴴ Q) where

  -- A mirrored clause family, certified covariant clause by clause, is
  -- semantically uniform in the residual effect grade. This discharges
  -- `Inference.ParamGround.GroundUniform.ground-uniform` for the fragment
  -- `CovDC` describes.

  ground-uniform-cov :
      (Ĥ : (op : Op)
         → wkᵉ-H Q ∣ (wkᵉ-ctx Γ) ᴱ̂ ∷ ⌜ param op ⌝ᵍ
                       ∷ [ rconst (mapᵉ (op-grade op)) ]
                           (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ}))
           ⊢C⦂ wkᵉ-v B ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ})))
    → (cH : ∀ op → CovDC (Ĥ op))
    → (pH : ∀ op ε'' → Paramᶜ (ground-clause θ h op ε'' (Ĥ op)))
    → EffUniformʰ {⟦ Γ ⟧ᵒᶜᵗˣ θ} {⟦ B ⟧ᵒᵛ θ}
                  (λ op ε'' → ground-clause θ h op ε'' (Ĥ op)) pH
  ground-uniform-cov Ĥ cH pH op {ε₁''} {ε₂''} qq =
       ∘ᵐ-congˡ (subst₂-den (E₁ ε₂'') (E₂ ε₂'') (D ε₂'') (pH op ε₂''))
    ∙≈ ∘ᵐ-assoc _ _ _
    ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
    ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ ctx-step)
    ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ
         (Fund.Cov-groundC θ qq (⊨ᴴ-wkᵉ-ground h) (⊨ᴴ-wkᵉ-ground h) (Ĥ op)
                           cΓ̂ cĈ (cH op)
                           (subst₂-Paramᶜ⁻ (E₁ ε₁'') (E₂ ε₁'') (D ε₁'') (pH op ε₁''))
                           (subst₂-Paramᶜ⁻ (E₁ ε₂'') (E₂ ε₂'') (D ε₂'') (pH op ε₂''))))
    ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
    ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙≈ ∘ᵐ-congˡ ty-step
    ∙≈ ∘ᵐ-assoc _ _ _
    ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (subst₂-den (E₁ ε₁'') (E₂ ε₁'') (D ε₁'') (pH op ε₁'')))
    where
      open Cov θ qq

      Γ̂ : OCtx (Θ +e) _
      Γ̂ = (wkᵉ-ctx Γ) ᴱ̂ ∷ ⌜ param op ⌝ᵍ
            ∷ [ rconst (mapᵉ (op-grade op)) ]
                (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ}))

      Ĉ : OCType (Θ +e)
      Ĉ = wkᵉ-v B ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ}))

      D : (ε'' : E) → ⟦ Γ̂ ⟧ᵒᶜᵗˣ (θ ,ᵍᵉ ε'') ⊢C⦂ ⟦ Ĉ ⟧ᵒᶜ (θ ,ᵍᵉ ε'')
      D ε'' = groundC (θ ,ᵍᵉ ε'') (⊨ᴴ-wkᵉ-ground h) (Ĥ op)

      E₁ : (ε'' : E)
         → ⟦ Γ̂ ⟧ᵒᶜᵗˣ (θ ,ᵍᵉ ε'')
         ≡ (⟦ Γ ⟧ᵒᶜᵗˣ θ) ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
             ∷ [ mapᵉ (op-grade op) ]
                 (type-of-gtype (arity op) ⇒ ⟦ B ⟧ᵒᵛ θ ‼ ε'')
      E₁ ε'' = ctxE (mapᵉ (op-grade op))
                    (ground-wkᵉ-ctx {θ = θ} {ε₀ = ε''} Γ)
                    (⌜⌝ᵍ-ground {θ = θ ,ᵍᵉ ε''} (param op))
                    (⌜⌝ᵍ-ground {θ = θ ,ᵍᵉ ε''} (arity op))
                    (ground-wkᵉ-v {θ = θ} {ε₀ = ε''} B)
                    ε''

      E₂ : (ε'' : E) → ⟦ Ĉ ⟧ᵒᶜ (θ ,ᵍᵉ ε'') ≡ ⟦ B ⟧ᵒᵛ θ ‼ (op-grade op ·ₑ ε'')
      E₂ ε'' = cong (_‼ (op-grade op ·ₑ ε''))
                    (ground-wkᵉ-v {θ = θ} {ε₀ = ε''} B)

      cΓ̂ : CovCtx Γ̂
      cΓ̂ = (nn-wkᵉ-ctx Γ , nn⇒CovV ⌜ param op ⌝ᵍ (nn-⌜⌝ᵍ (param op)))
         , (tt , (nn-⌜⌝ᵍ (arity op) , nn⇒CovV (wkᵉ-v B) (nn-wkᵉ-v B)))

      cĈ : CovC Ĉ
      cĈ = nn⇒CovV (wkᵉ-v B) (nn-wkᵉ-v B)

      ctx-step :
          invˣ⁻ (E₁ ε₂'')
            ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ qq)))
        ≈ᵐ covCtx Γ̂ cΓ̂ ∘ᵐ invˣ⁻ (E₁ ε₁'')
      ctx-step =
           ctx-square (ground-wkᵉ-ctx {θ = θ} {ε₀ = ε₁''} Γ)
                      (ground-wkᵉ-ctx {θ = θ} {ε₀ = ε₂''} Γ)
                      (nonew-ctx (wkᵉ-ctx Γ) (nn-wkᵉ-ctx Γ))
                      (⌜⌝ᵍ-ground {θ = θ ,ᵍᵉ ε₁''} (param op))
                      (⌜⌝ᵍ-ground {θ = θ ,ᵍᵉ ε₂''} (param op))
                      (nonew-v ⌜ param op ⌝ᵍ (nn-⌜⌝ᵍ (param op)))
                      (⌜⌝ᵍ-ground {θ = θ ,ᵍᵉ ε₁''} (arity op))
                      (⌜⌝ᵍ-ground {θ = θ ,ᵍᵉ ε₂''} (arity op))
                      (nonew-v ⌜ arity op ⌝ᵍ (nn-⌜⌝ᵍ (arity op)))
                      (ground-wkᵉ-v {θ = θ} {ε₀ = ε₁''} B)
                      (ground-wkᵉ-v {θ = θ} {ε₀ = ε₂''} B)
                      (nonew-v (wkᵉ-v B) (nn-wkᵉ-v B))
                      qq (≾ᵣ-reflexive (sym (nonew-r (rconst (mapᵉ (op-grade op))) tt)))
        ∙≈ ∘ᵐ-congˡ (mapˣᵐ-cong
             (mapˣᵐ-cong ≈ᵐ-refl
                         (≈ᵐ-sym (covV-nn ⌜ param op ⌝ᵍ
                                          (nn⇒CovV ⌜ param op ⌝ᵍ (nn-⌜⌝ᵍ (param op)))
                                          (nn-⌜⌝ᵍ (param op)))))
             (∘ᵐ-congˡ ([]-congᶠ (map⇒ᵐ-cong ≈ᵐ-refl
                (∘ᵐ-congˡ (T-congᶠ (≈ᵐ-sym (covV-nn (wkᵉ-v B)
                                             (nn⇒CovV (wkᵉ-v B) (nn-wkᵉ-v B))
                                             (nn-wkᵉ-v B)))))))))

      ty-step :
          invᶜ⁺ (E₂ ε₂'') ∘ᵐ covC Ĉ cĈ
        ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ qq) ∘ᵐ invᶜ⁺ (E₂ ε₁'')
      ty-step =
           ∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (covV-nn (wkᵉ-v B)
                                                (nn⇒CovV (wkᵉ-v B) (nn-wkᵉ-v B))
                                                (nn-wkᵉ-v B))))
        ∙≈ ty-square (ground-wkᵉ-v {θ = θ} {ε₀ = ε₁''} B)
                     (ground-wkᵉ-v {θ = θ} {ε₀ = ε₂''} B)
                     (nonew-v (wkᵉ-v B) (nn-wkᵉ-v B))
                     qq (ground-mono-e {θ = θ} qq
                           (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ})))

--------------------------------------------------------------
-- Sanity check: the certificates are inhabited              --
--------------------------------------------------------------

-- The canonical *forwarding* clause — re-perform the operation and pass the
-- result to the boxed continuation — is covariant. It uses `perform`,
-- `unbox`, `_·_` and `var`, each at a shape `CovDC` admits, so the
-- covariance hypothesis of `ground-uniform-cov` is not vacuous.

private

  forward : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {B : OVType Θ} → (op : Op)
          → wkᵉ-H Q ∣ (wkᵉ-ctx Γ) ᴱ̂ ∷ ⌜ param op ⌝ᵍ
                        ∷ [ rconst (mapᵉ (op-grade op)) ]
                            (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ}))
              ⊢C⦂ wkᵉ-v B ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ}))
  forward op =
    perform op
      (var (Tl-∷ Hd) (inj₂ ⊩≾̂ᵣ-refl))
      (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (eqᵣ ≡̂ᵣ-identityˡ)
        (var Hd (inj₂ ⊩≾̂ᵣ-refl) · var (Tl-∷ Hd) (inj₂ ⊩≾̂ᵣ-refl)))

  forward-cov : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {B : OVType Θ} → (op : Op)
              → CovDC (forward {Θ} {n} {Q} {Γ} {B} op)
  forward-cov op = tt , (tt , (nn-⌜⌝ᵍ (arity op) , tt , tt))
