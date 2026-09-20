------------------------------------------------------------------
-- Covariance certificates for grounding in the rigid grade       --
--                                                                --
-- Fix a grounding `θ : Grounding Θ` and two instantiations       --
-- `ε₁ ≾ₑ ε₂` of the rigid effect-grade variable `newᵉ`. A type   --
-- of the extended scope `Θ +e` then has two closed readings,     --
-- `⟦ A ⟧ᵒᵛ (θ ,ᵍᵉ ε₁)` and `⟦ A ⟧ᵒᵛ (θ ,ᵍᵉ ε₂)`, and this       --
-- module builds the coercion between their interpretations       --
-- whenever `newᵉ` occurs *covariantly* in `A`.                   --
--                                                                --
-- Variance in the model: `T-≤` is covariant in the effect grade  --
-- and `⟨⟩-≤` covariant in the resource grade, while `[]-≤` is    --
-- contravariant and `_⇒_`'s domain contravariant. As no grade    --
-- expression is antitone in `newᵉ`, a contravariant position     --
-- must be `newᵉ`-*free*; `NoNew*` is that syntactic condition    --
-- and `nonew-*` turns it into the equality of the two readings.  --
------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module TypeInference.ParamGround.Covariance
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
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_; Dec; yes; no)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types    S
open import Syntax.Contexts S

open import TypeInference.Open.Grades   S
open import TypeInference.Open.Types    S
open import TypeInference.Open.Contexts S
open import TypeInference.Open.Hyps     S

open import TypeInference.Open.Grounding S
  renaming (⟦_⟧ᵛ to ⟦_⟧ᵒᵛ; ⟦_⟧ᶜ to ⟦_⟧ᵒᶜ; ⟦_⟧ᶜᵗˣ to ⟦_⟧ᵒᶜᵗˣ)

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-≤; []-idᵐ; []-∘ᵐ; []-congᶠ;
                       []-≤-refl; []-≤-trans; []-≤-nat)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-≤; ⟨⟩-idᵐ; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ;
                     ⟨⟩-≤-refl; ⟨⟩-≤-trans; ⟨⟩-≤-nat; ⟨⟩-≤-irr;
                     η; μ; εᵘ; ⟨⟩-η-nat; ⟨⟩-μ-nat; ⟨⟩-μ-≤; ext-nat)
open GroundTypes GTy
open Monad Mon using (Tᵒ; Tᶠ; T-≤; T-idᵐ; T-∘ᵐ; T-congᶠ;
                      T-≤-refl; T-≤-trans; T-≤-nat)

open import DenotationalSemantics.Interpretation.Types     S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts  S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE

open import TypeInference.ParamGround S Cat Fut Pst Adj GTy Mon GE
  using (ground-mono-e; ground-mono-r)

-- The syntactic condition "the newly bound effect-grade variable does not
-- occur". Only a `newᵉ`-free expression reads the same under the two
-- instantiations, and a contravariant position needs exactly that.

NoNewE : ∀ {Θ} → EExp (Θ +e) → Set
NoNewE (evar zero)    = ⊥
NoNewE (evar (suc i)) = ⊤
NoNewE (econst ε)     = ⊤
NoNewE (ε ·̂ₑ ε')      = NoNewE ε × NoNewE ε'

NoNewR : ∀ {Θ} → RExp (Θ +e) → Set
NoNewR (rvar i)   = ⊤
NoNewR (rconst ρ) = ⊤
NoNewR (ρ ·̂ᵣ ρ')  = NoNewR ρ × NoNewR ρ'
NoNewR ∣ ε ∣̂ᵉ     = NoNewE ε

mutual

  NoNewV : ∀ {Θ} → OVType (Θ +e) → Set
  NoNewV (tvar α)  = ⊤
  NoNewV (Base b)  = ⊤
  NoNewV Unit      = ⊤
  NoNewV Bool      = ⊤
  NoNewV (A |×| B) = NoNewV A × NoNewV B
  NoNewV Empty     = ⊤
  NoNewV (A ⇒ C)   = NoNewV A × NoNewC C
  NoNewV ([ ρ ] A) = NoNewR ρ × NoNewV A

  NoNewC : ∀ {Θ} → OCType (Θ +e) → Set
  NoNewC (A ‼ ε) = NoNewV A × NoNewE ε

NoNewCtx : ∀ {Θ n} → OCtx (Θ +e) n → Set
NoNewCtx []        = ⊤
NoNewCtx (Γ ∷ A)   = NoNewCtx Γ × NoNewV A
NoNewCtx (Γ ⟨ ρ ⟩) = NoNewCtx Γ × NoNewR ρ

nn-wkᵉ-e : ∀ {Θ} → (ε : EExp Θ) → NoNewE (wkᵉ-e ε)
nn-wkᵉ-e (evar i)   = tt
nn-wkᵉ-e (econst ε) = tt
nn-wkᵉ-e (ε ·̂ₑ ε')  = nn-wkᵉ-e ε , nn-wkᵉ-e ε'

nn-wkᵉ-r : ∀ {Θ} → (ρ : RExp Θ) → NoNewR (wkᵉ-r ρ)
nn-wkᵉ-r (rvar i)   = tt
nn-wkᵉ-r (rconst ρ) = tt
nn-wkᵉ-r (ρ ·̂ᵣ ρ')  = nn-wkᵉ-r ρ , nn-wkᵉ-r ρ'
nn-wkᵉ-r ∣ ε ∣̂ᵉ     = nn-wkᵉ-e ε

mutual

  nn-wkᵉ-v : ∀ {Θ} → (A : OVType Θ) → NoNewV (wkᵉ-v A)
  nn-wkᵉ-v (tvar α)  = tt
  nn-wkᵉ-v (Base b)  = tt
  nn-wkᵉ-v Unit      = tt
  nn-wkᵉ-v Bool      = tt
  nn-wkᵉ-v (A |×| B) = nn-wkᵉ-v A , nn-wkᵉ-v B
  nn-wkᵉ-v Empty     = tt
  nn-wkᵉ-v (A ⇒ C)   = nn-wkᵉ-v A , nn-wkᵉ-c C
  nn-wkᵉ-v ([ ρ ] A) = nn-wkᵉ-r ρ , nn-wkᵉ-v A

  nn-wkᵉ-c : ∀ {Θ} → (C : OCType Θ) → NoNewC (wkᵉ-c C)
  nn-wkᵉ-c (A ‼ ε) = nn-wkᵉ-v A , nn-wkᵉ-e ε

nn-wkᵉ-ctx : ∀ {Θ n} → (Γ : OCtx Θ n) → NoNewCtx (wkᵉ-ctx Γ)
nn-wkᵉ-ctx []        = tt
nn-wkᵉ-ctx (Γ ∷ A)   = nn-wkᵉ-ctx Γ , nn-wkᵉ-v A
nn-wkᵉ-ctx (Γ ⟨ ρ ⟩) = nn-wkᵉ-ctx Γ , nn-wkᵉ-r ρ

-- A ground type embeds `newᵉ`-free

nn-⌜⌝ᵍ : ∀ {Θ} → (G : GType) → NoNewV (⌜_⌝ᵍ {Θ +e} G)
nn-⌜⌝ᵍ (Base b)   = tt
nn-⌜⌝ᵍ Unit       = tt
nn-⌜⌝ᵍ Bool       = tt
nn-⌜⌝ᵍ Empty      = tt
nn-⌜⌝ᵍ (G |×|ᵍ H) = nn-⌜⌝ᵍ G , nn-⌜⌝ᵍ H
nn-⌜⌝ᵍ ([ ρ ]ᵍ G) = tt , nn-⌜⌝ᵍ G

inv⁺ : ∀ {A B : VType} → A ≡ B → ⟦ A ⟧ᵛ →ᵐ ⟦ B ⟧ᵛ
inv⁺ refl = idᵐ

inv⁻ : ∀ {A B : VType} → A ≡ B → ⟦ B ⟧ᵛ →ᵐ ⟦ A ⟧ᵛ
inv⁻ refl = idᵐ

invᶜ⁺ : ∀ {C D : CType} → C ≡ D → ⟦ C ⟧ᶜ →ᵐ ⟦ D ⟧ᶜ
invᶜ⁺ refl = idᵐ

invˣ⁺ : ∀ {Γ Δ : Ctx} → Γ ≡ Δ → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Δ ⟧ᶜᵗˣ
invˣ⁺ refl = idᵐ

-- Proof irrelevance (UIP) of the transports

inv⁺-irr : ∀ {A B : VType} → (e e' : A ≡ B) → inv⁺ e ≈ᵐ inv⁺ e'
inv⁺-irr e e' rewrite uip {p = e} {q = e'} = ≈ᵐ-refl

inv⁻-irr : ∀ {A B : VType} → (e e' : A ≡ B) → inv⁻ e ≈ᵐ inv⁻ e'
inv⁻-irr e e' rewrite uip {p = e} {q = e'} = ≈ᵐ-refl

invᶜ⁺-irr : ∀ {C D : CType} → (e e' : C ≡ D) → invᶜ⁺ e ≈ᵐ invᶜ⁺ e'
invᶜ⁺-irr e e' rewrite uip {p = e} {q = e'} = ≈ᵐ-refl

invˣ⁺-irr : ∀ {Γ Δ : Ctx} → (e e' : Γ ≡ Δ) → invˣ⁺ e ≈ᵐ invˣ⁺ e'
invˣ⁺-irr e e' rewrite uip {p = e} {q = e'} = ≈ᵐ-refl

-- Functoriality and invertibility

inv⁺-trans : ∀ {A B C : VType} → (e : A ≡ B) → (e' : B ≡ C)
           → inv⁺ e' ∘ᵐ inv⁺ e ≈ᵐ inv⁺ (trans e e')
inv⁺-trans refl refl = ∘ᵐ-identityˡ _

inv⁺∘inv⁻ : ∀ {A B : VType} → (e : A ≡ B) → inv⁺ e ∘ᵐ inv⁻ e ≈ᵐ idᵐ
inv⁺∘inv⁻ refl = ∘ᵐ-identityˡ _

inv⁻∘inv⁺ : ∀ {A B : VType} → (e : A ≡ B) → inv⁻ e ∘ᵐ inv⁺ e ≈ᵐ idᵐ
inv⁻∘inv⁺ refl = ∘ᵐ-identityˡ _

invˣ⁺-trans : ∀ {Γ Δ Ξ : Ctx} → (e : Γ ≡ Δ) → (e' : Δ ≡ Ξ)
            → invˣ⁺ e' ∘ᵐ invˣ⁺ e ≈ᵐ invˣ⁺ (trans e e')
invˣ⁺-trans refl refl = ∘ᵐ-identityˡ _

-- Grade relaxation is irrelevant in its witness, for the box as for `⟨_⟩`.

[]-≤-irr : ∀ {A ρ₁ ρ₂} → (w w' : ρ₁ ≾ᵣ ρ₂) → []-≤ {A} w ≈ᵐ []-≤ {A} w'
[]-≤-irr {A} w w' rewrite ≾ᵣ-irrelevant w w' = ≈ᵐ-refl

T-≤-irr : ∀ {A ε₁ ε₂} → (w w' : ε₁ ≾ₑ ε₂) → T-≤ {A} w ≈ᵐ T-≤ {A} w'
T-≤-irr {A} w w' rewrite ≾ₑ-irrelevant w w' = ≈ᵐ-refl

-- `map⇒ᵐ` is a congruence

map⇒ᵐ-cong : ∀ {A B C D} {f f' : A →ᵐ B} {g g' : C →ᵐ D}
           → f ≈ᵐ f' → g ≈ᵐ g' → map⇒ᵐ f g ≈ᵐ map⇒ᵐ f' g'
map⇒ᵐ-cong r r' =
  curryᵐ-cong (≈ᵐ-trans (∘ᵐ-congˡ r')
                        (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-cong ≈ᵐ-refl r))))

-- The transports commute with each type/context former: this is what lets a
-- structurally built coercion collapse to a transport at a `newᵉ`-free type.

inv⁺-× : ∀ {A₁ A₂ B₁ B₂ : VType} → (e : A₁ ≡ A₂) → (e' : B₁ ≡ B₂)
       → mapˣᵐ (inv⁺ e) (inv⁺ e') ≈ᵐ inv⁺ (cong₂ _|×|_ e e')
inv⁺-× refl refl = mapˣᵐ-idᵐ

inv⁺-⇒ : ∀ {A₁ A₂ : VType} {C₁ C₂ : CType} → (e : A₁ ≡ A₂) → (e' : C₁ ≡ C₂)
       → map⇒ᵐ (inv⁻ e) (invᶜ⁺ e') ≈ᵐ inv⁺ (cong₂ _⇒_ e e')
inv⁺-⇒ refl refl = map⇒ᵐ-idᵐ

inv⁺-box : ∀ {ρ₁ ρ₂ : R} {A₁ A₂ : VType} → (e : ρ₁ ≡ ρ₂) → (e' : A₁ ≡ A₂)
         → (w : ρ₂ ≾ᵣ ρ₁)
         → [ ρ₂ ]ᶠ (inv⁺ e') ∘ᵐ []-≤ w ≈ᵐ inv⁺ (cong₂ [_]_ e e')
inv⁺-box refl refl w =
  ≈ᵐ-trans (∘ᵐ-congˡ []-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans ([]-≤-irr w ≾ᵣ-refl) []-≤-refl))

invᶜ⁺-‼ : ∀ {A₁ A₂ : VType} {ϵ₁ ϵ₂ : E} → (e : A₁ ≡ A₂) → (e' : ϵ₁ ≡ ϵ₂)
        → (w : ϵ₁ ≾ₑ ϵ₂)
        → Tᶠ (inv⁺ e) ∘ᵐ T-≤ w ≈ᵐ invᶜ⁺ (cong₂ _‼_ e e')
invᶜ⁺-‼ refl refl w =
  ≈ᵐ-trans (∘ᵐ-congˡ T-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityˡ _)
  (≈ᵐ-trans (T-≤-irr w ≾ₑ-refl) (T-≤-refl ≾ₑ-refl)))

invˣ⁺-∷ : ∀ {Γ₁ Γ₂ : Ctx} {A₁ A₂ : VType} → (e : Γ₁ ≡ Γ₂) → (e' : A₁ ≡ A₂)
        → mapˣᵐ (invˣ⁺ e) (inv⁺ e') ≈ᵐ invˣ⁺ (cong₂ _∷_ e e')
invˣ⁺-∷ refl refl = mapˣᵐ-idᵐ

invˣ⁺-⟨⟩ : ∀ {Γ₁ Γ₂ : Ctx} {ρ₁ ρ₂ : R} → (e : Γ₁ ≡ Γ₂) → (e' : ρ₁ ≡ ρ₂)
         → (w : ρ₁ ≾ᵣ ρ₂)
         → ⟨⟩-≤ w ∘ᵐ ⟨ ρ₁ ⟩ᶠ (invˣ⁺ e) ≈ᵐ invˣ⁺ (cong₂ _⟨_⟩ e e')
invˣ⁺-⟨⟩ refl refl w =
  ≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
  (≈ᵐ-trans (∘ᵐ-identityʳ _)
  (≈ᵐ-trans (⟨⟩-≤-irr w ≾ᵣ-refl) ⟨⟩-≤-refl))

-- `newᵉ` occurs only covariantly: freely under `|×|`, under the graded
-- monad's effect (`T-≤` covariant) and under a lock (`⟨⟩-≤` covariant);
-- never in a function's domain nor in a box's grade, both contravariant.

mutual

  CovV : ∀ {Θ} → OVType (Θ +e) → Set
  CovV (tvar α)  = ⊤
  CovV (Base b)  = ⊤
  CovV Unit      = ⊤
  CovV Bool      = ⊤
  CovV (A |×| B) = CovV A × CovV B
  CovV Empty     = ⊤
  CovV (A ⇒ C)   = NoNewV A × CovC C
  CovV ([ ρ ] A) = NoNewR ρ × CovV A

  CovC : ∀ {Θ} → OCType (Θ +e) → Set
  CovC (A ‼ ε) = CovV A

CovCtx : ∀ {Θ n} → OCtx (Θ +e) n → Set
CovCtx []        = ⊤
CovCtx (Γ ∷ A)   = CovCtx Γ × CovV A
CovCtx (Γ ⟨ ρ ⟩) = CovCtx Γ

nn⇒CovV : ∀ {Θ} → (A : OVType (Θ +e)) → NoNewV A → CovV A
nn⇒CovC : ∀ {Θ} → (C : OCType (Θ +e)) → NoNewC C → CovC C

nn⇒CovV (tvar α)  n = tt
nn⇒CovV (Base b)  n = tt
nn⇒CovV Unit      n = tt
nn⇒CovV Bool      n = tt
nn⇒CovV (A |×| B) (n , n') = nn⇒CovV A n , nn⇒CovV B n'
nn⇒CovV Empty     n = tt
nn⇒CovV (A ⇒ C)   (n , n') = n , nn⇒CovC C n'
nn⇒CovV ([ ρ ] A) (n , n') = n , nn⇒CovV A n'

nn⇒CovC (A ‼ ε) (n , n') = nn⇒CovV A n

nn⇒CovCtx : ∀ {Θ n} → (Γ : OCtx (Θ +e) n) → NoNewCtx Γ → CovCtx Γ
nn⇒CovCtx []        n        = tt
nn⇒CovCtx (Γ ∷ A)   (n , n') = nn⇒CovCtx Γ n , nn⇒CovV A n'
nn⇒CovCtx (Γ ⟨ ρ ⟩) (n , n') = nn⇒CovCtx Γ n

-- `NoNew*` and `Cov*` are built from `⊤`, `⊥` and `_×_`, hence are
-- propositions: a certificate is determined by what it certifies.

NoNewE-unique : ∀ {Θ} → (ε : EExp (Θ +e)) → (n n' : NoNewE ε) → n ≡ n'
NoNewE-unique (evar zero)    n n' = ⊥-elim n
NoNewE-unique (evar (suc i)) n n' = refl
NoNewE-unique (econst ε)     n n' = refl
NoNewE-unique (ε ·̂ₑ ε') (n , m) (n' , m') =
  cong₂ _,_ (NoNewE-unique ε n n') (NoNewE-unique ε' m m')

NoNewR-unique : ∀ {Θ} → (ρ : RExp (Θ +e)) → (n n' : NoNewR ρ) → n ≡ n'
NoNewR-unique (rvar i)   n n' = refl
NoNewR-unique (rconst ρ) n n' = refl
NoNewR-unique (ρ ·̂ᵣ ρ') (n , m) (n' , m') =
  cong₂ _,_ (NoNewR-unique ρ n n') (NoNewR-unique ρ' m m')
NoNewR-unique ∣ ε ∣̂ᵉ n n' = NoNewE-unique ε n n'

mutual

  NoNewV-unique : ∀ {Θ} → (A : OVType (Θ +e)) → (n n' : NoNewV A) → n ≡ n'
  NoNewV-unique (tvar α) n n' = refl
  NoNewV-unique (Base b) n n' = refl
  NoNewV-unique Unit     n n' = refl
  NoNewV-unique Bool     n n' = refl
  NoNewV-unique (A |×| B) (n , m) (n' , m') =
    cong₂ _,_ (NoNewV-unique A n n') (NoNewV-unique B m m')
  NoNewV-unique Empty    n n' = refl
  NoNewV-unique (A ⇒ C) (n , m) (n' , m') =
    cong₂ _,_ (NoNewV-unique A n n') (NoNewC-unique C m m')
  NoNewV-unique ([ ρ ] A) (n , m) (n' , m') =
    cong₂ _,_ (NoNewR-unique ρ n n') (NoNewV-unique A m m')

  NoNewC-unique : ∀ {Θ} → (C : OCType (Θ +e)) → (n n' : NoNewC C) → n ≡ n'
  NoNewC-unique (A ‼ ε) (n , m) (n' , m') =
    cong₂ _,_ (NoNewV-unique A n n') (NoNewE-unique ε m m')

mutual

  CovV-unique : ∀ {Θ} → (A : OVType (Θ +e)) → (c c' : CovV A) → c ≡ c'
  CovV-unique (tvar α) c c' = refl
  CovV-unique (Base b) c c' = refl
  CovV-unique Unit     c c' = refl
  CovV-unique Bool     c c' = refl
  CovV-unique (A |×| B) (c , d) (c' , d') =
    cong₂ _,_ (CovV-unique A c c') (CovV-unique B d d')
  CovV-unique Empty    c c' = refl
  CovV-unique (A ⇒ C) (n , d) (n' , d') =
    cong₂ _,_ (NoNewV-unique A n n') (CovC-unique C d d')
  CovV-unique ([ ρ ] A) (n , d) (n' , d') =
    cong₂ _,_ (NoNewR-unique ρ n n') (CovV-unique A d d')

  CovC-unique : ∀ {Θ} → (C : OCType (Θ +e)) → (c c' : CovC C) → c ≡ c'
  CovC-unique (A ‼ ε) c c' = CovV-unique A c c'


-- A variable's type occurs in its context, so a covariant context makes
-- the variable's type covariant too, and a `newᵉ`-free one `newᵉ`-free.

cov-∈ : ∀ {Θ m} {A : OVType (Θ +e)} {ρ : RExp (Θ +e)} {Γ : OCtx (Θ +e) m}
      → CovCtx Γ → A ∈̂[ ρ ] Γ → CovV A
cov-∈ (c , c') Hd        = c'
cov-∈ (c , c') (Tl-∷ x)  = cov-∈ c x
cov-∈ c        (Tl-⟨⟩ x) = cov-∈ c x


-- Left-to-right chaining of `≈ᵐ`

infixr 3 _∙≈_

_∙≈_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
_∙≈_ = ≈ᵐ-trans

module Cov {Θ : Scope} (θ : Grounding Θ) {ε₁ ε₂ : E} (q : ε₁ ≾ₑ ε₂) where

  θ₁ : Grounding (Θ +e)
  θ₁ = θ ,ᵍᵉ ε₁

  θ₂ : Grounding (Θ +e)
  θ₂ = θ ,ᵍᵉ ε₂

  nonew-e : (ε : EExp (Θ +e)) → NoNewE ε → ⟦ ε ⟧ᵉ θ₁ ≡ ⟦ ε ⟧ᵉ θ₂
  nonew-e (evar (suc i)) n = refl
  nonew-e (econst ε)     n = refl
  nonew-e (ε ·̂ₑ ε') (n , n') = cong₂ _·ₑ_ (nonew-e ε n) (nonew-e ε' n')

  nonew-r : (ρ : RExp (Θ +e)) → NoNewR ρ → ⟦ ρ ⟧ʳ θ₁ ≡ ⟦ ρ ⟧ʳ θ₂
  nonew-r (rvar i)   n = refl
  nonew-r (rconst ρ) n = refl
  nonew-r (ρ ·̂ᵣ ρ') (n , n') = cong₂ _·ᵣ_ (nonew-r ρ n) (nonew-r ρ' n')
  nonew-r ∣ ε ∣̂ᵉ     n       = cong mapᵉ (nonew-e ε n)

  mutual

    nonew-v : (A : OVType (Θ +e)) → NoNewV A → ⟦ A ⟧ᵒᵛ θ₁ ≡ ⟦ A ⟧ᵒᵛ θ₂
    nonew-v (tvar α)  n = refl
    nonew-v (Base b)  n = refl
    nonew-v Unit      n = refl
    nonew-v Bool      n = refl
    nonew-v (A |×| B) (n , n') = cong₂ _|×|_ (nonew-v A n) (nonew-v B n')
    nonew-v Empty     n = refl
    nonew-v (A ⇒ C)   (n , n') = cong₂ _⇒_ (nonew-v A n) (nonew-c C n')
    nonew-v ([ ρ ] A) (n , n') = cong₂ [_]_ (nonew-r ρ n) (nonew-v A n')

    nonew-c : (C : OCType (Θ +e)) → NoNewC C → ⟦ C ⟧ᵒᶜ θ₁ ≡ ⟦ C ⟧ᵒᶜ θ₂
    nonew-c (A ‼ ε) (n , n') = cong₂ _‼_ (nonew-v A n) (nonew-e ε n')

  nonew-ctx : ∀ {n} → (Γ : OCtx (Θ +e) n) → NoNewCtx Γ
            → ⟦ Γ ⟧ᵒᶜᵗˣ θ₁ ≡ ⟦ Γ ⟧ᵒᶜᵗˣ θ₂
  nonew-ctx []        n        = refl
  nonew-ctx (Γ ∷ A)   (n , n') = cong₂ _∷_ (nonew-ctx Γ n) (nonew-v A n')
  nonew-ctx (Γ ⟨ ρ ⟩) (n , n') = cong₂ _⟨_⟩ (nonew-ctx Γ n) (nonew-r ρ n')

  mutual

    covV : (A : OVType (Θ +e)) → CovV A → ⟦ ⟦ A ⟧ᵒᵛ θ₁ ⟧ᵛ →ᵐ ⟦ ⟦ A ⟧ᵒᵛ θ₂ ⟧ᵛ
    covV (tvar α)  c = idᵐ
    covV (Base b)  c = idᵐ
    covV Unit      c = idᵐ
    covV Bool      c = idᵐ
    covV (A |×| B) (c , c') = mapˣᵐ (covV A c) (covV B c')
    covV Empty     c = idᵐ
    covV (A ⇒ C)   (n , c) = map⇒ᵐ (inv⁻ (nonew-v A n)) (covC C c)
    covV ([ ρ ] A) (n , c) =
      [ ⟦ ρ ⟧ʳ θ₂ ]ᶠ (covV A c) ∘ᵐ []-≤ (≾ᵣ-reflexive (sym (nonew-r ρ n)))

    covC : (C : OCType (Θ +e)) → CovC C → ⟦ ⟦ C ⟧ᵒᶜ θ₁ ⟧ᶜ →ᵐ ⟦ ⟦ C ⟧ᵒᶜ θ₂ ⟧ᶜ
    covC (A ‼ ε) c = Tᶠ (covV A c) ∘ᵐ T-≤ (ground-mono-e {θ = θ} q ε)

  covCtx : ∀ {n} → (Γ : OCtx (Θ +e) n) → CovCtx Γ
         → ⟦ ⟦ Γ ⟧ᵒᶜᵗˣ θ₁ ⟧ᶜᵗˣ →ᵐ ⟦ ⟦ Γ ⟧ᵒᶜᵗˣ θ₂ ⟧ᶜᵗˣ
  covCtx []        c = idᵐ
  covCtx (Γ ∷ A)   (c , c') = mapˣᵐ (covCtx Γ c) (covV A c')
  covCtx (Γ ⟨ ρ ⟩) c =
    ⟨⟩-≤ (ground-mono-r {θ = θ} q ρ) ∘ᵐ ⟨ ⟦ ρ ⟧ʳ θ₁ ⟩ᶠ (covCtx Γ c)

  mutual

    covV-nn : (A : OVType (Θ +e)) → (c : CovV A) → (n : NoNewV A)
            → covV A c ≈ᵐ inv⁺ (nonew-v A n)
    covV-nn (tvar α) c n = ≈ᵐ-refl
    covV-nn (Base b) c n = ≈ᵐ-refl
    covV-nn Unit     c n = ≈ᵐ-refl
    covV-nn Bool     c n = ≈ᵐ-refl
    covV-nn (A |×| B) (c , c') (n , n') =
      ≈ᵐ-trans (mapˣᵐ-cong (covV-nn A c n) (covV-nn B c' n'))
               (inv⁺-× (nonew-v A n) (nonew-v B n'))
    covV-nn Empty    c n = ≈ᵐ-refl
    covV-nn (A ⇒ C) (n₀ , c) (n , n') =
      ≈ᵐ-trans (map⇒ᵐ-cong (inv⁻-irr (nonew-v A n₀) (nonew-v A n))
                           (covC-nn C c n'))
               (inv⁺-⇒ (nonew-v A n) (nonew-c C n'))
    covV-nn ([ ρ ] A) (n₀ , c) (n , n') =
      ≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (covV-nn A c n')))
               (inv⁺-box (nonew-r ρ n) (nonew-v A n')
                         (≾ᵣ-reflexive (sym (nonew-r ρ n₀))))

    covC-nn : (C : OCType (Θ +e)) → (c : CovC C) → (n : NoNewC C)
            → covC C c ≈ᵐ invᶜ⁺ (nonew-c C n)
    covC-nn (A ‼ ε) c (n , n') =
      ≈ᵐ-trans (∘ᵐ-congˡ (T-congᶠ (covV-nn A c n)))
               (invᶜ⁺-‼ (nonew-v A n) (nonew-e ε n')
                        (ground-mono-e {θ = θ} q ε))

  covCtx-nn : ∀ {m} → (Γ : OCtx (Θ +e) m) → (c : CovCtx Γ) → (n : NoNewCtx Γ)
            → covCtx Γ c ≈ᵐ invˣ⁺ (nonew-ctx Γ n)
  covCtx-nn []      c n = ≈ᵐ-refl
  covCtx-nn (Γ ∷ A) (c , c') (n , n') =
    ≈ᵐ-trans (mapˣᵐ-cong (covCtx-nn Γ c n) (covV-nn A c' n'))
             (invˣ⁺-∷ (nonew-ctx Γ n) (nonew-v A n'))
  covCtx-nn (Γ ⟨ ρ ⟩) c (n , n') =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (covCtx-nn Γ c n)))
             (invˣ⁺-⟨⟩ (nonew-ctx Γ n) (nonew-r ρ n')
                       (ground-mono-r {θ = θ} q ρ))

  -- `Eternal` has no clause for `_⇒_` or `[_]_`, and no other former of an
  -- open type carries a grade, so an eternal reading forces `newᵉ`-freeness.

  eternal-nn : (θ' : Grounding (Θ +e)) → (A : OVType (Θ +e))
             → Eternal (⟦ A ⟧ᵒᵛ θ') → NoNewV A
  eternal-nn θ' (tvar α)  et = tt
  eternal-nn θ' (Base b)  et = tt
  eternal-nn θ' Unit      et = tt
  eternal-nn θ' Bool      et = tt
  eternal-nn θ' (A |×| B) (et |×|ₑ et') =
    eternal-nn θ' A et , eternal-nn θ' B et'
  eternal-nn θ' Empty     et = tt

  -- Eternality of a type transfers between the two readings.

  eternal₁₂ : (A : OVType (Θ +e)) → Eternal (⟦ A ⟧ᵒᵛ θ₁) → Eternal (⟦ A ⟧ᵒᵛ θ₂)
  eternal₁₂ A et = subst Eternal (nonew-v A (eternal-nn θ₁ A et)) et

  eternal₂₁ : (A : OVType (Θ +e)) → Eternal (⟦ A ⟧ᵒᵛ θ₂) → Eternal (⟦ A ⟧ᵒᵛ θ₁)
  eternal₂₁ A et = subst Eternal (sym (nonew-v A (eternal-nn θ₂ A et))) et

  covV-irr : (A : OVType (Θ +e)) → (c c' : CovV A) → covV A c ≈ᵐ covV A c'
  covV-irr A c c' rewrite CovV-unique A c c' = ≈ᵐ-refl

  -- Naturality of the projection `var-proj` in the instantiation.

  cov-var-proj : ∀ {m} {A : OVType (Θ +e)} {ρ : RExp (Θ +e)} {Γ : OCtx (Θ +e) m}
               → (cΓ : CovCtx Γ) → (x : A ∈̂[ ρ ] Γ)
               → var-proj (ground-∈ θ₂ x) ∘ᵐ covCtx Γ cΓ
               ≈ᵐ ⟨⟩-≤ (ground-mono-r {θ = θ} q ρ)
                    ∘ᵐ ⟨ ⟦ ρ ⟧ʳ θ₁ ⟩ᶠ (covV _ (cov-∈ cΓ x))
                    ∘ᵐ var-proj (ground-∈ θ₁ x)
  cov-var-proj {A = A} (cΓ , cA) Hd =
       ∘ᵐ-assoc _ _ _
    ∙≈ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
    ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-η-nat (covV A cA)))
    ∙≈ ∘ᵐ-assoc _ _ _
    ∙≈ ≈ᵐ-sym (   ∘ᵐ-congˡ (⟨⟩-≤-irr _ ≾ᵣ-refl ∙≈ ⟨⟩-≤-refl)
               ∙≈ ∘ᵐ-identityˡ _)
  cov-var-proj (cΓ , cA) (Tl-∷ x) =
       ∘ᵐ-assoc _ _ _
    ∙≈ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
    ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙≈ ∘ᵐ-congˡ (cov-var-proj cΓ x)
    ∙≈ ∘ᵐ-assoc _ _ _
    ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  cov-var-proj {A = A} cΓ (Tl-⟨⟩ {ρ = ρ₀} {ρ' = ρ'} x) =
       ∘ᵐ-assoc _ _ _
    ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-nat _ _))
    ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
    ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
    ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-congᶠ (cov-var-proj cΓ x)))
    ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _))
    ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)))
    ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙≈ ∘ᵐ-congˡ aux
    ∙≈ ∘ᵐ-assoc _ _ _
    ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-μ-nat _)))
    ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
    ∙≈ ∘ᵐ-congˡ (⟨⟩-≤-irr _ (ground-mono-r {θ = θ} q (ρ' ·̂ᵣ ρ₀)))
    where
      aux : μ ∘ᵐ (   ⟨⟩-≤ (ground-mono-r {θ = θ} q ρ₀)
                  ∘ᵐ ⟨ ⟦ ρ₀ ⟧ʳ θ₁ ⟩ᶠ (⟨⟩-≤ (ground-mono-r {θ = θ} q ρ')))
          ≈ᵐ ⟨⟩-≤ _ ∘ᵐ μ
      aux =
           ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-≤-nat _ (ground-mono-r {θ = θ} q ρ₀)))
        ∙≈ ≈ᵐ-sym (⟨⟩-μ-≤ (ground-mono-r {θ = θ} q ρ₀)
                          (ground-mono-r {θ = θ} q ρ'))

  -- Naturality of the eternal extraction along a transport.

  extᵉ-inv⁺ : ∀ {A₁ A₂ : VType} → (e : A₁ ≡ A₂)
            → (et₁ : Eternal A₁) → (et₂ : Eternal A₂) → ∀ {ρ}
            → eternalᵛ-extᵉ et₂ {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (inv⁺ e)
            ≈ᵐ inv⁺ e ∘ᵐ eternalᵛ-extᵉ et₁ {ρ}
  extᵉ-inv⁺ refl et₁ et₂ =
    ≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
    (≈ᵐ-trans (∘ᵐ-identityʳ _)
    (≈ᵐ-trans (eternalᵛ-extᵉ-irr et₂ et₁) (≈ᵐ-sym (∘ᵐ-identityˡ _))))

  -- Unfolding `var-morphism` at a non-eternal type.

  var-morphism-unfold¬ᵉ : ∀ {Δ B ρ} → (¬et : ¬ Eternal B)
                        → (f : ¬ Eternal B → ρ ≾ᵣ uᵣ) → (y : B ∈[ ρ ] Δ)
                        → var-morphism f y ≈ᵐ εᵘ ∘ᵐ ⟨⟩-≤ (f ¬et) ∘ᵐ var-proj y
  var-morphism-unfold¬ᵉ {B = B} ¬et f y with eternal? B
  ... | yes et  = ⊥-elim (¬et et)
  ... | no ¬et' = ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr (f ¬et') (f ¬et)))

  -- Naturality of a variable's denotation in the instantiation.

  cov-var : ∀ {m} {A : OVType (Θ +e)} {ρ : RExp (Θ +e)} {Γ : OCtx (Θ +e) m}
          → (cΓ : CovCtx Γ) → (x : A ∈̂[ ρ ] Γ)
          → (f₁ : ¬ Eternal (⟦ A ⟧ᵒᵛ θ₁) → ⟦ ρ ⟧ʳ θ₁ ≾ᵣ uᵣ)
          → (f₂ : ¬ Eternal (⟦ A ⟧ᵒᵛ θ₂) → ⟦ ρ ⟧ʳ θ₂ ≾ᵣ uᵣ)
          → var-morphism f₂ (ground-∈ θ₂ x) ∘ᵐ covCtx Γ cΓ
          ≈ᵐ covV _ (cov-∈ cΓ x) ∘ᵐ var-morphism f₁ (ground-∈ θ₁ x)
  cov-var {A = A} {ρ} {Γ} cΓ x f₁ f₂ = go (eternal? (⟦ A ⟧ᵒᵛ θ₁))
    where
      go : Dec (Eternal (⟦ A ⟧ᵒᵛ θ₁))
         → var-morphism f₂ (ground-∈ θ₂ x) ∘ᵐ covCtx Γ cΓ
         ≈ᵐ covV A (cov-∈ cΓ x) ∘ᵐ var-morphism f₁ (ground-∈ θ₁ x)
      go (yes et₁) =
           ∘ᵐ-congˡ (var-morphism-unfoldᵉ (eternal₁₂ A et₁) f₂ (ground-∈ θ₂ x))
        ∙≈ ∘ᵐ-assoc _ _ _
        ∙≈ ∘ᵐ-congʳ (cov-var-proj cΓ x)
        ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
        ∙≈ ∘ᵐ-congˡ (eternalᵛ-extᵉ-≤ (eternal₁₂ A et₁) (ground-mono-r {θ = θ} q ρ))
        ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
        ∙≈ ∘ᵐ-congˡ (∘ᵐ-congʳ (⟨⟩-congᶠ (covV-nn A (cov-∈ cΓ x) nA)))
        ∙≈ ∘ᵐ-congˡ (extᵉ-inv⁺ (nonew-v A nA) et₁ (eternal₁₂ A et₁))
        ∙≈ ∘ᵐ-assoc _ _ _
        ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym (covV-nn A (cov-∈ cΓ x) nA))
        ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (var-morphism-unfoldᵉ et₁ f₁ (ground-∈ θ₁ x)))
        where
          nA : NoNewV A
          nA = eternal-nn θ₁ A et₁
      go (no ¬et₁) =
           ∘ᵐ-congˡ (var-morphism-unfold¬ᵉ ¬et₂ f₂ (ground-∈ θ₂ x))
        ∙≈ ∘ᵐ-assoc _ _ _
        ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
        ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (cov-var-proj cΓ x))
        ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        ∙≈ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-trans (ground-mono-r {θ = θ} q ρ) (f₂ ¬et₂)))
        ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
        ∙≈ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
        ∙≈ ∘ᵐ-congˡ (≈ᵐ-sym (ext-nat _ (covV A (cov-∈ cΓ x))))
        ∙≈ ∘ᵐ-assoc _ _ _
        ∙≈ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
        ∙≈ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr _ (f₁ ¬et₁))))
        ∙≈ ∘ᵐ-congʳ (≈ᵐ-sym (var-morphism-unfold¬ᵉ ¬et₁ f₁ (ground-∈ θ₁ x)))
        where
          ¬et₂ : ¬ Eternal (⟦ A ⟧ᵒᵛ θ₂)
          ¬et₂ et = ¬et₁ (eternal₂₁ A et)
