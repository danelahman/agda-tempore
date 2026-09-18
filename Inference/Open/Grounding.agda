------------------------------------------------------------------
-- Grounding the mirrored (open) language                         --
--                                                                --
-- A `Grounding Θ` assigns a closed type or grade to every        --
-- variable of the scope `Θ`, and the interpretations `⟦_⟧` send  --
-- every open expression, type and context to a closed one. The   --
-- barrier `_ᴱ̂` is sent to the eternal restriction `_ᴱ` of        --
-- `Syntax.Contexts`, on the nose.                                --
--                                                                --
-- On top of that sit the lemmas the grounding theorem consumes:  --
-- `θ ⊨ᴴ Q` (the grounding satisfies the hypothesis set),         --
-- groundings of convertibility, entailment and eternality, the   --
-- two membership translations, the round-trips of the closed     --
-- embeddings, and the collapse of an effect-scope weakening.     --
------------------------------------------------------------------

-- `Bool` is renamed, as `OVType` has a constructor of that name
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import Inference.Scopes

module Inference.Open.Grounding (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Contexts S
open import Syntax.Types    S

open import Inference.Open.Grades   S
open import Inference.Open.Types    S
open import Inference.Open.Contexts S
open import Inference.Open.Hyps     S

-- Only the two side conditions are needed; the constructors of the mirrored
-- judgement would otherwise clash with those of the original one.

open import Inference.Open.Language S using (VarOK; UnboxOK)

--------------------------------------------------------------
-- Groundings                                                --
--------------------------------------------------------------

record Grounding (Θ : Scope) : Set where
  constructor grounding
  field
    gTy : TyVar Θ → VType                  -- type variables to closed value types
    gR  : RVar Θ → R                       -- resource-grade variables to grades
    gE  : EVar Θ → E                       -- effect-grade variables to grades

open Grounding public

-- Extending a grounding along a scope extension. Defined by case analysis on
-- the variable rather than by composing with an injection, so that the
-- extension reduces on `zero` and on `suc`.

infixl 28 _,ᵍᵗ_ _,ᵍʳ_ _,ᵍᵉ_

_,ᵍᵗ_ : ∀ {Θ} → Grounding Θ → VType → Grounding (Θ +ty)
gTy (θ ,ᵍᵗ A) zero    = A
gTy (θ ,ᵍᵗ A) (suc α) = gTy θ α
gR  (θ ,ᵍᵗ A) i       = gR θ i
gE  (θ ,ᵍᵗ A) i       = gE θ i

_,ᵍʳ_ : ∀ {Θ} → Grounding Θ → R → Grounding (Θ +r)
gTy (θ ,ᵍʳ ρ) α       = gTy θ α
gR  (θ ,ᵍʳ ρ) zero    = ρ
gR  (θ ,ᵍʳ ρ) (suc i) = gR θ i
gE  (θ ,ᵍʳ ρ) i       = gE θ i

_,ᵍᵉ_ : ∀ {Θ} → Grounding Θ → E → Grounding (Θ +e)
gTy (θ ,ᵍᵉ ε) α       = gTy θ α
gR  (θ ,ᵍᵉ ε) i       = gR θ i
gE  (θ ,ᵍᵉ ε) zero    = ε
gE  (θ ,ᵍᵉ ε) (suc i) = gE θ i

--------------------------------------------------------------
-- Interpretation of open expressions, types and contexts    --
--------------------------------------------------------------

-- Grade expressions: every former is sent to its closed counterpart, so in
-- particular `⟦ ûᵣ ⟧ʳ θ` is `uᵣ` and `⟦ ∣ ε ∣̂ᵉ ⟧ʳ θ` is `mapᵉ ⟦ ε ⟧ᵉ θ`.

⟦_⟧ᵉ : ∀ {Θ} → EExp Θ → Grounding Θ → E
⟦ evar i   ⟧ᵉ θ = gE θ i
⟦ econst ε ⟧ᵉ θ = ε
⟦ ε ·̂ₑ ε'  ⟧ᵉ θ = ⟦ ε ⟧ᵉ θ ·ₑ ⟦ ε' ⟧ᵉ θ

⟦_⟧ʳ : ∀ {Θ} → RExp Θ → Grounding Θ → R
⟦ rvar i   ⟧ʳ θ = gR θ i
⟦ rconst ρ ⟧ʳ θ = ρ
⟦ ρ ·̂ᵣ ρ'  ⟧ʳ θ = ⟦ ρ ⟧ʳ θ ·ᵣ ⟦ ρ' ⟧ʳ θ
⟦ ∣ ε ∣̂ᵉ   ⟧ʳ θ = mapᵉ (⟦ ε ⟧ᵉ θ)

-- Types

mutual

  ⟦_⟧ᵛ : ∀ {Θ} → OVType Θ → Grounding Θ → VType
  ⟦ tvar α   ⟧ᵛ θ = gTy θ α
  ⟦ Base b   ⟧ᵛ θ = Base b
  ⟦ Unit     ⟧ᵛ θ = Unit
  ⟦ Bool     ⟧ᵛ θ = Bool
  ⟦ A |×| B  ⟧ᵛ θ = ⟦ A ⟧ᵛ θ |×| ⟦ B ⟧ᵛ θ
  ⟦ Empty    ⟧ᵛ θ = Empty
  ⟦ A ⇒ C    ⟧ᵛ θ = ⟦ A ⟧ᵛ θ ⇒ ⟦ C ⟧ᶜ θ
  ⟦ [ ρ ] A  ⟧ᵛ θ = [ ⟦ ρ ⟧ʳ θ ] ⟦ A ⟧ᵛ θ

  ⟦_⟧ᶜ : ∀ {Θ} → OCType Θ → Grounding Θ → CType
  ⟦ A ‼ ε ⟧ᶜ θ = ⟦ A ⟧ᵛ θ ‼ ⟦ ε ⟧ᵉ θ

-- Contexts: the barrier becomes the eternal restriction of the original.

⟦_⟧ᶜᵗˣ : ∀ {Θ n} → OCtx Θ n → Grounding Θ → Ctx
⟦ []      ⟧ᶜᵗˣ θ = []
⟦ Γ ∷ A   ⟧ᶜᵗˣ θ = ⟦ Γ ⟧ᶜᵗˣ θ ∷ ⟦ A ⟧ᵛ θ
⟦ Γ ⟨ ρ ⟩ ⟧ᶜᵗˣ θ = ⟦ Γ ⟧ᶜᵗˣ θ ⟨ ⟦ ρ ⟧ʳ θ ⟩
⟦ Γ ᴱ̂     ⟧ᶜᵗˣ θ = (⟦ Γ ⟧ᶜᵗˣ θ) ᴱ

--------------------------------------------------------------
-- Groundings satisfying a hypothesis set                    --
--------------------------------------------------------------

infix 4 _⊨ᴴ_

record _⊨ᴴ_ {Θ : Scope} (θ : Grounding Θ) (Q : Hyps Θ) : Set where
  constructor mk⊨ᴴ
  field
    etOK   : ∀ {α} → α ∈ ets Q → Eternal (gTy θ α)
    ordROK : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → ⟦ ρ ⟧ʳ θ ≾ᵣ ⟦ ρ' ⟧ʳ θ
    ordEOK : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → ⟦ ε ⟧ᵉ θ ≾ₑ ⟦ ε' ⟧ᵉ θ

open _⊨ᴴ_ public

-- Every grounding satisfies the empty hypothesis set

∅ᴴ-⊨ : ∀ {Θ} {θ : Grounding Θ} → θ ⊨ᴴ ∅ᴴ
∅ᴴ-⊨ = mk⊨ᴴ (λ ()) (λ ()) (λ ())

--------------------------------------------------------------
-- Grounding of convertibility                               --
--------------------------------------------------------------

ground-≡̂ᵣ : ∀ {Θ} {θ : Grounding Θ} {ρ ρ' : RExp Θ}
          → ρ ≡̂ᵣ ρ' → ⟦ ρ ⟧ʳ θ ≡ ⟦ ρ' ⟧ʳ θ
ground-≡̂ₑ : ∀ {Θ} {θ : Grounding Θ} {ε ε' : EExp Θ}
          → ε ≡̂ₑ ε' → ⟦ ε ⟧ᵉ θ ≡ ⟦ ε' ⟧ᵉ θ

ground-≡̂ᵣ ≡̂ᵣ-refl          = refl
ground-≡̂ᵣ (≡̂ᵣ-sym p)       = sym (ground-≡̂ᵣ p)
ground-≡̂ᵣ (≡̂ᵣ-trans p q)   = trans (ground-≡̂ᵣ p) (ground-≡̂ᵣ q)
ground-≡̂ᵣ (≡̂ᵣ-cong p q)    = cong₂ _·ᵣ_ (ground-≡̂ᵣ p) (ground-≡̂ᵣ q)
ground-≡̂ᵣ ≡̂ᵣ-assoc         = ·ᵣ-assoc _ _ _
ground-≡̂ᵣ ≡̂ᵣ-identityˡ     = ·ᵣ-identityˡ _
ground-≡̂ᵣ ≡̂ᵣ-identityʳ     = ·ᵣ-identityʳ _
ground-≡̂ᵣ ≡̂ᵣ-const-·       = refl
ground-≡̂ᵣ ≡̂ᵣ-map-·         = map-·ᵉ
ground-≡̂ᵣ ≡̂ᵣ-map-const     = refl
ground-≡̂ᵣ (≡̂ᵣ-map-cong p)  = cong mapᵉ (ground-≡̂ₑ p)

ground-≡̂ₑ ≡̂ₑ-refl        = refl
ground-≡̂ₑ (≡̂ₑ-sym p)     = sym (ground-≡̂ₑ p)
ground-≡̂ₑ (≡̂ₑ-trans p q) = trans (ground-≡̂ₑ p) (ground-≡̂ₑ q)
ground-≡̂ₑ (≡̂ₑ-cong p q)  = cong₂ _·ₑ_ (ground-≡̂ₑ p) (ground-≡̂ₑ q)
ground-≡̂ₑ ≡̂ₑ-assoc       = ·ₑ-assoc _ _ _
ground-≡̂ₑ ≡̂ₑ-identityˡ   = ·ₑ-identityˡ _
ground-≡̂ₑ ≡̂ₑ-identityʳ   = ·ₑ-identityʳ _
ground-≡̂ₑ ≡̂ₑ-const-·     = refl

--------------------------------------------------------------
-- Grounding of entailment                                   --
--------------------------------------------------------------

ground-≾ᵣ : ∀ {Θ} {θ : Grounding Θ} {Q : Hyps Θ} {ρ ρ' : RExp Θ}
          → θ ⊨ᴴ Q → Q ⊩ ρ ≾̂ᵣ ρ' → ⟦ ρ ⟧ʳ θ ≾ᵣ ⟦ ρ' ⟧ʳ θ
ground-≾ₑ : ∀ {Θ} {θ : Grounding Θ} {Q : Hyps Θ} {ε ε' : EExp Θ}
          → θ ⊨ᴴ Q → Q ⊩ ε ≾̂ₑ ε' → ⟦ ε ⟧ᵉ θ ≾ₑ ⟦ ε' ⟧ᵉ θ

ground-≾ᵣ h (hypᵣ m)     = ordROK h m
ground-≾ᵣ h (atomᵣ p)    = p
ground-≾ᵣ h (eqᵣ p)      = ≾ᵣ-reflexive (ground-≡̂ᵣ p)
ground-≾ᵣ h (transᵣ p q) = ≾ᵣ-trans (ground-≾ᵣ h p) (ground-≾ᵣ h q)
ground-≾ᵣ h (monoᵣ p q)  = ≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (ground-≾ᵣ h p))
                                    (·ᵣ-monoʳ-≾ᵣ (ground-≾ᵣ h q))
ground-≾ᵣ h (map-mono p) = map-monotoneᵉ (ground-≾ₑ h p)
ground-≾ᵣ {θ = θ} {ρ' = ρ'} h (minᵣ p) = p (⟦ ρ' ⟧ʳ θ)

ground-≾ₑ h (hypₑ m)     = ordEOK h m
ground-≾ₑ h (atomₑ p)    = p
ground-≾ₑ h (eqₑ p)      = ≾ₑ-reflexive (ground-≡̂ₑ p)
ground-≾ₑ h (transₑ p q) = ≾ₑ-trans (ground-≾ₑ h p) (ground-≾ₑ h q)
ground-≾ₑ h (monoₑ p q)  = ≾ₑ-trans (·ₑ-monoˡ-≾ₑ (ground-≾ₑ h p))
                                    (·ₑ-monoʳ-≾ₑ (ground-≾ₑ h q))
ground-≾ₑ {θ = θ} {ε' = ε'} h (minₑ p) = p (⟦ ε' ⟧ᵉ θ)

--------------------------------------------------------------
-- Grounding of eternality                                   --
--------------------------------------------------------------

ground-Et : ∀ {Θ} {θ : Grounding Θ} {Q : Hyps Θ} {A : OVType Θ}
          → θ ⊨ᴴ Q → Q ⊩ᴱ A → Eternal (⟦ A ⟧ᵛ θ)
ground-Et h (et-hyp m)       = etOK h m
ground-Et h (Baseₑ p)        = Baseₑ p
ground-Et h Unitₑ            = Unitₑ
ground-Et h Boolₑ            = Boolₑ
ground-Et h (et₁ |×|ₑ et₂)   = ground-Et h et₁ |×|ₑ ground-Et h et₂
ground-Et h Emptyₑ           = Emptyₑ

--------------------------------------------------------------
-- Grounding of variables                                    --
--                                                           --
-- Two translations: one for a variable that stays on this   --
-- side of every barrier, where each membership former maps  --
-- to its counterpart; one for a variable of eternal type,   --
-- which additionally crosses barriers via `∈-ᴱ`.            --
--------------------------------------------------------------

ground-∈ : ∀ {Θ n} {A : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
         → (θ : Grounding Θ) → (x : A ∈̂[ ρ ] Γ) → crossesᴱ̂ x ≡ false
         → ⟦ A ⟧ᵛ θ ∈[ ⟦ ρ ⟧ʳ θ ] ⟦ Γ ⟧ᶜᵗˣ θ
ground-∈ θ Hd        eq = Hd
ground-∈ θ (Tl-∷ x)  eq = Tl-∷ (ground-∈ θ x eq)
ground-∈ θ (Tl-⟨⟩ x) eq = Tl-⟨⟩ (ground-∈ θ x eq)

ground-∈ᴱ : ∀ {Θ n} {A : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
          → (θ : Grounding Θ) → (x : A ∈̂[ ρ ] Γ) → Eternal (⟦ A ⟧ᵛ θ)
          → ⟦ A ⟧ᵛ θ ∈[ ⟦ ρ ⟧ʳ θ ] ⟦ Γ ⟧ᶜᵗˣ θ
ground-∈ᴱ θ Hd        et = Hd
ground-∈ᴱ θ (Tl-∷ x)  et = Tl-∷ (ground-∈ᴱ θ x et)
ground-∈ᴱ θ (Tl-⟨⟩ x) et = Tl-⟨⟩ (ground-∈ᴱ θ x et)
ground-∈ᴱ θ (Tl-ᴱ̂ x)  et = ∈-ᴱ et (ground-∈ᴱ θ x et)

--------------------------------------------------------------
-- Grounding the side conditions of `var` and `unbox`        --
--                                                           --
-- `VarOK`/`UnboxOK` compute by recursion on the crossing     --
-- flag, so the flag is generalised to a `𝔹` argument with   --
-- its defining equation attached; the caller instantiates    --
-- it with `crossesᴱ̂ x` and `refl`.                          --
--------------------------------------------------------------

ground-var : ∀ {Θ n} {Q : Hyps Θ} {A : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
           → (θ : Grounding Θ) → θ ⊨ᴴ Q
           → (b : 𝔹) → (x : A ∈̂[ ρ ] Γ) → crossesᴱ̂ x ≡ b → VarOK Q A ρ b
           → (¬ Eternal (⟦ A ⟧ᵛ θ) → ⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)
           × (⟦ A ⟧ᵛ θ ∈[ ⟦ ρ ⟧ʳ θ ] ⟦ Γ ⟧ᶜᵗˣ θ)
ground-var θ h true  x eq ok =
  (λ ¬et → ⊥-elim (¬et (ground-Et h ok))) , ground-∈ᴱ θ x (ground-Et h ok)
ground-var θ h false x eq (inj₁ et) =
  (λ ¬et → ⊥-elim (¬et (ground-Et h et))) , ground-∈ θ x eq
ground-var θ h false x eq (inj₂ le) =
  (λ _ → ground-≾ᵣ h le) , ground-∈ θ x eq

ground-unbox : ∀ {Θ n} {Q : Hyps Θ} {A : OVType Θ} {ρ ρ' : RExp Θ} {Γ : OCtx Θ n}
             → (θ : Grounding Θ) → θ ⊨ᴴ Q
             → (b : 𝔹) → (x : [ ρ ] A ∈̂[ ρ' ] Γ) → crossesᴱ̂ x ≡ b
             → UnboxOK Q ρ' ρ b
             → (⟦ ρ' ⟧ʳ θ ≾ᵣ ⟦ ρ ⟧ʳ θ)
             × ([ ⟦ ρ ⟧ʳ θ ] ⟦ A ⟧ᵛ θ ∈[ ⟦ ρ' ⟧ʳ θ ] ⟦ Γ ⟧ᶜᵗˣ θ)
ground-unbox θ h false x eq le = ground-≾ᵣ h le , ground-∈ θ x eq

--------------------------------------------------------------
-- Round-trips of the closed embeddings                      --
--------------------------------------------------------------

mutual

  ⌜⌝ᵛ-ground : ∀ {Θ} {θ : Grounding Θ} → (A : VType) → ⟦ ⌜ A ⌝ᵛ ⟧ᵛ θ ≡ A
  ⌜⌝ᵛ-ground (Base b)   = refl
  ⌜⌝ᵛ-ground Unit       = refl
  ⌜⌝ᵛ-ground Bool       = refl
  ⌜⌝ᵛ-ground (A |×| B)  = cong₂ _|×|_ (⌜⌝ᵛ-ground A) (⌜⌝ᵛ-ground B)
  ⌜⌝ᵛ-ground Empty      = refl
  ⌜⌝ᵛ-ground (A ⇒ C)    = cong₂ _⇒_ (⌜⌝ᵛ-ground A) (⌜⌝ᶜ-ground C)
  ⌜⌝ᵛ-ground ([ ρ ] A)  = cong [ ρ ]_ (⌜⌝ᵛ-ground A)

  ⌜⌝ᶜ-ground : ∀ {Θ} {θ : Grounding Θ} → (C : CType) → ⟦ ⌜ C ⌝ᶜ ⟧ᶜ θ ≡ C
  ⌜⌝ᶜ-ground (A ‼ ε) = cong (_‼ ε) (⌜⌝ᵛ-ground A)

⌜⌝ᵍ-ground : ∀ {Θ} {θ : Grounding Θ} → (G : GType) → ⟦ ⌜ G ⌝ᵍ ⟧ᵛ θ ≡ type-of-gtype G
⌜⌝ᵍ-ground (Base b)    = refl
⌜⌝ᵍ-ground Unit        = refl
⌜⌝ᵍ-ground Bool        = refl
⌜⌝ᵍ-ground Empty       = refl
⌜⌝ᵍ-ground (A |×|ᵍ B)  = cong₂ _|×|_ (⌜⌝ᵍ-ground A) (⌜⌝ᵍ-ground B)
⌜⌝ᵍ-ground ([ ρ ]ᵍ A)  = cong [ ρ ]_ (⌜⌝ᵍ-ground A)

--------------------------------------------------------------
-- Collapse of an effect-scope weakening                     --
--                                                           --
-- Weakening into `Θ +e` and then grounding the new variable --
-- away is the identity on interpretations. Needed by the     --
-- `handle` case, whose clauses live at `Θ +e`.               --
--------------------------------------------------------------

ground-wkᵉ-e : ∀ {Θ} {θ : Grounding Θ} {ε₀ : E} → (ε : EExp Θ)
             → ⟦ wkᵉ-e ε ⟧ᵉ (θ ,ᵍᵉ ε₀) ≡ ⟦ ε ⟧ᵉ θ
ground-wkᵉ-e (evar i)   = refl
ground-wkᵉ-e (econst ε) = refl
ground-wkᵉ-e (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (ground-wkᵉ-e ε) (ground-wkᵉ-e ε')

ground-wkᵉ-r : ∀ {Θ} {θ : Grounding Θ} {ε₀ : E} → (ρ : RExp Θ)
             → ⟦ wkᵉ-r ρ ⟧ʳ (θ ,ᵍᵉ ε₀) ≡ ⟦ ρ ⟧ʳ θ
ground-wkᵉ-r (rvar i)   = refl
ground-wkᵉ-r (rconst ρ) = refl
ground-wkᵉ-r (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (ground-wkᵉ-r ρ) (ground-wkᵉ-r ρ')
ground-wkᵉ-r ∣ ε ∣̂ᵉ     = cong mapᵉ (ground-wkᵉ-e ε)

mutual

  ground-wkᵉ-v : ∀ {Θ} {θ : Grounding Θ} {ε₀ : E} → (A : OVType Θ)
               → ⟦ wkᵉ-v A ⟧ᵛ (θ ,ᵍᵉ ε₀) ≡ ⟦ A ⟧ᵛ θ
  ground-wkᵉ-v (tvar α)  = refl
  ground-wkᵉ-v (Base b)  = refl
  ground-wkᵉ-v Unit      = refl
  ground-wkᵉ-v Bool      = refl
  ground-wkᵉ-v (A |×| B) = cong₂ _|×|_ (ground-wkᵉ-v A) (ground-wkᵉ-v B)
  ground-wkᵉ-v Empty     = refl
  ground-wkᵉ-v (A ⇒ C)   = cong₂ _⇒_ (ground-wkᵉ-v A) (ground-wkᵉ-c C)
  ground-wkᵉ-v ([ ρ ] A) = cong₂ [_]_ (ground-wkᵉ-r ρ) (ground-wkᵉ-v A)

  ground-wkᵉ-c : ∀ {Θ} {θ : Grounding Θ} {ε₀ : E} → (C : OCType Θ)
               → ⟦ wkᵉ-c C ⟧ᶜ (θ ,ᵍᵉ ε₀) ≡ ⟦ C ⟧ᶜ θ
  ground-wkᵉ-c (A ‼ ε) = cong₂ _‼_ (ground-wkᵉ-v A) (ground-wkᵉ-e ε)

ground-wkᵉ-ctx : ∀ {Θ n} {θ : Grounding Θ} {ε₀ : E} → (Γ : OCtx Θ n)
               → ⟦ wkᵉ-ctx Γ ⟧ᶜᵗˣ (θ ,ᵍᵉ ε₀) ≡ ⟦ Γ ⟧ᶜᵗˣ θ
ground-wkᵉ-ctx []        = refl
ground-wkᵉ-ctx (Γ ∷ A)   = cong₂ _∷_ (ground-wkᵉ-ctx Γ) (ground-wkᵉ-v A)
ground-wkᵉ-ctx (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (ground-wkᵉ-ctx Γ) (ground-wkᵉ-r ρ)
ground-wkᵉ-ctx (Γ ᴱ̂)     = cong _ᴱ (ground-wkᵉ-ctx Γ)

-- An extended grounding satisfies the weakened hypothesis set

⊨ᴴ-wkᵉ-ground : ∀ {Θ} {θ : Grounding Θ} {Q : Hyps Θ} {ε₀ : E}
              → θ ⊨ᴴ Q → (θ ,ᵍᵉ ε₀) ⊨ᴴ wkᵉ-H Q
⊨ᴴ-wkᵉ-ground {Θ} {θ} {Q} {ε₀} h = mk⊨ᴴ et ordR ordE
  where
    et : ∀ {α} → α ∈ ets (wkᵉ-H Q) → Eternal (gTy (θ ,ᵍᵉ ε₀) α)
    et m with ∈-map⁻ (wkᵉ-tv Θ) m
    ... | α₀ , m₀ , refl = etOK h m₀

    ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ (wkᵉ-H Q)
         → ⟦ ρ ⟧ʳ (θ ,ᵍᵉ ε₀) ≾ᵣ ⟦ ρ' ⟧ʳ (θ ,ᵍᵉ ε₀)
    ordR m with ∈-map⁻ (mapᵖ wkᵉ-r) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
      subst₂ _≾ᵣ_ (sym (ground-wkᵉ-r ρ₀)) (sym (ground-wkᵉ-r ρ₀')) (ordROK h m₀)

    ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ (wkᵉ-H Q)
         → ⟦ ε ⟧ᵉ (θ ,ᵍᵉ ε₀) ≾ₑ ⟦ ε' ⟧ᵉ (θ ,ᵍᵉ ε₀)
    ordE m with ∈-map⁻ (mapᵖ wkᵉ-e) m
    ... | (ε₀' , ε₀'') , m₀ , refl =
      subst₂ _≾ₑ_ (sym (ground-wkᵉ-e ε₀')) (sym (ground-wkᵉ-e ε₀'')) (ordEOK h m₀)
