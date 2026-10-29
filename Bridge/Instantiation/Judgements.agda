------------------------------------------------------------------
-- Declarative satisfaction of hypotheses                       --
--                                                              --
-- A declarative instance `σ` satisfies `Q` (`σ ⊨ᴰ Q`) when     --
-- each atom of `Q` holds in the closed calculus at its         --
-- interpretation: an eternality atom as `Eternal`, a subtyping --
-- atom as `_<:ᵛ_`, an ordering in the grade's order, and a     --
-- var-rule disjunction as a sum.                               --
--                                                              --
-- Entailment is sound for it: what `Q` entails holds at every  --
-- instance satisfying `Q` (`sound-≾ᵣ`, `sound-≾ₑ`, `sound-⊩ᴱ`, --
-- `sound-<:ᵛ`, `sound-<:ᶜ`, `sound-VarOK`). A membership in an --
-- open context is one in its interpretation (`⟦_⟧ˣ`), and a    --
-- handler clause's weakened hypotheses hold at every extension --
-- of a satisfying instance (`⊨ᴰ-,ᵉ`).                          --
------------------------------------------------------------------

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.Maybe using (to-witness)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec) renaming (map to mapᵛ; [] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module Bridge.Instantiation.Judgements (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Language.Types                  S
open import ClosedCalculus.Syntax.Contexts  S
open import ClosedCalculus.Syntax.Subtyping S
import ClosedCalculus.Syntax.Erasure S as CE

open import OpenCalculus.Syntax.Grades   S
open import OpenCalculus.Syntax.Types    S
open import OpenCalculus.Syntax.Contexts S
open import OpenCalculus.Syntax.Subst    S
open import OpenCalculus.Hypotheses      S

open import Bridge.Instantiation.Types S

------------------------------------------------------------------------
-- Satisfaction

-- Grade orderings hold when each does in the grade's order

infix 4 _⊨ᴰᵒ_ _⊨ᴰ⟨_⟩_ _⊨ᴰᴼ_ _⊨ᴰ_

record _⊨ᴰᵒ_ {Θ : Scope} (σ : DInst Θ) (o : Ords Θ) : Set where
  constructor mk⊨ᴰᵒ
  field
    ⊨ors : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors o → ⟦ ρ ⟧ʳ σ ≾ᵣ ⟦ ρ' ⟧ʳ σ
    ⊨oes : ∀ {ε ε'} → (ε , ε') ∈ oes o → ⟦ ε ⟧ᵉ σ ≾ₑ ⟦ ε' ⟧ᵉ σ

open _⊨ᴰᵒ_ public

-- A quantified ordering `∀ᵉ j₁ … jₖ. O` holds when `O` does at every
-- extension by grades for its rigids

_⊨ᴰ⟨_⟩_ : ∀ {Θ} → DInst Θ → (k : ℕ) → Ords (Θ +eⁿ k) → Set
σ ⊨ᴰ⟨ zero ⟩  B = σ ⊨ᴰᵒ B
σ ⊨ᴰ⟨ suc k ⟩ B = (c : E) → (σ ,ᵉᴰ c) ⊨ᴰ⟨ k ⟩ B

_⊨ᴰᴼ_ : ∀ {Θ} → DInst Θ → QOrd Θ → Set
σ ⊨ᴰᴼ O = σ ⊨ᴰ⟨ rigids O ⟩ body O

-- A satisfying instance: each hypothesis holds, a quantified one at
-- every grade for its rigids; the truths hold at every instance

record _⊨ᴰ_ {Θ : Scope} (σ : DInst Θ) (Q : Hyps Θ) : Set where
  constructor mk⊨ᴰ
  field
    ⊨ets  : ∀ {α} → α ∈ ets Q → Eternal (ty σ α)
    ⊨subᵥ : ∀ {α β} → (α , β) ∈ subᵥ Q → ty σ α <:ᵛ ty σ β
    ⊨ordᵣ : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → ⟦ ρ ⟧ʳ σ ≾ᵣ ⟦ ρ' ⟧ʳ σ
    ⊨ordₑ : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → ⟦ ε ⟧ᵉ σ ≾ₑ ⟦ ε' ⟧ᵉ σ
    ⊨disj : ∀ {A ρ} → (A , ρ) ∈ disj Q → Eternal (⟦ A ⟧ᵛ σ) ⊎ (⟦ ρ ⟧ʳ σ ≾ᵣ uᵣ)
    ⊨qhyps : ∀ {O} → O ∈ qhyps Q → σ ⊨ᴰᴼ O

open _⊨ᴰ_ public

⊨ᴰ-∅ : ∀ {Θ} {σ : DInst Θ} → σ ⊨ᴰ ∅ᴴ
⊨ᴰ-∅ = mk⊨ᴰ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

⊨ᴰ-⊤ : ∀ {Θ} {σ : DInst Θ} → σ ⊨ᴰ ⊤ᴴ
⊨ᴰ-⊤ = mk⊨ᴰ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

-- Grade orderings along pointwise equal instances, at an instance of
-- the rigids, and along a substitution

⊨ᴰᵒ-≗ : ∀ {Θ} {σ σ' : DInst Θ} {o : Ords Θ} → σ ≗ᴰ σ' → σ ⊨ᴰᵒ o → σ' ⊨ᴰᵒ o
⊨ᴰᵒ-≗ p s = mk⊨ᴰᵒ
  (λ {ρ} {ρ'} m → subst₂ _≾ᵣ_ (⟦≗⟧ʳ p ρ) (⟦≗⟧ʳ p ρ') (⊨ors s m))
  (λ {ε} {ε'} m → subst₂ _≾ₑ_ (⟦≗⟧ᵉ p ε) (⟦≗⟧ᵉ p ε') (⊨oes s m))

⊨ᴰ⟨⟩-≗ : ∀ {Θ} {σ σ' : DInst Θ} → (k : ℕ) → {B : Ords (Θ +eⁿ k)}
       → σ ≗ᴰ σ' → σ ⊨ᴰ⟨ k ⟩ B → σ' ⊨ᴰ⟨ k ⟩ B
⊨ᴰ⟨⟩-≗ zero    p s = ⊨ᴰᵒ-≗ p s
⊨ᴰ⟨⟩-≗ (suc k) p s = λ c → ⊨ᴰ⟨⟩-≗ k (≗ᴰ-,ᵉ p c) (s c)

⊨ᴰ⟨⟩-at : ∀ {Θ k} {σ : DInst Θ} {B : Ords (Θ +eⁿ k)}
        → σ ⊨ᴰ⟨ k ⟩ B → (cs : Vec E k) → (σ ,ᵉᴰⁿ cs) ⊨ᴰᵒ B
⊨ᴰ⟨⟩-at s []ᵛ        = s
⊨ᴰ⟨⟩-at s (c ∷ᵛ cs) = ⊨ᴰ⟨⟩-at (s c) cs

⊨ᴰ⟨⟩-[] : ∀ {Θ Θ'} → (k : ℕ) → (τ : Subst Θ Θ') → (σ : DInst Θ') → {B : Ords (Θ +eⁿ k)}
        → (τ ⨟ᴰ σ) ⊨ᴰ⟨ k ⟩ B → σ ⊨ᴰ⟨ k ⟩ (B [ τ ↑ᵉⁿ k ]ᴼ)
⊨ᴰ⟨⟩-[] zero τ σ {B} s = mk⊨ᴰᵒ rd ed
  where
    rd : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors (B [ τ ]ᴼ) → ⟦ ρ ⟧ʳ σ ≾ᵣ ⟦ ρ' ⟧ʳ σ
    rd m with ∈-map⁻ (mapᵖ (_[ τ ]ʳ)) m
    ... | (x , y) , m₀ , refl = subst₂ _≾ᵣ_ (sym (⟦[]⟧ʳ τ σ x)) (sym (⟦[]⟧ʳ τ σ y)) (⊨ors s m₀)

    ed : ∀ {ε ε'} → (ε , ε') ∈ oes (B [ τ ]ᴼ) → ⟦ ε ⟧ᵉ σ ≾ₑ ⟦ ε' ⟧ᵉ σ
    ed m with ∈-map⁻ (mapᵖ (_[ τ ]ᵉ)) m
    ... | (x , y) , m₀ , refl = subst₂ _≾ₑ_ (sym (⟦[]⟧ᵉ τ σ x)) (sym (⟦[]⟧ᵉ τ σ y)) (⊨oes s m₀)
⊨ᴰ⟨⟩-[] (suc k) τ σ s c =
  ⊨ᴰ⟨⟩-[] k (τ ↑ᵉ) (σ ,ᵉᴰ c) (⊨ᴰ⟨⟩-≗ k (≗ᴰ-sym (↑ᵉ-⨟ᴰ τ σ c)) (s c))

------------------------------------------------------------------------
-- Soundness of convertibility and entailed ordering

sound-≡̂ᵣ : ∀ {Θ} {ρ ρ' : RExp Θ} → (σ : DInst Θ) → ρ ≡̂ᵣ ρ' → ⟦ ρ ⟧ʳ σ ≃ᵣ ⟦ ρ' ⟧ʳ σ
sound-≡̂ₑ : ∀ {Θ} {ε ε' : EExp Θ} → (σ : DInst Θ) → ε ≡̂ₑ ε' → ⟦ ε ⟧ᵉ σ ≃ₑ ⟦ ε' ⟧ᵉ σ
sound-≾ᵣ : ∀ {Θ} {σ : DInst Θ} {Q : Hyps Θ} {ρ ρ' : RExp Θ}
         → σ ⊨ᴰ Q → Q ⊩ ρ ≾̂ᵣ ρ' → ⟦ ρ ⟧ʳ σ ≾ᵣ ⟦ ρ' ⟧ʳ σ
sound-≾ₑ : ∀ {Θ} {σ : DInst Θ} {Q : Hyps Θ} {ε ε' : EExp Θ}
         → σ ⊨ᴰ Q → Q ⊩ ε ≾̂ₑ ε' → ⟦ ε ⟧ᵉ σ ≾ₑ ⟦ ε' ⟧ᵉ σ

-- An instance of the rigids at `σ` means their values; a closed one
-- means the values of its constants

private

  ⟦inst⟧ : ∀ {Θ k} → (es : Vec (EExp Θ) k) → (σ : DInst Θ)
         → ((idˢ ,ᵉⁿ es) ⨟ᴰ σ) ≗ᴰ (σ ,ᵉᴰⁿ mapᵛ (λ e → ⟦ e ⟧ᵉ σ) es)
  ⟦inst⟧ es σ = ≗ᴰ-trans (,ᵉⁿ-⨟ᴰ idˢ es σ) (≗ᴰ-,ᵉᴰⁿ (idˢ-⨟ᴰ σ) (mapᵛ (λ e → ⟦ e ⟧ᵉ σ) es))

  ⟦fact⟧ : ∀ {Θ k} → (es : Vec (EExp Θ) k) → (σ : DInst Θ)
         → ((from∅ ,ᵉⁿ mapᵛ econst (mapᵛ (λ e → ⟦ e ⟧ᵉ σ) es)) ⨟ᴰ ∅ᴰ)
             ≗ᴰ ((from∅ ,ᵉⁿ es) ⨟ᴰ σ)
  ⟦fact⟧ es σ =
    ≗ᴰ-trans (,ᵉⁿ-⨟ᴰ from∅ (mapᵛ econst cs) ∅ᴰ)
    (≗ᴰ-trans (subst (λ v → ((from∅ ⨟ᴰ ∅ᴰ) ,ᵉᴰⁿ mapᵛ (λ e → ⟦ e ⟧ᵉ ∅ᴰ) (mapᵛ econst cs))
                             ≗ᴰ ((from∅ ⨟ᴰ σ) ,ᵉᴰⁿ v))
                     (⟦consts⟧ cs)
                     (≗ᴰ-,ᵉᴰⁿ {σ = from∅ ⨟ᴰ ∅ᴰ} {σ' = from∅ ⨟ᴰ σ} (mk≗ᴰ (λ ()) (λ ()) (λ ()))
                              (mapᵛ (λ e → ⟦ e ⟧ᵉ ∅ᴰ) (mapᵛ econst cs))))
              (≗ᴰ-sym (,ᵉⁿ-⨟ᴰ from∅ es σ)))
    where
      cs = mapᵛ (λ e → ⟦ e ⟧ᵉ σ) es

sound-≡̂ᵣ σ ≡̂ᵣ-refl          = ≃ᵣ-refl
sound-≡̂ᵣ σ (≡̂ᵣ-sym p)       = ≃ᵣ-sym (sound-≡̂ᵣ σ p)
sound-≡̂ᵣ σ (≡̂ᵣ-trans p q)   = ≃ᵣ-trans (sound-≡̂ᵣ σ p) (sound-≡̂ᵣ σ q)
sound-≡̂ᵣ σ (≡̂ᵣ-cong p q)    = ·ᵣ-cong (sound-≡̂ᵣ σ p) (sound-≡̂ᵣ σ q)
sound-≡̂ᵣ σ (≡̂ᵣ-const e)     = e
sound-≡̂ᵣ σ ≡̂ᵣ-assoc         = ·ᵣ-assoc _ _ _
sound-≡̂ᵣ σ ≡̂ᵣ-identityˡ     = ·ᵣ-identityˡ _
sound-≡̂ᵣ σ ≡̂ᵣ-identityʳ     = ·ᵣ-identityʳ _
sound-≡̂ᵣ σ ≡̂ᵣ-const-·       = ≃ᵣ-refl
sound-≡̂ᵣ σ (≡̂ᵣ-comm ij)     = to-witness ij _ _
sound-≡̂ᵣ σ (≡̂ᵣ-cong-⊔ p q)  = ⊔ᵣ-cong (sound-≡̂ᵣ σ p) (sound-≡̂ᵣ σ q)
sound-≡̂ᵣ σ ≡̂ᵣ-const-⊔       = ≃ᵣ-refl
sound-≡̂ᵣ σ ≡̂ᵣ-comm-⊔        = ⊔ᵣ-comm _ _
sound-≡̂ᵣ σ ≡̂ᵣ-distribˡ-⊔    = ·ᵣ-distribˡ-⊔ᵣ _ _ _
sound-≡̂ᵣ σ ≡̂ᵣ-distribʳ-⊔    = ·ᵣ-distribʳ-⊔ᵣ _ _ _
sound-≡̂ᵣ σ ≡̂ᵣ-map-·         = map-·ᵉ
sound-≡̂ᵣ σ ≡̂ᵣ-map-⊔         = map-⊔ᵉ
sound-≡̂ᵣ σ ≡̂ᵣ-map-const     = ≃ᵣ-refl
sound-≡̂ᵣ σ (≡̂ᵣ-map-cong p)  = map-≃ᵉ (sound-≡̂ₑ σ p)
sound-≡̂ᵣ σ (≡̂ᵣ-absorb p)    = ⊔ᵣ-absorb (sound-≾ᵣ (⊨ᴰ-∅ {σ = σ}) p)

sound-≡̂ₑ σ ≡̂ₑ-refl          = ≃ₑ-refl
sound-≡̂ₑ σ (≡̂ₑ-sym p)       = ≃ₑ-sym (sound-≡̂ₑ σ p)
sound-≡̂ₑ σ (≡̂ₑ-trans p q)   = ≃ₑ-trans (sound-≡̂ₑ σ p) (sound-≡̂ₑ σ q)
sound-≡̂ₑ σ (≡̂ₑ-cong p q)    = ·ₑ-cong (sound-≡̂ₑ σ p) (sound-≡̂ₑ σ q)
sound-≡̂ₑ σ (≡̂ₑ-const e)     = e
sound-≡̂ₑ σ ≡̂ₑ-assoc         = ·ₑ-assoc _ _ _
sound-≡̂ₑ σ ≡̂ₑ-identityˡ     = ·ₑ-identityˡ _
sound-≡̂ₑ σ ≡̂ₑ-identityʳ     = ·ₑ-identityʳ _
sound-≡̂ₑ σ ≡̂ₑ-const-·       = ≃ₑ-refl
sound-≡̂ₑ σ (≡̂ₑ-comm ij)     = to-witness ij _ _
sound-≡̂ₑ σ (≡̂ₑ-cong-⊔ p q)  = ⊔ₑ-cong (sound-≡̂ₑ σ p) (sound-≡̂ₑ σ q)
sound-≡̂ₑ σ ≡̂ₑ-const-⊔       = ≃ₑ-refl
sound-≡̂ₑ σ ≡̂ₑ-comm-⊔        = ⊔ₑ-comm _ _
sound-≡̂ₑ σ ≡̂ₑ-distribˡ-⊔    = ·ₑ-distribˡ-⊔ₑ _ _ _
sound-≡̂ₑ σ ≡̂ₑ-distribʳ-⊔    = ·ₑ-distribʳ-⊔ₑ _ _ _
sound-≡̂ₑ σ (≡̂ₑ-absorb p)    = ⊔ₑ-absorb (sound-≾ₑ (⊨ᴰ-∅ {σ = σ}) p)

sound-≾ᵣ s (hypᵣ m)     = ⊨ordᵣ s m
sound-≾ᵣ s (atomᵣ p)    = p
sound-≾ᵣ {σ = σ} s (eqᵣ p) = ≃ᵣ⇒≾ᵣ (sound-≡̂ᵣ σ p)
sound-≾ᵣ s (transᵣ p q) = ≾ᵣ-trans (sound-≾ᵣ s p) (sound-≾ᵣ s q)
sound-≾ᵣ s (monoᵣ p q)  = ≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (sound-≾ᵣ s p)) (·ᵣ-monoʳ-≾ᵣ (sound-≾ᵣ s q))
sound-≾ᵣ s (map-mono p) = map-monotoneᵉ (sound-≾ₑ s p)
sound-≾ᵣ {σ = σ} s (⊔-ubˡᵣ {ρ₁} {ρ₂}) = ⊔ᵣ-ubˡ (⟦ ρ₁ ⟧ʳ σ) (⟦ ρ₂ ⟧ʳ σ)
sound-≾ᵣ {σ = σ} s (⊔-ubʳᵣ {ρ₁} {ρ₂}) = ⊔ᵣ-ubʳ (⟦ ρ₁ ⟧ʳ σ) (⟦ ρ₂ ⟧ʳ σ)
sound-≾ᵣ s (⊔-lubᵣ p q) = ⊔ᵣ-lub (sound-≾ᵣ s p) (sound-≾ᵣ s q)
sound-≾ᵣ {σ = σ} s (topᵣ {ρ}) = ≾-⊤ᵣ (⟦ ρ ⟧ʳ σ)
sound-≾ᵣ {σ = σ} {ρ' = ρ'} s (minᵣ ij) = to-witness ij (⟦ ρ' ⟧ʳ σ)
sound-≾ᵣ s (zeroˡᵣ p)   = ≾ᵣ-zero-productˡ (sound-≾ᵣ s p)
sound-≾ᵣ s (zeroʳᵣ p)   = ≾ᵣ-zero-productʳ (sound-≾ᵣ s p)
sound-≾ᵣ s (plusᵣ p q r) = Plus.c⁺-least p (sound-≾ᵣ s q) (sound-≾ᵣ s r)
sound-≾ᵣ s (indˡᵣ p q)  = Plus.⁺-indˡ p (sound-≾ᵣ s q)
sound-≾ᵣ s (indʳᵣ p q)  = Plus.⁺-indʳ p (sound-≾ᵣ s q)
sound-≾ᵣ {σ = σ} s (instᵣ {ρ = ρ} {ρ'} m mφ es) =
  subst₂ _≾ᵣ_ (sym (eq ρ)) (sym (eq ρ')) (⊨ors (⊨ᴰ⟨⟩-at (⊨qhyps s m) (mapᵛ (λ e → ⟦ e ⟧ᵉ σ) es)) mφ)
  where
    eq : ∀ x → ⟦ x [ idˢ ,ᵉⁿ es ]ʳ ⟧ʳ σ ≡ ⟦ x ⟧ʳ (σ ,ᵉᴰⁿ mapᵛ (λ e → ⟦ e ⟧ᵉ σ) es)
    eq x = trans (⟦[]⟧ʳ (idˢ ,ᵉⁿ es) σ x) (⟦≗⟧ʳ (⟦inst⟧ es σ) x)
sound-≾ᵣ {σ = σ} s (factᵣ {ρ = ρ} {ρ'} _ H es) =
  subst₂ _≾ᵣ_ (eq ρ) (eq ρ') (H es')
  where
    es' = mapᵛ econst (mapᵛ (λ e → ⟦ e ⟧ᵉ σ) es)
    eq : ∀ x → valʳ (x [ from∅ ,ᵉⁿ es' ]ʳ) ≡ ⟦ x [ from∅ ,ᵉⁿ es ]ʳ ⟧ʳ σ
    eq x = trans (sym (⟦⟧∅-valʳ (x [ from∅ ,ᵉⁿ es' ]ʳ)))
           (trans (⟦[]⟧ʳ (from∅ ,ᵉⁿ es') ∅ᴰ x)
           (trans (⟦≗⟧ʳ (⟦fact⟧ es σ) x) (sym (⟦[]⟧ʳ (from∅ ,ᵉⁿ es) σ x))))

sound-≾ₑ s (hypₑ m)     = ⊨ordₑ s m
sound-≾ₑ s (atomₑ p)    = p
sound-≾ₑ {σ = σ} s (eqₑ p) = ≃ₑ⇒≾ₑ (sound-≡̂ₑ σ p)
sound-≾ₑ s (transₑ p q) = ≾ₑ-trans (sound-≾ₑ s p) (sound-≾ₑ s q)
sound-≾ₑ s (monoₑ p q)  = ≾ₑ-trans (·ₑ-monoˡ-≾ₑ (sound-≾ₑ s p)) (·ₑ-monoʳ-≾ₑ (sound-≾ₑ s q))
sound-≾ₑ {σ = σ} s (⊔-ubˡₑ {ε₁} {ε₂}) = ⊔ₑ-ubˡ (⟦ ε₁ ⟧ᵉ σ) (⟦ ε₂ ⟧ᵉ σ)
sound-≾ₑ {σ = σ} s (⊔-ubʳₑ {ε₁} {ε₂}) = ⊔ₑ-ubʳ (⟦ ε₁ ⟧ᵉ σ) (⟦ ε₂ ⟧ᵉ σ)
sound-≾ₑ s (⊔-lubₑ p q) = ⊔ₑ-lub (sound-≾ₑ s p) (sound-≾ₑ s q)
sound-≾ₑ {σ = σ} s (topₑ {ε}) = ≾-⊤ₑ (⟦ ε ⟧ᵉ σ)
sound-≾ₑ {σ = σ} {ε' = ε'} s (minₑ ij) = to-witness ij (⟦ ε' ⟧ᵉ σ)
sound-≾ₑ s (zeroˡₑ p)   = ≾ₑ-zero-productˡ (sound-≾ₑ s p)
sound-≾ₑ s (zeroʳₑ p)   = ≾ₑ-zero-productʳ (sound-≾ₑ s p)
sound-≾ₑ s (plusₑ p q r) = Plus.c⁺-least p (sound-≾ₑ s q) (sound-≾ₑ s r)
sound-≾ₑ s (indˡₑ p q)  = Plus.⁺-indˡ p (sound-≾ₑ s q)
sound-≾ₑ s (indʳₑ p q)  = Plus.⁺-indʳ p (sound-≾ₑ s q)
sound-≾ₑ {σ = σ} s (instₑ {ε = ε} {ε'} m mφ es) =
  subst₂ _≾ₑ_ (sym (eq ε)) (sym (eq ε')) (⊨oes (⊨ᴰ⟨⟩-at (⊨qhyps s m) (mapᵛ (λ e → ⟦ e ⟧ᵉ σ) es)) mφ)
  where
    eq : ∀ x → ⟦ x [ idˢ ,ᵉⁿ es ]ᵉ ⟧ᵉ σ ≡ ⟦ x ⟧ᵉ (σ ,ᵉᴰⁿ mapᵛ (λ e → ⟦ e ⟧ᵉ σ) es)
    eq x = trans (⟦[]⟧ᵉ (idˢ ,ᵉⁿ es) σ x) (⟦≗⟧ᵉ (⟦inst⟧ es σ) x)
sound-≾ₑ {σ = σ} s (factₑ {ε = ε} {ε'} _ H es) =
  subst₂ _≾ₑ_ (eq ε) (eq ε') (H es')
  where
    es' = mapᵛ econst (mapᵛ (λ e → ⟦ e ⟧ᵉ σ) es)
    eq : ∀ x → valᵉ (x [ from∅ ,ᵉⁿ es' ]ᵉ) ≡ ⟦ x [ from∅ ,ᵉⁿ es ]ᵉ ⟧ᵉ σ
    eq x = trans (sym (⟦⟧∅-valᵉ (x [ from∅ ,ᵉⁿ es' ]ᵉ)))
           (trans (⟦[]⟧ᵉ (from∅ ,ᵉⁿ es') ∅ᴰ x)
           (trans (⟦≗⟧ᵉ (⟦fact⟧ es σ) x) (sym (⟦[]⟧ᵉ (from∅ ,ᵉⁿ es) σ x))))

------------------------------------------------------------------------
-- Soundness of the type-level judgements

-- Convertible types are subtypes of each other

sound-≡̂ᵛ : ∀ {Θ} {A A' : OVType Θ} → (σ : DInst Θ) → A ≡̂ᵛ A'
         → (⟦ A ⟧ᵛ σ <:ᵛ ⟦ A' ⟧ᵛ σ) × (⟦ A' ⟧ᵛ σ <:ᵛ ⟦ A ⟧ᵛ σ)
sound-≡̂ᶜ : ∀ {Θ} {C C' : OCType Θ} → (σ : DInst Θ) → C ≡̂ᶜ C'
         → (⟦ C ⟧ᶜ σ <:ᶜ ⟦ C' ⟧ᶜ σ) × (⟦ C' ⟧ᶜ σ <:ᶜ ⟦ C ⟧ᶜ σ)

sound-≡̂ᵛ σ (tvar≡̂ {α}) = <:ᵛ-refl (ty σ α) , <:ᵛ-refl (ty σ α)
sound-≡̂ᵛ σ Base≡̂       = Baseₛ refl , Baseₛ refl
sound-≡̂ᵛ σ Unit≡̂       = Unitₛ , Unitₛ
sound-≡̂ᵛ σ Bool≡̂       = Boolₛ , Boolₛ
sound-≡̂ᵛ σ Nat≡̂        = Natₛ , Natₛ
sound-≡̂ᵛ σ (p |×|≡̂ q)  = proj₁ (sound-≡̂ᵛ σ p) |×|ₛ proj₁ (sound-≡̂ᵛ σ q)
                        , proj₂ (sound-≡̂ᵛ σ p) |×|ₛ proj₂ (sound-≡̂ᵛ σ q)
sound-≡̂ᵛ σ (p |+|≡̂ q)  = proj₁ (sound-≡̂ᵛ σ p) |+|ₛ proj₁ (sound-≡̂ᵛ σ q)
                        , proj₂ (sound-≡̂ᵛ σ p) |+|ₛ proj₂ (sound-≡̂ᵛ σ q)
sound-≡̂ᵛ σ (|List|≡̂ p) = |List|ₛ (proj₁ (sound-≡̂ᵛ σ p)) , |List|ₛ (proj₂ (sound-≡̂ᵛ σ p))
sound-≡̂ᵛ σ Empty≡̂      = Emptyₛ , Emptyₛ
sound-≡̂ᵛ σ (p ⇒≡̂ q)    = proj₂ (sound-≡̂ᵛ σ p) ⇒ₛ proj₁ (sound-≡̂ᶜ σ q)
                        , proj₁ (sound-≡̂ᵛ σ p) ⇒ₛ proj₂ (sound-≡̂ᶜ σ q)
sound-≡̂ᵛ σ (p ⇛≡̂ q)    = <:ᵛ-refl handlerᴰ , <:ᵛ-refl handlerᴰ
sound-≡̂ᵛ σ ([ r ]≡̂ p)  = [ ≃ᵣ⇒≿ᵣ (sound-≡̂ᵣ σ r) ]ₛ proj₁ (sound-≡̂ᵛ σ p)
                        , [ ≃ᵣ⇒≾ᵣ (sound-≡̂ᵣ σ r) ]ₛ proj₂ (sound-≡̂ᵛ σ p)

sound-≡̂ᶜ σ (p ‼≡̂ e) = proj₁ (sound-≡̂ᵛ σ p) ‼ₛ ≃ₑ⇒≾ₑ (sound-≡̂ₑ σ e)
                    , proj₂ (sound-≡̂ᵛ σ p) ‼ₛ ≃ₑ⇒≿ₑ (sound-≡̂ₑ σ e)

module _ {Θ : Scope} {σ : DInst Θ} {Q : Hyps Θ} (s : σ ⊨ᴰ Q) where

  sound-⊩ᵗᵛ : ∀ {α β} → Q ⊩ᵗᵛ α ≾ β → ty σ α <:ᵛ ty σ β
  sound-⊩ᵗᵛ (reflᵗᵛ {α})  = <:ᵛ-refl (ty σ α)
  sound-⊩ᵗᵛ (hypᵗᵛ m)     = ⊨subᵥ s m
  sound-⊩ᵗᵛ (transᵗᵛ p q) = <:ᵛ-trans (sound-⊩ᵗᵛ p) (sound-⊩ᵗᵛ q)

  sound-⊩ᴱ : {A : OVType Θ} → Q ⊩ᴱ A → Eternal (⟦ A ⟧ᵛ σ)
  sound-⊩ᴱ (et-hyp m)     = ⊨ets s m
  sound-⊩ᴱ (et-subˡ p et) = <:ᵛ-eternalˡ (sound-⊩ᵗᵛ p) (sound-⊩ᴱ et)
  sound-⊩ᴱ (et-subʳ p et) = <:ᵛ-eternalʳ (sound-⊩ᵗᵛ p) (sound-⊩ᴱ et)
  sound-⊩ᴱ (Baseₑ p)      = Baseₑ p
  sound-⊩ᴱ Unitₑ          = Unitₑ
  sound-⊩ᴱ Boolₑ          = Boolₑ
  sound-⊩ᴱ Natₑ           = Natₑ
  sound-⊩ᴱ (p |×|ₑ q)     = sound-⊩ᴱ p |×|ₑ sound-⊩ᴱ q
  sound-⊩ᴱ (p |+|ₑ q)     = sound-⊩ᴱ p |+|ₑ sound-⊩ᴱ q
  sound-⊩ᴱ (|List|ₑ p)    = |List|ₑ (sound-⊩ᴱ p)
  sound-⊩ᴱ Emptyₑ         = Emptyₑ

  sound-<:ᵛ : {A B : OVType Θ} → Q ∣ A <:̂ᵛ B → ⟦ A ⟧ᵛ σ <:ᵛ ⟦ B ⟧ᵛ σ
  sound-<:ᶜ : {C D : OCType Θ} → Q ∣ C <:̂ᶜ D → ⟦ C ⟧ᶜ σ <:ᶜ ⟦ D ⟧ᶜ σ

  sound-<:ᵛ (tvarₛ p)   = sound-⊩ᵗᵛ p
  sound-<:ᵛ (Baseₛ p)   = Baseₛ p
  sound-<:ᵛ Unitₛ       = Unitₛ
  sound-<:ᵛ Boolₛ       = Boolₛ
  sound-<:ᵛ Natₛ        = Natₛ
  sound-<:ᵛ (p |×|ₛ q)  = sound-<:ᵛ p |×|ₛ sound-<:ᵛ q
  sound-<:ᵛ (p |+|ₛ q)  = sound-<:ᵛ p |+|ₛ sound-<:ᵛ q
  sound-<:ᵛ (|List|ₛ p) = |List|ₛ (sound-<:ᵛ p)
  sound-<:ᵛ Emptyₛ      = Emptyₛ
  sound-<:ᵛ (p ⇒ₛ q)    = sound-<:ᵛ p ⇒ₛ sound-<:ᶜ q
  sound-<:ᵛ (p ⇛ₛ q)    = <:ᵛ-refl handlerᴰ
  sound-<:ᵛ ([ p ]ₛ q)  = [ sound-≾ᵣ s p ]ₛ sound-<:ᵛ q

  sound-<:ᶜ (p ‼ₛ q) = sound-<:ᵛ p ‼ₛ sound-≾ₑ s q

  -- the var-rule disjunction

  sound-VarOK : {A : OVType Θ} {ρ : RExp Θ} → VarOK Q A ρ
              → Eternal (⟦ A ⟧ᵛ σ) ⊎ (⟦ ρ ⟧ʳ σ ≾ᵣ uᵣ)
  sound-VarOK (et-ok et) = inj₁ (sound-⊩ᴱ et)
  sound-VarOK (≾ᵘ-ok le) = inj₂ (sound-≾ᵣ s le)
  sound-VarOK (hyp-ok m p q) with ⊨disj s m
  ... | inj₁ et = inj₁ (<:ᵛ-eternalˡ (proj₁ (sound-≡̂ᵛ σ p)) et)
  ... | inj₂ le = inj₂ (≾ᵣ-trans (sound-≾ᵣ s q) le)

------------------------------------------------------------------------
-- Memberships

⟦_⟧ˣ : ∀ {Θ n} {Γ : OCtx Θ n} {A : OVType Θ} {ρ : RExp Θ}
     → A ∈̂[ ρ ] Γ → {σ : DInst Θ} → ⟦ A ⟧ᵛ σ ∈[ ⟦ ρ ⟧ʳ σ ] ⟦ Γ ⟧ᶜᵗˣ σ
⟦ Hd ⟧ˣ       = Hd
⟦ Tl-∷ x ⟧ˣ   = Tl-∷ ⟦ x ⟧ˣ
⟦ Tl-⟨⟩ x ⟧ˣ  = Tl-⟨⟩ ⟦ x ⟧ˣ

-- at the same position

⟦⟧ˣ-pos : ∀ {Θ n} {Γ : OCtx Θ n} {A : OVType Θ} {ρ : RExp Θ} {σ : DInst Θ}
        → (x : A ∈̂[ ρ ] Γ) → CE.var-pos (⟦ x ⟧ˣ {σ}) ≡ toℕ (var-pos x)
⟦⟧ˣ-pos Hd        = refl
⟦⟧ˣ-pos (Tl-∷ x)  = cong suc (⟦⟧ˣ-pos x)
⟦⟧ˣ-pos (Tl-⟨⟩ x) = ⟦⟧ˣ-pos x

------------------------------------------------------------------------
-- A handler clause is typed under `wkᵉ-H Q`, which every extension of
-- an instance satisfying `Q` satisfies

⊨ᴰ-,ᵉ : ∀ {Θ} {σ : DInst Θ} {Q : Hyps Θ} → (c : E) → σ ⊨ᴰ Q → (σ ,ᵉᴰ c) ⊨ᴰ wkᵉ-H Q
⊨ᴰ-,ᵉ {Θ} {σ} {Q} c s = mk⊨ᴰ ets' subᵥ' ordᵣ' ordₑ' disj' qhyps'
  where
    ets' : ∀ {α} → α ∈ ets (wkᵉ-H Q) → Eternal (ty (σ ,ᵉᴰ c) α)
    ets' m with ∈-map⁻ (wkᵉ-tv Θ) m
    ... | _ , m₀ , refl = ⊨ets s m₀

    subᵥ' : ∀ {α β} → (α , β) ∈ subᵥ (wkᵉ-H Q) → ty (σ ,ᵉᴰ c) α <:ᵛ ty (σ ,ᵉᴰ c) β
    subᵥ' m with ∈-map⁻ (mapᵖ (wkᵉ-tv Θ)) m
    ... | _ , m₀ , refl = ⊨subᵥ s m₀

    ordᵣ' : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ (wkᵉ-H Q)
          → ⟦ ρ ⟧ʳ (σ ,ᵉᴰ c) ≾ᵣ ⟦ ρ' ⟧ʳ (σ ,ᵉᴰ c)
    ordᵣ' m with ∈-map⁻ (mapᵖ wkᵉ-r) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
      subst₂ _≾ᵣ_ (sym (⟦wkᵉ⟧ʳ σ c ρ₀)) (sym (⟦wkᵉ⟧ʳ σ c ρ₀')) (⊨ordᵣ s m₀)

    ordₑ' : ∀ {ε ε'} → (ε , ε') ∈ ordₑ (wkᵉ-H Q)
          → ⟦ ε ⟧ᵉ (σ ,ᵉᴰ c) ≾ₑ ⟦ ε' ⟧ᵉ (σ ,ᵉᴰ c)
    ordₑ' m with ∈-map⁻ (mapᵖ wkᵉ-e) m
    ... | (ε₀ , ε₀') , m₀ , refl =
      subst₂ _≾ₑ_ (sym (⟦wkᵉ⟧ᵉ σ c ε₀)) (sym (⟦wkᵉ⟧ᵉ σ c ε₀')) (⊨ordₑ s m₀)

    disj' : ∀ {A ρ} → (A , ρ) ∈ disj (wkᵉ-H Q)
          → Eternal (⟦ A ⟧ᵛ (σ ,ᵉᴰ c)) ⊎ (⟦ ρ ⟧ʳ (σ ,ᵉᴰ c) ≾ᵣ uᵣ)
    disj' m with ∈-map⁻ (mapᵈ wkᵉ-v wkᵉ-r) m
    ... | (A₀ , ρ₀) , m₀ , refl =
      subst₂ (λ X r → Eternal X ⊎ (r ≾ᵣ uᵣ)) (sym (⟦wkᵉ⟧ᵛ σ c A₀)) (sym (⟦wkᵉ⟧ʳ σ c ρ₀))
             (⊨disj s m₀)

    qhyps' : ∀ {O} → O ∈ qhyps (wkᵉ-H Q) → (σ ,ᵉᴰ c) ⊨ᴰᴼ O
    qhyps' m with ∈-map⁻ (_[ wkˢᵉ ]ᵠ) m
    ... | O₀ , m₀ , refl =
      ⊨ᴰ⟨⟩-[] (rigids O₀) wkˢᵉ (σ ,ᵉᴰ c) (⊨ᴰ⟨⟩-≗ (rigids O₀) ≗ᴰ-refl (⊨qhyps s m₀))
