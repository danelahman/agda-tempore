------------------------------------------------------------------
-- Closed instances of the open syntax and declarative ones     --
--                                                              --
-- A closed instance `δ : Subst Θ ∅ˢ` replaces the variables by --
-- closed open types and grade expressions; a declarative       --
-- instance `σ : DInst Θ` by closed types and grades. The two   --
-- correspond.                                                  --
--                                                              --
-- Closed open syntax means its interpretation at the empty     --
-- instance (`⌞_⌟`), on grades the value. Every closed type     --
-- arises: `⌜_⌝ᵛ`, each grade a constant, is a section          --
-- (`⌞⌜_⌝⌟ᵛ`), and a closed open type is convertible to the     --
-- embedding of its meaning (`⌜⌞_⌟⌝ᵛ`).                         --
--                                                              --
-- A closed instance `δ` determines the declarative instance    --
-- `⌞ δ ⌟ˢ`, with `⌞ A [ δ ]ᵛ ⌟ᵛ ≡ ⟦ A ⟧ᵛ ⌞ δ ⌟ˢ` for grades,   --
-- types, computation types and contexts (`⌞[]⌟ᵛ` and the       --
-- like), and `δ ⊨ Q ∣ []` exactly when `⌞ δ ⌟ˢ ⊨ᴰ Q` (`⊨⇔⊨ᴰ`). --
-- Every declarative instance `σ` arises so, from `⌜ σ ⌝ˢ`,     --
-- which sends each variable to a constant: `⌞ ⌜ σ ⌝ˢ ⌟ˢ` is    --
-- `σ` pointwise (`⌞⌜_⌝ˢ⌟`), and satisfies what `σ` satisfies   --
-- (`⌜⌝ˢ-⊨`).                                                   --
------------------------------------------------------------------

open import Data.Fin using (zero; suc)
open import Data.List.Base using ([]) renaming (_∷_ to _∷ˡ_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Product using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module Instantiation.Correspondence (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types     S
open import Syntax.Contexts  S
open import Syntax.Subtyping S

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S

open import Instantiation.Types      S
open import Instantiation.Judgements S

------------------------------------------------------------------------
-- Pointwise equal instances interpret alike and satisfy alike

infix 4 _≗ᴰ_

record _≗ᴰ_ {Θ} (σ σ' : DInst Θ) : Set where
  constructor mk≗ᴰ
  field
    ty≗  : ∀ α → ty σ α ≡ ty σ' α
    res≗ : ∀ i → res σ i ≡ res σ' i
    eff≗ : ∀ i → eff σ i ≡ eff σ' i

open _≗ᴰ_ public

module _ {Θ} {σ σ' : DInst Θ} (p : σ ≗ᴰ σ') where

  ⟦≗⟧ᵉ : (ε : EExp Θ) → ⟦ ε ⟧ᵉ σ ≡ ⟦ ε ⟧ᵉ σ'
  ⟦≗⟧ᵉ (evar i)   = eff≗ p i
  ⟦≗⟧ᵉ (econst c) = refl
  ⟦≗⟧ᵉ (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (⟦≗⟧ᵉ ε) (⟦≗⟧ᵉ ε')
  ⟦≗⟧ᵉ (ε ⊔̂ₑ ε')  = cong₂ _⊔ₑ_ (⟦≗⟧ᵉ ε) (⟦≗⟧ᵉ ε')

  ⟦≗⟧ʳ : (ρ : RExp Θ) → ⟦ ρ ⟧ʳ σ ≡ ⟦ ρ ⟧ʳ σ'
  ⟦≗⟧ʳ (rvar i)   = res≗ p i
  ⟦≗⟧ʳ (rconst c) = refl
  ⟦≗⟧ʳ (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (⟦≗⟧ʳ ρ) (⟦≗⟧ʳ ρ')
  ⟦≗⟧ʳ (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔ᵣ_ (⟦≗⟧ʳ ρ) (⟦≗⟧ʳ ρ')
  ⟦≗⟧ʳ ∣ ε ∣̂ᵉ     = cong mapᵉ (⟦≗⟧ᵉ ε)

  mutual

    ⟦≗⟧ᵛ : (A : OVType Θ) → ⟦ A ⟧ᵛ σ ≡ ⟦ A ⟧ᵛ σ'
    ⟦≗⟧ᵛ (tvar α)   = ty≗ p α
    ⟦≗⟧ᵛ (Base b)   = refl
    ⟦≗⟧ᵛ Unit       = refl
    ⟦≗⟧ᵛ Bool       = refl
    ⟦≗⟧ᵛ Nat        = refl
    ⟦≗⟧ᵛ (A |×| B)  = cong₂ _|×|_ (⟦≗⟧ᵛ A) (⟦≗⟧ᵛ B)
    ⟦≗⟧ᵛ (A |+| B)  = cong₂ _|+|_ (⟦≗⟧ᵛ A) (⟦≗⟧ᵛ B)
    ⟦≗⟧ᵛ (|List| A) = cong |List| (⟦≗⟧ᵛ A)
    ⟦≗⟧ᵛ Empty      = refl
    ⟦≗⟧ᵛ (A ⇒ C)    = cong₂ _⇒_ (⟦≗⟧ᵛ A) (⟦≗⟧ᶜ C)
    ⟦≗⟧ᵛ ([ ρ ] A)  = cong₂ [_]_ (⟦≗⟧ʳ ρ) (⟦≗⟧ᵛ A)

    ⟦≗⟧ᶜ : (C : OCType Θ) → ⟦ C ⟧ᶜ σ ≡ ⟦ C ⟧ᶜ σ'
    ⟦≗⟧ᶜ (A ‼ ε) = cong₂ _‼_ (⟦≗⟧ᵛ A) (⟦≗⟧ᵉ ε)

  ⟦≗⟧ᶜᵗˣ : ∀ {n} → (Γ : OCtx Θ n) → ⟦ Γ ⟧ᶜᵗˣ σ ≡ ⟦ Γ ⟧ᶜᵗˣ σ'
  ⟦≗⟧ᶜᵗˣ []        = refl
  ⟦≗⟧ᶜᵗˣ (Γ ∷ A)   = cong₂ _∷_ (⟦≗⟧ᶜᵗˣ Γ) (⟦≗⟧ᵛ A)
  ⟦≗⟧ᶜᵗˣ (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (⟦≗⟧ᶜᵗˣ Γ) (⟦≗⟧ʳ ρ)

  ⊨ᴰ-≗ : {Q : Hyps Θ} → σ ⊨ᴰ Q → σ' ⊨ᴰ Q
  ⊨ᴰ-≗ s = mk⊨ᴰ
    (λ m → subst Eternal (ty≗ p _) (⊨ets s m))
    (λ m → subst₂ _<:ᵛ_ (ty≗ p _) (ty≗ p _) (⊨subᵥ s m))
    (λ {ρ} {ρ'} m → subst₂ _≾ᵣ_ (⟦≗⟧ʳ ρ) (⟦≗⟧ʳ ρ') (⊨ordᵣ s m))
    (λ {ε} {ε'} m → subst₂ _≾ₑ_ (⟦≗⟧ᵉ ε) (⟦≗⟧ᵉ ε') (⊨ordₑ s m))
    (λ {A} {ρ} m → subst₂ (λ X r → Eternal X ⊎ (r ≾ᵣ uᵣ)) (⟦≗⟧ᵛ A) (⟦≗⟧ʳ ρ) (⊨disj s m))

  ⊨ᴰᵒ-≗ : {o : Ords Θ} → σ ⊨ᴰᵒ o → σ' ⊨ᴰᵒ o
  ⊨ᴰᵒ-≗ s = mk⊨ᴰᵒ
    (λ {ρ} {ρ'} m → subst₂ _≾ᵣ_ (⟦≗⟧ʳ ρ) (⟦≗⟧ʳ ρ') (⊨ors s m))
    (λ {ε} {ε'} m → subst₂ _≾ₑ_ (⟦≗⟧ᵉ ε) (⟦≗⟧ᵉ ε') (⊨oes s m))

------------------------------------------------------------------------
-- Substitution: interpreting `X [ δ ]` at `σ` is interpreting `X` at
-- the composite `δ ⨟ᴰ σ`

infixl 25 _⨟ᴰ_

_⨟ᴰ_ : ∀ {Θ Θ'} → Subst Θ Θ' → DInst Θ' → DInst Θ
δ ⨟ᴰ σ = dinst (λ α → ⟦ sTy δ α ⟧ᵛ σ) (λ i → ⟦ sR δ i ⟧ʳ σ) (λ i → ⟦ sE δ i ⟧ᵉ σ)

module _ {Θ Θ'} (δ : Subst Θ Θ') (σ : DInst Θ') where

  ⟦[]⟧ᵉ : (ε : EExp Θ) → ⟦ ε [ δ ]ᵉ ⟧ᵉ σ ≡ ⟦ ε ⟧ᵉ (δ ⨟ᴰ σ)
  ⟦[]⟧ᵉ (evar i)   = refl
  ⟦[]⟧ᵉ (econst c) = refl
  ⟦[]⟧ᵉ (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (⟦[]⟧ᵉ ε) (⟦[]⟧ᵉ ε')
  ⟦[]⟧ᵉ (ε ⊔̂ₑ ε')  = cong₂ _⊔ₑ_ (⟦[]⟧ᵉ ε) (⟦[]⟧ᵉ ε')

  ⟦[]⟧ʳ : (ρ : RExp Θ) → ⟦ ρ [ δ ]ʳ ⟧ʳ σ ≡ ⟦ ρ ⟧ʳ (δ ⨟ᴰ σ)
  ⟦[]⟧ʳ (rvar i)   = refl
  ⟦[]⟧ʳ (rconst c) = refl
  ⟦[]⟧ʳ (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (⟦[]⟧ʳ ρ) (⟦[]⟧ʳ ρ')
  ⟦[]⟧ʳ (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔ᵣ_ (⟦[]⟧ʳ ρ) (⟦[]⟧ʳ ρ')
  ⟦[]⟧ʳ ∣ ε ∣̂ᵉ     = cong mapᵉ (⟦[]⟧ᵉ ε)

  mutual

    ⟦[]⟧ᵛ : (A : OVType Θ) → ⟦ A [ δ ]ᵛ ⟧ᵛ σ ≡ ⟦ A ⟧ᵛ (δ ⨟ᴰ σ)
    ⟦[]⟧ᵛ (tvar α)   = refl
    ⟦[]⟧ᵛ (Base b)   = refl
    ⟦[]⟧ᵛ Unit       = refl
    ⟦[]⟧ᵛ Bool       = refl
    ⟦[]⟧ᵛ Nat        = refl
    ⟦[]⟧ᵛ (A |×| B)  = cong₂ _|×|_ (⟦[]⟧ᵛ A) (⟦[]⟧ᵛ B)
    ⟦[]⟧ᵛ (A |+| B)  = cong₂ _|+|_ (⟦[]⟧ᵛ A) (⟦[]⟧ᵛ B)
    ⟦[]⟧ᵛ (|List| A) = cong |List| (⟦[]⟧ᵛ A)
    ⟦[]⟧ᵛ Empty      = refl
    ⟦[]⟧ᵛ (A ⇒ C)    = cong₂ _⇒_ (⟦[]⟧ᵛ A) (⟦[]⟧ᶜ C)
    ⟦[]⟧ᵛ ([ ρ ] A)  = cong₂ [_]_ (⟦[]⟧ʳ ρ) (⟦[]⟧ᵛ A)

    ⟦[]⟧ᶜ : (C : OCType Θ) → ⟦ C [ δ ]ᶜ ⟧ᶜ σ ≡ ⟦ C ⟧ᶜ (δ ⨟ᴰ σ)
    ⟦[]⟧ᶜ (A ‼ ε) = cong₂ _‼_ (⟦[]⟧ᵛ A) (⟦[]⟧ᵉ ε)

  ⟦[]⟧ᶜᵗˣ : ∀ {n} → (Γ : OCtx Θ n) → ⟦ Γ [ δ ]ᶜᵗˣ ⟧ᶜᵗˣ σ ≡ ⟦ Γ ⟧ᶜᵗˣ (δ ⨟ᴰ σ)
  ⟦[]⟧ᶜᵗˣ []        = refl
  ⟦[]⟧ᶜᵗˣ (Γ ∷ A)   = cong₂ _∷_ (⟦[]⟧ᶜᵗˣ Γ) (⟦[]⟧ᵛ A)
  ⟦[]⟧ᶜᵗˣ (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (⟦[]⟧ᶜᵗˣ Γ) (⟦[]⟧ʳ ρ)

-- Entailment along a substitution: an instance of the entailing set,
-- composed with the substitution, is an instance of the entailed one

sound-⊩ᴴ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {δ : Subst Θ Θ'} {σ : DInst Θ'}
         → Q' ⊩ᴴ Q [ δ ] → σ ⊨ᴰ Q' → (δ ⨟ᴰ σ) ⊨ᴰ Q
sound-⊩ᴴ {δ = δ} {σ} h s = mk⊨ᴰ
  (λ m → sound-⊩ᴱ s (⊩ets h m))
  (λ m → sound-<:ᵛ s (⊩subᵥ h m))
  (λ {ρ} {ρ'} m → subst₂ _≾ᵣ_ (⟦[]⟧ʳ δ σ ρ) (⟦[]⟧ʳ δ σ ρ') (sound-≾ᵣ s (⊩ordᵣ h m)))
  (λ {ε} {ε'} m → subst₂ _≾ₑ_ (⟦[]⟧ᵉ δ σ ε) (⟦[]⟧ᵉ δ σ ε') (sound-≾ₑ s (⊩ordₑ h m)))
  (λ {A} {ρ} m → subst₂ (λ X r → Eternal X ⊎ (r ≾ᵣ uᵣ)) (⟦[]⟧ᵛ δ σ A) (⟦[]⟧ʳ δ σ ρ)
                        (sound-VarOK s (⊩disj h m)))

sound-⊩ᵒ : ∀ {Θ Θ'} {o : Ords Θ} {Q' : Hyps Θ'} {δ : Subst Θ Θ'} {σ : DInst Θ'}
         → Q' ⊩ᵒ o [ δ ] → σ ⊨ᴰ Q' → (δ ⨟ᴰ σ) ⊨ᴰᵒ o
sound-⊩ᵒ {δ = δ} {σ} h s = mk⊨ᴰᵒ
  (λ {ρ} {ρ'} m → subst₂ _≾ᵣ_ (⟦[]⟧ʳ δ σ ρ) (⟦[]⟧ʳ δ σ ρ') (sound-≾ᵣ s (⊩ors h m)))
  (λ {ε} {ε'} m → subst₂ _≾ₑ_ (⟦[]⟧ᵉ δ σ ε) (⟦[]⟧ᵉ δ σ ε') (sound-≾ₑ s (⊩oes h m)))

------------------------------------------------------------------------
-- Closed open syntax: the interpretation at the empty instance

∅ᴰ : DInst ∅ˢ
∅ᴰ = dinst (λ ()) (λ ()) (λ ())

⌞_⌟ᵉ : EExp ∅ˢ → E
⌞ ε ⌟ᵉ = ⟦ ε ⟧ᵉ ∅ᴰ

⌞_⌟ʳ : RExp ∅ˢ → R
⌞ ρ ⌟ʳ = ⟦ ρ ⟧ʳ ∅ᴰ

⌞_⌟ᵛ : OVType ∅ˢ → VType
⌞ A ⌟ᵛ = ⟦ A ⟧ᵛ ∅ᴰ

⌞_⌟ᶜ : OCType ∅ˢ → CType
⌞ C ⌟ᶜ = ⟦ C ⟧ᶜ ∅ᴰ

⌞_⌟ᶜᵗˣ : ∀ {n} → OCtx ∅ˢ n → Ctx
⌞ Γ ⌟ᶜᵗˣ = ⟦ Γ ⟧ᶜᵗˣ ∅ᴰ

-- on grades, the values

⌞⌟-valᵉ : (ε : EExp ∅ˢ) → ⌞ ε ⌟ᵉ ≡ valᵉ ε
⌞⌟-valᵉ (evar ())
⌞⌟-valᵉ (econst c) = refl
⌞⌟-valᵉ (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (⌞⌟-valᵉ ε) (⌞⌟-valᵉ ε')
⌞⌟-valᵉ (ε ⊔̂ₑ ε')  = cong₂ _⊔ₑ_ (⌞⌟-valᵉ ε) (⌞⌟-valᵉ ε')

⌞⌟-valʳ : (ρ : RExp ∅ˢ) → ⌞ ρ ⌟ʳ ≡ valʳ ρ
⌞⌟-valʳ (rvar ())
⌞⌟-valʳ (rconst c) = refl
⌞⌟-valʳ (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (⌞⌟-valʳ ρ) (⌞⌟-valʳ ρ')
⌞⌟-valʳ (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔ᵣ_ (⌞⌟-valʳ ρ) (⌞⌟-valʳ ρ')
⌞⌟-valʳ ∣ ε ∣̂ᵉ     = cong mapᵉ (⌞⌟-valᵉ ε)

-- Every closed type arises: the embedding, each grade a constant, is a
-- section of `⌞_⌟`

mutual

  ⌜_⌝ᵛ : VType → OVType ∅ˢ
  ⌜ Base b ⌝ᵛ     = Base b
  ⌜ Unit ⌝ᵛ       = Unit
  ⌜ Bool ⌝ᵛ       = Bool
  ⌜ Nat ⌝ᵛ        = Nat
  ⌜ A |×| B ⌝ᵛ    = ⌜ A ⌝ᵛ |×| ⌜ B ⌝ᵛ
  ⌜ A |+| B ⌝ᵛ    = ⌜ A ⌝ᵛ |+| ⌜ B ⌝ᵛ
  ⌜ |List| A ⌝ᵛ   = |List| ⌜ A ⌝ᵛ
  ⌜ Empty ⌝ᵛ      = Empty
  ⌜ A ⇒ C ⌝ᵛ      = ⌜ A ⌝ᵛ ⇒ ⌜ C ⌝ᶜ
  ⌜ [ ρ ] A ⌝ᵛ    = [ rconst ρ ] ⌜ A ⌝ᵛ

  ⌜_⌝ᶜ : CType → OCType ∅ˢ
  ⌜ A ‼ ε ⌝ᶜ = ⌜ A ⌝ᵛ ‼ econst ε

mutual

  ⌞⌜_⌝⌟ᵛ : (A : VType) → ⌞ ⌜ A ⌝ᵛ ⌟ᵛ ≡ A
  ⌞⌜ Base b ⌝⌟ᵛ   = refl
  ⌞⌜ Unit ⌝⌟ᵛ     = refl
  ⌞⌜ Bool ⌝⌟ᵛ     = refl
  ⌞⌜ Nat ⌝⌟ᵛ      = refl
  ⌞⌜ A |×| B ⌝⌟ᵛ  = cong₂ _|×|_ ⌞⌜ A ⌝⌟ᵛ ⌞⌜ B ⌝⌟ᵛ
  ⌞⌜ A |+| B ⌝⌟ᵛ  = cong₂ _|+|_ ⌞⌜ A ⌝⌟ᵛ ⌞⌜ B ⌝⌟ᵛ
  ⌞⌜ |List| A ⌝⌟ᵛ = cong |List| ⌞⌜ A ⌝⌟ᵛ
  ⌞⌜ Empty ⌝⌟ᵛ    = refl
  ⌞⌜ A ⇒ C ⌝⌟ᵛ    = cong₂ _⇒_ ⌞⌜ A ⌝⌟ᵛ ⌞⌜ C ⌝⌟ᶜ
  ⌞⌜ [ ρ ] A ⌝⌟ᵛ  = cong ([ ρ ]_) ⌞⌜ A ⌝⌟ᵛ

  ⌞⌜_⌝⌟ᶜ : (C : CType) → ⌞ ⌜ C ⌝ᶜ ⌟ᶜ ≡ C
  ⌞⌜ A ‼ ε ⌝⌟ᶜ = cong (_‼ ε) ⌞⌜ A ⌝⌟ᵛ

-- and a closed open type is convertible to the embedding of its meaning

mutual

  ⌜⌞_⌟⌝ᵛ : (A : OVType ∅ˢ) → A ≡̂ᵛ ⌜ ⌞ A ⌟ᵛ ⌝ᵛ
  ⌜⌞ tvar () ⌟⌝ᵛ
  ⌜⌞ Base b ⌟⌝ᵛ   = Base≡̂
  ⌜⌞ Unit ⌟⌝ᵛ     = Unit≡̂
  ⌜⌞ Bool ⌟⌝ᵛ     = Bool≡̂
  ⌜⌞ Nat ⌟⌝ᵛ      = Nat≡̂
  ⌜⌞ A |×| B ⌟⌝ᵛ  = ⌜⌞ A ⌟⌝ᵛ |×|≡̂ ⌜⌞ B ⌟⌝ᵛ
  ⌜⌞ A |+| B ⌟⌝ᵛ  = ⌜⌞ A ⌟⌝ᵛ |+|≡̂ ⌜⌞ B ⌟⌝ᵛ
  ⌜⌞ |List| A ⌟⌝ᵛ = |List|≡̂ ⌜⌞ A ⌟⌝ᵛ
  ⌜⌞ Empty ⌟⌝ᵛ    = Empty≡̂
  ⌜⌞ A ⇒ C ⌟⌝ᵛ    = ⌜⌞ A ⌟⌝ᵛ ⇒≡̂ ⌜⌞ C ⌟⌝ᶜ
  ⌜⌞ [ ρ ] A ⌟⌝ᵛ  =
    [ subst (λ c → ρ ≡̂ᵣ rconst c) (sym (⌞⌟-valʳ ρ)) (valʳ-conv ρ) ]≡̂ ⌜⌞ A ⌟⌝ᵛ

  ⌜⌞_⌟⌝ᶜ : (C : OCType ∅ˢ) → C ≡̂ᶜ ⌜ ⌞ C ⌟ᶜ ⌝ᶜ
  ⌜⌞ A ‼ ε ⌟⌝ᶜ = ⌜⌞ A ⌟⌝ᵛ ‼≡̂ subst (λ c → ε ≡̂ₑ econst c) (sym (⌞⌟-valᵉ ε)) (valᵉ-conv ε)

------------------------------------------------------------------------
-- The two kinds of instance

-- A closed instance of the open syntax determines a declarative one,
-- interpreting at which is translating the instance

⌞_⌟ˢ : ∀ {Θ} → Subst Θ ∅ˢ → DInst Θ
⌞ δ ⌟ˢ = δ ⨟ᴰ ∅ᴰ

module _ {Θ} (δ : Subst Θ ∅ˢ) where

  ⌞[]⌟ᵉ : (ε : EExp Θ) → ⌞ ε [ δ ]ᵉ ⌟ᵉ ≡ ⟦ ε ⟧ᵉ ⌞ δ ⌟ˢ
  ⌞[]⌟ᵉ = ⟦[]⟧ᵉ δ ∅ᴰ

  ⌞[]⌟ʳ : (ρ : RExp Θ) → ⌞ ρ [ δ ]ʳ ⌟ʳ ≡ ⟦ ρ ⟧ʳ ⌞ δ ⌟ˢ
  ⌞[]⌟ʳ = ⟦[]⟧ʳ δ ∅ᴰ

  ⌞[]⌟ᵛ : (A : OVType Θ) → ⌞ A [ δ ]ᵛ ⌟ᵛ ≡ ⟦ A ⟧ᵛ ⌞ δ ⌟ˢ
  ⌞[]⌟ᵛ = ⟦[]⟧ᵛ δ ∅ᴰ

  ⌞[]⌟ᶜ : (C : OCType Θ) → ⌞ C [ δ ]ᶜ ⌟ᶜ ≡ ⟦ C ⟧ᶜ ⌞ δ ⌟ˢ
  ⌞[]⌟ᶜ = ⟦[]⟧ᶜ δ ∅ᴰ

  ⌞[]⌟ᶜᵗˣ : ∀ {n} → (Γ : OCtx Θ n) → ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ≡ ⟦ Γ ⟧ᶜᵗˣ ⌞ δ ⌟ˢ
  ⌞[]⌟ᶜᵗˣ = ⟦[]⟧ᶜᵗˣ δ ∅ᴰ

-- Every declarative instance arises so, from the closed instance
-- sending each variable to a constant

⌜_⌝ˢ : ∀ {Θ} → DInst Θ → Subst Θ ∅ˢ
⌜ σ ⌝ˢ = sub (λ α → ⌜ ty σ α ⌝ᵛ) (λ i → rconst (res σ i)) (λ i → econst (eff σ i))

⌞⌜_⌝ˢ⌟ : ∀ {Θ} → (σ : DInst Θ) → ⌞ ⌜ σ ⌝ˢ ⌟ˢ ≗ᴰ σ
⌞⌜ σ ⌝ˢ⌟ = mk≗ᴰ (λ α → ⌞⌜ ty σ α ⌝⌟ᵛ) (λ _ → refl) (λ _ → refl)

------------------------------------------------------------------------
-- Satisfaction: a closed instance satisfies `Q` exactly when the
-- declarative instance it determines does

-- eternality of a closed open type is eternality of its meaning

⌞⌟-⊩ᴱ : (A : OVType ∅ˢ) → Eternal ⌞ A ⌟ᵛ → ∅ᴴ ⊩ᴱ A
⌞⌟-⊩ᴱ (tvar ())
⌞⌟-⊩ᴱ (Base b)   (Baseₑ p)   = Baseₑ p
⌞⌟-⊩ᴱ Unit       Unitₑ       = Unitₑ
⌞⌟-⊩ᴱ Bool       Boolₑ       = Boolₑ
⌞⌟-⊩ᴱ Nat        Natₑ        = Natₑ
⌞⌟-⊩ᴱ (A |×| B)  (p |×|ₑ q)  = ⌞⌟-⊩ᴱ A p |×|ₑ ⌞⌟-⊩ᴱ B q
⌞⌟-⊩ᴱ (A |+| B)  (p |+|ₑ q)  = ⌞⌟-⊩ᴱ A p |+|ₑ ⌞⌟-⊩ᴱ B q
⌞⌟-⊩ᴱ (|List| A) (|List|ₑ p) = |List|ₑ (⌞⌟-⊩ᴱ A p)
⌞⌟-⊩ᴱ Empty      Emptyₑ      = Emptyₑ

-- subtyping between embeddings, with constant grades

⌜⌝-<:ᵛ : ∀ {A B} → A <:ᵛ B → ∅ᴴ ∣ ⌜ A ⌝ᵛ <:̂ᵛ ⌜ B ⌝ᵛ
⌜⌝-<:ᶜ : ∀ {C D} → C <:ᶜ D → ∅ᴴ ∣ ⌜ C ⌝ᶜ <:̂ᶜ ⌜ D ⌝ᶜ

⌜⌝-<:ᵛ (Baseₛ p)   = Baseₛ p
⌜⌝-<:ᵛ Unitₛ       = Unitₛ
⌜⌝-<:ᵛ Boolₛ       = Boolₛ
⌜⌝-<:ᵛ Natₛ        = Natₛ
⌜⌝-<:ᵛ (p |×|ₛ q)  = ⌜⌝-<:ᵛ p |×|ₛ ⌜⌝-<:ᵛ q
⌜⌝-<:ᵛ (p |+|ₛ q)  = ⌜⌝-<:ᵛ p |+|ₛ ⌜⌝-<:ᵛ q
⌜⌝-<:ᵛ (|List|ₛ p) = |List|ₛ (⌜⌝-<:ᵛ p)
⌜⌝-<:ᵛ Emptyₛ      = Emptyₛ
⌜⌝-<:ᵛ (p ⇒ₛ q)    = ⌜⌝-<:ᵛ p ⇒ₛ ⌜⌝-<:ᶜ q
⌜⌝-<:ᵛ ([ p ]ₛ q)  = [ atomᵣ p ]ₛ ⌜⌝-<:ᵛ q

⌜⌝-<:ᶜ (p ‼ₛ q) = ⌜⌝-<:ᵛ p ‼ₛ atomₑ q

-- subtyping between closed open types is subtyping of their meanings

⌞⌟-<:ᵛ : (A B : OVType ∅ˢ) → ⌞ A ⌟ᵛ <:ᵛ ⌞ B ⌟ᵛ → ∅ᴴ ∣ A <:̂ᵛ B
⌞⌟-<:ᵛ A B p =
  <:̂ᵛ-trans (≡̂ᵛ-<:̂ ⌜⌞ A ⌟⌝ᵛ) (<:̂ᵛ-trans (⌜⌝-<:ᵛ p) (≡̂ᵛ-<:̂ (≡̂ᵛ-sym ⌜⌞ B ⌟⌝ᵛ)))

⊨→⊨ᴰ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} → δ ⊨ Q ∣ [] → ⌞ δ ⌟ˢ ⊨ᴰ Q
⊨→⊨ᴰ (h , []ᴬ) = sound-⊩ᴴ h ⊨ᴰ-∅

⊨ᴰ→⊨ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} → ⌞ δ ⌟ˢ ⊨ᴰ Q → δ ⊨ Q ∣ []
⊨ᴰ→⊨ {Θ} {Q} {δ} s = mk⊩ᴴ ets' subᵥ' ordᵣ' ordₑ' disj' , []ᴬ
  where
    eqʳ : (ρ : RExp Θ) → valʳ (ρ [ δ ]ʳ) ≡ ⟦ ρ ⟧ʳ ⌞ δ ⌟ˢ
    eqʳ ρ = trans (sym (⌞⌟-valʳ (ρ [ δ ]ʳ))) (⌞[]⌟ʳ δ ρ)

    eqᵉ : (ε : EExp Θ) → valᵉ (ε [ δ ]ᵉ) ≡ ⟦ ε ⟧ᵉ ⌞ δ ⌟ˢ
    eqᵉ ε = trans (sym (⌞⌟-valᵉ (ε [ δ ]ᵉ))) (⌞[]⌟ᵉ δ ε)

    ets' : ∀ {α} → α ∈ ets Q → ∅ᴴ ⊩ᴱ sTy δ α
    ets' {α} m = ⌞⌟-⊩ᴱ (sTy δ α) (⊨ets s m)

    subᵥ' : ∀ {α β} → (α , β) ∈ subᵥ Q → ∅ᴴ ∣ sTy δ α <:̂ᵛ sTy δ β
    subᵥ' {α} {β} m = ⌞⌟-<:ᵛ (sTy δ α) (sTy δ β) (⊨subᵥ s m)

    ordᵣ' : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → ∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    ordᵣ' {ρ} {ρ'} m = val-≾ᵣ⁻ (subst₂ _≾ᵣ_ (sym (eqʳ ρ)) (sym (eqʳ ρ')) (⊨ordᵣ s m))

    ordₑ' : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → ∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
    ordₑ' {ε} {ε'} m = val-≾ₑ⁻ (subst₂ _≾ₑ_ (sym (eqᵉ ε)) (sym (eqᵉ ε')) (⊨ordₑ s m))

    disj' : ∀ {A ρ} → (A , ρ) ∈ disj Q → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ)
    disj' {A} {ρ} m with ⊨disj s m
    ... | inj₁ et = et-ok (⌞⌟-⊩ᴱ (A [ δ ]ᵛ) (subst Eternal (sym (⌞[]⌟ᵛ δ A)) et))
    ... | inj₂ le = ≾ᵘ-ok (val-≾ᵣ⁻ (subst (_≾ᵣ uᵣ) (sym (eqʳ ρ)) le))

⊨⇔⊨ᴰ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} → δ ⊨ Q ∣ [] ⇔ ⌞ δ ⌟ˢ ⊨ᴰ Q
⊨⇔⊨ᴰ = mk⇔ ⊨→⊨ᴰ ⊨ᴰ→⊨

-- so every declarative instance satisfying `Q` arises from a closed one

⌜⌝ˢ-⊨ : ∀ {Θ} {Q : Hyps Θ} {σ : DInst Θ} → σ ⊨ᴰ Q → ⌜ σ ⌝ˢ ⊨ Q ∣ []
⌜⌝ˢ-⊨ {σ = σ} s = ⊨ᴰ→⊨ (⊨ᴰ-≗ (≗ᴰ-sym ⌞⌜ σ ⌝ˢ⌟) s)
  where
    ≗ᴰ-sym : ∀ {Θ} {σ σ' : DInst Θ} → σ ≗ᴰ σ' → σ' ≗ᴰ σ
    ≗ᴰ-sym p = mk≗ᴰ (λ α → sym (ty≗ p α)) (λ i → sym (res≗ p i)) (λ i → sym (eff≗ p i))

------------------------------------------------------------------------
-- Obligations: one held in the open syntax, its rigids kept as
-- variables, holds declaratively at every grade for them

private

  ≗ᴰ-,ᵉ : ∀ {Θ} {σ σ' : DInst Θ} → σ ≗ᴰ σ' → (c : E) → (σ ,ᵉᴰ c) ≗ᴰ (σ' ,ᵉᴰ c)
  ≗ᴰ-,ᵉ p c = mk≗ᴰ (ty≗ p) (res≗ p) (λ { zero → refl ; (suc i) → eff≗ p i })

  ⊨ᴰ⟨⟩-≗ : ∀ {Θ} {σ σ' : DInst Θ} → (k : ℕ) → {B : Ords (Θ +eⁿ k)}
         → σ ≗ᴰ σ' → σ ⊨ᴰ⟨ k ⟩ B → σ' ⊨ᴰ⟨ k ⟩ B
  ⊨ᴰ⟨⟩-≗ zero    p s = ⊨ᴰᵒ-≗ p s
  ⊨ᴰ⟨⟩-≗ (suc k) p s = λ c → ⊨ᴰ⟨⟩-≗ k (≗ᴰ-,ᵉ p c) (s c)

  ↑ᵉ-⨟ᴰ : ∀ {Θ Θ'} → (δ : Subst Θ Θ') → (τ : DInst Θ') → (c : E)
        → ((δ ↑ᵉ) ⨟ᴰ (τ ,ᵉᴰ c)) ≗ᴰ ((δ ⨟ᴰ τ) ,ᵉᴰ c)
  ↑ᵉ-⨟ᴰ δ τ c = mk≗ᴰ (λ α → ⟦wkᵉ⟧ᵛ τ c (sTy δ α)) (λ i → ⟦wkᵉ⟧ʳ τ c (sR δ i))
                     (λ { zero → refl ; (suc i) → ⟦wkᵉ⟧ᵉ τ c (sE δ i) })

  sound-⊩ᴼ : ∀ {Θ Θ'} {Q' : Hyps Θ'} {δ : Subst Θ Θ'} {τ : DInst Θ'}
           → (k : ℕ) → {B : Ords (Θ +eⁿ k)}
           → wkᵉⁿ-H k Q' ⊩ᵒ B [ δ ↑ᵉⁿ k ] → τ ⊨ᴰ Q' → (δ ⨟ᴰ τ) ⊨ᴰ⟨ k ⟩ B
  sound-⊩ᴼ zero    h s = sound-⊩ᵒ h s
  sound-⊩ᴼ {δ = δ} {τ} (suc k) h s c =
    ⊨ᴰ⟨⟩-≗ k (↑ᵉ-⨟ᴰ δ τ c) (sound-⊩ᴼ {δ = δ ↑ᵉ} {τ ,ᵉᴰ c} k h (⊨ᴰ-,ᵉ c s))

⊩ᴼˢ→⊨ᴰᴿ : ∀ {Θ} {R : Obligs Θ} {δ : Subst Θ ∅ˢ} → ∅ᴴ ⊩ᴼˢ R [ δ ] → ⌞ δ ⌟ˢ ⊨ᴰᴿ R
⊩ᴼˢ→⊨ᴰᴿ []ᴬ                    = []ᴬ
⊩ᴼˢ→⊨ᴰᴿ {R = O ∷ˡ R} (h ∷ᴬ hs) = sound-⊩ᴼ (rigids O) h ⊨ᴰ-∅ ∷ᴬ ⊩ᴼˢ→⊨ᴰᴿ hs
