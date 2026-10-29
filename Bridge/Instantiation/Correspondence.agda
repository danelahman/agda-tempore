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
-- (`⌞⌜_⌝⌟ᵛ`), and a closed open type with no handler type is   --
-- convertible to the embedding of its meaning (`⌜⌞_⌟⌝ᵛ`).      --
--                                                              --
-- A closed instance `δ` determines the declarative instance    --
-- `⌞ δ ⌟ˢ`, with `⌞ A [ δ ]ᵛ ⌟ᵛ ≡ ⟦ A ⟧ᵛ ⌞ δ ⌟ˢ` for grades,   --
-- types, computation types and contexts (`⌞[]⌟ᵛ` and the       --
-- like), and, when no handler type is among its types,         --
-- `δ ⊨ Q` exactly when `⌞ δ ⌟ˢ ⊨ᴰ Q` (`⊨⇔⊨ᴰ`).                --
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
open import Data.Vec.Base using (Vec) renaming (map to mapᵛ)
open import Data.Unit using (tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module Bridge.Instantiation.Correspondence (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Language.Types                  S
open import ClosedCalculus.Syntax.Contexts  S
open import ClosedCalculus.Syntax.Subtyping S

open import OpenCalculus.Syntax.Grades        S
open import OpenCalculus.Syntax.Types         S
open import OpenCalculus.Syntax.Contexts      S
open import OpenCalculus.Syntax.Subst         S
open import OpenCalculus.Hypotheses           S
open import OpenCalculus.Hypotheses.Instances S

open import Bridge.Instantiation.Types      S
open import Bridge.Instantiation.Judgements S

------------------------------------------------------------------------
-- Pointwise equal instances interpret alike and satisfy alike

module _ {Θ} {σ σ' : DInst Θ} (p : σ ≗ᴰ σ') where

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
    ⟦≗⟧ᵛ (C ⇛ D)    = refl
    ⟦≗⟧ᵛ ([ ρ ] A)  = cong₂ [_]_ (⟦≗⟧ʳ p ρ) (⟦≗⟧ᵛ A)

    ⟦≗⟧ᶜ : (C : OCType Θ) → ⟦ C ⟧ᶜ σ ≡ ⟦ C ⟧ᶜ σ'
    ⟦≗⟧ᶜ (A ‼ ε) = cong₂ _‼_ (⟦≗⟧ᵛ A) (⟦≗⟧ᵉ p ε)

  ⟦≗⟧ᶜᵗˣ : ∀ {n} → (Γ : OCtx Θ n) → ⟦ Γ ⟧ᶜᵗˣ σ ≡ ⟦ Γ ⟧ᶜᵗˣ σ'
  ⟦≗⟧ᶜᵗˣ []        = refl
  ⟦≗⟧ᶜᵗˣ (Γ ∷ A)   = cong₂ _∷_ (⟦≗⟧ᶜᵗˣ Γ) (⟦≗⟧ᵛ A)
  ⟦≗⟧ᶜᵗˣ (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (⟦≗⟧ᶜᵗˣ Γ) (⟦≗⟧ʳ p ρ)

  ⊨ᴰ-≗ : {Q : Hyps Θ} → σ ⊨ᴰ Q → σ' ⊨ᴰ Q
  ⊨ᴰ-≗ s = mk⊨ᴰ
    (λ m → subst Eternal (ty≗ p _) (⊨ets s m))
    (λ m → subst₂ _<:ᵛ_ (ty≗ p _) (ty≗ p _) (⊨subᵥ s m))
    (λ {ρ} {ρ'} m → subst₂ _≾ᵣ_ (⟦≗⟧ʳ p ρ) (⟦≗⟧ʳ p ρ') (⊨ordᵣ s m))
    (λ {ε} {ε'} m → subst₂ _≾ₑ_ (⟦≗⟧ᵉ p ε) (⟦≗⟧ᵉ p ε') (⊨ordₑ s m))
    (λ {A} {ρ} m → subst₂ (λ X r → Eternal X ⊎ (r ≾ᵣ uᵣ)) (⟦≗⟧ᵛ A) (⟦≗⟧ʳ p ρ) (⊨disj s m))
    (λ {O} m → ⊨ᴰ⟨⟩-≗ (rigids O) p (⊨qhyps s m))

------------------------------------------------------------------------
-- Substitution: interpreting `X [ δ ]` at `σ` is interpreting `X` at
-- the composite `δ ⨟ᴰ σ`

module _ {Θ Θ'} (δ : Subst Θ Θ') (σ : DInst Θ') where

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
    ⟦[]⟧ᵛ (C ⇛ D)    = refl
    ⟦[]⟧ᵛ ([ ρ ] A)  = cong₂ [_]_ (⟦[]⟧ʳ δ σ ρ) (⟦[]⟧ᵛ A)

    ⟦[]⟧ᶜ : (C : OCType Θ) → ⟦ C [ δ ]ᶜ ⟧ᶜ σ ≡ ⟦ C ⟧ᶜ (δ ⨟ᴰ σ)
    ⟦[]⟧ᶜ (A ‼ ε) = cong₂ _‼_ (⟦[]⟧ᵛ A) (⟦[]⟧ᵉ δ σ ε)

  ⟦[]⟧ᶜᵗˣ : ∀ {n} → (Γ : OCtx Θ n) → ⟦ Γ [ δ ]ᶜᵗˣ ⟧ᶜᵗˣ σ ≡ ⟦ Γ ⟧ᶜᵗˣ (δ ⨟ᴰ σ)
  ⟦[]⟧ᶜᵗˣ []        = refl
  ⟦[]⟧ᶜᵗˣ (Γ ∷ A)   = cong₂ _∷_ (⟦[]⟧ᶜᵗˣ Γ) (⟦[]⟧ᵛ A)
  ⟦[]⟧ᶜᵗˣ (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (⟦[]⟧ᶜᵗˣ Γ) (⟦[]⟧ʳ δ σ ρ)

-- Pointwise equality is an equivalence, kept by extension and by
-- composition; composition with a substitution is associative

⨟ᴰ-≗ : ∀ {Θ Θ'} → (δ : Subst Θ Θ') → {σ σ' : DInst Θ'} → σ ≗ᴰ σ' → (δ ⨟ᴰ σ) ≗ᴰ (δ ⨟ᴰ σ')
⨟ᴰ-≗ δ p = mk≗ᴰ (λ α → ⟦≗⟧ᵛ p (sTy δ α)) (λ i → ⟦≗⟧ʳ p (sR δ i)) (λ i → ⟦≗⟧ᵉ p (sE δ i))

⨟ˢ-⨟ᴰ : ∀ {Θ Θ' Θ''} → (δ : Subst Θ Θ') → (δ' : Subst Θ' Θ'') → (σ : DInst Θ'')
       → ((δ ⨟ˢ δ') ⨟ᴰ σ) ≗ᴰ (δ ⨟ᴰ (δ' ⨟ᴰ σ))
⨟ˢ-⨟ᴰ δ δ' σ = mk≗ᴰ (λ α → ⟦[]⟧ᵛ δ' σ (sTy δ α)) (λ i → ⟦[]⟧ʳ δ' σ (sR δ i))
                     (λ i → ⟦[]⟧ᵉ δ' σ (sE δ i))

-- Entailment along a substitution: an instance of the entailing set,
-- composed with the substitution, is an instance of the entailed one,
-- a quantified ordering entailed at fresh rigids holding at every grade
-- for them

sound-⊩ᵒ : ∀ {Θ Θ'} {o : Ords Θ} {Q' : Hyps Θ'} {δ : Subst Θ Θ'} {σ : DInst Θ'}
         → Q' ⊩ᵒ o [ δ ] → σ ⊨ᴰ Q' → (δ ⨟ᴰ σ) ⊨ᴰᵒ o
sound-⊩ᵒ {δ = δ} {σ} h s = mk⊨ᴰᵒ
  (λ {ρ} {ρ'} m → subst₂ _≾ᵣ_ (⟦[]⟧ʳ δ σ ρ) (⟦[]⟧ʳ δ σ ρ') (sound-≾ᵣ s (⊩ors h m)))
  (λ {ε} {ε'} m → subst₂ _≾ₑ_ (⟦[]⟧ᵉ δ σ ε) (⟦[]⟧ᵉ δ σ ε') (sound-≾ₑ s (⊩oes h m)))

sound-⊩ᴼ : ∀ {Θ Θ'} {Q' : Hyps Θ'} {δ : Subst Θ Θ'} {τ : DInst Θ'}
         → (k : ℕ) → {B : Ords (Θ +eⁿ k)}
         → wkᵉⁿ-H k Q' ⊩ᵒ B [ δ ↑ᵉⁿ k ] → τ ⊨ᴰ Q' → (δ ⨟ᴰ τ) ⊨ᴰ⟨ k ⟩ B
sound-⊩ᴼ zero    h s = sound-⊩ᵒ h s
sound-⊩ᴼ {δ = δ} {τ} (suc k) h s c =
  ⊨ᴰ⟨⟩-≗ k (↑ᵉ-⨟ᴰ δ τ c) (sound-⊩ᴼ {δ = δ ↑ᵉ} {τ ,ᵉᴰ c} k h (⊨ᴰ-,ᵉ c s))


sound-⊩ᴴ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {δ : Subst Θ Θ'} {σ : DInst Θ'}
         → Q' ⊩ᴴ Q [ δ ] → σ ⊨ᴰ Q' → (δ ⨟ᴰ σ) ⊨ᴰ Q
sound-⊩ᴴ {δ = δ} {σ} h s = mk⊨ᴰ
  (λ m → sound-⊩ᴱ s (⊩ets h m))
  (λ m → sound-<:ᵛ s (⊩subᵥ h m))
  (λ {ρ} {ρ'} m → subst₂ _≾ᵣ_ (⟦[]⟧ʳ δ σ ρ) (⟦[]⟧ʳ δ σ ρ') (sound-≾ᵣ s (⊩ordᵣ h m)))
  (λ {ε} {ε'} m → subst₂ _≾ₑ_ (⟦[]⟧ᵉ δ σ ε) (⟦[]⟧ᵉ δ σ ε') (sound-≾ₑ s (⊩ordₑ h m)))
  (λ {A} {ρ} m → subst₂ (λ X r → Eternal X ⊎ (r ≾ᵣ uᵣ)) (⟦[]⟧ᵛ δ σ A) (⟦[]⟧ʳ δ σ ρ)
                        (sound-VarOK s (⊩disj h m)))
  (λ {O} m → sound-⊩ᴼ (rigids O) (⊩qhyps h m) s)

------------------------------------------------------------------------
-- Closed open syntax: the interpretation at the empty instance

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
⌞⌟-valᵉ = ⟦⟧∅-valᵉ

⌞⌟-valʳ : (ρ : RExp ∅ˢ) → ⌞ ρ ⌟ʳ ≡ valʳ ρ
⌞⌟-valʳ = ⟦⟧∅-valʳ

-- Every closed type arises: the embedding, each grade a constant, is a
-- section of `⌞_⌟`, and has no handler type

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

mutual

  ⌜⌝-noHandlerᵛ : (A : VType) → NoHandlerTypeᵛ ⌜ A ⌝ᵛ
  ⌜⌝-noHandlerᵛ (Base b)   = tt
  ⌜⌝-noHandlerᵛ Unit       = tt
  ⌜⌝-noHandlerᵛ Bool       = tt
  ⌜⌝-noHandlerᵛ Nat        = tt
  ⌜⌝-noHandlerᵛ (A |×| B)  = ⌜⌝-noHandlerᵛ A , ⌜⌝-noHandlerᵛ B
  ⌜⌝-noHandlerᵛ (A |+| B)  = ⌜⌝-noHandlerᵛ A , ⌜⌝-noHandlerᵛ B
  ⌜⌝-noHandlerᵛ (|List| A) = ⌜⌝-noHandlerᵛ A
  ⌜⌝-noHandlerᵛ Empty      = tt
  ⌜⌝-noHandlerᵛ (A ⇒ C)    = ⌜⌝-noHandlerᵛ A , ⌜⌝-noHandlerᶜ C
  ⌜⌝-noHandlerᵛ ([ ρ ] A)  = ⌜⌝-noHandlerᵛ A

  ⌜⌝-noHandlerᶜ : (C : CType) → NoHandlerTypeᶜ ⌜ C ⌝ᶜ
  ⌜⌝-noHandlerᶜ (A ‼ ε) = ⌜⌝-noHandlerᵛ A

-- and a closed open type with no handler type is convertible to the
-- embedding of its meaning

mutual

  ⌜⌞_⌟⌝ᵛ : (A : OVType ∅ˢ) → NoHandlerTypeᵛ A → A ≡̂ᵛ ⌜ ⌞ A ⌟ᵛ ⌝ᵛ
  ⌜⌞ tvar () ⌟⌝ᵛ
  ⌜⌞ Base b ⌟⌝ᵛ   h       = Base≡̂
  ⌜⌞ Unit ⌟⌝ᵛ     h       = Unit≡̂
  ⌜⌞ Bool ⌟⌝ᵛ     h       = Bool≡̂
  ⌜⌞ Nat ⌟⌝ᵛ      h       = Nat≡̂
  ⌜⌞ A |×| B ⌟⌝ᵛ  (h , k) = ⌜⌞ A ⌟⌝ᵛ h |×|≡̂ ⌜⌞ B ⌟⌝ᵛ k
  ⌜⌞ A |+| B ⌟⌝ᵛ  (h , k) = ⌜⌞ A ⌟⌝ᵛ h |+|≡̂ ⌜⌞ B ⌟⌝ᵛ k
  ⌜⌞ |List| A ⌟⌝ᵛ h       = |List|≡̂ (⌜⌞ A ⌟⌝ᵛ h)
  ⌜⌞ Empty ⌟⌝ᵛ    h       = Empty≡̂
  ⌜⌞ A ⇒ C ⌟⌝ᵛ    (h , k) = ⌜⌞ A ⌟⌝ᵛ h ⇒≡̂ ⌜⌞ C ⌟⌝ᶜ k
  ⌜⌞ [ ρ ] A ⌟⌝ᵛ  h       =
    [ subst (λ c → ρ ≡̂ᵣ rconst c) (sym (⌞⌟-valʳ ρ)) (valʳ-conv ρ) ]≡̂ ⌜⌞ A ⌟⌝ᵛ h

  ⌜⌞_⌟⌝ᶜ : (C : OCType ∅ˢ) → NoHandlerTypeᶜ C → C ≡̂ᶜ ⌜ ⌞ C ⌟ᶜ ⌝ᶜ
  ⌜⌞ A ‼ ε ⌟⌝ᶜ h =
    ⌜⌞ A ⌟⌝ᵛ h ‼≡̂ subst (λ c → ε ≡̂ₑ econst c) (sym (⌞⌟-valᵉ ε)) (valᵉ-conv ε)

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

-- subtyping between closed open types with no handler type is
-- subtyping of their meanings

⌞⌟-<:ᵛ : (A B : OVType ∅ˢ) → NoHandlerTypeᵛ A → NoHandlerTypeᵛ B
       → ⌞ A ⌟ᵛ <:ᵛ ⌞ B ⌟ᵛ → ∅ᴴ ∣ A <:̂ᵛ B
⌞⌟-<:ᵛ A B h k p =
  <:̂ᵛ-trans (≡̂ᵛ-<:̂ (⌜⌞ A ⌟⌝ᵛ h)) (<:̂ᵛ-trans (⌜⌝-<:ᵛ p) (≡̂ᵛ-<:̂ (≡̂ᵛ-sym (⌜⌞ B ⌟⌝ᵛ k))))

-- A substitution whose types have no handler type keeps a type, and a
-- context, without one

module _ {Θ Θ'} (δ : Subst Θ Θ') (hδ : ∀ α → NoHandlerTypeᵛ (sTy δ α)) where

  mutual

    noHandler-[]ᵛ : (A : OVType Θ) → NoHandlerTypeᵛ A → NoHandlerTypeᵛ (A [ δ ]ᵛ)
    noHandler-[]ᵛ (tvar α)   h       = hδ α
    noHandler-[]ᵛ (Base b)   h       = tt
    noHandler-[]ᵛ Unit       h       = tt
    noHandler-[]ᵛ Bool       h       = tt
    noHandler-[]ᵛ Nat        h       = tt
    noHandler-[]ᵛ (A |×| B)  (h , k) = noHandler-[]ᵛ A h , noHandler-[]ᵛ B k
    noHandler-[]ᵛ (A |+| B)  (h , k) = noHandler-[]ᵛ A h , noHandler-[]ᵛ B k
    noHandler-[]ᵛ (|List| A) h       = noHandler-[]ᵛ A h
    noHandler-[]ᵛ Empty      h       = tt
    noHandler-[]ᵛ (A ⇒ C)    (h , k) = noHandler-[]ᵛ A h , noHandler-[]ᶜ C k
    noHandler-[]ᵛ ([ ρ ] A)  h       = noHandler-[]ᵛ A h

    noHandler-[]ᶜ : (C : OCType Θ) → NoHandlerTypeᶜ C → NoHandlerTypeᶜ (C [ δ ]ᶜ)
    noHandler-[]ᶜ (A ‼ ε) h = noHandler-[]ᵛ A h

  noHandler-[]ᶜᵗˣ : ∀ {n} → (Γ : OCtx Θ n) → NoHandlerTypeᶜᵗˣ Γ
                  → NoHandlerTypeᶜᵗˣ (Γ [ δ ]ᶜᵗˣ)
  noHandler-[]ᶜᵗˣ []        h       = tt
  noHandler-[]ᶜᵗˣ (Γ ∷ A)   (h , k) = noHandler-[]ᶜᵗˣ Γ h , noHandler-[]ᵛ A k
  noHandler-[]ᶜᵗˣ (Γ ⟨ ρ ⟩) h       = noHandler-[]ᶜᵗˣ Γ h

-- A closed instance whose types have no handler type

NoHandlerTypeˢ : ∀ {Θ} → Subst Θ ∅ˢ → Set
NoHandlerTypeˢ δ = ∀ α → NoHandlerTypeᵛ (sTy δ α)

⊨→⊨ᴰ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} → δ ⊨ Q → ⌞ δ ⌟ˢ ⊨ᴰ Q
⊨→⊨ᴰ h = sound-⊩ᴴ (⊨⇒⊩ᴴ h) ⊨ᴰ-∅

-- a declaratively satisfying instance satisfies, a quantified
-- hypothesis at each closed instance of its rigids, their values

⊨ᴰ→⊨ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} → NoHandlerTypeˢ δ → ⌞ δ ⌟ˢ ⊨ᴰ Q → δ ⊨ Q
⊨ᴰ→⊨ {Θ} {Q} {δ} h s = mk⊩ᴵ ets' subᵥ' ordᵣ' ordₑ' disj' qhyps'
  where
    eqʳ : (ρ : RExp Θ) → valʳ (ρ [ δ ]ʳ) ≡ ⟦ ρ ⟧ʳ ⌞ δ ⌟ˢ
    eqʳ ρ = trans (sym (⌞⌟-valʳ (ρ [ δ ]ʳ))) (⌞[]⌟ʳ δ ρ)

    eqᵉ : (ε : EExp Θ) → valᵉ (ε [ δ ]ᵉ) ≡ ⟦ ε ⟧ᵉ ⌞ δ ⌟ˢ
    eqᵉ ε = trans (sym (⌞⌟-valᵉ (ε [ δ ]ᵉ))) (⌞[]⌟ᵉ δ ε)

    ets' : ∀ {α} → α ∈ ets Q → ∅ᴴ ⊩ᴱ sTy δ α
    ets' {α} m = ∅⇒⊩ᴱ (⌞⌟-⊩ᴱ (sTy δ α) (⊨ets s m))

    subᵥ' : ∀ {α β} → (α , β) ∈ subᵥ Q → ∅ᴴ ∣ sTy δ α <:̂ᵛ sTy δ β
    subᵥ' {α} {β} m = ∅⇒<:̂ᵛ (⌞⌟-<:ᵛ (sTy δ α) (sTy δ β) (h α) (h β) (⊨subᵥ s m))

    ordᵣ' : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → ∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    ordᵣ' {ρ} {ρ'} m = val-≾ᵣ⁻ (subst₂ _≾ᵣ_ (sym (eqʳ ρ)) (sym (eqʳ ρ')) (⊨ordᵣ s m))

    ordₑ' : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → ∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
    ordₑ' {ε} {ε'} m = val-≾ₑ⁻ (subst₂ _≾ₑ_ (sym (eqᵉ ε)) (sym (eqᵉ ε')) (⊨ordₑ s m))

    disj' : ∀ {A ρ} → (A , ρ) ∈ disj Q → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ)
    disj' {A} {ρ} m with ⊨disj s m
    ... | inj₁ et = et-ok (∅⇒⊩ᴱ (⌞⌟-⊩ᴱ (A [ δ ]ᵛ) (subst Eternal (sym (⌞[]⌟ᵛ δ A)) et)))
    ... | inj₂ le = ≾ᵘ-ok (val-≾ᵣ⁻ (subst (_≾ᵣ uᵣ) (sym (eqʳ ρ)) le))

    qhyps' : ∀ {O} → O ∈ qhyps Q → (es : Vec (EExp ∅ˢ) (rigids O)) → ∅ᴴ ⊩ᵒ body O [ δ ,ᵉⁿ es ]
    qhyps' {O} m es = mk⊩ᵒ r e
      where
        cs = mapᵛ (λ x → ⟦ x ⟧ᵉ ∅ᴰ) es
        d  = ⊨ᴰ⟨⟩-at (⊨qhyps s m) cs

        valeqʳ : (x : RExp (Θ +eⁿ rigids O)) → valʳ (x [ δ ,ᵉⁿ es ]ʳ) ≡ ⟦ x ⟧ʳ (⌞ δ ⌟ˢ ,ᵉᴰⁿ cs)
        valeqʳ x = trans (sym (⌞⌟-valʳ (x [ δ ,ᵉⁿ es ]ʳ)))
                         (trans (⟦[]⟧ʳ (δ ,ᵉⁿ es) ∅ᴰ x) (⟦≗⟧ʳ (,ᵉⁿ-⨟ᴰ δ es ∅ᴰ) x))

        valeqᵉ : (x : EExp (Θ +eⁿ rigids O)) → valᵉ (x [ δ ,ᵉⁿ es ]ᵉ) ≡ ⟦ x ⟧ᵉ (⌞ δ ⌟ˢ ,ᵉᴰⁿ cs)
        valeqᵉ x = trans (sym (⌞⌟-valᵉ (x [ δ ,ᵉⁿ es ]ᵉ)))
                         (trans (⟦[]⟧ᵉ (δ ,ᵉⁿ es) ∅ᴰ x) (⟦≗⟧ᵉ (,ᵉⁿ-⨟ᴰ δ es ∅ᴰ) x))

        r : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors (body O) → ∅ᴴ ⊩ ρ [ δ ,ᵉⁿ es ]ʳ ≾̂ᵣ ρ' [ δ ,ᵉⁿ es ]ʳ
        r {ρ} {ρ'} mφ = val-≾ᵣ⁻ (subst₂ _≾ᵣ_ (sym (valeqʳ ρ)) (sym (valeqʳ ρ')) (⊨ors d mφ))

        e : ∀ {ε ε'} → (ε , ε') ∈ oes (body O) → ∅ᴴ ⊩ ε [ δ ,ᵉⁿ es ]ᵉ ≾̂ₑ ε' [ δ ,ᵉⁿ es ]ᵉ
        e {ε} {ε'} mφ = val-≾ₑ⁻ (subst₂ _≾ₑ_ (sym (valeqᵉ ε)) (sym (valeqᵉ ε')) (⊨oes d mφ))

⊨⇔⊨ᴰ : ∀ {Θ} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} → NoHandlerTypeˢ δ
      → δ ⊨ Q ⇔ ⌞ δ ⌟ˢ ⊨ᴰ Q
⊨⇔⊨ᴰ h = mk⇔ ⊨→⊨ᴰ (⊨ᴰ→⊨ h)

-- so every declarative instance satisfying `Q` arises from a closed one

⌜⌝ˢ-⊨ : ∀ {Θ} {Q : Hyps Θ} {σ : DInst Θ} → σ ⊨ᴰ Q → ⌜ σ ⌝ˢ ⊨ Q
⌜⌝ˢ-⊨ {σ = σ} s = ⊨ᴰ→⊨ (λ α → ⌜⌝-noHandlerᵛ (ty σ α)) (⊨ᴰ-≗ (≗ᴰ-sym ⌞⌜ σ ⌝ˢ⌟) s)
