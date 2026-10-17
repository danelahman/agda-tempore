------------------------------------------------------------------
-- The side judgements of the open calculus at a closed         --
-- instance, as judgements of the closed calculus               --
--                                                              --
-- Eternality and subtyping from no hypotheses translate        --
-- structurally, entailed orderings by value. At an instance    --
-- `δ` satisfying `Q`, a membership is the membership of the    --
-- translated type at the value of its grade, and the var-rule  --
-- disjunction gives the closed rule's side condition. A        --
-- handler clause is typed under `wkᵉ-H Q`, which every         --
-- extension `δ ,ᵉ c` of such an instance satisfies.            --
------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Fin using (toℕ)
open import Data.Nat using (suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.Product using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module Bridge.Judgements (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types     S
open import Syntax.Contexts  S
open import Syntax.Subtyping S
import Syntax.Erasure S as CE

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S

open import Bridge.Types S

-- Eternality

et⌞_⌟ : {A : OVType ∅ˢ} → ∅ᴴ ⊩ᴱ A → Eternal ⌞ A ⌟ᵛ
et⌞ et-hyp () ⌟
et⌞ et-subˡ {α = ()} _ _ ⌟
et⌞ et-subʳ {β = ()} _ _ ⌟
et⌞ Baseₑ p ⌟     = Baseₑ p
et⌞ Unitₑ ⌟       = Unitₑ
et⌞ Boolₑ ⌟       = Boolₑ
et⌞ Natₑ ⌟        = Natₑ
et⌞ p |×|ₑ q ⌟    = et⌞ p ⌟ |×|ₑ et⌞ q ⌟
et⌞ p |+|ₑ q ⌟    = et⌞ p ⌟ |+|ₑ et⌞ q ⌟
et⌞ |List|ₑ p ⌟   = |List|ₑ et⌞ p ⌟
et⌞ Emptyₑ ⌟      = Emptyₑ

-- Subtyping

mutual

  sub⌞_⌟ᵛ : {A B : OVType ∅ˢ} → ∅ᴴ ∣ A <:̂ᵛ B → ⌞ A ⌟ᵛ <:ᵛ ⌞ B ⌟ᵛ
  sub⌞ tvarₛ {α = ()} _ ⌟ᵛ
  sub⌞ Baseₛ p ⌟ᵛ    = Baseₛ p
  sub⌞ Unitₛ ⌟ᵛ      = Unitₛ
  sub⌞ Boolₛ ⌟ᵛ      = Boolₛ
  sub⌞ Natₛ ⌟ᵛ       = Natₛ
  sub⌞ p |×|ₛ q ⌟ᵛ   = sub⌞ p ⌟ᵛ |×|ₛ sub⌞ q ⌟ᵛ
  sub⌞ p |+|ₛ q ⌟ᵛ   = sub⌞ p ⌟ᵛ |+|ₛ sub⌞ q ⌟ᵛ
  sub⌞ |List|ₛ p ⌟ᵛ  = |List|ₛ sub⌞ p ⌟ᵛ
  sub⌞ Emptyₛ ⌟ᵛ     = Emptyₛ
  sub⌞ p ⇒ₛ q ⌟ᵛ     = sub⌞ p ⌟ᵛ ⇒ₛ sub⌞ q ⌟ᶜ
  sub⌞ [ p ]ₛ q ⌟ᵛ   = [ val-≾ᵣ p ]ₛ sub⌞ q ⌟ᵛ

  sub⌞_⌟ᶜ : {C D : OCType ∅ˢ} → ∅ᴴ ∣ C <:̂ᶜ D → ⌞ C ⌟ᶜ <:ᶜ ⌞ D ⌟ᶜ
  sub⌞ p ‼ₛ q ⌟ᶜ = sub⌞ p ⌟ᵛ ‼ₛ val-≾ₑ q

-- At an instance satisfying the hypotheses

module _ {Θ : Scope} {Q : Hyps Θ} {δ : Subst Θ ∅ˢ} (h : ∅ᴴ ⊩ᴴ Q [ δ ]) where

  inst-⊩ᴱ : {A : OVType Θ} → Q ⊩ᴱ A → Eternal ⌞ A [ δ ]ᵛ ⌟ᵛ
  inst-⊩ᴱ et = et⌞ ⊩ᴱ-subst h et ⌟

  inst-<:ᵛ : {A B : OVType Θ} → Q ∣ A <:̂ᵛ B → ⌞ A [ δ ]ᵛ ⌟ᵛ <:ᵛ ⌞ B [ δ ]ᵛ ⌟ᵛ
  inst-<:ᵛ p = sub⌞ <:̂ᵛ-subst h p ⌟ᵛ

  inst-<:ᶜ : {C D : OCType Θ} → Q ∣ C <:̂ᶜ D → ⌞ C [ δ ]ᶜ ⌟ᶜ <:ᶜ ⌞ D [ δ ]ᶜ ⌟ᶜ
  inst-<:ᶜ p = sub⌞ <:̂ᶜ-subst h p ⌟ᶜ

  -- the var-rule disjunction as the closed rule's side condition

  inst-VarOK⌞⌟ : {A : OVType Θ} {ρ : RExp Θ} → VarOK Q A ρ
               → ¬ Eternal ⌞ A [ δ ]ᵛ ⌟ᵛ → valʳ (ρ [ δ ]ʳ) ≾ᵣ uᵣ
  inst-VarOK⌞⌟ ok ¬et with inst-VarOK h ok
  ... | inj₁ et = ⊥-elim (¬et et⌞ et ⌟)
  ... | inj₂ le = le

-- Memberships

var⌞_⌟ : ∀ {Θ n} {Γ : OCtx Θ n} {A : OVType Θ} {ρ : RExp Θ} {δ : Subst Θ ∅ˢ}
       → A ∈̂[ ρ ] Γ → ⌞ A [ δ ]ᵛ ⌟ᵛ ∈[ valʳ (ρ [ δ ]ʳ) ] ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ
var⌞ Hd ⌟       = Hd
var⌞ Tl-∷ x ⌟   = Tl-∷ var⌞ x ⌟
var⌞ Tl-⟨⟩ x ⌟  = Tl-⟨⟩ var⌞ x ⌟

-- and they point at the same position

var⌞⌟-pos : ∀ {Θ n} {Γ : OCtx Θ n} {A : OVType Θ} {ρ : RExp Θ} {δ : Subst Θ ∅ˢ}
          → (x : A ∈̂[ ρ ] Γ) → CE.var-pos (var⌞_⌟ {δ = δ} x) ≡ toℕ (var-pos x)
var⌞⌟-pos Hd        = refl
var⌞⌟-pos (Tl-∷ x)  = cong suc (var⌞⌟-pos x)
var⌞⌟-pos (Tl-⟨⟩ x) = var⌞⌟-pos x

-- Every extension of an instance satisfying `Q` satisfies `wkᵉ-H Q`

⊩ᴴ-,ᵉ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {σ : Subst Θ Θ'}
      → (c : EExp Θ') → Q' ⊩ᴴ Q [ σ ] → Q' ⊩ᴴ wkᵉ-H Q [ σ ,ᵉ c ]
⊩ᴴ-,ᵉ {Θ} {Q = Q} {Q'} {σ} c h = mk⊩ᴴ ets' subᵥ' ordᵣ' ordₑ' disj'
  where
    ets' : ∀ {α} → α ∈ ets (wkᵉ-H Q) → Q' ⊩ᴱ sTy (σ ,ᵉ c) α
    ets' m with ∈-map⁻ (wkᵉ-tv Θ) m
    ... | _ , m₀ , refl = ⊩ets h m₀

    subᵥ' : ∀ {α β} → (α , β) ∈ subᵥ (wkᵉ-H Q)
          → Q' ∣ sTy (σ ,ᵉ c) α <:̂ᵛ sTy (σ ,ᵉ c) β
    subᵥ' m with ∈-map⁻ (mapᵖ (wkᵉ-tv Θ)) m
    ... | _ , m₀ , refl = ⊩subᵥ h m₀

    ordᵣ' : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ (wkᵉ-H Q)
          → Q' ⊩ ρ [ σ ,ᵉ c ]ʳ ≾̂ᵣ ρ' [ σ ,ᵉ c ]ʳ
    ordᵣ' m with ∈-map⁻ (mapᵖ wkᵉ-r) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
      subst₂ (λ x y → Q' ⊩ x ≾̂ᵣ y) (sym (wk-,ᵉ-r σ c ρ₀)) (sym (wk-,ᵉ-r σ c ρ₀'))
             (⊩ordᵣ h m₀)

    ordₑ' : ∀ {ε ε'} → (ε , ε') ∈ ordₑ (wkᵉ-H Q)
          → Q' ⊩ ε [ σ ,ᵉ c ]ᵉ ≾̂ₑ ε' [ σ ,ᵉ c ]ᵉ
    ordₑ' m with ∈-map⁻ (mapᵖ wkᵉ-e) m
    ... | (ε₀ , ε₀') , m₀ , refl =
      subst₂ (λ x y → Q' ⊩ x ≾̂ₑ y) (sym (wk-,ᵉ-e σ c ε₀)) (sym (wk-,ᵉ-e σ c ε₀'))
             (⊩ordₑ h m₀)

    disj' : ∀ {A ρ} → (A , ρ) ∈ disj (wkᵉ-H Q)
          → VarOK Q' (A [ σ ,ᵉ c ]ᵛ) (ρ [ σ ,ᵉ c ]ʳ)
    disj' m with ∈-map⁻ (mapᵈ wkᵉ-v wkᵉ-r) m
    ... | (A₀ , ρ₀) , m₀ , refl =
      subst₂ (VarOK Q') (sym (wk-,ᵉ-v σ c A₀)) (sym (wk-,ᵉ-r σ c ρ₀)) (⊩disj h m₀)
