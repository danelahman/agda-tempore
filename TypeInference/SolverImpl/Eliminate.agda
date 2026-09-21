------------------------------------------------------------------
-- Eliminating an unknown from a report                           --
--                                                                --
-- An unknown occurring below nowhere else is sent to the join of --
-- the hypotheses bounding it below, and those hypotheses go with --
-- it; an unknown absent from the reported type is eliminated     --
-- outright by the same step. Every grounding of the result       --
-- realises the original at the same type, every grounding of the --
-- original satisfies the result, and the reported type becomes a --
-- subtype of what it was. The two grade sorts are treated alike; --
-- open types carry no join, so a type variable is eliminated     --
-- against a single bound.                                        --
--                                                                --
-- Following Pottier's simplification of subtyping constraints    --
-- (ICFP 1996).                                                   --
------------------------------------------------------------------

open import Data.Bool.Base using (false; _∨_) renaming (Bool to 𝔹)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Eliminate (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types     S using (VType; CType; Eternal; _|×|ₑ_)
open import Syntax.Subtyping S

import Syntax.Types S as T

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Grounding S

open import TypeInference.SolverImpl.Polarity S

-- Updating one slot of a finitely indexed family, structurally so that
-- both equations hold without deciding equality in the definition.

upd : ∀ {n} {A : Set} → Fin n → A → (Fin n → A) → Fin n → A
upd zero    a f zero    = a
upd zero    a f (suc j) = f (suc j)
upd (suc i) a f zero    = f zero
upd (suc i) a f (suc j) = upd i a (λ k → f (suc k)) j

upd-≡ : ∀ {n} {A : Set} → (i : Fin n) → (a : A) → (f : Fin n → A) → upd i a f i ≡ a
upd-≡ zero    a f = refl
upd-≡ (suc i) a f = upd-≡ i a (λ k → f (suc k))

upd-≢ : ∀ {n} {A : Set} → (i j : Fin n) → (a : A) → (f : Fin n → A) → ¬ (i ≡ j)
      → upd i a f j ≡ f j
upd-≢ zero    zero    a f ¬p = ⊥-elim (¬p refl)
upd-≢ zero    (suc j) a f ¬p = refl
upd-≢ (suc i) zero    a f ¬p = refl
upd-≢ (suc i) (suc j) a f ¬p = upd-≢ i j a (λ k → f (suc k)) (λ q → ¬p (cong suc q))

-- Reading the polarity analysis back

⌊⌋-false : ∀ {n} {i j : Fin n} → ⌊ i ≟ᶠ j ⌋ ≡ false → ¬ (i ≡ j)
⌊⌋-false {i = i} {j = j} q with i ≟ᶠ j
... | yes _  = λ _ → ⊥-elim (tf q)
  where tf : (𝔹.true) ≡ false → _
        tf ()
... | no  ¬p = ¬p

∨-false : (a b : 𝔹) → a ∨ b ≡ false → (a ≡ false) × (b ≡ false)
∨-false false b e = refl , e

below-∪ : (p q : Pol) → below (p ∪ᴾ q) ≡ false
        → (below p ≡ false) × (below q ≡ false)
below-∪ p q e = ∨-false (below p) (below q) e

-- Eternality lives on the skeleton, which subtyping preserves, so it
-- transfers between two groundings related pointwise on the type
-- variables.

Et-<: : ∀ {Θ} {θ θ' : Grounding Θ} → (∀ α → gTy θ' α <:ᵛ gTy θ α)
      → (A : OVType Θ) → Eternal (⟦ A ⟧ᵛ θ) → Eternal (⟦ A ⟧ᵛ θ')
Et-<: k (tvar α)  et = <:ᵛ-eternalˡ (k α) et
Et-<: k (Base b)  et = et
Et-<: k Unit      et = et
Et-<: k Bool      et = et
Et-<: k (A |×| B) (p |×|ₑ q) = Et-<: k A p |×|ₑ Et-<: k B q
Et-<: k Empty     et = et

-- The signed shape of the two conclusions

atᵉ : Sign → E → E → Set
atᵉ ⁺ x y = x ≾ₑ y
atᵉ ⁻ x y = y ≾ₑ x

atʳ : Sign → R → R → Set
atʳ ⁺ x y = x ≾ᵣ y
atʳ ⁻ x y = y ≾ᵣ x

atᵛ : Sign → VType → VType → Set
atᵛ ⁺ A B = A <:ᵛ B
atᵛ ⁻ A B = B <:ᵛ A

atᶜ : Sign → CType → CType → Set
atᶜ ⁺ C D = C <:ᶜ D
atᶜ ⁻ C D = D <:ᶜ C

atᵉ-refl : (s : Sign) → (x : E) → atᵉ s x x
atᵉ-refl ⁺ x = ≾ₑ-refl
atᵉ-refl ⁻ x = ≾ₑ-refl

atʳ-refl : (s : Sign) → (x : R) → atʳ s x x
atʳ-refl ⁺ x = ≾ᵣ-refl
atʳ-refl ⁻ x = ≾ᵣ-refl

atᵛ-refl : (s : Sign) → (A : VType) → atᵛ s A A
atᵛ-refl ⁺ A = <:ᵛ-refl A
atᵛ-refl ⁻ A = <:ᵛ-refl A

atᵉ-· : (s : Sign) → {x x' y y' : E}
      → atᵉ s x y → atᵉ s x' y' → atᵉ s (x ·ₑ x') (y ·ₑ y')
atᵉ-· ⁺ p q = ≾ₑ-trans (·ₑ-monoˡ-≾ₑ p) (·ₑ-monoʳ-≾ₑ q)
atᵉ-· ⁻ p q = ≾ₑ-trans (·ₑ-monoˡ-≾ₑ p) (·ₑ-monoʳ-≾ₑ q)

atʳ-· : (s : Sign) → {x x' y y' : R}
      → atʳ s x y → atʳ s x' y' → atʳ s (x ·ᵣ x') (y ·ᵣ y')
atʳ-· ⁺ p q = ≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ p) (·ᵣ-monoʳ-≾ᵣ q)
atʳ-· ⁻ p q = ≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ p) (·ᵣ-monoʳ-≾ᵣ q)

atᵉ-⊔ : (s : Sign) → {x x' y y' : E}
      → atᵉ s x y → atᵉ s x' y' → atᵉ s (x ⊔ₑ x') (y ⊔ₑ y')
atᵉ-⊔ ⁺ p q = ⊔ₑ-mono p q
atᵉ-⊔ ⁻ p q = ⊔ₑ-mono p q

atʳ-⊔ : (s : Sign) → {x x' y y' : R}
      → atʳ s x y → atʳ s x' y' → atʳ s (x ⊔ᵣ x') (y ⊔ᵣ y')
atʳ-⊔ ⁺ p q = ⊔ᵣ-mono p q
atʳ-⊔ ⁻ p q = ⊔ᵣ-mono p q

atʳ-map : (s : Sign) → {x y : E} → atᵉ s x y → atʳ s (mapᵉ x) (mapᵉ y)
atʳ-map ⁺ p = map-monotoneᵉ p
atʳ-map ⁻ p = map-monotoneᵉ p

atᵛ-|×| : (s : Sign) → {A A' B B' : VType}
        → atᵛ s A A' → atᵛ s B B' → atᵛ s (A T.|×| B) (A' T.|×| B')
atᵛ-|×| ⁺ p q = p |×|ₛ q
atᵛ-|×| ⁻ p q = p |×|ₛ q

atᵛ-⇒ : (s : Sign) → {A A' : VType} {C C' : CType}
      → atᵛ (flipˢ s) A A' → atᶜ s C C' → atᵛ s (A T.⇒ C) (A' T.⇒ C')
atᵛ-⇒ ⁺ p q = p ⇒ₛ q
atᵛ-⇒ ⁻ p q = p ⇒ₛ q

atᵛ-box : (s : Sign) → {ρ ρ' : R} {A A' : VType}
        → atʳ (flipˢ s) ρ ρ' → atᵛ s A A' → atᵛ s (T.[ ρ ] A) (T.[ ρ' ] A')
atᵛ-box ⁺ p q = [ p ]ₛ q
atᵛ-box ⁻ p q = [ p ]ₛ q

atᶜ-‼ : (s : Sign) → {A A' : VType} {ε ε' : E}
      → atᵛ s A A' → atᵉ s ε ε' → atᶜ s (A T.‼ ε) (A' T.‼ ε')
atᶜ-‼ ⁺ p q = p ‼ₛ q
atᶜ-‼ ⁻ p q = p ‼ₛ q

sbᵉ-e : ∀ {Θ} → EVar Θ → EExp Θ → EExp Θ → EExp Θ
sbᵉ-e i b (evar j)   = upd i b evar j
sbᵉ-e i b (econst ε) = econst ε
sbᵉ-e i b (ε ·̂ₑ ε')  = sbᵉ-e i b ε ·̂ₑ sbᵉ-e i b ε'
sbᵉ-e i b (ε ⊔̂ₑ ε')  = sbᵉ-e i b ε ⊔̂ₑ sbᵉ-e i b ε'

sbᵉ-r : ∀ {Θ} → EVar Θ → EExp Θ → RExp Θ → RExp Θ
sbᵉ-r i b (rvar j)   = rvar j
sbᵉ-r i b (rconst ρ) = rconst ρ
sbᵉ-r i b (ρ ·̂ᵣ ρ')  = sbᵉ-r i b ρ ·̂ᵣ sbᵉ-r i b ρ'
sbᵉ-r i b (ρ ⊔̂ᵣ ρ')  = sbᵉ-r i b ρ ⊔̂ᵣ sbᵉ-r i b ρ'
sbᵉ-r i b ∣ ε ∣̂ᵉ     = ∣ sbᵉ-e i b ε ∣̂ᵉ

mutual

  sbᵉ-v : ∀ {Θ} → EVar Θ → EExp Θ → OVType Θ → OVType Θ
  sbᵉ-v i b (tvar α)  = tvar α
  sbᵉ-v i b (Base c)  = Base c
  sbᵉ-v i b Unit      = Unit
  sbᵉ-v i b Bool      = Bool
  sbᵉ-v i b (A |×| B) = sbᵉ-v i b A |×| sbᵉ-v i b B
  sbᵉ-v i b Empty     = Empty
  sbᵉ-v i b (A ⇒ C)   = sbᵉ-v i b A ⇒ sbᵉ-c i b C
  sbᵉ-v i b ([ ρ ] A) = [ sbᵉ-r i b ρ ] sbᵉ-v i b A

  sbᵉ-c : ∀ {Θ} → EVar Θ → EExp Θ → OCType Θ → OCType Θ
  sbᵉ-c i b (A ‼ ε) = sbᵉ-v i b A ‼ sbᵉ-e i b ε

lowᵉ : ∀ {Θ} → Grounding Θ → EVar Θ → E → Grounding Θ
lowᵉ θ i e = grounding (gTy θ) (gR θ) (upd i e (gE θ))

⟦sbᵉ⟧-e : ∀ {Θ} {θ : Grounding Θ} → (i : EVar Θ) → (b : EExp Θ) → (ε : EExp Θ)
        → ⟦ sbᵉ-e i b ε ⟧ᵉ θ ≡ ⟦ ε ⟧ᵉ (lowᵉ θ i (⟦ b ⟧ᵉ θ))
⟦sbᵉ⟧-e {θ = θ} i b (evar j) with i ≟ᶠ j
... | yes refl = trans (cong (λ x → ⟦ x ⟧ᵉ θ) (upd-≡ i b evar))
                       (sym (upd-≡ i (⟦ b ⟧ᵉ θ) (gE θ)))
... | no  ¬p   = trans (cong (λ x → ⟦ x ⟧ᵉ θ) (upd-≢ i j b evar ¬p))
                       (sym (upd-≢ i j (⟦ b ⟧ᵉ θ) (gE θ) ¬p))
⟦sbᵉ⟧-e i b (econst ε) = refl
⟦sbᵉ⟧-e i b (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (⟦sbᵉ⟧-e i b ε) (⟦sbᵉ⟧-e i b ε')
⟦sbᵉ⟧-e i b (ε ⊔̂ₑ ε')  = cong₂ _⊔ₑ_ (⟦sbᵉ⟧-e i b ε) (⟦sbᵉ⟧-e i b ε')

⟦sbᵉ⟧-r : ∀ {Θ} {θ : Grounding Θ} → (i : EVar Θ) → (b : EExp Θ) → (ρ : RExp Θ)
        → ⟦ sbᵉ-r i b ρ ⟧ʳ θ ≡ ⟦ ρ ⟧ʳ (lowᵉ θ i (⟦ b ⟧ᵉ θ))
⟦sbᵉ⟧-r i b (rvar j)   = refl
⟦sbᵉ⟧-r i b (rconst ρ) = refl
⟦sbᵉ⟧-r i b (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (⟦sbᵉ⟧-r i b ρ) (⟦sbᵉ⟧-r i b ρ')
⟦sbᵉ⟧-r i b (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔ᵣ_ (⟦sbᵉ⟧-r i b ρ) (⟦sbᵉ⟧-r i b ρ')
⟦sbᵉ⟧-r i b ∣ ε ∣̂ᵉ     = cong mapᵉ (⟦sbᵉ⟧-e i b ε)

mutual

  ⟦sbᵉ⟧-v : ∀ {Θ} {θ : Grounding Θ} → (i : EVar Θ) → (b : EExp Θ) → (A : OVType Θ)
          → ⟦ sbᵉ-v i b A ⟧ᵛ θ ≡ ⟦ A ⟧ᵛ (lowᵉ θ i (⟦ b ⟧ᵉ θ))
  ⟦sbᵉ⟧-v i b (tvar α)  = refl
  ⟦sbᵉ⟧-v i b (Base c)  = refl
  ⟦sbᵉ⟧-v i b Unit      = refl
  ⟦sbᵉ⟧-v i b Bool      = refl
  ⟦sbᵉ⟧-v i b (A |×| B) = cong₂ T._|×|_ (⟦sbᵉ⟧-v i b A) (⟦sbᵉ⟧-v i b B)
  ⟦sbᵉ⟧-v i b Empty     = refl
  ⟦sbᵉ⟧-v i b (A ⇒ C)   = cong₂ T._⇒_ (⟦sbᵉ⟧-v i b A) (⟦sbᵉ⟧-c i b C)
  ⟦sbᵉ⟧-v i b ([ ρ ] A) = cong₂ T.[_]_ (⟦sbᵉ⟧-r i b ρ) (⟦sbᵉ⟧-v i b A)

  ⟦sbᵉ⟧-c : ∀ {Θ} {θ : Grounding Θ} → (i : EVar Θ) → (b : EExp Θ) → (C : OCType Θ)
          → ⟦ sbᵉ-c i b C ⟧ᶜ θ ≡ ⟦ C ⟧ᶜ (lowᵉ θ i (⟦ b ⟧ᵉ θ))
  ⟦sbᵉ⟧-c i b (A ‼ ε) = cong₂ T._‼_ (⟦sbᵉ⟧-v i b A) (⟦sbᵉ⟧-e i b ε)

-- An unknown absent from an expression is invisible to a change of its
-- value.

invᵉ-e : ∀ {Θ} {θ : Grounding Θ} {e₀ : E} → (i : EVar Θ) → (ε : EExp Θ)
       → below (polₑ-e i ⁻ ε) ≡ false → ⟦ ε ⟧ᵉ (lowᵉ θ i e₀) ≡ ⟦ ε ⟧ᵉ θ
invᵉ-e {θ = θ} {e₀} i (evar j) q = upd-≢ i j e₀ (gE θ) (⌊⌋-false q)
invᵉ-e i (econst ε) q = refl
invᵉ-e i (ε ·̂ₑ ε')  q =
  cong₂ _·ₑ_ (invᵉ-e i ε (proj₁ d)) (invᵉ-e i ε' (proj₂ d))
  where d = below-∪ (polₑ-e i ⁻ ε) (polₑ-e i ⁻ ε') q
invᵉ-e i (ε ⊔̂ₑ ε')  q =
  cong₂ _⊔ₑ_ (invᵉ-e i ε (proj₁ d)) (invᵉ-e i ε' (proj₂ d))
  where d = below-∪ (polₑ-e i ⁻ ε) (polₑ-e i ⁻ ε') q

-- Lowering an unknown lowers whatever has no occurrence of it below

module _ {Θ : Scope} (θ : Grounding Θ) (i : EVar Θ) (e₀ : E)
         (le : e₀ ≾ₑ gE θ i) where

  private
    θ⁻ : Grounding Θ
    θ⁻ = lowᵉ θ i e₀

  monoᵉ-e : (s : Sign) → (ε : EExp Θ) → below (polₑ-e i s ε) ≡ false
          → atᵉ s (⟦ ε ⟧ᵉ θ⁻) (⟦ ε ⟧ᵉ θ)
  monoᵉ-e ⁺ (evar j) q with i ≟ᶠ j
  ... | yes refl = subst (λ x → x ≾ₑ gE θ i) (sym (upd-≡ i e₀ (gE θ))) le
  ... | no  ¬p   = subst (λ x → x ≾ₑ gE θ j) (sym (upd-≢ i j e₀ (gE θ) ¬p)) ≾ₑ-refl
  monoᵉ-e ⁻ (evar j) q =
    ≾ₑ-reflexive (sym (upd-≢ i j e₀ (gE θ) (⌊⌋-false q)))
  monoᵉ-e s (econst ε) q = atᵉ-refl s ε
  monoᵉ-e s (ε ·̂ₑ ε')  q =
    atᵉ-· s (monoᵉ-e s ε (proj₁ d)) (monoᵉ-e s ε' (proj₂ d))
    where d = below-∪ (polₑ-e i s ε) (polₑ-e i s ε') q
  monoᵉ-e s (ε ⊔̂ₑ ε')  q =
    atᵉ-⊔ s (monoᵉ-e s ε (proj₁ d)) (monoᵉ-e s ε' (proj₂ d))
    where d = below-∪ (polₑ-e i s ε) (polₑ-e i s ε') q

  monoᵉ-r : (s : Sign) → (ρ : RExp Θ) → below (polₑ-r i s ρ) ≡ false
          → atʳ s (⟦ ρ ⟧ʳ θ⁻) (⟦ ρ ⟧ʳ θ)
  monoᵉ-r s (rvar j)   q = atʳ-refl s (gR θ j)
  monoᵉ-r s (rconst ρ) q = atʳ-refl s ρ
  monoᵉ-r s (ρ ·̂ᵣ ρ')  q =
    atʳ-· s (monoᵉ-r s ρ (proj₁ d)) (monoᵉ-r s ρ' (proj₂ d))
    where d = below-∪ (polₑ-r i s ρ) (polₑ-r i s ρ') q
  monoᵉ-r s (ρ ⊔̂ᵣ ρ')  q =
    atʳ-⊔ s (monoᵉ-r s ρ (proj₁ d)) (monoᵉ-r s ρ' (proj₂ d))
    where d = below-∪ (polₑ-r i s ρ) (polₑ-r i s ρ') q
  monoᵉ-r s ∣ ε ∣̂ᵉ     q = atʳ-map s (monoᵉ-e s ε q)

  mutual

    monoᵉ-v : (s : Sign) → (A : OVType Θ) → below (polₑ-v i s A) ≡ false
            → atᵛ s (⟦ A ⟧ᵛ θ⁻) (⟦ A ⟧ᵛ θ)
    monoᵉ-v s (tvar α)  q = atᵛ-refl s (gTy θ α)
    monoᵉ-v s (Base c)  q = atᵛ-refl s (T.Base c)
    monoᵉ-v s Unit      q = atᵛ-refl s T.Unit
    monoᵉ-v s Bool      q = atᵛ-refl s T.Bool
    monoᵉ-v s (A |×| B) q =
      atᵛ-|×| s (monoᵉ-v s A (proj₁ d)) (monoᵉ-v s B (proj₂ d))
      where d = below-∪ (polₑ-v i s A) (polₑ-v i s B) q
    monoᵉ-v s Empty     q = atᵛ-refl s T.Empty
    monoᵉ-v s (A ⇒ C)   q =
      atᵛ-⇒ s (monoᵉ-v (flipˢ s) A (proj₁ d)) (monoᵉ-c s C (proj₂ d))
      where d = below-∪ (polₑ-v i (flipˢ s) A) (polₑ-c i s C) q
    monoᵉ-v s ([ ρ ] A) q =
      atᵛ-box s (monoᵉ-r (flipˢ s) ρ (proj₁ d)) (monoᵉ-v s A (proj₂ d))
      where d = below-∪ (polₑ-r i (flipˢ s) ρ) (polₑ-v i s A) q

    monoᵉ-c : (s : Sign) → (C : OCType Θ) → below (polₑ-c i s C) ≡ false
            → atᶜ s (⟦ C ⟧ᶜ θ⁻) (⟦ C ⟧ᶜ θ)
    monoᵉ-c s (A ‼ ε) q =
      atᶜ-‼ s (monoᵉ-v s A (proj₁ d)) (monoᵉ-e s ε (proj₂ d))
      where d = below-∪ (polₑ-v i s A) (polₑ-e i s ε) q

-- Reading the folded analysis at one entry of a component

polsₑ-ordᵣ-∈ : ∀ {Θ} → (i : EVar Θ) → (l : List (RExp Θ × RExp Θ))
             → below (polsₑ-ordᵣ i l) ≡ false
             → ∀ {ρ ρ'} → (ρ , ρ') ∈ l
             → (below (polₑ-r i ⁺ ρ) ≡ false) × (below (polₑ-r i ⁻ ρ') ≡ false)
polsₑ-ordᵣ-∈ i ((ρ₀ , ρ₀') ∷ l) q (here refl) = proj₁ d₁ , proj₁ d₂
  where d₁ = below-∪ (polₑ-r i ⁺ ρ₀) (polₑ-r i ⁻ ρ₀' ∪ᴾ polsₑ-ordᵣ i l) q
        d₂ = below-∪ (polₑ-r i ⁻ ρ₀') (polsₑ-ordᵣ i l) (proj₂ d₁)
polsₑ-ordᵣ-∈ i ((ρ₀ , ρ₀') ∷ l) q (there m) = polsₑ-ordᵣ-∈ i l (proj₂ d₂) m
  where d₁ = below-∪ (polₑ-r i ⁺ ρ₀) (polₑ-r i ⁻ ρ₀' ∪ᴾ polsₑ-ordᵣ i l) q
        d₂ = below-∪ (polₑ-r i ⁻ ρ₀') (polsₑ-ordᵣ i l) (proj₂ d₁)

polsₑ-ordₑ-∈ : ∀ {Θ} → (i : EVar Θ) → (l : List (EExp Θ × EExp Θ))
             → below (polsₑ-ordₑ i l) ≡ false
             → ∀ {ε ε'} → (ε , ε') ∈ l
             → (below (polₑ-e i ⁺ ε) ≡ false) × (below (polₑ-e i ⁻ ε') ≡ false)
polsₑ-ordₑ-∈ i ((ε₀ , ε₀') ∷ l) q (here refl) = proj₁ d₁ , proj₁ d₂
  where d₁ = below-∪ (polₑ-e i ⁺ ε₀) (polₑ-e i ⁻ ε₀' ∪ᴾ polsₑ-ordₑ i l) q
        d₂ = below-∪ (polₑ-e i ⁻ ε₀') (polsₑ-ordₑ i l) (proj₂ d₁)
polsₑ-ordₑ-∈ i ((ε₀ , ε₀') ∷ l) q (there m) = polsₑ-ordₑ-∈ i l (proj₂ d₂) m
  where d₁ = below-∪ (polₑ-e i ⁺ ε₀) (polₑ-e i ⁻ ε₀' ∪ᴾ polsₑ-ordₑ i l) q
        d₂ = below-∪ (polₑ-e i ⁻ ε₀') (polsₑ-ordₑ i l) (proj₂ d₁)

polsₑ-disj-∈ : ∀ {Θ} → (i : EVar Θ) → (l : List (OVType Θ × RExp Θ))
             → below (polsₑ-disj i l) ≡ false
             → ∀ {A ρ} → (A , ρ) ∈ l → below (polₑ-r i ⁺ ρ) ≡ false
polsₑ-disj-∈ i ((A₀ , ρ₀) ∷ l) q (here refl) =
  proj₁ (below-∪ (polₑ-r i ⁺ ρ₀) (polsₑ-disj i l) q)
polsₑ-disj-∈ i ((A₀ , ρ₀) ∷ l) q (there m)   =
  polsₑ-disj-∈ i l (proj₂ (below-∪ (polₑ-r i ⁺ ρ₀) (polsₑ-disj i l) q)) m

-- One step: the reported type, the hypothesis set, and the three facts
-- relating them

record Elim {Θ : Scope} (C : OCType Θ) (Q : Hyps Θ) : Set where
  constructor mkElim
  field
    Ĉ     : OCType Θ
    Q̂     : Hyps Θ
    keep  : (θ : Grounding Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ Q̂
    real  : (θ : Grounding Θ) → θ ⊨ᴴ Q̂
          → Σ[ θ' ∈ Grounding Θ ] ((θ' ⊨ᴴ Q) × (⟦ C ⟧ᶜ θ' ≡ ⟦ Ĉ ⟧ᶜ θ))
    princ : (θ : Grounding Θ) → θ ⊨ᴴ Q → ⟦ Ĉ ⟧ᶜ θ <:ᶜ ⟦ C ⟧ᶜ θ

open Elim public

idElim : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → Elim C Q
idElim C Q = mkElim C Q (λ θ h → h) (λ θ h → θ , h , refl)
                        (λ θ h → <:ᶜ-refl (⟦ C ⟧ᶜ θ))

infixl 5 _⨾ᴱ_

_⨾ᴱ_ : ∀ {Θ} {C : OCType Θ} {Q : Hyps Θ} → (r : Elim C Q)
     → Elim (Ĉ r) (Q̂ r) → Elim C Q
_⨾ᴱ_ r s = mkElim (Ĉ s) (Q̂ s)
  (λ θ h → keep s θ (keep r θ h))
  (λ θ h → let t₁ = real s θ h
               t₂ = real r (proj₁ t₁) (proj₁ (proj₂ t₁))
           in proj₁ t₂ , proj₁ (proj₂ t₂) , trans (proj₂ (proj₂ t₂)) (proj₂ (proj₂ t₁)))
  (λ θ h → <:ᶜ-trans (princ s θ (keep r θ h)) (princ r θ h))

-- The join of a non-empty list of bounds, its head named so that a
-- lone bound is its own join and folded to the left so that the join
-- reads in the order the bounds were met.

joinₑ : ∀ {Θ} → EExp Θ → List (EExp Θ) → EExp Θ
joinₑ ε []        = ε
joinₑ ε (ε' ∷ εs) = joinₑ (ε ⊔̂ₑ ε') εs

joinₑ-ub : ∀ {Θ} {θ : Grounding Θ} → (ε₀ : EExp Θ) → (εs : List (EExp Θ))
         → ∀ {ε} → ε ∈ ε₀ ∷ εs → ⟦ ε ⟧ᵉ θ ≾ₑ ⟦ joinₑ ε₀ εs ⟧ᵉ θ
joinₑ-ub ε₀ []        (here refl) = ≾ₑ-refl
joinₑ-ub {θ = θ} ε₀ (ε₁ ∷ εs) (here refl) =
  ≾ₑ-trans (⊔ₑ-ubˡ (⟦ ε₀ ⟧ᵉ θ) (⟦ ε₁ ⟧ᵉ θ))
           (joinₑ-ub (ε₀ ⊔̂ₑ ε₁) εs (here refl))
joinₑ-ub {θ = θ} ε₀ (ε₁ ∷ εs) (there (here refl)) =
  ≾ₑ-trans (⊔ₑ-ubʳ (⟦ ε₀ ⟧ᵉ θ) (⟦ ε₁ ⟧ᵉ θ))
           (joinₑ-ub (ε₀ ⊔̂ₑ ε₁) εs (here refl))
joinₑ-ub ε₀ (ε₁ ∷ εs) (there (there m)) = joinₑ-ub (ε₀ ⊔̂ₑ ε₁) εs (there m)

joinₑ-lub : ∀ {Θ} {θ : Grounding Θ} {x : E} → (ε₀ : EExp Θ) → (εs : List (EExp Θ))
          → (∀ {ε} → ε ∈ ε₀ ∷ εs → ⟦ ε ⟧ᵉ θ ≾ₑ x)
          → ⟦ joinₑ ε₀ εs ⟧ᵉ θ ≾ₑ x
joinₑ-lub ε₀ []        k = k (here refl)
joinₑ-lub ε₀ (ε₁ ∷ εs) k =
  joinₑ-lub (ε₀ ⊔̂ₑ ε₁) εs
    (λ { (here refl) → ⊔ₑ-lub (k (here refl)) (k (there (here refl)))
       ; (there m)   → k (there (there m)) })

joinₑ-below : ∀ {Θ} → (i : EVar Θ) → (ε₀ : EExp Θ) → (εs : List (EExp Θ))
            → below (polₑ-e i ⁻ (joinₑ ε₀ εs)) ≡ false
            → ∀ {ε} → ε ∈ ε₀ ∷ εs → below (polₑ-e i ⁻ ε) ≡ false
joinₑ-below i ε₀ []        q (here refl) = q
joinₑ-below i ε₀ (ε₁ ∷ εs) q (here refl) =
  proj₁ (below-∪ (polₑ-e i ⁻ ε₀) (polₑ-e i ⁻ ε₁)
                 (joinₑ-below i (ε₀ ⊔̂ₑ ε₁) εs q (here refl)))
joinₑ-below i ε₀ (ε₁ ∷ εs) q (there (here refl)) =
  proj₂ (below-∪ (polₑ-e i ⁻ ε₀) (polₑ-e i ⁻ ε₁)
                 (joinₑ-below i (ε₀ ⊔̂ₑ ε₁) εs q (here refl)))
joinₑ-below i ε₀ (ε₁ ∷ εs) q (there (there m)) =
  joinₑ-below i (ε₀ ⊔̂ₑ ε₁) εs q (there m)

-- The hypotheses bounding an unknown below, and the rest

record Splitₑ {Θ : Scope} (i : EVar Θ) (l : List (EExp Θ × EExp Θ)) : Set where
  constructor split
  field
    bnd   : EExp Θ
    bnds  : List (EExp Θ)
    rest  : List (EExp Θ × EExp Θ)
    mem   : ∀ {ε} → ε ∈ bnd ∷ bnds → (ε , evar i) ∈ l
    sub   : ∀ {p} → p ∈ rest → p ∈ l
    cases : ∀ {ε ε'} → (ε , ε') ∈ l
          → ((ε ∈ bnd ∷ bnds) × (ε' ≡ evar i)) ⊎ ((ε , ε') ∈ rest)

open Splitₑ

-- The bound the unknown is sent to

lubₑ : ∀ {Θ} {i : EVar Θ} {l : List (EExp Θ × EExp Θ)} → Splitₑ i l → EExp Θ
lubₑ s = joinₑ (bnd s) (bnds s)

-- A hypothesis that is not a bound joins the rest; one that is joins
-- the bounds

consₑ : ∀ {Θ} {i : EVar Θ} {l : List (EExp Θ × EExp Θ)} {ε₀ ε₀'} → Splitₑ i l
      → Splitₑ i ((ε₀ , ε₀') ∷ l)
consₑ {ε₀ = ε₀} {ε₀'} s =
  split (bnd s) (bnds s) ((ε₀ , ε₀') ∷ rest s)
        (λ m → there (mem s m))
        (λ { (here refl) → here refl ; (there m) → there (sub s m) })
        (λ { (here refl) → inj₂ (here refl)
           ; (there m)   → [ inj₁ , (λ r → inj₂ (there r)) ]′ (cases s m) })

moreₑ : ∀ {Θ} {i : EVar Θ} {l : List (EExp Θ × EExp Θ)} {ε₀} → Splitₑ i l
      → Splitₑ i ((ε₀ , evar i) ∷ l)
moreₑ {ε₀ = ε₀} s =
  split ε₀ (bnd s ∷ bnds s) (rest s)
        (λ { (here refl) → here refl ; (there m) → there (mem s m) })
        (λ m → there (sub s m))
        (λ { (here refl) → inj₁ (here refl , refl)
           ; (there m)   → [ (λ { (mb , e) → inj₁ (there mb , e) })
                           , inj₂ ]′ (cases s m) })

oneₑ : ∀ {Θ} {i : EVar Θ} {l : List (EExp Θ × EExp Θ)} {ε₀}
     → Splitₑ i ((ε₀ , evar i) ∷ l)
oneₑ {l = l} {ε₀} =
  split ε₀ [] l
        (λ { (here refl) → here refl ; (there ()) })
        there
        (λ { (here refl) → inj₁ (here refl , refl) ; (there m) → inj₂ m })

splitₑ : ∀ {Θ} → (i : EVar Θ) → (l : List (EExp Θ × EExp Θ)) → Maybe (Splitₑ i l)
splitₑ i [] = nothing
splitₑ i ((ε , evar j) ∷ l) with i ≟ᶠ j
... | yes refl with splitₑ i l
...   | just s  = just (moreₑ s)
...   | nothing = just oneₑ
splitₑ i ((ε , evar j) ∷ l) | no _ with splitₑ i l
... | just s  = just (consₑ s)
... | nothing = nothing
splitₑ i ((ε , econst _) ∷ l) with splitₑ i l
... | just s  = just (consₑ s)
... | nothing = nothing
splitₑ i ((ε , _ ·̂ₑ _) ∷ l) with splitₑ i l
... | just s  = just (consₑ s)
... | nothing = nothing
splitₑ i ((ε , _ ⊔̂ₑ _) ∷ l) with splitₑ i l
... | just s  = just (consₑ s)
... | nothing = nothing

stepᵉ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ)
      → (s : Splitₑ i (ordₑ Q))
      → below (polₑ-e i ⁻ (lubₑ s)) ≡ false
      → below (polₑᴴ (hyps (ets Q) (subᵥ Q) (ordᵣ Q) (rest s) (disj Q)) i) ≡ false
      → below (polₑ-c i ⁺ C) ≡ false
      → Elim C Q
stepᵉ {Θ} C Q i s cb cq cc = mkElim Ĉ₀ Q₀ keep₀ real₀ princ₀
  where
    b : EExp Θ
    b = lubₑ s

    Ĉ₀ : OCType Θ
    Ĉ₀ = sbᵉ-c i b C

    Q₀ : Hyps Θ
    Q₀ = hyps (ets Q) (subᵥ Q)
              (map (mapᵖ (sbᵉ-r i b)) (ordᵣ Q))
              (map (mapᵖ (sbᵉ-e i b)) (rest s))
              (map (mapᵈ (sbᵉ-v i b) (sbᵉ-r i b)) (disj Q))

    d₁ = below-∪ (polsₑ-ordᵣ i (ordᵣ Q))
                 (polsₑ-ordₑ i (rest s) ∪ᴾ polsₑ-disj i (disj Q)) cq
    d₂ = below-∪ (polsₑ-ordₑ i (rest s)) (polsₑ-disj i (disj Q)) (proj₂ d₁)

    cR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q
       → (below (polₑ-r i ⁺ ρ) ≡ false) × (below (polₑ-r i ⁻ ρ') ≡ false)
    cR = polsₑ-ordᵣ-∈ i (ordᵣ Q) (proj₁ d₁)

    cE : ∀ {ε ε'} → (ε , ε') ∈ rest s
       → (below (polₑ-e i ⁺ ε) ≡ false) × (below (polₑ-e i ⁻ ε') ≡ false)
    cE = polsₑ-ordₑ-∈ i (rest s) (proj₁ d₂)

    cD : ∀ {A ρ} → (A , ρ) ∈ disj Q → below (polₑ-r i ⁺ ρ) ≡ false
    cD = polsₑ-disj-∈ i (disj Q) (proj₂ d₂)

    -- membership of an image

    ∈-mapᵖʳ : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q
            → (sbᵉ-r i b ρ , sbᵉ-r i b ρ') ∈ map (mapᵖ (sbᵉ-r i b)) (ordᵣ Q)
    ∈-mapᵖʳ = ∈-map⁺ (mapᵖ (sbᵉ-r i b))

    ∈-mapᵖᵉ : ∀ {ε ε'} → (ε , ε') ∈ rest s
            → (sbᵉ-e i b ε , sbᵉ-e i b ε') ∈ map (mapᵖ (sbᵉ-e i b)) (rest s)
    ∈-mapᵖᵉ = ∈-map⁺ (mapᵖ (sbᵉ-e i b))

    ∈-mapᵈ' : ∀ {A ρ} → (A , ρ) ∈ disj Q
            → (sbᵉ-v i b A , sbᵉ-r i b ρ) ∈ map (mapᵈ (sbᵉ-v i b) (sbᵉ-r i b)) (disj Q)
    ∈-mapᵈ' = ∈-map⁺ (mapᵈ (sbᵉ-v i b) (sbᵉ-r i b))

    keep₀ : (θ : Grounding Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ Q₀
    keep₀ θ h = mk⊨ᴴ (etOK h) (subOK h) ordR ordE dsj
      where
        e₀ : E
        e₀ = ⟦ b ⟧ᵉ θ

        le : e₀ ≾ₑ gE θ i
        le = joinₑ-lub (bnd s) (bnds s) (λ m → ordEOK h (mem s m))

        ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ (sbᵉ-r i b)) (ordᵣ Q)
             → ⟦ ρ ⟧ʳ θ ≾ᵣ ⟦ ρ' ⟧ʳ θ
        ordR m = go (ordᵣ Q) (λ q → q) m
          where
            go : (l : List (RExp Θ × RExp Θ)) → (∀ {p} → p ∈ l → p ∈ ordᵣ Q)
               → ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ (sbᵉ-r i b)) l
               → ⟦ ρ ⟧ʳ θ ≾ᵣ ⟦ ρ' ⟧ʳ θ
            go ((ρ₀ , ρ₀') ∷ l) k (here refl) =
              subst₂ _≾ᵣ_ (sym (⟦sbᵉ⟧-r i b ρ₀)) (sym (⟦sbᵉ⟧-r i b ρ₀'))
                (≾ᵣ-trans (monoᵉ-r θ i e₀ le ⁺ ρ₀ (proj₁ (cR (k (here refl)))))
                (≾ᵣ-trans (ordROK h (k (here refl)))
                          (monoᵉ-r θ i e₀ le ⁻ ρ₀' (proj₂ (cR (k (here refl)))))))
            go ((ρ₀ , ρ₀') ∷ l) k (there m) = go l (λ q → k (there q)) m

        ordE : ∀ {ε ε'} → (ε , ε') ∈ map (mapᵖ (sbᵉ-e i b)) (rest s)
             → ⟦ ε ⟧ᵉ θ ≾ₑ ⟦ ε' ⟧ᵉ θ
        ordE m = go (rest s) (λ q → q) m
          where
            go : (l : List (EExp Θ × EExp Θ)) → (∀ {p} → p ∈ l → p ∈ rest s)
               → ∀ {ε ε'} → (ε , ε') ∈ map (mapᵖ (sbᵉ-e i b)) l
               → ⟦ ε ⟧ᵉ θ ≾ₑ ⟦ ε' ⟧ᵉ θ
            go ((ε₀ , ε₀') ∷ l) k (here refl) =
              subst₂ _≾ₑ_ (sym (⟦sbᵉ⟧-e i b ε₀)) (sym (⟦sbᵉ⟧-e i b ε₀'))
                (≾ₑ-trans (monoᵉ-e θ i e₀ le ⁺ ε₀ (proj₁ (cE (k (here refl)))))
                (≾ₑ-trans (ordEOK h (sub s (k (here refl))))
                          (monoᵉ-e θ i e₀ le ⁻ ε₀' (proj₂ (cE (k (here refl)))))))
            go ((ε₀ , ε₀') ∷ l) k (there m) = go l (λ q → k (there q)) m

        dsj : ∀ {A ρ} → (A , ρ) ∈ map (mapᵈ (sbᵉ-v i b) (sbᵉ-r i b)) (disj Q)
            → Eternal (⟦ A ⟧ᵛ θ) ⊎ (⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)
        dsj m = go (disj Q) (λ q → q) m
          where
            go : (l : List (OVType Θ × RExp Θ)) → (∀ {p} → p ∈ l → p ∈ disj Q)
               → ∀ {A ρ} → (A , ρ) ∈ map (mapᵈ (sbᵉ-v i b) (sbᵉ-r i b)) l
               → Eternal (⟦ A ⟧ᵛ θ) ⊎ (⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)
            go ((A₀ , ρ₀) ∷ l) k (here refl) =
              [ (λ et → inj₁ (subst Eternal (sym (⟦sbᵉ⟧-v i b A₀))
                                    (Et-<: (λ γ → <:ᵛ-refl _) A₀ et)))
              , (λ lu → inj₂ (subst (_≾ᵣ uᵣ) (sym (⟦sbᵉ⟧-r i b ρ₀))
                                    (≾ᵣ-trans (monoᵉ-r θ i e₀ le ⁺ ρ₀
                                                 (cD (k (here refl)))) lu)))
              ]′ (disjOK h (k (here refl)))
            go ((A₀ , ρ₀) ∷ l) k (there m) = go l (λ q → k (there q)) m

    real₀ : (θ : Grounding Θ) → θ ⊨ᴴ Q₀
          → Σ[ θ' ∈ Grounding Θ ] ((θ' ⊨ᴴ Q) × (⟦ C ⟧ᶜ θ' ≡ ⟦ Ĉ₀ ⟧ᶜ θ))
    real₀ θ h = θ' , mk⊨ᴴ (etOK h) (subOK h) ordR ordE dsj , sym (⟦sbᵉ⟧-c i b C)
      where
        θ' : Grounding Θ
        θ' = lowᵉ θ i (⟦ b ⟧ᵉ θ)

        ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → ⟦ ρ ⟧ʳ θ' ≾ᵣ ⟦ ρ' ⟧ʳ θ'
        ordR {ρ} {ρ'} m =
          subst₂ _≾ᵣ_ (⟦sbᵉ⟧-r i b ρ) (⟦sbᵉ⟧-r i b ρ') (ordROK h (∈-mapᵖʳ m))

        ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → ⟦ ε ⟧ᵉ θ' ≾ₑ ⟦ ε' ⟧ᵉ θ'
        ordE {ε} {ε'} m with cases s m
        ... | inj₁ (mb , refl) =
              subst₂ _≾ₑ_ (sym (invᵉ-e i ε (joinₑ-below i (bnd s) (bnds s) cb mb)))
                          (sym (upd-≡ i (⟦ b ⟧ᵉ θ) (gE θ)))
                     (joinₑ-ub {θ = θ} (bnd s) (bnds s) mb)
        ... | inj₂ m' =
              subst₂ _≾ₑ_ (⟦sbᵉ⟧-e i b ε) (⟦sbᵉ⟧-e i b ε') (ordEOK h (∈-mapᵖᵉ m'))

        dsj : ∀ {A ρ} → (A , ρ) ∈ disj Q
            → Eternal (⟦ A ⟧ᵛ θ') ⊎ (⟦ ρ ⟧ʳ θ' ≾ᵣ uᵣ)
        dsj {A} {ρ} m =
          [ (λ et → inj₁ (subst Eternal (⟦sbᵉ⟧-v i b A) et))
          , (λ lu → inj₂ (subst (_≾ᵣ uᵣ) (⟦sbᵉ⟧-r i b ρ) lu))
          ]′ (disjOK h (∈-mapᵈ' m))

    princ₀ : (θ : Grounding Θ) → θ ⊨ᴴ Q → ⟦ Ĉ₀ ⟧ᶜ θ <:ᶜ ⟦ C ⟧ᶜ θ
    princ₀ θ h =
      subst (_<:ᶜ ⟦ C ⟧ᶜ θ) (sym (⟦sbᵉ⟧-c i b C))
            (monoᵉ-c θ i (⟦ b ⟧ᵉ θ)
                     (joinₑ-lub (bnd s) (bnds s) (λ m → ordEOK h (mem s m)))
                     ⁺ C cc)

-- The search: one unknown at a time, the first that qualifies

stepᵉ? : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : EVar Θ) → Maybe (Elim C Q)
stepᵉ? C Q i with splitₑ i (ordₑ Q)
... | nothing = nothing
... | just s
    with below (polₑ-e i ⁻ (lubₑ s)) in c1
       | below (polₑᴴ (hyps (ets Q) (subᵥ Q) (ordᵣ Q) (rest s) (disj Q)) i) in c2
       | below (polₑ-c i ⁺ C) in c3
...   | false | false | false = just (stepᵉ C Q i s c1 c2 c3)
...   | _     | _     | _     = nothing

fins : (n : ℕ) → List (Fin n)
fins zero    = []
fins (suc n) = zero ∷ map suc (fins n)

firstᵉ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → List (EVar Θ) → Maybe (Elim C Q)
firstᵉ C Q []       = nothing
firstᵉ C Q (i ∷ is) with stepᵉ? C Q i
... | just r  = just r
... | nothing = firstᵉ C Q is

-- Effect expressions carry no resource unknown, so only the resource
-- expressions and the box grades of a type move.

sbʳ-r : ∀ {Θ} → RVar Θ → RExp Θ → RExp Θ → RExp Θ
sbʳ-r i b (rvar j)   = upd i b rvar j
sbʳ-r i b (rconst ρ) = rconst ρ
sbʳ-r i b (ρ ·̂ᵣ ρ')  = sbʳ-r i b ρ ·̂ᵣ sbʳ-r i b ρ'
sbʳ-r i b (ρ ⊔̂ᵣ ρ')  = sbʳ-r i b ρ ⊔̂ᵣ sbʳ-r i b ρ'
sbʳ-r i b ∣ ε ∣̂ᵉ     = ∣ ε ∣̂ᵉ

mutual

  sbʳ-v : ∀ {Θ} → RVar Θ → RExp Θ → OVType Θ → OVType Θ
  sbʳ-v i b (tvar α)  = tvar α
  sbʳ-v i b (Base c)  = Base c
  sbʳ-v i b Unit      = Unit
  sbʳ-v i b Bool      = Bool
  sbʳ-v i b (A |×| B) = sbʳ-v i b A |×| sbʳ-v i b B
  sbʳ-v i b Empty     = Empty
  sbʳ-v i b (A ⇒ C)   = sbʳ-v i b A ⇒ sbʳ-c i b C
  sbʳ-v i b ([ ρ ] A) = [ sbʳ-r i b ρ ] sbʳ-v i b A

  sbʳ-c : ∀ {Θ} → RVar Θ → RExp Θ → OCType Θ → OCType Θ
  sbʳ-c i b (A ‼ ε) = sbʳ-v i b A ‼ ε

lowʳ : ∀ {Θ} → Grounding Θ → RVar Θ → R → Grounding Θ
lowʳ θ i ρ = grounding (gTy θ) (upd i ρ (gR θ)) (gE θ)

⟦lowʳ⟧-e : ∀ {Θ} {θ : Grounding Θ} {ρ₀ : R} → (i : RVar Θ) → (ε : EExp Θ)
         → ⟦ ε ⟧ᵉ (lowʳ θ i ρ₀) ≡ ⟦ ε ⟧ᵉ θ
⟦lowʳ⟧-e i (evar j)   = refl
⟦lowʳ⟧-e i (econst ε) = refl
⟦lowʳ⟧-e i (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (⟦lowʳ⟧-e i ε) (⟦lowʳ⟧-e i ε')
⟦lowʳ⟧-e i (ε ⊔̂ₑ ε')  = cong₂ _⊔ₑ_ (⟦lowʳ⟧-e i ε) (⟦lowʳ⟧-e i ε')

⟦sbʳ⟧-r : ∀ {Θ} {θ : Grounding Θ} → (i : RVar Θ) → (b : RExp Θ) → (ρ : RExp Θ)
        → ⟦ sbʳ-r i b ρ ⟧ʳ θ ≡ ⟦ ρ ⟧ʳ (lowʳ θ i (⟦ b ⟧ʳ θ))
⟦sbʳ⟧-r {θ = θ} i b (rvar j) with i ≟ᶠ j
... | yes refl = trans (cong (λ x → ⟦ x ⟧ʳ θ) (upd-≡ i b rvar))
                       (sym (upd-≡ i (⟦ b ⟧ʳ θ) (gR θ)))
... | no  ¬p   = trans (cong (λ x → ⟦ x ⟧ʳ θ) (upd-≢ i j b rvar ¬p))
                       (sym (upd-≢ i j (⟦ b ⟧ʳ θ) (gR θ) ¬p))
⟦sbʳ⟧-r i b (rconst ρ) = refl
⟦sbʳ⟧-r i b (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (⟦sbʳ⟧-r i b ρ) (⟦sbʳ⟧-r i b ρ')
⟦sbʳ⟧-r i b (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔ᵣ_ (⟦sbʳ⟧-r i b ρ) (⟦sbʳ⟧-r i b ρ')
⟦sbʳ⟧-r i b ∣ ε ∣̂ᵉ     = cong mapᵉ (sym (⟦lowʳ⟧-e i ε))

mutual

  ⟦sbʳ⟧-v : ∀ {Θ} {θ : Grounding Θ} → (i : RVar Θ) → (b : RExp Θ) → (A : OVType Θ)
          → ⟦ sbʳ-v i b A ⟧ᵛ θ ≡ ⟦ A ⟧ᵛ (lowʳ θ i (⟦ b ⟧ʳ θ))
  ⟦sbʳ⟧-v i b (tvar α)  = refl
  ⟦sbʳ⟧-v i b (Base c)  = refl
  ⟦sbʳ⟧-v i b Unit      = refl
  ⟦sbʳ⟧-v i b Bool      = refl
  ⟦sbʳ⟧-v i b (A |×| B) = cong₂ T._|×|_ (⟦sbʳ⟧-v i b A) (⟦sbʳ⟧-v i b B)
  ⟦sbʳ⟧-v i b Empty     = refl
  ⟦sbʳ⟧-v i b (A ⇒ C)   = cong₂ T._⇒_ (⟦sbʳ⟧-v i b A) (⟦sbʳ⟧-c i b C)
  ⟦sbʳ⟧-v i b ([ ρ ] A) = cong₂ T.[_]_ (⟦sbʳ⟧-r i b ρ) (⟦sbʳ⟧-v i b A)

  ⟦sbʳ⟧-c : ∀ {Θ} {θ : Grounding Θ} → (i : RVar Θ) → (b : RExp Θ) → (C : OCType Θ)
          → ⟦ sbʳ-c i b C ⟧ᶜ θ ≡ ⟦ C ⟧ᶜ (lowʳ θ i (⟦ b ⟧ʳ θ))
  ⟦sbʳ⟧-c i b (A ‼ ε) = cong₂ T._‼_ (⟦sbʳ⟧-v i b A) (sym (⟦lowʳ⟧-e i ε))

invʳ-r : ∀ {Θ} {θ : Grounding Θ} {ρ₀ : R} → (i : RVar Θ) → (ρ : RExp Θ)
       → below (polᵣ-r i ⁻ ρ) ≡ false → ⟦ ρ ⟧ʳ (lowʳ θ i ρ₀) ≡ ⟦ ρ ⟧ʳ θ
invʳ-r {θ = θ} {ρ₀} i (rvar j) q = upd-≢ i j ρ₀ (gR θ) (⌊⌋-false q)
invʳ-r i (rconst ρ) q = refl
invʳ-r i (ρ ·̂ᵣ ρ')  q =
  cong₂ _·ᵣ_ (invʳ-r i ρ (proj₁ d)) (invʳ-r i ρ' (proj₂ d))
  where d = below-∪ (polᵣ-r i ⁻ ρ) (polᵣ-r i ⁻ ρ') q
invʳ-r i (ρ ⊔̂ᵣ ρ')  q =
  cong₂ _⊔ᵣ_ (invʳ-r i ρ (proj₁ d)) (invʳ-r i ρ' (proj₂ d))
  where d = below-∪ (polᵣ-r i ⁻ ρ) (polᵣ-r i ⁻ ρ') q
invʳ-r i ∣ ε ∣̂ᵉ     q = cong mapᵉ (⟦lowʳ⟧-e i ε)

module _ {Θ : Scope} (θ : Grounding Θ) (i : RVar Θ) (ρ₀ : R)
         (le : ρ₀ ≾ᵣ gR θ i) where

  private
    θ⁻ʳ : Grounding Θ
    θ⁻ʳ = lowʳ θ i ρ₀

  monoʳ-r : (s : Sign) → (ρ : RExp Θ) → below (polᵣ-r i s ρ) ≡ false
          → atʳ s (⟦ ρ ⟧ʳ θ⁻ʳ) (⟦ ρ ⟧ʳ θ)
  monoʳ-r ⁺ (rvar j) q with i ≟ᶠ j
  ... | yes refl = subst (λ x → x ≾ᵣ gR θ i) (sym (upd-≡ i ρ₀ (gR θ))) le
  ... | no  ¬p   = subst (λ x → x ≾ᵣ gR θ j) (sym (upd-≢ i j ρ₀ (gR θ) ¬p)) ≾ᵣ-refl
  monoʳ-r ⁻ (rvar j) q =
    ≾ᵣ-reflexive (sym (upd-≢ i j ρ₀ (gR θ) (⌊⌋-false q)))
  monoʳ-r s (rconst ρ) q = atʳ-refl s ρ
  monoʳ-r s (ρ ·̂ᵣ ρ')  q =
    atʳ-· s (monoʳ-r s ρ (proj₁ d)) (monoʳ-r s ρ' (proj₂ d))
    where d = below-∪ (polᵣ-r i s ρ) (polᵣ-r i s ρ') q
  monoʳ-r s (ρ ⊔̂ᵣ ρ')  q =
    atʳ-⊔ s (monoʳ-r s ρ (proj₁ d)) (monoʳ-r s ρ' (proj₂ d))
    where d = below-∪ (polᵣ-r i s ρ) (polᵣ-r i s ρ') q
  monoʳ-r s ∣ ε ∣̂ᵉ     q =
    subst (λ x → atʳ s (mapᵉ x) (mapᵉ (⟦ ε ⟧ᵉ θ))) (sym (⟦lowʳ⟧-e i ε))
          (atʳ-refl s (mapᵉ (⟦ ε ⟧ᵉ θ)))

  mutual

    monoʳ-v : (s : Sign) → (A : OVType Θ) → below (polᵣ-v i s A) ≡ false
            → atᵛ s (⟦ A ⟧ᵛ θ⁻ʳ) (⟦ A ⟧ᵛ θ)
    monoʳ-v s (tvar α)  q = atᵛ-refl s (gTy θ α)
    monoʳ-v s (Base c)  q = atᵛ-refl s (T.Base c)
    monoʳ-v s Unit      q = atᵛ-refl s T.Unit
    monoʳ-v s Bool      q = atᵛ-refl s T.Bool
    monoʳ-v s (A |×| B) q =
      atᵛ-|×| s (monoʳ-v s A (proj₁ d)) (monoʳ-v s B (proj₂ d))
      where d = below-∪ (polᵣ-v i s A) (polᵣ-v i s B) q
    monoʳ-v s Empty     q = atᵛ-refl s T.Empty
    monoʳ-v s (A ⇒ C)   q =
      atᵛ-⇒ s (monoʳ-v (flipˢ s) A (proj₁ d)) (monoʳ-c s C (proj₂ d))
      where d = below-∪ (polᵣ-v i (flipˢ s) A) (polᵣ-c i s C) q
    monoʳ-v s ([ ρ ] A) q =
      atᵛ-box s (monoʳ-r (flipˢ s) ρ (proj₁ d)) (monoʳ-v s A (proj₂ d))
      where d = below-∪ (polᵣ-r i (flipˢ s) ρ) (polᵣ-v i s A) q

    monoʳ-c : (s : Sign) → (C : OCType Θ) → below (polᵣ-c i s C) ≡ false
            → atᶜ s (⟦ C ⟧ᶜ θ⁻ʳ) (⟦ C ⟧ᶜ θ)
    monoʳ-c s (A ‼ ε) q =
      atᶜ-‼ s (monoʳ-v s A q)
              (subst (λ x → atᵉ s x (⟦ ε ⟧ᵉ θ)) (sym (⟦lowʳ⟧-e i ε))
                     (atᵉ-refl s (⟦ ε ⟧ᵉ θ)))

polsᵣ-ord-∈ : ∀ {Θ} → (i : RVar Θ) → (l : List (RExp Θ × RExp Θ))
            → below (polsᵣ-ord i l) ≡ false
            → ∀ {ρ ρ'} → (ρ , ρ') ∈ l
            → (below (polᵣ-r i ⁺ ρ) ≡ false) × (below (polᵣ-r i ⁻ ρ') ≡ false)
polsᵣ-ord-∈ i ((ρ₀ , ρ₀') ∷ l) q (here refl) = proj₁ d₁ , proj₁ d₂
  where d₁ = below-∪ (polᵣ-r i ⁺ ρ₀) (polᵣ-r i ⁻ ρ₀' ∪ᴾ polsᵣ-ord i l) q
        d₂ = below-∪ (polᵣ-r i ⁻ ρ₀') (polsᵣ-ord i l) (proj₂ d₁)
polsᵣ-ord-∈ i ((ρ₀ , ρ₀') ∷ l) q (there m) = polsᵣ-ord-∈ i l (proj₂ d₂) m
  where d₁ = below-∪ (polᵣ-r i ⁺ ρ₀) (polᵣ-r i ⁻ ρ₀' ∪ᴾ polsᵣ-ord i l) q
        d₂ = below-∪ (polᵣ-r i ⁻ ρ₀') (polsᵣ-ord i l) (proj₂ d₁)

polsᵣ-disj-∈ : ∀ {Θ} → (i : RVar Θ) → (l : List (OVType Θ × RExp Θ))
             → below (polsᵣ-disj i l) ≡ false
             → ∀ {A ρ} → (A , ρ) ∈ l → below (polᵣ-r i ⁺ ρ) ≡ false
polsᵣ-disj-∈ i ((A₀ , ρ₀) ∷ l) q (here refl) =
  proj₁ (below-∪ (polᵣ-r i ⁺ ρ₀) (polsᵣ-disj i l) q)
polsᵣ-disj-∈ i ((A₀ , ρ₀) ∷ l) q (there m)   =
  polsᵣ-disj-∈ i l (proj₂ (below-∪ (polᵣ-r i ⁺ ρ₀) (polsᵣ-disj i l) q)) m

joinᵣ : ∀ {Θ} → RExp Θ → List (RExp Θ) → RExp Θ
joinᵣ ρ []        = ρ
joinᵣ ρ (ρ' ∷ ρs) = joinᵣ (ρ ⊔̂ᵣ ρ') ρs

joinᵣ-ub : ∀ {Θ} {θ : Grounding Θ} → (ρ₀ : RExp Θ) → (ρs : List (RExp Θ))
         → ∀ {ρ} → ρ ∈ ρ₀ ∷ ρs → ⟦ ρ ⟧ʳ θ ≾ᵣ ⟦ joinᵣ ρ₀ ρs ⟧ʳ θ
joinᵣ-ub ρ₀ []        (here refl) = ≾ᵣ-refl
joinᵣ-ub {θ = θ} ρ₀ (ρ₁ ∷ ρs) (here refl) =
  ≾ᵣ-trans (⊔ᵣ-ubˡ (⟦ ρ₀ ⟧ʳ θ) (⟦ ρ₁ ⟧ʳ θ))
           (joinᵣ-ub (ρ₀ ⊔̂ᵣ ρ₁) ρs (here refl))
joinᵣ-ub {θ = θ} ρ₀ (ρ₁ ∷ ρs) (there (here refl)) =
  ≾ᵣ-trans (⊔ᵣ-ubʳ (⟦ ρ₀ ⟧ʳ θ) (⟦ ρ₁ ⟧ʳ θ))
           (joinᵣ-ub (ρ₀ ⊔̂ᵣ ρ₁) ρs (here refl))
joinᵣ-ub ρ₀ (ρ₁ ∷ ρs) (there (there m)) = joinᵣ-ub (ρ₀ ⊔̂ᵣ ρ₁) ρs (there m)

joinᵣ-lub : ∀ {Θ} {θ : Grounding Θ} {x : R} → (ρ₀ : RExp Θ) → (ρs : List (RExp Θ))
          → (∀ {ρ} → ρ ∈ ρ₀ ∷ ρs → ⟦ ρ ⟧ʳ θ ≾ᵣ x)
          → ⟦ joinᵣ ρ₀ ρs ⟧ʳ θ ≾ᵣ x
joinᵣ-lub ρ₀ []        k = k (here refl)
joinᵣ-lub ρ₀ (ρ₁ ∷ ρs) k =
  joinᵣ-lub (ρ₀ ⊔̂ᵣ ρ₁) ρs
    (λ { (here refl) → ⊔ᵣ-lub (k (here refl)) (k (there (here refl)))
       ; (there m)   → k (there (there m)) })

joinᵣ-below : ∀ {Θ} → (i : RVar Θ) → (ρ₀ : RExp Θ) → (ρs : List (RExp Θ))
            → below (polᵣ-r i ⁻ (joinᵣ ρ₀ ρs)) ≡ false
            → ∀ {ρ} → ρ ∈ ρ₀ ∷ ρs → below (polᵣ-r i ⁻ ρ) ≡ false
joinᵣ-below i ρ₀ []        q (here refl) = q
joinᵣ-below i ρ₀ (ρ₁ ∷ ρs) q (here refl) =
  proj₁ (below-∪ (polᵣ-r i ⁻ ρ₀) (polᵣ-r i ⁻ ρ₁)
                 (joinᵣ-below i (ρ₀ ⊔̂ᵣ ρ₁) ρs q (here refl)))
joinᵣ-below i ρ₀ (ρ₁ ∷ ρs) q (there (here refl)) =
  proj₂ (below-∪ (polᵣ-r i ⁻ ρ₀) (polᵣ-r i ⁻ ρ₁)
                 (joinᵣ-below i (ρ₀ ⊔̂ᵣ ρ₁) ρs q (here refl)))
joinᵣ-below i ρ₀ (ρ₁ ∷ ρs) q (there (there m)) =
  joinᵣ-below i (ρ₀ ⊔̂ᵣ ρ₁) ρs q (there m)

record Splitʳ {Θ : Scope} (i : RVar Θ) (l : List (RExp Θ × RExp Θ)) : Set where
  constructor splitr
  field
    bndʳ   : RExp Θ
    bndsʳ  : List (RExp Θ)
    restʳ  : List (RExp Θ × RExp Θ)
    memʳ   : ∀ {ρ} → ρ ∈ bndʳ ∷ bndsʳ → (ρ , rvar i) ∈ l
    subʳ   : ∀ {p} → p ∈ restʳ → p ∈ l
    casesʳ : ∀ {ρ ρ'} → (ρ , ρ') ∈ l
           → ((ρ ∈ bndʳ ∷ bndsʳ) × (ρ' ≡ rvar i)) ⊎ ((ρ , ρ') ∈ restʳ)

open Splitʳ

lubʳ : ∀ {Θ} {i : RVar Θ} {l : List (RExp Θ × RExp Θ)} → Splitʳ i l → RExp Θ
lubʳ s = joinᵣ (bndʳ s) (bndsʳ s)

consʳ : ∀ {Θ} {i : RVar Θ} {l : List (RExp Θ × RExp Θ)} {ρ₀ ρ₀'} → Splitʳ i l
      → Splitʳ i ((ρ₀ , ρ₀') ∷ l)
consʳ {ρ₀ = ρ₀} {ρ₀'} s =
  splitr (bndʳ s) (bndsʳ s) ((ρ₀ , ρ₀') ∷ restʳ s)
         (λ m → there (memʳ s m))
         (λ { (here refl) → here refl ; (there m) → there (subʳ s m) })
         (λ { (here refl) → inj₂ (here refl)
            ; (there m)   → [ inj₁ , (λ r → inj₂ (there r)) ]′ (casesʳ s m) })

moreʳ : ∀ {Θ} {i : RVar Θ} {l : List (RExp Θ × RExp Θ)} {ρ₀} → Splitʳ i l
      → Splitʳ i ((ρ₀ , rvar i) ∷ l)
moreʳ {ρ₀ = ρ₀} s =
  splitr ρ₀ (bndʳ s ∷ bndsʳ s) (restʳ s)
         (λ { (here refl) → here refl ; (there m) → there (memʳ s m) })
         (λ m → there (subʳ s m))
         (λ { (here refl) → inj₁ (here refl , refl)
            ; (there m)   → [ (λ { (mb , e) → inj₁ (there mb , e) })
                            , inj₂ ]′ (casesʳ s m) })

oneʳ : ∀ {Θ} {i : RVar Θ} {l : List (RExp Θ × RExp Θ)} {ρ₀}
     → Splitʳ i ((ρ₀ , rvar i) ∷ l)
oneʳ {l = l} {ρ₀} =
  splitr ρ₀ [] l
         (λ { (here refl) → here refl ; (there ()) })
         there
         (λ { (here refl) → inj₁ (here refl , refl) ; (there m) → inj₂ m })

splitʳ : ∀ {Θ} → (i : RVar Θ) → (l : List (RExp Θ × RExp Θ)) → Maybe (Splitʳ i l)
splitʳ i [] = nothing
splitʳ i ((ρ , rvar j) ∷ l) with i ≟ᶠ j
... | yes refl with splitʳ i l
...   | just s  = just (moreʳ s)
...   | nothing = just oneʳ
splitʳ i ((ρ , rvar j) ∷ l) | no _ with splitʳ i l
... | just s  = just (consʳ s)
... | nothing = nothing
splitʳ i ((ρ , rconst _) ∷ l) with splitʳ i l
... | just s  = just (consʳ s)
... | nothing = nothing
splitʳ i ((ρ , _ ·̂ᵣ _) ∷ l) with splitʳ i l
... | just s  = just (consʳ s)
... | nothing = nothing
splitʳ i ((ρ , _ ⊔̂ᵣ _) ∷ l) with splitʳ i l
... | just s  = just (consʳ s)
... | nothing = nothing
splitʳ i ((ρ , ∣ _ ∣̂ᵉ) ∷ l) with splitʳ i l
... | just s  = just (consʳ s)
... | nothing = nothing

stepʳ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ)
      → (s : Splitʳ i (ordᵣ Q))
      → below (polᵣ-r i ⁻ (lubʳ s)) ≡ false
      → below (polᵣᴴ (hyps (ets Q) (subᵥ Q) (restʳ s) (ordₑ Q) (disj Q)) i) ≡ false
      → below (polᵣ-c i ⁺ C) ≡ false
      → Elim C Q
stepʳ {Θ} C Q i s cb cq cc = mkElim Ĉ₀ Q₀ keep₀ real₀ princ₀
  where
    b : RExp Θ
    b = lubʳ s

    Ĉ₀ : OCType Θ
    Ĉ₀ = sbʳ-c i b C

    Q₀ : Hyps Θ
    Q₀ = hyps (ets Q) (subᵥ Q)
              (map (mapᵖ (sbʳ-r i b)) (restʳ s))
              (ordₑ Q)
              (map (mapᵈ (sbʳ-v i b) (sbʳ-r i b)) (disj Q))

    d₁ = below-∪ (polsᵣ-ord i (restʳ s)) (polsᵣ-disj i (disj Q)) cq

    cR : ∀ {ρ ρ'} → (ρ , ρ') ∈ restʳ s
       → (below (polᵣ-r i ⁺ ρ) ≡ false) × (below (polᵣ-r i ⁻ ρ') ≡ false)
    cR = polsᵣ-ord-∈ i (restʳ s) (proj₁ d₁)

    cD : ∀ {A ρ} → (A , ρ) ∈ disj Q → below (polᵣ-r i ⁺ ρ) ≡ false
    cD = polsᵣ-disj-∈ i (disj Q) (proj₂ d₁)

    ∈-mapᵖʳ : ∀ {ρ ρ'} → (ρ , ρ') ∈ restʳ s
            → (sbʳ-r i b ρ , sbʳ-r i b ρ') ∈ map (mapᵖ (sbʳ-r i b)) (restʳ s)
    ∈-mapᵖʳ = ∈-map⁺ (mapᵖ (sbʳ-r i b))

    ∈-mapᵈ' : ∀ {A ρ} → (A , ρ) ∈ disj Q
            → (sbʳ-v i b A , sbʳ-r i b ρ) ∈ map (mapᵈ (sbʳ-v i b) (sbʳ-r i b)) (disj Q)
    ∈-mapᵈ' = ∈-map⁺ (mapᵈ (sbʳ-v i b) (sbʳ-r i b))

    keep₀ : (θ : Grounding Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ Q₀
    keep₀ θ h = mk⊨ᴴ (etOK h) (subOK h) ordR (ordEOK h) dsj
      where
        ρ₀ : R
        ρ₀ = ⟦ b ⟧ʳ θ

        le : ρ₀ ≾ᵣ gR θ i
        le = joinᵣ-lub (bndʳ s) (bndsʳ s) (λ m → ordROK h (memʳ s m))

        ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ (sbʳ-r i b)) (restʳ s)
             → ⟦ ρ ⟧ʳ θ ≾ᵣ ⟦ ρ' ⟧ʳ θ
        ordR m = go (restʳ s) (λ q → q) m
          where
            go : (l : List (RExp Θ × RExp Θ)) → (∀ {p} → p ∈ l → p ∈ restʳ s)
               → ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ (sbʳ-r i b)) l
               → ⟦ ρ ⟧ʳ θ ≾ᵣ ⟦ ρ' ⟧ʳ θ
            go ((ρ' , ρ'') ∷ l) k (here refl) =
              subst₂ _≾ᵣ_ (sym (⟦sbʳ⟧-r i b ρ')) (sym (⟦sbʳ⟧-r i b ρ''))
                (≾ᵣ-trans (monoʳ-r θ i ρ₀ le ⁺ ρ' (proj₁ (cR (k (here refl)))))
                (≾ᵣ-trans (ordROK h (subʳ s (k (here refl))))
                          (monoʳ-r θ i ρ₀ le ⁻ ρ'' (proj₂ (cR (k (here refl)))))))
            go ((ρ' , ρ'') ∷ l) k (there m) = go l (λ q → k (there q)) m

        dsj : ∀ {A ρ} → (A , ρ) ∈ map (mapᵈ (sbʳ-v i b) (sbʳ-r i b)) (disj Q)
            → Eternal (⟦ A ⟧ᵛ θ) ⊎ (⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)
        dsj m = go (disj Q) (λ q → q) m
          where
            go : (l : List (OVType Θ × RExp Θ)) → (∀ {p} → p ∈ l → p ∈ disj Q)
               → ∀ {A ρ} → (A , ρ) ∈ map (mapᵈ (sbʳ-v i b) (sbʳ-r i b)) l
               → Eternal (⟦ A ⟧ᵛ θ) ⊎ (⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)
            go ((A₀ , ρ₀') ∷ l) k (here refl) =
              [ (λ et → inj₁ (subst Eternal (sym (⟦sbʳ⟧-v i b A₀))
                                    (Et-<: (λ γ → <:ᵛ-refl _) A₀ et)))
              , (λ lu → inj₂ (subst (_≾ᵣ uᵣ) (sym (⟦sbʳ⟧-r i b ρ₀'))
                                    (≾ᵣ-trans (monoʳ-r θ i ρ₀ le ⁺ ρ₀'
                                                 (cD (k (here refl)))) lu)))
              ]′ (disjOK h (k (here refl)))
            go ((A₀ , ρ₀') ∷ l) k (there m) = go l (λ q → k (there q)) m

    real₀ : (θ : Grounding Θ) → θ ⊨ᴴ Q₀
          → Σ[ θ' ∈ Grounding Θ ] ((θ' ⊨ᴴ Q) × (⟦ C ⟧ᶜ θ' ≡ ⟦ Ĉ₀ ⟧ᶜ θ))
    real₀ θ h = θ' , mk⊨ᴴ (etOK h) (subOK h) ordR ordE dsj , sym (⟦sbʳ⟧-c i b C)
      where
        θ' : Grounding Θ
        θ' = lowʳ θ i (⟦ b ⟧ʳ θ)

        ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → ⟦ ε ⟧ᵉ θ' ≾ₑ ⟦ ε' ⟧ᵉ θ'
        ordE {ε} {ε'} m =
          subst₂ _≾ₑ_ (sym (⟦lowʳ⟧-e i ε)) (sym (⟦lowʳ⟧-e i ε')) (ordEOK h m)

        ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → ⟦ ρ ⟧ʳ θ' ≾ᵣ ⟦ ρ' ⟧ʳ θ'
        ordR {ρ} {ρ'} m with casesʳ s m
        ... | inj₁ (mb , refl) =
              subst₂ _≾ᵣ_ (sym (invʳ-r i ρ (joinᵣ-below i (bndʳ s) (bndsʳ s) cb mb)))
                          (sym (upd-≡ i (⟦ b ⟧ʳ θ) (gR θ)))
                     (joinᵣ-ub {θ = θ} (bndʳ s) (bndsʳ s) mb)
        ... | inj₂ m' =
              subst₂ _≾ᵣ_ (⟦sbʳ⟧-r i b ρ) (⟦sbʳ⟧-r i b ρ') (ordROK h (∈-mapᵖʳ m'))

        dsj : ∀ {A ρ} → (A , ρ) ∈ disj Q
            → Eternal (⟦ A ⟧ᵛ θ') ⊎ (⟦ ρ ⟧ʳ θ' ≾ᵣ uᵣ)
        dsj {A} {ρ} m =
          [ (λ et → inj₁ (subst Eternal (⟦sbʳ⟧-v i b A) et))
          , (λ lu → inj₂ (subst (_≾ᵣ uᵣ) (⟦sbʳ⟧-r i b ρ) lu))
          ]′ (disjOK h (∈-mapᵈ' m))

    princ₀ : (θ : Grounding Θ) → θ ⊨ᴴ Q → ⟦ Ĉ₀ ⟧ᶜ θ <:ᶜ ⟦ C ⟧ᶜ θ
    princ₀ θ h =
      subst (_<:ᶜ ⟦ C ⟧ᶜ θ) (sym (⟦sbʳ⟧-c i b C))
            (monoʳ-c θ i (⟦ b ⟧ʳ θ)
                     (joinᵣ-lub (bndʳ s) (bndsʳ s) (λ m → ordROK h (memʳ s m)))
                     ⁺ C cc)

stepʳ? : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (i : RVar Θ) → Maybe (Elim C Q)
stepʳ? C Q i with splitʳ i (ordᵣ Q)
... | nothing = nothing
... | just s
    with below (polᵣ-r i ⁻ (lubʳ s)) in c1
       | below (polᵣᴴ (hyps (ets Q) (subᵥ Q) (restʳ s) (ordₑ Q) (disj Q)) i) in c2
       | below (polᵣ-c i ⁺ C) in c3
...   | false | false | false = just (stepʳ C Q i s c1 c2 c3)
...   | _     | _     | _     = nothing

firstʳ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → List (RVar Θ) → Maybe (Elim C Q)
firstʳ C Q []       = nothing
firstʳ C Q (i ∷ is) with stepʳ? C Q i
... | just r  = just r
... | nothing = firstʳ C Q is

-- The bound of a type variable is another type variable, so the
-- substitution acts on the eternality and subtyping atoms too.

idᶠ : ∀ {n} → Fin n → Fin n
idᶠ β = β

mutual

  sbᵗ-v : ∀ {Θ} → TyVar Θ → TyVar Θ → OVType Θ → OVType Θ
  sbᵗ-v α δ (tvar β)  = tvar (upd α δ idᶠ β)
  sbᵗ-v α δ (Base c)  = Base c
  sbᵗ-v α δ Unit      = Unit
  sbᵗ-v α δ Bool      = Bool
  sbᵗ-v α δ (A |×| B) = sbᵗ-v α δ A |×| sbᵗ-v α δ B
  sbᵗ-v α δ Empty     = Empty
  sbᵗ-v α δ (A ⇒ C)   = sbᵗ-v α δ A ⇒ sbᵗ-c α δ C
  sbᵗ-v α δ ([ ρ ] A) = [ ρ ] sbᵗ-v α δ A

  sbᵗ-c : ∀ {Θ} → TyVar Θ → TyVar Θ → OCType Θ → OCType Θ
  sbᵗ-c α δ (A ‼ ε) = sbᵗ-v α δ A ‼ ε

lowᵗ : ∀ {Θ} → Grounding Θ → TyVar Θ → VType → Grounding Θ
lowᵗ θ α B = grounding (upd α B (gTy θ)) (gR θ) (gE θ)

⟦lowᵗ⟧-e : ∀ {Θ} {θ : Grounding Θ} {B : VType} → (α : TyVar Θ) → (ε : EExp Θ)
         → ⟦ ε ⟧ᵉ (lowᵗ θ α B) ≡ ⟦ ε ⟧ᵉ θ
⟦lowᵗ⟧-e α (evar j)   = refl
⟦lowᵗ⟧-e α (econst ε) = refl
⟦lowᵗ⟧-e α (ε ·̂ₑ ε')  = cong₂ _·ₑ_ (⟦lowᵗ⟧-e α ε) (⟦lowᵗ⟧-e α ε')
⟦lowᵗ⟧-e α (ε ⊔̂ₑ ε')  = cong₂ _⊔ₑ_ (⟦lowᵗ⟧-e α ε) (⟦lowᵗ⟧-e α ε')

⟦lowᵗ⟧-r : ∀ {Θ} {θ : Grounding Θ} {B : VType} → (α : TyVar Θ) → (ρ : RExp Θ)
         → ⟦ ρ ⟧ʳ (lowᵗ θ α B) ≡ ⟦ ρ ⟧ʳ θ
⟦lowᵗ⟧-r α (rvar j)   = refl
⟦lowᵗ⟧-r α (rconst ρ) = refl
⟦lowᵗ⟧-r α (ρ ·̂ᵣ ρ')  = cong₂ _·ᵣ_ (⟦lowᵗ⟧-r α ρ) (⟦lowᵗ⟧-r α ρ')
⟦lowᵗ⟧-r α (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔ᵣ_ (⟦lowᵗ⟧-r α ρ) (⟦lowᵗ⟧-r α ρ')
⟦lowᵗ⟧-r α ∣ ε ∣̂ᵉ     = cong mapᵉ (⟦lowᵗ⟧-e α ε)

mutual

  ⟦sbᵗ⟧-v : ∀ {Θ} {θ : Grounding Θ} → (α δ : TyVar Θ) → (A : OVType Θ)
          → ⟦ sbᵗ-v α δ A ⟧ᵛ θ ≡ ⟦ A ⟧ᵛ (lowᵗ θ α (gTy θ δ))
  ⟦sbᵗ⟧-v {θ = θ} α δ (tvar β) with α ≟ᶠ β
  ... | yes refl = trans (cong (gTy θ) (upd-≡ α δ idᶠ))
                         (sym (upd-≡ α (gTy θ δ) (gTy θ)))
  ... | no  ¬p   = trans (cong (gTy θ) (upd-≢ α β δ idᶠ ¬p))
                         (sym (upd-≢ α β (gTy θ δ) (gTy θ) ¬p))
  ⟦sbᵗ⟧-v α δ (Base c)  = refl
  ⟦sbᵗ⟧-v α δ Unit      = refl
  ⟦sbᵗ⟧-v α δ Bool      = refl
  ⟦sbᵗ⟧-v α δ (A |×| B) = cong₂ T._|×|_ (⟦sbᵗ⟧-v α δ A) (⟦sbᵗ⟧-v α δ B)
  ⟦sbᵗ⟧-v α δ Empty     = refl
  ⟦sbᵗ⟧-v α δ (A ⇒ C)   = cong₂ T._⇒_ (⟦sbᵗ⟧-v α δ A) (⟦sbᵗ⟧-c α δ C)
  ⟦sbᵗ⟧-v α δ ([ ρ ] A) =
    cong₂ T.[_]_ (sym (⟦lowᵗ⟧-r α ρ)) (⟦sbᵗ⟧-v α δ A)

  ⟦sbᵗ⟧-c : ∀ {Θ} {θ : Grounding Θ} → (α δ : TyVar Θ) → (C : OCType Θ)
          → ⟦ sbᵗ-c α δ C ⟧ᶜ θ ≡ ⟦ C ⟧ᶜ (lowᵗ θ α (gTy θ δ))
  ⟦sbᵗ⟧-c α δ (A ‼ ε) = cong₂ T._‼_ (⟦sbᵗ⟧-v α δ A) (sym (⟦lowᵗ⟧-e α ε))

module _ {Θ : Scope} (θ : Grounding Θ) (α : TyVar Θ) (B : VType)
         (le : B <:ᵛ gTy θ α) where

  private
    θ⁻ᵗ : Grounding Θ
    θ⁻ᵗ = lowᵗ θ α B

  mutual

    monoᵗ-v : (s : Sign) → (A : OVType Θ) → below (polₜ-v α s A) ≡ false
            → atᵛ s (⟦ A ⟧ᵛ θ⁻ᵗ) (⟦ A ⟧ᵛ θ)
    monoᵗ-v ⁺ (tvar β) q with α ≟ᶠ β
    ... | yes refl = subst (λ x → x <:ᵛ gTy θ α) (sym (upd-≡ α B (gTy θ))) le
    ... | no  ¬p   = subst (λ x → x <:ᵛ gTy θ β) (sym (upd-≢ α β B (gTy θ) ¬p))
                           (<:ᵛ-refl (gTy θ β))
    monoᵗ-v ⁻ (tvar β) q =
      subst (λ x → gTy θ β <:ᵛ x) (sym (upd-≢ α β B (gTy θ) (⌊⌋-false q)))
            (<:ᵛ-refl (gTy θ β))
    monoᵗ-v s (Base c)  q = atᵛ-refl s (T.Base c)
    monoᵗ-v s Unit      q = atᵛ-refl s T.Unit
    monoᵗ-v s Bool      q = atᵛ-refl s T.Bool
    monoᵗ-v s (A |×| B') q =
      atᵛ-|×| s (monoᵗ-v s A (proj₁ d)) (monoᵗ-v s B' (proj₂ d))
      where d = below-∪ (polₜ-v α s A) (polₜ-v α s B') q
    monoᵗ-v s Empty     q = atᵛ-refl s T.Empty
    monoᵗ-v s (A ⇒ C)   q =
      atᵛ-⇒ s (monoᵗ-v (flipˢ s) A (proj₁ d)) (monoᵗ-c s C (proj₂ d))
      where d = below-∪ (polₜ-v α (flipˢ s) A) (polₜ-c α s C) q
    monoᵗ-v s ([ ρ ] A) q =
      subst (λ x → atᵛ s (T.[ x ] ⟦ A ⟧ᵛ θ⁻ᵗ) (T.[ ⟦ ρ ⟧ʳ θ ] ⟦ A ⟧ᵛ θ))
            (sym (⟦lowᵗ⟧-r α ρ))
            (atᵛ-box s (atʳ-refl (flipˢ s) (⟦ ρ ⟧ʳ θ)) (monoᵗ-v s A q))

    monoᵗ-c : (s : Sign) → (C : OCType Θ) → below (polₜ-c α s C) ≡ false
            → atᶜ s (⟦ C ⟧ᶜ θ⁻ᵗ) (⟦ C ⟧ᶜ θ)
    monoᵗ-c s (A ‼ ε) q =
      subst (λ x → atᶜ s (⟦ A ⟧ᵛ θ⁻ᵗ T.‼ x) (⟦ A ⟧ᵛ θ T.‼ ⟦ ε ⟧ᵉ θ))
            (sym (⟦lowᵗ⟧-e α ε))
            (atᶜ-‼ s (monoᵗ-v s A q) (atᵉ-refl s (⟦ ε ⟧ᵉ θ)))

Et-low : ∀ {Θ} → (θ : Grounding Θ) → (α : TyVar Θ) → (B : VType)
       → B <:ᵛ gTy θ α → (A : OVType Θ)
       → Eternal (⟦ A ⟧ᵛ θ) → Eternal (⟦ A ⟧ᵛ (lowᵗ θ α B))
Et-low θ α B le = Et-<: (λ γ → monoᵗ-v θ α B le ⁺ (tvar γ) refl)

polsₜ-sub-∈ : ∀ {n} → (α : Fin n) → (l : List (Fin n × Fin n))
            → below (polsₜ-sub α l) ≡ false
            → ∀ {β γ} → (β , γ) ∈ l → ⌊ α ≟ᶠ γ ⌋ ≡ false
polsₜ-sub-∈ α ((β₀ , γ₀) ∷ l) q (here refl) = proj₁ d₂
  where d₁ = below-∪ (atˢ ⁺ ⌊ α ≟ᶠ β₀ ⌋) (atˢ ⁻ ⌊ α ≟ᶠ γ₀ ⌋ ∪ᴾ polsₜ-sub α l) q
        d₂ = below-∪ (atˢ ⁻ ⌊ α ≟ᶠ γ₀ ⌋) (polsₜ-sub α l) (proj₂ d₁)
polsₜ-sub-∈ α ((β₀ , γ₀) ∷ l) q (there m) = polsₜ-sub-∈ α l (proj₂ d₂) m
  where d₁ = below-∪ (atˢ ⁺ ⌊ α ≟ᶠ β₀ ⌋) (atˢ ⁻ ⌊ α ≟ᶠ γ₀ ⌋ ∪ᴾ polsₜ-sub α l) q
        d₂ = below-∪ (atˢ ⁻ ⌊ α ≟ᶠ γ₀ ⌋) (polsₜ-sub α l) (proj₂ d₁)

record Splitᵗ {n : ℕ} (α : Fin n) (l : List (Fin n × Fin n)) : Set where
  constructor splitt
  field
    bndᵗ   : Fin n
    restᵗ  : List (Fin n × Fin n)
    memᵗ   : (bndᵗ , α) ∈ l
    subᵗ   : ∀ {p} → p ∈ restᵗ → p ∈ l
    casesᵗ : ∀ {p} → p ∈ l → (p ≡ (bndᵗ , α)) ⊎ (p ∈ restᵗ)

open Splitᵗ

consᵗ : ∀ {n} {α : Fin n} {l : List (Fin n × Fin n)} {p} → Splitᵗ α l
      → Splitᵗ α (p ∷ l)
consᵗ {p = p} s =
  splitt (bndᵗ s) (p ∷ restᵗ s) (there (memᵗ s))
         (λ { (here refl) → here refl ; (there m) → there (subᵗ s m) })
         (λ { (here refl) → inj₂ (here refl)
            ; (there m)   → [ inj₁ , (λ r → inj₂ (there r)) ]′ (casesᵗ s m) })

splitᵗ : ∀ {n} → (α : Fin n) → (l : List (Fin n × Fin n)) → Maybe (Splitᵗ α l)
splitᵗ α [] = nothing
splitᵗ α ((β , γ) ∷ l) with α ≟ᶠ γ
... | yes refl = just (splitt β l (here refl) there
                              (λ { (here refl) → inj₁ refl ; (there m) → inj₂ m }))
... | no  _    with splitᵗ α l
...   | just s  = just (consᵗ s)
...   | nothing = nothing

stepᵗ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (α : TyVar Θ)
      → (s : Splitᵗ α (subᵥ Q))
      → below (polₜ-v {Θ} α ⁻ (tvar (bndᵗ s))) ≡ false
      → below (polₜᴴ (hyps (ets Q) (restᵗ s) (ordᵣ Q) (ordₑ Q) (disj Q)) α) ≡ false
      → below (polₜ-c α ⁺ C) ≡ false
      → Elim C Q
stepᵗ {Θ} C Q α s cb cq cc = mkElim Ĉ₀ Q₀ keep₀ real₀ princ₀
  where
    δ : TyVar Θ
    δ = bndᵗ s

    Ĉ₀ : OCType Θ
    Ĉ₀ = sbᵗ-c α δ C

    Q₀ : Hyps Θ
    Q₀ = hyps (map (upd α δ idᶠ) (ets Q))
              (map (mapᵖ (upd α δ idᶠ)) (restᵗ s))
              (ordᵣ Q) (ordₑ Q)
              (map (mapᵈ (sbᵗ-v α δ) (λ ρ → ρ)) (disj Q))

    α≢δ : ¬ (α ≡ δ)
    α≢δ = ⌊⌋-false cb

    cS : ∀ {β γ} → (β , γ) ∈ restᵗ s → ⌊ α ≟ᶠ γ ⌋ ≡ false
    cS = polsₜ-sub-∈ α (restᵗ s) cq

    tvsb : (θ : Grounding Θ) → (β : TyVar Θ)
         → gTy θ (upd α δ idᶠ β) ≡ gTy (lowᵗ θ α (gTy θ δ)) β
    tvsb θ β = ⟦sbᵗ⟧-v {Θ} {θ} α δ (tvar β)

    keep₀ : (θ : Grounding Θ) → θ ⊨ᴴ Q → θ ⊨ᴴ Q₀
    keep₀ θ h = mk⊨ᴴ et' sub' (ordROK h) (ordEOK h) dsj
      where
        le : gTy θ δ <:ᵛ gTy θ α
        le = subOK h (memᵗ s)

        et' : ∀ {x} → x ∈ map (upd α δ idᶠ) (ets Q) → Eternal (gTy θ x)
        et' m = go (ets Q) (λ q → q) m
          where
            go : (l : List (TyVar Θ)) → (∀ {β} → β ∈ l → β ∈ ets Q)
               → ∀ {x} → x ∈ map (upd α δ idᶠ) l → Eternal (gTy θ x)
            go (β ∷ l) k (here refl) =
              subst Eternal (sym (tvsb θ β))
                    (Et-low θ α (gTy θ δ) le (tvar β) (etOK h (k (here refl))))
            go (β ∷ l) k (there m) = go l (λ q → k (there q)) m

        sub' : ∀ {x y} → (x , y) ∈ map (mapᵖ (upd α δ idᶠ)) (restᵗ s)
             → gTy θ x <:ᵛ gTy θ y
        sub' m = go (restᵗ s) (λ q → q) m
          where
            go : (l : List (TyVar Θ × TyVar Θ)) → (∀ {p} → p ∈ l → p ∈ restᵗ s)
               → ∀ {x y} → (x , y) ∈ map (mapᵖ (upd α δ idᶠ)) l
               → gTy θ x <:ᵛ gTy θ y
            go ((β , γ) ∷ l) k (here refl) =
              subst₂ _<:ᵛ_ (sym (tvsb θ β)) (sym (tvsb θ γ))
                (<:ᵛ-trans (monoᵗ-v θ α (gTy θ δ) le ⁺ (tvar β) refl)
                (<:ᵛ-trans (subOK h (subᵗ s (k (here refl))))
                           (monoᵗ-v θ α (gTy θ δ) le ⁻ (tvar γ) (cS (k (here refl))))))
            go ((β , γ) ∷ l) k (there m) = go l (λ q → k (there q)) m

        dsj : ∀ {A ρ} → (A , ρ) ∈ map (mapᵈ (sbᵗ-v α δ) (λ ρ → ρ)) (disj Q)
            → Eternal (⟦ A ⟧ᵛ θ) ⊎ (⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)
        dsj m = go (disj Q) (λ q → q) m
          where
            go : (l : List (OVType Θ × RExp Θ)) → (∀ {p} → p ∈ l → p ∈ disj Q)
               → ∀ {A ρ} → (A , ρ) ∈ map (mapᵈ (sbᵗ-v α δ) (λ ρ → ρ)) l
               → Eternal (⟦ A ⟧ᵛ θ) ⊎ (⟦ ρ ⟧ʳ θ ≾ᵣ uᵣ)
            go ((A₀ , ρ₀) ∷ l) k (here refl) =
              [ (λ et → inj₁ (subst Eternal (sym (⟦sbᵗ⟧-v α δ A₀))
                                    (Et-low θ α (gTy θ δ) le A₀ et)))
              , (λ lu → inj₂ lu) ]′ (disjOK h (k (here refl)))
            go ((A₀ , ρ₀) ∷ l) k (there m) = go l (λ q → k (there q)) m

    real₀ : (θ : Grounding Θ) → θ ⊨ᴴ Q₀
          → Σ[ θ' ∈ Grounding Θ ] ((θ' ⊨ᴴ Q) × (⟦ C ⟧ᶜ θ' ≡ ⟦ Ĉ₀ ⟧ᶜ θ))
    real₀ θ h = θ' , mk⊨ᴴ et' sub' ordR ordE dsj , sym (⟦sbᵗ⟧-c α δ C)
      where
        θ' : Grounding Θ
        θ' = lowᵗ θ α (gTy θ δ)

        et' : ∀ {β} → β ∈ ets Q → Eternal (gTy θ' β)
        et' {β} m = subst Eternal (tvsb θ β)
                          (etOK h (∈-map⁺ (upd α δ idᶠ) m))

        sub' : ∀ {β γ} → (β , γ) ∈ subᵥ Q → gTy θ' β <:ᵛ gTy θ' γ
        sub' {β} {γ} m with casesᵗ s m
        ... | inj₁ refl =
              subst₂ _<:ᵛ_ (sym (upd-≢ α δ (gTy θ δ) (gTy θ) α≢δ))
                           (sym (upd-≡ α (gTy θ δ) (gTy θ)))
                     (<:ᵛ-refl (gTy θ δ))
        ... | inj₂ m' =
              subst₂ _<:ᵛ_ (tvsb θ β) (tvsb θ γ)
                     (subOK h (∈-map⁺ (mapᵖ (upd α δ idᶠ)) m'))

        ordR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → ⟦ ρ ⟧ʳ θ' ≾ᵣ ⟦ ρ' ⟧ʳ θ'
        ordR {ρ} {ρ'} m =
          subst₂ _≾ᵣ_ (sym (⟦lowᵗ⟧-r α ρ)) (sym (⟦lowᵗ⟧-r α ρ')) (ordROK h m)

        ordE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → ⟦ ε ⟧ᵉ θ' ≾ₑ ⟦ ε' ⟧ᵉ θ'
        ordE {ε} {ε'} m =
          subst₂ _≾ₑ_ (sym (⟦lowᵗ⟧-e α ε)) (sym (⟦lowᵗ⟧-e α ε')) (ordEOK h m)

        dsj : ∀ {A ρ} → (A , ρ) ∈ disj Q
            → Eternal (⟦ A ⟧ᵛ θ') ⊎ (⟦ ρ ⟧ʳ θ' ≾ᵣ uᵣ)
        dsj {A} {ρ} m =
          [ (λ et → inj₁ (subst Eternal (⟦sbᵗ⟧-v α δ A) et))
          , (λ lu → inj₂ (subst (_≾ᵣ uᵣ) (sym (⟦lowᵗ⟧-r α ρ)) lu))
          ]′ (disjOK h (∈-map⁺ (mapᵈ (sbᵗ-v α δ) (λ ρ → ρ)) m))

    princ₀ : (θ : Grounding Θ) → θ ⊨ᴴ Q → ⟦ Ĉ₀ ⟧ᶜ θ <:ᶜ ⟦ C ⟧ᶜ θ
    princ₀ θ h =
      subst (_<:ᶜ ⟦ C ⟧ᶜ θ) (sym (⟦sbᵗ⟧-c α δ C))
            (monoᵗ-c θ α (gTy θ δ) (subOK h (memᵗ s)) ⁺ C cc)

stepᵗ? : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → (α : TyVar Θ) → Maybe (Elim C Q)
stepᵗ? {Θ} C Q α with splitᵗ α (subᵥ Q)
... | nothing = nothing
... | just s
    with below (polₜ-v {Θ} α ⁻ (tvar (bndᵗ s))) in c1
       | below (polₜᴴ (hyps (ets Q) (restᵗ s) (ordᵣ Q) (ordₑ Q) (disj Q)) α) in c2
       | below (polₜ-c α ⁺ C) in c3
...   | false | false | false = just (stepᵗ C Q α s c1 c2 c3)
...   | _     | _     | _     = nothing

firstᵗ : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → List (TyVar Θ) → Maybe (Elim C Q)
firstᵗ C Q []       = nothing
firstᵗ C Q (α ∷ αs) with stepᵗ? C Q α
... | just r  = just r
... | nothing = firstᵗ C Q αs

anyStep : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → Maybe (Elim C Q)
anyStep {Θ} C Q with firstᵉ C Q (fins (nE Θ))
... | just r  = just r
... | nothing with firstʳ C Q (fins (nR Θ))
...   | just r  = just r
...   | nothing = firstᵗ C Q (fins (nTy Θ))

reduce : ∀ {Θ} → ℕ → (C : OCType Θ) → (Q : Hyps Θ) → Elim C Q
reduce zero    C Q = idElim C Q
reduce (suc n) C Q with anyStep C Q
... | nothing = idElim C Q
... | just r  = r ⨾ᴱ reduce n (Ĉ r) (Q̂ r)

-- One round per unknown suffices: a step removes one

eliminate : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → Elim C Q
eliminate {Θ} C Q = reduce (nE Θ + nR Θ + nTy Θ) C Q
