------------------------------------------------------------------
-- Strengthening a report to the variables occurring in it        --
--                                                                --
-- A mask keeps some variables of each sort. The kept ones form a --
-- smaller scope, embedded back in order by a renaming `ι`, and   --
-- an expression all of whose variables are kept is strengthened  --
-- along it: renaming the result along `ι` gives the expression   --
-- back on the nose. A grounding of the smaller scope extends     --
-- along `ι`, by any value on the variables dropped.              --
--                                                                --
-- `strengthen` takes the mask of the variables occurring in a    --
-- type or a hypothesis set, and strengthens both along it.       --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false; _∨_; if_then_else_) renaming (Bool to 𝔹)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using () renaming (map to map⊎)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Strengthen (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types     S using (Eternal)
open import Syntax.Subtyping S using (_<:ᵛ_; _<:ᶜ_)

import Syntax.Types S as T

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Grounding S

open import TypeInference.SolverImpl.Eliminate S using (Elim; Ĉ; Q̂; keep; real; princ)
open import TypeInference.SolverImpl.Core.Occurs S
  using (occᵗ-v; occᵗ-c; occʳ-r; occʳ-v; occʳ-c; occᵉ-e; occᵉ-r; occᵉ-v; occᵉ-c)

------------------------------------------------------------------------
-- Thinning by a mask
--
-- `count p` variables are kept, `emb p` embeds them in order, `str p`
-- finds a kept variable among them, and `ext p` extends a family on the
-- kept variables by a default on the others.

count : ∀ {n} → (Fin n → 𝔹) → ℕ
count {zero}  p = zero
count {suc n} p = if p zero then suc (count (λ i → p (suc i)))
                            else count (λ i → p (suc i))

embC : ∀ {k n} → (b : 𝔹) → (Fin k → Fin n) → Fin (if b then suc k else k) → Fin (suc n)
embC true  f zero    = zero
embC true  f (suc j) = suc (f j)
embC false f j       = suc (f j)

emb : ∀ {n} → (p : Fin n → 𝔹) → Fin (count p) → Fin n
emb {zero}  p ()
emb {suc n} p = embC (p zero) (emb (λ i → p (suc i)))

str₀ : ∀ {k} → (b : 𝔹) → b ≡ true → Fin (if b then suc k else k)
str₀ true  _ = zero

strₛ : ∀ {k} → (b : 𝔹) → Fin k → Fin (if b then suc k else k)
strₛ true  j = suc j
strₛ false j = j

str : ∀ {n} → (p : Fin n → 𝔹) → (i : Fin n) → p i ≡ true → Fin (count p)
str {suc n} p zero    h = str₀ (p zero) h
str {suc n} p (suc i) h = strₛ (p zero) (str (λ i → p (suc i)) i h)

emb-str : ∀ {n} → (p : Fin n → 𝔹) → (i : Fin n) → (h : p i ≡ true)
        → emb p (str p i h) ≡ i
emb-str {suc n} p zero    h = go (p zero) h
  where
    go : (b : 𝔹) → (h : b ≡ true)
       → embC b (emb (λ i → p (suc i))) (str₀ b h) ≡ zero
    go true _ = refl
emb-str {suc n} p (suc i) h =
  trans (go (p zero) (str p' i h)) (cong suc (emb-str p' i h))
  where
    p' : Fin n → 𝔹
    p' j = p (suc j)

    go : (b : 𝔹) → (j : Fin (count p'))
       → embC b (emb p') (strₛ b j) ≡ suc (emb p' j)
    go true  j = refl
    go false j = refl

extC : ∀ {k n} {A : Set} → (b : 𝔹) → ((Fin k → A) → Fin n → A) → A
     → (Fin (if b then suc k else k) → A) → Fin (suc n) → A
extC true  e a g zero    = g zero
extC true  e a g (suc i) = e (λ j → g (suc j)) i
extC false e a g zero    = a
extC false e a g (suc i) = e g i

ext : ∀ {n} {A : Set} → (p : Fin n → 𝔹) → A → (Fin (count p) → A) → Fin n → A
ext {zero}  p a g ()
ext {suc n} p a g = extC (p zero) (ext (λ i → p (suc i)) a) a g

ext-emb : ∀ {n} {A : Set} → (p : Fin n → 𝔹) → (a : A) → (g : Fin (count p) → A)
        → (j : Fin (count p)) → ext p a g (emb p j) ≡ g j
ext-emb {suc n} {A} p a g j = go (p zero) g j
  where
    p' : Fin n → 𝔹
    p' i = p (suc i)

    go : (b : 𝔹) → (g : Fin (if b then suc (count p') else count p') → A)
       → (j : Fin (if b then suc (count p') else count p'))
       → extC b (ext p' a) a g (embC b (emb p') j) ≡ g j
    go true  g zero    = refl
    go true  g (suc j) = ext-emb p' a (λ j → g (suc j)) j
    go false g j       = ext-emb p' a g j

------------------------------------------------------------------------
-- Sets of variables, as masks of the three sorts

record Vars (Θ : Scope) : Set where
  constructor vars
  field
    vᵗ : TyVar Θ → 𝔹
    vʳ : RVar Θ → 𝔹
    vᵉ : EVar Θ → 𝔹

open Vars public

infixr 6 _∪ᵛ_
infix  4 _⊆ᵛ_

∅ᵛ : ∀ {Θ} → Vars Θ
∅ᵛ = vars (λ _ → false) (λ _ → false) (λ _ → false)

_∪ᵛ_ : ∀ {Θ} → Vars Θ → Vars Θ → Vars Θ
V ∪ᵛ W = vars (λ α → vᵗ V α ∨ vᵗ W α) (λ i → vʳ V i ∨ vʳ W i) (λ i → vᵉ V i ∨ vᵉ W i)

⋃ᵛ : ∀ {Θ} {X : Set} → (X → Vars Θ) → List X → Vars Θ
⋃ᵛ f []       = ∅ᵛ
⋃ᵛ f (x ∷ xs) = f x ∪ᵛ ⋃ᵛ f xs

record _⊆ᵛ_ {Θ : Scope} (V W : Vars Θ) : Set where
  constructor mk⊆ᵛ
  field
    ⊆ᵗ : ∀ α → vᵗ V α ≡ true → vᵗ W α ≡ true
    ⊆ʳ : ∀ i → vʳ V i ≡ true → vʳ W i ≡ true
    ⊆ᵉ : ∀ i → vᵉ V i ≡ true → vᵉ W i ≡ true

open _⊆ᵛ_ public

∨-inˡ : ∀ {a b} → a ≡ true → a ∨ b ≡ true
∨-inˡ refl = refl

∨-inʳ : ∀ a {b} → b ≡ true → a ∨ b ≡ true
∨-inʳ true  _ = refl
∨-inʳ false h = h

⊆-∪ˡ : ∀ {Θ} (V W : Vars Θ) {M : Vars Θ} → V ∪ᵛ W ⊆ᵛ M → V ⊆ᵛ M
⊆-∪ˡ V W h = mk⊆ᵛ (λ α o → ⊆ᵗ h α (∨-inˡ o)) (λ i o → ⊆ʳ h i (∨-inˡ o))
                  (λ i o → ⊆ᵉ h i (∨-inˡ o))

⊆-∪ʳ : ∀ {Θ} (V W : Vars Θ) {M : Vars Θ} → V ∪ᵛ W ⊆ᵛ M → W ⊆ᵛ M
⊆-∪ʳ V W h = mk⊆ᵛ (λ α o → ⊆ᵗ h α (∨-inʳ (vᵗ V α) o))
                  (λ i o → ⊆ʳ h i (∨-inʳ (vʳ V i) o))
                  (λ i o → ⊆ᵉ h i (∨-inʳ (vᵉ V i) o))

⊆-refl : ∀ {Θ} {V : Vars Θ} → V ⊆ᵛ V
⊆-refl = mk⊆ᵛ (λ _ o → o) (λ _ o → o) (λ _ o → o)

≟-self : ∀ {n} → (i : Fin n) → ⌊ i ≟ᶠ i ⌋ ≡ true
≟-self i with i ≟ᶠ i
... | yes _  = refl
... | no  ¬p = ⊥-elim (¬p refl)

------------------------------------------------------------------------
-- The variables occurring in an expression, a type, and a hypothesis set

fvᵉ : ∀ {Θ} → EExp Θ → Vars Θ
fvᵉ ε = vars (λ _ → false) (λ _ → false) (λ i → occᵉ-e i ε)

fvʳ : ∀ {Θ} → RExp Θ → Vars Θ
fvʳ ρ = vars (λ _ → false) (λ i → occʳ-r i ρ) (λ i → occᵉ-r i ρ)

fvᵛ : ∀ {Θ} → OVType Θ → Vars Θ
fvᵛ A = vars (λ α → occᵗ-v α A) (λ i → occʳ-v i A) (λ i → occᵉ-v i A)

fvᶜ : ∀ {Θ} → OCType Θ → Vars Θ
fvᶜ C = vars (λ α → occᵗ-c α C) (λ i → occʳ-c i C) (λ i → occᵉ-c i C)

fvᵗ : ∀ {Θ} → TyVar Θ → Vars Θ
fvᵗ α = fvᵛ (tvar α)

fvᵗᵗ : ∀ {Θ} → TyVar Θ × TyVar Θ → Vars Θ
fvᵗᵗ (α , β) = fvᵗ α ∪ᵛ fvᵗ β

fvʳʳ : ∀ {Θ} → RExp Θ × RExp Θ → Vars Θ
fvʳʳ (ρ , ρ') = fvʳ ρ ∪ᵛ fvʳ ρ'

fvᵉᵉ : ∀ {Θ} → EExp Θ × EExp Θ → Vars Θ
fvᵉᵉ (ε , ε') = fvᵉ ε ∪ᵛ fvᵉ ε'

fvᵛʳ : ∀ {Θ} → OVType Θ × RExp Θ → Vars Θ
fvᵛʳ (A , ρ) = fvᵛ A ∪ᵛ fvʳ ρ

fvᴴ : ∀ {Θ} → Hyps Θ → Vars Θ
fvᴴ Q = ⋃ᵛ fvᵗ (ets Q) ∪ᵛ ⋃ᵛ fvᵗᵗ (subᵥ Q) ∪ᵛ ⋃ᵛ fvʳʳ (ordᵣ Q)
        ∪ᵛ ⋃ᵛ fvᵉᵉ (ordₑ Q) ∪ᵛ ⋃ᵛ fvᵛʳ (disj Q)

hyps-≡ : ∀ {Θ} {a a' : List (TyVar Θ)} {b b' : List (TyVar Θ × TyVar Θ)}
           {c c' : List (RExp Θ × RExp Θ)} {d d' : List (EExp Θ × EExp Θ)}
           {e e' : List (OVType Θ × RExp Θ)}
       → a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → hyps a b c d e ≡ hyps a' b' c' d' e'
hyps-≡ refl refl refl refl refl = refl

------------------------------------------------------------------------
-- Renamings, and their action on hypothesis sets

record Ren (Θ Θ' : Scope) : Set where
  constructor ren
  field
    rTy : TyVar Θ → TyVar Θ'
    rR  : RVar Θ → RVar Θ'
    rE  : EVar Θ → EVar Θ'

open Ren public

⌜_⌝ʳ : ∀ {Θ Θ'} → Ren Θ Θ' → Subst Θ Θ'
⌜ r ⌝ʳ = sub (λ α → tvar (rTy r α)) (λ i → rvar (rR r i)) (λ i → evar (rE r i))

infixl 50 _[_]ᴴ

_[_]ᴴ : ∀ {Θ Θ'} → Hyps Θ → Ren Θ Θ' → Hyps Θ'
Q [ r ]ᴴ = hyps (map (rTy r) (ets Q))
                (map (mapᵖ (rTy r)) (subᵥ Q))
                (map (mapᵖ (_[ ⌜ r ⌝ʳ ]ʳ)) (ordᵣ Q))
                (map (mapᵖ (_[ ⌜ r ⌝ʳ ]ᵉ)) (ordₑ Q))
                (map (mapᵈ (_[ ⌜ r ⌝ʳ ]ᵛ) (_[ ⌜ r ⌝ʳ ]ʳ)) (disj Q))

-- Groundings agreeing along a renaming satisfy a hypothesis set and its
-- renaming alike

module _ {Θ Θ'} (r : Ren Θ Θ') {θ : Grounding Θ} {θ' : Grounding Θ'}
         (p : ⌜ r ⌝ʳ ⨟ᵍ θ' ≐ᵍ θ) where

  private

    eqʳ : (ρ : RExp Θ) → ⟦ ρ [ ⌜ r ⌝ʳ ]ʳ ⟧ʳ θ' ≡ ⟦ ρ ⟧ʳ θ
    eqʳ ρ = trans (⟦⟧-⨟ᵍ-r ⌜ r ⌝ʳ θ' ρ) (⟦≐⟧ʳ p ρ)

    eqᵉ : (ε : EExp Θ) → ⟦ ε [ ⌜ r ⌝ʳ ]ᵉ ⟧ᵉ θ' ≡ ⟦ ε ⟧ᵉ θ
    eqᵉ ε = trans (⟦⟧-⨟ᵍ-e ⌜ r ⌝ʳ θ' ε) (⟦≐⟧ᵉ p ε)

    eqᵛ : (A : OVType Θ) → ⟦ A [ ⌜ r ⌝ʳ ]ᵛ ⟧ᵛ θ' ≡ ⟦ A ⟧ᵛ θ
    eqᵛ A = trans (⟦⟧-⨟ᵍ-v ⌜ r ⌝ʳ θ' A) (⟦≐⟧ᵛ p A)

  ⊨-ren : {Q : Hyps Θ} → θ ⊨ᴴ Q → θ' ⊨ᴴ Q [ r ]ᴴ
  ⊨-ren {Q} h = mk⊨ᴴ et sb oR oE dj
    where
      et : ∀ {α} → α ∈ map (rTy r) (ets Q) → Eternal (gTy θ' α)
      et m with ∈-map⁻ (rTy r) m
      ... | α , m' , refl = subst Eternal (sym (≐ᵍᵗ p α)) (etOK h m')

      sb : ∀ {α β} → (α , β) ∈ map (mapᵖ (rTy r)) (subᵥ Q) → gTy θ' α <:ᵛ gTy θ' β
      sb m with ∈-map⁻ (mapᵖ (rTy r)) m
      ... | (α , β) , m' , refl =
            subst₂ _<:ᵛ_ (sym (≐ᵍᵗ p α)) (sym (≐ᵍᵗ p β)) (subOK h m')

      oR : ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ (_[ ⌜ r ⌝ʳ ]ʳ)) (ordᵣ Q)
         → ⟦ ρ ⟧ʳ θ' ≾ᵣ ⟦ ρ' ⟧ʳ θ'
      oR m with ∈-map⁻ (mapᵖ (_[ ⌜ r ⌝ʳ ]ʳ)) m
      ... | (ρ , ρ') , m' , refl = subst₂ _≾ᵣ_ (sym (eqʳ ρ)) (sym (eqʳ ρ')) (ordROK h m')

      oE : ∀ {ε ε'} → (ε , ε') ∈ map (mapᵖ (_[ ⌜ r ⌝ʳ ]ᵉ)) (ordₑ Q)
         → ⟦ ε ⟧ᵉ θ' ≾ₑ ⟦ ε' ⟧ᵉ θ'
      oE m with ∈-map⁻ (mapᵖ (_[ ⌜ r ⌝ʳ ]ᵉ)) m
      ... | (ε , ε') , m' , refl = subst₂ _≾ₑ_ (sym (eqᵉ ε)) (sym (eqᵉ ε')) (ordEOK h m')

      dj : ∀ {A ρ} → (A , ρ) ∈ map (mapᵈ (_[ ⌜ r ⌝ʳ ]ᵛ) (_[ ⌜ r ⌝ʳ ]ʳ)) (disj Q)
         → _
      dj m with ∈-map⁻ (mapᵈ (_[ ⌜ r ⌝ʳ ]ᵛ) (_[ ⌜ r ⌝ʳ ]ʳ)) m
      ... | (A , ρ) , m' , refl =
            map⊎ (subst Eternal (sym (eqᵛ A))) (subst (_≾ᵣ uᵣ) (sym (eqʳ ρ))) (disjOK h m')

  ⊨-ren⁻ : {Q : Hyps Θ} → θ' ⊨ᴴ Q [ r ]ᴴ → θ ⊨ᴴ Q
  ⊨-ren⁻ {Q} h = mk⊨ᴴ
    (λ {α} m → subst Eternal (≐ᵍᵗ p α) (etOK h (∈-map⁺ (rTy r) m)))
    (λ {α} {β} m → subst₂ _<:ᵛ_ (≐ᵍᵗ p α) (≐ᵍᵗ p β) (subOK h (∈-map⁺ (mapᵖ (rTy r)) m)))
    (λ {ρ} {ρ'} m → subst₂ _≾ᵣ_ (eqʳ ρ) (eqʳ ρ')
                      (ordROK h (∈-map⁺ (mapᵖ (_[ ⌜ r ⌝ʳ ]ʳ)) m)))
    (λ {ε} {ε'} m → subst₂ _≾ₑ_ (eqᵉ ε) (eqᵉ ε')
                      (ordEOK h (∈-map⁺ (mapᵖ (_[ ⌜ r ⌝ʳ ]ᵉ)) m)))
    (λ {A} {ρ} m → map⊎ (subst Eternal (eqᵛ A)) (subst (_≾ᵣ uᵣ) (eqʳ ρ))
                      (disjOK h (∈-map⁺ (mapᵈ (_[ ⌜ r ⌝ʳ ]ᵛ) (_[ ⌜ r ⌝ʳ ]ʳ)) m)))

------------------------------------------------------------------------
-- Strengthening along a mask

module _ {Θ : Scope} (M : Vars Θ) where

  -- the scope of the kept variables, and its embedding

  kept : Scope
  kept = scope (count (vᵗ M)) (count (vʳ M)) (count (vᵉ M))

  thin : Ren kept Θ
  thin = ren (emb (vᵗ M)) (emb (vʳ M)) (emb (vᵉ M))

  strᵗ : (α : TyVar Θ) → fvᵗ α ⊆ᵛ M → TyVar kept
  strᵗ α h = str (vᵗ M) α (⊆ᵗ h α (≟-self α))

  strᵉ : (ε : EExp Θ) → fvᵉ ε ⊆ᵛ M → EExp kept
  strᵉ (evar i)   h = evar (str (vᵉ M) i (⊆ᵉ h i (≟-self i)))
  strᵉ (econst c) h = econst c
  strᵉ (ε ·̂ₑ ε')  h = strᵉ ε (⊆-∪ˡ (fvᵉ ε) (fvᵉ ε') h) ·̂ₑ strᵉ ε' (⊆-∪ʳ (fvᵉ ε) (fvᵉ ε') h)
  strᵉ (ε ⊔̂ₑ ε')  h = strᵉ ε (⊆-∪ˡ (fvᵉ ε) (fvᵉ ε') h) ⊔̂ₑ strᵉ ε' (⊆-∪ʳ (fvᵉ ε) (fvᵉ ε') h)

  strʳ : (ρ : RExp Θ) → fvʳ ρ ⊆ᵛ M → RExp kept
  strʳ (rvar i)   h = rvar (str (vʳ M) i (⊆ʳ h i (≟-self i)))
  strʳ (rconst c) h = rconst c
  strʳ (ρ ·̂ᵣ ρ')  h = strʳ ρ (⊆-∪ˡ (fvʳ ρ) (fvʳ ρ') h) ·̂ᵣ strʳ ρ' (⊆-∪ʳ (fvʳ ρ) (fvʳ ρ') h)
  strʳ (ρ ⊔̂ᵣ ρ')  h = strʳ ρ (⊆-∪ˡ (fvʳ ρ) (fvʳ ρ') h) ⊔̂ᵣ strʳ ρ' (⊆-∪ʳ (fvʳ ρ) (fvʳ ρ') h)
  strʳ ∣ ε ∣̂ᵉ     h = ∣ strᵉ ε h ∣̂ᵉ

  private

    ⊆-‼ᵛ : (A : OVType Θ) → (ε : EExp Θ) → fvᶜ (A ‼ ε) ⊆ᵛ M → fvᵛ A ⊆ᵛ M
    ⊆-‼ᵛ A ε h = mk⊆ᵛ (⊆ᵗ h) (⊆ʳ h) (λ i o → ⊆ᵉ h i (∨-inˡ o))

    ⊆-‼ᵉ : (A : OVType Θ) → (ε : EExp Θ) → fvᶜ (A ‼ ε) ⊆ᵛ M → fvᵉ ε ⊆ᵛ M
    ⊆-‼ᵉ A ε h = mk⊆ᵛ (λ _ ()) (λ _ ()) (λ i o → ⊆ᵉ h i (∨-inʳ (occᵉ-v i A) o))

  mutual

    strᵛ : (A : OVType Θ) → fvᵛ A ⊆ᵛ M → OVType kept
    strᵛ (tvar α)  h = tvar (strᵗ α h)
    strᵛ (Base b)  h = Base b
    strᵛ Unit      h = Unit
    strᵛ Bool      h = Bool
    strᵛ (A |×| B) h = strᵛ A (⊆-∪ˡ (fvᵛ A) (fvᵛ B) h) |×| strᵛ B (⊆-∪ʳ (fvᵛ A) (fvᵛ B) h)
    strᵛ Empty     h = Empty
    strᵛ (A ⇒ C)   h = strᵛ A (⊆-∪ˡ (fvᵛ A) (fvᶜ C) h) ⇒ strᶜ C (⊆-∪ʳ (fvᵛ A) (fvᶜ C) h)
    strᵛ ([ ρ ] A) h = [ strʳ ρ (⊆-∪ˡ (fvʳ ρ) (fvᵛ A) h) ] strᵛ A (⊆-∪ʳ (fvʳ ρ) (fvᵛ A) h)

    strᶜ : (C : OCType Θ) → fvᶜ C ⊆ᵛ M → OCType kept
    strᶜ (A ‼ ε) h = strᵛ A (⊆-‼ᵛ A ε h) ‼ strᵉ ε (⊆-‼ᵉ A ε h)

  -- a list, each of whose members is strengthened

  strˡ : {X Y : Set} → (f : X → Vars Θ) → ((x : X) → f x ⊆ᵛ M → Y)
       → (xs : List X) → ⋃ᵛ f xs ⊆ᵛ M → List Y
  strˡ f s []       h = []
  strˡ f s (x ∷ xs) h = s x (⊆-∪ˡ (f x) (⋃ᵛ f xs) h) ∷ strˡ f s xs (⊆-∪ʳ (f x) (⋃ᵛ f xs) h)

  strᵗᵗ : (x : TyVar Θ × TyVar Θ) → fvᵗᵗ x ⊆ᵛ M → TyVar kept × TyVar kept
  strᵗᵗ (α , β) h = strᵗ α (⊆-∪ˡ (fvᵗ α) (fvᵗ β) h) , strᵗ β (⊆-∪ʳ (fvᵗ α) (fvᵗ β) h)

  strʳʳ : (x : RExp Θ × RExp Θ) → fvʳʳ x ⊆ᵛ M → RExp kept × RExp kept
  strʳʳ (ρ , ρ') h = strʳ ρ (⊆-∪ˡ (fvʳ ρ) (fvʳ ρ') h) , strʳ ρ' (⊆-∪ʳ (fvʳ ρ) (fvʳ ρ') h)

  strᵉᵉ : (x : EExp Θ × EExp Θ) → fvᵉᵉ x ⊆ᵛ M → EExp kept × EExp kept
  strᵉᵉ (ε , ε') h = strᵉ ε (⊆-∪ˡ (fvᵉ ε) (fvᵉ ε') h) , strᵉ ε' (⊆-∪ʳ (fvᵉ ε) (fvᵉ ε') h)

  strᵛʳ : (x : OVType Θ × RExp Θ) → fvᵛʳ x ⊆ᵛ M → OVType kept × RExp kept
  strᵛʳ (A , ρ) h = strᵛ A (⊆-∪ˡ (fvᵛ A) (fvʳ ρ) h) , strʳ ρ (⊆-∪ʳ (fvᵛ A) (fvʳ ρ) h)

  strᴴ : (Q : Hyps Θ) → fvᴴ Q ⊆ᵛ M → Hyps kept
  strᴴ Q h = hyps (strˡ fvᵗ  strᵗ  (ets Q)  h₁)
                  (strˡ fvᵗᵗ strᵗᵗ (subᵥ Q) h₂)
                  (strˡ fvʳʳ strʳʳ (ordᵣ Q) h₃)
                  (strˡ fvᵉᵉ strᵉᵉ (ordₑ Q) h₄)
                  (strˡ fvᵛʳ strᵛʳ (disj Q) h₅)
    where
      V₁ = ⋃ᵛ fvᵗ (ets Q)
      V₂ = ⋃ᵛ fvᵗᵗ (subᵥ Q)
      V₃ = ⋃ᵛ fvʳʳ (ordᵣ Q)
      V₄ = ⋃ᵛ fvᵉᵉ (ordₑ Q)
      V₅ = ⋃ᵛ fvᵛʳ (disj Q)
      h₁ = ⊆-∪ˡ V₁ _ h
      h₂ = ⊆-∪ˡ V₂ _ (⊆-∪ʳ V₁ _ h)
      h₃ = ⊆-∪ˡ V₃ _ (⊆-∪ʳ V₂ _ (⊆-∪ʳ V₁ _ h))
      h₄ = ⊆-∪ˡ V₄ V₅ (⊆-∪ʳ V₃ _ (⊆-∪ʳ V₂ _ (⊆-∪ʳ V₁ _ h)))
      h₅ = ⊆-∪ʳ V₄ V₅ (⊆-∪ʳ V₃ _ (⊆-∪ʳ V₂ _ (⊆-∪ʳ V₁ _ h)))

  -- renaming a strengthening back along `ι` gives what was strengthened

  strᵗ-ι : (α : TyVar Θ) → (h : fvᵗ α ⊆ᵛ M) → rTy thin (strᵗ α h) ≡ α
  strᵗ-ι α h = emb-str (vᵗ M) α _

  strᵉ-ι : (ε : EExp Θ) → (h : fvᵉ ε ⊆ᵛ M) → strᵉ ε h [ ⌜ thin ⌝ʳ ]ᵉ ≡ ε
  strᵉ-ι (evar i)   h = cong evar (emb-str (vᵉ M) i _)
  strᵉ-ι (econst c) h = refl
  strᵉ-ι (ε ·̂ₑ ε')  h = cong₂ _·̂ₑ_ (strᵉ-ι ε _) (strᵉ-ι ε' _)
  strᵉ-ι (ε ⊔̂ₑ ε')  h = cong₂ _⊔̂ₑ_ (strᵉ-ι ε _) (strᵉ-ι ε' _)

  strʳ-ι : (ρ : RExp Θ) → (h : fvʳ ρ ⊆ᵛ M) → strʳ ρ h [ ⌜ thin ⌝ʳ ]ʳ ≡ ρ
  strʳ-ι (rvar i)   h = cong rvar (emb-str (vʳ M) i _)
  strʳ-ι (rconst c) h = refl
  strʳ-ι (ρ ·̂ᵣ ρ')  h = cong₂ _·̂ᵣ_ (strʳ-ι ρ _) (strʳ-ι ρ' _)
  strʳ-ι (ρ ⊔̂ᵣ ρ')  h = cong₂ _⊔̂ᵣ_ (strʳ-ι ρ _) (strʳ-ι ρ' _)
  strʳ-ι ∣ ε ∣̂ᵉ     h = cong ∣_∣̂ᵉ (strᵉ-ι ε h)

  mutual

    strᵛ-ι : (A : OVType Θ) → (h : fvᵛ A ⊆ᵛ M) → strᵛ A h [ ⌜ thin ⌝ʳ ]ᵛ ≡ A
    strᵛ-ι (tvar α)  h = cong tvar (strᵗ-ι α h)
    strᵛ-ι (Base b)  h = refl
    strᵛ-ι Unit      h = refl
    strᵛ-ι Bool      h = refl
    strᵛ-ι (A |×| B) h = cong₂ _|×|_ (strᵛ-ι A _) (strᵛ-ι B _)
    strᵛ-ι Empty     h = refl
    strᵛ-ι (A ⇒ C)   h = cong₂ _⇒_ (strᵛ-ι A _) (strᶜ-ι C _)
    strᵛ-ι ([ ρ ] A) h = cong₂ [_]_ (strʳ-ι ρ _) (strᵛ-ι A _)

    strᶜ-ι : (C : OCType Θ) → (h : fvᶜ C ⊆ᵛ M) → strᶜ C h [ ⌜ thin ⌝ʳ ]ᶜ ≡ C
    strᶜ-ι (A ‼ ε) h = cong₂ _‼_ (strᵛ-ι A _) (strᵉ-ι ε _)

  strˡ-ι : {X Y : Set} → (f : X → Vars Θ) → (s : (x : X) → f x ⊆ᵛ M → Y)
         → (g : Y → X) → (∀ x h → g (s x h) ≡ x)
         → (xs : List X) → (h : ⋃ᵛ f xs ⊆ᵛ M) → map g (strˡ f s xs h) ≡ xs
  strˡ-ι f s g e []       h = refl
  strˡ-ι f s g e (x ∷ xs) h = cong₂ _∷_ (e x _) (strˡ-ι f s g e xs _)

  strᴴ-ι : (Q : Hyps Θ) → (h : fvᴴ Q ⊆ᵛ M) → strᴴ Q h [ thin ]ᴴ ≡ Q
  strᴴ-ι Q h =
    hyps-≡ (strˡ-ι fvᵗ  strᵗ  (rTy thin) strᵗ-ι (ets Q) _)
           (strˡ-ι fvᵗᵗ strᵗᵗ (mapᵖ (rTy thin)) eᵗᵗ (subᵥ Q) _)
           (strˡ-ι fvʳʳ strʳʳ (mapᵖ (_[ ⌜ thin ⌝ʳ ]ʳ)) eʳʳ (ordᵣ Q) _)
           (strˡ-ι fvᵉᵉ strᵉᵉ (mapᵖ (_[ ⌜ thin ⌝ʳ ]ᵉ)) eᵉᵉ (ordₑ Q) _)
           (strˡ-ι fvᵛʳ strᵛʳ (mapᵈ (_[ ⌜ thin ⌝ʳ ]ᵛ) (_[ ⌜ thin ⌝ʳ ]ʳ)) eᵛʳ (disj Q) _)
    where
      eᵗᵗ : ∀ x h → mapᵖ (rTy thin) (strᵗᵗ x h) ≡ x
      eᵗᵗ (α , β) h = cong₂ _,_ (strᵗ-ι α (⊆-∪ˡ (fvᵗ α) (fvᵗ β) h))
                                (strᵗ-ι β (⊆-∪ʳ (fvᵗ α) (fvᵗ β) h))

      eʳʳ : ∀ x h → mapᵖ (_[ ⌜ thin ⌝ʳ ]ʳ) (strʳʳ x h) ≡ x
      eʳʳ (ρ , ρ') h = cong₂ _,_ (strʳ-ι ρ _) (strʳ-ι ρ' _)

      eᵉᵉ : ∀ x h → mapᵖ (_[ ⌜ thin ⌝ʳ ]ᵉ) (strᵉᵉ x h) ≡ x
      eᵉᵉ (ε , ε') h = cong₂ _,_ (strᵉ-ι ε _) (strᵉ-ι ε' _)

      eᵛʳ : ∀ x h → mapᵈ (_[ ⌜ thin ⌝ʳ ]ᵛ) (_[ ⌜ thin ⌝ʳ ]ʳ) (strᵛʳ x h) ≡ x
      eᵛʳ (A , ρ) h = cong₂ _,_ (strᵛ-ι A _) (strʳ-ι ρ _)

  -- a grounding of the kept variables, extended by the units

  extᵍ : Grounding kept → Grounding Θ
  extᵍ θ = grounding (ext (vᵗ M) T.Unit (gTy θ)) (ext (vʳ M) uᵣ (gR θ))
                     (ext (vᵉ M) uₑ (gE θ))

  extᵍ-ι : (θ : Grounding kept) → ⌜ thin ⌝ʳ ⨟ᵍ extᵍ θ ≐ᵍ θ
  extᵍ-ι θ = mk≐ᵍ (ext-emb (vᵗ M) T.Unit (gTy θ)) (ext-emb (vʳ M) uᵣ (gR θ))
                  (ext-emb (vᵉ M) uₑ (gE θ))

------------------------------------------------------------------------
-- The step: a type and a hypothesis set, stated over the variables
-- occurring in them

record Strengthened {Θ : Scope} (X : OCType Θ) (Q : Hyps Θ) : Set where
  constructor strengthened
  field
    Θ⁻   : Scope
    ι   : Ren Θ⁻ Θ
    X⁻   : OCType Θ⁻
    Q⁻   : Hyps Θ⁻
    X-ι  : X⁻ [ ⌜ ι ⌝ʳ ]ᶜ ≡ X
    Q-ι  : Q⁻ [ ι ]ᴴ ≡ Q
    ext-ι : (θ : Grounding Θ⁻) → Σ[ θ' ∈ Grounding Θ ] (⌜ ι ⌝ʳ ⨟ᵍ θ' ≐ᵍ θ)

strengthen : ∀ {Θ} → (X : OCType Θ) → (Q : Hyps Θ) → Strengthened X Q
strengthen X Q =
  strengthened (kept M) (thin M) (strᶜ M X hX) (strᴴ M Q hQ)
               (strᶜ-ι M X hX) (strᴴ-ι M Q hQ) (λ θ → extᵍ M θ , extᵍ-ι M θ)
  where
    M  = fvᶜ X ∪ᵛ fvᴴ Q
    hX = ⊆-∪ˡ (fvᶜ X) (fvᴴ Q) ⊆-refl
    hQ = ⊆-∪ʳ (fvᶜ X) (fvᴴ Q) ⊆-refl

------------------------------------------------------------------------
-- After an elimination: its certificates, read along `ι`

module _ {Θ : Scope} {C : OCType Θ} {Q : Hyps Θ} (el : Elim C Q)
         (sr : Strengthened (Ĉ el) (Q̂ el)) where

  open Strengthened sr

  ⟦X⁻⟧ : (θ : Grounding Θ) → ⟦ Ĉ el ⟧ᶜ θ ≡ ⟦ X⁻ ⟧ᶜ (⌜ ι ⌝ʳ ⨟ᵍ θ)
  ⟦X⁻⟧ θ = trans (cong (λ Y → ⟦ Y ⟧ᶜ θ) (sym X-ι)) (⟦⟧-⨟ᵍ-c ⌜ ι ⌝ʳ θ X⁻)

  keep⁻ : (θ : Grounding Θ) → θ ⊨ᴴ Q → (⌜ ι ⌝ʳ ⨟ᵍ θ) ⊨ᴴ Q⁻
  keep⁻ θ h = ⊨-ren⁻ ι (mk≐ᵍ (λ _ → refl) (λ _ → refl) (λ _ → refl))
                (subst (θ ⊨ᴴ_) (sym Q-ι) (keep el θ h))

  real⁻ : (θ : Grounding Θ⁻) → θ ⊨ᴴ Q⁻
        → Σ[ θ' ∈ Grounding Θ ] ((θ' ⊨ᴴ Q) × (⟦ C ⟧ᶜ θ' ≡ ⟦ X⁻ ⟧ᶜ θ))
  real⁻ θ h with ext-ι θ
  ... | θ₁ , p with real el θ₁ (subst (θ₁ ⊨ᴴ_) Q-ι (⊨-ren ι p h))
  ...   | θ' , h' , q = θ' , h' , trans q (trans (⟦X⁻⟧ θ₁) (⟦≐⟧ᶜ p X⁻))

  princ⁻ : (θ : Grounding Θ) → θ ⊨ᴴ Q → ⟦ X⁻ ⟧ᶜ (⌜ ι ⌝ʳ ⨟ᵍ θ) <:ᶜ ⟦ C ⟧ᶜ θ
  princ⁻ θ h = subst (_<:ᶜ ⟦ C ⟧ᶜ θ) (⟦X⁻⟧ θ) (princ el θ h)
