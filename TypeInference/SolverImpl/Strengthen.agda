------------------------------------------------------------------
-- Strengthening a report to the variables occurring in it        --
--                                                                --
-- A mask keeps some variables of each sort. The kept ones form a --
-- smaller scope, embedded back in order by a renaming `ι`, and   --
-- an expression all of whose variables are kept is strengthened  --
-- along it: renaming the result along `ι` gives the expression   --
-- back on the nose. An instance of the smaller scope extends     --
-- along `ι`, by closed values on the variables dropped.          --
--                                                                --
-- `strengthen` takes the mask of the variables occurring in a    --
-- type, a hypothesis set, or the image of a substitution, and    --
-- strengthens the three along it.                                --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Strengthen (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S

open import TypeInference.SolverImpl.Vars      S
open import TypeInference.SolverImpl.Eliminate S using (Elim; Ĉ; Q̂; η; conv; inst; keep; princ)
open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-v)

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

-- the embedded variables are kept

emb-kept : ∀ {n} → (p : Fin n → 𝔹) → (j : Fin (count p)) → p (emb p j) ≡ true
emb-kept {suc n} p = go (p zero) refl
  where
    p' : Fin n → 𝔹
    p' i = p (suc i)

    go : (b : 𝔹) → p zero ≡ b → (j : Fin (if b then suc (count p') else count p'))
       → p (embC b (emb p') j) ≡ true
    go true  e zero    = e
    go true  e (suc j) = emb-kept p' j
    go false e j       = emb-kept p' j

------------------------------------------------------------------------
-- Hypothesis sets, equal field by field

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

-- A renamed set entails the set along the renaming, and so its
-- instances are instances of the set

⊩ᴴ-ren : ∀ {Θ Θ'} {Q : Hyps Θ} → (r : Ren Θ Θ') → Q [ r ]ᴴ ⊩ᴴ Q [ ⌜ r ⌝ʳ ]
⊩ᴴ-ren r =
  mk⊩ᴴ (λ m → et-hyp (∈-map⁺ (rTy r) m))
       (λ m → tvarₛ (hypᵗᵛ (∈-map⁺ (mapᵖ (rTy r)) m)))
       (λ m → hypᵣ (∈-map⁺ (mapᵖ (_[ ⌜ r ⌝ʳ ]ʳ)) m))
       (λ m → hypₑ (∈-map⁺ (mapᵖ (_[ ⌜ r ⌝ʳ ]ᵉ)) m))
       (λ m → hyp-ok₀ (∈-map⁺ (mapᵈ (_[ ⌜ r ⌝ʳ ]ᵛ) (_[ ⌜ r ⌝ʳ ]ʳ)) m))

⊩ᴴ-ren⁻ : ∀ {Θ Θ' Θ''} {Q : Hyps Θ} {Q' : Hyps Θ''} → (r : Ren Θ Θ') → {δ : Subst Θ' Θ''}
        → Q' ⊩ᴴ Q [ r ]ᴴ [ δ ] → Q' ⊩ᴴ Q [ ⌜ r ⌝ʳ ⨟ˢ δ ]
⊩ᴴ-ren⁻ r h = ⊩ᴴ-⨟ h (⊩ᴴ-ren r)

⊩ᴴ-ren⁺ : ∀ {Θ Θ' Θ''} {Q : Hyps Θ} {Q' : Hyps Θ''} → (r : Ren Θ Θ') → {δ : Subst Θ' Θ''}
        → Q' ⊩ᴴ Q [ ⌜ r ⌝ʳ ⨟ˢ δ ] → Q' ⊩ᴴ Q [ r ]ᴴ [ δ ]
⊩ᴴ-ren⁺ {Q = Q} {Q'} r {δ} h = mk⊩ᴴ et sb oR oE dj
  where
    et : ∀ {α} → α ∈ map (rTy r) (ets Q) → Q' ⊩ᴱ sTy δ α
    et m with ∈-map⁻ (rTy r) m
    ... | α , m' , refl = ⊩ets h m'

    sb : ∀ {α β} → (α , β) ∈ map (mapᵖ (rTy r)) (subᵥ Q) → Q' ∣ sTy δ α <:̂ᵛ sTy δ β
    sb m with ∈-map⁻ (mapᵖ (rTy r)) m
    ... | (α , β) , m' , refl = ⊩subᵥ h m'

    oR : ∀ {ρ ρ'} → (ρ , ρ') ∈ map (mapᵖ (_[ ⌜ r ⌝ʳ ]ʳ)) (ordᵣ Q)
       → Q' ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    oR m with ∈-map⁻ (mapᵖ (_[ ⌜ r ⌝ʳ ]ʳ)) m
    ... | (ρ , ρ') , m' , refl =
          subst₂ (λ x y → Q' ⊩ x ≾̂ᵣ y) (sym ([⨟]ʳ ρ ⌜ r ⌝ʳ δ)) (sym ([⨟]ʳ ρ' ⌜ r ⌝ʳ δ))
                 (⊩ordᵣ h m')

    oE : ∀ {ε ε'} → (ε , ε') ∈ map (mapᵖ (_[ ⌜ r ⌝ʳ ]ᵉ)) (ordₑ Q)
       → Q' ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
    oE m with ∈-map⁻ (mapᵖ (_[ ⌜ r ⌝ʳ ]ᵉ)) m
    ... | (ε , ε') , m' , refl =
          subst₂ (λ x y → Q' ⊩ x ≾̂ₑ y) (sym ([⨟]ᵉ ε ⌜ r ⌝ʳ δ)) (sym ([⨟]ᵉ ε' ⌜ r ⌝ʳ δ))
                 (⊩ordₑ h m')

    dj : ∀ {A ρ} → (A , ρ) ∈ map (mapᵈ (_[ ⌜ r ⌝ʳ ]ᵛ) (_[ ⌜ r ⌝ʳ ]ʳ)) (disj Q)
       → VarOK Q' (A [ δ ]ᵛ) (ρ [ δ ]ʳ)
    dj m with ∈-map⁻ (mapᵈ (_[ ⌜ r ⌝ʳ ]ᵛ) (_[ ⌜ r ⌝ʳ ]ʳ)) m
    ... | (A , ρ) , m' , refl =
          subst₂ (VarOK Q') (sym ([⨟]ᵛ A ⌜ r ⌝ʳ δ)) (sym ([⨟]ʳ ρ ⌜ r ⌝ʳ δ)) (⊩disj h m')

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

  -- a substitution, each of whose images is strengthened

  strˢ : ∀ {Θ₀} → (τ : Subst Θ₀ Θ) → fvˢ τ ⊆ᵛ M → Subst Θ₀ kept
  strˢ τ h = sub (λ α → strᵛ (sTy τ α) (⋃ᶠ-⊆ _ h₁ α)) (λ i → strʳ (sR τ i) (⋃ᶠ-⊆ _ h₂ i))
                 (λ i → strᵉ (sE τ i) (⋃ᶠ-⊆ _ h₃ i))
    where
      Vᵗ = ⋃ᶠ (λ α → fvᵛ (sTy τ α))
      Vʳ = ⋃ᶠ (λ i → fvʳ (sR τ i))
      Vᵉ = ⋃ᶠ (λ i → fvᵉ (sE τ i))
      h₁ = ⊆-∪ˡ Vᵗ (Vʳ ∪ᵛ Vᵉ) h
      h₂ = ⊆-∪ˡ Vʳ Vᵉ (⊆-∪ʳ Vᵗ (Vʳ ∪ᵛ Vᵉ) h)
      h₃ = ⊆-∪ʳ Vʳ Vᵉ (⊆-∪ʳ Vᵗ (Vʳ ∪ᵛ Vᵉ) h)

  strˢ-ι : ∀ {Θ₀} → (τ : Subst Θ₀ Θ) → (h : fvˢ τ ⊆ᵛ M) → strˢ τ h ⨟ˢ ⌜ thin ⌝ʳ ≐ˢ τ
  strˢ-ι τ h = mk≐ˢ (λ α → strᵛ-ι (sTy τ α) _) (λ i → strʳ-ι (sR τ i) _)
                    (λ i → strᵉ-ι (sE τ i) _)

  -- an instance of the kept variables, extended by closed constants on
  -- the others

  extⁱ : ∀ {Ψ} → Subst kept Ψ → Subst Θ Ψ
  extⁱ δ = sub (ext (vᵗ M) Unit (sTy δ)) (ext (vʳ M) ûᵣ (sR δ)) (ext (vᵉ M) ûₑ (sE δ))

  extⁱ-ι : ∀ {Ψ} → (δ : Subst kept Ψ) → ⌜ thin ⌝ʳ ⨟ˢ extⁱ δ ≐ˢ δ
  extⁱ-ι δ = mk≐ˢ (ext-emb (vᵗ M) Unit (sTy δ)) (ext-emb (vʳ M) ûᵣ (sR δ))
                  (ext-emb (vᵉ M) ûₑ (sE δ))

-- A substitution fixing a set fixes every substitution whose image
-- lies in it

fixes-≐ : ∀ {Θ₀ Θ} {F : Vars Θ} {η : Subst Θ Θ} → Fixes F η
        → (τ : Subst Θ₀ Θ) → fvˢ τ ⊆ᵛ F → τ ⨟ˢ η ≐ˢ τ
fixes-≐ {F = F} {η} f τ h =
  ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (strˢ-ι F τ h)) η)
  (≐ˢ-trans (⨟-assoc (strˢ F τ h) ⌜ thin F ⌝ʳ η)
  (≐ˢ-trans (⨟-congʳ (strˢ F τ h) thin-fix) (strˢ-ι F τ h)))
  where
    thin-fix : ⌜ thin F ⌝ʳ ⨟ˢ η ≐ˢ ⌜ thin F ⌝ʳ
    thin-fix = mk≐ˢ (λ j → fixᵗ f _ (emb-kept (vᵗ F) j)) (λ j → fixʳ f _ (emb-kept (vʳ F) j))
                    (λ j → fixᵉ f _ (emb-kept (vᵉ F) j))

------------------------------------------------------------------------
-- The step: a type, a hypothesis set and a substitution, stated over
-- the variables occurring in them

record Strengthened {Θ₀ Θ : Scope} (τ : Subst Θ₀ Θ) (X : OCType Θ) (Q : Hyps Θ) : Set where
  constructor strengthened
  field
    Θ⁻    : Scope
    ι     : Ren Θ⁻ Θ
    τ⁻    : Subst Θ₀ Θ⁻
    X⁻    : OCType Θ⁻
    Q⁻    : Hyps Θ⁻
    τ-ι   : τ⁻ ⨟ˢ ⌜ ι ⌝ʳ ≐ˢ τ
    X-ι   : X⁻ [ ⌜ ι ⌝ʳ ]ᶜ ≡ X
    Q-ι   : Q⁻ [ ι ]ᴴ ≡ Q
    ext-ι : ∀ {Ψ} → (δ : Subst Θ⁻ Ψ) → Σ[ δ' ∈ Subst Θ Ψ ] (⌜ ι ⌝ʳ ⨟ˢ δ' ≐ˢ δ)

strengthen : ∀ {Θ₀ Θ} → (τ : Subst Θ₀ Θ) → (X : OCType Θ) → (Q : Hyps Θ) → Strengthened τ X Q
strengthen τ X Q =
  strengthened (kept M) (thin M) (strˢ M τ hτ) (strᶜ M X hX) (strᴴ M Q hQ)
               (strˢ-ι M τ hτ) (strᶜ-ι M X hX) (strᴴ-ι M Q hQ) (λ δ → extⁱ M δ , extⁱ-ι M δ)
  where
    M  = fvᶜ X ∪ᵛ fvᴴ Q ∪ᵛ fvˢ τ
    hX = ⊆-∪ˡ (fvᶜ X) (fvᴴ Q ∪ᵛ fvˢ τ) ⊆-refl
    hQ = ⊆-∪ˡ (fvᴴ Q) (fvˢ τ) (⊆-∪ʳ (fvᶜ X) (fvᴴ Q ∪ᵛ fvˢ τ) ⊆-refl)
    hτ = ⊆-∪ʳ (fvᴴ Q) (fvˢ τ) (⊆-∪ʳ (fvᶜ X) (fvᴴ Q ∪ᵛ fvˢ τ) ⊆-refl)

------------------------------------------------------------------------
-- After an elimination: its certificates, read along `ι`

module _ {Θ₀ Θ : Scope} {τ : Subst Θ₀ Θ} {C : OCType Θ} {Q : Hyps Θ} (el : Elim C Q)
         (sr : Strengthened τ (Ĉ el) (Q̂ el)) where

  open Strengthened sr

  conv⁻ : X⁻ [ ⌜ ι ⌝ʳ ]ᶜ ≡̂ᶜ C [ η el ]ᶜ
  conv⁻ = subst (_≡̂ᶜ C [ η el ]ᶜ) (sym X-ι) (conv el)

  inst⁻ : Q⁻ [ ι ]ᴴ ⊩ᴴ Q [ η el ]
  inst⁻ = subst (_⊩ᴴ Q [ η el ]) (sym Q-ι) (inst el)

  keep⁻ : (δ : Subst Θ ∅ˢ) → ∅ᴴ ⊩ᴴ Q [ δ ] → ∅ᴴ ⊩ᴴ Q⁻ [ ⌜ ι ⌝ʳ ⨟ˢ δ ]
  keep⁻ δ h = ⊩ᴴ-ren⁻ ι (subst (λ P → ∅ᴴ ⊩ᴴ P [ δ ]) (sym Q-ι) (keep el δ h))

  princ⁻ : (δ : Subst Θ ∅ˢ) → ∅ᴴ ⊩ᴴ Q [ δ ] → ∅ᴴ ∣ X⁻ [ ⌜ ι ⌝ʳ ⨟ˢ δ ]ᶜ <:̂ᶜ C [ δ ]ᶜ
  princ⁻ δ h =
    subst (λ Y → ∅ᴴ ∣ Y <:̂ᶜ C [ δ ]ᶜ)
          (trans (cong (_[ δ ]ᶜ) (sym X-ι)) ([⨟]ᶜ X⁻ ⌜ ι ⌝ʳ δ))
          (princ el δ h)
