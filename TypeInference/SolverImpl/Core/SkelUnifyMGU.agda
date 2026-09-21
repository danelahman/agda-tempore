------------------------------------------------------------------
-- Most general unifiers of skeletons                             --
--                                                                --
-- A successful run of `unifyᵏ` returns a most general unifier:   --
-- every substitution unifying the equations factors through the  --
-- returned store. A failure refutes the equations for every      --
-- substitution. No skeleton variable is rigid, so maximality     --
-- relative to the empty store already is most-generality.        --
--                                                                --
-- Follows McBride's `Max` characterisation of most general       --
-- unifiers and the optimist's lemma (JFP 2003).                  --
------------------------------------------------------------------

open import Data.Bool.Base using (if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; punchIn)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_) renaming (map to mmap)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; m≤n⇒m≤1+n; 1+n≰n)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Core.SkelUnifyMGU (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (BaseType; _≡ᵇ?_)

open import TypeInference.SolverImpl.Core.Thick
open import TypeInference.SolverImpl.Core.Rigid S
  using (zip₂-just; zip₂-nothing; map-nothing; thick-nothing)
open import TypeInference.SolverImpl.Core.Skel           S
open import TypeInference.SolverImpl.Core.SkelUnify      S
open import TypeInference.SolverImpl.Core.SkelUnifySound S using (bind-just; dec-if)

refl≐ᵏ : ∀ {n m} {σ : SSub n m} → σ ≐ᵏ σ
refl≐ᵏ α = refl

sym≐ᵏ : ∀ {n m} {σ δ : SSub n m} → σ ≐ᵏ δ → δ ≐ᵏ σ
sym≐ᵏ q α = sym (q α)

trans≐ᵏ : ∀ {n m} {σ δ γ : SSub n m} → σ ≐ᵏ δ → δ ≐ᵏ γ → σ ≐ᵏ γ
trans≐ᵏ q r α = trans (q α) (r α)

⨟ᵏ-assoc : ∀ {n m l k} → (σ : SSub n m) → (δ : SSub m l) → (γ : SSub l k)
         → ((σ ⨟ᵏ δ) ⨟ᵏ γ) ≐ᵏ (σ ⨟ᵏ (δ ⨟ᵏ γ))
⨟ᵏ-assoc σ δ γ α = [⨟]ᵏ (σ α) δ γ

⨟ᵏ-congʳ : ∀ {n m l} → (σ : SSub n m) → {δ γ : SSub m l} → δ ≐ᵏ γ → (σ ⨟ᵏ δ) ≐ᵏ (σ ⨟ᵏ γ)
⨟ᵏ-congʳ σ q α = [≐]ᵏ q (σ α)

bind-nothing : ∀ {X Y : Set} → (m : Maybe X) → (f : X → Maybe Y) → (m >>= f) ≡ nothing
             → (m ≡ nothing) ⊎ Σ[ x ∈ X ] ((m ≡ just x) × (f x ≡ nothing))
bind-nothing nothing  f q = inj₁ refl
bind-nothing (just x) f q = inj₂ (x , refl , q)

dec-if-nothing : ∀ {P X : Set} → (d : Dec P) → (m m' : Maybe X)
               → (if ⌊ d ⌋ then m else m') ≡ nothing
               → (P × (m ≡ nothing)) ⊎ ((¬ P) × (m' ≡ nothing))
dec-if-nothing (yes r) m m' q = inj₁ (r , q)
dec-if-nothing (no nr) m m' q = inj₂ (nr , q)

sBase-inj : ∀ {n} {b b' : BaseType} → sBase {n} b ≡ sBase b' → b ≡ b'
sBase-inj refl = refl

s×-inj : ∀ {n} {t t' u u' : Skel n} → (t s× u) ≡ (t' s× u') → (t ≡ t') × (u ≡ u')
s×-inj refl = refl , refl

s⇒-inj : ∀ {n} {t t' u u' : Skel n} → (t s⇒ u) ≡ (t' s⇒ u') → (t ≡ t') × (u ≡ u')
s⇒-inj refl = refl , refl

sBox-inj : ∀ {n} {t t' : Skel n} → sBox t ≡ sBox t' → t ≡ t'
sBox-inj refl = refl

-- Substitutions unifying an equation are closed under pointwise
-- equality

Unifies¹ᵏ-resp≐ : ∀ {n m} {σ δ : SSub n m} → σ ≐ᵏ δ → (e : SEqn n)
                → Unifies¹ᵏ e σ → Unifies¹ᵏ e δ
Unifies¹ᵏ-resp≐ q (t , u) p = trans (sym ([≐]ᵏ q t)) (trans p ([≐]ᵏ q u))

Unifiesᵏ-resp≐ : ∀ {n m} {σ δ : SSub n m} → σ ≐ᵏ δ → (es : SEqns n)
               → Unifiesᵏ es σ → Unifiesᵏ es δ
Unifiesᵏ-resp≐ q []       ps       = tt
Unifiesᵏ-resp≐ q (e ∷ es) (p , ps) = Unifies¹ᵏ-resp≐ q e p , Unifiesᵏ-resp≐ q es ps

-- Substituting into an equation before solving it

Unifies¹ᵏ-[]ᵏ⁻ : ∀ {n m l} → (t u : Skel n) → (σ : SSub n m) → (γ : SSub m l)
               → Unifies¹ᵏ (t , u) (σ ⨟ᵏ γ) → Unifies¹ᵏ (t [ σ ]ᵏ , u [ σ ]ᵏ) γ
Unifies¹ᵏ-[]ᵏ⁻ t u σ γ p = trans ([⨟]ᵏ t σ γ) (trans p (sym ([⨟]ᵏ u σ γ)))

-- Occurrence of a skeleton variable

data Occᵏ {n : ℕ} (α : Fin n) : Skel n → Set where
  occ-var : Occᵏ α (svar α)
  occ-×ˡ  : ∀ {t u} → Occᵏ α t → Occᵏ α (t s× u)
  occ-×ʳ  : ∀ {t u} → Occᵏ α u → Occᵏ α (t s× u)
  occ-⇒ˡ  : ∀ {t u} → Occᵏ α t → Occᵏ α (t s⇒ u)
  occ-⇒ʳ  : ∀ {t u} → Occᵏ α u → Occᵏ α (t s⇒ u)
  occ-box : ∀ {t}   → Occᵏ α t → Occᵏ α (sBox t)

sizeᵏ : ∀ {n} → Skel n → ℕ
sizeᵏ (svar α)  = 1
sizeᵏ (sBase b) = 1
sizeᵏ sUnit     = 1
sizeᵏ sBool     = 1
sizeᵏ (t s× u)  = suc (sizeᵏ t + sizeᵏ u)
sizeᵏ sEmpty    = 1
sizeᵏ (t s⇒ u)  = suc (sizeᵏ t + sizeᵏ u)
sizeᵏ (sBox t)  = suc (sizeᵏ t)

-- A failed occurrence check exhibits the occurrence

checkᵏ-nothing : ∀ {n} → (α : Fin (suc n)) → (t : Skel (suc n)) → checkᵏ α t ≡ nothing
               → Occᵏ α t
checkᵏ-nothing α (svar β)   q =
  subst (λ z → Occᵏ α (svar z))
        (sym (thick-nothing α β (map-nothing svar (thick α β) q))) occ-var
checkᵏ-nothing α (sBase b)  ()
checkᵏ-nothing α sUnit      ()
checkᵏ-nothing α sBool      ()
checkᵏ-nothing α (t₁ s× t₂) q with zip₂-nothing _s×_ (checkᵏ α t₁) (checkᵏ α t₂) q
... | inj₁ r = occ-×ˡ (checkᵏ-nothing α t₁ r)
... | inj₂ r = occ-×ʳ (checkᵏ-nothing α t₂ r)
checkᵏ-nothing α sEmpty     ()
checkᵏ-nothing α (t₁ s⇒ t₂) q with zip₂-nothing _s⇒_ (checkᵏ α t₁) (checkᵏ α t₂) q
... | inj₁ r = occ-⇒ˡ (checkᵏ-nothing α t₁ r)
... | inj₂ r = occ-⇒ʳ (checkᵏ-nothing α t₂ r)
checkᵏ-nothing α (sBox t₁)  q =
  occ-box (checkᵏ-nothing α t₁ (map-nothing sBox_ (checkᵏ α t₁) q))

occ≤ᵏ : ∀ {n m} {t : Skel n} → (α : Fin n) → (σ : SSub n m) → Occᵏ α t
      → sizeᵏ (σ α) ≤ sizeᵏ (t [ σ ]ᵏ)
occ≤ᵏ α σ occ-var     = ≤-refl
occ≤ᵏ α σ (occ-×ˡ o)  = m≤n⇒m≤1+n (≤-trans (occ≤ᵏ α σ o) (m≤m+n _ _))
occ≤ᵏ α σ (occ-×ʳ o)  = m≤n⇒m≤1+n (≤-trans (occ≤ᵏ α σ o) (m≤n+m _ _))
occ≤ᵏ α σ (occ-⇒ˡ o)  = m≤n⇒m≤1+n (≤-trans (occ≤ᵏ α σ o) (m≤m+n _ _))
occ≤ᵏ α σ (occ-⇒ʳ o)  = m≤n⇒m≤1+n (≤-trans (occ≤ᵏ α σ o) (m≤n+m _ _))
occ≤ᵏ α σ (occ-box o) = m≤n⇒m≤1+n (occ≤ᵏ α σ o)

-- A variable occurring in a skeleton other than itself is never sent
-- to that skeleton's instance

no-cycleᵏ : ∀ {n m} {t : Skel n} → (α : Fin n) → (σ : SSub n m) → ¬ (t ≡ svar α)
          → Occᵏ α t → ¬ (σ α ≡ t [ σ ]ᵏ)
no-cycleᵏ α σ nv occ-var     u = nv refl
no-cycleᵏ α σ nv (occ-×ˡ o)  u =
  1+n≰n (subst (suc (sizeᵏ (σ α)) ≤_) (sym (cong sizeᵏ u))
               (s≤s (≤-trans (occ≤ᵏ α σ o) (m≤m+n _ _))))
no-cycleᵏ α σ nv (occ-×ʳ o)  u =
  1+n≰n (subst (suc (sizeᵏ (σ α)) ≤_) (sym (cong sizeᵏ u))
               (s≤s (≤-trans (occ≤ᵏ α σ o) (m≤n+m _ _))))
no-cycleᵏ α σ nv (occ-⇒ˡ o)  u =
  1+n≰n (subst (suc (sizeᵏ (σ α)) ≤_) (sym (cong sizeᵏ u))
               (s≤s (≤-trans (occ≤ᵏ α σ o) (m≤m+n _ _))))
no-cycleᵏ α σ nv (occ-⇒ʳ o)  u =
  1+n≰n (subst (suc (sizeᵏ (σ α)) ≤_) (sym (cong sizeᵏ u))
               (s≤s (≤-trans (occ≤ᵏ α σ o) (m≤n+m _ _))))
no-cycleᵏ α σ nv (occ-box o) u =
  1+n≰n (subst (suc (sizeᵏ (σ α)) ≤_) (sym (cong sizeᵏ u)) (s≤s (occ≤ᵏ α σ o)))

-- A skeleton that passes the occurrence check is the thinning of the
-- skeleton the check returns

thinᵏ : ∀ {n} → Fin (suc n) → SSub n (suc n)
thinᵏ α β = svar (punchIn α β)

checkᵏ-thinᵏ : ∀ {n} → (α : Fin (suc n)) → (t : Skel (suc n)) → {u : Skel n}
             → checkᵏ α t ≡ just u → u [ thinᵏ α ]ᵏ ≡ t
checkᵏ-thinᵏ α (svar β)   q with map-just svar (thick α β) q
... | β₀ , r , refl = cong svar (sym (thick-just α β β₀ r))
checkᵏ-thinᵏ α (sBase b)  refl = refl
checkᵏ-thinᵏ α sUnit      refl = refl
checkᵏ-thinᵏ α sBool      refl = refl
checkᵏ-thinᵏ α (t₁ s× t₂) q with zip₂-just _s×_ (checkᵏ α t₁) (checkᵏ α t₂) q
... | _ , _ , q₁ , q₂ , refl =
  cong₂ _s×_ (checkᵏ-thinᵏ α t₁ q₁) (checkᵏ-thinᵏ α t₂ q₂)
checkᵏ-thinᵏ α sEmpty     refl = refl
checkᵏ-thinᵏ α (t₁ s⇒ t₂) q with zip₂-just _s⇒_ (checkᵏ α t₁) (checkᵏ α t₂) q
... | _ , _ , q₁ , q₂ , refl =
  cong₂ _s⇒_ (checkᵏ-thinᵏ α t₁ q₁) (checkᵏ-thinᵏ α t₂ q₂)
checkᵏ-thinᵏ α (sBox t₁)  q with map-just sBox_ (checkᵏ α t₁) q
... | _ , q₁ , refl = cong sBox_ (checkᵏ-thinᵏ α t₁ q₁)

-- A property of substitutions out of one scope

record Propertyᵏ (n : ℕ) : Set₁ where
  constructor propᵏ
  field
    at    : ∀ {m} → SSub n m → Set
    resp≐ : ∀ {m} {σ δ : SSub n m} → σ ≐ᵏ δ → at σ → at δ

open Propertyᵏ public

infixl 30 _⋄ᵏ_

_⋄ᵏ_ : ∀ {n n'} → Propertyᵏ n → SSub n n' → Propertyᵏ n'
P ⋄ᵏ τ = propᵏ (λ δ → at P (τ ⨟ᵏ δ)) (λ q p → resp≐ P (⨟ᵏ-congʳ τ q) p)

Uniᵏ : ∀ {n} → SEqn n → Propertyᵏ n
Uniᵏ e = propᵏ (Unifies¹ᵏ e) (λ q p → Unifies¹ᵏ-resp≐ q e p)

Unisᵏ : ∀ {n} → SEqns n → Propertyᵏ n
Unisᵏ es = propᵏ (Unifiesᵏ es) (λ q ps → Unifiesᵏ-resp≐ q es ps)

-- Maximality relative to the store the call starts from: every
-- solution of the property extending that store is an instance of the
-- returned store.

record Maxᵏ {n m l : ℕ} (P : Propertyᵏ n) (τ : SAList n m) (τ'' : SAList n l) : Set where
  constructor maxᵏ
  field
    fact : ∀ {k} → (δ : SSub m k) → at (P ⋄ᵏ ⟦ τ ⟧ᴷ) δ
         → Σ[ δ' ∈ SSub l k ] ((⟦ τ'' ⟧ᴷ ⨟ᵏ δ') ≐ᵏ (⟦ τ ⟧ᴷ ⨟ᵏ δ))

open Maxᵏ public

record Specᵏ {n m : ℕ} (P : Propertyᵏ n) (τ : SAList n m) (x : Maybe (Solᵏ n)) : Set where
  constructor specᵏ
  field
    onJust    : ∀ {l} {τ'' : SAList n l} → x ≡ just (l , τ'') → Maxᵏ P τ τ''
    onNothing : x ≡ nothing → ∀ {k} → (δ : SSub m k) → ¬ at (P ⋄ᵏ ⟦ τ ⟧ᴷ) δ

open Specᵏ public

Maxᵏ-id : ∀ {n m} {P : Propertyᵏ n} {τ : SAList n m} → Maxᵏ P τ τ
Maxᵏ-id = maxᵏ (λ δ p → δ , refl≐ᵏ)

-- The store is returned unchanged

keepᵏ : ∀ {n m} {P : Propertyᵏ n} {τ : SAList n m} → Specᵏ P τ (just (m , τ))
keepᵏ = specᵏ (λ { refl → Maxᵏ-id }) (λ ())

-- The property has no solution at all: the verdict is immaterial

clashᵏ : ∀ {n m} {P : Propertyᵏ n} {τ : SAList n m} {x : Maybe (Solᵏ n)}
       → (∀ {k} → (δ : SSub m k) → ¬ at (P ⋄ᵏ ⟦ τ ⟧ᴷ) δ) → Specᵏ P τ x
clashᵏ nc = specᵏ (λ _ → maxᵏ (λ δ p → ⊥-elim (nc δ p))) (λ _ → nc)

-- Comparing two constants

const-specᵏ : ∀ {n m} {P : Propertyᵏ n} {τ : SAList n m} {Q : Set}
            → (d : Dec Q) → (∀ {k} → (δ : SSub m k) → at (P ⋄ᵏ ⟦ τ ⟧ᴷ) δ → Q)
            → Specᵏ P τ (if ⌊ d ⌋ then just (m , τ) else nothing)
const-specᵏ (yes r) f = keepᵏ
const-specᵏ (no nr) f = clashᵏ (λ δ p → nr (f δ p))

-- Weakening the property along an implication

Maxᵏ-map : ∀ {n m l} {P P' : Propertyᵏ n} {τ : SAList n m} {τ'' : SAList n l}
         → (∀ {k} {σ : SSub n k} → at P' σ → at P σ) → Maxᵏ P τ τ'' → Maxᵏ P' τ τ''
Maxᵏ-map f (maxᵏ g) = maxᵏ (λ δ p → g δ (f p))

Specᵏ-map : ∀ {n m} {P P' : Propertyᵏ n} {τ : SAList n m} {x : Maybe (Solᵏ n)}
          → (∀ {k} {σ : SSub n k} → at P' σ → at P σ) → Specᵏ P τ x → Specᵏ P' τ x
Specᵏ-map f (specᵏ j nc) = specᵏ (λ q → Maxᵏ-map f (j q)) (λ q δ p → nc q δ (f p))

-- Two calls in sequence: the second starts from the store the first
-- returned, and the factorisations compose.

seq-specᵏ : ∀ {n m} {P P₁ P₂ : Propertyᵏ n} {τ : SAList n m}
          → (x : Maybe (Solᵏ n)) → (f : Solᵏ n → Maybe (Solᵏ n))
          → Specᵏ P₁ τ x
          → (∀ {m₁} → (τ₁ : SAList n m₁) → Specᵏ P₂ τ₁ (f (m₁ , τ₁)))
          → (∀ {k} {σ : SSub n k} → at P σ → at P₁ σ × at P₂ σ)
          → Specᵏ P τ (x >>= f)
seq-specᵏ {n} {m} {P} {P₁} {P₂} {τ} x f s₁ s₂ split = specᵏ yes' no'
  where
    yes' : ∀ {l} {τ₂ : SAList n l} → (x >>= f) ≡ just (l , τ₂) → Maxᵏ P τ τ₂
    yes' q with bind-just x f q
    ... | (m₁ , τ₁) , q₁ , q₂ = maxᵏ (λ δ p →
            let h₁ = fact (onJust s₁ q₁) δ (proj₁ (split p))
                h₂ = fact (onJust (s₂ τ₁) q₂) (proj₁ h₁)
                          (resp≐ P₂ (sym≐ᵏ (proj₂ h₁)) (proj₂ (split p)))
            in proj₁ h₂ , trans≐ᵏ (proj₂ h₂) (proj₂ h₁))

    no' : (x >>= f) ≡ nothing → ∀ {k} → (δ : SSub m k) → ¬ at (P ⋄ᵏ ⟦ τ ⟧ᴷ) δ
    no' q δ p with bind-nothing x f q
    ... | inj₁ r = onNothing s₁ r δ (proj₁ (split p))
    ... | inj₂ ((m₁ , τ₁) , r₁ , r₂) =
            let h = proj₂ (fact (onJust s₁ r₁) δ (proj₁ (split p)))
            in onNothing (s₂ τ₁) r₂ _ (resp≐ P₂ (sym≐ᵏ h) (proj₂ (split p)))

-- Descending through one binding of the store

glueᵏ : ∀ {n m l k} → (r : Skel n) → (α : Fin (suc n))
      → (τ : SAList n m) → (τ' : SAList n l)
      → (δ : SSub m k) → (δ' : SSub l k) → (⟦ τ' ⟧ᴷ ⨟ᵏ δ') ≐ᵏ (⟦ τ ⟧ᴷ ⨟ᵏ δ)
      → (⟦ r /ᵏ α ∷ τ' ⟧ᴷ ⨟ᵏ δ') ≐ᵏ (⟦ r /ᵏ α ∷ τ ⟧ᴷ ⨟ᵏ δ)
glueᵏ r α τ τ' δ δ' h =
  trans≐ᵏ (⨟ᵏ-assoc (r forᵏ α) ⟦ τ' ⟧ᴷ δ')
          (trans≐ᵏ (⨟ᵏ-congʳ (r forᵏ α) h) (sym≐ᵏ (⨟ᵏ-assoc (r forᵏ α) ⟦ τ ⟧ᴷ δ)))

descᵏ-spec : ∀ {n m} → (r : Skel n) → (α : Fin (suc n)) → (t u : Skel (suc n))
           → (τ : SAList n m) → {x : Maybe (Solᵏ n)}
           → Specᵏ (Uniᵏ (t [ r forᵏ α ]ᵏ , u [ r forᵏ α ]ᵏ)) τ x
           → Specᵏ (Uniᵏ (t , u)) (r /ᵏ α ∷ τ) (mmap (consᵏ r α) x)
descᵏ-spec {n} {m} r α t u τ {x} s = specᵏ yes' no'
  where
    down : ∀ {k} → (δ : SSub m k) → Unifies¹ᵏ (t , u) (⟦ r /ᵏ α ∷ τ ⟧ᴷ ⨟ᵏ δ)
         → Unifies¹ᵏ (t [ r forᵏ α ]ᵏ , u [ r forᵏ α ]ᵏ) (⟦ τ ⟧ᴷ ⨟ᵏ δ)
    down δ p = Unifies¹ᵏ-[]ᵏ⁻ t u (r forᵏ α) (⟦ τ ⟧ᴷ ⨟ᵏ δ)
                 (Unifies¹ᵏ-resp≐ (⨟ᵏ-assoc (r forᵏ α) ⟦ τ ⟧ᴷ δ) (t , u) p)

    yes' : ∀ {l} {τ'' : SAList (suc n) l} → mmap (consᵏ r α) x ≡ just (l , τ'')
         → Maxᵏ (Uniᵏ (t , u)) (r /ᵏ α ∷ τ) τ''
    yes' q with map-just (consᵏ r α) x q
    ... | (_ , τ') , q' , refl = maxᵏ (λ δ p →
            let h = fact (onJust s q') δ (down δ p)
            in proj₁ h , glueᵏ r α τ τ' δ (proj₁ h) (proj₂ h))

    no' : mmap (consᵏ r α) x ≡ nothing → ∀ {k} → (δ : SSub m k)
        → ¬ Unifies¹ᵏ (t , u) (⟦ r /ᵏ α ∷ τ ⟧ᴷ ⨟ᵏ δ)
    no' q δ p = onNothing s (map-nothing (consᵏ r α) x q) δ (down δ p)

-- A solution of the binding is recovered from the store by restricting
-- it along the thinning of the bound variable

bindᵏ-max : ∀ {n} → (α : Fin (suc n)) → (t : Skel (suc n)) → {u : Skel n}
          → checkᵏ α t ≡ just u
          → Maxᵏ (Uniᵏ (svar α , t)) anilᵏ (u /ᵏ α ∷ anilᵏ)
bindᵏ-max {n} α t {u} q = maxᵏ lem
  where
    lem : ∀ {k} → (δ : SSub (suc n) k) → at (Uniᵏ (svar α , t) ⋄ᵏ ⟦ anilᵏ ⟧ᴷ) δ
        → Σ[ δ' ∈ SSub n k ] ((⟦ u /ᵏ α ∷ anilᵏ ⟧ᴷ ⨟ᵏ δ') ≐ᵏ (⟦ anilᵏ ⟧ᴷ ⨟ᵏ δ))
    lem {k} δ p = δ' , var
      where
        δ' : SSub n k
        δ' β = δ (punchIn α β)

        hit : u [ δ' ]ᵏ ≡ δ α
        hit = trans (sym ([⨟]ᵏ u (thinᵏ α) δ))
                    (trans (cong (_[ δ ]ᵏ) (checkᵏ-thinᵏ α t q)) (sym p))

        var : (β : Fin (suc n))
            → ((u forᵏ α) β [ idᵏ ]ᵏ) [ δ' ]ᵏ ≡ δ β
        var β with thick α β in r
        ... | just β₀ = cong δ (sym (thick-just α β β₀ r))
        ... | nothing =
              trans (cong (_[ δ' ]ᵏ) ([id]ᵏ u))
                    (trans hit (cong δ (sym (thick-nothing α β r))))

flexᵏ-inv : ∀ {n} → (α : Fin n) → (t : Skel n) → {l : ℕ} → {τ'' : SAList n l}
          → flexᵏ α t ≡ just (l , τ'') → Maxᵏ (Uniᵏ (svar α , t)) anilᵏ τ''
flexᵏ-inv {zero}  ()
flexᵏ-inv {suc n} α t eq
  with map-just (λ t' → n , t' /ᵏ α ∷ anilᵏ) (checkᵏ α t) eq
... | u , q , refl = bindᵏ-max α t q

flexᵏ-no : ∀ {n} → (α : Fin n) → (t : Skel n) → flexᵏ α t ≡ nothing → Occᵏ α t
flexᵏ-no {zero}  ()
flexᵏ-no {suc n} α t eq =
  checkᵏ-nothing α t (map-nothing (λ t' → n , t' /ᵏ α ∷ anilᵏ) (checkᵏ α t) eq)

flexᵏ-spec : ∀ {n} → (α : Fin n) → (t : Skel n) → ¬ (t ≡ svar α)
           → Specᵏ (Uniᵏ (svar α , t)) anilᵏ (flexᵏ α t)
flexᵏ-spec α t nv =
  specᵏ (flexᵏ-inv α t) (λ eq δ p → no-cycleᵏ α δ nv (flexᵏ-no α t eq) p)

flexFlexᵏ-spec : ∀ {n} → (α β : Fin n)
               → Specᵏ (Uniᵏ (svar α , svar β)) anilᵏ (flexFlexᵏ α β)
flexFlexᵏ-spec {n} α β = specᵏ yes' no'
  where
    yes' : ∀ {l} {τ'' : SAList n l} → flexFlexᵏ α β ≡ just (l , τ'')
         → Maxᵏ (Uniᵏ (svar α , svar β)) anilᵏ τ''
    yes' eq with dec-if (α ≟ᶠ β) (just (n , anilᵏ)) (flexᵏ α (svar β)) eq
    ... | inj₁ (r , refl) = Maxᵏ-id
    ... | inj₂ q          = flexᵏ-inv α (svar β) q

    no' : flexFlexᵏ α β ≡ nothing → ∀ {k} → (δ : SSub n k)
        → ¬ Unifies¹ᵏ (svar α , svar β) (⟦ anilᵏ ⟧ᴷ ⨟ᵏ δ)
    no' eq δ p with dec-if-nothing (α ≟ᶠ β) (just (n , anilᵏ)) (flexᵏ α (svar β)) eq
    ... | inj₁ (r , ())
    ... | inj₂ (ne , q) with flexᵏ-no α (svar β) q
    ...   | occ-var = ne refl

amguᵏ-spec : ∀ {n m} → (t u : Skel n) → (τ : SAList n m)
           → Specᵏ (Uniᵏ (t , u)) τ (amguᵏ t u (m , τ))

amguᵏ-spec t u (r /ᵏ α ∷ τ) =
  descᵏ-spec r α t u τ (amguᵏ-spec (t [ r forᵏ α ]ᵏ) (u [ r forᵏ α ]ᵏ) τ)

amguᵏ-spec (svar α)  (svar β)    anilᵏ = flexFlexᵏ-spec α β
amguᵏ-spec (svar α)  (sBase b')  anilᵏ = flexᵏ-spec α (sBase b') (λ ())
amguᵏ-spec (svar α)  sUnit       anilᵏ = flexᵏ-spec α sUnit (λ ())
amguᵏ-spec (svar α)  sBool       anilᵏ = flexᵏ-spec α sBool (λ ())
amguᵏ-spec (svar α) (u₁ s× u₂)   anilᵏ = flexᵏ-spec α (u₁ s× u₂) (λ ())
amguᵏ-spec (svar α)  sEmpty      anilᵏ = flexᵏ-spec α sEmpty (λ ())
amguᵏ-spec (svar α) (u₁ s⇒ u₂)   anilᵏ = flexᵏ-spec α (u₁ s⇒ u₂) (λ ())
amguᵏ-spec (svar α) (sBox u₁)    anilᵏ = flexᵏ-spec α (sBox u₁) (λ ())

amguᵏ-spec (sBase b)   (svar β) anilᵏ = Specᵏ-map sym (flexᵏ-spec β (sBase b) (λ ()))
amguᵏ-spec sUnit       (svar β) anilᵏ = Specᵏ-map sym (flexᵏ-spec β sUnit (λ ()))
amguᵏ-spec sBool       (svar β) anilᵏ = Specᵏ-map sym (flexᵏ-spec β sBool (λ ()))
amguᵏ-spec (t₁ s× t₂)  (svar β) anilᵏ = Specᵏ-map sym (flexᵏ-spec β (t₁ s× t₂) (λ ()))
amguᵏ-spec sEmpty      (svar β) anilᵏ = Specᵏ-map sym (flexᵏ-spec β sEmpty (λ ()))
amguᵏ-spec (t₁ s⇒ t₂)  (svar β) anilᵏ = Specᵏ-map sym (flexᵏ-spec β (t₁ s⇒ t₂) (λ ()))
amguᵏ-spec (sBox t₁)   (svar β) anilᵏ = Specᵏ-map sym (flexᵏ-spec β (sBox t₁) (λ ()))

amguᵏ-spec (sBase b) (sBase b')  anilᵏ = const-specᵏ (b ≡ᵇ? b') (λ δ p → sBase-inj p)
amguᵏ-spec (sBase b) sUnit       anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (sBase b) sBool       anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (sBase b) (u₁ s× u₂)  anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (sBase b) sEmpty      anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (sBase b) (u₁ s⇒ u₂)  anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (sBase b) (sBox u₁)   anilᵏ = clashᵏ (λ δ ())

amguᵏ-spec sUnit (sBase b')      anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sUnit sUnit           anilᵏ = keepᵏ
amguᵏ-spec sUnit sBool           anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sUnit (u₁ s× u₂)      anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sUnit sEmpty          anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sUnit (u₁ s⇒ u₂)      anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sUnit (sBox u₁)       anilᵏ = clashᵏ (λ δ ())

amguᵏ-spec sBool (sBase b')      anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sBool sUnit           anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sBool sBool           anilᵏ = keepᵏ
amguᵏ-spec sBool (u₁ s× u₂)      anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sBool sEmpty          anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sBool (u₁ s⇒ u₂)      anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sBool (sBox u₁)       anilᵏ = clashᵏ (λ δ ())

amguᵏ-spec (t₁ s× t₂) (sBase b') anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (t₁ s× t₂) sUnit      anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (t₁ s× t₂) sBool      anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec {n} (t₁ s× t₂) (u₁ s× u₂) anilᵏ =
  seq-specᵏ (amguᵏ t₁ u₁ (n , anilᵏ)) (amguᵏ t₂ u₂)
            (amguᵏ-spec t₁ u₁ anilᵏ) (amguᵏ-spec t₂ u₂)
            (λ p → s×-inj p)
amguᵏ-spec (t₁ s× t₂) sEmpty     anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (t₁ s× t₂) (u₁ s⇒ u₂) anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (t₁ s× t₂) (sBox u₁)  anilᵏ = clashᵏ (λ δ ())

amguᵏ-spec sEmpty (sBase b')     anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sEmpty sUnit          anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sEmpty sBool          anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sEmpty (u₁ s× u₂)     anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sEmpty sEmpty         anilᵏ = keepᵏ
amguᵏ-spec sEmpty (u₁ s⇒ u₂)     anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec sEmpty (sBox u₁)      anilᵏ = clashᵏ (λ δ ())

amguᵏ-spec (t₁ s⇒ t₂) (sBase b') anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (t₁ s⇒ t₂) sUnit      anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (t₁ s⇒ t₂) sBool      anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (t₁ s⇒ t₂) (u₁ s× u₂) anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (t₁ s⇒ t₂) sEmpty     anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec {n} (t₁ s⇒ t₂) (u₁ s⇒ u₂) anilᵏ =
  seq-specᵏ (amguᵏ t₁ u₁ (n , anilᵏ)) (amguᵏ t₂ u₂)
            (amguᵏ-spec t₁ u₁ anilᵏ) (amguᵏ-spec t₂ u₂)
            (λ p → s⇒-inj p)
amguᵏ-spec (t₁ s⇒ t₂) (sBox u₁)  anilᵏ = clashᵏ (λ δ ())

amguᵏ-spec (sBox t₁) (sBase b')  anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (sBox t₁) sUnit       anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (sBox t₁) sBool       anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (sBox t₁) (u₁ s× u₂)  anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (sBox t₁) sEmpty      anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (sBox t₁) (u₁ s⇒ u₂)  anilᵏ = clashᵏ (λ δ ())
amguᵏ-spec (sBox t₁) (sBox u₁)   anilᵏ =
  Specᵏ-map (λ p → sBox-inj p) (amguᵏ-spec t₁ u₁ anilᵏ)

unifyᴷ-spec : ∀ {n m} → (es : SEqns n) → (τ : SAList n m)
            → Specᵏ (Unisᵏ es) τ (unifyᴷ es (m , τ))
unifyᴷ-spec []             τ = keepᵏ
unifyᴷ-spec {n} {m} ((t , u) ∷ es) τ =
  seq-specᵏ (amguᵏ t u (m , τ)) (unifyᴷ es)
            (amguᵏ-spec t u τ) (λ τ₁ → unifyᴷ-spec es τ₁)
            (λ p → p)

unifyᵏ-max : ∀ {n m} → (es : SEqns n) → {τ : SAList n m}
           → unifyᵏ es ≡ just (m , τ)
           → ∀ {l} → (σ : SSub n l) → Unifiesᵏ es σ
           → Σ[ δ ∈ SSub m l ] ((⟦ τ ⟧ᴷ ⨟ᵏ δ) ≐ᵏ σ)
unifyᵏ-max es eq σ ps = fact (onJust (unifyᴷ-spec es anilᵏ) eq) σ ps

unifyᵏ-fail : ∀ {n} → (es : SEqns n) → unifyᵏ es ≡ nothing
            → ∀ {l} → (σ : SSub n l) → ¬ Unifiesᵏ es σ
unifyᵏ-fail es eq σ ps = onNothing (unifyᴷ-spec es anilᵏ) eq σ ps

private

  -- the store dominates a solution of its own

  σ₁ : SSub 1 0
  σ₁ _ = sBox sUnit

  ex-max : Σ[ δ ∈ SSub 0 0 ]
             ((⟦ sBox sUnit /ᵏ Fin.zero ∷ anilᵏ ⟧ᴷ ⨟ᵏ δ) ≐ᵏ σ₁)
  ex-max = unifyᵏ-max ((svar Fin.zero , sBox sUnit) ∷ []) refl σ₁ (refl , tt)

  -- a shape clash is refuted for every substitution

  ex-clash : ∀ {l} → (σ : SSub 0 l) → ¬ Unifiesᵏ ((sUnit , sBool) ∷ []) σ
  ex-clash = unifyᵏ-fail ((sUnit , sBool) ∷ []) refl

  -- and so is a cyclic demand

  ex-occurs : ∀ {l} → (σ : SSub 1 l)
            → ¬ Unifiesᵏ ((svar Fin.zero , svar Fin.zero s× sUnit) ∷ []) σ
  ex-occurs = unifyᵏ-fail ((svar Fin.zero , svar Fin.zero s× sUnit) ∷ []) refl
