------------------------------------------------------------------
-- Properties of variable expansion                             --
--                                                              --
-- The shape of an open type is its skeleton with all type      --
-- variables identified. Subtyping relates only types of equal  --
-- shape, and `subDec` succeeds exactly on a pair of            --
-- decorations of one skeleton.                                 --
--                                                              --
-- `_◃ᵛ_` states that an open type decorates a skeleton: a type --
-- variable at each skeleton variable and the same former       --
-- everywhere else. `_⊑ᵛ_` relaxes it to an arbitrary type at   --
-- each skeleton variable. `decorate` produces a decoration     --
-- (`decorate-◃`) that is most general among the relaxed ones   --
-- (`decorate-max`).                                            --
--                                                              --
-- `expandSub` makes every demand of its list decomposable      --
-- (`expandSub-dec`); its substitution is most general among    --
-- those that satisfy the demands, and its failure refutes them --
-- (`expandSub-max`).                                           --
------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′) renaming (map to mmap)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec.Base using (Vec; lookup; tabulate)
  renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Vec.Properties using (lookup∘tabulate)

open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Expand (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (_≡ᵇ?_)

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.SolverImpl.Core.Skel         S
open import TypeInference.SolverImpl.Core.SkelUnify    S
open import TypeInference.SolverImpl.Core.SkelUnifySound S using (unifyᵏ-sound)
open import TypeInference.SolverImpl.Core.SkelUnifyMGU   S
  using (unifyᵏ-max; unifyᵏ-fail; s×-inj; s⇒-inj; sBox-inj)
open import TypeInference.SolverImpl.Core.Decorate     S
open import TypeInference.SolverImpl.Core.Rigid        S using (zip₂)

open import TypeInference.SolverImpl.Resid S

-- Shapes: skeletons over a single variable, in which all type variables
-- are identified.

mutual

  shapeᵛ : ∀ {Ψ} → OVType Ψ → Skel 1
  shapeᵛ (tvar α)  = svar zero
  shapeᵛ (Base b)  = sBase b
  shapeᵛ Unit      = sUnit
  shapeᵛ Bool      = sBool
  shapeᵛ (A |×| B) = shapeᵛ A s× shapeᵛ B
  shapeᵛ Empty     = sEmpty
  shapeᵛ (A ⇒ C)   = shapeᵛ A s⇒ shapeᶜ C
  shapeᵛ ([ ρ ] A) = sBox shapeᵛ A

  shapeᶜ : ∀ {Ψ} → OCType Ψ → Skel 1
  shapeᶜ (A ‼ ε) = shapeᵛ A

-- The shapes a substitution gives the type variables

shapeˢ : ∀ {Ψ Ψ'} → Subst Ψ Ψ' → SSub (nTy Ψ) 1
shapeˢ δ α = shapeᵛ (sTy δ α)

mutual

  shape-[]ᵛ : ∀ {Ψ Ψ'} → (A : OVType Ψ) → (δ : Subst Ψ Ψ')
            → shapeᵛ (A [ δ ]ᵛ) ≡ skelᵛ A [ shapeˢ δ ]ᵏ
  shape-[]ᵛ (tvar α)  δ = refl
  shape-[]ᵛ (Base b)  δ = refl
  shape-[]ᵛ Unit      δ = refl
  shape-[]ᵛ Bool      δ = refl
  shape-[]ᵛ (A |×| B) δ = cong₂ _s×_ (shape-[]ᵛ A δ) (shape-[]ᵛ B δ)
  shape-[]ᵛ Empty     δ = refl
  shape-[]ᵛ (A ⇒ C)   δ = cong₂ _s⇒_ (shape-[]ᵛ A δ) (shape-[]ᶜ C δ)
  shape-[]ᵛ ([ ρ ] A) δ = cong sBox_ (shape-[]ᵛ A δ)

  shape-[]ᶜ : ∀ {Ψ Ψ'} → (C : OCType Ψ) → (δ : Subst Ψ Ψ')
            → shapeᶜ (C [ δ ]ᶜ) ≡ skelᶜ C [ shapeˢ δ ]ᵏ
  shape-[]ᶜ (A ‼ ε) δ = shape-[]ᵛ A δ

-- Subtyping preserves the shape

mutual

  <:̂ᵛ-shape : ∀ {Θ} {Q : Hyps Θ} {A B} → Q ∣ A <:̂ᵛ B → shapeᵛ A ≡ shapeᵛ B
  <:̂ᵛ-shape (tvarₛ p)    = refl
  <:̂ᵛ-shape (Baseₛ refl) = refl
  <:̂ᵛ-shape Unitₛ        = refl
  <:̂ᵛ-shape Boolₛ        = refl
  <:̂ᵛ-shape (p |×|ₛ q)   = cong₂ _s×_ (<:̂ᵛ-shape p) (<:̂ᵛ-shape q)
  <:̂ᵛ-shape Emptyₛ       = refl
  <:̂ᵛ-shape (p ⇒ₛ q)     = cong₂ _s⇒_ (sym (<:̂ᵛ-shape p)) (<:̂ᶜ-shape q)
  <:̂ᵛ-shape ([ r ]ₛ p)   = cong sBox_ (<:̂ᵛ-shape p)

  <:̂ᶜ-shape : ∀ {Θ} {Q : Hyps Θ} {C D} → Q ∣ C <:̂ᶜ D → shapeᶜ C ≡ shapeᶜ D
  <:̂ᶜ-shape (p ‼ₛ r) = <:̂ᵛ-shape p

-- An open type refines a skeleton when it has the same formers
-- outside the skeleton's variables

infix 4 _⊑ᵛ_ _⊑ᶜ_

data _⊑ᵛ_ {Ψ : Scope} {n : ℕ} : Skel n → OVType Ψ → Set
data _⊑ᶜ_ {Ψ : Scope} {n : ℕ} : Skel n → OCType Ψ → Set

data _⊑ᵛ_ {Ψ} {n} where
  var⊑   : ∀ {γ A} → svar γ ⊑ᵛ A
  Base⊑  : ∀ {b} → sBase {n} b ⊑ᵛ Base {Ψ} b
  Unit⊑  : sUnit {n} ⊑ᵛ Unit {Ψ}
  Bool⊑  : sBool {n} ⊑ᵛ Bool {Ψ}
  _×⊑_   : ∀ {t u A B} → t ⊑ᵛ A → u ⊑ᵛ B → (t s× u) ⊑ᵛ (A |×| B)
  Empty⊑ : sEmpty {n} ⊑ᵛ Empty {Ψ}
  _⇒⊑_   : ∀ {t u A C} → t ⊑ᵛ A → u ⊑ᶜ C → (t s⇒ u) ⊑ᵛ (A ⇒ C)
  Box⊑   : ∀ {t A ρ} → t ⊑ᵛ A → sBox t ⊑ᵛ ([ ρ ] A)

data _⊑ᶜ_ {Ψ} {n} where
  ‼⊑ : ∀ {t A ε} → t ⊑ᵛ A → t ⊑ᶜ (A ‼ ε)

-- A skeleton whose instance has a type's shape refines that type

mutual

  ⊑-from : ∀ {Ψ n} → (t : Skel n) → (ζ : SSub n 1) → (A : OVType Ψ)
         → t [ ζ ]ᵏ ≡ shapeᵛ A → t ⊑ᵛ A
  ⊑-from (svar γ)  ζ A           eq   = var⊑
  ⊑-from (sBase b) ζ (tvar α)    ()
  ⊑-from (sBase b) ζ (Base b')   refl = Base⊑
  ⊑-from (sBase b) ζ Unit        ()
  ⊑-from (sBase b) ζ Bool        ()
  ⊑-from (sBase b) ζ (A |×| B)   ()
  ⊑-from (sBase b) ζ Empty       ()
  ⊑-from (sBase b) ζ (A ⇒ C)     ()
  ⊑-from (sBase b) ζ ([ ρ ] A)   ()
  ⊑-from sUnit     ζ (tvar α)    ()
  ⊑-from sUnit     ζ (Base b')   ()
  ⊑-from sUnit     ζ Unit        refl = Unit⊑
  ⊑-from sUnit     ζ Bool        ()
  ⊑-from sUnit     ζ (A |×| B)   ()
  ⊑-from sUnit     ζ Empty       ()
  ⊑-from sUnit     ζ (A ⇒ C)     ()
  ⊑-from sUnit     ζ ([ ρ ] A)   ()
  ⊑-from sBool     ζ (tvar α)    ()
  ⊑-from sBool     ζ (Base b')   ()
  ⊑-from sBool     ζ Unit        ()
  ⊑-from sBool     ζ Bool        refl = Bool⊑
  ⊑-from sBool     ζ (A |×| B)   ()
  ⊑-from sBool     ζ Empty       ()
  ⊑-from sBool     ζ (A ⇒ C)     ()
  ⊑-from sBool     ζ ([ ρ ] A)   ()
  ⊑-from (t s× u)  ζ (tvar α)    ()
  ⊑-from (t s× u)  ζ (Base b')   ()
  ⊑-from (t s× u)  ζ Unit        ()
  ⊑-from (t s× u)  ζ Bool        ()
  ⊑-from (t s× u)  ζ (A |×| B)   eq   =
    ⊑-from t ζ A (proj₁ (s×-inj eq)) ×⊑ ⊑-from u ζ B (proj₂ (s×-inj eq))
  ⊑-from (t s× u)  ζ Empty       ()
  ⊑-from (t s× u)  ζ (A ⇒ C)     ()
  ⊑-from (t s× u)  ζ ([ ρ ] A)   ()
  ⊑-from sEmpty    ζ (tvar α)    ()
  ⊑-from sEmpty    ζ (Base b')   ()
  ⊑-from sEmpty    ζ Unit        ()
  ⊑-from sEmpty    ζ Bool        ()
  ⊑-from sEmpty    ζ (A |×| B)   ()
  ⊑-from sEmpty    ζ Empty       refl = Empty⊑
  ⊑-from sEmpty    ζ (A ⇒ C)     ()
  ⊑-from sEmpty    ζ ([ ρ ] A)   ()
  ⊑-from (t s⇒ u)  ζ (tvar α)    ()
  ⊑-from (t s⇒ u)  ζ (Base b')   ()
  ⊑-from (t s⇒ u)  ζ Unit        ()
  ⊑-from (t s⇒ u)  ζ Bool        ()
  ⊑-from (t s⇒ u)  ζ (A |×| B)   ()
  ⊑-from (t s⇒ u)  ζ Empty       ()
  ⊑-from (t s⇒ u)  ζ (A ⇒ C)     eq   =
    ⊑-from t ζ A (proj₁ (s⇒-inj eq)) ⇒⊑ ⊑-fromᶜ u ζ C (proj₂ (s⇒-inj eq))
  ⊑-from (t s⇒ u)  ζ ([ ρ ] A)   ()
  ⊑-from (sBox t)  ζ (tvar α)    ()
  ⊑-from (sBox t)  ζ (Base b')   ()
  ⊑-from (sBox t)  ζ Unit        ()
  ⊑-from (sBox t)  ζ Bool        ()
  ⊑-from (sBox t)  ζ (A |×| B)   ()
  ⊑-from (sBox t)  ζ Empty       ()
  ⊑-from (sBox t)  ζ (A ⇒ C)     ()
  ⊑-from (sBox t)  ζ ([ ρ ] A)   eq   = Box⊑ (⊑-from t ζ A (sBox-inj eq))

  ⊑-fromᶜ : ∀ {Ψ n} → (t : Skel n) → (ζ : SSub n 1) → (C : OCType Ψ)
          → t [ ζ ]ᵏ ≡ shapeᶜ C → t ⊑ᶜ C
  ⊑-fromᶜ t ζ (A ‼ ε) eq = ‼⊑ (⊑-from t ζ A eq)

-- An open type decorates a skeleton when it refines it with a type
-- variable at every skeleton variable

infix 4 _◃ᵛ_ _◃ᶜ_

data _◃ᵛ_ {Ψ : Scope} {n : ℕ} : Skel n → OVType Ψ → Set
data _◃ᶜ_ {Ψ : Scope} {n : ℕ} : Skel n → OCType Ψ → Set

data _◃ᵛ_ {Ψ} {n} where
  var◃   : ∀ {γ α} → svar γ ◃ᵛ tvar α
  Base◃  : ∀ {b} → sBase {n} b ◃ᵛ Base {Ψ} b
  Unit◃  : sUnit {n} ◃ᵛ Unit {Ψ}
  Bool◃  : sBool {n} ◃ᵛ Bool {Ψ}
  _×◃_   : ∀ {t u A B} → t ◃ᵛ A → u ◃ᵛ B → (t s× u) ◃ᵛ (A |×| B)
  Empty◃ : sEmpty {n} ◃ᵛ Empty {Ψ}
  _⇒◃_   : ∀ {t u A C} → t ◃ᵛ A → u ◃ᶜ C → (t s⇒ u) ◃ᵛ (A ⇒ C)
  Box◃   : ∀ {t A ρ} → t ◃ᵛ A → sBox t ◃ᵛ ([ ρ ] A)

data _◃ᶜ_ {Ψ} {n} where
  ‼◃ : ∀ {t A ε} → t ◃ᵛ A → t ◃ᶜ (A ‼ ε)

-- Two decorations of one skeleton decompose

mutual

  ◃-subDec : ∀ {Ψ n} {t : Skel n} {A B : OVType Ψ} → t ◃ᵛ A → t ◃ᵛ B
           → Σ[ d ∈ SubDec A B ] (subDec A B ≡ just d)
  ◃-subDec var◃      var◃      = _ , refl
  ◃-subDec (Base◃ {b}) Base◃ with b ≡ᵇ? b
  ... | yes refl = _ , refl
  ... | no ¬p    = ⊥-elim (¬p refl)
  ◃-subDec Unit◃     Unit◃     = _ , refl
  ◃-subDec Bool◃     Bool◃     = _ , refl
  ◃-subDec Empty◃    Empty◃    = _ , refl
  ◃-subDec (p ×◃ q)  (p' ×◃ q') =
    _ , cong₂ (zip₂ pairᴰ) (proj₂ (◃-subDec p p')) (proj₂ (◃-subDec q q'))
  ◃-subDec (p ⇒◃ q)  (p' ⇒◃ q') =
    _ , cong₂ (zip₂ arrᴰ) (proj₂ (◃-subDec p' p)) (proj₂ (◃-subDecᶜ q q'))
  ◃-subDec (Box◃ p)  (Box◃ p') =
    _ , cong (mmap (boxᴰ _ _)) (proj₂ (◃-subDec p p'))

  ◃-subDecᶜ : ∀ {Ψ n} {t : Skel n} {C D : OCType Ψ} → t ◃ᶜ C → t ◃ᶜ D
            → Σ[ d ∈ SubDecᶜ C D ] (subDecᶜ C D ≡ just d)
  ◃-subDecᶜ (‼◃ p) (‼◃ q) = _ , cong (mmap (bangᴰ _ _)) (proj₂ (◃-subDec p q))

-- A decoration of a store decorates every skeleton through it

mutual

  ◃-skel : ∀ {Ψ Ψ' n} → (A : OVType Ψ) → {τ : SSub (nTy Ψ) n} → {ω : Subst Ψ Ψ'}
         → ((α : TyVar Ψ) → τ α ◃ᵛ sTy ω α) → (skelᵛ A [ τ ]ᵏ) ◃ᵛ (A [ ω ]ᵛ)
  ◃-skel (tvar α)  k = k α
  ◃-skel (Base b)  k = Base◃
  ◃-skel Unit      k = Unit◃
  ◃-skel Bool      k = Bool◃
  ◃-skel (A |×| B) k = ◃-skel A k ×◃ ◃-skel B k
  ◃-skel Empty     k = Empty◃
  ◃-skel (A ⇒ C)   k = ◃-skel A k ⇒◃ ◃-skelᶜ C k
  ◃-skel ([ ρ ] A) k = Box◃ (◃-skel A k)

  ◃-skelᶜ : ∀ {Ψ Ψ' n} → (C : OCType Ψ) → {τ : SSub (nTy Ψ) n} → {ω : Subst Ψ Ψ'}
          → ((α : TyVar Ψ) → τ α ◃ᵛ sTy ω α) → (skelᶜ C [ τ ]ᵏ) ◃ᶜ (C [ ω ]ᶜ)
  ◃-skelᶜ (A ‼ ε) k = ‼◃ (◃-skel A k)

-- A substitution that renames the type variables

record TyRen {Ψ Ψ' : Scope} (w : Subst Ψ Ψ') : Set where
  constructor tyren
  field tyRen : (α : TyVar Ψ) → Σ[ β ∈ TyVar Ψ' ] (sTy w α ≡ tvar β)

open TyRen public

TyRen-idˢ : ∀ {Ψ} → TyRen (idˢ {Ψ})
TyRen-idˢ = tyren (λ α → α , refl)

TyRen-wkᵗ : ∀ {Ψ} → TyRen (wkˢᵗ {Ψ})
TyRen-wkᵗ {Ψ} = tyren (λ α → wkᵗ-tv Ψ α , refl)

TyRen-wkʳ : ∀ {Ψ} → TyRen (wkˢʳ {Ψ})
TyRen-wkʳ {Ψ} = tyren (λ α → wkʳ-tv Ψ α , refl)

TyRen-wkᵉ : ∀ {Ψ} → TyRen (wkˢᵉ {Ψ})
TyRen-wkᵉ {Ψ} = tyren (λ α → wkᵉ-tv Ψ α , refl)

TyRen-⨟ : ∀ {Ψ Ψ₁ Ψ'} {w : Subst Ψ Ψ₁} {w' : Subst Ψ₁ Ψ'}
        → TyRen w → TyRen w' → TyRen (w ⨟ˢ w')
TyRen-⨟ {Ψ} {Ψ₁} {Ψ'} {w} {w'} r r' = tyren f
  where
    f : (α : TyVar Ψ) → Σ[ β ∈ TyVar Ψ' ] (sTy (w ⨟ˢ w') α ≡ tvar β)
    f α with tyRen r α
    ... | β , q with tyRen r' β
    ...   | γ , q' = γ , trans (cong (_[ w' ]ᵛ) q) q'

mutual

  ◃-ren : ∀ {Ψ Ψ' n} {t : Skel n} {A : OVType Ψ} {σ : Subst Ψ Ψ'}
        → TyRen σ → t ◃ᵛ A → t ◃ᵛ (A [ σ ]ᵛ)
  ◃-ren {t = svar γ} r (var◃ {α = α}) with tyRen r α
  ... | β , q = subst (svar γ ◃ᵛ_) (sym q) var◃
  ◃-ren r Base◃     = Base◃
  ◃-ren r Unit◃     = Unit◃
  ◃-ren r Bool◃     = Bool◃
  ◃-ren r (p ×◃ q)  = ◃-ren r p ×◃ ◃-ren r q
  ◃-ren r Empty◃    = Empty◃
  ◃-ren r (p ⇒◃ q)  = ◃-ren r p ⇒◃ ◃-renᶜ r q
  ◃-ren r (Box◃ p)  = Box◃ (◃-ren r p)

  ◃-renᶜ : ∀ {Ψ Ψ' n} {t : Skel n} {C : OCType Ψ} {σ : Subst Ψ Ψ'}
         → TyRen σ → t ◃ᶜ C → t ◃ᶜ (C [ σ ]ᶜ)
  ◃-renᶜ r (‼◃ p) = ‼◃ (◃-ren r p)

◃-wkʳ : ∀ {Ψ n} {t : Skel n} {A : OVType Ψ} → t ◃ᵛ A → t ◃ᵛ wkʳ-v A
◃-wkʳ {t = t} {A = A} d = subst (t ◃ᵛ_) (wkˢʳ-v A) (◃-ren TyRen-wkʳ d)

◃-wkᵉ : ∀ {Ψ n} {t : Skel n} {A : OVType Ψ} → t ◃ᵛ A → t ◃ᵛ wkᵉ-v A
◃-wkᵉ {t = t} {A = A} d = subst (t ◃ᵛ_) (wkˢᵉ-v A) (◃-ren TyRen-wkᵉ d)

-- `decorate` renames the given type variables and produces a decoration

Dec◃ : ∀ {m} → (Ψ : Scope) → Skel m
     → Σ[ Ψ' ∈ Scope ] (Subst Ψ Ψ' × OVType Ψ') → Set
Dec◃ Ψ t (Ψ' , w , A) = TyRen w × (t ◃ᵛ A)

decorate-◃ : ∀ {m} → (Ψ : Scope) → (t : Skel m) → Dec◃ Ψ t (decorate Ψ t)
decorate-◃ Ψ (svar γ)  = TyRen-wkᵗ , var◃
decorate-◃ Ψ (sBase b) = TyRen-idˢ , Base◃
decorate-◃ Ψ sUnit     = TyRen-idˢ , Unit◃
decorate-◃ Ψ sBool     = TyRen-idˢ , Bool◃
decorate-◃ Ψ sEmpty    = TyRen-idˢ , Empty◃
decorate-◃ Ψ (t s× u) with decorate Ψ t | decorate-◃ Ψ t
... | Ψ₁ , w₁ , A | r₁ , d₁ with decorate Ψ₁ u | decorate-◃ Ψ₁ u
...   | Ψ₂ , w₂ , B | r₂ , d₂ = TyRen-⨟ r₁ r₂ , (◃-ren r₂ d₁ ×◃ d₂)
decorate-◃ Ψ (t s⇒ u) with decorate Ψ t | decorate-◃ Ψ t
... | Ψ₁ , w₁ , A | r₁ , d₁ with decorate Ψ₁ u | decorate-◃ Ψ₁ u
...   | Ψ₂ , w₂ , B | r₂ , d₂ =
        TyRen-⨟ (TyRen-⨟ r₁ r₂) TyRen-wkᵉ ,
        (◃-wkᵉ (◃-ren r₂ d₁) ⇒◃ ‼◃ (◃-wkᵉ d₂))
decorate-◃ Ψ (sBox t) with decorate Ψ t | decorate-◃ Ψ t
... | Ψ₁ , w₁ , A | r₁ , d₁ = TyRen-⨟ r₁ TyRen-wkʳ , Box◃ (◃-wkʳ d₁)

-- A refinement of the skeleton is an instance of its decoration

wkʳ-inst : ∀ {Ψ Ψ'} → (A : OVType Ψ) → (δ : Subst Ψ Ψ') → (ρ : RExp Ψ')
         → wkʳ-v A [ δ ,ʳ ρ ]ᵛ ≡ A [ δ ]ᵛ
wkʳ-inst A δ ρ = trans (cong (_[ δ ,ʳ ρ ]ᵛ) (sym (wkˢʳ-v A)))
                       (trans ([⨟]ᵛ A wkˢʳ (δ ,ʳ ρ)) ([≐]ᵛ (wkˢʳ-,ʳ δ ρ) A))

wkᵉ-inst : ∀ {Ψ Ψ'} → (A : OVType Ψ) → (δ : Subst Ψ Ψ') → (ε : EExp Ψ')
         → wkᵉ-v A [ δ ,ᵉ ε ]ᵛ ≡ A [ δ ]ᵛ
wkᵉ-inst A δ ε = trans (cong (_[ δ ,ᵉ ε ]ᵛ) (sym (wkˢᵉ-v A)))
                       (trans ([⨟]ᵛ A wkˢᵉ (δ ,ᵉ ε)) ([≐]ᵛ (wkˢᵉ-,ᵉ δ ε) A))

DecMax : ∀ {Ψ Ψ''} → Subst Ψ Ψ'' → OVType Ψ''
       → Σ[ Ψ' ∈ Scope ] (Subst Ψ Ψ' × OVType Ψ') → Set
DecMax {Ψ'' = Ψ''} δ A₀ (Ψ' , w , A) =
  Σ[ δ₁ ∈ Subst Ψ' Ψ'' ] (((w ⨟ˢ δ₁) ≐ˢ δ) × (A [ δ₁ ]ᵛ ≡ A₀))

decorate-max : ∀ {m Ψ''} → (Ψ : Scope) → (t : Skel m) → (δ : Subst Ψ Ψ'')
             → {A₀ : OVType Ψ''} → t ⊑ᵛ A₀ → DecMax δ A₀ (decorate Ψ t)
decorate-max Ψ (svar γ)  δ {A₀} var⊑ = (δ ,ᵗ A₀) , wkˢᵗ-,ᵗ δ A₀ , refl
decorate-max Ψ (sBase b) δ Base⊑  = δ , ⨟-idˡ δ , refl
decorate-max Ψ sUnit     δ Unit⊑  = δ , ⨟-idˡ δ , refl
decorate-max Ψ sBool     δ Bool⊑  = δ , ⨟-idˡ δ , refl
decorate-max Ψ sEmpty    δ Empty⊑ = δ , ⨟-idˡ δ , refl
decorate-max Ψ (t s× u) δ (p ×⊑ q) with decorate Ψ t | decorate-max Ψ t δ p
... | Ψ₁ , w₁ , A | δ₁ , tri₁ , eq₁ with decorate Ψ₁ u | decorate-max Ψ₁ u δ₁ q
...   | Ψ₂ , w₂ , B | δ₂ , tri₂ , eq₂ =
        δ₂ ,
        ≐ˢ-trans (⨟-assoc w₁ w₂ δ₂) (≐ˢ-trans (⨟-congʳ w₁ tri₂) tri₁) ,
        cong₂ _|×|_ (trans ([⨟]ᵛ A w₂ δ₂) (trans ([≐]ᵛ tri₂ A) eq₁)) eq₂
decorate-max Ψ (t s⇒ u) δ {_ ⇒ (_ ‼ ε)} (p ⇒⊑ ‼⊑ q)
  with decorate Ψ t | decorate-max Ψ t δ p
... | Ψ₁ , w₁ , A | δ₁ , tri₁ , eq₁ with decorate Ψ₁ u | decorate-max Ψ₁ u δ₁ q
...   | Ψ₂ , w₂ , B | δ₂ , tri₂ , eq₂ =
        (δ₂ ,ᵉ ε) ,
        ≐ˢ-trans (⨟-assoc (w₁ ⨟ˢ w₂) wkˢᵉ (δ₂ ,ᵉ ε))
          (≐ˢ-trans (⨟-congʳ (w₁ ⨟ˢ w₂) (wkˢᵉ-,ᵉ δ₂ ε))
            (≐ˢ-trans (⨟-assoc w₁ w₂ δ₂) (≐ˢ-trans (⨟-congʳ w₁ tri₂) tri₁))) ,
        cong₂ _⇒_
          (trans (wkᵉ-inst (A [ w₂ ]ᵛ) δ₂ ε)
                 (trans ([⨟]ᵛ A w₂ δ₂) (trans ([≐]ᵛ tri₂ A) eq₁)))
          (cong (_‼ ε) (trans (wkᵉ-inst B δ₂ ε) eq₂))
decorate-max Ψ (sBox t) δ {[ ρ ] _} (Box⊑ p) with decorate Ψ t | decorate-max Ψ t δ p
... | Ψ₁ , w₁ , A | δ₁ , tri₁ , eq₁ =
      (δ₁ ,ʳ ρ) ,
      ≐ˢ-trans (⨟-assoc w₁ wkˢʳ (δ₁ ,ʳ ρ))
               (≐ˢ-trans (⨟-congʳ w₁ (wkˢʳ-,ʳ δ₁ ρ)) tri₁) ,
      cong ([ ρ ]_) (trans (wkʳ-inst A δ₁ ρ) eq₁)

-- The same, for a whole vector: an entry left undecorated is one
-- whose skeleton is still a variable.

Ent◃ : ∀ {Ψ' m} → Skel m → Maybe (OVType Ψ') → Set
Ent◃ {m = m} t nothing  = Σ[ γ ∈ Fin m ] (t ≡ svar γ)
Ent◃         t (just A) = t ◃ᵛ A

Dec*◃ : ∀ {m k} → (Ψ : Scope) → Vec (Skel m) k
      → Σ[ Ψ' ∈ Scope ] (Subst Ψ Ψ' × Vec (Maybe (OVType Ψ')) k) → Set
Dec*◃ {k = k} Ψ ts (Ψ' , w , As) =
  TyRen w × ((i : Fin k) → Ent◃ (lookup ts i) (lookup As i))

decorate*-◃ : ∀ {m k} → (Ψ : Scope) → (ts : Vec (Skel m) k)
            → Dec*◃ Ψ ts (decorate* Ψ ts)
decorate*-◃ Ψ []ⱽ        = TyRen-idˢ , λ ()
decorate*-◃ Ψ (t ∷ⱽ ts) with svar? t in e
... | just γ with decorate* Ψ ts | decorate*-◃ Ψ ts
...   | Ψ' , w , As | r , k =
        r , λ { zero → γ , svar?-just t e ; (suc i) → k i }
decorate*-◃ Ψ (t ∷ⱽ ts) | nothing with decorate Ψ t | decorate-◃ Ψ t
... | Ψ₁ , w₁ , A | r₁ , d₁ with decorate* Ψ₁ ts | decorate*-◃ Ψ₁ ts
...   | Ψ₂ , w₂ , As | r₂ , k =
        TyRen-⨟ r₁ r₂ , λ { zero → ◃-ren r₂ d₁ ; (suc i) → k i }

Mt : ∀ {Ψ' Ψ''} → Maybe (OVType Ψ') → OVType Ψ'' → Subst Ψ' Ψ'' → Set
Mt nothing  A₀ δ₁ = ⊤
Mt (just A) A₀ δ₁ = A [ δ₁ ]ᵛ ≡ A₀

Dec*Max : ∀ {Ψ Ψ'' k} → Subst Ψ Ψ'' → Vec (OVType Ψ'') k
        → Σ[ Ψ' ∈ Scope ] (Subst Ψ Ψ' × Vec (Maybe (OVType Ψ')) k) → Set
Dec*Max {Ψ'' = Ψ''} {k = k} δ A₀s (Ψ' , w , As) =
  Σ[ δ₁ ∈ Subst Ψ' Ψ'' ]
    (((w ⨟ˢ δ₁) ≐ˢ δ) × ((i : Fin k) → Mt (lookup As i) (lookup A₀s i) δ₁))

decorate*-max : ∀ {m k Ψ''} → (Ψ : Scope) → (ts : Vec (Skel m) k) → (δ : Subst Ψ Ψ'')
              → (A₀s : Vec (OVType Ψ'') k)
              → ((i : Fin k) → lookup ts i ⊑ᵛ lookup A₀s i)
              → Dec*Max δ A₀s (decorate* Ψ ts)
decorate*-max Ψ []ⱽ δ []ⱽ ps = δ , ⨟-idˡ δ , λ ()
decorate*-max Ψ (t ∷ⱽ ts) δ (A₀ ∷ⱽ A₀s) ps with svar? t
... | just γ with decorate* Ψ ts | decorate*-max Ψ ts δ A₀s (λ i → ps (suc i))
...   | Ψ' , w , As | δ₁ , tri , ms = δ₁ , tri , λ { zero → tt ; (suc i) → ms i }
decorate*-max Ψ (t ∷ⱽ ts) δ (A₀ ∷ⱽ A₀s) ps | nothing
  with decorate Ψ t | decorate-max Ψ t δ (ps zero)
... | Ψ₁ , w₁ , A | δ₁ , tri₁ , eq₁
  with decorate* Ψ₁ ts | decorate*-max Ψ₁ ts δ₁ A₀s (λ i → ps (suc i))
...   | Ψ₂ , w₂ , As | δ₂ , tri₂ , ms =
        δ₂ , ≐ˢ-trans (⨟-assoc w₁ w₂ δ₂) (≐ˢ-trans (⨟-congʳ w₁ tri₂) tri₁) ,
        λ { zero → trans ([⨟]ᵛ A w₂ δ₂) (trans ([≐]ᵛ tri₂ A) eq₁)
          ; (suc i) → ms i }

-- Properties of the refinement of a whole store

Expᵏ◃ : ∀ {m} → (Ψ : Scope) → SSub (nTy Ψ) m → Σ[ Ψ' ∈ Scope ] (Subst Ψ Ψ') → Set
Expᵏ◃ Ψ σ x = (α : TyVar Ψ) → σ α ◃ᵛ sTy (proj₂ x) α

expandᵏ-◃ : ∀ {m} → (Ψ : Scope) → (σ : SSub (nTy Ψ) m) → Expᵏ◃ Ψ σ (expandᵏ Ψ σ)
expandᵏ-◃ Ψ σ with decorate* Ψ (tabulate σ) | decorate*-◃ Ψ (tabulate σ)
... | Ψ' , w , As | r , k = g
  where
    g : (α : TyVar Ψ) → σ α ◃ᵛ maybe′ (λ A → A) (sTy w α) (lookup As α)
    g α with lookup As α | k α
    ... | just A  | d     = subst (_◃ᵛ A) (lookup∘tabulate σ α) d
    ... | nothing | γ , q with tyRen r α
    ...   | β , q' =
            subst₂ _◃ᵛ_ (trans (sym q) (lookup∘tabulate σ α)) (sym q') (var◃ {γ = γ})

Expᵏmax : ∀ {m Ψ''} → (Ψ : Scope) → SSub (nTy Ψ) m → Subst Ψ Ψ''
        → Σ[ Ψ' ∈ Scope ] (Subst Ψ Ψ') → Set
Expᵏmax {Ψ'' = Ψ''} Ψ σ δ x = Σ[ δ' ∈ Subst (proj₁ x) Ψ'' ] ((proj₂ x ⨟ˢ δ') ≐ˢ δ)

expandᵏ-max : ∀ {m Ψ''} → (Ψ : Scope) → (σ : SSub (nTy Ψ) m) → (δ : Subst Ψ Ψ'')
            → ((α : TyVar Ψ) → σ α ⊑ᵛ sTy δ α) → Expᵏmax Ψ σ δ (expandᵏ Ψ σ)
expandᵏ-max Ψ σ δ ps
  with decorate* Ψ (tabulate σ)
     | decorate*-max Ψ (tabulate σ) δ (tabulate (sTy δ))
         (λ α → subst₂ _⊑ᵛ_ (sym (lookup∘tabulate σ α))
                            (sym (lookup∘tabulate (sTy δ) α)) (ps α))
... | Ψ' , w , As | δ₁ , tri , ms =
      δ₁ , mk≐ˢ tyq (λ i → ≐ʳ tri i) (λ i → ≐ᵉ tri i)
  where
    tyq : (α : TyVar Ψ)
        → maybe′ (λ A → A) (sTy w α) (lookup As α) [ δ₁ ]ᵛ ≡ sTy δ α
    tyq α with lookup As α | ms α
    ... | just A  | m = trans m (lookup∘tabulate (sTy δ) α)
    ... | nothing | _ = ≐ᵗ tri α

-- Unification of a list of demands, atom by atom

unifies-∈ : ∀ {Ψ n} → (l : List (OVType Ψ × OVType Ψ)) → (σ : SSub (nTy Ψ) n)
          → Unifiesᵏ (skelEqns l) σ
          → ∀ {A B} → (A , B) ∈ l → skelᵛ A [ σ ]ᵏ ≡ skelᵛ B [ σ ]ᵏ
unifies-∈ ((A , B) ∷ l) σ (u , us) (here refl) = u
unifies-∈ ((A , B) ∷ l) σ (u , us) (there m)   = unifies-∈ l σ us m

unifies⁺ : ∀ {Ψ n} → (l : List (OVType Ψ × OVType Ψ)) → (σ : SSub (nTy Ψ) n)
         → (∀ {A B} → (A , B) ∈ l → skelᵛ A [ σ ]ᵏ ≡ skelᵛ B [ σ ]ᵏ)
         → Unifiesᵏ (skelEqns l) σ
unifies⁺ []             σ k = tt
unifies⁺ ((A , B) ∷ l) σ k = k (here refl) , unifies⁺ l σ (λ m → k (there m))

-- The shapes of a substitution satisfying every demand unify the
-- demands' skeletons

shape-unifies : ∀ {Ψ Ψ''} {Q : Hyps Ψ''} → (l : List (OVType Ψ × OVType Ψ))
              → (δ₀ : Subst Ψ Ψ'')
              → (∀ {A B} → (A , B) ∈ l → Q ∣ A [ δ₀ ]ᵛ <:̂ᵛ B [ δ₀ ]ᵛ)
              → Unifiesᵏ (skelEqns l) (shapeˢ δ₀)
shape-unifies l δ₀ k =
  unifies⁺ l (shapeˢ δ₀)
    (λ {A} {B} m → trans (sym (shape-[]ᵛ A δ₀))
                         (trans (<:̂ᵛ-shape (k m)) (shape-[]ᵛ B δ₀)))

Expᵏdec : ∀ {Ψ} → List (OVType Ψ × OVType Ψ)
        → Σ[ Ψ' ∈ Scope ] (Subst Ψ Ψ') → Set
Expᵏdec l x = ∀ {A B} → (A , B) ∈ l
            → Σ[ d ∈ SubDec (A [ proj₂ x ]ᵛ) (B [ proj₂ x ]ᵛ) ]
                (subDec (A [ proj₂ x ]ᵛ) (B [ proj₂ x ]ᵛ) ≡ just d)

ExpDec : ∀ {Ψ} → List (OVType Ψ × OVType Ψ)
       → Maybe (Σ[ Ψ' ∈ Scope ] (Subst Ψ Ψ')) → Set
ExpDec l = maybe′ (Expᵏdec l) ⊤

-- Every pair the expansion was asked about decomposes afterwards

expandSub-dec : ∀ {Ψ} → (l : List (OVType Ψ × OVType Ψ)) → ExpDec l (expandSub l)
expandSub-dec {Ψ} l with unifyᵏ (skelEqns l) in e
... | nothing      = tt
... | just (m , τ) = f
  where
    dec : (A : OVType Ψ) → (skelᵛ A [ ⟦ τ ⟧ᴷ ]ᵏ) ◃ᵛ (A [ proj₂ (expandᵏ Ψ ⟦ τ ⟧ᴷ) ]ᵛ)
    dec A = ◃-skel A (expandᵏ-◃ Ψ ⟦ τ ⟧ᴷ)

    f : Expᵏdec l (expandᵏ Ψ ⟦ τ ⟧ᴷ)
    f {A} {B} mem =
      ◃-subDec (dec A)
               (subst (_◃ᵛ (B [ proj₂ (expandᵏ Ψ ⟦ τ ⟧ᴷ) ]ᵛ))
                      (sym (unifies-∈ l ⟦ τ ⟧ᴷ (unifyᵏ-sound (skelEqns l) e) mem))
                      (dec B))

ExpMax : ∀ {Ψ Ψ''} → Subst Ψ Ψ''
       → Maybe (Σ[ Ψ' ∈ Scope ] (Subst Ψ Ψ')) → Set
ExpMax {Ψ} δ₀ = maybe′ (λ x → Σ[ δ' ∈ Subst (proj₁ x) _ ] ((proj₂ x ⨟ˢ δ') ≐ˢ δ₀)) ⊥

-- The expansion is most general among the substitutions that satisfy
-- the demands, and its failure refutes them

expandSub-max : ∀ {Ψ Ψ''} {Q : Hyps Ψ''} → (l : List (OVType Ψ × OVType Ψ))
              → (δ₀ : Subst Ψ Ψ'')
              → (∀ {A B} → (A , B) ∈ l → Q ∣ A [ δ₀ ]ᵛ <:̂ᵛ B [ δ₀ ]ᵛ)
              → ExpMax δ₀ (expandSub l)
expandSub-max {Ψ} l δ₀ k with unifyᵏ (skelEqns l) in e
... | nothing      = unifyᵏ-fail (skelEqns l) e (shapeˢ δ₀) (shape-unifies l δ₀ k)
... | just (m , τ) =
      expandᵏ-max Ψ ⟦ τ ⟧ᴷ δ₀
        (λ α → ⊑-from (⟦ τ ⟧ᴷ α) (proj₁ fac) (sTy δ₀ α) (proj₂ fac α))
  where
    fac = unifyᵏ-max (skelEqns l) e (shapeˢ δ₀) (shape-unifies l δ₀ k)
