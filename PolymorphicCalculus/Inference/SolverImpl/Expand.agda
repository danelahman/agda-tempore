------------------------------------------------------------------
-- Properties of variable expansion                             --
--                                                              --
-- The shape of an open type is its skeleton with all type      --
-- variables identified; subtyping relates only types of equal  --
-- shape, and `subDec` succeeds exactly on two decorations of   --
-- one skeleton (`_◃ᵛ_`). `decorate` produces a decoration      --
-- (`decorate-◃`), most general among the refinements `_⊑ᵛ_`    --
-- (`decorate-max`).                                            --
--                                                              --
-- Contract. `expandSub` makes every demand of its list         --
-- decomposable (`expandSub-dec`); its substitution is most     --
-- general among those satisfying the demands, and its failure  --
-- refutes them (`expandSub-max`).                              --
------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′) renaming (map to mmap)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Vec.Base using (Vec; lookup; tabulate)
  renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Vec.Properties using (lookup∘tabulate)

open import Relation.Nullary using (yes; no)

open import Grades.Base
open import Language.BaseTypes using (module BaseTypes)
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.SolverImpl.Expand (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open BaseTypes BTs using (_≡ᵇ?_)

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses               S

open import PolymorphicCalculus.Inference.SolverImpl.Core.Skel         S
open import PolymorphicCalculus.Inference.SolverImpl.Core.SkelUnify    S
open import PolymorphicCalculus.Inference.SolverImpl.Core.SkelUnifySound S using (unifyᵏ-sound)
open import PolymorphicCalculus.Inference.SolverImpl.Core.SkelUnifyMGU   S
  using (unifyᵏ-max; unifyᵏ-fail; s×-inj; s+-inj; s⇒-inj; s⇛-inj; sBox-inj; sList-inj)
open import PolymorphicCalculus.Inference.SolverImpl.Core.Decorate S
open import PolymorphicCalculus.Inference.SolverImpl.Core.Rigid    S using (zip₂)

open import PolymorphicCalculus.Inference.SolverImpl.Former S using (decompose)
open import PolymorphicCalculus.Inference.SolverImpl.Resid S

-- Shapes: skeletons over a single variable, all type variables identified

mutual

  shapeᵛ : ∀ {Ω} → OVType Ω → Skel 1
  shapeᵛ (tvar α)  = svar zero
  shapeᵛ (Base b)  = sBase b
  shapeᵛ unit      = sUnit
  shapeᵛ bool      = sBool
  shapeᵛ nat       = sNat
  shapeᵛ (A |×| B) = shapeᵛ A s× shapeᵛ B
  shapeᵛ (A |+| B) = shapeᵛ A s+ shapeᵛ B
  shapeᵛ (list A)  = sList (shapeᵛ A)
  shapeᵛ empty     = sEmpty
  shapeᵛ (A ⇒ C)   = shapeᵛ A s⇒ shapeᶜ C
  shapeᵛ (C ⇛ D)   = shapeᶜ C s⇛ shapeᶜ D
  shapeᵛ ([ ρ ] A) = sBox shapeᵛ A

  shapeᶜ : ∀ {Ω} → OCType Ω → Skel 1
  shapeᶜ (A ! ε) = shapeᵛ A

-- The shapes a substitution gives the type variables

shapeˢ : ∀ {Ω Ω'} → Subst Ω Ω' → SSub (nTy Ω) 1
shapeˢ δ α = shapeᵛ (sTy δ α)

mutual

  shape-[]ᵛ : ∀ {Ω Ω'} → (A : OVType Ω) → (δ : Subst Ω Ω')
            → shapeᵛ (A [ δ ]ᵛ) ≡ skelᵛ A [ shapeˢ δ ]ᵏ
  shape-[]ᵛ (tvar α)  δ = refl
  shape-[]ᵛ (Base b)  δ = refl
  shape-[]ᵛ unit      δ = refl
  shape-[]ᵛ bool      δ = refl
  shape-[]ᵛ nat       δ = refl
  shape-[]ᵛ (A |×| B) δ = cong₂ _s×_ (shape-[]ᵛ A δ) (shape-[]ᵛ B δ)
  shape-[]ᵛ (A |+| B) δ = cong₂ _s+_ (shape-[]ᵛ A δ) (shape-[]ᵛ B δ)
  shape-[]ᵛ (list A)  δ = cong sList (shape-[]ᵛ A δ)
  shape-[]ᵛ empty     δ = refl
  shape-[]ᵛ (A ⇒ C)   δ = cong₂ _s⇒_ (shape-[]ᵛ A δ) (shape-[]ᶜ C δ)
  shape-[]ᵛ (C ⇛ D)   δ = cong₂ _s⇛_ (shape-[]ᶜ C δ) (shape-[]ᶜ D δ)
  shape-[]ᵛ ([ ρ ] A) δ = cong sBox_ (shape-[]ᵛ A δ)

  shape-[]ᶜ : ∀ {Ω Ω'} → (C : OCType Ω) → (δ : Subst Ω Ω')
            → shapeᶜ (C [ δ ]ᶜ) ≡ skelᶜ C [ shapeˢ δ ]ᵏ
  shape-[]ᶜ (A ! ε) δ = shape-[]ᵛ A δ

-- Subtyping preserves the shape

mutual

  <:̂ᵛ-shape : ∀ {Θ} {Q : Hyps Θ} {A B} → Q ⊩ A <:̂ᵛ B → shapeᵛ A ≡ shapeᵛ B
  <:̂ᵛ-shape (tvarₛ p)    = refl
  <:̂ᵛ-shape (Baseₛ refl) = refl
  <:̂ᵛ-shape unitₛ        = refl
  <:̂ᵛ-shape boolₛ        = refl
  <:̂ᵛ-shape natₛ         = refl
  <:̂ᵛ-shape (p |×|ₛ q)   = cong₂ _s×_ (<:̂ᵛ-shape p) (<:̂ᵛ-shape q)
  <:̂ᵛ-shape (p |+|ₛ q)   = cong₂ _s+_ (<:̂ᵛ-shape p) (<:̂ᵛ-shape q)
  <:̂ᵛ-shape (listₛ p)    = cong sList (<:̂ᵛ-shape p)
  <:̂ᵛ-shape emptyₛ       = refl
  <:̂ᵛ-shape (p ⇒ₛ q)     = cong₂ _s⇒_ (sym (<:̂ᵛ-shape p)) (<:̂ᶜ-shape q)
  <:̂ᵛ-shape (p ⇛ₛ q)     = cong₂ _s⇛_ (sym (<:̂ᶜ-shape p)) (<:̂ᶜ-shape q)
  <:̂ᵛ-shape ([ r ]ₛ p)   = cong sBox_ (<:̂ᵛ-shape p)

  <:̂ᶜ-shape : ∀ {Θ} {Q : Hyps Θ} {C D} → Q ⊩ C <:̂ᶜ D → shapeᶜ C ≡ shapeᶜ D
  <:̂ᶜ-shape (p !ₛ r) = <:̂ᵛ-shape p

-- An open type refines a skeleton when it has the same formers outside the
-- skeleton's variables

infix 4 _⊑ᵛ_ _⊑ᶜ_

data _⊑ᵛ_ {Ω : Scope} {n : ℕ} : Skel n → OVType Ω → Set
data _⊑ᶜ_ {Ω : Scope} {n : ℕ} : Skel n → OCType Ω → Set

data _⊑ᵛ_ {Ω} {n} where
  var⊑   : ∀ {γ A} → svar γ ⊑ᵛ A
  Base⊑  : ∀ {b} → sBase {n} b ⊑ᵛ Base {Ω} b
  unit⊑  : sUnit {n} ⊑ᵛ unit {Ω}
  bool⊑  : sBool {n} ⊑ᵛ bool {Ω}
  nat⊑   : sNat {n} ⊑ᵛ nat {Ω}
  _×⊑_   : ∀ {t u A B} → t ⊑ᵛ A → u ⊑ᵛ B → (t s× u) ⊑ᵛ (A |×| B)
  _+⊑_   : ∀ {t u A B} → t ⊑ᵛ A → u ⊑ᵛ B → (t s+ u) ⊑ᵛ (A |+| B)
  list⊑  : ∀ {t A} → t ⊑ᵛ A → sList t ⊑ᵛ (list A)
  empty⊑ : sEmpty {n} ⊑ᵛ empty {Ω}
  _⇒⊑_   : ∀ {t u A C} → t ⊑ᵛ A → u ⊑ᶜ C → (t s⇒ u) ⊑ᵛ (A ⇒ C)
  _⇛⊑_   : ∀ {t u C D} → t ⊑ᶜ C → u ⊑ᶜ D → (t s⇛ u) ⊑ᵛ (C ⇛ D)
  Box⊑   : ∀ {t A ρ} → t ⊑ᵛ A → sBox t ⊑ᵛ ([ ρ ] A)

data _⊑ᶜ_ {Ω} {n} where
  !⊑ : ∀ {t A ε} → t ⊑ᵛ A → t ⊑ᶜ (A ! ε)

-- A skeleton whose instance has a type's shape refines that type

mutual

  ⊑-from : ∀ {Ω n} → (t : Skel n) → (ζ : SSub n 1) → (A : OVType Ω)
         → t [ ζ ]ᵏ ≡ shapeᵛ A → t ⊑ᵛ A
  ⊑-from (svar γ)  ζ A           eq   = var⊑
  ⊑-from (sBase b) ζ (tvar α)    ()
  ⊑-from (sBase b) ζ (Base b')   refl = Base⊑
  ⊑-from (sBase b) ζ unit        ()
  ⊑-from (sBase b) ζ bool        ()
  ⊑-from (sBase b) ζ nat         ()
  ⊑-from (sBase b) ζ (A |×| B)   ()
  ⊑-from (sBase b) ζ (A |+| B)   ()
  ⊑-from (sBase b) ζ empty       ()
  ⊑-from (sBase b) ζ (A ⇒ C)     ()
  ⊑-from (sBase b) ζ (C ⇛ D)     ()
  ⊑-from (sBase b) ζ ([ ρ ] A)   ()
  ⊑-from (sBase b) ζ (list A)    ()
  ⊑-from sUnit     ζ (tvar α)    ()
  ⊑-from sUnit     ζ (Base b')   ()
  ⊑-from sUnit     ζ unit        refl = unit⊑
  ⊑-from sUnit     ζ bool        ()
  ⊑-from sUnit     ζ nat         ()
  ⊑-from sUnit     ζ (A |×| B)   ()
  ⊑-from sUnit     ζ (A |+| B)   ()
  ⊑-from sUnit     ζ empty       ()
  ⊑-from sUnit     ζ (A ⇒ C)     ()
  ⊑-from sUnit     ζ (C ⇛ D)     ()
  ⊑-from sUnit     ζ ([ ρ ] A)   ()
  ⊑-from sUnit     ζ (list A)    ()
  ⊑-from sBool     ζ (tvar α)    ()
  ⊑-from sBool     ζ (Base b')   ()
  ⊑-from sBool     ζ unit        ()
  ⊑-from sBool     ζ bool        refl = bool⊑
  ⊑-from sBool     ζ nat         ()
  ⊑-from sBool     ζ (A |×| B)   ()
  ⊑-from sBool     ζ (A |+| B)   ()
  ⊑-from sBool     ζ empty       ()
  ⊑-from sBool     ζ (A ⇒ C)     ()
  ⊑-from sBool     ζ (C ⇛ D)     ()
  ⊑-from sBool     ζ ([ ρ ] A)   ()
  ⊑-from sBool     ζ (list A)    ()
  ⊑-from sNat      ζ (tvar α)    ()
  ⊑-from sNat      ζ (Base b')   ()
  ⊑-from sNat      ζ unit        ()
  ⊑-from sNat      ζ bool        ()
  ⊑-from sNat      ζ nat         refl = nat⊑
  ⊑-from sNat      ζ (A |×| B)   ()
  ⊑-from sNat      ζ (A |+| B)   ()
  ⊑-from sNat      ζ empty       ()
  ⊑-from sNat      ζ (A ⇒ C)     ()
  ⊑-from sNat      ζ (C ⇛ D)     ()
  ⊑-from sNat      ζ ([ ρ ] A)   ()
  ⊑-from sNat      ζ (list A)    ()
  ⊑-from (t s× u)  ζ (tvar α)    ()
  ⊑-from (t s× u)  ζ (Base b')   ()
  ⊑-from (t s× u)  ζ unit        ()
  ⊑-from (t s× u)  ζ bool        ()
  ⊑-from (t s× u)  ζ nat         ()
  ⊑-from (t s× u)  ζ (A |×| B)   eq   =
    ⊑-from t ζ A (proj₁ (s×-inj eq)) ×⊑ ⊑-from u ζ B (proj₂ (s×-inj eq))
  ⊑-from (t s× u)  ζ (A |+| B)   ()
  ⊑-from (t s× u)  ζ empty       ()
  ⊑-from (t s× u)  ζ (A ⇒ C)     ()
  ⊑-from (t s× u)  ζ (C ⇛ D)     ()
  ⊑-from (t s× u)  ζ ([ ρ ] A)   ()
  ⊑-from (t s× u)  ζ (list A)    ()
  ⊑-from (t s+ u)  ζ (tvar α)    ()
  ⊑-from (t s+ u)  ζ (Base b')   ()
  ⊑-from (t s+ u)  ζ unit        ()
  ⊑-from (t s+ u)  ζ bool        ()
  ⊑-from (t s+ u)  ζ nat         ()
  ⊑-from (t s+ u)  ζ (A |+| B)   eq   =
    ⊑-from t ζ A (proj₁ (s+-inj eq)) +⊑ ⊑-from u ζ B (proj₂ (s+-inj eq))
  ⊑-from (t s+ u)  ζ (A |×| B)   ()
  ⊑-from (t s+ u)  ζ empty       ()
  ⊑-from (t s+ u)  ζ (A ⇒ C)     ()
  ⊑-from (t s+ u)  ζ (C ⇛ D)     ()
  ⊑-from (t s+ u)  ζ ([ ρ ] A)   ()
  ⊑-from (t s+ u)  ζ (list A)    ()
  ⊑-from sEmpty    ζ (tvar α)    ()
  ⊑-from sEmpty    ζ (Base b')   ()
  ⊑-from sEmpty    ζ unit        ()
  ⊑-from sEmpty    ζ bool        ()
  ⊑-from sEmpty    ζ nat         ()
  ⊑-from sEmpty    ζ (A |×| B)   ()
  ⊑-from sEmpty    ζ (A |+| B)   ()
  ⊑-from sEmpty    ζ empty       refl = empty⊑
  ⊑-from sEmpty    ζ (A ⇒ C)     ()
  ⊑-from sEmpty    ζ (C ⇛ D)     ()
  ⊑-from sEmpty    ζ ([ ρ ] A)   ()
  ⊑-from sEmpty    ζ (list A)    ()
  ⊑-from (t s⇒ u)  ζ (tvar α)    ()
  ⊑-from (t s⇒ u)  ζ (Base b')   ()
  ⊑-from (t s⇒ u)  ζ unit        ()
  ⊑-from (t s⇒ u)  ζ bool        ()
  ⊑-from (t s⇒ u)  ζ nat         ()
  ⊑-from (t s⇒ u)  ζ (A |×| B)   ()
  ⊑-from (t s⇒ u)  ζ (A |+| B)   ()
  ⊑-from (t s⇒ u)  ζ empty       ()
  ⊑-from (t s⇒ u)  ζ (A ⇒ C)     eq   =
    ⊑-from t ζ A (proj₁ (s⇒-inj eq)) ⇒⊑ ⊑-fromᶜ u ζ C (proj₂ (s⇒-inj eq))
  ⊑-from (t s⇒ u)  ζ ([ ρ ] A)   ()
  ⊑-from (t s⇒ u)  ζ (list A)    ()
  ⊑-from (t s⇒ u)  ζ (C ⇛ D)     ()
  ⊑-from (t s⇛ u)  ζ (tvar α)    ()
  ⊑-from (t s⇛ u)  ζ (Base b')   ()
  ⊑-from (t s⇛ u)  ζ unit        ()
  ⊑-from (t s⇛ u)  ζ bool        ()
  ⊑-from (t s⇛ u)  ζ nat         ()
  ⊑-from (t s⇛ u)  ζ (A |×| B)   ()
  ⊑-from (t s⇛ u)  ζ (A |+| B)   ()
  ⊑-from (t s⇛ u)  ζ empty       ()
  ⊑-from (t s⇛ u)  ζ (A ⇒ C)     ()
  ⊑-from (t s⇛ u)  ζ (C ⇛ D)     eq   =
    ⊑-fromᶜ t ζ C (proj₁ (s⇛-inj eq)) ⇛⊑ ⊑-fromᶜ u ζ D (proj₂ (s⇛-inj eq))
  ⊑-from (t s⇛ u)  ζ ([ ρ ] A)   ()
  ⊑-from (t s⇛ u)  ζ (list A)    ()
  ⊑-from (sBox t)  ζ (tvar α)    ()
  ⊑-from (sBox t)  ζ (Base b')   ()
  ⊑-from (sBox t)  ζ unit        ()
  ⊑-from (sBox t)  ζ bool        ()
  ⊑-from (sBox t)  ζ nat         ()
  ⊑-from (sBox t)  ζ (A |×| B)   ()
  ⊑-from (sBox t)  ζ (A |+| B)   ()
  ⊑-from (sBox t)  ζ empty       ()
  ⊑-from (sBox t)  ζ (A ⇒ C)     ()
  ⊑-from (sBox t)  ζ (C ⇛ D)     ()
  ⊑-from (sBox t)  ζ ([ ρ ] A)   eq   = Box⊑ (⊑-from t ζ A (sBox-inj eq))
  ⊑-from (sBox t)  ζ (list A)    ()
  ⊑-from (sList t) ζ (tvar α)    ()
  ⊑-from (sList t) ζ (Base b')   ()
  ⊑-from (sList t) ζ unit        ()
  ⊑-from (sList t) ζ bool        ()
  ⊑-from (sList t) ζ nat         ()
  ⊑-from (sList t) ζ (A |×| B)   ()
  ⊑-from (sList t) ζ (A |+| B)   ()
  ⊑-from (sList t) ζ empty       ()
  ⊑-from (sList t) ζ (A ⇒ C)     ()
  ⊑-from (sList t) ζ (C ⇛ D)     ()
  ⊑-from (sList t) ζ ([ ρ ] A)   ()
  ⊑-from (sList t) ζ (list A)    eq   = list⊑ (⊑-from t ζ A (sList-inj eq))

  ⊑-fromᶜ : ∀ {Ω n} → (t : Skel n) → (ζ : SSub n 1) → (C : OCType Ω)
          → t [ ζ ]ᵏ ≡ shapeᶜ C → t ⊑ᶜ C
  ⊑-fromᶜ t ζ (A ! ε) eq = !⊑ (⊑-from t ζ A eq)

-- An open type decorates a skeleton when it refines it with a type variable at
-- every skeleton variable

infix 4 _◃ᵛ_ _◃ᶜ_

data _◃ᵛ_ {Ω : Scope} {n : ℕ} : Skel n → OVType Ω → Set
data _◃ᶜ_ {Ω : Scope} {n : ℕ} : Skel n → OCType Ω → Set

data _◃ᵛ_ {Ω} {n} where
  var◃   : ∀ {γ α} → svar γ ◃ᵛ tvar α
  Base◃  : ∀ {b} → sBase {n} b ◃ᵛ Base {Ω} b
  unit◃  : sUnit {n} ◃ᵛ unit {Ω}
  bool◃  : sBool {n} ◃ᵛ bool {Ω}
  nat◃   : sNat {n} ◃ᵛ nat {Ω}
  _×◃_   : ∀ {t u A B} → t ◃ᵛ A → u ◃ᵛ B → (t s× u) ◃ᵛ (A |×| B)
  _+◃_   : ∀ {t u A B} → t ◃ᵛ A → u ◃ᵛ B → (t s+ u) ◃ᵛ (A |+| B)
  list◃  : ∀ {t A} → t ◃ᵛ A → sList t ◃ᵛ (list A)
  empty◃ : sEmpty {n} ◃ᵛ empty {Ω}
  _⇒◃_   : ∀ {t u A C} → t ◃ᵛ A → u ◃ᶜ C → (t s⇒ u) ◃ᵛ (A ⇒ C)
  _⇛◃_   : ∀ {t u C D} → t ◃ᶜ C → u ◃ᶜ D → (t s⇛ u) ◃ᵛ (C ⇛ D)
  Box◃   : ∀ {t A ρ} → t ◃ᵛ A → sBox t ◃ᵛ ([ ρ ] A)

data _◃ᶜ_ {Ω} {n} where
  !◃ : ∀ {t A ε} → t ◃ᵛ A → t ◃ᶜ (A ! ε)

-- Two decorations of one skeleton decompose

◃-fits : ∀ {Ω n} {t : Skel n} {A B : OVType Ω} → t ◃ᵛ A → t ◃ᵛ B
       → Fitsᴰ (λ X Y → Σ[ u ∈ Skel n ] (u ◃ᵛ X × u ◃ᵛ Y)) (decompose A B)
◃-fits var◃          var◃            = tt
◃-fits (Base◃ {b})   Base◃           with b ≡ᵇ? b
... | yes refl = []
... | no ¬p    = ⊥-elim (¬p refl)
◃-fits unit◃         unit◃           = []
◃-fits bool◃         bool◃           = []
◃-fits nat◃          nat◃            = []
◃-fits empty◃        empty◃          = []
◃-fits (p ×◃ q)      (p' ×◃ q')      = (_ , p , p') ∷ (_ , q , q') ∷ []
◃-fits (p +◃ q)      (p' +◃ q')      = (_ , p , p') ∷ (_ , q , q') ∷ []
◃-fits (list◃ p)     (list◃ p')      = (_ , p , p') ∷ []
◃-fits (p ⇒◃ !◃ q)   (p' ⇒◃ !◃ q')   = (_ , p , p') ∷ (_ , q , q') ∷ tt ∷ []
◃-fits (!◃ p ⇛◃ !◃ q) (!◃ p' ⇛◃ !◃ q') = (_ , p , p') ∷ tt ∷ (_ , q , q') ∷ tt ∷ []
◃-fits (Box◃ p)      (Box◃ p')       = tt ∷ (_ , p , p') ∷ []

◃-subDec : ∀ {Ω n} {t : Skel n} {A B : OVType Ω} → t ◃ᵛ A → t ◃ᵛ B
         → Σ[ d ∈ SubDec A B ] (subDec A B ≡ just d)
◃-subDec {n = n} p q =
  SubDecJust.subDec-Just (λ X Y → Σ[ u ∈ Skel n ] (u ◃ᵛ X × u ◃ᵛ Y))
                         (λ { (u , a , b) → u , b , a }) (λ { (u , a , b) → ◃-fits a b })
                         (_ , p , q)

-- A decoration of a store decorates every skeleton through it

mutual

  ◃-skel : ∀ {Ω Ω' n} → (A : OVType Ω) → {τ : SSub (nTy Ω) n} → {ω : Subst Ω Ω'}
         → ((α : TyVar Ω) → τ α ◃ᵛ sTy ω α) → (skelᵛ A [ τ ]ᵏ) ◃ᵛ (A [ ω ]ᵛ)
  ◃-skel (tvar α)  k = k α
  ◃-skel (Base b)  k = Base◃
  ◃-skel unit      k = unit◃
  ◃-skel bool      k = bool◃
  ◃-skel nat       k = nat◃
  ◃-skel (A |×| B) k = ◃-skel A k ×◃ ◃-skel B k
  ◃-skel (A |+| B) k = ◃-skel A k +◃ ◃-skel B k
  ◃-skel (list A)  k = list◃ (◃-skel A k)
  ◃-skel empty     k = empty◃
  ◃-skel (A ⇒ C)   k = ◃-skel A k ⇒◃ ◃-skelᶜ C k
  ◃-skel (C ⇛ D)   k = ◃-skelᶜ C k ⇛◃ ◃-skelᶜ D k
  ◃-skel ([ ρ ] A) k = Box◃ (◃-skel A k)

  ◃-skelᶜ : ∀ {Ω Ω' n} → (C : OCType Ω) → {τ : SSub (nTy Ω) n} → {ω : Subst Ω Ω'}
          → ((α : TyVar Ω) → τ α ◃ᵛ sTy ω α) → (skelᶜ C [ τ ]ᵏ) ◃ᶜ (C [ ω ]ᶜ)
  ◃-skelᶜ (A ! ε) k = !◃ (◃-skel A k)

-- A substitution that renames the type variables

record TyRen {Ω Ω' : Scope} (w : Subst Ω Ω') : Set where
  constructor tyren
  field tyRen : (α : TyVar Ω) → Σ[ β ∈ TyVar Ω' ] (sTy w α ≡ tvar β)

open TyRen public

TyRen-idˢ : ∀ {Ω} → TyRen (idˢ {Ω})
TyRen-idˢ = tyren (λ α → α , refl)

TyRen-wkᵗ : ∀ {Ω} → TyRen (wkˢᵗ {Ω})
TyRen-wkᵗ {Ω} = tyren (λ α → wkᵗ-tv Ω α , refl)

TyRen-wkʳ : ∀ {Ω} → TyRen (wkˢʳ {Ω})
TyRen-wkʳ {Ω} = tyren (λ α → wkʳ-tv Ω α , refl)

TyRen-wkᵉ : ∀ {Ω} → TyRen (wkˢᵉ {Ω})
TyRen-wkᵉ {Ω} = tyren (λ α → wkᵉ-tv Ω α , refl)

TyRen-⨟ : ∀ {Ω Ω₁ Ω'} {w : Subst Ω Ω₁} {w' : Subst Ω₁ Ω'}
        → TyRen w → TyRen w' → TyRen (w ⨟ˢ w')
TyRen-⨟ {Ω} {Ω₁} {Ω'} {w} {w'} r r' = tyren f
  where
    f : (α : TyVar Ω) → Σ[ β ∈ TyVar Ω' ] (sTy (w ⨟ˢ w') α ≡ tvar β)
    f α with tyRen r α
    ... | β , q with tyRen r' β
    ...   | γ , q' = γ , trans (cong (_[ w' ]ᵛ) q) q'

mutual

  ◃-ren : ∀ {Ω Ω' n} {t : Skel n} {A : OVType Ω} {σ : Subst Ω Ω'}
        → TyRen σ → t ◃ᵛ A → t ◃ᵛ (A [ σ ]ᵛ)
  ◃-ren {t = svar γ} r (var◃ {α = α}) with tyRen r α
  ... | β , q = subst (svar γ ◃ᵛ_) (sym q) var◃
  ◃-ren r Base◃     = Base◃
  ◃-ren r unit◃     = unit◃
  ◃-ren r bool◃     = bool◃
  ◃-ren r nat◃      = nat◃
  ◃-ren r (p ×◃ q)  = ◃-ren r p ×◃ ◃-ren r q
  ◃-ren r (p +◃ q)  = ◃-ren r p +◃ ◃-ren r q
  ◃-ren r (list◃ p) = list◃ (◃-ren r p)
  ◃-ren r empty◃    = empty◃
  ◃-ren r (p ⇒◃ q)  = ◃-ren r p ⇒◃ ◃-renᶜ r q
  ◃-ren r (p ⇛◃ q)  = ◃-renᶜ r p ⇛◃ ◃-renᶜ r q
  ◃-ren r (Box◃ p)  = Box◃ (◃-ren r p)

  ◃-renᶜ : ∀ {Ω Ω' n} {t : Skel n} {C : OCType Ω} {σ : Subst Ω Ω'}
         → TyRen σ → t ◃ᶜ C → t ◃ᶜ (C [ σ ]ᶜ)
  ◃-renᶜ r (!◃ p) = !◃ (◃-ren r p)

◃-wkʳ : ∀ {Ω n} {t : Skel n} {A : OVType Ω} → t ◃ᵛ A → t ◃ᵛ wkʳ-v A
◃-wkʳ {t = t} {A = A} d = subst (t ◃ᵛ_) (wkˢʳ-v A) (◃-ren TyRen-wkʳ d)

◃-wkᵉ : ∀ {Ω n} {t : Skel n} {A : OVType Ω} → t ◃ᵛ A → t ◃ᵛ wkᵉ-v A
◃-wkᵉ {t = t} {A = A} d = subst (t ◃ᵛ_) (wkˢᵉ-v A) (◃-ren TyRen-wkᵉ d)

-- `decorate` renames the given type variables and produces a decoration

Dec◃ : ∀ {m} → (Ω : Scope) → Skel m
     → Σ[ Ω' ∈ Scope ] (Subst Ω Ω' × OVType Ω') → Set
Dec◃ Ω t (Ω' , w , A) = TyRen w × (t ◃ᵛ A)

decorate-◃ : ∀ {m} → (Ω : Scope) → (t : Skel m) → Dec◃ Ω t (decorate Ω t)
decorate-◃ Ω (svar γ)  = TyRen-wkᵗ , var◃
decorate-◃ Ω (sBase b) = TyRen-idˢ , Base◃
decorate-◃ Ω sUnit     = TyRen-idˢ , unit◃
decorate-◃ Ω sBool     = TyRen-idˢ , bool◃
decorate-◃ Ω sNat      = TyRen-idˢ , nat◃
decorate-◃ Ω sEmpty    = TyRen-idˢ , empty◃
decorate-◃ Ω (t s× u) with decorate Ω t | decorate-◃ Ω t
... | Ω₁ , w₁ , A | r₁ , d₁ with decorate Ω₁ u | decorate-◃ Ω₁ u
...   | Ω₂ , w₂ , B | r₂ , d₂ = TyRen-⨟ r₁ r₂ , (◃-ren r₂ d₁ ×◃ d₂)
decorate-◃ Ω (t s+ u) with decorate Ω t | decorate-◃ Ω t
... | Ω₁ , w₁ , A | r₁ , d₁ with decorate Ω₁ u | decorate-◃ Ω₁ u
...   | Ω₂ , w₂ , B | r₂ , d₂ = TyRen-⨟ r₁ r₂ , (◃-ren r₂ d₁ +◃ d₂)
decorate-◃ Ω (sList t) with decorate Ω t | decorate-◃ Ω t
... | Ω₁ , w₁ , A | r₁ , d₁ = r₁ , list◃ d₁
decorate-◃ Ω (t s⇒ u) with decorate Ω t | decorate-◃ Ω t
... | Ω₁ , w₁ , A | r₁ , d₁ with decorate Ω₁ u | decorate-◃ Ω₁ u
...   | Ω₂ , w₂ , B | r₂ , d₂ =
        TyRen-⨟ (TyRen-⨟ r₁ r₂) TyRen-wkᵉ ,
        (◃-wkᵉ (◃-ren r₂ d₁) ⇒◃ !◃ (◃-wkᵉ d₂))
decorate-◃ Ω (t s⇛ u) with decorate Ω t | decorate-◃ Ω t
... | Ω₁ , w₁ , A | r₁ , d₁ with decorate Ω₁ u | decorate-◃ Ω₁ u
...   | Ω₂ , w₂ , B | r₂ , d₂ =
        TyRen-⨟ (TyRen-⨟ (TyRen-⨟ r₁ r₂) TyRen-wkᵉ) TyRen-wkᵉ ,
        (!◃ (◃-wkᵉ (◃-wkᵉ (◃-ren r₂ d₁))) ⇛◃ !◃ (◃-wkᵉ (◃-wkᵉ d₂)))
decorate-◃ Ω (sBox t) with decorate Ω t | decorate-◃ Ω t
... | Ω₁ , w₁ , A | r₁ , d₁ = TyRen-⨟ r₁ TyRen-wkʳ , Box◃ (◃-wkʳ d₁)

-- A refinement of the skeleton is an instance of its decoration

wkʳ-inst : ∀ {Ω Ω'} → (A : OVType Ω) → (δ : Subst Ω Ω') → (ρ : RExp Ω')
         → wkʳ-v A [ δ ,ʳ ρ ]ᵛ ≡ A [ δ ]ᵛ
wkʳ-inst A δ ρ = trans (cong (_[ δ ,ʳ ρ ]ᵛ) (sym (wkˢʳ-v A)))
                       (trans ([⨟]ᵛ A wkˢʳ (δ ,ʳ ρ)) ([≐]ᵛ (wkˢʳ-,ʳ δ ρ) A))

wkᵉ-inst : ∀ {Ω Ω'} → (A : OVType Ω) → (δ : Subst Ω Ω') → (ε : EExp Ω')
         → wkᵉ-v A [ δ ,ᵉ ε ]ᵛ ≡ A [ δ ]ᵛ
wkᵉ-inst A δ ε = trans (cong (_[ δ ,ᵉ ε ]ᵛ) (sym (wkˢᵉ-v A)))
                       (trans ([⨟]ᵛ A wkˢᵉ (δ ,ᵉ ε)) ([≐]ᵛ (wkˢᵉ-,ᵉ δ ε) A))

DecMax : ∀ {Ω Ω''} → Subst Ω Ω'' → OVType Ω''
       → Σ[ Ω' ∈ Scope ] (Subst Ω Ω' × OVType Ω') → Set
DecMax {Ω'' = Ω''} δ A₀ (Ω' , w , A) =
  Σ[ δ₁ ∈ Subst Ω' Ω'' ] (((w ⨟ˢ δ₁) ≐ˢ δ) × (A [ δ₁ ]ᵛ ≡ A₀))

decorate-max : ∀ {m Ω''} → (Ω : Scope) → (t : Skel m) → (δ : Subst Ω Ω'')
             → {A₀ : OVType Ω''} → t ⊑ᵛ A₀ → DecMax δ A₀ (decorate Ω t)
decorate-max Ω (svar γ)  δ {A₀} var⊑ = (δ ,ᵗ A₀) , wkˢᵗ-,ᵗ δ A₀ , refl
decorate-max Ω (sBase b) δ Base⊑  = δ , ⨟-idˡ δ , refl
decorate-max Ω sUnit     δ unit⊑  = δ , ⨟-idˡ δ , refl
decorate-max Ω sBool     δ bool⊑  = δ , ⨟-idˡ δ , refl
decorate-max Ω sNat      δ nat⊑   = δ , ⨟-idˡ δ , refl
decorate-max Ω sEmpty    δ empty⊑ = δ , ⨟-idˡ δ , refl
decorate-max Ω (t s× u) δ (p ×⊑ q) with decorate Ω t | decorate-max Ω t δ p
... | Ω₁ , w₁ , A | δ₁ , tri₁ , eq₁ with decorate Ω₁ u | decorate-max Ω₁ u δ₁ q
...   | Ω₂ , w₂ , B | δ₂ , tri₂ , eq₂ =
        δ₂ ,
        ≐ˢ-trans (⨟-assoc w₁ w₂ δ₂) (≐ˢ-trans (⨟-congʳ w₁ tri₂) tri₁) ,
        cong₂ _|×|_ (trans ([⨟]ᵛ A w₂ δ₂) (trans ([≐]ᵛ tri₂ A) eq₁)) eq₂
decorate-max Ω (t s+ u) δ (p +⊑ q) with decorate Ω t | decorate-max Ω t δ p
... | Ω₁ , w₁ , A | δ₁ , tri₁ , eq₁ with decorate Ω₁ u | decorate-max Ω₁ u δ₁ q
...   | Ω₂ , w₂ , B | δ₂ , tri₂ , eq₂ =
        δ₂ ,
        ≐ˢ-trans (⨟-assoc w₁ w₂ δ₂) (≐ˢ-trans (⨟-congʳ w₁ tri₂) tri₁) ,
        cong₂ _|+|_ (trans ([⨟]ᵛ A w₂ δ₂) (trans ([≐]ᵛ tri₂ A) eq₁)) eq₂
decorate-max Ω (sList t) δ (list⊑ p) with decorate Ω t | decorate-max Ω t δ p
... | Ω₁ , w₁ , A | δ₁ , tri₁ , eq₁ = δ₁ , tri₁ , cong list eq₁
decorate-max Ω (t s⇒ u) δ {_ ⇒ (_ ! ε)} (p ⇒⊑ !⊑ q)
  with decorate Ω t | decorate-max Ω t δ p
... | Ω₁ , w₁ , A | δ₁ , tri₁ , eq₁ with decorate Ω₁ u | decorate-max Ω₁ u δ₁ q
...   | Ω₂ , w₂ , B | δ₂ , tri₂ , eq₂ =
        (δ₂ ,ᵉ ε) ,
        ≐ˢ-trans (⨟-assoc (w₁ ⨟ˢ w₂) wkˢᵉ (δ₂ ,ᵉ ε))
          (≐ˢ-trans (⨟-congʳ (w₁ ⨟ˢ w₂) (wkˢᵉ-,ᵉ δ₂ ε))
            (≐ˢ-trans (⨟-assoc w₁ w₂ δ₂) (≐ˢ-trans (⨟-congʳ w₁ tri₂) tri₁))) ,
        cong₂ _⇒_
          (trans (wkᵉ-inst (A [ w₂ ]ᵛ) δ₂ ε)
                 (trans ([⨟]ᵛ A w₂ δ₂) (trans ([≐]ᵛ tri₂ A) eq₁)))
          (cong (_! ε) (trans (wkᵉ-inst B δ₂ ε) eq₂))
decorate-max Ω (t s⇛ u) δ {(_ ! ε) ⇛ (_ ! ε')} (!⊑ p ⇛⊑ !⊑ q)
  with decorate Ω t | decorate-max Ω t δ p
... | Ω₁ , w₁ , A | δ₁ , tri₁ , eq₁ with decorate Ω₁ u | decorate-max Ω₁ u δ₁ q
...   | Ω₂ , w₂ , B | δ₂ , tri₂ , eq₂ =
        (δ₂ ,ᵉ ε ,ᵉ ε') ,
        ≐ˢ-trans (⨟-assoc (w₁ ⨟ˢ w₂ ⨟ˢ wkˢᵉ) wkˢᵉ (δ₂ ,ᵉ ε ,ᵉ ε'))
          (≐ˢ-trans (⨟-congʳ (w₁ ⨟ˢ w₂ ⨟ˢ wkˢᵉ) (wkˢᵉ-,ᵉ (δ₂ ,ᵉ ε) ε'))
            (≐ˢ-trans (⨟-assoc (w₁ ⨟ˢ w₂) wkˢᵉ (δ₂ ,ᵉ ε))
              (≐ˢ-trans (⨟-congʳ (w₁ ⨟ˢ w₂) (wkˢᵉ-,ᵉ δ₂ ε))
                (≐ˢ-trans (⨟-assoc w₁ w₂ δ₂) (≐ˢ-trans (⨟-congʳ w₁ tri₂) tri₁))))) ,
        cong₂ _⇛_
          (cong (_! ε)
            (trans (wkᵉ-inst (wkᵉ-v (A [ w₂ ]ᵛ)) (δ₂ ,ᵉ ε) ε')
              (trans (wkᵉ-inst (A [ w₂ ]ᵛ) δ₂ ε)
                (trans ([⨟]ᵛ A w₂ δ₂) (trans ([≐]ᵛ tri₂ A) eq₁)))))
          (cong (_! ε')
            (trans (wkᵉ-inst (wkᵉ-v B) (δ₂ ,ᵉ ε) ε') (trans (wkᵉ-inst B δ₂ ε) eq₂)))
decorate-max Ω (sBox t) δ {[ ρ ] _} (Box⊑ p) with decorate Ω t | decorate-max Ω t δ p
... | Ω₁ , w₁ , A | δ₁ , tri₁ , eq₁ =
      (δ₁ ,ʳ ρ) ,
      ≐ˢ-trans (⨟-assoc w₁ wkˢʳ (δ₁ ,ʳ ρ))
               (≐ˢ-trans (⨟-congʳ w₁ (wkˢʳ-,ʳ δ₁ ρ)) tri₁) ,
      cong ([ ρ ]_) (trans (wkʳ-inst A δ₁ ρ) eq₁)

-- The same, for a whole vector; an entry left undecorated has a variable skeleton

Ent◃ : ∀ {Ω' m} → Skel m → Maybe (OVType Ω') → Set
Ent◃ {m = m} t nothing  = Σ[ γ ∈ Fin m ] (t ≡ svar γ)
Ent◃         t (just A) = t ◃ᵛ A

Dec*◃ : ∀ {m k} → (Ω : Scope) → Vec (Skel m) k
      → Σ[ Ω' ∈ Scope ] (Subst Ω Ω' × Vec (Maybe (OVType Ω')) k) → Set
Dec*◃ {k = k} Ω ts (Ω' , w , As) =
  TyRen w × ((i : Fin k) → Ent◃ (lookup ts i) (lookup As i))

decorate*-◃ : ∀ {m k} → (Ω : Scope) → (ts : Vec (Skel m) k)
            → Dec*◃ Ω ts (decorate* Ω ts)
decorate*-◃ Ω []ⱽ        = TyRen-idˢ , λ ()
decorate*-◃ Ω (t ∷ⱽ ts) with svar? t in e
... | just γ with decorate* Ω ts | decorate*-◃ Ω ts
...   | Ω' , w , As | r , k =
        r , λ { zero → γ , svar?-just t e ; (suc i) → k i }
decorate*-◃ Ω (t ∷ⱽ ts) | nothing with decorate Ω t | decorate-◃ Ω t
... | Ω₁ , w₁ , A | r₁ , d₁ with decorate* Ω₁ ts | decorate*-◃ Ω₁ ts
...   | Ω₂ , w₂ , As | r₂ , k =
        TyRen-⨟ r₁ r₂ , λ { zero → ◃-ren r₂ d₁ ; (suc i) → k i }

Mt : ∀ {Ω' Ω''} → Maybe (OVType Ω') → OVType Ω'' → Subst Ω' Ω'' → Set
Mt nothing  A₀ δ₁ = ⊤
Mt (just A) A₀ δ₁ = A [ δ₁ ]ᵛ ≡ A₀

Dec*Max : ∀ {Ω Ω'' k} → Subst Ω Ω'' → Vec (OVType Ω'') k
        → Σ[ Ω' ∈ Scope ] (Subst Ω Ω' × Vec (Maybe (OVType Ω')) k) → Set
Dec*Max {Ω'' = Ω''} {k = k} δ A₀s (Ω' , w , As) =
  Σ[ δ₁ ∈ Subst Ω' Ω'' ]
    (((w ⨟ˢ δ₁) ≐ˢ δ) × ((i : Fin k) → Mt (lookup As i) (lookup A₀s i) δ₁))

decorate*-max : ∀ {m k Ω''} → (Ω : Scope) → (ts : Vec (Skel m) k) → (δ : Subst Ω Ω'')
              → (A₀s : Vec (OVType Ω'') k)
              → ((i : Fin k) → lookup ts i ⊑ᵛ lookup A₀s i)
              → Dec*Max δ A₀s (decorate* Ω ts)
decorate*-max Ω []ⱽ δ []ⱽ ps = δ , ⨟-idˡ δ , λ ()
decorate*-max Ω (t ∷ⱽ ts) δ (A₀ ∷ⱽ A₀s) ps with svar? t
... | just γ with decorate* Ω ts | decorate*-max Ω ts δ A₀s (λ i → ps (suc i))
...   | Ω' , w , As | δ₁ , tri , ms = δ₁ , tri , λ { zero → tt ; (suc i) → ms i }
decorate*-max Ω (t ∷ⱽ ts) δ (A₀ ∷ⱽ A₀s) ps | nothing
  with decorate Ω t | decorate-max Ω t δ (ps zero)
... | Ω₁ , w₁ , A | δ₁ , tri₁ , eq₁
  with decorate* Ω₁ ts | decorate*-max Ω₁ ts δ₁ A₀s (λ i → ps (suc i))
...   | Ω₂ , w₂ , As | δ₂ , tri₂ , ms =
        δ₂ , ≐ˢ-trans (⨟-assoc w₁ w₂ δ₂) (≐ˢ-trans (⨟-congʳ w₁ tri₂) tri₁) ,
        λ { zero → trans ([⨟]ᵛ A w₂ δ₂) (trans ([≐]ᵛ tri₂ A) eq₁)
          ; (suc i) → ms i }

-- Properties of the refinement of a whole store

Expᵏ◃ : ∀ {m} → (Ω : Scope) → SSub (nTy Ω) m → Σ[ Ω' ∈ Scope ] (Subst Ω Ω') → Set
Expᵏ◃ Ω σ x = (α : TyVar Ω) → σ α ◃ᵛ sTy (proj₂ x) α

expandᵏ-◃ : ∀ {m} → (Ω : Scope) → (σ : SSub (nTy Ω) m) → Expᵏ◃ Ω σ (expandᵏ Ω σ)
expandᵏ-◃ Ω σ with decorate* Ω (tabulate σ) | decorate*-◃ Ω (tabulate σ)
... | Ω' , w , As | r , k = g
  where
    g : (α : TyVar Ω) → σ α ◃ᵛ maybe′ (λ A → A) (sTy w α) (lookup As α)
    g α with lookup As α | k α
    ... | just A  | d     = subst (_◃ᵛ A) (lookup∘tabulate σ α) d
    ... | nothing | γ , q with tyRen r α
    ...   | β , q' =
            subst₂ _◃ᵛ_ (trans (sym q) (lookup∘tabulate σ α)) (sym q') (var◃ {γ = γ})

Expᵏmax : ∀ {m Ω''} → (Ω : Scope) → SSub (nTy Ω) m → Subst Ω Ω''
        → Σ[ Ω' ∈ Scope ] (Subst Ω Ω') → Set
Expᵏmax {Ω'' = Ω''} Ω σ δ x = Σ[ δ' ∈ Subst (proj₁ x) Ω'' ] ((proj₂ x ⨟ˢ δ') ≐ˢ δ)

expandᵏ-max : ∀ {m Ω''} → (Ω : Scope) → (σ : SSub (nTy Ω) m) → (δ : Subst Ω Ω'')
            → ((α : TyVar Ω) → σ α ⊑ᵛ sTy δ α) → Expᵏmax Ω σ δ (expandᵏ Ω σ)
expandᵏ-max Ω σ δ ps
  with decorate* Ω (tabulate σ)
     | decorate*-max Ω (tabulate σ) δ (tabulate (sTy δ))
         (λ α → subst₂ _⊑ᵛ_ (sym (lookup∘tabulate σ α))
                            (sym (lookup∘tabulate (sTy δ) α)) (ps α))
... | Ω' , w , As | δ₁ , tri , ms =
      δ₁ , mk≐ˢ tyq (λ i → ≐ʳ tri i) (λ i → ≐ᵉ tri i)
  where
    tyq : (α : TyVar Ω)
        → maybe′ (λ A → A) (sTy w α) (lookup As α) [ δ₁ ]ᵛ ≡ sTy δ α
    tyq α with lookup As α | ms α
    ... | just A  | m = trans m (lookup∘tabulate (sTy δ) α)
    ... | nothing | _ = ≐ᵗ tri α

-- Unification of a list of demands, atom by atom

unifies-∈ : ∀ {Ω n} → (l : List (OVType Ω × OVType Ω)) → (σ : SSub (nTy Ω) n)
          → Unifiesᵏ (skelEqns l) σ
          → ∀ {A B} → (A , B) ∈ l → skelᵛ A [ σ ]ᵏ ≡ skelᵛ B [ σ ]ᵏ
unifies-∈ ((A , B) ∷ l) σ (u , us) (here refl) = u
unifies-∈ ((A , B) ∷ l) σ (u , us) (there m)   = unifies-∈ l σ us m

unifies⁺ : ∀ {Ω n} → (l : List (OVType Ω × OVType Ω)) → (σ : SSub (nTy Ω) n)
         → (∀ {A B} → (A , B) ∈ l → skelᵛ A [ σ ]ᵏ ≡ skelᵛ B [ σ ]ᵏ)
         → Unifiesᵏ (skelEqns l) σ
unifies⁺ []             σ k = tt
unifies⁺ ((A , B) ∷ l) σ k = k (here refl) , unifies⁺ l σ (λ m → k (there m))

-- The shapes of a substitution satisfying every demand unify their skeletons

shape-unifies : ∀ {Ω Ω''} {Q : Hyps Ω''} → (l : List (OVType Ω × OVType Ω))
              → (δ₀ : Subst Ω Ω'')
              → (∀ {A B} → (A , B) ∈ l → Q ⊩ A [ δ₀ ]ᵛ <:̂ᵛ B [ δ₀ ]ᵛ)
              → Unifiesᵏ (skelEqns l) (shapeˢ δ₀)
shape-unifies l δ₀ k =
  unifies⁺ l (shapeˢ δ₀)
    (λ {A} {B} m → trans (sym (shape-[]ᵛ A δ₀))
                         (trans (<:̂ᵛ-shape (k m)) (shape-[]ᵛ B δ₀)))

Expᵏdec : ∀ {Ω} → List (OVType Ω × OVType Ω)
        → Σ[ Ω' ∈ Scope ] (Subst Ω Ω') → Set
Expᵏdec l x = ∀ {A B} → (A , B) ∈ l
            → Σ[ d ∈ SubDec (A [ proj₂ x ]ᵛ) (B [ proj₂ x ]ᵛ) ]
                (subDec (A [ proj₂ x ]ᵛ) (B [ proj₂ x ]ᵛ) ≡ just d)

ExpDec : ∀ {Ω} → List (OVType Ω × OVType Ω)
       → Maybe (Σ[ Ω' ∈ Scope ] (Subst Ω Ω')) → Set
ExpDec l = maybe′ (Expᵏdec l) ⊤

-- Every pair the expansion was asked about decomposes afterwards

expandSub-dec : ∀ {Ω} → (l : List (OVType Ω × OVType Ω)) → ExpDec l (expandSub l)
expandSub-dec {Ω} l with unifyᵏ (skelEqns l) in e
... | nothing      = tt
... | just (m , τ) = f
  where
    dec : (A : OVType Ω) → (skelᵛ A [ ⟦ τ ⟧ᴷ ]ᵏ) ◃ᵛ (A [ proj₂ (expandᵏ Ω ⟦ τ ⟧ᴷ) ]ᵛ)
    dec A = ◃-skel A (expandᵏ-◃ Ω ⟦ τ ⟧ᴷ)

    f : Expᵏdec l (expandᵏ Ω ⟦ τ ⟧ᴷ)
    f {A} {B} mem =
      ◃-subDec (dec A)
               (subst (_◃ᵛ (B [ proj₂ (expandᵏ Ω ⟦ τ ⟧ᴷ) ]ᵛ))
                      (sym (unifies-∈ l ⟦ τ ⟧ᴷ (unifyᵏ-sound (skelEqns l) e) mem))
                      (dec B))

ExpMax : ∀ {Ω Ω''} → Subst Ω Ω''
       → Maybe (Σ[ Ω' ∈ Scope ] (Subst Ω Ω')) → Set
ExpMax {Ω} δ₀ = maybe′ (λ x → Σ[ δ' ∈ Subst (proj₁ x) _ ] ((proj₂ x ⨟ˢ δ') ≐ˢ δ₀)) ⊥

-- The expansion is most general among the substitutions satisfying the demands,
-- and its failure refutes them

expandSub-max : ∀ {Ω Ω''} {Q : Hyps Ω''} → (l : List (OVType Ω × OVType Ω))
              → (δ₀ : Subst Ω Ω'')
              → (∀ {A B} → (A , B) ∈ l → Q ⊩ A [ δ₀ ]ᵛ <:̂ᵛ B [ δ₀ ]ᵛ)
              → ExpMax δ₀ (expandSub l)
expandSub-max {Ω} l δ₀ k with unifyᵏ (skelEqns l) in e
... | nothing      = unifyᵏ-fail (skelEqns l) e (shapeˢ δ₀) (shape-unifies l δ₀ k)
... | just (m , τ) =
      expandᵏ-max Ω ⟦ τ ⟧ᴷ δ₀
        (λ α → ⊑-from (⟦ τ ⟧ᴷ α) (proj₁ fac) (sTy δ₀ α) (proj₂ fac α))
  where
    fac = unifyᵏ-max (skelEqns l) e (shapeˢ δ₀) (shape-unifies l δ₀ k)
