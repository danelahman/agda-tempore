--------------------------------------------------------------------------
-- Handler clauses against substitution.                                --
--                                                                      --
-- A clause family lives over `Γ ++ᶜ Dcl`, an ordinary suffix extension --
-- by the barrier lock and the clause's two binders. `IsSub` records a  --
-- transport of one, so towers of them compose and are identified by    --
-- `uip`; `cl-≡` says that substituting in a clause is the general      --
-- substitution at that suffix.                                         --
--------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.Syntax.Substitution.Clauses (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming.Action S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Substitution    S
open import MonomorphicCalculus.Syntax.Types           S

open import MonomorphicCalculus.Syntax.Renaming.Equivalence  S
open import MonomorphicCalculus.Syntax.Renaming.Coherence    S
open import MonomorphicCalculus.Syntax.Terms.Equivalence     S
open import MonomorphicCalculus.Syntax.Terms.Transport       S

open import MonomorphicCalculus.Syntax.Substitution.Base              S
open import MonomorphicCalculus.Syntax.Substitution.Lookup            S
open import MonomorphicCalculus.Syntax.Substitution.Action            S
open import MonomorphicCalculus.Syntax.Substitution.Equivalence       S
open import MonomorphicCalculus.Syntax.Substitution.Interchange       S
open import MonomorphicCalculus.Syntax.Substitution.Chain             S
open import MonomorphicCalculus.Syntax.Substitution.ChainEquivalence  S
open import MonomorphicCalculus.Syntax.Substitution.Variables         S
open import MonomorphicCalculus.Syntax.Substitution.At                S

-- The barrier lock and a clause's two binders, as a suffix.

Dcl : VType → Op → E → Ctx
Dcl D op ε'' =
  [] ⟨ ⊤ᵣ ⟩
     ∷ type-of-gtype (param op)
     ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ D ‼ ε'')

-- Every renaming reaching a clause comes out as an `eq-ren`-conjugated core;
-- the helpers below fuse nested conjugations, extend one by a suffix, and turn
-- a conjugation into transports around the core's action.

infix 4 _≐ʳconj⟨_,_,_⟩

_≐ʳconj⟨_,_,_⟩ : ∀ {Γ₁ Γ₁' Γ₂ Γ₂'} → Ren [] Γ₂' Γ₁
              → (Γ₁ ≡ Γ₁') → Ren [] Γ₂ Γ₁' → (Γ₂ ≡ Γ₂') → Set
R ≐ʳconj⟨ e , K , e' ⟩ = R ≐ʳ (eq-ren e ∘ʳ K ∘ʳ eq-ren e')

conj-fuse : ∀ {Γ₁ Γ₀ Γ₀' Γ₂ Γ₂' Γ₃}
          → {R : Ren [] Γ₂' Γ₀} → (a : Γ₁ ≡ Γ₀) → (a' : Γ₂' ≡ Γ₃)
          → {K : Ren [] Γ₂ Γ₀'} → (b : Γ₀ ≡ Γ₀') → (b' : Γ₂ ≡ Γ₂')
          → R ≐ʳconj⟨ b , K , b' ⟩
          → (eq-ren a ∘ʳ R ∘ʳ eq-ren a') ≐ʳconj⟨ trans a b , K , trans b' a' ⟩
conj-fuse {R = R} refl refl {K = K} b b' h =
  ≐ʳ-trans (∘ʳ-identityˡ-≐ʳ _)
    (≐ʳ-trans (∘ʳ-identityʳ-≐ʳ _)
      (≐ʳ-trans h
        (∘ʳ-≐ʳ ≐ʳ-refl (∘ʳ-≐ʳ ≐ʳ-refl (eq-ren-≐ʳ b' (trans b' refl))))))

conj-cong-ren : ∀ {Γ₁ Γ₁' Γ₂ Γ₂'} → (Δ : Ctx)
              → {R : Ren [] Γ₂' Γ₁} → (e : Γ₁ ≡ Γ₁')
              → {K : Ren [] Γ₂ Γ₁'} → (e' : Γ₂ ≡ Γ₂')
              → R ≐ʳconj⟨ e , K , e' ⟩
              → cong-ren {Γ'' = Δ} R
                  ≐ʳconj⟨ cong (_++ᶜ Δ) e , cong-ren {Γ'' = Δ} K
                        , cong (_++ᶜ Δ) e' ⟩
conj-cong-ren Δ e e' h =
  ≐ʳ-trans (cong-ren-≐ʳ Δ h)
    (≐ʳ-trans (cong-ren-∘-≐ʳ Δ _ _)
      (∘ʳ-≐ʳ (cong-ren-eq-ren-≐ʳ Δ e)
            (≐ʳ-trans (cong-ren-∘-≐ʳ Δ _ _)
                      (∘ʳ-≐ʳ ≐ʳ-refl (cong-ren-eq-ren-≐ʳ Δ e')))))

C-rename-conj : ∀ {Γ₁ Γ₁' Γ₂ Γ₂' C}
              → {R : Ren [] Γ₂' Γ₁} → (e : Γ₁ ≡ Γ₁')
              → {K : Ren [] Γ₂ Γ₁'} → (e' : Γ₂ ≡ Γ₂')
              → R ≐ʳconj⟨ e , K , e' ⟩
              → (X : Γ₁ ⊢C⦂ C)
              → C-rename R X
              ≡ subst (_⊢C⦂ C) e' (C-rename K (subst (_⊢C⦂ C) e X))
C-rename-conj e {K = K} e' h X =
  trans (C-rename-≡ h X)
    (trans (C-rename-∘ (eq-ren e) (K ∘ʳ eq-ren e') X)
      (trans
        (C-rename-cong (K ∘ʳ eq-ren e') (C-rename-eq-≡ e ≐ʳ-refl X))
        (trans (C-rename-∘ K (eq-ren e') _)
                  (C-rename-eq-≡ e' ≐ʳ-refl _))))

-- Recording "X is some transport of h" makes the transports compose, and two
-- such records of the same `h` are equal by `uip`.

IsSub : ∀ {Γ₀ Γ₁ C} → Γ₀ ⊢C⦂ C → Γ₁ ⊢C⦂ C → Set
IsSub {Γ₀} {Γ₁} {C} h X = Σ[ e ∈ Γ₀ ≡ Γ₁ ] X ≡ subst (_⊢C⦂ C) e h

isSub-refl : ∀ {Γ₀ C} → (h : Γ₀ ⊢C⦂ C) → IsSub h h
isSub-refl h = refl , refl

isSub-substC : ∀ {Γ₀ Γ₁ Γ₂ C} → {h : Γ₀ ⊢C⦂ C} → (X : Γ₁ ⊢C⦂ C) → (e : Γ₁ ≡ Γ₂)
             → IsSub h X → IsSub h (subst (_⊢C⦂ C) e X)
isSub-substC {C = C} {h = h} X e (e₀ , q) =
  trans e₀ e
  , trans (cong (subst (_⊢C⦂ C) e) q) (subst-fuseᶜ e₀ e h)

isSub-cast : ∀ {Γ₀ Γ₁ Γ₂ C} → {h : Γ₀ ⊢C⦂ C} → (X : Γ₁ ⊢C⦂ C) → (e : Γ₁ ≡ Γ₂)
           → IsSub h X → IsSub h (castᶜ e X)
isSub-cast {C = C} X e p =
  subst (IsSub _) (sym (castᶜ≡subst e X)) (isSub-substC X e p)

isSub-reassoc : ∀ {Γ₀ Γ₁ Γ₂ C} → {h : Γ₀ ⊢C⦂ C} → {X : Γ₁ ⊢C⦂ C} → {Y : Γ₂ ⊢C⦂ C}
              → IsSub h X → IsSub h Y → IsSub Y X
isSub-reassoc {C = C} {h = h} (e , q) (e' , q') =
  trans (sym e') e
  , trans q
      (trans (cong (λ z → subst (_⊢C⦂ C) z h)
                   (uip {p = e} {q = trans e' (trans (sym e') e)}))
        (trans (sym (subst-fuseᶜ e' (trans (sym e') e) h))
               (cong (subst (_⊢C⦂ C) (trans (sym e') e)) (sym q'))))

-- two transports of `≡`-related terms are `≡`-related

isSub-≡ : ∀ {Γ₀ Γ₁ C} → {M M' : Γ₀ ⊢C⦂ C} → {X Y : Γ₁ ⊢C⦂ C}
        → IsSub M X → IsSub M' Y → M ≡ M' → X ≡ Y
isSub-≡ {C = C} {M' = M'} (e , q) (e' , q') eM =
  trans (q)
    (trans (substᶜ-≡ e eM)
      ((trans (cong (λ z → subst (_⊢C⦂ C) z M') (uip {p = e} {q = e'}))
                   (sym q'))))

-- The `_≡_`-flavoured alignment, taking the terms and the values related only
-- up to `_≡_`.

sub-at-≡ : ∀ {Γ₁ Γ₂ B C Θ₁ Θ₂} → (eΓ : Γ₁ ≡ Γ₂) → (eΘ : Θ₁ ≡ Θ₂)
         → (X₁ : ((Γ₁ ∷ B) ++ᶜ Θ₁) ⊢C⦂ C) → (X₂ : ((Γ₂ ∷ B) ++ᶜ Θ₂) ⊢C⦂ C)
         → (e : ((Γ₁ ∷ B) ++ᶜ Θ₁) ≡ ((Γ₂ ∷ B) ++ᶜ Θ₂))
         → X₂ ≡ subst (_⊢C⦂ C) e X₁
         → (V₁ : Γ₁ ⊢V⦂ B) → (V₂ : Γ₂ ⊢V⦂ B)
         → subst (_⊢V⦂ B) eΓ V₁ ≡ V₂
         → (e' : (Γ₁ ++ᶜ Θ₁) ≡ (Γ₂ ++ᶜ Θ₂))
         → X₂ [ split-≡-++ᶜ {Γ₂ ∷ B} {Θ₂} ↦ V₂ ]c
         ≡ subst (_⊢C⦂ C) e' (X₁ [ split-≡-++ᶜ {Γ₁ ∷ B} {Θ₁} ↦ V₁ ]c)
sub-at-≡ {C = C} refl refl X₁ X₂ e eX V₁ V₂ eV e'
  rewrite uip {p = e} {q = refl} | uip {p = e'} {q = refl} =
  sub-≡ᶜ split-≡-++ᶜ (sym eV) eX

-- The general substitution at the clause's own suffix. Both sides build the
-- same generating substitution: `split-++ʳ s (Dcl D op ε)` peels the suffix
-- into the three congruences `_[_↦_]cl` applies.

cl-≡ : ∀ {Γ₀ Γ₁ Γ₂ A D} → (s : Γ₁ ∷ A , Γ₂ split Γ₀) → (W : Γ₁ ⊢V⦂ A)
     → (H : Fam D (Γ₀ ⟨ ⊤ᵣ ⟩)) → (op : Op) → (ε : E)
     → (H [ s ↦ W ]cl) op ε
     ≡ (H op ε) [ split-++ʳ s (Dcl D op ε) ↦ W ]c
cl-≡ s W H op ε = refl
