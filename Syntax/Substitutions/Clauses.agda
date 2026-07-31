------------------------------------------------------------------------
-- Handler clauses against substitution.                               --
--                                                                     --
-- A clause family lives over `Γ ᴱ ++ᶜ Dcl`, so every step that reaches --
-- one is either a transport of it or a substitution at the *restricted* --
-- context. `IsSub` records the first kind so that towers of them        --
-- compose and are identified by `uip`; `cl-yes` says what the second    --
-- kind is — a `sub-atᶜ` at the splitting's own halves.                  --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions.Clauses (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.RenActions    S
open import Syntax.Renamings     S
open import Syntax.Substitutions S
open import Syntax.Types         S

open import Syntax.Renamings.Equivalence S
open import Syntax.Renamings.Coherence   S
open import Syntax.Terms.Equivalence     S
open import Syntax.Terms.Transport       S

open import Syntax.Substitutions.Base             S
open import Syntax.Substitutions.Lookup           S
open import Syntax.Substitutions.Action           S
open import Syntax.Substitutions.Equivalence      S
open import Syntax.Substitutions.Interchange      S
open import Syntax.Substitutions.Chain            S
open import Syntax.Substitutions.ChainEquivalence S
open import Syntax.Substitutions.Restrict         S
open import Syntax.Substitutions.Variables        S
open import Syntax.Substitutions.At               S

-- A clause's two binders, as a suffix.

Dcl : VType → Op → E → Ctx
Dcl D op ε'' =
  [] ∷ type-of-gtype (param op)
     ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ D ‼ ε'')

------------------------------------------------------------------------
-- CONJUGATED DECOMPOSITIONS
--
-- Every renaming reaching a clause comes out as an `eq-ren`-conjugated core;
-- the helpers below fuse nested conjugations, extend one by a suffix, and turn
-- a conjugation into transports around the core's action.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- BEING A TRANSPORT
--
-- Recording "X is some transport of h" makes the transports compose, and two
-- such records of the same `h` are equal by `uip`.
------------------------------------------------------------------------

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

-- the two shapes the clause level actually presents

isSub-Cl : ∀ {Γ₀ Γ₁ Γ₂ D} → (op : Op) → (ε : E)
         → {h : Γ₀ ⊢C⦂ D ‼ (op-grade op ·ₑ ε)}
         → (X : Cl D op ε (Γ₁ ᴱ)) → (e : Γ₁ ≡ Γ₂)
         → IsSub h X → IsSub h (Cl-cast op ε e X)
isSub-Cl {D = D} op ε X e p =
  isSub-cast X
    (cong (λ Γ₃ → Γ₃ ᴱ ∷ type-of-gtype (param op)
                     ∷ [ mapᵉ (op-grade op) ]
                         (type-of-gtype (arity op) ⇒ D ‼ ε))
          e)
    p

isSub-substD : ∀ {Γ₀ Γ₁ Γ₂ C} → (Dc : Ctx) → {h : Γ₀ ⊢C⦂ C}
             → (X : (Γ₁ ++ᶜ Dc) ⊢C⦂ C) → (e : Γ₁ ≡ Γ₂)
             → IsSub h X
             → IsSub h (subst (λ Γ₃ → (Γ₃ ++ᶜ Dc) ⊢C⦂ C) e X)
isSub-substD Dc X e p =
  subst (IsSub _) (sym (subst-++ᶜʳ Dc e X))
        (isSub-substC X (cong (_++ᶜ Dc) e) p)

isSub-reassoc : ∀ {Γ₀ Γ₁ Γ₂ C} → {h : Γ₀ ⊢C⦂ C} → {X : Γ₁ ⊢C⦂ C} → {Y : Γ₂ ⊢C⦂ C}
              → IsSub h X → IsSub h Y → IsSub Y X
isSub-reassoc {C = C} {h = h} (e , q) (e' , q') =
  trans (sym e') e
  , trans q
      (trans (cong (λ z → subst (_⊢C⦂ C) z h)
                   (uip {p = e} {q = trans e' (trans (sym e') e)}))
        (trans (sym (subst-fuseᶜ e' (trans (sym e') e) h))
               (cong (subst (_⊢C⦂ C) (trans (sym e') e)) (sym q'))))

isSub-trans : ∀ {Γ₀ Γ₁ Γ₂ C} → {h : Γ₀ ⊢C⦂ C} → {X : Γ₁ ⊢C⦂ C} → {Y : Γ₂ ⊢C⦂ C}
            → IsSub h X → IsSub X Y → IsSub h Y
isSub-trans {C = C} {h = h} (e , q) (e' , q') =
  trans e e'
  , trans q' (trans (cong (subst (_⊢C⦂ C) e') q) (subst-fuseᶜ e e' h))

isSub-uniq : ∀ {Γ₀ Γ₁ C} → {h : Γ₀ ⊢C⦂ C} → {X Y : Γ₁ ⊢C⦂ C}
           → IsSub h X → IsSub h Y → X ≡ Y
isSub-uniq {C = C} {h = h} (e , q) (e' , q') =
  trans q (trans (cong (λ z → subst (_⊢C⦂ C) z h) (uip {p = e} {q = e'}))
                 (sym q'))

-- two transports of `≡`-related terms are `≡`-related

isSub-≡ : ∀ {Γ₀ Γ₁ C} → {M M' : Γ₀ ⊢C⦂ C} → {X Y : Γ₁ ⊢C⦂ C}
        → IsSub M X → IsSub M' Y → M ≡ M' → X ≡ Y
isSub-≡ {C = C} {M' = M'} (e , q) (e' , q') eM =
  trans (q)
    (trans (substᶜ-≡ e eM)
      ((trans (cong (λ z → subst (_⊢C⦂ C) z M') (uip {p = e} {q = e'}))
                   (sym q'))))

------------------------------------------------------------------------
-- ALIGNING TWO BOUNDARY SUBSTITUTIONS
------------------------------------------------------------------------

-- `sub-atᶜ` is natural in a transport of its prefix, its suffix, its term and
-- its value. Proved by matching the two context equations; the `IsSub` premise
-- then forces the terms equal, its own equation being a loop.

sub-at-IsSub : ∀ {Γ₁ Γ₂ B C Θ₁ Θ₂} → (eΓ : Γ₁ ≡ Γ₂) → (eΘ : Θ₁ ≡ Θ₂)
             → (X₁ : ((Γ₁ ∷ B) ++ᶜ Θ₁) ⊢C⦂ C)
             → (X₂ : ((Γ₂ ∷ B) ++ᶜ Θ₂) ⊢C⦂ C)
             → IsSub X₁ X₂
             → (V₁ : Γ₁ ⊢V⦂ B) → (V₂ : Γ₂ ⊢V⦂ B)
             → subst (_⊢V⦂ B) eΓ V₁ ≡ V₂
             → IsSub (sub-atᶜ Θ₁ X₁ V₁) (sub-atᶜ Θ₂ X₂ V₂)
sub-at-IsSub refl refl X₁ X₂ (e , q) V .V refl =
  refl , cong (λ z → sub-atᶜ _ z V) (trans q (subst-loopᶜ e X₁))

-- The `_≡_`-flavoured alignment, taking the terms and the values related only
-- up to `_≡_`.

sub-at-≡ : ∀ {Γ₁ Γ₂ B C Θ₁ Θ₂} → (eΓ : Γ₁ ≡ Γ₂) → (eΘ : Θ₁ ≡ Θ₂)
         → (X₁ : ((Γ₁ ∷ B) ++ᶜ Θ₁) ⊢C⦂ C) → (X₂ : ((Γ₂ ∷ B) ++ᶜ Θ₂) ⊢C⦂ C)
         → (e : ((Γ₁ ∷ B) ++ᶜ Θ₁) ≡ ((Γ₂ ∷ B) ++ᶜ Θ₂))
         → X₂ ≡ subst (_⊢C⦂ C) e X₁
         → (V₁ : Γ₁ ⊢V⦂ B) → (V₂ : Γ₂ ⊢V⦂ B)
         → subst (_⊢V⦂ B) eΓ V₁ ≡ V₂
         → (e' : (Γ₁ ++ᶜ Θ₁) ≡ (Γ₂ ++ᶜ Θ₂))
         → sub-atᶜ Θ₂ X₂ V₂ ≡ subst (_⊢C⦂ C) e' (sub-atᶜ Θ₁ X₁ V₁)
sub-at-≡ {C = C} refl refl X₁ X₂ e eX V₁ V₂ eV e'
  rewrite uip {p = e} {q = refl} | uip {p = e'} {q = refl} =
  trans (sub-atᶜ-≡ _ V₂ eX) (sub-atᶜ-≡ᵥ _ X₁ (sym eV))

-- The eternal restriction respects a transport of its context.

restrict-substᵛ : ∀ {Γ₁ Γ₂ A} → (e : Γ₁ ≡ Γ₂) → (et : Eternal A) → (V : Γ₁ ⊢V⦂ A)
                → eternal-val-restrict et (subst (_⊢V⦂ A) e V)
                ≡ subst (_⊢V⦂ A) (cong _ᴱ e) (eternal-val-restrict et V)
restrict-substᵛ refl et V = refl

------------------------------------------------------------------------
-- WHAT `_[_↦_]cl` IS AT AN ETERNAL TYPE
--
-- It is `sub-atᶜ` at the *restricted* contexts — but at the splitting's own
-- halves (`split-l x ᴱ`, `split-r x ᴱ ++ᶜ Dcl`), not at the contexts those are
-- propositionally equal to: only there do `split-++ʳ (∈-ᴱ-split et x) Dcl` and
-- `split-≡-++ᶜ` have literally the same halves, so `split→∈-unique` applies on
-- the nose. Both are transports of one and the same substituted clause, which
-- is what the two lemmas below record; `isSub-uniq` then identifies them.
------------------------------------------------------------------------

-- The context equation between the clause's own context and the one the
-- splitting names it at.

bigEqCl : ∀ {Γ₀ A ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀) → (D : VType)
        → (op : Op) → (ε : E)
        → (split-l (split→∈ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε)))
             ++ᶜ split-r (split→∈ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε))))
        ≡ ((split-l x ++ᶜ split-r x) ᴱ ++ᶜ Dcl D op ε)
bigEqCl {Γ₀} {A} et x D op ε =
  trans (cong₂ _++ᶜ_ (split→∈-split-l s) (split→∈-split-r s))
    (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) (Dcl D op ε)))
           (cong (_++ᶜ Dcl D op ε) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
  where
    s = split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε)

clBody : ∀ {Γ₀ A ρ D} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀)
       → (W : split-l x ⊢V⦂ A) → (H : Fam D (Γ₀ ᴱ)) → (op : Op) → (ε : E)
       → (split-l (split→∈ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε)))
            ++ᶜ split-r (split→∈ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε))))
         ⊢C⦂ D ‼ (op-grade op ·ₑ ε)
clBody {D = D} et x W H op ε =
  (H op ε) [ split→∈ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε))
             ↦ subst (_⊢V⦂ _)
                 (sym (split→∈-split-l
                        (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε))))
                 (eternal-val-restrict et W) ]c

-- The clause substitution is that body, transported: at an eternal type the
-- restricted substitution *is* the restricted value put in for the variable
-- `∈-ᴱ-split` names, which is `restrict-sub-at-et`.

cl-yes-raw : ∀ {Γ₀ A ρ D} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀)
           → (W : split-l x ⊢V⦂ A) → (H : Fam D (Γ₀ ᴱ)) → (op : Op) → (ε : E)
           → IsSub (clBody et x W H op ε) ((H [ x ↦ W ]cl) op ε)
cl-yes-raw {D = D} et x W H op ε =
  bigEqCl et x D op ε , cl-et-≡ et x W H op ε (bigEqCl et x D op ε)

cl-yes-sub : ∀ {Γ₀ A ρ D} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀)
           → (W : split-l x ⊢V⦂ A) → (H : Fam D (Γ₀ ᴱ)) → (op : Op) → (ε : E)
           → (e : (Γ₀ ᴱ ++ᶜ Dcl D op ε)
                ≡ ((split-l x ᴱ ∷ A) ++ᶜ (split-r x ᴱ ++ᶜ Dcl D op ε)))
           → IsSub (clBody et x W H op ε)
                   (sub-atᶜ {split-l x ᴱ} {A} (split-r x ᴱ ++ᶜ Dcl D op ε)
                            (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) e (H op ε))
                            (eternal-val-restrict et W))
cl-yes-sub {Γ₀} {A} {ρ} {D} et x W H op ε e =
  isSub-cast _ (castOf {split-l x ᴱ} {A} (split-r x ᴱ ++ᶜ Dcl D op ε))
    (_ , sub-cast-C′ e (H op ε) v y ey U U' eU)
  where
    Dc = Dcl D op ε
    Γ₀' = split-l x ᴱ
    Θ₀' = split-r x ᴱ ++ᶜ Dc

    s = split-++ʳ (∈-ᴱ-split et x) Dc
    v = split→∈ s
    y = split→∈ (split-≡-++ᶜ {Γ₀' ∷ A} {Θ₀'})

    ey : subst (λ Γ₁ → A ∈[ ctx-grade Θ₀' ] Γ₁) e v ≡ y
    ey = split→∈-unique e s (split-≡-++ᶜ {Γ₀' ∷ A} {Θ₀'})

    U : split-l v ⊢V⦂ A
    U = subst (_⊢V⦂ A) (sym (split→∈-split-l s)) (eternal-val-restrict et W)

    U' : split-l y ⊢V⦂ A
    U' = bval Θ₀' (eternal-val-restrict et W)

    eU : subst (_⊢V⦂ A) (trans (split-l-cast e v) (cong split-l ey)) U ≡ U'
    eU =
      trans (subst-fuseᵛ (sym (split→∈-split-l s))
                         (trans (split-l-cast e v) (cong split-l ey))
                         (eternal-val-restrict et W))
        (trans (substᵛ-irr _
                  (sym (split→∈-split-l (split-≡-++ᶜ {Γ₀' ∷ A} {Θ₀'})))
                  (eternal-val-restrict et W))
               (sym (castᵛ≡subst _ (eternal-val-restrict et W))))

cl-yes : ∀ {Γ₀ A ρ D} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀)
       → (W : split-l x ⊢V⦂ A) → (H : Fam D (Γ₀ ᴱ)) → (op : Op) → (ε : E)
       → (e : (Γ₀ ᴱ ++ᶜ Dcl D op ε)
            ≡ ((split-l x ᴱ ∷ A) ++ᶜ (split-r x ᴱ ++ᶜ Dcl D op ε)))
       → IsSub (sub-atᶜ {split-l x ᴱ} {A} (split-r x ᴱ ++ᶜ Dcl D op ε)
                        (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) e (H op ε))
                        (eternal-val-restrict et W))
               ((H [ x ↦ W ]cl) op ε)
cl-yes et x W H op ε e =
  isSub-reassoc (cl-yes-raw et x W H op ε) (cl-yes-sub et x W H op ε e)

-- The equation `cl-yes` wants is the splitting's own.

eCl : ∀ {Γ₀ A ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀) → (D : VType)
    → (op : Op) → (ε : E)
    → (Γ₀ ᴱ ++ᶜ Dcl D op ε)
    ≡ ((split-l x ᴱ ∷ A) ++ᶜ (split-r x ᴱ ++ᶜ Dcl D op ε))
eCl et x D op ε =
  sym (split-≡ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε)))
