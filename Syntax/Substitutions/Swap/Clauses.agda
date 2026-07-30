------------------------------------------------------------------------
-- The clause cases, and the swap theorem.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality
module Syntax.Substitutions.Swap.Clauses (Spec : LanguageSpec) where
open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts      Spec
open import Syntax.Language      Spec
open import Syntax.RenActions    Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

open import Syntax.Renamings.Equivalence    Spec
open import Syntax.Renamings.Coherence      Spec
open import Syntax.Terms.Equivalence        Spec
open import Syntax.Terms.Transport          Spec
open import Syntax.Substitutions.Equivalence Spec
open import Syntax.Substitutions.Variables   Spec
open import Syntax.Substitutions.Weakening   Spec
open import Syntax.Substitutions.Renaming    Spec
open import Syntax.Substitutions.Swap.Base Spec
open import Syntax.Substitutions.Swap.Variables Spec

-- BEING A TRANSPORT OF A GIVEN TERM
--
-- Every clause-level step that does not substitute is a transport, of one
-- of two shapes (`Cl-cast`, and `⟨ no ¬et ⟩cl`'s own `subst` at the
-- `_++ᶜ D` motive). Recording "X is some transport of h" makes them
-- compose, and two such records of the same `h` are equal by `uip` —
-- which is the whole of the both-non-eternal branch.
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

-- the shape `⟨ no ¬et ⟩[_↦_]cl` transports at
isSub-substD : ∀ {Γ₀ Γ₁ Γ₂ C} → (Dc : Ctx) → {h : Γ₀ ⊢C⦂ C}
             → (X : (Γ₁ ++ᶜ Dc) ⊢C⦂ C) → (e : Γ₁ ≡ Γ₂)
             → IsSub h X
             → IsSub h (subst (λ Γ₃ → (Γ₃ ++ᶜ Dc) ⊢C⦂ C) e X)
isSub-substD Dc X e p =
  subst (IsSub _) (sym (subst-++ᶜʳ Dc e X))
        (isSub-substC X (cong (_++ᶜ Dc) e) p)

-- two transports of one term are transports of each other

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

-- BOTH ENTRIES NON-ETERNAL
--
-- Neither `⟨ no ¬et ⟩cl` substitutes, so each side is a tower of
-- transports over the same clause: four on the left, six on the right.

cl-swap-nn : ∀ {Γ B₁ B₂ D} → (¬et₁ : ¬ Eternal B₁) → (¬et₂ : ¬ Eternal B₂)
           → (Θ : Ctx) → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁) → (op : Op) → (ε : E)
           → ClSwap (no ¬et₁) (no ¬et₂) Θ H W₂ W₁ op ε

cl-swap-nn {Γ} {B₁} {B₂} {D} ¬et₁ ¬et₂ Θ H W₂ W₁ op ε =
  (isSub-uniq lhs rhs)
  where
    Dc = Dcl D op ε

    lhs : IsSub (H op ε) (outerᴴ′ (no ¬et₁) (no ¬et₂) Θ H W₂ W₁ op ε)
    lhs =
      isSub-Cl op ε _ (castOf {Γ} {B₁} Θ)
        (isSub-substD Dc _ (ᴱ-drop-split ¬et₁ (bvar B₁ Θ))
          (isSub-Cl op ε _ (castOf {Γ ∷ B₁} {B₂} Θ)
            (isSub-substD Dc _ (ᴱ-drop-split ¬et₂ (bvar B₂ Θ))
              (isSub-refl (H op ε)))))

    rhs : IsSub (H op ε) (innerᴴ′ (no ¬et₁) (no ¬et₂) Θ H W₂ W₁ op ε)
    rhs =
      isSub-Cl op ε _ (castOf {Γ} {B₂} Θ)
        (isSub-substD Dc _ (ᴱ-drop-split ¬et₂ (bvar B₂ Θ))
          (isSub-Cl op ε _ (assocᴮ⁻ Γ B₂ Θ)
            (isSub-Cl op ε _ (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))
              (isSub-substD Dc _
                (ᴱ-drop-split ¬et₁ (bvar B₁ (([] ∷ B₂) ++ᶜ Θ)))
                (isSub-Cl op ε _ (assocᴮ Γ B₁ B₂ Θ)
                          (isSub-refl (H op ε)))))))

-- `sub-atᶜ` is natural in a transport of its prefix, its suffix, its term
-- and its value — which is what the eternal branches need, `cl-yes`
-- landing the two sides at contexts that agree only propositionally.
-- Proved by matching the two context equations; the `IsSub` premise then
-- forces the terms equal, its own equation being a loop.

sub-at-IsSub : ∀ {Γ₁ Γ₂ B C Θ₁ Θ₂} → (eΓ : Γ₁ ≡ Γ₂) → (eΘ : Θ₁ ≡ Θ₂)
             → (X₁ : ((Γ₁ ∷ B) ++ᶜ Θ₁) ⊢C⦂ C)
             → (X₂ : ((Γ₂ ∷ B) ++ᶜ Θ₂) ⊢C⦂ C)
             → IsSub X₁ X₂
             → (V₁ : Γ₁ ⊢V⦂ B) → (V₂ : Γ₂ ⊢V⦂ B)
             → subst (_⊢V⦂ B) eΓ V₁ ≡ V₂
             → IsSub (sub-atᶜ Θ₁ X₁ V₁) (sub-atᶜ Θ₂ X₂ V₂)
sub-at-IsSub refl refl X₁ X₂ (e , q) V .V refl =
  refl , cong (λ z → sub-atᶜ _ z V) (trans q (subst-loopᶜ e X₁))

-- The eternal restriction respects a transport of its context.

restrict-substᵛ : ∀ {Γ₁ Γ₂ A} → (e : Γ₁ ≡ Γ₂) → (et : Eternal A) → (V : Γ₁ ⊢V⦂ A)
                → eternal-val-restrict et (subst (_⊢V⦂ A) e V)
                ≡ subst (_⊢V⦂ A) (cong _ᴱ e) (eternal-val-restrict et V)
restrict-substᵛ refl et V = refl

------------------------------------------------------------------------
-- WHAT `⟨ yes et ⟩[_↦_]cl` REALLY IS
--
-- It is `sub-atᶜ` at the *restricted* contexts — but at the splitting's
-- own halves (`split-l x ᴱ`, `split-r x ᴱ ++ᶜ Dcl`), not at the contexts
-- those are propositionally equal to. That is `sub-wk-handle-et`'s
-- hard-won move, and the reason for it is the same: only there do
-- `split-++ʳ (∈-ᴱ-split et x) Dcl` and `split-≡-++ᶜ` have literally the
-- same halves, so `split→∈-unique` applies on the nose.
--
-- Both `⟨ yes et ⟩cl` and that `sub-atᶜ` are transports of one and the
-- same substituted clause, which is what the two lemmas below record;
-- `isSub-uniq` then identifies them.
------------------------------------------------------------------------

-- the substituted clause both sides are transports of

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

-- the clause substitution is that, transported (definitionally)

cl-yes-raw : ∀ {Γ₀ A ρ D} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀)
           → (W : split-l x ⊢V⦂ A) → (H : Fam D (Γ₀ ᴱ)) → (op : Op) → (ε : E)
           → IsSub (clBody et x W H op ε) (⟨ yes et ⟩[ x ↦ W ]cl H op ε)
cl-yes-raw et x W H op ε = _ , refl

-- and so is the `sub-atᶜ` at the splitting's own halves

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

-- hence the clause substitution *is* that `sub-atᶜ`, transported

cl-yes : ∀ {Γ₀ A ρ D} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀)
       → (W : split-l x ⊢V⦂ A) → (H : Fam D (Γ₀ ᴱ)) → (op : Op) → (ε : E)
       → (e : (Γ₀ ᴱ ++ᶜ Dcl D op ε)
            ≡ ((split-l x ᴱ ∷ A) ++ᶜ (split-r x ᴱ ++ᶜ Dcl D op ε)))
       → IsSub (sub-atᶜ {split-l x ᴱ} {A} (split-r x ᴱ ++ᶜ Dcl D op ε)
                        (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) e (H op ε))
                        (eternal-val-restrict et W))
               (⟨ yes et ⟩[ x ↦ W ]cl H op ε)
cl-yes et x W H op ε e =
  isSub-reassoc (cl-yes-raw et x W H op ε) (cl-yes-sub et x W H op ε e)

-- The equation `cl-yes` wants is the splitting's own.

eCl : ∀ {Γ₀ A ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀) → (D : VType)
    → (op : Op) → (ε : E)
    → (Γ₀ ᴱ ++ᶜ Dcl D op ε)
    ≡ ((split-l x ᴱ ∷ A) ++ᶜ (split-r x ᴱ ++ᶜ Dcl D op ε))
eCl et x D op ε =
  sym (split-≡ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε)))

-- ONE ENTRY ETERNAL
--
-- Exactly one side of each order substitutes, and both substitute the
-- same restricted value — but `cl-yes` lands them at contexts that agree
-- only propositionally (`split-r (bvar B₁ Θ) ≡ Θ` against
-- `split-r (bvar B₁ (([] ∷ B₂) ++ᶜ Θ)) ≡ ([] ∷ B₂) ++ᶜ Θ`, whose eternal
-- parts coincide because `B₂` is not eternal). `sub-at-IsSub` aligns
-- them; everything else is transports.

cl-swap-en : ∀ {Γ B₁ B₂ D} → (et₁ : Eternal B₁) → (¬et₂ : ¬ Eternal B₂)
           → (Θ : Ctx) → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁) → (op : Op) → (ε : E)
           → ClSwap (yes et₁) (no ¬et₂) Θ H W₂ W₁ op ε

cl-swap-en {Γ} {B₁} {B₂} {D} et₁ ¬et₂ Θ H W₂ W₁ op ε =
  (isSub-uniq lhs rhs)
  where
    Dc = Dcl D op ε
    Δ₂ = [] ∷ B₂
    Ŵ₂ = V-rename (wk-ren {A = B₁}) W₂

    xL = bvar {Γ} B₁ Θ
    xR = bvar {Γ} B₁ (Δ₂ ++ᶜ Θ)

    K : Fam D (((Γ ∷ B₁) ++ᶜ Θ) ᴱ)
    K = sub-atᴴ′ (no ¬et₂) Θ H Ŵ₂

    H' : Fam D (((Γ ∷ B₁) ++ᶜ (Δ₂ ++ᶜ Θ)) ᴱ)
    H' op' ε' = Cl-cast op' ε' (assocᴮ Γ B₁ B₂ Θ) (H op' ε')

    eL = eCl et₁ xL D op ε
    eR = eCl et₁ xR D op ε

    -- both substituted terms are transports of the clause
    isL : IsSub (H op ε) (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eL (K op ε))
    isL =
      isSub-substC _ eL
        (isSub-Cl op ε _ (castOf {Γ ∷ B₁} {B₂} Θ)
          (isSub-substD Dc _ (ᴱ-drop-split ¬et₂ (bvar B₂ Θ))
            (isSub-refl (H op ε))))

    isR : IsSub (H op ε) (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eR (H' op ε))
    isR =
      isSub-substC _ eR
        (isSub-Cl op ε _ (assocᴮ Γ B₁ B₂ Θ) (isSub-refl (H op ε)))

    -- and the two prefixes/suffixes agree
    eΓ : split-l xL ᴱ ≡ split-l xR ᴱ
    eΓ = cong _ᴱ (trans (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₁} {Θ}))
                        (sym (split→∈-split-l
                               (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ}))))

    -- `B₂` is not eternal, so the extra entry disappears from the
    -- restriction and the two suffixes' eternal parts coincide
    eΘᴱ : Θ ᴱ ≡ (Δ₂ ++ᶜ Θ) ᴱ
    eΘᴱ = sym (trans (ᴱ-++ᶜ Δ₂ Θ)
                (trans (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-drop {[]} {B₂} ¬et₂))
                       (++ᶜ-identityˡ {Θ ᴱ})))

    eΘ : (split-r xL ᴱ ++ᶜ Dc) ≡ (split-r xR ᴱ ++ᶜ Dc)
    eΘ = cong (_++ᶜ Dc)
              (trans (cong _ᴱ (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₁} {Θ})))
                (trans eΘᴱ
                       (cong _ᴱ (sym (split→∈-split-r
                                       (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ}))))))

    eV : subst (_⊢V⦂ B₁) eΓ
           (eternal-val-restrict et₁ (bval {Γ} Θ W₁))
       ≡ eternal-val-restrict et₁ (bval {Γ} (Δ₂ ++ᶜ Θ) W₁)
    eV =
      trans (cong (subst (_⊢V⦂ B₁) eΓ)
              (trans (cong (eternal-val-restrict et₁)
                           (castᵛ≡subst _ W₁))
                     (restrict-substᵛ _ et₁ W₁)))
        (trans (subst-fuseᵛ _ eΓ (eternal-val-restrict et₁ W₁))
          (trans (substᵛ-irr _ (cong _ᴱ (sym (split→∈-split-l
                                    (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ}))))
                             (eternal-val-restrict et₁ W₁))
            (trans (sym (restrict-substᵛ _ et₁ W₁))
                   (cong (eternal-val-restrict et₁)
                         (sym (castᵛ≡subst _ W₁))))))

    aligned : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                             (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eL (K op ε))
                             (eternal-val-restrict et₁ (bval Θ W₁)))
                    (sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                             (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eR (H' op ε))
                             (eternal-val-restrict et₁ (bval (Δ₂ ++ᶜ Θ) W₁)))
    aligned = sub-at-IsSub eΓ eΘ _ _ (isSub-reassoc isR isL) _ _ eV

    lhs : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                         (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eL (K op ε))
                         (eternal-val-restrict et₁ (bval Θ W₁)))
                (outerᴴ′ (yes et₁) (no ¬et₂) Θ H W₂ W₁ op ε)
    lhs =
      isSub-trans (cl-yes et₁ xL (bval Θ W₁) K op ε eL)
        (isSub-Cl op ε _ (castOf {Γ} {B₁} Θ) (isSub-refl _))

    rhs : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                         (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eL (K op ε))
                         (eternal-val-restrict et₁ (bval Θ W₁)))
                (innerᴴ′ (yes et₁) (no ¬et₂) Θ H W₂ W₁ op ε)
    rhs =
      isSub-trans aligned
        (isSub-trans (cl-yes et₁ xR (bval (Δ₂ ++ᶜ Θ) W₁) H' op ε eR)
          (isSub-Cl op ε _ (castOf {Γ} {B₂} Θ)
            (isSub-substD Dc _ (ᴱ-drop-split ¬et₂ (bvar B₂ Θ))
              (isSub-Cl op ε _ (assocᴮ⁻ Γ B₂ Θ)
                (isSub-Cl op ε _ (castOf {Γ} {B₁} (Δ₂ ++ᶜ Θ))
                          (isSub-refl _))))))

-- THE VALUE BRIDGE THE TWO REMAINING BRANCHES NEED
--
-- Where the left order weakens the outer value past `B₁` before
-- restricting it and the right order does not, the two agree — at a
-- *non-eternal* `B₁` the restriction of the weakening is the identity
-- (`ren-ᴱ-∷′ B₁ (no ¬et₁)` is `id-ren`), so this is
-- `eternal-val-restrict-ren` followed by `V-rename-id-≡`. Stated against
-- an arbitrary proof of the (only propositional) context equation, so the
-- caller may present it with whichever proof it has; `rewrite` then
-- reduces both `_ᴱ` and `ᴱ-∷-drop`, and `uip` finishes.

-- renaming along an identity-like renaming is the transport (the value
-- counterpart of `C-rename-eq-≡`)

V-rename-eq-≡ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {r : Ren [] Γ' Γ}
              → r ≐ʳ eq-ren e → (V : Γ ⊢V⦂ A)
              → V-rename r V ≡ subst (_⊢V⦂ A) e V
V-rename-eq-≡ refl h V = V-rename-id-≡ h V

restrict-wk-ne-≡ : ∀ {Γ₀ A B} → (¬et : ¬ Eternal B) → (et : Eternal A)
                 → (V : Γ₀ ⊢V⦂ A) → (e : Γ₀ ᴱ ≡ (Γ₀ ∷ B) ᴱ)
                 → eternal-val-restrict et (V-rename (wk-ren {A = B}) V)
                 ≡ subst (_⊢V⦂ A) e (eternal-val-restrict et V)
restrict-wk-ne-≡ {Γ₀} {A} {B} ¬et et V e =
  trans (eternal-val-restrict-ren et (wk-ren {A = B}) V)
           (V-rename-eq-≡ e (restrict-wk-≐ʳ ¬et [] e) (eternal-val-restrict et V))

-- and the action respects `_≡_` in the value it substitutes

sub-atᶜ-≡ᵥ : ∀ {Γ' B C} → (Θ : Ctx) → (X : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C)
           → {V V' : Γ' ⊢V⦂ B} → V ≡ V'
           → sub-atᶜ Θ X V ≡ sub-atᶜ Θ X V'
sub-atᶜ-≡ᵥ Θ X eV = castᶜ-≡ _ (sub-≡ᶜ _ (castᵛ-≡ _ eV) (refl {x = X}))

-- two transports of `≡`-related terms are `≡`-related

isSub-≡ : ∀ {Γ₀ Γ₁ C} → {M M' : Γ₀ ⊢C⦂ C} → {X Y : Γ₁ ⊢C⦂ C}
        → IsSub M X → IsSub M' Y → M ≡ M' → X ≡ Y
isSub-≡ {C = C} {M' = M'} (e , q) (e' , q') eM =
  trans (q)
    (trans (substᶜ-≡ e eM)
      ((trans (cong (λ z → subst (_⊢C⦂ C) z M') (uip {p = e} {q = e'}))
                   (sym q'))))

-- THE OUTER ENTRY ETERNAL, THE INNER ONE NOT
--
-- As `cl-swap-en`, except that here the two substituted values differ: the
-- left order restricts `W₂` *weakened past `B₁`*, the right order restricts
-- `W₂` itself. `restrict-wk-ne-≡` bridges them — at a non-eternal `B₁` the
-- restriction of that weakening is the identity — so the two `sub-atᶜ`s
-- agree only up to `_≡_`, and the branch is `≡` rather than `≡`.

cl-swap-ne : ∀ {Γ B₁ B₂ D} → (¬et₁ : ¬ Eternal B₁) → (et₂ : Eternal B₂)
           → (Θ : Ctx) → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁) → (op : Op) → (ε : E)
           → ClSwap (no ¬et₁) (yes et₂) Θ H W₂ W₁ op ε

cl-swap-ne {Γ} {B₁} {B₂} {D} ¬et₁ et₂ Θ H W₂ W₁ op ε =
  isSub-≡ lhs' rhs valStep
  where
    CT = D ‼ (op-grade op ·ₑ ε)
    Dc = Dcl D op ε
    Δ₂ = [] ∷ B₂
    Ŵ₂ = V-rename (wk-ren {A = B₁}) W₂

    xL = bvar {Γ ∷ B₁} B₂ Θ
    xR = bvar {Γ} B₂ Θ

    G : Fam D (((Γ ∷ B₂) ++ᶜ Θ) ᴱ)
    G = inner₀ᴴ′ (no ¬et₁) Θ H W₁

    eL = eCl et₂ xL D op ε
    eR = eCl et₂ xR D op ε

    VL = eternal-val-restrict et₂ (bval {Γ ∷ B₁} Θ Ŵ₂)
    VR = eternal-val-restrict et₂ (bval {Γ} Θ W₂)

    isL : IsSub (H op ε) (subst (_⊢C⦂ CT) eL (H op ε))
    isL = isSub-substC _ eL (isSub-refl (H op ε))

    isR : IsSub (H op ε) (subst (_⊢C⦂ CT) eR (G op ε))
    isR =
      isSub-substC _ eR
        (isSub-Cl op ε _ (assocᴮ⁻ Γ B₂ Θ)
          (isSub-Cl op ε _ (castOf {Γ} {B₁} (Δ₂ ++ᶜ Θ))
            (isSub-substD Dc _ (ᴱ-drop-split ¬et₁ (bvar B₁ (Δ₂ ++ᶜ Θ)))
              (isSub-Cl op ε _ (assocᴮ Γ B₁ B₂ Θ) (isSub-refl (H op ε))))))

    -- `B₁` is not eternal, so the two prefixes' eternal parts coincide
    eΓ : split-l xL ᴱ ≡ split-l xR ᴱ
    eΓ = trans (cong _ᴱ (split→∈-split-l (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ})))
           (trans (ᴱ-∷-drop {Γ} {B₁} ¬et₁)
                  (cong _ᴱ (sym (split→∈-split-l
                                  (split-≡-++ᶜ {Γ ∷ B₂} {Θ})))))

    eΘ : (split-r xL ᴱ ++ᶜ Dc) ≡ (split-r xR ᴱ ++ᶜ Dc)
    eΘ = cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
              (trans (split→∈-split-r (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ}))
                     (sym (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₂} {Θ}))))

    aligned : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                             (subst (_⊢C⦂ CT) eL (H op ε)) VL)
                    (sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                             (subst (_⊢C⦂ CT) eR (G op ε))
                             (subst (_⊢V⦂ B₂) eΓ VL))
    aligned = sub-at-IsSub eΓ eΘ _ _ (isSub-reassoc isR isL) VL _ refl

    lhs : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                         (subst (_⊢C⦂ CT) eL (H op ε)) VL)
                (outerᴴ′ (no ¬et₁) (yes et₂) Θ H W₂ W₁ op ε)
    lhs =
      isSub-trans (cl-yes et₂ xL (bval Θ Ŵ₂) H op ε eL)
        (isSub-Cl op ε _ (castOf {Γ} {B₁} Θ)
          (isSub-substD Dc _ (ᴱ-drop-split ¬et₁ (bvar B₁ Θ))
            (isSub-Cl op ε _ (castOf {Γ ∷ B₁} {B₂} Θ) (isSub-refl _))))

    rhs : IsSub (sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                         (subst (_⊢C⦂ CT) eR (G op ε)) VR)
                (innerᴴ′ (no ¬et₁) (yes et₂) Θ H W₂ W₁ op ε)
    rhs =
      isSub-trans (cl-yes et₂ xR (bval Θ W₂) G op ε eR)
        (isSub-Cl op ε _ (castOf {Γ} {B₂} Θ) (isSub-refl _))

    cL : (Γ ∷ B₁) ≡ split-l xL
    cL = sym (split→∈-split-l (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ}))

    cR : Γ ≡ split-l xR
    cR = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₂} {Θ}))

    e₀ : Γ ᴱ ≡ (Γ ∷ B₁) ᴱ
    e₀ = sym (ᴱ-∷-drop {Γ} {B₁} ¬et₁)

    eVal : subst (_⊢V⦂ B₂) eΓ VL ≡ VR
    eVal =
      trans
        ((cong (subst (_⊢V⦂ B₂) eΓ)
                (trans (cong (eternal-val-restrict et₂) (castᵛ≡subst cL Ŵ₂))
                       (restrict-substᵛ cL et₂ Ŵ₂))))
        (trans
          (substᵛ-≡ eΓ (substᵛ-≡ (cong _ᴱ cL)
                                 (restrict-wk-ne-≡ ¬et₁ et₂ W₂ e₀)))
          (            (trans (cong (subst (_⊢V⦂ B₂) eΓ)
                     (subst-fuseᵛ e₀ (cong _ᴱ cL)
                                  (eternal-val-restrict et₂ W₂)))
              (trans (subst-fuseᵛ (trans e₀ (cong _ᴱ cL)) eΓ
                                  (eternal-val-restrict et₂ W₂))
                (trans (substᵛ-irr (trans (trans e₀ (cong _ᴱ cL)) eΓ)
                                   (cong _ᴱ cR)
                                   (eternal-val-restrict et₂ W₂))
                  (trans (sym (restrict-substᵛ cR et₂ W₂))
                         (cong (eternal-val-restrict et₂)
                               (sym (castᵛ≡subst cR W₂)))))))))

    valStep : sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eR (G op ε))
                      (subst (_⊢V⦂ B₂) eΓ VL)
            ≡ sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                       (subst (_⊢C⦂ CT) eR (G op ε)) VR
    valStep = sub-atᶜ-≡ᵥ _ _ eVal

    lhs' : IsSub (sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                          (subst (_⊢C⦂ CT) eR (G op ε))
                          (subst (_⊢V⦂ B₂) eΓ VL))
                 (outerᴴ′ (no ¬et₁) (yes et₂) Θ H W₂ W₁ op ε)
    lhs' = isSub-reassoc lhs aligned

-- The eternal counterpart of `restrict-wk-ne-≡`: at an *eternal* `B` the
-- restriction of the weakening is the weakening again, so restricting a
-- `B`-weakened value is weakening its restriction — which is exactly the
-- value `outerᶜ` hands its inner step.

restrict-wk-et-≡ᵛ : ∀ {Γ₀ A B} → (etB : Eternal B) → (et : Eternal A)
                  → (V : Γ₀ ⊢V⦂ A) → (e : (Γ₀ ∷ B) ᴱ ≡ Γ₀ ᴱ ∷ B)
                  → eternal-val-restrict et (V-rename (wk-ren {A = B}) V)
                  ≡ subst (_⊢V⦂ A) (sym e)
                       (V-rename (wk-ren {A = B}) (eternal-val-restrict et V))
restrict-wk-et-≡ᵛ {Γ₀} {A} {B} etB et V e =
  trans (eternal-val-restrict-ren et (wk-ren {A = B}) V)
    (trans (V-rename-≡ (restrict-wk-et-≐ʳ etB [] refl e)
                          (eternal-val-restrict et V))
      (trans (V-rename-∘ (eq-ren refl) (wk-ren ∘ʳ eq-ren (sym e))
                            (eternal-val-restrict et V))
        (trans
          (V-rename-cong (wk-ren ∘ʳ eq-ren (sym e))
                         (V-rename-id-≡ ≐ʳ-refl _))
          (trans (V-rename-∘ (wk-ren {A = B}) (eq-ren (sym e)) _)
                    (V-rename-eq-≡ (sym e) ≐ʳ-refl _)))))

-- The `_≡_`-flavoured alignment the both-eternal branch needs. Unlike
-- `sub-at-IsSub` it takes the terms related only up to `_≡_` and the
-- values only up to `_≡_` — which is what the nested case forces, the
-- inner `sub-atᶜ`s' values being restrictions of *weakened* values, equal
-- to the unweakened ones only up to `restrict-wk-et-≡ᵛ`.

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

-- The recursion the both-eternal branch makes, with its context given by
-- an equation rather than literally — as `sub-wk-C-cast`, and for the same
-- reason: casting the clause into shape is not structurally smaller, so the
-- termination checker would reject it. Forward-declared here and defined
-- after the induction, which puts it in the same recursive group; the
-- decrease is the clause `H op ε` against the `handle` node.

sub-swap-C-cast : ∀ {Γ B₁ B₂ Γ₀ C} → (Θ : Ctx)
                → (e : Γ₀ ≡ ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
                → (M : Γ₀ ⊢C⦂ C) → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
                → SubSwapC Θ (subst (_⊢C⦂ C) e M) W₂ W₁

-- BOTH ENTRIES ETERNAL
--
-- Both orders substitute twice, so after `cl-yes` on all four
-- substitutions the two sides *are* `outerᶜ` and `innerᶜ` at the
-- restricted contexts — at an eternal `B₁`, `(Γ ∷ B₁) ᴱ` is `Γ ᴱ ∷ B₁`,
-- and at an eternal `B₂` the right order's inner suffix is
-- `([] ∷ B₂) ++ᶜ Θ ᴱ ++ᶜ Dcl`, which is `inner₀ᶜ`'s own re-bracketing up
-- to one `++ᶜ-assoc`. So the branch is `sub-swap-C` at `Θ ᴱ ++ᶜ Dcl`, and
-- the rest is the nested alignment: `sub-at-≡` at the inner level, then
-- again at the outer, on each side.

cl-swap-ee : ∀ {Γ B₁ B₂ D} → (et₁ : Eternal B₁) → (et₂ : Eternal B₂)
           → (Θ : Ctx) → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁) → (op : Op) → (ε : E)
           → ClSwap (yes et₁) (yes et₂) Θ H W₂ W₁ op ε

cl-swap-ee {Γ} {B₁} {B₂} {D} et₁ et₂ Θ H W₂ W₁ op ε =
  trans ee-left
    (trans (substᶜ-≡ eLfin (sub-swap-C-cast Θ' eXfull (H op ε) V₂ᴱ V₁ᴱ))
      (trans ((cong (λ z → subst (_⊢C⦂ CT) z (innerᶜ Θ' X V₂ᴱ V₁ᴱ))
                            (uip {p = eLfin} {q = eRfin})))
                (sym ee-right)))
  where
    CT = D ‼ (op-grade op ·ₑ ε)
    Dc = Dcl D op ε
    Δ₂ = [] ∷ B₂
    Θ' = Θ ᴱ ++ᶜ Dc
    Ŵ₂ = V-rename (wk-ren {A = B₁}) W₂

    V₁ᴱ = eternal-val-restrict et₁ W₁
    V₂ᴱ = eternal-val-restrict et₂ W₂

    -- the restriction of the doubly-extended context
    eᴱ : (Γ ∷ B₁ ∷ B₂) ᴱ ≡ Γ ᴱ ∷ B₁ ∷ B₂
    eᴱ = trans (ᴱ-∷-keep {Γ ∷ B₁} {B₂} et₂)
               (cong (_∷ B₂) (ᴱ-∷-keep {Γ} {B₁} et₁))

    eXfull : (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ ++ᶜ Dc) ≡ ((Γ ᴱ ∷ B₁ ∷ B₂) ++ᶜ Θ')
    eXfull =
      trans (cong (_++ᶜ Dc)
              (trans (ᴱ-++ᶜ (Γ ∷ B₁ ∷ B₂) Θ) (cong (_++ᶜ Θ ᴱ) eᴱ)))
            (++ᶜ-assoc (Γ ᴱ ∷ B₁ ∷ B₂) (Θ ᴱ) Dc)

    X : ((Γ ᴱ ∷ B₁ ∷ B₂) ++ᶜ Θ') ⊢C⦂ CT
    X = subst (_⊢C⦂ CT) eXfull (H op ε)

    ----------------------------------------------------------------
    -- the left order
    ----------------------------------------------------------------

    xL₁ = bvar {Γ} B₁ Θ
    xL₂ = bvar {Γ ∷ B₁} B₂ Θ

    K : Fam D (((Γ ∷ B₁) ++ᶜ Θ) ᴱ)
    K = sub-atᴴ′ (yes et₂) Θ H Ŵ₂

    eL₂ = eCl et₂ xL₂ D op ε
    eL₁ = eCl et₁ xL₁ D op ε

    VL₂ = eternal-val-restrict et₂ (bval {Γ ∷ B₁} Θ Ŵ₂)
    VL₁ = eternal-val-restrict et₁ (bval {Γ} Θ W₁)

    subatL₂ = sub-atᶜ {split-l xL₂ ᴱ} {B₂} (split-r xL₂ ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eL₂ (H op ε)) VL₂
    subatL₁ = sub-atᶜ {split-l xL₁ ᴱ} {B₁} (split-r xL₁ ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eL₁ (K op ε)) VL₁

    cL₂ : (Γ ∷ B₁) ≡ split-l xL₂
    cL₂ = sym (split→∈-split-l (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ}))

    cL₁ : Γ ≡ split-l xL₁
    cL₁ = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₁} {Θ}))

    eΓL₂ : split-l xL₂ ᴱ ≡ Γ ᴱ ∷ B₁
    eΓL₂ = trans (cong _ᴱ (sym cL₂)) (ᴱ-∷-keep {Γ} {B₁} et₁)

    eΘL₂ : (split-r xL₂ ᴱ ++ᶜ Dc) ≡ Θ'
    eΘL₂ = cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                (split→∈-split-r (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ}))

    eΓL₁ : split-l xL₁ ᴱ ≡ Γ ᴱ
    eΓL₁ = cong _ᴱ (sym cL₁)

    eΘL₁ : (split-r xL₁ ᴱ ++ᶜ Dc) ≡ Θ'
    eΘL₁ = cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₁} {Θ}))

    valL₂ : subst (_⊢V⦂ B₂) eΓL₂ VL₂ ≡ V-rename (wk-ren {A = B₁}) V₂ᴱ
    valL₂ =
      trans
        ((cong (subst (_⊢V⦂ B₂) eΓL₂)
                (trans (cong (eternal-val-restrict et₂) (castᵛ≡subst cL₂ Ŵ₂))
                       (restrict-substᵛ cL₂ et₂ Ŵ₂))))
        (trans
          (substᵛ-≡ eΓL₂
            (substᵛ-≡ (cong _ᴱ cL₂)
              (restrict-wk-et-≡ᵛ et₁ et₂ W₂ (ᴱ-∷-keep {Γ} {B₁} et₁))))
          (            (trans (cong (subst (_⊢V⦂ B₂) eΓL₂)
                     (subst-fuseᵛ (sym (ᴱ-∷-keep {Γ} {B₁} et₁)) (cong _ᴱ cL₂)
                                  (V-rename (wk-ren {A = B₁}) V₂ᴱ)))
              (trans (subst-fuseᵛ _ eΓL₂ (V-rename (wk-ren {A = B₁}) V₂ᴱ))
                     (substᵛ-irr _ refl (V-rename (wk-ren {A = B₁}) V₂ᴱ))))))

    valL₁ : subst (_⊢V⦂ B₁) eΓL₁ VL₁ ≡ V₁ᴱ
    valL₁ =
              (trans (cong (subst (_⊢V⦂ B₁) eΓL₁)
                 (trans (cong (eternal-val-restrict et₁) (castᵛ≡subst cL₁ W₁))
                        (restrict-substᵛ cL₁ et₁ W₁)))
          (trans (subst-fuseᵛ (cong _ᴱ cL₁) eΓL₁ V₁ᴱ)
                 (substᵛ-irr _ refl V₁ᴱ)))

    -- the inner alignment
    Oᴵ = sub-atᶜ {Γ ᴱ ∷ B₁} {B₂} Θ' X (V-rename (wk-ren {A = B₁}) V₂ᴱ)

    eIL : ((split-l xL₂ ᴱ ∷ B₂) ++ᶜ (split-r xL₂ ᴱ ++ᶜ Dc))
        ≡ ((Γ ᴱ ∷ B₁ ∷ B₂) ++ᶜ Θ')
    eIL = cong₂ (λ Γ₀ Θ₀ → (Γ₀ ∷ B₂) ++ᶜ Θ₀) eΓL₂ eΘL₂

    eIL' : (split-l xL₂ ᴱ ++ᶜ (split-r xL₂ ᴱ ++ᶜ Dc)) ≡ ((Γ ᴱ ∷ B₁) ++ᶜ Θ')
    eIL' = cong₂ _++ᶜ_ eΓL₂ eΘL₂

    oI : Oᴵ ≡ subst (_⊢C⦂ CT) eIL' subatL₂
    oI =
      sub-at-≡ eΓL₂ eΘL₂ (subst (_⊢C⦂ CT) eL₂ (H op ε)) X eIL
        ((sym (trans (subst-fuseᶜ eL₂ eIL (H op ε))
                          (cong (λ z → subst (_⊢C⦂ CT) z (H op ε))
                                (uip {p = trans eL₂ eIL} {q = eXfull})))))
        VL₂ (V-rename (wk-ren {A = B₁}) V₂ᴱ) valL₂ eIL'

    kIs : IsSub subatL₂ (subst (_⊢C⦂ CT) eL₁ (K op ε))
    kIs =
      isSub-substC _ eL₁
        (isSub-Cl op ε _ (castOf {Γ ∷ B₁} {B₂} Θ)
          (cl-yes et₂ xL₂ (bval Θ Ŵ₂) H op ε eL₂))

    eOL : ((split-l xL₁ ᴱ ∷ B₁) ++ᶜ (split-r xL₁ ᴱ ++ᶜ Dc))
        ≡ ((Γ ᴱ ∷ B₁) ++ᶜ Θ')
    eOL = cong₂ (λ Γ₀ Θ₀ → (Γ₀ ∷ B₁) ++ᶜ Θ₀) eΓL₁ eΘL₁

    eOL' : (split-l xL₁ ᴱ ++ᶜ (split-r xL₁ ᴱ ++ᶜ Dc)) ≡ (Γ ᴱ ++ᶜ Θ')
    eOL' = cong₂ _++ᶜ_ eΓL₁ eΘL₁

    termO : Oᴵ ≡ subst (_⊢C⦂ CT) eOL (subst (_⊢C⦂ CT) eL₁ (K op ε))
    termO =
      trans oI
        (          (trans (cong (λ z → subst (_⊢C⦂ CT) z subatL₂)
                       (uip {p = eIL'} {q = trans (proj₁ kIs) eOL}))
            (trans (sym (subst-fuseᶜ (proj₁ kIs) eOL subatL₂))
                   (cong (subst (_⊢C⦂ CT) eOL) (sym (proj₂ kIs))))))

    oO : outerᶜ Θ' X V₂ᴱ V₁ᴱ ≡ subst (_⊢C⦂ CT) eOL' subatL₁
    oO =
      sub-at-≡ eΓL₁ eΘL₁ (subst (_⊢C⦂ CT) eL₁ (K op ε)) Oᴵ eOL termO
               VL₁ V₁ᴱ valL₁ eOL'

    lIs : IsSub subatL₁ (outerᴴ′ (yes et₁) (yes et₂) Θ H W₂ W₁ op ε)
    lIs =
      isSub-Cl op ε _ (castOf {Γ} {B₁} Θ)
        (cl-yes et₁ xL₁ (bval Θ W₁) K op ε eL₁)

    eLfin : (Γ ᴱ ++ᶜ Θ') ≡ (((Γ ++ᶜ Θ) ᴱ) ++ᶜ Dc)
    eLfin = trans (sym eOL') (proj₁ lIs)

    ee-left : outerᴴ′ (yes et₁) (yes et₂) Θ H W₂ W₁ op ε
            ≡ subst (_⊢C⦂ CT) eLfin (outerᶜ Θ' X V₂ᴱ V₁ᴱ)
    ee-left =
      trans ((proj₂ lIs))
        (sym
          (trans (substᶜ-≡ eLfin oO)
            ((trans (subst-fuseᶜ eOL' eLfin subatL₁)
                         (cong (λ z → subst (_⊢C⦂ CT) z subatL₁) uip)))))

    ----------------------------------------------------------------
    -- the right order
    ----------------------------------------------------------------

    xR₂ = bvar {Γ} B₂ Θ
    xR₁ = bvar {Γ} B₁ (Δ₂ ++ᶜ Θ)

    H' : Fam D (((Γ ∷ B₁) ++ᶜ (Δ₂ ++ᶜ Θ)) ᴱ)
    H' op' ε' = Cl-cast op' ε' (assocᴮ Γ B₁ B₂ Θ) (H op' ε')

    G : Fam D (((Γ ∷ B₂) ++ᶜ Θ) ᴱ)
    G = inner₀ᴴ′ (yes et₁) Θ H W₁

    eR₁ = eCl et₁ xR₁ D op ε
    eR₂ = eCl et₂ xR₂ D op ε

    VR₁ = eternal-val-restrict et₁ (bval {Γ} (Δ₂ ++ᶜ Θ) W₁)
    VR₂ = eternal-val-restrict et₂ (bval {Γ} Θ W₂)

    subatR₁ = sub-atᶜ {split-l xR₁ ᴱ} {B₁} (split-r xR₁ ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eR₁ (H' op ε)) VR₁
    subatR₂ = sub-atᶜ {split-l xR₂ ᴱ} {B₂} (split-r xR₂ ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eR₂ (G op ε)) VR₂

    cR₁ : Γ ≡ split-l xR₁
    cR₁ = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ}))

    cR₂ : Γ ≡ split-l xR₂
    cR₂ = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₂} {Θ}))

    eΓR₁ : split-l xR₁ ᴱ ≡ Γ ᴱ
    eΓR₁ = cong _ᴱ (sym cR₁)

    eΓR₂ : split-l xR₂ ᴱ ≡ Γ ᴱ
    eΓR₂ = cong _ᴱ (sym cR₂)

    -- at an eternal `B₂` the extra entry survives the restriction, and
    -- one `++ᶜ-assoc` turns it into `inner₀ᶜ`'s own bracketing
    eΘR₁ : (split-r xR₁ ᴱ ++ᶜ Dc) ≡ (Δ₂ ++ᶜ Θ')
    eΘR₁ =
      trans (cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                  (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ})))
        (trans (cong (_++ᶜ Dc)
                 (trans (ᴱ-++ᶜ Δ₂ Θ)
                        (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-keep {[]} {B₂} et₂))))
               (++ᶜ-assoc Δ₂ (Θ ᴱ) Dc))

    eΘR₂ : (split-r xR₂ ᴱ ++ᶜ Dc) ≡ Θ'
    eΘR₂ = cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₂} {Θ}))

    valR₁ : subst (_⊢V⦂ B₁) eΓR₁ VR₁ ≡ V₁ᴱ
    valR₁ =
              (trans (cong (subst (_⊢V⦂ B₁) eΓR₁)
                 (trans (cong (eternal-val-restrict et₁) (castᵛ≡subst cR₁ W₁))
                        (restrict-substᵛ cR₁ et₁ W₁)))
          (trans (subst-fuseᵛ (cong _ᴱ cR₁) eΓR₁ V₁ᴱ)
                 (substᵛ-irr _ refl V₁ᴱ)))

    valR₂ : subst (_⊢V⦂ B₂) eΓR₂ VR₂ ≡ V₂ᴱ
    valR₂ =
              (trans (cong (subst (_⊢V⦂ B₂) eΓR₂)
                 (trans (cong (eternal-val-restrict et₂) (castᵛ≡subst cR₂ W₂))
                        (restrict-substᵛ cR₂ et₂ W₂)))
          (trans (subst-fuseᵛ (cong _ᴱ cR₂) eΓR₂ V₂ᴱ)
                 (substᵛ-irr _ refl V₂ᴱ)))

    Iᴵ = sub-atᶜ {Γ ᴱ} {B₁} (Δ₂ ++ᶜ Θ')
                 (castᶜ (assocᴮ (Γ ᴱ) B₁ B₂ Θ') X) V₁ᴱ

    eIR : ((split-l xR₁ ᴱ ∷ B₁) ++ᶜ (split-r xR₁ ᴱ ++ᶜ Dc))
        ≡ ((Γ ᴱ ∷ B₁) ++ᶜ (Δ₂ ++ᶜ Θ'))
    eIR = cong₂ (λ Γ₀ Θ₀ → (Γ₀ ∷ B₁) ++ᶜ Θ₀) eΓR₁ eΘR₁

    eIR' : (split-l xR₁ ᴱ ++ᶜ (split-r xR₁ ᴱ ++ᶜ Dc)) ≡ (Γ ᴱ ++ᶜ (Δ₂ ++ᶜ Θ'))
    eIR' = cong₂ _++ᶜ_ eΓR₁ eΘR₁

    iI : Iᴵ ≡ subst (_⊢C⦂ CT) eIR' subatR₁
    iI =
      sub-at-≡ eΓR₁ eΘR₁ (subst (_⊢C⦂ CT) eR₁ (H' op ε))
               (castᶜ (assocᴮ (Γ ᴱ) B₁ B₂ Θ') X) eIR
        (          (trans (castᶜ≡subst (assocᴮ (Γ ᴱ) B₁ B₂ Θ') X)
            (trans (subst-fuseᶜ eXfull (assocᴮ (Γ ᴱ) B₁ B₂ Θ') (H op ε))
              (trans (cong (λ z → subst (_⊢C⦂ CT) z (H op ε))
                           (uip {q = trans (cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                                                 (assocᴮ Γ B₁ B₂ Θ))
                                           (trans eR₁ eIR)}))
                (trans (sym (subst-fuseᶜ (cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                                               (assocᴮ Γ B₁ B₂ Θ))
                                         (trans eR₁ eIR) (H op ε)))
                  (trans (cong (subst (_⊢C⦂ CT) (trans eR₁ eIR))
                               (sym (castᶜ≡subst _ (H op ε))))
                         (sym (subst-fuseᶜ eR₁ eIR (H' op ε)))))))))
        VR₁ V₁ᴱ valR₁ eIR'

    gIs : IsSub subatR₁ (subst (_⊢C⦂ CT) eR₂ (G op ε))
    gIs =
      isSub-substC _ eR₂
        (isSub-Cl op ε _ (assocᴮ⁻ Γ B₂ Θ)
          (isSub-Cl op ε _ (castOf {Γ} {B₁} (Δ₂ ++ᶜ Θ))
            (cl-yes et₁ xR₁ (bval (Δ₂ ++ᶜ Θ) W₁) H' op ε eR₁)))

    eOR : ((split-l xR₂ ᴱ ∷ B₂) ++ᶜ (split-r xR₂ ᴱ ++ᶜ Dc))
        ≡ ((Γ ᴱ ∷ B₂) ++ᶜ Θ')
    eOR = cong₂ (λ Γ₀ Θ₀ → (Γ₀ ∷ B₂) ++ᶜ Θ₀) eΓR₂ eΘR₂

    eOR' : (split-l xR₂ ᴱ ++ᶜ (split-r xR₂ ᴱ ++ᶜ Dc)) ≡ (Γ ᴱ ++ᶜ Θ')
    eOR' = cong₂ _++ᶜ_ eΓR₂ eΘR₂

    termOR : castᶜ (assocᴮ⁻ (Γ ᴱ) B₂ Θ') Iᴵ
           ≡ subst (_⊢C⦂ CT) eOR (subst (_⊢C⦂ CT) eR₂ (G op ε))
    termOR =
      trans ((castᶜ≡subst (assocᴮ⁻ (Γ ᴱ) B₂ Θ') Iᴵ))
        (trans (substᶜ-≡ (assocᴮ⁻ (Γ ᴱ) B₂ Θ') iI)
          (            (trans (subst-fuseᶜ eIR' (assocᴮ⁻ (Γ ᴱ) B₂ Θ') subatR₁)
              (trans (cong (λ z → subst (_⊢C⦂ CT) z subatR₁)
                           (uip {q = trans (proj₁ gIs) eOR}))
                (trans (sym (subst-fuseᶜ (proj₁ gIs) eOR subatR₁))
                       (cong (subst (_⊢C⦂ CT) eOR) (sym (proj₂ gIs))))))))

    iO : innerᶜ Θ' X V₂ᴱ V₁ᴱ ≡ subst (_⊢C⦂ CT) eOR' subatR₂
    iO =
      sub-at-≡ eΓR₂ eΘR₂ (subst (_⊢C⦂ CT) eR₂ (G op ε))
               (castᶜ (assocᴮ⁻ (Γ ᴱ) B₂ Θ') Iᴵ) eOR termOR
               VR₂ V₂ᴱ valR₂ eOR'

    rIs : IsSub subatR₂ (innerᴴ′ (yes et₁) (yes et₂) Θ H W₂ W₁ op ε)
    rIs =
      isSub-Cl op ε _ (castOf {Γ} {B₂} Θ)
        (cl-yes et₂ xR₂ (bval Θ W₂) G op ε eR₂)

    eRfin : (Γ ᴱ ++ᶜ Θ') ≡ (((Γ ++ᶜ Θ) ᴱ) ++ᶜ Dc)
    eRfin = trans (sym eOR') (proj₁ rIs)

    ee-right : innerᴴ′ (yes et₁) (yes et₂) Θ H W₂ W₁ op ε
             ≡ subst (_⊢C⦂ CT) eRfin (innerᶜ Θ' X V₂ᴱ V₁ᴱ)
    ee-right =
      trans ((proj₂ rIs))
        (sym
          (trans (substᶜ-≡ eRfin iO)
            ((trans (subst-fuseᶜ eOR' eRfin subatR₂)
                         (cong (λ z → subst (_⊢C⦂ CT) z subatR₂) uip)))))

-- The dispatch. `sub-atᴴ` *is* `sub-atᴴ′ (eternal? B)`, so instantiating
-- the two decisions recovers the statement on the nose.

sub-swap-clause : ∀ {Γ B₁ B₂ D} → (Θ : Ctx)
                → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
                → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
                → (op : Op) → (ε : E)
                → outerᴴ Θ H W₂ W₁ op ε ≡ innerᴴ Θ H W₂ W₁ op ε

sub-swap-clause {Γ} {B₁} {B₂} Θ H W₂ W₁ op ε =
  go (eternal? B₁) (eternal? B₂)
  where
    go : (dec₁ : Dec (Eternal B₁)) → (dec₂ : Dec (Eternal B₂))
       → ClSwap dec₁ dec₂ Θ H W₂ W₁ op ε
    go (no ¬et₁)  (no ¬et₂)  = cl-swap-nn ¬et₁ ¬et₂ Θ H W₂ W₁ op ε
    go (yes et₁)  (no ¬et₂)  = cl-swap-en et₁  ¬et₂ Θ H W₂ W₁ op ε
    go (no ¬et₁)  (yes et₂)  = cl-swap-ne ¬et₁ et₂  Θ H W₂ W₁ op ε
    go (yes et₁)  (yes et₂)  = cl-swap-ee et₁  et₂  Θ H W₂ W₁ op ε

sub-swap-handle : ∀ {Γ B₁ B₂ A D ε ε'} → (Θ : Ctx)
                → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
                → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
                → (N : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ D ‼ ε')
                → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
                → SubSwapC Θ M W₂ W₁
                → SubSwapC (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₂ W₁
                → SubSwapC Θ (handle M `with H `in N) W₂ W₁

sub-swap-handle {Γ} {B₁} {B₂} {A} {ε = ε} Θ M H N W₂ W₁ ihM ihN =
  trans
    ((trans (cong (λ z → sub-atᶜ Θ z W₁)
                       (sub-at-handle Θ M H N Ŵ₂))
                 (sub-at-handle Θ (sub-atᶜ Θ M Ŵ₂) (sub-atᴴ Θ H Ŵ₂)
                                (sub-atᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N Ŵ₂) W₁)))
    (trans
      (handle-≡ ihM (λ op ε'' → sub-swap-clause Θ H W₂ W₁ op ε'') ihN)
      ((sym (trans (cong (λ z → sub-atᶜ Θ z W₂)
                              (inner₀-handle Θ M H N W₁))
                        (sub-at-handle Θ (inner₀ᶜ Θ M W₁) (inner₀ᴴ Θ H W₁)
                                       (inner₀ᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₁)
                                       W₂)))))
  where
    Ŵ₂ = V-rename (wk-ren {A = B₁}) W₂


sub-swap-V : ∀ {Γ B₁ B₂ A} → (Θ : Ctx) → (U : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A)
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
           → SubSwapV Θ U W₂ W₁

sub-swap-C : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C)
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
           → SubSwapC Θ M W₂ W₁

sub-swap-V Θ (var f y) W₂ W₁ = sub-swap-var Θ y f W₂ W₁

sub-swap-V {Γ} {B₁} {B₂} Θ (const c) W₂ W₁ =
  trans ((trans (cong (λ z → sub-atᵛ Θ z W₁) (sub-at-const Θ (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-const Θ W₁)))
           ((sym (trans (cong (λ z → sub-atᵛ Θ z W₂)
                                   (inner₀-const Θ W₁))
                             (sub-at-const Θ W₂))))

sub-swap-V {Γ} {B₁} {B₂} Θ ⋆ W₂ W₁ =
  trans ((trans (cong (λ z → sub-atᵛ Θ z W₁) (sub-at-⋆ Θ (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-⋆ Θ W₁)))
           ((sym (trans (cong (λ z → sub-atᵛ Θ z W₂) (inner₀-⋆ Θ W₁))
                             (sub-at-⋆ Θ W₂))))

sub-swap-V {Γ} {B₁} {B₂} Θ ⦉ V₁ , V₂ ⦊ W₂ W₁ =
  trans ((trans (cong (λ z → sub-atᵛ Θ z W₁) (sub-at-pair Θ V₁ V₂ (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-pair Θ (sub-atᵛ Θ V₁ (V-rename (wk-ren {A = B₁}) W₂))
                                       (sub-atᵛ Θ V₂ (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (trans (cong₂ ⦉_,_⦊ (sub-swap-V Θ V₁ W₂ W₁) (sub-swap-V Θ V₂ W₂ W₁))
      ((sym (trans (cong (λ z → sub-atᵛ Θ z W₂)
                              (inner₀-pair Θ V₁ V₂ W₁))
                        (sub-at-pair Θ (inner₀ᵛ Θ V₁ W₁)
                                       (inner₀ᵛ Θ V₂ W₁) W₂)))))

sub-swap-V {Γ} {B₁} {B₂} {A ⇒ C} Θ (lam N) W₂ W₁ =
  trans ((trans (cong (λ z → sub-atᵛ Θ z W₁) (sub-at-lam Θ N (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-lam Θ (sub-atᶜ (Θ ∷ A) N (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (trans (cong lam (sub-swap-C (Θ ∷ A) N W₂ W₁))
      ((sym (trans (cong (λ z → sub-atᵛ Θ z W₂) (inner₀-lam Θ N W₁))
                        (sub-at-lam Θ (inner₀ᶜ (Θ ∷ A) N W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (return V) W₂ W₁ =
  trans ((trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-ret Θ V (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-ret Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (trans (cong return (sub-swap-V Θ V W₂ W₁))
      ((sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-ret Θ V W₁))
                        (sub-at-ret Θ (inner₀ᵛ Θ V W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (_⨟_ {A = A} {ε = ε} M N) W₂ W₁ =
  trans ((trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-seq Θ M N (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-seq Θ (sub-atᶜ Θ M (V-rename (wk-ren {A = B₁}) W₂))
                                      (sub-atᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (trans (cong₂ _⨟_ (sub-swap-C Θ M W₂ W₁)
                     (sub-swap-C (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₂ W₁))
      ((sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-seq Θ M N W₁))
                        (sub-at-seq Θ (inner₀ᶜ Θ M W₁)
                                      (inner₀ᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (V · U) W₂ W₁ =
  trans ((trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-app Θ V U (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-app Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂))
                                      (sub-atᵛ Θ U (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (trans (cong₂ _·_ (sub-swap-V Θ V W₂ W₁) (sub-swap-V Θ U W₂ W₁))
      ((sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-app Θ V U W₁))
                        (sub-at-app Θ (inner₀ᵛ Θ V W₁)
                                      (inner₀ᵛ Θ U W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (match_`in_ {A = A₁} {B = A₂} V N) W₂ W₁ =
  trans ((trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-match Θ V N (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-match Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂))
                                        (sub-atᶜ (Θ ∷ A₁ ∷ A₂) N (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (trans (cong₂ match_`in_ (sub-swap-V Θ V W₂ W₁)
                       (sub-swap-C (Θ ∷ A₁ ∷ A₂) N W₂ W₁))
      ((sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-match Θ V N W₁))
                        (sub-at-match Θ (inner₀ᵛ Θ V W₁)
                                        (inner₀ᶜ (Θ ∷ A₁ ∷ A₂) N W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (absurd V) W₂ W₁ =
  trans ((trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-absurd Θ V (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-absurd Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (trans (cong absurd (sub-swap-V Θ V W₂ W₁))
      ((sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-absurd Θ V W₁))
                        (sub-at-absurd Θ (inner₀ᵛ Θ V W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (perform op V N) W₂ W₁ =
  trans ((trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-perform Θ V N (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-perform Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂))
                           (sub-atᶜ (Θ ⟨ mapᵉ (op-grade op) ⟩
                                       ∷ type-of-gtype (arity op)) N (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (trans (cong₂ (perform _) (sub-swap-V Θ V W₂ W₁)
                         (sub-swap-C (Θ ⟨ mapᵉ (op-grade op) ⟩
                                        ∷ type-of-gtype (arity op)) N W₂ W₁))
      ((sym (trans (cong (λ z → sub-atᶜ Θ z W₂)
                              (inner₀-perform Θ V N W₁))
                        (sub-at-perform Θ (inner₀ᵛ Θ V W₁)
                           (inner₀ᶜ (Θ ⟨ mapᵉ (op-grade op) ⟩
                                       ∷ type-of-gtype (arity op)) N W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (delay τ M) W₂ W₁ =
  trans ((trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-delay Θ M (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-delay Θ (sub-atᶜ (Θ ⟨ of-natʳ τ ⟩) M (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (trans (cong (delay _) (sub-swap-C (Θ ⟨ of-natʳ τ ⟩) M W₂ W₁))
      ((sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-delay Θ M W₁))
                        (sub-at-delay Θ (inner₀ᶜ (Θ ⟨ of-natʳ τ ⟩) M W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (box {A = A} {ρ = ρ} V M) W₂ W₁ =
  trans ((trans (cong (λ z → sub-atᶜ Θ z W₁)
                              (sub-at-box Θ V M (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-box Θ
                           (sub-atᵛ (Θ ⟨ ρ ⟩) V (V-rename (wk-ren {A = B₁}) W₂))
                           (sub-atᶜ (Θ ∷ [ ρ ] A) M
                                    (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (trans (cong₂ box (sub-swap-V (Θ ⟨ ρ ⟩) V W₂ W₁)
                     (sub-swap-C (Θ ∷ [ ρ ] A) M W₂ W₁))
      ((sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-box Θ V M W₁))
                        (sub-at-box Θ (inner₀ᵛ (Θ ⟨ ρ ⟩) V W₁)
                                      (inner₀ᶜ (Θ ∷ [ ρ ] A) M W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (coerce p M) W₂ W₁ =
  trans ((trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-coerce Θ M (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-coerce Θ (sub-atᶜ Θ M (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (trans (coerce-≡ (sub-swap-C Θ M W₂ W₁))
      ((sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-coerce Θ M W₁))
                        (sub-at-coerce Θ (inner₀ᶜ Θ M W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (handle_`with_`in {A = A} {ε = ε} M H N) W₂ W₁ =
  sub-swap-handle Θ M H N W₂ W₁
    (sub-swap-C Θ M W₂ W₁) (sub-swap-C (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₂ W₁)

sub-swap-C {Γ} {B₁} {B₂} Θ (unbox {A = A} w V M) W₂ W₁ =
  sub-swap-unbox Θ w V M W₂ W₁ (sub-swap-C (Θ ∷ A) M W₂ W₁)

sub-swap-C-cast Θ refl M W₂ W₁ = sub-swap-C Θ M W₂ W₁

