------------------------------------------------------------------------
-- Restriction, conjugated decompositions, and the clause renamings.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality
module Syntax.Substitutions.Renaming.Clauses (Spec : LanguageSpec) where
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
open import Syntax.Substitutions.Renaming.Variables Spec

-- RESTRICTING A SUFFIX-EXTENDED RENAMING
--
-- Restricting a binder extension: at an eternal binder the restriction
-- keeps it, at a non-eternal one it drops it — in both cases conjugated
-- by `eq-ren`s at the (only propositional) context equalities.
------------------------------------------------------------------------

restrict-∷-et-≐ʳ : ∀ {Γ Γ' B} → (r : Ren [] Γ' Γ) → (et : Eternal B)
                → (e₁ : (Γ ∷ B) ᴱ ≡ Γ ᴱ ∷ B)
                → (e₂ : (Γ' ∷ B) ᴱ ≡ Γ' ᴱ ∷ B)
                → restrict-ren {Ξ = []} (cong-∷-ren {A = B} r)
                ≐ʳ (eq-ren e₁
                    ∘ʳ cong-∷-ren {A = B} (restrict-ren r) ∘ʳ eq-ren (sym e₂))

restrict-∷-et-≐ʳ r et e₁ e₂
  rewrite eternal?-yes et
        | uip {p = e₁} {q = refl} | uip {p = e₂} {q = refl} =
  ≐ʳ-sym (≐ʳ-trans (∘ʳ-identityˡ-≐ʳ _) (∘ʳ-identityʳ-≐ʳ _))

restrict-∷-ne-≐ʳ : ∀ {Γ Γ' B} → (r : Ren [] Γ' Γ) → (¬et : ¬ Eternal B)
                → (e₁ : (Γ ∷ B) ᴱ ≡ Γ ᴱ)
                → (e₂ : (Γ' ∷ B) ᴱ ≡ Γ' ᴱ)
                → restrict-ren {Ξ = []} (cong-∷-ren {A = B} r)
                ≐ʳ (eq-ren e₁ ∘ʳ restrict-ren r ∘ʳ eq-ren (sym e₂))

restrict-∷-ne-≐ʳ r ¬et e₁ e₂
  rewrite eternal?-no ¬et
        | uip {p = e₁} {q = refl} | uip {p = e₂} {q = refl} =
  ≐ʳ-sym (≐ʳ-trans (∘ʳ-identityˡ-≐ʳ _) (∘ʳ-identityʳ-≐ʳ _))

------------------------------------------------------------------------
-- SPLITTING UNIQUENESS ACROSS TRANSPORTED HALVES
--
-- `split→∈-unique` requires the two splittings' halves to agree on the
-- nose; here they agree only propositionally, so the halves' equations
-- are matched first and the grade transport rides along.
------------------------------------------------------------------------

split→∈-unique₂ : ∀ {Γ Γ' Γ₁ Γ₁' Γ₂ Γ₂' A}
                → (eΓ₁ : Γ₁ ≡ Γ₁') → (eΓ₂ : Γ₂ ≡ Γ₂') → (e : Γ ≡ Γ')
                → (s : Γ₁ ∷ A , Γ₂ split Γ) → (s' : Γ₁' ∷ A , Γ₂' split Γ')
                → subst (λ Γ₀ → A ∈[ ctx-grade Γ₂' ] Γ₀) e
                    (subst (λ ρ₀ → A ∈[ ρ₀ ] Γ) (cong ctx-grade eΓ₂)
                           (split→∈ s))
                ≡ split→∈ s'
split→∈-unique₂ refl refl e s s' = split→∈-unique e s s'

-- The two halves' equations induced by a grade-and-context transport of
-- the substituted variable.

sl-eq : ∀ {Γ Γ' A ρ ρ'} → (eρ : ρ ≡ ρ') → (e : Γ ≡ Γ')
      → (x : A ∈[ ρ ] Γ) → (y : A ∈[ ρ' ] Γ')
      → subst (λ Γ₀ → A ∈[ ρ' ] Γ₀) e (subst (λ ρ₀ → A ∈[ ρ₀ ] Γ) eρ x) ≡ y
      → split-l x ≡ split-l y
sl-eq refl e x y ey = trans (split-l-cast e x) (cong split-l ey)

sr-eq : ∀ {Γ Γ' A ρ ρ'} → (eρ : ρ ≡ ρ') → (e : Γ ≡ Γ')
      → (x : A ∈[ ρ ] Γ) → (y : A ∈[ ρ' ] Γ')
      → subst (λ Γ₀ → A ∈[ ρ' ] Γ₀) e (subst (λ ρ₀ → A ∈[ ρ₀ ] Γ) eρ x) ≡ y
      → split-r x ≡ split-r y
sr-eq refl e x y ey = trans (split-r-cast e x) (cong split-r ey)

-- `sub-cast-C′` with the substituted variable's grade transported too.

sub-cast-C″ : ∀ {Γ Γ' A C ρ ρ'} → (eρ : ρ ≡ ρ') → (e : Γ ≡ Γ')
            → (M : Γ ⊢C⦂ C)
            → (x : A ∈[ ρ ] Γ) → (y : A ∈[ ρ' ] Γ')
            → (ey : subst (λ Γ₀ → A ∈[ ρ' ] Γ₀) e
                          (subst (λ ρ₀ → A ∈[ ρ₀ ] Γ) eρ x) ≡ y)
            → (U : split-l x ⊢V⦂ A) → (U' : split-l y ⊢V⦂ A)
            → (eU : subst (_⊢V⦂ A) (sl-eq eρ e x y ey) U ≡ U')
            → (subst (_⊢C⦂ C) e M) [ y ↦ U' ]c
            ≡ subst (_⊢C⦂ C) (cong₂ _++ᶜ_ (sl-eq eρ e x y ey)
                                          (sr-eq eρ e x y ey))
                (M [ x ↦ U ]c)
sub-cast-C″ refl e M x y ey U U' eU = sub-cast-C′ e M x y ey U U' eU

------------------------------------------------------------------------
-- THE ETERNAL RESTRICTION IS NATURAL IN RENAMING
--
-- The var case goes through the reflection `∈-ᴱ⁻`: both sides' targets
-- reflect to `var-img r x`, so `∈-ᴱ⁻-inj` identifies them.
------------------------------------------------------------------------

eternal-val-restrict-ren : ∀ {Γ Γ' A} → (et : Eternal A)
                         → (r : Ren [] Γ' Γ) → (W : Γ ⊢V⦂ A)
                         → eternal-val-restrict et (V-rename r W)
                         ≡ V-rename (restrict-ren r) (eternal-val-restrict et W)

eternal-val-restrict-ren {Γ} {Γ'} et r (var f x) =
  trans
    (eternal-val-restrict-cong et (var-ren-≡ r x f fet))
    (sym (var-ren-img-≡ (restrict-ren r) (∈-ᴱ et x) fet
                           (sym tgt-eq) fet))
  where
    fet : ∀ {ρ₀} → ¬ Eternal _ → ρ₀ ≾ᵣ uᵣ
    fet ¬et = ⊥-elim (¬et et)

    tgt-eq : _≡_ {A = Var (Γ' ᴱ) _}
                 (uᵣ , ∈-ᴱ et (proj₂ (var-img r x)))
                 (var-img (restrict-ren r) (∈-ᴱ et x))
    tgt-eq =
      ∈-ᴱ⁻-inj Γ' _ _
        (trans (∈-ᴱ⁻-∈-ᴱ Γ' et (proj₂ (var-img r x)))
          (sym (trans (restrict-img⁻ r (∈-ᴱ et x))
                      (cong (var-img′ r) (∈-ᴱ⁻-∈-ᴱ Γ et x)))))

eternal-val-restrict-ren et r (const c) = refl
eternal-val-restrict-ren et r ⋆         = refl
eternal-val-restrict-ren (et₁ |×|ₑ et₂) r ⦉ V₁ , V₂ ⦊ =
  cong₂ ⦉_,_⦊ (eternal-val-restrict-ren et₁ r V₁)
         (eternal-val-restrict-ren et₂ r V₂)

------------------------------------------------------------------------
-- THE `ren-sub` STATEMENT, ABBREVIATED
------------------------------------------------------------------------

RenSubC : ∀ {Γ Γ' B C} → Ren [] Γ' Γ → (Θ : Ctx)
        → ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ C → Γ ⊢V⦂ B → Set
RenSubC {Γ} {Γ'} {B} r Θ M W =
  C-rename (cong-ren {Γ'' = Θ} r)
      (castᶜ (castOf {Γ} {B} Θ)
        (M [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
             ↦ castᵛ (sym (split→∈-split-l
                             (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]c))
  ≡ castᶜ (castOf {Γ'} {B} Θ)
       ((C-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) M)
          [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
            ↦ castᵛ (sym (split→∈-split-l
                            (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                    (V-rename r W) ]c)

-- A clause's two binders, as a suffix.

Dcl : VType → Op → E → Ctx
Dcl D op ε'' =
  [] ∷ type-of-gtype (param op)
     ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ D ‼ ε'')

-- The clause context, relocated to the recursion's canonical contexts.

ren-sub-eTot : ∀ {Γ B} → (Θ : Ctx) → Eternal B → (Δ : Ctx)
             → ((Γ ∷ B) ++ᶜ Θ) ᴱ ++ᶜ Δ ≡ (Γ ᴱ ∷ B) ++ᶜ (Θ ᴱ ++ᶜ Δ)
ren-sub-eTot {Γ} {B} Θ et Δ =
  trans (cong (_++ᶜ Δ)
              (trans (ᴱ-++ᶜ (Γ ∷ B) Θ)
                     (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-keep {Γ} {B} et))))
        (++ᶜ-assoc (Γ ᴱ ∷ B) (Θ ᴱ) Δ)

------------------------------------------------------------------------
-- CONJUGATED DECOMPOSITIONS
--
-- Every renaming this proof decomposes comes out as an `eq-ren`-conjugated
-- core; the two helpers below fuse nested conjugations and turn a
-- conjugation into transports around the core's action.
------------------------------------------------------------------------

infix 4 _≐ʳconj⟨_,_,_⟩

_≐ʳconj⟨_,_,_⟩ : ∀ {Γ₁ Γ₁' Γ₂ Γ₂'} → Ren [] Γ₂' Γ₁
              → (Γ₁ ≡ Γ₁') → Ren [] Γ₂ Γ₁' → (Γ₂ ≡ Γ₂') → Set
R ≐ʳconj⟨ e , K , e' ⟩ = R ≐ʳ (eq-ren e ∘ʳ K ∘ʳ eq-ren e')

-- Fusing a conjugation of a conjugation.

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

-- Extending a conjugation by a suffix.

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

-- The action of a conjugated renaming is the core's action between the
-- two transports.

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
-- THE TWO CLAUSE RENAMINGS, DECOMPOSED
--
-- Both sides of `ren-sub-handle`'s clause comparison rename by
-- `cong-ren {D}` of a restriction of a suffix-extended renaming; both
-- decompose onto the same core over the canonical restricted contexts.
------------------------------------------------------------------------

-- The left side: `restrict-ren (cong-ren {Θ} r)`, extended by the two
-- clause binders.

clause-ren-l-≐ʳ : ∀ {Γ Γ'} → (r : Ren [] Γ' Γ) → (Θ Δ : Ctx)
               → cong-ren {Γ'' = Δ}
                   (restrict-ren {Ξ = []} (cong-ren {Γ'' = Θ} r))
               ≐ʳconj⟨ trans (cong (_++ᶜ Δ) (ᴱ-++ᶜ Γ Θ))
                             (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) Δ)
                     , cong-ren {Γ'' = Θ ᴱ ++ᶜ Δ} (restrict-ren {Ξ = []} r)
                     , sym (trans (cong (_++ᶜ Δ) (ᴱ-++ᶜ Γ' Θ))
                                  (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) Δ)) ⟩
clause-ren-l-≐ʳ {Γ} {Γ'} r Θ Δ =
  ≐ʳ-trans
    (conj-cong-ren Δ (ᴱ-++ᶜ Γ Θ) (sym (ᴱ-++ᶜ Γ' Θ))
       (restrict-cong-≐ʳ r Θ (ᴱ-++ᶜ Γ Θ) (ᴱ-++ᶜ Γ' Θ)))
    (≐ʳ-trans
      (conj-fuse (cong (_++ᶜ Δ) (ᴱ-++ᶜ Γ Θ))
                 (cong (_++ᶜ Δ) (sym (ᴱ-++ᶜ Γ' Θ)))
                 (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) Δ)
                 (sym (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) Δ))
                 (cong-ren-assoc-≐ʳ (Θ ᴱ) Δ (restrict-ren {Ξ = []} r)))
      (∘ʳ-≐ʳ ≐ʳ-refl (∘ʳ-≐ʳ ≐ʳ-refl (eq-ren-≐ʳ _ _))))

-- The right side: `restrict-ren (cong-ren {Θ} (cong-∷-ren r))` at an
-- eternal substituted type — the restriction keeps the binder.

clause-ren-r-et-≐ʳ : ∀ {Γ Γ' B} → (r : Ren [] Γ' Γ) → (et : Eternal B)
                  → (Θ Δ : Ctx)
                  → cong-ren {Γ'' = Δ}
                      (restrict-ren {Ξ = []}
                        (cong-ren {Γ'' = Θ} (cong-∷-ren {A = B} r)))
                  ≐ʳconj⟨ ren-sub-eTot {Γ} {B} Θ et Δ
                        , cong-ren {Γ'' = Θ ᴱ ++ᶜ Δ}
                            (cong-∷-ren {A = B} (restrict-ren {Ξ = []} r))
                        , sym (ren-sub-eTot {Γ'} {B} Θ et Δ) ⟩
clause-ren-r-et-≐ʳ {Γ} {Γ'} {B} r et Θ Δ =
  ≐ʳ-trans
    (conj-cong-ren Δ _ _
      (≐ʳ-trans
        (restrict-cong-≐ʳ (cong-∷-ren {A = B} r) Θ
           (ᴱ-++ᶜ (Γ ∷ B) Θ) (ᴱ-++ᶜ (Γ' ∷ B) Θ))
        (conj-fuse (ᴱ-++ᶜ (Γ ∷ B) Θ) (sym (ᴱ-++ᶜ (Γ' ∷ B) Θ))
           (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-keep {Γ} {B} et))
           (cong (_++ᶜ Θ ᴱ) (sym (ᴱ-∷-keep {Γ'} {B} et)))
           (conj-cong-ren (Θ ᴱ) (ᴱ-∷-keep {Γ} {B} et)
              (sym (ᴱ-∷-keep {Γ'} {B} et))
              (restrict-∷-et-≐ʳ r et (ᴱ-∷-keep {Γ} {B} et)
                                    (ᴱ-∷-keep {Γ'} {B} et))))))
    (≐ʳ-trans
      (conj-fuse _ _
         (++ᶜ-assoc (Γ ᴱ ∷ B) (Θ ᴱ) Δ)
         (sym (++ᶜ-assoc (Γ' ᴱ ∷ B) (Θ ᴱ) Δ))
         (cong-ren-assoc-≐ʳ (Θ ᴱ) Δ (cong-∷-ren {A = B} (restrict-ren {Ξ = []} r))))
      (∘ʳ-≐ʳ ≐ʳ-refl (∘ʳ-≐ʳ ≐ʳ-refl (eq-ren-≐ʳ _ _))))

-- The same at a non-eternal substituted type — the restriction drops it.

clause-ren-r-ne-≐ʳ : ∀ {Γ Γ' B} → (r : Ren [] Γ' Γ) → (¬et : ¬ Eternal B)
                  → (Θ Δ : Ctx)
                  → cong-ren {Γ'' = Δ}
                      (restrict-ren {Ξ = []}
                        (cong-ren {Γ'' = Θ} (cong-∷-ren {A = B} r)))
                  ≐ʳconj⟨ trans (cong (_++ᶜ Δ)
                                  (trans (ᴱ-++ᶜ (Γ ∷ B) Θ)
                                    (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-drop {Γ} {B} ¬et))))
                                (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) Δ)
                        , cong-ren {Γ'' = Θ ᴱ ++ᶜ Δ} (restrict-ren {Ξ = []} r)
                        , sym (trans (cong (_++ᶜ Δ)
                                       (trans (ᴱ-++ᶜ (Γ' ∷ B) Θ)
                                         (cong (_++ᶜ Θ ᴱ)
                                               (ᴱ-∷-drop {Γ'} {B} ¬et))))
                                     (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) Δ)) ⟩
clause-ren-r-ne-≐ʳ {Γ} {Γ'} {B} r ¬et Θ Δ =
  ≐ʳ-trans
    (conj-cong-ren Δ _ _
      (≐ʳ-trans
        (restrict-cong-≐ʳ (cong-∷-ren {A = B} r) Θ
           (ᴱ-++ᶜ (Γ ∷ B) Θ) (ᴱ-++ᶜ (Γ' ∷ B) Θ))
        (conj-fuse (ᴱ-++ᶜ (Γ ∷ B) Θ) (sym (ᴱ-++ᶜ (Γ' ∷ B) Θ))
           (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-drop {Γ} {B} ¬et))
           (cong (_++ᶜ Θ ᴱ) (sym (ᴱ-∷-drop {Γ'} {B} ¬et)))
           (conj-cong-ren (Θ ᴱ) (ᴱ-∷-drop {Γ} {B} ¬et)
              (sym (ᴱ-∷-drop {Γ'} {B} ¬et))
              (restrict-∷-ne-≐ʳ r ¬et (ᴱ-∷-drop {Γ} {B} ¬et)
                                     (ᴱ-∷-drop {Γ'} {B} ¬et))))))
    (≐ʳ-trans
      (conj-fuse _ _
         (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) Δ)
         (sym (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) Δ))
         (cong-ren-assoc-≐ʳ (Θ ᴱ) Δ (restrict-ren {Ξ = []} r)))
      (∘ʳ-≐ʳ ≐ʳ-refl (∘ʳ-≐ʳ ≐ʳ-refl (eq-ren-≐ʳ _ _))))

------------------------------------------------------------------------
-- `handle`, NON-ETERNAL
--
-- Both sides' clause components are the same core renaming
-- `cong-ren {Θ ᴱ ++ᶜ D₀} (restrict-ren r)` of the clause, inside
-- transport chains with the same endpoints, so after both are decomposed
-- (`clause-ren-l-≐ʳ`/`clause-ren-r-ne-≐ʳ`) `uip` closes the comparison.
------------------------------------------------------------------------

ren-sub-handle-ne : ∀ {Γ Γ' B A B' ε ε'} → (r : Ren [] Γ' Γ) → (Θ : Ctx)
                  → (¬et : ¬ Eternal B)
                  → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
                  → (H : (op : Op) → (ε'' : E) →
                           ((Γ ∷ B) ++ᶜ Θ) ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                           ⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                  → (N : ((Γ ∷ B) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B' ‼ ε')
                  → (W : Γ ⊢V⦂ B)
                  → (hM : RenSubC r Θ M W)
                  → (hN : RenSubC r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
                  → RenSubC r Θ (handle M `with H `in N) W

ren-sub-handle-ne {Γ} {Γ'} {B} {A} {B'} {ε} r Θ ¬et M H N W hM hN
  rewrite eternal?-no ¬et =
  trans ((cong (C-rename (cong-ren {Γ'' = Θ} r))
                       (cast-handle (castOf {Γ} {B} Θ))))
    (trans
      (handle-≡ hM (λ op ε'' → clause op ε'')
        (trans
          ((cong (C-rename (cong-ren {Γ'' = Θ ⟨ mapᵉ ε ⟩ ∷ A} r))
                      (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                       (castOf {Γ} {B} Θ))
                                 (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _)))
          (trans hN
            ((castᶜ-irr (castOf {Γ'} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A))
                             (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                   (castOf {Γ'} {B} Θ)) _)))))
      ((sym (cast-handle (castOf {Γ'} {B} Θ)))))
  where
    z₀  = split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
    z₀' = split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})

    clause : (op : Op) → (ε'' : E) → _
    clause op ε'' =
      trans
        (C-rename-conj eLL eLL' (clause-ren-l-≐ʳ r Θ D₀) _)
        (trans
          ((cong (λ z → subst (_⊢C⦂ CT) eLL' (C-rename K z)) inner-eq))
          (trans
            (uip²)
            (sym
              (trans (r1)
                (trans
                  (substᶜ-≡ TRout
                    (C-rename-conj eRR eRR'
                       (clause-ren-r-ne-≐ʳ r ¬et Θ D₀) (H op ε'')))
                  ((subst-fuseᶜ eRR' TRout _)))))))
      where
        D₀ = [] ∷ type-of-gtype (param op)
                ∷ [ mapᵉ (op-grade op) ]
                    (type-of-gtype (arity op) ⇒ B' ‼ ε'')

        CT = B' ‼ (op-grade op ·ₑ ε'')

        K = cong-ren {Γ'' = Θ ᴱ ++ᶜ D₀} (restrict-ren {Ξ = []} r)

        cDL = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε''))
                   (castOf {Γ} {B} Θ)

        cDR = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε''))
                   (castOf {Γ'} {B} Θ)

        eLL = trans (cong (_++ᶜ D₀) (ᴱ-++ᶜ Γ Θ)) (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) D₀)

        eLL' = sym (trans (cong (_++ᶜ D₀) (ᴱ-++ᶜ Γ' Θ))
                          (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) D₀))

        eRR = trans (cong (_++ᶜ D₀)
                          (trans (ᴱ-++ᶜ (Γ ∷ B) Θ)
                                 (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-drop {Γ} {B} ¬et))))
                    (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) D₀)

        eRR' = sym (trans (cong (_++ᶜ D₀)
                                (trans (ᴱ-++ᶜ (Γ' ∷ B) Θ)
                                       (cong (_++ᶜ Θ ᴱ)
                                             (ᴱ-∷-drop {Γ'} {B} ¬et))))
                          (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) D₀))

        dropL = ᴱ-drop-split ¬et z₀
        dropR = ᴱ-drop-split ¬et z₀'

        TL = trans (trans (cong (_++ᶜ D₀) dropL) cDL) eLL

        TRout = trans (cong (_++ᶜ D₀) dropR) cDR

        inner-eq : subst (_⊢C⦂ CT) eLL
                     (castᶜ cDL
                       (subst (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                                        ∷ [ mapᵉ (op-grade op) ]
                                            (type-of-gtype (arity op)
                                              ⇒ B' ‼ ε'')
                                      ⊢C⦂ CT)
                              dropL (H op ε'')))
                 ≡ subst (_⊢C⦂ CT) TL (H op ε'')
        inner-eq =
          trans (cong (subst (_⊢C⦂ CT) eLL)
                   (trans (cong (castᶜ cDL)
                                (subst-++ᶜʳ D₀ dropL (H op ε'')))
                     (trans (castᶜ≡subst cDL _)
                            (subst-fuseᶜ (cong (_++ᶜ D₀) dropL) cDL
                                         (H op ε'')))))
                (subst-fuseᶜ (trans (cong (_++ᶜ D₀) dropL) cDL) eLL (H op ε''))

        r1 : castᶜ cDR
               (subst (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                                ∷ [ mapᵉ (op-grade op) ]
                                    (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                              ⊢C⦂ CT)
                      dropR
                      (C-rename (cong-∷-ren (cong-∷-ren
                                  (restrict-ren {Ξ = []}
                                    (cong-ren {Γ'' = Θ} (cong-∷-ren r)))))
                                (H op ε'')))
           ≡ subst (_⊢C⦂ CT) TRout
               (C-rename (cong-∷-ren (cong-∷-ren
                           (restrict-ren {Ξ = []}
                             (cong-ren {Γ'' = Θ} (cong-∷-ren r)))))
                         (H op ε''))
        r1 =
          trans (cong (castᶜ cDR) (subst-++ᶜʳ D₀ dropR _))
            (trans (castᶜ≡subst cDR _)
                   (subst-fuseᶜ (cong (_++ᶜ D₀) dropR) cDR _))

        uip² : subst (_⊢C⦂ CT) eLL'
                 (C-rename K (subst (_⊢C⦂ CT) TL (H op ε'')))
             ≡ subst (_⊢C⦂ CT) (trans eRR' TRout)
                 (C-rename K (subst (_⊢C⦂ CT) eRR (H op ε'')))
        uip² =
          trans (cong (λ p → subst (_⊢C⦂ CT) eLL'
                               (C-rename K (subst (_⊢C⦂ CT) p (H op ε''))))
                      (uip {p = TL} {q = eRR}))
                (cong (λ p → subst (_⊢C⦂ CT) p
                               (C-rename K (subst (_⊢C⦂ CT) eRR (H op ε''))))
                      (uip {p = eLL'} {q = trans eRR' TRout}))

------------------------------------------------------------------------
-- `handle`, ETERNAL
--
-- The clause substitutes the restricted value, so the comparison is the
-- recursion (`hH`, `ren-sub-C` at the canonical restricted contexts) with
-- the goal's two substitutions carried over by `sub-cast-C″` — the
-- splittings' halves agree with the canonical ones only propositionally,
-- which `split→∈-unique₂` absorbs — and the value mismatch bridged by
-- `eternal-val-restrict-ren`.
------------------------------------------------------------------------

ren-sub-handle-et : ∀ {Γ Γ' B A B' ε ε'} → (r : Ren [] Γ' Γ) → (Θ : Ctx)
                  → (et : Eternal B)
                  → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
                  → (H : (op : Op) → (ε'' : E) →
                           ((Γ ∷ B) ++ᶜ Θ) ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                           ⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                  → (N : ((Γ ∷ B) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B' ‼ ε')
                  → (W : Γ ⊢V⦂ B)
                  → (hM : RenSubC r Θ M W)
                  → (hN : RenSubC r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
                  → (hH : (op : Op) → (ε'' : E)
                        → RenSubC {Γ ᴱ} {Γ' ᴱ} {B}
                            (restrict-ren {Ξ = []} r) (Θ ᴱ ++ᶜ Dcl B' op ε'')
                            (subst (_⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                                   (ren-sub-eTot {Γ} {B} Θ et (Dcl B' op ε''))
                                   (H op ε''))
                            (eternal-val-restrict et W))
                  → RenSubC r Θ (handle M `with H `in N) W

ren-sub-handle-et {Γ} {Γ'} {B} {A} {B'} {ε} r Θ et M H N W hM hN hH =
  trans ((cong (C-rename (cong-ren {Γ'' = Θ} r))
                       (cast-handle (castOf {Γ} {B} Θ))))
    (trans
      (handle-≡ hM (λ op ε'' → clause op ε'')
        (trans
          ((cong (C-rename (cong-ren {Γ'' = Θ ⟨ mapᵉ ε ⟩ ∷ A} r))
                      (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                       (castOf {Γ} {B} Θ))
                                 (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _)))
          (trans hN
            ((castᶜ-irr (castOf {Γ'} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A))
                             (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                   (castOf {Γ'} {B} Θ)) _)))))
      ((sym (cast-handle (castOf {Γ'} {B} Θ)))))
  where
    z₀  = split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
    z₀' = split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})

    cWL = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B} {Θ}))
    cWR = sym (split→∈-split-l (split-≡-++ᶜ {Γ' ∷ B} {Θ}))

    clause : (op : Op) → (ε'' : E) → _
    clause op ε'' =
      trans
        ((cong (λ d → C-rename
                             (cong-∷-ren (cong-∷-ren
                               (restrict-ren {Ξ = []}
                                 (cong-ren {Γ'' = Θ} r))))
                             (castᶜ cDL
                               (⟨ d ⟩[ z₀ ↦ castᵛ cWL W ]cl H op ε'')))
                    (eternal?-yes et)))
        (trans
          (C-rename-conj eLL eLL' (clause-ren-l-≐ʳ r Θ D₀) _)
          (trans
            ((cong (λ z → subst (_⊢C⦂ CT) eLL' (C-rename KL z))
                        inner-eq-L))
            (trans
              (substᶜ-≡ eLL' (hH op ε''))
              (trans (out-eq)
                (sym
                  (trans
                    ((cong (λ d → castᶜ cDR
                                         (⟨ d ⟩[ z₀'
                                               ↦ castᵛ cWR (V-rename r W)
                                               ]cl
                                            (λ op₁ ε₁ →
                                               C-rename
                                                 (cong-∷-ren (cong-∷-ren
                                                   (restrict-ren {Ξ = []}
                                                     (cong-ren {Γ'' = Θ}
                                                       (cong-∷-ren r)))))
                                                 (H op₁ ε₁))
                                            op ε''))
                                (eternal?-yes et)))
                    gr-chain))))))
      where
        D₀ = Dcl B' op ε''

        CT = B' ‼ (op-grade op ·ₑ ε'')

        Θ₀ = Θ ᴱ ++ᶜ D₀

        KL = cong-ren {Γ'' = Θ₀} (restrict-ren {Ξ = []} r)
        KR = cong-ren {Γ'' = Θ₀} (cong-∷-ren {A = B} (restrict-ren {Ξ = []} r))

        eT   = ren-sub-eTot {Γ} {B} Θ et D₀
        eTΓ' = ren-sub-eTot {Γ'} {B} Θ et D₀

        Ĥ  = H op ε''
        H⁺ = subst (_⊢C⦂ CT) eT Ĥ

        sL = split-++ʳ (∈-ᴱ-split et z₀) D₀
        sR = split-++ʳ (∈-ᴱ-split et z₀') D₀

        xL = split→∈ sL
        xR = split→∈ sR

        y₁ = split→∈ (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})
        y₂ = split→∈ (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})

        VL = subst (_⊢V⦂ B) (sym (split→∈-split-l sL))
                   (eternal-val-restrict et (castᵛ cWL W))
        VR = subst (_⊢V⦂ B) (sym (split→∈-split-l sR))
                   (eternal-val-restrict et (castᵛ cWR (V-rename r W)))

        U₁ = castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})))
                   (eternal-val-restrict et W)
        U₂ = castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})))
                   (V-rename (restrict-ren {Ξ = []} r)
                             (eternal-val-restrict et W))

        cDL = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε''))
                   (castOf {Γ} {B} Θ)

        cDR = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε''))
                   (castOf {Γ'} {B} Θ)

        eLL = trans (cong (_++ᶜ D₀) (ᴱ-++ᶜ Γ Θ)) (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) D₀)

        eLL' = sym (trans (cong (_++ᶜ D₀) (ᴱ-++ᶜ Γ' Θ))
                          (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) D₀))

        bigEL = trans (cong₂ _++ᶜ_ (split→∈-split-l sL) (split→∈-split-r sL))
                  (trans (sym (++ᶜ-assoc ((split-l z₀) ᴱ) ((split-r z₀) ᴱ) D₀))
                         (cong (_++ᶜ D₀)
                               (sym (ᴱ-++ᶜ (split-l z₀) (split-r z₀)))))

        bigER = trans (cong₂ _++ᶜ_ (split→∈-split-l sR) (split→∈-split-r sR))
                  (trans (sym (++ᶜ-assoc ((split-l z₀') ᴱ) ((split-r z₀') ᴱ) D₀))
                         (cong (_++ᶜ D₀)
                               (sym (ᴱ-++ᶜ (split-l z₀') (split-r z₀')))))

        -- the left substitution, carried to the canonical contexts

        eΓ₁L = cong _ᴱ (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B} {Θ}))
        eΓ₂L = cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D₀)
                    (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B} {Θ}))

        eρL = cong ctx-grade eΓ₂L

        eyL : subst (λ Γ₀ → B ∈[ ctx-grade Θ₀ ] Γ₀) eT
                (subst (λ ρ₀ → B ∈[ ρ₀ ] (((Γ ∷ B) ++ᶜ Θ) ᴱ ++ᶜ D₀)) eρL xL)
            ≡ y₁
        eyL = split→∈-unique₂ eΓ₁L eΓ₂L eT sL (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})

        slL = sl-eq eρL eT xL y₁ eyL

        eUL : subst (_⊢V⦂ B) slL VL ≡ U₁
        eUL =
          trans (cong (subst (_⊢V⦂ B) slL)
                  (trans (cong (subst (_⊢V⦂ B) (sym (split→∈-split-l sL)))
                               (trans (restrict-castᵛ cWL et W)
                                      (castᵛ≡subst (cong _ᴱ cWL)
                                        (eternal-val-restrict et W))))
                         (subst-fuseᵛ (cong _ᴱ cWL)
                                      (sym (split→∈-split-l sL))
                                      (eternal-val-restrict et W))))
            (trans (subst-fuseᵛ (trans (cong _ᴱ cWL)
                                       (sym (split→∈-split-l sL)))
                                slL (eternal-val-restrict et W))
              (trans (substᵛ-irr (trans (trans (cong _ᴱ cWL)
                                               (sym (split→∈-split-l sL)))
                                        slL)
                        (sym (split→∈-split-l (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})))
                        (eternal-val-restrict et W))
                     (sym (castᵛ≡subst
                             (sym (split→∈-split-l (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})))
                             (eternal-val-restrict et W)))))

        subCL : H⁺ [ y₁ ↦ U₁ ]c
              ≡ subst (_⊢C⦂ CT)
                  (cong₂ _++ᶜ_ slL (sr-eq eρL eT xL y₁ eyL))
                  (Ĥ [ xL ↦ VL ]c)
        subCL = sub-cast-C″ eρL eT Ĥ xL y₁ eyL VL U₁ eUL

        inner-eq-L : subst (_⊢C⦂ CT) eLL
                       (castᶜ cDL (subst (_⊢C⦂ CT) bigEL (Ĥ [ xL ↦ VL ]c)))
                   ≡ castᶜ (castOf {Γ ᴱ} {B} Θ₀) (H⁺ [ y₁ ↦ U₁ ]c)
        inner-eq-L =
          trans (cong (subst (_⊢C⦂ CT) eLL)
                  (trans (castᶜ≡subst cDL _)
                         (subst-fuseᶜ bigEL cDL _)))
            (trans (subst-fuseᶜ (trans bigEL cDL) eLL _)
              (trans (cong (λ p → subst (_⊢C⦂ CT) p (Ĥ [ xL ↦ VL ]c))
                           (uip {p = trans (trans bigEL cDL) eLL}
                                {q = trans (cong₂ _++ᶜ_ slL
                                             (sr-eq eρL eT xL y₁ eyL))
                                           (castOf {Γ ᴱ} {B} Θ₀)}))
                (sym (trans (castᶜ≡subst (castOf {Γ ᴱ} {B} Θ₀) _)
                       (trans (cong (subst (_⊢C⦂ CT) (castOf {Γ ᴱ} {B} Θ₀))
                                    subCL)
                              (subst-fuseᶜ (cong₂ _++ᶜ_ slL
                                             (sr-eq eρL eT xL y₁ eyL))
                                           (castOf {Γ ᴱ} {B} Θ₀) _))))))

        -- the right substitution, likewise

        eΓ₁R = cong _ᴱ (sym (split→∈-split-l (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
        eΓ₂R = cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D₀)
                    (sym (split→∈-split-r (split-≡-++ᶜ {Γ' ∷ B} {Θ})))

        eρR = cong ctx-grade eΓ₂R

        eyR : subst (λ Γ₀ → B ∈[ ctx-grade ((split-r z₀') ᴱ ++ᶜ D₀) ] Γ₀)
                    (sym eTΓ')
                (subst (λ ρ₀ → B ∈[ ρ₀ ] ((Γ' ᴱ ∷ B) ++ᶜ Θ₀)) eρR y₂)
            ≡ xR
        eyR = split→∈-unique₂ eΓ₁R eΓ₂R (sym eTΓ')
                              (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀}) sR

        slR = sl-eq eρR (sym eTΓ') y₂ xR eyR

        VR″ = subst (_⊢V⦂ B) slR U₂

        X₂ = (C-rename KR H⁺) [ y₂ ↦ U₂ ]c

        subCR : (subst (_⊢C⦂ CT) (sym eTΓ') (C-rename KR H⁺)) [ xR ↦ VR″ ]c
              ≡ subst (_⊢C⦂ CT)
                  (cong₂ _++ᶜ_ slR (sr-eq eρR (sym eTΓ') y₂ xR eyR))
                  X₂
        subCR = sub-cast-C″ eρR (sym eTΓ') (C-rename KR H⁺) y₂ xR eyR
                            U₂ VR″ refl

        eVR : VR ≡ VR″
        eVR =
          trans
            ((cong (subst (_⊢V⦂ B) (sym (split→∈-split-l sR)))
                        (restrict-castᵛ cWR et (V-rename r W))))
            (trans
              (substᵛ-≡ (sym (split→∈-split-l sR))
                 (castᵛ-≡ (cong _ᴱ cWR) (eternal-val-restrict-ren et r W)))
              (
                (trans (cong (subst (_⊢V⦂ B) (sym (split→∈-split-l sR)))
                             (castᵛ≡subst (cong _ᴱ cWR)
                               (V-rename (restrict-ren {Ξ = []} r)
                                         (eternal-val-restrict et W))))
                  (trans (subst-fuseᵛ (cong _ᴱ cWR)
                                      (sym (split→∈-split-l sR))
                                      (V-rename (restrict-ren {Ξ = []} r)
                                                (eternal-val-restrict et W)))
                    (trans (substᵛ-irr
                              (trans (cong _ᴱ cWR)
                                     (sym (split→∈-split-l sR)))
                              (trans (sym (split→∈-split-l
                                            (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})))
                                     slR)
                              (V-rename (restrict-ren {Ξ = []} r)
                                        (eternal-val-restrict et W)))
                      (sym (trans (cong (subst (_⊢V⦂ B) slR)
                                        (castᵛ≡subst
                                          (sym (split→∈-split-l
                                                 (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})))
                                          (V-rename (restrict-ren {Ξ = []} r)
                                                    (eternal-val-restrict et W))))
                                  (subst-fuseᵛ
                                    (sym (split→∈-split-l
                                           (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})))
                                    slR
                                    (V-rename (restrict-ren {Ξ = []} r)
                                              (eternal-val-restrict et W))))))))))

        TRfin = trans (trans (cong₂ _++ᶜ_ slR
                               (sr-eq eρR (sym eTΓ') y₂ xR eyR))
                             bigER)
                      cDR

        gr-chain : castᶜ cDR
                     (subst (_⊢C⦂ CT) bigER
                       ((C-rename (cong-∷-ren (cong-∷-ren
                                    (restrict-ren {Ξ = []}
                                      (cong-ren {Γ'' = Θ} (cong-∷-ren r)))))
                                  Ĥ)
                          [ xR ↦ VR ]c))
                 ≡ subst (_⊢C⦂ CT) TRfin X₂
        gr-chain =
          trans
            (castᶜ-≡ cDR (substᶜ-≡ bigER
              (sub-≡ᶜ xR eVR
                 (C-rename-conj eT (sym eTΓ')
                    (clause-ren-r-et-≐ʳ r et Θ D₀) Ĥ))))
            (trans
              ((cong (λ z → castᶜ cDR (subst (_⊢C⦂ CT) bigER z)) subCR))
              ((trans (cong (castᶜ cDR)
                              (subst-fuseᶜ (cong₂ _++ᶜ_ slR
                                             (sr-eq eρR (sym eTΓ') y₂ xR eyR))
                                           bigER X₂))
                       (trans (castᶜ≡subst cDR _)
                              (subst-fuseᶜ (trans (cong₂ _++ᶜ_ slR
                                                    (sr-eq eρR (sym eTΓ')
                                                           y₂ xR eyR))
                                                  bigER)
                                           cDR X₂)))))

        out-eq : subst (_⊢C⦂ CT) eLL'
                   (castᶜ (castOf {Γ' ᴱ} {B} Θ₀) X₂)
               ≡ subst (_⊢C⦂ CT) TRfin X₂
        out-eq =
          trans (cong (subst (_⊢C⦂ CT) eLL')
                      (castᶜ≡subst (castOf {Γ' ᴱ} {B} Θ₀) X₂))
            (trans (subst-fuseᶜ (castOf {Γ' ᴱ} {B} Θ₀) eLL' X₂)
                   (cong (λ p → subst (_⊢C⦂ CT) p X₂)
                         (uip {p = trans (castOf {Γ' ᴱ} {B} Θ₀) eLL'}
                              {q = TRfin})))

-- The dispatcher: the two halves' own statements each fit the unreduced
-- goal, so a `Dec` argument is matched instead of a `with`.

ren-sub-handle : ∀ {Γ Γ' B A B' ε ε'} → (r : Ren [] Γ' Γ) → (Θ : Ctx)
               → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
               → (H : (op : Op) → (ε'' : E) →
                        ((Γ ∷ B) ++ᶜ Θ) ᴱ ∷ type-of-gtype (param op)
                          ∷ [ mapᵉ (op-grade op) ]
                              (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                        ⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
               → (N : ((Γ ∷ B) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B' ‼ ε')
               → (W : Γ ⊢V⦂ B)
               → (hM : RenSubC r Θ M W)
               → (hN : RenSubC r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
               → (hH : (et : Eternal B) → (op : Op) → (ε'' : E)
                     → RenSubC {Γ ᴱ} {Γ' ᴱ} {B}
                         (restrict-ren {Ξ = []} r) (Θ ᴱ ++ᶜ Dcl B' op ε'')
                         (subst (_⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                                (ren-sub-eTot {Γ} {B} Θ et (Dcl B' op ε''))
                                (H op ε''))
                         (eternal-val-restrict et W))
               → RenSubC r Θ (handle M `with H `in N) W

ren-sub-handle {B = B} r Θ M H N W hM hN hH = go (eternal? B)
  where
    go : Dec (Eternal B) → _
    go (yes et) = ren-sub-handle-et r Θ et M H N W hM hN (hH et)
    go (no ¬et) = ren-sub-handle-ne r Θ ¬et M H N W hM hN

