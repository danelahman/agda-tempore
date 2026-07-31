------------------------------------------------------------------------
-- When two generating substitutions act alike.                       --
--                                                                    --
-- `Sub₀` is a free syntactic structure, so distinct generators can    --
-- put the same values in the same places. `_≐ˢ₀_` compares them by    --
-- what they do to a variable — as a value, and, at box type, as a     --
-- resource variable — and the action respects it.                     --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions.Equivalence (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.RenActions S
open import Syntax.Renamings  S
open import Syntax.Types      S

open import Syntax.Renamings.Equivalence S
open import Syntax.Renamings.Coherence   S
open import Syntax.Terms.Equivalence     S

open import Syntax.Substitutions   S

open import Syntax.Substitutions.Base   S
open import Syntax.Substitutions.Lookup S
open import Syntax.Substitutions.Action S

-- The grade bound a `var` carries is irrelevant, and so is the one handed to
-- the observation.

sub-var₀-irr : ∀ {Γ Γ' A ρ} → (s : Sub₀ [] Γ Γ') → (x : A ∈[ ρ ] Γ')
             → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
             → sub-var₀ s x f ≡ sub-var₀ s x f'
sub-var₀-irr s x f f' = cong (sub-var₀ s x) (bound-irr f f')

-- An eternal type discharges a grade bound whatever the grade.

et-bound : ∀ {A ρ} → Eternal A → ¬ Eternal A → ρ ≾ᵣ uᵣ
et-bound et ¬et = ⊥-elim (¬et et)

-- Two `var` nodes at the same image agree.

var-img-≡ : ∀ {Γ A} {t t' : Var Γ A} → t ≡ t'
          → (f  : ¬ Eternal A → proj₁ t  ≾ᵣ uᵣ)
          → (f' : ¬ Eternal A → proj₁ t' ≾ᵣ uᵣ)
          → var f (proj₂ t) ≡ var f' (proj₂ t')
var-img-≡ refl f f' = var-≡

------------------------------------------------------------------------
-- ACTING ALIKE
------------------------------------------------------------------------

-- Where a substitution sends a resource variable, forgetting the grade bound.
-- This is what an `unbox` node stores.

tgt-img₀ : ∀ {Γ Γ' A ρ ρ'} → Sub₀ [] Γ Γ' → [ ρ ] A ∈[ ρ' ] Γ' → Var Γ ([ ρ ] A)
tgt-img₀ s y = proj₁ (sub-tgt₀ s y) , proj₁ (proj₂ (sub-tgt₀ s y))

infix 4 _≐ˢ₀_

-- A record, not a function type, for the same reason as `_≐ʳ_`: it is used at
-- substitutions Agda has to infer.
--
-- Two fields, because `atᵗ` is not derivable from `atᵛ`: a box-typed variable
-- has no `≾ᵣ uᵣ` bound, so it is never read as a value.

record _≐ˢ₀_ {Γ Γ'} (s s' : Sub₀ [] Γ Γ') : Set where
  constructor mk≐ˢ₀
  field
    atᵛ : ∀ {A ρ} → (x : A ∈[ ρ ] Γ') → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
        → sub-var₀ s x f ≡ sub-var₀ s' x f
    atᵗ : ∀ {A ρ ρ'} → (y : [ ρ ] A ∈[ ρ' ] Γ') → tgt-img₀ s y ≡ tgt-img₀ s' y

open _≐ˢ₀_ public

≐ˢ₀-refl : ∀ {Γ Γ'} {s : Sub₀ [] Γ Γ'} → s ≐ˢ₀ s
≐ˢ₀-refl = mk≐ˢ₀ (λ x f → refl) (λ y → refl)

≐ˢ₀-sym : ∀ {Γ Γ'} {s s' : Sub₀ [] Γ Γ'} → s ≐ˢ₀ s' → s' ≐ˢ₀ s
≐ˢ₀-sym h = mk≐ˢ₀ (λ x f → sym (atᵛ h x f)) (λ y → sym (atᵗ h y))

≐ˢ₀-trans : ∀ {Γ Γ'} {s s' s'' : Sub₀ [] Γ Γ'}
          → s ≐ˢ₀ s' → s' ≐ˢ₀ s'' → s ≐ˢ₀ s''
≐ˢ₀-trans h h' =
  mk≐ˢ₀ (λ x f → trans (atᵛ h x f) (atᵛ h' x f))
        (λ y → trans (atᵗ h y) (atᵗ h' y))

------------------------------------------------------------------------
-- THE CONGRUENCES
--
-- Unlike a renaming's, a substitution's image is a *term*, so a congruence
-- weakens it (`∷`) or extends it past a lock (`⟨⟩`) rather than relocating a
-- variable. Each is therefore a `cong` of the operation the clause applies.
------------------------------------------------------------------------

cong-∷-sub-≐ˢ₀ : ∀ {Γ Γ' A} {s s' : Sub₀ [] Γ Γ'}
               → s ≐ˢ₀ s' → cong-∷-sub {A = A} s ≐ˢ₀ cong-∷-sub s'
cong-∷-sub-≐ˢ₀ h = mk≐ˢ₀ goᵛ goᵗ
  where
    goᵛ : ∀ {A' ρ'} → (x : A' ∈[ ρ' ] _) → (f : _) → _
    goᵛ Hd       f = refl
    goᵛ (Tl-∷ y) f = cong (V-rename wk-ren) (atᵛ h y f)

    goᵗ : ∀ {A' ρ ρ'} → (y : [ ρ ] A' ∈[ ρ' ] _) → _
    goᵗ Hd       = refl
    goᵗ (Tl-∷ y) = cong Var-∷ (atᵗ h y)

-- Crossing a lock splits on the variable's eternality, but both sides split on
-- the same decision — the clause takes it as an argument.

cong-⟨⟩-sub-≐ˢ₀ : ∀ {Γ Γ' ρ} {s s' : Sub₀ [] Γ Γ'}
                → s ≐ˢ₀ s' → cong-⟨⟩-sub {ρ = ρ} s ≐ˢ₀ cong-⟨⟩-sub s'
cong-⟨⟩-sub-≐ˢ₀ {ρ = ρ} h = mk≐ˢ₀ goᵛ goᵗ
  where
    goᵛ : ∀ {A' ρ'} → (x : A' ∈[ ρ' ] _) → (f : _) → _
    goᵛ {A'} (Tl-⟨⟩ y) f with eternal? A'
    ... | yes et = cong (eternal-val-ext et) (atᵛ h y _)
    ... | no ¬et = cong (V-rename _) (atᵛ h y _)

    goᵗ : ∀ {A' ρ₀ ρ'} → (y : [ ρ₀ ] A' ∈[ ρ' ] _) → _
    goᵗ (Tl-⟨⟩ y) = cong (Var-⟨⟩ ρ) (atᵗ h y)

cong-sub₀-≐ˢ₀ : ∀ {Γ Γ'} {s s' : Sub₀ [] Γ Γ'} → (Γ₀ : Ctx)
              → s ≐ˢ₀ s' → cong-sub₀ {Γ'' = Γ₀} s ≐ˢ₀ cong-sub₀ s'
cong-sub₀-≐ˢ₀ []         h = h
cong-sub₀-≐ˢ₀ (Γ₀ ∷ A)   h = cong-∷-sub-≐ˢ₀ (cong-sub₀-≐ˢ₀ Γ₀ h)
cong-sub₀-≐ˢ₀ (Γ₀ ⟨ ρ ⟩) h = cong-⟨⟩-sub-≐ˢ₀ (cong-sub₀-≐ˢ₀ Γ₀ h)

------------------------------------------------------------------------
-- ETERNAL VALUES AGAINST RENAMING
------------------------------------------------------------------------

-- Restricting an eternal value is natural in renaming: the `var` case goes
-- through the reflection `∈-ᴱ⁻`, both sides' targets reflecting to `var-img r x`.

eternal-val-restrict-ren : ∀ {Γ Γ' A} → (et : Eternal A)
                         → (r : Ren [] Γ Γ') → (W : Γ' ⊢V⦂ A)
                         → eternal-val-restrict et (V-rename r W)
                         ≡ V-rename (restrict-ren r) (eternal-val-restrict et W)

eternal-val-restrict-ren {Γ} {Γ'} et r (var f x) =
  trans
    (cong (eternal-val-restrict et) (var-ren-≡ r x f fet))
    (sym (var-ren-img-≡ (restrict-ren r) (∈-ᴱ et x) fet (sym tgt-eq) fet))
  where
    fet : ∀ {ρ₀} → ¬ Eternal _ → ρ₀ ≾ᵣ uᵣ
    fet ¬et = ⊥-elim (¬et et)

    tgt-eq : _≡_ {A = Var (Γ ᴱ) _}
                 (uᵣ , ∈-ᴱ et (proj₂ (var-img r x)))
                 (var-img (restrict-ren r) (∈-ᴱ et x))
    tgt-eq =
      ∈-ᴱ⁻-inj Γ _ _
        (trans (∈-ᴱ⁻-∈-ᴱ Γ et (proj₂ (var-img r x)))
          (sym (trans (restrict-img⁻ r (∈-ᴱ et x))
                      (cong (var-img′ r) (∈-ᴱ⁻-∈-ᴱ Γ' et x)))))

eternal-val-restrict-ren et r (const c) = refl
eternal-val-restrict-ren et r ⋆         = refl
eternal-val-restrict-ren (et₁ |×|ₑ et₂) r ⦉ V₁ , V₂ ⦊ =
  cong₂ ⦉_,_⦊ (eternal-val-restrict-ren et₁ r V₁)
              (eternal-val-restrict-ren et₂ r V₂)

-- The restriction drops the lock an eternal extension crossed.

eternal-val-restrict-ext : ∀ {Γ A ρ} → (et et' : Eternal A) → (W : Γ ⊢V⦂ A)
                         → eternal-val-restrict et (eternal-val-ext {ρ = ρ} et' W)
                         ≡ eternal-val-restrict et W

eternal-val-restrict-ext et et' (var f x) = var-≡
eternal-val-restrict-ext et et' (const c) = refl
eternal-val-restrict-ext et et' ⋆         = refl
eternal-val-restrict-ext (et₁ |×|ₑ et₂) (et₁' |×|ₑ et₂') ⦉ V₁ , V₂ ⦊ =
  cong₂ ⦉_,_⦊ (eternal-val-restrict-ext et₁ et₁' V₁)
              (eternal-val-restrict-ext et₂ et₂' V₂)

-- Reflection is undone by `∈-ᴱ`, which is `∈-ᴱ⁻-∈-ᴱ` read through injectivity.

∈-ᴱ-∈-ᴱ⁻ : (Γ : Ctx) → ∀ {A ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ ᴱ)
         → _≡_ {A = Var (Γ ᴱ) A} (ρ , x) (uᵣ , ∈-ᴱ et (proj₂ (∈-ᴱ⁻ Γ x)))
∈-ᴱ-∈-ᴱ⁻ Γ et x =
  ∈-ᴱ⁻-inj Γ _ _ (sym (∈-ᴱ⁻-∈-ᴱ Γ et (proj₂ (∈-ᴱ⁻ Γ x))))

------------------------------------------------------------------------
-- THE ETERNAL RESTRICTION
--
-- `restrict-sub₀` recurses on the substitution, so this is not a congruence of
-- a function of the image. It goes through the reflection `∈-ᴱ⁻`: the image
-- under the restricted substitution is the restriction of the image under the
-- original one. Unlike for renamings no injectivity is needed at the end —
-- `eternal-val-restrict` maps the unrestricted image to the restricted context.
------------------------------------------------------------------------

-- The value-carrying clause, with the decision as an argument. Both sides are
-- read in `Γ ᴱ`, so the decision appears only in the variable's own context.

restrict-sub-img⁻-∷ : ∀ {Γ B} → (V : Γ ⊢V⦂ B) → (dec : Dec (Eternal B))
                    → ∀ {A ρ} → (x : A ∈[ ρ ] ᴱ-∷ (Γ ᴱ) B dec) → (et : Eternal A)
                    → sub-var₀ (restrict-val-sub {[]} {Γ} {B} dec V) x (et-bound et)
                    ≡ eternal-val-restrict et
                        (sub-var₀ (val-sub V) (proj₂ (∈-ᴱ⁻-∷ Γ B dec x)) (et-bound et))

restrict-sub-img⁻-∷ {Γ} V (yes etB) Hd et =
  cong (λ e → eternal-val-restrict e V) (eternal-irrelevant etB et)
restrict-sub-img⁻-∷ {Γ} V (yes etB) (Tl-∷ y) et =
  var-img-≡ (∈-ᴱ-∈-ᴱ⁻ Γ et y) (et-bound et) (et-bound et)
restrict-sub-img⁻-∷ {Γ} V (no ¬etB) x et =
  var-img-≡ (∈-ᴱ-∈-ᴱ⁻ Γ et x) _ (et-bound et)

-- RESTRICTION AGAINST WEAKENING
--
-- Whether the added variable survives the restriction is only decidable, so
-- both statements are conjugated by an arbitrary proof of the context equation
-- they need, as `restrict-wk-et-≐ʳ` and `restrict-wk-≐ʳ` are.

-- Renaming along an identity-like renaming is the transport.

V-rename-eq-≡ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {r : Ren [] Γ' Γ}
              → r ≐ʳ eq-ren e → (V : Γ ⊢V⦂ A)
              → V-rename r V ≡ subst (_⊢V⦂ A) e V
V-rename-eq-≡ refl h V = V-rename-id-≡ h V

-- At an eternal `B` the restriction of the weakening is the weakening again.

restrict-wk-et-≡ᵛ : ∀ {Γ₀ A B} → (etB : Eternal B) → (et : Eternal A)
                  → (V : Γ₀ ⊢V⦂ A) → (e : (Γ₀ ∷ B) ᴱ ≡ Γ₀ ᴱ ∷ B)
                  → eternal-val-restrict et (V-rename (wk-ren {A = B}) V)
                  ≡ subst (_⊢V⦂ A) (sym e)
                       (V-rename (wk-ren {A = B}) (eternal-val-restrict et V))
restrict-wk-et-≡ᵛ {Γ₀} {A} {B} etB et V e =
  trans (eternal-val-restrict-ren et (wk-ren {A = B}) V)
    (trans (V-rename-≡ (restrict-wk-et-≐ʳ etB [] refl e) (eternal-val-restrict et V))
      (trans (V-rename-∘ (eq-ren refl) (wk-ren ∘ʳ eq-ren (sym e))
                         (eternal-val-restrict et V))
        (trans (V-rename-cong (wk-ren ∘ʳ eq-ren (sym e)) (V-rename-id-≡ ≐ʳ-refl _))
          (trans (V-rename-∘ (wk-ren {A = B}) (eq-ren (sym e)) _)
                 (V-rename-eq-≡ (sym e) ≐ʳ-refl _)))))

-- At a non-eternal `B` it is the identity.

restrict-wk-ne-≡ᵛ : ∀ {Γ₀ A B} → (¬etB : ¬ Eternal B) → (et : Eternal A)
                  → (V : Γ₀ ⊢V⦂ A) → (e : Γ₀ ᴱ ≡ (Γ₀ ∷ B) ᴱ)
                  → eternal-val-restrict et (V-rename (wk-ren {A = B}) V)
                  ≡ subst (_⊢V⦂ A) e (eternal-val-restrict et V)
restrict-wk-ne-≡ᵛ {Γ₀} {A} {B} ¬etB et V e =
  trans (eternal-val-restrict-ren et (wk-ren {A = B}) V)
        (V-rename-eq-≡ e (restrict-wk-≐ʳ ¬etB [] e) (eternal-val-restrict et V))

------------------------------------------------------------------------

-- The congruence's clause, with the decision and the context equation it
-- justifies both as arguments; the recursive call is passed in.

restrict-sub-img⁻-∷-cong :
    ∀ {Δ Δ' B} → (s : Sub₀ [] Δ Δ') → (dec : Dec (Eternal B))
  → (e : ᴱ-∷ (Δ ᴱ) B dec ≡ (Δ ∷ B) ᴱ)
  → ∀ {A ρ} → (x : A ∈[ ρ ] ᴱ-∷ (Δ' ᴱ) B dec) → (et : Eternal A)
  → (ih : ∀ {A' ρ'} → (y : A' ∈[ ρ' ] Δ' ᴱ) → (et' : Eternal A')
        → sub-var₀ (restrict-sub₀ s) y (et-bound et')
        ≡ eternal-val-restrict et' (sub-var₀ s (proj₂ (∈-ᴱ⁻ Δ' y)) (et-bound et')))
  → subst (_⊢V⦂ A) e
      (sub-var₀ (restrict-∷-sub {[]} {Δ} {Δ'} {B} dec (restrict-sub₀ s)) x (et-bound et))
  ≡ eternal-val-restrict et
      (sub-var₀ (cong-∷-sub s) (proj₂ (∈-ᴱ⁻-∷ Δ' B dec x)) (et-bound et))

restrict-sub-img⁻-∷-cong {Δ} {Δ'} {B} s (yes etB) e Hd et ih
  rewrite eternal?-yes etB | uip {p = e} {q = refl} = var-≡

restrict-sub-img⁻-∷-cong {Δ} {Δ'} {B} s (yes etB) e (Tl-∷ y) et ih =
  trans (cong (λ V → subst (_⊢V⦂ _) e (V-rename wk-ren V)) (ih y et))
    (trans (cong (λ e₀ → subst (_⊢V⦂ _) e₀
                           (V-rename wk-ren (eternal-val-restrict et U)))
                 (uip {p = e} {q = sym (sym e)}))
           (sym (restrict-wk-et-≡ᵛ etB et U (sym e))))
  where
    U = sub-var₀ s (proj₂ (∈-ᴱ⁻ Δ' y)) (et-bound et)

restrict-sub-img⁻-∷-cong {Δ} {Δ'} {B} s (no ¬etB) e x et ih =
  trans (cong (subst (_⊢V⦂ _) e) (ih x et))
        (sym (restrict-wk-ne-≡ᵛ ¬etB et U e))
  where
    U = sub-var₀ s (proj₂ (∈-ᴱ⁻ Δ' x)) (et-bound et)

------------------------------------------------------------------------

restrict-sub-img⁻ : ∀ {Γ Γ'} → (s : Sub₀ [] Γ Γ') → ∀ {A ρ}
                  → (x : A ∈[ ρ ] Γ' ᴱ) → (et : Eternal A)
                  → sub-var₀ (restrict-sub₀ s) x (et-bound et)
                  ≡ eternal-val-restrict et
                      (sub-var₀ s (proj₂ (∈-ᴱ⁻ Γ' x)) (et-bound et))

restrict-sub-img⁻ {Γ} {Γ'} ⌜ r ⌝ x et =
  var-img-≡ tgt-eq (λ ¬et → ≾ᵣ-trans _ (et-bound et ¬et)) (et-bound et)
  where
    tgt-eq : _≡_ {A = Var (Γ ᴱ) _}
                 (var-img (restrict-ren r) x)
                 (uᵣ , ∈-ᴱ et (proj₂ (var-img′ r (∈-ᴱ⁻ Γ' x))))
    tgt-eq =
      ∈-ᴱ⁻-inj Γ _ _
        (trans (restrict-img⁻ r x)
               (sym (∈-ᴱ⁻-∈-ᴱ Γ et (proj₂ (var-img′ r (∈-ᴱ⁻ Γ' x))))))

restrict-sub-img⁻ {Γ} (val-sub {Δ} {B} V) x et =
  restrict-sub-img⁻-∷ V (eternal? B) x et

restrict-sub-img⁻ (cong-∷-sub {Δ} {Δ'} {B} s) x et =
  restrict-sub-img⁻-∷-cong s (eternal? B) refl x et (λ y et' → restrict-sub-img⁻ s y et')

restrict-sub-img⁻ {Γ} {Γ' ⟨ ρ ⟩} (cong-⟨⟩-sub s) x et
  rewrite eternal?-yes et =
  trans (restrict-sub-img⁻ s x et)
        (sym (eternal-val-restrict-ext et et
               (sub-var₀ s (proj₂ (∈-ᴱ⁻ Γ' x)) (et-bound et))))

-- The resource-variable image is unaffected: a box type is never eternal, so
-- no variable of a restricted context has one.

tgt-img₀-ᴱ : ∀ {A ρ ρ'} → (Γ' : Ctx) → (y : [ ρ ] A ∈[ ρ' ] Γ' ᴱ) → ⊥
tgt-img₀-ᴱ Γ' y with ec-eternal (ᴱ-EternalCtx Γ') y
... | ()

restrict-sub₀-≐ˢ₀ : ∀ {Γ Γ'} {s s' : Sub₀ [] Γ Γ'}
                  → s ≐ˢ₀ s' → restrict-sub₀ s ≐ˢ₀ restrict-sub₀ s'
restrict-sub₀-≐ˢ₀ {Γ} {Γ'} {s} {s'} h = mk≐ˢ₀ goᵛ goᵗ
  where
    goᵛ : ∀ {A ρ} → (x : A ∈[ ρ ] Γ' ᴱ) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
        → sub-var₀ (restrict-sub₀ s) x f ≡ sub-var₀ (restrict-sub₀ s') x f
    goᵛ {A} x f =
      trans (sub-var₀-irr (restrict-sub₀ s) x f (et-bound et))
        (trans (restrict-sub-img⁻ s x et)
          (trans (cong (eternal-val-restrict et) (atᵛ h (proj₂ (∈-ᴱ⁻ Γ' x)) (et-bound et)))
            (trans (sym (restrict-sub-img⁻ s' x et))
                   (sub-var₀-irr (restrict-sub₀ s') x (et-bound et) f))))
      where
        et : Eternal A
        et = ec-eternal (ᴱ-EternalCtx Γ') x

    goᵗ : ∀ {A ρ ρ'} → (y : [ ρ ] A ∈[ ρ' ] Γ' ᴱ)
        → tgt-img₀ (restrict-sub₀ s) y ≡ tgt-img₀ (restrict-sub₀ s') y
    goᵗ y = ⊥-elim (tgt-img₀-ᴱ Γ' y)

------------------------------------------------------------------------
-- THE ACTION RESPECTS ACTING ALIKE
--
-- Induction on the term. At `var` and `unbox` the whole content is the
-- hypothesis; the binding formers use `cong-sub₀-≐ˢ₀` and `handle` uses
-- `restrict-sub₀-≐ˢ₀`.
------------------------------------------------------------------------

mutual

  V-sub₀-≐ˢ₀ : ∀ {Γ Γ' A} {s s' : Sub₀ [] Γ Γ'} → s ≐ˢ₀ s'
             → (V : Γ' ⊢V⦂ A) → V-sub₀ s V ≡ V-sub₀ s' V

  V-sub₀-≐ˢ₀ h (var f x) = atᵛ h x f
  V-sub₀-≐ˢ₀ h (const c) = refl
  V-sub₀-≐ˢ₀ h ⋆         = refl
  V-sub₀-≐ˢ₀ h ⦉ V , W ⦊  = cong₂ ⦉_,_⦊ (V-sub₀-≐ˢ₀ h V) (V-sub₀-≐ˢ₀ h W)
  V-sub₀-≐ˢ₀ h (lam M)   = cong lam (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ∷ _) h) M)

  C-sub₀-≐ˢ₀ : ∀ {Γ Γ' C} {s s' : Sub₀ [] Γ Γ'} → s ≐ˢ₀ s'
             → (M : Γ' ⊢C⦂ C) → C-sub₀ s M ≡ C-sub₀ s' M

  C-sub₀-≐ˢ₀ h (return V) = cong return (V-sub₀-≐ˢ₀ h V)
  C-sub₀-≐ˢ₀ h (M ⨟ N) =
    cong₂ _⨟_ (C-sub₀-≐ˢ₀ h M) (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-sub₀-≐ˢ₀ h (V · W) = cong₂ _·_ (V-sub₀-≐ˢ₀ h V) (V-sub₀-≐ˢ₀ h W)
  C-sub₀-≐ˢ₀ h (match V `in M) =
    cong₂ match_`in_ (V-sub₀-≐ˢ₀ h V) (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ∷ _ ∷ _) h) M)
  C-sub₀-≐ˢ₀ h (absurd V) = cong absurd (V-sub₀-≐ˢ₀ h V)
  C-sub₀-≐ˢ₀ h (perform op V M) =
    cong₂ (perform _) (V-sub₀-≐ˢ₀ h V)
          (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ (_ ⟨ _ ⟩ ∷ _) h) M)
  C-sub₀-≐ˢ₀ h (delay τ M) =
    cong (delay _) (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ⟨ _ ⟩) h) M)
  C-sub₀-≐ˢ₀ h (handle M `with H `in N) =
    handle-≡ (C-sub₀-≐ˢ₀ h M)
      (λ op ε'' →
         C-sub₀-≐ˢ₀ (cong-∷-sub-≐ˢ₀ (cong-∷-sub-≐ˢ₀ (restrict-sub₀-≐ˢ₀ h))) (H op ε''))
      (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ (_ ⟨ _ ⟩ ∷ _) h) N)
  C-sub₀-≐ˢ₀ h (unbox x rel M) =
    unbox-≡ (atᵗ h x) (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ∷ _) h) M)
  C-sub₀-≐ˢ₀ h (box V M) =
    cong₂ box (V-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ⟨ _ ⟩) h) V)
              (C-sub₀-≐ˢ₀ (cong-sub₀-≐ˢ₀ ([] ∷ _) h) M)
  C-sub₀-≐ˢ₀ h (coerce rel M) = coerce-≡ (C-sub₀-≐ˢ₀ h M)


-- ETERNAL VALUES

eternal-val-ext-cong : ∀ {Γ A ρ} → (et : Eternal A) → {V V' : Γ ⊢V⦂ A}
                     → V ≡ V'
                     → eternal-val-ext {ρ = ρ} et V ≡ eternal-val-ext et V'
eternal-val-ext-cong et = cong (eternal-val-ext et)

substᶜ-≡ : ∀ {C Γ₁ Γ₂} → (e : Γ₁ ≡ Γ₂) → {M M' : Γ₁ ⊢C⦂ C}
         → M ≡ M' → subst (_⊢C⦂ C) e M ≡ subst (_⊢C⦂ C) e M'
substᶜ-≡ {C} e = cong (subst (_⊢C⦂ C) e)

substᶜ-≡′ : (f : Ctx → Ctx) → ∀ {C Γ₁ Γ₂} → (e : Γ₁ ≡ Γ₂) → {M M' : f Γ₁ ⊢C⦂ C}
          → M ≡ M'
          → subst (λ z → f z ⊢C⦂ C) e M ≡ subst (λ z → f z ⊢C⦂ C) e M'
substᶜ-≡′ f {C} e = cong (subst (λ z → f z ⊢C⦂ C) e)

------------------------------------------------------------------------
-- SUBSTITUTION IS A CONGRUENCE
------------------------------------------------------------------------

sub-≡ᵛ : ∀ {Γ Γ₁ Γ₂ A B} → (s : Γ₁ ∷ A , Γ₂ split Γ) → {W W' : Γ₁ ⊢V⦂ A}
       → W ≡ W' → {V V' : Γ ⊢V⦂ B} → V ≡ V'
       → (V [ s ↦ W ]v) ≡ (V' [ s ↦ W' ]v)
sub-≡ᵛ s eW eV = cong₂ (λ U V₀ → V₀ [ s ↦ U ]v) eW eV

sub-≡ᶜ : ∀ {Γ Γ₁ Γ₂ A C} → (s : Γ₁ ∷ A , Γ₂ split Γ) → {W W' : Γ₁ ⊢V⦂ A}
       → W ≡ W' → {M M' : Γ ⊢C⦂ C} → M ≡ M'
       → (M [ s ↦ W ]c) ≡ (M' [ s ↦ W' ]c)
sub-≡ᶜ s eW eM = cong₂ (λ U M₀ → M₀ [ s ↦ U ]c) eW eM

