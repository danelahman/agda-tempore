------------------------------------------------------------------------
-- Extended regular expressions, elaborated to canonical tables.       --
--                                                                     --
-- Letters, the empty word, any single letter, union, concatenation,   --
-- iteration, intersection and complement. An expression denotes a    --
-- predicate on words, by recursion on the expression; `elab` builds   --
-- its canonical table one operation at a time, and `elab-correct`     --
-- says the table recognises exactly the denoted words.                --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc)

module Syntax.Grades.Regular.Expression (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; T; not; _∧_; _∨_)
open import Data.Bool.Properties using (T-∧; T-∨; T-not-≡)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃; ∃₂; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

open import Syntax.Grades.Regular.Automaton k
open import Syntax.Grades.Regular.Canonical k
import Syntax.Grades.Regular.Operations k as O
open import Syntax.Grades.Regular.Constructions k using (_∈*_; none; more)
open import Syntax.Grades.Regular.Properties k
open import Syntax.Grades.Regular.Boolean k

open Equivalence using (to; from)

------------------------------------------------------------------------
-- Syntax

infixl 6 _∣_
infixl 5 _&_
infixl 7 _·_
infix  8 _*
infix  8 ~_
infix  9 ‵_

data Expr : Set where
  ‵_  : Letter → Expr
  ε   : Expr
  Σ   : Expr
  _∣_ : Expr → Expr → Expr
  _·_ : Expr → Expr → Expr
  _*  : Expr → Expr
  _&_ : Expr → Expr → Expr
  ~_  : Expr → Expr

-- a letter repeated

_^_ : Letter → ℕ → Expr
a ^ zero  = ε
a ^ suc n = ‵ a · a ^ n

------------------------------------------------------------------------
-- Denotation

data Star (P : Word → Set) (w : Word) : Set where
  none : w ≡ [] → Star P w
  more : ∀ u v → w ≡ u ++ v → P u → Star P v → Star P w

⟦_⟧ : Expr → Word → Set
⟦ ‵ a   ⟧ w = w ≡ a ∷ []
⟦ ε     ⟧ w = w ≡ []
⟦ Σ     ⟧ w = ∃ λ a → w ≡ a ∷ []
⟦ e ∣ f ⟧ w = ⟦ e ⟧ w ⊎ ⟦ f ⟧ w
⟦ e · f ⟧ w = ∃₂ λ u v → w ≡ u ++ v × ⟦ e ⟧ u × ⟦ f ⟧ v
⟦ e *   ⟧ w = Star ⟦ e ⟧ w
⟦ e & f ⟧ w = ⟦ e ⟧ w × ⟦ f ⟧ w
⟦ ~ e   ⟧ w = ¬ ⟦ e ⟧ w

------------------------------------------------------------------------
-- Elaboration

elab : Expr → DFA
elab (‵ a)   = O.⟦ a ∷ [] ⟧
elab ε       = O.ε
elab Σ       = Σ₁
elab (e ∣ f) = elab e O.∪ elab f
elab (e · f) = elab e O.· elab f
elab (e *)   = elab e O.*
elab (e & f) = elab e ∩ elab f
elab (~ e)   = ∁ elab e

elab-wf : ∀ e → WellFormed (elab e)
elab-wf (‵ a)   = ⟦⟧-wf (a ∷ [])
elab-wf ε       = ⟦⟧-wf []
elab-wf Σ       = Σ₁-wf
elab-wf (e ∣ f) = ∪-wf {elab e} {elab f} (elab-wf e) (elab-wf f)
elab-wf (e · f) = ·-wf {elab e} {elab f} (elab-wf e) (elab-wf f)
elab-wf (e *)   = *-wf {elab e} (elab-wf e)
elab-wf (e & f) = ∩-wf {elab e} {elab f} (elab-wf e) (elab-wf f)
elab-wf (~ e)   = ∁-wf {elab e} (elab-wf e)

elab-canonical : ∀ e → canon (elab e) ≡ elab e
elab-canonical (‵ a)   = ⟦⟧-canonical (a ∷ [])
elab-canonical ε       = ⟦⟧-canonical []
elab-canonical Σ       = Σ₁-canonical
elab-canonical (e ∣ f) = ∪-canonical {elab e} {elab f} (elab-wf e) (elab-wf f)
elab-canonical (e · f) = ·-canonical {elab e} {elab f} (elab-wf e) (elab-wf f)
elab-canonical (e *)   = *-canonical {elab e} (elab-wf e)
elab-canonical (e & f) = ∩-canonical {elab e} {elab f} (elab-wf e) (elab-wf f)
elab-canonical (~ e)   = ∁-canonical {elab e} (elab-wf e)

------------------------------------------------------------------------
-- Correctness

private
  T-subst : ∀ {a b : Bool} → a ≡ b → T a ⇔ T b
  T-subst refl = mk⇔ (λ t → t) (λ t → t)

  _∘⇔_ : ∀ {A B C : Set} → B ⇔ C → A ⇔ B → A ⇔ C
  g ∘⇔ f = mk⇔ (λ a → to g (to f a)) (λ c → from f (from g c))

  T-not : ∀ {b} → T (not b) ⇔ (¬ T b)
  T-not {false} = mk⇔ (λ _ ()) (λ _ → _)
  T-not {true}  = mk⇔ (λ ()) (λ n → n _)

  -- iteration of a language is iteration of its predicate

  star⁺ : ∀ {L P} → (∀ u → u ∈ L → P u) → ∀ {w} → w ∈* L → Star P w
  star⁺ f (none eq)            = none eq
  star⁺ f (more u v eq u∈ v∈) = more u v eq (f u u∈) (star⁺ f v∈)

  star⁻ : ∀ {L P} → (∀ u → P u → u ∈ L) → ∀ {w} → Star P w → w ∈* L
  star⁻ f (none eq)            = none eq
  star⁻ f (more u v eq pu sv) = more u v eq (f u pu) (star⁻ f sv)

elab-correct : ∀ e w → w ∈ elab e ⇔ ⟦ e ⟧ w
elab-correct (‵ a)   w = ∈-⟦⟧ (a ∷ []) w
elab-correct ε       w = ∈-⟦⟧ [] w
elab-correct Σ       w = ∈-Σ₁ w
elab-correct (e ∣ f) w =
  mk⇔ (λ t → [ (λ x → inj₁ (to (elab-correct e w) x)) , (λ y → inj₂ (to (elab-correct f w) y)) ]′
                (to T-∨ t))
      (λ { (inj₁ x) → from T-∨ (inj₁ (from (elab-correct e w) x))
         ; (inj₂ y) → from T-∨ (inj₂ (from (elab-correct f w) y)) })
  ∘⇔ T-subst (∪-accepts {elab e} {elab f} (elab-wf e) (elab-wf f) w)
  where open import Data.Sum.Base using ([_,_]′)
elab-correct (e · f) w =
  mk⇔ (λ { (u , v , eq , u∈ , v∈) → u , v , eq , to (elab-correct e u) u∈ , to (elab-correct f v) v∈ })
      (λ { (u , v , eq , u∈ , v∈) → u , v , eq , from (elab-correct e u) u∈ , from (elab-correct f v) v∈ })
  ∘⇔ ∈-· {elab e} {elab f} (elab-wf e) (elab-wf f) w
elab-correct (e *)   w =
  mk⇔ (star⁺ (λ u → to (elab-correct e u))) (star⁻ (λ u → from (elab-correct e u)))
  ∘⇔ ∈-* {elab e} (elab-wf e) w
elab-correct (e & f) w =
  mk⇔ (λ t → to (elab-correct e w) (proj₁ (to T-∧ t)) , to (elab-correct f w) (proj₂ (to T-∧ t)))
      (λ { (x , y) → from T-∧ (from (elab-correct e w) x , from (elab-correct f w) y) })
  ∘⇔ T-subst (∩-accepts {elab e} {elab f} (elab-wf e) (elab-wf f) w)
elab-correct (~ e)   w =
  mk⇔ (λ n x → n (from (elab-correct e w) x)) (λ n x → n (to (elab-correct e w) x))
  ∘⇔ (T-not ∘⇔ T-subst (∁-accepts {elab e} (elab-wf e) w))
