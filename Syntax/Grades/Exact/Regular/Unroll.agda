------------------------------------------------------------------------
-- Unbounded upper stretches as iterations of bounded ones.           --
--                                                                    --
-- In an Archimedean time domain a stretch of any length is a         --
-- sequence of stretches of at most a positive length `δ`, and a      --
-- sequence of stretches with one set fits the stretch of their total --
-- length:                                                            --
--                                                                    --
--   str S ∞  ≈  (str S ≤δ)*                                          --
--                                                                    --
-- `unroll` rewrites every unbounded stretch of an upper expression   --
-- this way, keeping its runs up to equivalence.                      --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)
import Syntax.Grades.Traces.RunningTimes as RunningTimes
import Syntax.Durations.Monus as Monus
import Syntax.Grades.Exact.Grid as Grid

module Syntax.Grades.Exact.Regular.Unroll
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op)
  (archimedean : Grid.Archimedean T)
  (δ : Duration.Carrier D) (δ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) δ) where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat.Base using (zero; suc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T using (Hi; fin; ∞; ⁺; ⊑⇒≤; ≤⇒⁺⊑⁺)
  renaming (_∣_ to _∣ᶜ_)
open import Syntax.Grades.Exact.Grid T using (_×ᴰ_)
open import Syntax.Grades.Exact.Base T Op n code code-injective
open import Syntax.Grades.Exact.Order T Op n code code-injective using (_⊑_; ⊑-refl; ⊑-trans; lab-∙)
open import Syntax.Grades.Exact.Lift T Op n code code-injective
open import Syntax.Grades.Exact.Expression T Op n code code-injective running

------------------------------------------------------------------------
-- Stretches split and joined

private
  ∙⊑++ : ∀ x y → x ∙ y ⊑ x ++ y
  ∙⊑++ x y = ≡ˡ⇒⊑ (trans (dur-∙ x y) (sym (dur-++ x y))) (λ p _ → lab-∙ x y p)

  ++⊑∙ : ∀ x y → x ++ y ⊑ x ∙ y
  ++⊑∙ x y = ≡ˡ⇒⊑ (trans (dur-++ x y) (sym (dur-∙ x y))) (λ p _ → sym (lab-∙ x y p))

split⊑ : ∀ S a b → stretch S (a +ᴰ b) ⊑ stretch S a ++ stretch S b
split⊑ S a b =
  subst (_⊑ stretch S a ++ stretch S b) (sym (stretch-hom S a b)) (∙⊑++ (stretch S a) (stretch S b))

join⊑ : ∀ S a b → stretch S a ++ stretch S b ⊑ stretch S (a +ᴰ b)
join⊑ S a b =
  subst (stretch S a ++ stretch S b ⊑_) (sym (stretch-hom S a b)) (++⊑∙ (stretch S a) (stretch S b))

------------------------------------------------------------------------
-- Iteration is monotone

Star-mono : ∀ {X Y} → X ≾ Y → Star X ≾ Star Y
Star-mono f _ stop = [] , stop , ⊑-refl
Star-mono f _ (more {x} {y} x∈ y∈) with f x x∈ | Star-mono f y y∈
... | x′ , x′∈ , xx′ | y′ , y′∈ , yy′ = x′ ++ y′ , more x′∈ y′∈ , ⊑-++ xx′ yy′

------------------------------------------------------------------------
-- An unbounded stretch is an iteration of bounded ones

≤δ : OpSet → Expr upper
≤δ S = str S (fin (δ ∣ᶜ ⁺))

private
  stretch-0 : ∀ S → stretch S 0ᴰ ≡ []
  stretch-0 S = stretch-zero S 0ᴰ (λ q → <⇒≢ q refl)

  chop : ∀ S m τ → τ ≤ᴰ m ×ᴰ δ → Σ[ y ∈ Word ] Star ⟦ ≤δ S ⟧ y × stretch S τ ⊑ y
  chop S zero τ r =
    [] , stop , subst (_⊑ []) (sym (trans (cong (stretch S) (≤0⇒≡0 r)) (stretch-0 S))) ⊑-refl
  chop S (suc m) τ r with τ ≤ᴰ? δ
  ... | yes τδ =
    stretch S τ ++ [] , more (τ , ≤⇒⁺⊑⁺ τδ , refl) stop ,
    subst (stretch S τ ⊑_) (sym (++-identityʳ (stretch S τ))) ⊑-refl
  ... | no ¬τδ with chop S m (τ ∸ᴰ δ) (∸-≤-+ r)
  ...   | y , y∈ , fit =
    stretch S δ ++ y , more (δ , ≤⇒⁺⊑⁺ ≤ᴰ-refl , refl) y∈ ,
    ⊑-trans (subst (λ z → stretch S z ⊑ stretch S δ ++ stretch S (τ ∸ᴰ δ))
                   (+-∸ (<⇒≤ ¬τδ)) (split⊑ S δ (τ ∸ᴰ δ)))
            (⊑-++ (⊑-refl {stretch S δ}) fit)

  glue : ∀ S {y} → Star ⟦ ≤δ S ⟧ y → Σ[ τ ∈ Carrier ] y ⊑ stretch S τ
  glue S stop = 0ᴰ , subst ([] ⊑_) (sym (stretch-0 S)) ⊑-refl
  glue S (more (a , _ , refl) y∈) with glue S y∈
  ... | b , fit = a +ᴰ b , ⊑-trans (⊑-++ (⊑-refl {stretch S a}) fit) (join⊑ S a b)

unbounded≈ : ∀ S → ⟦ str {upper} S ∞ ⟧ ≈ ⟦ ≤δ S * ⟧
unbounded≈ S = to , from
  where
    to : ⟦ str {upper} S ∞ ⟧ ≾ ⟦ ≤δ S * ⟧
    to _ (τ , _ , refl) = chop S (proj₁ (archimedean δ τ δ-pos)) τ (proj₂ (archimedean δ τ δ-pos))
    from : ⟦ ≤δ S * ⟧ ≾ ⟦ str {upper} S ∞ ⟧
    from y y∈ with glue S y∈
    ... | τ , fit = stretch S τ , (τ , _ , refl) , fit

------------------------------------------------------------------------
-- Unrolling an expression

unroll : Expr upper → Expr upper
unroll ε         = ε
unroll (ops A)   = ops A
unroll (str S ∞) = ≤δ S *
unroll (str S (fin c)) = str S (fin c)
unroll (e ∣ f)   = unroll e ∣ unroll f
unroll (e · f)   = unroll e · unroll f
unroll (e *)     = unroll e *

private
  ≈-refl : ∀ {X} → X ≈ X
  ≈-refl = ≾-refl , ≾-refl

  ∪-cong : ∀ {X X′ Y Y′} → X ≈ X′ → Y ≈ Y′ → (X ∪ᴸ Y) ≈ (X′ ∪ᴸ Y′)
  ∪-cong (a , b) (c , d) =
    ∪-lub (≾-trans a (∪-ubˡ _ _)) (≾-trans c (∪-ubʳ _ _)) ,
    ∪-lub (≾-trans b (∪-ubˡ _ _)) (≾-trans d (∪-ubʳ _ _))

unroll-≈ : ∀ e → ⟦ unroll e ⟧ ≈ ⟦ e ⟧
unroll-≈ ε               = ≈-refl
unroll-≈ (ops A)         = ≈-refl
unroll-≈ (str S ∞)       = proj₂ (unbounded≈ S) , proj₁ (unbounded≈ S)
unroll-≈ (str S (fin c)) = ≈-refl
unroll-≈ (e ∣ f)         = ∪-cong (unroll-≈ e) (unroll-≈ f)
unroll-≈ (e · f)         with unroll-≈ e | unroll-≈ f
... | a , b | c , d = ·-mono a c , ·-mono b d
unroll-≈ (e *)           with unroll-≈ e
... | a , b = Star-mono a , Star-mono b
