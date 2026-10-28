------------------------------------------------------------------------
-- Regular expressions over an arbitrary set of letters, coded over a --
-- finite alphabet.                                                   --
--                                                                    --
-- An expression over letters `A` has finitely many occurrences of    --
-- letters; its code is the extended regular expression over `Fin k`, --
-- `k` the number of occurrences, with each occurrence its own        --
-- letter, and decoding maps a letter back to the letter it occurs    --
-- as. The coded words decode to the words of the expression, and     --
-- every word of the expression is the decoding of a coded word.      --
------------------------------------------------------------------------

module Grades.Regular.Coding where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product.Base using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

import Grades.Regular.Expression
module R {k} = Grades.Regular.Expression k

------------------------------------------------------------------------
-- Expressions over letters

infixl 6 _∣_
infixl 7 _·_
infix  8 _*

data Rx (A : Set) : Set where
  ∅   : Rx A
  ε   : Rx A
  lit : A → Rx A
  _∣_ : Rx A → Rx A → Rx A
  _·_ : Rx A → Rx A → Rx A
  _*  : Rx A → Rx A

module _ {A : Set} where

  data StarA (P : List A → Set) : List A → Set where
    stop : StarA P []
    more : ∀ {u v} → P u → StarA P v → StarA P (u ++ v)

  ⟦_⟧ᴬ : Rx A → List A → Set
  ⟦ ∅     ⟧ᴬ w = ⊥
  ⟦ ε     ⟧ᴬ w = w ≡ []
  ⟦ lit a ⟧ᴬ w = w ≡ a ∷ []
  ⟦ r ∣ s ⟧ᴬ w = ⟦ r ⟧ᴬ w ⊎ ⟦ s ⟧ᴬ w
  ⟦ r · s ⟧ᴬ w = Σ[ u ∈ List A ] Σ[ v ∈ List A ] w ≡ u ++ v × ⟦ r ⟧ᴬ u × ⟦ s ⟧ᴬ v
  ⟦ r *   ⟧ᴬ w = StarA ⟦ r ⟧ᴬ w

  -- every letter occurrence satisfies a predicate

  AllLits : (A → Set) → Rx A → Set
  AllLits P ∅       = Data.Unit.⊤ where import Data.Unit
  AllLits P ε       = Data.Unit.⊤ where import Data.Unit
  AllLits P (lit a) = P a
  AllLits P (r ∣ s) = AllLits P r × AllLits P s
  AllLits P (r · s) = AllLits P r × AllLits P s
  AllLits P (r *)   = AllLits P r

  ------------------------------------------------------------------------
  -- Occurrences

  size : Rx A → ℕ
  size ∅       = 0
  size ε       = 0
  size (lit _) = 1
  size (r ∣ s) = size r + size s
  size (r · s) = size r + size s
  size (r *)   = size r

  letterAt : (r : Rx A) → Fin (size r) → A
  letterAt (lit a) _ = a
  letterAt (r ∣ s) i = [ letterAt r , letterAt s ]′ (splitAt (size r) i)
  letterAt (r · s) i = [ letterAt r , letterAt s ]′ (splitAt (size r) i)
  letterAt (r *)   i = letterAt r i

  allLits : ∀ {P} (r : Rx A) → AllLits P r → ∀ i → P (letterAt r i)
  allLits (lit a) p _ = p
  allLits {P} (r ∣ s) (p , q) i with splitAt (size r) i
  ... | inj₁ j = allLits r p j
  ... | inj₂ j = allLits s q j
  allLits {P} (r · s) (p , q) i with splitAt (size r) i
  ... | inj₁ j = allLits r p j
  ... | inj₂ j = allLits s q j
  allLits (r *) p i = allLits r p i

  ------------------------------------------------------------------------
  -- The code, each occurrence placed by an injection into the alphabet

  codeAt : (r : Rx A) → ∀ {k} → (Fin (size r) → Fin k) → R.Expr {k}
  codeAt ∅       ι = R.~ (R.Σ R.*)
  codeAt ε       ι = R.ε
  codeAt (lit a) ι = R.‵ ι zero
  codeAt (r ∣ s) ι = codeAt r (ι ∘ (_↑ˡ size s)) R.∣ codeAt s (ι ∘ (size r ↑ʳ_))
  codeAt (r · s) ι = codeAt r (ι ∘ (_↑ˡ size s)) R.· codeAt s (ι ∘ (size r ↑ʳ_))
  codeAt (r *)   ι = codeAt r ι R.*

  Agree : ∀ {k} (dec : Fin k → A) (r : Rx A) → (Fin (size r) → Fin k) → Set
  Agree dec r ι = ∀ i → dec (ι i) ≡ letterAt r i

  private
    agreeˡ : ∀ {k} (dec : Fin k → A) r s ι → Agree dec (r ∣ s) ι → Agree dec r (ι ∘ (_↑ˡ size s))
    agreeˡ dec r s ι ag i = trans (ag (i ↑ˡ size s)) (cong [ letterAt r , letterAt s ]′ (splitAt-↑ˡ (size r) i (size s)))

    agreeʳ : ∀ {k} (dec : Fin k → A) r s ι → Agree dec (r ∣ s) ι → Agree dec s (ι ∘ (size r ↑ʳ_))
    agreeʳ dec r s ι ag i = trans (ag (size r ↑ʳ i)) (cong [ letterAt r , letterAt s ]′ (splitAt-↑ʳ (size r) (size s) i))

    agreeˡ· : ∀ {k} (dec : Fin k → A) r s ι → Agree dec (r · s) ι → Agree dec r (ι ∘ (_↑ˡ size s))
    agreeˡ· dec r s ι ag i = trans (ag (i ↑ˡ size s)) (cong [ letterAt r , letterAt s ]′ (splitAt-↑ˡ (size r) i (size s)))

    agreeʳ· : ∀ {k} (dec : Fin k → A) r s ι → Agree dec (r · s) ι → Agree dec s (ι ∘ (size r ↑ʳ_))
    agreeʳ· dec r s ι ag i = trans (ag (size r ↑ʳ i)) (cong [ letterAt r , letterAt s ]′ (splitAt-↑ʳ (size r) (size s) i))

    every : ∀ {k} (u : List (Fin k)) → R.⟦ R.Σ R.* ⟧ u
    every []      = R.none refl
    every (a ∷ u) = R.more (a ∷ []) u refl (a , refl) (every u)

  code⇒ : ∀ {k} {dec : Fin k → A} r {ι} → Agree dec r ι → ∀ {u} → R.⟦ codeAt r ι ⟧ u → ⟦ r ⟧ᴬ (map dec u)
  code⇒ ∅ ag {u} c = ⊥-elim (c (every u))
  code⇒ ε ag refl = refl
  code⇒ (lit a) ag refl = cong (_∷ []) (ag zero)
  code⇒ {dec = dec} (r ∣ s) {ι} ag (inj₁ c) = inj₁ (code⇒ r (agreeˡ dec r s ι ag) c)
  code⇒ {dec = dec} (r ∣ s) {ι} ag (inj₂ c) = inj₂ (code⇒ s (agreeʳ dec r s ι ag) c)
  code⇒ {dec = dec} (r · s) {ι} ag (u , v , refl , cu , cv) =
    map dec u , map dec v , map-++ dec u v , code⇒ r (agreeˡ· dec r s ι ag) cu , code⇒ s (agreeʳ· dec r s ι ag) cv
  code⇒ {dec = dec} (r *) {ι} ag c = star c
    where
      star : ∀ {u} → R.Star R.⟦ codeAt r ι ⟧ u → StarA ⟦ r ⟧ᴬ (map dec u)
      star (R.none refl) = stop
      star (R.more u v refl cu sv) = subst (StarA ⟦ r ⟧ᴬ) (sym (map-++ dec u v)) (more (code⇒ r ag cu) (star sv))

  ⇒code : ∀ {k} {dec : Fin k → A} r {ι} → Agree dec r ι → ∀ {w} → ⟦ r ⟧ᴬ w
        → Σ[ u ∈ List (Fin k) ] R.⟦ codeAt r ι ⟧ u × map dec u ≡ w
  ⇒code ε ag refl = [] , refl , refl
  ⇒code (lit a) {ι} ag refl = ι zero ∷ [] , refl , cong (_∷ []) (ag zero)
  ⇒code {dec = dec} (r ∣ s) {ι} ag (inj₁ x) with ⇒code r (agreeˡ dec r s ι ag) x
  ... | u , c , e = u , inj₁ c , e
  ⇒code {dec = dec} (r ∣ s) {ι} ag (inj₂ x) with ⇒code s (agreeʳ dec r s ι ag) x
  ... | u , c , e = u , inj₂ c , e
  ⇒code {dec = dec} (r · s) {ι} ag (w₁ , w₂ , refl , x₁ , x₂) with ⇒code {dec = dec} r (agreeˡ· dec r s ι ag) x₁ | ⇒code {dec = dec} s (agreeʳ· dec r s ι ag) x₂
  ... | u , c , refl | v , d , refl = u ++ v , (u , v , refl , c , d) , map-++ dec u v
  ⇒code {k} {dec} (r *) {ι} ag x = star x
    where
      star : ∀ {w} → StarA ⟦ r ⟧ᴬ w → Σ[ u ∈ List (Fin k) ] R.Star R.⟦ codeAt r ι ⟧ u × map dec u ≡ w
      star stop = [] , R.none refl , refl
      star (more x₁ x₂) with ⇒code {dec = dec} r ag x₁ | star x₂
      ... | u , c , refl | v , d , refl = u ++ v , R.more u v refl c d , map-++ dec u v

  -- the code of an expression, and its decoding

  code : (r : Rx A) → R.Expr {size r}
  code r = codeAt r id

  code-sound : ∀ r {u} → R.⟦ code r ⟧ u → ⟦ r ⟧ᴬ (map (letterAt r) u)
  code-sound r = code⇒ r (λ _ → refl)

  code-complete : ∀ r {w} → ⟦ r ⟧ᴬ w → Σ[ u ∈ List (Fin (size r)) ] R.⟦ code r ⟧ u × map (letterAt r) u ≡ w
  code-complete r = ⇒code r (λ _ → refl)
