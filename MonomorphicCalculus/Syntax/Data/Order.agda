------------------------------------------------------------------------
-- The structural order on data is a strict total order.              --
--                                                                    --
-- A comparison `c` is lawful when swapping its arguments flips its   --
-- outcome, `equal` is equality, and `less` is transitive. The base   --
-- types' comparisons are lawful, and lawfulness is closed under the  --
-- formers, so `compareᵈ` is lawful at every eternal type and `less`  --
-- is a strict total order (`compareᵈ-isStrictTotalOrder`). Each      --
-- relation of `Cmp` then means what its name says.                   --
------------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)

open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Relation.Binary.Structures using (IsStrictTotalOrder; IsStrictPartialOrder)

open import Language.BaseTypes using (order-of)
open import Language.Comparisons
open import Language.Spec

open import Util.Equality

module MonomorphicCalculus.Syntax.Data.Order (S : LanguageSpec) where

open LanguageSpec S

open import MonomorphicCalculus.Syntax.Types S
open import MonomorphicCalculus.Syntax.Data  S

flipᵒ : Order → Order
flipᵒ less    = greater
flipᵒ equal   = equal
flipᵒ greater = less

record Lawful {X : Set} (c : X → X → Order) : Set where
  field
    swap   : ∀ x y → c y x ≡ flipᵒ (c x y)
    exact  : ∀ {x y} → c x y ≡ equal → x ≡ y
    reflex : ∀ x → c x x ≡ equal
    trans< : ∀ {x y z} → c x y ≡ less → c y z ≡ less → c x z ≡ less

open Lawful

-- Lexicographic combination

lex-swap : ∀ a b → lexᵒ (flipᵒ a) (flipᵒ b) ≡ flipᵒ (lexᵒ a b)
lex-swap less    b = refl
lex-swap equal   b = refl
lex-swap greater b = refl

lex-exact : ∀ {a b} → lexᵒ a b ≡ equal → (a ≡ equal) × (b ≡ equal)
lex-exact {equal} e = refl , e

-- transitivity of a lexicographic pair, the second component's for the
-- one triple at hand

lex-trans : ∀ {X} {c : X → X → Order} → Lawful c → ∀ {x x' x''} {b b' b''}
          → (b ≡ less → b' ≡ less → b'' ≡ less)
          → lexᵒ (c x x') b ≡ less → lexᵒ (c x' x'') b' ≡ less
          → lexᵒ (c x x'') b'' ≡ less
lex-trans {c = c} L {x} {x'} {x''} {b} {b'} {b''} t h h' =
  go (c x x') (c x' x'') refl refl h h'
  where
    go : ∀ a a' → c x x' ≡ a → c x' x'' ≡ a'
       → lexᵒ a b ≡ less → lexᵒ a' b' ≡ less → lexᵒ (c x x'') b'' ≡ less
    go less less e e' _ _ = cong (λ o → lexᵒ o b'') (trans< L e e')
    go less equal e e' _ _ =
      subst (λ z → lexᵒ (c x z) b'' ≡ less) (exact L e') (cong (λ o → lexᵒ o b'') e)
    go equal less e e' _ _ =
      subst (λ z → lexᵒ (c z x'') b'' ≡ less) (sym (exact L e)) (cong (λ o → lexᵒ o b'') e')
    go equal equal e e' h h' =
      subst (λ z → lexᵒ (c x z) b'' ≡ less) (exact L e')
        (subst (λ z → lexᵒ (c x z) b'' ≡ less) (exact L e)
          (trans (cong (λ o → lexᵒ o b'') (reflex L x)) (t h h')))
    go less    greater _ _ _ ()
    go equal   greater _ _ _ ()
    go greater _       _ _ () _

-- The base types: a strict total order's trichotomy

module _ {X : Set} {_<_ : X → X → Set} (sto : IsStrictTotalOrder _≡_ _<_) where

  private
    module O = IsStrictTotalOrder sto

    c : X → X → Order
    c x y = order-of (O.compare x y)

    <⇒less : ∀ {x y} → x < y → c x y ≡ less
    <⇒less {x} {y} p with O.compare x y
    ... | tri< _ _ _  = refl
    ... | tri≈ ¬p _ _ = ⊥-elim (¬p p)
    ... | tri> ¬p _ _ = ⊥-elim (¬p p)

    less⇒< : ∀ {x y} → c x y ≡ less → x < y
    less⇒< {x} {y} e with O.compare x y
    less⇒< () | tri≈ _ _ _
    less⇒< () | tri> _ _ _
    ... | tri< p _ _ = p

  order-of-lawful : Lawful c
  order-of-lawful .swap x y with O.compare x y | O.compare y x
  ... | tri< _ _ ¬q  | tri< q _ _   = ⊥-elim (¬q q)
  ... | tri< _ ¬e _  | tri≈ _ e _   = ⊥-elim (¬e (sym e))
  ... | tri< _ _ _   | tri> _ _ _   = refl
  ... | tri≈ _ _ ¬q  | tri< q _ _   = ⊥-elim (¬q q)
  ... | tri≈ _ _ _   | tri≈ _ _ _   = refl
  ... | tri≈ ¬p _ _  | tri> _ _ p   = ⊥-elim (¬p p)
  ... | tri> _ _ _   | tri< _ _ _   = refl
  ... | tri> _ ¬e _  | tri≈ _ e _   = ⊥-elim (¬e (sym e))
  ... | tri> ¬p _ _  | tri> _ _ p   = ⊥-elim (¬p p)
  order-of-lawful .exact {x} {y} e with O.compare x y
  order-of-lawful .exact () | tri< _ _ _
  order-of-lawful .exact () | tri> _ _ _
  ... | tri≈ _ p _ = p
  order-of-lawful .reflex x with O.compare x x
  ... | tri< p _ _ = ⊥-elim (O.irrefl refl p)
  ... | tri≈ _ _ _ = refl
  ... | tri> _ _ p = ⊥-elim (O.irrefl refl p)
  order-of-lawful .trans< e e' = <⇒less (O.trans (less⇒< e) (less⇒< e'))

-- The formers

𝔹-lawful : Lawful compareᴮ
𝔹-lawful .swap false false = refl
𝔹-lawful .swap false true  = refl
𝔹-lawful .swap true  false = refl
𝔹-lawful .swap true  true  = refl
𝔹-lawful .exact {false} {false} _ = refl
𝔹-lawful .exact {true}  {true}  _ = refl
𝔹-lawful .reflex false = refl
𝔹-lawful .reflex true  = refl
𝔹-lawful .trans< {false} {true} {true} _ ()
𝔹-lawful .trans< {false} {true} {false} _ ()
𝔹-lawful .trans< {false} {false} () _
𝔹-lawful .trans< {true}  {false} () _
𝔹-lawful .trans< {true}  {true}  () _

ℕ-lawful : Lawful compareᴺ
ℕ-lawful .swap zero    zero    = refl
ℕ-lawful .swap zero    (suc _) = refl
ℕ-lawful .swap (suc _) zero    = refl
ℕ-lawful .swap (suc n) (suc m) = ℕ-lawful .swap n m
ℕ-lawful .exact {zero}  {zero}  _ = refl
ℕ-lawful .exact {suc n} {suc m} e = cong suc (ℕ-lawful .exact e)
ℕ-lawful .reflex zero    = refl
ℕ-lawful .reflex (suc n) = ℕ-lawful .reflex n
ℕ-lawful .trans< {zero}  {suc _} {suc _} _ _ = refl
ℕ-lawful .trans< {suc n} {suc m} {suc k} e e' = ℕ-lawful .trans< {n} {m} {k} e e'

×-lawful : ∀ {A₁ A₂} {et₁ : Et A₁} {et₂ : Et A₂}
         → Lawful (compareᵈ et₁) → Lawful (compareᵈ et₂)
         → Lawful (compareᵈ (et₁ |×|ₑ et₂))
×-lawful {et₁ = et₁} {et₂} L M .swap (x , y) (x' , y') =
  trans (cong₂ lexᵒ (L .swap x x') (M .swap y y'))
        (lex-swap (compareᵈ et₁ x x') (compareᵈ et₂ y y'))
×-lawful L M .exact {x , y} {x' , y'} e with lex-exact e
... | e₁ , e₂ = cong₂ _,_ (L .exact e₁) (M .exact e₂)
×-lawful L M .reflex (x , y) = cong₂ lexᵒ (L .reflex x) (M .reflex y)
×-lawful L M .trans< {x , y} {x' , y'} {x'' , y''} = lex-trans L (M .trans<)

⊎-lawful : ∀ {A₁ A₂} {et₁ : Et A₁} {et₂ : Et A₂}
         → Lawful (compareᵈ et₁) → Lawful (compareᵈ et₂)
         → Lawful (compareᵈ (et₁ |+|ₑ et₂))
⊎-lawful L M .swap (inj₁ x) (inj₁ x') = L .swap x x'
⊎-lawful L M .swap (inj₁ _) (inj₂ _)  = refl
⊎-lawful L M .swap (inj₂ _) (inj₁ _)  = refl
⊎-lawful L M .swap (inj₂ y) (inj₂ y') = M .swap y y'
⊎-lawful L M .exact {inj₁ _} {inj₁ _} e = cong inj₁ (L .exact e)
⊎-lawful L M .exact {inj₂ _} {inj₂ _} e = cong inj₂ (M .exact e)
⊎-lawful L M .reflex (inj₁ x) = L .reflex x
⊎-lawful L M .reflex (inj₂ y) = M .reflex y
⊎-lawful L M .trans< {inj₁ _} {inj₁ _} {inj₁ _} e e' = L .trans< e e'
⊎-lawful L M .trans< {inj₁ _} {inj₁ _} {inj₂ _} _ _  = refl
⊎-lawful L M .trans< {inj₁ _} {inj₂ _} {inj₂ _} _ _  = refl
⊎-lawful L M .trans< {inj₂ _} {inj₂ _} {inj₂ _} e e' = M .trans< e e'

List-lawful : ∀ {X} {c : X → X → Order} → Lawful c → Lawful (compareᴸ c)
List-lawful L .swap []       []       = refl
List-lawful L .swap []       (_ ∷ _)  = refl
List-lawful L .swap (_ ∷ _)  []       = refl
List-lawful {c = c} L .swap (x ∷ xs) (y ∷ ys) =
  trans (cong₂ lexᵒ (L .swap x y) (List-lawful L .swap xs ys))
        (lex-swap (c x y) (compareᴸ c xs ys))
List-lawful L .exact {[]}     {[]}     _ = refl
List-lawful L .exact {x ∷ xs} {y ∷ ys} e with lex-exact e
... | e₁ , e₂ = cong₂ _∷_ (L .exact e₁) (List-lawful L .exact e₂)
List-lawful L .reflex []       = refl
List-lawful L .reflex (x ∷ xs) = cong₂ lexᵒ (L .reflex x) (List-lawful L .reflex xs)
List-lawful L .trans< {[]}     {_ ∷ _}  {_ ∷ _}  _ _  = refl
List-lawful L .trans< {_ ∷ _}  {_ ∷ _}  {[]}     _ ()
List-lawful L .trans< {x ∷ xs} {y ∷ ys} {z ∷ zs} e e' =
  lex-trans L (List-lawful L .trans< {xs} {ys} {zs}) e e'

-- Every eternal type's comparison is lawful

compareᵈ-lawful : ∀ {A} → (et : Et A) → Lawful (compareᵈ et)
compareᵈ-lawful (Baseₑ eb)     = order-of-lawful (≺ᵇ-isStrictTotalOrder eb)
compareᵈ-lawful unitₑ          = record { swap = λ _ _ → refl ; exact = λ _ → refl
                                        ; reflex = λ _ → refl ; trans< = λ () }
compareᵈ-lawful boolₑ          = 𝔹-lawful
compareᵈ-lawful natₑ           = ℕ-lawful
compareᵈ-lawful (et₁ |×|ₑ et₂) =
  ×-lawful {et₁ = et₁} {et₂} (compareᵈ-lawful et₁) (compareᵈ-lawful et₂)
compareᵈ-lawful (et₁ |+|ₑ et₂) =
  ⊎-lawful {et₁ = et₁} {et₂} (compareᵈ-lawful et₁) (compareᵈ-lawful et₂)
compareᵈ-lawful (listₑ et)     = List-lawful (compareᵈ-lawful et)
compareᵈ-lawful emptyₑ         = record { swap = λ () ; exact = λ { {()} } ; reflex = λ ()
                                        ; trans< = λ { {()} } }

-- The strict order: `less`

_<[_]_ : ∀ {A} → ⟪ A ⟫ → Et A → ⟪ A ⟫ → Set
x <[ et ] y = compareᵈ et x y ≡ less

compareᵈ-isStrictTotalOrder : ∀ {A} → (et : Et A)
                            → IsStrictTotalOrder _≡_ (λ x y → x <[ et ] y)
compareᵈ-isStrictTotalOrder et = record
  { isStrictPartialOrder = record
      { isEquivalence = isEquivalence
      ; irrefl        = λ { {x} refl e → case (trans (sym (L .reflex x)) e) }
      ; trans         = L .trans<
      ; <-resp-≈      = (λ { refl e → e }) , (λ { refl e → e }) }
  ; compare = tri }
  where
    L = compareᵈ-lawful et

    case : equal ≡ less → ⊥
    case ()

    tri : ∀ x y → Tri (x <[ et ] y) (x ≡ y) (y <[ et ] x)
    tri x y with compareᵈ et x y in e
    ... | less    = tri< refl (λ { refl → case (trans (sym (L .reflex x)) e) })
                         (λ e' → flipless (trans (sym (L .swap x y)) e') e)
      where flipless : flipᵒ (compareᵈ et x y) ≡ less → compareᵈ et x y ≡ less → ⊥
            flipless f g rewrite g = case' f
              where case' : greater ≡ less → ⊥
                    case' ()
    ... | equal   = tri≈ (λ ()) (L .exact e) (λ e' → noteq (trans (sym (L .swap x y)) e') e)
      where noteq : flipᵒ (compareᵈ et x y) ≡ less → compareᵈ et x y ≡ equal → ⊥
            noteq f g rewrite g = case f
    ... | greater = tri> (λ ()) (λ { refl → gt≠eq (trans (sym e) (L .reflex x)) })
                         (trans (L .swap x y) (cong flipᵒ e))
      where gt≠eq : greater ≡ equal → ⊥
            gt≠eq ()

-- What the relations of `Cmp` mean

holds-eq : ∀ {A} → (et : Et A) → ∀ {x y}
         → holds eq (compareᵈ et x y) ≡ true → x ≡ y
holds-eq et {x} {y} h with compareᵈ et x y in e
... | equal = compareᵈ-lawful et .exact e

holds-gt : ∀ {A} → (et : Et A) → ∀ x y
         → holds gt (compareᵈ et x y) ≡ holds lt (compareᵈ et y x)
holds-gt et x y rewrite compareᵈ-lawful et .swap x y with compareᵈ et x y
... | less    = refl
... | equal   = refl
... | greater = refl

holds-le : ∀ {A} → (et : Et A) → ∀ {x y}
         → holds le (compareᵈ et x y) ≡ true → (x <[ et ] y) ⊎ (x ≡ y)
holds-le et {x} {y} h with compareᵈ et x y in e
... | less  = inj₁ refl
... | equal = inj₂ (compareᵈ-lawful et .exact e)
