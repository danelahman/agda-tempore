------------------------------------------------------------------
-- The order on data is a strict total order                    --
--                                                              --
-- A comparison `c` is lawful when swapping its arguments flips --
-- its outcome, `equal` is equality, and `less` is transitive.  --
-- The base types' comparisons are lawful, and lawfulness is    --
-- closed under the formers, so `compareᴰ` is lawful on the     --
-- data of every closed eternal type and `less` is a strict     --
-- total order on them (`compareᴰ-isStrictTotalOrder`). Then    --
-- `eq` holds only of equal data and `le` only of `less` or     --
-- equal data, and `gt` is `lt` with its arguments swapped      --
-- (`holds-eq`, `holds-le`, `holds-gt`).                        --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Relation.Binary.Structures using (IsStrictTotalOrder)
open import Relation.Nullary using (yes; no)

open import Language.BaseTypes using (module BaseTypes; order-of)
open import Language.Comparisons
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.OperationalSemantics.Data.Order (S : LanguageSpec) where

open LanguageSpec S
open BaseTypes BTs
  using (BaseConstants; EternalBaseType; eternalBaseType?; _≡ᵇ?_; ≺ᵇ-isStrictTotalOrder; compareᵇ)

open import PolymorphicCalculus.Syntax.Types                   S
open import PolymorphicCalculus.Hypotheses                     S
open import PolymorphicCalculus.OperationalSemantics.Reduction S using (compareᴰ)
open import PolymorphicCalculus.OperationalSemantics.Data      S

-- The comparison of data of one type, by their datums

compareᵈ : ∀ {A} → ⟪ A ⟫ → ⟪ A ⟫ → Order
compareᵈ x y = compareᴰ ⌊ x ⌋ᵈ ⌊ y ⌋ᵈ

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

-- the comparison of the constants of an eternal base type

compareᵈ-base : ∀ {b} → .(eb : EternalBaseType b) → (c c' : BaseConstants b)
              → compareᵈ (base c) (base c') ≡ compareᵇ eb c c'
compareᵈ-base {b} eb c c' with b ≡ᵇ? b
... | no ¬p = ⊥-elim (¬p refl)
... | yes refl with eternalBaseType? b
...   | yes _  = refl
...   | no ¬eb = ⊥-elim-irr (¬eb eb)

base-lawful : ∀ {b} → .(EternalBaseType b) → Lawful (compareᵈ {Base b})
base-lawful {b} eb = record
  { swap = sw ; exact = ex ; reflex = rf ; trans< = λ {x} {y} {z} → tr {x} {y} {z} }
  where
    O = order-of-lawful (≺ᵇ-isStrictTotalOrder eb)
    β = compareᵈ-base eb

    sw : ∀ (x y : ⟪ Base b ⟫) → compareᵈ y x ≡ flipᵒ (compareᵈ x y)
    sw (base c) (base c') = trans (β c' c) (trans (O .swap c c') (cong flipᵒ (sym (β c c'))))

    ex : ∀ {x y : ⟪ Base b ⟫} → compareᵈ x y ≡ equal → x ≡ y
    ex {base c} {base c'} e = cong base (O .exact (trans (sym (β c c')) e))

    rf : ∀ (x : ⟪ Base b ⟫) → compareᵈ x x ≡ equal
    rf (base c) = trans (β c c) (O .reflex c)

    tr : ∀ {x y z : ⟪ Base b ⟫} → compareᵈ x y ≡ less → compareᵈ y z ≡ less → compareᵈ x z ≡ less
    tr {base c} {base c'} {base c''} e e' =
      trans (β c c'') (O .trans< (trans (sym (β c c')) e) (trans (sym (β c' c'')) e'))

-- The formers

empty-lawful : ∀ {A} → (⟪ A ⟫ → ⊥) → Lawful (compareᵈ {A})
empty-lawful ¬x .swap x _        = ⊥-elim (¬x x)
empty-lawful ¬x .exact {x} _     = ⊥-elim (¬x x)
empty-lawful ¬x .reflex x        = ⊥-elim (¬x x)
empty-lawful ¬x .trans< {x} _ _  = ⊥-elim (¬x x)

unit-lawful : Lawful (compareᵈ {unit})
unit-lawful .swap unit unit         = refl
unit-lawful .exact {unit} {unit} _  = refl
unit-lawful .reflex unit            = refl
unit-lawful .trans< {unit} {unit} ()

𝔹-lawful : Lawful (compareᵈ {bool})
𝔹-lawful .swap (bit false) (bit false) = refl
𝔹-lawful .swap (bit false) (bit true)  = refl
𝔹-lawful .swap (bit true)  (bit false) = refl
𝔹-lawful .swap (bit true)  (bit true)  = refl
𝔹-lawful .exact {bit false} {bit false} _ = refl
𝔹-lawful .exact {bit true}  {bit true}  _ = refl
𝔹-lawful .reflex (bit false) = refl
𝔹-lawful .reflex (bit true)  = refl
𝔹-lawful .trans< {bit false} {bit true}  {bit true}  _ ()
𝔹-lawful .trans< {bit false} {bit true}  {bit false} _ ()
𝔹-lawful .trans< {bit false} {bit false} () _
𝔹-lawful .trans< {bit true}  {bit false} () _
𝔹-lawful .trans< {bit true}  {bit true}  () _

ℕ-lawful : Lawful (compareᵈ {nat})
ℕ-lawful .swap numᶻ     numᶻ     = refl
ℕ-lawful .swap numᶻ     (numˢ _) = refl
ℕ-lawful .swap (numˢ _) numᶻ     = refl
ℕ-lawful .swap (numˢ n) (numˢ m) = ℕ-lawful .swap n m
ℕ-lawful .exact {numᶻ}   {numᶻ}   _ = refl
ℕ-lawful .exact {numˢ n} {numˢ m} e = cong numˢ (ℕ-lawful .exact e)
ℕ-lawful .reflex numᶻ     = refl
ℕ-lawful .reflex (numˢ n) = ℕ-lawful .reflex n
ℕ-lawful .trans< {numᶻ}   {numˢ _} {numˢ _} _ _ = refl
ℕ-lawful .trans< {numˢ n} {numˢ m} {numˢ k} e e' = ℕ-lawful .trans< {n} {m} {k} e e'

×-lawful : ∀ {A₁ A₂} → Lawful (compareᵈ {A₁}) → Lawful (compareᵈ {A₂})
         → Lawful (compareᵈ {A₁ |×| A₂})
×-lawful L M .swap (pair x y) (pair x' y') =
  trans (cong₂ lexᵒ (L .swap x x') (M .swap y y'))
        (lex-swap (compareᵈ x x') (compareᵈ y y'))
×-lawful L M .exact {pair x y} {pair x' y'} e with lex-exact e
... | e₁ , e₂ = cong₂ pair (L .exact e₁) (M .exact e₂)
×-lawful L M .reflex (pair x y) = cong₂ lexᵒ (L .reflex x) (M .reflex y)
×-lawful L M .trans< {pair x y} {pair x' y'} {pair x'' y''} =
  lex-trans L {x} {x'} {x''} (M .trans< {y} {y'} {y''})

⊎-lawful : ∀ {A₁ A₂} → Lawful (compareᵈ {A₁}) → Lawful (compareᵈ {A₂})
         → Lawful (compareᵈ {A₁ |+| A₂})
⊎-lawful L M .swap (left x)  (left x')  = L .swap x x'
⊎-lawful L M .swap (left _)  (right _)  = refl
⊎-lawful L M .swap (right _) (left _)   = refl
⊎-lawful L M .swap (right y) (right y') = M .swap y y'
⊎-lawful L M .exact {left _}  {left _}  e = cong left (L .exact e)
⊎-lawful L M .exact {right _} {right _} e = cong right (M .exact e)
⊎-lawful L M .reflex (left x)  = L .reflex x
⊎-lawful L M .reflex (right y) = M .reflex y
⊎-lawful L M .trans< {left x}  {left x'}  {left x''}  e e' = L .trans< {x} {x'} {x''} e e'
⊎-lawful L M .trans< {left _}  {left _}  {right _} _ _  = refl
⊎-lawful L M .trans< {left _}  {right _} {right _} _ _  = refl
⊎-lawful L M .trans< {right y} {right y'} {right y''} e e' = M .trans< {y} {y'} {y''} e e'

List-lawful : ∀ {A} → Lawful (compareᵈ {A}) → Lawful (compareᵈ {list A})
List-lawful L .swap nilᵈ         nilᵈ         = refl
List-lawful L .swap nilᵈ         (consᵈ _ _)  = refl
List-lawful L .swap (consᵈ _ _)  nilᵈ         = refl
List-lawful L .swap (consᵈ x xs) (consᵈ y ys) =
  trans (cong₂ lexᵒ (L .swap x y) (List-lawful L .swap xs ys))
        (lex-swap (compareᵈ x y) (compareᵈ xs ys))
List-lawful L .exact {nilᵈ}       {nilᵈ}       _ = refl
List-lawful L .exact {consᵈ x xs} {consᵈ y ys} e with lex-exact e
... | e₁ , e₂ = cong₂ consᵈ (L .exact e₁) (List-lawful L .exact e₂)
List-lawful L .reflex nilᵈ         = refl
List-lawful L .reflex (consᵈ x xs) = cong₂ lexᵒ (L .reflex x) (List-lawful L .reflex xs)
List-lawful L .trans< {nilᵈ}       {consᵈ _ _}  {consᵈ _ _}  _ _  = refl
List-lawful L .trans< {consᵈ _ _}  {consᵈ _ _}  {nilᵈ}       _ ()
List-lawful L .trans< {consᵈ x xs} {consᵈ y ys} {consᵈ z zs} e e' =
  lex-trans L {x} {y} {z} (List-lawful L .trans< {xs} {ys} {zs}) e e'

-- The comparison of the data of every closed eternal type is lawful

compareᴰ-lawful : ∀ {A} → ∅ᴴ ⊩Et A → Lawful (compareᵈ {A})
compareᴰ-lawful (et-hyp _)    = empty-lawful λ ()
compareᴰ-lawful (et-subˡ _ _) = empty-lawful λ ()
compareᴰ-lawful (et-subʳ _ _) = empty-lawful λ ()
compareᴰ-lawful (Baseₑ eb)    = base-lawful eb
compareᴰ-lawful unitₑ         = unit-lawful
compareᴰ-lawful boolₑ         = 𝔹-lawful
compareᴰ-lawful natₑ          = ℕ-lawful
compareᴰ-lawful (e₁ |×|ₑ e₂)  = ×-lawful (compareᴰ-lawful e₁) (compareᴰ-lawful e₂)
compareᴰ-lawful (e₁ |+|ₑ e₂)  = ⊎-lawful (compareᴰ-lawful e₁) (compareᴰ-lawful e₂)
compareᴰ-lawful (listₑ e)     = List-lawful (compareᴰ-lawful e)
compareᴰ-lawful emptyₑ        = empty-lawful λ ()

-- The strict order: `less`

compareᴰ-isStrictTotalOrder : ∀ {A} → ∅ᴴ ⊩Et A
                            → IsStrictTotalOrder (_≡_ {A = ⟪ A ⟫})
                                                 (λ x y → compareᴰ ⌊ x ⌋ᵈ ⌊ y ⌋ᵈ ≡ less)
compareᴰ-isStrictTotalOrder {A} et = record
  { isStrictPartialOrder = record
      { isEquivalence = isEquivalence
      ; irrefl        = λ { {x} refl e → case (trans (sym (L .reflex x)) e) }
      ; trans         = λ {x} {y} {z} → L .trans< {x} {y} {z}
      ; <-resp-≈      = (λ { refl e → e }) , (λ { refl e → e }) }
  ; compare = tri }
  where
    L = compareᴰ-lawful et

    case : equal ≡ less → ⊥
    case ()

    tri : ∀ (x y : ⟪ A ⟫) → Tri (compareᵈ x y ≡ less) (x ≡ y) (compareᵈ y x ≡ less)
    tri x y with compareᵈ x y in e
    ... | less    = tri< refl (λ { refl → case (trans (sym (L .reflex x)) e) })
                         (λ e' → flipless (trans (sym (L .swap x y)) e') e)
      where flipless : flipᵒ (compareᵈ x y) ≡ less → compareᵈ x y ≡ less → ⊥
            flipless f g rewrite g = case' f
              where case' : greater ≡ less → ⊥
                    case' ()
    ... | equal   = tri≈ (λ ()) (L .exact e) (λ e' → noteq (trans (sym (L .swap x y)) e') e)
      where noteq : flipᵒ (compareᵈ x y) ≡ less → compareᵈ x y ≡ equal → ⊥
            noteq f g rewrite g = case f
    ... | greater = tri> (λ ()) (λ { refl → gt≠eq (trans (sym e) (L .reflex x)) })
                         (trans (L .swap x y) (cong flipᵒ e))
      where gt≠eq : greater ≡ equal → ⊥
            gt≠eq ()

-- What the relations of `Cmp` mean

holds-eq : ∀ {A} → ∅ᴴ ⊩Et A → ∀ {x y : ⟪ A ⟫}
         → holds eq (compareᵈ x y) ≡ true → x ≡ y
holds-eq et {x} {y} h with compareᵈ x y in e
... | equal = compareᴰ-lawful et .exact e

holds-gt : ∀ {A} → ∅ᴴ ⊩Et A → ∀ (x y : ⟪ A ⟫)
         → holds gt (compareᵈ x y) ≡ holds lt (compareᵈ y x)
holds-gt et x y rewrite compareᴰ-lawful et .swap x y with compareᵈ x y
... | less    = refl
... | equal   = refl
... | greater = refl

holds-le : ∀ {A} → ∅ᴴ ⊩Et A → ∀ {x y : ⟪ A ⟫}
         → holds le (compareᵈ x y) ≡ true → (compareᵈ x y ≡ less) ⊎ (x ≡ y)
holds-le et {x} {y} h with compareᵈ x y in e
... | less  = inj₁ refl
... | equal = inj₂ (compareᴰ-lawful et .exact e)
