------------------------------------------------------------------------
-- Preordered grades: grades whose order is a preorder, with equality --
-- the order's equivalence.                                           --
--                                                                    --
-- The shape is that of `Grade`, read up to the equivalence           --
--                                                                    --
--   c ≈ d   =   c ≾ d × d ≾ c                                        --
--                                                                    --
-- instead of equality: the monoid laws and the inclusion of           --
-- durations hold up to `≈`, the order is reflexive, transitive and   --
-- decidable, and there is no antisymmetry. Joins, the top, the       --
-- monotone product, its distributivity over joins and the zero-      --
-- product property of the unit are as in `Grade`. A grade whose      --
-- elements are descriptions of sets, compared by what they describe, --
-- takes this shape when the descriptions have no canonical form.     --
--                                                                    --
-- Two preordered grades over one duration monoid have a              --
-- componentwise product.                                             --
------------------------------------------------------------------------

module Syntax.Grades.Preordered where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Level using () renaming (zero to lzero)
open import Relation.Binary.Core using (Rel; _Preserves_⟶_)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Decidable)
open import Relation.Nullary using (Dec; yes; no)

open import Syntax.Durations using (Duration)

record PreorderedGrade (D : Duration) : Set₁ where
  private
    module D = Duration D

  infixl 7 _·_
  infixl 6 _⊔_
  infix  4 _≾_ _≈_

  field

    -- carrier and operations
    Carrier : Set₀
    _·_     : Carrier → Carrier → Carrier
    u       : Carrier
    _≾_     : Rel Carrier lzero
    ⊤       : Carrier
    _⊔_     : Carrier → Carrier → Carrier
    of-dur  : D.Carrier → Carrier

  -- equality is the order's equivalence
  _≈_ : Rel Carrier lzero
  c ≈ d = c ≾ d × d ≾ c

  field

    -- a monoid, up to equivalence
    ·-identityˡ : (c : Carrier) → (u · c) ≈ c
    ·-identityʳ : (c : Carrier) → (c · u) ≈ c
    ·-assoc     : (c d e : Carrier) → (c · d) · e ≈ c · (d · e)

    -- a decidable preorder
    ≾-refl  : Reflexive _≾_
    ≾-trans : Transitive _≾_
    _≾?_    : Decidable _≾_

    -- ⊤ is the greatest grade
    ≾-⊤ : (c : Carrier) → c ≾ ⊤

    -- ⊔ is a binary join
    ⊔-ubˡ : (c d : Carrier) → c ≾ c ⊔ d
    ⊔-ubʳ : (c d : Carrier) → d ≾ c ⊔ d
    ⊔-lub : {c d e : Carrier} → c ≾ e → d ≾ e → c ⊔ d ≾ e

    -- an ordered monoid; · distributes over ⊔
    ·-monoˡ-≾      : ∀ {c} → _Preserves_⟶_ (_· c) _≾_ _≾_
    ·-monoʳ-≾      : ∀ {c} → _Preserves_⟶_ (c ·_) _≾_ _≾_
    ·-distribˡ-⊔-≾ : (c d e : Carrier) → c · (d ⊔ e) ≾ (c · d) ⊔ (c · e)
    ·-distribʳ-⊔-≾ : (c d e : Carrier) → (d ⊔ e) · c ≾ (d · c) ⊔ (e · c)

    -- the unit's zero-product property
    ≾-zero-productˡ : ∀ {c d} → c · d ≾ u → c ≾ u
    ≾-zero-productʳ : ∀ {c d} → c · d ≾ u → d ≾ u

    -- durations included as a monoid morphism, up to equivalence
    of-dur-zero : of-dur D.0ᴰ ≈ u
    of-dur-plus : ∀ {τ τ'} → of-dur (τ D.+ᴰ τ') ≈ of-dur τ · of-dur τ'

  -- the equivalence is decidable
  _≈?_ : Decidable _≈_
  c ≈? d with c ≾? d | d ≾? c
  ... | yes p | yes q = yes (p , q)
  ... | no ¬p | _     = no λ r → ¬p (proj₁ r)
  ... | yes _ | no ¬q = no λ r → ¬q (proj₂ r)

  -- ⊔ is monotone
  ⊔-mono : ∀ {c c' d d'} → c ≾ c' → d ≾ d' → c ⊔ d ≾ c' ⊔ d'
  ⊔-mono {c} {c'} {d} {d'} p q =
    ⊔-lub (≾-trans p (⊔-ubˡ c' d')) (≾-trans q (⊔-ubʳ c' d'))

------------------------------------------------------------------------
-- The componentwise product

infixr 2 _×ᵖ_

_×ᵖ_ : {D : Duration} → PreorderedGrade D → PreorderedGrade D → PreorderedGrade D
G₁ ×ᵖ G₂ = record
  { Carrier = G₁.Carrier × G₂.Carrier
  ; _·_     = λ { (a , b) (c , d) → (a G₁.· c) , (b G₂.· d) }
  ; u       = G₁.u , G₂.u
  ; _≾_     = λ { (a , b) (c , d) → (a G₁.≾ c) × (b G₂.≾ d) }
  ; ⊤       = G₁.⊤ , G₂.⊤
  ; _⊔_     = λ { (a , b) (c , d) → (a G₁.⊔ c) , (b G₂.⊔ d) }
  ; of-dur  = λ τ → G₁.of-dur τ , G₂.of-dur τ
  ; ·-identityˡ = λ { (a , b) → pair (G₁.·-identityˡ a) (G₂.·-identityˡ b) }
  ; ·-identityʳ = λ { (a , b) → pair (G₁.·-identityʳ a) (G₂.·-identityʳ b) }
  ; ·-assoc     = λ { (a , b) (c , d) (e , f) → pair (G₁.·-assoc a c e) (G₂.·-assoc b d f) }
  ; ≾-refl  = G₁.≾-refl , G₂.≾-refl
  ; ≾-trans = λ { (p , q) (p' , q') → G₁.≾-trans p p' , G₂.≾-trans q q' }
  ; _≾?_    = λ { (a , b) (c , d) → both (a G₁.≾? c) (b G₂.≾? d) }
  ; ≾-⊤     = λ { (a , b) → G₁.≾-⊤ a , G₂.≾-⊤ b }
  ; ⊔-ubˡ   = λ { (a , b) (c , d) → G₁.⊔-ubˡ a c , G₂.⊔-ubˡ b d }
  ; ⊔-ubʳ   = λ { (a , b) (c , d) → G₁.⊔-ubʳ a c , G₂.⊔-ubʳ b d }
  ; ⊔-lub   = λ { (p , q) (p' , q') → G₁.⊔-lub p p' , G₂.⊔-lub q q' }
  ; ·-monoˡ-≾ = λ { (p , q) → G₁.·-monoˡ-≾ p , G₂.·-monoˡ-≾ q }
  ; ·-monoʳ-≾ = λ { (p , q) → G₁.·-monoʳ-≾ p , G₂.·-monoʳ-≾ q }
  ; ·-distribˡ-⊔-≾ = λ { (a , b) (c , d) (e , f) → G₁.·-distribˡ-⊔-≾ a c e , G₂.·-distribˡ-⊔-≾ b d f }
  ; ·-distribʳ-⊔-≾ = λ { (a , b) (c , d) (e , f) → G₁.·-distribʳ-⊔-≾ a c e , G₂.·-distribʳ-⊔-≾ b d f }
  ; ≾-zero-productˡ = λ { (p , q) → G₁.≾-zero-productˡ p , G₂.≾-zero-productˡ q }
  ; ≾-zero-productʳ = λ { (p , q) → G₁.≾-zero-productʳ p , G₂.≾-zero-productʳ q }
  ; of-dur-zero = pair G₁.of-dur-zero G₂.of-dur-zero
  ; of-dur-plus = pair G₁.of-dur-plus G₂.of-dur-plus
  }
  where
    module G₁ = PreorderedGrade G₁
    module G₂ = PreorderedGrade G₂
    pair : ∀ {a a' b b'} → a G₁.≈ a' → b G₂.≈ b' → (a G₁.≾ a' × b G₂.≾ b') × (a' G₁.≾ a × b' G₂.≾ b)
    pair (p , p') (q , q') = (p , q) , (p' , q')
    both : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
    both (yes a) (yes b) = yes (a , b)
    both (no ¬a) _       = no λ r → ¬a (proj₁ r)
    both (yes _) (no ¬b) = no λ r → ¬b (proj₂ r)
