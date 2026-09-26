------------------------------------------------------------------
-- Values for one unknown, read off the orderings it is in        --
--                                                                --
-- Over the expressions of one grade sort, an unknown `v` and a   --
-- list of orderings. Each rule gives `v` a value where the       --
-- orderings are shaped for it:                                   --
--   * lowering: every ordering holds trivially, has `v` on no    --
--     right side, or is `x ≾ v` with `x` free of `v` (a bound    --
--     below, `Lows`); the value is the join of the bounds, or,   --
--     with none, a least element;                                --
--   * the upper bound: every ordering holds trivially, has `v`   --
--     on no left side, or is `v ≾ x'` with `x'` the bound `U` or --
--     decided (from no hypotheses) above it, `U` free of `v`     --
--     (`Ups`); the value is `U`;                                 --
--   * the top: `v` on no left side (`FreeL`);                    --
--   * an equal value, found by the caller.                       --
-- Which unknowns may move, in which order, and what else a value --
-- must respect are the caller's.                                 --
--                                                                --
-- Contract. The orderings are read through an interpretation of  --
-- the sides before and after the assignment (`f₀`, `f₁`) into a  --
-- preorder, agreeing where `v` does not occur: at an instance    --
-- (`Localise`), or by entailment along the assignment            --
-- (`Eliminate`). Each value keeps every ordering: lowering and   --
-- the least element where they lie below `v` (`lower-keeps`),    --
-- the upper bound and the top where they lie above it            --
-- (`raise-keeps`, `raise-free`), an equal value always           --
-- (`equal-keeps`); an unknown on no right side survives lowering --
-- (`lower-free`). Lowering is principal: each bound is an        --
-- ordering below `v` (`src`), so wherever the orderings hold     --
-- their join lies below `v` (`joinₑ-lub⊩`). That the upper bound --
-- and the top are least is not claimed.                          --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; true; false) renaming (Bool to 𝔹)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (Dec; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Bounds (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-e; occᵉ-r; occʳ-r)
open import TypeInference.SolverImpl.Normal      S using (decide≾ᵣ; decide≾ₑ)

isFalse : (b : 𝔹) → Maybe (b ≡ false)
isFalse false = just refl
isFalse true  = nothing

private
  ∨-false : (b b' : 𝔹) → b ∨ b' ≡ false → (b ≡ false) × (b' ≡ false)
  ∨-false false b' q = refl , q
  ∨-false true  b' ()

------------------------------------------------------------------------
-- How `v` occurs in a list of orderings: an ordering holds at every
-- instance, or `v` is absent from its right (left) side

module Sides {X : Set} (_≟_ : Decidable (_≡_ {A = X})) (occ : X → 𝔹) where

  FreeR : X × X → Set
  FreeR (x , x') = (x ≡ x') ⊎ (occ x' ≡ false)

  FreeL : X × X → Set
  FreeL (x , x') = (x ≡ x') ⊎ (occ x ≡ false)

  freeRs : (l : List (X × X)) → Maybe (∀ {a} → a ∈ l → FreeR a)
  freeRs []             = just (λ ())
  freeRs ((x , x') ∷ l) = go (freeRs l) (x ≟ x') (isFalse (occ x'))
    where
      go : Maybe (∀ {a} → a ∈ l → FreeR a) → _ → Maybe (occ x' ≡ false)
         → Maybe (∀ {a} → a ∈ (x , x') ∷ l → FreeR a)
      go nothing  _        _        = nothing
      go (just f) (yes e)  _        = just (λ { (here refl) → inj₁ e ; (there m) → f m })
      go (just f) (no _)   (just q) = just (λ { (here refl) → inj₂ q ; (there m) → f m })
      go (just f) (no _)   nothing  = nothing

  freeLs : (l : List (X × X)) → Maybe (∀ {a} → a ∈ l → FreeL a)
  freeLs []             = just (λ ())
  freeLs ((x , x') ∷ l) = go (freeLs l) (x ≟ x') (isFalse (occ x))
    where
      go : Maybe (∀ {a} → a ∈ l → FreeL a) → _ → Maybe (occ x ≡ false)
         → Maybe (∀ {a} → a ∈ (x , x') ∷ l → FreeL a)
      go nothing  _        _        = nothing
      go (just f) (yes e)  _        = just (λ { (here refl) → inj₁ e ; (there m) → f m })
      go (just f) (no _)   (just q) = just (λ { (here refl) → inj₂ q ; (there m) → f m })
      go (just f) (no _)   nothing  = nothing

  -- The orderings read before (`f₀`) and after (`f₁`) an assignment to
  -- `v`, the two agreeing where `v` does not occur

  module Keep {Y : Set} (_⊑_ : Y → Y → Set)
              (⊑-refl : ∀ {y} → y ⊑ y) (⊑-trans : ∀ {y y' y''} → y ⊑ y' → y' ⊑ y'' → y ⊑ y'')
              (f₀ f₁ : X → Y) (same : ∀ {x} → occ x ≡ false → f₁ x ≡ f₀ x) where

    Holds : (X → Y) → List (X × X) → Set
    Holds f l = ∀ {x x'} → (x , x') ∈ l → f x ⊑ f x'

    -- Lowering keeps an ordering with `v` on no right side, raising one
    -- with `v` on no left side

    lowerR : ∀ {x x'} → FreeR (x , x') → (∀ y → f₁ y ⊑ f₀ y) → f₀ x ⊑ f₀ x' → f₁ x ⊑ f₁ x'
    lowerR (inj₁ refl) lo h = ⊑-refl
    lowerR {x} (inj₂ q) lo h = ⊑-trans (lo x) (subst (f₀ x ⊑_) (sym (same q)) h)

    raiseL : ∀ {x x'} → FreeL (x , x') → (∀ y → f₀ y ⊑ f₁ y) → f₀ x ⊑ f₀ x' → f₁ x ⊑ f₁ x'
    raiseL (inj₁ refl) hi h = ⊑-refl
    raiseL {x' = x'} (inj₂ q) hi h = ⊑-trans (subst (_⊑ f₀ x') (sym (same q)) h) (hi x')

    lower-free : ∀ {l} → (∀ {a} → a ∈ l → FreeR a) → (∀ y → f₁ y ⊑ f₀ y)
               → Holds f₀ l → Holds f₁ l
    lower-free fr lo h m = lowerR (fr m) lo (h m)

    raise-free : ∀ {l} → (∀ {a} → a ∈ l → FreeL a) → (∀ y → f₀ y ⊑ f₁ y)
               → Holds f₀ l → Holds f₁ l
    raise-free fl hi h m = raiseL (fl m) hi (h m)

    -- A value equal to `v` keeps every ordering

    equal-keeps : ∀ {l} → (∀ y → f₁ y ⊑ f₀ y) → (∀ y → f₀ y ⊑ f₁ y)
                → Holds f₀ l → Holds f₁ l
    equal-keeps lo hi h {x} {x'} m = ⊑-trans (lo x) (⊑-trans (h m) (hi x'))

------------------------------------------------------------------------
-- The bounds of `v`, below and above, under a decided order `_≤_`

module Bounds {X : Set} (_≟_ : Decidable (_≡_ {A = X})) (occ : X → 𝔹) (v : X)
              (_≤_ : X → X → Set) (dec≤ : (x y : X) → Maybe (x ≤ y)) where

  open Sides _≟_ occ public

  -- The bounds below, each free of `v`; every other ordering has `v`
  -- on no right side

  record Lows (l : List (X × X)) : Set where
    constructor lows
    field
      bnds  : List X
      rest  : List (X × X)
      cls   : ∀ {x x'} → (x , x') ∈ l → ((x' ≡ v) × (x ∈ bnds)) ⊎ ((x , x') ∈ rest)
      src   : ∀ {x} → x ∈ bnds → (x , v) ∈ l
      rest⊆ : ∀ {a} → a ∈ rest → a ∈ l
      restR : ∀ {a} → a ∈ rest → FreeR a

  open Lows public

  lowsOf : (l : List (X × X)) → Maybe (Lows l)
  lowsOf []             = just (lows [] [] (λ ()) (λ ()) (λ ()) (λ ()))
  lowsOf ((x , x') ∷ l) = go (lowsOf l) (x' ≟ v) (isFalse (occ x)) (x ≟ x') (isFalse (occ x'))
    where
      toRest : Lows l → FreeR (x , x') → Lows ((x , x') ∷ l)
      toRest (lows L r c s sb f) fr =
        lows L ((x , x') ∷ r)
             (λ { (here refl) → inj₂ (here refl)
                ; (there m)   → [ inj₁ , (λ m' → inj₂ (there m')) ]′ (c m) })
             (λ m → there (s m))
             (λ { (here refl) → here refl ; (there m) → there (sb m) })
             (λ { (here refl) → fr ; (there m) → f m })

      go : Maybe (Lows l) → Dec (x' ≡ v) → Maybe (occ x ≡ false) → Dec (x ≡ x')
         → Maybe (occ x' ≡ false) → Maybe (Lows ((x , x') ∷ l))
      go nothing                    _        _        _       _        = nothing
      go (just (lows L r c s sb f)) (yes e)  (just _) _       _        =
        just (lows (x ∷ L) r
                   (λ { (here refl) → inj₁ (e , here refl)
                      ; (there m)   → [ (λ { (e' , mb) → inj₁ (e' , there mb) })
                                      , (λ m' → inj₂ m') ]′ (c m) })
                   (λ { (here refl) → here (cong (x ,_) (sym e)) ; (there m) → there (s m) })
                   (λ m → there (sb m)) f)
      go (just lw)                  _        _        (yes e) _        = just (toRest lw (inj₁ e))
      go (just lw)                  _        _        (no _)  (just q) = just (toRest lw (inj₂ q))
      go (just lw)                  _        _        (no _)  nothing  = nothing

  -- A bound above: every ordering with `v` on its left is `v ≾ U`, or
  -- has a right side decided above `U`; every other has `v` on no left
  -- side

  record Capped (U : X) (l : List (X × X)) : Set where
    constructor capped
    field
      restᵘ  : List (X × X)
      clsᵘ   : ∀ {x x'} → (x , x') ∈ l
             → ((x ≡ v) × ((x' ≡ U) ⊎ (U ≤ x'))) ⊎ ((x , x') ∈ restᵘ)
      rest⊆ᵘ : ∀ {a} → a ∈ restᵘ → a ∈ l
      restL  : ∀ {a} → a ∈ restᵘ → FreeL a

  open Capped public

  record Ups (l : List (X × X)) : Set where
    constructor ups
    field
      cap  : X
      capF : occ cap ≡ false
      srcᵘ : (v , cap) ∈ l
      capd : Capped cap l

  open Ups public

  -- The upper bounds free of `v`, each a candidate

  capsOf : (l : List (X × X)) → List (Σ[ U ∈ X ] ((occ U ≡ false) × ((v , U) ∈ l)))
  capsOf []             = []
  capsOf ((x , x') ∷ l) = go (x ≟ v) (isFalse (occ x')) (capsOf l)
    where
      shift : List (Σ[ U ∈ X ] ((occ U ≡ false) × ((v , U) ∈ l)))
            → List (Σ[ U ∈ X ] ((occ U ≡ false) × ((v , U) ∈ (x , x') ∷ l)))
      shift []                   = []
      shift ((U , q , m) ∷ us) = (U , q , there m) ∷ shift us

      go : _ → Maybe (occ x' ≡ false) → List (Σ[ U ∈ X ] ((occ U ≡ false) × ((v , U) ∈ l)))
         → List (Σ[ U ∈ X ] ((occ U ≡ false) × ((v , U) ∈ (x , x') ∷ l)))
      go (yes e) (just q) us = (x' , q , here (cong (_, x') (sym e))) ∷ shift us
      go _       _        us = shift us

  upsAt : (U : X) → (l : List (X × X)) → Maybe (Capped U l)
  upsAt U []             = just (capped [] (λ ()) (λ ()) (λ ()))
  upsAt U ((x , x') ∷ l) = go (upsAt U l) (x ≟ x') (isFalse (occ x)) (x ≟ v)
    where
      above : Dec (x' ≡ U) → Maybe ((x' ≡ U) ⊎ (U ≤ x'))
      above (yes e) = just (inj₁ e)
      above (no _) with dec≤ U x'
      ... | just p  = just (inj₂ p)
      ... | nothing = nothing

      toRest : Capped U l → FreeL (x , x') → Capped U ((x , x') ∷ l)
      toRest (capped r c sb f) fl =
        capped ((x , x') ∷ r)
               (λ { (here refl) → inj₂ (here refl)
                  ; (there m)   → [ inj₁ , (λ m' → inj₂ (there m')) ]′ (c m) })
               (λ { (here refl) → here refl ; (there m) → there (sb m) })
               (λ { (here refl) → fl ; (there m) → f m })

      toCap : Capped U l → x ≡ v → (x' ≡ U) ⊎ (U ≤ x') → Capped U ((x , x') ∷ l)
      toCap (capped r c sb f) e u =
        capped r (λ { (here refl) → inj₁ (e , u)
                    ; (there m)   → [ inj₁ , (λ m' → inj₂ m') ]′ (c m) })
               (λ m → there (sb m)) f

      go : Maybe (Capped U l) → Dec (x ≡ x') → Maybe (occ x ≡ false) → Dec (x ≡ v)
         → Maybe (Capped U ((x , x') ∷ l))
      go nothing  _       _        _       = nothing
      go (just c) (yes e) _        _       = just (toRest c (inj₁ e))
      go (just c) (no _)  (just q) _       = just (toRest c (inj₂ q))
      go (just c) (no _)  nothing  (yes e) with above (x' ≟ U)
      ... | just u  = just (toCap c e u)
      ... | nothing = nothing
      go (just c) (no _)  nothing  (no _)  = nothing

  -- The upper bound: the first candidate below every other one

  upsOf : (l : List (X × X)) → Maybe (Ups l)
  upsOf l = go (capsOf l)
    where
      go : List (Σ[ U ∈ X ] ((occ U ≡ false) × ((v , U) ∈ l))) → Maybe (Ups l)
      go []                   = nothing
      go ((U , q , m) ∷ us) with upsAt U l
      ... | just c  = just (ups U q m c)
      ... | nothing = go us

  -- The rules keep the orderings

  module Keepᵇ {Y : Set} (_⊑_ : Y → Y → Set)
               (⊑-refl : ∀ {y} → y ⊑ y) (⊑-trans : ∀ {y y' y''} → y ⊑ y' → y' ⊑ y'' → y ⊑ y'')
               (f₀ f₁ : X → Y) (same : ∀ {x} → occ x ≡ false → f₁ x ≡ f₀ x) where

    open Keep _⊑_ ⊑-refl ⊑-trans f₀ f₁ same public

    -- Lowering to a value above every bound (the join, or a least
    -- element where there is none)

    lower-keeps : ∀ {l} → (lw : Lows l) → (∀ y → f₁ y ⊑ f₀ y)
                → (∀ {x} → x ∈ bnds lw → f₀ x ⊑ f₁ v) → Holds f₀ l → Holds f₁ l
    lower-keeps lw lo ub h m with cls lw m
    ... | inj₁ (refl , mb) = ⊑-trans (lo _) (ub mb)
    ... | inj₂ mr          = lowerR (restR lw mr) lo (h m)

    -- Raising to the upper bound

    raise-keeps : ∀ {l} → (up : Ups l) → (∀ y → f₀ y ⊑ f₁ y) → f₁ v ⊑ f₁ (cap up)
                → (∀ {y y'} → y ≤ y' → f₁ y ⊑ f₁ y') → Holds f₀ l → Holds f₁ l
    raise-keeps up hi hit dec h m with clsᵘ (capd up) m
    ... | inj₁ (refl , inj₁ refl) = hit
    ... | inj₁ (refl , inj₂ p)    = ⊑-trans hit (dec p)
    ... | inj₂ mr                 = raiseL (restL (capd up) mr) hi (h m)

------------------------------------------------------------------------
-- Grade expressions

-- The two sorts, the order decided from no hypotheses; an effect
-- unknown in resource expressions

module Bᵉ {Ψ} (k : EVar Ψ) =
  Bounds (_≟ᵉ_ {Ψ}) (occᵉ-e {Ψ} k) (evar k) (∅ᴴ ⊩_≾̂ₑ_) (decide≾ₑ {Q = ∅ᴴ})
module Bᵉʳ {Ψ} (k : EVar Ψ) = Sides (_≟ʳ_ {Ψ}) (occᵉ-r {Ψ} k)
module Bʳ {Ψ} (k : RVar Ψ) =
  Bounds (_≟ʳ_ {Ψ}) (occʳ-r {Ψ} k) (rvar k) (∅ᴴ ⊩_≾̂ᵣ_) (decide≾ᵣ {Q = ∅ᴴ})

-- An assignment leaves alone what the assigned unknown does not occur in

updᵉ-e : ∀ {Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → (ε : EExp Ψ)
       → occᵉ-e k ε ≡ false → ε [ updᵉ k b ]ᵉ ≡ ε
updᵉ-e k b (evar i)   q = updᵉ-miss k b i q
updᵉ-e k b (econst c) q = refl
updᵉ-e k b (ε ·̂ₑ ε')  q with ∨-false (occᵉ-e k ε) (occᵉ-e k ε') q
... | q₁ , q₂ = cong₂ _·̂ₑ_ (updᵉ-e k b ε q₁) (updᵉ-e k b ε' q₂)
updᵉ-e k b (ε ⊔̂ₑ ε')  q with ∨-false (occᵉ-e k ε) (occᵉ-e k ε') q
... | q₁ , q₂ = cong₂ _⊔̂ₑ_ (updᵉ-e k b ε q₁) (updᵉ-e k b ε' q₂)

updᵉ-r : ∀ {Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → (ρ : RExp Ψ)
       → occᵉ-r k ρ ≡ false → ρ [ updᵉ k b ]ʳ ≡ ρ
updᵉ-r k b (rvar i)   q = refl
updᵉ-r k b (rconst c) q = refl
updᵉ-r k b (ρ ·̂ᵣ ρ')  q with ∨-false (occᵉ-r k ρ) (occᵉ-r k ρ') q
... | q₁ , q₂ = cong₂ _·̂ᵣ_ (updᵉ-r k b ρ q₁) (updᵉ-r k b ρ' q₂)
updᵉ-r k b (ρ ⊔̂ᵣ ρ')  q with ∨-false (occᵉ-r k ρ) (occᵉ-r k ρ') q
... | q₁ , q₂ = cong₂ _⊔̂ᵣ_ (updᵉ-r k b ρ q₁) (updᵉ-r k b ρ' q₂)
updᵉ-r k b ∣ ε ∣̂ᵉ     q = cong ∣_∣̂ᵉ (updᵉ-e k b ε q)

updʳ-r : ∀ {Ψ} → (k : RVar Ψ) → (b : RExp Ψ) → (ρ : RExp Ψ)
       → occʳ-r k ρ ≡ false → ρ [ updʳ k b ]ʳ ≡ ρ
updʳ-r k b (rvar i)   q = updʳ-miss k b i q
updʳ-r k b (rconst c) q = refl
updʳ-r k b (ρ ·̂ᵣ ρ')  q with ∨-false (occʳ-r k ρ) (occʳ-r k ρ') q
... | q₁ , q₂ = cong₂ _·̂ᵣ_ (updʳ-r k b ρ q₁) (updʳ-r k b ρ' q₂)
updʳ-r k b (ρ ⊔̂ᵣ ρ')  q with ∨-false (occʳ-r k ρ) (occʳ-r k ρ') q
... | q₁ , q₂ = cong₂ _⊔̂ᵣ_ (updʳ-r k b ρ q₁) (updʳ-r k b ρ' q₂)
updʳ-r k b ∣ ε ∣̂ᵉ     q = cong ∣_∣̂ᵉ (updʳ-e k b ε)

-- The join of a non-empty list of bounds, its head named so that a
-- lone bound is its own join and folded to the left so that the join
-- reads in the order the bounds were met, and its least upper bound

joinₑ : ∀ {Θ} → EExp Θ → List (EExp Θ) → EExp Θ
joinₑ ε []        = ε
joinₑ ε (ε' ∷ εs) = joinₑ (ε ⊔̂ₑ ε') εs

joinₑ-ub⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (τ : Subst Ψ Ψ') → (x₀ : EExp Ψ) → (xs : List (EExp Ψ))
          → ∀ {x} → x ∈ x₀ ∷ xs → Q ⊩ x [ τ ]ᵉ ≾̂ₑ joinₑ x₀ xs [ τ ]ᵉ
joinₑ-ub⊩ τ x₀ []        (here refl) = ⊩≾̂ₑ-refl
joinₑ-ub⊩ τ x₀ (x₁ ∷ xs) (here refl) = transₑ ⊔-ubˡₑ (joinₑ-ub⊩ τ (x₀ ⊔̂ₑ x₁) xs (here refl))
joinₑ-ub⊩ τ x₀ (x₁ ∷ xs) (there (here refl)) =
  transₑ ⊔-ubʳₑ (joinₑ-ub⊩ τ (x₀ ⊔̂ₑ x₁) xs (here refl))
joinₑ-ub⊩ τ x₀ (x₁ ∷ xs) (there (there m)) = joinₑ-ub⊩ τ (x₀ ⊔̂ₑ x₁) xs (there m)

joinₑ-lub⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {y : EExp Ψ'} → (τ : Subst Ψ Ψ')
           → (x₀ : EExp Ψ) → (xs : List (EExp Ψ))
           → (∀ {x} → x ∈ x₀ ∷ xs → Q ⊩ x [ τ ]ᵉ ≾̂ₑ y)
           → Q ⊩ joinₑ x₀ xs [ τ ]ᵉ ≾̂ₑ y
joinₑ-lub⊩ τ x₀ []        k = k (here refl)
joinₑ-lub⊩ τ x₀ (x₁ ∷ xs) k =
  joinₑ-lub⊩ τ (x₀ ⊔̂ₑ x₁) xs
    (λ { (here refl) → ⊔-lubₑ (k (here refl)) (k (there (here refl)))
       ; (there m)   → k (there (there m)) })

joinᵣ : ∀ {Θ} → RExp Θ → List (RExp Θ) → RExp Θ
joinᵣ ρ []        = ρ
joinᵣ ρ (ρ' ∷ ρs) = joinᵣ (ρ ⊔̂ᵣ ρ') ρs

joinᵣ-ub⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (τ : Subst Ψ Ψ') → (x₀ : RExp Ψ) → (xs : List (RExp Ψ))
          → ∀ {x} → x ∈ x₀ ∷ xs → Q ⊩ x [ τ ]ʳ ≾̂ᵣ joinᵣ x₀ xs [ τ ]ʳ
joinᵣ-ub⊩ τ x₀ []        (here refl) = ⊩≾̂ᵣ-refl
joinᵣ-ub⊩ τ x₀ (x₁ ∷ xs) (here refl) = transᵣ ⊔-ubˡᵣ (joinᵣ-ub⊩ τ (x₀ ⊔̂ᵣ x₁) xs (here refl))
joinᵣ-ub⊩ τ x₀ (x₁ ∷ xs) (there (here refl)) =
  transᵣ ⊔-ubʳᵣ (joinᵣ-ub⊩ τ (x₀ ⊔̂ᵣ x₁) xs (here refl))
joinᵣ-ub⊩ τ x₀ (x₁ ∷ xs) (there (there m)) = joinᵣ-ub⊩ τ (x₀ ⊔̂ᵣ x₁) xs (there m)

joinᵣ-lub⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {y : RExp Ψ'} → (τ : Subst Ψ Ψ')
           → (x₀ : RExp Ψ) → (xs : List (RExp Ψ))
           → (∀ {x} → x ∈ x₀ ∷ xs → Q ⊩ x [ τ ]ʳ ≾̂ᵣ y)
           → Q ⊩ joinᵣ x₀ xs [ τ ]ʳ ≾̂ᵣ y
joinᵣ-lub⊩ τ x₀ []        k = k (here refl)
joinᵣ-lub⊩ τ x₀ (x₁ ∷ xs) k =
  joinᵣ-lub⊩ τ (x₀ ⊔̂ᵣ x₁) xs
    (λ { (here refl) → ⊔-lubᵣ (k (here refl)) (k (there (here refl)))
       ; (there m)   → k (there (there m)) })
