------------------------------------------------------------------------
-- Antichains along a map of traces.                                  --
--                                                                    --
-- A map `f` from the traces of one time domain to those of another   --
-- that is a monoid morphism for sequencing and monotone for two      --
-- trace orders carries antichains to antichains: the image of an     --
-- antichain is the normal form of the images of its members. The     --
-- normal form only removes members whose closure the rest already    --
-- covers, and `f` keeps closures, so normalising before or after     --
-- mapping comes to the same (`mapˢ-n`). So the map preserves the     --
-- language product, the union, singletons and the order, as a grade  --
-- morphism between the lifted grades asks.                           --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)

import Grades.Traces.Base as Base
import Grades.Traces.Order as Order
import Grades.Traces.Reduced as Reduced

module Grades.Traces.Embedding
  {D₁ D₂ : Duration} (T₁ : TimeDomain D₁) (T₂ : TimeDomain D₂)
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (P₁ : Order.TracePartialOrder T₁ Op) (P₂ : Order.TracePartialOrder T₂ Op)
  (f : Base.Trace T₁ Op → Base.Trace T₂ Op)
  (f-∙ : (s t : Base.Trace T₁ Op)
       → f (Base._∙_ T₁ Op s t) ≡ Base._∙_ T₂ Op (f s) (f t))
  (f-mono : {s t : Base.Trace T₁ Op}
          → Order.TracePartialOrder._≼_ P₁ s t
          → Order.TracePartialOrder._≼_ P₂ (f s) (f t))
  where

open import Data.List.Base using (List; []; _∷_; [_]; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Product using (_,_)

module R₁ = Reduced T₁ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans P₁
module R₂ = Reduced T₂ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans P₂

open Order.TracePartialOrder P₁ using () renaming (_≼_ to _≼₁_)
open Order.TracePartialOrder P₂ using () renaming (_≼_ to _≼₂_; ≼-trans to ≼₂-trans)

------------------------------------------------------------------------
-- Lists of traces

mapˢ : List (Base.Trace T₁ Op) → List (Base.Trace T₂ Op)
mapˢ = map f

-- the image keeps closures

mapˢ-◃ : ∀ {v xs} → v R₁.◃ xs → f v R₂.◃ mapˢ xs
mapˢ-◃ {v} p with find p
... | y , y∈xs , y≼v = R₂.◃-intro (∈-map⁺ f y∈xs) (f-mono y≼v)

-- so mapping commutes with normalising, up to normalising the image

mapˢ-n : (xs : List (Base.Trace T₁ Op)) → R₂.n (mapˢ (R₁.n xs)) ≡ R₂.n (mapˢ xs)
mapˢ-n xs = R₂.n-ext into out
  where
    into : ∀ {v} → v R₂.◃ mapˢ (R₁.n xs) → v R₂.◃ mapˢ xs
    into = R₂.◃-⊆ (λ m → mapped m)
      where
        mapped : ∀ {w} → w ∈ mapˢ (R₁.n xs) → w ∈ mapˢ xs
        mapped m with ∈-map⁻ f m
        ... | x , x∈n , refl = ∈-map⁺ f (R₁.n-∈⁻ x∈n)

    out : ∀ {v} → v R₂.◃ mapˢ xs → v R₂.◃ mapˢ (R₁.n xs)
    out p with find p
    ... | y , y∈ , y≼v with ∈-map⁻ f y∈
    ...   | x , x∈xs , refl =
            Any.map (λ z≼fx → ≼₂-trans z≼fx y≼v)
                    (mapˢ-◃ (R₁.n-◃⁻ xs (R₁.◃-∈ x∈xs)))

-- and is a morphism for the language product

mapˢ-·ˢ : (xs ys : List (Base.Trace T₁ Op))
        → mapˢ (xs R₁.·ˢ ys) ≡ mapˢ xs R₂.·ˢ mapˢ ys
mapˢ-·ˢ []       ys = refl
mapˢ-·ˢ (x ∷ xs) ys =
  trans (map-++ f (map (Base._∙_ T₁ Op x) ys) (xs R₁.·ˢ ys))
        (cong₂ _++_ (row ys) (mapˢ-·ˢ xs ys))
  where
    row : ∀ ys → map f (map (Base._∙_ T₁ Op x) ys) ≡ map (Base._∙_ T₂ Op (f x)) (map f ys)
    row []       = refl
    row (y ∷ ys) = cong₂ _∷_ (f-∙ x y) (row ys)

private
  map-ne : ∀ {xs} → R₁.NonEmpty xs → R₂.NonEmpty (mapˢ xs)
  map-ne {x ∷ xs} _ = _

------------------------------------------------------------------------
-- Antichains

mapᴬ : R₁.Antichain → R₂.Antichain
mapᴬ P = R₂.acSet (mapˢ (R₁.traces P)) (map-ne (R₁.nonempty P))

mapᴬ-· : (P Q : R₁.Antichain) → mapᴬ (P R₁.· Q) ≡ mapᴬ P R₂.· mapᴬ Q
mapᴬ-· P Q =
  R₂.ac-ext
    (trans (mapˢ-n (R₁.traces P R₁.·ˢ R₁.traces Q))
           (trans (cong R₂.n (mapˢ-·ˢ (R₁.traces P) (R₁.traces Q)))
                  (sym (R₂.n-·ˢ (mapˢ (R₁.traces P)) (mapˢ (R₁.traces Q))))))

mapᴬ-⊔ : (P Q : R₁.Antichain) → mapᴬ (P R₁.⊔ Q) ≡ mapᴬ P R₂.⊔ mapᴬ Q
mapᴬ-⊔ P Q =
  R₂.ac-ext
    (trans (mapˢ-n (R₁.traces P ++ R₁.traces Q))
           (trans (cong R₂.n (map-++ f (R₁.traces P) (R₁.traces Q)))
                  (sym (R₂.n-++ (mapˢ (R₁.traces P)) (mapˢ (R₁.traces Q))))))

mapᴬ-singleton : (t : Base.Trace T₁ Op) → mapᴬ (R₁.singleton t) ≡ R₂.singleton (f t)
mapᴬ-singleton t =
  R₂.ac-ext (R₂.n-reduced-id [ f t ] _ (R₂.singleton-reduced (f t)))

mapᴬ-mono : {P Q : R₁.Antichain} → P R₁.≾ Q → mapᴬ P R₂.≾ mapᴬ Q
mapᴬ-mono {P} {Q} rel = R₂.◃-≾ˢ step
  where
    step : ∀ {v} → v ∈ R₂.traces (mapᴬ P) → v R₂.◃ R₂.traces (mapᴬ Q)
    step m with ∈-map⁻ f (R₂.n-∈⁻ m)
    ... | p , p∈P , refl =
          R₂.n-◃⁻ (mapˢ (R₁.traces Q)) (mapˢ-◃ (R₁.≾ˢ-◃ rel p∈P))
