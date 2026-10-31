------------------------------------------------------------------------
-- Grade morphisms between lifted trace grades.                       --
--                                                                    --
-- A map `f` of traces between two time domains, a monoid morphism    --
-- that sends the pure delay by `τ` to the pure delay by `h τ` for a  --
-- morphism `h` of durations, lifts to grade morphisms along `h`      --
-- between the lifted grades built over the two time domains, as soon --
-- as it is monotone for the trace orders they are built at. The      --
-- carriers are mapped through `Traces.Embedding`; the two-sided      --
-- grade's coherence field is carried by mapping the witnessing run.  --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Data.Product using (Σ; _×_)
open import Relation.Nullary using (Dec)

open import Grades.Durations using (Duration; TimeDomain; _→ᴰ_)

import Grades.Traces.Base as Base
import Grades.Traces.Order as Order

module Grades.Examples.Traces.Lifted.Morphism
  {D₁ D₂ : Duration} (T₁ : TimeDomain D₁) (T₂ : TimeDomain D₂) (h : D₁ →ᴰ D₂)
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (f : Base.Trace T₁ Op → Base.Trace T₂ Op)
  (f-∙ : (s t : Base.Trace T₁ Op)
       → f (Base._∙_ T₁ Op s t) ≡ Base._∙_ T₂ Op (f s) (f t))
  (f-ε : f Base.ε ≡ Base.ε)
  (f-⟨⟩ : (τ : Duration.Carrier D₁)
        → f (Base.⟨_⟩ T₁ Op τ) ≡ Base.⟨_⟩ T₂ Op (_→ᴰ_.map h τ))
  where

open import Data.List.Base using (List; map)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import Grades.Base using (strictᵍ; Grade; GradeMorphism; StrictMorphism)

import Grades.Traces.Embedding as Embedding
import Grades.Traces.Durations as Dur
import Grades.Examples.Traces.Lifted.LeftSided as LeftSided
import Grades.Examples.Traces.Lifted.RightSided as RightSided
import Grades.Examples.Traces.Lifted.TwoSided as TwoSided

------------------------------------------------------------------------
-- Lower bounds

module Left (O₁ : Order.TraceOrder T₁ Op) (O₂ : Order.TraceOrder T₂ Op)
  (f-mono : {s t : Base.Trace T₁ Op}
          → Order.TraceOrder._≼_ O₁ s t → Order.TraceOrder._≼_ O₂ (f s) (f t))
  where

  private
    module L₁ = LeftSided T₁ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans O₁
    module L₂ = LeftSided T₂ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans O₂
    module E = Embedding T₁ T₂ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
                 (Order.TraceOrder.base O₁) (Order.TraceOrder.base O₂) f f-∙ f-mono

  left-sided→ˢ : StrictMorphism h L₁.left-sided L₂.left-sided

  left-sided→ : GradeMorphism h L₁.left-sided L₂.left-sided
  left-sided→ = strictᵍ left-sided→ˢ

  left-sided→ˢ = record
    { map          = E.mapᴬ
    ; map-monotone = λ {P} {Q} → E.mapᴬ-mono {P} {Q}
    ; map-u        = trans (E.mapᴬ-singleton _) (cong L₂.singleton f-ε)
    ; map-·        = λ {P} {Q} → E.mapᴬ-· P Q
    ; map-⊤        = trans (E.mapᴬ-singleton _) (cong L₂.singleton f-ε)
    ; map-⊔        = λ {P} {Q} → E.mapᴬ-⊔ P Q
    ; map-of-dur   = λ {τ} → trans (E.mapᴬ-singleton _) (cong L₂.singleton (f-⟨⟩ τ))
    }

------------------------------------------------------------------------
-- Upper bounds

module Right (O₁ : Order.TraceOrder T₁ Op) (O₂ : Order.TraceOrder T₂ Op)
  (f-mono : {s t : Base.Trace T₁ Op}
          → Order.TraceOrder._≼_ O₁ s t → Order.TraceOrder._≼_ O₂ (f s) (f t))
  where

  module R₁ = RightSided T₁ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans O₁
  module R₂ = RightSided T₂ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans O₂
  module E = Embedding T₁ T₂ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
                 (Order.flipᵖ T₁ Op (Order.TraceOrder.base O₁))
                 (Order.flipᵖ T₂ Op (Order.TraceOrder.base O₂)) f f-∙ f-mono

  mapᵇ : R₁.Bounds → R₂.Bounds
  mapᵇ (R₁.within P) = R₂.within (E.mapᴬ P)
  mapᵇ R₁.unbounded  = R₂.unbounded

  mapᵇ-mono : {P Q : R₁.Bounds} → P R₁.≾ Q → mapᵇ P R₂.≾ mapᵇ Q
  mapᵇ-mono {R₁.within P} {R₁.within Q} r = E.mapᴬ-mono {P} {Q} r
  mapᵇ-mono {R₁.within _} {R₁.unbounded} _ = tt
  mapᵇ-mono {R₁.unbounded} {R₁.unbounded} _ = tt

  mapᵇ-· : (P Q : R₁.Bounds) → mapᵇ (P R₁.·ᵇ Q) ≡ mapᵇ P R₂.·ᵇ mapᵇ Q
  mapᵇ-· (R₁.within P) (R₁.within Q) = cong R₂.within_ (E.mapᴬ-· P Q)
  mapᵇ-· (R₁.within _) R₁.unbounded  = refl
  mapᵇ-· R₁.unbounded  _             = refl

  mapᵇ-⊔ : (P Q : R₁.Bounds) → mapᵇ (P R₁.⊔ᵇ Q) ≡ mapᵇ P R₂.⊔ᵇ mapᵇ Q
  mapᵇ-⊔ (R₁.within P) (R₁.within Q) = cong R₂.within_ (E.mapᴬ-⊔ P Q)
  mapᵇ-⊔ (R₁.within _) R₁.unbounded  = refl
  mapᵇ-⊔ R₁.unbounded  _             = refl

  right-sided→ˢ : StrictMorphism h R₁.right-sided R₂.right-sided

  right-sided→ : GradeMorphism h R₁.right-sided R₂.right-sided
  right-sided→ = strictᵍ right-sided→ˢ

  right-sided→ˢ = record
    { map          = mapᵇ
    ; map-monotone = λ {P} {Q} → mapᵇ-mono {P} {Q}
    ; map-u        = cong R₂.within_
                       (trans (E.mapᴬ-singleton _) (cong R₂.singleton f-ε))
    ; map-·        = λ {P} {Q} → mapᵇ-· P Q
    ; map-⊤        = refl
    ; map-⊔        = λ {P} {Q} → mapᵇ-⊔ P Q
    ; map-of-dur   = λ {τ} → cong R₂.within_
                       (trans (E.mapᴬ-singleton _) (cong R₂.singleton (f-⟨⟩ τ)))
    }

------------------------------------------------------------------------
-- Intervals

module Two
  (costˡᵒ₁ costʰⁱ₁ : Op → Duration.Carrier D₁)
  (cost-≤₁ : (o : Op) → TimeDomain._≤ᴰ_ T₁ (costˡᵒ₁ o) (costʰⁱ₁ o))
  (costˡᵒ₂ costʰⁱ₂ : Op → Duration.Carrier D₂)
  (cost-≤₂ : (o : Op) → TimeDomain._≤ᴰ_ T₂ (costˡᵒ₂ o) (costʰⁱ₂ o))
  (Oᶠ₁ Oᶜ₁ : Order.TraceOrder T₁ Op) (Oᶠ₂ Oᶜ₂ : Order.TraceOrder T₂ Op)
  (durᶠ₁ : {s t : Base.Trace T₁ Op} → Order.TraceOrder._≼_ Oᶠ₁ s t
         → TimeDomain._≤ᴰ_ T₁ (Dur.Durations.duration T₁ Op costˡᵒ₁ s)
                              (Dur.Durations.duration T₁ Op costˡᵒ₁ t))
  (durᶜ₁ : {s t : Base.Trace T₁ Op} → Order.TraceOrder._≼_ Oᶜ₁ s t
         → TimeDomain._≤ᴰ_ T₁ (Dur.Durations.duration T₁ Op costʰⁱ₁ s)
                              (Dur.Durations.duration T₁ Op costʰⁱ₁ t))
  (durᶠ₂ : {s t : Base.Trace T₂ Op} → Order.TraceOrder._≼_ Oᶠ₂ s t
         → TimeDomain._≤ᴰ_ T₂ (Dur.Durations.duration T₂ Op costˡᵒ₂ s)
                              (Dur.Durations.duration T₂ Op costˡᵒ₂ t))
  (durᶜ₂ : {s t : Base.Trace T₂ Op} → Order.TraceOrder._≼_ Oᶜ₂ s t
         → TimeDomain._≤ᴰ_ T₂ (Dur.Durations.duration T₂ Op costʰⁱ₂ s)
                              (Dur.Durations.duration T₂ Op costʰⁱ₂ t))
  (f-monoᶠ : {s t : Base.Trace T₁ Op}
           → Order.TraceOrder._≼_ Oᶠ₁ s t → Order.TraceOrder._≼_ Oᶠ₂ (f s) (f t))
  (f-monoᶜ : {s t : Base.Trace T₁ Op}
           → Order.TraceOrder._≼_ Oᶜ₁ s t → Order.TraceOrder._≼_ Oᶜ₂ (f s) (f t))
  (consistent?₁ : (p q : Base.Trace T₁ Op)
                → Dec (Σ (Base.Trace T₁ Op) (λ x → Order.TraceOrder._≼_ Oᶠ₁ p x
                                                × Order.TraceOrder._≼_ Oᶜ₁ x q)))
  (consistent?₂ : (p q : Base.Trace T₂ Op)
                → Dec (Σ (Base.Trace T₂ Op) (λ x → Order.TraceOrder._≼_ Oᶠ₂ p x
                                                × Order.TraceOrder._≼_ Oᶜ₂ x q)))
  where

  private
    module W₁ = TwoSided T₁ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ₁ costʰⁱ₁ cost-≤₁
                  Oᶠ₁ Oᶜ₁ durᶠ₁ durᶜ₁ consistent?₁
    module W₂ = TwoSided T₂ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ₂ costʰⁱ₂ cost-≤₂
                  Oᶠ₂ Oᶜ₂ durᶠ₂ durᶜ₂ consistent?₂
    module ML = Left Oᶠ₁ Oᶠ₂ f-monoᶠ
    module MR = Right Oᶜ₁ Oᶜ₂ f-monoᶜ
    module EL = Embedding T₁ T₂ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
                  (Order.TraceOrder.base Oᶠ₁) (Order.TraceOrder.base Oᶠ₂) f f-∙ f-monoᶠ
    module ER = Embedding T₁ T₂ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
                  (Order.flipᵖ T₁ Op (Order.TraceOrder.base Oᶜ₁))
                  (Order.flipᵖ T₂ Op (Order.TraceOrder.base Oᶜ₂)) f f-∙ f-monoᶜ

  -- consistency survives the map: the image of the witnessing run
  -- witnesses it between the images of the witnessing pair

  map-◇ˢ₀ : {xs ys : List (Base.Trace T₁ Op)}
          → xs W₁.◇ˢ₀ ys → map f xs W₂.◇ˢ₀ map f ys
  map-◇ˢ₀ p with W₁.◇ˢ₀-elim p
  ... | W₁.witness p∈ q∈ (x , px , xq) =
        W₂.◇ˢ₀-intro (∈-map⁺ f p∈) (∈-map⁺ f q∈) (f x , f-monoᶠ px , f-monoᶜ xq)

  map-◇ˢ : {xs : List (Base.Trace T₁ Op)} {Y : MR.R₁.Bounds}
         → xs W₁.◇ˢ Y → EL.R₂.n (map f xs) W₂.◇ˢ MR.mapᵇ Y
  map-◇ˢ {xs} {MR.R₁.within Q} p =
    W₂.◇ˢ₀-n-n {map f xs} {map f (MR.R₁.traces Q)} (map-◇ˢ₀ p)
  map-◇ˢ {xs} {MR.R₁.unbounded} _ = tt

  mapᵗˢ : W₁.TwoSided → W₂.TwoSided
  mapᵗˢ i =
    W₂.[ EL.mapᴬ (W₁.lo i) , MR.mapᵇ (W₁.hi i) ]
       {map-◇ˢ {EL.R₁.traces (W₁.lo i)} {W₁.hi i} (W₁.lo◇hi i)}

  two-sided→ : GradeMorphism h W₁.two-sided W₂.two-sided
  two-sided→ = strictᵍ record
    { map          = mapᵗˢ
    ; map-monotone = λ { {i} {j} (p , q) →
                           EL.mapᴬ-mono {W₁.lo i} {W₁.lo j} p
                         , MR.mapᵇ-mono {W₁.hi i} {W₁.hi j} q }
    ; map-u        = W₂.eqᵗˢ (StrictMorphism.map-u ML.left-sided→ˢ)
                             (StrictMorphism.map-u MR.right-sided→ˢ)
    ; map-·        = λ {i} {j} → W₂.eqᵗˢ (EL.mapᴬ-· (W₁.lo i) (W₁.lo j))
                                         (MR.mapᵇ-· (W₁.hi i) (W₁.hi j))
    ; map-⊤        = W₂.eqᵗˢ (StrictMorphism.map-⊤ ML.left-sided→ˢ) refl
    ; map-⊔        = λ {i} {j} → W₂.eqᵗˢ (EL.mapᴬ-⊔ (W₁.lo i) (W₁.lo j))
                                         (MR.mapᵇ-⊔ (W₁.hi i) (W₁.hi j))
    ; map-of-dur   = λ {τ} → W₂.eqᵗˢ (StrictMorphism.map-of-dur ML.left-sided→ˢ {τ})
                                     (StrictMorphism.map-of-dur MR.right-sided→ˢ {τ})
    }
