------------------------------------------------------------------
-- The alternatives of a sum, and what grouping, folding and      --
-- pruning do to them                                             --
--                                                                --
-- Grouping keeps every alternative, each below one of the result --
-- slot by slot, a folded slot holding the join of the group's    --
-- constants. Grouping, folding and pruning keep the skeletons    --
-- among those of the alternatives they are given.                --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<ᵇ_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no)

open import Syntax.LanguageSpec

open import Util.Equality

module TypeInference.SolverImpl.Invariants.Sums (S : LanguageSpec) where

open import TypeInference.SolverImpl.Product S using (Alts; alt; _∷⁺_; _⧺_; mapᴬ; module Grouping)

------------------------------------------------------------------------
-- Membership

infix 4 _∈ᴬ_

data _∈ᴬ_ {X : Set} (x : X) : Alts X → Set where
  inAlt  : x ∈ᴬ alt x
  inHead : ∀ {s} → x ∈ᴬ (x ∷⁺ s)
  inTail : ∀ {y s} → x ∈ᴬ s → x ∈ᴬ (y ∷⁺ s)

module _ {X : Set} where

  ∈-⧺ˡ : ∀ {x : X} {s t} → x ∈ᴬ s → x ∈ᴬ (s ⧺ t)
  ∈-⧺ˡ inAlt      = inHead
  ∈-⧺ˡ inHead     = inHead
  ∈-⧺ˡ (inTail m) = inTail (∈-⧺ˡ m)

  ∈-⧺ʳ : ∀ {x : X} (s : Alts X) {t} → x ∈ᴬ t → x ∈ᴬ (s ⧺ t)
  ∈-⧺ʳ (alt y)  m = inTail m
  ∈-⧺ʳ (y ∷⁺ s) m = inTail (∈-⧺ʳ s m)

  ∈-⧺⁻ : ∀ {x : X} (s : Alts X) {t} → x ∈ᴬ (s ⧺ t) → x ∈ᴬ s ⊎ x ∈ᴬ t
  ∈-⧺⁻ (alt y)  inHead     = inj₁ inAlt
  ∈-⧺⁻ (alt y)  (inTail m) = inj₂ m
  ∈-⧺⁻ (y ∷⁺ s) inHead     = inj₁ inHead
  ∈-⧺⁻ (y ∷⁺ s) (inTail m) with ∈-⧺⁻ s m
  ... | inj₁ m' = inj₁ (inTail m')
  ... | inj₂ m' = inj₂ m'

  ∈-alt⁻ : ∀ {x y : X} → x ∈ᴬ alt y → x ≡ y
  ∈-alt⁻ inAlt = refl

module _ {X Y : Set} (f : X → Y) where

  ∈-map : ∀ {x s} → x ∈ᴬ s → f x ∈ᴬ mapᴬ f s
  ∈-map inAlt      = inAlt
  ∈-map inHead     = inHead
  ∈-map (inTail m) = inTail (∈-map m)

  ∈-map⁻ : ∀ {y} (s : Alts X) → y ∈ᴬ mapᴬ f s → Σ[ x ∈ X ] ((x ∈ᴬ s) × (y ≡ f x))
  ∈-map⁻ (alt x)  inAlt      = x , inAlt , refl
  ∈-map⁻ (x ∷⁺ s) inHead     = x , inHead , refl
  ∈-map⁻ (x ∷⁺ s) (inTail m) with ∈-map⁻ s m
  ... | x' , m' , e = x' , inTail m' , e

------------------------------------------------------------------------
-- Grouping, over an order on the constants that the join bounds

module Groups
  {X K V : Set} (_≈_ : X → X → Set)
  (≈-refl   : ∀ {a} → a ≈ a)
  (≈-sym    : ∀ {a b} → a ≈ b → b ≈ a)
  (≈-trans  : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c)
  (_∙_ _∨_  : X → X → X)
  (∙-cong   : ∀ {a a' b b'} → a ≈ a' → b ≈ b' → (a ∙ b) ≈ (a' ∙ b'))
  (∨-cong   : ∀ {a a' b b'} → a ≈ a' → b ≈ b' → (a ∨ b) ≈ (a' ∨ b'))
  (∨-idem   : ∀ {a} → (a ∨ a) ≈ a)
  (∨-comm   : ∀ {a b} → (a ∨ b) ≈ (b ∨ a))
  (∨-assoc  : ∀ {a b c} → ((a ∨ b) ∨ c) ≈ (a ∨ (b ∨ c)))
  (distribˡ : ∀ {a b c} → (a ∙ (b ∨ c)) ≈ ((a ∙ b) ∨ (a ∙ c)))
  (distribʳ : ∀ {a b c} → ((b ∨ c) ∙ a) ≈ ((b ∙ a) ∨ (c ∙ a)))
  (κ : K → X) (_⊔ᴷ_ : K → K → K)
  (κ-⊔      : ∀ {c d} → (κ c ∨ κ d) ≈ κ (c ⊔ᴷ d))
  (_≟ᴷ_     : DecidableEquality K)
  (ν : V → X) (_≟ⱽ_ : DecidableEquality V) (_<ⱽ_ : V → V → 𝔹)
  where

  open Grouping _≈_ ≈-refl ≈-sym ≈-trans _∙_ _∨_ ∙-cong ∨-cong ∨-idem ∨-comm ∨-assoc
                distribˡ distribʳ κ _⊔ᴷ_ κ-⊔ _≟ᴷ_ ν _≟ⱽ_ _<ⱽ_

  ----------------------------------------------------------------------
  -- Skeletons: whatever holds of every skeleton given holds of every
  -- one returned

  module Skel (Sk : List V → Set) where

    SkP : Prod → Set
    SkP P = Sk (proj₁ P)

    SkG : Group → Set
    SkG G = Sk (proj₁ G)

    insert-sk : ∀ P Gs → SkP P → (∀ {G} → G ∈ᴬ Gs → SkG G) → ∀ {G} → G ∈ᴬ insert P Gs → SkG G
    insert-sk (vs , s) (alt (ws , g)) p h m with vs ≟ˢ ws
    ... | yes refl with m
    ...   | inAlt = p
    insert-sk (vs , s) (alt (ws , g)) p h m | no _ with vs <ˢ ws
    ...   | true with m
    ...     | inHead          = p
    ...     | inTail inAlt    = h inAlt
    insert-sk (vs , s) (alt (ws , g)) p h m | no _ | false with m
    ...     | inHead          = h inAlt
    ...     | inTail inAlt    = p
    insert-sk (vs , s) ((ws , g) ∷⁺ Gs) p h m with vs ≟ˢ ws
    ... | yes refl with m
    ...   | inHead   = p
    ...   | inTail m' = h (inTail m')
    insert-sk (vs , s) ((ws , g) ∷⁺ Gs) p h m | no _ with vs <ˢ ws
    ...   | true with m
    ...     | inHead            = p
    ...     | inTail inHead     = h inHead
    ...     | inTail (inTail m') = h (inTail m')
    insert-sk (vs , s) ((ws , g) ∷⁺ Gs) p h m | no _ | false with m
    ...     | inHead    = h inHead
    ...     | inTail m' = insert-sk (vs , s) Gs p (λ m'' → h (inTail m'')) m'

    groups-sk : ∀ ps → (∀ {P} → P ∈ᴬ ps → SkP P) → ∀ {G} → G ∈ᴬ groups ps → SkG G
    groups-sk (alt P)   h inAlt = h inAlt
    groups-sk (P ∷⁺ ps) h m =
      insert-sk P (groups ps) (h inHead) (groups-sk ps (λ m' → h (inTail m'))) m

    foldGroup-sk : ∀ G → SkG G → SkG (foldGroup G)
    foldGroup-sk (vs , g) h with fold? g
    ... | just _  = h
    ... | nothing = h

    members-sk : ∀ G → SkG G → ∀ {P} → P ∈ᴬ members G → SkP P
    members-sk (vs , g) h m with ∈-map⁻ (vs ,_) g m
    ... | _ , _ , refl = h

    flatten-sk : ∀ Gs → (∀ {G} → G ∈ᴬ Gs → SkG G) → ∀ {P} → P ∈ᴬ flatten Gs → SkP P
    flatten-sk (alt G)   h m = members-sk G (h inAlt) m
    flatten-sk (G ∷⁺ Gs) h m with ∈-⧺⁻ (members G) m
    ... | inj₁ m' = members-sk G (h inHead) m'
    ... | inj₂ m' = flatten-sk Gs (λ m'' → h (inTail m'')) m'

    mapFold-sk : ∀ Gs → (∀ {G} → G ∈ᴬ Gs → SkG G) → ∀ {G} → G ∈ᴬ mapᴬ foldGroup Gs → SkG G
    mapFold-sk Gs h m with ∈-map⁻ foldGroup Gs m
    ... | G , m' , refl = foldGroup-sk G (h m')

    canonical-sk : ∀ ps → (∀ {P} → P ∈ᴬ ps → SkP P) → ∀ {P} → P ∈ᴬ canonical ps → SkP P
    canonical-sk ps h =
      flatten-sk (mapᴬ foldGroup (groups ps)) (mapFold-sk (groups ps) (groups-sk ps h))

    module Pr (_≲_ : X → X → Set) (absorb : ∀ {a b} → a ≲ b → (a ∨ b) ≈ b)
              (_≲?_ : (P P' : Prod) → Maybe (⟦ P ⟧ᵖ ≲ ⟦ P' ⟧ᵖ)) where

      open Pruning _≲_ absorb _≲?_

      ∷?-sk : ∀ P m → SkP P → (∀ {s} → m ≡ just s → ∀ {Q} → Q ∈ᴬ s → SkP Q)
            → ∀ {Q} → Q ∈ᴬ (P ∷? m) → SkP Q
      ∷?-sk P nothing  p h inAlt      = p
      ∷?-sk P (just s) p h inHead     = p
      ∷?-sk P (just s) p h (inTail m) = h refl m

      sweep-sk : ∀ P s → (∀ {Q} → Q ∈ᴬ s → SkP Q)
               → ∀ {s'} → proj₁ (sweep P s) ≡ just s' → ∀ {Q} → Q ∈ᴬ s' → SkP Q
      sweep-sk P (alt K) h e m with K ≲? P
      sweep-sk P (alt K) h () m | just _
      sweep-sk P (alt K) h refl inAlt | nothing = h inAlt
      sweep-sk P (K ∷⁺ s) h e m with K ≲? P | sweep P s | sweep-sk P s (λ m' → h (inTail m'))
      ... | just _  | m₀ , _ | ih = ih e m
      sweep-sk P (K ∷⁺ s) h refl m | nothing | m₀ , _ | ih =
        ∷?-sk K m₀ (h inHead) ih m

      prune-sk : ∀ ps → (∀ {P} → P ∈ᴬ ps → SkP P) → ∀ {P} → P ∈ᴬ prune ps → SkP P
      prune-sk (alt P)  h m = h m
      prune-sk (P ∷⁺ s) h m with below? P (prune s)
      ... | just _  = prune-sk s (λ m' → h (inTail m')) m
      ... | nothing =
            ∷?-sk P (proj₁ (sweep P (prune s))) (h inHead)
                  (sweep-sk P (prune s) (prune-sk s (λ m' → h (inTail m')))) m

      round-sk : ∀ ps → (∀ {P} → P ∈ᴬ ps → SkP P) → ∀ {P} → P ∈ᴬ round ps → SkP P
      round-sk ps h = prune-sk (canonical ps) (canonical-sk ps h)

      rounds-sk : ∀ n ps → (∀ {P} → P ∈ᴬ ps → SkP P) → ∀ {P} → P ∈ᴬ rounds n ps → SkP P
      rounds-sk zero    ps h m = h m
      rounds-sk (suc n) ps h m with size (round ps) <ᵇ size ps
      ... | true  = rounds-sk n (round ps) (round-sk ps h) m
      ... | false = round-sk ps h m

      maximal-sk : ∀ ps → (∀ {P} → P ∈ᴬ ps → SkP P) → ∀ {P} → P ∈ᴬ maximal ps → SkP P
      maximal-sk ps = rounds-sk (size ps) ps

  ----------------------------------------------------------------------
  -- Every alternative is below one of the grouped and folded sum, slot
  -- by slot

  module Below (_≤_ : K → K → Set) (≤-refl : ∀ {c} → c ≤ c)
               (≤-trans : ∀ {c d e} → c ≤ d → d ≤ e → c ≤ e)
               (ubˡ : ∀ c d → c ≤ (c ⊔ᴷ d)) (ubʳ : ∀ c d → d ≤ (c ⊔ᴷ d)) where

    infix 4 _≤ˢ_ _≤ᵖ_

    data _≤ˢ_ : ∀ {vs} → Slots vs → Slots vs → Set where
      ≤⌜⌝ : ∀ {c d} → c ≤ d → ⌜ c ⌝ ≤ˢ ⌜ d ⌝
      ≤▸  : ∀ {a vs c d} {s t : Slots vs} → c ≤ d → s ≤ˢ t → _▸_ {a} c s ≤ˢ (d ▸ t)

    data _≤ᵖ_ : Prod → Prod → Set where
      ≤ᵖ-at : ∀ {vs} {s t : Slots vs} → s ≤ˢ t → (vs , s) ≤ᵖ (vs , t)

    ≤ˢ-refl : ∀ {vs} {s : Slots vs} → s ≤ˢ s
    ≤ˢ-refl {s = ⌜ c ⌝} = ≤⌜⌝ ≤-refl
    ≤ˢ-refl {s = c ▸ s} = ≤▸ ≤-refl ≤ˢ-refl

    -- an alternative within a group, below one of it

    within-∈ : ∀ {vs} (s : Slots vs) g {p} → within? s g ≡ just p → s ∈ᴬ g
    within-∈ s (alt t) e with s ≟ᵏ t
    within-∈ s (alt t) e | yes refl = inAlt
    within-∈ s (alt t) () | no _
    within-∈ s (t ∷⁺ g) e with s ≟ᵏ t
    ... | yes refl = inHead
    ... | no _ with within? s g in e'
    ...   | just p' = inTail (within-∈ s g e')
    within-∈ s (t ∷⁺ g) () | no _ | nothing

    add-new : ∀ {vs} (s : Slots vs) g → s ∈ᴬ add s g
    add-new s g with within? s g in e
    ... | just _  = within-∈ s g e
    ... | nothing = inHead

    add-old : ∀ {vs} (s : Slots vs) g {t} → t ∈ᴬ g → t ∈ᴬ add s g
    add-old s g m with within? s g
    ... | just _  = m
    ... | nothing = inTail m

    -- a member of a group of the given skeleton

    InG : Prod → Alts Group → Set
    InG (vs , s) Gs = Σ[ g ∈ Alts (Slots vs) ] (((vs , g) ∈ᴬ Gs) × (s ∈ᴬ g))

    insert-new : ∀ P Gs → InG P (insert P Gs)
    insert-new (vs , s) (alt (ws , g)) with vs ≟ˢ ws
    ... | yes refl = add s g , inAlt , add-new s g
    ... | no _ with vs <ˢ ws
    ...   | true  = alt s , inHead , inAlt
    ...   | false = alt s , inTail inAlt , inAlt
    insert-new (vs , s) ((ws , g) ∷⁺ Gs) with vs ≟ˢ ws
    ... | yes refl = add s g , inHead , add-new s g
    ... | no _ with vs <ˢ ws
    ...   | true  = alt s , inHead , inAlt
    ...   | false with insert-new (vs , s) Gs
    ...     | g' , m , m' = g' , inTail m , m'

    insert-old : ∀ P Gs {Q} → InG Q Gs → InG Q (insert P Gs)
    insert-old (vs , s) (alt (ws , g)) {us , t} (g₀ , inAlt , m') with vs ≟ˢ ws
    ... | yes refl = add s g , inAlt , add-old s g m'
    ... | no _ with vs <ˢ ws
    ...   | true  = g , inTail inAlt , m'
    ...   | false = g , inHead , m'
    insert-old (vs , s) ((ws , g) ∷⁺ Gs) {us , t} (g₀ , inHead , m') with vs ≟ˢ ws
    ... | yes refl = add s g , inHead , add-old s g m'
    ... | no _ with vs <ˢ ws
    ...   | true  = g , inTail inHead , m'
    ...   | false = g , inHead , m'
    insert-old (vs , s) ((ws , g) ∷⁺ Gs) {us , t} (g₀ , inTail m , m') with vs ≟ˢ ws
    ... | yes refl = g₀ , inTail m , m'
    ... | no _ with vs <ˢ ws
    ...   | true  = g₀ , inTail (inTail m) , m'
    ...   | false with insert-old (vs , s) Gs {us , t} (g₀ , m , m')
    ...     | g' , m₄ , m₅ = g' , inTail m₄ , m₅

    groups-in : ∀ ps {P} → P ∈ᴬ ps → InG P (groups ps)
    groups-in (alt (vs , s)) inAlt       = alt s , inAlt , inAlt
    groups-in (P ∷⁺ ps)      inHead      = insert-new P (groups ps)
    groups-in (P ∷⁺ ps)      (inTail m)  = insert-old P (groups ps) (groups-in ps m)

    -- folding a group: its members all lie below the fold

    joinᴷ-ub : ∀ g {c} → ⌜ c ⌝ ∈ᴬ g → c ≤ joinᴷ g
    joinᴷ-ub (alt ⌜ c ⌝)  inAlt      = ≤-refl
    joinᴷ-ub (⌜ c ⌝ ∷⁺ g) inHead     = ubˡ c (joinᴷ g)
    joinᴷ-ub (⌜ c ⌝ ∷⁺ g) (inTail m) = ≤-trans (joinᴷ-ub g m) (ubʳ c (joinᴷ g))

    tails-∈ : ∀ {a vs} (g : Alts (Slots (a ∷ vs))) {c s} → (c ▸ s) ∈ᴬ g → s ∈ᴬ tails g
    tails-∈ (alt (_ ▸ _))  inAlt      = inAlt
    tails-∈ ((_ ▸ _) ∷⁺ g) inHead     = inHead
    tails-∈ ((_ ▸ _) ∷⁺ g) (inTail m) = inTail (tails-∈ g m)

    sameHead-∈ : ∀ {a vs} (g : Alts (Slots (a ∷ vs))) {c p} → sameHead? g ≡ just (c , p)
               → ∀ {d s} → (d ▸ s) ∈ᴬ g → d ≡ c
    sameHead-∈ (alt (c ▸ s)) refl inAlt = refl
    sameHead-∈ ((c ▸ s) ∷⁺ g) e m with sameHead? g in e₁
    sameHead-∈ ((c ▸ s) ∷⁺ g) () m | nothing
    ... | just (c' , p) with c ≟ᴷ c'
    sameHead-∈ ((c ▸ s) ∷⁺ g) () m | just (c' , p) | no _
    ... | yes refl with e | m
    ...   | refl | inHead    = refl
    ...   | refl | inTail m' = sameHead-∈ g e₁ m'

    sameTail-≤ : ∀ {a vs} (g : Alts (Slots (a ∷ vs))) {s' p} → sameTail? g ≡ just (s' , p)
               → ∀ {s} → s ∈ᴬ g → s ≤ˢ s'
    sameTail-≤ (alt (c ▸ s)) refl inAlt = ≤ˢ-refl
    sameTail-≤ ((c ▸ s) ∷⁺ g) e m with sameTail? g in e₁
    sameTail-≤ ((c ▸ s) ∷⁺ g) () m | nothing
    ... | just (c' ▸ s₁ , p) with s ≟ᵏ s₁
    sameTail-≤ ((c ▸ s) ∷⁺ g) () m | just (c' ▸ s₁ , p) | no _
    ... | yes refl with e | m
    ...   | refl | inHead    = ≤▸ (ubˡ c c') ≤ˢ-refl
    ...   | refl | inTail m' with sameTail-≤ g e₁ m'
    ...     | ≤▸ q r = ≤▸ (≤-trans q (ubʳ c c')) r

    fold-≤ : ∀ {vs} (g : Alts (Slots vs)) {s' p} → fold? g ≡ just (s' , p) → ∀ {s} → s ∈ᴬ g → s ≤ˢ s'
    fold-≤ {[]} g refl {⌜ c ⌝} m = ≤⌜⌝ (joinᴷ-ub g m)
    fold-≤ {_ ∷ _} g e m with sameHead? g in e₁
    ... | nothing = sameTail-≤ g e m
    ... | just (c , p) with fold? (tails g) in e₂
    ...   | nothing = sameTail-≤ g e m
    fold-≤ {_ ∷ _} g refl {d ▸ s} m | just (c , p) | just (s₁ , q) =
      ≤▸ (subst (_≤ c) (sym (sameHead-∈ g e₁ m)) ≤-refl) (fold-≤ (tails g) e₂ (tails-∈ g m))

    foldGroup-≤ : ∀ vs (g : Alts (Slots vs)) {s} → s ∈ᴬ g
                → Σ[ t ∈ Slots vs ] (((vs , t) ∈ᴬ members (foldGroup (vs , g))) × (s ≤ˢ t))
    foldGroup-≤ vs g m with fold? g in e
    ... | just (s' , p) = s' , inAlt , fold-≤ g e m
    ... | nothing       = _ , ∈-map (vs ,_) m , ≤ˢ-refl

    flatten-∈ : ∀ Gs {G P} → G ∈ᴬ Gs → P ∈ᴬ members (foldGroup G) → P ∈ᴬ flatten (mapᴬ foldGroup Gs)
    flatten-∈ (alt G)   inAlt      m' = m'
    flatten-∈ (G ∷⁺ Gs) inHead     m' = ∈-⧺ˡ m'
    flatten-∈ (G ∷⁺ Gs) (inTail m) m' =
      ∈-⧺ʳ (members (foldGroup G)) (flatten-∈ Gs m m')

    canonical-≤ : ∀ ps {P} → P ∈ᴬ ps → Σ[ P' ∈ Prod ] ((P' ∈ᴬ canonical ps) × (P ≤ᵖ P'))
    canonical-≤ ps {vs , s} m with groups-in ps m
    ... | g , mg , ms with foldGroup-≤ vs g ms
    ...   | t , mt , le = (vs , t) , flatten-∈ (groups ps) mg mt , ≤ᵖ-at le
