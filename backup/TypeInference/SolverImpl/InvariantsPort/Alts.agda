------------------------------------------------------------------
-- Alternatives of a sum                                          --
--                                                                --
-- Membership in `Alts`, and the skeletons of a grouped, folded   --
-- and pruned sum (`Grouping`): a property of every skeleton of   --
-- the input holds of every skeleton of the output.               --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.List.Base using (List)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (zero; suc; _<ᵇ_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no)

open import Syntax.LanguageSpec

open import Util.Equality

module TypeInference.SolverImpl.Invariants.Alts (S : LanguageSpec) where

open import TypeInference.SolverImpl.Product S using (Alts; alt; _∷⁺_; _⧺_; mapᴬ; module Grouping)

------------------------------------------------------------------------
-- Membership

infix 4 _∈ᴬ_

data _∈ᴬ_ {X : Set} (x : X) : Alts X → Set where
  inAlt  : x ∈ᴬ alt x
  inHead : ∀ {s} → x ∈ᴬ (x ∷⁺ s)
  inTail : ∀ {y s} → x ∈ᴬ s → x ∈ᴬ (y ∷⁺ s)

module _ {X : Set} where

  ∈ᴬ-⧺⁻ : ∀ {x : X} (s : Alts X) {t} → x ∈ᴬ (s ⧺ t) → x ∈ᴬ s ⊎ x ∈ᴬ t
  ∈ᴬ-⧺⁻ (alt y)  inHead     = inj₁ inAlt
  ∈ᴬ-⧺⁻ (alt y)  (inTail m) = inj₂ m
  ∈ᴬ-⧺⁻ (y ∷⁺ s) inHead     = inj₁ inHead
  ∈ᴬ-⧺⁻ (y ∷⁺ s) (inTail m) with ∈ᴬ-⧺⁻ s m
  ... | inj₁ m' = inj₁ (inTail m')
  ... | inj₂ m' = inj₂ m'

  ∈ᴬ-alt⁻ : ∀ {x y : X} → x ∈ᴬ alt y → x ≡ y
  ∈ᴬ-alt⁻ inAlt = refl

module _ {X Y : Set} (f : X → Y) where

  ∈ᴬ-map⁻ : ∀ {y} (s : Alts X) → y ∈ᴬ mapᴬ f s → Σ[ x ∈ X ] ((x ∈ᴬ s) × (y ≡ f x))
  ∈ᴬ-map⁻ (alt x)  inAlt      = x , inAlt , refl
  ∈ᴬ-map⁻ (x ∷⁺ s) inHead     = x , inHead , refl
  ∈ᴬ-map⁻ (x ∷⁺ s) (inTail m) with ∈ᴬ-map⁻ s m
  ... | x' , m' , e = x' , inTail m' , e

------------------------------------------------------------------------
-- Skeletons, at the parameters of `Grouping`

module Skeletons
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
  (Sk : List V → Set)
  where

  open Grouping _≈_ ≈-refl ≈-sym ≈-trans _∙_ _∨_ ∙-cong ∨-cong ∨-idem ∨-comm ∨-assoc
                distribˡ distribʳ κ _⊔ᴷ_ κ-⊔ _≟ᴷ_ ν _≟ⱽ_ _<ⱽ_

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
  ...     | inHead       = p
  ...     | inTail inAlt = h inAlt
  insert-sk (vs , s) (alt (ws , g)) p h m | no _ | false with m
  ...     | inHead       = h inAlt
  ...     | inTail inAlt = p
  insert-sk (vs , s) ((ws , g) ∷⁺ Gs) p h m with vs ≟ˢ ws
  ... | yes refl with m
  ...   | inHead    = p
  ...   | inTail m' = h (inTail m')
  insert-sk (vs , s) ((ws , g) ∷⁺ Gs) p h m | no _ with vs <ˢ ws
  ...   | true with m
  ...     | inHead             = p
  ...     | inTail inHead      = h inHead
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
  members-sk (vs , g) h m with ∈ᴬ-map⁻ (vs ,_) g m
  ... | _ , _ , refl = h

  flatten-sk : ∀ Gs → (∀ {G} → G ∈ᴬ Gs → SkG G) → ∀ {P} → P ∈ᴬ flatten Gs → SkP P
  flatten-sk (alt G)   h m = members-sk G (h inAlt) m
  flatten-sk (G ∷⁺ Gs) h m with ∈ᴬ-⧺⁻ (members G) m
  ... | inj₁ m' = members-sk G (h inHead) m'
  ... | inj₂ m' = flatten-sk Gs (λ m'' → h (inTail m'')) m'

  canonical-sk : ∀ ps → (∀ {P} → P ∈ᴬ ps → SkP P) → ∀ {P} → P ∈ᴬ canonical ps → SkP P
  canonical-sk ps h = flatten-sk (mapᴬ foldGroup (groups ps)) fs
    where
      fs : ∀ {G} → G ∈ᴬ mapᴬ foldGroup (groups ps) → SkG G
      fs m with ∈ᴬ-map⁻ foldGroup (groups ps) m
      ... | G , m' , refl = foldGroup-sk G (groups-sk ps h m')

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
    sweep-sk P (K ∷⁺ s) h refl m | nothing | m₀ , _ | ih = ∷?-sk K m₀ (h inHead) ih m

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
