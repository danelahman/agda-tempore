------------------------------------------------------------------
-- Canonical forms add no unknown                                 --
--                                                                --
-- A whole unknown is its own canonical form (`canonₑ-var`,       --
-- `canonᵣ-var`); each unknown of a canonical form is one of the  --
-- expression (`canonₑ-occ`, `canonᵣ-occʳ`, `canonᵣ-occᵉ`). So     --
-- good sides, and the pieces of split orderings, stay good.      --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)

open import Algebra.Definitions using (Commutative)
open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Invariants.Canon (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-e; occᵉ-r; occʳ-r)
open import TypeInference.SolverImpl.Core.Rigid S using (∨-true; ∨-left; ∨-right; dec-true; true-dec)
open import TypeInference.SolverImpl.Product S
open import TypeInference.SolverImpl.Normal S using (decide≾ᵣ; decide≾ₑ)
open import TypeInference.SolverImpl.Canon S
open import TypeInference.SolverImpl.Resid S
open import TypeInference.SolverImpl.Invariants.Alts S
open import TypeInference.SolverImpl.Invariants.Outer S
open import TypeInference.SolverImpl.Invariants.Residual S

------------------------------------------------------------------------
-- Lists

insertBy-∈ : ∀ {A : Set} (_<_ : A → A → 𝔹) (a : A) (l : List A) {x}
           → x ∈ insertBy _<_ a l → (x ≡ a) ⊎ (x ∈ l)
insertBy-∈ _<_ a []       (here e) = inj₁ e
insertBy-∈ _<_ a (b ∷ bs) m with b < a | m
... | true  | here e  = inj₂ (here e)
... | true  | there m' with insertBy-∈ _<_ a bs m'
...   | inj₁ e   = inj₁ e
...   | inj₂ m'' = inj₂ (there m'')
insertBy-∈ _<_ a (b ∷ bs) m | false | here e   = inj₁ e
insertBy-∈ _<_ a (b ∷ bs) m | false | there m' = inj₂ m'

sortBy-∈ : ∀ {A : Set} (_<_ : A → A → 𝔹) (l : List A) {x} → x ∈ sortBy _<_ l → x ∈ l
sortBy-∈ _<_ (a ∷ as) m with insertBy-∈ _<_ a (sortBy _<_ as) m
... | inj₁ e  = here e
... | inj₂ m' = there (sortBy-∈ _<_ as m')

------------------------------------------------------------------------
-- Effect grades

module SkEₑ {Θ : Scope} =
  Skeletons {EExp Θ} {E} {EVar Θ} _≡̂ₑ_ ≡̂ₑ-refl ≡̂ₑ-sym ≡̂ₑ-trans _·̂ₑ_ _⊔̂ₑ_
            ≡̂ₑ-cong ≡̂ₑ-cong-⊔ ≡̂ₑ-idem-⊔ ≡̂ₑ-comm-⊔ ≡̂ₑ-assoc-⊔
            ≡̂ₑ-distribˡ-⊔ ≡̂ₑ-distribʳ-⊔
            econst _⊔ₑ_ ≡̂ₑ-const-⊔ _≡ₑ?_ evar _≟ᶠ_ (_<ᵉᵛ_ {Θ})

-- The top, as its own normal form

Tₑ : ∀ {Θ} → List (EAtom Θ)
Tₑ = consₑ (ac ⊤ₑ) []

-- A variable of a product comes from the atoms it is built from

consₑ-av : ∀ {Θ} (a : EAtom Θ) (l : List (EAtom Θ)) {i}
         → av i ∈ consₑ a l → (a ≡ av i) ⊎ (av i ∈ l)
consₑ-av (ac c) (ac d ∷ l) m with consₑ-av (ac (c ·ₑ d)) l m
... | inj₁ ()
... | inj₂ m' = inj₂ (there m')
consₑ-av (ac c) [] m with c ≡ₑ? uₑ | m
... | yes _ | ()
... | no _  | there ()
consₑ-av (ac c) (av j ∷ l) m with c ≡ₑ? uₑ | m
... | yes _ | m'       = inj₂ m'
... | no _  | there m' = inj₂ m'
consₑ-av (av j) l (here e)  = inj₁ (sym e)
consₑ-av (av j) l (there m) = inj₂ m

appₑ-av : ∀ {Θ} (as ys : List (EAtom Θ)) {i} → av i ∈ appₑ as ys → (av i ∈ as) ⊎ (av i ∈ ys)
appₑ-av []       ys m = inj₂ m
appₑ-av (a ∷ as) ys m with consₑ-av a (appₑ as ys) m
... | inj₁ refl = inj₁ (here refl)
... | inj₂ m' with appₑ-av as ys m'
...   | inj₁ m'' = inj₁ (there m'')
...   | inj₂ m'' = inj₂ m''

Tₑ-av : ∀ {Θ} {i : EVar Θ} → av i ∈ Tₑ {Θ} → ⊥
Tₑ-av m with consₑ-av (ac ⊤ₑ) [] m
... | inj₁ ()
... | inj₂ ()

-- The alternatives of a sum built by the normal form

withinₑ-∈ : ∀ {Θ} (P : List (EAtom Θ)) s {p} → withinₑ? P s ≡ just p → P ∈ᴬ s
withinₑ-∈ P (alt Q) e with P ≟ᵖₑ Q
withinₑ-∈ P (alt Q) e  | yes refl = inAlt
withinₑ-∈ P (alt Q) () | no _
withinₑ-∈ P (Q ∷⁺ t) e with P ≟ᵖₑ Q
... | yes refl = inHead
... | no _ with withinₑ? P t in e'
...   | just _ = inTail (withinₑ-∈ P t e')
withinₑ-∈ P (Q ∷⁺ t) () | no _ | nothing

nubₑ-∈⁻ : ∀ {Θ} (s : Alts (List (EAtom Θ))) {P} → P ∈ᴬ nubₑ s → P ∈ᴬ s
nubₑ-∈⁻ (alt P)  m = m
nubₑ-∈⁻ (P ∷⁺ s) m with withinₑ? P (nubₑ s)
... | just _ = inTail (nubₑ-∈⁻ s m)
... | nothing with m
...   | inHead    = inHead
...   | inTail m' = inTail (nubₑ-∈⁻ s m')

mul1ₑ-∈⁻ : ∀ {Θ} (P : List (EAtom Θ)) t {Q} → Q ∈ᴬ mul1ₑ P t
         → Σ[ P' ∈ List (EAtom Θ) ] ((P' ∈ᴬ t) × (Q ≡ appₑ P P'))
mul1ₑ-∈⁻ P (alt P')  inAlt      = P' , inAlt , refl
mul1ₑ-∈⁻ P (P' ∷⁺ t) inHead     = P' , inHead , refl
mul1ₑ-∈⁻ P (P' ∷⁺ t) (inTail m) with mul1ₑ-∈⁻ P t m
... | P'' , m' , e = P'' , inTail m' , e

mulₑ-∈⁻ : ∀ {Θ} (s t : Alts (List (EAtom Θ))) {Q} → Q ∈ᴬ mulₑ s t
        → Σ[ P ∈ List (EAtom Θ) ] Σ[ P' ∈ List (EAtom Θ) ]
            ((P ∈ᴬ s) × (P' ∈ᴬ t) × (Q ≡ appₑ P P'))
mulₑ-∈⁻ (alt P)  t m with mul1ₑ-∈⁻ P t m
... | P' , m' , e = P , P' , inAlt , m' , e
mulₑ-∈⁻ (P ∷⁺ s) t m with ∈ᴬ-⧺⁻ (mul1ₑ P t) m
... | inj₁ m' with mul1ₑ-∈⁻ P t m'
...   | P' , m'' , e = P , P' , inHead , m'' , e
mulₑ-∈⁻ (P ∷⁺ s) t m | inj₂ m' with mulₑ-∈⁻ s t m'
...   | P₀ , P' , m₀ , m'' , e = P₀ , P' , inTail m₀ , m'' , e

absorbₑ-∈⁻ : ∀ {Θ} (s : Alts (List (EAtom Θ))) {Q} → Q ∈ᴬ absorbₑ s → (Q ∈ᴬ s) ⊎ (Q ≡ Tₑ)
absorbₑ-∈⁻ s m with topSumₑ? s
... | just _  = inj₂ (∈ᴬ-alt⁻ m)
... | nothing = inj₁ m

-- The variables of the normal form are the expression's

flatₑ-av : ∀ {Θ} (ε : EExp Θ) {P i} → P ∈ᴬ flatₑ ε → av i ∈ P → occᵉ-e i ε ≡ true
flatₑ-av (evar j)   {i = i} inAlt (here refl) = dec-true (i ≟ᶠ i) refl
flatₑ-av (econst c) inAlt a with consₑ-av (ac c) [] a
... | inj₁ ()
... | inj₂ ()
flatₑ-av (ε ·̂ₑ ε')  {i = i} m a with absorbₑ-∈⁻ (nubₑ (mulₑ (flatₑ ε) (flatₑ ε'))) m
... | inj₂ refl = ⊥-elim (Tₑ-av a)
... | inj₁ m' with mulₑ-∈⁻ (flatₑ ε) (flatₑ ε') (nubₑ-∈⁻ _ m')
...   | P , P' , m₁ , m₂ , refl with appₑ-av P P' a
...     | inj₁ a₁ = ∨-left (occᵉ-e i ε) _ (flatₑ-av ε m₁ a₁)
...     | inj₂ a₂ = ∨-right (occᵉ-e i ε) _ (flatₑ-av ε' m₂ a₂)
flatₑ-av (ε ⊔̂ₑ ε')  {i = i} m a with absorbₑ-∈⁻ (nubₑ (flatₑ ε ⧺ flatₑ ε')) m
... | inj₂ refl = ⊥-elim (Tₑ-av a)
... | inj₁ m' with ∈ᴬ-⧺⁻ (flatₑ ε) (nubₑ-∈⁻ _ m')
...   | inj₁ m₁ = ∨-left (occᵉ-e i ε) _ (flatₑ-av ε m₁ a)
...   | inj₂ m₂ = ∨-right (occᵉ-e i ε) _ (flatₑ-av ε' m₂ a)

varsᵃₑ-∈ : ∀ {Θ} (l : List (EAtom Θ)) {a} → a ∈ varsᵃₑ l → a ∈ l
varsᵃₑ-∈ (ac _ ∷ l) m         = there (varsᵃₑ-∈ l m)
varsᵃₑ-∈ (av i ∷ l) (here e)  = here e
varsᵃₑ-∈ (av i ∷ l) (there m) = there (varsᵃₑ-∈ l m)

commuteₑ-av : ∀ {Θ} (P : List (EAtom Θ)) {i} → av i ∈ commuteₑ P → av i ∈ P
commuteₑ-av P m with consₑ-av (ac (constₑ P)) (sortBy _<ᵉᵃ_ (varsᵃₑ P)) m
... | inj₁ ()
... | inj₂ m' = varsᵃₑ-∈ P (sortBy-∈ _<ᵉᵃ_ (varsᵃₑ P) m')

commSumₑ-∈⁻ : ∀ {Θ} (c : Maybe (Commutative _≡_ _·ₑ_)) (s : Alts (List (EAtom Θ))) {Q}
            → Q ∈ᴬ commSumₑ c s
            → Σ[ P ∈ List (EAtom Θ) ] ((P ∈ᴬ s) × ((Q ≡ P) ⊎ (Q ≡ commuteₑ P)))
commSumₑ-∈⁻ nothing  s m = _ , m , inj₁ refl
commSumₑ-∈⁻ (just _) s m with ∈ᴬ-map⁻ commuteₑ s (nubₑ-∈⁻ _ m)
... | P , m' , e = P , m' , inj₂ e

nrmₑ-av : ∀ {Θ} (ε : EExp Θ) {Q i} → Q ∈ᴬ nrmₑ ε → av i ∈ Q → occᵉ-e i ε ≡ true
nrmₑ-av ε m a with commSumₑ-∈⁻ ·ₑ-comm? (flatₑ ε) m
... | P , m' , inj₁ refl = flatₑ-av ε m' a
... | P , m' , inj₂ refl = flatₑ-av ε m' (commuteₑ-av P a)

-- A product with the top among its factors, replaced by the top

absorbProdₑ-av : ∀ {Θ} (P : List (EAtom Θ)) {i} → av i ∈ absorbProdₑ P → av i ∈ P
absorbProdₑ-av P m with Is-just? uₑ-least?
... | nothing = m
... | just ij with topProdₑ? ij P
...   | just _  = ⊥-elim (Tₑ-av m)
...   | nothing = m

-- Skeletons and slots

slotsₑ-av : ∀ {Θ} (m : Maybe E) (P : List (EAtom Θ)) {i} → i ∈ proj₁ (slotsₑ m P) → av i ∈ P
slotsₑ-av m (ac c ∷ P) w         = there (slotsₑ-av _ P w)
slotsₑ-av m (av j ∷ P) (here e)  = here (cong av e)
slotsₑ-av m (av j ∷ P) (there w) = there (slotsₑ-av nothing P w)

atomsₑ-av : ∀ {Θ vs} (s : Gₑ.Slots {Θ} vs) {i} → av i ∈ atomsₑ s → i ∈ vs
atomsₑ-av Gₑ.⌜ c ⌝ a with consₑ-av (ac c) [] a
... | inj₁ ()
... | inj₂ ()
atomsₑ-av (Gₑ._▸_ {j} c s) a with consₑ-av (ac c) (av j ∷ atomsₑ s) a
... | inj₂ (here refl) = here refl
... | inj₂ (there a')  = there (atomsₑ-av s a')

-- The variables of a read-back

⟦⟧ᵉᵖ-av : ∀ {Θ} (P : List (EAtom Θ)) {i} → occᵉ-e i ⟦ P ⟧ᵉᵖ ≡ true → av i ∈ P
⟦⟧ᵉᵖ-av []               ()
⟦⟧ᵉᵖ-av (ac c ∷ [])      ()
⟦⟧ᵉᵖ-av (av j ∷ [])      {i} q = here (cong av (true-dec (i ≟ᶠ j) q))
⟦⟧ᵉᵖ-av (ac c ∷ b ∷ as)  q = there (⟦⟧ᵉᵖ-av (b ∷ as) q)
⟦⟧ᵉᵖ-av {Θ} (av j ∷ bas@(b ∷ as)) {i} q =
  [ (λ q' → here (cong av (true-dec (i ≟ᶠ j) q'))) , (λ q' → there (⟦⟧ᵉᵖ-av bas q')) ]′
    (∨-true (occᵉ-e i (evar {Θ} j)) (occᵉ-e i ⟦ bas ⟧ᵉᵖ) q)

⟦⟧ᵉᵖ⁺-av : ∀ {Θ} (s : Alts (List (EAtom Θ))) {i} → occᵉ-e i ⟦ s ⟧ᵉᵖ⁺ ≡ true
         → Σ[ P ∈ List (EAtom Θ) ] ((P ∈ᴬ s) × (av i ∈ P))
⟦⟧ᵉᵖ⁺-av (alt P)  q = P , inAlt , ⟦⟧ᵉᵖ-av P q
⟦⟧ᵉᵖ⁺-av (P ∷⁺ s) {i} q with ∨-true (occᵉ-e i ⟦ P ⟧ᵉᵖ) _ q
... | inj₁ q' = P , inHead , ⟦⟧ᵉᵖ-av P q'
... | inj₂ q' with ⟦⟧ᵉᵖ⁺-av s q'
...   | P' , m , a = P' , inTail m , a

-- Every variable of an alternative of the canonical form is one of the
-- expression

canonSumₑ-av : ∀ {Θ} (ε : EExp Θ) {P i} → P ∈ᴬ canonSumₑ (nrmₑ ε) → av i ∈ P
             → occᵉ-e i ε ≡ true
canonSumₑ-av {Θ} ε m a
  with ∈ᴬ-map⁻ (λ P → atomsₑ (proj₂ P)) (Mₑ.maximal (toProdsₑ (mapᴬ absorbProdₑ (nrmₑ ε)))) m
... | (vs , s) , m' , refl = sk m' (atomsₑ-av s a)
  where
    Sk : List (EVar Θ) → Set
    Sk vs = ∀ {j} → j ∈ vs → occᵉ-e j ε ≡ true

    open SkEₑ {Θ} Sk
    open Pr (∅ᴴ ⊩_≾̂ₑ_) ≡̂ₑ-absorb (λ P P' → decide≾ₑ {Q = ∅ᴴ} Gₑ.⟦ P ⟧ᵖ Gₑ.⟦ P' ⟧ᵖ)

    ins : ∀ {P} → P ∈ᴬ toProdsₑ (mapᴬ absorbProdₑ (nrmₑ ε)) → SkP P
    ins m₀ with ∈ᴬ-map⁻ (slotsₑ nothing) (mapᴬ absorbProdₑ (nrmₑ ε)) m₀
    ... | Q , mQ , refl with ∈ᴬ-map⁻ absorbProdₑ (nrmₑ ε) mQ
    ...   | Q₀ , mQ₀ , refl = λ w → nrmₑ-av ε mQ₀ (absorbProdₑ-av Q₀ (slotsₑ-av nothing _ w))

    sk : ∀ {P} → P ∈ᴬ Mₑ.maximal (toProdsₑ (mapᴬ absorbProdₑ (nrmₑ ε))) → SkP P
    sk = maximal-sk (toProdsₑ (mapᴬ absorbProdₑ (nrmₑ ε))) ins

canonₑ-occ : ∀ {Θ} (ε : EExp Θ) {i} → occᵉ-e i (canonₑ ε) ≡ true → occᵉ-e i ε ≡ true
canonₑ-occ ε q with ⟦⟧ᵉᵖ⁺-av (canonSumₑ (nrmₑ ε)) q
... | P , m , a = canonSumₑ-av ε m a

-- A whole unknown

nrmₑ-whole : ∀ {Θ} (k : EVar Θ) → nrmₑ (evar k) ≡ alt {List (EAtom Θ)} (av k ∷ [])
nrmₑ-whole k with ·ₑ-comm?
... | nothing = refl
... | just _ with uₑ ≡ₑ? uₑ
...   | yes _ = refl
...   | no ¬p = ⊥-elim (¬p refl)

absorbProdₑ-whole : ∀ {Θ} (k : EVar Θ) → absorbProdₑ {Θ} (av k ∷ []) ≡ av k ∷ []
absorbProdₑ-whole k with Is-just? uₑ-least?
... | nothing = refl
... | just _  = refl

atoms-wholeₑ : ∀ {Θ} (k : EVar Θ)
             → atomsₑ (Gₑ._▸_ {Θ} {a = k} uₑ (Gₑ.⌜_⌝ {Θ} uₑ)) ≡ av k ∷ []
atoms-wholeₑ k with uₑ ≡ₑ? uₑ
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

canonₑ-var : ∀ {Θ} (k : EVar Θ) → canonₑ (evar k) ≡ evar k
canonₑ-var {Θ} k =
  trans (cong (λ s → ⟦ canonSumₑ {Θ} s ⟧ᵉᵖ⁺) (nrmₑ-whole k))
  (trans (cong (λ (P : List (EAtom Θ)) → ⟦ fromProdsₑ (Mₑ.maximal {Θ} (toProdsₑ (alt P))) ⟧ᵉᵖ⁺)
               (absorbProdₑ-whole k))
         (cong (λ l → ⟦ alt {List (EAtom Θ)} l ⟧ᵉᵖ⁺) (atoms-wholeₑ k)))

------------------------------------------------------------------------
-- Resource grades

module SkEᵣ {Θ : Scope} =
  Skeletons {RExp Θ} {R} {RVAtom Θ} _≡̂ᵣ_ ≡̂ᵣ-refl ≡̂ᵣ-sym ≡̂ᵣ-trans _·̂ᵣ_ _⊔̂ᵣ_
            ≡̂ᵣ-cong ≡̂ᵣ-cong-⊔ ≡̂ᵣ-idem-⊔ ≡̂ᵣ-comm-⊔ ≡̂ᵣ-assoc-⊔
            ≡̂ᵣ-distribˡ-⊔ ≡̂ᵣ-distribʳ-⊔
            rconst _⊔ᵣ_ ≡̂ᵣ-const-⊔ _≡ᵣ?_ ⟦_⟧ʳᵛ _≟ʳᵛ_ _<ʳᵛ_

Tᵣ : ∀ {Θ} → List (RAtom Θ)
Tᵣ = consᵣ (rc ⊤ᵣ) []

-- An atom of a product is a constant, or comes from the atoms it is
-- built from

IsCᵣ : ∀ {Θ} → RAtom Θ → Set
IsCᵣ a = Σ[ c ∈ R ] (a ≡ rc c)

consᵣ-∈ : ∀ {Θ} (a : RAtom Θ) (l : List (RAtom Θ)) {v} → v ∈ consᵣ a l
        → IsCᵣ v ⊎ ((v ≡ a) ⊎ (v ∈ l))
consᵣ-∈ (rc c) (rc d ∷ l) m with consᵣ-∈ (rc (c ·ᵣ d)) l m
... | inj₁ k         = inj₁ k
... | inj₂ (inj₁ e)  = inj₁ (_ , e)
... | inj₂ (inj₂ m') = inj₂ (inj₂ (there m'))
consᵣ-∈ (rc c) [] m with c ≡ᵣ? uᵣ | m
... | yes _ | ()
... | no _  | here e = inj₁ (c , e)
consᵣ-∈ (rc c) (rv j ∷ l) m with c ≡ᵣ? uᵣ | m
... | yes _ | m'       = inj₂ (inj₂ m')
... | no _  | here e   = inj₁ (c , e)
... | no _  | there m' = inj₂ (inj₂ m')
consᵣ-∈ (rc c) (rm j ∷ l) m with c ≡ᵣ? uᵣ | m
... | yes _ | m'       = inj₂ (inj₂ m')
... | no _  | here e   = inj₁ (c , e)
... | no _  | there m' = inj₂ (inj₂ m')
consᵣ-∈ (rv j) l (here e)  = inj₂ (inj₁ e)
consᵣ-∈ (rv j) l (there m) = inj₂ (inj₂ m)
consᵣ-∈ (rm j) l (here e)  = inj₂ (inj₁ e)
consᵣ-∈ (rm j) l (there m) = inj₂ (inj₂ m)

appᵣ-∈ : ∀ {Θ} (as ys : List (RAtom Θ)) {v} → v ∈ appᵣ as ys
       → IsCᵣ v ⊎ ((v ∈ as) ⊎ (v ∈ ys))
appᵣ-∈ []       ys m = inj₂ (inj₂ m)
appᵣ-∈ (a ∷ as) ys m with consᵣ-∈ a (appᵣ as ys) m
... | inj₁ k           = inj₁ k
... | inj₂ (inj₁ refl) = inj₂ (inj₁ (here refl))
... | inj₂ (inj₂ m') with appᵣ-∈ as ys m'
...   | inj₁ k          = inj₁ k
...   | inj₂ (inj₁ m'') = inj₂ (inj₁ (there m''))
...   | inj₂ (inj₂ m'') = inj₂ (inj₂ m'')

Tᵣ-∈ : ∀ {Θ} {v : RAtom Θ} → v ∈ Tᵣ {Θ} → IsCᵣ v
Tᵣ-∈ m with consᵣ-∈ (rc ⊤ᵣ) [] m
... | inj₁ k         = k
... | inj₂ (inj₁ e)  = _ , e
... | inj₂ (inj₂ ())

-- The alternatives of a sum built by the normal form

withinᵣ-∈ : ∀ {Θ} (P : List (RAtom Θ)) s {p} → withinᵣ? P s ≡ just p → P ∈ᴬ s
withinᵣ-∈ P (alt Q) e with P ≟ᵖᵣ Q
withinᵣ-∈ P (alt Q) e  | yes refl = inAlt
withinᵣ-∈ P (alt Q) () | no _
withinᵣ-∈ P (Q ∷⁺ t) e with P ≟ᵖᵣ Q
... | yes refl = inHead
... | no _ with withinᵣ? P t in e'
...   | just _ = inTail (withinᵣ-∈ P t e')
withinᵣ-∈ P (Q ∷⁺ t) () | no _ | nothing

nubᵣ-∈⁻ : ∀ {Θ} (s : Alts (List (RAtom Θ))) {P} → P ∈ᴬ nubᵣ s → P ∈ᴬ s
nubᵣ-∈⁻ (alt P)  m = m
nubᵣ-∈⁻ (P ∷⁺ s) m with withinᵣ? P (nubᵣ s)
... | just _ = inTail (nubᵣ-∈⁻ s m)
... | nothing with m
...   | inHead    = inHead
...   | inTail m' = inTail (nubᵣ-∈⁻ s m')

mul1ᵣ-∈⁻ : ∀ {Θ} (P : List (RAtom Θ)) t {Q} → Q ∈ᴬ mul1ᵣ P t
         → Σ[ P' ∈ List (RAtom Θ) ] ((P' ∈ᴬ t) × (Q ≡ appᵣ P P'))
mul1ᵣ-∈⁻ P (alt P')  inAlt      = P' , inAlt , refl
mul1ᵣ-∈⁻ P (P' ∷⁺ t) inHead     = P' , inHead , refl
mul1ᵣ-∈⁻ P (P' ∷⁺ t) (inTail m) with mul1ᵣ-∈⁻ P t m
... | P'' , m' , e = P'' , inTail m' , e

mulᵣ-∈⁻ : ∀ {Θ} (s t : Alts (List (RAtom Θ))) {Q} → Q ∈ᴬ mulᵣ s t
        → Σ[ P ∈ List (RAtom Θ) ] Σ[ P' ∈ List (RAtom Θ) ]
            ((P ∈ᴬ s) × (P' ∈ᴬ t) × (Q ≡ appᵣ P P'))
mulᵣ-∈⁻ (alt P)  t m with mul1ᵣ-∈⁻ P t m
... | P' , m' , e = P , P' , inAlt , m' , e
mulᵣ-∈⁻ (P ∷⁺ s) t m with ∈ᴬ-⧺⁻ (mul1ᵣ P t) m
... | inj₁ m' with mul1ᵣ-∈⁻ P t m'
...   | P' , m'' , e = P , P' , inHead , m'' , e
mulᵣ-∈⁻ (P ∷⁺ s) t m | inj₂ m' with mulᵣ-∈⁻ s t m'
...   | P₀ , P' , m₀ , m'' , e = P₀ , P' , inTail m₀ , m'' , e

absorbᵣ-∈⁻ : ∀ {Θ} (s : Alts (List (RAtom Θ))) {Q} → Q ∈ᴬ absorbᵣ s → (Q ∈ᴬ s) ⊎ (Q ≡ Tᵣ)
absorbᵣ-∈⁻ s m with topSumᵣ? s
... | just _  = inj₂ (∈ᴬ-alt⁻ m)
... | nothing = inj₁ m

-- The variable atoms of the normal form are the expression's

OccAᵐ : ∀ {Θ} → RAtom Θ → EExp Θ → Set
OccAᵐ (rc _) ε = ⊤
OccAᵐ (rv _) ε = ⊥
OccAᵐ (rm i) ε = occᵉ-e i ε ≡ true

OccAᵣ : ∀ {Θ} → RAtom Θ → RExp Θ → Set
OccAᵣ (rc _) ρ = ⊤
OccAᵣ (rv i) ρ = occʳ-r i ρ ≡ true
OccAᵣ (rm i) ρ = occᵉ-r i ρ ≡ true

module _ {Θ} (ε ε' : EExp Θ) where

  occAᵐˡ : ∀ v → OccAᵐ v ε → OccAᵐ v (ε ·̂ₑ ε')
  occAᵐˡ (rc _) o = tt
  occAᵐˡ (rm i) o = ∨-left (occᵉ-e i ε) _ o

  occAᵐʳ : ∀ v → OccAᵐ v ε' → OccAᵐ v (ε ·̂ₑ ε')
  occAᵐʳ (rc _) o = tt
  occAᵐʳ (rm i) o = ∨-right (occᵉ-e i ε) _ o

  occAᵐˡ⊔ : ∀ v → OccAᵐ v ε → OccAᵐ v (ε ⊔̂ₑ ε')
  occAᵐˡ⊔ (rc _) o = tt
  occAᵐˡ⊔ (rm i) o = ∨-left (occᵉ-e i ε) _ o

  occAᵐʳ⊔ : ∀ v → OccAᵐ v ε' → OccAᵐ v (ε ⊔̂ₑ ε')
  occAᵐʳ⊔ (rc _) o = tt
  occAᵐʳ⊔ (rm i) o = ∨-right (occᵉ-e i ε) _ o

module _ {Θ} (ρ ρ' : RExp Θ) where

  occAˡ : ∀ v → OccAᵣ v ρ → OccAᵣ v (ρ ·̂ᵣ ρ')
  occAˡ (rc _) o = tt
  occAˡ (rv i) o = ∨-left (occʳ-r i ρ) _ o
  occAˡ (rm i) o = ∨-left (occᵉ-r i ρ) _ o

  occAʳ : ∀ v → OccAᵣ v ρ' → OccAᵣ v (ρ ·̂ᵣ ρ')
  occAʳ (rc _) o = tt
  occAʳ (rv i) o = ∨-right (occʳ-r i ρ) _ o
  occAʳ (rm i) o = ∨-right (occᵉ-r i ρ) _ o

  occAˡ⊔ : ∀ v → OccAᵣ v ρ → OccAᵣ v (ρ ⊔̂ᵣ ρ')
  occAˡ⊔ (rc _) o = tt
  occAˡ⊔ (rv i) o = ∨-left (occʳ-r i ρ) _ o
  occAˡ⊔ (rm i) o = ∨-left (occᵉ-r i ρ) _ o

  occAʳ⊔ : ∀ v → OccAᵣ v ρ' → OccAᵣ v (ρ ⊔̂ᵣ ρ')
  occAʳ⊔ (rc _) o = tt
  occAʳ⊔ (rv i) o = ∨-right (occʳ-r i ρ) _ o
  occAʳ⊔ (rm i) o = ∨-right (occᵉ-r i ρ) _ o

occAᵐ→ᵣ : ∀ {Θ} (v : RAtom Θ) (ε : EExp Θ) → OccAᵐ v ε → OccAᵣ v ∣ ε ∣̂ᵉ
occAᵐ→ᵣ (rc _) ε o = tt
occAᵐ→ᵣ (rm i) ε o = o

flatᵐ-var : ∀ {Θ} (ε : EExp Θ) {P v} → P ∈ᴬ flatᵐ ε → v ∈ P → OccAᵐ v ε
flatᵐ-var (evar j)   inAlt (here refl) = dec-true (j ≟ᶠ j) refl
flatᵐ-var (econst c) inAlt a with consᵣ-∈ (rc (mapᵉ c)) [] a
... | inj₁ (_ , refl)  = tt
... | inj₂ (inj₁ refl) = tt
... | inj₂ (inj₂ ())
flatᵐ-var (ε ·̂ₑ ε')  m a with absorbᵣ-∈⁻ (nubᵣ (mulᵣ (flatᵐ ε) (flatᵐ ε'))) m
... | inj₂ refl with Tᵣ-∈ a
...   | _ , refl = tt
flatᵐ-var (ε ·̂ₑ ε')  {v = v} m a | inj₁ m' with mulᵣ-∈⁻ (flatᵐ ε) (flatᵐ ε') (nubᵣ-∈⁻ _ m')
...   | P , P' , m₁ , m₂ , refl with appᵣ-∈ P P' a
...     | inj₁ (_ , refl) = tt
...     | inj₂ (inj₁ a₁)  = occAᵐˡ ε ε' v (flatᵐ-var ε m₁ a₁)
...     | inj₂ (inj₂ a₂)  = occAᵐʳ ε ε' v (flatᵐ-var ε' m₂ a₂)
flatᵐ-var (ε ⊔̂ₑ ε')  m a with absorbᵣ-∈⁻ (nubᵣ (flatᵐ ε ⧺ flatᵐ ε')) m
... | inj₂ refl with Tᵣ-∈ a
...   | _ , refl = tt
flatᵐ-var (ε ⊔̂ₑ ε')  {v = v} m a | inj₁ m' with ∈ᴬ-⧺⁻ (flatᵐ ε) (nubᵣ-∈⁻ _ m')
...   | inj₁ m₁ = occAᵐˡ⊔ ε ε' v (flatᵐ-var ε m₁ a)
...   | inj₂ m₂ = occAᵐʳ⊔ ε ε' v (flatᵐ-var ε' m₂ a)

flatᵣ-var : ∀ {Θ} (ρ : RExp Θ) {P v} → P ∈ᴬ flatᵣ ρ → v ∈ P → OccAᵣ v ρ
flatᵣ-var (rvar j)   inAlt (here refl) = dec-true (j ≟ᶠ j) refl
flatᵣ-var (rconst c) inAlt a with consᵣ-∈ (rc c) [] a
... | inj₁ (_ , refl)  = tt
... | inj₂ (inj₁ refl) = tt
... | inj₂ (inj₂ ())
flatᵣ-var (ρ ·̂ᵣ ρ')  m a with absorbᵣ-∈⁻ (nubᵣ (mulᵣ (flatᵣ ρ) (flatᵣ ρ'))) m
... | inj₂ refl with Tᵣ-∈ a
...   | _ , refl = tt
flatᵣ-var (ρ ·̂ᵣ ρ')  {v = v} m a | inj₁ m' with mulᵣ-∈⁻ (flatᵣ ρ) (flatᵣ ρ') (nubᵣ-∈⁻ _ m')
...   | P , P' , m₁ , m₂ , refl with appᵣ-∈ P P' a
...     | inj₁ (_ , refl) = tt
...     | inj₂ (inj₁ a₁)  = occAˡ ρ ρ' v (flatᵣ-var ρ m₁ a₁)
...     | inj₂ (inj₂ a₂)  = occAʳ ρ ρ' v (flatᵣ-var ρ' m₂ a₂)
flatᵣ-var (ρ ⊔̂ᵣ ρ')  m a with absorbᵣ-∈⁻ (nubᵣ (flatᵣ ρ ⧺ flatᵣ ρ')) m
... | inj₂ refl with Tᵣ-∈ a
...   | _ , refl = tt
flatᵣ-var (ρ ⊔̂ᵣ ρ')  {v = v} m a | inj₁ m' with ∈ᴬ-⧺⁻ (flatᵣ ρ) (nubᵣ-∈⁻ _ m')
...   | inj₁ m₁ = occAˡ⊔ ρ ρ' v (flatᵣ-var ρ m₁ a)
...   | inj₂ m₂ = occAʳ⊔ ρ ρ' v (flatᵣ-var ρ' m₂ a)
flatᵣ-var ∣ ε ∣̂ᵉ     {v = v} m a = occAᵐ→ᵣ v ε (flatᵐ-var ε m a)

varsᵃᵣ-∈ : ∀ {Θ} (l : List (RAtom Θ)) {a} → a ∈ varsᵃᵣ l → a ∈ l
varsᵃᵣ-∈ (rc _ ∷ l) m         = there (varsᵃᵣ-∈ l m)
varsᵃᵣ-∈ (rv i ∷ l) (here e)  = here e
varsᵃᵣ-∈ (rv i ∷ l) (there m) = there (varsᵃᵣ-∈ l m)
varsᵃᵣ-∈ (rm i ∷ l) (here e)  = here e
varsᵃᵣ-∈ (rm i ∷ l) (there m) = there (varsᵃᵣ-∈ l m)

commuteᵣ-∈ : ∀ {Θ} (P : List (RAtom Θ)) {v} → v ∈ commuteᵣ P → IsCᵣ v ⊎ (v ∈ P)
commuteᵣ-∈ P m with consᵣ-∈ (rc (constᵣ P)) (sortBy _<ʳᵃ_ (varsᵃᵣ P)) m
... | inj₁ k         = inj₁ k
... | inj₂ (inj₁ e)  = inj₁ (_ , e)
... | inj₂ (inj₂ m') = inj₂ (varsᵃᵣ-∈ P (sortBy-∈ _<ʳᵃ_ (varsᵃᵣ P) m'))

commSumᵣ-∈⁻ : ∀ {Θ} (c : Maybe (Commutative _≡_ _·ᵣ_)) (s : Alts (List (RAtom Θ))) {Q}
            → Q ∈ᴬ commSumᵣ c s
            → Σ[ P ∈ List (RAtom Θ) ] ((P ∈ᴬ s) × ((Q ≡ P) ⊎ (Q ≡ commuteᵣ P)))
commSumᵣ-∈⁻ nothing  s m = _ , m , inj₁ refl
commSumᵣ-∈⁻ (just _) s m with ∈ᴬ-map⁻ commuteᵣ s (nubᵣ-∈⁻ _ m)
... | P , m' , e = P , m' , inj₂ e

nrmᵣ-var : ∀ {Θ} (ρ : RExp Θ) {Q v} → Q ∈ᴬ nrmᵣ ρ → v ∈ Q → OccAᵣ v ρ
nrmᵣ-var ρ m a with commSumᵣ-∈⁻ ·ᵣ-comm? (flatᵣ ρ) m
... | P , m' , inj₁ refl = flatᵣ-var ρ m' a
... | P , m' , inj₂ refl with commuteᵣ-∈ P a
...   | inj₁ (_ , refl) = tt
...   | inj₂ a'         = flatᵣ-var ρ m' a'

-- A product with the top among its factors, replaced by the top

absorbProdᵣ-∈ : ∀ {Θ} (P : List (RAtom Θ)) {v} → v ∈ absorbProdᵣ P → IsCᵣ v ⊎ (v ∈ P)
absorbProdᵣ-∈ P m with Is-just? uᵣ-least?
... | nothing = inj₂ m
... | just ij with topProdᵣ? ij P
...   | just _  = inj₁ (Tᵣ-∈ m)
...   | nothing = inj₂ m

-- Skeletons and slots

atomsᵣ-var : ∀ {Θ vs} (s : Gᵣ.Slots {Θ} vs) {v} → v ∈ atomsᵣ s
           → IsCᵣ v ⊎ (Σ[ a ∈ RVAtom Θ ] ((a ∈ vs) × (v ≡ varAtomᵣ a)))
atomsᵣ-var Gᵣ.⌜ c ⌝ w with consᵣ-∈ (rc c) [] w
... | inj₁ k         = inj₁ k
... | inj₂ (inj₁ e)  = inj₁ (c , e)
... | inj₂ (inj₂ ())
atomsᵣ-var (Gᵣ._▸_ {a} c s) w with consᵣ-∈ (rc c) (varAtomᵣ a ∷ atomsᵣ s) w
... | inj₁ k                = inj₁ k
... | inj₂ (inj₁ e)         = inj₁ (c , e)
... | inj₂ (inj₂ (here e))  = inj₂ (a , here refl , e)
... | inj₂ (inj₂ (there w')) with atomsᵣ-var s w'
...   | inj₁ k            = inj₁ k
...   | inj₂ (a' , m , e) = inj₂ (a' , there m , e)

slotsᵣ-var : ∀ {Θ} (m : Maybe R) (P : List (RAtom Θ)) {a} → a ∈ proj₁ (slotsᵣ m P)
           → varAtomᵣ a ∈ P
slotsᵣ-var m (rc c ∷ P) w           = there (slotsᵣ-var _ P w)
slotsᵣ-var m (rv j ∷ P) (here refl) = here refl
slotsᵣ-var m (rv j ∷ P) (there w)   = there (slotsᵣ-var nothing P w)
slotsᵣ-var m (rm j ∷ P) (here refl) = here refl
slotsᵣ-var m (rm j ∷ P) (there w)   = there (slotsᵣ-var nothing P w)

-- The variables of a read-back, of either sort

⟦⟧ʳᵖ-rv : ∀ {Θ} (P : List (RAtom Θ)) {i} → occʳ-r i ⟦ P ⟧ʳᵖ ≡ true → rv i ∈ P
⟦⟧ʳᵖ-rv []              ()
⟦⟧ʳᵖ-rv (rc c ∷ [])     ()
⟦⟧ʳᵖ-rv (rv j ∷ [])     {i} q = here (cong rv (true-dec (i ≟ᶠ j) q))
⟦⟧ʳᵖ-rv (rm j ∷ [])     ()
⟦⟧ʳᵖ-rv (rc c ∷ b ∷ as) q = there (⟦⟧ʳᵖ-rv (b ∷ as) q)
⟦⟧ʳᵖ-rv (rm j ∷ b ∷ as) q = there (⟦⟧ʳᵖ-rv (b ∷ as) q)
⟦⟧ʳᵖ-rv {Θ} (rv j ∷ bas@(b ∷ as)) {i} q =
  [ (λ q' → here (cong rv (true-dec (i ≟ᶠ j) q'))) , (λ q' → there (⟦⟧ʳᵖ-rv bas q')) ]′
    (∨-true (occʳ-r i (rvar {Θ} j)) (occʳ-r i ⟦ bas ⟧ʳᵖ) q)

⟦⟧ʳᵖ-rm : ∀ {Θ} (P : List (RAtom Θ)) {i} → occᵉ-r i ⟦ P ⟧ʳᵖ ≡ true → rm i ∈ P
⟦⟧ʳᵖ-rm []              ()
⟦⟧ʳᵖ-rm (rc c ∷ [])     ()
⟦⟧ʳᵖ-rm (rv j ∷ [])     ()
⟦⟧ʳᵖ-rm (rm j ∷ [])     {i} q = here (cong rm (true-dec (i ≟ᶠ j) q))
⟦⟧ʳᵖ-rm (rc c ∷ b ∷ as) q = there (⟦⟧ʳᵖ-rm (b ∷ as) q)
⟦⟧ʳᵖ-rm (rv j ∷ b ∷ as) q = there (⟦⟧ʳᵖ-rm (b ∷ as) q)
⟦⟧ʳᵖ-rm {Θ} (rm j ∷ bas@(b ∷ as)) {i} q =
  [ (λ q' → here (cong rm (true-dec (i ≟ᶠ j) q'))) , (λ q' → there (⟦⟧ʳᵖ-rm bas q')) ]′
    (∨-true (occᵉ-r i ∣ evar {Θ} j ∣̂ᵉ) (occᵉ-r i ⟦ bas ⟧ʳᵖ) q)

⟦⟧ʳᵖ⁺-rv : ∀ {Θ} (s : Alts (List (RAtom Θ))) {i} → occʳ-r i ⟦ s ⟧ʳᵖ⁺ ≡ true
         → Σ[ P ∈ List (RAtom Θ) ] ((P ∈ᴬ s) × (rv i ∈ P))
⟦⟧ʳᵖ⁺-rv (alt P)  q = P , inAlt , ⟦⟧ʳᵖ-rv P q
⟦⟧ʳᵖ⁺-rv (P ∷⁺ s) {i} q with ∨-true (occʳ-r i ⟦ P ⟧ʳᵖ) _ q
... | inj₁ q' = P , inHead , ⟦⟧ʳᵖ-rv P q'
... | inj₂ q' with ⟦⟧ʳᵖ⁺-rv s q'
...   | P' , m , a = P' , inTail m , a

⟦⟧ʳᵖ⁺-rm : ∀ {Θ} (s : Alts (List (RAtom Θ))) {i} → occᵉ-r i ⟦ s ⟧ʳᵖ⁺ ≡ true
         → Σ[ P ∈ List (RAtom Θ) ] ((P ∈ᴬ s) × (rm i ∈ P))
⟦⟧ʳᵖ⁺-rm (alt P)  q = P , inAlt , ⟦⟧ʳᵖ-rm P q
⟦⟧ʳᵖ⁺-rm (P ∷⁺ s) {i} q with ∨-true (occᵉ-r i ⟦ P ⟧ʳᵖ) _ q
... | inj₁ q' = P , inHead , ⟦⟧ʳᵖ-rm P q'
... | inj₂ q' with ⟦⟧ʳᵖ⁺-rm s q'
...   | P' , m , a = P' , inTail m , a

-- Every variable atom of an alternative of the canonical form is one of
-- the expression

canonSumᵣ-var : ∀ {Θ} (ρ : RExp Θ) {P v} → P ∈ᴬ canonSumᵣ (nrmᵣ ρ) → v ∈ P → OccAᵣ v ρ
canonSumᵣ-var {Θ} ρ {v = v} m w
  with ∈ᴬ-map⁻ (λ P → atomsᵣ (proj₂ P)) (Mᵣ.maximal (toProdsᵣ (mapᴬ absorbProdᵣ (nrmᵣ ρ)))) m
... | (vs , s) , m' , refl with atomsᵣ-var s w
...   | inj₁ (c , refl)      = tt
...   | inj₂ (a , ma , refl) = sk m' ma
  where
    Sk : List (RVAtom Θ) → Set
    Sk vs = ∀ {a} → a ∈ vs → OccAᵣ (varAtomᵣ a) ρ

    open SkEᵣ {Θ} Sk
    open Pr (∅ᴴ ⊩_≾̂ᵣ_) ≡̂ᵣ-absorb (λ P P' → decide≾ᵣ {Q = ∅ᴴ} Gᵣ.⟦ P ⟧ᵖ Gᵣ.⟦ P' ⟧ᵖ)

    back : ∀ Q₀ {a} → varAtomᵣ a ∈ absorbProdᵣ Q₀ → Q₀ ∈ᴬ nrmᵣ ρ → OccAᵣ (varAtomᵣ a) ρ
    back Q₀ {a} w' mQ₀ with absorbProdᵣ-∈ Q₀ w'
    back Q₀ {vr _} w' mQ₀ | inj₁ (_ , ())
    back Q₀ {vm _} w' mQ₀ | inj₁ (_ , ())
    ... | inj₂ w'' = nrmᵣ-var ρ mQ₀ w''

    ins : ∀ {P} → P ∈ᴬ toProdsᵣ (mapᴬ absorbProdᵣ (nrmᵣ ρ)) → SkP P
    ins m₀ with ∈ᴬ-map⁻ (slotsᵣ nothing) (mapᴬ absorbProdᵣ (nrmᵣ ρ)) m₀
    ... | Q , mQ , refl with ∈ᴬ-map⁻ absorbProdᵣ (nrmᵣ ρ) mQ
    ...   | Q₀ , mQ₀ , refl = λ w' → back Q₀ (slotsᵣ-var nothing _ w') mQ₀

    sk : ∀ {P} → P ∈ᴬ Mᵣ.maximal (toProdsᵣ (mapᴬ absorbProdᵣ (nrmᵣ ρ))) → SkP P
    sk = maximal-sk (toProdsᵣ (mapᴬ absorbProdᵣ (nrmᵣ ρ))) ins

canonᵣ-occʳ : ∀ {Θ} (ρ : RExp Θ) {i} → occʳ-r i (canonᵣ ρ) ≡ true → occʳ-r i ρ ≡ true
canonᵣ-occʳ ρ q with ⟦⟧ʳᵖ⁺-rv (canonSumᵣ (nrmᵣ ρ)) q
... | P , m , w = canonSumᵣ-var ρ m w

canonᵣ-occᵉ : ∀ {Θ} (ρ : RExp Θ) {i} → occᵉ-r i (canonᵣ ρ) ≡ true → occᵉ-r i ρ ≡ true
canonᵣ-occᵉ ρ q with ⟦⟧ʳᵖ⁺-rm (canonSumᵣ (nrmᵣ ρ)) q
... | P , m , w = canonSumᵣ-var ρ m w

-- A whole unknown

nrmᵣ-whole : ∀ {Θ} (k : RVar Θ) → nrmᵣ (rvar k) ≡ alt {List (RAtom Θ)} (rv k ∷ [])
nrmᵣ-whole k with ·ᵣ-comm?
... | nothing = refl
... | just _ with uᵣ ≡ᵣ? uᵣ
...   | yes _ = refl
...   | no ¬p = ⊥-elim (¬p refl)

absorbProdᵣ-whole : ∀ {Θ} (k : RVar Θ) → absorbProdᵣ {Θ} (rv k ∷ []) ≡ rv k ∷ []
absorbProdᵣ-whole k with Is-just? uᵣ-least?
... | nothing = refl
... | just _  = refl

atoms-wholeᵣ : ∀ {Θ} (k : RVar Θ)
             → atomsᵣ (Gᵣ._▸_ {Θ} {a = vr k} uᵣ (Gᵣ.⌜_⌝ {Θ} uᵣ)) ≡ rv k ∷ []
atoms-wholeᵣ k with uᵣ ≡ᵣ? uᵣ
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

canonᵣ-var : ∀ {Θ} (k : RVar Θ) → canonᵣ (rvar k) ≡ rvar k
canonᵣ-var {Θ} k =
  trans (cong (λ s → ⟦ canonSumᵣ {Θ} s ⟧ʳᵖ⁺) (nrmᵣ-whole k))
  (trans (cong (λ (P : List (RAtom Θ)) → ⟦ fromProdsᵣ (Mᵣ.maximal {Θ} (toProdsᵣ (alt P))) ⟧ʳᵖ⁺)
               (absorbProdᵣ-whole k))
         (cong (λ l → ⟦ alt {List (RAtom Θ)} l ⟧ʳᵖ⁺) (atoms-wholeᵣ k)))

------------------------------------------------------------------------
-- Good sides

module _ {Θ Ψ} {P : Subst Θ Ψ} where

  goodₑ-canon : ∀ {ε} → Goodₑ P ε → Goodₑ P (canonₑ ε)
  goodₑ-canon     (whole k) = subst (Goodₑ P) (sym (canonₑ-var k)) (whole k)
  goodₑ-canon {ε} (outer o) = outer (λ q → o (canonₑ-occ ε q))

  goodᵣ-canon : ∀ {ρ} → Goodᵣ P ρ → Goodᵣ P (canonᵣ ρ)
  goodᵣ-canon     (whole k)        = subst (Goodᵣ P) (sym (canonᵣ-var k)) (whole k)
  goodᵣ-canon {ρ} (outer (oe , or)) =
    outer ((λ q → oe (canonᵣ-occᵉ ρ q)) , (λ q → or (canonᵣ-occʳ ρ q)))

------------------------------------------------------------------------
-- Split orderings: each piece is an alternative of the canonical left
-- side below the canonical right side

splits-∈ : ∀ {Ψ} {X : Set} {Pr : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set}
         → (f : (a : X) → Pieces Pr a) → (l : List X) → ∀ {b} → b ∈ Split.out (splits f l)
         → Σ[ a ∈ X ] ((a ∈ l) × (b ∈ Pieces.parts (f a)))
splits-∈ f (a ∷ l) m with ∈-++⁻ (Pieces.parts (f a)) m
... | inj₁ m' = a , here refl , m'
... | inj₂ m' with splits-∈ f l m'
...   | a' , ma , mb = a' , there ma , mb

partsʳ-∈ : ∀ {Ψ} (s : Alts (List (RAtom Ψ))) (y : RExp Ψ) {x z} → (x , z) ∈ partsʳ s y
         → (z ≡ y) × (Σ[ p ∈ List (RAtom Ψ) ] ((p ∈ᴬ s) × (x ≡ ⟦ p ⟧ʳᵖ)))
partsʳ-∈ (alt p)  y (here refl) = refl , p , inAlt , refl
partsʳ-∈ (p ∷⁺ s) y (here refl) = refl , p , inHead , refl
partsʳ-∈ (p ∷⁺ s) y (there m) with partsʳ-∈ s y m
... | e , p' , m' , e' = e , p' , inTail m' , e'

partsₑ-∈ : ∀ {Ψ} (s : Alts (List (EAtom Ψ))) (y : EExp Ψ) {x z} → (x , z) ∈ partsₑ s y
         → (z ≡ y) × (Σ[ p ∈ List (EAtom Ψ) ] ((p ∈ᴬ s) × (x ≡ ⟦ p ⟧ᵉᵖ)))
partsₑ-∈ (alt p)  y (here refl) = refl , p , inAlt , refl
partsₑ-∈ (p ∷⁺ s) y (here refl) = refl , p , inHead , refl
partsₑ-∈ (p ∷⁺ s) y (there m) with partsₑ-∈ s y m
... | e , p' , m' , e' = e , p' , inTail m' , e'

-- The greater side of a piece is the canonical greater side

piecesʳ-great : ∀ {Ψ} (x y : RExp Ψ) {x' y'} → (x' , y') ∈ Pieces.parts (piecesʳ (x , y))
              → y' ≡ canonᵣ y
piecesʳ-great x y m = proj₁ (partsʳ-∈ (canonSumᵣ (nrmᵣ x)) (canonᵣ y) m)

piecesᵉ-great : ∀ {Ψ} (x y : EExp Ψ) {x' y'} → (x' , y') ∈ Pieces.parts (piecesᵉ (x , y))
              → y' ≡ canonₑ y
piecesᵉ-great x y m = proj₁ (partsₑ-∈ (canonSumₑ (nrmₑ x)) (canonₑ y) m)

-- The smaller side of a piece mentions no unknown the smaller side of
-- the ordering does not

piecesʳ-lessʳ : ∀ {Ψ} (x y : RExp Ψ) {x' y' i} → (x' , y') ∈ Pieces.parts (piecesʳ (x , y))
              → occʳ-r i x' ≡ true → occʳ-r i x ≡ true
piecesʳ-lessʳ x y m q with partsʳ-∈ (canonSumᵣ (nrmᵣ x)) (canonᵣ y) m
... | _ , p , mp , refl = canonSumᵣ-var x mp (⟦⟧ʳᵖ-rv p q)

piecesʳ-lessᵉ : ∀ {Ψ} (x y : RExp Ψ) {x' y' i} → (x' , y') ∈ Pieces.parts (piecesʳ (x , y))
              → occᵉ-r i x' ≡ true → occᵉ-r i x ≡ true
piecesʳ-lessᵉ x y m q with partsʳ-∈ (canonSumᵣ (nrmᵣ x)) (canonᵣ y) m
... | _ , p , mp , refl = canonSumᵣ-var x mp (⟦⟧ʳᵖ-rm p q)

piecesᵉ-less : ∀ {Ψ} (x y : EExp Ψ) {x' y' i} → (x' , y') ∈ Pieces.parts (piecesᵉ (x , y))
             → occᵉ-e i x' ≡ true → occᵉ-e i x ≡ true
piecesᵉ-less x y m q with partsₑ-∈ (canonSumₑ (nrmₑ x)) (canonₑ y) m
... | _ , p , mp , refl = canonSumₑ-av x mp (⟦⟧ᵉᵖ-av p q)

-- Good greater sides stay good

module _ {Θ Ψ} {P : Subst Θ Ψ} where

  splitsʳ-good : (l : List (RExp Ψ × RExp Ψ)) → (∀ {x y} → (x , y) ∈ l → Goodᵣ P y)
               → ∀ {x y} → (x , y) ∈ Split.out (splits piecesʳ l) → Goodᵣ P y
  splitsʳ-good l g m with splits-∈ piecesʳ l m
  ... | (x₀ , y₀) , m₀ , mp =
        subst (Goodᵣ P) (sym (piecesʳ-great x₀ y₀ mp)) (goodᵣ-canon (g m₀))

  splitsᵉ-good : (l : List (EExp Ψ × EExp Ψ)) → (∀ {x y} → (x , y) ∈ l → Goodₑ P y)
               → ∀ {x y} → (x , y) ∈ Split.out (splits piecesᵉ l) → Goodₑ P y
  splitsᵉ-good l g m with splits-∈ piecesᵉ l m
  ... | (x₀ , y₀) , m₀ , mp =
        subst (Goodₑ P) (sym (piecesᵉ-great x₀ y₀ mp)) (goodₑ-canon (g m₀))

  -- A residual with its orderings split, whatever its disjunctions

  resinv-normal : ∀ {R : Resid Ψ} {ds' : List (OVType Ψ × RExp Ψ)} → ResInv P R
                → ResInv P (resid (Split.out (splits piecesʳ (rs R)))
                                  (Split.out (splits piecesᵉ (es R)))
                                  (ts R) (ss R) ds' (dfs R))
  resinv-normal {R} r =
    mkResInv (inv-ss r) (splitsʳ-good (rs R) (I1′ʳ r)) (splitsᵉ-good (es R) (I1′ᵉ r)) (I5 r)

-- The orderings of a canonical hypothesis set

canonᴴ-ordʳ : ∀ {Ψ} (Q : Hyps Ψ) {x' y'} → (x' , y') ∈ ordᵣ (canonᴴ Q)
            → Σ[ a ∈ RExp Ψ × RExp Ψ ] ((a ∈ ordᵣ Q) × ((x' , y') ∈ Pieces.parts (piecesʳ a)))
canonᴴ-ordʳ Q = splits-∈ piecesʳ (ordᵣ Q)

canonᴴ-ordᵉ : ∀ {Ψ} (Q : Hyps Ψ) {x' y'} → (x' , y') ∈ ordₑ (canonᴴ Q)
            → Σ[ a ∈ EExp Ψ × EExp Ψ ] ((a ∈ ordₑ Q) × ((x' , y') ∈ Pieces.parts (piecesᵉ a)))
canonᴴ-ordᵉ Q = splits-∈ piecesᵉ (ordₑ Q)
