------------------------------------------------------------------
-- The alternatives of a normal form                              --
--                                                                --
-- Every product of `nrmₑ`/`nrmᵣ` is in normal form: no constant   --
-- that is the unit, and no two constants side by side. Its       --
-- variables are those of the expression. An alternative of one   --
-- side of a join is an alternative of the join, unless the join  --
-- is the top.                                                    --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to isJust)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Algebra.Definitions using (Commutative)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Invariants.Flat (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S

open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-e; occᵉ-r; occʳ-r)
open import TypeInference.SolverImpl.Core.Rigid S using (∨-left; ∨-right; dec-true)
open import TypeInference.SolverImpl.Eliminate S using (joinₑ; joinᵣ)
open import TypeInference.SolverImpl.Product S
open import TypeInference.SolverImpl.Invariants.Sums S

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
insertBy-∈ _<_ a (b ∷ bs) m | false | here e  = inj₁ e
insertBy-∈ _<_ a (b ∷ bs) m | false | there m' = inj₂ m'

sortBy-∈ : ∀ {A : Set} (_<_ : A → A → 𝔹) (l : List A) {x} → x ∈ sortBy _<_ l → x ∈ l
sortBy-∈ _<_ (a ∷ as) m with insertBy-∈ _<_ a (sortBy _<_ as) m
... | inj₁ e  = here e
... | inj₂ m' = there (sortBy-∈ _<_ as m')

nothing-just : ∀ {A : Set} {m : Maybe A} → m ≡ nothing → Is-just m → ⊥
nothing-just refl ()

------------------------------------------------------------------------
-- Effect grades

-- The top, as its own normal form

Tₑ : ∀ {Θ} → List (EAtom Θ)
Tₑ = consₑ (ac ⊤ₑ) []

-- Products in normal form: starting with a variable or empty, or with
-- a constant that is not the unit and then so

mutual

  data NFᵛₑ {Θ} : List (EAtom Θ) → Set where
    nf[] : NFᵛₑ []
    nfv  : ∀ i {l} → NFₑ l → NFᵛₑ (av i ∷ l)

  data NFₑ {Θ} : List (EAtom Θ) → Set where
    nfᵛ : ∀ {l} → NFᵛₑ l → NFₑ l
    nfc : ∀ {c l} → ¬ (c ≡ uₑ) → NFᵛₑ l → NFₑ (ac c ∷ l)

consc-NFₑ : ∀ {Θ} c {l : List (EAtom Θ)} → NFᵛₑ l → NFₑ (consₑ (ac c) l)
consc-NFₑ c nf[] with c ≡ₑ? uₑ
... | yes _ = nfᵛ nf[]
... | no ¬p = nfc ¬p nf[]
consc-NFₑ c (nfv i n) with c ≡ₑ? uₑ
... | yes _ = nfᵛ (nfv i n)
... | no ¬p = nfc ¬p (nfv i n)

consₑ-NF : ∀ {Θ} (a : EAtom Θ) {l} → NFₑ l → NFₑ (consₑ a l)
consₑ-NF (av i) n               = nfᵛ (nfv i n)
consₑ-NF (ac c) (nfᵛ v)         = consc-NFₑ c v
consₑ-NF (ac c) (nfc {d} _ v)   = consc-NFₑ (c ·ₑ d) v

appₑ-NF : ∀ {Θ} (as : List (EAtom Θ)) {ys} → NFₑ ys → NFₑ (appₑ as ys)
appₑ-NF []       n = n
appₑ-NF (a ∷ as) n = consₑ-NF a (appₑ-NF as n)

-- A variable of a product comes from the atoms it is built from

consₑ-av : ∀ {Θ} (a : EAtom Θ) (l : List (EAtom Θ)) {i} → av i ∈ consₑ a l → (a ≡ av i) ⊎ (av i ∈ l)
consₑ-av (ac c) (ac d ∷ l) m with consₑ-av (ac (c ·ₑ d)) l m
... | inj₁ ()
... | inj₂ m' = inj₂ (there m')
consₑ-av (ac c) [] m with c ≡ₑ? uₑ | m
... | yes _ | ()
... | no _  | there ()
consₑ-av (ac c) (av j ∷ l) m with c ≡ₑ? uₑ | m
... | yes _ | m'        = inj₂ m'
... | no _  | there m'  = inj₂ m'
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

-- Sums

withinₑ-∈ : ∀ {Θ} (P : List (EAtom Θ)) s {p} → withinₑ? P s ≡ just p → P ∈ᴬ s
withinₑ-∈ P (alt Q) e with P ≟ᵖₑ Q
withinₑ-∈ P (alt Q) e  | yes refl = inAlt
withinₑ-∈ P (alt Q) () | no _
withinₑ-∈ P (Q ∷⁺ t) e with P ≟ᵖₑ Q
... | yes refl = inHead
... | no _ with withinₑ? P t in e'
...   | just _ = inTail (withinₑ-∈ P t e')
withinₑ-∈ P (Q ∷⁺ t) () | no _ | nothing

nubₑ-∈ : ∀ {Θ} (s : Alts (List (EAtom Θ))) {P} → P ∈ᴬ s → P ∈ᴬ nubₑ s
nubₑ-∈ (alt P)  m = m
nubₑ-∈ (P ∷⁺ s) inHead with withinₑ? P (nubₑ s) in e
... | just _  = withinₑ-∈ P (nubₑ s) e
... | nothing = inHead
nubₑ-∈ (P ∷⁺ s) (inTail m) with withinₑ? P (nubₑ s)
... | just _  = nubₑ-∈ s m
... | nothing = inTail (nubₑ-∈ s m)

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
        → Σ[ P ∈ List (EAtom Θ) ] Σ[ P' ∈ List (EAtom Θ) ] ((P ∈ᴬ s) × (P' ∈ᴬ t) × (Q ≡ appₑ P P'))
mulₑ-∈⁻ (alt P)  t m with mul1ₑ-∈⁻ P t m
... | P' , m' , e = P , P' , inAlt , m' , e
mulₑ-∈⁻ (P ∷⁺ s) t m with ∈-⧺⁻ (mul1ₑ P t) m
... | inj₁ m' with mul1ₑ-∈⁻ P t m'
...   | P' , m'' , e = P , P' , inHead , m'' , e
mulₑ-∈⁻ (P ∷⁺ s) t m | inj₂ m' with mulₑ-∈⁻ s t m'
...   | P₀ , P' , m₀ , m'' , e = P₀ , P' , inTail m₀ , m'' , e

absorbₑ-∈⁻ : ∀ {Θ} (s : Alts (List (EAtom Θ))) {Q} → Q ∈ᴬ absorbₑ s → (Q ∈ᴬ s) ⊎ (Q ≡ Tₑ)
absorbₑ-∈⁻ s m with topSumₑ? s
... | just _  = inj₂ (∈-alt⁻ m)
... | nothing = inj₁ m

-- The top is found

isTop-Tₑ : ∀ {Θ} → Is-just (isTopₑ? (Tₑ {Θ}))
isTop-Tₑ with ⊤ₑ ≡ₑ? uₑ
... | yes p with uₑ ≡ₑ? ⊤ₑ
...   | yes _ = isJust tt
...   | no ¬q = ⊥-elim (¬q (sym p))
isTop-Tₑ | no _ with ⊤ₑ ≡ₑ? ⊤ₑ
...   | yes _ = isJust tt
...   | no ¬q = ⊥-elim (¬q refl)

topSumₑ-∈ : ∀ {Θ} (s : Alts (List (EAtom Θ))) {P} → Is-just (isTopₑ? P) → P ∈ᴬ s
          → Is-just (topSumₑ? s)
topSumₑ-∈ (alt P) j inAlt with isTopₑ? P | j
... | just _ | _ = isJust tt
topSumₑ-∈ (P ∷⁺ s) j inHead with isTopₑ? P | j
... | just _ | _ = isJust tt
topSumₑ-∈ (P ∷⁺ s) j (inTail m) with isTopₑ? P
... | just _ = isJust tt
... | nothing with topSumₑ? s | topSumₑ-∈ s j m
...   | just _ | _ = isJust tt

-- Normal form throughout

flatₑ-NF : ∀ {Θ} (ε : EExp Θ) {P} → P ∈ᴬ flatₑ ε → NFₑ P
flatₑ-NF (evar i)   inAlt = nfᵛ (nfv i (nfᵛ nf[]))
flatₑ-NF (econst c) inAlt = consₑ-NF (ac c) (nfᵛ nf[])
flatₑ-NF (ε ·̂ₑ ε')  m with absorbₑ-∈⁻ (nubₑ (mulₑ (flatₑ ε) (flatₑ ε'))) m
... | inj₂ refl = consₑ-NF (ac ⊤ₑ) (nfᵛ nf[])
... | inj₁ m' with mulₑ-∈⁻ (flatₑ ε) (flatₑ ε') (nubₑ-∈⁻ _ m')
...   | P , P' , _ , m₂ , refl = appₑ-NF P (flatₑ-NF ε' m₂)
flatₑ-NF (ε ⊔̂ₑ ε')  m with absorbₑ-∈⁻ (nubₑ (flatₑ ε ⧺ flatₑ ε')) m
... | inj₂ refl = consₑ-NF (ac ⊤ₑ) (nfᵛ nf[])
... | inj₁ m' with ∈-⧺⁻ (flatₑ ε) (nubₑ-∈⁻ _ m')
...   | inj₁ m₁ = flatₑ-NF ε m₁
...   | inj₂ m₂ = flatₑ-NF ε' m₂

IsVₑ : ∀ {Θ} → EAtom Θ → Set
IsVₑ a = Σ[ i ∈ _ ] (a ≡ av i)

varsᵃₑ-V : ∀ {Θ} (l : List (EAtom Θ)) {a} → a ∈ varsᵃₑ l → IsVₑ a
varsᵃₑ-V (ac _ ∷ l) m         = varsᵃₑ-V l m
varsᵃₑ-V (av i ∷ l) (here e)  = i , e
varsᵃₑ-V (av i ∷ l) (there m) = varsᵃₑ-V l m

varsᵃₑ-∈ : ∀ {Θ} (l : List (EAtom Θ)) {a} → a ∈ varsᵃₑ l → a ∈ l
varsᵃₑ-∈ (ac _ ∷ l) m         = there (varsᵃₑ-∈ l m)
varsᵃₑ-∈ (av i ∷ l) (here e)  = here e
varsᵃₑ-∈ (av i ∷ l) (there m) = there (varsᵃₑ-∈ l m)

allV-NFₑ : ∀ {Θ} (l : List (EAtom Θ)) → (∀ {a} → a ∈ l → IsVₑ a) → NFᵛₑ l
allV-NFₑ []      f = nf[]
allV-NFₑ (a ∷ l) f with f (here refl)
... | i , refl = nfv i (nfᵛ (allV-NFₑ l (λ m → f (there m))))

commuteₑ-NF : ∀ {Θ} (P : List (EAtom Θ)) → NFₑ (commuteₑ P)
commuteₑ-NF P =
  consₑ-NF (ac (constₑ P))
    (nfᵛ (allV-NFₑ _ (λ m → varsᵃₑ-V P (sortBy-∈ _<ᵉᵃ_ (varsᵃₑ P) m))))

commuteₑ-av : ∀ {Θ} (P : List (EAtom Θ)) {i} → av i ∈ commuteₑ P → av i ∈ P
commuteₑ-av P m with consₑ-av (ac (constₑ P)) (sortBy _<ᵉᵃ_ (varsᵃₑ P)) m
... | inj₁ ()
... | inj₂ m' = varsᵃₑ-∈ P (sortBy-∈ _<ᵉᵃ_ (varsᵃₑ P) m')

commSumₑ-∈⁻ : ∀ {Θ} (c : Maybe (Commutative _≡_ _·ₑ_)) (s : Alts (List (EAtom Θ))) {Q}
            → Q ∈ᴬ commSumₑ c s → Σ[ P ∈ List (EAtom Θ) ] ((P ∈ᴬ s) × ((Q ≡ P) ⊎ (Q ≡ commuteₑ P)))
commSumₑ-∈⁻ nothing  s m = _ , m , inj₁ refl
commSumₑ-∈⁻ (just _) s m with ∈-map⁻ commuteₑ s (nubₑ-∈⁻ _ m)
... | P , m' , e = P , m' , inj₂ e

nrmₑ-NF : ∀ {Θ} (ε : EExp Θ) {Q} → Q ∈ᴬ nrmₑ ε → NFₑ Q
nrmₑ-NF ε m with commSumₑ-∈⁻ ·ₑ-comm? (flatₑ ε) m
... | P , m' , inj₁ refl = flatₑ-NF ε m'
... | P , m' , inj₂ refl = commuteₑ-NF P

-- The variables of the alternatives are the expression's

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
... | inj₁ m' with ∈-⧺⁻ (flatₑ ε) (nubₑ-∈⁻ _ m')
...   | inj₁ m₁ = ∨-left (occᵉ-e i ε) _ (flatₑ-av ε m₁ a)
...   | inj₂ m₂ = ∨-right (occᵉ-e i ε) _ (flatₑ-av ε' m₂ a)

nrmₑ-av : ∀ {Θ} (ε : EExp Θ) {Q i} → Q ∈ᴬ nrmₑ ε → av i ∈ Q → occᵉ-e i ε ≡ true
nrmₑ-av ε m a with commSumₑ-∈⁻ ·ₑ-comm? (flatₑ ε) m
... | P , m' , inj₁ refl = flatₑ-av ε m' a
... | P , m' , inj₂ refl = flatₑ-av ε m' (commuteₑ-av P a)

-- An alternative of one side of a join is one of the join, unless the
-- join is the top

Coversₑ : ∀ {Θ} → Alts (List (EAtom Θ)) → List (EAtom Θ) → Set
Coversₑ s P = (P ∈ᴬ s) ⊎ (s ≡ alt Tₑ)

flatₑ-⊔ˡ : ∀ {Θ} (x y : EExp Θ) {P} → Coversₑ (flatₑ x) P → Coversₑ (flatₑ (x ⊔̂ₑ y)) P
flatₑ-⊔ˡ x y c with topSumₑ? (nubₑ (flatₑ x ⧺ flatₑ y)) in e
... | just _  = inj₂ refl
... | nothing with c
...   | inj₁ m = inj₁ (nubₑ-∈ _ (∈-⧺ˡ m))
...   | inj₂ q with topSumₑ-∈ (nubₑ (flatₑ x ⧺ flatₑ y)) isTop-Tₑ
                   (nubₑ-∈ _ (∈-⧺ˡ (subst (Tₑ ∈ᴬ_) (sym q) inAlt)))
...     | j = ⊥-elim (nothing-just e j)

flatₑ-⊔ʳ : ∀ {Θ} (x y : EExp Θ) {P} → Coversₑ (flatₑ y) P → Coversₑ (flatₑ (x ⊔̂ₑ y)) P
flatₑ-⊔ʳ x y c with topSumₑ? (nubₑ (flatₑ x ⧺ flatₑ y)) in e
... | just _  = inj₂ refl
... | nothing with c
...   | inj₁ m = inj₁ (nubₑ-∈ _ (∈-⧺ʳ (flatₑ x) m))
...   | inj₂ q with topSumₑ-∈ (nubₑ (flatₑ x ⧺ flatₑ y)) isTop-Tₑ
                   (nubₑ-∈ _ (∈-⧺ʳ (flatₑ x) (subst (Tₑ ∈ᴬ_) (sym q) inAlt)))
...     | j = ⊥-elim (nothing-just e j)

flatₑ-joinˡ : ∀ {Θ} (z : EExp Θ) xs {P} → Coversₑ (flatₑ z) P → Coversₑ (flatₑ (joinₑ z xs)) P
flatₑ-joinˡ z []       c = c
flatₑ-joinˡ z (x ∷ xs) c = flatₑ-joinˡ (z ⊔̂ₑ x) xs (flatₑ-⊔ˡ z x c)

flatₑ-join : ∀ {Θ} (x₀ : EExp Θ) xs {x P} → x ∈ x₀ ∷ xs → P ∈ᴬ flatₑ x
           → Coversₑ (flatₑ (joinₑ x₀ xs)) P
flatₑ-join x₀ xs        (here refl)         m = flatₑ-joinˡ x₀ xs (inj₁ m)
flatₑ-join x₀ (x₁ ∷ xs) (there (here refl)) m = flatₑ-joinˡ (x₀ ⊔̂ₑ x₁) xs (flatₑ-⊔ʳ x₀ x₁ (inj₁ m))
flatₑ-join x₀ (x₁ ∷ xs) (there (there w))   m = flatₑ-join (x₀ ⊔̂ₑ x₁) xs (there w) m

-- ... and so at the normal forms, the top being then one constant

TopAltₑ : ∀ {Θ} → List (EAtom Θ) → Set
TopAltₑ Q = Σ[ c ∈ E ] ((Q ≡ consₑ (ac c) []) × (⊤ₑ ≾ₑ c))

commute-Tₑ : ∀ {Θ} → TopAltₑ (commuteₑ (Tₑ {Θ}))
commute-Tₑ with ⊤ₑ ≡ₑ? uₑ
... | yes p = uₑ , refl , ≾ₑ-reflexive p
... | no _  = ⊤ₑ ·ₑ uₑ , refl , ≾ₑ-reflexive (sym (·ₑ-identityʳ ⊤ₑ))

nrmₑ-join : ∀ {Θ} (x₀ : EExp Θ) xs {x Q} → x ∈ x₀ ∷ xs → Q ∈ᴬ nrmₑ x
          → Σ[ Q' ∈ List (EAtom Θ) ] ((Q' ∈ᴬ nrmₑ (joinₑ x₀ xs)) × ((Q' ≡ Q) ⊎ TopAltₑ Q'))
nrmₑ-join x₀ xs {x} w m with ·ₑ-comm?
... | nothing with flatₑ-join x₀ xs w m
...   | inj₁ m' = _ , m' , inj₁ refl
...   | inj₂ q  = Tₑ , subst (Tₑ ∈ᴬ_) (sym q) inAlt , inj₂ (⊤ₑ , refl , ≾ₑ-refl)
nrmₑ-join x₀ xs {x} w m | just _ with ∈-map⁻ commuteₑ (flatₑ x) (nubₑ-∈⁻ _ m)
... | P , mP , refl with flatₑ-join x₀ xs w mP
...   | inj₁ m' = commuteₑ P , nubₑ-∈ _ (∈-map commuteₑ m') , inj₁ refl
...   | inj₂ q  = commuteₑ Tₑ , subst (λ s → commuteₑ Tₑ ∈ᴬ nubₑ (mapᴬ commuteₑ s)) (sym q) inAlt ,
                  inj₂ commute-Tₑ

------------------------------------------------------------------------
-- Resource grades

Tᵣ : ∀ {Θ} → List (RAtom Θ)
Tᵣ = consᵣ (rc ⊤ᵣ) []

mutual

  data NFᵛᵣ {Θ} : List (RAtom Θ) → Set where
    nf[] : NFᵛᵣ []
    nfv  : ∀ i {l} → NFᵣ l → NFᵛᵣ (rv i ∷ l)
    nfm  : ∀ i {l} → NFᵣ l → NFᵛᵣ (rm i ∷ l)

  data NFᵣ {Θ} : List (RAtom Θ) → Set where
    nfᵛ : ∀ {l} → NFᵛᵣ l → NFᵣ l
    nfc : ∀ {c l} → ¬ (c ≡ uᵣ) → NFᵛᵣ l → NFᵣ (rc c ∷ l)

consc-NFᵣ : ∀ {Θ} c {l : List (RAtom Θ)} → NFᵛᵣ l → NFᵣ (consᵣ (rc c) l)
consc-NFᵣ c nf[] with c ≡ᵣ? uᵣ
... | yes _ = nfᵛ nf[]
... | no ¬p = nfc ¬p nf[]
consc-NFᵣ c (nfv i n) with c ≡ᵣ? uᵣ
... | yes _ = nfᵛ (nfv i n)
... | no ¬p = nfc ¬p (nfv i n)
consc-NFᵣ c (nfm i n) with c ≡ᵣ? uᵣ
... | yes _ = nfᵛ (nfm i n)
... | no ¬p = nfc ¬p (nfm i n)

consᵣ-NF : ∀ {Θ} (a : RAtom Θ) {l} → NFᵣ l → NFᵣ (consᵣ a l)
consᵣ-NF (rv i) n             = nfᵛ (nfv i n)
consᵣ-NF (rm i) n             = nfᵛ (nfm i n)
consᵣ-NF (rc c) (nfᵛ v)       = consc-NFᵣ c v
consᵣ-NF (rc c) (nfc {d} _ v) = consc-NFᵣ (c ·ᵣ d) v

appᵣ-NF : ∀ {Θ} (as : List (RAtom Θ)) {ys} → NFᵣ ys → NFᵣ (appᵣ as ys)
appᵣ-NF []       n = n
appᵣ-NF (a ∷ as) n = consᵣ-NF a (appᵣ-NF as n)

-- An atom of a product is a constant, or comes from the atoms it is
-- built from

IsCᵣ : ∀ {Θ} → RAtom Θ → Set
IsCᵣ a = Σ[ c ∈ R ] (a ≡ rc c)

consᵣ-∈ : ∀ {Θ} (a : RAtom Θ) (l : List (RAtom Θ)) {v} → v ∈ consᵣ a l
        → IsCᵣ v ⊎ ((v ≡ a) ⊎ (v ∈ l))
consᵣ-∈ (rc c) (rc d ∷ l) m with consᵣ-∈ (rc (c ·ᵣ d)) l m
... | inj₁ k          = inj₁ k
... | inj₂ (inj₁ e)   = inj₁ (_ , e)
... | inj₂ (inj₂ m')  = inj₂ (inj₂ (there m'))
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

appᵣ-∈ : ∀ {Θ} (as ys : List (RAtom Θ)) {v} → v ∈ appᵣ as ys → IsCᵣ v ⊎ ((v ∈ as) ⊎ (v ∈ ys))
appᵣ-∈ []       ys m = inj₂ (inj₂ m)
appᵣ-∈ (a ∷ as) ys m with consᵣ-∈ a (appᵣ as ys) m
... | inj₁ k              = inj₁ k
... | inj₂ (inj₁ refl)    = inj₂ (inj₁ (here refl))
... | inj₂ (inj₂ m') with appᵣ-∈ as ys m'
...   | inj₁ k            = inj₁ k
...   | inj₂ (inj₁ m'')   = inj₂ (inj₁ (there m''))
...   | inj₂ (inj₂ m'')   = inj₂ (inj₂ m'')

Tᵣ-∈ : ∀ {Θ} {v : RAtom Θ} → v ∈ Tᵣ {Θ} → IsCᵣ v
Tᵣ-∈ m with consᵣ-∈ (rc ⊤ᵣ) [] m
... | inj₁ k              = k
... | inj₂ (inj₁ e)       = _ , e
... | inj₂ (inj₂ ())

-- Sums

withinᵣ-∈ : ∀ {Θ} (P : List (RAtom Θ)) s {p} → withinᵣ? P s ≡ just p → P ∈ᴬ s
withinᵣ-∈ P (alt Q) e with P ≟ᵖᵣ Q
withinᵣ-∈ P (alt Q) e  | yes refl = inAlt
withinᵣ-∈ P (alt Q) () | no _
withinᵣ-∈ P (Q ∷⁺ t) e with P ≟ᵖᵣ Q
... | yes refl = inHead
... | no _ with withinᵣ? P t in e'
...   | just _ = inTail (withinᵣ-∈ P t e')
withinᵣ-∈ P (Q ∷⁺ t) () | no _ | nothing

nubᵣ-∈ : ∀ {Θ} (s : Alts (List (RAtom Θ))) {P} → P ∈ᴬ s → P ∈ᴬ nubᵣ s
nubᵣ-∈ (alt P)  m = m
nubᵣ-∈ (P ∷⁺ s) inHead with withinᵣ? P (nubᵣ s) in e
... | just _  = withinᵣ-∈ P (nubᵣ s) e
... | nothing = inHead
nubᵣ-∈ (P ∷⁺ s) (inTail m) with withinᵣ? P (nubᵣ s)
... | just _  = nubᵣ-∈ s m
... | nothing = inTail (nubᵣ-∈ s m)

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
        → Σ[ P ∈ List (RAtom Θ) ] Σ[ P' ∈ List (RAtom Θ) ] ((P ∈ᴬ s) × (P' ∈ᴬ t) × (Q ≡ appᵣ P P'))
mulᵣ-∈⁻ (alt P)  t m with mul1ᵣ-∈⁻ P t m
... | P' , m' , e = P , P' , inAlt , m' , e
mulᵣ-∈⁻ (P ∷⁺ s) t m with ∈-⧺⁻ (mul1ᵣ P t) m
... | inj₁ m' with mul1ᵣ-∈⁻ P t m'
...   | P' , m'' , e = P , P' , inHead , m'' , e
mulᵣ-∈⁻ (P ∷⁺ s) t m | inj₂ m' with mulᵣ-∈⁻ s t m'
...   | P₀ , P' , m₀ , m'' , e = P₀ , P' , inTail m₀ , m'' , e

absorbᵣ-∈⁻ : ∀ {Θ} (s : Alts (List (RAtom Θ))) {Q} → Q ∈ᴬ absorbᵣ s → (Q ∈ᴬ s) ⊎ (Q ≡ Tᵣ)
absorbᵣ-∈⁻ s m with topSumᵣ? s
... | just _  = inj₂ (∈-alt⁻ m)
... | nothing = inj₁ m

isTop-Tᵣ : ∀ {Θ} → Is-just (isTopᵣ? (Tᵣ {Θ}))
isTop-Tᵣ with ⊤ᵣ ≡ᵣ? uᵣ
... | yes p with uᵣ ≡ᵣ? ⊤ᵣ
...   | yes _ = isJust tt
...   | no ¬q = ⊥-elim (¬q (sym p))
isTop-Tᵣ | no _ with ⊤ᵣ ≡ᵣ? ⊤ᵣ
...   | yes _ = isJust tt
...   | no ¬q = ⊥-elim (¬q refl)

topSumᵣ-∈ : ∀ {Θ} (s : Alts (List (RAtom Θ))) {P} → Is-just (isTopᵣ? P) → P ∈ᴬ s
          → Is-just (topSumᵣ? s)
topSumᵣ-∈ (alt P) j inAlt with isTopᵣ? P | j
... | just _ | _ = isJust tt
topSumᵣ-∈ (P ∷⁺ s) j inHead with isTopᵣ? P | j
... | just _ | _ = isJust tt
topSumᵣ-∈ (P ∷⁺ s) j (inTail m) with isTopᵣ? P
... | just _ = isJust tt
... | nothing with topSumᵣ? s | topSumᵣ-∈ s j m
...   | just _ | _ = isJust tt

-- Normal form throughout

flatᵐ-NF : ∀ {Θ} (ε : EExp Θ) {P} → P ∈ᴬ flatᵐ ε → NFᵣ P
flatᵐ-NF (evar i)   inAlt = nfᵛ (nfm i (nfᵛ nf[]))
flatᵐ-NF (econst c) inAlt = consᵣ-NF (rc (mapᵉ c)) (nfᵛ nf[])
flatᵐ-NF (ε ·̂ₑ ε')  m with absorbᵣ-∈⁻ (nubᵣ (mulᵣ (flatᵐ ε) (flatᵐ ε'))) m
... | inj₂ refl = consᵣ-NF (rc ⊤ᵣ) (nfᵛ nf[])
... | inj₁ m' with mulᵣ-∈⁻ (flatᵐ ε) (flatᵐ ε') (nubᵣ-∈⁻ _ m')
...   | P , P' , _ , m₂ , refl = appᵣ-NF P (flatᵐ-NF ε' m₂)
flatᵐ-NF (ε ⊔̂ₑ ε')  m with absorbᵣ-∈⁻ (nubᵣ (flatᵐ ε ⧺ flatᵐ ε')) m
... | inj₂ refl = consᵣ-NF (rc ⊤ᵣ) (nfᵛ nf[])
... | inj₁ m' with ∈-⧺⁻ (flatᵐ ε) (nubᵣ-∈⁻ _ m')
...   | inj₁ m₁ = flatᵐ-NF ε m₁
...   | inj₂ m₂ = flatᵐ-NF ε' m₂

flatᵣ-NF : ∀ {Θ} (ρ : RExp Θ) {P} → P ∈ᴬ flatᵣ ρ → NFᵣ P
flatᵣ-NF (rvar i)   inAlt = nfᵛ (nfv i (nfᵛ nf[]))
flatᵣ-NF (rconst c) inAlt = consᵣ-NF (rc c) (nfᵛ nf[])
flatᵣ-NF (ρ ·̂ᵣ ρ')  m with absorbᵣ-∈⁻ (nubᵣ (mulᵣ (flatᵣ ρ) (flatᵣ ρ'))) m
... | inj₂ refl = consᵣ-NF (rc ⊤ᵣ) (nfᵛ nf[])
... | inj₁ m' with mulᵣ-∈⁻ (flatᵣ ρ) (flatᵣ ρ') (nubᵣ-∈⁻ _ m')
...   | P , P' , _ , m₂ , refl = appᵣ-NF P (flatᵣ-NF ρ' m₂)
flatᵣ-NF (ρ ⊔̂ᵣ ρ')  m with absorbᵣ-∈⁻ (nubᵣ (flatᵣ ρ ⧺ flatᵣ ρ')) m
... | inj₂ refl = consᵣ-NF (rc ⊤ᵣ) (nfᵛ nf[])
... | inj₁ m' with ∈-⧺⁻ (flatᵣ ρ) (nubᵣ-∈⁻ _ m')
...   | inj₁ m₁ = flatᵣ-NF ρ m₁
...   | inj₂ m₂ = flatᵣ-NF ρ' m₂
flatᵣ-NF ∣ ε ∣̂ᵉ     m = flatᵐ-NF ε m

-- The variable atoms, resource variables and images of effect ones

IsVᵣ : ∀ {Θ} → RAtom Θ → Set
IsVᵣ a = (Σ[ i ∈ _ ] (a ≡ rv i)) ⊎ (Σ[ i ∈ _ ] (a ≡ rm i))

varsᵃᵣ-V : ∀ {Θ} (l : List (RAtom Θ)) {a} → a ∈ varsᵃᵣ l → IsVᵣ a
varsᵃᵣ-V (rc _ ∷ l) m         = varsᵃᵣ-V l m
varsᵃᵣ-V (rv i ∷ l) (here e)  = inj₁ (i , e)
varsᵃᵣ-V (rv i ∷ l) (there m) = varsᵃᵣ-V l m
varsᵃᵣ-V (rm i ∷ l) (here e)  = inj₂ (i , e)
varsᵃᵣ-V (rm i ∷ l) (there m) = varsᵃᵣ-V l m

varsᵃᵣ-∈ : ∀ {Θ} (l : List (RAtom Θ)) {a} → a ∈ varsᵃᵣ l → a ∈ l
varsᵃᵣ-∈ (rc _ ∷ l) m         = there (varsᵃᵣ-∈ l m)
varsᵃᵣ-∈ (rv i ∷ l) (here e)  = here e
varsᵃᵣ-∈ (rv i ∷ l) (there m) = there (varsᵃᵣ-∈ l m)
varsᵃᵣ-∈ (rm i ∷ l) (here e)  = here e
varsᵃᵣ-∈ (rm i ∷ l) (there m) = there (varsᵃᵣ-∈ l m)

allV-NFᵣ : ∀ {Θ} (l : List (RAtom Θ)) → (∀ {a} → a ∈ l → IsVᵣ a) → NFᵛᵣ l
allV-NFᵣ []      f = nf[]
allV-NFᵣ (a ∷ l) f with f (here refl)
... | inj₁ (i , refl) = nfv i (nfᵛ (allV-NFᵣ l (λ m → f (there m))))
... | inj₂ (i , refl) = nfm i (nfᵛ (allV-NFᵣ l (λ m → f (there m))))

commuteᵣ-NF : ∀ {Θ} (P : List (RAtom Θ)) → NFᵣ (commuteᵣ P)
commuteᵣ-NF P =
  consᵣ-NF (rc (constᵣ P))
    (nfᵛ (allV-NFᵣ _ (λ m → varsᵃᵣ-V P (sortBy-∈ _<ʳᵃ_ (varsᵃᵣ P) m))))

commuteᵣ-∈ : ∀ {Θ} (P : List (RAtom Θ)) {v} → v ∈ commuteᵣ P → IsCᵣ v ⊎ (v ∈ P)
commuteᵣ-∈ P m with consᵣ-∈ (rc (constᵣ P)) (sortBy _<ʳᵃ_ (varsᵃᵣ P)) m
... | inj₁ k          = inj₁ k
... | inj₂ (inj₁ e)   = inj₁ (_ , e)
... | inj₂ (inj₂ m')  = inj₂ (varsᵃᵣ-∈ P (sortBy-∈ _<ʳᵃ_ (varsᵃᵣ P) m'))

commSumᵣ-∈⁻ : ∀ {Θ} (c : Maybe (Commutative _≡_ _·ᵣ_)) (s : Alts (List (RAtom Θ))) {Q}
            → Q ∈ᴬ commSumᵣ c s → Σ[ P ∈ List (RAtom Θ) ] ((P ∈ᴬ s) × ((Q ≡ P) ⊎ (Q ≡ commuteᵣ P)))
commSumᵣ-∈⁻ nothing  s m = _ , m , inj₁ refl
commSumᵣ-∈⁻ (just _) s m with ∈-map⁻ commuteᵣ s (nubᵣ-∈⁻ _ m)
... | P , m' , e = P , m' , inj₂ e

nrmᵣ-NF : ∀ {Θ} (ρ : RExp Θ) {Q} → Q ∈ᴬ nrmᵣ ρ → NFᵣ Q
nrmᵣ-NF ρ m with commSumᵣ-∈⁻ ·ᵣ-comm? (flatᵣ ρ) m
... | P , m' , inj₁ refl = flatᵣ-NF ρ m'
... | P , m' , inj₂ refl = commuteᵣ-NF P

-- The variables of the alternatives are the expression's

OccAᵐ : ∀ {Θ} → RAtom Θ → EExp Θ → Set
OccAᵐ (rc _) ε = ⊤
OccAᵐ (rv _) ε = ⊥
OccAᵐ (rm i) ε = occᵉ-e i ε ≡ true

OccAᵣ : ∀ {Θ} → RAtom Θ → RExp Θ → Set
OccAᵣ (rc _) ρ = ⊤
OccAᵣ (rv i) ρ = occʳ-r i ρ ≡ true
OccAᵣ (rm i) ρ = occᵉ-r i ρ ≡ true

flatᵐ-var : ∀ {Θ} (ε : EExp Θ) {P v} → P ∈ᴬ flatᵐ ε → v ∈ P → OccAᵐ v ε
flatᵐ-var (evar j)   {v = v} inAlt (here refl) = dec-true (j ≟ᶠ j) refl
flatᵐ-var (econst c) {v = v} inAlt a with consᵣ-∈ (rc (mapᵉ c)) [] a
... | inj₁ (_ , refl)     = tt
... | inj₂ (inj₁ refl)    = tt
... | inj₂ (inj₂ ())
flatᵐ-var (ε ·̂ₑ ε')  {v = v} m a with absorbᵣ-∈⁻ (nubᵣ (mulᵣ (flatᵐ ε) (flatᵐ ε'))) m
... | inj₂ refl with Tᵣ-∈ a
...   | _ , refl = tt
flatᵐ-var (ε ·̂ₑ ε')  {v = v} m a | inj₁ m' with mulᵣ-∈⁻ (flatᵐ ε) (flatᵐ ε') (nubᵣ-∈⁻ _ m')
...   | P , P' , m₁ , m₂ , refl with appᵣ-∈ P P' a
...     | inj₁ (_ , refl) = tt
...     | inj₂ (inj₁ a₁) = left v (flatᵐ-var ε m₁ a₁)
  where
    left : ∀ v → OccAᵐ v ε → OccAᵐ v (ε ·̂ₑ ε')
    left (rc _) o = tt
    left (rm i) o = ∨-left (occᵉ-e i ε) _ o
...     | inj₂ (inj₂ a₂) = right v (flatᵐ-var ε' m₂ a₂)
  where
    right : ∀ v → OccAᵐ v ε' → OccAᵐ v (ε ·̂ₑ ε')
    right (rc _) o = tt
    right (rm i) o = ∨-right (occᵉ-e i ε) _ o
flatᵐ-var (ε ⊔̂ₑ ε')  {v = v} m a with absorbᵣ-∈⁻ (nubᵣ (flatᵐ ε ⧺ flatᵐ ε')) m
... | inj₂ refl with Tᵣ-∈ a
...   | _ , refl = tt
flatᵐ-var (ε ⊔̂ₑ ε')  {v = v} m a | inj₁ m' with ∈-⧺⁻ (flatᵐ ε) (nubᵣ-∈⁻ _ m')
...   | inj₁ m₁ = left v (flatᵐ-var ε m₁ a)
  where
    left : ∀ v → OccAᵐ v ε → OccAᵐ v (ε ⊔̂ₑ ε')
    left (rc _) o = tt
    left (rm i) o = ∨-left (occᵉ-e i ε) _ o
...   | inj₂ m₂ = right v (flatᵐ-var ε' m₂ a)
  where
    right : ∀ v → OccAᵐ v ε' → OccAᵐ v (ε ⊔̂ₑ ε')
    right (rc _) o = tt
    right (rm i) o = ∨-right (occᵉ-e i ε) _ o

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

flatᵣ-var : ∀ {Θ} (ρ : RExp Θ) {P v} → P ∈ᴬ flatᵣ ρ → v ∈ P → OccAᵣ v ρ
flatᵣ-var (rvar j)   inAlt (here refl) = dec-true (j ≟ᶠ j) refl
flatᵣ-var (rconst c) inAlt a with consᵣ-∈ (rc c) [] a
... | inj₁ (_ , refl)     = tt
... | inj₂ (inj₁ refl)    = tt
... | inj₂ (inj₂ ())
flatᵣ-var (ρ ·̂ᵣ ρ')  {v = v} m a with absorbᵣ-∈⁻ (nubᵣ (mulᵣ (flatᵣ ρ) (flatᵣ ρ'))) m
... | inj₂ refl with Tᵣ-∈ a
...   | _ , refl = tt
flatᵣ-var (ρ ·̂ᵣ ρ')  {v = v} m a | inj₁ m' with mulᵣ-∈⁻ (flatᵣ ρ) (flatᵣ ρ') (nubᵣ-∈⁻ _ m')
...   | P , P' , m₁ , m₂ , refl with appᵣ-∈ P P' a
...     | inj₁ (_ , refl) = tt
...     | inj₂ (inj₁ a₁) = occAˡ ρ ρ' v (flatᵣ-var ρ m₁ a₁)
...     | inj₂ (inj₂ a₂) = occAʳ ρ ρ' v (flatᵣ-var ρ' m₂ a₂)
flatᵣ-var (ρ ⊔̂ᵣ ρ')  {v = v} m a with absorbᵣ-∈⁻ (nubᵣ (flatᵣ ρ ⧺ flatᵣ ρ')) m
... | inj₂ refl with Tᵣ-∈ a
...   | _ , refl = tt
flatᵣ-var (ρ ⊔̂ᵣ ρ')  {v = v} m a | inj₁ m' with ∈-⧺⁻ (flatᵣ ρ) (nubᵣ-∈⁻ _ m')
...   | inj₁ m₁ = occAˡ⊔ ρ ρ' v (flatᵣ-var ρ m₁ a)
...   | inj₂ m₂ = occAʳ⊔ ρ ρ' v (flatᵣ-var ρ' m₂ a)
flatᵣ-var ∣ ε ∣̂ᵉ     {v = v} m a = occAᵐ→ᵣ v ε (flatᵐ-var ε m a)

nrmᵣ-var : ∀ {Θ} (ρ : RExp Θ) {Q v} → Q ∈ᴬ nrmᵣ ρ → v ∈ Q → OccAᵣ v ρ
nrmᵣ-var ρ m a with commSumᵣ-∈⁻ ·ᵣ-comm? (flatᵣ ρ) m
... | P , m' , inj₁ refl = flatᵣ-var ρ m' a
... | P , m' , inj₂ refl with commuteᵣ-∈ P a
...   | inj₁ (_ , refl) = tt
...   | inj₂ a' = flatᵣ-var ρ m' a'

-- An alternative of one side of a join is one of the join, unless the
-- join is the top

Coversᵣ : ∀ {Θ} → Alts (List (RAtom Θ)) → List (RAtom Θ) → Set
Coversᵣ s P = (P ∈ᴬ s) ⊎ (s ≡ alt Tᵣ)

flatᵣ-⊔ˡ : ∀ {Θ} (x y : RExp Θ) {P} → Coversᵣ (flatᵣ x) P → Coversᵣ (flatᵣ (x ⊔̂ᵣ y)) P
flatᵣ-⊔ˡ x y c with topSumᵣ? (nubᵣ (flatᵣ x ⧺ flatᵣ y)) in e
... | just _  = inj₂ refl
... | nothing with c
...   | inj₁ m = inj₁ (nubᵣ-∈ _ (∈-⧺ˡ m))
...   | inj₂ q = ⊥-elim (nothing-just e (topSumᵣ-∈ (nubᵣ (flatᵣ x ⧺ flatᵣ y)) isTop-Tᵣ
                           (nubᵣ-∈ _ (∈-⧺ˡ (subst (Tᵣ ∈ᴬ_) (sym q) inAlt)))))

flatᵣ-⊔ʳ : ∀ {Θ} (x y : RExp Θ) {P} → Coversᵣ (flatᵣ y) P → Coversᵣ (flatᵣ (x ⊔̂ᵣ y)) P
flatᵣ-⊔ʳ x y c with topSumᵣ? (nubᵣ (flatᵣ x ⧺ flatᵣ y)) in e
... | just _  = inj₂ refl
... | nothing with c
...   | inj₁ m = inj₁ (nubᵣ-∈ _ (∈-⧺ʳ (flatᵣ x) m))
...   | inj₂ q = ⊥-elim (nothing-just e (topSumᵣ-∈ (nubᵣ (flatᵣ x ⧺ flatᵣ y)) isTop-Tᵣ
                           (nubᵣ-∈ _ (∈-⧺ʳ (flatᵣ x) (subst (Tᵣ ∈ᴬ_) (sym q) inAlt)))))

flatᵣ-joinˡ : ∀ {Θ} (z : RExp Θ) xs {P} → Coversᵣ (flatᵣ z) P → Coversᵣ (flatᵣ (joinᵣ z xs)) P
flatᵣ-joinˡ z []       c = c
flatᵣ-joinˡ z (x ∷ xs) c = flatᵣ-joinˡ (z ⊔̂ᵣ x) xs (flatᵣ-⊔ˡ z x c)

flatᵣ-join : ∀ {Θ} (x₀ : RExp Θ) xs {x P} → x ∈ x₀ ∷ xs → P ∈ᴬ flatᵣ x
           → Coversᵣ (flatᵣ (joinᵣ x₀ xs)) P
flatᵣ-join x₀ xs        (here refl)         m = flatᵣ-joinˡ x₀ xs (inj₁ m)
flatᵣ-join x₀ (x₁ ∷ xs) (there (here refl)) m = flatᵣ-joinˡ (x₀ ⊔̂ᵣ x₁) xs (flatᵣ-⊔ʳ x₀ x₁ (inj₁ m))
flatᵣ-join x₀ (x₁ ∷ xs) (there (there w))   m = flatᵣ-join (x₀ ⊔̂ᵣ x₁) xs (there w) m

TopAltᵣ : ∀ {Θ} → List (RAtom Θ) → Set
TopAltᵣ Q = Σ[ c ∈ R ] ((Q ≡ consᵣ (rc c) []) × (⊤ᵣ ≾ᵣ c))

commute-Tᵣ : ∀ {Θ} → TopAltᵣ (commuteᵣ (Tᵣ {Θ}))
commute-Tᵣ with ⊤ᵣ ≡ᵣ? uᵣ
... | yes p = uᵣ , refl , ≾ᵣ-reflexive p
... | no _  = ⊤ᵣ ·ᵣ uᵣ , refl , ≾ᵣ-reflexive (sym (·ᵣ-identityʳ ⊤ᵣ))

nrmᵣ-join : ∀ {Θ} (x₀ : RExp Θ) xs {x Q} → x ∈ x₀ ∷ xs → Q ∈ᴬ nrmᵣ x
          → Σ[ Q' ∈ List (RAtom Θ) ] ((Q' ∈ᴬ nrmᵣ (joinᵣ x₀ xs)) × ((Q' ≡ Q) ⊎ TopAltᵣ Q'))
nrmᵣ-join x₀ xs {x} w m with ·ᵣ-comm?
... | nothing with flatᵣ-join x₀ xs w m
...   | inj₁ m' = _ , m' , inj₁ refl
...   | inj₂ q  = Tᵣ , subst (Tᵣ ∈ᴬ_) (sym q) inAlt , inj₂ (⊤ᵣ , refl , ≾ᵣ-refl)
nrmᵣ-join x₀ xs {x} w m | just _ with ∈-map⁻ commuteᵣ (flatᵣ x) (nubᵣ-∈⁻ _ m)
... | P , mP , refl with flatᵣ-join x₀ xs w mP
...   | inj₁ m' = commuteᵣ P , nubᵣ-∈ _ (∈-map commuteᵣ m') , inj₁ refl
...   | inj₂ q  = commuteᵣ Tᵣ , subst (λ s → commuteᵣ Tᵣ ∈ᴬ nubᵣ (mapᴬ commuteᵣ s)) (sym q) inAlt ,
                  inj₂ commute-Tᵣ
