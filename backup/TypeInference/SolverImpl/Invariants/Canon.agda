------------------------------------------------------------------
-- Canonical forms keep a whole unknown whole, and mention no     --
-- unknown the expression does not                                --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Invariants.Canon (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-e; occᵉ-r; occʳ-r)
open import TypeInference.SolverImpl.Core.Rigid S using (∨-true; dec-true; true-dec)
open import TypeInference.SolverImpl.Normal S
open import TypeInference.SolverImpl.Canon S
open import TypeInference.SolverImpl.Invariants.Sums S
open import TypeInference.SolverImpl.Invariants.Flat S
open import TypeInference.SolverImpl.Invariants.Join S using (module GEₑ; module GEᵣ)

------------------------------------------------------------------------
-- Effect grades

-- a whole unknown

nrmₑ-whole : ∀ {Θ} (k : EVar Θ) → nrmₑ (evar k) ≡ alt {List (EAtom Θ)} (av k ∷ [])
nrmₑ-whole k with ·ₑ-comm?
... | nothing = refl
... | just _ with uₑ ≡ₑ? uₑ
...   | yes _ = refl
...   | no ¬p = ⊥-elim (¬p refl)

atoms-varₑ : ∀ {Θ} (k : EVar Θ) → atomsₑ (Gₑ._▸_ {Θ} {a = k} uₑ (Gₑ.⌜_⌝ {Θ} uₑ)) ≡ av k ∷ []
atoms-varₑ k with uₑ ≡ₑ? uₑ
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

canonₑ-var : ∀ {Θ} (k : EVar Θ) → canonₑ (evar k) ≡ evar k
canonₑ-var {Θ} k =
  trans (cong (λ s → ⟦ canonSumₑ {Θ} s ⟧ᵉᵖ⁺) (nrmₑ-whole k))
        (cong (λ l → ⟦ alt {List (EAtom Θ)} l ⟧ᵉᵖ⁺) (atoms-varₑ k))

-- the variables of a read-back

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

-- products and their skeletons

atomsₑ-av : ∀ {Θ vs} (s : Gₑ.Slots {Θ} vs) {i} → av i ∈ atomsₑ s → i ∈ vs
atomsₑ-av Gₑ.⌜ c ⌝ a with consₑ-av (ac c) [] a
... | inj₁ ()
... | inj₂ ()
atomsₑ-av (Gₑ._▸_ {j} c s) a with consₑ-av (ac c) (av j ∷ atomsₑ s) a
... | inj₂ (here refl) = here refl
... | inj₂ (there a')  = there (atomsₑ-av s a')

slotsₑ-av : ∀ {Θ} (m : Maybe E) (P : List (EAtom Θ)) {i} → i ∈ proj₁ (slotsₑ m P) → av i ∈ P
slotsₑ-av m (ac c ∷ P) w         = there (slotsₑ-av _ P w)
slotsₑ-av m (av j ∷ P) (here e)  = here (cong av e)
slotsₑ-av m (av j ∷ P) (there w) = there (slotsₑ-av nothing P w)

canonₑ-occ : ∀ {Θ} (ε : EExp Θ) {i} → occᵉ-e i (canonₑ ε) ≡ true → occᵉ-e i ε ≡ true
canonₑ-occ {Θ} ε {i} q with ⟦⟧ᵉᵖ⁺-av (canonSumₑ (nrmₑ ε)) q
... | P , m , a with ∈-map⁻ (λ P → atomsₑ (proj₂ P)) (Mₑ.maximal (toProdsₑ (nrmₑ ε))) m
...   | (vs , s) , m' , refl = sk m' (atomsₑ-av s a)
  where
    Sk : List (EVar Θ) → Set
    Sk vs = ∀ {j} → j ∈ vs → occᵉ-e j ε ≡ true

    open GEₑ.Skel {Θ} Sk
    open Pr (∅ᴴ ⊩_≾̂ₑ_) ≡̂ₑ-absorb (λ P P' → decide≾ₑ {Q = ∅ᴴ} Gₑ.⟦ P ⟧ᵖ Gₑ.⟦ P' ⟧ᵖ)

    ins : ∀ {P} → P ∈ᴬ toProdsₑ (nrmₑ ε) → SkP P
    ins m₀ with ∈-map⁻ (slotsₑ nothing) (nrmₑ ε) m₀
    ... | Q , mQ , refl = λ w → nrmₑ-av ε mQ (slotsₑ-av nothing Q w)

    sk : ∀ {P} → P ∈ᴬ Mₑ.maximal (toProdsₑ (nrmₑ ε)) → SkP P
    sk = maximal-sk (toProdsₑ (nrmₑ ε)) ins

------------------------------------------------------------------------
-- Resource grades

nrmᵣ-whole : ∀ {Θ} (k : RVar Θ) → nrmᵣ (rvar k) ≡ alt {List (RAtom Θ)} (rv k ∷ [])
nrmᵣ-whole k with ·ᵣ-comm?
... | nothing = refl
... | just _ with uᵣ ≡ᵣ? uᵣ
...   | yes _ = refl
...   | no ¬p = ⊥-elim (¬p refl)

atoms-varᵣ : ∀ {Θ} (k : RVar Θ) → atomsᵣ (Gᵣ._▸_ {Θ} {a = vr k} uᵣ (Gᵣ.⌜_⌝ {Θ} uᵣ)) ≡ rv k ∷ []
atoms-varᵣ k with uᵣ ≡ᵣ? uᵣ
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

canonᵣ-var : ∀ {Θ} (k : RVar Θ) → canonᵣ (rvar k) ≡ rvar k
canonᵣ-var {Θ} k =
  trans (cong (λ s → ⟦ canonSumᵣ {Θ} s ⟧ʳᵖ⁺) (nrmᵣ-whole k))
        (cong (λ l → ⟦ alt {List (RAtom Θ)} l ⟧ʳᵖ⁺) (atoms-varᵣ k))

-- the variables of a read-back, of either sort

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

atomsᵣ-var : ∀ {Θ vs} (s : Gᵣ.Slots {Θ} vs) {v} → v ∈ atomsᵣ s
           → IsCᵣ v ⊎ (Σ[ a ∈ RVAtom Θ ] ((a ∈ vs) × (v ≡ varAtomᵣ a)))
atomsᵣ-var Gᵣ.⌜ c ⌝ w with consᵣ-∈ (rc c) [] w
... | inj₁ k            = inj₁ k
... | inj₂ (inj₁ e)     = inj₁ (c , e)
... | inj₂ (inj₂ ())
atomsᵣ-var (Gᵣ._▸_ {a} c s) w with consᵣ-∈ (rc c) (varAtomᵣ a ∷ atomsᵣ s) w
... | inj₁ k                   = inj₁ k
... | inj₂ (inj₁ e)            = inj₁ (c , e)
... | inj₂ (inj₂ (here e))     = inj₂ (a , here refl , e)
... | inj₂ (inj₂ (there w')) with atomsᵣ-var s w'
...   | inj₁ k             = inj₁ k
...   | inj₂ (a' , m , e)  = inj₂ (a' , there m , e)

slotsᵣ-var : ∀ {Θ} (m : Maybe R) (P : List (RAtom Θ)) {a} → a ∈ proj₁ (slotsᵣ m P) → varAtomᵣ a ∈ P
slotsᵣ-var m (rc c ∷ P) w          = there (slotsᵣ-var _ P w)
slotsᵣ-var m (rv j ∷ P) (here refl) = here refl
slotsᵣ-var m (rv j ∷ P) (there w)  = there (slotsᵣ-var nothing P w)
slotsᵣ-var m (rm j ∷ P) (here refl) = here refl
slotsᵣ-var m (rm j ∷ P) (there w)  = there (slotsᵣ-var nothing P w)

-- every variable atom of the canonical form is one of the expression

canonᵣ-var-occ : ∀ {Θ} (ρ : RExp Θ) {P v} → P ∈ᴬ canonSumᵣ (nrmᵣ ρ) → v ∈ P → OccAᵣ v ρ
canonᵣ-var-occ {Θ} ρ {v = v} m w
  with ∈-map⁻ (λ P → atomsᵣ (proj₂ P)) (Mᵣ.maximal (toProdsᵣ (nrmᵣ ρ))) m
... | (vs , s) , m' , refl with atomsᵣ-var s w
...   | inj₁ (c , refl)     = tt
...   | inj₂ (a , ma , refl) = sk m' ma
  where
    Sk : List (RVAtom Θ) → Set
    Sk vs = ∀ {a} → a ∈ vs → OccAᵣ (varAtomᵣ a) ρ

    open GEᵣ.Skel {Θ} Sk
    open Pr (∅ᴴ ⊩_≾̂ᵣ_) ≡̂ᵣ-absorb (λ P P' → decide≾ᵣ {Q = ∅ᴴ} Gᵣ.⟦ P ⟧ᵖ Gᵣ.⟦ P' ⟧ᵖ)

    ins : ∀ {P} → P ∈ᴬ toProdsᵣ (nrmᵣ ρ) → SkP P
    ins m₀ with ∈-map⁻ (slotsᵣ nothing) (nrmᵣ ρ) m₀
    ... | Q , mQ , refl = λ w' → nrmᵣ-var ρ mQ (slotsᵣ-var nothing Q w')

    sk : ∀ {P} → P ∈ᴬ Mᵣ.maximal (toProdsᵣ (nrmᵣ ρ)) → SkP P
    sk = maximal-sk (toProdsᵣ (nrmᵣ ρ)) ins

canonᵣ-occʳ : ∀ {Θ} (ρ : RExp Θ) {i} → occʳ-r i (canonᵣ ρ) ≡ true → occʳ-r i ρ ≡ true
canonᵣ-occʳ ρ q with ⟦⟧ʳᵖ⁺-rv (canonSumᵣ (nrmᵣ ρ)) q
... | P , m , w = canonᵣ-var-occ ρ m w

canonᵣ-occᵉ : ∀ {Θ} (ρ : RExp Θ) {i} → occᵉ-r i (canonᵣ ρ) ≡ true → occᵉ-r i ρ ≡ true
canonᵣ-occᵉ ρ q with ⟦⟧ʳᵖ⁺-rm (canonSumᵣ (nrmᵣ ρ)) q
... | P , m , w = canonᵣ-var-occ ρ m w
