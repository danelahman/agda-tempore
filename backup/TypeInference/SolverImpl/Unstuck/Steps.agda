------------------------------------------------------------------
-- When a local unknown gets a value                              --
--                                                                --
-- The conditions under which `Localise` gives a local unknown a  --
-- value, stated as properties of the residual, and the tests of  --
-- `stepᵉ`/`stepʳ` succeeding on them. One set per rule:          --
--                                                                --
--   lower  a lower bound free of the unknown, and on every right --
--          side the unknown whole or absent;                     --
--   upper  a bound above it, free of it, that the decider puts   --
--          below every other bound above it, and on every left   --
--          side the unknown whole or absent;                     --
--   unit   the unit least, and the unknown on no right side;     --
--   top    the unknown on no left side.                          --
--                                                                --
-- Each also asks the unknown to be absent from every type, from  --
-- every disjunction's grade where it is raised, and the deferred --
-- entries to keep the side the move leaves fixed.                --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; true; false) renaming (Bool to 𝔹)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe using (Is-just)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Unstuck.Steps (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S using (∅ᴴ; Is-just?; _⊩_≾̂ₑ_; _⊩_≾̂ᵣ_)
open import TypeInference.OpenSyntax.Instances S using (_↑ᵉⁿ_)

open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-e; occᵉ-r; occᵉ-v; occʳ-r; occʳ-v)
open import TypeInference.SolverImpl.Core.Rigid S using (dec-true)
open import TypeInference.SolverImpl.Deferred S
  using (Dfr; nb; body; ors; oes; allOf; Dir; dir↓; dir↑; Still; still; still?; stills?;
         Fixedʳ; Fixedᵉ; fixedʳ?; fixedᵉ?)
open import TypeInference.SolverImpl.Resid    S
open import TypeInference.SolverImpl.Normal   S using (decide≾ᵣ; decide≾ₑ)
open import TypeInference.SolverImpl.Eliminate S using (joinₑ; joinᵣ)
open import TypeInference.SolverImpl.Localise S

------------------------------------------------------------------------
-- Generic: the tests of `Sides` and `Bounds` succeed

isFalse-ok : ∀ {b} → b ≡ false → isFalse b ≡ nothing → ⊥
isFalse-ok refl ()

allOf-ok : ∀ {X : Set} {P : X → Set} → (f : (a : X) → Maybe (P a)) → (l : List X)
         → (∀ {a} → a ∈ l → f a ≡ nothing → ⊥) → allOf f l ≡ nothing → ⊥
allOf-ok f []      h ()
allOf-ok f (a ∷ l) h with f a in e | allOf f l in e'
... | just _  | just _  = λ ()
... | nothing | _       = λ _ → h (here refl) e
... | just _  | nothing = λ _ → allOf-ok f l (λ m → h (there m)) e'

isJust?-ok : ∀ {A : Set} → (m : Maybe A) → Is-just m → Is-just? m ≡ nothing → ⊥
isJust?-ok (just _) _ ()

first-nothing : ∀ {X : Set} → (x y : Maybe X) → first x y ≡ nothing → (x ≡ nothing) × (y ≡ nothing)
first-nothing nothing y q = refl , q
first-nothing (just _) y ()

allFalse-ok : ∀ {Y : Set} → (f : Y → 𝔹) → (l : List Y) → (∀ {y} → y ∈ l → f y ≡ false)
            → allFalse f l ≡ nothing → ⊥
allFalse-ok f []      h ()
allFalse-ok f (y ∷ l) h with isFalse (f y) in e | allFalse f l in e'
... | just _  | just _  = λ ()
... | nothing | _       = λ _ → isFalse-ok (h (here refl)) e
... | just _  | nothing = λ _ → allFalse-ok f l (λ m → h (there m)) e'

module SidesOK {X : Set} (_≟_ : Decidable (_≡_ {A = X})) (occ : X → 𝔹) where

  open Sides _≟_ occ

  freeRs-ok : (l : List (X × X)) → (∀ {a} → a ∈ l → FreeR a) → freeRs l ≡ nothing → ⊥
  freeRs-ok []             h ()
  freeRs-ok ((x , x') ∷ l) h with freeRs l in e | x ≟ x' | isFalse (occ x') in eo | h (here refl)
  ... | nothing | _     | _       | _       = λ _ → freeRs-ok l (λ m → h (there m)) e
  ... | just f  | yes _ | _       | _       = λ ()
  ... | just f  | no _  | just _  | _       = λ ()
  ... | just f  | no ne | nothing | inj₁ eq = λ _ → ne eq
  ... | just f  | no _  | nothing | inj₂ q  = λ _ → isFalse-ok q eo

  freeLs-ok : (l : List (X × X)) → (∀ {a} → a ∈ l → FreeL a) → freeLs l ≡ nothing → ⊥
  freeLs-ok []             h ()
  freeLs-ok ((x , x') ∷ l) h with freeLs l in e | x ≟ x' | isFalse (occ x) in eo | h (here refl)
  ... | nothing | _     | _       | _       = λ _ → freeLs-ok l (λ m → h (there m)) e
  ... | just f  | yes _ | _       | _       = λ ()
  ... | just f  | no _  | just _  | _       = λ ()
  ... | just f  | no ne | nothing | inj₁ eq = λ _ → ne eq
  ... | just f  | no _  | nothing | inj₂ q  = λ _ → isFalse-ok q eo

module BoundsOK {X : Set} (_≟_ : Decidable (_≡_ {A = X})) (occ : X → 𝔹) (v : X)
                (_≤_ : X → X → Set) (dec≤ : (x y : X) → Maybe (x ≤ y))
                (occ-v : occ v ≡ true) where

  open Bounds _≟_ occ v _≤_ dec≤

  -- every ordering has `v` whole on its right below a bound free of it,
  -- or leaves the right side alone

  LowOK : X × X → Set
  LowOK (x , x') = ((x' ≡ v) × (occ x ≡ false)) ⊎ FreeR (x , x')

  lowsOf-ok : (l : List (X × X)) → (∀ {a} → a ∈ l → LowOK a) → lowsOf l ≡ nothing → ⊥
  lowsOf-ok []             h ()
  lowsOf-ok ((x , x') ∷ l) h
    with lowsOf l in e | x' ≟ v | isFalse (occ x) in ex | x ≟ x' | isFalse (occ x') in ex' | h (here refl)
  ... | nothing | _      | _       | _      | _       | _                = λ _ → lowsOf-ok l (λ m → h (there m)) e
  ... | just _  | yes _  | just _  | _      | _       | _                = λ ()
  ... | just _  | yes _  | nothing | yes _  | _       | _                = λ ()
  ... | just _  | no _   | _       | yes _  | _       | _                = λ ()
  ... | just _  | yes _  | nothing | no _   | just _  | _                = λ ()
  ... | just _  | no _   | _       | no _   | just _  | _                = λ ()
  ... | just _  | yes _  | nothing | no _   | nothing | inj₁ (_ , qx)    = λ _ → isFalse-ok qx ex
  ... | just _  | yes _  | nothing | no ne  | nothing | inj₂ (inj₁ eq)   = λ _ → ne eq
  ... | just _  | yes _  | nothing | no _   | nothing | inj₂ (inj₂ q)    = λ _ → isFalse-ok q ex'
  ... | just _  | no nv  | _       | no _   | nothing | inj₁ (ev , _)    = λ _ → nv ev
  ... | just _  | no _   | _       | no ne  | nothing | inj₂ (inj₁ eq)   = λ _ → ne eq
  ... | just _  | no _   | _       | no _   | nothing | inj₂ (inj₂ q)    = λ _ → isFalse-ok q ex'

  -- a lower bound free of `v` is among those found

  lowsOf-bnd : (l : List (X × X)) → (L : Lows l) → lowsOf l ≡ just L
             → ∀ {x} → (x , v) ∈ l → occ x ≡ false → x ∈ bnds L
  lowsOf-bnd ((y , y') ∷ l) L eq m q
    with lowsOf l in e | y' ≟ v | isFalse (occ y) in ey | y ≟ y' | isFalse (occ y')
  ... | nothing | _ | _ | _ | _ = ⊥-elim (nj eq)
    where nj : ∀ {A : Set} {a : A} → nothing ≡ just a → ⊥
          nj ()
  ... | just L₀ | yes ev | just qy | _ | _ with eq | m
  ...   | refl | here refl = here refl
  ...   | refl | there m'  = there (lowsOf-bnd l L₀ e m' q)
  lowsOf-bnd ((y , y') ∷ l) L eq m q | just L₀ | yes ev | nothing | yes _ | _ with eq | m
  ...   | refl | here refl = ⊥-elim (isFalse-ok q ey)
  ...   | refl | there m'  = lowsOf-bnd l L₀ e m' q
  lowsOf-bnd ((y , y') ∷ l) L eq m q | just L₀ | no nv | _ | yes _ | _ with eq | m
  ...   | refl | here refl = ⊥-elim (nv refl)
  ...   | refl | there m'  = lowsOf-bnd l L₀ e m' q
  lowsOf-bnd ((y , y') ∷ l) L eq m q | just L₀ | yes ev | nothing | no _ | just _ with eq | m
  ...   | refl | here refl = ⊥-elim (isFalse-ok q ey)
  ...   | refl | there m'  = lowsOf-bnd l L₀ e m' q
  lowsOf-bnd ((y , y') ∷ l) L eq m q | just L₀ | no nv | _ | no _ | just _ with eq | m
  ...   | refl | here refl = ⊥-elim (nv refl)
  ...   | refl | there m'  = lowsOf-bnd l L₀ e m' q
  lowsOf-bnd ((y , y') ∷ l) L () m q | just L₀ | yes ev | nothing | no _ | nothing
  lowsOf-bnd ((y , y') ∷ l) L () m q | just L₀ | no nv  | _       | no _ | nothing

  -- with `v` absent from every right side, no lower bound is found

  lowsOf-none : (l : List (X × X)) → (∀ {a} → a ∈ l → FreeR a)
              → (L : Lows l) → lowsOf l ≡ just L → bnds L ≡ []
  lowsOf-none []             h L refl = refl
  lowsOf-none ((x , x') ∷ l) h L eq
    with lowsOf l in e | x' ≟ v | isFalse (occ x) in ex | x ≟ x' | isFalse (occ x') in ex' | h (here refl)
  ... | nothing | _       | _       | _     | _      | _        = ⊥-elim (nj eq)
    where nj : ∀ {A : Set} {a : A} → nothing ≡ just a → ⊥
          nj ()
  ... | just L₀ | yes refl | just qx | _    | _      | inj₁ refl = ⊥-elim (tf (trans (sym occ-v) qx))
    where tf : true ≡ false → ⊥
          tf ()
  ... | just L₀ | yes refl | just qx | _    | _      | inj₂ q    = ⊥-elim (tf (trans (sym occ-v) q))
    where tf : true ≡ false → ⊥
          tf ()
  ... | just L₀ | yes _ | nothing | yes _  | _      | _ with eq
  ...   | refl = lowsOf-none l (λ m → h (there m)) L₀ e
  lowsOf-none ((x , x') ∷ l) h L eq | just L₀ | no _ | _ | yes _ | _ | _ with eq
  ...   | refl = lowsOf-none l (λ m → h (there m)) L₀ e
  lowsOf-none ((x , x') ∷ l) h L eq | just L₀ | yes _ | nothing | no _ | just _ | _ with eq
  ...   | refl = lowsOf-none l (λ m → h (there m)) L₀ e
  lowsOf-none ((x , x') ∷ l) h L eq | just L₀ | no _ | _ | no _ | just _ | _ with eq
  ...   | refl = lowsOf-none l (λ m → h (there m)) L₀ e
  lowsOf-none ((x , x') ∷ l) h L () | just L₀ | yes _ | nothing | no _ | nothing | _
  lowsOf-none ((x , x') ∷ l) h L () | just L₀ | no _  | _       | no _ | nothing | _

  -- a bound above `v`, free of it, that the decider puts below every
  -- other bound above it

  UpOK : X → X × X → Set
  UpOK U (x , x') = FreeL (x , x') ⊎ ((x ≡ v) × ((x' ≡ U) ⊎ (dec≤ U x' ≡ nothing → ⊥)))

  upsAt-ok : (U : X) → (l : List (X × X)) → (∀ {a} → a ∈ l → UpOK U a) → upsAt U l ≡ nothing → ⊥
  upsAt-ok U []             h ()
  upsAt-ok U ((x , x') ∷ l) h
    with upsAt U l in e | x ≟ x' | isFalse (occ x) in ex | x ≟ v | h (here refl)
  ... | nothing | _     | _       | _      | _                      = λ _ → upsAt-ok U l (λ m → h (there m)) e
  ... | just _  | yes _ | _       | _      | _                      = λ ()
  ... | just _  | no _  | just _  | _      | _                      = λ ()
  ... | just _  | no ne | nothing | _      | inj₁ (inj₁ eq)         = λ _ → ne eq
  ... | just _  | no _  | nothing | _      | inj₁ (inj₂ q)          = λ _ → isFalse-ok q ex
  ... | just _  | no _  | nothing | no nv  | inj₂ (ev , _)          = λ _ → nv ev
  ... | just _  | no _  | nothing | yes _  | inj₂ (_ , inj₁ eU) with x' ≟ U
  ...   | yes _  = λ ()
  ...   | no neU = λ _ → neU eU
  upsAt-ok U ((x , x') ∷ l) h | just _ | no _ | nothing | yes _ | inj₂ (_ , inj₂ dj) with x' ≟ U
  ...   | yes _  = λ ()
  ...   | no _ with dec≤ U x'
  ...     | just _  = λ ()
  ...     | nothing = λ _ → dj refl

  Cand : List (X × X) → Set
  Cand l = Σ[ U ∈ X ] (((v , U) ∈ l) × (occ U ≡ false))

  shiftCaps-∈ : ∀ {a} {l : List (X × X)} (us : List (Cand l)) → ∀ {U}
              → U ∈ map proj₁ us → U ∈ map proj₁ (shiftCaps {a = a} us)
  shiftCaps-∈ (u ∷ us) (here refl) = here refl
  shiftCaps-∈ (u ∷ us) (there m)   = there (shiftCaps-∈ us m)

  capsOf-∈ : (l : List (X × X)) → ∀ {U} → (v , U) ∈ l → occ U ≡ false → U ∈ map proj₁ (capsOf l)
  capsOf-∈ ((x , x') ∷ l) m q with x ≟ v | isFalse (occ x') in ex' | m
  ... | yes refl | just q' | here refl = here refl
  ... | yes refl | nothing | here refl = ⊥-elim (isFalse-ok q ex')
  ... | no nv    | _       | here refl = ⊥-elim (nv refl)
  ... | yes refl | just q' | there m'  = there (shiftCaps-∈ (capsOf l) (capsOf-∈ l m' q))
  ... | yes refl | nothing | there m'  = shiftCaps-∈ (capsOf l) (capsOf-∈ l m' q)
  ... | no nv    | _       | there m'  = shiftCaps-∈ (capsOf l) (capsOf-∈ l m' q)

  firstUp-ok : (l : List (X × X)) → (us : List (Cand l)) → ∀ {U} → U ∈ map proj₁ us
             → (upsAt U l ≡ nothing → ⊥) → firstUp l us ≡ nothing → ⊥
  firstUp-ok l ((U' , m , q) ∷ us) mu h with upsAt U' l in e
  ... | just _  = λ ()
  firstUp-ok l ((U' , m , q) ∷ us) (here refl) h | nothing = λ _ → h e
  firstUp-ok l ((U' , m , q) ∷ us) (there mu)  h | nothing = firstUp-ok l us mu h

  upsOf-ok : (l : List (X × X)) → ∀ {U} → (v , U) ∈ l → occ U ≡ false
           → (∀ {a} → a ∈ l → UpOK U a) → upsOf l ≡ nothing → ⊥
  upsOf-ok l m q h = firstUp-ok l (capsOf l) (capsOf-∈ l m q) (upsAt-ok _ l h)

------------------------------------------------------------------------
-- The deferred entries kept, the unknown absent from the types and
-- the disjunctions' grades: the tests succeed

fixedʳ?-ok : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (a : RExp Ψ × RExp Ψ)
           → Fixedʳ d σ a → fixedʳ? d σ a ≡ nothing → ⊥
fixedʳ?-ok dir↓ σ (x , y) q with y [ σ ]ʳ ≟ʳ y
... | yes _ = λ ()
... | no n  = λ _ → n q
fixedʳ?-ok dir↑ σ (x , y) q with x [ σ ]ʳ ≟ʳ x
... | yes _ = λ ()
... | no n  = λ _ → n q

fixedᵉ?-ok : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (a : EExp Ψ × EExp Ψ)
           → Fixedᵉ d σ a → fixedᵉ? d σ a ≡ nothing → ⊥
fixedᵉ?-ok dir↓ σ (x , y) q with y [ σ ]ᵉ ≟ᵉ y
... | yes _ = λ ()
... | no n  = λ _ → n q
fixedᵉ?-ok dir↑ σ (x , y) q with x [ σ ]ᵉ ≟ᵉ x
... | yes _ = λ ()
... | no n  = λ _ → n q

still?-ok : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (E : Dfr Ψ) → Still d σ E → still? d σ E ≡ nothing → ⊥
still?-ok d σ E (still sr se)
  with allOf (fixedʳ? d (σ ↑ᵉⁿ nb E)) (ors (body E)) in er
     | allOf (fixedᵉ? d (σ ↑ᵉⁿ nb E)) (oes (body E)) in ee
... | just _  | just _  = λ ()
... | nothing | _       = λ _ → allOf-ok _ (ors (body E)) (λ {a} m → fixedʳ?-ok d _ a (sr m)) er
... | just _  | nothing = λ _ → allOf-ok _ (oes (body E)) (λ {a} m → fixedᵉ?-ok d _ a (se m)) ee

stills?-ok : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (D : List (Dfr Ψ))
           → (∀ {E} → E ∈ D → Still d σ E) → stills? d σ D ≡ nothing → ⊥
stills?-ok d σ D h = allOf-ok (still? d σ) D (λ {E} m → still?-ok d σ E (h m))

cleanᵉ?-ok : ∀ {Ψ} → (k : EVar Ψ) → (R : Resid Ψ) → Cleanᵉ k R → cleanᵉ? k R ≡ nothing → ⊥
cleanᵉ?-ok k R (cleanᵉ t s d)
  with allFalse (occᵉ-v k) (ts R) in et
     | allFalse (occᵉ-ss k) (ss R) in es'
     | allFalse (occᵉ-dty k) (ds R) in ed
... | just _  | just _  | just _  = λ ()
... | nothing | _       | _       = λ _ → allFalse-ok _ (ts R) t et
... | just _  | nothing | _       = λ _ → allFalse-ok _ (ss R) s es'
... | just _  | just _  | nothing = λ _ → allFalse-ok _ (ds R) d ed

cleanʳ?-ok : ∀ {Ψ} → (k : RVar Ψ) → (R : Resid Ψ) → Cleanʳ k R → cleanʳ? k R ≡ nothing → ⊥
cleanʳ?-ok k R (cleanʳ t s d)
  with allFalse (occʳ-v k) (ts R) in et
     | allFalse (occʳ-ss k) (ss R) in es'
     | allFalse (occʳ-dty k) (ds R) in ed
... | just _  | just _  | just _  = λ ()
... | nothing | _       | _       = λ _ → allFalse-ok _ (ts R) t et
... | just _  | nothing | _       = λ _ → allFalse-ok _ (ss R) s es'
... | just _  | just _  | nothing = λ _ → allFalse-ok _ (ds R) d ed

dfreeᵉ?-ok : ∀ {Ψ} → (k : EVar Ψ) → (R : Resid Ψ) → DFreeᵉ k R → dfreeᵉ? k R ≡ nothing → ⊥
dfreeᵉ?-ok k R h with allFalse (occᵉ-dgr k) (ds R) in e
... | just _  = λ ()
... | nothing = λ _ → allFalse-ok _ (ds R) h e

dfreeʳ?-ok : ∀ {Ψ} → (k : RVar Ψ) → (R : Resid Ψ) → DFreeʳ k R → dfreeʳ? k R ≡ nothing → ⊥
dfreeʳ?-ok k R h with allFalse (occʳ-dgr k) (ds R) in e
... | just _  = λ ()
... | nothing = λ _ → allFalse-ok _ (ds R) h e

------------------------------------------------------------------------
-- An effect unknown

module _ {Ψ} (k : EVar Ψ) (R : Resid Ψ) where

  private
    module BO = BoundsOK (_≟ᵉ_ {Ψ}) (occᵉ-e {Ψ} k) (evar k) (∅ᴴ ⊩_≾̂ₑ_) (decide≾ₑ {Q = ∅ᴴ})
                         (dec-true (k ≟ᶠ k) refl)
    module SE = SidesOK (_≟ᵉ_ {Ψ}) (occᵉ-e {Ψ} k)
    module SR = SidesOK (_≟ʳ_ {Ψ}) (occᵉ-r {Ψ} k)

  -- the deferred entries keep their greater (smaller) sides, whatever
  -- the unknown is sent to

  Downᵉ Upᵉ : Set
  Downᵉ = ∀ b → ∀ {E} → E ∈ dfs R → Still dir↓ (updᵉ k b) E
  Upᵉ   = ∀ b → ∀ {E} → E ∈ dfs R → Still dir↑ (updᵉ k b) E

  record Lowerᵉ : Set where
    constructor lowerᵉ
    field
      l-cl : Cleanᵉ k R
      l-rs : ∀ {a} → a ∈ rs R → Bᵉʳ.FreeR {Ψ} k a
      l-es : ∀ {a} → a ∈ es R → BO.LowOK a
      l-lb : Σ[ x ∈ EExp Ψ ] (((x , evar k) ∈ es R) × (occᵉ-e k x ≡ false))
      l-dn : Downᵉ

  record Upperᵉ : Set where
    constructor upperᵉ
    field
      u-cl  : Cleanᵉ k R
      u-rs  : ∀ {a} → a ∈ rs R → Bᵉʳ.FreeL {Ψ} k a
      u-df  : DFreeᵉ k R
      u-cap : EExp Ψ
      u-src : (evar k , u-cap) ∈ es R
      u-cfr : occᵉ-e k u-cap ≡ false
      u-es  : ∀ {a} → a ∈ es R → BO.UpOK u-cap a
      u-up  : Upᵉ

  record Unitᵉ : Set where
    constructor unitᵉ
    field
      n-ij : Is-just uₑ-least?
      n-cl : Cleanᵉ k R
      n-rs : ∀ {a} → a ∈ rs R → Bᵉʳ.FreeR {Ψ} k a
      n-es : ∀ {a} → a ∈ es R → Bᵉ.FreeR {Ψ} k a
      n-oc : occursᵉ k R ≡ true
      n-dn : Downᵉ

  record Topᵉ : Set where
    constructor topᵉ
    field
      t-cl : Cleanᵉ k R
      t-es : ∀ {a} → a ∈ es R → Bᵉ.FreeL {Ψ} k a
      t-rs : ∀ {a} → a ∈ rs R → Bᵉʳ.FreeL {Ψ} k a
      t-df : DFreeᵉ k R
      t-oc : occursᵉ⁺ k R ≡ true
      t-up : Upᵉ

  Readyᵉ : Set
  Readyᵉ = Lowerᵉ ⊎ Upperᵉ ⊎ Unitᵉ ⊎ Topᵉ

  -- each rule's test succeeds on its conditions

  lowerᵉ?-ok : (cl : Cleanᵉ k R) → Lowerᵉ
             → lowerᵉ? k R cl (Bᵉ.lowsOf {Ψ} k (es R)) (Bᵉʳ.freeRs {Ψ} k (rs R)) ≡ nothing → ⊥
  lowerᵉ?-ok cl (lowerᵉ _ hr he (x₀ , m₀ , q₀) hd)
    with Bᵉ.lowsOf {Ψ} k (es R) in el | Bᵉʳ.freeRs {Ψ} k (rs R) in ef
  ... | nothing | _ = λ _ → BO.lowsOf-ok (es R) he el
  ... | just _  | nothing = λ _ → SR.freeRs-ok (rs R) hr ef
  ... | just L@(Bᵉ.lows [] c s f) | just fr with BO.lowsOf-bnd (es R) L el m₀ q₀
  ...   | ()
  lowerᵉ?-ok cl (lowerᵉ _ hr he (x₀ , m₀ , q₀) hd)
    | just (Bᵉ.lows (x ∷ xs) c s f) | just fr with stills? dir↓ (updᵉ k (joinₑ x xs)) (dfs R) in es'
  ...   | just _  = λ ()
  ...   | nothing = λ _ → stills?-ok dir↓ _ (dfs R) (hd (joinₑ x xs)) es'

  raiseᵉ?-ok : (cl : Cleanᵉ k R) → Upperᵉ
             → raiseᵉ? k R cl (Bᵉ.upsOf {Ψ} k (es R)) (Bᵉʳ.freeLs {Ψ} k (rs R)) (dfreeᵉ? k R) ≡ nothing → ⊥
  raiseᵉ?-ok cl (upperᵉ _ hr hdf U mU qU he hu)
    with Bᵉ.upsOf {Ψ} k (es R) in eu | Bᵉʳ.freeLs {Ψ} k (rs R) in el | dfreeᵉ? k R in ed
  ... | nothing | _       | _       = λ _ → BO.upsOf-ok (es R) mU qU he eu
  ... | just _  | nothing | _       = λ _ → SR.freeLs-ok (rs R) hr el
  ... | just _  | just _  | nothing = λ _ → dfreeᵉ?-ok k R hdf ed
  ... | just up | just _  | just _ with stills? dir↑ (updᵉ k (Bᵉ.cap up)) (dfs R) in es'
  ...   | just _  = λ ()
  ...   | nothing = λ _ → stills?-ok dir↑ _ (dfs R) (hu (Bᵉ.cap up)) es'

  unitᵉ?-ok : (cl : Cleanᵉ k R) → Unitᵉ
            → unitᵉ? k R cl (Is-just? uₑ-least?) (Bᵉ.lowsOf {Ψ} k (es R)) (Bᵉʳ.freeRs {Ψ} k (rs R))
                     (occursᵉ k R) ≡ nothing → ⊥
  unitᵉ?-ok cl (unitᵉ ij _ hr he oc hd)
    with Is-just? uₑ-least? in ei | Bᵉ.lowsOf {Ψ} k (es R) in el | Bᵉʳ.freeRs {Ψ} k (rs R) in ef
       | occursᵉ k R | oc
  ... | nothing | _       | _       | _    | _    = λ _ → isJust?-ok uₑ-least? ij ei
  ... | just _  | nothing | _       | _    | _    = λ _ → BO.lowsOf-ok (es R) (λ m → inj₂ (he m)) el
  ... | just _  | just _  | nothing | _    | _    = λ _ → SR.freeRs-ok (rs R) hr ef
  ... | just _  | just L@(Bᵉ.lows (x ∷ xs) c s f) | just _ | _ | _ with BO.lowsOf-none (es R) he L el
  ...   | ()
  unitᵉ?-ok cl (unitᵉ ij _ hr he oc hd)
    | just _ | just (Bᵉ.lows [] c s f) | just _ | true | refl
    with stills? dir↓ (updᵉ k ûₑ) (dfs R) in es'
  ...   | just _  = λ ()
  ...   | nothing = λ _ → stills?-ok dir↓ _ (dfs R) (hd ûₑ) es'

  topᵉ?-ok : (cl : Cleanᵉ k R) → Topᵉ
           → topᵉ? k R cl (Bᵉ.freeLs {Ψ} k (es R)) (Bᵉʳ.freeLs {Ψ} k (rs R)) (dfreeᵉ? k R)
                   (occursᵉ⁺ k R) ≡ nothing → ⊥
  topᵉ?-ok cl (topᵉ _ he hr hdf oc hu)
    with Bᵉ.freeLs {Ψ} k (es R) in ee | Bᵉʳ.freeLs {Ψ} k (rs R) in el | dfreeᵉ? k R in ed
       | occursᵉ⁺ k R | oc
  ... | nothing | _       | _       | _    | _    = λ _ → SE.freeLs-ok (es R) he ee
  ... | just _  | nothing | _       | _    | _    = λ _ → SR.freeLs-ok (rs R) hr el
  ... | just _  | just _  | nothing | _    | _    = λ _ → dfreeᵉ?-ok k R hdf ed
  ... | just _  | just _  | just _  | true | refl with stills? dir↑ (updᵉ k (econst ⊤ₑ)) (dfs R) in es'
  ...   | just _  = λ ()
  ...   | nothing = λ _ → stills?-ok dir↑ _ (dfs R) (hu (econst ⊤ₑ)) es'

  -- A ready unknown is given a value

  stepᵉ-ok : Readyᵉ → stepᵉ k R ≡ nothing → ⊥
  stepᵉ-ok rd with cleanᵉ? k R in ec
  ... | nothing = λ _ → cleanᵉ?-ok k R (clean rd) ec
    where
      clean : Readyᵉ → Cleanᵉ k R
      clean (inj₁ r)               = Lowerᵉ.l-cl r
      clean (inj₂ (inj₁ r))        = Upperᵉ.u-cl r
      clean (inj₂ (inj₂ (inj₁ r))) = Unitᵉ.n-cl r
      clean (inj₂ (inj₂ (inj₂ r))) = Topᵉ.t-cl r
  ... | just cl = λ q → go rd (first4 q)
    where
      Lo = lowerᵉ? k R cl (Bᵉ.lowsOf {Ψ} k (es R)) (Bᵉʳ.freeRs {Ψ} k (rs R))
      Ra = raiseᵉ? k R cl (Bᵉ.upsOf {Ψ} k (es R)) (Bᵉʳ.freeLs {Ψ} k (rs R)) (dfreeᵉ? k R)
      Un = unitᵉ? k R cl (Is-just? uₑ-least?) (Bᵉ.lowsOf {Ψ} k (es R)) (Bᵉʳ.freeRs {Ψ} k (rs R))
                  (occursᵉ k R)
      To = topᵉ? k R cl (Bᵉ.freeLs {Ψ} k (es R)) (Bᵉʳ.freeLs {Ψ} k (rs R)) (dfreeᵉ? k R) (occursᵉ⁺ k R)

      first4 : first Lo (first Ra (first Un To)) ≡ nothing
             → (Lo ≡ nothing) × (Ra ≡ nothing) × (Un ≡ nothing) × (To ≡ nothing)
      first4 q with first-nothing Lo _ q
      ... | q₁ , q' with first-nothing Ra _ q'
      ...   | q₂ , q'' with first-nothing Un To q''
      ...     | q₃ , q₄ = q₁ , q₂ , q₃ , q₄

      go : Readyᵉ → (Lo ≡ nothing) × (Ra ≡ nothing) × (Un ≡ nothing) × (To ≡ nothing) → ⊥
      go (inj₁ r)               (q , _)         = lowerᵉ?-ok cl r q
      go (inj₂ (inj₁ r))        (_ , q , _)     = raiseᵉ?-ok cl r q
      go (inj₂ (inj₂ (inj₁ r))) (_ , _ , q , _) = unitᵉ?-ok cl r q
      go (inj₂ (inj₂ (inj₂ r))) (_ , _ , _ , q) = topᵉ?-ok cl r q

------------------------------------------------------------------------
-- A resource unknown

module _ {Ψ} (k : RVar Ψ) (R : Resid Ψ) where

  private
    module BO = BoundsOK (_≟ʳ_ {Ψ}) (occʳ-r {Ψ} k) (rvar k) (∅ᴴ ⊩_≾̂ᵣ_) (decide≾ᵣ {Q = ∅ᴴ})
                         (dec-true (k ≟ᶠ k) refl)
    module SR = SidesOK (_≟ʳ_ {Ψ}) (occʳ-r {Ψ} k)

  Downʳ Upʳ : Set
  Downʳ = ∀ b → ∀ {E} → E ∈ dfs R → Still dir↓ (updʳ k b) E
  Upʳ   = ∀ b → ∀ {E} → E ∈ dfs R → Still dir↑ (updʳ k b) E

  record Lowerʳ : Set where
    constructor lowerʳ
    field
      l-cl : Cleanʳ k R
      l-rs : ∀ {a} → a ∈ rs R → BO.LowOK a
      l-lb : Σ[ x ∈ RExp Ψ ] (((x , rvar k) ∈ rs R) × (occʳ-r k x ≡ false))
      l-dn : Downʳ

  record Upperʳ : Set where
    constructor upperʳ
    field
      u-cl  : Cleanʳ k R
      u-df  : DFreeʳ k R
      u-cap : RExp Ψ
      u-src : (rvar k , u-cap) ∈ rs R
      u-cfr : occʳ-r k u-cap ≡ false
      u-rs  : ∀ {a} → a ∈ rs R → BO.UpOK u-cap a
      u-up  : Upʳ

  record Unitʳ : Set where
    constructor unitʳ
    field
      n-ij : Is-just uᵣ-least?
      n-cl : Cleanʳ k R
      n-rs : ∀ {a} → a ∈ rs R → Bʳ.FreeR {Ψ} k a
      n-oc : occursʳ k R ≡ true
      n-dn : Downʳ

  record Topʳ : Set where
    constructor topʳ
    field
      t-cl : Cleanʳ k R
      t-rs : ∀ {a} → a ∈ rs R → Bʳ.FreeL {Ψ} k a
      t-df : DFreeʳ k R
      t-oc : occursʳ⁺ k R ≡ true
      t-up : Upʳ

  Readyʳ : Set
  Readyʳ = Lowerʳ ⊎ Upperʳ ⊎ Unitʳ ⊎ Topʳ

  lowerʳ?-ok : (cl : Cleanʳ k R) → Lowerʳ → lowerʳ? k R cl (Bʳ.lowsOf {Ψ} k (rs R)) ≡ nothing → ⊥
  lowerʳ?-ok cl (lowerʳ _ hr (x₀ , m₀ , q₀) hd) with Bʳ.lowsOf {Ψ} k (rs R) in el
  ... | nothing = λ _ → BO.lowsOf-ok (rs R) hr el
  ... | just L@(Bʳ.lows [] c s f) with BO.lowsOf-bnd (rs R) L el m₀ q₀
  ...   | ()
  lowerʳ?-ok cl (lowerʳ _ hr (x₀ , m₀ , q₀) hd)
    | just (Bʳ.lows (x ∷ xs) c s f) with stills? dir↓ (updʳ k (joinᵣ x xs)) (dfs R) in es'
  ...   | just _  = λ ()
  ...   | nothing = λ _ → stills?-ok dir↓ _ (dfs R) (hd (joinᵣ x xs)) es'

  raiseʳ?-ok : (cl : Cleanʳ k R) → Upperʳ
             → raiseʳ? k R cl (Bʳ.upsOf {Ψ} k (rs R)) (dfreeʳ? k R) ≡ nothing → ⊥
  raiseʳ?-ok cl (upperʳ _ hdf U mU qU hr hu)
    with Bʳ.upsOf {Ψ} k (rs R) in eu | dfreeʳ? k R in ed
  ... | nothing | _       = λ _ → BO.upsOf-ok (rs R) mU qU hr eu
  ... | just _  | nothing = λ _ → dfreeʳ?-ok k R hdf ed
  ... | just up | just _ with stills? dir↑ (updʳ k (Bʳ.cap up)) (dfs R) in es'
  ...   | just _  = λ ()
  ...   | nothing = λ _ → stills?-ok dir↑ _ (dfs R) (hu (Bʳ.cap up)) es'

  unitʳ?-ok : (cl : Cleanʳ k R) → Unitʳ
            → unitʳ? k R cl (Is-just? uᵣ-least?) (Bʳ.lowsOf {Ψ} k (rs R)) (occursʳ k R) ≡ nothing → ⊥
  unitʳ?-ok cl (unitʳ ij _ hr oc hd)
    with Is-just? uᵣ-least? in ei | Bʳ.lowsOf {Ψ} k (rs R) in el | occursʳ k R | oc
  ... | nothing | _       | _    | _    = λ _ → isJust?-ok uᵣ-least? ij ei
  ... | just _  | nothing | _    | _    = λ _ → BO.lowsOf-ok (rs R) (λ m → inj₂ (hr m)) el
  ... | just _  | just L@(Bʳ.lows (x ∷ xs) c s f) | _ | _ with BO.lowsOf-none (rs R) hr L el
  ...   | ()
  unitʳ?-ok cl (unitʳ ij _ hr oc hd) | just _ | just (Bʳ.lows [] c s f) | true | refl
    with stills? dir↓ (updʳ k ûᵣ) (dfs R) in es'
  ...   | just _  = λ ()
  ...   | nothing = λ _ → stills?-ok dir↓ _ (dfs R) (hd ûᵣ) es'

  topʳ?-ok : (cl : Cleanʳ k R) → Topʳ
           → topʳ? k R cl (Bʳ.freeLs {Ψ} k (rs R)) (dfreeʳ? k R) (occursʳ⁺ k R) ≡ nothing → ⊥
  topʳ?-ok cl (topʳ _ hr hdf oc hu)
    with Bʳ.freeLs {Ψ} k (rs R) in el | dfreeʳ? k R in ed | occursʳ⁺ k R | oc
  ... | nothing | _       | _    | _    = λ _ → SR.freeLs-ok (rs R) hr el
  ... | just _  | nothing | _    | _    = λ _ → dfreeʳ?-ok k R hdf ed
  ... | just _  | just _  | true | refl with stills? dir↑ (updʳ k (rconst ⊤ᵣ)) (dfs R) in es'
  ...   | just _  = λ ()
  ...   | nothing = λ _ → stills?-ok dir↑ _ (dfs R) (hu (rconst ⊤ᵣ)) es'

  stepʳ-ok : Readyʳ → stepʳ k R ≡ nothing → ⊥
  stepʳ-ok rd with cleanʳ? k R in ec
  ... | nothing = λ _ → cleanʳ?-ok k R (clean rd) ec
    where
      clean : Readyʳ → Cleanʳ k R
      clean (inj₁ r)               = Lowerʳ.l-cl r
      clean (inj₂ (inj₁ r))        = Upperʳ.u-cl r
      clean (inj₂ (inj₂ (inj₁ r))) = Unitʳ.n-cl r
      clean (inj₂ (inj₂ (inj₂ r))) = Topʳ.t-cl r
  ... | just cl = λ q → go rd (first4 q)
    where
      Lo = lowerʳ? k R cl (Bʳ.lowsOf {Ψ} k (rs R))
      Ra = raiseʳ? k R cl (Bʳ.upsOf {Ψ} k (rs R)) (dfreeʳ? k R)
      Un = unitʳ? k R cl (Is-just? uᵣ-least?) (Bʳ.lowsOf {Ψ} k (rs R)) (occursʳ k R)
      To = topʳ? k R cl (Bʳ.freeLs {Ψ} k (rs R)) (dfreeʳ? k R) (occursʳ⁺ k R)

      first4 : first Lo (first Ra (first Un To)) ≡ nothing
             → (Lo ≡ nothing) × (Ra ≡ nothing) × (Un ≡ nothing) × (To ≡ nothing)
      first4 q with first-nothing Lo _ q
      ... | q₁ , q' with first-nothing Ra _ q'
      ...   | q₂ , q'' with first-nothing Un To q''
      ...     | q₃ , q₄ = q₁ , q₂ , q₃ , q₄

      go : Readyʳ → (Lo ≡ nothing) × (Ra ≡ nothing) × (Un ≡ nothing) × (To ≡ nothing) → ⊥
      go (inj₁ r)               (q , _)         = lowerʳ?-ok cl r q
      go (inj₂ (inj₁ r))        (_ , q , _)     = raiseʳ?-ok cl r q
      go (inj₂ (inj₂ (inj₁ r))) (_ , _ , q , _) = unitʳ?-ok cl r q
      go (inj₂ (inj₂ (inj₂ r))) (_ , _ , _ , q) = topʳ?-ok cl r q
