------------------------------------------------------------------
-- Values for one unknown, read off the orderings of its sort   --
--                                                              --
-- A sort (`Sort`) reads the expressions of one grade sort for  --
-- an unknown `v`: whether `v` occurs, the order decided from   --
-- no hypotheses, the join, the unit, the top, canonical forms, --
-- whether the unit is least, which expressions may replace     --
-- `v`, an expression with `v` sent to a value (`put`), the     --
-- product and a product's factors, and the closure of an       --
-- expression where the hints declare it (`Closure`; none       --
-- through the image of an effect unknown). An ordering is      --
-- valid when it is reflexive or decided (`Valid`); it bounds   --
-- `v` on neither side. An oracle (`Oracle`) says whether `v`   --
-- may decrease, or increase, to a value, the atoms outside the --
-- sort keeping their meaning.                                  --
-- The rules, each a proposition with its decider:              --
--   * lowering (`Lows`, `lower`), principal: every ordering is --
--     valid, has `v` on no right side, is `x ≾ v` with `x`     --
--     free of `v`, a lower bound, of which there is one, or is --
--     a cycle `p ≾ v` with `v` in `p`. From the join `L` of    --
--     the lower bounds, the value is `V = B* · L · C*`, and    --
--     `V = (B* · L · C*)⁺` where a cycle is `v · v ≾ v`: `B`   --
--     and `C` join the multipliers of the cycles `b · v ≾ v`   --
--     and `v · c ≾ v`, `b` and `c` free of `v`, `X* · y` is    --
--     `y ⊔ X⁺ · y`, or `y` where each multiplier leaves `y`,   --
--     decided, and an expression absorbing its own iteration,  --
--     decided, is its own closure (`Shapes`, `Clo`, `StarL`,   --
--     `StarR`, `Sq`). `V` is taken where the closures it needs --
--     exist and every cycle, of any shape, closes at it, `p`   --
--     with `v` sent to `V` decided below `V` (`Closes`,        --
--     `LowTo`);                                                --
--   * raising (`Ups`, `raise`), instance-keeping: the first    --
--     ordering `v ≾ U`, `U` free of `v`, that caps the others, --
--     every ordering being valid, reflexive, with `v` on no    --
--     left side, or `v ≾ x'` with `U ≾ x'` decided; the value  --
--     is `U`;                                                  --
--   * least (`least`), principal: as lowering with no lower    --
--     bound, where the unit is least, `L` being the unit;      --
--   * top (`top`), instance-keeping: every ordering is valid,  --
--     has `v` on no left side, or has `v` as its whole right   --
--     side (`UnderTop`); the value is the top;                 --
--   * forced unit (`Forces`), principal: an ordering `x ≾ y`   --
--     with `x` canonically `v` and `y` decided below the unit, --
--     the unit being least; every solution sends `v` to the    --
--     unit, whatever the occurrences of `v`;                   --
--   * equating (`equate`), principal: the first expression an  --
--     ordering sets against `v`, an earlier unknown or free of --
--     `v`, that a given test places above and below `v`.       --
-- The caller determines which unknowns may be assigned, in     --
-- which order, and what an oracle asks. Lowering and raising   --
-- follow the elimination of variables by polarity (Pottier,    --
-- ICFP 1996; Trifonov and Smith, SAS 1996).                    --
--                                                              --
-- Contract. The orderings are read through interpretations of  --
-- the sides before and after the assignment (`f₀`, `f₁`) into  --
-- a preorder that agree where `v` does not occur, and that     --
-- keep the decided order after it: at an instance              --
-- (`Localise`), or by entailment along the assignment          --
-- (`Eliminate`). Each value keeps every ordering: lowering and --
-- the least element keep those that lie below `v` and its      --
-- cycles (`lower-keeps`), the upper bound and the top those    --
-- that lie above it (`raise-keeps`, `raise-free`), the top     --
-- also those with `v` as the right side (`top-keeps`), and an  --
-- equal value all of them (`equal-keeps`); an unknown on no    --
-- right side remains so under lowering (`lower-free`). Under   --
-- lowering, each ordering with `v` on its right side holds     --
-- outright, being a lower bound, a cycle, a bound free of `v`, --
-- or valid (`lower-drops`). Lowering is principal: each lower  --
-- bound is an ordering below `v` (`src`), so wherever the      --
-- orderings hold, their join lies below `v` (`joinₑ-lub⊩`),    --
-- and so does `V`, by one argument from the laws of the        --
-- closure for every shape of cycle (`srcᶜ`, `indˡₑ`, `indʳₑ`,  --
-- `plusₑ`; `LowToₑ`). That the upper bound and the top are     --
-- least is not claimed.                                        --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; not; true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (toℕ)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Data.Maybe using (Is-just)
open import Data.Nat.Base using (_<ᵇ_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Relation.Binary.Definitions using (DecidableEquality; Decidable)
open import Relation.Nullary using (Dec; yes; no)

open import Grades.Base
open import Grades.Hints using (SystemHints; module SystemHintsInterface)
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Inference.SolverImpl.Values (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) where

open LanguageSpec S
open GradeSystemInterface Grades
open SystemHintsInterface hints

open import OpenCalculus.Syntax.Grades S
open import OpenCalculus.Syntax.Subst  S
open import OpenCalculus.Hypotheses    S

open import OpenCalculus.Inference.SolverImpl.Core.Occurs S using (occᵉ-e; occᵉ-r; occʳ-r)
open import OpenCalculus.Inference.SolverImpl.Entail      S hints using (decideᵣ; decideₑ; full)
open import OpenCalculus.Inference.SolverImpl.Canon       S hints using (canonᵣ; canonₑ)

isFalse : (b : 𝔹) → Maybe (b ≡ false)
isFalse false = just refl
isFalse true  = nothing

private
  ∨-false : (b b' : 𝔹) → b ∨ b' ≡ false → (b ≡ false) × (b' ≡ false)
  ∨-false false b' q = refl , q
  ∨-false true  b' ()

  true≢false : true ≡ false → ⊥
  true≢false ()

-- A property of every entry of a list, decided entry by entry

every : ∀ {X : Set} {P : X → Set} → ((a : X) → Maybe (P a)) → (l : List X)
      → Maybe (∀ {a} → a ∈ l → P a)
every p []      = just (λ ())
every p (a ∷ l) with p a | every p l
... | just q | just f = just (λ { (here refl) → q ; (there m) → f m })
... | _      | _      = nothing

-- The entries of a list a decider rejects, each other one accepted

record Parts {X : Set} (P : X → Set) (l : List X) : Set where
  constructor parts
  field
    kept  : List X
    kept⊆ : ∀ {a} → a ∈ kept → a ∈ l
    which : ∀ {a} → a ∈ l → P a ⊎ (a ∈ kept)

open Parts public

partition : ∀ {X : Set} {P : X → Set} → ((a : X) → Maybe (P a)) → (l : List X) → Parts P l
partition p []      = parts [] (λ ()) (λ ())
partition {P = P} p (a ∷ l) = go (p a) (partition p l)
  where
    go : Maybe (P a) → Parts P l → Parts P (a ∷ l)
    go (just v) (parts k s c) =
      parts k (λ m → there (s m)) (λ { (here refl) → inj₁ v ; (there m) → c m })
    go nothing  (parts k s c) =
      parts (a ∷ k) (λ { (here refl) → here refl ; (there m) → there (s m) })
            (λ { (here refl) → inj₂ (here refl)
               ; (there m)   → [ inj₁ , (λ m' → inj₂ (there m')) ]′ (c m) })

-- The join of a non-empty list, given as a head and a tail and folded
-- to the left: a lone entry is its own join, and the join lists the
-- entries in the order met

joins : ∀ {X : Set} → (X → X → X) → X → List X → X
joins _⊔_ x []        = x
joins _⊔_ x (x' ∷ xs) = joins _⊔_ (x ⊔ x') xs

------------------------------------------------------------------------
-- Equal values keep every ordering: read before (`f₀`) and after
-- (`f₁`) an assignment, each side moves by as little in either
-- direction

equal-keeps : ∀ {X Y : Set} {_⊑_ : Y → Y → Set}
            → (∀ {y y' y''} → y ⊑ y' → y' ⊑ y'' → y ⊑ y'')
            → {f₀ f₁ : X → Y} {l : List (X × X)} → (∀ y → f₁ y ⊑ f₀ y) → (∀ y → f₀ y ⊑ f₁ y)
            → (∀ {x x'} → (x , x') ∈ l → f₀ x ⊑ f₀ x') → ∀ {x x'} → (x , x') ∈ l → f₁ x ⊑ f₁ x'
equal-keeps ⊑-trans lo hi h {x} {x'} m = ⊑-trans (lo x) (⊑-trans (h m) (hi x'))

------------------------------------------------------------------------
-- The expressions of one sort, read for one unknown

record Sort (X : Set) : Set₁ where
  field
    _≟_    : (x y : X) → Maybe (x ≡ y)   -- equality, where it is decided
    occ    : X → 𝔹                  -- whether the unknown occurs
    self   : X                      -- the unknown, as an expression
    _≤_    : X → X → Set            -- the order decided from no hypotheses
    dec≤   : (x y : X) → Maybe (x ≤ y)
    _≅_    : X → X → Set                -- sameness, the grades up to equivalence
    _≅?_   : Decidable _≅_
    ≅⇒≤    : ∀ {x y} → x ≅ y → x ≤ y
    join   : X → X → X
    unit   : X
    top    : X
    canon  : X → X
    Least  : Set                    -- the unit is least
    least? : Maybe Least
    fit    : X → 𝔹                  -- an earlier unknown, or free of the unknown
    put    : X → X → X              -- `put b x`: `x` with the unknown sent to `b`
    mul    : X → X → X              -- the product
    factors : (x : X) → Maybe (Σ[ y ∈ X ] Σ[ z ∈ X ] (x ≡ mul y z))   -- a product's factors
    Closure  : X → X → Set          -- `Closure x y`: `y` is the closure of `x`
    closure? : (x : X) → Maybe (Σ[ y ∈ X ] Closure x y)

module Rules {X : Set} (s : Sort X) where

  open Sort s

  ----------------------------------------------------------------------
  -- How the unknown occurs in a list of orderings

  -- Valid: reflexive, or decided, sides the same included

  Valid : X × X → Set
  Valid (x , x') = (x ≡ x') ⊎ (x ≤ x')

  valid? : (a : X × X) → Maybe (Valid a)
  valid? (x , x') with x ≅? x'
  ... | yes e = just (inj₂ (≅⇒≤ e))
  ... | no _  = map inj₂ (dec≤ x x')

  -- Valid, or the unknown absent from the right (left) side

  FreeR : X × X → Set
  FreeR (x , x') = Valid (x , x') ⊎ (occ x' ≡ false)

  FreeL : X × X → Set
  FreeL (x , x') = Valid (x , x') ⊎ (occ x ≡ false)

  freeR? : (a : X × X) → Maybe (FreeR a)
  freeR? (x , x') with isFalse (occ x')
  ... | just q  = just (inj₂ q)
  ... | nothing = map inj₁ (valid? (x , x'))

  freeL? : (a : X × X) → Maybe (FreeL a)
  freeL? (x , x') with isFalse (occ x)
  ... | just q  = just (inj₂ q)
  ... | nothing = map inj₁ (valid? (x , x'))

  freeRs : (l : List (X × X)) → Maybe (∀ {a} → a ∈ l → FreeR a)
  freeRs = every freeR?

  freeLs : (l : List (X × X)) → Maybe (∀ {a} → a ∈ l → FreeL a)
  freeLs = every freeL?

  -- The orderings that are not valid, each other one valid

  Live : List (X × X) → Set
  Live = Parts Valid

  lives : (l : List (X × X)) → Live l
  lives = partition valid?

  ----------------------------------------------------------------------
  -- Lowering: the bounds below, each free of the unknown, and the
  -- cycles, orderings `p ≾ v` with `p` mentioning the unknown; every
  -- other ordering has it on no right side, or is valid

  record Lows (l : List (X × X)) : Set where
    constructor lows
    field
      bnds  : List X
      cycs  : List X
      rest  : List (X × X)
      cls   : ∀ {x x'} → (x , x') ∈ l
            → ((x' ≡ self) × (x ∈ bnds)) ⊎ ((x' ≡ self) × (x ∈ cycs)) ⊎ ((x , x') ∈ rest)
      src   : ∀ {x} → x ∈ bnds → (x , self) ∈ l
      srcᶜ  : ∀ {x} → x ∈ cycs → (x , self) ∈ l
      bndF  : ∀ {x} → x ∈ bnds → occ x ≡ false
      rest⊆ : ∀ {a} → a ∈ rest → a ∈ l
      restR : ∀ {a} → a ∈ rest → FreeR a

  open Lows public

  lowsOf : (l : List (X × X)) → Maybe (Lows l)
  lowsOf []             = just (lows [] [] [] (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()))
  lowsOf ((x , x') ∷ l) = go (lowsOf l) (x' ≟ self) (isFalse (occ x)) (freeR? (x , x'))
    where
      toRest : Lows l → FreeR (x , x') → Lows ((x , x') ∷ l)
      toRest (lows L C r c s sc bf sb f) fr =
        lows L C ((x , x') ∷ r)
             (λ { (here refl) → inj₂ (inj₂ (here refl))
                ; (there m)   → [ inj₁ , [ (λ y → inj₂ (inj₁ y)) , (λ m' → inj₂ (inj₂ (there m'))) ]′ ]′
                                  (c m) })
             (λ m → there (s m)) (λ m → there (sc m)) bf
             (λ { (here refl) → here refl ; (there m) → there (sb m) })
             (λ { (here refl) → fr ; (there m) → f m })

      toCyc : Lows l → x' ≡ self → Lows ((x , x') ∷ l)
      toCyc (lows L C r c s sc bf sb f) e =
        lows L (x ∷ C) r
             (λ { (here refl) → inj₂ (inj₁ (e , here refl))
                ; (there m)   → [ inj₁ , [ (λ { (e' , mc) → inj₂ (inj₁ (e' , there mc)) })
                                         , (λ m' → inj₂ (inj₂ m')) ]′ ]′ (c m) })
             (λ m → there (s m))
             (λ { (here refl) → here (cong (x ,_) (sym e)) ; (there m) → there (sc m) })
             bf (λ m → there (sb m)) f

      go : Maybe (Lows l) → Maybe (x' ≡ self) → Maybe (occ x ≡ false) → Maybe (FreeR (x , x'))
         → Maybe (Lows ((x , x') ∷ l))
      go nothing                            _       _        _         = nothing
      go (just (lows L C r c s sc bf sb f)) (just e) (just q) _         =
        just (lows (x ∷ L) C r
                   (λ { (here refl) → inj₁ (e , here refl)
                      ; (there m)   → [ (λ { (e' , mb) → inj₁ (e' , there mb) })
                                      , (λ m' → inj₂ m') ]′ (c m) })
                   (λ { (here refl) → here (cong (x ,_) (sym e)) ; (there m) → there (s m) })
                   (λ m → there (sc m))
                   (λ { (here refl) → q ; (there m) → bf m })
                   (λ m → there (sb m)) f)
      go (just lw)                          _       _        (just fr) = just (toRest lw fr)
      go (just lw)                          (just e) _        nothing   = just (toCyc lw e)
      go (just lw)                          nothing  _        nothing   = nothing

  -- Each cycle holds once the unknown is sent to `b`, by the decided
  -- order

  Closes : (l : List (X × X)) → Lows l → X → Set
  Closes l lw b = ∀ {p} → p ∈ cycs lw → put b p ≤ b

  closes? : (l : List (X × X)) → (lw : Lows l) → (b : X) → Maybe (Closes l lw b)
  closes? l lw b = every (λ p → dec≤ (put b p) b) (cycs lw)

  -- Whether an entry is in a list

  _∈?_ : (x : X) → (xs : List X) → Maybe (x ∈ xs)
  x ∈? []       = nothing
  x ∈? (y ∷ ys) with x ≟ y
  ... | just e = just (here e)
  ... | nothing  = map there (x ∈? ys)

  -- The cycles of the shapes the value is built from: left-linear
  -- `b · v ≾ v` and right-linear `v · c ≾ v`, `b` and `c` free of the
  -- unknown, and quadratic `v · v ≾ v`; a cycle of any other shape is
  -- left to `Closes`

  record Shapes (cs : List X) : Set where
    constructor shapes
    field
      lefts  : List X
      rights : List X
      quad   : Maybe (mul self self ∈ cs)
      leftˢ  : ∀ {b} → b ∈ lefts → mul b self ∈ cs
      rightˢ : ∀ {c} → c ∈ rights → mul self c ∈ cs

  open Shapes public

  shapesOf : (cs : List X) → Shapes cs
  shapesOf []       = shapes [] [] nothing (λ ()) (λ ())
  shapesOf (p ∷ cs) = go (shapesOf cs) (factors p)
    where
      shift : Shapes cs → Shapes (p ∷ cs)
      shift (shapes ls rs q lˢ rˢ) =
        shapes ls rs (map there q) (λ m → there (lˢ m)) (λ m → there (rˢ m))

      byFactors : Shapes cs → (y z : X) → p ≡ mul y z
                → Maybe (y ≡ self) → Maybe (z ≡ self) → Maybe (occ y ≡ false) → Maybe (occ z ≡ false)
                → Shapes (p ∷ cs)
      byFactors (shapes ls rs q lˢ rˢ) y z e (just refl) (just refl) _ _ =
        shapes ls rs (just (here (sym e))) (λ m → there (lˢ m)) (λ m → there (rˢ m))
      byFactors (shapes ls rs q lˢ rˢ) y z e _ (just refl) (just _) _ =
        shapes (y ∷ ls) rs (map there q)
               (λ { (here refl) → here (sym e) ; (there m) → there (lˢ m) }) (λ m → there (rˢ m))
      byFactors (shapes ls rs q lˢ rˢ) y z e (just refl) _ _ (just _) =
        shapes ls (z ∷ rs) (map there q)
               (λ m → there (lˢ m)) (λ { (here refl) → here (sym e) ; (there m) → there (rˢ m) })
      byFactors sh y z e _ _ _ _ = shift sh

      go : Shapes cs → Maybe (Σ[ y ∈ X ] Σ[ z ∈ X ] (p ≡ mul y z)) → Shapes (p ∷ cs)
      go sh nothing            = shift sh
      go sh (just (y , z , e)) =
        byFactors sh y z e (y ≟ self) (z ≟ self) (isFalse (occ y)) (isFalse (occ z))

  -- The closure `x⁺` of an expression: `x` where it absorbs its own
  -- iteration, decided; else the closure of its value, where the hints
  -- declare it

  data Clo (x : X) : X → Set where
    idem  : mul x x ≤ x → Clo x x
    const : ∀ {x⁺} → Closure x x⁺ → Clo x x⁺

  clo? : (x : X) → Maybe (Σ[ x⁺ ∈ X ] Clo x x⁺)
  clo? x with dec≤ (mul x x) x
  ... | just p  = just (x , idem p)
  ... | nothing = map (λ (x⁺ , c) → x⁺ , const c) (closure? x)

  -- `B* · y`, `B` the join of the left multipliers `bs`: `y` where each
  -- multiplier leaves it, decided; else `y ⊔ B⁺ · y`. Its mirror
  -- `y · C*`.

  data StarL (bs : List X) (y : X) : X → Set where
    stays : (∀ {b} → b ∈ bs → mul b y ≤ y) → StarL bs y y
    grows : ∀ {b₀ bs' B⁺} → bs ≡ b₀ ∷ bs' → Clo (joins join b₀ bs') B⁺
          → StarL bs y (join y (mul B⁺ y))

  data StarR (cs : List X) (y : X) : X → Set where
    stays : (∀ {c} → c ∈ cs → mul y c ≤ y) → StarR cs y y
    grows : ∀ {c₀ cs' C⁺} → cs ≡ c₀ ∷ cs' → Clo (joins join c₀ cs') C⁺
          → StarR cs y (join y (mul y C⁺))

  starL? : (bs : List X) → (y : X) → Maybe (Σ[ z ∈ X ] StarL bs y z)
  starL? bs y with every (λ b → dec≤ (mul b y) y) bs
  ... | just st = just (y , stays st)
  ... | nothing = at bs refl
    where
      at : (bs' : List X) → bs ≡ bs' → Maybe (Σ[ z ∈ X ] StarL bs y z)
      at []         e = nothing
      at (b₀ ∷ bs') e = map (λ (B⁺ , c) → join y (mul B⁺ y) , grows e c) (clo? (joins join b₀ bs'))

  starR? : (cs : List X) → (y : X) → Maybe (Σ[ z ∈ X ] StarR cs y z)
  starR? cs y with every (λ c → dec≤ (mul y c) y) cs
  ... | just st = just (y , stays st)
  ... | nothing = at cs refl
    where
      at : (cs' : List X) → cs ≡ cs' → Maybe (Σ[ z ∈ X ] StarR cs y z)
      at []         e = nothing
      at (c₀ ∷ cs') e = map (λ (C⁺ , c) → join y (mul y C⁺) , grows e c) (clo? (joins join c₀ cs'))

  -- The closure, where there is a quadratic cycle

  data Sq {cs : List X} (sh : Shapes cs) (x : X) : X → Set where
    linear    : quad sh ≡ nothing → Sq sh x x
    quadratic : ∀ {m x⁺} → quad sh ≡ just m → Clo x x⁺ → Sq sh x x⁺

  sq? : ∀ {cs} → (sh : Shapes cs) → (x : X) → Maybe (Σ[ x⁺ ∈ X ] Sq sh x x⁺)
  sq? sh x = go (quad sh) refl
    where
      go : (q : Maybe _) → quad sh ≡ q → Maybe (Σ[ x⁺ ∈ X ] Sq sh x x⁺)
      go nothing  e = just (x , linear e)
      go (just m) e = map (λ (x⁺ , c) → x⁺ , quadratic e c) (clo? x)

  -- The value of lowering from `L`, the join of the bounds or the unit:
  -- `V = B* · L · C*`, and `V = (B* · L · C*)⁺` where there is a
  -- quadratic cycle, where every cycle closes at `V`. Every solution of
  -- `L ≾ v` and the cycles of the three shapes lies above `V`.

  record LowTo (l : List (X × X)) (lw : Lows l) (L V : X) : Set where
    constructor lowTo
    field
      sh  : Shapes (cycs lw)
      y z : X
      stL : StarL (lefts sh) L y
      stR : StarR (rights sh) y z
      sq  : Sq sh z V
      cl  : Closes l lw V

  lowTo? : (l : List (X × X)) → (lw : Lows l) → (L : X) → Maybe (Σ[ V ∈ X ] LowTo l lw L V)
  lowTo? l lw L with shapesOf (cycs lw)
  ... | sh with starL? (lefts sh) L
  ...   | nothing         = nothing
  ...   | just (y , stL) with starR? (rights sh) y
  ...     | nothing         = nothing
  ...     | just (z , stR) with sq? sh z
  ...       | nothing        = nothing
  ...       | just (V , sq') = map (λ (cl : Closes l lw V) → V , lowTo sh y z stL stR sq' cl) (closes? l lw V)

  -- The value closes every cycle

  lowTo-closes : ∀ {l lw L V} → LowTo l lw L V → Closes l lw V
  lowTo-closes = LowTo.cl

  ----------------------------------------------------------------------
  -- Raising: a bound above, `U`. Every ordering with the unknown on its
  -- left is `v ≾ U`, or has a right side decided above `U`, or is
  -- valid; every other has it on no left side, or is reflexive

  record Capped (U : X) (l : List (X × X)) : Set where
    constructor capped
    field
      restᵘ  : List (X × X)
      clsᵘ   : ∀ {x x'} → (x , x') ∈ l
             → ((x ≡ self) × ((x' ≡ U) ⊎ (U ≤ x'))) ⊎ ((x , x') ∈ restᵘ)
      rest⊆ᵘ : ∀ {a} → a ∈ restᵘ → a ∈ l
      restL  : ∀ {a} → a ∈ restᵘ → FreeL a

  open Capped public

  record Ups (l : List (X × X)) : Set where
    constructor ups
    field
      cap  : X
      capF : occ cap ≡ false
      srcᵘ : (self , cap) ∈ l
      capd : Capped cap l

  open Ups public

  -- The upper bounds free of the unknown, each a candidate

  capsOf : (l : List (X × X)) → List (Σ[ U ∈ X ] ((occ U ≡ false) × ((self , U) ∈ l)))
  capsOf []             = []
  capsOf ((x , x') ∷ l) = go (x ≟ self) (isFalse (occ x')) (capsOf l)
    where
      shift : List (Σ[ U ∈ X ] ((occ U ≡ false) × ((self , U) ∈ l)))
            → List (Σ[ U ∈ X ] ((occ U ≡ false) × ((self , U) ∈ (x , x') ∷ l)))
      shift []                 = []
      shift ((U , q , m) ∷ us) = (U , q , there m) ∷ shift us

      go : Maybe (x ≡ self) → Maybe (occ x' ≡ false)
         → List (Σ[ U ∈ X ] ((occ U ≡ false) × ((self , U) ∈ l)))
         → List (Σ[ U ∈ X ] ((occ U ≡ false) × ((self , U) ∈ (x , x') ∷ l)))
      go (just e) (just q) us = (x' , q , here (cong (_, x') (sym e))) ∷ shift us
      go _       _        us = shift us

  upsAt : (U : X) → (l : List (X × X)) → Maybe (Capped U l)
  upsAt U []             = just (capped [] (λ ()) (λ ()) (λ ()))
  upsAt U ((x , x') ∷ l) = go (upsAt U l) (same x x') (isFalse (occ x))
    where
      same : (y y' : X) → Maybe (y ≤ y')
      same y y' with y ≅? y'
      ... | yes e = just (≅⇒≤ e)
      ... | no _  = nothing

      above : x ≡ self → Maybe ((x ≡ self) × ((x' ≡ U) ⊎ (U ≤ x')))
      above e with same U x'
      ... | just p  = just (e , inj₂ p)
      ... | nothing = map (λ p → e , inj₂ p) (dec≤ U x')

      capOf : Maybe (x ≡ self) → Maybe ((x ≡ self) × ((x' ≡ U) ⊎ (U ≤ x')))
      capOf (just e) = above e
      capOf nothing  = nothing

      toRest : Capped U l → FreeL (x , x') → Capped U ((x , x') ∷ l)
      toRest (capped r c sb f) fl =
        capped ((x , x') ∷ r)
               (λ { (here refl) → inj₂ (here refl)
                  ; (there m)   → [ inj₁ , (λ m' → inj₂ (there m')) ]′ (c m) })
               (λ { (here refl) → here refl ; (there m) → there (sb m) })
               (λ { (here refl) → fl ; (there m) → f m })

      toCap : Capped U l → (x ≡ self) × ((x' ≡ U) ⊎ (U ≤ x')) → Capped U ((x , x') ∷ l)
      toCap (capped r c sb f) u =
        capped r (λ { (here refl) → inj₁ u
                    ; (there m)   → [ inj₁ , (λ m' → inj₂ m') ]′ (c m) })
               (λ m → there (sb m)) f

      orValid : Capped U l → Maybe ((x ≡ self) × ((x' ≡ U) ⊎ (U ≤ x'))) → Maybe (x ≤ x')
              → Maybe (Capped U ((x , x') ∷ l))
      orValid c (just u) _        = just (toCap c u)
      orValid c nothing  (just p) = just (toRest c (inj₁ (inj₂ p)))
      orValid c nothing  nothing  = nothing

      go : Maybe (Capped U l) → Maybe (x ≤ x') → Maybe (occ x ≡ false)
         → Maybe (Capped U ((x , x') ∷ l))
      go nothing  _       _        = nothing
      go (just c) (just e) _        = just (toRest c (inj₁ (inj₂ e)))
      go (just c) nothing  (just q) = just (toRest c (inj₂ q))
      go (just c) nothing  nothing  = orValid c (capOf (x ≟ self)) (dec≤ x x')

  -- The first candidate that caps the others

  upsOf : (l : List (X × X)) → Maybe (Ups l)
  upsOf l = go (capsOf l)
    where
      go : List (Σ[ U ∈ X ] ((occ U ≡ false) × ((self , U) ∈ l))) → Maybe (Ups l)
      go []                 = nothing
      go ((U , q , m) ∷ us) with upsAt U l
      ... | just c  = just (ups U q m c)
      ... | nothing = go us

  ----------------------------------------------------------------------
  -- The forced unit: `x ≾ y`, `x` canonically the unknown and `y`
  -- decided below the unit, the unit being least

  Forces : X × X → Set
  Forces (x , y) = Least × (canon x ≡ self) × (y ≤ unit)

  forces? : (a : X × X) → Maybe (Forces a)
  forces? (x , y) with least? | canon x ≟ self
  ... | just lst | just e = map (λ p → lst , e , p) (dec≤ y unit)
  ... | _        | _     = nothing

  ----------------------------------------------------------------------
  -- Equating: the expressions an ordering sets against the unknown, the
  -- first fit one that a test places above and below it

  facing : List (X × X) → List X
  facing []             = []
  facing ((x , x') ∷ l) with x ≟ self | x' ≟ self
  ... | just _ | _     = x' ∷ facing l
  ... | nothing | just _ = x ∷ facing l
  ... | nothing | nothing = facing l

  equate : {Ent : X → X → Set} → ((x y : X) → Maybe (Ent x y)) → List (X × X)
         → Maybe (Σ[ b ∈ X ] (Ent self b × Ent b self))
  equate {Ent} ent l = go (facing l)
    where
      go : List X → Maybe (Σ[ b ∈ X ] (Ent self b × Ent b self))
      go []       = nothing
      go (b ∷ bs) with fit b | ent self b | ent b self
      ... | true | just p | just q = just (b , p , q)
      ... | _    | _      | _      = go bs

  ----------------------------------------------------------------------
  -- The rules over an oracle

  record Oracle : Set₁ where
    field
      Lower  : X → Set              -- the unknown may decrease to the value
      lower? : (b : X) → Maybe (Lower b)
      Raise  : X → Set              -- the unknown may increase to the value
      raise? : (b : X) → Maybe (Raise b)

  open Oracle

  -- Lowering, principal

  record ByLower (o : Oracle) (l : List (X × X)) : Set where
    constructor byLower
    field
      lw  : Lows l
      lo  : X
      los : List X
      lbs : bnds lw ≡ lo ∷ los
      val : X
      to  : LowTo l lw (joins join lo los) val
      may : Lower o val

  lower : (o : Oracle) → (l : List (X × X)) → Maybe (ByLower o l)
  lower o l = go (lowsOf l)
    where
      at : (lw : Lows l) → (bs : List X) → bnds lw ≡ bs → Maybe (ByLower o l)
      at lw []       e = nothing
      at lw (x ∷ xs) e with lowTo? l lw (joins join x xs)
      ... | just (b , to) = map (byLower lw x xs e b to) (lower? o b)
      ... | nothing       = nothing

      go : Maybe (Lows l) → Maybe (ByLower o l)
      go (just lw) = at lw (bnds lw) refl
      go nothing   = nothing

  -- Raising, instance-keeping

  record ByRaise (o : Oracle) (l : List (X × X)) : Set where
    constructor byRaise
    field
      up  : Ups l
      may : Raise o (cap up)

  raise : (o : Oracle) → (l : List (X × X)) → Maybe (ByRaise o l)
  raise o l = go (upsOf l)
    where
      go : Maybe (Ups l) → Maybe (ByRaise o l)
      go (just up) = map (byRaise up) (raise? o (cap up))
      go nothing   = nothing

  -- The least element, principal

  record ByLeast (o : Oracle) (l : List (X × X)) : Set where
    constructor byLeast
    field
      lw  : Lows l
      nob : bnds lw ≡ []
      lst : Least
      val : X
      to  : LowTo l lw unit val
      may : Lower o val

  least : (o : Oracle) → (l : List (X × X)) → Maybe (ByLeast o l)
  least o l = go least? (lowsOf l)
    where
      at : Least → (lw : Lows l) → (bs : List X) → bnds lw ≡ bs → Maybe (ByLeast o l)
      at lst lw []      e with lowTo? l lw unit
      ... | just (b , to) = map (byLeast lw e lst b to) (lower? o b)
      ... | nothing       = nothing
      at lst lw (_ ∷ _) e = nothing

      go : Maybe Least → Maybe (Lows l) → Maybe (ByLeast o l)
      go (just lst) (just lw) = at lst lw (bnds lw) refl
      go _          _         = nothing

  -- The top, instance-keeping: every ordering is valid, has the unknown
  -- on no left side, or has it as its whole right side

  UnderTop : X × X → Set
  UnderTop (x , x') = FreeL (x , x') ⊎ (x' ≡ self)

  underTop? : (a : X × X) → Maybe (UnderTop a)
  underTop? (x , x') with freeL? (x , x')
  ... | just f  = just (inj₁ f)
  ... | nothing with x' ≟ self
  ...   | just e = just (inj₂ e)
  ...   | nothing  = nothing

  record ByTop (o : Oracle) (l : List (X × X)) : Set where
    constructor byTop
    field
      fl  : ∀ {a} → a ∈ l → UnderTop a
      may : Raise o top

  topOf : (o : Oracle) → (l : List (X × X)) → Maybe (ByTop o l)
  topOf o l with every underTop? l
  ... | just fl = map (byTop fl) (raise? o top)
  ... | nothing = nothing

  ----------------------------------------------------------------------
  -- The rules keep the orderings: read before (`f₀`) and after (`f₁`)
  -- an assignment, the two agreeing where the unknown does not occur,
  -- and the decided order kept after it

  module Keep {Y : Set} (_⊑_ : Y → Y → Set)
              (⊑-refl : ∀ {y} → y ⊑ y) (⊑-trans : ∀ {y y' y''} → y ⊑ y' → y' ⊑ y'' → y ⊑ y'')
              (f₀ f₁ : X → Y) (same : ∀ {x} → occ x ≡ false → f₁ x ≡ f₀ x)
              (dec : ∀ {y y'} → y ≤ y' → f₁ y ⊑ f₁ y') where

    Holds : (X → Y) → List (X × X) → Set
    Holds f l = ∀ {x x'} → (x , x') ∈ l → f x ⊑ f x'

    valid-holds : ∀ {x x'} → Valid (x , x') → f₁ x ⊑ f₁ x'
    valid-holds (inj₁ refl) = ⊑-refl
    valid-holds (inj₂ p)    = dec p

    -- Lowering keeps an ordering with the unknown on no right side,
    -- raising one with it on no left side

    lowerR : ∀ {x x'} → FreeR (x , x') → (∀ y → f₁ y ⊑ f₀ y) → f₀ x ⊑ f₀ x' → f₁ x ⊑ f₁ x'
    lowerR (inj₁ v) lo h = valid-holds v
    lowerR {x} (inj₂ q) lo h = ⊑-trans (lo x) (subst (f₀ x ⊑_) (sym (same q)) h)

    raiseL : ∀ {x x'} → FreeL (x , x') → (∀ y → f₀ y ⊑ f₁ y) → f₀ x ⊑ f₀ x' → f₁ x ⊑ f₁ x'
    raiseL (inj₁ v) hi h = valid-holds v
    raiseL {x' = x'} (inj₂ q) hi h = ⊑-trans (subst (_⊑ f₀ x') (sym (same q)) h) (hi x')

    lower-free : ∀ {l} → (∀ {a} → a ∈ l → FreeR a) → (∀ y → f₁ y ⊑ f₀ y)
               → Holds f₀ l → Holds f₁ l
    lower-free fr lo h m = lowerR (fr m) lo (h m)

    raise-free : ∀ {l} → (∀ {a} → a ∈ l → FreeL a) → (∀ y → f₀ y ⊑ f₁ y)
               → Holds f₀ l → Holds f₁ l
    raise-free fl hi h m = raiseL (fl m) hi (h m)

    -- Lowering to a value above every bound (the join, or the least
    -- element where there is none)

    -- the cycles holding at the value

    lower-keeps : ∀ {l} → (lw : Lows l) → (∀ y → f₁ y ⊑ f₀ y)
                → (∀ {x} → x ∈ bnds lw → f₀ x ⊑ f₁ self)
                → (∀ {x} → x ∈ cycs lw → f₁ x ⊑ f₁ self) → Holds f₀ l → Holds f₁ l
    lower-keeps lw lo ub cy h m with cls lw m
    ... | inj₁ (refl , mb)        = ⊑-trans (lo _) (ub mb)
    ... | inj₂ (inj₁ (refl , mc)) = cy mc
    ... | inj₂ (inj₂ mr)          = lowerR (restR lw mr) lo (h m)

    -- ... and makes each ordering with the unknown on its greater side
    -- hold outright: it is a bound, below the value, a cycle, or valid

    lower-drops : ∀ {l} → (lw : Lows l) → (∀ {x} → x ∈ bnds lw → f₀ x ⊑ f₁ self)
                → (∀ {x} → x ∈ cycs lw → f₁ x ⊑ f₁ self)
                → ∀ {x x'} → (x , x') ∈ l → occ x' ≡ true → f₁ x ⊑ f₁ x'
    lower-drops lw ub cy m q with cls lw m
    ... | inj₁ (refl , mb)        = subst (_⊑ f₁ self) (sym (same (bndF lw mb))) (ub mb)
    ... | inj₂ (inj₁ (refl , mc)) = cy mc
    ... | inj₂ (inj₂ mr) with restR lw mr
    ...   | inj₁ v  = valid-holds v
    ...   | inj₂ q' = ⊥-elim (true≢false (trans (sym q) q'))

    -- Raising to the top, where every side lies below the top
    -- (`f₁ self`)

    top-keeps : ∀ {l} → (∀ {a} → a ∈ l → UnderTop a) → (∀ y → f₀ y ⊑ f₁ y)
              → (∀ y → f₁ y ⊑ f₁ self) → Holds f₀ l → Holds f₁ l
    top-keeps ut hi tp h {x} m with ut m
    ... | inj₁ fl   = raiseL fl hi (h m)
    ... | inj₂ refl = tp x

    -- Raising to the upper bound

    raise-keeps : ∀ {l} → (up : Ups l) → (∀ y → f₀ y ⊑ f₁ y) → f₁ self ⊑ f₁ (cap up)
                → Holds f₀ l → Holds f₁ l
    raise-keeps up hi hit h m with clsᵘ (capd up) m
    ... | inj₁ (refl , inj₁ refl) = hit
    ... | inj₁ (refl , inj₂ p)    = ⊑-trans hit (dec p)
    ... | inj₂ mr                 = raiseL (restL (capd up) mr) hi (h m)

------------------------------------------------------------------------
-- The sorts of grade expressions

-- The expressions fit to replace an unknown: an unknown of smaller
-- index, or one free of it

fitₑ : ∀ {Θ} → EVar Θ → EExp Θ → 𝔹
fitₑ i (evar j) = toℕ j <ᵇ toℕ i
fitₑ i ε        = not (occᵉ-e i ε)

fitᵣ : ∀ {Θ} → RVar Θ → RExp Θ → 𝔹
fitᵣ i (rvar j) = toℕ j <ᵇ toℕ i
fitᵣ i ρ        = not (occʳ-r i ρ)

-- Through the image, the unit is least where both units are and the
-- projection reflects the order at the unit: `∣ e ∣ ≾ u` then sends `e`
-- to the effect unit, whose image lies below every resource grade

Reflects : Set
Reflects = (e : E) → mapᵉ e ≾ᵣ uᵣ → e ≾ₑ uₑ

LeastImage : Set
LeastImage = Is-just uₑ-least? × Reflects × Is-just uᵣ-least?

leastImage? : Maybe LeastImage
leastImage? with Is-just? uₑ-least? | reflects-u? | Is-just? uᵣ-least?
... | just a | just r | just c = just (a , r , c)
... | _      | _      | _      = nothing

-- The value of a variable-free expression, convertible to it

evalₑ : ∀ {Ψ} → (ε : EExp Ψ) → Maybe (Σ[ c ∈ E ] (ε ≡̂ₑ econst c))
evalₑ (evar _)   = nothing
evalₑ (econst c) = just (c , ≡̂ₑ-refl)
evalₑ (a ·̂ₑ b) with evalₑ a | evalₑ b
... | just (c , p) | just (d , q) = just (c ·ₑ d , ≡̂ₑ-trans (≡̂ₑ-cong p q) ≡̂ₑ-const-·)
... | _            | _            = nothing
evalₑ (a ⊔̂ₑ b) with evalₑ a | evalₑ b
... | just (c , p) | just (d , q) = just (c ⊔ₑ d , ≡̂ₑ-trans (≡̂ₑ-cong-⊔ p q) ≡̂ₑ-const-⊔)
... | _            | _            = nothing

evalᵣ : ∀ {Ψ} → (ρ : RExp Ψ) → Maybe (Σ[ c ∈ R ] (ρ ≡̂ᵣ rconst c))
evalᵣ (rvar _)   = nothing
evalᵣ (rconst c) = just (c , ≡̂ᵣ-refl)
evalᵣ (a ·̂ᵣ b) with evalᵣ a | evalᵣ b
... | just (c , p) | just (d , q) = just (c ·ᵣ d , ≡̂ᵣ-trans (≡̂ᵣ-cong p q) ≡̂ᵣ-const-·)
... | _            | _            = nothing
evalᵣ (a ⊔̂ᵣ b) with evalᵣ a | evalᵣ b
... | just (c , p) | just (d , q) = just (c ⊔ᵣ d , ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ p q) ≡̂ᵣ-const-⊔)
... | _            | _            = nothing
evalᵣ ∣ ε ∣̂ᵉ with evalₑ ε
... | just (c , p) = just (mapᵉ c , ≡̂ᵣ-trans (≡̂ᵣ-map-cong p) ≡̂ᵣ-map-const)
... | nothing      = nothing

-- The closure of an expression: that of its value, where the hints
-- declare it

Closureₑ : ∀ {Ψ} → EExp Ψ → EExp Ψ → Set
Closureₑ L L⁺ = Σ[ c ∈ E ] Σ[ p ∈ Plus _·ₑ_ _≾ₑ_ c ] ((L ≡̂ₑ econst c) × (L⁺ ≡ econst (Plus.c⁺ p)))

closureₑ? : ∀ {Ψ} → (L : EExp Ψ) → Maybe (Σ[ L⁺ ∈ EExp Ψ ] Closureₑ L L⁺)
closureₑ? L with evalₑ L
... | nothing       = nothing
... | just (c , eq) with plusₑ? c
...   | nothing = nothing
...   | just p  = just (econst (Plus.c⁺ p) , c , p , eq , refl)

Closureᵣ : ∀ {Ψ} → RExp Ψ → RExp Ψ → Set
Closureᵣ L L⁺ = Σ[ c ∈ R ] Σ[ p ∈ Plus _·ᵣ_ _≾ᵣ_ c ] ((L ≡̂ᵣ rconst c) × (L⁺ ≡ rconst (Plus.c⁺ p)))

closureᵣ? : ∀ {Ψ} → (L : RExp Ψ) → Maybe (Σ[ L⁺ ∈ RExp Ψ ] Closureᵣ L L⁺)
closureᵣ? L with evalᵣ L
... | nothing       = nothing
... | just (c , eq) with plusᵣ? c
...   | nothing = nothing
...   | just p  = just (rconst (Plus.c⁺ p) , c , p , eq , refl)

-- The factors of a product

factorsₑ : ∀ {Ψ} → (x : EExp Ψ) → Maybe (Σ[ y ∈ EExp Ψ ] Σ[ z ∈ EExp Ψ ] (x ≡ y ·̂ₑ z))
factorsₑ (y ·̂ₑ z) = just (y , z , refl)
factorsₑ _        = nothing

factorsᵣ : ∀ {Ψ} → (x : RExp Ψ) → Maybe (Σ[ y ∈ RExp Ψ ] Σ[ z ∈ RExp Ψ ] (x ≡ y ·̂ᵣ z))
factorsᵣ (y ·̂ᵣ z) = just (y , z , refl)
factorsᵣ _        = nothing

-- An image `∣ b ∣` as the value of the image of an effect unknown sends
-- the unknown to `b`; any other expression leaves it

putⁱ : ∀ {Ψ} → EVar Ψ → RExp Ψ → RExp Ψ → RExp Ψ
putⁱ k ∣ b ∣̂ᵉ     x = x [ updᵉ k b ]ʳ
putⁱ k (rvar _)   x = x
putⁱ k (rconst _) x = x
putⁱ k (_ ·̂ᵣ _)   x = x
putⁱ k (_ ⊔̂ᵣ _)   x = x

-- Effect expressions for an effect unknown, resource expressions for a
-- resource unknown, and resource expressions for an effect unknown
-- through its image `∣ k ∣`

sortᵉ : ∀ {Ψ} → EVar Ψ → Sort (EExp Ψ)
sortᵉ k = record
  { _≟_ = _≡ᵉ?_ ; _≅_ = _≅ᵉ_ ; _≅?_ = _≟ᵉ_ ; ≅⇒≤ = λ e → eqₑ (≅ᵉ⇒≡̂ e)
  ; occ = occᵉ-e k ; self = evar k
  ; _≤_ = ∅ᴴ ⊩_≾̂ₑ_ ; dec≤ = decideₑ full ∅ᴴ
  ; join = _⊔̂ₑ_ ; unit = ûₑ ; top = econst ⊤ₑ ; canon = canonₑ
  ; Least = Is-just uₑ-least? ; least? = Is-just? uₑ-least? ; fit = fitₑ k
  ; put = λ b x → x [ updᵉ k b ]ᵉ ; mul = _·̂ₑ_ ; factors = factorsₑ
  ; Closure = Closureₑ ; closure? = closureₑ? }

sortʳ : ∀ {Ψ} → RVar Ψ → Sort (RExp Ψ)
sortʳ k = record
  { _≟_ = _≡ʳ?_ ; _≅_ = _≅ʳ_ ; _≅?_ = _≟ʳ_ ; ≅⇒≤ = λ e → eqᵣ (≅ʳ⇒≡̂ e)
  ; occ = occʳ-r k ; self = rvar k
  ; _≤_ = ∅ᴴ ⊩_≾̂ᵣ_ ; dec≤ = decideᵣ full ∅ᴴ
  ; join = _⊔̂ᵣ_ ; unit = ûᵣ ; top = rconst ⊤ᵣ ; canon = canonᵣ
  ; Least = Is-just uᵣ-least? ; least? = Is-just? uᵣ-least? ; fit = fitᵣ k
  ; put = λ b x → x [ updʳ k b ]ʳ ; mul = _·̂ᵣ_ ; factors = factorsᵣ
  ; Closure = Closureᵣ ; closure? = closureᵣ? }

imageᵉ : ∀ {Ψ} → EVar Ψ → Sort (RExp Ψ)
imageᵉ k = record
  { _≟_ = _≡ʳ?_ ; _≅_ = _≅ʳ_ ; _≅?_ = _≟ʳ_ ; ≅⇒≤ = λ e → eqᵣ (≅ʳ⇒≡̂ e)
  ; occ = occᵉ-r k ; self = ∣ evar k ∣̂ᵉ
  ; _≤_ = ∅ᴴ ⊩_≾̂ᵣ_ ; dec≤ = decideᵣ full ∅ᴴ
  ; join = _⊔̂ᵣ_ ; unit = ûᵣ ; top = rconst ⊤ᵣ ; canon = canonᵣ
  ; Least = LeastImage ; least? = leastImage? ; fit = λ _ → false ; put = putⁱ k
  ; mul = _·̂ᵣ_ ; factors = factorsᵣ ; Closure = λ _ _ → ⊥ ; closure? = λ _ → nothing }

module Vᵉ {Ψ} (k : EVar Ψ) = Rules {EExp Ψ} (sortᵉ k)
module Vʳ {Ψ} (k : RVar Ψ) = Rules {RExp Ψ} (sortʳ k)
module Vⁱ {Ψ} (k : EVar Ψ) = Rules {RExp Ψ} (imageᵉ k)

------------------------------------------------------------------------
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

------------------------------------------------------------------------
-- The join of the lower bounds, with its least-upper-bound property

joinₑ : ∀ {Θ} → EExp Θ → List (EExp Θ) → EExp Θ
joinₑ = joins _⊔̂ₑ_

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
joinᵣ = joins _⊔̂ᵣ_

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

------------------------------------------------------------------------
-- The value of lowering lies above `L` and, wherever `L` lies below the
-- unknown and the orderings hold, below the unknown, by one argument
-- for every shape: each left multiplier `b` gives `b · v ≾ v`, so
-- their join `B` does (distributivity), so `B⁺ · v ≾ v` (`indˡ`), and
-- `B* · L ≾ v` by monotonicity; the mirror for `C*`; and, `v · v ≾ v`
-- holding as well, the closure lies below `v` (`plus`). An expression
-- absorbing its own iteration is its own closure, and a star that
-- leaves its argument is the argument.

-- the join of left (right) multipliers leaves what each leaves

joinₑ-mulˡ⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {w : EExp Ψ'} → (τ : Subst Ψ Ψ')
            → (x₀ : EExp Ψ) → (xs : List (EExp Ψ))
            → (∀ {x} → x ∈ x₀ ∷ xs → Q ⊩ x [ τ ]ᵉ ·̂ₑ w ≾̂ₑ w)
            → Q ⊩ joinₑ x₀ xs [ τ ]ᵉ ·̂ₑ w ≾̂ₑ w
joinₑ-mulˡ⊩ τ x₀ []        k = k (here refl)
joinₑ-mulˡ⊩ τ x₀ (x₁ ∷ xs) k =
  joinₑ-mulˡ⊩ τ (x₀ ⊔̂ₑ x₁) xs
    (λ { (here refl) → transₑ (eqₑ ≡̂ₑ-distribʳ-⊔) (⊔-lubₑ (k (here refl)) (k (there (here refl))))
       ; (there m)   → k (there (there m)) })

joinₑ-mulʳ⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {w : EExp Ψ'} → (τ : Subst Ψ Ψ')
            → (x₀ : EExp Ψ) → (xs : List (EExp Ψ))
            → (∀ {x} → x ∈ x₀ ∷ xs → Q ⊩ w ·̂ₑ x [ τ ]ᵉ ≾̂ₑ w)
            → Q ⊩ w ·̂ₑ joinₑ x₀ xs [ τ ]ᵉ ≾̂ₑ w
joinₑ-mulʳ⊩ τ x₀ []        k = k (here refl)
joinₑ-mulʳ⊩ τ x₀ (x₁ ∷ xs) k =
  joinₑ-mulʳ⊩ τ (x₀ ⊔̂ₑ x₁) xs
    (λ { (here refl) → transₑ (eqₑ ≡̂ₑ-distribˡ-⊔) (⊔-lubₑ (k (here refl)) (k (there (here refl))))
       ; (there m)   → k (there (there m)) })

joinᵣ-mulˡ⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {w : RExp Ψ'} → (τ : Subst Ψ Ψ')
            → (x₀ : RExp Ψ) → (xs : List (RExp Ψ))
            → (∀ {x} → x ∈ x₀ ∷ xs → Q ⊩ x [ τ ]ʳ ·̂ᵣ w ≾̂ᵣ w)
            → Q ⊩ joinᵣ x₀ xs [ τ ]ʳ ·̂ᵣ w ≾̂ᵣ w
joinᵣ-mulˡ⊩ τ x₀ []        k = k (here refl)
joinᵣ-mulˡ⊩ τ x₀ (x₁ ∷ xs) k =
  joinᵣ-mulˡ⊩ τ (x₀ ⊔̂ᵣ x₁) xs
    (λ { (here refl) → transᵣ (eqᵣ ≡̂ᵣ-distribʳ-⊔) (⊔-lubᵣ (k (here refl)) (k (there (here refl))))
       ; (there m)   → k (there (there m)) })

joinᵣ-mulʳ⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {w : RExp Ψ'} → (τ : Subst Ψ Ψ')
            → (x₀ : RExp Ψ) → (xs : List (RExp Ψ))
            → (∀ {x} → x ∈ x₀ ∷ xs → Q ⊩ w ·̂ᵣ x [ τ ]ʳ ≾̂ᵣ w)
            → Q ⊩ w ·̂ᵣ joinᵣ x₀ xs [ τ ]ʳ ≾̂ᵣ w
joinᵣ-mulʳ⊩ τ x₀ []        k = k (here refl)
joinᵣ-mulʳ⊩ τ x₀ (x₁ ∷ xs) k =
  joinᵣ-mulʳ⊩ τ (x₀ ⊔̂ᵣ x₁) xs
    (λ { (here refl) → transᵣ (eqᵣ ≡̂ᵣ-distribˡ-⊔) (⊔-lubᵣ (k (here refl)) (k (there (here refl))))
       ; (there m)   → k (there (there m)) })

module LowToₑ {Ψ} (k : EVar Ψ) {l : List (EExp Ψ × EExp Ψ)} (lw : Vᵉ.Lows {Ψ} k l) where

  -- the closure of an expression lies above it, below every grade above
  -- it absorbing its own iteration, and leaves what the expression leaves

  clo-above : ∀ {x x⁺} → Vᵉ.Clo {Ψ} k x x⁺ → ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
            → Q ⊩ x [ δ ]ᵉ ≾̂ₑ x⁺ [ δ ]ᵉ
  clo-above (Vᵉ.idem _)                    δ = ⊩≾̂ₑ-refl
  clo-above (Vᵉ.const (c , p , eq , refl)) δ =
    transₑ (eqₑ (≡̂ₑ-subst δ eq)) (atomₑ (Plus.≾-c⁺ p))

  clo-least : ∀ {x x⁺} → Vᵉ.Clo {Ψ} k x x⁺ → ∀ {Ψ'} {Q : Hyps Ψ'} {w} → (τ : Subst Ψ Ψ')
            → Q ⊩ x [ τ ]ᵉ ≾̂ₑ w → Q ⊩ w ·̂ₑ w ≾̂ₑ w → Q ⊩ x⁺ [ τ ]ᵉ ≾̂ₑ w
  clo-least (Vᵉ.idem _)                    τ h _  = h
  clo-least (Vᵉ.const (c , p , eq , refl)) τ h sq =
    plusₑ p (transₑ (eqₑ (≡̂ₑ-sym (≡̂ₑ-subst τ eq))) h) sq

  clo-indˡ : ∀ {x x⁺} → Vᵉ.Clo {Ψ} k x x⁺ → ∀ {Ψ'} {Q : Hyps Ψ'} {w} → (τ : Subst Ψ Ψ')
           → Q ⊩ x [ τ ]ᵉ ·̂ₑ w ≾̂ₑ w → Q ⊩ x⁺ [ τ ]ᵉ ·̂ₑ w ≾̂ₑ w
  clo-indˡ (Vᵉ.idem _)                    τ h = h
  clo-indˡ (Vᵉ.const (c , p , eq , refl)) τ h =
    indˡₑ p (transₑ (eqₑ (≡̂ₑ-cong (≡̂ₑ-sym (≡̂ₑ-subst τ eq)) ≡̂ₑ-refl)) h)

  clo-indʳ : ∀ {x x⁺} → Vᵉ.Clo {Ψ} k x x⁺ → ∀ {Ψ'} {Q : Hyps Ψ'} {w} → (τ : Subst Ψ Ψ')
           → Q ⊩ w ·̂ₑ x [ τ ]ᵉ ≾̂ₑ w → Q ⊩ w ·̂ₑ x⁺ [ τ ]ᵉ ≾̂ₑ w
  clo-indʳ (Vᵉ.idem _)                    τ h = h
  clo-indʳ (Vᵉ.const (c , p , eq , refl)) τ h =
    indʳₑ p (transₑ (eqₑ (≡̂ₑ-cong ≡̂ₑ-refl (≡̂ₑ-sym (≡̂ₑ-subst τ eq)))) h)

  -- the value lies above `L`

  grows : ∀ {L V} → Vᵉ.LowTo {Ψ} k l lw L V → ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
        → Q ⊩ L [ δ ]ᵉ ≾̂ₑ V [ δ ]ᵉ
  grows (Vᵉ.lowTo sh y z stL stR sq _) {Q = Q} δ = transₑ (starL stL) (transₑ (starR stR) (sqr sq))
    where
      starL : ∀ {bs L y} → Vᵉ.StarL {Ψ} k bs L y → Q ⊩ L [ δ ]ᵉ ≾̂ₑ y [ δ ]ᵉ
      starL (Vᵉ.stays _)   = ⊩≾̂ₑ-refl
      starL (Vᵉ.grows _ _) = ⊔-ubˡₑ

      starR : ∀ {cs y z} → Vᵉ.StarR {Ψ} k cs y z → Q ⊩ y [ δ ]ᵉ ≾̂ₑ z [ δ ]ᵉ
      starR (Vᵉ.stays _)   = ⊩≾̂ₑ-refl
      starR (Vᵉ.grows _ _) = ⊔-ubˡₑ

      sqr : ∀ {cs} {sh : Vᵉ.Shapes {Ψ} k cs} {z V} → Vᵉ.Sq {Ψ} k sh z V
          → Q ⊩ z [ δ ]ᵉ ≾̂ₑ V [ δ ]ᵉ
      sqr (Vᵉ.linear _)      = ⊩≾̂ₑ-refl
      sqr (Vᵉ.quadratic _ c) = clo-above c δ

  -- ... and below the unknown, wherever `L` does and the orderings hold

  least : ∀ {L V} → Vᵉ.LowTo {Ψ} k l lw L V → ∀ {Ψ'} {Q : Hyps Ψ'} → (τ : Subst Ψ Ψ')
        → Q ⊩ L [ τ ]ᵉ ≾̂ₑ sE τ k
        → (∀ {a a'} → (a , a') ∈ l → Q ⊩ a [ τ ]ᵉ ≾̂ₑ a' [ τ ]ᵉ)
        → Q ⊩ V [ τ ]ᵉ ≾̂ₑ sE τ k
  least (Vᵉ.lowTo sh y z stL stR sq _) {Q = Q} τ hL h = sqr sq (starR stR (starL stL hL))
    where
      cyc : ∀ {p} → p ∈ Vᵉ.cycs lw → Q ⊩ p [ τ ]ᵉ ≾̂ₑ sE τ k
      cyc m = h (Vᵉ.srcᶜ lw m)

      starL : ∀ {L y} → Vᵉ.StarL {Ψ} k (Vᵉ.lefts sh) L y
            → Q ⊩ L [ τ ]ᵉ ≾̂ₑ sE τ k → Q ⊩ y [ τ ]ᵉ ≾̂ₑ sE τ k
      starL (Vᵉ.stays _)              hy = hy
      starL (Vᵉ.grows {b₀} {bs'} e c) hy =
        ⊔-lubₑ hy (transₑ (monoₑ ⊩≾̂ₑ-refl hy)
                          (clo-indˡ c τ (joinₑ-mulˡ⊩ τ b₀ bs'
                             (λ {x} m → cyc (Vᵉ.leftˢ sh (subst (x ∈_) (sym e) m))))))

      starR : ∀ {y z} → Vᵉ.StarR {Ψ} k (Vᵉ.rights sh) y z
            → Q ⊩ y [ τ ]ᵉ ≾̂ₑ sE τ k → Q ⊩ z [ τ ]ᵉ ≾̂ₑ sE τ k
      starR (Vᵉ.stays _)              hy = hy
      starR (Vᵉ.grows {c₀} {cs'} e c) hy =
        ⊔-lubₑ hy (transₑ (monoₑ hy ⊩≾̂ₑ-refl)
                          (clo-indʳ c τ (joinₑ-mulʳ⊩ τ c₀ cs'
                             (λ {x} m → cyc (Vᵉ.rightˢ sh (subst (x ∈_) (sym e) m))))))

      sqr : ∀ {z V} → Vᵉ.Sq {Ψ} k sh z V → Q ⊩ z [ τ ]ᵉ ≾̂ₑ sE τ k → Q ⊩ V [ τ ]ᵉ ≾̂ₑ sE τ k
      sqr (Vᵉ.linear _)                  hz = hz
      sqr (Vᵉ.quadratic {m = m} _ c) hz = clo-least c τ hz (cyc m)

  -- for lowering from the join of the bounds: the value lies above each
  -- bound, and below the unknown wherever the orderings hold

  module Join {x₀ : EExp Ψ} {xs : List (EExp Ψ)} (e : Vᵉ.bnds lw ≡ x₀ ∷ xs) where

    above : ∀ {b} → Vᵉ.LowTo {Ψ} k l lw (joinₑ x₀ xs) b → ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
          → ∀ {y} → y ∈ Vᵉ.bnds lw → Q ⊩ y [ δ ]ᵉ ≾̂ₑ b [ δ ]ᵉ
    above to δ m = transₑ (joinₑ-ub⊩ δ x₀ xs (subst (_ ∈_) e m)) (grows to δ)

    below : ∀ {b} → Vᵉ.LowTo {Ψ} k l lw (joinₑ x₀ xs) b → ∀ {Ψ'} {Q : Hyps Ψ'} → (τ : Subst Ψ Ψ')
          → (∀ {a a'} → (a , a') ∈ l → Q ⊩ a [ τ ]ᵉ ≾̂ₑ a' [ τ ]ᵉ)
          → Q ⊩ b [ τ ]ᵉ ≾̂ₑ sE τ k
    below to τ h =
      least to τ (joinₑ-lub⊩ τ x₀ xs (λ {y} m → h {y} (Vᵉ.src lw (subst (_ ∈_) (sym e) m)))) h

module LowToᵣ {Ψ} (k : RVar Ψ) {l : List (RExp Ψ × RExp Ψ)} (lw : Vʳ.Lows {Ψ} k l) where

  -- the closure of an expression lies above it, below every grade above
  -- it absorbing its own iteration, and leaves what the expression leaves

  clo-above : ∀ {x x⁺} → Vʳ.Clo {Ψ} k x x⁺ → ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
            → Q ⊩ x [ δ ]ʳ ≾̂ᵣ x⁺ [ δ ]ʳ
  clo-above (Vʳ.idem _)                    δ = ⊩≾̂ᵣ-refl
  clo-above (Vʳ.const (c , p , eq , refl)) δ =
    transᵣ (eqᵣ (≡̂ᵣ-subst δ eq)) (atomᵣ (Plus.≾-c⁺ p))

  clo-least : ∀ {x x⁺} → Vʳ.Clo {Ψ} k x x⁺ → ∀ {Ψ'} {Q : Hyps Ψ'} {w} → (τ : Subst Ψ Ψ')
            → Q ⊩ x [ τ ]ʳ ≾̂ᵣ w → Q ⊩ w ·̂ᵣ w ≾̂ᵣ w → Q ⊩ x⁺ [ τ ]ʳ ≾̂ᵣ w
  clo-least (Vʳ.idem _)                    τ h _  = h
  clo-least (Vʳ.const (c , p , eq , refl)) τ h sq =
    plusᵣ p (transᵣ (eqᵣ (≡̂ᵣ-sym (≡̂ᵣ-subst τ eq))) h) sq

  clo-indˡ : ∀ {x x⁺} → Vʳ.Clo {Ψ} k x x⁺ → ∀ {Ψ'} {Q : Hyps Ψ'} {w} → (τ : Subst Ψ Ψ')
           → Q ⊩ x [ τ ]ʳ ·̂ᵣ w ≾̂ᵣ w → Q ⊩ x⁺ [ τ ]ʳ ·̂ᵣ w ≾̂ᵣ w
  clo-indˡ (Vʳ.idem _)                    τ h = h
  clo-indˡ (Vʳ.const (c , p , eq , refl)) τ h =
    indˡᵣ p (transᵣ (eqᵣ (≡̂ᵣ-cong (≡̂ᵣ-sym (≡̂ᵣ-subst τ eq)) ≡̂ᵣ-refl)) h)

  clo-indʳ : ∀ {x x⁺} → Vʳ.Clo {Ψ} k x x⁺ → ∀ {Ψ'} {Q : Hyps Ψ'} {w} → (τ : Subst Ψ Ψ')
           → Q ⊩ w ·̂ᵣ x [ τ ]ʳ ≾̂ᵣ w → Q ⊩ w ·̂ᵣ x⁺ [ τ ]ʳ ≾̂ᵣ w
  clo-indʳ (Vʳ.idem _)                    τ h = h
  clo-indʳ (Vʳ.const (c , p , eq , refl)) τ h =
    indʳᵣ p (transᵣ (eqᵣ (≡̂ᵣ-cong ≡̂ᵣ-refl (≡̂ᵣ-sym (≡̂ᵣ-subst τ eq)))) h)

  -- the value lies above `L`

  grows : ∀ {L V} → Vʳ.LowTo {Ψ} k l lw L V → ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
        → Q ⊩ L [ δ ]ʳ ≾̂ᵣ V [ δ ]ʳ
  grows (Vʳ.lowTo sh y z stL stR sq _) {Q = Q} δ = transᵣ (starL stL) (transᵣ (starR stR) (sqr sq))
    where
      starL : ∀ {bs L y} → Vʳ.StarL {Ψ} k bs L y → Q ⊩ L [ δ ]ʳ ≾̂ᵣ y [ δ ]ʳ
      starL (Vʳ.stays _)   = ⊩≾̂ᵣ-refl
      starL (Vʳ.grows _ _) = ⊔-ubˡᵣ

      starR : ∀ {cs y z} → Vʳ.StarR {Ψ} k cs y z → Q ⊩ y [ δ ]ʳ ≾̂ᵣ z [ δ ]ʳ
      starR (Vʳ.stays _)   = ⊩≾̂ᵣ-refl
      starR (Vʳ.grows _ _) = ⊔-ubˡᵣ

      sqr : ∀ {cs} {sh : Vʳ.Shapes {Ψ} k cs} {z V} → Vʳ.Sq {Ψ} k sh z V
          → Q ⊩ z [ δ ]ʳ ≾̂ᵣ V [ δ ]ʳ
      sqr (Vʳ.linear _)      = ⊩≾̂ᵣ-refl
      sqr (Vʳ.quadratic _ c) = clo-above c δ

  -- ... and below the unknown, wherever `L` does and the orderings hold

  least : ∀ {L V} → Vʳ.LowTo {Ψ} k l lw L V → ∀ {Ψ'} {Q : Hyps Ψ'} → (τ : Subst Ψ Ψ')
        → Q ⊩ L [ τ ]ʳ ≾̂ᵣ sR τ k
        → (∀ {a a'} → (a , a') ∈ l → Q ⊩ a [ τ ]ʳ ≾̂ᵣ a' [ τ ]ʳ)
        → Q ⊩ V [ τ ]ʳ ≾̂ᵣ sR τ k
  least (Vʳ.lowTo sh y z stL stR sq _) {Q = Q} τ hL h = sqr sq (starR stR (starL stL hL))
    where
      cyc : ∀ {p} → p ∈ Vʳ.cycs lw → Q ⊩ p [ τ ]ʳ ≾̂ᵣ sR τ k
      cyc m = h (Vʳ.srcᶜ lw m)

      starL : ∀ {L y} → Vʳ.StarL {Ψ} k (Vʳ.lefts sh) L y
            → Q ⊩ L [ τ ]ʳ ≾̂ᵣ sR τ k → Q ⊩ y [ τ ]ʳ ≾̂ᵣ sR τ k
      starL (Vʳ.stays _)              hy = hy
      starL (Vʳ.grows {b₀} {bs'} e c) hy =
        ⊔-lubᵣ hy (transᵣ (monoᵣ ⊩≾̂ᵣ-refl hy)
                          (clo-indˡ c τ (joinᵣ-mulˡ⊩ τ b₀ bs'
                             (λ {x} m → cyc (Vʳ.leftˢ sh (subst (x ∈_) (sym e) m))))))

      starR : ∀ {y z} → Vʳ.StarR {Ψ} k (Vʳ.rights sh) y z
            → Q ⊩ y [ τ ]ʳ ≾̂ᵣ sR τ k → Q ⊩ z [ τ ]ʳ ≾̂ᵣ sR τ k
      starR (Vʳ.stays _)              hy = hy
      starR (Vʳ.grows {c₀} {cs'} e c) hy =
        ⊔-lubᵣ hy (transᵣ (monoᵣ hy ⊩≾̂ᵣ-refl)
                          (clo-indʳ c τ (joinᵣ-mulʳ⊩ τ c₀ cs'
                             (λ {x} m → cyc (Vʳ.rightˢ sh (subst (x ∈_) (sym e) m))))))

      sqr : ∀ {z V} → Vʳ.Sq {Ψ} k sh z V → Q ⊩ z [ τ ]ʳ ≾̂ᵣ sR τ k → Q ⊩ V [ τ ]ʳ ≾̂ᵣ sR τ k
      sqr (Vʳ.linear _)                  hz = hz
      sqr (Vʳ.quadratic {m = m} _ c) hz = clo-least c τ hz (cyc m)

  -- for lowering from the join of the bounds: the value lies above each
  -- bound, and below the unknown wherever the orderings hold

  module Join {x₀ : RExp Ψ} {xs : List (RExp Ψ)} (e : Vʳ.bnds lw ≡ x₀ ∷ xs) where

    above : ∀ {b} → Vʳ.LowTo {Ψ} k l lw (joinᵣ x₀ xs) b → ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
          → ∀ {y} → y ∈ Vʳ.bnds lw → Q ⊩ y [ δ ]ʳ ≾̂ᵣ b [ δ ]ʳ
    above to δ m = transᵣ (joinᵣ-ub⊩ δ x₀ xs (subst (_ ∈_) e m)) (grows to δ)

    below : ∀ {b} → Vʳ.LowTo {Ψ} k l lw (joinᵣ x₀ xs) b → ∀ {Ψ'} {Q : Hyps Ψ'} → (τ : Subst Ψ Ψ')
          → (∀ {a a'} → (a , a') ∈ l → Q ⊩ a [ τ ]ʳ ≾̂ᵣ a' [ τ ]ʳ)
          → Q ⊩ b [ τ ]ʳ ≾̂ᵣ sR τ k
    below to τ h =
      least to τ (joinᵣ-lub⊩ τ x₀ xs (λ {y} m → h {y} (Vʳ.src lw (subst (_ ∈_) (sym e) m)))) h
