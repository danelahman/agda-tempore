------------------------------------------------------------------------
-- The order on one-sided expressions with iteration, decided.        --
--                                                                    --
-- In a commensurable time domain the durations of two expressions,   --
-- and the running times of the operations, are multiples of one unit --
-- `δ`. Then                                                          --
--                                                                    --
--   ⟦ e ⟧ ≾ ⟦ f ⟧   iff   L(X) ⊆ L(D_f)                              --
--                                                                    --
-- where X is the regular set of words of letters of `e` (its         --
-- unbounded stretches unrolled into iterations of stretches of at    --
-- most `δ`, in the upper instance), read as pieces at their extremal --
-- weights, and D_f the determinised automaton of reader              --
-- configurations against the words of `f`, both in units of `δ`.     --
--                                                                    --
-- The proof composes: `e` and `f` denote the runs of their words     --
-- (`Regular.Words`); a word is below the union of the words of `f`   --
-- exactly when the reader accepts it against one of them, sound for  --
-- each and complete against a family on a grid (`Reader.*.Family`);  --
-- the reader sees words on the grid as their counts of units         --
-- (`Reader.Rename`, `Exact.Grid`); and the automaton accepts what    --
-- the reader accepts against some word of `f` (`Regular.Upper`,      --
-- `Regular.Lower`). Inclusion of regular languages is decided by     --
-- `Regular.Decide`.                                                  --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain; Dense)
import Syntax.Grades.Traces.RunningTimes as RunningTimes
import Syntax.Durations.Monus as Monus
import Syntax.Grades.Exact.Grid as Grid

module Syntax.Grades.Exact.Regular.Decide
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (name : Fin n → Op) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ)
  (commensurable : Grid.Commensurable T) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map; allFin)
open import Data.List.Properties using (map-∘)
open import Data.List.Membership.Propositional using (_∈_; find; lose)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺; ∈-map⁻; ∈-allFin)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)

open import Syntax.Durations.Nat using (ℕᵀ)
open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T
  using (Cut; Hi; fin; ∞; pt; lo; hi; Side; ⁺; ⁻; 0⁺; _⊑ʰ_)
  renaming (_∣_ to _∣ᶜ_; _⊑_ to _⊑ᶜ_)
import Syntax.Durations.Intervals ℕᵀ as N

open import Syntax.Grades.Exact.Grid T
  using (_×ᴰ_; Unit; Archimedean; commensurable⇒archimedean; module Scale)
open import Syntax.Grades.Exact.Base T Op n code code-injective
open import Syntax.Grades.Exact.Order T Op n code code-injective using (_⊑_; ⊑-trans)
open import Syntax.Grades.Exact.Lift T Op n code code-injective using (Lang; _≾_; _≈_)
open import Syntax.Grades.Exact.Expression T Op n code code-injective running
open import Syntax.Grades.Exact.Letters T Op n code code-injective running
open import Syntax.Grades.Exact.Reader T Op n code code-injective running using (module Upper; module Lower)
open import Syntax.Grades.Exact.Reader.Transfer T Op n code code-injective running using (mapˡ)
open import Syntax.Grades.Exact.Reader.Rename T Op n code code-injective running using (module Rename)
open import Syntax.Grades.Exact.Finite T Op n code code-injective name code-name running dense κ κ-pos
  using (words; strWords; opw; members; Fine)
open import Syntax.Grades.Exact.Regular.Words T Op n code code-injective name code-name running dense κ κ-pos
open import Syntax.Grades.Regular.Coding as C using (Rx; size; letterAt; AllLits)
  renaming (code to codeRx; allLits to litsAt)
import Syntax.Grades.Regular.Automaton as Automaton
import Syntax.Grades.Regular.Expression as RE
import Syntax.Grades.Regular.Decide as RD
import Syntax.Grades.Exact.Regular.Unroll as Unroll
import Syntax.Grades.Exact.Regular.Upper as UpperAutomaton
import Syntax.Grades.Exact.Regular.Lower as LowerAutomaton
import Syntax.Grades.Exact.Regular.Gap as Gap
import Syntax.Grades.Exact.Reader.Upper.Family as UF
import Syntax.Grades.Exact.Reader.Lower.Family as LF
open import Syntax.Grades.Exact.Reader.Upper T Op n code code-injective running
  using (Ph; Fitsᵁ) renaming (RunU to RunUᵀ)
open import Syntax.Grades.Exact.Reader.Lower T Op n code code-injective running
  using (Pl; Fitsᴸ) renaming (RunL to RunLᵀ)
open import Syntax.Grades.Exact.Reader.Upper.Correct T Op n code code-injective running dense κ κ-pos
  using (symᵁ; soundᵁ; ValidW)
open import Syntax.Grades.Exact.Reader.Lower.Correct T Op n code code-injective running dense κ κ-pos
  using (symᴸ; soundᴸ)
open import Syntax.Grades.Exact.Reader.Upper.Close T Op n code code-injective running dense using (Valid)
open import Syntax.Grades.Exact.Reader.Lower.Read T Op n code code-injective running using (ValidL)

open RunningTimes.RunningTimes running using (rt; rt-bounded)
open RunningTimes T Op using (Bounded) renaming (fin to bfin)
open Equivalence using (to; from)

archimedean : Archimedean
archimedean = commensurable⇒archimedean commensurable

------------------------------------------------------------------------
-- The durations an expression mentions

ptʰ : Hi → Carrier
ptʰ (fin c) = pt c
ptʰ ∞       = 0ᴰ

rtHis rtLos : List Carrier
rtHis = map (λ c → ptʰ (hi (rt (name c)))) (allFin n)
rtLos = map (λ c → pt (lo (rt (name c)))) (allFin n)

endsᵁ : Expr upper → List Carrier
endsᵁ (str _ (fin c)) = pt c ∷ []
endsᵁ (e ∣ f)         = endsᵁ e ++ endsᵁ f
endsᵁ (e · f)         = endsᵁ e ++ endsᵁ f
endsᵁ (e *)           = endsᵁ e
endsᵁ _               = []

endsᴸ : Expr lower → List Carrier
endsᴸ (str _ c) = pt c ∷ []
endsᴸ (e ∣ f)   = endsᴸ e ++ endsᴸ f
endsᴸ (e · f)   = endsᴸ e ++ endsᴸ f
endsᴸ (e *)     = endsᴸ e
endsᴸ _         = []

private
  name-code : ∀ o → name (code o) ≡ o
  name-code o = code-injective (code-name (code o))

  rtHi∈ : ∀ o → ptʰ (hi (rt o)) ∈ rtHis
  rtHi∈ o = subst (λ o′ → ptʰ (hi (rt o′)) ∈ rtHis) (name-code o)
                  (∈-map⁺ (λ c → ptʰ (hi (rt (name c)))) (∈-allFin (code o)))

  rtLo∈ : ∀ o → pt (lo (rt o)) ∈ rtLos
  rtLo∈ o = subst (λ o′ → pt (lo (rt o′)) ∈ rtLos) (name-code o)
                  (∈-map⁺ (λ c → pt (lo (rt (name c)))) (∈-allFin (code o)))

------------------------------------------------------------------------
-- Durations on the grid of a unit, as counts of units

module OnUnit (xs : List Carrier) where

  open Unit (commensurable xs) public
  open Scale δ-pos public

  OnGrid : Carrier → Set
  OnGrid q = count q ×ᴰ δ ≡ q

  OnGridʰ : Hi → Set
  OnGridʰ (fin c) = OnGrid (pt c)
  OnGridʰ ∞       = ⊤

  listed : ∀ {q} → q ∈ xs → OnGrid q
  listed = counts

  on-δ : OnGrid δ
  on-δ = trans (cong (_×ᴰ δ) count-δ) (+ᴰ-identityʳ δ)

  sideℕ : Side → N.Side
  sideℕ ⁻ = N.⁻
  sideℕ ⁺ = N.⁺

  sc-side : ∀ s → scˢ (sideℕ s) ≡ s
  sc-side ⁻ = refl
  sc-side ⁺ = refl

  downᶜ : Cut → N.Cut
  downᶜ (p ∣ᶜ s) = count p N.∣ sideℕ s

  downʰ : Hi → N.Hi
  downʰ (fin c) = N.fin (downᶜ c)
  downʰ ∞       = N.∞

  sc-downᶜ : ∀ c → OnGrid (pt c) → scᶜ (downᶜ c) ≡ c
  sc-downᶜ (p ∣ᶜ s) g = cong₂ _∣ᶜ_ g (sc-side s)

  sc-downʰ : ∀ h → OnGridʰ h → scʰ (downʰ h) ≡ h
  sc-downʰ (fin c) g = cong fin (sc-downᶜ c g)
  sc-downʰ ∞       _ = refl

  -- letters and pieces, counted

  OnGridL : Letter Hi → Set
  OnGridL (op _)   = ⊤
  OnGridL (st _ h) = OnGridʰ h

  OnGridLᴸ : Letter Cut → Set
  OnGridLᴸ (op _)   = ⊤
  OnGridLᴸ (st _ c) = OnGrid (pt c)

  sc-letter : ∀ ℓ → OnGridL ℓ → mapˡ scʰ (mapˡ downʰ ℓ) ≡ ℓ
  sc-letter (op o)   _ = refl
  sc-letter (st S h) g = cong (st S) (sc-downʰ h g)

  sc-letterᴸ : ∀ ℓ → OnGridLᴸ ℓ → mapˡ scᶜ (mapˡ downᶜ ℓ) ≡ ℓ
  sc-letterᴸ (op o)   _ = refl
  sc-letterᴸ (st S c) g = cong (st S) (sc-downᶜ c g)

  -- the readers in counts of units see what the readers in durations see

  scP : Kind × N.Hi → Ph
  scP (k , h) = k , scʰ h

  scPᴸ : Kind × N.Cut → Pl
  scPᴸ (k , c) = k , scᶜ c

  Fitsℕᵁ : List (Kind × N.Hi) → List N.Hi → Set
  Fitsℕᵁ pre cs = Gap.sumʰ (map proj₂ pre) N.⊑ʰ Gap.sumʰ cs

  Fitsℕᴸ : List (Kind × N.Cut) → List N.Cut → Set
  Fitsℕᴸ pre cs = Gap.sumˡ cs N.⊑ Gap.sumˡ (map proj₂ pre)

  private
    wts : ∀ pre → map proj₂ (map scP pre) ≡ map scʰ (map proj₂ pre)
    wts []      = refl
    wts (p ∷ pre) = cong (_ ∷_) (wts pre)

    wtsᴸ : ∀ pre → map proj₂ (map scPᴸ pre) ≡ map scᶜ (map proj₂ pre)
    wtsᴸ []      = refl
    wtsᴸ (p ∷ pre) = cong (_ ∷_) (wtsᴸ pre)

    fitsᵁ : ∀ pre cs → Fitsᵁ (map scP pre) (map scʰ cs) ⇔ Fitsℕᵁ pre cs
    fitsᵁ pre cs =
      mk⇔ (λ h → from (scʰ-⇔ (Gap.sumʰ (map proj₂ pre)) (Gap.sumʰ cs)) (subst₂ _⊑ʰ_ e₁ (sym (scʰ-sum cs)) h))
          (λ h → subst₂ _⊑ʰ_ (sym e₁) (scʰ-sum cs) (to (scʰ-⇔ (Gap.sumʰ (map proj₂ pre)) (Gap.sumʰ cs)) h))
      where
        e₁ : sumʰ (map proj₂ (map scP pre)) ≡ scʰ (Gap.sumʰ (map proj₂ pre))
        e₁ = trans (cong sumʰ (wts pre)) (sym (scʰ-sum (map proj₂ pre)))

    fitsᴸ : ∀ pre cs → Fitsᴸ (map scPᴸ pre) (map scᶜ cs) ⇔ Fitsℕᴸ pre cs
    fitsᴸ pre cs =
      mk⇔ (λ h → from (scᶜ-⇔ (Gap.sumˡ cs) (Gap.sumˡ (map proj₂ pre))) (subst₂ _⊑ᶜ_ (sym (scᶜ-sum cs)) e₁ h))
          (λ h → subst₂ _⊑ᶜ_ (scᶜ-sum cs) (sym e₁) (to (scᶜ-⇔ (Gap.sumˡ cs) (Gap.sumˡ (map proj₂ pre))) h))
      where
        e₁ : sumˡ (map proj₂ (map scPᴸ pre)) ≡ scᶜ (Gap.sumˡ (map proj₂ pre))
        e₁ = trans (cong sumˡ (wtsᴸ pre)) (sym (scᶜ-sum (map proj₂ pre)))

  module RU = Rename.U proj₁ proj₁ Fitsℕᵁ Fitsᵁ scP scʰ (λ _ → refl) fitsᵁ
  module RL = Rename.L proj₁ proj₁ Fitsℕᴸ Fitsᴸ scPᴸ scᶜ (λ _ → refl) fitsᴸ

------------------------------------------------------------------------
-- The letters of an expression's own letters

private
  allOps : ∀ {s} {P : Letter (End s) → Set} → (∀ o → P (op o)) → ∀ cs → All (All P) (map (opw {s}) cs)
  allOps p []       = []
  allOps p (c ∷ cs) = (p (name c) ∷ []) ∷ allOps p cs

  strAllᵁ : ∀ S h → All (All (_≡ st S h)) (strWords upper S h)
  strAllᵁ S ∞ = (refl ∷ []) ∷ []
  strAllᵁ S (fin (p ∣ᶜ side)) with 0ᴰ <ᴰ? p
  ... | yes _ = (refl ∷ []) ∷ []
  ... | no _ with side
  ...   | ⁺ = [] ∷ []
  ...   | ⁻ = []

  strAllᴸ : ∀ S c → All (All (λ ℓ → ℓ ≡ st S c ⊎ ℓ ≡ st S (0ᴰ ∣ᶜ ⁺))) (strWords lower S c)
  strAllᴸ S (p ∣ᶜ side) with 0ᴰ <ᴰ? p
  ... | yes _ = (inj₁ refl ∷ []) ∷ []
  ... | no _ with side
  ...   | ⁺ = (inj₁ refl ∷ []) ∷ []
  ...   | ⁻ = [] ∷ (inj₂ refl ∷ []) ∷ []

  BL : Letter Hi → Set
  BL (op _)   = ⊤
  BL (st _ h) = Bounded h

  -- the property, letter by letter, of a decoded word
  all-map : ∀ {A L : Set} {P : L → Set} (dec : A → L) → (∀ a → P (dec a)) → ∀ u → All P (map dec u)
  all-map dec p []      = []
  all-map dec p (a ∷ u) = p a ∷ all-map dec p u

  ++ˡ : ∀ {A : Set} {xs ys : List A} {P : A → Set} → (∀ {q} → q ∈ xs ++ ys → P q) → ∀ {q} → q ∈ xs → P q
  ++ˡ h m = h (∈-++⁺ˡ m)

  ++ʳ : ∀ {A : Set} {xs ys : List A} {P : A → Set} → (∀ {q} → q ∈ xs ++ ys → P q) → ∀ {q} → q ∈ ys → P q
  ++ʳ {xs = xs} h m = h (∈-++⁺ʳ xs m)

------------------------------------------------------------------------
-- The upper instance

module Up (e f : Expr upper) where

  xs : List Carrier
  xs = 0ᴰ ∷ endsᵁ e ++ endsᵁ f ++ rtHis

  open OnUnit xs
  open Unroll T Op n code code-injective running archimedean δ δ-pos using (unroll; unroll-≈; ≤δ)

  e′ : Expr upper
  e′ = unroll e

  rX rY : Rx (Letter Hi)
  rX = toRx e′
  rY = toRx f

  kX kY : ℕ
  kX = size rX
  kY = size rY

  lX : Fin kX → Letter Hi
  lX = letterAt rX

  lY : Fin kY → Letter Hi
  lY = letterAt rY

  module EX = RE kX
  module EY = RE kY

  X : Automaton.DFA kX
  X = EX.elab (codeRx rX)

  M : Automaton.DFA kY
  M = EY.elab (codeRx rY)

  -- the letters are on the grid, and those of `e′` bounded

  private
    in-xs : ∀ {q} → q ∈ endsᵁ e ++ endsᵁ f ++ rtHis → OnGrid q
    in-xs m = listed (there m)

    on-e : ∀ {q} → q ∈ endsᵁ e → OnGrid q
    on-e m = in-xs (∈-++⁺ˡ m)

    on-f : ∀ {q} → q ∈ endsᵁ f → OnGrid q
    on-f m = in-xs (∈-++⁺ʳ (endsᵁ e) (∈-++⁺ˡ m))

    on-rt : ∀ o → OnGridʰ (hi (rt o))
    on-rt o with hi (rt o) | rtHi∈ o
    ... | fin c | m = in-xs (∈-++⁺ʳ (endsᵁ e) (∈-++⁺ʳ (endsᵁ f) m))
    ... | ∞     | _ = tt

    leaf-str : ∀ S h → OnGridʰ h → All (All OnGridL) (strWords upper S h)
    leaf-str S h g = All.map (All.map (λ { refl → g })) (strAllᵁ S h)

    leaves-unroll : ∀ e → (∀ {q} → q ∈ endsᵁ e → OnGrid q) → Leaves OnGridL (unroll e)
    leaves-unroll ε _ = [] ∷ []
    leaves-unroll (ops A) _ = allOps (λ _ → tt) (members A)
    leaves-unroll (str S ∞) _ = leaf-str S (fin (δ ∣ᶜ ⁺)) on-δ
    leaves-unroll (str S (fin c)) g = leaf-str S (fin c) (g (here refl))
    leaves-unroll (e ∣ f) g = leaves-unroll e (++ˡ g) , leaves-unroll f (++ʳ {xs = endsᵁ e} g)
    leaves-unroll (e · f) g = leaves-unroll e (++ˡ g) , leaves-unroll f (++ʳ {xs = endsᵁ e} g)
    leaves-unroll (e *) g = leaves-unroll e g

    leaves-f : ∀ f → (∀ {q} → q ∈ endsᵁ f → OnGrid q) → Leaves OnGridL f
    leaves-f ε _ = [] ∷ []
    leaves-f (ops A) _ = allOps (λ _ → tt) (members A)
    leaves-f (str S ∞) _ = leaf-str S ∞ tt
    leaves-f (str S (fin c)) g = leaf-str S (fin c) (g (here refl))
    leaves-f (e ∣ f) g = leaves-f e (++ˡ g) , leaves-f f (++ʳ {xs = endsᵁ e} g)
    leaves-f (e · f) g = leaves-f e (++ˡ g) , leaves-f f (++ʳ {xs = endsᵁ e} g)
    leaves-f (e *) g = leaves-f e g

    leaves-bounded : ∀ e → Leaves BL (unroll e)
    leaves-bounded ε = [] ∷ []
    leaves-bounded (ops A) = allOps (λ _ → tt) (members A)
    leaves-bounded (str S ∞) = All.map (All.map (λ { refl → bfin _ })) (strAllᵁ S (fin (δ ∣ᶜ ⁺)))
    leaves-bounded (str S (fin c)) = All.map (All.map (λ { refl → bfin _ })) (strAllᵁ S (fin c))
    leaves-bounded (e ∣ f) = leaves-bounded e , leaves-bounded f
    leaves-bounded (e · f) = leaves-bounded e , leaves-bounded f
    leaves-bounded (e *) = leaves-bounded e

  gX : ∀ a → OnGridL (lX a)
  gX = litsAt rX (allLits e′ (leaves-unroll e on-e))

  bX : ∀ a → BL (lX a)
  bX = litsAt rX (allLits e′ (leaves-bounded e))

  gY : ∀ b → OnGridL (lY b)
  gY = litsAt rY (allLits f (leaves-f f on-f))

  -- the letters in counts of units

  downP : Ph → Kind × N.Hi
  downP (k , h) = k , downʰ h

  decX : Fin kX → Kind × N.Hi
  decX a = downP (symᵁ (lX a))

  decY : Fin kY → Letter N.Hi
  decY b = mapˡ downʰ (lY b)

  private
    fin-down : ∀ h → Bounded h → Σ ℕ λ j → Σ N.Side λ u → downʰ h ≡ N.fin (j N.∣ u)
    fin-down (fin (p ∣ᶜ s)) _ = count p , sideℕ s , refl
    fin-down ∞ ()

    fin-rt : ∀ o → Bounded (hi (rt o))
    fin-rt o = rt-bounded o

  decX-fin : ∀ a → Σ ℕ λ j → Σ N.Side λ u → proj₂ (decX a) ≡ N.fin (j N.∣ u)
  decX-fin a with lX a | bX a
  ... | op o   | _ = fin-down (hi (rt o)) (fin-rt o)
  ... | st S h | b = fin-down h b

  module A = UpperAutomaton T Op n code code-injective running kX kY M (EY.elab-wf (codeRx rY)) decX decY decX-fin

  private
    sc-decX : ∀ a → scP (decX a) ≡ symᵁ (lX a)
    sc-decX a with lX a | gX a
    ... | op o   | _ = cong (opk o ,_) (sc-downʰ (hi (rt o)) (on-rt o))
    ... | st S h | g = cong (stk S ,_) (sc-downʰ h g)

    pieces-sc : ∀ u → map scP (map decX u) ≡ map symᵁ (map lX u)
    pieces-sc []      = refl
    pieces-sc (a ∷ u) = cong₂ _∷_ (sc-decX a) (pieces-sc u)

    bounds-sc : ∀ uY → map (mapˡ scʰ) (map decY uY) ≡ map lY uY
    bounds-sc []       = refl
    bounds-sc (b ∷ uY) = cong₂ _∷_ (sc-letter (lY b) (gY b)) (bounds-sc uY)

    -- the reader in counts of units, against the words of `f`
    toᵀ : ∀ u uY → Upper.RunU proj₁ Fitsℕᵁ (map decX u) (map decY uY) → RunUᵀ (map symᵁ (map lX u)) (map lY uY)
    toᵀ u uY r = subst₂ RunUᵀ (pieces-sc u) (bounds-sc uY) (to (RU.rename (map decX u) (map decY uY)) r)

    toℕ : ∀ u uY → RunUᵀ (map symᵁ (map lX u)) (map lY uY) → Upper.RunU proj₁ Fitsℕᵁ (map decX u) (map decY uY)
    toℕ u uY r = from (RU.rename (map decX u) (map decY uY)) (subst₂ RunUᵀ (sym (pieces-sc u)) (sym (bounds-sc uY)) r)

    module F = UF T Op n code code-injective running dense κ κ-pos archimedean δ δ-pos

    bounded-w : ∀ u → F.BoundedW (map lX u)
    bounded-w []      = tt
    bounded-w (a ∷ u) with lX a | bX a
    ... | op o   | _ = bounded-w u
    ... | st S h | b = b , bounded-w u

    grid-v : ∀ uY → F.GridW (map lY uY)
    grid-v []       = tt
    grid-v (b ∷ uY) with lY b | gY b
    ... | op o   | _ = grid-v uY
    ... | st S ∞ | _ = tt , grid-v uY
    ... | st S (fin (p ∣ᶜ s)) | g = (count p , g) , grid-v uY

    Fam : Word′ upper → Set
    Fam v = Σ[ uY ∈ List (Fin kY) ] EY.⟦ codeRx rY ⟧ uY × map lY uY ≡ v

  -- below the words of `f` exactly when in the table

  complete : ⟦ e ⟧ ≾ ⟦ f ⟧ → Automaton._⊆_ kX X A.determinised
  complete g u u∈ = from (A.∈-reader u) (uY , fin′ , toℕ u uY r)
    where
      c = to (EX.elab-correct (codeRx rX) u) u∈
      w = map lX u
      wd : Wd e′ w
      wd = toRx⇒ e′ (C.code-sound rX c)
      below : ⟦ w ⟧ʷ ≾ F.UnionF Fam
      below x x∈ with proj₁ (unroll-≈ e) x (wd⇐ e′ wd x∈)
      ... | x′ , x′∈ , xx′ with g x′ x′∈
      ...   | y , y∈ , x′y with wd⇒ f y∈
      ...     | v , wdv , y∈v with C.code-complete rY (⇒toRx f wdv)
      ...       | uY′ , cY , refl = y , (map lY uY′ , (uY′ , cY , refl) , y∈v) , ⊑-trans xx′ x′y
      found = F.completeᶠ w (proj₁ (fineᵂ e′ wd)) (bounded-w u) Fam
                (λ { {v} (uY′ , _ , refl) → grid-v uY′ }) below
      uY = proj₁ (proj₁ (proj₂ found))
      cY = proj₁ (proj₂ (proj₁ (proj₂ found)))
      r : RunUᵀ (map symᵁ w) (map lY uY)
      r = subst (RunUᵀ (map symᵁ w)) (sym (proj₂ (proj₂ (proj₁ (proj₂ found))))) (proj₂ (proj₂ found))
      fin′ = from (EY.elab-correct (codeRx rY) uY) cY

  sound : Automaton._⊆_ kX X A.determinised → ⟦ e ⟧ ≾ ⟦ f ⟧
  sound sub x x∈ = y , wd⇐ f wdv y∈v , ⊑-trans xx′ x′y
    where
      lifted = proj₂ (unroll-≈ e) x x∈
      x′  = proj₁ lifted
      xx′ = proj₂ (proj₂ lifted)
      runs = wd⇒ e′ (proj₁ (proj₂ lifted))
      w   = proj₁ runs
      wd  = proj₁ (proj₂ runs)
      coded = C.code-complete rX (⇒toRx e′ wd)
      u   = proj₁ coded
      ew : map lX u ≡ w
      ew  = proj₂ (proj₂ coded)
      reads = to (A.∈-reader u) (sub u (from (EX.elab-correct (codeRx rX) u) (proj₁ (proj₂ coded))))
      uY  = proj₁ reads
      cY  = to (EY.elab-correct (codeRx rY) uY) (proj₁ (proj₂ reads))
      wdv : Wd f (map lY uY)
      wdv = toRx⇒ f (C.code-sound rY cY)
      x′∈ : ⟦ map lX u ⟧ʷ x′
      x′∈ = subst (λ z → ⟦ z ⟧ʷ x′) (sym ew) (proj₂ (proj₂ runs))
      found = soundᵁ (map lX u) (map lY uY) (proj₂ (fineᵂ f wdv)) (toᵀ u uY (proj₂ (proj₂ reads))) x′ x′∈
      y   = proj₁ found
      y∈v = proj₁ (proj₂ found)
      x′y = proj₂ (proj₂ found)

  decide⇔ : ⟦ e ⟧ ≾ ⟦ f ⟧ ⇔ Automaton._⊆_ kX X A.determinised
  decide⇔ = mk⇔ complete sound

  decide : Dec (⟦ e ⟧ ≾ ⟦ f ⟧)
  decide = map′ sound complete (RD._⊆?_ kX {X} {A.determinised} (EX.elab-wf (codeRx rX)) A.determinised-wf)

-- the upper order, decided

infix 4 _≾ᵁ?_

_≾ᵁ?_ : (e f : Expr upper) → Dec (⟦ e ⟧ ≾ ⟦ f ⟧)
e ≾ᵁ? f = Up.decide e f

------------------------------------------------------------------------
-- The lower instance

module Lo (e f : Expr lower) where

  xs : List Carrier
  xs = 0ᴰ ∷ endsᴸ e ++ endsᴸ f ++ rtLos

  open OnUnit xs

  rX rY : Rx (Letter Cut)
  rX = toRx e
  rY = toRx f

  kX kY : ℕ
  kX = size rX
  kY = size rY

  lX : Fin kX → Letter Cut
  lX = letterAt rX

  lY : Fin kY → Letter Cut
  lY = letterAt rY

  module EX = RE kX
  module EY = RE kY

  X : Automaton.DFA kX
  X = EX.elab (codeRx rX)

  M : Automaton.DFA kY
  M = EY.elab (codeRx rY)

  private
    in-xs : ∀ {q} → q ∈ endsᴸ e ++ endsᴸ f ++ rtLos → OnGrid q
    in-xs m = listed (there m)

    on-0 : OnGrid 0ᴰ
    on-0 = listed (here refl)

    on-rt : ∀ o → OnGrid (pt (lo (rt o)))
    on-rt o = in-xs (∈-++⁺ʳ (endsᴸ e) (∈-++⁺ʳ (endsᴸ f) (rtLo∈ o)))

    leaves : ∀ e → (∀ {q} → q ∈ endsᴸ e → OnGrid q) → Leaves OnGridLᴸ e
    leaves ε _ = [] ∷ []
    leaves (ops A) _ = allOps (λ _ → tt) (members A)
    leaves (str S c) g = All.map (All.map (λ { (inj₁ refl) → g (here refl) ; (inj₂ refl) → on-0 })) (strAllᴸ S c)
    leaves (e ∣ f) g = leaves e (++ˡ g) , leaves f (++ʳ {xs = endsᴸ e} g)
    leaves (e · f) g = leaves e (++ˡ g) , leaves f (++ʳ {xs = endsᴸ e} g)
    leaves (e *) g = leaves e g

  gX : ∀ a → OnGridLᴸ (lX a)
  gX = litsAt rX (allLits e (leaves e (λ m → in-xs (∈-++⁺ˡ m))))

  gY : ∀ b → OnGridLᴸ (lY b)
  gY = litsAt rY (allLits f (leaves f (λ m → in-xs (∈-++⁺ʳ (endsᴸ e) (∈-++⁺ˡ m)))))

  downP : Pl → Kind × N.Cut
  downP (k , c) = k , downᶜ c

  decX : Fin kX → Kind × N.Cut
  decX a = downP (symᴸ (lX a))

  decY : Fin kY → Letter N.Cut
  decY b = mapˡ downᶜ (lY b)

  module A = LowerAutomaton T Op n code code-injective running kX kY M (EY.elab-wf (codeRx rY)) decX decY

  private
    sc-decX : ∀ a → scPᴸ (decX a) ≡ symᴸ (lX a)
    sc-decX a with lX a | gX a
    ... | op o   | _ = cong (opk o ,_) (sc-downᶜ (lo (rt o)) (on-rt o))
    ... | st S c | g = cong (stk S ,_) (sc-downᶜ c g)

    pieces-sc : ∀ u → map scPᴸ (map decX u) ≡ map symᴸ (map lX u)
    pieces-sc []      = refl
    pieces-sc (a ∷ u) = cong₂ _∷_ (sc-decX a) (pieces-sc u)

    bounds-sc : ∀ uY → map (mapˡ scᶜ) (map decY uY) ≡ map lY uY
    bounds-sc []       = refl
    bounds-sc (b ∷ uY) = cong₂ _∷_ (sc-letterᴸ (lY b) (gY b)) (bounds-sc uY)

    toᵀ : ∀ u uY → Lower.RunL proj₁ Fitsℕᴸ (map decX u) (map decY uY) → RunLᵀ (map symᴸ (map lX u)) (map lY uY)
    toᵀ u uY r = subst₂ RunLᵀ (pieces-sc u) (bounds-sc uY) (to (RL.rename (map decX u) (map decY uY)) r)

    toℕ : ∀ u uY → RunLᵀ (map symᴸ (map lX u)) (map lY uY) → Lower.RunL proj₁ Fitsℕᴸ (map decX u) (map decY uY)
    toℕ u uY r = from (RL.rename (map decX u) (map decY uY)) (subst₂ RunLᵀ (sym (pieces-sc u)) (sym (bounds-sc uY)) r)

    module F = LF T Op n code code-injective running dense κ κ-pos archimedean δ δ-pos

    grid-v : ∀ uY → F.GridWˡ (map lY uY)
    grid-v []       = tt
    grid-v (b ∷ uY) with lY b | gY b
    ... | op o   | _ = grid-v uY
    ... | st S c | g = (count (pt c) , g) , grid-v uY

    Fam : Word′ lower → Set
    Fam v = Σ[ uY ∈ List (Fin kY) ] EY.⟦ codeRx rY ⟧ uY × map lY uY ≡ v

  complete : ⟦ e ⟧ ≾ ⟦ f ⟧ → Automaton._⊆_ kX X A.determinised
  complete g u u∈ = from (A.∈-reader u) (uY , fin′ , toℕ u uY r)
    where
      c = to (EX.elab-correct (codeRx rX) u) u∈
      w = map lX u
      wd : Wd e w
      wd = toRx⇒ e (C.code-sound rX c)
      below : ⟦ w ⟧ʷ ≾ F.UnionFˡ Fam
      below x x∈ with g x (wd⇐ e wd x∈)
      ... | y , y∈ , xy with wd⇒ f y∈
      ...   | v , wdv , y∈v with C.code-complete rY (⇒toRx f wdv)
      ...     | uY′ , cY , refl = y , (map lY uY′ , (uY′ , cY , refl) , y∈v) , xy
      gF : ∀ {v} → Fam v → F.GridWˡ v × ValidL v
      gF (uY′ , cY , refl) = grid-v uY′ , fineᵂ f (toRx⇒ f (C.code-sound rY cY))
      found = F.completeᶠᴸ w (fineᵂ e wd) Fam gF below
      uY = proj₁ (proj₁ (proj₂ found))
      cY = proj₁ (proj₂ (proj₁ (proj₂ found)))
      r : RunLᵀ (map symᴸ w) (map lY uY)
      r = subst (RunLᵀ (map symᴸ w)) (sym (proj₂ (proj₂ (proj₁ (proj₂ found))))) (proj₂ (proj₂ found))
      fin′ = from (EY.elab-correct (codeRx rY) uY) cY

  sound : Automaton._⊆_ kX X A.determinised → ⟦ e ⟧ ≾ ⟦ f ⟧
  sound sub x x∈ = proj₁ found , wd⇐ f wdv (proj₁ (proj₂ found)) , proj₂ (proj₂ found)
    where
      runs = wd⇒ e x∈
      w   = proj₁ runs
      wd  = proj₁ (proj₂ runs)
      coded = C.code-complete rX (⇒toRx e wd)
      u   = proj₁ coded
      ew : map lX u ≡ w
      ew  = proj₂ (proj₂ coded)
      reads = to (A.∈-reader u) (sub u (from (EX.elab-correct (codeRx rX) u) (proj₁ (proj₂ coded))))
      uY  = proj₁ reads
      cY  = to (EY.elab-correct (codeRx rY) uY) (proj₁ (proj₂ reads))
      wdv : Wd f (map lY uY)
      wdv = toRx⇒ f (C.code-sound rY cY)
      x∈′ : ⟦ map lX u ⟧ʷ x
      x∈′ = subst (λ z → ⟦ z ⟧ʷ x) (sym ew) (proj₂ (proj₂ runs))
      found = soundᴸ (map lX u) (map lY uY) (toᵀ u uY (proj₂ (proj₂ reads))) x x∈′

  decide⇔ : ⟦ e ⟧ ≾ ⟦ f ⟧ ⇔ Automaton._⊆_ kX X A.determinised
  decide⇔ = mk⇔ complete sound

  decide : Dec (⟦ e ⟧ ≾ ⟦ f ⟧)
  decide = map′ sound complete (RD._⊆?_ kX {X} {A.determinised} (EX.elab-wf (codeRx rX)) A.determinised-wf)

-- the lower order, decided

infix 4 _≾ᴸ?_

_≾ᴸ?_ : (e f : Expr lower) → Dec (⟦ e ⟧ ≾ ⟦ f ⟧)
e ≾ᴸ? f = Lo.decide e f
