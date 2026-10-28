------------------------------------------------------------------------
-- The words of an expression with iteration: a regular set of words  --
-- of letters.                                                        --
--                                                                    --
-- A letter of an expression contributes its finitely many words      --
-- (`Exact.Finite`); union, concatenation and iteration act on sets   --
-- of words as on languages. An expression denotes the union of the   --
-- runs of its words,                                                 --
--                                                                    --
--   ⟦ e ⟧ x   iff   ⟦ w ⟧ʷ x  for some word w of e                   --
--                                                                    --
-- and every word of an expression is of the reader's kind.           --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain; Dense)
import Grades.Traces.RunningTimes as RunningTimes
import Grades.Durations.Monus as Monus

module Grades.Exact.Regular.Words
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (name : Fin n → Op) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ) where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (find) renaming (_∈_ to _∈ˡ_)
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Lift T Op n code code-injective
open import Grades.Exact.Expression T Op n code code-injective running
open import Grades.Exact.Letters T Op n code code-injective running
open import Grades.Exact.Reader.Upper.Close T Op n code code-injective running dense
  using (Valid)
open import Grades.Exact.Reader.Upper.Correct T Op n code code-injective running dense κ κ-pos
  using (ValidW)
open import Grades.Exact.Reader.Lower.Read T Op n code code-injective running
  using (ValidL)
open import Grades.Exact.Finite T Op n code code-injective name code-name running dense κ κ-pos
  using (words; words⇒; words⇐; Fine; fine)

------------------------------------------------------------------------
-- Iteration of a set of words

data StarW {s} (W : Word′ s → Set) : Word′ s → Set where
  stop : StarW W []
  more : ∀ {u v} → W u → StarW W v → StarW W (u ++ v)

------------------------------------------------------------------------
-- The words of an expression

Wd : ∀ {s} → Expr s → Word′ s → Set
Wd ε         w = w ∈ˡ words ε
Wd (ops A)   w = w ∈ˡ words (ops A)
Wd (str S e) w = w ∈ˡ words (str S e)
Wd (e ∣ f)   w = Wd e w ⊎ Wd f w
Wd (e · f)   w = Σ[ u ∈ Word′ _ ] Σ[ v ∈ Word′ _ ] w ≡ u ++ v × Wd e u × Wd f v
Wd (e *)     w = StarW (Wd e) w

------------------------------------------------------------------------
-- Runs of concatenated words

⟦++⟧⇒ : ∀ {s} (u w : Word′ s) {x} → ⟦ u ++ w ⟧ʷ x → (⟦ u ⟧ʷ ·ᴸ ⟦ w ⟧ʷ) x
⟦++⟧⇒ []      w x∈ = [] , _ , refl , refl , x∈
⟦++⟧⇒ (ℓ ∷ u) w (x₁ , x′ , refl , x₁∈ , x′∈) with ⟦++⟧⇒ u w x′∈
... | x₂ , x₃ , refl , x₂∈ , x₃∈ =
  x₁ ++ x₂ , x₃ , sym (++-assoc x₁ x₂ x₃) , (x₁ , x₂ , refl , x₁∈ , x₂∈) , x₃∈

⟦++⟧⇐ : ∀ {s} (u w : Word′ s) {x} → (⟦ u ⟧ʷ ·ᴸ ⟦ w ⟧ʷ) x → ⟦ u ++ w ⟧ʷ x
⟦++⟧⇐ []      w (_ , x₂ , refl , refl , x₂∈) = x₂∈
⟦++⟧⇐ (ℓ ∷ u) w (_ , x₃ , refl , (x₁ , x₂ , refl , x₁∈ , x₂∈) , x₃∈) =
  x₁ , x₂ ++ x₃ , ++-assoc x₁ x₂ x₃ , x₁∈ , ⟦++⟧⇐ u w (x₂ , x₃ , refl , x₂∈ , x₃∈)

------------------------------------------------------------------------
-- An expression denotes the union of the runs of its words

Runs : ∀ {s} → Expr s → Lang
Runs e x = Σ[ w ∈ Word′ _ ] Wd e w × ⟦ w ⟧ʷ x

wd⇒ : ∀ {s} (e : Expr s) {x} → ⟦ e ⟧ x → Runs e x
wd⇒ ε         x∈ with find (words⇒ ε tt x∈)
... | w , m , y = w , m , y
wd⇒ (ops A)   x∈ with find (words⇒ (ops A) tt x∈)
... | w , m , y = w , m , y
wd⇒ (str S e) x∈ with find (words⇒ (str S e) tt x∈)
... | w , m , y = w , m , y
wd⇒ (e ∣ f)   (inj₁ x∈) with wd⇒ e x∈
... | w , m , y = w , inj₁ m , y
wd⇒ (e ∣ f)   (inj₂ x∈) with wd⇒ f x∈
... | w , m , y = w , inj₂ m , y
wd⇒ (e · f)   (x₁ , x₂ , refl , x₁∈ , x₂∈) with wd⇒ e x₁∈ | wd⇒ f x₂∈
... | u , mu , yu | v , mv , yv =
  u ++ v , (u , v , refl , mu , mv) , ⟦++⟧⇐ u v (x₁ , x₂ , refl , yu , yv)
wd⇒ (e *)     stop = [] , stop , refl
wd⇒ (e *)     (more {x₁} {x₂} x₁∈ x₂∈) with wd⇒ e x₁∈ | wd⇒ (e *) x₂∈
... | u , mu , yu | v , mv , yv =
  u ++ v , more mu mv , ⟦++⟧⇐ u v (x₁ , x₂ , refl , yu , yv)

wd⇐ : ∀ {s} (e : Expr s) {w x} → Wd e w → ⟦ w ⟧ʷ x → ⟦ e ⟧ x
wd⇐ ε         m y = words⇐ ε tt m y
wd⇐ (ops A)   m y = words⇐ (ops A) tt m y
wd⇐ (str S e) m y = words⇐ (str S e) tt m y
wd⇐ (e ∣ f)   (inj₁ m) y = inj₁ (wd⇐ e m y)
wd⇐ (e ∣ f)   (inj₂ m) y = inj₂ (wd⇐ f m y)
wd⇐ (e · f)   (u , v , refl , mu , mv) y with ⟦++⟧⇒ u v y
... | x₁ , x₂ , refl , y₁ , y₂ = x₁ , x₂ , refl , wd⇐ e mu y₁ , wd⇐ f mv y₂
wd⇐ (e *)     stop refl = stop
wd⇐ (e *)     (more {u} {v} mu mv) y with ⟦++⟧⇒ u v y
... | x₁ , x₂ , refl , y₁ , y₂ = more (wd⇐ e mu y₁) (wd⇐ (e *) mv y₂)

runs-≈ : ∀ {s} (e : Expr s) → ⟦ e ⟧ ≈ Runs e
runs-≈ e = ⊆⇒≾ (λ x → wd⇒ e) , ⊆⇒≾ (λ { x (w , m , y) → wd⇐ e m y })

------------------------------------------------------------------------
-- The words are of the reader's kind

private
  validW-++ : ∀ (u w : Word′ upper) → ValidW u → ValidW w → ValidW (u ++ w)
  validW-++ []           w _        vw = vw
  validW-++ (op _ ∷ u)   w vu       vw = validW-++ u w vu vw
  validW-++ (st _ _ ∷ u) w (p , vu) vw = p , validW-++ u w vu vw

  valid-++ : ∀ (u w : Word′ upper) → Valid u → Valid w → Valid (u ++ w)
  valid-++ []           w _        vw = vw
  valid-++ (op _ ∷ u)   w vu       vw = valid-++ u w vu vw
  valid-++ (st _ _ ∷ u) w (p , vu) vw = p , valid-++ u w vu vw

  validL-++ : ∀ (u w : Word′ lower) → ValidL u → ValidL w → ValidL (u ++ w)
  validL-++ []           w _        vw = vw
  validL-++ (op _ ∷ u)   w vu       vw = validL-++ u w vu vw
  validL-++ (st _ _ ∷ u) w (p , vu) vw = p , validL-++ u w vu vw

fine-++ : ∀ s (u w : Word′ s) → Fine s u → Fine s w → Fine s (u ++ w)
fine-++ upper u w (a , b) (c , d) = validW-++ u w a c , valid-++ u w b d
fine-++ lower u w a c = validL-++ u w a c

fine-[] : ∀ s → Fine s []
fine-[] upper = tt , tt
fine-[] lower = tt

fineᵂ : ∀ {s} (e : Expr s) {w} → Wd e w → Fine s w
fineᵂ ε         m = fine ε m
fineᵂ (ops A)   m = fine (ops A) m
fineᵂ (str S e) m = fine (str S e) m
fineᵂ (e ∣ f)   (inj₁ m) = fineᵂ e m
fineᵂ (e ∣ f)   (inj₂ m) = fineᵂ f m
fineᵂ {s} (e · f) (u , v , refl , mu , mv) = fine-++ s u v (fineᵂ e mu) (fineᵂ f mv)
fineᵂ {s} (e *) stop = fine-[] s
fineᵂ {s} (e *) (more {u} {v} mu mv) = fine-++ s u v (fineᵂ e mu) (fineᵂ (e *) mv)

------------------------------------------------------------------------
-- The words as a regular expression over letters

open import Grades.Regular.Coding as C using (Rx; ⟦_⟧ᴬ; StarA; AllLits)
open import Data.List.Relation.Unary.Any using (here; there)

private
  wordRx : ∀ {s} → Word′ s → Rx (Letter (End s))
  wordRx []      = C.ε
  wordRx (ℓ ∷ w) = C.lit ℓ C.· wordRx w

  unionRx : ∀ {s} → List (Word′ s) → Rx (Letter (End s))
  unionRx []       = C.∅
  unionRx (w ∷ ws) = wordRx w C.∣ unionRx ws

  wordRx⇒ : ∀ {s} (w : Word′ s) {w′} → ⟦ wordRx w ⟧ᴬ w′ → w′ ≡ w
  wordRx⇒ []      refl = refl
  wordRx⇒ (ℓ ∷ w) (_ , v , refl , refl , x) = cong (ℓ ∷_) (wordRx⇒ w x)

  ⇒wordRx : ∀ {s} (w : Word′ s) → ⟦ wordRx w ⟧ᴬ w
  ⇒wordRx []      = refl
  ⇒wordRx (ℓ ∷ w) = ℓ ∷ [] , w , refl , refl , ⇒wordRx w

  unionRx⇒ : ∀ {s} (ws : List (Word′ s)) {w} → ⟦ unionRx ws ⟧ᴬ w → w ∈ˡ ws
  unionRx⇒ (w′ ∷ ws) (inj₁ x) = here (wordRx⇒ w′ x)
  unionRx⇒ (w′ ∷ ws) (inj₂ x) = there (unionRx⇒ ws x)

  ⇒unionRx : ∀ {s} (ws : List (Word′ s)) {w} → w ∈ˡ ws → ⟦ unionRx ws ⟧ᴬ w
  ⇒unionRx (w′ ∷ ws) (here refl) = inj₁ (⇒wordRx w′)
  ⇒unionRx (w′ ∷ ws) (there m) = inj₂ (⇒unionRx ws m)

toRx : ∀ {s} → Expr s → Rx (Letter (End s))
toRx ε         = unionRx (words ε)
toRx (ops A)   = unionRx (words (ops A))
toRx (str S e) = unionRx (words (str S e))
toRx (e ∣ f)   = toRx e C.∣ toRx f
toRx (e · f)   = toRx e C.· toRx f
toRx (e *)     = toRx e C.*

toRx⇒ : ∀ {s} (e : Expr s) {w} → ⟦ toRx e ⟧ᴬ w → Wd e w
toRx⇒ ε         x = unionRx⇒ (words ε) x
toRx⇒ (ops A)   x = unionRx⇒ (words (ops A)) x
toRx⇒ (str S e) x = unionRx⇒ (words (str S e)) x
toRx⇒ (e ∣ f)   (inj₁ x) = inj₁ (toRx⇒ e x)
toRx⇒ (e ∣ f)   (inj₂ x) = inj₂ (toRx⇒ f x)
toRx⇒ (e · f)   (u , v , eq , x , y) = u , v , eq , toRx⇒ e x , toRx⇒ f y
toRx⇒ (e *)     x = star x
  where
    star : ∀ {w} → StarA ⟦ toRx e ⟧ᴬ w → StarW (Wd e) w
    star C.stop         = stop
    star (C.more x₁ x₂) = more (toRx⇒ e x₁) (star x₂)

⇒toRx : ∀ {s} (e : Expr s) {w} → Wd e w → ⟦ toRx e ⟧ᴬ w
⇒toRx ε         m = ⇒unionRx (words ε) m
⇒toRx (ops A)   m = ⇒unionRx (words (ops A)) m
⇒toRx (str S e) m = ⇒unionRx (words (str S e)) m
⇒toRx (e ∣ f)   (inj₁ m) = inj₁ (⇒toRx e m)
⇒toRx (e ∣ f)   (inj₂ m) = inj₂ (⇒toRx f m)
⇒toRx (e · f)   (u , v , eq , x , y) = u , v , eq , ⇒toRx e x , ⇒toRx f y
⇒toRx (e *)     m = star m
  where
    star : ∀ {w} → StarW (Wd e) w → StarA ⟦ toRx e ⟧ᴬ w
    star stop         = C.stop
    star (more x₁ x₂) = C.more (⇒toRx e x₁) (star x₂)

-- a property of every letter of every word of each letter of an
-- expression holds of every letter of its regular expression

open import Data.List.Relation.Unary.All as All using (All)

private
  allWord : ∀ {s} {P : Letter (End s) → Set} (w : Word′ s) → All P w → AllLits P (wordRx w)
  allWord []      _          = _
  allWord (ℓ ∷ w) (p All.∷ ps) = p , allWord w ps

  allUnion : ∀ {s} {P : Letter (End s) → Set} (ws : List (Word′ s)) → All (All P) ws → AllLits P (unionRx ws)
  allUnion []       _          = _
  allUnion (w ∷ ws) (p All.∷ ps) = allWord w p , allUnion ws ps

-- the letters of an expression's own letters

Leaves : ∀ {s} → (Letter (End s) → Set) → Expr s → Set
Leaves P ε         = All (All P) (words ε)
Leaves P (ops A)   = All (All P) (words (ops A))
Leaves P (str S e) = All (All P) (words (str S e))
Leaves P (e ∣ f)   = Leaves P e × Leaves P f
Leaves P (e · f)   = Leaves P e × Leaves P f
Leaves P (e *)     = Leaves P e

allLits : ∀ {s} {P : Letter (End s) → Set} (e : Expr s) → Leaves P e → AllLits P (toRx e)
allLits ε         l = allUnion (words ε) l
allLits (ops A)   l = allUnion (words (ops A)) l
allLits (str S e) l = allUnion (words (str S e)) l
allLits (e ∣ f)   (l , l′) = allLits e l , allLits f l′
allLits (e · f)   (l , l′) = allLits e l , allLits f l′
allLits (e *)     l = allLits e l
