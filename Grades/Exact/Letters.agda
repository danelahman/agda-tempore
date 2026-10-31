------------------------------------------------------------------------
-- Words of one-sided interval letters, and their instances as pieces.--
--                                                                    --
-- A word of an instance is a sequence of letters: one operation, or  --
-- a stretch with a set of operations and an end of the instance. It  --
-- denotes the concatenations of instances of its letters. An         --
-- instance is described letter by letter by a list of pieces, each   --
-- a kind (the operation, or the set of the stretch) with a length:   --
-- `Shape v ps` says the pieces `ps` are admitted by the letters `v`, --
-- `WordOf ps x` that `x` is the exact word they make, a stretch of   --
-- length zero being no item at all.                                  --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Letters
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op) where

open import Data.Fin.Subset using (_∈_; _⊆_; ⁅_⁆)
open import Data.Fin.Subset.Properties using (_∈?_; _⊆?_; x∈⁅y⁆⇒x≡y; x∈⁅x⁆)
open import Data.List.Base using (List; []; _∷_; _++_; map; foldr)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Monus T using (Carrier; 0ᴰ; _+ᴰ_)
open import Grades.Durations.Intervals.Dense T using (_∈ⁱ_)

open import Grades.Exact.Base T Op n code code-injective
open import Grades.Exact.Lift T Op n code code-injective
open import Grades.Exact.Expression T Op n code code-injective running
  using (Instance; upper; lower; End; _∈ᵉ_; opsᴸ; strᴸ)
open import Grades.Exact.Pour T Op n code code-injective using (Adm)

open RunningTimes.RunningTimes running using (rt)

------------------------------------------------------------------------
-- Kinds of pieces, and what a stretch admits

data Kind : Set where
  opk : Op → Kind
  stk : OpSet → Kind

AdmK : Kind → OpSet → Set
AdmK (opk o)  S = code o ∈ S
AdmK (stk S′) S = S′ ⊆ S

AdmK? : ∀ k S → Dec (AdmK k S)
AdmK? (opk o)  S = code o ∈? S
AdmK? (stk S′) S = S′ ⊆? S

kind : Item → Kind
kind (op o _) = opk o
kind (st _ S) = stk S

adm-kind : ∀ i {S} → AdmK (kind i) S → Adm i S
adm-kind (op o d) a = a
adm-kind (st d S) a = a

kind-adm : ∀ i {S} → Adm i S → AdmK (kind i) S
kind-adm (op o d) a = a
kind-adm (st d S) a = a

------------------------------------------------------------------------
-- Letters and words

data Letter (L : Set) : Set where
  op : Op → Letter L
  st : OpSet → L → Letter L

Word′ : Instance → Set
Word′ s = List (Letter (End s))

⟦_⟧ˡ : ∀ {s} → Letter (End s) → Lang
⟦ op o   ⟧ˡ = opsᴸ ⁅ code o ⁆
⟦ st S e ⟧ˡ = strᴸ S e

⟦_⟧ʷ : ∀ {s} → Word′ s → Lang
⟦ []    ⟧ʷ = 𝟏ᴸ
⟦ ℓ ∷ v ⟧ʷ = ⟦ ℓ ⟧ˡ ·ᴸ ⟦ v ⟧ʷ

------------------------------------------------------------------------
-- Instances as pieces

Piece : Set → Set
Piece W = Kind × W

-- the pieces admitted by the letters, one to one

data Shape {s} : Word′ s → List (Piece Carrier) → Set where
  []  : Shape [] []
  op  : ∀ {o τ v ps} → Shape v ps → Shape (op o ∷ v) ((opk o , τ) ∷ ps)
  st  : ∀ {S e τ v ps} → τ ∈ᵉ e → Shape v ps → Shape (st S e ∷ v) ((stk S , τ) ∷ ps)

-- the exact word the pieces make; operations run for a time their
-- running-time interval admits

data WordOf : List (Piece Carrier) → Word → Set where
  []  : WordOf [] []
  op  : ∀ {o d ps x} → ∣ d ∣⁺ ∈ⁱ rt o → WordOf ps x
      → WordOf ((opk o , ∣ d ∣⁺) ∷ ps) (op o d ∷ x)
  st  : ∀ {S τ ps x} → WordOf ps x → WordOf ((stk S , τ) ∷ ps) (stretch S τ ++ x)

Inst : ∀ {s} → Word → Word′ s → Set
Inst y v = Σ[ ps ∈ List (Piece Carrier) ] Shape v ps × WordOf ps y

-- the instances are the words of the language

inst-⟦⟧ : ∀ {s} {y} (v : Word′ s) → Inst y v → ⟦ v ⟧ʷ y
inst-⟦⟧ [] (_ , [] , []) = refl
inst-⟦⟧ (op o ∷ v) (_ , op sh , op {d = d} r wo) =
  op o d ∷ [] , _ , refl , (o , d , x∈⁅x⁆ (code o) , r , refl) , inst-⟦⟧ v (_ , sh , wo)
inst-⟦⟧ (st S e ∷ v) (_ , st {τ = τ} a sh , st wo) =
  stretch S τ , _ , refl , (τ , a , refl) , inst-⟦⟧ v (_ , sh , wo)

⟦⟧-inst : ∀ {s} {y} (v : Word′ s) → ⟦ v ⟧ʷ y → Inst y v
⟦⟧-inst [] refl = [] , [] , []
⟦⟧-inst (op o ∷ v) (_ , y , refl , (o′ , d , c , r , refl) , y∈) with code-injective (x∈⁅y⁆⇒x≡y (code o) c)
... | refl with ⟦⟧-inst v y∈
...   | ps , sh , wo = (opk o , ∣ d ∣⁺) ∷ ps , op sh , op r wo
⟦⟧-inst (st S e ∷ v) (_ , y , refl , (τ , a , refl) , y∈) with ⟦⟧-inst v y∈
... | ps , sh , wo = (stk S , τ) ∷ ps , st a sh , st wo

-- the pieces of an exact word, one for each item

pieces : Word → List (Piece Carrier)
pieces = map (λ i → kind i , len i)

-- the total length of pieces

sumᴰ : List Carrier → Carrier
sumᴰ = foldr _+ᴰ_ 0ᴰ

amts : List (Piece Carrier) → List Carrier
amts = map proj₂
  where open import Data.Product using (proj₂)
