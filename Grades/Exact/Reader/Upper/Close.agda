-------------------------------------------------------------------------
-- Closing the bounds of an upper run.                                 --
--                                                                     --
-- On an exact run, an accepting upper run against any bounds is also  --
-- an accepting run against closed bounds within them: a bound with no --
-- end is closed past every sum the run could compare against it, and  --
-- an open end close enough below itself that every comparison the     --
-- run could make keeps its outcome. The comparisons are finitely      --
-- many (the sums of infixes of the run against the sums of            --
-- subsequences of the bounds), and density supplies the closed ends.  --
-------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain; Dense)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Exact.Reader.Upper.Close
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_; map; foldr; [_])
open import Data.List.Properties using (++-assoc; map-++; ∷-injectiveˡ; ∷-injectiveʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T
  using (Cut; Hi; fin; ∞; _⊑ʰ_; ⁺; ⁻; 0⁺; _+ʰ_; ⊑⇒≤; ≤⇒⁺⊑⁺; by-pt; by-side;
         ⊑ʰ-trans; ⊑ʰ-∞; +ʰ-mono; +ʰ-monoʳ; +ʰ-identityʳ; +ʰ-inflate; ⊑ʰ-refl)
  renaming (_∣_ to _∣ᶜ_)

open import Grades.Durations.Intervals.Dense T using (⊑⁻⇒<)
open import Grades.Exact.Letters T Op n code code-injective running
open import Grades.Exact.Positions T Op n code code-injective running using (amts-++)
open import Grades.Exact.Reader.Transfer T Op n code code-injective running
open import Grades.Exact.Reader.Upper T Op n code code-injective running
open import Grades.Exact.Reader.Upper.Read T Op n code code-injective running
  using (cancel-cl)

private
  π₁ = proj₁
  π₂ = proj₂

  variable
    a b c : Carrier

  ≮⇒≥ : ¬ (a <ᴰ b) → b ≤ᴰ a
  ≮⇒≥ {a} {b} ¬p with b ≤ᴰ? a
  ... | yes r = r
  ... | no ¬r = ⊥-elim (¬p ¬r)

------------------------------------------------------------------------
-- Lists of values

maxL : List Carrier → Carrier
maxL = foldr _⊔ᴰ_ 0ᴰ

∈-maxL : ∀ {x xs} → x ∈ xs → x ≤ᴰ maxL xs
∈-maxL {x} {.x ∷ xs} (here refl) = ⊔-ubˡ x (maxL xs)
∈-maxL {x} {y ∷ xs}  (there m)   = ≤ᴰ-trans (∈-maxL m) (⊔-ubʳ y (maxL xs))

maxL-< : ∀ {c} xs → (∀ {x} → x ∈ xs → x <ᴰ c) → 0ᴰ <ᴰ c → maxL xs <ᴰ c
maxL-< []       h z = z
maxL-< {c} (x ∷ xs) h z with x ≤ᴰ? maxL xs
... | yes _ = maxL-< xs (λ m → h (there m)) z
... | no _  = h (here refl)

-- the sums of the subsequences of a list of bounds

subsums : List Hi → List Hi
subsums []       = fin 0⁺ ∷ []
subsums (h ∷ hs) = subsums hs ++ map (h +ʰ_) (subsums hs)

sub-∈ : ∀ {cs hs} → Sub cs hs → sumʰ cs ∈ subsums hs
sub-∈ []       = here refl
sub-∈ {h ∷ cs} {.h ∷ hs} (keep s) = ∈-++⁺ʳ (subsums hs) (∈-map⁺ (h +ʰ_) (sub-∈ s))
sub-∈ {cs} {h ∷ hs} (drop s) = ∈-++⁺ˡ (sub-∈ s)

-- the sums of the infixes of a list of lengths

prefixSums infixSums : List Carrier → List Carrier
prefixSums []       = 0ᴰ ∷ []
prefixSums (a ∷ as) = 0ᴰ ∷ map (a +ᴰ_) (prefixSums as)
infixSums []       = 0ᴰ ∷ []
infixSums (a ∷ as) = prefixSums (a ∷ as) ++ infixSums as

prefix-∈ : ∀ pre b {xs} → pre ++ b ≡ xs → sumᴰ pre ∈ prefixSums xs
prefix-∈ []        b {[]}     e = here refl
prefix-∈ []        b {_ ∷ _}  e = here refl
prefix-∈ (p ∷ pre) b {x ∷ xs} refl = there (∈-map⁺ (p +ᴰ_) (prefix-∈ pre b refl))

infix-∈ : ∀ a pre b {xs} → a ++ pre ++ b ≡ xs → sumᴰ pre ∈ infixSums xs
infix-∈ [] pre b {[]} e with pre
... | [] = here refl
infix-∈ [] pre b {x ∷ xs} e = ∈-++⁺ˡ (prefix-∈ pre b e)
infix-∈ (a ∷ as) pre b {x ∷ xs} refl = ∈-++⁺ʳ (prefixSums (a ∷ _)) (infix-∈ as pre b refl)

------------------------------------------------------------------------
-- Upper ends

-- every bound admits zero

Valid : List (Letter Hi) → Set
Valid []           = ⊤
Valid (op _ ∷ v)   = Valid v
Valid (st _ h ∷ v) = fin 0⁺ ⊑ʰ h × Valid v

private
  -- a closed end below an open one lies strictly below its point
  ⁺⊑⁻ : ∀ {a b} → fin (a ∣ᶜ ⁺) ⊑ʰ fin (b ∣ᶜ ⁻) → a <ᴰ b
  ⁺⊑⁻ r = ⊑⁻⇒< r refl

  All0 : List Hi → Set
  All0 []       = ⊤
  All0 (c ∷ cs) = fin 0⁺ ⊑ʰ c × All0 cs

  sum-0 : ∀ cs → All0 cs → fin 0⁺ ⊑ʰ sumʰ cs
  sum-0 []       _        = ⊑ʰ-refl
  sum-0 (c ∷ cs) (z , zs) = subst (_⊑ʰ c +ʰ sumʰ cs) (+ʰ-identityʳ (fin 0⁺)) (+ʰ-mono z (sum-0 cs zs))

  all0-sub : ∀ {cs ds : List (Hi × Hi)} → Sub cs ds → All0 (map π₂ ds) → All0 (map π₂ cs)
  all0-sub []       _        = tt
  all0-sub (keep s) (z , zs) = z , all0-sub s zs
  all0-sub (drop s) (_ , zs) = all0-sub s zs

  All : ∀ {A : Set} → (A → Set) → List A → Set
  All P []       = ⊤
  All P (x ∷ xs) = P x × All P xs

  sum-mono : ∀ {cs : List (Hi × Hi)} → All (λ c → π₂ c ⊑ʰ π₁ c) cs → sumʰ (map π₂ cs) ⊑ʰ sumʰ (map π₁ cs)
  sum-mono {[]}     _        = ⊑ʰ-refl
  sum-mono {c ∷ cs} (r , rs) = +ʰ-mono r (sum-mono rs)

  all-sub : ∀ {A : Set} {P : A → Set} {cs ds} → Sub cs ds → All P ds → All P cs
  all-sub []       _        = tt
  all-sub (keep s) (z , zs) = z , all-sub s zs
  all-sub (drop s) (_ , zs) = all-sub s zs

  -- the closed reading of a sum past a closed part
  cl-split : ∀ {ψ X} → ψ ≤ᴰ X → cl X ≡ cl ψ +ʰ cl (X ∸ᴰ ψ)
  cl-split {ψ} {X} r = cong cl (sym (+-∸ r))

------------------------------------------------------------------------
-- Choosing a closed end within each bound

-- the closed end chosen for a bound, against the sums `Xs` and the
-- subsequence sums `Ss` of the later bounds

data Pick (h : Hi) (Ss : List Hi) (Xs : List Carrier) (ψ : Carrier) : Set where
  pick : cl ψ ⊑ʰ h
       → (∀ {X S} → X ∈ Xs → ψ <ᴰ X → S ∈ Ss → cl X ⊑ʰ h +ʰ S → cl (X ∸ᴰ ψ) ⊑ʰ S)
       → Pick h Ss Xs ψ

private
  -- the values an open end must stay above
  cands : Carrier → List Carrier → List Hi → List Carrier
  cand  : Carrier → Carrier → Hi → List Carrier
  cand c X ∞ = []
  cand c X (fin (s ∣ᶜ t)) with X <ᴰ? c +ᴰ s
  ... | yes _ = X ∸ᴰ s ∷ []
  ... | no _  = []
  cands c []       Ss = []
  cands c (X ∷ Xs) Ss = foldr (λ S r → cand c X S ++ r) [] Ss ++ cands c Xs Ss

  cand-∈ : ∀ {c X s t} → X <ᴰ c +ᴰ s → X ∸ᴰ s ∈ cand c X (fin (s ∣ᶜ t))
  cand-∈ {c} {X} {s} r with X <ᴰ? c +ᴰ s
  ... | yes _ = here refl
  ... | no ¬r = ⊥-elim (¬r r)

  cand-< : ∀ {c X S y} → 0ᴰ <ᴰ c → y ∈ cand c X S → y <ᴰ c
  cand-< {c} {X} {∞} _ ()
  cand-< {c} {X} {fin (s ∣ᶜ t)} z m with X <ᴰ? c +ᴰ s
  cand-< {c} {X} {fin (s ∣ᶜ t)} z (here refl) | yes r = case (s ≤ᴰ? X)
    where
      case : Dec (s ≤ᴰ X) → X ∸ᴰ s <ᴰ c
      case (yes sX) = λ w → r (≤ᴰ-trans (+ᴰ-monoˡ-≤ s w) (≤ᴰ-reflexive (∸-+ sX)))
      case (no ¬sX) = subst (_<ᴰ c) (sym (∸-≰ ¬sX)) z
  cand-< {c} {X} {fin (s ∣ᶜ t)} z () | no _

  inner-∈ : ∀ {c X S y} Ss → S ∈ Ss → y ∈ cand c X S → y ∈ foldr (λ S r → cand c X S ++ r) [] Ss
  inner-∈ (S ∷ Ss) (here refl) m = ∈-++⁺ˡ m
  inner-∈ {c} {X} (S′ ∷ Ss) (there s) m = ∈-++⁺ʳ (cand c X S′) (inner-∈ Ss s m)

  inner-< : ∀ {c X y} → 0ᴰ <ᴰ c → ∀ Ss → y ∈ foldr (λ S r → cand c X S ++ r) [] Ss → y <ᴰ c
  inner-< {c} {X} z (S ∷ Ss) m with ∈-++⁻ (cand c X S) m
  ... | inj₁ m′ = cand-< {S = S} z m′
  ... | inj₂ m′ = inner-< z Ss m′

  cands-∈ : ∀ {c X S} Xs Ss → X ∈ Xs → S ∈ Ss → ∀ {y} → y ∈ cand c X S → y ∈ cands c Xs Ss
  cands-∈ (X ∷ Xs) Ss (here refl) s m = ∈-++⁺ˡ (inner-∈ Ss s m)
  cands-∈ {c} (X′ ∷ Xs) Ss (there x) s m = ∈-++⁺ʳ (foldr (λ S r → cand c X′ S ++ r) [] Ss) (cands-∈ Xs Ss x s m)

  cands-< : ∀ {c y} → 0ᴰ <ᴰ c → ∀ Xs Ss → y ∈ cands c Xs Ss → y <ᴰ c
  cands-< {c} z (X ∷ Xs) Ss m with ∈-++⁻ (foldr (λ S r → cand c X S ++ r) [] Ss) m
  ... | inj₁ m′ = inner-< z Ss m′
  ... | inj₂ m′ = cands-< z Xs Ss m′

choose-end : ∀ h Ss Xs → fin 0⁺ ⊑ʰ h → Σ[ ψ ∈ Carrier ] Pick h Ss Xs ψ
choose-end ∞ Ss Xs _ =
  maxL Xs , pick tt (λ x r _ _ → ⊥-elim (r (∈-maxL x)))
choose-end (fin (c ∣ᶜ ⁺)) Ss Xs _ =
  c , pick ⊑ʰ-refl (λ {X} {S} x r s t → cancel-cl c (subst (_⊑ʰ fin (c ∣ᶜ ⁺) +ʰ S) (cl-split (<⇒≤ r)) t))
choose-end (fin (c ∣ᶜ ⁻)) Ss Xs z with dense (maxL-< (cands c Xs Ss) (cands-< (⁺⊑⁻ z) Xs Ss) (⁺⊑⁻ z))
... | ψ , m<ψ , ψ<c = ψ , pick (by-pt ψ<c) below
  where
    below : ∀ {X S} → X ∈ Xs → ψ <ᴰ X → S ∈ Ss → cl X ⊑ʰ fin (c ∣ᶜ ⁻) +ʰ S → cl (X ∸ᴰ ψ) ⊑ʰ S
    below {X} {∞} x r s t = tt
    below {X} {fin (s′ ∣ᶜ t′)} x r s t = by-pt X∸ψ<s
      where
        X<cs : X <ᴰ c +ᴰ s′
        X<cs = ⁺⊑⁻ t
        X∸s<ψ : X ∸ᴰ s′ <ᴰ ψ
        X∸s<ψ = ≤-<-trans (∈-maxL (cands-∈ Xs Ss x s (cand-∈ {t = t′} X<cs))) m<ψ
        X∸ψ<s : X ∸ᴰ ψ <ᴰ s′
        X∸ψ<s le = X∸s<ψ (+-≤-∸ (≤ᴰ-trans (≤ᴰ-+ s′ ψ) sψ≤X) sψ≤X)
          where
            sψ≤X : s′ +ᴰ ψ ≤ᴰ X
            sψ≤X = ≤ᴰ-trans (+ᴰ-monoˡ-≤ ψ le) (≤ᴰ-reflexive (∸-+ (<⇒≤ r)))

------------------------------------------------------------------------
-- Closed ends for all the bounds of a word

-- the closed ends lie within the bounds

data Within : List (Letter Carrier) → List (Letter Hi) → Set where
  []  : Within [] []
  op  : ∀ {o vc v} → Within vc v → Within (op o ∷ vc) (op o ∷ v)
  st  : ∀ {S ψ h vc v} → cl ψ ⊑ʰ h → Within vc v → Within (st S ψ ∷ vc) (st S h ∷ v)

private
  capsˡ : ∀ {L L′} (f : L → L′) v → capsOf (map (mapˡ f) v) ≡ map f (capsOf v)
  capsˡ f []           = refl
  capsˡ f (op _ ∷ v)   = capsˡ f v
  capsˡ f (st _ c ∷ v) = cong (f c ∷_) (capsˡ f v)

  sub-map : ∀ {A B : Set} (f : A → B) {xs ys} → Sub xs ys → Sub (map f xs) (map f ys)
  sub-map f []       = []
  sub-map f (keep s) = keep (sub-map f s)
  sub-map f (drop s) = drop (sub-map f s)

Good : List (Letter (Hi × Hi)) → List Carrier → Set
Good vz Xs = ∀ cs → Sub cs (capsOf vz) → ∀ {X} → X ∈ Xs
           → cl X ⊑ʰ sumʰ (map π₁ cs) → cl X ⊑ʰ sumʰ (map π₂ cs)

record Choice (v : List (Letter Hi)) (Xs : List Carrier) : Set where
  field
    vz     : List (Letter (Hi × Hi))
    first  : map (mapˡ π₁) vz ≡ v
    vc     : List (Letter Carrier)
    second : map (mapˡ π₂) vz ≡ map clo vc
    within : Within vc v
    below  : All (λ c → π₂ c ⊑ʰ π₁ c) (capsOf vz)
    zeros  : All0 (map π₂ (capsOf vz))
    good   : Good vz Xs

choose : ∀ v → Valid v → ∀ Xs → Choice v Xs
choose [] _ Xs = record
  { vz = [] ; first = refl ; vc = [] ; second = refl ; within = []
  ; below = tt ; zeros = tt ; good = λ { [] [] x t → t } }
choose (op o ∷ v) val Xs with choose v val Xs
... | ch = record
  { vz = op o ∷ C.vz ; first = cong (op o ∷_) C.first ; vc = op o ∷ C.vc
  ; second = cong (op o ∷_) C.second ; within = op C.within
  ; below = C.below ; zeros = C.zeros ; good = C.good }
  where module C = Choice ch
choose (st S h ∷ v) (vh , val) Xs with choose-end h (subsums (capsOf v)) Xs vh
... | ψ , pick ψh bel with choose v val (Xs ++ map (_∸ᴰ ψ) Xs)
...   | ch = record
  { vz = st S (h , cl ψ) ∷ C.vz ; first = cong (st S h ∷_) C.first
  ; vc = st S ψ ∷ C.vc ; second = cong (st S (cl ψ) ∷_) C.second
  ; within = st ψh C.within
  ; below = ψh , C.below ; zeros = ≤⇒⁺⊑⁺ (0ᴰ-least ψ) , C.zeros
  ; good = good }
  where
    module C = Choice ch
    good : Good (st S (h , cl ψ) ∷ C.vz) Xs
    good cs (drop s) x t = C.good cs s (∈-++⁺ˡ x) t
    good (.(h , cl ψ) ∷ cs) (keep s) {X} x t with ψ <ᴰ? X
    ... | no ¬r =
      ⊑ʰ-trans (≤⇒⁺⊑⁺ (≮⇒≥ ¬r))
               (+ʰ-inflate (cl ψ) (sum-0 (map π₂ cs) (all0-sub s C.zeros)))
    ... | yes r =
      subst (_⊑ʰ cl ψ +ʰ sumʰ (map π₂ cs)) (sym (cl-split (<⇒≤ r)))
        (+ʰ-monoʳ (cl ψ)
          (C.good cs s (∈-++⁺ʳ Xs (∈-map⁺ (_∸ᴰ ψ) x))
             (bel x r (subst (λ z → sumʰ (map π₁ cs) ∈ subsums z)
                         (trans (sym (capsˡ π₁ C.vz)) (cong capsOf C.first))
                         (sub-∈ (sub-map π₁ s))) t)))

------------------------------------------------------------------------
-- An upper run on an exact run is a run against closed bounds within
-- the given ones

private
  diag : ∀ {A : Set} → A → A × A
  diag a = a , a

  map-π-diag₁ : ∀ {A : Set} (xs : List A) → map π₁ (map diag xs) ≡ xs
  map-π-diag₁ []       = refl
  map-π-diag₁ (x ∷ xs) = cong (x ∷_) (map-π-diag₁ xs)

  map-π-diag₂ : ∀ {A : Set} (xs : List A) → map π₂ (map diag xs) ≡ xs
  map-π-diag₂ []       = refl
  map-π-diag₂ (x ∷ xs) = cong (x ∷_) (map-π-diag₂ xs)

  -- an infix of a mapped list is the map of an infix
  infix-map : ∀ {A B : Set} (f : A → B) a pre b xs → a ++ pre ++ b ≡ map f xs
            → Σ[ a′ ∈ List A ] Σ[ pre′ ∈ List A ] Σ[ b′ ∈ List A ]
                a′ ++ pre′ ++ b′ ≡ xs × pre ≡ map f pre′
  prefix-map : ∀ {A B : Set} (f : A → B) pre b xs → pre ++ b ≡ map f xs
             → Σ[ pre′ ∈ List A ] Σ[ b′ ∈ List A ] pre′ ++ b′ ≡ xs × pre ≡ map f pre′
  prefix-map f []        b xs       e = [] , xs , refl , refl
  prefix-map f (p ∷ pre) b (x ∷ xs) e with prefix-map f pre b xs (∷-injectiveʳ e) | ∷-injectiveˡ e
  ... | pre′ , b′ , refl , refl | refl = x ∷ pre′ , b′ , refl , refl

  infix-map f []       pre b xs e with prefix-map f pre b xs e
  ... | pre′ , b′ , e′ , e″ = [] , pre′ , b′ , e′ , e″
  infix-map f (a ∷ as) pre b (x ∷ xs) e with infix-map f as pre b xs (∷-injectiveʳ e)
  ... | a′ , pre′ , b′ , refl , refl = x ∷ a′ , pre′ , b′ , refl , refl

  diag-π : ∀ {A : Set} a (z : A × A) b xs → a ++ z ∷ b ≡ map diag xs → π₁ z ≡ π₂ z
  diag-π []      z b (x ∷ xs) e with ∷-injectiveˡ e
  ... | refl = refl
  diag-π (_ ∷ a) z b (x ∷ xs) e = diag-π a z b xs (∷-injectiveʳ e)

closeᵁ : ∀ cps v → Valid v → RunU (map toHi cps) v
       → Σ[ vc ∈ List (Letter Carrier) ] Within vc v × RunU (map toHi cps) (map clo vc)
closeᵁ cps v val r = C.vc , C.within , result
  where
    Xs = infixSums (amts cps)
    ch = choose v val Xs
    module C = Choice ch
    zs₀ = map diag (map toHi cps)

    agree : ∀ a pre b cs → a ++ pre ++ b ≡ zs₀ → Sub cs (capsOf C.vz)
          → Fitsᵁ (map π₁ pre) (map π₁ cs) ⇔ Fitsᵁ (map π₂ pre) (map π₂ cs)
    agree a pre b cs e s with infix-map diag a pre b (map toHi cps) e
    ... | a′ , pre′ , b′ , e′ , refl with infix-map toHi a′ pre′ b′ cps e′
    ...   | a″ , pre″ , b″ , e″ , refl =
      mk⇔ (λ t → subst (λ P → Fitsᵁ P (map π₂ cs)) (sym (map-π-diag₂ (map toHi pre″)))
                  (subst (_⊑ʰ sumʰ (map π₂ cs)) (sym (sum-toHi pre″))
                    (C.good cs s X∈
                      (subst (_⊑ʰ sumʰ (map π₁ cs)) (sum-toHi pre″)
                        (subst (λ P → Fitsᵁ P (map π₁ cs)) (map-π-diag₁ (map toHi pre″)) t)))))
          (λ t → subst (λ P → Fitsᵁ P (map π₁ cs)) (sym (map-π-diag₁ (map toHi pre″)))
                  (⊑ʰ-trans (subst (λ P → Fitsᵁ P (map π₂ cs)) (map-π-diag₂ (map toHi pre″)) t)
                            (sum-mono (all-sub s C.below))))
      where
        X∈ : sumᴰ (amts pre″) ∈ Xs
        X∈ = infix-∈ (amts a″) (amts pre″) (amts b″)
               (trans (cong (amts a″ ++_) (sym (amts-++ pre″ b″)))
                 (trans (sym (amts-++ a″ (pre″ ++ b″))) (cong amts e″)))

    kinds : ∀ a z b → a ++ z ∷ b ≡ zs₀ → proj₁ (π₁ z) ≡ proj₁ (π₂ z)
    kinds a z b e = cong proj₁ (diag-π a z b (map toHi cps) e)

    module A = Agree proj₁ Fitsᵁ zs₀ C.vz kinds agree

    result : RunU (map toHi cps) (map clo C.vc)
    result = subst₂ RunU (map-π-diag₂ (map toHi cps)) C.second
               (Equivalence.to A.agreeᵁ
                 (subst₂ RunU (sym (map-π-diag₁ (map toHi cps))) (sym C.first) r))
