------------------------------------------------------------------------
-- Closing the bounds of a lower run.                                 --
--                                                                    --
-- On an exact run, an accepting lower run against any bounds is also --
-- an accepting run against closed bounds within them: an open end is --
-- closed just above itself, close enough that every comparison the   --
-- run could make keeps its outcome.                                  --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain; Dense)
import Syntax.Grades.Traces.RunningTimes as RunningTimes
import Syntax.Durations.Monus as Monus

module Syntax.Grades.Exact.Reader.Lower.Close
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_; map; foldr; [_])
open import Data.List.Properties using (++-assoc; map-++; ∷-injectiveˡ; ∷-injectiveʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Monus T
open import Syntax.Durations.Intervals T
  using (Cut; ⁺; ⁻; 0⁻; _+ˡ_; ⊑⇒≤; ≤⇒⁻⊑⁻; by-pt; by-side; ⁻≤; ⁺≤⁺;
         +ˡ-monoˡ; +ˡ-monoʳ; +ˡ-identityʳ)
  renaming (_∣_ to _∣ᶜ_; _⊑_ to _⊑ᶜ_; ⊑-refl to ⊑ᶜ-refl; ⊑-trans to ⊑ᶜ-trans)
open import Syntax.Durations.Intervals.Dense T using (⊑⁻⇒<)

open import Syntax.Grades.Exact.Letters T Op n code code-injective running
open import Syntax.Grades.Exact.Positions T Op n code code-injective running using (amts-++)
open import Syntax.Grades.Exact.Reader.Transfer T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Lower T Op n code code-injective running
open import Syntax.Grades.Exact.Reader.Lower.Read T Op n code code-injective running
  using (cancel-cl⁻)
open import Syntax.Grades.Exact.Reader.Upper.Close T Op n code code-injective running dense
  using (infixSums; infix-∈)

private
  π₁ = proj₁
  π₂ = proj₂

------------------------------------------------------------------------
-- Lists of values

minFrom : Carrier → List Carrier → Carrier
minFrom = foldr _⊓ᴰ_

∈-minFrom : ∀ {d x xs} → x ∈ xs → minFrom d xs ≤ᴰ x
∈-minFrom {d} {x} {.x ∷ xs} (here refl) = ⊓-lbˡ x (minFrom d xs)
∈-minFrom {d} {x} {y ∷ xs}  (there m)   = ≤ᴰ-trans (⊓-lbʳ y (minFrom d xs)) (∈-minFrom m)

minFrom-> : ∀ {c d} xs → (∀ {x} → x ∈ xs → c <ᴰ x) → c <ᴰ d → c <ᴰ minFrom d xs
minFrom-> []       h z = z
minFrom-> {c} {d} (x ∷ xs) h z with x ≤ᴰ? minFrom d xs
... | yes _ = h (here refl)
... | no _  = minFrom-> xs (λ m → h (there m)) z

subsumsˡ : List Cut → List Cut
subsumsˡ []       = 0⁻ ∷ []
subsumsˡ (c ∷ cs) = subsumsˡ cs ++ map (c +ˡ_) (subsumsˡ cs)

sub-∈ˡ : ∀ {cs hs} → Sub cs hs → sumˡ cs ∈ subsumsˡ hs
sub-∈ˡ []       = here refl
sub-∈ˡ {h ∷ cs} {.h ∷ hs} (keep s) = ∈-++⁺ʳ (subsumsˡ hs) (∈-map⁺ (h +ˡ_) (sub-∈ˡ s))
sub-∈ˡ {cs} {h ∷ hs} (drop s) = ∈-++⁺ˡ (sub-∈ˡ s)

------------------------------------------------------------------------
-- Choosing a closed end above each bound

data Pickˡ (c : Cut) (Ss : List Cut) (Xs : List Carrier) (ψ : Carrier) : Set where
  pick : c ⊑ᶜ cl⁻ ψ
       → (∀ {X S} → X ∈ Xs → S ∈ Ss → c +ˡ S ⊑ᶜ cl⁻ X → ψ ≤ᴰ X × S ⊑ᶜ cl⁻ (X ∸ᴰ ψ))
       → Pickˡ c Ss Xs ψ

private
  -- the values an open end must stay below
  cand : Carrier → Carrier → Cut → List Carrier
  cand p X (s ∣ᶜ u) with p +ᴰ s <ᴰ? X
  ... | yes _ = X ∸ᴰ s ∷ []
  ... | no _  = []

  cands : Carrier → List Carrier → List Cut → List Carrier
  cands p []       Ss = []
  cands p (X ∷ Xs) Ss = foldr (λ S r → cand p X S ++ r) [] Ss ++ cands p Xs Ss

  cand-∈ : ∀ {p X s u} → p +ᴰ s <ᴰ X → X ∸ᴰ s ∈ cand p X (s ∣ᶜ u)
  cand-∈ {p} {X} {s} r with p +ᴰ s <ᴰ? X
  ... | yes _ = here refl
  ... | no ¬r = ⊥-elim (¬r r)

  cand-> : ∀ {p X S y} → y ∈ cand p X S → p <ᴰ y
  cand-> {p} {X} {s ∣ᶜ u} m with p +ᴰ s <ᴰ? X
  cand-> {p} {X} {s ∣ᶜ u} (here refl) | yes r =
    λ le → r (≤ᴰ-trans (≤-+-∸ X s) (≤ᴰ-trans (+ᴰ-monoʳ-≤ s le) (≤ᴰ-reflexive (+ᴰ-comm s p))))
  cand-> {p} {X} {s ∣ᶜ u} () | no _

  inner-∈ : ∀ {p X S y} Ss → S ∈ Ss → y ∈ cand p X S → y ∈ foldr (λ S r → cand p X S ++ r) [] Ss
  inner-∈ (S ∷ Ss) (here refl) m = ∈-++⁺ˡ m
  inner-∈ {p} {X} (S′ ∷ Ss) (there s) m = ∈-++⁺ʳ (cand p X S′) (inner-∈ Ss s m)

  inner-> : ∀ {p X y} Ss → y ∈ foldr (λ S r → cand p X S ++ r) [] Ss → p <ᴰ y
  inner-> {p} {X} (S ∷ Ss) m with ∈-++⁻ (cand p X S) m
  ... | inj₁ m′ = cand-> {S = S} m′
  ... | inj₂ m′ = inner-> Ss m′

  cands-∈ : ∀ {p X S} Xs Ss → X ∈ Xs → S ∈ Ss → ∀ {y} → y ∈ cand p X S → y ∈ cands p Xs Ss
  cands-∈ (X ∷ Xs) Ss (here refl) s m = ∈-++⁺ˡ (inner-∈ Ss s m)
  cands-∈ {p} (X′ ∷ Xs) Ss (there x) s m =
    ∈-++⁺ʳ (foldr (λ S r → cand p X′ S ++ r) [] Ss) (cands-∈ Xs Ss x s m)

  cands-> : ∀ {p y} Xs Ss → y ∈ cands p Xs Ss → p <ᴰ y
  cands-> {p} (X ∷ Xs) Ss m with ∈-++⁻ (foldr (λ S r → cand p X S ++ r) [] Ss) m
  ... | inj₁ m′ = inner-> Ss m′
  ... | inj₂ m′ = cands-> Xs Ss m′

  -- a closed end at a point, and what it leaves
  cl⁻-split : ∀ {ψ X} → ψ ≤ᴰ X → cl⁻ X ≡ cl⁻ ψ +ˡ cl⁻ (X ∸ᴰ ψ)
  cl⁻-split r = cong cl⁻ (sym (+-∸ r))

  pt≤ : ∀ {p s S X} → (p ∣ᶜ s) +ˡ S ⊑ᶜ cl⁻ X → p ≤ᴰ X
  pt≤ {p} {s} {q ∣ᶜ t} {X} r = ≤ᴰ-trans (≤ᴰ-+ p q) (⊑⇒≤ r)

choose-endˡ : ∀ c Ss Xs → Σ[ ψ ∈ Carrier ] Pickˡ c Ss Xs ψ
choose-endˡ (p ∣ᶜ ⁻) Ss Xs =
  p , pick ⊑ᶜ-refl (λ {X} {S} x s t →
    pt≤ {p} {⁻} {S} t , cancel-cl⁻ p (subst ((p ∣ᶜ ⁻) +ˡ S ⊑ᶜ_) (cl⁻-split (pt≤ {p} {⁻} {S} t)) t))
choose-endˡ (p ∣ᶜ ⁺) Ss Xs
  with dense (minFrom-> (cands p Xs Ss) (cands-> Xs Ss) (<-+ κ-pos))
... | ψ , p<ψ , ψ<m = ψ , pick (by-pt p<ψ) above
  where
    above : ∀ {X S} → X ∈ Xs → S ∈ Ss → (p ∣ᶜ ⁺) +ˡ S ⊑ᶜ cl⁻ X → ψ ≤ᴰ X × S ⊑ᶜ cl⁻ (X ∸ᴰ ψ)
    above {X} {s ∣ᶜ u} x m t = <⇒≤ ψ<X , by-pt s<X∸ψ
      where
        ps<X : p +ᴰ s <ᴰ X
        ps<X = ⊑⁻⇒< t refl
        ψ<X∸s : ψ <ᴰ X ∸ᴰ s
        ψ<X∸s = <-≤-trans ψ<m (∈-minFrom (cands-∈ Xs Ss x m (cand-∈ {u = u} ps<X)))
        s≤X : s ≤ᴰ X
        s≤X = ≤ᴰ-trans (≤ᴰ-+ˡ s p) (<⇒≤ ps<X)
        ψ<X : ψ <ᴰ X
        ψ<X = <-≤-trans ψ<X∸s (∸-≤-self X s)
        s<X∸ψ : s <ᴰ X ∸ᴰ ψ
        s<X∸ψ le = ψ<X∸s (∸-≤-+ (≤ᴰ-trans (≤ᴰ-reflexive (sym (+-∸ (<⇒≤ ψ<X))))
                                (≤ᴰ-trans (+ᴰ-monoʳ-≤ ψ le) (≤ᴰ-reflexive (+ᴰ-comm ψ s)))))

------------------------------------------------------------------------
-- Closed ends for all the bounds of a word

data Withinˡ : List (Letter Carrier) → List (Letter Cut) → Set where
  []  : Withinˡ [] []
  op  : ∀ {o vc v} → Withinˡ vc v → Withinˡ (op o ∷ vc) (op o ∷ v)
  st  : ∀ {S ψ c vc v} → c ⊑ᶜ cl⁻ ψ → Withinˡ vc v → Withinˡ (st S ψ ∷ vc) (st S c ∷ v)

private
  All : ∀ {A : Set} → (A → Set) → List A → Set
  All P []       = ⊤
  All P (x ∷ xs) = P x × All P xs

  all-sub : ∀ {A : Set} {P : A → Set} {cs ds} → Sub cs ds → All P ds → All P cs
  all-sub []       _        = tt
  all-sub (keep s) (z , zs) = z , all-sub s zs
  all-sub (drop s) (_ , zs) = all-sub s zs

  sum-mono : ∀ {cs : List (Cut × Cut)} → All (λ c → π₁ c ⊑ᶜ π₂ c) cs → sumˡ (map π₁ cs) ⊑ᶜ sumˡ (map π₂ cs)
  sum-mono {[]}     _        = ⊑ᶜ-refl
  sum-mono {c ∷ cs} (r , rs) = ⊑ᶜ-trans (+ˡ-monoˡ (sumˡ (map π₁ cs)) r) (+ˡ-monoʳ (π₂ c) (sum-mono rs))

  capsˡ : ∀ {L L′} (f : L → L′) v → capsOf (map (mapˡ f) v) ≡ map f (capsOf v)
  capsˡ f []           = refl
  capsˡ f (op _ ∷ v)   = capsˡ f v
  capsˡ f (st _ c ∷ v) = cong (f c ∷_) (capsˡ f v)

  sub-map : ∀ {A B : Set} (f : A → B) {xs ys} → Sub xs ys → Sub (map f xs) (map f ys)
  sub-map f []       = []
  sub-map f (keep s) = keep (sub-map f s)
  sub-map f (drop s) = drop (sub-map f s)

Goodˡ : List (Letter (Cut × Cut)) → List Carrier → Set
Goodˡ vz Xs = ∀ cs → Sub cs (capsOf vz) → ∀ {X} → X ∈ Xs
            → sumˡ (map π₁ cs) ⊑ᶜ cl⁻ X → sumˡ (map π₂ cs) ⊑ᶜ cl⁻ X

record Choiceˡ (v : List (Letter Cut)) (Xs : List Carrier) : Set where
  field
    vz     : List (Letter (Cut × Cut))
    first  : map (mapˡ π₁) vz ≡ v
    vc     : List (Letter Carrier)
    second : map (mapˡ π₂) vz ≡ map clo⁻ vc
    within : Withinˡ vc v
    below  : All (λ c → π₁ c ⊑ᶜ π₂ c) (capsOf vz)
    good   : Goodˡ vz Xs

chooseˡ : ∀ v Xs → Choiceˡ v Xs
chooseˡ [] Xs = record
  { vz = [] ; first = refl ; vc = [] ; second = refl ; within = []
  ; below = tt ; good = λ { [] [] x t → t } }
chooseˡ (op o ∷ v) Xs with chooseˡ v Xs
... | ch = record
  { vz = op o ∷ C.vz ; first = cong (op o ∷_) C.first ; vc = op o ∷ C.vc
  ; second = cong (op o ∷_) C.second ; within = op C.within
  ; below = C.below ; good = C.good }
  where module C = Choiceˡ ch
chooseˡ (st S c ∷ v) Xs with choose-endˡ c (subsumsˡ (capsOf v)) Xs
... | ψ , pick cψ above with chooseˡ v (Xs ++ map (_∸ᴰ ψ) Xs)
...   | ch = record
  { vz = st S (c , cl⁻ ψ) ∷ C.vz ; first = cong (st S c ∷_) C.first
  ; vc = st S ψ ∷ C.vc ; second = cong (st S (cl⁻ ψ) ∷_) C.second
  ; within = st cψ C.within
  ; below = cψ , C.below
  ; good = good }
  where
    module C = Choiceˡ ch
    good : Goodˡ (st S (c , cl⁻ ψ) ∷ C.vz) Xs
    good cs (drop s) x t = C.good cs s (∈-++⁺ˡ x) t
    good (.(c , cl⁻ ψ) ∷ cs) (keep s) {X} x t with above x Sm t
      where
        Sm : sumˡ (map π₁ cs) ∈ subsumsˡ (capsOf v)
        Sm = subst (λ z → sumˡ (map π₁ cs) ∈ subsumsˡ z)
               (trans (sym (capsˡ π₁ C.vz)) (cong capsOf C.first))
               (sub-∈ˡ (sub-map π₁ s))
    ... | ψ≤X , rest =
      subst (cl⁻ ψ +ˡ sumˡ (map π₂ cs) ⊑ᶜ_) (sym (cl⁻-split ψ≤X))
        (+ˡ-monoʳ (cl⁻ ψ) (C.good cs s (∈-++⁺ʳ Xs (∈-map⁺ (_∸ᴰ ψ) x)) rest))

------------------------------------------------------------------------
-- A lower run on an exact run is a run against closed bounds within
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

closeᴸ : ∀ cps v → RunL (map toLo cps) v
       → Σ[ vc ∈ List (Letter Carrier) ] Withinˡ vc v × RunL (map toLo cps) (map clo⁻ vc)
closeᴸ cps v r = C.vc , C.within , result
  where
    Xs = infixSums (amts cps)
    ch = chooseˡ v Xs
    module C = Choiceˡ ch
    zs₀ = map diag (map toLo cps)

    agree : ∀ a pre b (cs : List (Cut × Cut)) → a ++ pre ++ b ≡ zs₀ → Sub cs (capsOf C.vz)
          → Fitsᴸ (map π₁ pre) (map π₁ cs) ⇔ Fitsᴸ (map π₂ pre) (map π₂ cs)
    agree a pre b cs e s with infix-map diag a pre b (map toLo cps) e
    ... | a′ , pre′ , b′ , e′ , refl with infix-map toLo a′ pre′ b′ cps e′
    ...   | a″ , pre″ , b″ , e″ , refl =
      mk⇔ (λ t → subst (λ P → Fitsᴸ P (map π₂ cs)) (sym (map-π-diag₂ (map toLo pre″)))
                  (subst (sumˡ (map π₂ cs) ⊑ᶜ_) (sym (sum-toLo pre″))
                    (C.good cs s X∈
                      (subst (sumˡ (map π₁ cs) ⊑ᶜ_) (sum-toLo pre″)
                        (subst (λ P → Fitsᴸ P (map π₁ cs)) (map-π-diag₁ (map toLo pre″)) t)))))
          (λ t → subst (λ P → Fitsᴸ P (map π₁ cs)) (sym (map-π-diag₁ (map toLo pre″)))
                  (⊑ᶜ-trans (sum-mono (all-sub s C.below))
                            (subst (λ P → Fitsᴸ P (map π₂ cs)) (map-π-diag₂ (map toLo pre″)) t)))
      where
        X∈ : sumᴰ (amts pre″) ∈ Xs
        X∈ = infix-∈ (amts a″) (amts pre″) (amts b″)
               (trans (cong (amts a″ ++_) (sym (amts-++ pre″ b″)))
                 (trans (sym (amts-++ a″ (pre″ ++ b″))) (cong amts e″)))

    kinds : ∀ a z b → a ++ z ∷ b ≡ zs₀ → proj₁ (π₁ z) ≡ proj₁ (π₂ z)
    kinds a z b e = cong proj₁ (diag-π a z b (map toLo cps) e)

    module A = Agree proj₁ Fitsᴸ zs₀ C.vz kinds agree

    result : RunL (map toLo cps) (map clo⁻ C.vc)
    result = subst₂ RunL (map-π-diag₂ (map toLo cps)) C.second
               (Equivalence.to A.agreeᴸ
                 (subst₂ RunL (sym (map-π-diag₁ (map toLo cps))) (sym C.first) r))
