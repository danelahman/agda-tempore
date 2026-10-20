------------------------------------------------------------------------
-- The lower reader against a regular set of bounds, in whole steps.  --
--                                                                    --
-- As for the upper reader (`Regular.Upper`): the bounds are the      --
-- words of a table `M` over letters `Fin kY`, the pieces letters     --
-- `Fin kX`, and the automaton's states are the reader's              --
-- configurations,                                                    --
--                                                                    --
--   free q        between chains, the bound at state q of M          --
--   ch q S g m    in a chain whose stretch admits S, the bound at q, --
--                 the chain summarised by its lower gap g, m when    --
--                 the first piece has overflowed                     --
--                                                                    --
-- A piece pours freely, overflows into the next stretch when the     --
-- chain is met inside it and not before, and a chain closes once met.--
-- States of M from which M accepts nothing are left out. A chain not --
-- yet met lacks at most the largest bound and weight, so finitely    --
-- many configurations serve.                                         --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)
open import Syntax.Durations.Nat using (ℕᵀ)
import Syntax.Grades.Traces.RunningTimes as RunningTimes
import Syntax.Durations.Intervals as Intervals
import Syntax.Grades.Exact.Letters as Letters
import Syntax.Grades.Regular.Automaton as Automaton
open import Data.Product using (_×_)

module Syntax.Grades.Exact.Regular.Lower
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op)
  (kX kY : ℕ)
  (M : Automaton.DFA kY) (M-wf : Automaton.WellFormed kY M)
  (decX : Fin kX → Letters.Kind T Op n code code-injective running × Intervals.Cut ℕᵀ)
  (decY : Fin kY → Letters.Letter T Op n code code-injective running (Intervals.Cut ℕᵀ)) where

open import Data.Bool.Base using (Bool; true; false; not; _∧_) renaming (T to IsTrue)
open import Data.Bool.Properties using (T?)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; +[1+_]; _⊖_; _-_)
import Data.Integer.Properties as ℤ
open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_; map; concatMap; allFin; foldr; upTo; [_])
open import Data.List.Properties using (map-++)
open import Data.List.Membership.Propositional using (_∈_; find; lose)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻; ∈-concatMap⁺; ∈-concatMap⁻; ∈-allFin; ∈-upTo⁺; ∈-upTo⁻)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product using (Σ; Σ-syntax; ∃; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Durations.Intervals ℕᵀ
open import Syntax.Grades.Exact.Base T Op n code code-injective using (OpSet; _≟ˢ_)
open import Syntax.Grades.Exact.Letters T Op n code code-injective running
  using (Kind; opk; stk; AdmK; AdmK?; Letter; op; st)
open import Syntax.Grades.Exact.Reader T Op n code code-injective running using (module Lower; _≟ᴷ_)
open import Syntax.Grades.Exact.Regular.Gap
import Syntax.Grades.Regular.Automaton kY as Y
open import Syntax.Grades.Regular.Basics kY using (next-<; start-<)
open import Syntax.Grades.Regular.Determinise kX as Det using (ENFA; Silent*; Acc)

open Equivalence using (to; from)

------------------------------------------------------------------------
-- The reader in whole steps

P : Set
P = Kind × Cut

Fitsℕ : List P → List Cut → Set
Fitsℕ pre cs = sumˡ cs ⊑ sumˡ (map proj₂ pre)

open Lower proj₁ Fitsℕ

sm : List P → List Cut → Gᴸ
sm pre cs = normᴸ (sumˡ (map proj₂ pre)) (sumˡ cs)

private
  sumˡ-∷ʳ : ∀ cs c → sumˡ (cs ∷ʳ c) ≡ sumˡ cs +ˡ c
  sumˡ-∷ʳ []       c = trans (+ˡ-identityʳ c) (sym (+ˡ-identityˡ c))
  sumˡ-∷ʳ (k ∷ cs) c = trans (cong (k +ˡ_) (sumˡ-∷ʳ cs c)) (sym (+ˡ-assoc k (sumˡ cs) c))

  map-∷ʳ : ∀ {A B : Set} (f : A → B) xs x → map f (xs ∷ʳ x) ≡ map f xs ∷ʳ f x
  map-∷ʳ f xs x = map-++ f xs [ x ]

init : Cut → Gᴸ
init c = normᴸ 0⁻ c

sm-start : ∀ c → sm [] (c ∷ []) ≡ init c
sm-start c = cong (normᴸ 0⁻) (+ˡ-identityʳ c)

sm-pour : ∀ pre p cs → sm (pre ∷ʳ p) cs ≡ addpᴸ (sm pre cs) (proj₂ p)
sm-pour pre p cs =
  trans (cong (λ h → normᴸ h (sumˡ cs))
          (trans (cong sumˡ (map-∷ʳ proj₂ pre p)) (sumˡ-∷ʳ (map proj₂ pre) (proj₂ p))))
        (normᴸ-addp (sumˡ (map proj₂ pre)) (sumˡ cs) (proj₂ p))

sm-fits : ∀ pre cs → Fitsℕ pre cs ⇔ fitsᴸ (sm pre cs)
sm-fits pre cs = normᴸ-fits (sumˡ (map proj₂ pre)) (sumˡ cs)

sm-enter : ∀ pre cs c → ¬ Fitsℕ pre cs → sm pre (cs ∷ʳ c) ≡ addcᴸ (sm pre cs) c
sm-enter pre cs c ¬f =
  trans (cong (normᴸ (sumˡ (map proj₂ pre))) (sumˡ-∷ʳ cs c))
        (normᴸ-addc (sumˡ (map proj₂ pre)) (sumˡ cs) c ¬f)

------------------------------------------------------------------------
-- Configurations

data Cfg : Set where
  free : ℕ → Cfg
  ch   : ℕ → OpSet → Gᴸ → Bool → Cfg

private
  _≟ˢⁱ_ : DecidableEquality Side
  ⁻ ≟ˢⁱ ⁻ = yes refl
  ⁺ ≟ˢⁱ ⁺ = yes refl
  ⁻ ≟ˢⁱ ⁺ = no λ ()
  ⁺ ≟ˢⁱ ⁻ = no λ ()

  _≟ᴳ_ : DecidableEquality Gᴸ
  gapᴸ d s t ≟ᴳ gapᴸ d′ s′ t′ with d ℤ.≟ d′ | s ≟ˢⁱ s′ | t ≟ˢⁱ t′
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬e | _ | _ = no λ { refl → ¬e refl }
  ... | _ | no ¬e | _ = no λ { refl → ¬e refl }
  ... | _ | _ | no ¬e = no λ { refl → ¬e refl }
  gapᴸ _ _ _ ≟ᴳ sat = no λ ()
  sat ≟ᴳ gapᴸ _ _ _ = no λ ()
  sat ≟ᴳ sat        = yes refl

  _≟ᵇ_ : DecidableEquality Bool
  false ≟ᵇ false = yes refl
  true  ≟ᵇ true  = yes refl
  false ≟ᵇ true  = no λ ()
  true  ≟ᵇ false = no λ ()

_≟ᶜ_ : DecidableEquality Cfg
free q ≟ᶜ free q′ with q ℕ.≟ q′
... | yes refl = yes refl
... | no ¬e    = no λ { refl → ¬e refl }
ch q S g m ≟ᶜ ch q′ S′ g′ m′ with q ℕ.≟ q′ | S ≟ˢ S′ | g ≟ᴳ g′ | m ≟ᵇ m′
... | yes refl | yes refl | yes refl | yes refl = yes refl
... | no ¬e | _ | _ | _ = no λ { refl → ¬e refl }
... | _ | no ¬e | _ | _ = no λ { refl → ¬e refl }
... | _ | _ | no ¬e | _ = no λ { refl → ¬e refl }
... | _ | _ | _ | no ¬e = no λ { refl → ¬e refl }
free _ ≟ᶜ ch _ _ _ _ = no λ ()
ch _ _ _ _ ≟ᶜ free _ = no λ ()

------------------------------------------------------------------------
-- The moves

private
  ys : List (Fin kY)
  ys = allFin kY

  next : ℕ → Fin kY → ℕ
  next = Y.next M

  when : ∀ {A X : Set} → Dec X → List A → List A
  when (yes _) xs = xs
  when (no _)  _  = []

  _∧?_ : ∀ {X Y : Set} → Dec X → Dec Y → Dec (X × Y)
  yes x ∧? yes y = yes (x , y)
  yes _ ∧? no ¬y = no λ { (_ , y) → ¬y y }
  no ¬x ∧? _     = no λ { (x , _) → ¬x x }

  not? : ∀ {X : Set} → Dec X → Dec (¬ X)
  not? (yes x) = no λ ¬x → ¬x x
  not? (no ¬x) = yes ¬x

-- the states of M from which some word is accepted; a dead state is
-- not final and has every letter loop on it

dead : ℕ → Bool
dead q = not (Y.isFinal M q) ∧ all (λ b → next q b ℕ.≡ᵇ q) ys

Live : ℕ → Set
Live q = IsTrue (not (dead q))

live? : ∀ q → Dec (Live q)
live? q = T? (not (dead q))

private
  all-∈ : ∀ (f : Fin kY → Bool) xs → IsTrue (all f xs) → ∀ {b} → b ∈ xs → IsTrue (f b)
  all-∈ f (x ∷ xs) t (here refl) with f x
  ... | true = tt
  all-∈ f (x ∷ xs) t (there m) with f x
  ... | true = all-∈ f xs t m

  ∧-r : ∀ {x y} → IsTrue (x ∧ y) → IsTrue y
  ∧-r {true} t = t

  dead-run : ∀ q → IsTrue (dead q) → ∀ uY → Y.run M q uY ≡ q
  dead-run q d []       = refl
  dead-run q d (b ∷ uY) =
    trans (cong (λ r → Y.run M r uY)
                (ℕ.≡ᵇ⇒≡ _ _ (all-∈ (λ b → next q b ℕ.≡ᵇ q) ys (∧-r {not (Y.isFinal M q)} d) (∈-allFin b))))
          (dead-run q d uY)

live-of : ∀ q uY → IsTrue (Y.isFinal M (Y.run M q uY)) → Live q
live-of q uY f with dead q in e
... | false = tt
... | true  = not-final (subst IsTrue (sym e) tt)
                (subst (λ r → IsTrue (Y.isFinal M r)) (dead-run q (subst IsTrue (sym e) tt) uY) f)
  where
    not-final : ∀ {b c} → IsTrue (not b ∧ c) → IsTrue b → ⊥
    not-final {true} () _

-- stretch letters of the bound started and entered; operation letters
-- matched

startOf : ℕ → Fin kY → Letter Cut → List Cfg
startOf q b (st S c) = when (live? (next q b)) (ch (next q b) S (init c) false ∷ [])
startOf q b (op _)   = []

enterOf : ℕ → Gᴸ → Fin kY → Letter Cut → List Cfg
enterOf q g b (st S c) = when (live? (next q b)) (ch (next q b) S (addcᴸ g c) true ∷ [])
enterOf q g b (op _)   = []

matchOf : P → ℕ → Fin kY → Letter Cut → List Cfg
matchOf p q b (op o)   = when (live? (next q b)) (when (proj₁ p ≟ᴷ opk o) (free (next q b) ∷ []))
matchOf p q b (st _ _) = []

-- a piece overflows when the chain is met inside it and not before

Overflows : Fin kX → OpSet → Gᴸ → Set
Overflows a S g = AdmK (proj₁ (decX a)) S × ¬ fitsᴸ g × fitsᴸ (addpᴸ g (proj₂ (decX a)))

overflows? : ∀ a S g → Dec (Overflows a S g)
overflows? a S g = AdmK? (proj₁ (decX a)) S ∧? (not? (fitsᴸ? g) ∧? fitsᴸ? (addpᴸ g (proj₂ (decX a))))

overOf : Maybe (Fin kX) → ℕ → OpSet → Gᴸ → List Cfg
overOf nothing  q S g = []
overOf (just a) q S g = when (overflows? a S g) (concatMap (λ b → enterOf q g b (decY b)) ys)

closeOf : ℕ → Gᴸ → Bool → List Cfg
closeOf q g false = when (fitsᴸ? g) (free q ∷ [])
closeOf q g true  = []

silentᶜ : Maybe (Fin kX) → Cfg → List Cfg
silentᶜ x (free q)     = concatMap (λ b → startOf q b (decY b)) ys
silentᶜ x (ch q S g m) = overOf x q S g ++ closeOf q g m

readsᶜ : Fin kX → Cfg → List Cfg
readsᶜ a (free q)     = concatMap (λ b → matchOf (decX a) q b (decY b)) ys
readsᶜ a (ch q S g m) = when (AdmK? (proj₁ (decX a)) S) (ch q S (addpᴸ g (proj₂ (decX a))) false ∷ [])

acceptᶜ : Cfg → Bool
acceptᶜ (free q) = Y.isFinal M q
acceptᶜ _        = false

reader : ENFA Cfg
reader = record { start = free 0 ; silent = silentᶜ ; reads = readsᶜ ; accept = acceptᶜ }

------------------------------------------------------------------------
-- Inverting and building the moves

private
  when-∈ : ∀ {A X : Set} (d : Dec X) {xs : List A} {x} → x ∈ when d xs → X × x ∈ xs
  when-∈ (yes p) m = p , m

  ∈-when : ∀ {A X : Set} (d : Dec X) {xs : List A} {x} → X → x ∈ xs → x ∈ when d xs
  ∈-when (yes _) _ m = m
  ∈-when (no ¬p) p _ = ⊥-elim (¬p p)

  start-∈ : ∀ q {c} → c ∈ concatMap (λ b → startOf q b (decY b)) ys
          → Σ[ b ∈ Fin kY ] Σ[ S ∈ OpSet ] Σ[ h ∈ Cut ] decY b ≡ st S h × c ≡ ch (next q b) S (init h) false
  start-∈ q m with find (∈-concatMap⁻ (λ b → startOf q b (decY b)) {xs = ys} m)
  ... | b , _ , m′ with decY b in e
  ...   | st S h with when-∈ (live? (next q b)) m′
  ...     | _ , here refl = b , S , h , e , refl

  enter-∈ : ∀ q g {c} → c ∈ concatMap (λ b → enterOf q g b (decY b)) ys
          → Σ[ b ∈ Fin kY ] Σ[ S ∈ OpSet ] Σ[ h ∈ Cut ] decY b ≡ st S h × c ≡ ch (next q b) S (addcᴸ g h) true
  enter-∈ q g m with find (∈-concatMap⁻ (λ b → enterOf q g b (decY b)) {xs = ys} m)
  ... | b , _ , m′ with decY b in e
  ...   | st S h with when-∈ (live? (next q b)) m′
  ...     | _ , here refl = b , S , h , e , refl

  match-∈ : ∀ a q {c} → c ∈ concatMap (λ b → matchOf (decX a) q b (decY b)) ys
          → Σ[ b ∈ Fin kY ] Σ[ o ∈ Op ] decY b ≡ op o × proj₁ (decX a) ≡ opk o × c ≡ free (next q b)
  match-∈ a q m with find (∈-concatMap⁻ (λ b → matchOf (decX a) q b (decY b)) {xs = ys} m)
  ... | b , _ , m′ with decY b in e
  ...   | op o with when-∈ (live? (next q b)) m′
  ...     | _ , m″ with when-∈ (proj₁ (decX a) ≟ᴷ opk o) m″
  ...       | k , here refl = b , o , e , k , refl

  close-∈ : ∀ q g m {c} → c ∈ closeOf q g m → c ≡ free q × m ≡ false × fitsᴸ g
  close-∈ q g false mm with when-∈ (fitsᴸ? g) mm
  ... | f , here refl = refl , refl , f

  pour-∈ : ∀ a q S g m {c} → c ∈ readsᶜ a (ch q S g m)
         → c ≡ ch q S (addpᴸ g (proj₂ (decX a))) false × AdmK (proj₁ (decX a)) S
  pour-∈ a q S g m mm with when-∈ (AdmK? (proj₁ (decX a)) S) mm
  ... | ad , here refl = refl , ad

  ∈-start : ∀ q b S h → decY b ≡ st S h → Live (next q b) → ch (next q b) S (init h) false ∈ concatMap (λ b → startOf q b (decY b)) ys
  ∈-start q b S h e l =
    ∈-concatMap⁺ (λ b → startOf q b (decY b)) (lose (∈-allFin b) (subst (λ ℓ → _ ∈ startOf q b ℓ) (sym e) (∈-when (live? (next q b)) l (here refl))))

  ∈-enter : ∀ q g b S h → decY b ≡ st S h → Live (next q b) → ch (next q b) S (addcᴸ g h) true ∈ concatMap (λ b → enterOf q g b (decY b)) ys
  ∈-enter q g b S h e l =
    ∈-concatMap⁺ (λ b → enterOf q g b (decY b)) (lose (∈-allFin b) (subst (λ ℓ → _ ∈ enterOf q g b ℓ) (sym e) (∈-when (live? (next q b)) l (here refl))))

  ∈-match : ∀ a q b o → decY b ≡ op o → proj₁ (decX a) ≡ opk o → Live (next q b)
          → free (next q b) ∈ concatMap (λ b → matchOf (decX a) q b (decY b)) ys
  ∈-match a q b o e k l =
    ∈-concatMap⁺ (λ b → matchOf (decX a) q b (decY b))
      (lose (∈-allFin b) (subst (λ ℓ → _ ∈ matchOf (decX a) q b ℓ) (sym e)
        (∈-when (live? (next q b)) l (∈-when (proj₁ (decX a) ≟ᴷ opk o) k (here refl)))))

------------------------------------------------------------------------
-- What a configuration accepts

Lq : ℕ → List (Letter Cut) → Set
Lq q v = Σ[ u ∈ Y.Word ] IsTrue (Y.isFinal M (Y.run M q u)) × map decY u ≡ v

Sem : Cfg → List P → Set
Sem (free q)     ps = Σ[ v ∈ _ ] Lq q v × RunL ps v
Sem (ch q S g m) ps = ∀ pre cs → sm pre cs ≡ g → Σ[ v ∈ _ ] Lq q v × ChL S pre cs m ps v

data Ahead : Maybe (Fin kX) → List P → Set where
  end   : Ahead nothing []
  ahead : ∀ a ps → Ahead (just a) (decX a ∷ ps)

private
  Lq-∷ : ∀ q b {v} → Lq (next q b) v → Lq q (decY b ∷ v)
  Lq-∷ q b (u , f , refl) = b ∷ u , f , refl

  silent-sound : ∀ x ps → Ahead x ps → ∀ c {c′} → c′ ∈ silentᶜ x c → Sem c′ ps → Sem c ps
  silent-sound x ps ah (free q) m s with start-∈ q m
  ... | b , S , h , e , refl with s [] (h ∷ []) (sm-start h)
  ...   | v , lv , k = st S h ∷ v , subst (λ ℓ → Lq q (ℓ ∷ v)) e (Lq-∷ q b lv) , start k
  silent-sound x ps ah (ch q S g m) mm s with ∈-++⁻ (overOf x q S g) mm
  silent-sound (just a) (.(decX a) ∷ ps) (ahead .a .ps) (ch q S g m) mm s | inj₁ m′
    with when-∈ (overflows? a S g) m′
  ... | (ad , ¬f , f) , m″ with enter-∈ q g m″
  ...   | b , S′ , h , e , refl = λ pre cs eg →
          let ¬F : ¬ Fitsℕ pre cs
              ¬F = λ F → ¬f (subst fitsᴸ eg (to (sm-fits pre cs) F))
              (v , lv , k) = s pre (cs ∷ʳ h) (trans (sm-enter pre cs h ¬F) (cong (λ z → addcᴸ z h) eg))
          in st S′ h ∷ v , subst (λ ℓ → Lq q (ℓ ∷ v)) e (Lq-∷ q b lv) ,
             over ad ¬F (from (sm-fits (pre ∷ʳ decX a) cs)
                          (subst fitsᴸ (sym (trans (sm-pour pre (decX a) cs) (cong (λ z → addpᴸ z _) eg))) f)) k
  silent-sound x ps ah (ch q S g m) mm s | inj₂ m′ with close-∈ q g m m′
  ... | refl , refl , f = λ pre cs e → let (v , lv , r) = s in
        v , lv , close (from (sm-fits pre cs) (subst fitsᴸ (sym e) f)) r

  reads-sound : ∀ a ps c {c″} → c″ ∈ readsᶜ a c → Sem c″ ps → Sem c (decX a ∷ ps)
  reads-sound a ps (free q) m s with match-∈ a q m
  ... | b , o , e , k , refl with s
  ...   | v , lv , r = op o ∷ v , subst (λ ℓ → Lq q (ℓ ∷ v)) e (Lq-∷ q b lv) , match k r
  reads-sound a ps (ch q S g m) mm s with pour-∈ a q S g m mm
  ... | refl , ad = λ pre cs e →
        let (v , lv , k) = s (pre ∷ʳ decX a) cs (trans (sm-pour pre (decX a) cs) (cong (λ z → addpᴸ z _) e)) in
        v , lv , pour ad k

  accept-sound : ∀ c → IsTrue (acceptᶜ c) → Sem c []
  accept-sound (free q) f = [] , ([] , f , refl) , done

  silents-sound : ∀ x ps → Ahead x ps → ∀ {c c′} → Silent* reader x c c′ → Sem c′ ps → Sem c ps
  silents-sound x ps ah Det.here        s = s
  silents-sound x ps ah (Det.there m r) s = silent-sound x ps ah _ m (silents-sound x ps ah r s)

sound : ∀ c u → Acc reader c u → Sem c (map decX u)
sound c []      (c′ , r , f)            = silents-sound nothing [] end r (accept-sound c′ f)
sound c (a ∷ u) (c′ , c″ , r , m , acc) =
  silents-sound (just a) (decX a ∷ map decX u) (ahead a _) r (reads-sound a (map decX u) c′ m (sound c″ u acc))

------------------------------------------------------------------------
-- Runs of the reader are accepting runs of the automaton

private
  hd : List (Fin kX) → Maybe (Fin kX)
  hd []      = nothing
  hd (a ∷ _) = just a

  acc-silent : ∀ c c′ u → c′ ∈ silentᶜ (hd u) c → Acc reader c′ u → Acc reader c u
  acc-silent c c′ []      m (c″ , r , f)            = c″ , Det.there m r , f
  acc-silent c c′ (a ∷ u) m (c₁ , c₂ , r , m′ , acc) = c₁ , c₂ , Det.there m r , m′ , acc

  map-[] : ∀ {A B : Set} {f : A → B} xs → map f xs ≡ [] → xs ≡ []
  map-[] []      _ = refl

  map-∷ : ∀ {A B : Set} {f : A → B} xs {y ys} → map f xs ≡ y ∷ ys
        → Σ[ x ∈ A ] Σ[ xs′ ∈ List A ] xs ≡ x ∷ xs′ × f x ≡ y × map f xs′ ≡ ys
  map-∷ (x ∷ xs) refl = x , xs , refl , refl , refl

  Fin′ : ℕ → Y.Word → Set
  Fin′ q uY = IsTrue (Y.isFinal M (Y.run M q uY))

  mutual

    comp-run : ∀ {ps v} → RunL ps v → ∀ u uY q → map decX u ≡ ps → map decY uY ≡ v → Fin′ q uY
             → Acc reader (free q) u
    comp-run done u uY q eu ev f with map-[] u eu | map-[] uY ev
    ... | refl | refl = free q , Det.here , f
    comp-run (match {o = o} k r) u uY q eu ev f with map-∷ u eu | map-∷ uY ev
    ... | a , u′ , refl , ea , eu′ | b , uY′ , refl , eb , ev′ =
      free q , free (next q b) , Det.here ,
      ∈-match a q b o eb (trans (cong proj₁ ea) k) (live-of (next q b) uY′ f) ,
      comp-run r u′ uY′ (next q b) eu′ ev′ f
    comp-run (start {S} {c} h) u uY q eu ev f with map-∷ uY ev
    ... | b , uY′ , refl , eb , ev′ =
      acc-silent (free q) _ u (∈-start q b S c eb (live-of (next q b) uY′ f))
        (subst (λ g → Acc reader (ch (next q b) S g false) u) (sm-start c)
          (comp-ch h u uY′ (next q b) eu ev′ f))

    comp-ch : ∀ {S pre cs m ps v} → ChL S pre cs m ps v → ∀ u uY q → map decX u ≡ ps → map decY uY ≡ v
            → Fin′ q uY → Acc reader (ch q S (sm pre cs) m) u
    comp-ch {S} {pre} {cs} {m} (pour ad h) u uY q eu ev f with map-∷ u eu
    ... | a , u′ , refl , refl , eu′ =
      ch q S (sm pre cs) m , ch q S (addpᴸ (sm pre cs) (proj₂ (decX a))) false , Det.here ,
      ∈-when (AdmK? (proj₁ (decX a)) S) ad (here refl) ,
      subst (λ g → Acc reader (ch q S g false) u′) (sm-pour pre (decX a) cs)
        (comp-ch h u′ uY q eu′ ev f)
    comp-ch {S} {pre} {cs} {m} (over {S′ = S′} {c} ad ¬F F k) u uY q eu ev f with map-∷ u eu | map-∷ uY ev
    ... | a , u′ , refl , refl , eu′ | b , uY′ , refl , eb , ev′ =
      acc-silent (ch q S (sm pre cs) m) _ (a ∷ u′)
        (∈-++⁺ˡ (∈-when (overflows? a S (sm pre cs))
                   (ad , (λ fg → ¬F (from (sm-fits pre cs) fg)) ,
                    subst fitsᴸ (sm-pour pre (decX a) cs) (to (sm-fits (pre ∷ʳ decX a) cs) F))
                   (∈-enter q (sm pre cs) b S′ c eb (live-of (next q b) uY′ f))))
        (subst (λ g → Acc reader (ch (next q b) S′ g true) (a ∷ u′)) (sm-enter pre cs c ¬F)
          (comp-ch k (a ∷ u′) uY′ (next q b) (cong (decX a ∷_) eu′) ev′ f))
    comp-ch {S} {pre} {cs} (close F r) u uY q eu ev f =
      acc-silent (ch q S (sm pre cs) false) (free q) u
        (∈-++⁺ʳ (overOf (hd u) q S (sm pre cs)) (∈-when (fitsᴸ? (sm pre cs)) (to (sm-fits pre cs) F) (here refl)))
        (comp-run r u uY q eu ev f)

ReadsSome : List (Fin kX) → Set
ReadsSome u = Σ[ uY ∈ Y.Word ] IsTrue (Y.isFinal M (Y.run M 0 uY)) × RunL (map decX u) (map decY uY)

accepts⇔ : ∀ u → Acc reader (free 0) u ⇔ ReadsSome u
accepts⇔ u = mk⇔ to′ (λ { (uY , f , r) → comp-run r u uY 0 refl refl f })
  where
    to′ : Acc reader (free 0) u → ReadsSome u
    to′ acc with sound (free 0) u acc
    ... | v , (uY , f , refl) , r = uY , f , r

------------------------------------------------------------------------
-- Finitely many configurations

private
  maxL : List ℕ → ℕ
  maxL = foldr ℕ._⊔_ 0

  ≤-maxL : ∀ {x xs} → x ∈ xs → x ℕ.≤ maxL xs
  ≤-maxL {x} {.x ∷ xs} (here refl) = ℕ.m≤m⊔n x (maxL xs)
  ≤-maxL {x} {y ∷ xs}  (there m)   = ℕ.≤-trans (≤-maxL m) (ℕ.m≤n⊔m y (maxL xs))

  capOf : Letter Cut → ℕ
  capOf (st _ (k ∣ _)) = k
  capOf _              = 0

  wOf : P → ℕ
  wOf (_ , (j ∣ _)) = j

  setOf : Letter Cut → List OpSet
  setOf (st S _) = S ∷ []
  setOf (op _)   = []

maxc maxw bound : ℕ
maxc  = maxL (map (λ b → capOf (decY b)) ys)
maxw  = maxL (map (λ a → wOf (decX a)) (allFin kX))
bound = maxw ℕ.+ maxc

sides : List Side
sides = ⁻ ∷ ⁺ ∷ []

gaps : ℕ → List Gᴸ
gaps N = sat ∷ concatMap (λ k → concatMap (λ s → map (gapᴸ (ℤ.- (+ k)) s) sides) sides) (upTo (ℕ.suc N))

sets : List OpSet
sets = concatMap (λ b → setOf (decY b)) ys

states : List ℕ
states = upTo (Y.size M)

univ : List Cfg
univ = map free states
    ++ concatMap (λ q → concatMap (λ S → concatMap (λ g → map (ch q S g) (false ∷ true ∷ [])) (gaps bound)) sets) states

data InGaps (N : ℕ) : Gᴸ → Set where
  sat : InGaps N sat
  gap : ∀ {k} s t → k ℕ.≤ N → InGaps N (gapᴸ (ℤ.- (+ k)) s t)

data Good : Cfg → Set where
  free : ∀ {q} → q ℕ.< Y.size M → Good (free q)
  ch   : ∀ {q S g m} → q ℕ.< Y.size M → S ∈ sets → InGaps bound g → Good (ch q S g m)

private
  in-sides : ∀ s → s ∈ sides
  in-sides ⁻ = here refl
  in-sides ⁺ = there (here refl)

  in-gaps : ∀ {N g} → InGaps N g → g ∈ gaps N
  in-gaps sat = here refl
  in-gaps {N} (gap {k} s t r) =
    there (∈-concatMap⁺ (λ k → concatMap (λ s → map (gapᴸ (ℤ.- (+ k)) s) sides) sides)
      (lose (∈-upTo⁺ (ℕ.s≤s r)) (∈-concatMap⁺ (λ s → map (gapᴸ (ℤ.- (+ k)) s) sides)
        (lose (in-sides s) (∈-map⁺ (gapᴸ (ℤ.- (+ k)) s) (in-sides t))))))

  in-bools : ∀ m → m ∈ (false ∷ true ∷ [])
  in-bools false = here refl
  in-bools true  = there (here refl)

  gaps⁻ : ∀ {N g} → g ∈ gaps N → InGaps N g
  gaps⁻ (here refl) = sat
  gaps⁻ {N} (there m) with find (∈-concatMap⁻ (λ k → concatMap (λ s → map (gapᴸ (ℤ.- (+ k)) s) sides) sides) {xs = upTo (ℕ.suc N)} m)
  ... | k , k∈ , m′ with find (∈-concatMap⁻ (λ s → map (gapᴸ (ℤ.- (+ k)) s) sides) {xs = sides} m′)
  ...   | s , _ , m″ with ∈-map⁻ (gapᴸ (ℤ.- (+ k)) s) m″
  ...     | t , _ , refl = gap s t (ℕ.≤-pred (∈-upTo⁻ k∈))

  chs : List Cfg
  chs = concatMap (λ q → concatMap (λ S → concatMap (λ g → map (ch q S g) (false ∷ true ∷ [])) (gaps bound)) sets) states

good⇒∈ : ∀ {c} → Good c → c ∈ univ
good⇒∈ (free {q} r) = ∈-++⁺ˡ (∈-map⁺ free (∈-upTo⁺ r))
good⇒∈ (ch {q} {S} {g} {m} r S∈ gg) =
  ∈-++⁺ʳ (map free states)
    (∈-concatMap⁺ (λ q → concatMap (λ S → concatMap (λ g → map (ch q S g) (false ∷ true ∷ [])) (gaps bound)) sets)
      (lose (∈-upTo⁺ r) (∈-concatMap⁺ (λ S → concatMap (λ g → map (ch q S g) (false ∷ true ∷ [])) (gaps bound))
        (lose S∈ (∈-concatMap⁺ (λ g → map (ch q S g) (false ∷ true ∷ []))
          (lose (in-gaps gg) (∈-map⁺ (ch q S g) (in-bools m))))))))

∈⇒good : ∀ {c} → c ∈ univ → Good c
∈⇒good m with ∈-++⁻ (map free states) m
... | inj₁ m′ with ∈-map⁻ free m′
...   | q , q∈ , refl = free (∈-upTo⁻ q∈)
∈⇒good m | inj₂ m″ with find (∈-concatMap⁻ (λ q → concatMap (λ S → concatMap (λ g → map (ch q S g) (false ∷ true ∷ [])) (gaps bound)) sets) {xs = states} m″)
... | q , q∈ , m₁ with find (∈-concatMap⁻ (λ S → concatMap (λ g → map (ch q S g) (false ∷ true ∷ [])) (gaps bound)) {xs = sets} m₁)
...   | S , S∈ , m₂ with find (∈-concatMap⁻ (λ g → map (ch q S g) (false ∷ true ∷ [])) {xs = gaps bound} m₂)
...     | g , g∈ , m₃ with ∈-map⁻ (ch q S g) m₃
...       | b , _ , refl = ch (∈-upTo⁻ q∈) S∈ (gaps⁻ g∈)

------------------------------------------------------------------------
-- The moves stay among them

private
  cap-≤ : ∀ b {S k t} → decY b ≡ st S (k ∣ t) → k ℕ.≤ maxc
  cap-≤ b e = subst (ℕ._≤ maxc) (cong capOf e) (≤-maxL (∈-map⁺ (λ b → capOf (decY b)) (∈-allFin b)))

  w-≤ : ∀ a → wOf (decX a) ℕ.≤ maxw
  w-≤ a = ≤-maxL (∈-map⁺ (λ a → wOf (decX a)) (∈-allFin a))

  set-∈ : ∀ b {S h} → decY b ≡ st S h → S ∈ sets
  set-∈ b e = ∈-concatMap⁺ (λ b → setOf (decY b)) (lose (∈-allFin b) (subst (λ ℓ → _ ∈ setOf ℓ) (sym e) (here refl)))

  -- a chain not met lacks at most `N`
  mk-good : ∀ {N} d s t → (¬ Above d t s → Σ[ k ∈ ℕ ] d ≡ ℤ.- (+ k) × k ℕ.≤ N) → InGaps N (mkᴸ d s t)
  mk-good d s t h with Above? d t s
  ... | yes _ = sat
  ... | no ¬a with h ¬a
  ...   | k , refl , r = gap s t r

  mk-fits : ∀ d s t → fitsᴸ (mkᴸ d s t) → Above d t s
  mk-fits d s t f with Above? d t s
  ... | yes a = a
  mk-fits d s t () | no _

  init-good : ∀ b {S h} → decY b ≡ st S h → InGaps bound (init h)
  init-good b {h = k ∣ t} e =
    mk-good (0 ⊖ k) ⁻ t (λ _ → k , trans (ℤ.⊖-≤ ℕ.z≤n) refl , ℕ.≤-trans (cap-≤ b e) (ℕ.m≤n+m maxc maxw))

  neg-+ : ∀ k w → ℤ.- (+ k) ℤ.+ + w ≡ w ⊖ k
  neg-+ = ℤ.-m+n≡n⊖m

  pour-good : ∀ a {g} → InGaps bound g → InGaps bound (addpᴸ g (proj₂ (decX a)))
  pour-good a sat = sat
  pour-good a (gap {k} s t r) with proj₂ (decX a)
  ... | w ∣ u = mk-good (ℤ.- (+ k) ℤ.+ + w) (s ∨ˢ u) t
      (λ ¬a → let wk = ¬above-⊖ w k (λ h → ¬a (subst (λ d → Above d t (s ∨ˢ u)) (sym (neg-+ k w)) h)) in
              k ℕ.∸ w , trans (neg-+ k w) (ℤ.⊖-≤ wk) , ℕ.≤-trans (ℕ.m∸n≤m k w) r)

  enter-good : ∀ a b {S g S′ h} → Overflows a S g → decY b ≡ st S′ h → InGaps bound g → InGaps bound (addcᴸ g h)
  enter-good a b (_ , ¬f , _) e sat = ⊥-elim (¬f tt)
  enter-good a b {h = c ∣ v} (_ , _ , f) e (gap {k} s t r) with proj₂ (decX a) in ew
  ... | w ∣ u =
    mk-good (ℤ.- (+ k) - + c) s (t ∨ˢ v)
      (λ _ → k ℕ.+ c , trans (sym (ℤ.neg-distrib-+ (+ k) (+ c))) (cong ℤ.-_ (sym (ℤ.pos-+ k c))) ,
             ℕ.+-mono-≤ (ℕ.≤-trans kw (subst (ℕ._≤ maxw) (cong (λ z → wOf (proj₁ (decX a) , z)) ew) (w-≤ a)))
                        (cap-≤ b e))
    where
      kw : k ℕ.≤ w
      kw = above-⊖ w k (subst (λ d → Above d t (s ∨ˢ u)) (neg-+ k w) (mk-fits _ _ _ f))

  next-good : ∀ {q} b → q ℕ.< Y.size M → next q b ℕ.< Y.size M
  next-good b r = next-< M M-wf r b

  silent-good : ∀ x {c c′} → Good c → c′ ∈ silentᶜ x c → Good c′
  silent-good x (free r) m with start-∈ _ m
  ... | b , S , h , e , refl = ch (next-good b r) (set-∈ b e) (init-good b e)
  silent-good x (ch {q} {S} {g} {mm} r S∈ gg) m with ∈-++⁻ (overOf x q S g) m
  silent-good (just a) (ch {q} {S} {g} r S∈ gg) m | inj₁ m′ with when-∈ (overflows? a S g) m′
  ... | ov , m″ with enter-∈ q g m″
  ...   | b , S′ , h , e , refl = ch (next-good b r) (set-∈ b e) (enter-good a b ov e gg)
  silent-good x (ch {q} {S} {g} {mm} r S∈ gg) m | inj₂ m′ with close-∈ q g mm m′
  ... | refl , _ , _ = free r

  reads-good : ∀ a {c c′} → Good c → c′ ∈ readsᶜ a c → Good c′
  reads-good a (free {q} r) m with match-∈ a q m
  ... | b , o , e , k , refl = free (next-good b r)
  reads-good a (ch {q} {S} {g} {mm} r S∈ gg) m with pour-∈ a q S g mm m
  ... | refl , ad = ch r S∈ (pour-good a gg)

------------------------------------------------------------------------
-- The table of the reader against M

open Det.Determinise _≟ᶜ_ reader univ
  (good⇒∈ (free (start-< M M-wf)))
  (λ x m m′ → good⇒∈ (silent-good x (∈⇒good m) m′))
  (λ a m m′ → good⇒∈ (reads-good a (∈⇒good m) m′))
  public using (determinised; determinised-wf; ∈-determinised)

∈-reader : ∀ u → Automaton._∈_ kX u determinised ⇔ ReadsSome u
∈-reader u = mk⇔ (λ t → to (accepts⇔ u) (to (∈-determinised u) t))
                 (λ r → from (∈-determinised u) (from (accepts⇔ u) r))
