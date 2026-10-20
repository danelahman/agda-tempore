------------------------------------------------------------------------
-- The upper reader against a regular set of bounds, in whole steps.  --
--                                                                    --
-- The bounds are the words of a table `M` over letters `Fin kY`,     --
-- each letter standing for an upper letter of whole steps; the       --
-- pieces read are letters `Fin kX`, each standing for a piece. The   --
-- reader is run against all bounds at once by an automaton with      --
-- silent moves, whose states are reader configurations:              --
--                                                                    --
--   free q        between chains, the bound at state q of M          --
--   ch q S g m    in a chain whose stretch admits S, the bound at q, --
--                 the chain summarised by its gap g (`Regular.Gap`), --
--                 m when the first piece has overflowed              --
--   ov q g        a piece overflowing, passing stretches of the      --
--                 bound                                              --
--                                                                    --
-- Each move of the reader is a move of the automaton, reading a      --
-- piece when it pours or matches one, silent otherwise; so a word of --
-- pieces is accepted exactly when the reader accepts it against some --
-- bound of M. States of M from which M accepts nothing are left out. --
-- The gaps the automaton meets are bounded by the largest bound and  --
-- weight, so finitely many configurations serve and the automaton    --
-- determinises (`Regular.Determinise`).                              --
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
open import Data.Product using (_×_; Σ; proj₂)

module Syntax.Grades.Exact.Regular.Upper
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (running : RunningTimes.RunningTimes T Op)
  (kX kY : ℕ)
  (M : Automaton.DFA kY) (M-wf : Automaton.WellFormed kY M)
  (decX : Fin kX → Letters.Kind T Op n code code-injective running × Intervals.Hi ℕᵀ)
  (decY : Fin kY → Letters.Letter T Op n code code-injective running (Intervals.Hi ℕᵀ))
  (decX-fin : ∀ a → Σ ℕ λ j → Σ (Intervals.Side ℕᵀ) λ u → proj₂ (decX a) ≡ Intervals.fin (j Intervals.∣ u)) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; not; _∧_) renaming (T to IsTrue)
open import Data.Bool.Properties using (T?)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; +[1+_]; _⊖_; _-_)
import Data.Integer.Properties as ℤ
open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_; map; concatMap; allFin; foldr; upTo; [_])
open import Data.List.Properties using (map-++)
open import Data.List.Membership.Propositional using (_∈_; find; lose)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻; ∈-concatMap⁺; ∈-concatMap⁻; ∈-allFin; ∈-upTo⁺)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)

open import Syntax.Durations.Intervals ℕᵀ
open import Syntax.Grades.Exact.Base T Op n code code-injective using (OpSet; _≟ˢ_)
open import Syntax.Grades.Exact.Letters T Op n code code-injective running
  using (Kind; opk; stk; AdmK; AdmK?; Letter; op; st)
open import Syntax.Grades.Exact.Reader T Op n code code-injective running using (module Upper; _≟ᴷ_)
open import Syntax.Grades.Exact.Regular.Gap
import Syntax.Grades.Regular.Automaton kY as Y
open import Syntax.Grades.Regular.Basics kY using (next-<; start-<)
open import Syntax.Grades.Regular.Determinise kX as Det using (ENFA; Silent*; Acc)

open Equivalence using (to; from)

------------------------------------------------------------------------
-- The reader in whole steps

P : Set
P = Kind × Hi

Fitsℕ : List P → List Hi → Set
Fitsℕ pre cs = sumʰ (map proj₂ pre) ⊑ʰ sumʰ cs

open Upper proj₁ Fitsℕ

-- the gap of a chain

sm : List P → List Hi → Gᵁ
sm pre cs = normᵁ (sumʰ (map proj₂ pre)) (sumʰ cs)

private
  sumʰ-∷ʳ : ∀ hs h → sumʰ (hs ∷ʳ h) ≡ sumʰ hs +ʰ h
  sumʰ-∷ʳ []       h = trans (+ʰ-identityʳ h) (sym (+ʰ-identityˡ h))
  sumʰ-∷ʳ (k ∷ hs) h = trans (cong (k +ʰ_) (sumʰ-∷ʳ hs h)) (sym (+ʰ-assoc k (sumʰ hs) h))

  map-∷ʳ : ∀ {A B : Set} (f : A → B) xs x → map f (xs ∷ʳ x) ≡ map f xs ∷ʳ f x
  map-∷ʳ f xs x = map-++ f xs [ x ]

init : Hi → Gᵁ
init c = normᵁ (fin 0⁺) c

sm-start : ∀ c → sm [] (c ∷ []) ≡ init c
sm-start c = cong (normᵁ (fin 0⁺)) (+ʰ-identityʳ c)

sm-pour : ∀ pre p cs → sm (pre ∷ʳ p) cs ≡ addpᵁ (sm pre cs) (proj₂ p)
sm-pour pre p cs =
  trans (cong (λ h → normᵁ h (sumʰ cs))
          (trans (cong sumʰ (map-∷ʳ proj₂ pre p)) (sumʰ-∷ʳ (map proj₂ pre) (proj₂ p))))
        (normᵁ-addp (sumʰ (map proj₂ pre)) (sumʰ cs) (proj₂ p))

sm-enter : ∀ pre cs c → sm pre (cs ∷ʳ c) ≡ addcᵁ (sm pre cs) c
sm-enter pre cs c =
  trans (cong (normᵁ (sumʰ (map proj₂ pre))) (sumʰ-∷ʳ cs c))
        (normᵁ-addc (sumʰ (map proj₂ pre)) (sumʰ cs) c)

sm-fits : ∀ pre cs → Fitsℕ pre cs ⇔ fitsᵁ (sm pre cs)
sm-fits pre cs = normᵁ-fits (sumʰ (map proj₂ pre)) (sumʰ cs)

------------------------------------------------------------------------
-- Configurations

data Cfg : Set where
  free : ℕ → Cfg
  ch   : ℕ → OpSet → Gᵁ → Bool → Cfg
  ov   : ℕ → Gᵁ → Cfg

private
  _≟ˢⁱ_ : DecidableEquality Side
  ⁻ ≟ˢⁱ ⁻ = yes refl
  ⁺ ≟ˢⁱ ⁺ = yes refl
  ⁻ ≟ˢⁱ ⁺ = no λ ()
  ⁺ ≟ˢⁱ ⁻ = no λ ()

  _≟ᴳ_ : DecidableEquality Gᵁ
  gap d s t ≟ᴳ gap d′ s′ t′ with d ℤ.≟ d′ | s ≟ˢⁱ s′ | t ≟ˢⁱ t′
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬e | _ | _ = no λ { refl → ¬e refl }
  ... | _ | no ¬e | _ = no λ { refl → ¬e refl }
  ... | _ | _ | no ¬e = no λ { refl → ¬e refl }
  gap _ _ _ ≟ᴳ open∞  = no λ ()
  gap _ _ _ ≟ᴳ stuck∞ = no λ ()
  open∞ ≟ᴳ gap _ _ _  = no λ ()
  open∞ ≟ᴳ open∞      = yes refl
  open∞ ≟ᴳ stuck∞     = no λ ()
  stuck∞ ≟ᴳ gap _ _ _ = no λ ()
  stuck∞ ≟ᴳ open∞     = no λ ()
  stuck∞ ≟ᴳ stuck∞    = yes refl

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
ov q g ≟ᶜ ov q′ g′ with q ℕ.≟ q′ | g ≟ᴳ g′
... | yes refl | yes refl = yes refl
... | no ¬e | _ = no λ { refl → ¬e refl }
... | _ | no ¬e = no λ { refl → ¬e refl }
free _ ≟ᶜ ch _ _ _ _ = no λ ()
free _ ≟ᶜ ov _ _     = no λ ()
ch _ _ _ _ ≟ᶜ free _ = no λ ()
ch _ _ _ _ ≟ᶜ ov _ _ = no λ ()
ov _ _ ≟ᶜ free _     = no λ ()
ov _ _ ≟ᶜ ch _ _ _ _ = no λ ()

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

  both : ∀ {X Y : Set} → Dec X → Dec Y → Dec (X × ¬ Y)
  both (yes x) (no ¬y) = yes (x , ¬y)
  both (yes _) (yes y) = no λ { (_ , ¬y) → ¬y y }
  both (no ¬x) _       = no λ { (x , _) → ¬x x }

  both′ : ∀ {X Y : Set} → Dec X → Dec Y → Dec (X × Y)
  both′ (yes x) (yes y) = yes (x , y)
  both′ (yes _) (no ¬y) = no λ { (_ , y) → ¬y y }
  both′ (no ¬x) _       = no λ { (x , _) → ¬x x }

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

-- stretch letters of the bound started, entered and passed; operation
-- letters matched

startOf : ℕ → Fin kY → Letter Hi → List Cfg
startOf q b (st S c) = when (live? (next q b)) (ch (next q b) S (init c) false ∷ [])
startOf q b (op _)   = []

enterOf : ℕ → Gᵁ → Fin kY → Letter Hi → List Cfg
enterOf q g b (st S c) = when (live? (next q b)) (ch (next q b) S (addcᵁ g c) true ∷ ov (next q b) g ∷ [])
enterOf q g b (op _)   = []

matchOf : P → ℕ → Fin kY → Letter Hi → List Cfg
matchOf p q b (op o)   = when (live? (next q b)) (when (proj₁ p ≟ᴷ opk o) (free (next q b) ∷ []))
matchOf p q b (st _ _) = []

overOf : Maybe (Fin kX) → ℕ → OpSet → Gᵁ → List Cfg
overOf nothing  q S g = []
overOf (just a) q S g = when (both (AdmK? (proj₁ (decX a)) S) (fitsᵁ? (addpᵁ g (proj₂ (decX a))))) (ov q g ∷ [])

closeOf : ℕ → Bool → List Cfg
closeOf q false = free q ∷ []
closeOf q true  = []

silentᶜ : Maybe (Fin kX) → Cfg → List Cfg
silentᶜ x (free q)     = concatMap (λ b → startOf q b (decY b)) ys
silentᶜ x (ch q S g m) = overOf x q S g ++ closeOf q m
silentᶜ (just _) (ov q g) = concatMap (λ b → enterOf q g b (decY b)) ys
silentᶜ nothing  (ov _ _) = []

readsᶜ : Fin kX → Cfg → List Cfg
readsᶜ a (free q)     = concatMap (λ b → matchOf (decX a) q b (decY b)) ys
readsᶜ a (ch q S g m) =
  when (both′ (AdmK? (proj₁ (decX a)) S) (fitsᵁ? (addpᵁ g (proj₂ (decX a)))))
       (ch q S (addpᵁ g (proj₂ (decX a))) false ∷ [])
readsᶜ a (ov _ _)     = []

acceptᶜ : Cfg → Bool
acceptᶜ (free q) = Y.isFinal M q
acceptᶜ _        = false

reader : ENFA Cfg
reader = record { start = free 0 ; silent = silentᶜ ; reads = readsᶜ ; accept = acceptᶜ }

------------------------------------------------------------------------
-- Inverting the moves

private
  when-∈ : ∀ {A X : Set} (d : Dec X) {xs : List A} {x} → x ∈ when d xs → X × x ∈ xs
  when-∈ (yes p) m = p , m

  ∈-when : ∀ {A X : Set} (d : Dec X) {xs : List A} {x} → X → x ∈ xs → x ∈ when d xs
  ∈-when (yes _) _ m = m
  ∈-when (no ¬p) p _ = ⊥-elim (¬p p)

  over-∈ : ∀ a q S g {c} → c ∈ overOf (just a) q S g
         → c ≡ ov q g × AdmK (proj₁ (decX a)) S × ¬ fitsᵁ (addpᵁ g (proj₂ (decX a)))
  over-∈ a q S g m with when-∈ (both (AdmK? (proj₁ (decX a)) S) (fitsᵁ? (addpᵁ g (proj₂ (decX a))))) m
  ... | (ad , ¬f) , here refl = refl , ad , ¬f

  close-∈ : ∀ q m {c} → c ∈ closeOf q m → c ≡ free q × m ≡ false
  close-∈ q false (here refl) = refl , refl

  start-∈ : ∀ q {c} → c ∈ concatMap (λ b → startOf q b (decY b)) ys
          → Σ[ b ∈ Fin kY ] Σ[ S ∈ OpSet ] Σ[ h ∈ Hi ] decY b ≡ st S h × c ≡ ch (next q b) S (init h) false
  start-∈ q m with find (∈-concatMap⁻ (λ b → startOf q b (decY b)) {xs = ys} m)
  ... | b , _ , m′ with decY b in e
  ...   | st S h with when-∈ (live? (next q b)) m′
  ...     | _ , here refl = b , S , h , e , refl

  enter-∈ : ∀ q g {c} → c ∈ concatMap (λ b → enterOf q g b (decY b)) ys
          → Σ[ b ∈ Fin kY ] Σ[ S ∈ OpSet ] Σ[ h ∈ Hi ] decY b ≡ st S h
            × (c ≡ ch (next q b) S (addcᵁ g h) true ⊎ c ≡ ov (next q b) g)
  enter-∈ q g m with find (∈-concatMap⁻ (λ b → enterOf q g b (decY b)) {xs = ys} m)
  ... | b , _ , m′ with decY b in e
  ...   | st S h with when-∈ (live? (next q b)) m′
  ...     | _ , here refl         = b , S , h , e , inj₁ refl
  ...     | _ , there (here refl) = b , S , h , e , inj₂ refl

  match-∈ : ∀ a q {c} → c ∈ concatMap (λ b → matchOf (decX a) q b (decY b)) ys
          → Σ[ b ∈ Fin kY ] Σ[ o ∈ Op ] decY b ≡ op o × proj₁ (decX a) ≡ opk o × c ≡ free (next q b)
  match-∈ a q m with find (∈-concatMap⁻ (λ b → matchOf (decX a) q b (decY b)) {xs = ys} m)
  ... | b , _ , m′ with decY b in e
  ...   | op o with when-∈ (live? (next q b)) m′
  ...     | _ , m″ with when-∈ (proj₁ (decX a) ≟ᴷ opk o) m″
  ...       | k , here refl = b , o , e , k , refl

  pour-∈ : ∀ a q S g m {c} → c ∈ readsᶜ a (ch q S g m)
         → c ≡ ch q S (addpᵁ g (proj₂ (decX a))) false × AdmK (proj₁ (decX a)) S × fitsᵁ (addpᵁ g (proj₂ (decX a)))
  pour-∈ a q S g m mm with when-∈ (both′ (AdmK? (proj₁ (decX a)) S) (fitsᵁ? (addpᵁ g (proj₂ (decX a))))) mm
  ... | (ad , f) , here refl = refl , ad , f

  -- and building them

  ∈-start : ∀ q b S h → decY b ≡ st S h → Live (next q b) → ch (next q b) S (init h) false ∈ concatMap (λ b → startOf q b (decY b)) ys
  ∈-start q b S h e l =
    ∈-concatMap⁺ (λ b → startOf q b (decY b)) (lose (∈-allFin b) (subst (λ ℓ → _ ∈ startOf q b ℓ) (sym e) (∈-when (live? (next q b)) l (here refl))))

  ∈-enter : ∀ q g b S h → decY b ≡ st S h → Live (next q b) → ch (next q b) S (addcᵁ g h) true ∈ concatMap (λ b → enterOf q g b (decY b)) ys
  ∈-enter q g b S h e l =
    ∈-concatMap⁺ (λ b → enterOf q g b (decY b)) (lose (∈-allFin b) (subst (λ ℓ → _ ∈ enterOf q g b ℓ) (sym e) (∈-when (live? (next q b)) l (here refl))))

  ∈-pass : ∀ q g b S h → decY b ≡ st S h → Live (next q b) → ov (next q b) g ∈ concatMap (λ b → enterOf q g b (decY b)) ys
  ∈-pass q g b S h e l =
    ∈-concatMap⁺ (λ b → enterOf q g b (decY b)) (lose (∈-allFin b) (subst (λ ℓ → _ ∈ enterOf q g b ℓ) (sym e) (∈-when (live? (next q b)) l (there (here refl)))))

  ∈-match : ∀ a q b o → decY b ≡ op o → proj₁ (decX a) ≡ opk o → Live (next q b)
          → free (next q b) ∈ concatMap (λ b → matchOf (decX a) q b (decY b)) ys
  ∈-match a q b o e k l =
    ∈-concatMap⁺ (λ b → matchOf (decX a) q b (decY b))
      (lose (∈-allFin b) (subst (λ ℓ → _ ∈ matchOf (decX a) q b ℓ) (sym e)
        (∈-when (live? (next q b)) l (∈-when (proj₁ (decX a) ≟ᴷ opk o) k (here refl)))))

------------------------------------------------------------------------
-- What a configuration accepts

-- the bounds accepted from a state of M

Lq : ℕ → List (Letter Hi) → Set
Lq q v = Σ[ u ∈ Y.Word ] IsTrue (Y.isFinal M (Y.run M q u)) × map decY u ≡ v

Sem : Cfg → List P → Set
Sem (free q)     ps       = Σ[ v ∈ _ ] Lq q v × RunU ps v
Sem (ch q S g m) ps       = ∀ pre cs → sm pre cs ≡ g → Σ[ v ∈ _ ] Lq q v × ChU S pre cs m ps v
Sem (ov q g)     []       = ⊥
Sem (ov q g)     (p ∷ ps) = ∀ pre cs → sm pre cs ≡ g → Σ[ v ∈ _ ] Lq q v × OverU pre cs p ps v

-- the pieces still to be read, and what a silent move may see of them

data Ahead : Maybe (Fin kX) → List P → Set where
  end  : Ahead nothing []
  ahead : ∀ a ps → Ahead (just a) (decX a ∷ ps)

private
  Lq-∷ : ∀ q b {v} → Lq (next q b) v → Lq q (decY b ∷ v)
  Lq-∷ q b (u , f , refl) = b ∷ u , f , refl

  silent-sound : ∀ x ps → Ahead x ps → ∀ c {c′} → c′ ∈ silentᶜ x c → Sem c′ ps → Sem c ps
  silent-sound x ps ah (free q) m s with start-∈ q m
  ... | b , S , h , e , refl with s [] (h ∷ []) (sm-start h)
  ...   | v , lv , k = st S h ∷ v , subst (λ ℓ → Lq q (ℓ ∷ v)) e (Lq-∷ q b lv) , start k
  silent-sound x ps ah (ch q S g m) mm s with ∈-++⁻ (overOf x q S g) mm
  silent-sound (just a) (.(decX a) ∷ ps) (ahead .a .ps) (ch q S g m) mm s | inj₁ m′ with over-∈ a q S g m′
  ... | refl , ad , ¬f = λ pre cs e → let (v , lv , o) = s pre cs e in
        v , lv , over ad (λ h → ¬f (subst fitsᵁ (trans (sm-pour pre (decX a) cs) (cong (λ z → addpᵁ z _) e))
                                     (to (sm-fits (pre ∷ʳ decX a) cs) h))) o
  silent-sound x ps ah (ch q S g m) mm s | inj₂ m′ with close-∈ q m m′
  ... | refl , refl = λ pre cs e → let (v , lv , r) = s in v , lv , close r
  silent-sound (just a) (.(decX a) ∷ ps) (ahead .a .ps) (ov q g) m s with enter-∈ q g m
  ... | b , S , h , e , inj₁ refl = λ pre cs eg →
        let (v , lv , k) = s pre (cs ∷ʳ h) (trans (sm-enter pre cs h) (cong (λ z → addcᵁ z h) eg)) in
        st S h ∷ v , subst (λ ℓ → Lq q (ℓ ∷ v)) e (Lq-∷ q b lv) , enter k
  ... | b , S , h , e , inj₂ refl = λ pre cs eg →
        let (v , lv , o) = s pre cs eg in
        st S h ∷ v , subst (λ ℓ → Lq q (ℓ ∷ v)) e (Lq-∷ q b lv) , pass o
  silent-sound nothing [] end (ov q g) ()

  reads-sound : ∀ a ps c {c″} → c″ ∈ readsᶜ a c → Sem c″ ps → Sem c (decX a ∷ ps)
  reads-sound a ps (free q) m s with match-∈ a q m
  ... | b , o , e , k , refl with s
  ...   | v , lv , r = op o ∷ v , subst (λ ℓ → Lq q (ℓ ∷ v)) e (Lq-∷ q b lv) , match k r
  reads-sound a ps (ch q S g m) mm s with pour-∈ a q S g m mm
  ... | refl , ad , f = λ pre cs e →
        let (v , lv , k) = s (pre ∷ʳ decX a) cs (trans (sm-pour pre (decX a) cs) (cong (λ z → addpᵁ z _) e)) in
        v , lv , pour ad (from (sm-fits (pre ∷ʳ decX a) cs)
                           (subst fitsᵁ (sym (trans (sm-pour pre (decX a) cs) (cong (λ z → addpᵁ z _) e))) f)) k
  reads-sound a ps (ov _ _) ()

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

  ∈-over : ∀ a q S g → AdmK (proj₁ (decX a)) S → ¬ fitsᵁ (addpᵁ g (proj₂ (decX a)))
         → ov q g ∈ overOf (just a) q S g
  ∈-over a q S g ad ¬f =
    ∈-when (both (AdmK? (proj₁ (decX a)) S) (fitsᵁ? (addpᵁ g (proj₂ (decX a))))) (ad , ¬f) (here refl)

  ∈-pour : ∀ a q S g m → AdmK (proj₁ (decX a)) S → fitsᵁ (addpᵁ g (proj₂ (decX a)))
         → ch q S (addpᵁ g (proj₂ (decX a))) false ∈ readsᶜ a (ch q S g m)
  ∈-pour a q S g m ad f =
    ∈-when (both′ (AdmK? (proj₁ (decX a)) S) (fitsᵁ? (addpᵁ g (proj₂ (decX a))))) (ad , f) (here refl)

  Fin′ : ℕ → Y.Word → Set
  Fin′ q uY = IsTrue (Y.isFinal M (Y.run M q uY))

  mutual

    comp-run : ∀ {ps v} → RunU ps v → ∀ u uY q → map decX u ≡ ps → map decY uY ≡ v → Fin′ q uY
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

    comp-ch : ∀ {S pre cs m ps v} → ChU S pre cs m ps v → ∀ u uY q → map decX u ≡ ps → map decY uY ≡ v
            → Fin′ q uY → Acc reader (ch q S (sm pre cs) m) u
    comp-ch {S} {pre} {cs} {m} (pour {p = p} ad fi h) u uY q eu ev f with map-∷ u eu
    ... | a , u′ , refl , refl , eu′ =
      ch q S (sm pre cs) m , ch q S (addpᵁ (sm pre cs) (proj₂ (decX a))) false , Det.here ,
      ∈-pour a q S (sm pre cs) m ad (subst fitsᵁ (sm-pour pre (decX a) cs) (to (sm-fits (pre ∷ʳ decX a) cs) fi)) ,
      subst (λ g → Acc reader (ch q S g false) u′) (sm-pour pre (decX a) cs)
        (comp-ch h u′ uY q eu′ ev f)
    comp-ch {S} {pre} {cs} {m} (over ad ¬fi o) u uY q eu ev f with map-∷ u eu
    ... | a , u′ , refl , refl , eu′ =
      acc-silent (ch q S (sm pre cs) m) _ (a ∷ u′)
        (∈-++⁺ˡ (∈-over a q S (sm pre cs) ad
                  (λ h → ¬fi (from (sm-fits (pre ∷ʳ decX a) cs) (subst fitsᵁ (sym (sm-pour pre (decX a) cs)) h)))))
        (comp-ov o a u′ uY q refl eu′ ev f)
    comp-ch {S} {pre} {cs} (close r) u uY q eu ev f =
      acc-silent (ch q S (sm pre cs) false) (free q) u
        (∈-++⁺ʳ (overOf (hd u) q S (sm pre cs)) (here refl))
        (comp-run r u uY q eu ev f)

    comp-ov : ∀ {pre cs p ps v} → OverU pre cs p ps v → ∀ a u uY q → decX a ≡ p → map decX u ≡ ps
            → map decY uY ≡ v → Fin′ q uY → Acc reader (ov q (sm pre cs)) (a ∷ u)
    comp-ov {pre} {cs} (enter {S} {c} h) a u uY q ea eu ev f with map-∷ uY ev
    ... | b , uY′ , refl , eb , ev′ =
      acc-silent (ov q (sm pre cs)) _ (a ∷ u) (∈-enter q (sm pre cs) b S c eb (live-of (next q b) uY′ f))
        (subst (λ g → Acc reader (ch (next q b) S g true) (a ∷ u)) (sm-enter pre cs c)
          (comp-ch h (a ∷ u) uY′ (next q b) (cong₂ _∷_ ea eu) ev′ f))
    comp-ov {pre} {cs} (pass {S} {c} o) a u uY q ea eu ev f with map-∷ uY ev
    ... | b , uY′ , refl , eb , ev′ =
      acc-silent (ov q (sm pre cs)) _ (a ∷ u) (∈-pass q (sm pre cs) b S c eb (live-of (next q b) uY′ f))
        (comp-ov o a u uY′ (next q b) ea eu ev′ f)

-- the automaton accepts a word of pieces exactly when the reader
-- accepts it against some bound of M

ReadsSome : List (Fin kX) → Set
ReadsSome u = Σ[ uY ∈ Y.Word ] IsTrue (Y.isFinal M (Y.run M 0 uY)) × RunU (map decX u) (map decY uY)

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

  capOf : Letter Hi → ℕ
  capOf (st _ (fin (k ∣ _))) = k
  capOf _                    = 0

  wOf : P → ℕ
  wOf (_ , fin (j ∣ _)) = j
  wOf (_ , ∞)           = 0

  setOf : Letter Hi → List OpSet
  setOf (st S _) = S ∷ []
  setOf (op _)   = []

maxc maxw bound : ℕ
maxc  = maxL (map (λ b → capOf (decY b)) ys)
maxw  = maxL (map (λ a → wOf (decX a)) (allFin kX))
bound = maxw ℕ.+ maxc

sides : List Side
sides = ⁻ ∷ ⁺ ∷ []

gaps : ℕ → List Gᵁ
gaps N = open∞ ∷ stuck∞ ∷ concatMap (λ k → concatMap (λ s → map (gap (+ k) s) sides) sides) (upTo (ℕ.suc N))

sets : List OpSet
sets = concatMap (λ b → setOf (decY b)) ys

states : List ℕ
states = upTo (Y.size M)

univ : List Cfg
univ = map free states
    ++ concatMap (λ q → concatMap (λ S → concatMap (λ g → map (ch q S g) (false ∷ true ∷ [])) (gaps bound)) sets) states
    ++ concatMap (λ q → map (ov q) (gaps maxw)) states

data InGaps (N : ℕ) : Gᵁ → Set where
  open∞  : InGaps N open∞
  stuck∞ : InGaps N stuck∞
  gap    : ∀ {k} s t → k ℕ.≤ N → InGaps N (gap (+ k) s t)

data Good : Cfg → Set where
  free : ∀ {q} → q ℕ.< Y.size M → Good (free q)
  ch   : ∀ {q S g m} → q ℕ.< Y.size M → S ∈ sets → InGaps bound g → Good (ch q S g m)
  ov   : ∀ {q g} → q ℕ.< Y.size M → InGaps maxw g → Good (ov q g)

private
  in-sides : ∀ s → s ∈ sides
  in-sides ⁻ = here refl
  in-sides ⁺ = there (here refl)

  in-gaps : ∀ {N g} → InGaps N g → g ∈ gaps N
  in-gaps open∞ = here refl
  in-gaps stuck∞ = there (here refl)
  in-gaps {N} (gap {k} s t r) =
    there (there (∈-concatMap⁺ (λ k → concatMap (λ s → map (gap (+ k) s) sides) sides)
      (lose (∈-upTo⁺ (ℕ.s≤s r)) (∈-concatMap⁺ (λ s → map (gap (+ k) s) sides) (lose (in-sides s) (∈-map⁺ (gap (+ k) s) (in-sides t)))))))

  in-bools : ∀ m → m ∈ (false ∷ true ∷ [])
  in-bools false = here refl
  in-bools true  = there (here refl)

good⇒∈ : ∀ {c} → Good c → c ∈ univ
good⇒∈ (free {q} r) = ∈-++⁺ˡ (∈-map⁺ free (∈-upTo⁺ r))
good⇒∈ (ch {q} {S} {g} {m} r S∈ gg) =
  ∈-++⁺ʳ (map free states) (∈-++⁺ˡ
    (∈-concatMap⁺ (λ q → concatMap (λ S → concatMap (λ g → map (ch q S g) (false ∷ true ∷ [])) (gaps bound)) sets)
      (lose (∈-upTo⁺ r) (∈-concatMap⁺ (λ S → concatMap (λ g → map (ch q S g) (false ∷ true ∷ [])) (gaps bound))
        (lose S∈ (∈-concatMap⁺ (λ g → map (ch q S g) (false ∷ true ∷ []))
          (lose (in-gaps gg) (∈-map⁺ (ch q S g) (in-bools m)))))))))
good⇒∈ (ov {q} {g} r gg) =
  ∈-++⁺ʳ (map free states) (∈-++⁺ʳ (concatMap (λ q → concatMap (λ S → concatMap (λ g → map (ch q S g) (false ∷ true ∷ [])) (gaps bound)) sets) states)
    (∈-concatMap⁺ (λ q → map (ov q) (gaps maxw)) (lose (∈-upTo⁺ r) (∈-map⁺ (ov q) (in-gaps gg)))))

private
  gaps⁻ : ∀ {N g} → g ∈ gaps N → InGaps N g
  gaps⁻ (here refl) = open∞
  gaps⁻ (there (here refl)) = stuck∞
  gaps⁻ {N} (there (there m)) with find (∈-concatMap⁻ (λ k → concatMap (λ s → map (gap (+ k) s) sides) sides) {xs = upTo (ℕ.suc N)} m)
  ... | k , k∈ , m′ with find (∈-concatMap⁻ (λ s → map (gap (+ k) s) sides) {xs = sides} m′)
  ...   | s , _ , m″ with ∈-map⁻ (gap (+ k) s) m″
  ...     | t , _ , refl = gap s t (ℕ.≤-pred (upTo-< k∈))
    where
      upTo-< : ∀ {k M} → k ∈ upTo M → k ℕ.< M
      upTo-< = Data.List.Membership.Propositional.Properties.∈-upTo⁻

∈⇒good : ∀ {c} → c ∈ univ → Good c
∈⇒good m with ∈-++⁻ (map free states) m
... | inj₁ m′ with ∈-map⁻ free m′
...   | q , q∈ , refl = free (Data.List.Membership.Propositional.Properties.∈-upTo⁻ q∈)
∈⇒good m | inj₂ m′ with ∈-++⁻ (concatMap (λ q → concatMap (λ S → concatMap (λ g → map (ch q S g) (false ∷ true ∷ [])) (gaps bound)) sets) states) m′
... | inj₁ m″ with find (∈-concatMap⁻ (λ q → concatMap (λ S → concatMap (λ g → map (ch q S g) (false ∷ true ∷ [])) (gaps bound)) sets) {xs = states} m″)
...   | q , q∈ , m₁ with find (∈-concatMap⁻ (λ S → concatMap (λ g → map (ch q S g) (false ∷ true ∷ [])) (gaps bound)) {xs = sets} m₁)
...     | S , S∈ , m₂ with find (∈-concatMap⁻ (λ g → map (ch q S g) (false ∷ true ∷ [])) {xs = gaps bound} m₂)
...       | g , g∈ , m₃ with ∈-map⁻ (ch q S g) m₃
...         | b , _ , refl = ch (Data.List.Membership.Propositional.Properties.∈-upTo⁻ q∈) S∈ (gaps⁻ g∈)
∈⇒good m | inj₂ m′ | inj₂ m″ with find (∈-concatMap⁻ (λ q → map (ov q) (gaps maxw)) {xs = states} m″)
... | q , q∈ , m₁ with ∈-map⁻ (ov q) m₁
...   | g , g∈ , refl = ov (Data.List.Membership.Propositional.Properties.∈-upTo⁻ q∈) (gaps⁻ g∈)

------------------------------------------------------------------------
-- The moves stay among them

private
  cap-≤ : ∀ b {S k t} → decY b ≡ st S (fin (k ∣ t)) → k ℕ.≤ maxc
  cap-≤ b e = subst (ℕ._≤ maxc) (cong capOf e) (≤-maxL (∈-map⁺ (λ b → capOf (decY b)) (∈-allFin b)))

  w-≤ : ∀ a {j u} → proj₂ (decX a) ≡ fin (j ∣ u) → j ℕ.≤ maxw
  w-≤ a {j} {u} e =
    subst (ℕ._≤ maxw) (cong (λ h → wOf (proj₁ (decX a) , h)) e) (≤-maxL (∈-map⁺ (λ a → wOf (decX a)) (∈-allFin a)))

  set-∈ : ∀ b {S h} → decY b ≡ st S h → S ∈ sets
  set-∈ b e = ∈-concatMap⁺ (λ b → setOf (decY b)) (lose (∈-allFin b) (subst (λ ℓ → _ ∈ setOf ℓ) (sym e) (here refl)))

  init-good : ∀ b {S h} → decY b ≡ st S h → InGaps bound (init h)
  init-good b {h = ∞} e = open∞
  init-good b {h = fin (k ∣ t)} e =
    subst (λ d → InGaps bound (gap d ⁺ t)) (sym (ℤ.⊖-≥ {k} {0} ℕ.z≤n))
      (gap ⁺ t (ℕ.≤-trans (cap-≤ b e) (ℕ.m≤n+m maxc maxw)))

  pour-good : ∀ a {g} → InGaps bound g → fitsᵁ (addpᵁ g (proj₂ (decX a))) → InGaps bound (addpᵁ g (proj₂ (decX a)))
  pour-good a gg f with proj₂ (decX a) | decX-fin a
  pour-good a open∞ f | _ | _ = open∞
  pour-good a stuck∞ f | _ | _ = stuck∞
  pour-good a (gap {k} s t r) f | .(fin (j ∣ u)) | j , u , refl =
    subst (λ d → InGaps bound (gap d (s ∧ˢ u) t))
      (sym (trans (ℤ.[+m]-[+n]≡m⊖n k j) (ℤ.⊖-≥ jk)))
      (gap (s ∧ˢ u) t (ℕ.≤-trans (ℕ.m∸n≤m k j) r))
    where
      jk : j ℕ.≤ k
      jk = above-⊖ k j (subst (λ d → Above d (s ∧ˢ u) t) (ℤ.[+m]-[+n]≡m⊖n k j) f)

  over-good : ∀ a {g} → InGaps bound g → ¬ fitsᵁ (addpᵁ g (proj₂ (decX a))) → InGaps maxw g
  over-good a gg ¬f with proj₂ (decX a) in ew | decX-fin a
  over-good a open∞ ¬f | _ | _ = ⊥-elim (¬f tt)
  over-good a stuck∞ ¬f | _ | _ = stuck∞
  over-good a (gap {k} s t r) ¬f | .(fin (j ∣ u)) | j , u , refl =
    gap s t (ℕ.≤-trans (¬above-⊖ k j (λ h → ¬f (subst (λ d → Above d (s ∧ˢ u) t) (sym (ℤ.[+m]-[+n]≡m⊖n k j)) h)))
                       (w-≤ a ew))

  enter-good : ∀ b {g S h} → InGaps maxw g → decY b ≡ st S h → InGaps bound (addcᵁ g h)
  enter-good b {h = ∞} open∞ e = open∞
  enter-good b {h = fin _} open∞ e = open∞
  enter-good b {h = ∞} stuck∞ e = open∞
  enter-good b {h = fin (_ ∣ _)} stuck∞ e = stuck∞
  enter-good b {h = ∞} (gap s t r) e = open∞
  enter-good b {h = fin (c ∣ u)} (gap {k} s t r) e =
    subst (λ d → InGaps bound (gap d s (t ∧ˢ u))) (ℤ.pos-+ k c)
      (gap s (t ∧ˢ u) (ℕ.+-mono-≤ r (cap-≤ b e)))

  next-good : ∀ {q} b → q ℕ.< Y.size M → next q b ℕ.< Y.size M
  next-good b r = next-< M M-wf r b

  silent-good : ∀ x {c c′} → Good c → c′ ∈ silentᶜ x c → Good c′
  silent-good x (free r) m with start-∈ _ m
  ... | b , S , h , e , refl = ch (next-good b r) (set-∈ b e) (init-good b e)
  silent-good x (ch {q} {S} {g} {mm} r S∈ gg) m with ∈-++⁻ (overOf x q S g) m
  silent-good (just a) (ch {q} {S} {g} r S∈ gg) m | inj₁ m′ with over-∈ a q S g m′
  ... | refl , ad , ¬f = ov r (over-good a gg ¬f)
  silent-good x (ch {q} {S} {g} {mm} r S∈ gg) m | inj₂ m′ with close-∈ q mm m′
  ... | refl , _ = free r
  silent-good (just a) (ov {q} {g} r gg) m with enter-∈ q g m
  ... | b , S , h , e , inj₁ refl = ch (next-good b r) (set-∈ b e) (enter-good b gg e)
  ... | b , S , h , e , inj₂ refl = ov (next-good b r) gg
  silent-good nothing (ov r gg) ()

  reads-good : ∀ a {c c′} → Good c → c′ ∈ readsᶜ a c → Good c′
  reads-good a (free {q} r) m with match-∈ a q m
  ... | b , o , e , k , refl = free (next-good b r)
  reads-good a (ch {q} {S} {g} {mm} r S∈ gg) m with pour-∈ a q S g mm m
  ... | refl , ad , f = ch r S∈ (pour-good a gg f)
  reads-good a (ov _ _) ()

------------------------------------------------------------------------
-- The table of the reader against M

open Det.Determinise _≟ᶜ_ reader univ
  (good⇒∈ (free (start-< M M-wf)))
  (λ x m m′ → good⇒∈ (silent-good x (∈⇒good m) m′))
  (λ a m m′ → good⇒∈ (reads-good a (∈⇒good m) m′))
  public using (determinised; determinised-wf; ∈-determinised)

-- a word of pieces is in the table exactly when the reader accepts it
-- against some bound of M

∈-reader : ∀ u → Automaton._∈_ kX u determinised ⇔ ReadsSome u
∈-reader u = mk⇔ (λ t → to (accepts⇔ u) (to (∈-determinised u) t))
                 (λ r → from (∈-determinised u) (from (accepts⇔ u) r))
