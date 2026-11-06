------------------------------------------------------------------------
-- Mode times: the time a computation spends in each mode of a        --
-- device, between a start and an end mode.                           --
--                                                                    --
-- A grade gives each pair of a start and an end mode either no       --
-- trace, or a realisable box of the times of its traces: an interval --
-- of whole steps for the time in each mode and for the total time    --
-- (`ModeTimes.Boxes`). It is a mode matrix over the boxes            --
-- (`Matrix.ModeGrade`): total, its only trace from `stuck` to        --
-- `stuck` at no time, and each change between two distinct ordinary  --
-- modes a change, its total time having a positive upper end.        --
-- Sequencing is the matrix product, the boxes adding up along a      --
-- trace, the join is the entrywise hull, and the order entrywise     --
-- inclusion, no trace least. The unit keeps every mode at no time    --
-- and is not least; the product does not commute.                    --
--                                                                    --
-- A delay keeps the mode and its time is spent in it (`delays`). An  --
-- operation takes its running time in the mode it starts from, its   --
-- change of mode taking effect at its end, and gets stuck at no time --
-- from a mode it is not performed in (`occurrence`); the running     --
-- times are a parameter of the operations' grades, as in the cost    --
-- models. A grade is listed by entries between named modes, modes    --
-- not named `⋆` and `⋆'`, and `stuck` `✗`, each entry a template     --
-- naming its own start mode (`listing`, `Template`); a mode from     --
-- which no entry starts is stuck at no time.                         --
------------------------------------------------------------------------

module Grades.Examples.SemiDirect.ModeTimes where

open import Data.Bool.Base using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; concatMap) renaming (map to mapᴸ)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; _≡ᵇ_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to 𝟙ᵗ)
open import Function.Base using (_$_)
open import Relation.Nullary using (¬_; Dec; yes; no; ¬?)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)
open import Grades.Indexed using (ℕ-names; module Maps; Names)
open import Grades.Examples.Time.Interval
open import Grades.Examples.SemiDirect.ModeTimes.Boxes
open import Grades.Matrix.Dioid using (Dioid)
open import Grades.Matrix.Nominal ℕ-names using (Equivariant)
open import Grades.Matrix.Modes ℕ-names
  using (Mode; stuck; ⌜_⌝; Name; _≟ᴺ_; _∈?_; swap; swapᴹ; swap-a; swap-b; swap-fix; swap-inv; swap-∈; swap-∉;
         swap-injective; ⌜⌝-injective)

import Grades.Matrix.Modes
import Data.List.Base

open import Util.Equality

open Maps ℕ-names using (Map; _∣_; _!_; others; named; lookup; everywhere; map₂; !-map₂;
                         pointwise⁻; pointwise⁺)

private
  module T = Dioid times
  module Eq = Equivariant equivariant-times
  module I = Grade interval
open T using () renaming (Carrier to Entry; _≤_ to _≤ᵗ_; _≈_ to _≈ᵗ_)

------------------------------------------------------------------------
-- The conditions of mode matrices: a change has a total with a
-- positive upper end

Change : Entry → Set
Change (nothing , _)        = 𝟙ᵗ
Change (just (m , t) , _)   = ¬ (t ≾ᵢ 𝟏ᵢ)

change? : ∀ x → Dec (Change x)
change? (nothing , _)      = yes tt
change? (just (m , t) , _) = ¬? (t ≾ᵢ? 𝟏ᵢ)

private
  totals : ∀ {m t m' t' r r'} → (just (m , t) , r) ≤ᵗ (just (m' , t') , r') → t ≾ᵢ t'
  totals (_ , q) = q

  not-𝟏 : ∀ {t t'} → ¬ (t ≾ᵢ 𝟏ᵢ) → t ≾ᵢ t' → ¬ (t' ≾ᵢ 𝟏ᵢ)
  not-𝟏 {t} {t'} n p q = n (I.≾-trans {t} {t'} {𝟏ᵢ} p q)

open import Grades.Matrix.ModeGrade ℕ-names times equivariant-times

time-entries : ModeEntries
time-entries = record
  { nontrivial       = λ ()
  ; no-zero-divisors = λ { {nothing , _} _ → inj₁ tt
                         ; {just _ , _} {nothing , _} _ → inj₂ tt
                         ; {just _ , _} {just _ , _} () }
  ; unit-reflects     = λ { {just (m , t) , _} {just (m' , t') , _} (p , q) _ _ →
                              ( pointwise⁺ _≾ᵢ_ {m} {everywhere 𝟏ᵢ} (λ s → I.≾-zero-productˡ {m ! s} {m' ! s}
                                   (subst (_≾ᵢ 𝟏ᵢ) (!-map₂ _·ᵢ_ m m' s) (pointwise⁻ _≾ᵢ_ {map₂ _·ᵢ_ m m'} {everywhere 𝟏ᵢ} p s)))
                              , I.≾-zero-productˡ {t} {t'} q )
                            , ( pointwise⁺ _≾ᵢ_ {m'} {everywhere 𝟏ᵢ} (λ s → I.≾-zero-productʳ {m ! s} {m' ! s}
                                   (subst (_≾ᵢ 𝟏ᵢ) (!-map₂ _·ᵢ_ m m' s) (pointwise⁻ _≾ᵢ_ {map₂ _·ᵢ_ m m'} {everywhere 𝟏ᵢ} p s)))
                              , I.≾-zero-productʳ {t} {t'} q )
                          ; {nothing , _} _ a≰ _ → ⊥-elim (a≰ tt)
                          ; {just _ , _} {nothing , _} _ _ b≰ → ⊥-elim (b≰ tt) }
  ; Change           = Change
  ; change-𝟘         = λ { {nothing , _} _ → tt ; {just _ , _} () }
  ; change-⊤         = λ { (_ , ()) }
  ; change-≈         = λ { {nothing , _} {nothing , _} _ c → tt
                         ; {just _ , _} {nothing , _} (() , _) c
                         ; {nothing , _} {just _ , _} (_ , ()) c
                         ; {just (_ , t) , _} {just (_ , t') , _} ((_ , q) , _) c → not-𝟏 {t} {t'} c q }
  ; change-⊕         = λ { {nothing , _} _ c → c
                         ; {just _ , _} {nothing , _} c _ → c
                         ; {just (_ , t) , _} {just (_ , t') , _} c _ → not-𝟏 {t} {t ⊔ᵢ t'} c (I.⊔-ubˡ t t') }
  ; change-⊗ˡ        = λ { {nothing , _} _ → tt
                         ; {just _ , _} {nothing , _} _ → tt
                         ; {just (_ , t) , _} {just (_ , t') , _} c q → c (I.≾-zero-productˡ {t} {t'} q) }
  ; change-⊗ʳ        = λ { {nothing , _} _ → tt
                         ; {just _ , _} {nothing , _} _ → tt
                         ; {just (_ , t) , _} {just (_ , t') , _} c q → c (I.≾-zero-productʳ {t} {t'} q) }
  ; change-not-unit  = λ { {nothing , _} _ a≰ _ _ → a≰ tt
                         ; {just _ , _} {nothing , _} _ _ b≰ _ → b≰ tt
                         ; {just (_ , t) , _} {just (_ , t') , _} c _ _ (_ , q) → c (I.≾-zero-productˡ {t} {t'} q) }
  ; change-act       = λ { {x = nothing , _} c → tt ; {x = just _ , _} c → c }
  ; change-orbit     = λ { {x = nothing , _} c → tt ; {x = just _ , _} c → c }
  }

open import Grades.Matrix.Matrices ℕ-names times equivariant-times
  using (Matrix; module Matrix; entry; _≟ᴹ_; Iᴹ; Iᴹ-diag; Iᴹ-off; _⊗ᴹ_; ⊗ᴹ-ub; ⊗ᴹ-lub;
         pointwise⇒≤ᴹ; _≤ᵖ_; _≤ᴹ_)
open Matrix

------------------------------------------------------------------------
-- A time spent in the start mode

private
  ≈-just : ∀ {m m' t t'} r r'
         → (∀ s → m ! s ≡ m' ! s) → t ≡ t'
         → (just (m , t) , r) ≈ᵗ (just (m' , t') , r')
  ≈-just {m} {m'} {t} _ _ e refl =
      (pointwise⁺ _≾ᵢ_ {m} {m'} (λ s → I.≾-reflexive (e s)) , I.≾-refl {t})
    , (pointwise⁺ _≾ᵢ_ {m'} {m} (λ s → I.≾-reflexive (sym (e s))) , I.≾-refl {t})

  sel : ∀ {A X : Set} → Dec A → X → X → X
  sel (yes _) x _ = x
  sel (no _)  _ y = y

  sel-iff : ∀ {A B X : Set} {x y : X} → (A → B) → (B → A) → (d : Dec A) (d' : Dec B) → sel d x y ≡ sel d' x y
  sel-iff f g (yes a) (yes b) = refl
  sel-iff f g (yes a) (no ¬b) = ⊥-elim (¬b (f a))
  sel-iff f g (no ¬a) (yes b) = ⊥-elim (¬a (g b))
  sel-iff f g (no ¬a) (no ¬b) = refl

-- the box with `i` in one mode and nothing elsewhere

single : Name → Interval∞ → Map Interval∞
single p i = 𝟏ᵢ ∣ ((p , i) ∷ [])

private
  single-! : ∀ p i s → single p i ! s ≡ sel (s ≟ᴺ p) i 𝟏ᵢ
  single-! p i s with s ≟ᴺ p
  ... | yes _ = refl
  ... | no _  = refl

  single-swap : ∀ a b p i s → single (swap a b p) i ! s ≡ single p i ! swap a b s
  single-swap a b p i s =
    trans (single-! (swap a b p) i s)
      (trans (sel-iff (λ e → trans (cong (swap a b) e) (swap-inv a b p))
                      (λ e → trans (sym (swap-inv a b s)) (cong (swap a b) e))
                      (s ≟ᴺ swap a b p) (swap a b s ≟ᴺ p))
             (sym (single-! p i (swap a b s))))

  0+ : ∀ n → n + 0 ≡ n
  0+ = ℕₚ.+-identityʳ

  min∈ : ∀ i → min i ∈ᵢ i
  min∈ i = ℕₚ.≤-refl , min≤max i

-- the time `i` spent in the start mode `p`

spent : Interval∞ → Name → Entry
spent i p =
  just (single p i , i) ,
  witness ((p , min i) ∷ []) ((λ ()) , tt) ,
  fits ,
  subst (_∈ᵢ i) (sym (0+ (min i))) (min∈ i)
  where
    fits : ∀ s → time ((p , min i) ∷ []) s ∈ᵢ single p i ! s
    fits s with s ≟ᴺ p
    ... | yes _ = min∈ i
    ... | no _  = 0∈𝟏ᵢ

spent-swap : ∀ i a b p → spent i (swap a b p) ≈ᵗ Eq.act a b (spent i p)
spent-swap i a b p = ≈-just {single (swap a b p) i} {rename (swap a b) (single p i)} {i} {i}
  (proj₂ (spent i (swap a b p))) (proj₂ (Eq.act a b (spent i p))) (λ s → trans (single-swap a b p i s) (sym (rename-! a b (single p i) s))) refl

------------------------------------------------------------------------
-- Templates: entries naming their start mode, alike for the modes not
-- in `F`

record Template (F : List Name) : Set where
  field
    at          : Name → Entry
    equivariant : ∀ {a b} → a ∉ F → b ∉ F → ∀ p → at (swap a b p) ≈ᵗ Eq.act a b (at p)

open Template public

-- no trace, and stuck at no time

none none-stuck : ∀ {F} → Template F
at none _ = T.𝟘
equivariant none {a} {b} _ _ _ = T.≈-sym {Eq.act a b T.𝟘} {T.𝟘} (Eq.act-𝟘 a b)
at none-stuck _ = T.𝟙
equivariant none-stuck {a} {b} _ _ _ = T.≈-sym {Eq.act a b T.𝟙} {T.𝟙} (Eq.act-𝟙 a b)

-- a time spent in the start mode

in-start : ∀ {F} → Interval∞ → Template F
at (in-start i) = spent i
equivariant (in-start i) {a} {b} _ _ p = spent-swap i a b p

-- a box naming only modes in `F`, the same from every start mode,
-- realisable by the given summary

private
  _∈ᵢ?_ : ∀ n i → Dec (n ∈ᵢ i)
  n ∈ᵢ? i = (min i ℕₚ.≤? n) ×-dec (↑ n ≤∞? max i)

  keysᴹ : Map Interval∞ → List Name
  keysᴹ m = mapᴸ proj₁ (named m)

  time-∉ : ∀ es s → s ∉ keys es → time es s ≡ 0
  time-∉ []              s _ = refl
  time-∉ ((s' , n) ∷ es) s p with s ≟ᴺ s'
  ... | yes e = ⊥-elim (p (here e))
  ... | no _  = time-∉ es s (λ q → p (there q))

  lookup-∉′ : ∀ (d : Interval∞) es s → s ∉ mapᴸ proj₁ es → lookup d es s ≡ d
  lookup-∉′ d []              s _ = refl
  lookup-∉′ d ((s' , c) ∷ es) s p with s ≟ᴺ s'
  ... | yes e = ⊥-elim (p (here e))
  ... | no _  = lookup-∉′ d es s (λ q → p (there q))

  lookup-swap : ∀ {F a b} (d : Interval∞) es → (∀ {k} → k ∈ mapᴸ proj₁ es → k ∈ F) → a ∉ F → b ∉ F
              → ∀ s → lookup d es (swap a b s) ≡ lookup d es s
  lookup-swap d []              sub a∉ b∉ s = refl
  lookup-swap {F} {a} {b} d ((k , c) ∷ es) sub a∉ b∉ s with swap a b s ≟ᴺ k | s ≟ᴺ k
  ... | yes _ | yes _ = refl
  ... | yes e | no ne = ⊥-elim (ne (trans (sym (swap-inv a b s)) (trans (cong (swap a b) e) (swap-∈ a∉ b∉ (sub (here refl))))))
  ... | no ne | yes e = ⊥-elim (ne (trans (cong (swap a b) e) (swap-∈ a∉ b∉ (sub (here refl)))))
  ... | no _  | no _  = lookup-swap d es (λ q → sub (there q)) a∉ b∉ s

module _ (w : Witness) (m : Map Interval∞) (t : Interval∞) where

  private
    es = entries w
    candidates : List Name
    candidates = fresh-name ∷ (keys es Data.List.Base.++ keysᴹ m)
      where
        open import Data.List.Base using (_++_)
        fresh-name = Names.fresh ℕ-names (keys es ++ keysᴹ m)

  -- whether the summary fits the box, decided at its modes, those of
  -- the box and a fresh one
  fits? : Dec (Fits w m t)
  fits? with All.all? (λ s → time es s ∈ᵢ? (m ! s)) candidates
                 | total-time es ∈ᵢ? t
  ... | no ¬all | _ = no λ (f , _) → ¬all (All.tabulate λ {s} _ → f s)
  ... | yes _ | no ¬tot = no λ (_ , tot) → ¬tot tot
  ... | yes all | yes tot = yes (pointwise , tot)
    where
      open import Data.List.Base using (_++_)
      open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
      f₀ = Names.fresh ℕ-names (keys es ++ keysᴹ m)
      f₀∉ = Names.fresh-∉ ℕ-names (keys es ++ keysᴹ m)
      pointwise : ∀ s → time es s ∈ᵢ m ! s
      pointwise s with s ∈? (keys es ++ keysᴹ m)
      ... | yes s∈ = All.lookup all (there s∈)
      ... | no s∉ =
        subst₂ _∈ᵢ_ (trans (time-∉ es f₀ (λ p → f₀∉ (∈-++⁺ˡ p))) (sym (time-∉ es s (λ p → s∉ (∈-++⁺ˡ p)))))
                    (trans (lookup-∉′ (others m) (named m) f₀ (λ p → f₀∉ (∈-++⁺ʳ (keys es) p)))
                           (sym (lookup-∉′ (others m) (named m) s (λ p → s∉ (∈-++⁺ʳ (keys es) p)))))
                    (All.lookup all (here refl))

open import Relation.Nullary.Decidable using (True; toWitness)

bounds : ∀ {F} (m : Map Interval∞) (t : Interval∞) (w : Witness)
       → {fit : True (fits? w m t)}
       → {sub : True (All.all? (λ k → k ∈? F) (keysᴹ m))}
       → Template F
at (bounds m t w {fit}) _ = just (m , t) , w , toWitness fit
equivariant (bounds {F} m t w {fit} {sub}) {a} {b} a∉ b∉ p =
  ≈-just {m} {rename (swap a b) m} {t} {t} (w , toWitness fit) (proj₂ (Eq.act a b (just (m , t) , w , toWitness fit)))
    (λ s → sym (trans (rename-! a b m s)
                      (lookup-swap (others m) (named m)
                         (λ k∈ → All.lookup (toWitness sub) k∈) a∉ b∉ s)))
    refl

------------------------------------------------------------------------
-- Listings of entries

-- a mode named, one not named, another not named, and `stuck`

data Point : Set where
  ⟨_⟩ : ℕ → Point
  ⋆ ⋆' ✗ : Point

_==_ : Point → Point → Bool
⟨ m ⟩ == ⟨ n ⟩ = m ≡ᵇ n
⋆     == ⋆     = true
⋆'    == ⋆'    = true
✗     == ✗     = true
_     == _     = false

module Listing (F : List Name) where

  -- the point of a start mode, and of an end mode from it

  start-point : Name → Point
  start-point p = sel (p ∈? F) ⟨ p ⟩ ⋆

  end-point : Name → Mode → Point
  end-point p stuck   = ✗
  end-point p ⌜ q ⌝ = sel (q ∈? F) ⟨ q ⟩ (sel (q ≟ᴺ p) ⋆ ⋆')

  private
    sel-yes : ∀ {A X : Set} {x y : X} → A → (d : Dec A) → sel d x y ≡ x
    sel-yes a (yes _) = refl
    sel-yes a (no ¬a) = ⊥-elim (¬a a)

    sel-no : ∀ {A X : Set} {x y : X} → ¬ A → (d : Dec A) → sel d x y ≡ y
    sel-no ¬a (yes a) = ⊥-elim (¬a a)
    sel-no ¬a (no _)  = refl

    named-swap : ∀ {a b} → a ∉ F → b ∉ F → ∀ q {X : Set} {f : Name → X} {y : X}
               → sel (swap a b q ∈? F) (f (swap a b q)) y ≡ sel (q ∈? F) (f q) y
    named-swap {a} {b} a∉ b∉ q {X} {f} {y} = case (q ∈? F)
      where
        case : (d : Dec (q ∈ F)) → sel (swap a b q ∈? F) (f (swap a b q)) y ≡ sel d (f q) y
        case (yes q∈) =
          trans (cong (λ r → sel (r ∈? F) (f r) y) (swap-∈ a∉ b∉ q∈)) (sel-yes q∈ (q ∈? F))
        case (no q∉)  = sel-no (swap-∉ a∉ b∉ q∉) (swap a b q ∈? F)

  start-swap : ∀ {a b} → a ∉ F → b ∉ F → ∀ p → start-point (swap a b p) ≡ start-point p
  start-swap a∉ b∉ p = named-swap a∉ b∉ p {f = ⟨_⟩}

  end-swap : ∀ {a b} → a ∉ F → b ∉ F → ∀ p y → end-point (swap a b p) (swapᴹ a b y) ≡ end-point p y
  end-swap a∉ b∉ p stuck = refl
  end-swap {a} {b} a∉ b∉ p ⌜ q ⌝ =
    trans (named-swap a∉ b∉ q {f = ⟨_⟩} {y = sel (swap a b q ≟ᴺ swap a b p) ⋆ ⋆'})
          (cong (sel (q ∈? F) ⟨ q ⟩)
                (sel-iff (λ e → swap-injective e) (cong (swap a b)) (swap a b q ≟ᴺ swap a b p) (q ≟ᴺ p)))

  -- the template of an entry, and whether a point starts one

  find : List (Point × Point × Template F) → Point → Point → Maybe (Template F)
  find []                   x y = nothing
  find ((x' , y' , T) ∷ es) x y = if (x == x') ∧ (y == y') then just T else find es x y

  starts : List (Point × Point × Template F) → Point → Bool
  starts []                 x = false
  starts ((x' , _ , _) ∷ es) x = (x == x') ∨ starts es x

  -- the entry from a start mode with no entry of its own: stuck at no
  -- time where the start point starts no entry
  unlisted : Bool → Mode → Entry
  unlisted false stuck   = T.𝟙
  unlisted _     _       = T.𝟘

  entry-of : Maybe (Template F) → Bool → Name → Mode → Entry
  entry-of (just T) _ p _ = at T p
  entry-of nothing  b p y = unlisted b y

  private
    unlisted-swap : ∀ a b s y → unlisted s (swapᴹ a b y) ≈ᵗ Eq.act a b (unlisted s y)
    unlisted-swap a b false stuck   = T.≈-sym {Eq.act a b T.𝟙} {T.𝟙} (Eq.act-𝟙 a b)
    unlisted-swap a b false ⌜ _ ⌝ = T.≈-sym {Eq.act a b T.𝟘} {T.𝟘} (Eq.act-𝟘 a b)
    unlisted-swap a b true  stuck   = T.≈-sym {Eq.act a b T.𝟘} {T.𝟘} (Eq.act-𝟘 a b)
    unlisted-swap a b true  ⌜ _ ⌝ = T.≈-sym {Eq.act a b T.𝟘} {T.𝟘} (Eq.act-𝟘 a b)

    entry-of-swap : ∀ {a b} → a ∉ F → b ∉ F → ∀ t s p y
                  → entry-of t s (swap a b p) (swapᴹ a b y) ≈ᵗ Eq.act a b (entry-of t s p y)
    entry-of-swap a∉ b∉ (just T) s p y = equivariant T a∉ b∉ p
    entry-of-swap {a} {b} a∉ b∉ nothing s p y = unlisted-swap a b s y

  -- the matrix of a list of entries

  listing : List (Point × Point × Template F) → Matrix
  modes (listing es) = F
  row (listing es) p y = entry-of (find es (start-point p) (end-point p y)) (starts es (start-point p)) p y
  equivariant (listing es) {a} {b} a∉ b∉ p y =
    subst₂ (λ x z → entry-of (find es x z) (starts es x) (swap a b p) (swapᴹ a b y)
                      ≈ᵗ Eq.act a b (entry-of (find es (start-point p) (end-point p y)) (starts es (start-point p)) p y))
           (sym (start-swap a∉ b∉ p)) (sym (end-swap a∉ b∉ p y))
           (entry-of-swap a∉ b∉ (find es (start-point p) (end-point p y)) (starts es (start-point p)) p y)

------------------------------------------------------------------------
-- The grade

open ModeEntries time-entries using ()
open Decided time-entries change? public using (decided)
open ModeMatrix

-- the entries of a grade

entryᵐ : ModeMatrix time-entries → Mode → Mode → Entry
entryᵐ x = entry (mat x)

-- a listed grade

listed : (F : List Name) (es : List (Point × Point × Template F))
       → {t : True (Decided.total? time-entries change? (Listing.listing F es))}
       → {c : True (Decided.changes? time-entries change? (Listing.listing F es))}
       → ModeMatrix time-entries
listed F es {t} {c} = decided (Listing.listing F es) {t} {c}

-- an operation performed from the start points of `behaviour`, taking
-- each to its end point and spending the running time `rt` in the
-- start mode, or getting stuck at no time

occurrence-entries : ∀ {F} → List (Point × Point) → Interval∞ → List (Point × Point × Template F)
occurrence-entries []             rt = []
occurrence-entries ((x , y) ∷ bs) rt =
  (x , y , (if y == ✗ then none-stuck else in-start rt)) ∷ occurrence-entries bs rt

behaviour-modes : List (Point × Point) → List Name
behaviour-modes = concatMap λ { (x , y) → name x Data.List.Base.++ name y }
  where
    name : Point → List Name
    name ⟨ n ⟩ = n ∷ []
    name _     = []

occurrence : (bs : List (Point × Point)) (rt : Interval∞)
           → {t : True (Decided.total? time-entries change?
                          (Listing.listing (behaviour-modes bs) (occurrence-entries bs rt)))}
           → {c : True (Decided.changes? time-entries change?
                          (Listing.listing (behaviour-modes bs) (occurrence-entries bs rt)))}
           → ModeMatrix time-entries
occurrence bs rt {t} {c} = listed (behaviour-modes bs) (occurrence-entries bs rt) {t} {c}

------------------------------------------------------------------------
-- Delays: the mode kept, the time spent in it

private
  dur : ℕ → Interval∞
  dur = Grade.ι interval

delay-matrix : ℕ → Matrix
modes (delay-matrix n) = []
row (delay-matrix n) p y = sel (y ≟ᴹ ⌜ p ⌝) (spent (dur n) p) T.𝟘
equivariant (delay-matrix n) {a} {b} _ _ p y =
  subst (λ e → e ≈ᵗ Eq.act a b (sel (y ≟ᴹ ⌜ p ⌝) (spent (dur n) p) T.𝟘))
        (sym (sel-iff (λ e → swapᴹ-injective e) (λ e → cong (swapᴹ a b) e) (swapᴹ a b y ≟ᴹ ⌜ swap a b p ⌝) (y ≟ᴹ ⌜ p ⌝)))
        (case (y ≟ᴹ ⌜ p ⌝))
  where
    swapᴹ-injective : ∀ {x z} → swapᴹ a b x ≡ swapᴹ a b z → x ≡ z
    swapᴹ-injective {x} {z} e =
      trans (sym (Grades.Matrix.Modes.swapᴹ-inv ℕ-names a b x))
        (trans (cong (swapᴹ a b) e) (Grades.Matrix.Modes.swapᴹ-inv ℕ-names a b z))
    case : (d : Dec (y ≡ ⌜ p ⌝)) → sel d (spent (dur n) (swap a b p)) T.𝟘 ≈ᵗ Eq.act a b (sel d (spent (dur n) p) T.𝟘)
    case (yes _) = spent-swap (dur n) a b p
    case (no _)  = T.≈-sym {Eq.act a b T.𝟘} {T.𝟘} (Eq.act-𝟘 a b)

private
  sel-yes′ : ∀ {A X : Set} {x y : X} → A → (d : Dec A) → sel d x y ≡ x
  sel-yes′ a (yes _) = refl
  sel-yes′ a (no ¬a) = ⊥-elim (¬a a)

  sel-no′ : ∀ {A X : Set} {x y : X} → ¬ A → (d : Dec A) → sel d x y ≡ y
  sel-no′ ¬a (yes a) = ⊥-elim (¬a a)
  sel-no′ ¬a (no _)  = refl

  diag-entry : ∀ n p → entry (delay-matrix n) ⌜ p ⌝ ⌜ p ⌝ ≡ spent (dur n) p
  diag-entry n p = sel-yes′ refl (⌜ p ⌝ ≟ᴹ ⌜ p ⌝)

  off-entry : ∀ n p {y} → ¬ y ≡ ⌜ p ⌝ → entry (delay-matrix n) ⌜ p ⌝ y ≡ T.𝟘
  off-entry n p {y} ne = sel-no′ ne (y ≟ᴹ ⌜ p ⌝)

  -- the boxes of delays, pointwise
  zero-box : ∀ p → spent (dur 0) p ≈ᵗ T.𝟙
  zero-box p =
      (pointwise⁺ _≾ᵢ_ {single p (dur 0)} {everywhere 𝟏ᵢ}
         (λ s → subst (_≾ᵢ 𝟏ᵢ) (sym (single-! p (dur 0) s)) (le (s ≟ᴺ p))) , (z≤n , z≤n))
    , (pointwise⁺ _≾ᵢ_ {everywhere 𝟏ᵢ} {single p (dur 0)}
         (λ s → subst (𝟏ᵢ ≾ᵢ_) (sym (single-! p (dur 0) s)) (ge (s ≟ᴺ p))) , (z≤n , z≤n))
    where
      le : ∀ {A : Set} (d : Dec A) → sel d (dur 0) 𝟏ᵢ ≾ᵢ 𝟏ᵢ
      le (yes _) = z≤n , z≤n
      le (no _)  = z≤n , z≤n
      ge : ∀ {A : Set} (d : Dec A) → 𝟏ᵢ ≾ᵢ sel d (dur 0) 𝟏ᵢ
      ge (yes _) = z≤n , z≤n
      ge (no _)  = z≤n , z≤n

  plus-box : ∀ m n p → spent (dur (m + n)) p ≈ᵗ T._⊗_ (spent (dur m) p) (spent (dur n) p)
  plus-box m n p =
      (pointwise⁺ _≾ᵢ_ {single p (dur (m + n))} {map₂ _·ᵢ_ (single p (dur m)) (single p (dur n))}
         (λ s → subst₂ _≾ᵢ_ (sym (single-! p (dur (m + n)) s))
                  (sym (trans (!-map₂ _·ᵢ_ (single p (dur m)) (single p (dur n)) s)
                              (cong₂ _·ᵢ_ (single-! p (dur m) s) (single-! p (dur n) s))))
                  (le (s ≟ᴺ p)))
      , (ℕₚ.≤-refl , ℕₚ.≤-refl))
    , (pointwise⁺ _≾ᵢ_ {map₂ _·ᵢ_ (single p (dur m)) (single p (dur n))} {single p (dur (m + n))}
         (λ s → subst₂ _≾ᵢ_
                  (sym (trans (!-map₂ _·ᵢ_ (single p (dur m)) (single p (dur n)) s)
                              (cong₂ _·ᵢ_ (single-! p (dur m) s) (single-! p (dur n) s))))
                  (sym (single-! p (dur (m + n)) s))
                  (ge (s ≟ᴺ p)))
      , (ℕₚ.≤-refl , ℕₚ.≤-refl))
    where
      le : ∀ {A : Set} (d : Dec A) → sel d (dur (m + n)) 𝟏ᵢ ≾ᵢ (sel d (dur m) 𝟏ᵢ ·ᵢ sel d (dur n) 𝟏ᵢ)
      le (yes _) = ℕₚ.≤-refl , ℕₚ.≤-refl
      le (no _)  = z≤n , z≤n
      ge : ∀ {A : Set} (d : Dec A) → (sel d (dur m) 𝟏ᵢ ·ᵢ sel d (dur n) 𝟏ᵢ) ≾ᵢ sel d (dur (m + n)) 𝟏ᵢ
      ge (yes _) = ℕₚ.≤-refl , ℕₚ.≤-refl
      ge (no _)  = z≤n , z≤n

delayᵐ : ℕ → ModeMatrix time-entries
mat (delayᵐ n) = delay-matrix n
total (delayᵐ n) p = ⌜ p ⌝ , λ le → subst (λ e → ¬ (e ≤ᵗ T.𝟘)) (sym (diag-entry n p)) (λ ()) le
changes (delayᵐ n) {p} {q} ne =
  ModeEntries.change-𝟘 time-entries (T.≤-reflexive (off-entry n p (λ e → ne (sym (⌜⌝-injective e)))))

private
  stuck-rows : ∀ {M N : Matrix} {y} → entry M stuck y ≤ᵗ entry N stuck y
  stuck-rows {y = stuck}   = T.≤-refl {T.𝟙}
  stuck-rows {y = ⌜ _ ⌝} = T.≤-refl {T.𝟘}

  delay-zero : (mat (delayᵐ 0) ≤ᴹ Iᴹ) × (Iᴹ ≤ᴹ mat (delayᵐ 0))
  delay-zero = pointwise⇒≤ᴹ le , pointwise⇒≤ᴹ ge
    where
      le : mat (delayᵐ 0) ≤ᵖ Iᴹ
      le stuck y = stuck-rows {mat (delayᵐ 0)} {Iᴹ} {y}
      le ⌜ p ⌝ y = case (y ≟ᴹ ⌜ p ⌝)
        where
          case : Dec (y ≡ ⌜ p ⌝) → entry (delay-matrix 0) ⌜ p ⌝ y ≤ᵗ entry Iᴹ ⌜ p ⌝ y
          case (yes refl) = subst₂ _≤ᵗ_ (sym (diag-entry 0 p)) (sym (Iᴹ-diag ⌜ p ⌝)) (proj₁ (zero-box p))
          case (no ne) = subst (_≤ᵗ entry Iᴹ ⌜ p ⌝ y) (sym (off-entry 0 p ne)) (T.𝟘-≤ (entry Iᴹ ⌜ p ⌝ y))
      ge : Iᴹ ≤ᵖ mat (delayᵐ 0)
      ge stuck y = stuck-rows {Iᴹ} {mat (delayᵐ 0)} {y}
      ge ⌜ p ⌝ y = case (y ≟ᴹ ⌜ p ⌝)
        where
          case : Dec (y ≡ ⌜ p ⌝) → entry Iᴹ ⌜ p ⌝ y ≤ᵗ entry (delay-matrix 0) ⌜ p ⌝ y
          case (yes refl) = subst₂ _≤ᵗ_ (sym (Iᴹ-diag ⌜ p ⌝)) (sym (diag-entry 0 p)) (proj₂ (zero-box p))
          case (no ne) = subst (_≤ᵗ entry (delay-matrix 0) ⌜ p ⌝ y) (sym (Iᴹ-off (λ e → ne (sym e))))
                               (T.𝟘-≤ (entry (delay-matrix 0) ⌜ p ⌝ y))

  delay-plus : ∀ m n → (mat (delayᵐ (m + n)) ≤ᴹ (mat (delayᵐ m) ⊗ᴹ mat (delayᵐ n)))
                     × ((mat (delayᵐ m) ⊗ᴹ mat (delayᵐ n)) ≤ᴹ mat (delayᵐ (m + n)))
  delay-plus m n = pointwise⇒≤ᴹ le , pointwise⇒≤ᴹ ge
    where
      Dm = delay-matrix m
      Dn = delay-matrix n
      le : delay-matrix (m + n) ≤ᵖ (Dm ⊗ᴹ Dn)
      le stuck y = stuck-rows {delay-matrix (m + n)} {Dm ⊗ᴹ Dn} {y}
      le ⌜ p ⌝ y = case (y ≟ᴹ ⌜ p ⌝)
        where
          case : Dec (y ≡ ⌜ p ⌝) → entry (delay-matrix (m + n)) ⌜ p ⌝ y ≤ᵗ entry (Dm ⊗ᴹ Dn) ⌜ p ⌝ y
          case (yes refl) =
            T.≤-trans {a} {b} {e} (T.≤-reflexive (diag-entry (m + n) p))
              (T.≤-trans {b} {c} {e} (proj₁ (plus-box m n p))
                (T.≤-trans {c} {d} {e} (T.≤-reflexive (sym (cong₂ T._⊗_ (diag-entry m p) (diag-entry n p))))
                           (⊗ᴹ-ub Dm Dn ⌜ p ⌝ ⌜ p ⌝ ⌜ p ⌝)))
            where
              a = entry (delay-matrix (m + n)) ⌜ p ⌝ ⌜ p ⌝
              b = spent (dur (m + n)) p
              c = T._⊗_ (spent (dur m) p) (spent (dur n) p)
              d = T._⊗_ (entry Dm ⌜ p ⌝ ⌜ p ⌝) (entry Dn ⌜ p ⌝ ⌜ p ⌝)
              e = entry (Dm ⊗ᴹ Dn) ⌜ p ⌝ ⌜ p ⌝
          case (no ne) = subst (_≤ᵗ entry (Dm ⊗ᴹ Dn) ⌜ p ⌝ y) (sym (off-entry (m + n) p ne))
                               (T.𝟘-≤ (entry (Dm ⊗ᴹ Dn) ⌜ p ⌝ y))
      ge : (Dm ⊗ᴹ Dn) ≤ᵖ delay-matrix (m + n)
      ge stuck y = stuck-rows {Dm ⊗ᴹ Dn} {delay-matrix (m + n)} {y}
      ge ⌜ p ⌝ y = ⊗ᴹ-lub Dm Dn ⌜ p ⌝ y {entry (delay-matrix (m + n)) ⌜ p ⌝ y} term
        where
          term : ∀ q → T._⊗_ (entry Dm ⌜ p ⌝ q) (entry Dn q y) ≤ᵗ entry (delay-matrix (m + n)) ⌜ p ⌝ y
          term q = caseq (q ≟ᴹ ⌜ p ⌝) (y ≟ᴹ ⌜ p ⌝)
            where
              target = entry (delay-matrix (m + n)) ⌜ p ⌝ y
              caseq : Dec (q ≡ ⌜ p ⌝) → Dec (y ≡ ⌜ p ⌝) → T._⊗_ (entry Dm ⌜ p ⌝ q) (entry Dn q y) ≤ᵗ target
              caseq (no nq) _ =
                T.≤-trans {T._⊗_ (entry Dm ⌜ p ⌝ q) (entry Dn q y)} {T._⊗_ T.𝟘 (entry Dn q y)} {target}
                  (T.⊗-mono {entry Dm ⌜ p ⌝ q} {T.𝟘} {entry Dn q y} {entry Dn q y} (T.≤-reflexive (off-entry m p nq)) (T.≤-refl {entry Dn q y}))
                  (T.≤-trans {T._⊗_ T.𝟘 (entry Dn q y)} {T.𝟘} {target} (T.⊗-zeroˡ (entry Dn q y)) (T.𝟘-≤ target))
              caseq (yes refl) (yes refl) =
                T.≤-trans {d} {c} {target} (T.≤-reflexive (cong₂ T._⊗_ (diag-entry m p) (diag-entry n p)))
                  (T.≤-trans {c} {spent (dur (m + n)) p} {target} (proj₂ (plus-box m n p))
                             (T.≤-reflexive (sym (diag-entry (m + n) p))))
                where
                  c = T._⊗_ (spent (dur m) p) (spent (dur n) p)
                  d = T._⊗_ (entry Dm ⌜ p ⌝ ⌜ p ⌝) (entry Dn ⌜ p ⌝ ⌜ p ⌝)
              caseq (yes refl) (no ny) =
                T.≤-trans {T._⊗_ (entry Dm ⌜ p ⌝ ⌜ p ⌝) (entry Dn ⌜ p ⌝ y)} {T._⊗_ (entry Dm ⌜ p ⌝ ⌜ p ⌝) T.𝟘} {target}
                  (T.⊗-mono {entry Dm ⌜ p ⌝ ⌜ p ⌝} {entry Dm ⌜ p ⌝ ⌜ p ⌝} {entry Dn ⌜ p ⌝ y} {T.𝟘} (T.≤-refl {entry Dm ⌜ p ⌝ ⌜ p ⌝}) (T.≤-reflexive (off-entry n p ny)))
                  (T.≤-trans {T._⊗_ (entry Dm ⌜ p ⌝ ⌜ p ⌝) T.𝟘} {T.𝟘} {target} (T.⊗-zeroʳ (entry Dm ⌜ p ⌝ ⌜ p ⌝)) (T.𝟘-≤ target))

delays : Delays time-entries ℕᴰ
delays = record
  { delay      = delayᵐ
  ; delay-zero = delay-zero
  ; delay-plus = delay-plus
  }

mode-times : Grade ℕᴰ
mode-times = mode-grade-with time-entries delays
